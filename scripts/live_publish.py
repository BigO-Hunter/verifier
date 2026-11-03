"""Fresh trusted writer watches immutable Lean checkpoints; never executes proof data."""
import json
import os
from pathlib import Path
import re
import time
import pr_submissions as p
import submissions as s


def archive(artifact):
    p.validate_artifact_size(artifact)
    raw=p.api(f"actions/artifacts/{artifact['id']}/zip",raw=True)
    return p.read_archive(raw,artifact)


def issue_final_available(run, number):
    """Read fresh run state, not the watcher's earlier artifact snapshot."""
    current = p.api(f"actions/runs/{run['id']}")
    if current['run_attempt'] != run['run_attempt'] or current['status'] == 'completed':
        return True
    names = {
        f"verifier-receipt-and-logs-{run['id']}-{run['run_attempt']}-{number}",
        f"direct-submission-{run['id']}-{run['run_attempt']}-{number}",
    }
    page = 1
    while True:
        artifacts = p.api(f"actions/runs/{run['id']}/artifacts?per_page=100&page={page}")['artifacts']
        if any(a['name'] in names for a in artifacts):
            return True
        if len(artifacts) < 100:
            return False
        page += 1
        if page > 10:
            # Fail closed if an unexpected run has too many artifacts to inspect.
            return True


def publish_issue(run, artifact):
    files=archive(artifact)
    selected=json.loads(files['selected-request.json'])
    receipt=json.loads(files['receipt.json'])
    number=selected['issue_number']
    if type(number) is not int or number<=0 or artifact['name'] != f"verifier-receipt-and-logs-{run['id']}-{run['run_attempt']}-{number}-lean":
        raise ValueError('Early issue artifact identity mismatch')
    if receipt.get('verification_stage') != 'lean':
        raise ValueError('Missing Lean checkpoint stage')
    for name,expected in receipt.get('artifact_sha256',{}).items():
        if name not in files or p.digest(files[name])!=expected:
            raise ValueError('Early receipt log hash mismatch')
    issue=p.api(f'issues/{number}')
    smoke_test=__import__('smoke').active(selected)
    expected=s.issue_input(issue,smoke=smoke_test)
    if smoke_test:
        expected=__import__('smoke').issue_submission(expected)
    if issue['state']!='open' or expected!=selected['submission'] or s.body_hash(issue['body'])!=selected['issue_body_sha256'] or issue['user']['login']!=selected['issue_submitter_login']:
        return
    url=f"https://github.com/{s.REPOSITORY}/actions/runs/{run['id']}/artifacts/{artifact['id']}"
    env=s.envelope(receipt,selected,run['id'],run['run_attempt'],run['head_sha'],url)
    env.update(verification_stage='lean',receipt_sha256=p.digest(files['receipt.json']),
        receipt_artifact={'id':artifact['id'],'name':artifact['name'],'digest':artifact['digest'],'archive_url':url},
        publisher_commit=os.environ['GITHUB_SHA'],publisher_run_id=os.environ['GITHUB_RUN_ID'],publisher_run_attempt=os.environ['GITHUB_RUN_ATTEMPT'],workflow_conclusion=run['conclusion'])
    if issue_final_available(run, number):
        return
    Path('published').mkdir(exist_ok=True)
    Path(f'published/direct-submission-{number}-lean.json').write_text(s.canonical(env)+'\n')
    status='Lean Verified' if env['verification_status']=='passed' else env['verification_status']
    if selected.get('test_only'):status='TEST ONLY: '+status+' (never imported)'
    elif env['verification_status']=='passed' and s.derivation_hold(selected):status+='. '+s.HOLD_TEXT.format(item='issue').removesuffix('.')
    # GitHub has no atomic artifact-check/comment-write operation. Describe the
    # immutable checkpoint, never current nanoda status: final publication can
    # race the last API read without making this historical statement false.
    s.comment_once(number,f"Lean checkpoint recorded: {status}. This checkpoint does not include the final nanoda result.\n\n[Lean checkpoint receipt and logs]({url}) · [Current workflow results](https://github.com/{s.REPOSITORY}/actions/runs/{run['id']})",p.api)


def watch():
    event=json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    run_id=event['workflow_run']['id'];attempt=event['workflow_run']['run_attempt']
    seen=set();expected=None;silent=set();deadline=time.monotonic()+330*60
    while time.monotonic()<deadline:
        run=p.api(f'actions/runs/{run_id}')
        p.validate_run_identity(run,allow_running=True)
        if run['run_attempt']!=attempt:
            return
        artifacts=p.api(f'actions/runs/{run_id}/artifacts?per_page=100')['artifacts']
        if expected is None:
            inputs=[a for a in artifacts if a['name']==f'direct-requests-{run_id}-{attempt}' and not a.get('expired')]
            if len(inputs)>1:raise ValueError('Duplicate selection artifact')
            if inputs:
                selected=archive(inputs[0])
                if len(selected)>10 or any(not re.fullmatch(r'[1-9][0-9]*\.json',k) for k in selected):
                    raise ValueError('Invalid selection artifact')
                expected={int(k[:-5]) for k in selected}
                # A silent maintainer smoke gets no checkpoint comment and no review label.
                silent={int(k[:-5]) for k,raw in selected.items() if __import__('smoke').silent(json.loads(raw))}
        for artifact in artifacts:
            match=re.fullmatch(rf'(pr-verification|verifier-receipt-and-logs)-{run_id}-{attempt}-([1-9][0-9]*)-lean',artifact['name'])
            if not match or artifact.get('expired') or artifact['id'] in seen:continue
            if expected is None or int(match[2]) not in expected:raise ValueError('Checkpoint outside selected batch')
            if int(match[2]) in silent:
                seen.add(artifact['id']);continue
            try:
                if match[1]=='pr-verification':p.publish_pr(artifact,stage='lean')
                else:publish_issue(run,artifact)
            except (ValueError, KeyError) as exc:
                print('Checkpoint requires review:', type(exc).__name__, flush=True)
                p.label_review(int(match[2]),f'{run_id} {attempt}')
            seen.add(artifact['id'])
        if run['status']=='completed' or (expected is not None and len(seen)==len(expected)):
            return
        time.sleep(20)
    raise TimeoutError('Lean publication watcher deadline exceeded')


if __name__=='__main__':
    event=json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    if event.get('action')=='in_progress':watch()
    else:p.publish_batch()
