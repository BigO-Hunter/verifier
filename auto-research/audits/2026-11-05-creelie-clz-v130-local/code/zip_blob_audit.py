#!/usr/bin/env python3
"""zip_blob_audit.py — prove the deposited Zenodo zip's files are byte-identical to the git pin.

Compares every regular file in the zip against the blob hash of the same path in the pinned
commit (git hash-object of the extracted file vs `git ls-tree -r <pin>` blob id). Reports
counts of mismatches, files only in the zip, and files only in the tree. Directory entries
are ignored.

Usage: python3 zip_blob_audit.py <artifact.zip> <git-clone> <commit>
"""
import subprocess
import sys
import zipfile

zip_path, repo, commit = sys.argv[1], sys.argv[2], sys.argv[3]
prefix = None
zin = zipfile.ZipFile(zip_path)
zip_files = {}
for info in zin.infolist():
    if info.is_dir():
        continue
    name = info.filename
    if prefix is None:
        prefix = name.split("/", 1)[0] + "/"
    rel = name[len(prefix):] if name.startswith(prefix) else name
    blob = zin.read(info)
    oid = subprocess.run(
        ["git", "-C", repo, "hash-object", "--stdin"],
        input=blob, capture_output=True, check=True,
    ).stdout.decode().strip()
    zip_files[rel] = (oid, len(blob))

tree = {}
out = subprocess.run(
    ["git", "-C", repo, "ls-tree", "-r", "-l", commit],
    capture_output=True, check=True,
).stdout.decode().splitlines()
for line in out:
    meta, path = line.split("\t", 1)
    mode, otype, oid, size = meta.split()
    if otype == "blob":
        tree[path] = (oid, int(size))

mismatch = [p for p in zip_files if p in tree and zip_files[p][0] != tree[p][0]]
missing_in_git = [p for p in zip_files if p not in tree]
in_git_only = [p for p in tree if p not in zip_files]
print(f"zip_file={zip_path} prefix={prefix} commit={commit}")
print(f"files_checked={len(zip_files)} tree_blobs={len(tree)}")
print(f"mismatches={len(mismatch)} missing_in_git={len(missing_in_git)} in_git_not_zip={len(in_git_only)}")
for p in mismatch[:20]:
    print(f"MISMATCH {p} zip={zip_files[p][0]} tree={tree[p][0]} size={zip_files[p][1]}")
for p in missing_in_git[:20]:
    print(f"ZIP_ONLY {p} size={zip_files[p][1]}")
for p in in_git_only[:20]:
    print(f"GIT_ONLY {p} size={tree[p][1]}")
sys.exit(0 if not mismatch and not missing_in_git and not in_git_only else 1)
