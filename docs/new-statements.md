# Contribute a trusted Lean statement

Ask for a route in an issue first; open a statement pull request only when a maintainer asks for one.

A problem needs a trusted statement before the verifier can accept direct proof
submissions. Contributors can propose that statement in a normal review PR.
Maintainers review statement PRs; the proof-submission bot does not merge them.

## Files to include

Use a new folder with the problem's site slug:

```text
challenges/<problem>/
  Statement.lean
  README.md
  LICENSE             # when required by the source license
```

Keep supporting model definitions in this folder. The README must link to the
problem page on [bigospeedrun.com](https://bigospeedrun.com), explain the model
and bound, and identify the Lean version and exact Mathlib commit. Use Mathlib
and its pinned dependencies only. Do not add external libraries, build hooks,
network downloads, custom axioms, or compiled files.

For an existing statement, give the source repository, full commit SHA, original
file paths, authors, license, and file hashes. Preserve license and attribution
notices. Keep the frozen upstream statement byte-identical and put any target
adapter in a separate file. For a new statement, identify its authors and license.

## State the model and the bound

The model must match the problem page: inputs, outputs, uniformity, arithmetic
operations, preprocessing, cost measure, and asymptotic conventions. Explain any
assumptions. A weaker model or a different input domain needs review before it
can represent that board.

Expose a proposition with the bound as a parameter. Follow the DFT shape in
[challenges/dft](../challenges/dft/) and the exact target in
[the target guide](targets.md): fixed definitions describe a valid algorithm;
the target asserts that such an algorithm exists with the stated cost bound.
The verifier substitutes the submitted exact rational into this proposition and
checks a theorem named `Race.bound`. The contributor does not choose a new model
through that parameter. Document the parameter's range and whether larger or
smaller values improve the bound. Current direct submissions require an attained
bound; strict frontiers need a separate contract change.

The trusted target describes the claim to prove. It must not include an assumed
proof of the submitted bound. Permitted proof axioms are `propext`,
`Classical.choice`, and `Quot.sound` only.

## Review before merge

Maintainers review the mathematical statement against the site model, the cost
accounting, parameter meaning, and possible vacuous or unintended claims. They
also review provenance and licensing, the dependency pins, and all definitions
that Comparator must match.

Maintainers add the verifier-owned profile, target generator, form option, and
receipt/import bindings as part of enabling the statement. They test statement
matching, wrong-bound rejection, and the axiom audit. Lean checks run on GitHub
Actions, not on the office server. A normal build alone is insufficient:
Comparator must accept the exact statement with the Lean kernel and permitted
axioms; nanoda supplies the advisory second check.

Once maintainers merge and enable the reviewed statement, the problem is open
to direct proof submissions through either an issue or a proof PR. The normal
record gate and proof checks still apply. Merging a statement does not verify
any claimed algorithm or transfer credit to its contributors.
