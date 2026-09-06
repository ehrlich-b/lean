# Validation and publication

Every push and pull request runs two checks:

- `publication-boundary`: test the publication guard; check tracked files,
  exported module coverage, source hashes, prohibited proof placeholders, and
  common private-data/credential patterns. This is a conservative screen, not
  a comprehensive secret scanner.
- `lean-validation`: build the entire exported library from pinned project
  source, audit the transitive axioms of every declaration defined in our
  modules (including declarations in Mathlib namespaces), and replay the
  imported environment with `leanchecker --fresh`.

Only `propext`, `Classical.choice`, and `Quot.sound` are allowed by the axiom
check. The kernel replay is separate from the axiom audit. Project build outputs
are not cached; dependency builds are cached by toolchain and manifest hashes.
CI uploads logs, source hashes, dependency pins and checked commit for 30 days.
A weekly scheduled run checks main again. Third-party actions are pinned by SHA;
workflows use read-only repository permission and no private credentials.

Proofs may be generated and reviewed by AI. Before publication the maintainer
must still reconcile the frozen statement, proof review, current source,
duplicate search and concrete consumers. CI does not establish novelty,
mathematical usefulness, or faithful modeling of an intended application.

Publish through a work branch and a PR in this repository. Require both checks
on the current commit against the current base before merging. Never bypass a
failed check. Keep dependency and validation-infrastructure changes separate
from mathematical result batches. Upstream contribution requires its own review;
this repository's successful CI does not imply upstream acceptance.
