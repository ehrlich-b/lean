# Verification and limitations

The public source is the exported import closure of the integrated development
library. It contains no unfinished task stubs. Every newly exported theorem
module is bound by a publication receipt to exact private candidate and
integration evidence.

Development candidates underwent two isolated Comparator/kernel checks,
digest-bound AI review, and a combined build on the capped WSL verifier.
Concrete application callers were separately checked where their admission
required them. Raw development records may contain private operational
information and are not included here. `docs/source-manifest.json` binds the
Lean files and dependency pins by hash.

The archived `verification/build-result.json` and `verification/build.log`
describe the initial release; they do not attest later modules. For each new
public commit, the CI workflow builds the complete exported root from pinned
source, audits transitive axioms, and runs `leanchecker --fresh`. Its run and
uploaded logs are the public validation record for that commit.

No independent NanoDa replay or Palomar registration is claimed. A passing Lean
build does not establish novelty, mathematical significance, optimal API design,
or fidelity to every intended informal interpretation. Those remain open review
questions. The source is available for others to inspect and reproduce.

The project is pinned to Lean 4.33.1; prebuilt Mathlib caches may not
match that patch toolchain. `lake build LeanFactory` can therefore compile many
dependencies on a first checkout. No automatic model invocation or paid service
is part of this public build.
