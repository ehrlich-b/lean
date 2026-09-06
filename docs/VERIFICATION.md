# Verification and limitations

The public source is the exported import closure of the integrated development
library. It contains 32 theorem declarations and no unfinished task stubs.

Before publication, the public snapshot is built in a fresh project directory
on Linux/WSL, using the pinned Lean toolchain and existing read-only dependency
artifacts. The build uses one CPU equivalent, a 5 GiB memory cap, no swap, and
the development verifier lock. This is not a from-source rebuild of Mathlib.
The receipt in `verification/build-result.json` records the actual outcome;
`verification/build.log` records compiler output.

Earlier development candidates underwent isolated Comparator checks and AI
review. Raw development records contain private operational information and
are not included in this snapshot. The public receipt establishes the combined
build only; it is not a substitute for publishing a full independent replay
package. `source-manifest.json` binds the Lean files and dependency pins by hash.

No independent NanoDa replay or Palomar registration is claimed. A passing Lean
build does not establish novelty, mathematical significance, optimal API design,
or fidelity to every intended informal interpretation. Those remain open review
questions. The source is available for others to inspect and reproduce.

The initial release is pinned to Lean 4.33.1; prebuilt Mathlib caches may not
match that patch toolchain. `lake build LeanFactory` can therefore compile many
dependencies on a first checkout. No automatic model invocation or paid service
is part of this public build.
