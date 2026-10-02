# Contributing

This repository is a Palomar-style formalization of classical facts about the
Erdős 249 totient series. It does not claim a proof that the sum is irrational.

To adapt or extend the development:

1. Keep `Challenge.lean` as the small statement-only surface.
2. Put proofs in `Erdos249/` and re-export them from `Solution.lean`.
3. Keep `comparator.json` in sync with the advertised theorems.
4. Do not add a proof of the open irrationality question unless that proof is
   genuinely established in the literature and kernel-checked here.
5. After changing dependencies, run `lake update` and
   `cd docbuild && lake update`, then commit both manifests.

Submission policy: [Palomar CONTRIBUTING](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
The public form is [https://submit.palomar-registry.org/](https://submit.palomar-registry.org/).
