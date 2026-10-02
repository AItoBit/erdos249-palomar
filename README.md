# Erdős 249 totient series

[![CI](https://github.com/AItoBit/erdos249-palomar/actions/workflows/ci.yml/badge.svg)](https://github.com/AItoBit/erdos249-palomar/actions/workflows/ci.yml)

Lean 4 formalization of two classical facts about the series
\(\sum \varphi(n)/2^n\) that appears in
[Erdős problem 249](https://www.erdosproblems.com/249).

The irrationality of the sum is **open**. This repository does not prove it.

What is proved:

- the real series \(\sum_n \varphi(n)/2^n\) converges;
- its sum \(S\) satisfies \(1 < S < 2\), so \(S\) is not an integer.

The \(n = 0\) term vanishes because \(\varphi(0) = 0\).

## Palomar layout

- `Challenge.lean` is the small statement surface a reader audits.
- `Solution.lean` supplies the matching proofs.
- `Erdos249/` contains the supporting lemmas.
- `comparator.json` tells Comparator which declarations must match.
- `formalization.yaml` records provenance, authorship, and review metadata.
- Submit at [https://submit.palomar-registry.org/](https://submit.palomar-registry.org/).

## Build

```bash
lake exe cache get
lake build
```

Lean toolchain: `leanprover/lean4:v4.35.0-rc2`, matching the pinned Mathlib revision.
