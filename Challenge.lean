module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Totient
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

/-!
# Erdős problem 249: the totient series

Erdős asked whether
$$
\sum_{n} \frac{\varphi(n)}{2^n}
$$
is irrational, where $\varphi$ is Euler's totient function. See
[erdosproblems.com/249](https://www.erdosproblems.com/249). The question remains
open.

This Challenge records two classical facts that make the series a well-defined
real number strictly between $1$ and $2$. The $n = 0$ term vanishes because
$\varphi(0) = 0$, so the sum over `ℕ` agrees with the usual sum from $n = 1$.

The decimal expansion of the sum is OEIS A256936. These statements do not
decide irrationality.
-/

namespace Erdos249

/--
The series $\sum_n \varphi(n)/2^n$ appearing in Erdős problem 249.
The $n = 0$ term is zero because $\varphi(0) = 0$.
-/
noncomputable def erdos249Sum : ℝ := ∑' n : ℕ, (n.totient : ℝ) / (2 : ℝ) ^ n

/-- The series $\sum \varphi(n)/2^n$ converges. -/
theorem erdos249Sum_summable : Summable fun n : ℕ ↦ (n.totient : ℝ) / (2 : ℝ) ^ n := by
  sorry

/--
$1 < \sum \varphi(n)/2^n < 2$. In particular the sum is not an integer.
This does not decide whether the sum is irrational.
-/
theorem erdos249Sum_mem_Ioo : erdos249Sum ∈ Set.Ioo (1 : ℝ) 2 := by
  sorry

end Erdos249
