module

public import Erdos249

public section

/-!
# Proved solution

Comparator checks that these declarations match `Challenge.lean` and that the
proofs use only the permitted axioms.
-/

namespace Erdos249

/-- The series $\sum \varphi(n)/2^n$ converges. -/
theorem erdos249Sum_summable : Summable fun n : ℕ ↦ (n.totient : ℝ) / (2 : ℝ) ^ n :=
  term_summable

/--
$1 < \sum \varphi(n)/2^n < 2$. In particular the sum is not an integer.
This does not decide whether the sum is irrational.
-/
theorem erdos249Sum_mem_Ioo :
    (∑' n : ℕ, (n.totient : ℝ) / (2 : ℝ) ^ n) ∈ Set.Ioo (1 : ℝ) 2 :=
  tsum_mem_Ioo

end Erdos249
