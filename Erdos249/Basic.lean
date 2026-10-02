module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Totient
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Supporting lemmas for the Erdős 249 series

These facts are classical. They do not decide whether the sum is irrational.
-/

namespace Erdos249

/-- The general term of the series as a multiple of a geometric term. -/
theorem term_eq (n : ℕ) :
    (n.totient : ℝ) / (2 : ℝ) ^ n = (n.totient : ℝ) * (1 / 2 : ℝ) ^ n := by
  rw [div_eq_mul_inv, inv_pow, ← one_div]

/-- $\varphi(n)/2^n \le n/2^n$. -/
theorem term_le (n : ℕ) :
    (n.totient : ℝ) / (2 : ℝ) ^ n ≤ (n : ℝ) * (1 / 2 : ℝ) ^ n := by
  rw [term_eq]
  gcongr
  · positivity
  · exact Nat.cast_le.mpr n.totient_le

/-- The series $\sum \varphi(n)/2^n$ converges. -/
theorem term_summable : Summable fun n : ℕ ↦ (n.totient : ℝ) / (2 : ℝ) ^ n :=
  .of_nonneg_of_le (fun _ ↦ by positivity) term_le
    (by simpa using
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))

/-- $1 < \sum \varphi(n)/2^n < 2$. -/
theorem tsum_mem_Ioo :
    (∑' n : ℕ, (n.totient : ℝ) / (2 : ℝ) ^ n) ∈ Set.Ioo (1 : ℝ) 2 := by
  have hf (n : ℕ) : 0 ≤ (n.totient : ℝ) / (2 : ℝ) ^ n := by positivity
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hsumg : Summable fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  constructor
  · have hφ3 : Nat.totient 3 = 2 := by rw [Nat.totient_prime Nat.prime_three]
    have hφ4 : Nat.totient 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.totient_prime_pow Nat.prime_two (by norm_num)]
      norm_num
    have hpartial : ∑ n ∈ Finset.range 5, (n.totient : ℝ) / (2 : ℝ) ^ n = (9 : ℝ) / 8 := by
      simp [Finset.sum_range_succ, Nat.totient_zero, Nat.totient_one, Nat.totient_two, hφ3, hφ4]
      norm_num
    have hle := term_summable.sum_le_tsum (Finset.range 5) fun _ _ ↦ hf _
    have : (9 : ℝ) / 8 ≤ ∑' n : ℕ, (n.totient : ℝ) / (2 : ℝ) ^ n :=
      hpartial.trans_le hle
    linarith
  · have hlt := Summable.tsum_lt_tsum_of_nonneg (i := 2) hf term_le ?_ hsumg
    · have hgval : (∑' n : ℕ, (n : ℝ) * (1 / 2 : ℝ) ^ n) = 2 := by
        rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
        norm_num
      simpa [hgval] using hlt
    · simp [Nat.totient_two]
      norm_num

end Erdos249
