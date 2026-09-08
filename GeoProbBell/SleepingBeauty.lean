/-
# Sleeping Beauty

§1 of the post: the uniform reference distribution, the credence `P_H(μ)`, its
two endpoints, and the fact that a contrast orthogonal to the reference reads
off the dial exactly.
-/
import GeoProbBell.Master

open Finset

namespace GeoProbBell

variable {ι : Type*} [Fintype ι]

/-- The uniform reference distribution on an `n`-slot chart. -/
noncomputable def unif (n : ℕ) : Fin n → ℝ := fun _ => 1 / n

theorem sum_unif {n : ℕ} (hn : n ≠ 0) : ∑ i, unif n i = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [unif, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The credence attached to a slot that carried weight `1/2` before the chart
change: `P_H(μ) = μ/2 + (1-μ)/n`. -/
theorem heads {n : ℕ} (μ : ℝ) (d : Fin n → ℝ) (i : Fin n)
    (hd : ∑ j, d j = 1) (hi : d i = 1 / 2) :
    mix (unif n) μ d i = μ / 2 + (1 - μ) / n := by
  simp only [mix, unif, hd, hi]
  ring

theorem heads_closed {n : ℕ} (hn : (n : ℝ) ≠ 0) (μ : ℝ) :
    μ / 2 + (1 - μ) / n = (μ * (n - 2) + 2) / (2 * n) := by
  field_simp
  ring

/-- At `μ = 1` the halfer's answer `1/2`; at `μ = 0` the fully blended `1/n`.
At `n = 3` these are the two famous answers. -/
theorem heads_endpoints {n : ℕ} (d : Fin n → ℝ) (i : Fin n)
    (hd : ∑ j, d j = 1) (hi : d i = 1 / 2) :
    mix (unif n) 1 d i = 1 / 2 ∧ mix (unif n) 0 d i = 1 / n := by
  constructor
  · rw [heads 1 d i hd hi]; ring
  · rw [heads 0 d i hd hi]; ring

/-- **A contrast reads off the dial.**  If `⟨c,d⟩ = 1` and `⟨c,u⟩ = 0` then
`⟨c, M(μ) d⟩ = μ` exactly.  This is `S_SB(μ) = μ`, and it is the structural
reason for "one index, one factor of `μ`". -/
theorem contrast (u : ι → ℝ) (μ : ℝ) (c d : ι → ℝ) (hd : ∑ j, d j = 1)
    (h1 : pair c d = 1) (h2 : pair c u = 0) :
    pair c (mix u μ d) = μ := by
  rw [master u μ c d hd, h1, h2]; ring

/-- The mean of a readout against the uniform reference.  With
`∑ v = 1 + (-1) + (n-2) s` this is the `c_n s` of §8. -/
theorem mean_unif {n : ℕ} (v : Fin n → ℝ) (s : ℝ) (hv : ∑ k, v k = (n - 2) * s) :
    pair (unif n) v = (n - 2) * s / n := by
  simp only [pair, unif, ← mul_sum, hv]
  ring

end GeoProbBell
