/-
# The chart-change dial

Charts, distributions, readouts, and the one-parameter family of chart changes
`mix u μ`.  Corresponds to §1 and §6 of the post.

The dial is defined against an *arbitrary* reference distribution `u`, not just
the uniform one.  The uniform `u ≡ 1/N` of the post is the special case
`GeoProbBell.unif` in `GeoProbBell.SleepingBeauty`.  Carrying `u` around keeps
every proof in this file free of division, which is why the group law below is
a one-line ring identity.
-/
import Mathlib

open Finset

namespace GeoProbBell

variable {ι : Type*} [Fintype ι]

/-- The pairing of a readout with a distribution: `⟨w, d⟩ = ∑ᵢ wᵢ dᵢ`. -/
def pair (w d : ι → ℝ) : ℝ := ∑ i, w i * d i

theorem pair_comm (w d : ι → ℝ) : pair w d = pair d w := by
  simp only [pair, mul_comm]

/-- The chart-change dial with reference distribution `u`.  For the uniform
reference `u ≡ 1/N` this is the matrix `μ • I + ((1-μ)/N) • J`. -/
def mix (u : ι → ℝ) (μ : ℝ) (d : ι → ℝ) : ι → ℝ :=
  fun i => μ * d i + (1 - μ) * u i * (∑ j, d j)

/-- The transpose of the dial, acting on a readout. -/
def adj (u : ι → ℝ) (μ : ℝ) (w : ι → ℝ) : ι → ℝ :=
  fun i => μ * w i + (1 - μ) * pair u w

/-- The dial preserves total mass. -/
theorem sum_mix (u : ι → ℝ) (hu : ∑ i, u i = 1) (μ : ℝ) (d : ι → ℝ) :
    ∑ i, mix u μ d i = ∑ i, d i := by
  have h : ∀ i : ι, mix u μ d i = μ * d i + ((1 - μ) * (∑ j, d j)) * u i := by
    intro i; simp only [mix]; ring
  simp only [h]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, hu]
  ring

/-- The dial preserves nonnegativity for `0 ≤ μ ≤ 1`. -/
theorem mix_nonneg (u : ι → ℝ) (μ : ℝ) (d : ι → ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, 0 ≤ d i) (i : ι) : 0 ≤ mix u μ d i := by
  have hD : 0 ≤ ∑ j, d j := Finset.sum_nonneg fun j _ => hd j
  have hA : 0 ≤ μ * d i := mul_nonneg h0 (hd i)
  have hB : 0 ≤ (1 - μ) * u i * (∑ j, d j) :=
    mul_nonneg (mul_nonneg (by linarith) (hu i)) hD
  show 0 ≤ μ * d i + (1 - μ) * u i * (∑ j, d j)
  linarith

/-- **Group law.**  Dials compose by multiplying their parameters:
`M(μ) M(ν) = M(μν)`. -/
theorem mix_mix (u : ι → ℝ) (hu : ∑ i, u i = 1) (μ ν : ℝ) (d : ι → ℝ) :
    mix u μ (mix u ν d) = mix u (μ * ν) d := by
  funext i
  have h : ∑ j, mix u ν d j = ∑ j, d j := sum_mix u hu ν d
  have hq : mix u ν d i = ν * d i + (1 - ν) * u i * (∑ j, d j) := rfl
  calc mix u μ (mix u ν d) i
      = μ * (mix u ν d i) + (1 - μ) * u i * (∑ j, mix u ν d j) := rfl
    _ = μ * (ν * d i + (1 - ν) * u i * (∑ j, d j))
          + (1 - μ) * u i * (∑ j, d j) := by rw [hq, h]
    _ = (μ * ν) * d i + (1 - μ * ν) * u i * (∑ j, d j) := by ring
    _ = mix u (μ * ν) d i := rfl

/-- `μ = 1` is the identity of the group. -/
theorem mix_one (u : ι → ℝ) (d : ι → ℝ) : mix u 1 d = d := by
  funext i
  show 1 * d i + (1 - 1) * u i * (∑ j, d j) = d i
  ring

/-- **Inverse.**  `M(μ)⁻¹ = M(1/μ)` for `μ ≠ 0`.

Note that this is an inverse *as a linear map*.  For `μ ∈ (0,1)` the matrix
`M(1/μ)` has negative off-diagonal entries, so it is not itself a legal chart
change: un-mixing is algebra, not observation. -/
theorem mix_inv (u : ι → ℝ) (hu : ∑ i, u i = 1) (μ : ℝ) (hμ : μ ≠ 0) (d : ι → ℝ) :
    mix u (1 / μ) (mix u μ d) = d := by
  rw [mix_mix u hu, one_div, inv_mul_cancel₀ hμ, mix_one]

/-- `μ = 0` is the absorbing element: it collapses every distribution onto the
reference one. -/
theorem mix_zero (u : ι → ℝ) (d : ι → ℝ) (hd : ∑ j, d j = 1) : mix u 0 d = u := by
  funext i
  show 0 * d i + (1 - 0) * u i * (∑ j, d j) = u i
  rw [hd]; ring

end GeoProbBell
