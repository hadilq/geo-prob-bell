/-
# The master formula

Propositions 1 and 2 of the post (§6): how a chart change acts on a correlation
number, and the fact that it never strengthens a readout.
-/
import GeoProbBell.Mixer

open Finset

namespace GeoProbBell

variable {ι : Type*} [Fintype ι]

/-- The dial acts on the pairing by an affine rescaling. -/
theorem pair_mix (u : ι → ℝ) (μ : ℝ) (w d : ι → ℝ) :
    pair w (mix u μ d) = μ * pair w d + (1 - μ) * pair w u * (∑ j, d j) := by
  have h : ∀ i : ι, w i * mix u μ d i
      = μ * (w i * d i) + ((1 - μ) * (∑ j, d j)) * (w i * u i) := by
    intro i; simp only [mix]; ring
  simp only [pair, h, sum_add_distrib, ← mul_sum]
  ring

/-- **Proposition 1 (master formula).**  On a probability vector the chart
change reads `E' = μ E + (1-μ) ⟨w, u⟩`.

One index, one factor of `μ`. -/
theorem master (u : ι → ℝ) (μ : ℝ) (w d : ι → ℝ) (hd : ∑ j, d j = 1) :
    pair w (mix u μ d) = μ * pair w d + (1 - μ) * pair w u := by
  rw [pair_mix, hd]; ring

/-- The dial moved onto the readout: `⟨M(μ)ᵀ w, d⟩ = ⟨w, M(μ) d⟩`.

This is what licenses the reading of Proposition 1 in the post: a chart change
never touches the recorded vector, it reweights the readout. -/
theorem pair_adj (u : ι → ℝ) (μ : ℝ) (w d : ι → ℝ) (hd : ∑ j, d j = 1) :
    pair (adj u μ w) d = pair w (mix u μ d) := by
  rw [master u μ w d hd, pair_comm w u]
  have h : ∀ i : ι, adj u μ w i * d i
      = μ * (w i * d i) + ((1 - μ) * pair u w) * d i := by
    intro i; simp only [adj]; ring
  simp only [pair, h, sum_add_distrib, ← mul_sum]
  rw [hd]
  ring

/-- **Proposition 2 (contraction lemma).**  A chart change never strengthens a
readout: spreading the same events over more event-types can only weaken the
verdict. -/
theorem adj_le (u : ι → ℝ) (μ : ℝ) (w : ι → ℝ) (c : ℝ)
    (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (hw : ∀ i, |w i| ≤ c) (hu : |pair u w| ≤ c) (i : ι) :
    |adj u μ w i| ≤ c := by
  have hw' := abs_le.mp (hw i)
  have hu' := abs_le.mp hu
  have hμ : (0:ℝ) ≤ 1 - μ := by linarith
  have p1 : 0 ≤ μ * (w i + c) := mul_nonneg h0 (by linarith [hw'.1])
  have p2 : 0 ≤ μ * (c - w i) := mul_nonneg h0 (by linarith [hw'.2])
  have p3 : 0 ≤ (1 - μ) * (pair u w + c) := mul_nonneg hμ (by linarith [hu'.1])
  have p4 : 0 ≤ (1 - μ) * (c - pair u w) := mul_nonneg hμ (by linarith [hu'.2])
  show |μ * w i + (1 - μ) * pair u w| ≤ c
  rw [abs_le]
  constructor <;> nlinarith [p1, p2, p3, p4]

end GeoProbBell
