/-
# CHSH under a chart change

§5 and §6 of the post.  Nothing quantum-mechanical is assumed anywhere in this
project; Tsirelson's number enters only as the hypothesis
`hT : |chsh E| ≤ 2 * Real.sqrt 2` of `chsh_bound`.
-/
import GeoProbBell.Master

open Finset

namespace GeoProbBell

/-- The CHSH combination of four correlation numbers.  The two indices are
*settings*, not outcomes. -/
def chsh (E : Fin 2 → Fin 2 → ℝ) : ℝ := E 0 0 + E 0 1 + E 1 0 - E 1 1

/-- **The transformation law.**  A chart change is affine on every correlation
number, with the same `μ` and the same offset for all four setting pairs, since
the chart belongs to the observer and not to what she chose to measure.  Hence
`S' = μ S + 2(1-μ) ω̄`. -/
theorem chsh_affine (μ b : ℝ) (E : Fin 2 → Fin 2 → ℝ) :
    chsh (fun x y => μ * E x y + (1 - μ) * b) = μ * chsh E + 2 * (1 - μ) * b := by
  simp only [chsh]; ring

/-- **The local bound is chart-independent.**  If the original correlations obey
`|S| ≤ 2`, so do the re-charted ones, whatever value the observer gives to the
event-types she cannot resolve.  So `2` remains the right thing to compare
against on the new chart. -/
theorem chsh_local_preserved (μ b : ℝ) (E : Fin 2 → Fin 2 → ℝ)
    (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (hb : |b| ≤ 1) (hE : |chsh E| ≤ 2) :
    |chsh (fun x y => μ * E x y + (1 - μ) * b)| ≤ 2 := by
  rw [chsh_affine, abs_le]
  have hb' := abs_le.mp hb
  have hE' := abs_le.mp hE
  have hμ : (0:ℝ) ≤ 1 - μ := by linarith
  have p1 : 0 ≤ μ * (2 - chsh E) := mul_nonneg h0 (by linarith [hE'.2])
  have p2 : 0 ≤ μ * (chsh E + 2) := mul_nonneg h0 (by linarith [hE'.1])
  have p3 : 0 ≤ (1 - μ) * (1 - b) := mul_nonneg hμ (by linarith [hb'.2])
  have p4 : 0 ≤ (1 - μ) * (b + 1) := mul_nonneg hμ (by linarith [hb'.1])
  constructor <;> nlinarith [p1, p2, p3, p4]

/-- The re-charted CHSH value, bounded using Tsirelson's number as an input.
This is the boxed inequality of §8. -/
theorem chsh_bound (μ b : ℝ) (E : Fin 2 → Fin 2 → ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (hT : |chsh E| ≤ 2 * Real.sqrt 2) :
    |chsh (fun x y => μ * E x y + (1 - μ) * b)|
      ≤ 2 * Real.sqrt 2 * μ + 2 * (1 - μ) * |b| := by
  rw [chsh_affine, abs_le]
  have hT' := abs_le.mp hT
  have hb' := abs_le.mp (le_refl |b|)
  have hμ : (0:ℝ) ≤ 1 - μ := by linarith
  have p1 : 0 ≤ μ * (2 * Real.sqrt 2 - chsh E) := mul_nonneg h0 (by linarith [hT'.2])
  have p2 : 0 ≤ μ * (chsh E + 2 * Real.sqrt 2) := mul_nonneg h0 (by linarith [hT'.1])
  have p3 : 0 ≤ (1 - μ) * (|b| - b) := mul_nonneg hμ (by linarith [hb'.2])
  have p4 : 0 ≤ (1 - μ) * (b + |b|) := mul_nonneg hμ (by linarith [hb'.1])
  constructor <;> nlinarith [p1, p2, p3, p4]

end GeoProbBell
