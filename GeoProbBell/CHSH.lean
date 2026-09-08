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
  rw [chsh_affine]
  have hA : |μ * chsh E| ≤ μ * 2 := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left hE h0
  have hB : |2 * (1 - μ) * b| ≤ 2 * (1 - μ) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 - μ))]
    exact mul_le_of_le_one_right (by linarith) hb
  calc |μ * chsh E + 2 * (1 - μ) * b| ≤ |μ * chsh E| + |2 * (1 - μ) * b| := abs_add _ _
    _ ≤ μ * 2 + 2 * (1 - μ) := add_le_add hA hB
    _ = 2 := by ring

/-- The re-charted CHSH value, bounded using Tsirelson's number as an input.
This is the boxed inequality of §8. -/
theorem chsh_bound (μ b : ℝ) (E : Fin 2 → Fin 2 → ℝ) (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (hT : |chsh E| ≤ 2 * Real.sqrt 2) :
    |chsh (fun x y => μ * E x y + (1 - μ) * b)|
      ≤ 2 * Real.sqrt 2 * μ + 2 * (1 - μ) * |b| := by
  rw [chsh_affine]
  have hA : |μ * chsh E| ≤ μ * (2 * Real.sqrt 2) := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left hT h0
  have hB : |2 * (1 - μ) * b| = 2 * (1 - μ) * |b| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 - μ))]
  calc |μ * chsh E + 2 * (1 - μ) * b| ≤ |μ * chsh E| + |2 * (1 - μ) * b| := abs_add _ _
    _ = |μ * chsh E| + 2 * (1 - μ) * |b| := by rw [hB]
    _ ≤ μ * (2 * Real.sqrt 2) + 2 * (1 - μ) * |b| := by linarith
    _ = 2 * Real.sqrt 2 * μ + 2 * (1 - μ) * |b| := by ring

end GeoProbBell
