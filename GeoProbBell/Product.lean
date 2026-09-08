/-
# The product chart

§3, §6 and §9 of the post: the two-wing counting space, the factorisation of a
product readout's mean, and the wing-wise dial `M(μ) ⊗ M(μ)` which — unlike the
joint dial — carries two factors of `μ`.
-/
import GeoProbBell.Master

open Finset

namespace GeoProbBell

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A product of two distributions is a distribution on the product chart. -/
theorem prod_dist (uA : α → ℝ) (uB : β → ℝ) (h1 : ∑ a, uA a = 1) (h2 : ∑ b, uB b = 1) :
    ∑ q : α × β, uA q.1 * uB q.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, h2, mul_one, h1]

/-- The pairing of a product readout with a product reference factorises:
`ω̄ = v̄_A v̄_B`. -/
theorem pair_prod (uA vA : α → ℝ) (uB vB : β → ℝ) :
    (∑ q : α × β, (uA q.1 * uB q.2) * (vA q.1 * vB q.2))
      = (pair uA vA) * (pair uB vB) := by
  simp only [pair]
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- **Wing-wise re-charting.**  If each wing's readout is transformed by its own
dial, the correlation picks up two factors of `μ` plus two cross terms built
from the marginal means. -/
theorem wing_pair (uA vA : α → ℝ) (uB vB : β → ℝ) (μ : ℝ) (p : α × β → ℝ)
    (hp : ∑ q, p q = 1) :
    (∑ q : α × β, (adj uA μ vA q.1 * adj uB μ vB q.2) * p q)
      = μ ^ 2 * (∑ q : α × β, (vA q.1 * vB q.2) * p q)
        + μ * (1 - μ) * pair uB vB * (∑ q : α × β, vA q.1 * p q)
        + μ * (1 - μ) * pair uA vA * (∑ q : α × β, vB q.2 * p q)
        + (1 - μ) ^ 2 * pair uA vA * pair uB vB := by
  have h : ∀ q : α × β, (adj uA μ vA q.1 * adj uB μ vB q.2) * p q
      = μ ^ 2 * ((vA q.1 * vB q.2) * p q)
        + (μ * (1 - μ) * pair uB vB) * (vA q.1 * p q)
        + (μ * (1 - μ) * pair uA vA) * (vB q.2 * p q)
        + ((1 - μ) ^ 2 * pair uA vA * pair uB vB) * p q := by
    intro q; simp only [adj]; ring
  simp only [h, sum_add_distrib, ← mul_sum, hp]
  ring

/-- With unbiased marginals — which the standard Bell table has — the two cross
terms drop out and `E' = μ² E + (1-μ)² v̄_A v̄_B`. -/
theorem wing_pair_unbiased (uA vA : α → ℝ) (uB vB : β → ℝ) (μ : ℝ) (p : α × β → ℝ)
    (hp : ∑ q, p q = 1)
    (hA : (∑ q : α × β, vA q.1 * p q) = 0) (hB : (∑ q : α × β, vB q.2 * p q) = 0) :
    (∑ q : α × β, (adj uA μ vA q.1 * adj uB μ vB q.2) * p q)
      = μ ^ 2 * (∑ q : α × β, (vA q.1 * vB q.2) * p q)
        + (1 - μ) ^ 2 * pair uA vA * pair uB vB := by
  rw [wing_pair uA vA uB vB μ p hp, hA, hB]; ring

end GeoProbBell
