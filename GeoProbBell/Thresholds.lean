/-
# The walls

§7, §8 and §9 of the post.  Each threshold is stated as an `iff`, in a
division-free form, so that the statement is checkable by eye against the
inequality it comes from.

Joint dial:
  `q = 0`      wall at `√2/2 = 1/√2 ≈ 0.7071`   (depolarising visibility)
  general `q`  some observer violates iff `μ(√2 - q) > 1 - q`
               every observer violates iff `μ(√2 + q) > 1 + q`
  `q → 1`      window becomes `(0, 2(√2-1)]`    (detection efficiency)

Wing-wise dial:
  `q = 0`      wall at `μ² > √2/2`, i.e. `μ > 2^(-1/4) ≈ 0.8409`
  `q = 1`      wall at `μ > 2(√2-1) ≈ 0.8284`
-/
import GeoProbBell.CHSH

namespace GeoProbBell

theorem sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  nlinarith [sqrt2_sq, Real.sqrt_nonneg (2 : ℝ)]

/-- **§7. Joint dial, unvalued padding.**  `2√2 μ > 2` exactly at the
depolarising visibility threshold `1/√2 = √2/2`. -/
theorem wall_unvalued (μ : ℝ) :
    2 < 2 * Real.sqrt 2 * μ ↔ Real.sqrt 2 / 2 < μ := by
  constructor <;> intro h <;> nlinarith [sqrt2_sq, sqrt2_gt_one, h]

/-- **§8. Some observer sees a violation.**  The wall is `μ₋ = (1-q)/(√2-q)`,
written here without division. -/
theorem wall_some (μ q : ℝ) :
    2 < 2 * Real.sqrt 2 * μ + 2 * (1 - μ) * q ↔ 1 - q < μ * (Real.sqrt 2 - q) := by
  constructor <;> intro h <;> nlinarith [h]

/-- **§8. Every observer sees a violation.**  The wall is `μ₊ = (1+q)/(√2+q)`. -/
theorem wall_every (μ q : ℝ) :
    2 < 2 * Real.sqrt 2 * μ - 2 * (1 - μ) * q ↔ 1 + q < μ * (Real.sqrt 2 + q) := by
  constructor <;> intro h <;> nlinarith [h]

/-- The upper end of the disagreement window as `q → 1` is `2(√2-1)`, the CHSH
detection-efficiency threshold. -/
theorem wall_every_one (μ : ℝ) :
    1 + 1 < μ * (Real.sqrt 2 + 1) ↔ 2 * (Real.sqrt 2 - 1) < μ := by
  constructor <;> intro h <;> nlinarith [sqrt2_sq, sqrt2_gt_one, h]

/-- The lower end of the disagreement window as `q → 1` is `0`. -/
theorem wall_some_one (μ : ℝ) : 1 - 1 < μ * (Real.sqrt 2 - 1) ↔ 0 < μ := by
  constructor <;> intro h <;> nlinarith [sqrt2_gt_one, h]

/-- **§9. Wing-wise dial.**  The violation condition is a quadratic in `μ`,
whose relevant root is `μ⋆(c)` in the post. -/
theorem wall_wing (μ q : ℝ) :
    2 < 2 * Real.sqrt 2 * μ ^ 2 + 2 * (1 - μ) ^ 2 * q
      ↔ 0 < (Real.sqrt 2 + q) * μ ^ 2 - 2 * q * μ + (q - 1) := by
  constructor <;> intro h <;> nlinarith [h]

/-- **§9. Wing-wise dial, unvalued padding**: the wall sits at `μ² = √2/2`,
i.e. `μ = 2^(-1/4) ≈ 0.8409`. -/
theorem wall_wing_unvalued (μ : ℝ) :
    2 < 2 * Real.sqrt 2 * μ ^ 2 ↔ Real.sqrt 2 / 2 < μ ^ 2 := by
  constructor <;> intro h <;> nlinarith [sqrt2_sq, sqrt2_gt_one, h]

theorem wall_wing_one_factor (μ : ℝ) :
    2 * Real.sqrt 2 * μ ^ 2 + 2 * (1 - μ) ^ 2 - 2
      = 2 * μ * ((Real.sqrt 2 + 1) * μ - 2) := by
  ring

/-- **§9. Wing-wise dial, fully valued padding**: the wall is the CHSH
detection-efficiency threshold `2(√2-1) ≈ 0.8284`, exactly the Garg–Mermin
number. -/
theorem wall_wing_valued (μ : ℝ) (hμ : 0 < μ) :
    2 < 2 * Real.sqrt 2 * μ ^ 2 + 2 * (1 - μ) ^ 2 ↔ 2 * (Real.sqrt 2 - 1) < μ := by
  have hfac := wall_wing_one_factor μ
  have hr := sqrt2_sq
  have h1 := sqrt2_gt_one
  constructor
  · intro h
    have hpos : 0 < (Real.sqrt 2 + 1) * μ - 2 := by nlinarith
    nlinarith
  · intro h
    have hpos : 0 < (Real.sqrt 2 + 1) * μ - 2 := by nlinarith
    nlinarith

end GeoProbBell
