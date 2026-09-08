/-
# Geometrical Probability of Bell's Theorem — formal companion

Lean 4 + Mathlib development of every algebraic claim made in the post
"Geometrical Probability of Bell's Theorem".

Import this module to get the whole development.

  GeoProbBell.Mixer          §1, §6  the dial, the group law, stochasticity
  GeoProbBell.Master         §6      the master formula, the contraction lemma
  GeoProbBell.SleepingBeauty §1      P_H(μ), its endpoints, S_SB(μ) = μ
  GeoProbBell.Product        §3, §9  the product chart, the wing-wise dial
  GeoProbBell.CHSH           §5, §6  S under a chart change, the local bound
  GeoProbBell.Thresholds     §7–§9   the walls

Nothing quantum-mechanical is assumed anywhere.  Tsirelson's 2√2 enters only as
a hypothesis of `GeoProbBell.chsh_bound`.
-/
import GeoProbBell.Mixer
import GeoProbBell.Master
import GeoProbBell.SleepingBeauty
import GeoProbBell.Product
import GeoProbBell.CHSH
import GeoProbBell.Thresholds
