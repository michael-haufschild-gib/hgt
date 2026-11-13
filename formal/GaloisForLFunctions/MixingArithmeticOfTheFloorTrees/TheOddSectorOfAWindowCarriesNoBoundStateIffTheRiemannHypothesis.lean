import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheFunctionalEquationReflectsEveryWindowAtInfiniteBlockSize
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero
import GaloisForLFunctions.RHTower.WeilParityPoleWeightWindows

/-!
# The odd sector of a window carries no bound state iff the Riemann hypothesis

At infinite block size the window form is invariant under the reflection `u ↦ c − u` about the
centre of the window (`neutralForm_reflect`), so it splits into an even and an odd sector. On a
packet odd about the centre, `g(c − u) = −g(u)`, the two charges are opposite up to the factor
`e^{c/2}` (`integral_mul_exp_of_odd`), and the pole term `−2AB` becomes a square of the right
sign (`neutralForm_of_odd`):

  `N(g) = W(g) + 2 e^{c/2} A(g)²`.

So on the odd sector the neutral form dominates Weil's form, and under RH it is nonnegative
(`neutralForm_nonneg_of_odd_of_riemannHypothesis`). Conversely, without RH there is an odd smooth
packet of vanishing first charge with negative Weil form (RHTower,
`exists_odd_poleFree_negative_of_not_riemannHypothesis`), on which the neutral form is Weil's form.
Hence (`riemannHypothesis_iff_forall_odd_neutralForm_nonneg`)

  **RH iff the odd sector of every window carries no bound state.**

The binding energy lives in the even sector, where the pole term `−2 e^{c/2} A²` is a negative
square of rank one: under RH the even sector holds exactly the one bound state, and the second
bound state that RH excludes is an odd one. In the pole-weight language of RHTower this is the
odd window `β ≤ 1` at `β = 0`.
-/

open MeasureTheory Complex
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open Zeta23

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- **On a packet odd about `c/2` the second charge is `−e^{c/2}` times the first.** -/
theorem integral_mul_exp_of_odd {g : ℝ → ℝ} {c : ℝ} (hodd : ∀ u, g (c - u) = -g u) :
    ∫ u, g u * Real.exp (u / 2) = -(Real.exp (c / 2) * ∫ u, g u * Real.exp (-u / 2)) := by
  have hr : reflectPacket c g = fun u => -g u := funext fun u => hodd u
  have h : ∫ u, -g u * Real.exp (u / 2) = Real.exp (c / 2) * ∫ v, g v * Real.exp (-v / 2) := by
    have := integral_reflect_mul_exp c g
    rwa [hr] at this
  have hneg : ∫ u, -g u * Real.exp (u / 2) = -∫ u, g u * Real.exp (u / 2) := by
    rw [← integral_neg]
    congr 1
    funext u
    ring
  rw [hneg] at h
  linarith

/-- **On the odd sector the pole term is a square of the right sign**:
`N(g) = W(g) + 2 e^{c/2} A(g)²`. -/
theorem neutralForm_of_odd (Q : ℕ) {g : ℝ → ℝ} {c : ℝ} (hodd : ∀ u, g (c - u) = -g u) :
    neutralForm Q g = packetForm Q g +
      2 * Real.exp (c / 2) * (∫ u, g u * Real.exp (-u / 2)) ^ 2 := by
  rw [neutralForm, integral_mul_exp_of_odd hodd]
  ring

/-- **Under RH the odd sector carries no bound state**: the neutral form is nonnegative on every
smooth packet odd about the centre of its window. -/
theorem neutralForm_nonneg_of_odd_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) {c : ℝ}
    (hodd : ∀ u, f (c - u) = -f u) : 0 ≤ neutralForm Q f := by
  have hW : 0 ≤ packetForm Q f := by
    rw [← zeroSum_eq_packetForm hf hfc hQ]
    exact re_zetaW_nonneg_of_riemannHypothesis hRH _
  rw [neutralForm_of_odd Q hodd]
  have : 0 ≤ 2 * Real.exp (c / 2) * (∫ u, f u * Real.exp (-u / 2)) ^ 2 := by positivity
  linarith

/-- **RH iff the odd sector of every window carries no bound state**: the neutral form is
nonnegative on every smooth compactly supported odd packet, for every contact range `Q` that
covers its support. -/
theorem riemannHypothesis_iff_forall_odd_neutralForm_nonneg :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ u, f (-u) = -f u) → ∀ Q : ℕ, (∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) →
        0 ≤ neutralForm Q f := by
  constructor
  · intro hRH f hf hfc hodd Q hQ
    exact neutralForm_nonneg_of_odd_of_riemannHypothesis hRH hf hfc hQ (c := 0)
      fun u => by rw [zero_sub]; exact hodd u
  · intro h
    by_contra hRH
    obtain ⟨f, hf, hfc, hodd, hp, hneg⟩ :=
      _root_.RHTower.exists_odd_poleFree_negative_of_not_riemannHypothesis hRH
    -- a contact range covering the support
    obtain ⟨a, ha⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℝ)
    have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
      have h1 : u ∈ tsupport f := subset_tsupport f hu
      have h2 := ha h1
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
    obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.exp (2 * a))
    have hQ' : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0 := by
      intro n hn
      have hn' : Real.exp (2 * a) < n := hQ.trans (by exact_mod_cast hn)
      have hlog : 2 * a < Real.log n :=
        (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < n by omega))).mpr hn'
      have hz : ∀ u, f u * f (u + Real.log n) = 0 := fun u => by
        by_cases hu : f u = 0
        · rw [hu, zero_mul]
        · obtain ⟨h1l, h1r⟩ := abs_le.mp (hsupp u hu)
          have h2 : f (u + Real.log n) = 0 := by
            by_contra h3
            obtain ⟨h3l, h3r⟩ := abs_le.mp (hsupp _ h3)
            linarith
          rw [h2, mul_zero]
      simp only [packetAutocorr, hz, integral_zero]
    have hN := h f hf hfc hodd Q hQ'
    -- the first charge is the transform at `i/2`, which vanishes
    have hA : ∫ u, f u * Real.exp (-u / 2) = 0 := by
      rw [_root_.RHTower.WeilLevyPole.paperFT_ofReal_I_div_two] at hp
      exact_mod_cast hp
    rw [neutralForm_eq_re_sub hf hfc hQ', Complex.sub_re, poleConfig_W_ofReal,
      Complex.ofReal_re, hA, zero_mul, mul_zero, sub_zero] at hN
    linarith

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
