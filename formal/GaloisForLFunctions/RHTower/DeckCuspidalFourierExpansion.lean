import GaloisForLFunctions.RHTower.DeckCuspidalConstantTerm
import GaloisForLFunctions.RHTower.MaassWhittakerUniqueness
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTail
import GaloisForLFunctions.RHTower.BandLeakageEnvelope

/-!
# Fourier expansion of cuspidal finite-deck eigenfunctions

Each deck coordinate of a cuspidal Laplace eigenfunction `U` is a real-`C²` Maass eigenfunction,
periodic under the level translation.  Its Fourier modes over the level period satisfy the modal
equation `a'' = (κ² - λ/y²) a` (the corpus windowed modal equation with periodic seams), and by
Cauchy–Schwarz and the corpus cusp-tail integrability `∫^∞ |a|²/y² < ∞`.  Hence the constant mode
vanishes (vanishing level horocycle averages) and every nonconstant mode is a multiple of the
Whittaker function `√y K_ν(|κ| y)`, `ν² = 1/4 - λ`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergMaassFourier SelbergMaassMean MaassWhittaker

noncomputable section

variable {N : ℕ}

/-- The `n`-th Fourier mode of the deck coordinate `q` over the level period. -/
def deckMode (U : ℍ → DeckSpace N) (q : Deck N) (n : ℤ) : ℝ → ℂ :=
  coefficient ((N + 1 : ℕ) : ℝ) n (component U q ∘ ofComplex)

namespace IsCuspLaplaceEigen

variable {lam : ℝ} {U : ℍ → DeckSpace N}

theorem isMaassEigenfunction_component (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) :
    IsMaassEigenfunction lam (component U q) := by
  refine ⟨((EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp_contDiffOn
    hU.contDiffOn, fun z => ?_⟩
  have h1 := hypLap_apply hU.contDiffOn z q
  rw [hU.eigen z, PiLp.smul_apply, smul_eq_mul] at h1
  change positiveHyperbolicLaplacian (fun w => U w q) z = (lam : ℂ) * U z q
  push_cast at h1
  linear_combination h1

/-- The eigenfunction as a vector of the form pre-domain. -/
def toPre (hU : IsCuspLaplaceEigen N lam U) : formPreDomain N := ⟨U, hU.mem_cuspidalFormPreDomain.1⟩

theorem component_periodic (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) {y : ℝ} (hy : 0 < y)
    (x : ℝ) : (component U q ∘ ofComplex) (point (x + ((N + 1 : ℕ) : ℝ)) y) =
      (component U q ∘ ofComplex) (point x y) :=
  component_level_periodic hU.toPre q hy x

/-- **The modal equation** `a'' = (κ² - λ/y²) a` for every Fourier mode. -/
theorem deckMode_hasDerivAt (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) (n : ℤ) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (deckMode U q n) (deriv (deckMode U q n) y) y ∧
      HasDerivAt (deriv (deckMode U q n))
        (((signedFrequency ((N + 1 : ℕ) : ℝ) n ^ 2 - lam / y ^ 2 : ℝ) : ℂ) *
          deckMode U q n y) y := by
  have hw : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hC2 : ContDiffOn ℝ 2 (component U q ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (hU.isMaassEigenfunction_component q).1
  have hC1 := hC2.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)
  refine ⟨(coefficient_hasDerivAt _ hw.le n hC1 hy).differentiableAt.hasDerivAt, ?_⟩
  have h2 := (coefficient_second_hasDerivAt _ hw.le n hC2 hy).differentiableAt.hasDerivAt
  refine h2.congr_deriv ?_
  have hmodal := windowedCoefficient_modal_equation (component U q)
    (hU.isMaassEigenfunction_component q) _ hw n hy
  have hp : ∀ x, (component U q ∘ ofComplex) (point (x + ((N + 1 : ℕ) : ℝ)) y) =
      (component U q ∘ ofComplex) (point x y) := fun x => hU.component_periodic q hy x
  have hs1 : (component U q ∘ ofComplex) (point ((N + 1 : ℕ) : ℝ) y) =
      (component U q ∘ ofComplex) (point 0 y) := by simpa using hp 0
  have hs2 : directional 1 (component U q ∘ ofComplex) (point ((N + 1 : ℕ) : ℝ) y) =
      directional 1 (component U q ∘ ofComplex) (point 0 y) := by
    simpa using directional_periodic hC1 hy _ hp 0
  rw [hs1, hs2, sub_self, sub_self, zero_div, mul_zero, zero_div, add_zero, add_zero] at hmodal
  unfold deckMode
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  push_cast at hmodal ⊢
  field_simp
  linear_combination -hmodal

/-- Coefficient bound by the horocycle mass. -/
theorem norm_deckMode_sq_le (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) (n : ℤ) {y : ℝ}
    (hy : 0 < y) :
    ‖deckMode U q n y‖ ^ 2 ≤ ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖U (ofComplex (point x y))‖ ^ 2 := by
  set w : ℝ := ((N + 1 : ℕ) : ℝ) with hwdef
  have hw : 0 < w := by positivity
  have hUc : Continuous U := continuous_of_isChartC1 (formPreDomain.c1 hU.toPre)
  have hG : Continuous (fun x : ℝ => ‖U (ofComplex (point x y))‖) :=
    (hUc.comp (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy)).norm
  have hGq : Continuous (fun x : ℝ => ‖U (ofComplex (point x y)) q‖) :=
    ((PiLp.continuous_apply 2 _ q).comp (hUc.comp
      (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy))).norm
  have h1 : ‖deckMode U q n y‖ ≤ (1 / w) * ∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y)) q‖ := by
    unfold deckMode coefficient _root_.RHTower.deningerFourierCoeff
    rw [norm_mul]
    have hn : ‖(1 / w : ℂ)‖ = 1 / w := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hw.le]
    rw [hn]
    refine mul_le_mul_of_nonneg_left ((intervalIntegral.norm_integral_le_integral_norm hw.le).trans
      (le_of_eq ?_)) (by positivity)
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [norm_mul, _root_.RHTower.deningerFourierKernel_norm, one_mul, Function.comp_apply,
      component]
  have h2 : (∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y)) q‖) ^ 2 ≤
      w * ∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y))‖ ^ 2 := by
    have hcs := GaloisForLFunctions.RHTower.sq_intervalIntegral_le hw hGq
    rw [sub_zero] at hcs
    refine hcs.trans (mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_on hw.le ((hGq.pow 2).intervalIntegrable _ _)
        ((hG.pow 2).intervalIntegrable _ _) fun x _ => ?_) hw.le)
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ q) 2
  have h3 : (∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y))‖ ^ 2) =
      w * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖U (ofComplex (point x y))‖ ^ 2 := by
    have hcoe : ((hU.toPre : formPreDomain N) : ℍ → DeckSpace N) = U := rfl
    have hl := value_normSq_interval_level_period hU.toPre hy 0
    rw [zero_add, zero_add, hcoe] at hl
    change (∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y))‖ ^ 2) = _ at hl
    rw [hl, zsmul_eq_mul]
    have hper : Function.Periodic (fun x : ℝ => ‖U (ofComplex (point x y))‖ ^ 2) 1 := fun x => by
      have := congrArg (fun r : ℝ => r ^ 2) (form_value_norm_one_periodic hU.toPre hy x)
      rw [hcoe] at this
      exact this
    have hshift := hper.intervalIntegral_add_eq 0 (-(1 / 2))
    rw [zero_add, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at hshift
    rw [hshift, hwdef]
    push_cast
    ring
  have hmass : 0 ≤ ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖U (ofComplex (point x y))‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
  have hI0 : 0 ≤ ∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y)) q‖ :=
    intervalIntegral.integral_nonneg hw.le fun x _ => norm_nonneg _
  calc ‖deckMode U q n y‖ ^ 2
      ≤ ((1 / w) * ∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y)) q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (1 / w) ^ 2 * (∫ x in (0 : ℝ)..w, ‖U (ofComplex (point x y)) q‖) ^ 2 := by ring
    _ ≤ (1 / w) ^ 2 * (w * (w * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖U (ofComplex (point x y))‖ ^ 2)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp

/-- **Square-integrability of every Fourier mode near the cusp.** -/
theorem deckMode_small (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) (n : ℤ) :
    IntegrableOn (fun y => ‖deckMode U q n y‖ ^ 2 / y ^ 2) (Ioi 1) := by
  have hprod := cusp_value_weighted_integrable
    (⟨U, hU.mem_cuspidalFormPreDomain⟩ : cuspidalFormPreDomain N) (le_refl (1 : ℝ))
  unfold _root_.RHTower.cuspRect at hprod
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  have hg := hprod.integral_prod_right
  refine hg.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_))
  · have hc : ContinuousOn (deckMode U q n) (Ioi 0) :=
      HasDerivAt.continuousOn fun y hy => (hU.deckMode_hasDerivAt q n hy).1
    have hc' : ContinuousOn (fun y => ‖deckMode U q n y‖ ^ 2 / y ^ 2) (Ioi 1) :=
      ((hc.norm.pow 2).div (continuousOn_id.pow 2) fun y hy =>
        pow_ne_zero 2 (ne_of_gt hy)).mono fun y (hy : 1 < y) => lt_trans one_pos hy
    exact hc'.aestronglyMeasurable measurableSet_Ioi
  · have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    rw [Real.norm_of_nonneg (by positivity)]
    have hb := hU.norm_deckMode_sq_le q n hy0
    have heq : (∫ x in _root_.RHTower.unitIcc,
        ‖(U : ℍ → DeckSpace N) (ofComplex (point (x, y).1 (x, y).2))‖ ^ 2 / (x, y).2 ^ 2) =
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖U (ofComplex (point x y))‖ ^ 2) / y ^ 2 := by
      simp only
      rw [integral_div, intervalIntegral.integral_of_le (by norm_num),
        integral_Icc_eq_integral_Ioc]
    change ‖deckMode U q n y‖ ^ 2 / y ^ 2 ≤ ∫ x in _root_.RHTower.unitIcc,
      ‖(U : ℍ → DeckSpace N) (ofComplex (point (x, y).1 (x, y).2))‖ ^ 2 / (x, y).2 ^ 2
    rw [heq]
    exact div_le_div_of_nonneg_right hb (by positivity)

/-- **The constant mode vanishes.** -/
theorem deckMode_zero (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) {y : ℝ} (hy : 0 < y) :
    deckMode U q 0 y = 0 := by
  have h0 := hU.levelCuspZero q hy 0
  rw [zero_add] at h0
  unfold deckMode coefficient _root_.RHTower.deningerFourierCoeff
  have hk : ∀ x : ℝ, _root_.RHTower.deningerFourierKernel ((N + 1 : ℕ) : ℝ) 0 x = 1 := fun x => by
    simp [_root_.RHTower.deningerFourierKernel]
  simp only [hk, one_mul, Function.comp_apply, component]
  rw [h0, mul_zero]

/-- **Whittaker expansion of the nonconstant modes**: for `n ≠ 0` and `ν² = 1/4 - λ`, the `n`-th
Fourier mode is `ρ √y K_ν(|κ_n| y)` with `κ_n = 2πn/(N+1)`. -/
theorem deckMode_eq_whittaker (hU : IsCuspLaplaceEigen N lam U) (q : Deck N) {n : ℤ} (hn : n ≠ 0)
    {ν : ℂ} (hν : ν ^ 2 = 1 / 4 - lam) :
    ∃ ρ : ℂ, ∀ y, 0 < y → deckMode U q n y =
      ρ * whittakerW |signedFrequency ((N + 1 : ℕ) : ℝ) n| ν y := by
  have hκ : signedFrequency ((N + 1 : ℕ) : ℝ) n ≠ 0 := by
    unfold signedFrequency
    have : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
    have : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    positivity
  refine eq_smul_whittakerW (abs_pos.2 hκ) hν (fun y hy => (hU.deckMode_hasDerivAt q n hy).1)
    (fun y hy => ?_) one_pos (hU.deckMode_small q n)
  rw [sq_abs]
  exact (hU.deckMode_hasDerivAt q n hy).2

end IsCuspLaplaceEigen

end

end GaloisForLFunctions.RHTower.DeckPointPair
