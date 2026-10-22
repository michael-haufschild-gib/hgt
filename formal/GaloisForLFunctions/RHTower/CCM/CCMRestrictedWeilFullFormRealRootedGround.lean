import GaloisForLFunctions.RHTower.CrossRootedPolarZeroXiStripObstruction
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstContactBoundaryRoughness
import GaloisForLFunctions.RHTower.WeilPrimeMeasureRigidityFinite

/-!
# Real-rooted ground states of the unconstrained restricted Weil form

At aperture `a` the restricted Weil form on the full CCM form domain (no pole-vanishing
constraint) is, in frequency (`source_eq_integral_add_pole`),

`Q_a(u) = ∫ S_a(ξ) |f̂_u(ξ)|² dξ + 2 Re (conj f̂_u(w₋) · f̂_u(w₊))`,

where `S_a` is the archimedean symbol minus the prime atoms `n ≤ e^{2a}` and `w_± = ±i/(4π)` are
the polar points, `w₋ = conj w₊`. Let `μ_a` be the bottom of the spectrum of the associated
self-adjoint operator (`ccmRestrictedWeilGroundEnergy`). A ground state is a form-domain vector
with `Q_a(u) = μ_a ‖J u‖²`.

**Theorem** (`exists_realRooted_fullGround`). At every aperture some nonzero ground state has a
Fourier–Laplace transform all of whose zeros are real. If the ground level is one-dimensional,
every nonzero ground state has only real transform zeros (`realRooted_of_finrank_eq_one`). No
parity, isolation or simplicity hypothesis enters the first statement, and no parity hypothesis
enters the second.

**Proof.**
* Division: if `f̂_u(w₀) = 0` with `Im w₀ ≠ 0`, then `f̂_v = f̂_u/(w − w₀)` is a form-domain
  transform (`exists_div`), and `f̂_u = (w − w₀) f̂_v` everywhere.
* Splitting: put `h₁ = u + i Im w₀ · v` and `h₂ = Im w₀ · v`. Then `f̂_{h₁} = (w − Re w₀) f̂_v`,
  and `(w − w̄₀)(w − w₀) = (w − Re w₀)² + (Im w₀)²` gives, for every `w`,
  `conj f̂_u(w̄) f̂_u(w) = conj f̂_{h₁}(w̄) f̂_{h₁}(w) + conj f̂_{h₂}(w̄) f̂_{h₂}(w)`
  (`pair_identity`).
  - On the real line this splits `|f̂_u|²`.
  - At `w = w_±` it splits the pole term.
  - So `Q` and `‖J ·‖²` are additive over `u ↦ (h₁, h₂)`, and minimality makes `v` a ground
    state.
* Finite multiplicity: the ground states form a closed subspace on which the compact embedding
  `J` is antilipschitz.
* Chain: iterated division at non-real zeros would give more linearly independent ground states
  than the dimension.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct

namespace RHTower.CCMFullRealRootedGround

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround

variable (a : SuzukiPositiveAperture)

/-! ## The frequency representation with the pole term -/

/-- The pole term `2 Re (conj f̂_u(w₋) f̂_u(w₊))` of the restricted Weil form. -/
def poleTerm (u : CCMArchimedeanFormDomain a) : ℝ :=
  ((starRingEnd ℂ) (unitaryLaplace (timeRep a u) (polarPoint (-1 / 2))) *
      unitaryLaplace (timeRep a u) (polarPoint (1 / 2)) +
    (starRingEnd ℂ) (unitaryLaplace (timeRep a u) (polarPoint (1 / 2))) *
      unitaryLaplace (timeRep a u) (polarPoint (-1 / 2))).re

theorem sourceWith_eq_integral_add_pole (lam : ℕ → ℝ) (N : ℕ) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadraticWith a lam N u =
      (∫ ξ : ℝ, weilAtomSymbol lam N ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) +
      ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2))
            (ccmArchimedeanFormToAperture a u)) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmArchimedeanFormToAperture a u) +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2))
            (ccmArchimedeanFormToAperture a u)) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmArchimedeanFormToAperture a u)).re := by
  have hterm : ∀ n : ℕ,
      (inner ℂ (logTranslationCLM (Real.log n) (ccmArchimedeanFormToAperture a u).1)
          (ccmArchimedeanFormToAperture a u).1 +
        inner ℂ (logTranslationCLM (-Real.log n) (ccmArchimedeanFormToAperture a u).1)
          (ccmArchimedeanFormToAperture a u).1).re =
        ∫ ξ : ℝ, 2 * Real.cos (2 * Real.pi * Real.log n * ξ) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    intro n
    rw [Complex.add_re, re_inner_logTranslation_eq_integral_cos,
      re_inner_logTranslation_eq_integral_cos,
      ← integral_add (integrable_cos_mul_norm_sq_ccmFormDomain a u _)
        (integrable_cos_mul_norm_sq_ccmFormDomain a u _)]
    congr 1
    funext ξ
    rw [show 2 * Real.pi * -Real.log n * ξ = -(2 * Real.pi * Real.log n * ξ) by ring,
      Real.cos_neg]
    ring
  have hW : Integrable (fun ξ : ℝ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    simpa [archimedeanWeilSymbol] using integrable_two_gammaHardyPhaseRate_mul_norm_sq u.1
  have hC : ∀ n : ℕ, Integrable (fun ξ : ℝ => lam n * (1 / Real.sqrt n) *
      (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) := by
    intro n
    refine ((integrable_cos_mul_norm_sq_ccmFormDomain a u (Real.log n)).const_mul
      (lam n * (1 / Real.sqrt n) * 2)).congr (Eventually.of_forall fun ξ => ?_)
    simp only
    ring
  have hfun : (fun ξ : ℝ => weilAtomSymbol lam N ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      fun ξ => archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 -
        ∑ n ∈ Finset.Icc 2 N, lam n * (1 / Real.sqrt n) *
          (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2 := by
    funext ξ
    simp only [weilAtomSymbol]
    rw [sub_mul, Finset.sum_mul]
  have harch : (∫ ξ : ℝ, archimedeanWeilSymbol ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      ∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(u.1 : ℝ → ℂ) xi‖ ^ 2 := by
    simp [archimedeanWeilSymbol]
  have hint : (∫ ξ : ℝ, weilAtomSymbol lam N ξ * ‖(u.1 : ℝ → ℂ) ξ‖ ^ 2) =
      (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) -
      ∑ n ∈ Finset.Icc 2 N, lam n * (1 / Real.sqrt n) *
        (inner ℂ (logTranslationCLM (Real.log n) (ccmArchimedeanFormToAperture a u).1)
            (ccmArchimedeanFormToAperture a u).1 +
          inner ℂ (logTranslationCLM (-Real.log n) (ccmArchimedeanFormToAperture a u).1)
            (ccmArchimedeanFormToAperture a u).1).re := by
    rw [hfun, integral_sub hW (integrable_finsetSum _ fun n _ => hC n),
      integral_finsetSum _ fun n _ => hC n, harch]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hterm n, ← integral_const_mul]
    congr 1
    funext ξ
    ring
  unfold ccmRestrictedWeilSourceQuadraticWith
  simp only
  rw [hint]
  ring

/-- **The restricted Weil form in frequency, with its pole term.** -/
theorem source_eq_integral_add_pole (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a u =
      (∫ ξ : ℝ, levelSymbol a ξ * ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2) + poleTerm a u := by
  rw [← ccmRestrictedWeilSourceQuadraticWith_eq a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    le_rfl (fun n _ _ => rfl) u, sourceWith_eq_integral_add_pole, inner_polar_eq, inner_polar_eq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [freq_ae a u] with ξ hξ
  rw [hξ]
  rfl

/-! ## The splitting identity -/

/-- The quadratic identity behind the zero flip, valid at every `w`. -/
theorem pair_identity (w w₀ A B : ℂ) :
    (starRingEnd ℂ) ((starRingEnd ℂ w - w₀) * A) * ((w - w₀) * B) =
      (starRingEnd ℂ) ((starRingEnd ℂ w - w₀) * A + I * (w₀.im : ℂ) * A) *
          ((w - w₀) * B + I * (w₀.im : ℂ) * B) +
        (starRingEnd ℂ) ((w₀.im : ℂ) * A) * ((w₀.im : ℂ) * B) := by
  have hc : (starRingEnd ℂ) w₀ = w₀ - 2 * I * (w₀.im : ℂ) := by
    apply Complex.ext <;> simp
    ring
  simp only [map_mul, map_add, map_sub, Complex.conj_conj, Complex.conj_ofReal, Complex.conj_I, hc]
  linear_combination (-((starRingEnd ℂ) A * B * (w₀.im : ℂ) ^ 2)) * I_sq

theorem conj_polarPoint (s : ℝ) : (starRingEnd ℂ) (polarPoint s) = polarPoint (-s) := by
  unfold polarPoint
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-! ## Ground states -/

/-- A ground state of the unconstrained form: Rayleigh value the bottom of the spectrum. -/
def IsFullGround (u : CCMArchimedeanFormDomain a) : Prop :=
  ccmRestrictedWeilSourceQuadratic a u =
    ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2

/-- **Division keeps the ground level.** -/
theorem isFullGround_div {u : CCMArchimedeanFormDomain a} (hu : IsFullGround a u) {w₀ : ℂ}
    (hz : unitaryLaplace (timeRep a u) w₀ = 0) (him : w₀.im ≠ 0)
    {v : CCMArchimedeanFormDomain a}
    (hv : ∀ w : ℂ, w ≠ w₀ →
      unitaryLaplace (timeRep a v) w = unitaryLaplace (timeRep a u) w / (w - w₀)) :
    IsFullGround a v := by
  set μ := ccmRestrictedWeilGroundEnergy a with hμ
  set F : CCMArchimedeanFormDomain a → ℂ → ℂ := fun x w => unitaryLaplace (timeRep a x) w
    with hF
  have hfac : ∀ w, F u w = (w - w₀) * F v w := by
    intro w
    by_cases hw : w = w₀
    · rw [hw, sub_self, zero_mul]
      exact hz
    · show unitaryLaplace (timeRep a u) w = (w - w₀) * unitaryLaplace (timeRep a v) w
      rw [hv w hw]
      field_simp [sub_ne_zero.mpr hw]
  set c : ℂ := I * w₀.im with hc
  set h₁ := u + c • v with hh₁
  set h₂ := (w₀.im : ℂ) • v with hh₂
  have hT₁ : ∀ w, F h₁ w = F u w + c * F v w := unitaryLaplace_timeRep_add_smul a u v c
  have hT₂ : ∀ w, F h₂ w = (w₀.im : ℂ) * F v w := unitaryLaplace_timeRep_smul a v _
  have hpair : ∀ w : ℂ, (starRingEnd ℂ) (F u ((starRingEnd ℂ) w)) * F u w =
      (starRingEnd ℂ) (F h₁ ((starRingEnd ℂ) w)) * F h₁ w +
        (starRingEnd ℂ) (F h₂ ((starRingEnd ℂ) w)) * F h₂ w := by
    intro w
    rw [hT₁, hT₁, hT₂, hT₂, hfac, hfac]
    exact pair_identity w w₀ (F v ((starRingEnd ℂ) w)) (F v w)
  -- the real line
  have hG : ∀ ξ : ℝ, F v ξ = F u ξ / ((ξ : ℂ) - w₀) := fun ξ => hv ξ (ne_of_im_ne_zero ξ him)
  have hsplit : ∀ ξ : ℝ, ‖F u ξ‖ ^ 2 = ‖F h₁ ξ‖ ^ 2 + ‖F h₂ ξ‖ ^ 2 := by
    intro ξ
    rw [hT₁, hT₂, hG]
    exact sq_norm_split _ ξ him
  have hNsum : ‖ccmArchimedeanFormToAperture a u‖ ^ 2 =
      ‖ccmArchimedeanFormToAperture a h₁‖ ^ 2 + ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 := by
    rw [← integral_norm_sq_eq, ← integral_norm_sq_eq, ← integral_norm_sq_eq,
      ← integral_add (integrable_norm_sq_unitaryLaplace a h₁)
        (integrable_norm_sq_unitaryLaplace a h₂)]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  -- the pole term
  have hpole : poleTerm a u = poleTerm a h₁ + poleTerm a h₂ := by
    have hp := hpair (polarPoint (1 / 2))
    have hm := hpair (polarPoint (-1 / 2))
    rw [conj_polarPoint] at hp hm
    have hneg : -(-1 / 2 : ℝ) = 1 / 2 := by norm_num
    have hneg' : -(1 / 2 : ℝ) = -1 / 2 := by norm_num
    rw [hneg'] at hp
    rw [hneg] at hm
    unfold poleTerm
    rw [← Complex.add_re]
    congr 1
    show (starRingEnd ℂ) (F u (polarPoint (-1 / 2))) * F u (polarPoint (1 / 2)) +
        (starRingEnd ℂ) (F u (polarPoint (1 / 2))) * F u (polarPoint (-1 / 2)) =
      (starRingEnd ℂ) (F h₁ (polarPoint (-1 / 2))) * F h₁ (polarPoint (1 / 2)) +
          (starRingEnd ℂ) (F h₁ (polarPoint (1 / 2))) * F h₁ (polarPoint (-1 / 2)) +
        ((starRingEnd ℂ) (F h₂ (polarPoint (-1 / 2))) * F h₂ (polarPoint (1 / 2)) +
          (starRingEnd ℂ) (F h₂ (polarPoint (1 / 2))) * F h₂ (polarPoint (-1 / 2)))
    rw [hp, hm]
    ring
  have hQsum : ccmRestrictedWeilSourceQuadratic a u =
      ccmRestrictedWeilSourceQuadratic a h₁ + ccmRestrictedWeilSourceQuadratic a h₂ := by
    rw [source_eq_integral_add_pole a u, source_eq_integral_add_pole a h₁,
      source_eq_integral_add_pole a h₂, hpole]
    have hI : (∫ ξ : ℝ, levelSymbol a ξ * ‖unitaryLaplace (timeRep a u) ξ‖ ^ 2) =
        (∫ ξ : ℝ, levelSymbol a ξ * ‖unitaryLaplace (timeRep a h₁) ξ‖ ^ 2) +
          ∫ ξ : ℝ, levelSymbol a ξ * ‖unitaryLaplace (timeRep a h₂) ξ‖ ^ 2 := by
      rw [← integral_add (integrable_levelSymbol_mul a h₁) (integrable_levelSymbol_mul a h₂)]
      exact integral_congr_ae (Eventually.of_forall fun ξ => by
        show levelSymbol a ξ * ‖F u ξ‖ ^ 2 =
          levelSymbol a ξ * ‖F h₁ ξ‖ ^ 2 + levelSymbol a ξ * ‖F h₂ ξ‖ ^ 2
        rw [hsplit ξ, mul_add])
    rw [hI]
    ring
  have hl₁ := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a h₁
  have hl₂ := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a h₂
  have heq₂ : ccmRestrictedWeilSourceQuadratic a h₂ =
      μ * ‖ccmArchimedeanFormToAperture a h₂‖ ^ 2 := by
    have hu' : ccmRestrictedWeilSourceQuadratic a u =
        μ * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := hu
    rw [hQsum, hNsum, mul_add] at hu'
    linarith
  have hy2 : (0 : ℝ) < w₀.im ^ 2 := by positivity
  rw [hh₂, ccmRestrictedWeilSourceQuadratic_smul, map_smul, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at heq₂
  have h' : w₀.im ^ 2 * ccmRestrictedWeilSourceQuadratic a v =
      w₀.im ^ 2 * (μ * ‖ccmArchimedeanFormToAperture a v‖ ^ 2) := by
    rw [heq₂]; ring
  exact mul_left_cancel₀ hy2.ne' h'

theorem isFullGround_smul {v : CCMArchimedeanFormDomain a} (hv : IsFullGround a v) (c : ℂ) :
    IsFullGround a (c • v) := by
  unfold IsFullGround at hv ⊢
  rw [ccmRestrictedWeilSourceQuadratic_smul, hv, map_smul, norm_smul]
  ring

theorem isFullGround_add {v w : CCMArchimedeanFormDomain a} (hv : IsFullGround a v)
    (hw : IsFullGround a w) : IsFullGround a (v + w) := by
  have hpar := ccmRestrictedWeilSourceQuadratic_parallelogram a v w
  have hnpar := parallelogram_law_with_norm ℂ (ccmArchimedeanFormToAperture a v)
    (ccmArchimedeanFormToAperture a w)
  rw [← map_add, ← map_sub] at hnpar
  have hs := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a (v + w)
  have hd := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a (v - w)
  have key : ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a (v + w)‖ ^ 2 +
      ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a (v - w)‖ ^ 2 =
      2 * (ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a v‖ ^ 2) +
        2 * (ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a w‖ ^ 2) := by
    linear_combination ccmRestrictedWeilGroundEnergy a * hnpar
  unfold IsFullGround at hv hw ⊢
  linarith

theorem isFullGround_zero : IsFullGround a 0 := by
  unfold IsFullGround
  rw [source_zero, map_zero, norm_zero]
  ring

/-- The ground states of the unconstrained form are a subspace of the form domain. -/
def fullGroundSubmodule : Submodule ℂ (CCMArchimedeanFormDomain a) where
  carrier := {u | IsFullGround a u}
  add_mem' := fun hv hw => isFullGround_add a hv hw
  zero_mem' := isFullGround_zero a
  smul_mem' := fun c _ hv => isFullGround_smul a hv c

theorem isClosed_fullGroundSubmodule :
    IsClosed (fullGroundSubmodule a : Set (CCMArchimedeanFormDomain a)) := by
  set J := ccmArchimedeanFormToAperture a
  have hset : (fullGroundSubmodule a : Set (CCMArchimedeanFormDomain a)) =
      {u | (ccmRestrictedWeilForm a u u).re - ccmRestrictedWeilGroundEnergy a * ‖J u‖ ^ 2 = 0} := by
    ext u
    simp only [SetLike.mem_coe, fullGroundSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, mem_setOf_eq, IsFullGround, ccmRestrictedWeilForm_self_re_eq_source,
      sub_eq_zero, J]
  rw [hset]
  have hJ : Continuous J := J.continuous
  have hform : Continuous fun u : CCMArchimedeanFormDomain a => ccmRestrictedWeilForm a u u := by
    unfold ccmRestrictedWeilForm
    exact (continuous_id.inner continuous_id).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp hJ).inner hJ)
  exact isClosed_eq ((Complex.continuous_re.comp hform).sub (continuous_const.mul (hJ.norm.pow 2)))
    continuous_const

/-- **The ground level has finite multiplicity.** -/
theorem finiteDimensional_fullGroundSubmodule :
    FiniteDimensional ℂ (fullGroundSubmodule a) := by
  haveI : CompleteSpace (fullGroundSubmodule a) :=
    (isClosed_fullGroundSubmodule a).completeSpace_coe
  set J := ccmArchimedeanFormToAperture a with hJdef
  set T : fullGroundSubmodule a →L[ℂ] suzukiApertureHilbert a :=
    J.comp (fullGroundSubmodule a).subtypeL with hTdef
  set C : ℝ := ccmRestrictedWeilGroundEnergy a + ‖ccmRestrictedWeilBoundedRemainder a‖
  have hbound : ∀ x : fullGroundSubmodule a,
      ‖x‖ ≤ ((Real.sqrt (max C 0)).toNNReal : ℝ) * ‖T x‖ := by
    intro x
    have hx : IsFullGround a (x : CCMArchimedeanFormDomain a) := x.2
    have h1 := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a x
    rw [hx] at h1
    have h2 : ‖x‖ ^ 2 ≤ max C 0 * ‖T x‖ ^ 2 := by
      have hTx : T x = J x := rfl
      have hnx : ‖x‖ = ‖(x : CCMArchimedeanFormDomain a).1‖ := rfl
      rw [hTx, hnx]
      calc ‖(x : CCMArchimedeanFormDomain a).1‖ ^ 2 ≤ C * ‖J x‖ ^ 2 := by
            simp only [C]; linarith
        _ ≤ max C 0 * ‖J x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    have h3 : ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h3, ← Real.sqrt_sq (norm_nonneg (T x)), ← Real.sqrt_mul (le_max_right _ _)]
    exact Real.sqrt_le_sqrt h2
  have hanti := T.antilipschitz_of_bound hbound
  have hemb := hanti.isClosedEmbedding T.uniformContinuous
  have hK := (isCompactOperator_ccmArchimedeanFormToAperture a).isCompact_closure_image_closedBall 1
  have hpre := hemb.isCompact_preimage hK
  refine FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos
    (hpre.of_isClosed_subset Metric.isClosed_closedBall ?_)
  intro x hx
  show T x ∈ closure (J '' Metric.closedBall 0 1)
  refine subset_closure ⟨(x : CCMArchimedeanFormDomain a), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  exact hx

/-- The transform on the real line, as a linear map on the ground subspace. -/
def fullRealTransform : fullGroundSubmodule a →ₗ[ℂ] (ℝ → ℂ) where
  toFun u := fun t : ℝ => unitaryLaplace (timeRep a (u : CCMArchimedeanFormDomain a)) t
  map_add' u v := by
    funext t
    have h := unitaryLaplace_timeRep_add_smul a u v 1 t
    rw [one_smul, one_mul] at h
    simpa only [Submodule.coe_add, Pi.add_apply] using h
  map_smul' c u := by
    funext t
    simpa only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul] using
      unitaryLaplace_timeRep_smul a u c t

/-- **Real-rooted ground states of the unconstrained restricted Weil form exist at every
aperture.** -/
theorem exists_realRooted_fullGround :
    ∃ u : CCMArchimedeanFormDomain a, IsFullGround a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      ∀ w : ℂ, unitaryLaplace (timeRep a u) w = 0 → w.im = 0 := by
  classical
  obtain ⟨u₀, hne₀, hQ₀⟩ := ccmRestrictedWeilSource_exists_groundFormState a
  have hg₀ : IsFullGround a u₀ := hQ₀
  by_contra hcon
  push Not at hcon
  let S := {u : CCMArchimedeanFormDomain a //
    IsFullGround a u ∧ ccmArchimedeanFormToAperture a u ≠ 0}
  have hstep : ∀ s : S, ∃ w : ℂ, ∃ v : S, unitaryLaplace (timeRep a s.1) w = 0 ∧ w.im ≠ 0 ∧
      ∀ t : ℝ, unitaryLaplace (timeRep a v.1) t =
        unitaryLaplace (timeRep a s.1) t / ((t : ℂ) - w) := by
    intro s
    obtain ⟨w, hw, him⟩ := hcon s.1 s.2.1 s.2.2
    obtain ⟨v, hv⟩ := exists_div a s.1 hw
    have hgv : IsFullGround a v := isFullGround_div a s.2.1 hw him hv
    have hnv : ccmArchimedeanFormToAperture a v ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := exists_real_ne_zero a s.2.2
      have hv0 : v = 0 := ccmArchimedeanFormToAperture_injective a (by rw [h0, map_zero])
      have h1 := hv t (ne_of_im_ne_zero t him)
      rw [hv0, unitaryLaplace_timeRep_zero, eq_comm, div_eq_zero_iff] at h1
      exact ht (h1.resolve_right (sub_ne_zero.mpr (ne_of_im_ne_zero t him)))
    exact ⟨w, ⟨v, hgv, hnv⟩, hw, him, fun t => hv t (ne_of_im_ne_zero t him)⟩
  choose zf nx _ himf hnx using hstep
  let chain : ℕ → S := fun k => nx^[k] ⟨u₀, hg₀, hne₀⟩
  let zs : ℕ → ℂ := fun k => zf (chain k)
  have hsucc : ∀ k, chain (k + 1) = nx (chain k) := fun k =>
    Function.iterate_succ_apply' nx k _
  have hform : ∀ (k : ℕ) (t : ℝ), unitaryLaplace (timeRep a (chain k).1) t =
      unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range k, ((t : ℂ) - zs l) := by
    intro k t
    induction k with
    | zero => simp [chain]
    | succ k ih => rw [hsucc, hnx, ih, Finset.prod_range_succ, div_div]
  haveI := finiteDimensional_fullGroundSubmodule a
  set d := Module.finrank ℂ (fullGroundSubmodule a)
  let g : Fin (d + 1) → fullGroundSubmodule a := fun i => ⟨(chain i).1, (chain i).2.1⟩
  have hli : LinearIndependent ℂ g := by
    apply LinearIndependent.of_comp (fullRealTransform a)
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let c' : ℕ → ℂ := fun j => if h : j < d + 1 then c ⟨j, h⟩ else 0
    have hreal : ∀ j < d, ∀ t : ℝ, (t : ℂ) - zs j ≠ 0 :=
      fun j _ t => sub_ne_zero.mpr (ne_of_im_ne_zero t (himf (chain j)))
    have hsum : ∀ t : ℝ, ∑ j ∈ Finset.range (d + 1), c' j *
        (unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range j, ((t : ℂ) - zs l)) = 0 := by
      intro t
      have h0 := congrFun hc t
      simp only [Finset.sum_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at h0
      rw [← h0, ← Fin.sum_univ_eq_sum_range (fun j => c' j *
        (unitaryLaplace (timeRep a u₀) t / ∏ l ∈ Finset.range j, ((t : ℂ) - zs l)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c', dif_pos j.isLt, Fin.eta]
      rw [← hform j t]
      rfl
    have := eq_zero_of_sum_div_prod (infinite_real_ne_zero a hne₀) zs d hreal c' hsum i
      (Nat.lt_succ_iff.mp i.isLt)
    simp only [c', dif_pos i.isLt, Fin.eta] at this
    exact this
  have hcard := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-- **A simple ground state is real-rooted, of either parity.** If the ground level of the
unconstrained form is one-dimensional, every nonzero ground state has only real transform
zeros. -/
theorem realRooted_of_finrank_eq_one (h1 : Module.finrank ℂ (fullGroundSubmodule a) = 1)
    {u : CCMArchimedeanFormDomain a} (hu : IsFullGround a u)
    (hne : ccmArchimedeanFormToAperture a u ≠ 0) :
    ∀ w : ℂ, unitaryLaplace (timeRep a u) w = 0 → w.im = 0 := by
  obtain ⟨u₀, hg₀, hne₀, hreal⟩ := exists_realRooted_fullGround a
  have hu₀ne : (⟨u₀, hg₀⟩ : fullGroundSubmodule a) ≠ 0 := by
    intro h
    apply hne₀
    have : u₀ = 0 := congrArg Subtype.val h
    rw [this, map_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u₀, hg₀⟩ : fullGroundSubmodule a)
    hu₀ne).mp h1 ⟨u, hu⟩
  have hcu : u = c • u₀ := (congrArg Subtype.val hc).symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    rw [hcu, zero_smul, map_zero]
  intro w hw
  rw [hcu, unitaryLaplace_timeRep_smul] at hw
  exact hreal w ((mul_eq_zero.mp hw).resolve_left hc0)

/-- **Receiver for Connes's ground states.** If real-rooted ground states of the unconstrained
restricted Weil forms (which exist at every aperture, `exists_realRooted_fullGround`) have
normalized transforms converging to `XiC` locally uniformly on the strip `|Im z| < 1/2`, then RH
holds. -/
theorem riemannHypothesis_of_fullGround_strip_convergence
    (a : ℕ → SuzukiPositiveAperture) (u : ∀ n, CCMArchimedeanFormDomain (a n)) (c : ℕ → ℂ)
    (hground : ∀ n, IsFullGround (a n) (u n) ∧
      ∀ w : ℂ, unitaryLaplace (timeRep (a n) (u n)) w = 0 → w.im = 0)
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => c n * unitaryLaplace (timeRep (a n) (u n)) (z / (2 * Real.pi))) XiC atTop
      RHTower.CCMXiStrip.centeredStrip) :
    RiemannHypothesis :=
  RHTower.CCMXiStrip.riemannHypothesis_of_crossRooted_strip_convergence a u c
    (fun n w hw _ _ => Or.inr ((hground n).2 w hw)) hconv

/-- **Weil's criterion needs only real-rooted test vectors.** RH holds exactly when, at every
aperture, the restricted Weil form is nonnegative on the form-domain vectors whose Fourier–Laplace
transforms have only real zeros. -/
theorem riemannHypothesis_iff_nonneg_on_realRooted :
    RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a),
      (∀ w : ℂ, unitaryLaplace (timeRep a u) w = 0 → w.im = 0) →
        0 ≤ ccmRestrictedWeilSourceQuadratic a u := by
  constructor
  · intro hRH a u _
    have h0 := RHTower.WeilDeletion.ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis hRH a
    have hl := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u
    have hn : 0 ≤ ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by positivity
    nlinarith
  · intro hpos
    by_contra hnot
    obtain ⟨a, hneg⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hnot
    obtain ⟨u, hu, hne, hreal⟩ := exists_realRooted_fullGround a
    have hq := hpos a u hreal
    have hn : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    have hu' : ccmRestrictedWeilSourceQuadratic a u =
        ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := hu
    nlinarith

end RHTower.CCMFullRealRootedGround
