import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AngularFourierRegularity
import GaloisForLFunctions.FamilyContinuationTheory.AngularPlainIdealSums

/-! # Primitive reflection with sextic infinity type

Angular Poisson reflection reverses infinity type. Primitive finite Fourier
inversion contributes a normalized Gauss factor, and rotation by the modulus
contributes an explicit unit phase.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
open SchwartzPlanePoisson HeckeFamily HeckeRowClosure HeckePrimitive
local notation "O" => Eisenstein.O

/-- Primitive angular lattice reflection, including its modulus phase. -/
theorem primitive_angular_lattice_reflection (n : ℕ) (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (W : 𝓢(ℝ, ℂ)) (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (X : ℝ) (hX : 0 < X) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      angularRadial n (fun t => W (t / X)) (ringComplex z)) =
      ((X : ℂ) * TraceCharacter.normalizedGauss c χ / (‖ringComplex c‖ : ℂ)) *
        (ringComplex c / (‖ringComplex c‖ : ℂ)) ^ n *
          ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
            ((conj (ringComplex h) / (‖ringComplex h‖ : ℂ)) ^ n *
              paperAngularFourier n W (X * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)) := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have h := actual_angular_poisson_trace n W hW X hX c (NeZero.ne c) χ
  change _ = (X / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ r : O ⧸ Ideal.span {c}, χ r *
      TraceCharacter.traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
      ((ringComplex c / (‖ringComplex c‖ : ℂ)) ^ n *
        (conj (ringComplex h) / (‖ringComplex h‖ : ℂ)) ^ n *
        paperAngularFourier n W (X * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)) at h
  simp_rw [TraceCharacter.transform_eq c χ hp] at h
  rw [h]
  simp only [Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [TraceCharacter.normalizedGauss]
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  ring

/-- The opposite infinity type, paired with an arbitrary finite character. -/
def oppositeGrossenPlainIdealSum (χ : Character) (k : ℕ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NonzeroIdeal, idealCoeff χ I.val * conj (idealPsiSix I.val) ^ k *
    W ((Ideal.absNorm I.val : ℝ) / X)

private theorem phase_radial_summable (χ : Character) (k : ℕ) (V : ℝ → ℂ)
    (X : ℝ) (hs : Summable (fun z : O => ‖V (‖ringComplex z‖ ^ 2 / X)‖)) :
    Summable (fun z : O => elementCoeff χ z * elemPsiSix z ^ k *
      V (‖ringComplex z‖ ^ 2 / X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro z
  rw [norm_mul, norm_mul, norm_pow]
  have he : ‖elementCoeff χ z‖ ≤ 1 := elementHom_norm χ z
  have ha := pow_le_one₀ (norm_nonneg (elemPsiSix z)) (norm_elemPsiSix_le_one z) (n := k)
  exact mul_le_of_le_one_left (norm_nonneg _)
    (by simpa only [one_mul] using mul_le_mul he ha (pow_nonneg (norm_nonneg _) _) zero_le_one)

private theorem phase_lattice_reindex (χ : Character) (k : ℕ) (V : ℝ → ℂ)
    (X : ℝ) (hs : Summable (fun z : O => ‖V (‖ringComplex z‖ ^ 2 / X)‖)) :
    (∑' z : O, elementCoeff χ z * elemPsiSix z ^ (k + 1) *
      V (‖ringComplex z‖ ^ 2 / X)) = 6 * grossenPlainIdealSum χ (k + 1) V X := by
  let f : O → ℂ := fun z => elementCoeff χ z * elemPsiSix z ^ (k + 1) *
    V (‖ringComplex z‖ ^ 2 / X)
  have h0 : f 0 = 0 := by
    simp only [f, map_zero, zero_pow (Nat.succ_ne_zero k), mul_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f ((u : O) * z) = f z := by
    simp only [f, elementCoeff_unit_mul, map_mul, elemPsiSix_unit, one_mul,
      norm_mul, norm_ringComplex_unit]
  have heq := tsum_unit_invariant_ideals f (phase_radial_summable χ (k + 1) V X hs) h0 hu
  have hterm (I : NonzeroIdeal) : f (cubicIdealGenerator I.val) =
      idealCoeff χ I.val * idealPsiSix I.val ^ (k + 1) *
        V ((Ideal.absNorm I.val : ℝ) / X) := by
    dsimp only [f]
    rw [← idealCoeff_span χ (cubicIdealGenerator_ne_zero I.val I.property),
      ← idealPsiSix_span_singleton, ringComplex_norm_sq_eq_absNorm_span, span_cubicIdealGenerator]
  simp_rw [hterm] at heq
  have hcard : Nat.card Oˣ = 6 := card_units_thirdCyclotomic K
  simpa only [hcard, Nat.cast_ofNat, grossenPlainIdealSum] using heq

private theorem elementCoeff_inverse_conj' (χ : Character) (z : O) :
    elementCoeff χ.inverse z = conj (elementCoeff χ z) := by
  letI : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact (MulChar.star_apply' χ.residue _).symm

private theorem opposite_phase_lattice_reindex (χ : Character) (k : ℕ) (V : ℝ → ℂ)
    (X : ℝ) (hs : Summable (fun z : O => ‖V (‖ringComplex z‖ ^ 2 / X)‖)) :
    (∑' z : O, elementCoeff χ z * conj (elemPsiSix z) ^ (k + 1) *
      V (‖ringComplex z‖ ^ 2 / X)) = 6 * oppositeGrossenPlainIdealSum χ (k + 1) V X := by
  have hs' : Summable (fun z : O => ‖conj (V (‖ringComplex z‖ ^ 2 / X))‖) := by
    simpa only [Complex.norm_conj] using hs
  have h := congrArg (starRingEnd ℂ) (phase_lattice_reindex χ.inverse k (fun x => conj (V x)) X hs')
  have hsix : conj (6 : ℂ) = 6 := Complex.conj_ofReal 6
  simpa only [grossenPlainIdealSum, oppositeGrossenPlainIdealSum, Complex.conj_tsum,
    map_mul, map_pow, hsix, elementCoeff_inverse_conj', idealCoeff_inverse_conj,
    Complex.conj_conj] using h

private theorem angular_fourier_lattice_summable (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => ‖paperAngularFourier n W (‖ringComplex z‖ ^ 2 / Y)‖) := by
  obtain ⟨S, C, hC, hb⟩ := paperAngularFourier_finite_seminorm_bound n 2
  have hs := (scaled_eisenstein_cauchy_summable (1 / Y) (by positivity)).mul_left
    (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro z
  have h := hb W hW (‖ringComplex z‖ ^ 2 / Y) (div_nonneg (sq_nonneg _) hY.le)
  have hd : 0 < (1 + ‖ringComplex z‖ ^ 2 / Y) ^ 2 := by positivity
  have hh : ‖paperAngularFourier n W (‖ringComplex z‖ ^ 2 / Y)‖ ≤
      (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
        (1 + ‖ringComplex z‖ ^ 2 / Y) ^ 2 :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using h)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh

/-- Exact ideal reflection reverses positive infinity type without a finite-principal exception. -/
theorem primitive_angular_ideal_reflection (k : ℕ) (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (W : 𝓢(ℝ, ℂ)) (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (X : ℝ) (hX : 0 < X) :
    oppositeGrossenPlainIdealSum (character c χ hu) (k + 1) W X =
      ((X : ℂ) * TraceCharacter.normalizedGauss c χ / (‖ringComplex c‖ : ℂ)) *
        conj (elemPsiSix c) ^ (k + 1) *
          grossenPlainIdealSum (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (k + 1)
            (paperAngularFourier (6 * (k + 1)) W) (‖ringComplex c‖ ^ 2 / X) := by
  have hc : 0 < ‖ringComplex c‖ := norm_pos_iff.mpr (CubicEisenstein.ringComplex_ne_zero (NeZero.ne c))
  have hY : 0 < ‖ringComplex c‖ ^ 2 / X := div_pos (sq_pos_of_pos hc) hX
  have hs : Summable (fun z : O => ‖W (‖ringComplex z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd := angular_fourier_lattice_summable (6 * (k + 1)) W hW _ hY
  have h := primitive_angular_lattice_reflection (6 * (k + 1)) c χ hp W hW X hX
  have hphase (z : O) : (ringComplex z / (‖ringComplex z‖ : ℂ)) ^ (6 * (k + 1)) =
      conj (elemPsiSix z) ^ (k + 1) := by
    simp only [elemPsiSix_apply, complexUnitConj_apply, map_pow, map_div₀,
      Complex.conj_conj, Complex.conj_ofReal, pow_mul]
  have hdual (z : O) : (conj (ringComplex z) / (‖ringComplex z‖ : ℂ)) ^ (6 * (k + 1)) =
      elemPsiSix z ^ (k + 1) := by
    rw [elemPsiSix_apply, complexUnitConj_apply, pow_mul]
  have harg (z : O) : X * ‖ringComplex z‖ ^ 2 / ‖ringComplex c‖ ^ 2 =
      ‖ringComplex z‖ ^ 2 / (‖ringComplex c‖ ^ 2 / X) := by
    rw [div_div_eq_mul_div]; ring
  simp only [angularRadial, hphase, hdual, harg, ← mul_assoc] at h
  change (∑' z : O, elementCoeff (character c χ hu) z * conj (elemPsiSix z) ^ (k + 1) *
      W (‖ringComplex z‖ ^ 2 / X)) =
      _ * (∑' z : O, elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z *
        elemPsiSix z ^ (k + 1) *
        paperAngularFourier (6 * (k + 1)) W (‖ringComplex z‖ ^ 2 / (‖ringComplex c‖ ^ 2 / X))) at h
  rw [opposite_phase_lattice_reindex _ k W X hs, phase_lattice_reindex _ k _ _ hd] at h
  linear_combination h / 6

/-- Square-root normalization leaves only the Gauss factor and modulus phase. -/
theorem primitive_angular_normalized_reflection (k : ℕ) (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (W : 𝓢(ℝ, ℂ)) (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ * oppositeGrossenPlainIdealSum (character c χ hu) (k + 1) W X =
      TraceCharacter.normalizedGauss c χ * conj (elemPsiSix c) ^ (k + 1) *
        ((Real.sqrt (‖ringComplex c‖ ^ 2 / X) : ℂ)⁻¹ *
          grossenPlainIdealSum (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (k + 1)
            (paperAngularFourier (6 * (k + 1)) W) (‖ringComplex c‖ ^ 2 / X)) := by
  rw [primitive_angular_ideal_reflection k c χ hu hp W hW X hX]
  have hc : 0 < ‖ringComplex c‖ := norm_pos_iff.mpr (CubicEisenstein.ringComplex_ne_zero (NeZero.ne c))
  have hs : Real.sqrt (‖ringComplex c‖ ^ 2 / X) = ‖ringComplex c‖ / Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hc.le]
  have hx : (Real.sqrt X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (‖ringComplex c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X : ℂ) ^ 2 = (X : ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs, Complex.ofReal_div]
  field_simp
  rw [hsq]

/-- Primitive reflection preserves the absolute normalized plain sum exactly. -/
theorem primitive_angular_normalized_norm (k : ℕ) (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (W : 𝓢(ℝ, ℂ)) (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (X : ℝ) (hX : 0 < X) :
    ‖(Real.sqrt X : ℂ)⁻¹ * oppositeGrossenPlainIdealSum (character c χ hu) (k + 1) W X‖ =
      ‖(Real.sqrt (‖ringComplex c‖ ^ 2 / X) : ℂ)⁻¹ *
        grossenPlainIdealSum (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (k + 1)
          (paperAngularFourier (6 * (k + 1)) W) (‖ringComplex c‖ ^ 2 / X)‖ := by
  rw [primitive_angular_normalized_reflection k c χ hu hp W hW X hX,
    norm_mul, norm_mul, TraceCharacter.normalizedGauss_norm c χ hp, norm_pow,
    Complex.norm_conj, norm_elemPsiSix_of_ne_zero (NeZero.ne c), one_pow, one_mul, one_mul]

/-- Complex conjugation reverses infinity type and the finite character. -/
theorem grossenPlainIdealSum_conj (χ : Character) (k : ℕ) (W : ℝ → ℂ) (X : ℝ) :
    conj (grossenPlainIdealSum χ k W X) =
      oppositeGrossenPlainIdealSum χ.inverse k (fun x => conj (W x)) X := by
  simp only [grossenPlainIdealSum, oppositeGrossenPlainIdealSum, Complex.conj_tsum,
    map_mul, map_pow, idealCoeff_inverse_conj]

theorem oppositeGrossenPlainIdealSum_conj (χ : Character) (k : ℕ) (W : ℝ → ℂ) (X : ℝ) :
    conj (oppositeGrossenPlainIdealSum χ k W X) =
      grossenPlainIdealSum χ.inverse k (fun x => conj (W x)) X := by
  simp only [grossenPlainIdealSum, oppositeGrossenPlainIdealSum, Complex.conj_tsum,
    map_mul, map_pow, idealCoeff_inverse_conj, Complex.conj_conj]

private theorem primitive_character_inverse (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) :
    (character c χ hu).inverse = character c χ⁻¹ (inverse_unit_trivial c χ hu) := rfl

/-- Radial transform for the anti-holomorphic angular source. -/
def oppositeAngularFourier (n : ℕ) (W : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  conj (paperAngularFourier n
    (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap W) x)

/-- Reflection for the infinity type occurring in the actual Grössencharacter
Dirichlet coefficients, with the conjugate angular radial transform. -/
theorem primitive_grossen_normalized_norm (k : ℕ) (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (W : 𝓢(ℝ, ℂ)) (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (X : ℝ) (hX : 0 < X) :
    ‖(Real.sqrt X : ℂ)⁻¹ * grossenPlainIdealSum (character c χ hu) (k + 1) W X‖ =
      ‖(Real.sqrt (‖ringComplex c‖ ^ 2 / X) : ℂ)⁻¹ *
        oppositeGrossenPlainIdealSum (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (k + 1)
          (oppositeAngularFourier (6 * (k + 1)) W) (‖ringComplex c‖ ^ 2 / X)‖ := by
  let V : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap W
  have hV : Function.support V ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x hx
    apply hW
    intro he
    exact hx (by change conj (W x) = 0; rw [he, map_zero])
  have h := primitive_angular_normalized_norm k c χ⁻¹
    (inverse_unit_trivial c χ hu) hp.inv V hV X hX
  simp only [inv_inv] at h
  have hleft : conj (oppositeGrossenPlainIdealSum
      (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (k + 1) V X) =
      grossenPlainIdealSum (character c χ hu) (k + 1) W X := by
    rw [oppositeGrossenPlainIdealSum_conj, primitive_character_inverse]
    simp only [inv_inv]
    congr 1
    funext x
    exact Complex.conj_conj (W x)
  have hl : ‖(Real.sqrt X : ℂ)⁻¹ * oppositeGrossenPlainIdealSum
      (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (k + 1) V X‖ =
      ‖(Real.sqrt X : ℂ)⁻¹ * grossenPlainIdealSum (character c χ hu) (k + 1) W X‖ := by
    rw [← Complex.norm_conj ((Real.sqrt X : ℂ)⁻¹ * _)]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, hleft]
  rw [hl] at h
  apply h.trans
  rw [← Complex.norm_conj ((Real.sqrt (‖ringComplex c‖ ^ 2 / X) : ℂ)⁻¹ * _)]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, grossenPlainIdealSum_conj,
    primitive_character_inverse, V]
  rfl

/-- Conjugating the input and output ray restrictions gives the opposite angular transform. -/
def oppositeAngularFourierRayCLM (n : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap).comp
    ((angularFourierRayCLM n).comp
      (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap))

theorem oppositeAngularFourier_eq_ray (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    oppositeAngularFourier n W = fun x => oppositeAngularFourierRayCLM n W (Real.sqrt x) := by
  let V : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap W
  have hV : Function.support V ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x hx
    apply hW
    intro he
    exact hx (by change conj (W x) = 0; rw [he, map_zero])
  funext x
  change conj (paperAngularFourier n V x) = conj (angularFourierRayCLM n V (Real.sqrt x))
  rw [paperAngularFourier_eq_ray n V hV]

theorem oppositeAngularFourier_contDiffOn (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ContDiffOn ℝ ∞ (oppositeAngularFourier n W) (Set.Ioi 0) := by
  rw [oppositeAngularFourier_eq_ray n W hW]
  exact contDiffOn_sqrt_profile _

theorem oppositeAngularFourier_log_contDiff (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => oppositeAngularFourier n W (x * Real.exp t)) := by
  rw [oppositeAngularFourier_eq_ray n W hW]
  exact contDiff_sqrt_profile_log _ x hx

/-- The Schwartz operator representing logarithmic derivatives of the opposite profile. -/
def oppositeAngularEulerCLM (n j : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (halfEulerIterateCLM j).comp (oppositeAngularFourierRayCLM n)

theorem oppositeAngularFourier_eulerDeriv (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (oppositeAngularFourier n W) j x =
      oppositeAngularEulerCLM n j W (Real.sqrt x) := by
  rw [oppositeAngularFourier_eq_ray n W hW, eulerDeriv_sqrt_profile _ j x hx]
  simp only [oppositeAngularEulerCLM, ContinuousLinearMap.comp_apply, halfEulerIterateCLM_apply]

/-- Every fixed number of Euler derivatives of the opposite profile has rapid decay
controlled by finitely many seminorms of the original annular source. -/
theorem oppositeAngularFourier_euler_source_weighted_bound (n A K : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ j ≤ K, ∀ x : ℝ, 0 ≤ x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (oppositeAngularFourier n W) j x‖ ≤
          C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨S, C, hC, hb⟩ :=
    schwartzCLM_family_finite_seminorm_control (oppositeAngularEulerCLM n) A K
  refine ⟨S, 2 ^ A * C, by positivity, ?_⟩
  intro W hW j hj x hx
  rw [oppositeAngularFourier_eulerDeriv n W hW j x hx]
  apply (sqrt_profile_rapid_bound (oppositeAngularEulerCLM n j W) A x hx).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb W j hj)
    (show 0 ≤ (2 : ℝ) ^ A by positivity)

end GaloisForLFunctions.FamilyContinuationTheory
