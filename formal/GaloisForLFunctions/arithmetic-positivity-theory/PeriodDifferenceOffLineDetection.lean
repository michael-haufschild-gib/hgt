import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw
import GaloisForLFunctions.RHTower.WeilFullConeWindowPinning

/-! Exact detection of a reflected off-line pair over a complete on-line lattice.
A period difference annihilates the entire lattice. Thin nonnegative seeds give
an explicit negative margin; the literal square diagonal and reflection defect
are retained, with no readout or sign assumption in the native applications. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology CompactlySupported ComplexConjugate
open _root_.Zeta23 _root_.RHTower
open _root_.RHTower.WeilOneSided
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false


/-- Vanishing on the entire lattice reduces every summable channel to the literal pair. -/
private theorem isolatedPair_tsum_eq {E : Type*} [NormedAddCommGroup E]
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1/2) (γ : ℝ)
    (F : ℂ → E) (hF : ∀ k : ℤ, F (verticalLatticePoint L 0 k) = 0) :
    (∑' ρ : (isolatedPairConfig hL hδ hδ' γ).carrier, F ρ) =
      F (offLinePoint δ γ)+F (offLinePoint (-δ) γ) := by
  have hline : HasSum (fun ρ : Set.range (verticalLatticePoint L 0) => F ρ) 0 := by
    have he : (fun ρ : Set.range (verticalLatticePoint L 0) => F ρ) = fun _ => 0 := by
      funext ρ
      rcases ρ with ⟨ρ, k, hk⟩
      subst ρ
      exact hF k
    rw [he]
    exact hasSum_zero
  have hp := hasSum_singleton (offLinePoint δ γ) F
  have hq := hasSum_singleton (offLinePoint (-δ) γ) F
  have hd₁ : Disjoint (Set.range (verticalLatticePoint L 0)) {offLinePoint δ γ} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨k, hk⟩
    have he := congrArg Complex.re hk
    simp only [verticalLatticePoint, offLinePoint] at he
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ})
      {offLinePoint (-δ) γ} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨k, hk⟩ | hk)
    · have he := congrArg Complex.re hk
      simp only [verticalLatticePoint, offLinePoint] at he
      linarith
    · rw [Set.mem_singleton_iff] at hk
      have he := congrArg Complex.re hk
      simp only [offLinePoint] at he
      linarith
  have hall := HasSum.add_disjoint (f := F) hd₂ (HasSum.add_disjoint (f := F) hd₁ hline hp) hq
  change (∑' ρ : ↥((Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ}) ∪ {offLinePoint (-δ) γ}), F ρ) = _
  simpa only [Function.comp_def, zero_add] using hall.tsum_eq

private theorem lattice_period_exponential {L : ℝ} (hL : 0 < L) (k : ℤ) :
    Complex.exp (I*((((k : ℝ)*(2*Real.pi/L) : ℝ) : ℂ))*(L : ℂ)) = 1 := by
  have he : I*((((k : ℝ)*(2*Real.pi/L) : ℝ) : ℂ))*(L : ℂ) =
      (k : ℂ)*(2*(Real.pi : ℂ)*I) := by
    push_cast
    field_simp [hL.ne']
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem periodDifference_online_readout_zero (f : C_c(ℝ, ℝ)) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    paperFT (shiftPair f (-1) L) ((((k : ℝ)*(2*Real.pi/L) : ℝ) : ℂ)) = 0 := by
  rw [paperFT_shiftPair (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport, lattice_period_exponential hL]
  simp

private theorem pair_period_exponential {L : ℝ} (hL : 0 < L) (α : ℝ) :
    Complex.exp (I*((2*Real.pi/L : ℝ)-I*(α : ℂ))*(L : ℂ)) =
      (Real.exp (α*L) : ℂ) := by
  have he : I*((2*Real.pi/L : ℝ)-I*(α : ℂ))*(L : ℂ) =
      ((α*L : ℝ) : ℂ)+2*(Real.pi : ℂ)*I := by
    push_cast
    field_simp [hL.ne']
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, ← Complex.ofReal_exp]

theorem periodDifference_pair_readout (f : C_c(ℝ, ℝ)) {L : ℝ} (hL : 0 < L) (α : ℝ) :
    paperFT (shiftPair f (-1) L) ((2*Real.pi/L : ℝ)-I*(α : ℂ)) =
      (1-(Real.exp (α*L) : ℂ))*paperFT (liftC f) ((2*Real.pi/L : ℝ)-I*(α : ℂ)) := by
  rw [paperFT_shiftPair (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport, pair_period_exponential hL]
  push_cast
  ring

def realTiltMass (f : C_c(ℝ, ℝ)) (α : ℝ) : ℝ := ∫ x, Real.exp (α*x)*f x

private theorem tilt_integrable (f : C_c(ℝ, ℝ)) (α : ℝ) :
    Integrable (fun x => Real.exp (α*x)*f x) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul f.continuous).integrable_of_hasCompactSupport
    f.hasCompactSupport.mul_left

theorem compact_nonnegative_readout_sector (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0) (α γ : ℝ) :
    ‖paperFT (liftC f) ((γ : ℂ)-I*(α : ℂ))-(realTiltMass f α : ℂ)‖ ≤
      (|γ| *R)*realTiltMass f α := by
  have he (x : ℝ) : I*((γ : ℂ)-I*(α : ℂ))*(x : ℂ) =
      ((α*x : ℝ) : ℂ)+I*((γ*x : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hpoint (x : ℝ) : liftC f x*Complex.exp (I*((γ : ℂ)-I*(α : ℂ))*(x : ℂ)) =
      ((Real.exp (α*x)*f x : ℝ) : ℂ)*Complex.exp (I*((γ*x : ℝ) : ℂ)) := by
    rw [he, Complex.exp_add, ← Complex.ofReal_exp]
    simp only [liftC, Complex.ofReal_mul]
    ring
  have hread : paperFT (liftC f) ((γ : ℂ)-I*(α : ℂ)) =
      ∫ x, ((Real.exp (α*x)*f x : ℝ) : ℂ)*Complex.exp (I*((γ*x : ℝ) : ℂ)) := by
    unfold paperFT
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hi : Integrable (fun x => ((Real.exp (α*x)*f x : ℝ) : ℂ)*Complex.exp (I*((γ*x : ℝ) : ℂ))) := by
    exact (integrable_liftC_mul_exp f.continuous f.hasCompactSupport ((γ : ℂ)-I*(α : ℂ))).congr
      (Filter.Eventually.of_forall hpoint)
  have hreal : Integrable (fun x => ((Real.exp (α*x)*f x : ℝ) : ℂ)) :=
    (tilt_integrable f α).ofReal
  have hd : paperFT (liftC f) ((γ : ℂ)-I*(α : ℂ))-(realTiltMass f α : ℂ) =
      ∫ x, ((Real.exp (α*x)*f x : ℝ) : ℂ)*(Complex.exp (I*((γ*x : ℝ) : ℂ))-1) := by
    rw [hread, realTiltMass, ← integral_complex_ofReal, ← integral_sub hi hreal]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hd]
  have hbound : ∀ x, ‖((Real.exp (α*x)*f x : ℝ) : ℂ)*(Complex.exp (I*((γ*x : ℝ) : ℂ))-1)‖ ≤
      (Real.exp (α*x)*f x)*(|γ| *R) := by
    intro x
    by_cases hx : R < |x|
    · simp [hR x hx]
    have hxR : |x| ≤ R := le_of_not_gt hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf x))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le (hf x))
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := γ*x)).trans ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hxR (abs_nonneg γ)
  have h := norm_integral_le_of_norm_le ((tilt_integrable f α).mul_const (|γ| *R))
    (Filter.Eventually.of_forall hbound)
  rw [integral_mul_const] at h
  simpa only [realTiltMass, mul_comm] using h


theorem compact_nonnegative_tilt_lower (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0)
    (hmass : 1 ≤ ∫ x, f x) (α : ℝ) :
    Real.exp (-|α| *R) ≤ realTiltMass f α := by
  have hpoint (x : ℝ) : Real.exp (-|α| *R)*f x ≤ Real.exp (α*x)*f x := by
    by_cases hx : R < |x|
    · simp [hR x hx]
    have hxR : |x| ≤ R := le_of_not_gt hx
    have ha : -|α| *R ≤ α*x := by
      have h := mul_le_mul_of_nonneg_left hxR (abs_nonneg α)
      have h' := neg_abs_le (α*x)
      rw [abs_mul] at h'
      linarith
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (hf x)
  calc
    _ ≤ Real.exp (-|α| *R)*(∫ x, f x) := by nlinarith [Real.exp_pos (-|α| *R)]
    _ = ∫ x, Real.exp (-|α| *R)*f x := (integral_const_mul _ _).symm
    _ ≤ realTiltMass f α := integral_mono
      ((f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).const_mul _)
      (tilt_integrable f α) hpoint

private theorem re_mul_conj_lower_of_quarter {U V : ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : ‖U-(A : ℂ)‖ ≤ A/4) (hV : ‖V-(B : ℂ)‖ ≤ B/4) :
    A*B/2 ≤ (U*conj V).re := by
  have hUr : |U.re-A| ≤ A/4 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using (Complex.abs_re_le_norm (U-(A : ℂ))).trans hU
  have hVr : |V.re-B| ≤ B/4 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using (Complex.abs_re_le_norm (V-(B : ℂ))).trans hV
  have hUi : |U.im| ≤ A/4 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using (Complex.abs_im_le_norm (U-(A : ℂ))).trans hU
  have hVi : |V.im| ≤ B/4 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using (Complex.abs_im_le_norm (V-(B : ℂ))).trans hV
  have hUr' : 3*A/4 ≤ U.re := by linarith [(abs_le.mp hUr).1]
  have hVr' : 3*B/4 ≤ V.re := by linarith [(abs_le.mp hVr).1]
  have hr : (3*A/4)*(3*B/4) ≤ U.re*V.re :=
    mul_le_mul hUr' hVr' (by positivity) (by linarith)
  have hi : |U.im*V.im| ≤ (A/4)*(B/4) := by
    rw [abs_mul]
    exact mul_le_mul hUi hVi (abs_nonneg _) (by positivity)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
  nlinarith [(abs_le.mp hi).1]

theorem isolatedPair_W_of_online_zero {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1/2) (γ : ℝ) (f : ℝ → ℂ)
    (hf : ∀ k : ℤ, paperFT f ((((k : ℝ)*(2*Real.pi/L) : ℝ) : ℂ)) = 0) :
    (isolatedPairConfig hL hδ hδ' γ).W f f =
      paperFT f ((γ : ℂ)-I*δ)*conj (paperFT f ((γ : ℂ)+I*δ))+
        paperFT f ((γ : ℂ)+I*δ)*conj (paperFT f ((γ : ℂ)-I*δ)) := by
  let Z := isolatedPairConfig hL hδ hδ' γ
  have hm (α : ℝ) (hα : α ≠ 0) : Z.mult (offLinePoint α γ) = 1 := by
    change (if (offLinePoint α γ).re = 1/2 then 2 else 1) = 1
    rw [if_neg]
    change ¬ (1/2+α = 1/2)
    intro he
    apply hα
    linarith
  have hconj₁ : conj ((γ : ℂ)-I*δ) = (γ : ℂ)+I*δ := by
    simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
  have hconj₂ : conj ((γ : ℂ)+I*δ) = (γ : ℂ)-I*δ := by
    simp [map_add, Complex.conj_ofReal, Complex.conj_I]
    ring
  have honline (k : ℤ) : Z.Wsummand f f (verticalLatticePoint L 0 k) = 0 := by
    unfold ZeroConfig.Wsummand
    rw [gammaOf_verticalLatticePoint]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero, hf k, zero_mul, mul_zero]
  change (∑' ρ : Z.carrier, Z.Wsummand f f ρ) = _
  rw [isolatedPair_tsum_eq hL hδ hδ' γ (Z.Wsummand f f) honline]
  unfold ZeroConfig.Wsummand
  rw [hm δ hδ.ne', hm (-δ) (neg_ne_zero.mpr hδ.ne'), gammaOf_offLinePoint, gammaOf_offLinePoint]
  simp only [Nat.cast_one, one_mul, Complex.ofReal_neg, mul_neg, sub_neg_eq_add, hconj₁, hconj₂]

/-- Thin nonnegative sources produce a strictly negative reflected-pair readout after a lattice difference. -/
theorem periodDifference_isolatedPair_negative_margin (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0)
    (hmass : 1 ≤ ∫ x, f x) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1/2)
    (hthin : (2*Real.pi/L)*R ≤ 1/4) :
    ((isolatedPairConfig hL hδ hδ' (2*Real.pi/L)).W (shiftPair f (-1) L) (shiftPair f (-1) L)).re ≤
      -((Real.exp (δ*L)-1)*(1-Real.exp (-(δ*L)))*Real.exp (-2*δ*R)) := by
  let γ := 2*Real.pi/L
  let U := paperFT (liftC f) ((γ : ℂ)-I*δ)
  let V := paperFT (liftC f) ((γ : ℂ)+I*δ)
  let A := realTiltMass f δ
  let B := realTiltMass f (-δ)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hA := compact_nonnegative_tilt_lower f hf hR hmass δ
  have hB := compact_nonnegative_tilt_lower f hf hR hmass (-δ)
  rw [abs_of_pos hδ] at hA
  rw [abs_neg, abs_of_pos hδ] at hB
  have hA0 : 0 ≤ A := (Real.exp_pos _).le.trans hA
  have hB0 : 0 ≤ B := (Real.exp_pos _).le.trans hB
  have hU : ‖U-(A : ℂ)‖ ≤ A/4 := by
    have h := compact_nonnegative_readout_sector f hf hR δ γ
    rw [abs_of_pos hγ] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hthin hA0).trans_eq (by ring))
  have hV : ‖V-(B : ℂ)‖ ≤ B/4 := by
    have h := compact_nonnegative_readout_sector f hf hR (-δ) γ
    simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add, abs_of_pos hγ] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hthin hB0).trans_eq (by ring))
  have hUV := re_mul_conj_lower_of_quarter hA0 hB0 hU hV
  have hAB : Real.exp (-2*δ*R) ≤ A*B := by
    have h := mul_le_mul hA hB (Real.exp_pos _).le hA0
    rw [← Real.exp_add] at h
    convert h using 1 <;> congr 1 <;> ring
  have hplus : 0 < Real.exp (δ*L)-1 := by
    have h := Real.one_lt_exp_iff.mpr (mul_pos hδ hL)
    linarith
  have hminus : 0 < 1-Real.exp (-(δ*L)) := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hδ hL))
    linarith
  rw [isolatedPair_W_of_online_zero hL hδ hδ' γ _ (periodDifference_online_readout_zero f hL)]
  have hread₁ := periodDifference_pair_readout f hL δ
  have hread₂ := periodDifference_pair_readout f hL (-δ)
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add, neg_mul] at hread₂
  rw [hread₁, hread₂]
  have he : (((1-(Real.exp (δ*L) : ℂ))*U)*conj ((1-(Real.exp (-(δ*L)) : ℂ))*V)+
      ((1-(Real.exp (-(δ*L)) : ℂ))*V)*conj ((1-(Real.exp (δ*L) : ℂ))*U)).re =
      -2*((Real.exp (δ*L)-1)*(1-Real.exp (-(δ*L))))*(U*conj V).re := by
    simp only [map_mul, map_sub, map_one, Complex.conj_ofReal, Complex.add_re,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    ring
  change _ ≤ _
  rw [he]
  have hc : 0 ≤ (Real.exp (δ*L)-1)*(1-Real.exp (-(δ*L))) := mul_nonneg hplus.le hminus.le
  have h1 := mul_le_mul_of_nonneg_left hUV hc
  have h2 := mul_le_mul_of_nonneg_left hAB hc
  nlinarith


/-- The complete square diagonal, with the configuration's literal multiplicities. -/
def configurationSquareMass (Z : ZeroConfig) (f : ℝ → ℂ) : ℝ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℝ)*‖paperFT f (gammaOf ρ)‖^2

/-- The complete reflection defect in the same transform normalization as `ZeroConfig.W`. -/
def configurationReflectionDefect (Z : ZeroConfig) (f : ℝ → ℂ) : ℝ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℝ)/2*
    ‖paperFT f (gammaOf ρ)-paperFT f (conj (gammaOf ρ))‖^2

theorem isolatedPair_diagonal_defect_of_online_zero {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1/2) (γ : ℝ) (f : ℝ → ℂ)
    (hf : ∀ k : ℤ, paperFT f ((((k : ℝ)*(2*Real.pi/L) : ℝ) : ℂ)) = 0) :
    configurationSquareMass (isolatedPairConfig hL hδ hδ' γ) f =
        ‖paperFT f ((γ : ℂ)-I*δ)‖^2+‖paperFT f ((γ : ℂ)+I*δ)‖^2 ∧
      configurationReflectionDefect (isolatedPairConfig hL hδ hδ' γ) f =
        ‖paperFT f ((γ : ℂ)-I*δ)-paperFT f ((γ : ℂ)+I*δ)‖^2 := by
  let Z := isolatedPairConfig hL hδ hδ' γ
  have hm (α : ℝ) (hα : α ≠ 0) : Z.mult (offLinePoint α γ) = 1 := by
    change (if (offLinePoint α γ).re = 1/2 then 2 else 1) = 1
    rw [if_neg]
    change ¬ (1/2+α = 1/2)
    intro he
    apply hα
    linarith
  have hconj₁ : conj ((γ : ℂ)-I*δ) = (γ : ℂ)+I*δ := by
    simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
  have hconj₂ : conj ((γ : ℂ)+I*δ) = (γ : ℂ)-I*δ := by
    simp [map_add, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hs (k : ℤ) : (Z.mult (verticalLatticePoint L 0 k) : ℝ)*
      ‖paperFT f (gammaOf (verticalLatticePoint L 0 k))‖^2 = 0 := by
    rw [gammaOf_verticalLatticePoint]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero, hf k, norm_zero, pow_two, mul_zero]
  have hd (k : ℤ) : (Z.mult (verticalLatticePoint L 0 k) : ℝ)/2*
      ‖paperFT f (gammaOf (verticalLatticePoint L 0 k))-
        paperFT f (conj (gammaOf (verticalLatticePoint L 0 k)))‖^2 = 0 := by
    rw [gammaOf_verticalLatticePoint]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero, Complex.conj_ofReal, hf k,
      sub_self, norm_zero, pow_two, mul_zero]
  constructor
  · change (∑' ρ : Z.carrier, (Z.mult ρ : ℝ)*‖paperFT f (gammaOf ρ)‖^2) = _
    rw [isolatedPair_tsum_eq hL hδ hδ' γ (fun ρ => (Z.mult ρ : ℝ)*‖paperFT f (gammaOf ρ)‖^2) hs,
      hm δ hδ.ne', hm (-δ) (neg_ne_zero.mpr hδ.ne'), gammaOf_offLinePoint, gammaOf_offLinePoint]
    simp only [Nat.cast_one, one_mul, Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  · change (∑' ρ : Z.carrier, (Z.mult ρ : ℝ)/2*
      ‖paperFT f (gammaOf ρ)-paperFT f (conj (gammaOf ρ))‖^2) = _
    rw [isolatedPair_tsum_eq hL hδ hδ' γ (fun ρ => (Z.mult ρ : ℝ)/2*
        ‖paperFT f (gammaOf ρ)-paperFT f (conj (gammaOf ρ))‖^2) hd,
      hm δ hδ.ne', hm (-δ) (neg_ne_zero.mpr hδ.ne'), gammaOf_offLinePoint, gammaOf_offLinePoint]
    simp only [Nat.cast_one, Complex.ofReal_neg, mul_neg, sub_neg_eq_add, hconj₁, hconj₂]
    rw [norm_sub_rev (paperFT f ((γ : ℂ)+I*δ)) (paperFT f ((γ : ℂ)-I*δ))]
    ring

/-- The on-line budget is exactly zero; the remaining diagonal and defect retain the whole pair. -/
theorem isolatedPair_reflection_identity_of_online_zero {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1/2) (γ : ℝ) (f : ℝ → ℂ)
    (hf : ∀ k : ℤ, paperFT f ((((k : ℝ)*(2*Real.pi/L) : ℝ) : ℂ)) = 0) :
    configurationSquareMass (isolatedPairConfig hL hδ hδ' γ) f-
      ((isolatedPairConfig hL hδ hδ' γ).W f f).re =
        configurationReflectionDefect (isolatedPairConfig hL hδ hδ' γ) f := by
  obtain ⟨hs, hd⟩ := isolatedPair_diagonal_defect_of_online_zero hL hδ hδ' γ f hf
  rw [hs, hd, isolatedPair_W_of_online_zero hL hδ hδ' γ f hf]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

theorem periodDifference_reflection_gap (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0)
    (hmass : 1 ≤ ∫ x, f x) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1/2)
    (hthin : (2*Real.pi/L)*R ≤ 1/4) :
    (Real.exp (δ*L)-1)*(1-Real.exp (-(δ*L)))*Real.exp (-2*δ*R) ≤
      configurationReflectionDefect (isolatedPairConfig hL hδ hδ' (2*Real.pi/L)) (shiftPair f (-1) L)-
        configurationSquareMass (isolatedPairConfig hL hδ hδ' (2*Real.pi/L)) (shiftPair f (-1) L) := by
  have hW := periodDifference_isolatedPair_negative_margin f hf hR hmass hL hδ hδ' hthin
  have he := isolatedPair_reflection_identity_of_online_zero hL hδ hδ' (2*Real.pi/L)
    (shiftPair f (-1) L) (periodDifference_online_readout_zero f hL)
  linarith

end GaloisForLFunctions.ArithmeticPositivityTheory
