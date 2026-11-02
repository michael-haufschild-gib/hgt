import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.QuantitativeConeCutoffs
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.EighthPowerHeightBounds
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineUniformBounds

/-!
# Tail estimates for prescribed spline corrections

Eighth-power height matching controls exact coefficient norms.
Supergeometric masses absorb geometric thresholds and inverse residual radii;
exponential separation of real levels supplies the additional residual mass.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma approachLevel_step (d D : ℝ) (k : ℕ) :
    approachLevel d D (k+1)-approachLevel d D k=(D-d)/2*(1/2 : ℝ)^k := by
  simp only [approachLevel,pow_succ]
  ring

/-- A fixed larger cutoff leaves a full additional correction mass in each residual. -/
lemma cone_new_frequency_squared_mass_bound {a b d D C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hdD : d < D)
    (hC : 8 ≤ ((D-d)/2*min a b)*C) (k : ℕ) {u : ℝ}
    (hu : u ∈ coneSquare a b (quantitativeCutoff C (k+1)) \ coneSquare a b (quantitativeCutoff C k)) :
    2*Real.exp (-(approachLevel d D (k+1)-approachLevel d D k)*u) ≤
      2*(correctionMass (k+1))^2 := by
  let gap := (D-d)/2*(1/2 : ℝ)^k
  have hgap : 0 ≤ gap := by dsimp only [gap]; positivity
  have hmin : 0 ≤ min a b := le_min ha.le hb.le
  have htime := coneSquare_new_lower ha.le hb.le hu
  have hN := quantitativeCutoff_lower C k
  have hprod : gap*((quantitativeCutoff C k : ℝ)*min a b) ≥
      (((D-d)/2*min a b)*C)*(4 : ℝ)^k := by
    have hh := mul_le_mul_of_nonneg_left hN (mul_nonneg hgap hmin)
    have he : gap*min a b*(C*(8 : ℝ)^k)=(((D-d)/2*min a b)*C)*(4 : ℝ)^k := by
      dsimp only [gap]
      have hp : (1/2 : ℝ)^k*(8 : ℝ)^k=(4 : ℝ)^k := by rw [← mul_pow]; norm_num
      calc
        (D-d)/2*(1/2 : ℝ)^k*min a b*(C*(8 : ℝ)^k)=
          (((D-d)/2*min a b)*C)*((1/2 : ℝ)^k*(8 : ℝ)^k) := by ring
        _ = _ := by rw [hp]
    rw [he] at hh
    nlinarith only [hh]
  have hbig := mul_le_mul_of_nonneg_right hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) k)
  have hu' := mul_le_mul_of_nonneg_left htime hgap
  have hexponent : 2*(4 : ℝ)^(k+1) ≤ gap*u := by
    rw [pow_succ]
    nlinarith only [hprod,hbig,hu']
  have he : Real.exp (-(2*(4 : ℝ)^(k+1)))=(correctionMass (k+1))^2 := by
    rw [correctionMass,pow_two,← Real.exp_add]
    congr 1
    ring
  rw [approachLevel_step]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (Real.exp_le_exp.mpr (by change -gap*u ≤ _; linarith only [hexponent])).trans_eq he

lemma matched_spline_height_pos {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) :
    0 < massRadius (2*A) n := massRadius_pos (by positivity) hn

lemma matched_spline_height_pow {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) :
    (massRadius (2*A) n)^8=(n : ℝ)/A := by
  rw [massRadius_pow (by positivity : 0 < 2*A) hn]
  ring

lemma le_matched_spline_height {A F : ℝ} (hA : 0 < A) (hF : 0 ≤ F) {n : ℕ}
    (hn : 0 < n) (hAF : A*F^8 ≤ 1) : F ≤ massRadius (2*A) n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hn
  have hpow : F^8 ≤ (n : ℝ)/A := (le_div_iff₀ hA).2 (by nlinarith only [hAF,hn1])
  have hr := Real.rpow_le_rpow (pow_nonneg hF 8) hpow (by norm_num : (0 : ℝ) ≤ 1/8)
  have he : (F^8)^(1/8 : ℝ)=F := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hF]
    norm_num
  have hh : massRadius (2*A) n=((n : ℝ)/A)^(1/8 : ℝ) := by
    unfold massRadius
    congr 1
    ring
  rwa [he,← hh] at hr

/-- Matched spline heights eventually dominate every geometric threshold. -/
lemma eventually_le_matched_spline_height {n : ℕ → ℕ} (hn : ∀ k, 0 < n k)
    {F : ℕ → ℝ} (hF : ∀ k, 0 ≤ F k) {U R : ℝ} (hR : 0 < R)
    (hFU : ∀ k, F k ≤ U*R^k) :
    ∀ᶠ k : ℕ in atTop, F k ≤ massRadius (2*correctionMass k) (n k) := by
  have hs := (summable_correctionMass_mul_pow (pow_pos hR 8)).mul_left (U^8)
  have hlim : Tendsto (fun k => correctionMass k*(U*R^k)^8) atTop (𝓝 0) := by
    have h := hs.tendsto_atTop_zero
    apply h.congr
    intro k
    have he : (R^8)^k=(R^k)^8 := by rw [← pow_mul,Nat.mul_comm 8 k,pow_mul]
    rw [he,mul_pow]
    ring
  have hsmall := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with k hk
  apply le_matched_spline_height (correctionMass_pos k) (hF k) (hn k)
  exact ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hF k) (hFU k) 8)
    (correctionMass_pos k).le).trans hk.le)

/-- One additional correction mass absorbs every geometric inverse residual radius. -/
lemma eventually_two_mass_le_radius {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) {U R : ℝ}
    (hR : 0 < R) (hεU : ∀ k, 1/ε k ≤ U*R^k) :
    ∀ᶠ k : ℕ in atTop, 2*correctionMass k ≤ ε k := by
  have hlim := ((summable_correctionMass_mul_pow hR).mul_left (2*U)).tendsto_atTop_zero
  have hsmall := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with k hk
  apply (div_le_one (hε k)).1
  calc
    _ = (2*correctionMass k)*(1/ε k) := by ring
    _ ≤ (2*correctionMass k)*(U*R^k) :=
      mul_le_mul_of_nonneg_left (hεU k) (mul_nonneg (by norm_num) (correctionMass_pos k).le)
    _ = (2*U)*(correctionMass k*R^k) := by ring
    _ ≤ 1 := hk.le

#print axioms cone_new_frequency_squared_mass_bound
#print axioms eventually_le_matched_spline_height
#print axioms eventually_two_mass_le_radius

def splineMomentCoefficient (z : ℂ) : ℂ := (Complex.sinh z/z)^8

lemma splineMomentCoefficient_neg (z : ℂ) :
    splineMomentCoefficient (-z)=splineMomentCoefficient z := by
  simp only [splineMomentCoefficient,Complex.sinh_neg,neg_div_neg_eq]

lemma splineMomentCoefficient_conj (z : ℂ) :
    splineMomentCoefficient ((starRingEnd ℂ) z)=(starRingEnd ℂ) (splineMomentCoefficient z) := by
  simp only [splineMomentCoefficient,Complex.sinh_conj,map_pow,map_div₀]

lemma splineMomentCoefficient_ne_zero {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    splineMomentCoefficient ((δ : ℂ)+(x : ℂ)*Complex.I) ≠ 0 := by
  have hz : (δ : ℂ)+(x : ℂ)*Complex.I ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,Complex.zero_re] at hr
    exact hδ.ne' hr
  exact pow_ne_zero 8 (div_ne_zero (spline_sinh_ne_zero hδ x) hz)

/-- Uniform coefficient decay, with no freedom to change atom weights. -/
lemma norm_splineMomentCoefficient_le {δ D H x : ℝ} (hδ : 0 ≤ δ) (hδD : δ ≤ D)
    (hH : 0 < H) (hx : H ≤ x) :
    ‖splineMomentCoefficient ((δ : ℂ)+(x : ℂ)*Complex.I)‖ ≤ splineNumeratorEnvelope D/H^8 := by
  let z : ℂ := (δ : ℂ)+(x : ℂ)*Complex.I
  have hnum : ‖Complex.sinh z‖^8 ≤ splineNumeratorEnvelope D := by
    have hh := (norm_shiftedSplineNumerator_le δ 0 x).trans
      (splineNumeratorBound_le_envelope hδ hδD)
    simpa only [shiftedSplineNumerator_eq,phase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,
      one_mul,norm_pow] using hh
  have hden : H ≤ ‖z‖ := by
    have hh := Complex.abs_im_le_norm z
    simp only [z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_add,add_zero] at hh
    exact hx.trans ((le_abs_self x).trans hh)
  have hB : 0 ≤ splineNumeratorEnvelope D := (pow_nonneg (norm_nonneg _) 8).trans hnum
  change ‖(Complex.sinh z/z)^8‖ ≤ _
  rw [norm_pow,norm_div,div_pow]
  calc
    _ ≤ splineNumeratorEnvelope D/‖z‖^8 :=
      div_le_div_of_nonneg_right hnum (pow_nonneg (norm_nonneg _) 8)
    _ ≤ splineNumeratorEnvelope D/H^8 := div_le_div_of_nonneg_left hB
      (pow_pos hH 8) (pow_le_pow_left₀ hH.le hden 8)

/-- Matching the eighth power of height to node count fixes the block's norm budget. -/
lemma sum_norm_splineMomentCoefficient_le {δ D A : ℝ} (hδ : 0 ≤ δ) (hδD : δ ≤ D)
    (hA : 0 < A) {n : ℕ} (hn : 0 < n) {γ : Fin n → ℝ}
    (hγ : ∀ j, massRadius (2*A) n ≤ γ j) :
    ∑ j, ‖splineMomentCoefficient ((δ : ℂ)+(γ j : ℂ)*Complex.I)‖ ≤
      splineNumeratorEnvelope D*A := by
  have hH : 0 < massRadius (2*A) n := matched_spline_height_pos hA hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow := matched_spline_height_pow hA hn
  calc
    _ ≤ ∑ _j : Fin n, splineNumeratorEnvelope D/(massRadius (2*A) n)^8 :=
      sum_le_sum fun j _ => norm_splineMomentCoefficient_le hδ hδD hH (hγ j)
    _ = splineNumeratorEnvelope D*A := by
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hpow]
      field_simp [hnR.ne',hA.ne']

#print axioms norm_splineMomentCoefficient_le
#print axioms sum_norm_splineMomentCoefficient_le
#print axioms splineMomentCoefficient_neg
#print axioms splineMomentCoefficient_conj
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
