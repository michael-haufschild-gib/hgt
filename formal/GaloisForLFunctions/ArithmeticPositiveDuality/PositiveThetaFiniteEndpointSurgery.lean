import GaloisForLFunctions.ArithmeticPositiveDuality.FiniteDonorThetaSources
import GaloisForLFunctions.ArithmeticPositiveDuality.ArbitraryEndpointJetsSurviveFiniteSurgery
import GaloisForLFunctions.ArithmeticPositiveDuality.UniformThetaPrimeDeletionBounds

/-!
# Positive theta sources under finite endpoint-jet surgery

Uniform real zero-division bounds allow a sufficiently narrow high donor
cluster to move off the critical line while its source stays positive.
The finite rational perturbation preserves arbitrarily many endpoint derivatives
and positivity after every finite literal prime deletion on the positive half-line.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology RHTower

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The real theta source for the clustered monomial perturbation. -/
def finiteSurgeryThetaSource (k : ℕ) (γ : Fin (2 * k + 2) → ℝ) (A w x : ℝ) : ℝ :=
  thetaCuspFullSource x - clusterSurgerySize k A w * finiteDonorThetaSource (2 * k + 1) γ x

theorem finiteSurgeryThetaSource_even (k : ℕ) (γ : Fin (2 * k + 2) → ℝ) (A w x : ℝ) :
    finiteSurgeryThetaSource k γ A w (-x) = finiteSurgeryThetaSource k γ A w x := by
  simp only [finiteSurgeryThetaSource, thetaCuspFullSource_neg, finiteDonorThetaSource_even]

theorem expMomentSource_finiteSurgeryThetaSource (k : ℕ) (γ : Fin (2 * k + 2) → ℝ) (A w : ℝ) :
    ExpMomentSource (fun x => (finiteSurgeryThetaSource k γ A w x : ℂ)) := by
  have he : (fun x => (finiteSurgeryThetaSource k γ A w x : ℂ)) =
      fun x => thetaSourceC x + (-((clusterSurgerySize k A w : ℝ) : ℂ)) *
        (finiteDonorThetaSource (2 * k + 1) γ x : ℂ) := by
    funext x
    simp only [finiteSurgeryThetaSource, thetaSourceC, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [he]
  exact expMomentSource_thetaSourceC.add
    ((expMomentSource_finiteDonorThetaSource (2 * k + 1) γ).const_mul _)

theorem smooth_finiteSurgeryThetaSource (k : ℕ) {γ : Fin (2 * k + 2) → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, XiC (γ i : ℂ) = 0) (A w : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (finiteSurgeryThetaSource k γ A w) := by
  have hu := smooth_finiteDonorThetaSource (2 * k + 1) hp hi hz
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => (finiteSurgeryThetaSource k γ A w x : ℂ)) := by
    simpa only [finiteSurgeryThetaSource, thetaSourceC, Complex.ofReal_sub, Complex.ofReal_mul] using
      contDiff_thetaSourceC.sub (contDiff_const.mul hu)
  have hr := Complex.reCLM.contDiff.comp hc
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ((finiteSurgeryThetaSource k γ A w x : ℂ).re)) at hr
  simpa only [Complex.ofReal_re] using hr

private theorem finiteDonorThetaSource_transform_xi (m : ℕ) {γ : Fin (m + 1) → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, XiC (γ i : ℂ) = 0) (s : ℂ) :
    sourceTransform (fun x => (finiteDonorThetaSource m γ x : ℂ)) (-(s - 1 / 2) * I) *
      criticalDonorDen γ s = xi s * surgeryCoordinate s ^ m := by
  let z := -(s - 1 / 2) * I
  have hlin : 1 / 2 + z * I = s := by
    dsimp only [z]
    calc
      _ = 1 / 2 - (s - 1 / 2) * I ^ 2 := by ring
      _ = s := by rw [I_sq]; ring
  have hq : -z ^ 2 - 1 / 4 = surgeryCoordinate s := by
    dsimp only [z, surgeryCoordinate]
    simp only [mul_pow, neg_sq, I_sq]
    ring
  have hD : (∏ i, ((γ i : ℂ) ^ 2 - z ^ 2)) = criticalDonorDen γ s := by
    unfold criticalDonorDen
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    linear_combination hq
  have h := finiteDonorThetaSource_transform m hp hi hz z
  rwa [hD, hq, XiC, hlin] at h

/-- The positive-source candidate realizes the same finite rational divisor surgery globally. -/
theorem finiteSurgeryThetaSource_transform_mul (k : ℕ) {γ : Fin (2 * k + 2) → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, XiC (γ i : ℂ) = 0) (A w : ℝ) (s : ℂ) :
    sourceTransform (fun x => (finiteSurgeryThetaSource k γ A w x : ℂ)) (-(s - 1 / 2) * I) *
      criticalDonorDen γ s = xi s * (criticalDonorDen γ s -
        (clusterSurgerySize k A w : ℂ) * surgeryCoordinate s ^ (2 * k + 1)) := by
  have he : (fun x => (finiteSurgeryThetaSource k γ A w x : ℂ)) =
      fun x => thetaSourceC x + (-((clusterSurgerySize k A w : ℝ) : ℂ)) *
        (finiteDonorThetaSource (2 * k + 1) γ x : ℂ) := by
    funext x
    simp only [finiteSurgeryThetaSource, thetaSourceC, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  have hlin : 1 / 2 + (-(s - 1 / 2) * I) * I = s := by
    calc
      _ = 1 / 2 - (s - 1 / 2) * I ^ 2 := by ring
      _ = s := by rw [I_sq]; ring
  rw [he, sourceTransform_add expMomentSource_thetaSourceC
    ((expMomentSource_finiteDonorThetaSource (2 * k + 1) γ).const_mul _),
    sourceTransform_const_mul, sourceTransform_thetaSourceC, XiC, hlin]
  have hu := finiteDonorThetaSource_transform_xi (2 * k + 1) hp hi hz s
  linear_combination -(clusterSurgerySize k A w : ℂ) * hu

private theorem clusterSurgerySize_mul_sourceCost_le (k : ℕ) {L ell A w : ℝ}
    (hL : 0 < L) (hell : 0 ≤ ell) (hw : 0 < w)
    (hAw : A - w = L ^ 2 + 1 / 4) (hwL : w ≤ 3 / 2 * L * ell) :
    clusterSurgerySize k A w * (realZeroDivisionConstant / L *
        ((1 + 5 * realZeroDivisionConstant) * L) ^ (2 * k + 1)) ≤
      (2 * 3 ^ (2 * k + 2) * realZeroDivisionConstant *
        (1 + 5 * realZeroDivisionConstant) ^ (2 * k + 1)) * ell ^ (2 * k + 2) := by
  let B := realZeroDivisionConstant
  let R := 1 + 5 * B
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one one_le_realZeroDivisionConstant
  have hR : 0 < R := by dsimp only [R]; positivity
  have hcost : 0 ≤ B / L * (R * L) ^ (2 * k + 1) := by positivity
  have hnum := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * w)
    (show 2 * w ≤ 3 * L * ell by linarith only [hwL]) (2 * k + 2)
  have hden := pow_le_pow_left₀ (sq_nonneg L)
    (show L ^ 2 ≤ A - w by rw [hAw]; linarith) (2 * k + 1)
  have hfrac : 2 * (2 * w) ^ (2 * k + 2) / (A - w) ^ (2 * k + 1) ≤
      2 * (3 * L * ell) ^ (2 * k + 2) / (L ^ 2) ^ (2 * k + 1) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (by norm_num))
      (by positivity) hden
  change clusterSurgerySize k A w * (B / L * (R * L) ^ (2 * k + 1)) ≤
    (2 * 3 ^ (2 * k + 2) * B * R ^ (2 * k + 1)) * ell ^ (2 * k + 2)
  calc
    _ ≤ (2 * (3 * L * ell) ^ (2 * k + 2) / (L ^ 2) ^ (2 * k + 1)) *
        (B / L * (R * L) ^ (2 * k + 1)) :=
      mul_le_mul_of_nonneg_right hfrac hcost
    _ = _ := by
      have hp : L ^ (2 * k + 2) * L ^ (2 * k + 1) = L * (L ^ 2) ^ (2 * k + 1) := by
        rw [← pow_add, ← pow_mul, ← pow_succ']
        congr 1
        omega
      field_simp
      simp only [mul_pow]
      linear_combination
        (2 * 3 ^ (2 * k + 2) * B * R ^ (2 * k + 1) * ell ^ (2 * k + 2)) * hp

/-- Arbitrarily close positive smooth theta sources realize finite off-line surgery while
preserving arbitrary endpoint jets, vertical normalization, and every finite prime deletion's
positivity on the positive half-line. -/
theorem positive_theta_sources_preserve_finite_endpoint_jets (K : ℕ)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ (φ : ℝ → ℝ) (F : ℂ → ℂ) (γ : Fin (2 * K + 2) → ℝ) (A w : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ ExpMomentSource (fun x => (φ x : ℂ)) ∧
      (∀ x, φ (-x) = φ x) ∧
      (∀ x, 0 < φ x ∧ |φ x - thetaCuspFullSource x| ≤ η * thetaCuspFullSource x) ∧
      (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        ∀ x, 0 ≤ x → 0 < thetaPrimeDeletion S φ x) ∧
      Differentiable ℂ F ∧
      (∀ s, F s = sourceTransform (fun x => (φ x : ℂ)) (-(s - 1 / 2) * I)) ∧
      Function.Injective γ ∧ (∀ i, 0 < γ i) ∧
      (∀ i, xi (1 / 2 + (γ i : ℂ) * I) = 0) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) ∧
      (∀ j ≤ 2 * K, iteratedDeriv j F 0 = iteratedDeriv j xi 0 ∧
        iteratedDeriv j F 1 = iteratedDeriv j xi 1) ∧
      (∀ σ : ℝ, Tendsto
        (fun t : ℝ => clusteredXiMultiplier K γ A w ((σ : ℂ) + (t : ℂ) * I))
        atTop (𝓝 1)) ∧
      (∀ s, s.re ≠ 1 / 2 → F s = xi s * clusteredXiMultiplier K γ A w s) ∧
      (∃ s, F s = 0 ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 ∧
        0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| < δ) ∧
      (∀ s, (clusterSurgeryPolynomial K (fun i => γ i ^ 2 + 1 / 4) A w).eval
          (surgeryCoordinate s) = 0 →
        F s = 0 ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 ∧
          0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| < δ) := by
  let B := realZeroDivisionConstant
  let R := 1 + 5 * B
  let C := 2 * 3 ^ (2 * K + 2) * B * R ^ (2 * K + 1)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one one_le_realZeroDivisionConstant
  have hR : 0 < R := by dsimp only [R]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  let τ := min η (min (1 / 2) thetaDeletionRelativeRadius)
  have hτ : 0 < τ := lt_min hη (lt_min (by norm_num) thetaDeletionRelativeRadius_pos)
  have hτη : τ ≤ η := min_le_left _ _
  have hτhalf : τ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hτrad : τ ≤ thetaDeletionRelativeRadius := (min_le_right _ _).trans (min_le_right _ _)
  let ell := min (δ / 8) (min (1 / 8) (τ / C))
  have hell : 0 < ell := by dsimp only [ell]; positivity
  have hu : ell ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδell : ell ≤ δ / 8 := min_le_left _ _
  have hCell : ell ≤ τ / C := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : C * ell ≤ τ := by
    have h := (le_div_iff₀ hC).mp hCell
    nlinarith only [h]
  have hpell : ell ^ (2 * K + 2) ≤ ell := by
    rw [show 2 * K + 2 = (2 * K + 1) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_left hell.le
      (pow_le_one₀ hell.le (by linarith only [hu] : ell ≤ 1))
  have hdδ : 4 * ell < δ := by linarith only [hδell, hδ]
  have hdhalf : 4 * ell ≤ 1 / 2 := by linarith only [hu]
  obtain ⟨L, γ, hL, hL1, hi, hγ⟩ := exists_critical_donor_cluster (2 * K + 2) hell 16
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hp (i : Fin (2 * K + 2)) : 0 < γ i := hL0.trans_le (hγ i).1
  have hz (i : Fin (2 * K + 2)) : xi (1 / 2 + (γ i : ℂ) * I) = 0 := (hγ i).2.2
  have hXi (i : Fin (2 * K + 2)) : XiC (γ i : ℂ) = 0 := hz i
  have hγwide (i : Fin (2 * K + 2)) : L ≤ γ i ∧ γ i ≤ 2 * L := by
    refine ⟨(hγ i).1, ?_⟩
    have h := (hγ i).2.1
    linarith only [h, hu, hL]
  obtain ⟨A, w, hw, hA, hscale, hwL, hparam, hdepth⟩ :=
    donor_cluster_geometry_with_scale hL hell hu
  let cost := B / L * (R * L) ^ (2 * K + 1)
  let ε := clusterSurgerySize K A w
  have hε : 0 < ε := clusterSurgerySize_pos K hw hA
  have hbudget : ε * cost ≤ τ := by
    have h := clusterSurgerySize_mul_sourceCost_le K hL0 hell.le hw hscale hwL
    change ε * cost ≤ C * ell ^ (2 * K + 2) at h
    exact h.trans ((mul_le_mul_of_nonneg_left hpell hC.le).trans hsmall)
  let φ := finiteSurgeryThetaSource K γ A w
  have hpert (x : ℝ) : |ε * finiteDonorThetaSource (2 * K + 1) γ x| ≤
      τ * thetaCuspFullSource x := by
    have hb := finiteDonorThetaSource_uniform_bound (2 * K + 1) hL1 hγwide x
    change |finiteDonorThetaSource (2 * K + 1) γ x| ≤ cost * thetaCuspFullSource x at hb
    calc
      _ = ε * |finiteDonorThetaSource (2 * K + 1) γ x| := by rw [abs_mul, abs_of_pos hε]
      _ ≤ ε * (cost * thetaCuspFullSource x) := mul_le_mul_of_nonneg_left hb hε.le
      _ = (ε * cost) * thetaCuspFullSource x := by ring
      _ ≤ τ * thetaCuspFullSource x :=
        mul_le_mul_of_nonneg_right hbudget (thetaCuspFullSource_pos x).le
  have hφpos (x : ℝ) : 0 < φ x ∧ |φ x - thetaCuspFullSource x| ≤
      η * thetaCuspFullSource x := by
    have hb := hpert x
    have hk := thetaCuspFullSource_pos x
    constructor
    · change 0 < thetaCuspFullSource x - ε * finiteDonorThetaSource (2 * K + 1) γ x
      have hhalf := mul_le_mul_of_nonneg_right hτhalf hk.le
      nlinarith only [hb, hhalf,
        le_abs_self (ε * finiteDonorThetaSource (2 * K + 1) γ x), hk]
    · have he : φ x - thetaCuspFullSource x =
          -(ε * finiteDonorThetaSource (2 * K + 1) γ x) := by
        dsimp only [φ, finiteSurgeryThetaSource, ε]
        ring
      rw [he, abs_neg]
      exact hb.trans (mul_le_mul_of_nonneg_right hτη hk.le)
  have hφexp : ExpMomentSource (fun x => (φ x : ℂ)) :=
    expMomentSource_finiteSurgeryThetaSource K γ A w
  have hdeletion (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (x : ℝ) (hx : 0 ≤ x) :
      0 < thetaPrimeDeletion S φ x := by
    apply thetaPrimeDeletion_pos_of_relative_ball (S := S) (hS := hS) (hx := hx)
    intro y _
    have he : φ y - thetaCuspFullSource y =
        -(ε * finiteDonorThetaSource (2 * K + 1) γ y) := by
      dsimp only [φ, finiteSurgeryThetaSource, ε]
      ring
    rw [he, abs_neg]
    exact (hpert y).trans
      (mul_le_mul_of_nonneg_right hτrad (thetaCuspFullSource_pos y).le)
  obtain ⟨F, G, hF, hG, hξ, hFG, hEq, hFE, hconj⟩ :=
    exists_entire_clustered_surgery K hp hi hz A w
  have hrealize : ∀ s, F s = sourceTransform (fun x => (φ x : ℂ)) (-(s - 1 / 2) * I) := by
    have hdiff : Differentiable ℂ
        (fun s : ℂ => sourceTransform (fun x => (φ x : ℂ)) (-(s - 1 / 2) * I)) :=
      hφexp.differentiable_sourceTransform.comp (by fun_prop)
    apply congrFun (entire_eq_of_off_line hF hdiff ?_)
    intro s hs
    rw [hEq s hs, clusteredXiMultiplier, ← mul_div_assoc]
    exact ((eq_div_iff (criticalDonorDen_ne_zero γ hs)).mpr
      (finiteSurgeryThetaSource_transform_mul K hp hi hXi A w s)).symm
  have ha (i : Fin (2 * K + 2)) : |γ i ^ 2 + 1 / 4 - A| ≤ w :=
    hparam (γ i) (hγ i).1 (hγ i).2.1
  have hroots (s : ℂ)
      (hs : (clusterSurgeryPolynomial K (fun i => γ i ^ 2 + 1 / 4) A w).eval
        (surgeryCoordinate s) = 0) :
      F s = 0 ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 ∧
        0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| < δ := by
    obtain ⟨him, hnorm⟩ := clusterSurgeryPolynomial_roots K hw hA ha hs
    have hd := hdepth s hnorm
    have hab := abs_lt.mp (hd.trans_le hdhalf)
    refine ⟨?_, ?_, ?_, by linarith only [hab.1], by linarith only [hab.2], hd.trans hdδ⟩
    · rw [clusterSurgeryPolynomial_eval] at hs
      rw [hFG s]
      change G s * ((∏ i, (surgeryCoordinate s + ((γ i ^ 2 + 1 / 4 : ℝ) : ℂ))) -
        (clusterSurgerySize K A w : ℂ) * surgeryCoordinate s ^ (2 * K + 1)) = 0
      rw [hs, mul_zero]
    · intro he
      apply him
      simp only [surgeryCoordinate, Complex.mul_im, Complex.sub_im, Complex.sub_re,
        Complex.one_re, Complex.one_im, sub_zero, he]
      ring
    · intro he
      apply him
      simp only [surgeryCoordinate, Complex.mul_im, Complex.sub_im, Complex.one_im,
        he, sub_self, mul_zero, zero_mul, add_zero]
  obtain ⟨q, hq, _, _⟩ := exists_clusterSurgeryPolynomial_root K hw hA ha
  let s : ℂ := 1 / 2 + Complex.sqrt (q + 1 / 4)
  have hs : surgeryCoordinate s = q := by
    have hsq : Complex.sqrt (q + 1 / 4) ^ 2 = q + 1 / 4 :=
      Complex.cpow_nat_inv_pow _ (by norm_num)
    dsimp only [surgeryCoordinate, s]
    linear_combination hsq
  exact ⟨φ, F, γ, A, w, smooth_finiteSurgeryThetaSource K hp hi hXi A w, hφexp,
    finiteSurgeryThetaSource_even K γ A w, hφpos, hdeletion, hF, hrealize, hi, hp, hz, hFE, hconj,
    clustered_surgery_endpoint_jets K hF hG hξ hFG hFE,
    clusteredXiMultiplier_tendsto_vertical K γ A w, hEq,
    ⟨s, hroots s (by rwa [hs])⟩, hroots⟩

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.positive_theta_sources_preserve_finite_endpoint_jets
