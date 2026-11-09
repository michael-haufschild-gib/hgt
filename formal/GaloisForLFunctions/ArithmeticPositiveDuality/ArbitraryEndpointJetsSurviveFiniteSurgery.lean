import GaloisForLFunctions.ArithmeticPositiveDuality.ClusteredEndpointPolynomial
import GaloisForLFunctions.ArithmeticPositiveDuality.ArbitrarilyLargeCriticalDonorClusters
import GaloisForLFunctions.ArithmeticPositiveDuality.TwoQuartetSurgeryPreservesXiEndpointJets
import GaloisForLFunctions.HTGeometry.AffineReflectionJet
import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational

/-!
# Arbitrary endpoint jets survive finite surgery on xi

A short cluster of actual critical-line zeros supplies a finite donor
divisor. An odd polynomial perturbation in `s(s-1)` moves its replacement
zeros off the line while preserving arbitrarily long jets at zero and one.
The entire surgery retains reflection, reality, and vertical normalization.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Polynomial

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The coordinate invariant under reflection about the critical line. -/
def surgeryCoordinate (s : ℂ) : ℂ := s * (s - 1)

@[simp] theorem surgeryCoordinate_one_sub (s : ℂ) :
    surgeryCoordinate (1 - s) = surgeryCoordinate s := by
  unfold surgeryCoordinate
  ring

@[simp] theorem surgeryCoordinate_conj (s : ℂ) :
    surgeryCoordinate (starRingEnd ℂ s) = starRingEnd ℂ (surgeryCoordinate s) := by
  simp only [surgeryCoordinate, map_mul, map_sub, map_one]

/-- The monic product removing one copy of every conjugate donor pair. -/
def criticalDonorDen {n : ℕ} (γ : Fin n → ℝ) (s : ℂ) : ℂ :=
  ∏ i, (surgeryCoordinate s + ((γ i ^ 2 + 1 / 4 : ℝ) : ℂ))

/-- The finite rational multiplier associated with a clustered donor polynomial. -/
def clusteredXiMultiplier (k : ℕ) (γ : Fin (2 * k + 2) → ℝ) (A w : ℝ) (s : ℂ) : ℂ :=
  (criticalDonorDen γ s - (clusterSurgerySize k A w : ℂ) *
    surgeryCoordinate s ^ (2 * k + 1)) / criticalDonorDen γ s

@[simp] theorem criticalDonorDen_one_sub {n : ℕ} (γ : Fin n → ℝ) (s : ℂ) :
    criticalDonorDen γ (1 - s) = criticalDonorDen γ s := by
  simp only [criticalDonorDen, surgeryCoordinate_one_sub]

@[simp] theorem criticalDonorDen_conj {n : ℕ} (γ : Fin n → ℝ) (s : ℂ) :
    criticalDonorDen γ (starRingEnd ℂ s) = starRingEnd ℂ (criticalDonorDen γ s) := by
  simp only [criticalDonorDen, surgeryCoordinate_conj, map_prod, map_add, Complex.conj_ofReal]

@[simp] theorem clusteredXiMultiplier_one_sub (k : ℕ) (γ : Fin (2 * k + 2) → ℝ)
    (A w : ℝ) (s : ℂ) :
    clusteredXiMultiplier k γ A w (1 - s) = clusteredXiMultiplier k γ A w s := by
  simp only [clusteredXiMultiplier, criticalDonorDen_one_sub, surgeryCoordinate_one_sub]

@[simp] theorem clusteredXiMultiplier_conj (k : ℕ) (γ : Fin (2 * k + 2) → ℝ)
    (A w : ℝ) (s : ℂ) :
    clusteredXiMultiplier k γ A w (starRingEnd ℂ s) =
      starRingEnd ℂ (clusteredXiMultiplier k γ A w s) := by
  simp only [clusteredXiMultiplier, criticalDonorDen_conj, surgeryCoordinate_conj,
    map_div₀, map_sub, map_mul, map_pow, Complex.conj_ofReal]

private def signedDonor {n : ℕ} (γ : Fin n → ℝ) (i : Fin n × Bool) : ℂ :=
  if i.2 then 1 / 2 + (γ i.1 : ℂ) * I else 1 / 2 - (γ i.1 : ℂ) * I

private theorem signedDonor_re {n : ℕ} (γ : Fin n → ℝ) (i : Fin n × Bool) :
    (signedDonor γ i).re = 1 / 2 := by
  rcases i with ⟨i, b⟩
  cases b <;> norm_num [signedDonor]

private theorem criticalDonorDen_eq_product {n : ℕ} (γ : Fin n → ℝ) (s : ℂ) :
    criticalDonorDen γ s = ∏ i : Fin n × Bool, (s - signedDonor γ i) := by
  rw [Fintype.prod_prod_type]
  unfold criticalDonorDen
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.prod_bool]
  apply Complex.ext <;>
    norm_num [signedDonor, surgeryCoordinate, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The donor denominator has no zero away from the critical line. -/
theorem criticalDonorDen_ne_zero {n : ℕ} (γ : Fin n → ℝ) {s : ℂ}
    (hs : s.re ≠ 1 / 2) : criticalDonorDen γ s ≠ 0 := by
  rw [criticalDonorDen_eq_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sub_ne_zero.mpr (fun he => hs (by rw [he, signedDonor_re]))

private theorem signedDonor_injective {n : ℕ} {γ : Fin n → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ) : Function.Injective (signedDonor γ) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ he
  have him := congrArg Complex.im he
  cases b <;> cases c <;> norm_num [signedDonor] at him
  · exact Prod.ext (hi (by linarith only [him])) rfl
  · linarith only [hp i, hp j, him]
  · linarith only [hp i, hp j, him]
  · exact Prod.ext (hi him) rfl

private theorem signedDonor_zero {n : ℕ} {γ : Fin n → ℝ}
    (hz : ∀ i, RHTower.xi (1 / 2 + (γ i : ℂ) * I) = 0) (i : Fin n × Bool) :
    RHTower.xi (signedDonor γ i) = 0 := by
  rcases i with ⟨i, b⟩
  cases b
  · have he : (1 / 2 - (γ i : ℂ) * I : ℂ) =
        starRingEnd ℂ (1 / 2 + (γ i : ℂ) * I) := by
      simp only [map_add, map_div₀, map_one, map_ofNat, map_mul,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    change RHTower.xi (1 / 2 - (γ i : ℂ) * I) = 0
    rw [he, RHTower.xi_conj, hz i, map_zero]
  · exact hz i

/-- Every finite family of distinct positive critical donor pairs has an entire quotient. -/
theorem exists_entire_critical_donor_quotient {n : ℕ} {γ : Fin n → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, RHTower.xi (1 / 2 + (γ i : ℂ) * I) = 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s, RHTower.xi s = G s * criticalDonorDen γ s := by
  classical
  let S := Finset.univ.image (signedDonor γ)
  obtain ⟨G, hG, he⟩ := entire_divide_finite_zeros S RHTower.xi_differentiable (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact signedDonor_zero hz i)
  refine ⟨G, hG, fun s => ?_⟩
  rw [he s, criticalDonorDen_eq_product]
  congr 1
  exact Finset.prod_image (signedDonor_injective hp hi).injOn

/-- Finite cancellation produces an entire surgery with the exact global flat difference. -/
theorem exists_entire_clustered_surgery (k : ℕ) {γ : Fin (2 * k + 2) → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ)
    (hz : ∀ i, RHTower.xi (1 / 2 + (γ i : ℂ) * I) = 0) (A w : ℝ) :
    ∃ F G : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ G ∧
      (∀ s, RHTower.xi s = G s * criticalDonorDen γ s) ∧
      (∀ s, F s = G s * (criticalDonorDen γ s -
        (clusterSurgerySize k A w : ℂ) * surgeryCoordinate s ^ (2 * k + 1))) ∧
      (∀ s, s.re ≠ 1 / 2 → F s = RHTower.xi s * clusteredXiMultiplier k γ A w s) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) := by
  obtain ⟨G, hG, he⟩ := exists_entire_critical_donor_quotient hp hi hz
  let F := fun s => G s * (criticalDonorDen γ s -
    (clusterSurgerySize k A w : ℂ) * surgeryCoordinate s ^ (2 * k + 1))
  have hF : Differentiable ℂ F := by
    apply hG.mul
    unfold criticalDonorDen surgeryCoordinate
    fun_prop
  have hEq (s : ℂ) (hs : s.re ≠ 1 / 2) :
      F s = RHTower.xi s * clusteredXiMultiplier k γ A w s := by
    rw [he s]
    dsimp only [F, clusteredXiMultiplier]
    field_simp [criticalDonorDen_ne_zero γ hs]
  refine ⟨F, G, hF, hG, he, fun _ => rfl, hEq, ?_, ?_⟩
  · have hsym : (fun s => F (1 - s)) = F := entire_eq_of_off_line
        (hF.comp (show Differentiable ℂ (fun s : ℂ => 1 - s) by fun_prop)) hF (by
      intro s hs
      have hs' : (1 - s).re ≠ 1 / 2 := by
        simp only [Complex.sub_re, Complex.one_re]
        intro h
        apply hs
        linarith only [h]
      rw [hEq (1 - s) hs', hEq s hs, RHTower.xi_one_sub, clusteredXiMultiplier_one_sub])
    exact congrFun hsym
  · have hsym : (fun s => starRingEnd ℂ (F (starRingEnd ℂ s))) = F :=
        entire_eq_of_off_line (RHTower.differentiable_conj_reflect hF) hF (by
      intro s hs
      rw [hEq (starRingEnd ℂ s) (by simpa only [Complex.conj_re] using hs),
        hEq s hs, RHTower.xi_conj, clusteredXiMultiplier_conj, map_mul,
        Complex.conj_conj, Complex.conj_conj])
    intro s
    have h := congrFun hsym (starRingEnd ℂ s)
    simpa only [Complex.conj_conj] using h.symm

private theorem flat_product_jet {m j : ℕ} {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hj : j < m) :
    iteratedDeriv j (fun s => s ^ m * B s) 0 = 0 := by
  change iteratedDeriv j ((id : ℂ → ℂ) ^ m * B) 0 = 0
  rw [iteratedDeriv_mul (analyticAt_id.pow m).contDiffAt hB.contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  have him : i < m := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hj
  change (j.choose i : ℂ) * iteratedDeriv i (fun s : ℂ => s ^ m) 0 *
    iteratedDeriv (j - i) B 0 = 0
  simp only [iteratedDeriv_pow, zero_pow (Nat.sub_pos_of_lt him).ne', mul_zero, zero_mul]

/-- The global monomial difference preserves the full endpoint jet through order `2k`. -/
theorem clustered_surgery_endpoint_jets (k : ℕ) {γ : Fin (2 * k + 2) → ℝ}
    {A w : ℝ} {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hξ : ∀ s, RHTower.xi s = G s * criticalDonorDen γ s)
    (hFG : ∀ s, F s = G s * (criticalDonorDen γ s -
      (clusterSurgerySize k A w : ℂ) * surgeryCoordinate s ^ (2 * k + 1)))
    (hFE : ∀ s, F (1 - s) = F s) :
    ∀ j ≤ 2 * k, iteratedDeriv j F 0 = iteratedDeriv j RHTower.xi 0 ∧
      iteratedDeriv j F 1 = iteratedDeriv j RHTower.xi 1 := by
  intro j hj
  have hFa : AnalyticAt ℂ F 0 := hF.analyticAt 0
  have hξa : AnalyticAt ℂ RHTower.xi 0 := RHTower.xi_differentiable.analyticAt 0
  have hdiff : F - RHTower.xi = fun s => s ^ (2 * k + 1) *
      (-(clusterSurgerySize k A w : ℂ) * (s - 1) ^ (2 * k + 1) * G s) := by
    funext s
    simp only [Pi.sub_apply, hFG s, hξ s, surgeryCoordinate, mul_pow]
    ring
  have hB : AnalyticAt ℂ (fun s =>
      -(clusterSurgerySize k A w : ℂ) * (s - 1) ^ (2 * k + 1) * G s) 0 := by
    exact ((analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow _)).mul
      (hG.analyticAt 0))
  have hz := flat_product_jet hB (show j < 2 * k + 1 by omega)
  rw [← hdiff, iteratedDeriv_sub hFa.contDiffAt hξa.contDiffAt, sub_eq_zero] at hz
  refine ⟨hz, ?_⟩
  have hf := HTGeometry.iteratedDeriv_comp_one_sub_of_analyticAt j
    (hF.analyticAt (1 - (0 : ℂ)))
  have hx := HTGeometry.iteratedDeriv_comp_one_sub_of_analyticAt j
    (RHTower.xi_differentiable.analyticAt (1 - (0 : ℂ)))
  simp only [hFE, RHTower.xi_one_sub, sub_zero] at hf hx
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
    (hf.symm.trans (hz.trans hx))

/-- Equal monic degrees retain the normalization along every vertical line. -/
theorem clusteredXiMultiplier_tendsto_vertical (k : ℕ) (γ : Fin (2 * k + 2) → ℝ)
    (A w σ : ℝ) :
    Tendsto (fun t : ℝ => clusteredXiMultiplier k γ A w ((σ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 1) := by
  let z := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I
  have hq : Tendsto (fun t => ‖surgeryCoordinate (z t)‖) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have h₁ : t ≤ ‖z t‖ := by
      simpa only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
        zero_add, abs_of_nonneg (by linarith only [ht] : 0 ≤ t)] using
        Complex.abs_im_le_norm (z t)
    have h₂ : t ≤ ‖z t - 1‖ := by
      simpa only [z, Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
        mul_one, mul_zero, add_zero, zero_add,
        abs_of_nonneg (by linarith only [ht] : 0 ≤ t)] using
        Complex.abs_im_le_norm (z t - 1)
    have hm := mul_le_mul h₁ h₂ (by linarith only [ht] : 0 ≤ t) (norm_nonneg (z t))
    change t ≤ ‖surgeryCoordinate (z t)‖
    rw [surgeryCoordinate, norm_mul]
    nlinarith only [hm, ht]
  let a := fun i => γ i ^ 2 + 1 / 4
  let D : ℂ[X] := ∏ i, (X + C (a i : ℂ))
  let N := clusterSurgeryPolynomial k a A w
  have hDm : D.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)
  have hDd : D.natDegree = 2 * k + 2 := by
    dsimp only [D]
    rw [natDegree_prod _ _ (fun i _ => (monic_X_add_C (a i : ℂ)).ne_zero)]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  obtain ⟨hNm, hNd⟩ := clusterSurgeryPolynomial_monic_degree k a A w
  have hD := tendsto_eval_div_pow_natDegree_of_norm_atTop hq D
  have hN := tendsto_eval_div_pow_natDegree_of_norm_atTop hq N
  rw [hDd, hDm.leadingCoeff] at hD
  change Tendsto (fun t => N.eval (surgeryCoordinate (z t)) /
    surgeryCoordinate (z t) ^ N.natDegree) atTop (𝓝 N.leadingCoeff) at hN
  rw [show N.natDegree = 2 * k + 2 from hNd,
    show N.leadingCoeff = 1 from hNm.leadingCoeff] at hN
  have hdiv := hN.div hD (one_ne_zero : (1 : ℂ) ≠ 0)
  rw [div_self (one_ne_zero : (1 : ℂ) ≠ 0)] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hq.eventually_gt_atTop 0, hD.eventually_ne (one_ne_zero : (1 : ℂ) ≠ 0)]
    with t ht hdt
  have hq0 : surgeryCoordinate (z t) ≠ 0 := by
    intro he
    simp only [he, norm_zero, lt_self_iff_false] at ht
  have hd0 : D.eval (surgeryCoordinate (z t)) ≠ 0 := by
    intro he
    exact hdt (by rw [he, zero_div])
  have hd : D.eval (surgeryCoordinate (z t)) = criticalDonorDen γ (z t) := by
    simp only [D, Polynomial.eval_prod, eval_add, eval_X, eval_C, a, criticalDonorDen]
  change (N.eval (surgeryCoordinate (z t)) / surgeryCoordinate (z t) ^ (2 * k + 2)) /
    (D.eval (surgeryCoordinate (z t)) / surgeryCoordinate (z t) ^ (2 * k + 2)) = _
  rw [show N.eval (surgeryCoordinate (z t)) = criticalDonorDen γ (z t) -
      (clusterSurgerySize k A w : ℂ) * surgeryCoordinate (z t) ^ (2 * k + 1) by
    simp only [N, clusterSurgeryPolynomial_eval, a, criticalDonorDen], hd]
  rw [hd] at hd0
  change _ = (criticalDonorDen γ (z t) - (clusterSurgerySize k A w : ℂ) *
    surgeryCoordinate (z t) ^ (2 * k + 1)) / criticalDonorDen γ (z t)
  field_simp [hq0, hd0]

/-- A short high ordinate interval gives narrow transverse confinement for replacement roots. -/
theorem donor_cluster_geometry_with_scale {L ell : ℝ}
    (hL : 16 ≤ L) (hell : 0 < ell) (hu : ell ≤ 1 / 8) :
    ∃ A w : ℝ, 0 < w ∧ 7 * w < A ∧
      A - w = L ^ 2 + 1 / 4 ∧ w ≤ 3 / 2 * L * ell ∧
      (∀ x : ℝ, L ≤ x → x ≤ L + ell → |x ^ 2 + 1 / 4 - A| ≤ w) ∧
      (∀ s : ℂ, ‖surgeryCoordinate s + (A : ℂ)‖ < 5 * w →
        |s.re - 1 / 2| < 4 * ell) := by
  let w := L * ell + ell ^ 2 / 2
  let A := (L ^ 2 + (L + ell) ^ 2) / 2 + 1 / 4
  have hL0 : 0 < L := by linarith only [hL]
  have hw : 0 < w := by dsimp only [w]; positivity
  have hAid : A = L ^ 2 + w + 1 / 4 := by dsimp only [A, w]; ring
  have hellL : ell ≤ L := by linarith only [hu, hL]
  have hwL : w ≤ 3 / 2 * L * ell := by
    have hm := mul_nonneg hell.le (sub_nonneg.mpr hellL)
    dsimp only [w]
    nlinarith only [hm]
  have hwsmall : w ≤ 3 / 16 * L := by
    have hm := mul_le_mul_of_nonneg_left hu hL0.le
    nlinarith only [hwL, hm]
  have hLsq : 16 * L ≤ L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hL hL0.le
    nlinarith only [hm]
  have hA : 7 * w < A := by nlinarith only [hAid, hwsmall, hLsq, hL0, hw]
  let H := Real.sqrt (A - 1 / 4)
  have hAnonneg : 0 ≤ A - 1 / 4 := by nlinarith only [hAid, hw, sq_nonneg L]
  have hHsq : H ^ 2 = A - 1 / 4 := Real.sq_sqrt hAnonneg
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hLH : L ≤ H := by nlinarith only [hHsq, hAid, hw, hH0, hL0]
  have hH : 0 < H := hL0.trans_le hLH
  refine ⟨A, w, hw, hA, by linarith only [hAid], hwL, ?_, ?_⟩
  · intro x hxl hxu
    have hlo := pow_le_pow_left₀ hL0.le hxl 2
    have hhi := pow_le_pow_left₀ (hL0.le.trans hxl) hxu 2
    rw [abs_le]
    dsimp only [A, w]
    constructor <;> nlinarith only [hlo, hhi]
  · intro s hs
    have hAc : A = H ^ 2 + 1 / 4 := by linarith only [hHsq]
    rw [hAc] at hs
    have hd := transverse_depth_lt_of_quadratic_distance hH s hs
    have hb : 5 * w / (2 * H) < 4 * ell := by
      rw [div_lt_iff₀ (by positivity : 0 < 2 * H)]
      have hm := mul_le_mul_of_nonneg_right hLH hell.le
      have hp := mul_pos hL0 hell
      nlinarith only [hwL, hm, hp]
    exact hd.trans hb

/-- Root confinement for a short high ordinate interval. -/
theorem donor_cluster_geometry {L ell : ℝ}
    (hL : 16 ≤ L) (hell : 0 < ell) (hu : ell ≤ 1 / 8) :
    ∃ A w : ℝ, 0 < w ∧ 7 * w < A ∧
      (∀ x : ℝ, L ≤ x → x ≤ L + ell → |x ^ 2 + 1 / 4 - A| ≤ w) ∧
      (∀ s : ℂ, ‖surgeryCoordinate s + (A : ℂ)‖ < 5 * w →
        |s.re - 1 / 2| < 4 * ell) := by
  obtain ⟨A, w, hw, hA, _, _, hp, hd⟩ := donor_cluster_geometry_with_scale hL hell hu
  exact ⟨A, w, hw, hA, hp, hd⟩

/-- Every finite endpoint jet of actual xi survives a finite rational surgery introducing
off-line zeros in an arbitrarily thin critical strip. All replacement zeros obey that width. -/
theorem arbitrary_endpoint_jets_survive_finite_xi_surgery (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : ℂ → ℂ) (γ : Fin (2 * K + 2) → ℝ) (A w : ℝ),
      Differentiable ℂ F ∧ Function.Injective γ ∧ (∀ i, 0 < γ i) ∧
      (∀ i, RHTower.xi (1 / 2 + (γ i : ℂ) * I) = 0) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) ∧
      (∀ j ≤ 2 * K, iteratedDeriv j F 0 = iteratedDeriv j RHTower.xi 0 ∧
        iteratedDeriv j F 1 = iteratedDeriv j RHTower.xi 1) ∧
      (∀ σ : ℝ, Tendsto
        (fun t : ℝ => clusteredXiMultiplier K γ A w ((σ : ℂ) + (t : ℂ) * I))
        atTop (𝓝 1)) ∧
      (∀ s, s.re ≠ 1 / 2 → F s = RHTower.xi s * clusteredXiMultiplier K γ A w s) ∧
      (∃ s, F s = 0 ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 ∧
        0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| < δ) ∧
      (∀ s, (clusterSurgeryPolynomial K (fun i => γ i ^ 2 + 1 / 4) A w).eval
          (surgeryCoordinate s) = 0 →
        F s = 0 ∧ s.re ≠ 1 / 2 ∧ s.im ≠ 0 ∧
          0 < s.re ∧ s.re < 1 ∧ |s.re - 1 / 2| < δ) := by
  let ell := min δ 1 / 8
  have hell : 0 < ell := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have hu : ell ≤ 1 / 8 := div_le_div_of_nonneg_right (min_le_right δ 1) (by norm_num)
  have hdδ : 4 * ell < δ := by
    have hm := min_le_left δ 1
    dsimp only [ell]
    linarith only [hm, hδ]
  have hdhalf : 4 * ell ≤ 1 / 2 := by linarith only [hu]
  obtain ⟨L, γ, hL, _, hi, hγ⟩ := exists_critical_donor_cluster (2 * K + 2) hell 16
  have hp (i : Fin (2 * K + 2)) : 0 < γ i := by
    have hl := (hγ i).1
    linarith only [hL, hl]
  have hz (i : Fin (2 * K + 2)) := (hγ i).2.2
  obtain ⟨A, w, hw, hA, hparam, hdepth⟩ := donor_cluster_geometry hL hell hu
  have ha (i : Fin (2 * K + 2)) : |γ i ^ 2 + 1 / 4 - A| ≤ w :=
    hparam (γ i) (hγ i).1 (hγ i).2.1
  obtain ⟨F, G, hF, hG, hξ, hFG, hEq, hFE, hconj⟩ :=
    exists_entire_clustered_surgery K hp hi hz A w
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
  refine ⟨F, γ, A, w, hF, hi, hp, hz, hFE, hconj, ?_,
    clusteredXiMultiplier_tendsto_vertical K γ A w, hEq, ⟨s, hroots s (by rwa [hs])⟩,
    hroots⟩
  intro j hj
  exact clustered_surgery_endpoint_jets K hF hG hξ hFG hFE j hj

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.arbitrary_endpoint_jets_survive_finite_xi_surgery
