import GaloisForLFunctions.IncommensurableGaborPinching.CosineKernelNonLatticeFloor

/-!
# Cosine-window sampling at arbitrary bandwidth

Cosine shape and Fourier bandwidth are independent parameters. The finite evaluation grid
converges uniformly on bulk ordinate pairs to the normalized cosine kernel, with error
`16 (c/w)²/T + 24w/L`. No upper bound on the bandwidth is required.
-/

noncomputable section

open Real MeasureTheory Filter Topology Finset
open scoped BigOperators

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- Realize a cosine window of shape `κ` on the grid and bandwidth of `P`. -/
def cosineParams (P : Zeta23.Params) (κ T : ℝ) : Zeta23.Params :=
  ⟨fun x => Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w (P.L T / 2 - P.w * x), P.lam, P.w⟩

/-- The frozen profile realizes the prescribed cosine window at its defining height. -/
lemma cosineParams_phi {P : Zeta23.Params} {κ T : ℝ} (hw : P.w ≠ 0) :
    (cosineParams P κ T).phi T = Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w := by
  funext u
  change Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w
    (P.L T / 2 - P.w * ((P.L T / 2 - |u|) / P.w)) = _
  rw [show P.L T / 2 - P.w * ((P.L T / 2 - |u|) / P.w) = |u| by field_simp; ring]
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu]
    exact Zeta23.ThmD.phiD_even u

private lemma admWindow_deriv_eq_zero {φ : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow φ L w c) {u : ℝ} (hu : L / 2 ≤ |u|) :
    deriv φ u = 0 := by
  have hmin : IsLocalMin φ u :=
    Filter.Eventually.of_forall fun x => by rw [hW.support u hu]; exact hW.nonneg x
  exact hmin.deriv_eq_zero

private lemma admWindow_abs_deriv_le {φ : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow φ L w c) (u : ℝ) :
    |deriv φ u| ≤ c / w := by
  rcases le_or_gt (L / 2) |u| with hu | hu
  · rw [admWindow_deriv_eq_zero hW hu, abs_zero]
    exact div_nonneg hW.c_nonneg hW.w_pos.le
  · have habs := abs_lt.mp hu
    have hle : -(L / 2) ≤ u := by linarith
    have hd1 : ContDiff ℝ 1 (deriv φ) := hW.contDiff.deriv'
    have hdiff : ∀ x, DifferentiableAt ℝ (deriv φ) x := fun x =>
      hd1.differentiable one_ne_zero x
    have hcont2 : Continuous (deriv (deriv φ)) := hd1.continuous_deriv le_rfl
    have hcs2 : HasCompactSupport (deriv (deriv φ)) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(L / 2)) (b := L / 2)) ?_
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hmem
      apply hx
      have hopen : IsOpen {y : ℝ | L / 2 < |y|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
      have hgt : L / 2 < |x| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
        rcases hmem with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have heq : deriv φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hgt] with y hy
        exact admWindow_deriv_eq_zero hW hy.le
      rw [heq.deriv_eq, deriv_const]
    have hint2 : Integrable (fun t => |deriv (deriv φ) t|) :=
      (hcont2.integrable_of_hasCompactSupport hcs2).abs
    have hzero : deriv φ (-(L / 2)) = 0 :=
      admWindow_deriv_eq_zero hW (by rw [abs_neg, abs_of_pos (by linarith [hW.L_pos])])
    have hftc : ∫ t in (-(L / 2))..u, deriv (deriv φ) t = deriv φ u - deriv φ (-(L / 2)) :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x)
        (hcont2.intervalIntegrable _ _)
    rw [hzero, sub_zero] at hftc
    rw [← hftc, intervalIntegral.integral_of_le hle]
    calc |∫ t in Set.Ioc (-(L / 2)) u, deriv (deriv φ) t|
        ≤ ∫ t in Set.Ioc (-(L / 2)) u, |deriv (deriv φ) t| := abs_integral_le_integral_abs
      _ ≤ ∫ t, |deriv (deriv φ) t| :=
          setIntegral_le_integral hint2 (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      _ ≤ c / w := hW.l1_deriv2

private lemma admWindow_grid_tail_sq_le {φ : ℝ → ℝ} {L w c : ℝ}
    (hW : Zeta23.AdmWindow φ L w c) {T γ : ℝ} (hT : 0 < T)
    (t : Finset ℤ)
    (hfar : ∀ k ∈ t, (T / 4) ≤ (γ - (T + k * (2 * Real.pi / L))) ^ 2) :
    ∑ k ∈ t, (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
      ≤ 4 * L ^ 2 * (c / w) ^ 2 / T := by
  set f : ℝ → ℂ := fun u => Complex.ofReal (φ u)
  set ψ : ℝ → ℂ := fun u => Complex.ofReal (deriv φ u)
  have hf_cd1 : ContDiff ℝ 1 f := hW.vC_contDiff.of_le (by norm_num)
  have hderiv_f : deriv f = ψ := by
    funext u
    exact (((hW.contDiff.differentiable (by norm_num) u).hasDerivAt).ofReal_comp).deriv
  have hψ_cont : Continuous ψ :=
    Complex.continuous_ofReal.comp (hW.contDiff.continuous_deriv (by norm_num))
  have hψ_supp : ∀ u, L / 2 ≤ |u| → ψ u = 0 := fun u hu => by
    simp only [ψ, admWindow_deriv_eq_zero hW hu, Complex.ofReal_zero]
  have hparseval := RHTower.sum_norm_sq_paperFT_grid_le hW.L_pos hψ_cont hψ_supp γ T t
  have hpt : ∀ k ∈ t,
      (T / 4) * (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
        ≤ ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2 := by
    intro k hk
    set r : ℝ := γ - (T + k * (2 * Real.pi / L))
    have hft := Zeta23.paperFT_deriv hf_cd1 hW.vC_hasCompactSupport (r : ℂ)
    rw [hderiv_f] at hft
    have hnorm : ‖Zeta23.paperFT ψ (r : ℂ)‖ ^ 2 = r ^ 2 * ‖Zeta23.paperFT f (r : ℂ)‖ ^ 2 := by
      rw [hft, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs]
    have hvhat : (Zeta23.AdmWindow.vHatR φ r) ^ 2 ≤ ‖Zeta23.paperFT f (r : ℂ)‖ ^ 2 := by
      have := Complex.abs_re_le_norm (Zeta23.paperFT f (r : ℂ))
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [hnorm]
    calc (T / 4) * (Zeta23.AdmWindow.vHatR φ r) ^ 2
        ≤ r ^ 2 * (Zeta23.AdmWindow.vHatR φ r) ^ 2 :=
          mul_le_mul_of_nonneg_right (hfar k hk) (sq_nonneg _)
      _ ≤ r ^ 2 * ‖Zeta23.paperFT f (r : ℂ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hvhat (sq_nonneg _)
  have hint_le : ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 ≤ L * (c / w) ^ 2 := by
    have hle : -(L / 2) ≤ L / 2 := by linarith [hW.L_pos]
    have hmono : ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2
        ≤ ∫ _ in (-(L / 2))..(L / 2), (c / w) ^ 2 := by
      apply intervalIntegral.integral_mono_on hle
        ((hψ_cont.norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const
      intro u _
      simp only [ψ, Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (admWindow_abs_deriv_le hW u) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  have hsum_le : (T / 4) * ∑ k ∈ t,
      (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
      ≤ L ^ 2 * (c / w) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ t, (T / 4) * (Zeta23.AdmWindow.vHatR φ (γ - (T + k * (2 * Real.pi / L)))) ^ 2
        ≤ ∑ k ∈ t, ‖Zeta23.paperFT ψ ((γ - (T + k * (2 * Real.pi / L)) : ℝ) : ℂ)‖ ^ 2 :=
          Finset.sum_le_sum hpt
      _ ≤ L * ∫ u in (-(L / 2))..(L / 2), ‖ψ u‖ ^ 2 := hparseval
      _ ≤ L * (L * (c / w) ^ 2) := mul_le_mul_of_nonneg_left hint_le hW.L_pos.le
      _ = L ^ 2 * (c / w) ^ 2 := by ring
  rw [le_div_iff₀ hT]
  linarith

private lemma VPhiR_phiD_close {ϱ : ℝ → ℝ} (hϱ : Zeta23.TaperProfile ϱ)
    {lam L w : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (r : ℝ) :
    |L⁻¹ * Zeta23.AdmWindow.VPhiR (Zeta23.ThmD.phiD ϱ lam L w) r
      - mtKernelNum lam (L / (2 * Real.pi) * r)| ≤ 2 * w / L := by
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hwL2 : 2 * w ≤ L := by linarith
  set φ := Zeta23.ThmD.phiD ϱ lam L w
  have hW := Zeta23.ThmD.admWindow_phiD hϱ h0 h1 hw hwL
  -- Express `VPhiR φ r` as `∫ u, φ u ^ 2 * cos (r * u)`
  have hVPhiR : Zeta23.AdmWindow.VPhiR φ r = ∫ u : ℝ, φ u ^ 2 * Real.cos (r * u) := by
    unfold Zeta23.AdmWindow.VPhiR Zeta23.AdmWindow.VPhi Zeta23.paperFT
    have hint_c : Integrable (fun u : ℝ => ((φ u ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) :=
      (hW.vSqC_continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (hW.vSqC_hasCompactSupport.mul_right)
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint_c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Complex.reCLM_apply]
    rw [show Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- Express `mtKernelNum` as `L⁻¹ * ∫ u, sharpW lam L u * cos (r * u)`
  have hsharp : mtKernelNum lam (L / (2 * Real.pi) * r)
      = L⁻¹ * ∫ u : ℝ, Zeta23.ThmD.sharpW lam L u * Real.cos (r * u) := by
    have hind : (fun u : ℝ => Zeta23.ThmD.sharpW lam L u * Real.cos (r * u))
        = (Set.Icc (-(L / 2)) (L / 2)).indicator
            (fun u => Zeta23.ThmD.vStar lam (u / L) * Real.cos (r * u)) := by
      funext u
      unfold Zeta23.ThmD.sharpW
      by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
    have hcomp := intervalIntegral.integral_comp_div
      (f := fun v => Zeta23.ThmD.vStar lam v * Real.cos (r * L * v))
      (a := -(L / 2)) (b := L / 2) hL.ne'
    have hcongr : ∫ x in (-(L / 2))..(L / 2), Zeta23.ThmD.vStar lam (x / L) * Real.cos (r * x)
        = ∫ x in (-(L / 2))..(L / 2), Zeta23.ThmD.vStar lam (x / L) * Real.cos (r * L * (x / L)) :=
      intervalIntegral.integral_congr fun x _ => by
        congr 2; field_simp
    rw [hcongr, hcomp, smul_eq_mul,
      show -(L / 2) / L = -(1 : ℝ) / 2 by field_simp,
      show (L / 2) / L = (1 : ℝ) / 2 by field_simp,
      ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
    unfold mtKernelNum
    refine intervalIntegral.integral_congr fun v _ => ?_
    congr 2
    field_simp
  rw [hVPhiR, hsharp, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  have hint_φ : Integrable (fun u : ℝ => φ u ^ 2 * Real.cos (r * u)) :=
    (hW.sq_continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hW.sq_hasCompactSupport.mul_right)
  have hint_k : Integrable (fun u : ℝ => Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)) := by
    have hk : Integrable (Zeta23.ThmD.sharpW lam L) := by
      unfold Zeta23.ThmD.sharpW
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (((by unfold Zeta23.ThmD.vStar; fun_prop :
          Continuous fun u : ℝ => Zeta23.ThmD.vStar lam (u / L)).continuousOn).integrableOn_compact
          isCompact_Icc)
    exact (hk.bdd_mul (c := 1) (by fun_prop : Continuous fun u => Real.cos (r * u)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)).congr
      (Filter.Eventually.of_forall fun u => mul_comm _ _)
  have hint_diff : Integrable (fun u : ℝ => |φ u ^ 2 - Zeta23.ThmD.sharpW lam L u|) := by
    have hk : Integrable (Zeta23.ThmD.sharpW lam L) := by
      unfold Zeta23.ThmD.sharpW
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (((by unfold Zeta23.ThmD.vStar; fun_prop :
          Continuous fun u : ℝ => Zeta23.ThmD.vStar lam (u / L)).continuousOn).integrableOn_compact
          isCompact_Icc)
    exact ((hW.integrable_pow two_pos).sub hk).abs
  rw [← MeasureTheory.integral_sub hint_φ hint_k]
  have hdiff_le : |(∫ u : ℝ, (φ u ^ 2 * Real.cos (r * u) - Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)))|
      ≤ 2 * w := by
    calc |(∫ u : ℝ, (φ u ^ 2 * Real.cos (r * u) - Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)))|
        ≤ ∫ u : ℝ, |φ u ^ 2 * Real.cos (r * u) - Zeta23.ThmD.sharpW lam L u * Real.cos (r * u)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ, |φ u ^ 2 - Zeta23.ThmD.sharpW lam L u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => abs_nonneg _) hint_diff
            (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← sub_mul, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ 2 * w := Zeta23.ThmD.integral_abs_phiDsq_sub_sharp hϱ h0 h1 hw0 hwL2
  rw [div_eq_mul_inv, mul_comm (2 * w)]
  exact mul_le_mul_of_nonneg_left hdiff_le (inv_nonneg.mpr hL.le)

/-- Uniform finite-height error, with independent cosine shape and bandwidth. -/
theorem pairGridOverlap_cosineParams_error (Z : Zeta23.ZeroConfig)
    {P : Zeta23.Params} (hϱ : Zeta23.TaperProfile P.ϱ)
    {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w)
    (hT16 : 16 ≤ T) (hLw : 16 * P.w ≤ P.L T) (hLpi : 2 * Real.pi ≤ P.L T)
    (x y : Zeta23.ZeroSide.ZI Z T)
    (hx_lo : T + Real.sqrt T ≤ (x : ℂ).im) (hx_hi : (x : ℂ).im ≤ 2 * T - Real.sqrt T)
    (hy_lo : T + Real.sqrt T ≤ (y : ℂ).im) (hy_hi : (y : ℂ).im ≤ 2 * T - Real.sqrt T) :
    |pairGridOverlap Z (cosineParams P κ T) T x y
      - mtKernel κ (P.L T / (2 * Real.pi) * |(x : ℂ).im - (y : ℂ).im|)|
      ≤ 16 * (Zeta23.ThmD.cDT P.ϱ κ / P.w) ^ 2 / T + 24 * P.w / P.L T := by
  set c := Zeta23.ThmD.cDT P.ϱ κ
  have hT_pos : 0 < T := by linarith
  have h8w : 8 * P.w ≤ P.L T := by linarith [hw]
  have hL_pos : 0 < P.L T := by linarith [hw]
  have hsqrt4 : 4 ≤ Real.sqrt T := by
    rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
    exact Real.sqrt_le_sqrt hT16
  have hhgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2 := by
    have h1 : 2 * Real.pi ≤ P.L T := hLpi
    have h2 : 2 * Real.pi / P.L T ≤ 1 := (div_le_one hL_pos).mpr h1
    linarith
  set φ := Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w
  set L := P.L T
  have hW : Zeta23.AdmWindow φ L P.w c := Zeta23.ThmD.admWindow_phiD hϱ hκ hκ1 hw h8w
  -- Identify `(cosineParams P κ T).phiHatR` and `(cosineParams P κ T).a`
  have hphi_eq : (cosineParams P κ T).phi T = φ := cosineParams_phi (by linarith : P.w ≠ 0)
  have hphiHatR_eq : ∀ r : ℝ, (cosineParams P κ T).phiHatR T r = Zeta23.AdmWindow.vHatR φ r := fun r => by
    unfold Zeta23.Params.phiHatR Zeta23.Params.phiHat Zeta23.AdmWindow.vHatR Zeta23.AdmWindow.vHat
    rw [hphi_eq]
  have ha_eq : (cosineParams P κ T).a T = L⁻¹ * ∫ u, φ u ^ 2 := by
    change (P.L T)⁻¹ * (∫ u, ((cosineParams P κ T).phi T u) ^ 2) = _
    rw [hphi_eq]
  set aD := (cosineParams P κ T).a T
  obtain ⟨haStar_lo, haStar_hi⟩ := aStar_bounds hκ.le hκ1
  have haD_close : |aD - Zeta23.ThmD.aStar κ| ≤ 4 * P.w / L := by
    rw [ha_eq]
    exact Zeta23.ThmD.aD_close hϱ hκ hκ1 hw h8w
  have hwL_small : 4 * P.w / L ≤ 1 / 4 := by
    rw [div_le_iff₀ hL_pos]; linarith [Real.pi_pos]
  have haD_lo : 1 / 4 ≤ aD := by linarith [(abs_le.mp haD_close).1]
  have haD_pos : 0 < aD := by linarith
  -- Omitted grid nodes lie beyond the bulk boundary margin.
  set d := P.d T
  set s : Finset ℤ := Finset.univ.image (fun k : Fin d => ((k : ℕ) : ℤ))
  have hinj : Function.Injective (fun k : Fin d => ((k : ℕ) : ℤ)) := by
    intro a b h; simp only [Nat.cast_inj] at h; exact Fin.ext h
  have hfar_of_bulk : ∀ γ : ℝ, T + Real.sqrt T ≤ γ → γ ≤ 2 * T - Real.sqrt T →
      ∀ k : ℤ, k ∉ s → T / 4 ≤ (γ - (T + k * (2 * Real.pi / L))) ^ 2 := by
    intro γ hγ_lo hγ_hi k hk_not
    have hk_cases : k < 0 ∨ (d : ℤ) ≤ k := by
      by_contra h
      rw [not_or, not_lt, not_le] at h
      apply hk_not
      rw [Finset.mem_image]
      refine ⟨⟨k.toNat, ?_⟩, Finset.mem_univ _, ?_⟩
      · have hk_nn : 0 ≤ k := h.1
        have hlt : k < (d : ℤ) := h.2
        omega
      · simp [Int.toNat_of_nonneg h.1]
    have hstep_pos : 0 < 2 * Real.pi / L := by positivity
    have hdiff_ge : Real.sqrt T / 2 ≤ |γ - (T + k * (2 * Real.pi / L))| := by
      rcases hk_cases with hk_neg | hk_ge
      · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
        have hkmul : (k : ℝ) * (2 * Real.pi / L) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hstep_pos.le
        have : Real.sqrt T / 2 ≤ γ - (T + k * (2 * Real.pi / L)) := by linarith [Real.sqrt_nonneg T]
        exact this.trans (le_abs_self _)
      · have hk_ge_r : (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
        have hd_gt : L * T / (2 * Real.pi) - 1 < (d : ℝ) :=
          Nat.sub_one_lt_floor (L * T / (2 * Real.pi))
        have htau_gt : 2 * T - 2 * Real.pi / L < T + (k : ℝ) * (2 * Real.pi / L) := by
          have h1 : (L * T / (2 * Real.pi) - 1) * (2 * Real.pi / L)
              < (k : ℝ) * (2 * Real.pi / L) :=
            mul_lt_mul_of_pos_right (hd_gt.trans_le hk_ge_r) hstep_pos
          have h2 : (L * T / (2 * Real.pi) - 1) * (2 * Real.pi / L) = T - 2 * Real.pi / L := by
            field_simp
          linarith
        have : Real.sqrt T / 2 ≤ -(γ - (T + k * (2 * Real.pi / L))) := by linarith
        exact this.trans (neg_le_abs _)
    have hsq := pow_le_pow_left₀ (by positivity) hdiff_ge 2
    rw [sq_abs, div_pow, Real.sq_sqrt hT_pos.le] at hsq
    linarith
  set γx := (x : ℂ).im
  set γy := (y : ℂ).im
  set g : ℤ → ℝ := fun k =>
    Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))
      * Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))
  have hhasSum : HasSum g (L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) :=
    hW.hasSum_vHatR_mul T γx γy
  have htail_fin : ∀ u : Finset ℤ, s ⊆ u →
      |(∑ k ∈ u, g k) - ∑ k ∈ s, g k| ≤ 4 * L ^ 2 * (c / P.w) ^ 2 / T := by
    intro u hsu
    rw [← Finset.sum_sdiff hsu, add_sub_cancel_right]
    set t := u \ s
    have ht_not : ∀ k ∈ t, k ∉ s := fun k hk => (Finset.mem_sdiff.mp hk).2
    have htx := admWindow_grid_tail_sq_le hW hT_pos t
      (fun k hk => hfar_of_bulk γx hx_lo hx_hi k (ht_not k hk))
    have hty := admWindow_grid_tail_sq_le hW hT_pos t
      (fun k hk => hfar_of_bulk γy hy_lo hy_hi k (ht_not k hk))
    have hcs : |∑ k ∈ t, g k|
        ≤ (∑ k ∈ t, (Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))) ^ 2
            + ∑ k ∈ t, (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))) ^ 2) / 2 := by
      calc |∑ k ∈ t, g k| ≤ ∑ k ∈ t, |g k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ t, ((Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))) ^ 2
              + (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))) ^ 2) / 2 := by
            refine Finset.sum_le_sum fun k _ => ?_
            simp only [g, abs_mul]
            have ha := abs_nonneg (Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L))))
            have hb := abs_nonneg (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L))))
            nlinarith [sq_nonneg (|Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))|
              - |Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L)))|),
              sq_abs (Zeta23.AdmWindow.vHatR φ (γx - (T + k * (2 * Real.pi / L)))),
              sq_abs (Zeta23.AdmWindow.vHatR φ (γy - (T + k * (2 * Real.pi / L))))]
        _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have hhasSum_tendsto : Tendsto (fun u : Finset ℤ => |(∑ k ∈ u, g k) - ∑ k ∈ s, g k|) atTop
      (𝓝 |(L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k|) :=
    (hhasSum.sub_const (∑ k ∈ s, g k)).abs
  have htail_full : |(L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k|
      ≤ 4 * L ^ 2 * (c / P.w) ^ 2 / T :=
    le_of_tendsto hhasSum_tendsto
      ((eventually_ge_atTop s).mono fun u hu => htail_fin u hu)
  -- Identify `pairGridOverlap` with `(aD * L ^ 2)⁻¹ * ∑ k ∈ s, g k`
  have hoverlap_eq : pairGridOverlap Z (cosineParams P κ T) T x y = (aD * L ^ 2)⁻¹ * ∑ k ∈ s, g k := by
    unfold pairGridOverlap
    change (aD * L ^ 2)⁻¹ * _ = _
    congr 1
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hphiHatR_eq, hphiHatR_eq]
    rfl
  set Ifull := L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) / aD
  have hstep1 : |pairGridOverlap Z (cosineParams P κ T) T x y - Ifull|
      ≤ 4 * (c / P.w) ^ 2 / (aD * T) := by
    rw [hoverlap_eq]
    have heq : (aD * L ^ 2)⁻¹ * (∑ k ∈ s, g k) - Ifull
        = -((aD * L ^ 2)⁻¹ * ((L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k)) := by
      simp only [Ifull]
      field_simp
      ring
    rw [heq, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < (aD * L ^ 2)⁻¹)]
    calc (aD * L ^ 2)⁻¹ * |(L * Zeta23.AdmWindow.VPhiR φ (γx - γy)) - ∑ k ∈ s, g k|
        ≤ (aD * L ^ 2)⁻¹ * (4 * L ^ 2 * (c / P.w) ^ 2 / T) :=
          mul_le_mul_of_nonneg_left htail_full (by positivity)
      _ = 4 * (c / P.w) ^ 2 / (aD * T) := by field_simp
  -- Taper and normalization errors compare the full grid with the cosine kernel.
  set Δ := L / (2 * Real.pi) * (γx - γy)
  have hV_close : |L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum κ Δ|
      ≤ 2 * P.w / L :=
    VPhiR_phiD_close hϱ hκ hκ1 hw h8w (γx - γy)
  have hN_le : |mtKernelNum κ Δ| ≤ Zeta23.ThmD.aStar κ :=
    abs_mtKernelNum_le_aStar hκ.le hκ1 Δ
  have haStar_pos : 0 < Zeta23.ThmD.aStar κ := by linarith
  have hstep2 : |Ifull - mtKernel κ Δ| ≤ 6 * P.w / (aD * L) := by
    simp only [Ifull, mtKernel]
    have hfrac : L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) / aD
        - mtKernelNum κ Δ / Zeta23.ThmD.aStar κ
        = ((L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum κ Δ)
              * Zeta23.ThmD.aStar κ
            + mtKernelNum κ Δ * (Zeta23.ThmD.aStar κ - aD))
          / (aD * Zeta23.ThmD.aStar κ) := by
      field_simp
      ring
    rw [hfrac, abs_div, abs_of_pos (mul_pos haD_pos haStar_pos),
      div_le_div_iff₀ (mul_pos haD_pos haStar_pos) (mul_pos haD_pos hL_pos)]
    have htri := abs_add_le
      ((L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum κ Δ) * Zeta23.ThmD.aStar κ)
      (mtKernelNum κ Δ * (Zeta23.ThmD.aStar κ - aD))
    rw [abs_mul, abs_mul, abs_of_pos haStar_pos, abs_sub_comm (Zeta23.ThmD.aStar κ) aD] at htri
    have h1 : |L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum κ Δ|
        * Zeta23.ThmD.aStar κ ≤ (2 * P.w / L) * Zeta23.ThmD.aStar κ :=
      mul_le_mul_of_nonneg_right hV_close haStar_pos.le
    have h2 : |mtKernelNum κ Δ| * |aD - Zeta23.ThmD.aStar κ|
        ≤ Zeta23.ThmD.aStar κ * (4 * P.w / L) :=
      mul_le_mul hN_le haD_close (abs_nonneg _) haStar_pos.le
    have hsum : (2 * P.w / L) * Zeta23.ThmD.aStar κ + Zeta23.ThmD.aStar κ * (4 * P.w / L)
        = (6 * P.w / L) * Zeta23.ThmD.aStar κ := by ring
    have hnum_le : |(L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum κ Δ)
          * Zeta23.ThmD.aStar κ + mtKernelNum κ Δ * (Zeta23.ThmD.aStar κ - aD)|
        ≤ (6 * P.w / L) * Zeta23.ThmD.aStar κ := by linarith
    calc |(L⁻¹ * Zeta23.AdmWindow.VPhiR φ (γx - γy) - mtKernelNum κ Δ)
            * Zeta23.ThmD.aStar κ + mtKernelNum κ Δ * (Zeta23.ThmD.aStar κ - aD)|
          * (aD * L)
        ≤ ((6 * P.w / L) * Zeta23.ThmD.aStar κ) * (aD * L) :=
          mul_le_mul_of_nonneg_right hnum_le (by positivity)
      _ = 6 * P.w * (aD * Zeta23.ThmD.aStar κ) := by field_simp
  -- Evenness removes the orientation of the ordinate gap.
  have hK_abs : mtKernel κ (L / (2 * Real.pi) * |γx - γy|) = mtKernel κ Δ := by
    have : L / (2 * Real.pi) * |γx - γy| = |Δ| := by
      simp only [Δ]
      rw [abs_mul, abs_of_pos (by positivity : 0 < L / (2 * Real.pi))]
    rw [this, mtKernel_abs]
  rw [hK_abs]
  have hsmall1 : 4 * (c / P.w) ^ 2 / (aD * T) ≤ 16 * (c / P.w) ^ 2 / T := by
    calc 4 * (c / P.w) ^ 2 / (aD * T)
        ≤ 4 * (c / P.w) ^ 2 / ((1 / 4) * T) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_right haD_lo hT_pos.le)
      _ = _ := by ring
  have hsmall2 : 6 * P.w / (aD * L) ≤ 24 * P.w / L := by
    calc 6 * P.w / (aD * L) ≤ 6 * P.w / ((1 / 4) * L) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_right haD_lo hL_pos.le)
      _ = _ := by ring
  exact (abs_sub_le _ Ifull _).trans (add_le_add (hstep1.trans hsmall1) (hstep2.trans hsmall2))

/-- Bulk overlap convergence holds for every positive bandwidth and every error tolerance. -/
theorem eventually_pairGridOverlap_cosineParams_close (Z : Zeta23.ZeroConfig)
    {P : Zeta23.Params} (hϱ : Zeta23.TaperProfile P.ϱ) (hlam : 0 < P.lam)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ x y : Zeta23.ZeroSide.ZI Z T,
      T + Real.sqrt T ≤ (x : ℂ).im → (x : ℂ).im ≤ 2 * T - Real.sqrt T →
      T + Real.sqrt T ≤ (y : ℂ).im → (y : ℂ).im ≤ 2 * T - Real.sqrt T →
      |pairGridOverlap Z (cosineParams P κ T) T x y
        - mtKernel κ (P.L T / (2 * Real.pi) * |(x : ℂ).im - (y : ℂ).im|)| ≤ ε := by
  have hLtop := Zeta23.Assembly.tendsto_L_atTop P hlam
  set C := 16 * (Zeta23.ThmD.cDT P.ϱ κ / P.w) ^ 2
  filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_ge_atTop (2 * C / ε),
    hLtop.eventually_ge_atTop (16 * P.w), hLtop.eventually_ge_atTop (2 * Real.pi),
    hLtop.eventually_ge_atTop (48 * P.w / ε)] with T hT hTC hLw hLpi hLε
  intro x y hx₁ hx₂ hy₁ hy₂
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < P.L T := by linarith [Real.pi_pos]
  have he₁ : C / T ≤ ε / 2 := by
    have h := (div_le_iff₀ hε).mp hTC
    rw [div_le_iff₀ hT0]
    nlinarith only [h]
  have he₂ : 24 * P.w / P.L T ≤ ε / 2 := by
    have h := (div_le_iff₀ hε).mp hLε
    rw [div_le_iff₀ hL0]
    nlinarith only [h]
  exact (pairGridOverlap_cosineParams_error Z hϱ hκ hκ1 hw hT hLw hLpi
    x y hx₁ hx₂ hy₁ hy₂).trans (by linarith only [he₁, he₂])

/-- Poisson normalization for the frozen cosine window, independent of bandwidth. -/
theorem cosineParams_poissonSq {P : Zeta23.Params} (hϱ : Zeta23.TaperProfile P.ϱ)
    {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) (hLw : 8 * P.w ≤ P.L T) :
    Zeta23.ZeroSide.PoissonSq T (cosineParams P κ T) := by
  have hW := Zeta23.ThmD.admWindow_phiD hϱ hκ hκ1 hw hLw
  have hφ := cosineParams_phi (P := P) (κ := κ) (T := T) (by linarith : P.w ≠ 0)
  intro γ
  have h := hW.hasSum_vHatR_mul T γ γ
  rw [sub_self, hW.VPhiR_zero] at h
  have ha : (cosineParams P κ T).a T =
      Zeta23.AdmWindow.av (Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w) (P.L T) := by
    change (P.L T)⁻¹ * (∫ u, ((cosineParams P κ T).phi T u) ^ 2) = _
    rw [hφ]
    rfl
  have hhat (r : ℝ) : (cosineParams P κ T).phiHatR T r =
      Zeta23.AdmWindow.vHatR (Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w) r := by
    unfold Zeta23.Params.phiHatR Zeta23.Params.phiHat Zeta23.AdmWindow.vHatR Zeta23.AdmWindow.vHat
    rw [hφ]
  simp only [hhat, ha]
  change HasSum (fun k : ℤ => Zeta23.AdmWindow.vHatR
    (Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w) (γ - (T + k * (2 * Real.pi / P.L T))) ^ 2)
    (Zeta23.AdmWindow.av (Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w) (P.L T) * P.L T ^ 2)
  simpa only [sq, mul_left_comm, mul_assoc] using h

/-- The cosine-window normalizer stays uniformly positive once `L ≥ 16w`. -/
theorem cosineParams_mass_ge_quarter {P : Zeta23.Params} (hϱ : Zeta23.TaperProfile P.ϱ)
    {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) (hLw : 16 * P.w ≤ P.L T) :
    1 / 4 ≤ (cosineParams P κ T).a T := by
  have h8 : 8 * P.w ≤ P.L T := by linarith only [hLw, hw]
  have hL : 0 < P.L T := by linarith only [hLw, hw]
  have hclose := Zeta23.ThmD.aD_close hϱ hκ hκ1 hw h8
  have hsmall : 4 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]
    linarith only [hLw]
  have ha := (aStar_bounds hκ.le hκ1).1
  unfold Zeta23.Params.a
  rw [cosineParams_phi (by linarith : P.w ≠ 0)]
  change 1 / 4 ≤ (P.L T)⁻¹ * ∫ u, (Zeta23.ThmD.phiD P.ϱ κ (P.L T) P.w u) ^ 2
  linarith only [(abs_le.mp hclose).1, hsmall, ha]

end GaloisForLFunctions.IncommensurableGaborPinching
