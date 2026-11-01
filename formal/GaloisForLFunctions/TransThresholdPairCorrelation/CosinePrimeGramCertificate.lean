import GaloisForLFunctions.IncommensurableGaborPinching.CosineWindowAnalyticBridge
import GaloisForLFunctions.IncommensurableGaborPinching.CosineWindowCalibration
import GaloisForLFunctions.IncommensurableGaborPinching.PositivePinchingEveryBandwidth
import GaloisForLFunctions.RHTower.ZetaThreeQuartersOfSurplus
import Zeta23.ThmD.PP

/-!
# The actual cosine prime Gram and its retained pinching credit

The diagonal uses the cosine moments b and J. Its signed surplus is evaluated
with the same window as the actual zero-side pair credit.
-/

noncomputable section
open Real Filter Topology MeasureTheory Zeta23 Zeta23.PrimeSide
open GaloisForLFunctions.IncommensurableGaborPinching
open RHTower Zeta23.ThmE Zeta23.Assembly RHLinalg

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Signed prime-Gram surplus in zero-count units for the canonical shape-one cosine window. -/
def zetaCosineFrobSurplus (lam T : ℝ) : ℝ :=
  RHTower.frobSurplus ((zetaCosineParams lam T).toSetting T)
    ((zetaCosineParams lam T).localFun T) /
      ((zetaCosineParams lam T).a T * (zetaCosineParams lam T).L T) ^ 2

/-- The archimedean and prime diagonal terms of the same cosine Gram. -/
def zetaCosineDiagonalPart (lam T : ℝ) : ℝ :=
  Mform ((zetaCosineParams lam T).PhiR T) T Zeta23.mu Zeta23.mu +
    (1 / (2 * π ^ 2)) * RHTower.ppDiag ((zetaCosineParams lam T).PhiR T) T
      ((zetaCosineParams lam T).X T) +
    2 * Mform ((zetaCosineParams lam T).PhiR T) T Zeta23.mu
      (Zeta23.PX ((zetaCosineParams lam T).X T)) +
    2 * Mform ((zetaCosineParams lam T).PhiR T) T Zeta23.mu
      (Zeta23.PiX ((zetaCosineParams lam T).X T)) +
    Mform ((zetaCosineParams lam T).PhiR T) T
      (Zeta23.PiX ((zetaCosineParams lam T).X T))
      (Zeta23.PiX ((zetaCosineParams lam T).X T))

private theorem mumu_main_retains_b {Mf b L I M₀ Cg l2 Cm SE T ell : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL : 0 ≤ L)
    (hM₀ : M₀ = T * ell / (4 * π ^ 2)) (hl2 : 0 < l2)
    (hint : I ≤ M₀ + Cg * M₀ / l2) (hM₀0 : 0 ≤ M₀)
    (hmm : Mf - 2 * π * b * L * I ≤ Cm * SE) :
    Mf ≤ T * L / (2 * π) * b * ell +
      |Cg| / (2 * π) * (T * L * ell / l2) + Cm * SE := by
  have hI : I ≤ M₀ + |Cg| * M₀ / l2 := by
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Cg) hM₀0) hl2.le
    linarith only [hint, h]
  have hup := mul_le_mul_of_nonneg_left hI
    (by positivity : 0 ≤ 2 * π * b * L)
  have herr := mul_le_mul_of_nonneg_right hb1
    (by positivity : 0 ≤ 2 * π * L * (|Cg| * M₀ / l2))
  rw [one_mul] at herr
  have hdist : 2 * π * b * L * (M₀ + |Cg| * M₀ / l2) =
      2 * π * b * L * M₀ + b * (2 * π * L * (|Cg| * M₀ / l2)) := by ring
  rw [hdist] at hup
  have he : 2 * π * b * L * M₀ + 2 * π * L * (|Cg| * M₀ / l2) =
      T * L / (2 * π) * b * ell + |Cg| / (2 * π) * (T * L * ell / l2) := by
    rw [hM₀]
    field_simp [Real.pi_ne_zero, hl2.ne']
    ring
  linarith only [hmm, hup, herr, he]

private theorem cosine_error_scales {T l L e X : ℝ}
    (hT : 0 < T) (hl : 1 ≤ l) (hlT : l ≤ T) (hL : 0 < L) (hLl : L ≤ 2 * l)
    (he0 : 0 ≤ e) (he : e ≤ 2 * l) (hX : 0 ≤ X) (hXT : Real.sqrt X ≤ T) :
    T * L * e ^ 2 / l ^ 2 ≤ 8 * (T * l ^ 2) ∧
    l ^ 2 * Real.log L ≤ 2 * (T * l ^ 2) ∧
    T * L ^ 2 ≤ 4 * (T * l ^ 2) ∧
    L ^ 3 ≤ 8 * (T * l ^ 2) ∧
    l * Real.sqrt X ≤ T * l ^ 2 ∧
    l * L * Real.sqrt X ≤ 2 * (T * l ^ 2) ∧
    L * X / T ≤ 2 * (T * l ^ 2) := by
  have hl0 : 0 < l := by linarith only [hl]
  have hls : l ≤ l ^ 2 := by nlinarith only [hl]
  have hLs : L ^ 2 ≤ 4 * l ^ 2 := by nlinarith only [hLl, hL]
  have hLX : X ≤ T ^ 2 := by nlinarith only [hXT, Real.sq_sqrt hX, Real.sqrt_nonneg X]
  have he2 : e ^ 2 ≤ 4 * l ^ 2 := by nlinarith only [he0, he]
  have h1 : T * L * e ^ 2 / l ^ 2 ≤ 8 * (T * l ^ 2) := by
    have hfirst : T * L * e ^ 2 / l ^ 2 ≤ 4 * T * L := by
      rw [div_le_iff₀ (sq_pos_of_pos hl0)]
      nlinarith only [mul_le_mul_of_nonneg_left he2 (mul_nonneg hT.le hL.le)]
    have hsecond := mul_le_mul_of_nonneg_left hLl hT.le
    have hthird := mul_le_mul_of_nonneg_left hls hT.le
    linarith only [hfirst, hsecond, hthird]
  have h2 : l ^ 2 * Real.log L ≤ 2 * (T * l ^ 2) := by
    have hlog : Real.log L ≤ 2 * T := by
      have hh := Real.log_le_sub_one_of_pos hL
      linarith only [hh, hLl, hlT]
    nlinarith only [mul_le_mul_of_nonneg_left hlog (sq_nonneg l)]
  have h3 : T * L ^ 2 ≤ 4 * (T * l ^ 2) := by
    nlinarith only [mul_le_mul_of_nonneg_left hLs hT.le]
  have h4 : L ^ 3 ≤ 8 * (T * l ^ 2) := by
    have hLT : L ≤ 2 * T := by linarith only [hLl, hlT]
    have hh := mul_le_mul hLT hLs (sq_nonneg L) (by positivity : 0 ≤ 2 * T)
    nlinarith only [hh]
  have h5 : l * Real.sqrt X ≤ T * l ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hXT hl0.le
    have hh' := mul_le_mul_of_nonneg_left hls hT.le
    nlinarith only [hh, hh']
  have h6 : l * L * Real.sqrt X ≤ 2 * (T * l ^ 2) := by
    have hh := mul_le_mul hLl hXT (Real.sqrt_nonneg X) (by positivity : 0 ≤ 2 * l)
    nlinarith only [mul_le_mul_of_nonneg_left hh hl0.le]
  have h7 : L * X / T ≤ 2 * (T * l ^ 2) := by
    rw [div_le_iff₀ hT]
    have hh := mul_le_mul hLl hLX hX (by positivity : 0 ≤ 2 * l)
    have hh' := mul_le_mul_of_nonneg_right hls (sq_nonneg T)
    nlinarith only [hh, hh']
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The actual prime diagonal retains the cosine lag moment at arbitrary bandwidth. -/
theorem sumA2g_cosine_close :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Params) (κ T : ℝ), TaperProfile P.ϱ →
      0 < κ → κ ≤ 1 → 1 ≤ P.w → 8 * P.w ≤ P.L T →
      |sumA2g (P.X T) ((cosineParams P κ T).g T) -
        (P.L T) ^ 3 / 2 * cosineWindowJ P κ T| ≤ C * (P.L T) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := ThmD.sumA2g_close paperInputs_zeta.cheb
  refine ⟨C, hC0, fun P κ T hϱ hκ hκ1 hw h8 => ?_⟩
  have hW := ThmD.admWindow_phiD hϱ hκ hκ1 hw h8
  have hφ := cosineParams_phi (P := P) (κ := κ) (T := T) (by linarith : P.w ≠ 0)
  have hgEq : (cosineParams P κ T).g T =
      AdmWindow.gv (ThmD.phiD P.ϱ κ (P.L T) P.w) := by
    unfold Params.g AdmWindow.gv
    rw [hφ]
  have hg := ThmD.gD_deriv_facts hϱ hκ hκ1 (by linarith : 0 < P.w)
    (by linarith : 2 * P.w ≤ P.L T)
  have hsupp : ∀ y : ℝ, P.L T ≤ y → (cosineParams P κ T).g T y = 0 := by
    intro y hy
    rw [hgEq]
    apply le_antisymm _ (hW.gv_nonneg y)
    calc
      _ ≤ AdmWindow.Av (ThmD.phiD P.ϱ κ (P.L T) P.w) y := hW.gv_le_Av y
      _ ≤ max (P.L T - |y|) 0 := hW.Av_le y
      _ = 0 := by
        rw [abs_of_nonneg (hW.L_pos.le.trans hy), max_eq_right (by linarith)]
  have h := hC (P.L T) (P.X T) ((cosineParams P κ T).g T)
    (by linarith : 8 ≤ P.L T) rfl
    (by rw [hgEq]; exact hg.1) (by rw [hgEq]; exact hg.2.1)
    (by rw [hgEq]; exact hg.2.2) hsupp
  have hJ : (P.L T) ^ 3 / 2 * cosineWindowJ P κ T =
      ∫ y in (0 : ℝ)..(P.L T), (cosineParams P κ T).g T y * y := by
    unfold cosineWindowJ
    field_simp [hW.L_pos.ne']
  rw [hJ]
  exact h


/-- The actual cosine diagonal has its matched moments, with an `O(T log² T)` error
through bandwidth two, including the endpoint. -/
theorem zetaCosine_diagonal_part_le (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T in atTop,
      zetaCosineDiagonalPart lam T ≤
        T * (zetaCosineParams lam T).L T / (2 * π) *
          ((zetaCosineParams lam T).b T * ell1 T ^ 2 +
            ((zetaCosineParams lam T).L T) ^ 2 *
              cosineWindowJ (paramsOf stdProfile lam) 1 T) + C * (T * Zeta23.l T ^ 2) := by
  let P := paramsOf stdProfile lam
  let cr := ThmD.cDT stdProfile 1
  have hΓ : GammaFacts := paperInputs_zeta.Gamma
  have hcheb : ChebyshevMertens := paperInputs_zeta.cheb
  obtain ⟨Cm, Tm, hCm, hm⟩ := prop_mumu_uniform_wide cr lam
  obtain ⟨CΓ, TΓ, hΓsq⟩ := hΓ.int_mu_sq
  obtain ⟨Cx, Tx, hCx, hx⟩ := prop_cross_uniform_wide cr hlam
  obtain ⟨Tμ, hμ⟩ := mu_abs_le_l hΓ
  obtain ⟨C₁, hC₁⟩ := hcheb.cheb2a
  obtain ⟨C₂, hC₂0, hC₂⟩ := sumA2g_cosine_close
  let Cd := 1 / (2 * π ^ 2) * ((1 / 2 + |C₁|) * (8 + 2 * cr))
  have hcr4 : 4 ≤ cr := ThmD.four_le_cDT taperProfile_stdProfile 1
  have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
  let C := 8 * (|CΓ| / (2 * π)) + 2 * Cm + 4 * (C₂ / π) +
    8 * Cd + 2 * Cx + 24 * π + 36 * π
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hloc := cosineParams_eventually_localHypsCoreW
    (P := P) taperProfile_stdProfile hlam (κ := 1) (by norm_num) le_rfl (by norm_num [P, paramsOf])
  filter_upwards [hloc, eventually_l_bounds,
    eventually_ge_atTop Tm, eventually_ge_atTop TΓ, eventually_ge_atTop Tx,
    eventually_ge_atTop Tμ, eventually_ge_atTop (1 : ℝ)] with T hF hlbounds hTm hTΓ hTx hTμ hTone
  obtain ⟨hlog1, hl1, hlo, hhi⟩ := hlbounds
  let Q := zetaCosineParams lam T
  let p := Q.toSetting T
  let F := Q.localFun T
  let l := Zeta23.l T
  let L := Q.L T
  let X := Q.X T
  let J := cosineWindowJ P 1 T
  change LocalHypsCoreW cr p F at hF
  have hT0 : 0 < T := by linarith only [hTone]
  have hπ := Real.pi_pos
  have hl0 : 0 < l := by linarith only [hl1]
  have hL0 : 0 < L := hF.L_pos
  have hL1 : 1 ≤ L := le_trans (by norm_num) hF.eight_le_L
  have hLl : L ≤ 2 * l := by
    change lam * l ≤ 2 * l
    exact mul_le_mul_of_nonneg_right hlam2 hl0.le
  have hXL : X = Real.exp L := rfl
  have hX2 : 2 ≤ X := by
    rw [hXL]
    have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    exact hh.trans (Real.exp_le_exp.mpr hL1)
  have hlogXL : Real.log X = L := by rw [hXL, Real.log_exp]
  have hsX : Real.sqrt X ≤ T := by
    have hh := sqrt_exp_lam_l_le (lam := lam) hlam.le hT0 hhi
    have hh' := Real.rpow_le_rpow_of_exponent_le hTone (by linarith only [hlam2] : lam / 2 ≤ 1)
    rw [Real.rpow_one] at hh'
    exact hh.trans hh'
  have hlT : l ≤ T := by linarith only [Real.log_le_sub_one_of_pos hT0, hhi]
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by linarith only [Real.log_two_gt_d9]
  have hc₁ : 2 * Real.log 2 - 1 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hell : ell1 T = l + (2 * Real.log 2 - 1) := by unfold ell1; change l + 2 * Real.log 2 - 1 = _; ring
  have hell0 : 0 ≤ ell1 T := by rw [hell]; linarith only [hl1, hc₀]
  have hell2 : ell1 T ≤ 2 * l := by rw [hell]; linarith only [hl1, hc₁]
  have hpT : p.T = T := rfl
  have hpL : p.L = L := rfl
  have hpX : p.X = X := rfl
  have hw : p.w = 1 := rfl
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hIΦ : ∫ x, F.Phi x ^ 2 ≤ 2 * π * L := hF.integral_Phi_sq_le
  -- (i) the archimedean diagonal
  have hmm := (abs_le.mp (hm 0 1 (by norm_num) le_rfl p F rfl hTm hF)).2
  rw [← mu_eq_muq, Nat.cast_one, Real.log_one, add_zero, one_pow, mul_one] at hmm
  have hint := (abs_le.mp (hΓsq T hTΓ)).2
  have hmumu := mumu_main_retains_b (Mf := Mform F.Phi p.T Zeta23.mu Zeta23.mu) (b := F.b) (L := L)
    (I := ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) (M₀ := T * ell1 T ^ 2 / (4 * π ^ 2)) (Cg := CΓ)
    (l2 := l ^ 2) (Cm := Cm) (SE := l ^ 2 * Real.log L) (T := T) (ell := ell1 T ^ 2)
    (by linarith only [hF.b_ge_half] : 0 ≤ F.b)
    (hF.b_le_a.trans hF.a_le_one) hL0.le rfl (by positivity)
    (by have e : CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / l ^ 2
            = CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / Zeta23.l T ^ 2 := rfl
        linarith only [hint, e]) (by positivity) hmm
  -- (ii) the prime diagonal
  have hdiag := (abs_le.mp (diag_estimate (Φ := F.Phi) (T := T) hT0.le hΦ hF.Phi_sq_integrable
    hF.Phi_sq_mul_abs_integrable hF.Phi_sq_fourier X)).2
  have hsum : sumA2g X F.g ≤ L ^ 3 / 2 * J + C₂ * L ^ 2 := by
    have hh := (abs_le.mp (hC₂ P 1 T taperProfile_stdProfile (by norm_num) le_rfl
      (by norm_num [P, paramsOf]) (by rw [show P.w = 1 from rfl, mul_one]; exact hF.eight_le_L))).2
    change sumA2g X F.g - L ^ 3 / 2 * J ≤ C₂ * L ^ 2 at hh
    linarith only [hh]
  have hsq := sum_acoef_sq_le_wide hC₁ hlogXL hX2
  have hsq0 : 0 ≤ ∑ n ∈ primeRange X, acoef n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hIabs := hF.integral_Phi_sq_mul_abs_le
  have hIabs0 : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  rw [hpL, hw, mul_one] at hIabs
  have hlogc : Real.log (cr * L / 4) ≤ cr * L / 4 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < cr * L / 4)
    linarith only [h]
  have hdiag' : (1 / (2 * π ^ 2)) * ppDiag F.Phi T X
      ≤ T / π * (L ^ 3 / 2 * J + C₂ * L ^ 2)
        + 1 / (2 * π ^ 2) * ((L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L)) := by
    have h1 : (1 / (2 * π ^ 2)) * ppDiag F.Phi T X
        ≤ T / π * sumA2g X F.g
          + (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x| := by
      unfold ppDiag; linarith only [hdiag]
    have h2 : T / π * sumA2g X F.g ≤ T / π * (L ^ 3 / 2 * J + C₂ * L ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3 : ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 2 * cr * L := by linarith only [hIabs, hlogc]
    have h4 : (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x|
        ≤ (L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L) :=
      mul_le_mul hsq h3 hIabs0 (hsq0.trans hsq)
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 1 / (2 * π ^ 2))
    rw [← mul_assoc] at h5
    linarith only [h1, h2, h5]
  -- (iii) the archimedean–prime cross term
  have hPX : PXc (fun _ => 1) p.X = Zeta23.PX X := funext fun τ => (PX_eq_PXc_one X τ).symm
  have hcross := hx 0 1 (by norm_num) le_rfl (fun _ => 1) coeffOK_one p F rfl hTx hF
  rw [← mu_eq_muq, hPX, Nat.cast_one, Real.log_one, add_zero, mul_one] at hcross
  -- pointwise bounds on the window
  have hμI : ∀ τ ∈ Set.Icc T (2 * T), |Zeta23.mu τ| ≤ l := fun τ hτ => hμ p hTμ τ hτ
  have hPiI : ∀ τ ∈ Set.Icc T (2 * T), |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X / T := by
    intro τ hτ
    refine (hF.PiX_bound τ).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) hT0
    rw [abs_of_nonneg (by linarith only [hτ.1, hT0])]; linarith only [hτ.1]
  -- (iv) archimedean–pole, (v) pole–pole
  have hmuPi := abs_Mform_le hT0.le hΦ hΓ.smooth.continuous hF.PiX_cont hF.Phi_sq_integrable hμI hPiI
  have hPiPi := abs_Mform_le hT0.le hΦ hF.PiX_cont hF.PiX_cont hF.Phi_sq_integrable hPiI hPiI
  have hsX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hmuPi' : |Mform F.Phi T Zeta23.mu (Zeta23.PiX X)| ≤ 6 * π * (l * L * Real.sqrt X) := by
    refine hmuPi.trans ?_
    have hc : 0 ≤ l * (3 * Real.sqrt X / T) := by positivity
    calc l * (3 * Real.sqrt X / T) * (T * ∫ x, F.Phi x ^ 2)
        ≤ l * (3 * Real.sqrt X / T) * (T * (2 * π * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIΦ hT0.le) hc
      _ = 6 * π * (l * L * Real.sqrt X) := by field_simp; ring
  have hPiPi' : |Mform F.Phi T (Zeta23.PiX X) (Zeta23.PiX X)| ≤ 18 * π * (L * X / T) := by
    refine hPiPi.trans ?_
    have hc : 0 ≤ 3 * Real.sqrt X / T * (3 * Real.sqrt X / T) := by positivity
    calc 3 * Real.sqrt X / T * (3 * Real.sqrt X / T) * (T * ∫ x, F.Phi x ^ 2)
        ≤ 3 * Real.sqrt X / T * (3 * Real.sqrt X / T) * (T * (2 * π * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIΦ hT0.le) hc
      _ = 18 * π * (L * Real.sqrt X ^ 2 / T) := by field_simp; ring
      _ = 18 * π * (L * X / T) := by rw [Real.sq_sqrt (by linarith only [hX2])]
  have hdiagError : 1 / (2 * π ^ 2) * ((L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L)) ≤ Cd * L ^ 3 := by
    have ha : L ^ 2 / 2 + C₁ * L ≤ (1 / 2 + |C₁|) * L ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self C₁) hL0.le
      have h2 := mul_le_mul_of_nonneg_left (show L ≤ L ^ 2 by nlinarith only [hL1]) (abs_nonneg C₁)
      linarith only [h1, h2]
    have hb : 8 + 2 * cr * L ≤ (8 + 2 * cr) * L := by linarith only [hL1]
    have hh := mul_le_mul ha hb (by positivity : 0 ≤ 8 + 2 * cr * L) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1 / (2 * π ^ 2))
    dsimp [Cd]
    nlinarith only [hh']
  obtain ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩ :=
    cosine_error_scales (l := l) hT0 hl1 hlT hL0 hLl hell0 hell2 (by linarith only [hX2]) hsX
  have he1 := mul_le_mul_of_nonneg_left hE1 (by positivity : 0 ≤ |CΓ| / (2 * π))
  have he2 := mul_le_mul_of_nonneg_left hE2 hCm
  have he3 := mul_le_mul_of_nonneg_left hE3 (by positivity : 0 ≤ C₂ / π)
  have he4 := mul_le_mul_of_nonneg_left hE4 hCd
  have he5 := mul_le_mul_of_nonneg_left hE5 (by positivity : 0 ≤ 2 * Cx)
  have he6 := mul_le_mul_of_nonneg_left hE6 (by positivity : 0 ≤ 12 * π)
  have he7 := mul_le_mul_of_nonneg_left hE7 (by positivity : 0 ≤ 18 * π)
  change Mform F.Phi T Zeta23.mu Zeta23.mu + (1 / (2 * π ^ 2)) * ppDiag F.Phi T X +
    2 * Mform F.Phi T Zeta23.mu (Zeta23.PX X) +
    2 * Mform F.Phi T Zeta23.mu (Zeta23.PiX X) +
    Mform F.Phi T (Zeta23.PiX X) (Zeta23.PiX X) ≤
      T * L / (2 * π) * (F.b * ell1 T ^ 2 + L ^ 2 * J) + C * (T * l ^ 2)
  have hc : Mform F.Phi T Zeta23.mu (Zeta23.PX X) ≤ Cx * (l * Real.sqrt X) :=
    (abs_le.mp hcross).2
  have hmp := (abs_le.mp hmuPi').2
  have hpp := (abs_le.mp hPiPi').2
  rw [hpT] at hmumu
  have hmain : T * L / (2 * π) * F.b * ell1 T ^ 2 + T / π * (L ^ 3 / 2 * J) =
      T * L / (2 * π) * (F.b * ell1 T ^ 2 + L ^ 2 * J) := by
    field_simp
  have hprimeError : T / π * (L ^ 3 / 2 * J + C₂ * L ^ 2) =
      T / π * (L ^ 3 / 2 * J) + (C₂ / π) * (T * L ^ 2) := by ring
  dsimp only [C]
  linarith only [hprimeError, hmain, hmumu, hdiag', hdiagError, hc, hmp, hpp, he1, he2, he3, he4, he5, he6, he7]


/-- At bandwidth at most two the actual normalized tail is uniformly bounded,
and the same cosine window satisfies the exact explicit-formula bridge. -/
theorem zetaCosine_bounded_tail (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T in atTop,
      let Q := zetaCosineParams lam T
      |rtrace (Q.hat T (zetaZeroConfig.Ez Q T))| ≤ B ∧
      frobSq (Q.hat T (zetaZeroConfig.Ez Q T)) ≤ B ^ 2 ∧
      zetaZeroConfig.Gz Q T = Q.Gp T := by
  let P := paramsOf stdProfile lam
  let c := ThmD.cDT stdProfile 1
  have hc4 : 4 ≤ c := ThmD.four_le_cDT taperProfile_stdProfile 1
  have hc : 0 ≤ c := by linarith only [hc4]
  have hP : ParamsValidFam P := ⟨taperProfile_stdProfile, hlam, by norm_num [P, paramsOf]⟩
  obtain ⟨A₀, hA₀, hloc⟩ := paperInputs_zeta.RvM.local_count
  have hA₀0 : 0 ≤ A₀ := by linarith only [hA₀]
  let B := 16 * A₀ * c ^ 2 / lam
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  have hlocal := cosineParams_eventually_localHypsCoreW (P := P)
    taperProfile_stdProfile hlam (κ := 1) (by norm_num) le_rfl (by norm_num [P, paramsOf])
  filter_upwards [hlocal, eventually_ge_atTop Tail.T₀] with T hF hT
  let Q := zetaCosineParams lam T
  have hT300 : 300 ≤ T := hT
  have hTone : 1 ≤ T := by linarith only [hT300]
  have hL : 0 < Q.L T := hF.L_pos
  have ha : 0 < Q.a T := hF.a_pos
  have ha2 : 1 / 2 ≤ Q.a T := hF.b_ge_half.trans hF.b_le_a
  have hl1 : 1 ≤ l T := hF.one_le_l
  have hl : 0 ≤ l T := by linarith only [hl1]
  have h8 : 8 * P.w ≤ P.L T := by rw [show P.w = 1 from rfl, mul_one]; exact hF.eight_le_L
  have hW := ThmD.admWindow_phiD taperProfile_stdProfile (show (0 : ℝ) < 1 by norm_num)
    le_rfl (show 1 ≤ P.w by norm_num [P, paramsOf]) h8
  have htail : Tail.TailHyp zetaZeroConfig Q T A₀ c :=
    { hT := hT
      hL := le_trans (by norm_num) hF.eight_le_L
      hA₀ := hA₀
      hloc := hloc
      hC₁ := hc
      hdecay := fun r y hy hz => cosineParams_phiHat_decay taperProfile_stdProfile
        (by norm_num) le_rfl (by norm_num [P, paramsOf]) h8 r y hy hz }
  have hinputs := htail.tailInputs ha (fun z => GzGp.phiHat_conj Q T z)
  have htheta := theta0_le_fam hP hT hA₀0 hc (R := c / 2) (by linarith)
  have hp : T ^ (lam / 2 - 1) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hTone
      (by linarith only [hlam2] : lam / 2 - 1 ≤ 0)
    simpa only [Real.rpow_zero] using hh
  have htheta' : Tail.theta0 A₀ (Real.exp (Q.L T / 4) * c) T ≤ 8 * A₀ * c ^ 2 * l T := by
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 32 * A₀ * (c / 2) ^ 2 * l T)
    change Tail.theta0 A₀ (Real.exp (Q.L T / 4) * c) T ≤
      32 * A₀ * (c / 2) ^ 2 * l T * T ^ (lam / 2 - 1) at htheta
    nlinarith only [htheta, hh]
  have hnorm : Tail.theta0 A₀ (Real.exp (Q.L T / 4) * c) T / (Q.a T * Q.L T) ≤ B := by
    rw [div_le_iff₀ (mul_pos ha hL)]
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha2 hL.le) hB
    have he : B * ((1 / 2) * Q.L T) = 8 * A₀ * c ^ 2 * l T := by
      change (16 * A₀ * c ^ 2 / lam) * ((1 / 2) * (lam * l T)) = _
      field_simp [hlam.ne']
      ring
    rw [he] at hh
    exact htheta'.trans hh
  obtain ⟨b, hb, htr, hfr, hble⟩ := hinputs.hat
  refine ⟨htr.trans (hble.trans hnorm), hfr.trans (pow_le_pow_left₀ hb (hble.trans hnorm) 2), ?_⟩
  refine zetaZeroConfig.Gz_eq_Gp Q T paperInputs_zeta.EF hL ?_ ?_
  · rw [show Q.phi T = ThmD.phiD P.ϱ 1 (P.L T) P.w from
      cosineParams_phi (by norm_num [P, paramsOf])]
    exact hW.vC_contDiff
  · rw [show Q.phi T = ThmD.phiD P.ϱ 1 (P.L T) P.w from
      cosineParams_phi (by norm_num [P, paramsOf])]
    exact closure_minimal hW.support_subset isClosed_Icc


/-- The explicit pinching credit survives transport to the actual prime Gram,
with a bounded tail coefficient even at bandwidth two. -/
theorem zetaCosine_prime_rankTrace (lam : ℝ) (hlam : 0 < lam) (hlam2 : lam ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T in atTop,
      let Q := zetaCosineParams lam T
      let F := frobSq (Q.hat T (Q.Gp T))
      4 * rtrace (Q.hat T (Q.Gp T)) - F - 2 * (zetaZeroConfig.N T (2 * T) : ℝ) -
        3 * (NII zetaZeroConfig T : ℝ) +
        (cosinePairFloor lam ^ 2 / 200) * (zetaZeroConfig.N T (2 * T) : ℝ) -
        B * (4 + 2 * Real.sqrt F + B) ≤ zetaZeroConfig.N0s T (2 * T) := by
  obtain ⟨B, hB, htail⟩ := zetaCosine_bounded_tail lam hlam hlam2
  refine ⟨B, hB, ?_⟩
  filter_upwards [htail, zetaCosine_explicit_rankTrace lam hlam] with T ht hr
  let Q := zetaCosineParams lam T
  obtain ⟨htr, hfr, hGp⟩ := ht
  have hGAE : Q.hat T (Q.Gp T) = Q.hat T (zetaZeroConfig.Az Q T) +
      Q.hat T (zetaZeroConfig.Ez Q T) := by
    rw [← hGp, ← hat_add]
    congr 1
    simp only [ZeroConfig.Ez, add_sub_cancel]
    rfl
  have hpert := four_tr_sub_frobSq_perturb hGAE hB htr hfr
  dsimp only at hr ⊢
  linarith only [hpert, hr]

end GaloisForLFunctions.TransThresholdPairCorrelation
