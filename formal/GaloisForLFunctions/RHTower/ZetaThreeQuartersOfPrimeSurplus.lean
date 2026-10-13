import GaloisForLFunctions.RHTower.ZetaThreeQuartersOfSurplus
import GaloisForLFunctions.RHTower.ZetaPrimePoleCross

/-!
# Three quarters on the line from the prime-pair surplus

The surplus of the bandwidth-`4/3` Frobenius norm (`frobSurplus`) is the prime surplus (`primeSurplus`:
off-diagonal prime pairs, sum frequencies and the end correction of the grid) plus twice the prime–pole
cross term (`frobSurplus_eq_primeSurplus`).  The cross term is `O(T^{5/6} log² T)` unconditionally
(`abs_Mform_PX_PiX_le`, here at bandwidth `4/3` with resonance width `T^{−1/2}`), so the hypothesis

`PrimeSurplusFourThirds`: the prime surplus is at most `1/18 + ε` of `(aL)² Tℓ₁/2π` for all large `T`

implies the surplus hypothesis (`surplusFourThirds_of_primeSurplus`), hence three quarters of the zeros
simple and on the line (`zeta_three_quarters_of_prime_surplus`,
`zeta_three_quarters_simple_of_prime_surplus`).
-/

open MeasureTheory Real Filter Topology Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

/-- **The prime surplus**: off-diagonal prime pairs, sum frequencies and the end correction. -/
def primeSurplus (p : Setting) (F : LocalFun) : ℝ :=
  (1 / (2 * π ^ 2)) * (ppOffDiag F.Phi p.T p.X + ppSumFreq F.Phi p.T p.X)
    + endForm p F (Zeta23.nuX p.X) (Zeta23.nuX p.X)

theorem frobSurplus_eq_primeSurplus (p : Setting) (F : LocalFun) :
    frobSurplus p F = primeSurplus p F + 2 * Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X) := by
  unfold frobSurplus primeSurplus; ring

/-- **The prime-surplus hypothesis at bandwidth `4/3`.** -/
def PrimeSurplusFourThirds : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    primeSurplus (params43.toSetting T) (params43.localFun T)
      ≤ (1 / 18 + ε) * (params43.a T * params43.L T) ^ 2 * (T * ell1 T / (2 * π))

/-- **The prime–pole cross term at bandwidth `4/3`**: `2|𝓜[P_X, Π_X]| ≤ (320/3) log²T · T^{5/6}` for all
large `T`. -/
theorem abs_Mform_PX_PiX_params43_le :
    ∀ᶠ T in atTop,
      2 * |Mform (params43.PhiR T) T (Zeta23.PX (params43.X T)) (Zeta23.PiX (params43.X T))|
        ≤ 320 / 3 * (Real.log T ^ 2 * T ^ (5 / 6 : ℝ)) := by
  have hP := paramsValidFam_params43
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨x₀, hx₀⟩ := paperInputs_zeta.cheb.cheb1b
  have hπ := Real.pi_pos
  have hl := Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity : (0:ℝ) < 2 * π))
  filter_upwards [eventually_ge_atTop TL, eventually_ge_atTop 1, eventually_l_bounds,
    hl.eventually_ge_atTop (|x₀| + 3)] with T hTL' hT1 ⟨hlog1, hl1, hlo, hhi⟩ hlbig
  have hF := hTL T hTL'
  set l := Zeta23.l T with hldef
  have hlbig' : |x₀| + 3 ≤ l := hlbig
  set L := params43.L T with hLdef
  set X := params43.X T with hXdef
  have hLl : L = 4 / 3 * l := rfl
  have hXL : X = Real.exp L := rfl
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ L := by rw [hLl]; linarith
  have hX3 : 3 ≤ X := by
    rw [hXL]
    have h1 : l + 1 ≤ Real.exp l := Real.add_one_le_exp l
    have h2 : Real.exp l ≤ Real.exp L := Real.exp_le_exp.mpr (by rw [hLl]; linarith)
    linarith [abs_nonneg x₀]
  have hXx₀ : x₀ ≤ X := by
    rw [hXL]
    have h1 : l + 1 ≤ Real.exp l := Real.add_one_le_exp l
    have h2 : Real.exp l ≤ Real.exp L := Real.exp_le_exp.mpr (by rw [hLl]; linarith)
    linarith [le_abs_self x₀]
  have hsum : ∑ n ∈ primeRange X, acoef n ≤ 3 * Real.sqrt X := by
    have := hx₀ X hXx₀
    unfold primeRange acoef; exact this
  have hlogX : Real.log X = L := by rw [hXL, Real.log_exp]
  -- the resonance width `δ = T^{−1/2}`
  set δ := T ^ (-(1 / 2) : ℝ) with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hT0 _
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
  have hΦ : Continuous (params43.PhiR T) := hF.Phi_contDiff.continuous
  have h := abs_Mform_PX_PiX_le hΦ hF.Phi_sq_integrable hX3 hT1 hδ0 hδ1 hsum
  have hW : ∫ x, params43.PhiR T x ^ 2 ≤ 2 * π * L := hF.integral_Phi_sq_le
  have hXT : X ≤ T ^ (4 / 3 : ℝ) := exp_lam_l_le (lam := 4 / 3) (by norm_num) hT0 hhi
  -- `X/(T δ) ≤ T^{5/6}` and `X δ ≤ T^{5/6}`
  have hTδ : T * δ = T ^ (1 / 2 : ℝ) := by
    rw [hδ, ← Real.rpow_one_add' hT0.le (by norm_num)]; norm_num
  have h56 : T ^ (4 / 3 : ℝ) = T ^ (5 / 6 : ℝ) * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hT12 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hA : X / (T * δ) ≤ T ^ (5 / 6 : ℝ) := by
    rw [hTδ, div_le_iff₀ hT12, ← h56]; exact hXT
  have hB : X * δ ≤ T ^ (5 / 6 : ℝ) := by
    have e : T ^ (4 / 3 : ℝ) * δ = T ^ (5 / 6 : ℝ) := by
      rw [hδ, ← Real.rpow_add hT0]; norm_num
    rw [← e]; exact mul_le_mul_of_nonneg_right hXT hδ0.le
  have hT56 : 1 ≤ T ^ (5 / 6 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hLT : L ≤ 4 / 3 * Real.log T := by rw [hLl]; linarith
  -- assemble
  rw [hlogX] at h
  have hW0 : 0 ≤ ∫ x, params43.PhiR T x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hbr : 9 * X / (π * T * δ) + 6 * L * (X * δ + 1) ≤ 15 * L * T ^ (5 / 6 : ℝ) := by
    have h1 : 9 * X / (π * T * δ) ≤ 3 * T ^ (5 / 6 : ℝ) := by
      have e : 9 * X / (π * T * δ) = 9 / π * (X / (T * δ)) := by field_simp
      rw [e]
      have h9 : 9 / π ≤ 3 := by rw [div_le_iff₀ hπ]; linarith [Real.pi_gt_three]
      exact mul_le_mul h9 hA (div_nonneg (by linarith) (by positivity)) (by norm_num)
    have h2 : 6 * L * (X * δ + 1) ≤ 12 * L * T ^ (5 / 6 : ℝ) := by
      have h3 : X * δ + 1 ≤ 2 * T ^ (5 / 6 : ℝ) := by linarith only [hB, hT56]
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith only [hL1] : (0:ℝ) ≤ 6 * L)
      linarith only [h4]
    have h5 : 3 * T ^ (5 / 6 : ℝ) ≤ 3 * L * T ^ (5 / 6 : ℝ) := by
      have := mul_le_mul_of_nonneg_right hL1 (by positivity : (0:ℝ) ≤ 3 * T ^ (5 / 6 : ℝ))
      linarith only [this]
    linarith only [h1, h2, h5]
  have hfin : |Mform (params43.PhiR T) T (Zeta23.PX X) (Zeta23.PiX X)|
      ≤ 2 * L * (15 * L * T ^ (5 / 6 : ℝ)) := by
    refine h.trans ?_
    have hWπ : (∫ x, params43.PhiR T x ^ 2) / π ≤ 2 * L := by
      rw [div_le_iff₀ hπ]; linarith
    exact mul_le_mul hWπ hbr (by positivity) (by positivity)
  have hLsq : L ^ 2 ≤ 16 / 9 * Real.log T ^ 2 := by
    have h1 := pow_le_pow_left₀ (by linarith only [hL1]) hLT 2
    have e : (4 / 3 * Real.log T) ^ 2 = 16 / 9 * Real.log T ^ 2 := by ring
    linarith only [h1, e]
  have e1 : 2 * L * (15 * L * T ^ (5 / 6 : ℝ)) = 30 * (L ^ 2 * T ^ (5 / 6 : ℝ)) := by ring
  have m : L ^ 2 * T ^ (5 / 6 : ℝ) ≤ 16 / 9 * Real.log T ^ 2 * T ^ (5 / 6 : ℝ) :=
    mul_le_mul_of_nonneg_right hLsq (by positivity)
  have e2 : 320 / 3 * (Real.log T ^ 2 * T ^ (5 / 6 : ℝ))
      = 60 * (16 / 9 * Real.log T ^ 2 * T ^ (5 / 6 : ℝ)) := by ring
  linarith only [hfin, e1, m, e2]

/-- **The prime-surplus hypothesis gives the surplus hypothesis.** -/
theorem surplusFourThirds_of_primeSurplus (h : PrimeSurplusFourThirds) : SurplusFourThirds := by
  intro ε hε
  have hπ := Real.pi_pos
  have hc : (0:ℝ) < ε / (9 * π) := by positivity
  obtain ⟨TL, hTLf⟩ := localHypsCoreW_eventually_fam paramsValidFam_params43
  have hs : (5:ℝ) / 6 < 1 := by norm_num
  have hK : (0:ℝ) ≤ 320 / 3 := by norm_num
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [h (ε / 2) hε2, abs_Mform_PX_PiX_params43_le,
    eventually_log_pow_rpow_le 2 hs hK hc, eventually_l_bounds, eventually_ge_atTop 1,
    eventually_ge_atTop TL] with T hS hcross hrate ⟨hlog1, hl1, hlo, hhi⟩ hT1 hTL
  have hT0 : 0 < T := by linarith
  set l := Zeta23.l T
  set a := params43.a T
  set D := (a * params43.L T) ^ 2 * (T * ell1 T / (2 * π)) with hD
  have hLl : params43.L T = 4 / 3 * l := rfl
  have hw : params43.w = 1 := rfl
  have hwL : 8 * params43.w ≤ params43.L T := by
    have h8 : 8 ≤ params43.L T := (hTLf T hTL).eight_le_L
    rw [hw]; linarith
  have ha2 : 1 / 2 ≤ a := half_le_a_fam paramsValidFam_params43 hwL
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hell : ell1 T = l + (2 * Real.log 2 - 1) := by unfold ell1; ring
  have hellge : l ≤ ell1 T := by rw [hell]; linarith
  have hDlow : 2 / (9 * π) * T ≤ D := by
    have h1 : (2 / 3 * l) ^ 2 ≤ (a * params43.L T) ^ 2 := by
      rw [hLl]; apply pow_le_pow_left₀ (by positivity); nlinarith
    have h2 : T * l / (2 * π) ≤ T * ell1 T / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hellge hT0.le
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : 2 / (9 * π) * T ≤ (2 / 3 * l) ^ 2 * (T * l / (2 * π)) := by
      have e : (2 / 3 * l) ^ 2 * (T * l / (2 * π)) = 2 / (9 * π) * (T * l ^ 3) := by
        field_simp; ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 1 ≤ l ^ 3 := one_le_pow₀ hl1
      nlinarith
    rw [hD]; linarith
  have hcr : 2 * Mform (params43.localFun T).Phi (params43.toSetting T).T
      (Zeta23.PX (params43.toSetting T).X) (Zeta23.PiX (params43.toSetting T).X) ≤ ε / 2 * D := by
    have h1 : 2 * Mform (params43.PhiR T) T (Zeta23.PX (params43.X T)) (Zeta23.PiX (params43.X T))
        ≤ 320 / 3 * (Real.log T ^ 2 * T ^ (5 / 6 : ℝ)) := by
      have := le_abs_self (Mform (params43.PhiR T) T (Zeta23.PX (params43.X T))
        (Zeta23.PiX (params43.X T)))
      linarith
    have h2 : 320 / 3 * (Real.log T ^ 2 * T ^ (5 / 6 : ℝ)) ≤ ε / (9 * π) * T := by
      have e : 320 / 3 * (Real.log T ^ 2 * T ^ (5 / 6 : ℝ)) = 320 / 3 * Real.log T ^ 2 * T ^ (5 / 6 : ℝ) := by
        ring
      linarith
    have h3 : ε / (9 * π) * T = ε / 2 * (2 / (9 * π) * T) := by field_simp
    have h4 := mul_le_mul_of_nonneg_left hDlow (by positivity : (0:ℝ) ≤ ε / 2)
    exact (h1.trans h2).trans (h3 ▸ h4)
  rw [frobSurplus_eq_primeSurplus]
  have hS' : primeSurplus (params43.toSetting T) (params43.localFun T) ≤ (1 / 18 + ε / 2) * D := by
    rw [hD, ← mul_assoc]; exact hS
  have e : (1 / 18 + ε) * (a * params43.L T) ^ 2 * (T * ell1 T / (2 * π))
      = (1 / 18 + ε / 2) * D + ε / 2 * D := by rw [hD]; ring
  rw [e]
  linarith

/-- **Three quarters on the line from the prime-surplus hypothesis.** -/
theorem zeta_three_quarters_of_prime_surplus (h : PrimeSurplusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  zeta_three_quarters_of_surplus (surplusFourThirds_of_primeSurplus h)

/-- **…and three quarters simple and on the line.** -/
theorem zeta_three_quarters_simple_of_prime_surplus (h : PrimeSurplusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  zeta_three_quarters_simple_of_surplus (surplusFourThirds_of_primeSurplus h)

end RHTower
