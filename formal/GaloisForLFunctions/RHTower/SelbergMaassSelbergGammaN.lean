import GaloisForLFunctions.RHTower.SelbergMaassSelbergBounds
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCoordIntegrable

open MeasureTheory UpperHalfPlane ModularGroup Set Complex
open scoped MatrixGroups Pointwise

/-!
# The Maass–Selberg relation for `Γ(N)`

On the coset piece `R_c 𝒟` of the `Γ(N)` cell, the truncation identity gives
`rowSum_Y(u)(R_c w) = Λ^Y_c E_u(w) + [Im w > Y] b_c(u) (Im w)^{1-u}` (`rowSum_eq`). Summing over the cosets turns
`∫ rowSum_Y(u) E_v` into an integral over the cell, which unfolds (`seed_unfold`) to the slab integral
`N Y^{u+v-1}/(u+v-1) + φ_{∞∞}(v) Y^{u-v}/(u-v)` (`sum_rowSum_eq`; the strip integrability comes from the chart,
`integrableOn_strip_seed`). The cusp pieces `∫_{𝒟, y>Y} y^{1-u} E_v(R_c ·)` reduce to `∫_Y^∞ y^{1-u} CT_c(v, y) y^{-2}`
by the zero mean of the non-constant parts over the cosets (`sum_cusp_CT_eq`), and the second truncation drops out
for the same reason. Hence, for `N ≥ 3`, `1 < Re v < Re u`, `Y ≥ 1` (`maassSelberg_region`):
`Σ_c ∫_𝒟 Λ^Y_c E_u · Λ^Y_c E_v dμ = N Y^{u+v-1}/(u+v-1) + φ_{∞∞}(v) Y^{u-v}/(u-v)
  − Σ_c b_c(u) (a_c Y^{v-u}/(u-v) + b_c(v) Y^{1-u-v}/(u+v-1))`.
-/

namespace GaloisForLFunctions.RHTower.SelbergMaassSelbergGammaN
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace
  GaloisForLFunctions.RHTower.SelbergCellCosetShift GaloisForLFunctions.RHTower.SelbergCuspConstantTerm
  GaloisForLFunctions.RHTower.SelbergMaassSelbergBounds GaloisForLFunctions.RHTower.SelbergTruncationIdentity
  GaloisForLFunctions.RHTower.SelbergMaassSelbergSlab GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
  GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergPoincarePairing
  GaloisForLFunctions.RHTower.SelbergPoincareUnfolding GaloisForLFunctions.RHTower.SelbergMaassSelbergCuspStep
  GaloisForLFunctions.RHTower.SelbergCuspZeroMean
open CongruenceSubgroup

local notation "𝐄" => GaloisForLFunctions.RHTower.SelbergPoincare.poincare

variable (N : ℕ) [NeZero N]

/-- The truncated row sum on the coset piece `R_c 𝒟`. -/
theorem rowSum_eq (c : Cosets N) {u : ℂ} (hu : 1 < u.re) {Y : ℝ} (hY : 1 ≤ Y) {w : ℍ} (hw : w ∈ fd) :
    rowSumY N u Y ((Quotient.out c : PSL2Z) • w) =
      Lc N c u Y w + if Y < w.im then bC N c u * ((w.im : ℝ) : ℂ) ^ (1 - u) else 0 := by
  have h := truncation_identity N (lift N c) hu hw hY
  rw [← lift_smul] at h
  unfold Lc
  rw [h, CT_eq]
  split_ifs <;> ring

theorem point_eq (x y : ℝ) : point x y = ⟨x, y⟩ := by apply Complex.ext <;> simp [point]

theorem integrableOn_strip_seed (hN : 3 ≤ N) {u v : ℂ} (hv : 1 < v.re) (huv : v.re < u.re) (Y : ℝ) :
    IntegrableOn (fun z => seedY u Y z * 𝐄 N 0 v z) (stripN N) volume := by
  have hA : MeasurableSet (Ico (0 : ℝ) N ×ˢ Ioi (0 : ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  rw [stripN_eq, UpperHalfPlaneCoordIntegrable.integrableOn_coord_iff hA (fun p hp => hp.2)]
  have hpt : ∀ p : ℝ × ℝ, 0 < p.2 → (ofComplex (⟨p.1, p.2⟩ : ℂ)).im = p.2 := fun p hp => by
    rw [ofComplex_apply_of_im_pos (by simpa using hp)]; rfl
  refine (integrableOn_slabG N hN hv huv Y).congr_fun (fun p hp => ?_) (measurableSet_Ico.prod measurableSet_Ioc)
    |>.of_forall_sdiff_eq_zero hA (fun p hp => ?_)
  · have hp2 : 0 < p.2 := hp.2.1
    simp only [slabG, seedY, ← point_eq]
    rw [show (ofComplex (point p.1 p.2)).im = p.2 by rw [point_eq]; exact hpt p hp2, if_pos hp.2.2]
    have hy0 : ((p.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp2.ne'
    rw [Complex.cpow_sub _ _ hy0, show ((p.2 : ℝ) : ℂ) ^ (2 : ℂ) = ((p.2 : ℝ) : ℂ) ^ (2 : ℕ) by
      rw [← Complex.cpow_natCast]; norm_num]
    field_simp
  · have hp2 : Y < p.2 := by
      have h2 : p ∉ Ico (0 : ℝ) N ×ˢ Ioc 0 Y := hp.2
      simp only [mem_prod, mem_Ioc, not_and, not_le] at h2
      exact h2 hp.1.1 hp.1.2
    simp only [seedY]
    rw [hpt p (hp.1.2), if_neg (not_le.mpr hp2), zero_mul, zero_div]

theorem integrableOn_piece_rowSum (c : Cosets N) {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) (huv : v.re < u.re)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun w => rowSumY N u Y ((Quotient.out c : PSL2Z) • w) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • w))
      fd volume := by
  have h := (integrableOn_Lc_mul_E N c hu hv huv hY).add
    ((integrableOn_above_pow_mul_E N c hv huv hY).const_mul (bC N c u))
  refine h.congr_fun (fun w hw => ?_) isClosed_fd.measurableSet
  simp only [Pi.add_apply]
  rw [rowSum_eq N c hu hY hw]
  split_ifs <;> ring

theorem integrableOn_cellP_rowSum {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) (huv : v.re < u.re)
    {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun z => rowSumY N u Y z * 𝐄 N 0 v z) (cellP N) volume := by
  haveI := GaloisForLFunctions.RHTower.SelbergCusppieceAveraging.finite_cosets N
  unfold cellP
  rw [integrableOn_finite_iUnion]
  intro c
  have h := integrableOn_piece_rowSum N c hu hv huv hY
  rw [← image_smul, (measurePreserving_smul (Quotient.out c : PSL2Z) volume).integrableOn_image
    (measurableEmbedding_const_smul _)]
  exact h

/-- **The unfolded truncated row sum**: `Σ_c ∫_𝒟 rowSum_Y(u)(R_c w) E_v(R_c w) dμ = N Y^{u+v-1}/(u+v-1) +
φ_{∞∞}(v) Y^{u-v}/(u-v)`. -/
theorem sum_rowSum_eq (hN : 3 ≤ N) {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) (huv : v.re < u.re)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ c : Cosets N, ∫ w in fd, rowSumY N u Y ((Quotient.out c : PSL2Z) • w) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • w) =
      N * (((Y : ℝ) : ℂ) ^ (u + v - 1) / (u + v - 1)) + GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry.phiσ N 1 v *
        (((Y : ℝ) : ℂ) ^ (u - v) / (u - v)) := by
  rw [← integral_finsetSum _ (fun c _ => integrableOn_piece_rowSum N c hu hv huv hY)]
  have hcell := integral_cellP_eq N (integrableOn_cellP_rowSum N hu hv huv hY)
  simp only [tsum_fintype] at hcell
  rw [← hcell]
  have hF : ∀ (h : GaloisForLFunctions.RHTower.SelbergPoincare.Hinf N) z, seedY u Y (((h : Gamma N) : SL(2, ℤ)) • z) = seedY u Y z := by
    intro h z
    obtain ⟨k, hk⟩ := Hinf_smul N h z
    have : (((h : Gamma N) : SL(2, ℤ)) • z) = h • z := rfl
    rw [this, hk]
    unfold seedY
    rw [ModularGroup.im_T_zpow_smul]
  have hg : ∀ (γ : Gamma N) z, 𝐄 N 0 v ((γ : SL(2, ℤ)) • z) = 𝐄 N 0 v z :=
    fun γ z => GaloisForLFunctions.RHTower.SelbergPoincare.poincare_smul N 0 v z γ
  have := GaloisForLFunctions.RHTower.SelbergSeedUnfolding.seed_unfold N hN hF hg
    (integrableOn_strip_seed N hN hv huv Y)
  unfold rowSumY
  rw [this, slab_eq N hN hv huv (by linarith)]

/-- A function of the height integrates over the cusp part of `𝒟` as `∫_Y^∞ h(y) y^{-2} dy`. -/
theorem cusp_height_integral {Y : ℝ} (hY : 1 ≤ Y) {h : ℝ → ℂ}
    (hint : IntegrableOn (fun p : ℝ × ℝ => h p.2 / ((p.2 : ℝ) : ℂ) ^ 2) (RHTower.cuspRect Y)) :
    ∫ z in fd ∩ {z : ℍ | Y < z.im}, h z.im = ∫ y in Ioi Y, h y / ((y : ℝ) : ℂ) ^ 2 := by
  have := cusp_iterated (Φ := fun p => h p.2) hY hint
  simp only at this
  rw [this]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  simp only
  rw [setIntegral_const, RHTower.unitIcc, measureReal_def, Real.volume_Icc]
  norm_num

theorem integral_Ioi_pow_CT {Y : ℝ} (hY : 1 ≤ Y) {u v : ℂ} (huv : v.re < u.re) (hv : 1 < v.re) (a b b' : ℂ) :
    ∫ y in Ioi Y, b * ((y : ℝ) : ℂ) ^ (1 - u) * (a * ((y : ℝ) : ℂ) ^ v + b' * ((y : ℝ) : ℂ) ^ (1 - v)) /
      ((y : ℝ) : ℂ) ^ 2 =
    b * (a * (((Y : ℝ) : ℂ) ^ (v - u) / (u - v)) + b' * (((Y : ℝ) : ℂ) ^ (1 - u - v) / (u + v - 1))) := by
  have hY0 : 0 < Y := by linarith
  have e : ∀ y ∈ Ioi Y, b * ((y : ℝ) : ℂ) ^ (1 - u) * (a * ((y : ℝ) : ℂ) ^ v + b' * ((y : ℝ) : ℂ) ^ (1 - v)) /
      ((y : ℝ) : ℂ) ^ 2 = b * a * ((y : ℝ) : ℂ) ^ (v - u - 1) + b * b' * ((y : ℝ) : ℂ) ^ (-u - v) := by
    intro y hy
    have hy0 : 0 < y := lt_trans hY0 hy
    have hyc : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have h2 : ((y : ℝ) : ℂ) ^ 2 = ((y : ℝ) : ℂ) ^ (2 : ℂ) := by rw [← Complex.cpow_natCast]; norm_num
    rw [h2]
    have e1 : ((y : ℝ) : ℂ) ^ (1 - u) * ((y : ℝ) : ℂ) ^ v = ((y : ℝ) : ℂ) ^ (v - u - 1) * ((y : ℝ) : ℂ) ^ (2 : ℂ) := by
      rw [← Complex.cpow_add _ _ hyc, ← Complex.cpow_add _ _ hyc]; ring_nf
    have e2 : ((y : ℝ) : ℂ) ^ (1 - u) * ((y : ℝ) : ℂ) ^ (1 - v) =
        ((y : ℝ) : ℂ) ^ (-u - v) * ((y : ℝ) : ℂ) ^ (2 : ℂ) := by
      rw [← Complex.cpow_add _ _ hyc, ← Complex.cpow_add _ _ hyc]; ring_nf
    have hy2 : ((y : ℝ) : ℂ) ^ (2 : ℂ) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    field_simp
    linear_combination (b * a) * e1 + (b * b') * e2
  rw [setIntegral_congr_fun measurableSet_Ioi e]
  have h1 : (v - u - 1).re < -1 := by simp; linarith
  have h2 : (-u - v).re < -1 := by simp; linarith
  rw [integral_add ((integrableOn_Ioi_cpow_of_lt h1 hY0).const_mul _) ((integrableOn_Ioi_cpow_of_lt h2 hY0).const_mul _),
    integral_const_mul, integral_const_mul, integral_Ioi_cpow_of_lt h1 hY0, integral_Ioi_cpow_of_lt h2 hY0]
  have hne1 : v - u - 1 + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne2 : -u - v + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne3 : u - v ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne4 : u + v - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [show v - u - 1 + 1 = v - u by ring, show -u - v + 1 = 1 - u - v by ring,
    show u - v = -(v - u) by ring, show u + v - 1 = -(1 - u - v) by ring, div_neg, div_neg]
  ring

theorem integrableOn_cusp_pow_CT (c : Cosets N) {u v : ℂ} (hv : 1 < v.re) (huv : v.re < u.re) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ (1 - u) * CT N c v p.2 / ((p.2 : ℝ) : ℂ) ^ 2)
      (RHTower.cuspRect Y) := by
  have hY0 : 0 < Y := by linarith
  set C := (count0 N (lift N c) : ℝ) + ‖bC N c v‖
  refine Integrable.mono' (RHTower.integrableOn_rpow_cuspRect (β := -1 - u.re + v.re) (by linarith) hY0 C) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ (RHTower.measurableSet_cuspRect Y)
    intro p hp
    have hp2 : 0 < p.2 := RHTower.cuspRect_pos hY0.le hp
    have hsnd : ContinuousAt (fun p : ℝ × ℝ => p.2) p := continuous_snd.continuousAt
    have hc : ContinuousAt (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) p := (Complex.continuous_ofReal.comp continuous_snd).continuousAt
    have hslit : ((p.2 : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hp2
    have hCT : ContinuousAt (fun p : ℝ × ℝ => CT N c v p.2) p :=
      ((continuousOn_CT N c v).continuousAt (Ioi_mem_nhds hp2)).comp hsnd
    exact (((hc.cpow continuousAt_const hslit).mul hCT).div (hc.pow 2)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hp2.ne'))).continuousWithinAt
  · refine (ae_restrict_iff' (RHTower.measurableSet_cuspRect Y)).mpr (Filter.Eventually.of_forall (fun p hp => ?_))
    have hp1 : 1 ≤ p.2 := by have := hp.2; simp only [mem_Ioi] at this; linarith
    have hp0 : 0 < p.2 := by linarith
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0, div_le_iff₀ (by positivity)]
    have hCT := norm_CT_le N c v hp0
    have hb := norm_nonneg (bC N c v)
    have e1 : p.2 ^ (1 - v.re) ≤ p.2 ^ v.re := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hCT' : ‖CT N c v p.2‖ ≤ C * p.2 ^ v.re := by
      refine hCT.trans ?_; simp only [C]; nlinarith [Real.rpow_nonneg hp0.le v.re]
    have hre : (1 - u).re = 1 - u.re := by simp
    rw [hre]
    calc p.2 ^ (1 - u.re) * ‖CT N c v p.2‖ ≤ p.2 ^ (1 - u.re) * (C * p.2 ^ v.re) :=
          mul_le_mul_of_nonneg_left hCT' (Real.rpow_nonneg hp0.le _)
      _ = C * p.2 ^ (-1 - u.re + v.re) * p.2 ^ 2 := by
          have e : p.2 ^ (-1 - u.re + v.re) * p.2 ^ 2 = p.2 ^ (1 - u.re) * p.2 ^ v.re := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hp0, ← Real.rpow_add hp0]; push_cast; ring_nf
          rw [mul_assoc C, e]; ring

/-- **The cusp constant-term integrals.** -/
theorem sum_cusp_CT_eq {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) (huv : v.re < u.re) {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ c : Cosets N, bC N c u * ∫ z in fd, (if Y < z.im then
      ((z.im : ℝ) : ℂ) ^ (1 - u) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) else 0) =
    ∑ c : Cosets N, bC N c u * ((count0 N (lift N c) : ℂ) * (((Y : ℝ) : ℂ) ^ (v - u) / (u - v)) +
      bC N c v * (((Y : ℝ) : ℂ) ^ (1 - u - v) / (u + v - 1))) := by
  have hY0 : 0 < Y := by linarith
  have hS : MeasurableSet {z : ℍ | Y < z.im} := measurableSet_above Y
  have hset : ∀ c : Cosets N, ∫ z in fd, (if Y < z.im then
      ((z.im : ℝ) : ℂ) ^ (1 - u) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) else 0) =
      ∫ z in fd ∩ {z : ℍ | Y < z.im}, ((z.im : ℝ) : ℂ) ^ (1 - u) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) := by
    intro c
    rw [← setIntegral_indicator hS]
    rfl
  -- integrability of the constant-term piece on the cusp part
  have hCTint : ∀ c : Cosets N, IntegrableOn (fun z : ℍ => ((z.im : ℝ) : ℂ) ^ (1 - u) * CT N c v z.im)
      (fd ∩ {z : ℍ | Y < z.im}) volume := by
    intro c
    rw [← RHTower.setOf_coord_cuspRect hY]
    have := (UpperHalfPlaneCoordIntegrable.integrableOn_coord_iff (RHTower.measurableSet_cuspRect Y)
      (fun p hp => RHTower.cuspRect_pos hY0.le hp) (fun z : ℍ => ((z.im : ℝ) : ℂ) ^ (1 - u) * CT N c v z.im)).mpr
    refine this ((integrableOn_cusp_pow_CT N c hv huv hY).congr_fun (fun p hp => ?_) (RHTower.measurableSet_cuspRect Y))
    have hp2 : 0 < p.2 := RHTower.cuspRect_pos hY0.le hp
    have him : (ofComplex (⟨p.1, p.2⟩ : ℂ)).im = p.2 := by
      rw [ofComplex_apply_of_im_pos (by simpa using hp2)]; rfl
    simp only [him]
  have hEint : ∀ c : Cosets N, IntegrableOn (fun z : ℍ => ((z.im : ℝ) : ℂ) ^ (1 - u) *
      𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)) (fd ∩ {z : ℍ | Y < z.im}) volume := by
    intro c
    have h := (integrableOn_above_pow_mul_E N c hv huv hY).mono_set (inter_subset_left (t := {z : ℍ | Y < z.im}))
    refine h.congr_fun (fun z hz => ?_) (isClosed_fd.measurableSet.inter hS)
    exact if_pos (show Y < z.im from hz.2)
  have hsplit : ∀ c : Cosets N, bC N c u * ∫ z in fd ∩ {z : ℍ | Y < z.im},
      ((z.im : ℝ) : ℂ) ^ (1 - u) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) =
      (∫ z in fd ∩ {z : ℍ | Y < z.im}, (if 0 < z.im then bC N c u * ((z.im : ℝ) : ℂ) ^ (1 - u) else 0) *
        (𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) - CT N c v z.im)) +
      bC N c u * ∫ y in Ioi Y, ((y : ℝ) : ℂ) ^ (1 - u) * CT N c v y / ((y : ℝ) : ℂ) ^ 2 := by
    intro c
    rw [← cusp_height_integral hY (h := fun y => ((y : ℝ) : ℂ) ^ (1 - u) * CT N c v y)
      (integrableOn_cusp_pow_CT N c hv huv hY)]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · apply setIntegral_congr_fun (isClosed_fd.measurableSet.inter hS)
      intro z _
      simp only [if_pos z.im_pos]
      ring
    · exact IntegrableOn.congr_fun (((hEint c).sub (hCTint c)).const_mul (bC N c u)) (fun z _ => by
        simp only [Pi.sub_apply, if_pos z.im_pos]; ring) (isClosed_fd.measurableSet.inter hS)
    · exact (hCTint c).const_mul _
  simp_rw [hset, hsplit]
  rw [Finset.sum_add_distrib]
  have hzero := sum_cusp_estar_zero N hv hY
    (fun c y => if 0 < y then bC N c u * ((y : ℝ) : ℂ) ^ (1 - u) else 0)
    (fun c y => by
      split_ifs
      · unfold bC; rw [(GaloisForLFunctions.RHTower.SelbergMaassSelbergBounds.coeff_sh N c hu).2]
      · rfl)
    (fun c => by
      refine ContinuousOn.congr (f := fun y : ℝ => bC N c u * ((y : ℝ) : ℂ) ^ (1 - u)) ?_ (fun y hy => if_pos hy)
      exact continuousOn_const.mul ((Complex.continuous_ofReal.continuousOn).cpow_const
        (fun y hy => Complex.ofReal_mem_slitPlane.mpr hy)))
    (a := 1 - u.re) (G := ∑ c : Cosets N, ‖bC N c u‖) (by linarith)
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun c y hy => by
      have hy0 : 0 < y := by linarith
      simp only [if_pos hy0]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      have hre : (1 - u).re = 1 - u.re := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun c => ‖bC N c u‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ c)) (Real.rpow_nonneg hy0.le _))
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  have e : ∀ y ∈ Ioi Y, ((y : ℝ) : ℂ) ^ (1 - u) * CT N c v y / ((y : ℝ) : ℂ) ^ 2 =
      1 * ((y : ℝ) : ℂ) ^ (1 - u) * ((count0 N (lift N c) : ℂ) * ((y : ℝ) : ℂ) ^ v +
        bC N c v * ((y : ℝ) : ℂ) ^ (1 - v)) / ((y : ℝ) : ℂ) ^ 2 := by
    intro y _; rw [CT_eq, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_pow_CT hY huv hv, one_mul]

/-- **The Maass–Selberg relation for `Γ(N)`** (`N ≥ 3`, `1 < Re v < Re u`, `Y ≥ 1`): the truncated pairing
`⟨Λ^Y E_∞(·, u), Λ^Y E_∞(·, v)⟩ = Σ_c ∫_𝒟 Λ^Y_c E_u · Λ^Y_c E_v dμ` equals
`N Y^{u+v-1}/(u+v-1) + φ_{∞∞}(v) Y^{u-v}/(u-v) − Σ_c b_c(u) (a_c Y^{v-u}/(u-v) + b_c(v) Y^{1-u-v}/(u+v-1))`,
with `CT_c(s, y) = a_c y^s + b_c(s) y^{1-s}` the constant term at the cusp `R_c ∞`. -/
theorem maassSelberg_region (hN : 3 ≤ N) {u v : ℂ} (hu : 1 < u.re) (hv : 1 < v.re) (huv : v.re < u.re)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ∑ c : Cosets N, ∫ z in fd, Lc N c u Y z * Lc N c v Y z =
      N * (((Y : ℝ) : ℂ) ^ (u + v - 1) / (u + v - 1)) +
        GaloisForLFunctions.RHTower.SelbergEisensteinScatteringEntry.phiσ N 1 v * (((Y : ℝ) : ℂ) ^ (u - v) / (u - v)) -
      ∑ c : Cosets N, bC N c u * ((count0 N (lift N c) : ℂ) * (((Y : ℝ) : ℂ) ^ (v - u) / (u - v)) +
        bC N c v * (((Y : ℝ) : ℂ) ^ (1 - u - v) / (u + v - 1))) := by
  have hS : MeasurableSet {z : ℍ | Y < z.im} := measurableSet_above Y
  -- Step A: remove the second truncation
  have hA : ∀ c : Cosets N, ∫ z in fd, Lc N c u Y z * Lc N c v Y z =
      (∫ z in fd, Lc N c u Y z * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)) -
        ∫ z in fd, (if Y < z.im then
          (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) * CT N c v z.im else 0) := by
    intro c
    rw [← integral_sub (integrableOn_Lc_mul_E N c hu hv huv hY) (integrableOn_above_estar_mul_CT N c hu hv huv hY)]
    apply integral_congr_ae
    filter_upwards with z
    simp only [Lc]
    split_ifs <;> ring
  -- Step B: the subtracted cusp pieces vanish in total
  have hB : ∑ c : Cosets N, ∫ z in fd, (if Y < z.im then
      (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) * CT N c v z.im else 0) = 0 := by
    have hset : ∀ c : Cosets N, ∫ z in fd, (if Y < z.im then
        (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) * CT N c v z.im else 0) =
        ∫ z in fd ∩ {z : ℍ | Y < z.im}, (if 0 < z.im then CT N c v z.im else 0) *
          (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) := by
      intro c
      rw [← setIntegral_indicator hS]
      apply setIntegral_congr_fun isClosed_fd.measurableSet
      intro z _
      simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos z.im_pos]
      split_ifs <;> ring
    simp_rw [hset]
    refine sum_cusp_estar_zero N hu hY (fun c y => if 0 < y then CT N c v y else 0)
      (fun c y => by
        by_cases hy : 0 < y
        · rw [if_pos hy, if_pos hy]; exact CT_sh N c hv hy
        · rw [if_neg hy, if_neg hy])
      (fun c => (continuousOn_CT N c v).congr (fun y hy => if_pos hy))
      (a := v.re) (G := ∑ c : Cosets N, ((count0 N (lift N c) : ℝ) + ‖bC N c v‖)) (by linarith)
      (Finset.sum_nonneg (fun c _ => by positivity)) (fun c y hy => ?_)
    have hy0 : 0 < y := by linarith
    simp only [if_pos hy0]
    refine (norm_CT_le N c v hy0).trans ?_
    have e1 : y ^ (1 - v.re) ≤ y ^ v.re := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    have hsingle := Finset.single_le_sum (f := fun c => ((count0 N (lift N c) : ℝ) + ‖bC N c v‖))
      (fun c _ => by positivity) (Finset.mem_univ c)
    have hb := norm_nonneg (bC N c v)
    have hp := Real.rpow_nonneg hy0.le v.re
    have hc0 : (0 : ℝ) ≤ (count0 N (lift N c) : ℝ) := Nat.cast_nonneg _
    calc (count0 N (lift N c) : ℝ) * y ^ v.re + ‖bC N c v‖ * y ^ (1 - v.re)
        ≤ ((count0 N (lift N c) : ℝ) + ‖bC N c v‖) * y ^ v.re := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hsingle hp
  -- Step C: the truncation identity
  have hC : ∀ c : Cosets N, ∫ z in fd, Lc N c u Y z * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) =
      (∫ z in fd, rowSumY N u Y ((Quotient.out c : PSL2Z) • z) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z)) -
        bC N c u * ∫ z in fd, (if Y < z.im then
          ((z.im : ℝ) : ℂ) ^ (1 - u) * 𝐄 N 0 v ((Quotient.out c : PSL2Z) • z) else 0) := by
    intro c
    rw [← integral_const_mul, ← integral_sub (integrableOn_piece_rowSum N c hu hv huv hY)
      ((integrableOn_above_pow_mul_E N c hv huv hY).const_mul _)]
    apply setIntegral_congr_fun isClosed_fd.measurableSet
    intro z hz
    simp only
    rw [rowSum_eq N c hu hY hz]
    split_ifs <;> ring
  simp_rw [hA, hC]
  rw [Finset.sum_sub_distrib, hB, sub_zero, Finset.sum_sub_distrib, sum_rowSum_eq N hN hu hv huv hY,
    sum_cusp_CT_eq N hu hv huv hY]

end GaloisForLFunctions.RHTower.SelbergMaassSelbergGammaN
