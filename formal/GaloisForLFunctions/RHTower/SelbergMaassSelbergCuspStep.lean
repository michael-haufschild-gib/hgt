import GaloisForLFunctions.RHTower.SelbergMaassSelbergSlab
import GaloisForLFunctions.RHTower.EisensteinMaassSelbergCuspIntegrals

open MeasureTheory UpperHalfPlane ModularGroup Set Complex
open scoped MatrixGroups Pointwise

/-!
# Step 1 of the `Γ(N)` Maass–Selberg relation: the cusp integrals of the non-constant parts vanish

`econst(y) = K y^{-3-σ}` (`econst_eq`), so `|E_∞(R_c z, u) − CT_c(u, Im z)| ≤ S₁S₂K y^{-3-Re u}`. On the cusp part
`𝒟 ∩ {y > Y}` (`Y ≥ 1`), Fubini in coordinates (`cusp_iterated`) and the zero mean over the cosets
(`sum_weighted_row_mean_zero`) give, for every shift-invariant continuous weight of growth `y^a`, `a < 4 + Re u`:
`Σ_c ∫_{𝒟 ∩ {y > Y}} g_c(y) (E_∞(R_c z, u) − CT_c(u, y)) dμ = 0` (`sum_cusp_estar_zero`).
-/

namespace GaloisForLFunctions.RHTower.SelbergMaassSelbergCuspStep
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace
  GaloisForLFunctions.RHTower.SelbergCellCosetShift GaloisForLFunctions.RHTower.SelbergCusppieceAveraging
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier GaloisForLFunctions.RHTower.SelbergCuspConstantTerm
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergPoincareKernel
  GaloisForLFunctions.RHTower.SelbergCuspZeroMean GaloisForLFunctions.RHTower.SelbergMaassMean
open CongruenceSubgroup

local notation "𝐄" => GaloisForLFunctions.RHTower.SelbergPoincare.poincare

variable (N : ℕ) [NeZero N]

/-- `econst(y) = K y^{-3-σ}`. -/
theorem econst_eq (σ R : ℝ) {y : ℝ} (hy : 0 < y) :
    econst N y σ σ R = (109 * ((1 + R) * N) ^ 4 * (2 * (N : ℝ) ^ (σ - 1) * cst σ) * (N : ℝ) ^ 2 /
      (2 * Real.pi) ^ 4) * y ^ (-(3 + σ)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold econst
  have e1 : (y / N) ^ (1 - σ) = y ^ (1 - σ) * (N : ℝ) ^ (σ - 1) := by
    rw [Real.div_rpow hy.le hN.le, div_eq_mul_inv, ← Real.rpow_neg hN.le]; ring_nf
  have e2 : y ^ (1 - σ) = y ^ (-(3 + σ)) * y ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]; ring_nf
  rw [e1, e2]
  field_simp
  ring

/-- Chart and Fubini on the cusp part of `𝒟`. -/
theorem cusp_iterated {Y : ℝ} (hY : 1 ≤ Y) {Φ : ℝ × ℝ → ℂ}
    (hint : IntegrableOn (fun p => Φ p / ((p.2 : ℝ) : ℂ) ^ 2) (RHTower.cuspRect Y)) :
    ∫ z in fd ∩ {z : ℍ | Y < z.im}, Φ (z.re, z.im) =
      ∫ y in Ioi Y, (∫ x in RHTower.unitIcc, Φ (x, y)) / ((y : ℝ) : ℂ) ^ 2 := by
  rw [RHTower.setIntegral_fd_above_eq hY Φ, RHTower.cuspRect, RHTower.setIntegral_prod_eq_iterated hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  simp only
  exact integral_div _ _

omit [NeZero N] in
theorem continuousAt_ofComplex_point {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun p : ℝ × ℝ => ofComplex (point p.1 p.2)) p := by
  have h1 : ContinuousAt (fun p : ℝ × ℝ => point p.1 p.2) p := by unfold point; fun_prop
  have hpos : 0 < (point p.1 p.2).im := by simpa [point] using hp
  have h2 : ContinuousAt ofComplex (point p.1 p.2) :=
    ofComplex.continuousAt (by exact ⟨⟨_, hpos⟩, Set.mem_univ _, rfl⟩)
  exact ContinuousAt.comp (f := fun p : ℝ × ℝ => point p.1 p.2) h2 h1

theorem continuousOn_CT (c : Cosets N) (u : ℂ) : ContinuousOn (fun y : ℝ => CT N c u y) (Ioi 0) := by
  unfold CT
  have hc : ContinuousOn (fun y : ℝ => ((y : ℝ) : ℂ)) (Ioi 0) := Complex.continuous_ofReal.continuousOn
  have hs : ∀ y ∈ Ioi (0 : ℝ), ((y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y hy => Complex.ofReal_mem_slitPlane.mpr hy
  exact (continuousOn_const.mul (hc.cpow_const hs)).add (continuousOn_const.mul (hc.cpow_const hs))

/-- **Step 1 of Maass–Selberg: the weighted non-constant parts integrate to zero over the cusps.** -/
theorem sum_cusp_estar_zero {u : ℂ} (hu : 1 < u.re) {Y : ℝ} (hY : 1 ≤ Y) (g : Cosets N → ℝ → ℂ)
    (hsh : ∀ c y, g (sh N c) y = g c y) (hgc : ∀ c, ContinuousOn (g c) (Ioi 0)) {a G : ℝ}
    (ha : a < 4 + u.re) (hG : 0 ≤ G) (hgb : ∀ c y, 1 ≤ y → ‖g c y‖ ≤ G * y ^ a) :
    ∑ c, ∫ z in fd ∩ {z : ℍ | Y < z.im},
      g c z.im * (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) = 0 := by
  have hY0 : 0 < Y := by linarith
  set Φ : Cosets N → ℝ × ℝ → ℂ := fun c p =>
    g c p.2 * (𝐄 N 0 u ((Quotient.out c : PSL2Z) • ofComplex (point p.1 p.2)) - CT N c u p.2)
  have hΦz : ∀ c (z : ℍ), g c z.im * (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im) =
      Φ c (z.re, z.im) := by
    intro c z; simp only [Φ, GaloisForLFunctions.RHTower.SelbergPoincarePairing.ofComplex_point]
  -- the constant of the decay bound
  set K : ℝ := 109 * ((1 + ‖u‖) * N) ^ 4 * (2 * (N : ℝ) ^ (u.re - 1) * cst u.re) * (N : ℝ) ^ 2 /
    (2 * Real.pi) ^ 4
  have hK : 0 ≤ K := by have := cst_nonneg u.re; simp only [K]; positivity
  have hS1 : 0 ≤ S1 u.re := tsum_nonneg (fun c => by split_ifs <;> positivity)
  have hS2 : 0 ≤ S2 := tsum_nonneg (fun c => by split_ifs <;> positivity)
  have hint : ∀ c, IntegrableOn (fun p => Φ c p / ((p.2 : ℝ) : ℂ) ^ 2) (RHTower.cuspRect Y) := by
    intro c
    refine Integrable.mono' (RHTower.integrableOn_rpow_cuspRect (β := a - 5 - u.re) (by linarith) hY0
      (G * (S1 u.re * (S2 * K)))) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ (RHTower.measurableSet_cuspRect Y)
      intro p hp
      have hp2 : 0 < p.2 := RHTower.cuspRect_pos hY0.le hp
      have hE : ContinuousAt (fun p : ℝ × ℝ => 𝐄 N 0 u ((Quotient.out c : PSL2Z) • ofComplex (point p.1 p.2))) p :=
        ((GaloisForLFunctions.RHTower.SelbergPoincareBounded.continuous_poincare N 0 hu).comp
          (continuous_const_smul _)).continuousAt.comp (continuousAt_ofComplex_point hp2)
      have hsnd : ContinuousAt (fun p : ℝ × ℝ => p.2) p := continuous_snd.continuousAt
      have hg : ContinuousAt (fun p : ℝ × ℝ => g c p.2) p :=
        ((hgc c).continuousAt (Ioi_mem_nhds hp2)).comp hsnd
      have hCT : ContinuousAt (fun p : ℝ × ℝ => CT N c u p.2) p :=
        ((continuousOn_CT N c u).continuousAt (Ioi_mem_nhds hp2)).comp hsnd
      have hy2 : ContinuousAt (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ 2) p :=
        (Complex.continuous_ofReal.comp continuous_snd).continuousAt.pow 2
      exact ((hg.mul (hE.sub hCT)).div hy2 (pow_ne_zero 2 (by exact_mod_cast hp2.ne'))).continuousWithinAt
    · refine (ae_restrict_iff' (RHTower.measurableSet_cuspRect Y)).mpr (Filter.Eventually.of_forall (fun p hp => ?_))
      have hp1 : 1 ≤ p.2 := by have := hp.2; simp only [mem_Ioi] at this; linarith
      have hp0 : 0 < p.2 := by linarith
      set z : ℍ := ofComplex (point p.1 p.2)
      have hzim : z.im = p.2 := (GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman.ofComplex_point hp0).1
      have hEst : ‖𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u p.2‖ ≤ S1 u.re * (S2 * (K * p.2 ^ (-(3 + u.re)))) := by
        rw [← hzim, poincare_sub_CT N c hu z]
        refine (GaloisForLFunctions.RHTower.SelbergCuspZeroMean.norm_Estarσ_le N _ (by linarith) z).trans (le_of_eq ?_)
        rw [econst_eq N _ _ z.im_pos, hzim]
      simp only [Φ]
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
      have hsq : 0 < p.2 ^ 2 := by positivity
      rw [div_le_iff₀ hsq]
      calc ‖g c p.2‖ * ‖𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u p.2‖
          ≤ (G * p.2 ^ a) * (S1 u.re * (S2 * (K * p.2 ^ (-(3 + u.re))))) :=
            mul_le_mul (hgb c p.2 hp1) hEst (norm_nonneg _) (by positivity)
        _ = G * (S1 u.re * (S2 * K)) * p.2 ^ (a - 5 - u.re) * p.2 ^ 2 := by
            have e : p.2 ^ (a - 5 - u.re) * p.2 ^ 2 = p.2 ^ a * p.2 ^ (-(3 + u.re)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_add hp0, ← Real.rpow_add hp0]; push_cast; ring_nf
            rw [mul_assoc (G * (S1 u.re * (S2 * K))), e]
            ring
  have hstep : ∀ c, (∫ z in fd ∩ {z : ℍ | Y < z.im},
      g c z.im * (𝐄 N 0 u ((Quotient.out c : PSL2Z) • z) - CT N c u z.im)) =
      ∫ y in Ioi Y, (∫ x in RHTower.unitIcc, Φ c (x, y)) / ((y : ℝ) : ℂ) ^ 2 := by
    intro c
    simp_rw [hΦz]
    exact cusp_iterated hY (hint c)
  simp_rw [hstep]
  have hyint : ∀ c ∈ (Finset.univ : Finset (Cosets N)),
      IntegrableOn (fun y => (∫ x in RHTower.unitIcc, Φ c (x, y)) / ((y : ℝ) : ℂ) ^ 2) (Ioi Y) := by
    intro c _
    have h := hint c
    unfold IntegrableOn at h
    rw [RHTower.cuspRect, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    have h2 := h.integral_prod_right
    refine h2.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only
    exact integral_div _ _
  rw [← integral_finsetSum _ hyint]
  refine integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Filter.Eventually.of_forall (fun y hy => ?_)))
  have hy0 : 0 < y := by simp only [mem_Ioi] at hy; linarith
  simp only [Pi.zero_apply]
  rw [← Finset.sum_div]
  apply div_eq_zero_iff.mpr; left
  have hrow : ∀ c, (∫ x in RHTower.unitIcc, Φ c (x, y)) = g c y *
      ((∫ x in (-1 / 2 : ℝ)..(1 / 2), 𝐄 N 0 u ((Quotient.out c : PSL2Z) • pt x y hy0)) - CT N c u y) := by
    intro c
    have hcont := continuous_E_row N c hu hy0
    simp only [Φ]
    rw [integral_const_mul]
    congr 1
    have e1 : (fun x : ℝ => 𝐄 N 0 u ((Quotient.out c : PSL2Z) • ofComplex (point x y)) - CT N c u y) =
        fun x => 𝐄 N 0 u ((Quotient.out c : PSL2Z) • pt x y hy0) - CT N c u y := by
      funext x; rw [pt_eq]
    rw [e1, RHTower.unitIcc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  simp_rw [hrow]
  exact sum_weighted_row_mean_zero N (fun c => g c y) (fun c => hsh c y) hu hy0

end GaloisForLFunctions.RHTower.SelbergMaassSelbergCuspStep
