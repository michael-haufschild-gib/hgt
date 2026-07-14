import GaloisForLFunctions.HTGeometry.InverseGammaPolygammaPrincipalPartJet

/-!
# Factorial pole clusters of digamma composed with Gamma

This module records the discrete consequences of the analytic reciprocal-Gamma pole branches.
It proves the eventually genuine nonzero-residue pole cluster at reciprocal integers, the first
position and residue scaling limits, the balanced limit recovering the digamma value, and the
all-order coefficient transport from the position germ to the residue interpolation.
-/


namespace GaloisForLFunctions

open Complex Filter Topology Set

theorem iteratedDeriv_neg_sq_mul_deriv_zero
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {j : ℕ} (hj : 1 ≤ j) :
    iteratedDeriv (j + 1) (fun x : ℂ => -(x ^ 2) * deriv f x) 0 =
      -((j : ℂ) * ((j + 1 : ℕ) : ℂ)) * iteratedDeriv j f 0 := by
  have hpoly : ContDiffAt ℂ (j + 1) (fun x : ℂ => -(x ^ 2)) 0 := by fun_prop
  have hfder : ContDiffAt ℂ (j + 1) (deriv f) 0 := by
    exact hf.deriv.contDiffAt.of_le le_top
  have hmono (i : ℕ) :
      iteratedDeriv i (fun x : ℂ => -(x ^ 2)) 0 = if i = 2 then -2 else 0 := by
    change iteratedDeriv i (-(fun x : ℂ => x ^ 2)) 0 = _
    rw [iteratedDeriv_neg, iteratedDeriv_fun_pow_zero]
    split_ifs <;> ring
  change iteratedDeriv (j + 1) ((fun x : ℂ => -(x ^ 2)) * deriv f) 0 = _
  rw [iteratedDeriv_mul hpoly hfder]
  rw [Finset.sum_eq_single 2]
  · rw [hmono, if_pos rfl]
    have hjsub : j + 1 - 2 = j - 1 := by omega
    rw [hjsub]
    have hsucc : iteratedDeriv (j - 1) (deriv f) 0 = iteratedDeriv j f 0 := by
      have h := congrFun (iteratedDeriv_succ' (f := f) (n := j - 1)) 0
      rw [Nat.sub_add_cancel hj] at h
      exact h.symm
    rw [hsucc]
    rw [Nat.cast_choose_two]
    norm_num
    left
    ring
  · intro b hb hne
    simp only [Finset.mem_range] at hb
    rw [hmono, if_neg hne]
    simp
  · simp only [Finset.mem_range]
    omega

theorem ReciprocalGammaPoleBranch.residueInterpolation_all_order_coeff
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) {j : ℕ} (hj : 1 ≤ j) :
    iteratedDeriv (j + 1) (inverseGammaBranchResidueInterpolation zn) 0 =
      -((j : ℂ) * ((j + 1 : ℕ) : ℂ)) * iteratedDeriv j zn 0 := by
  exact iteratedDeriv_neg_sq_mul_deriv_zero zn.analyticAt_zero hj

theorem tendsto_natCast_inv_complex :
    Tendsto (fun m : ℕ => ((m : ℂ)⁻¹)) atTop (nhds 0) := by
  have hreal : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using hreal.ofReal

theorem tendsto_natCast_inv_complex_nhdsNE :
    Tendsto (fun m : ℕ => ((m : ℂ)⁻¹)) atTop (nhdsWithin 0 {0}ᶜ) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_natCast_inv_complex, ?_⟩
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hm
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact inv_ne_zero (by exact_mod_cast (Nat.ne_of_gt hm))

/-- For all sufficiently large positive integers, reciprocal-integer branch samples are genuine
inverse-Gamma values and nonzero-residue simple poles of `digamma ∘ Gamma`. -/
theorem ReciprocalGammaPoleBranch.factorial_cluster_eventually
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    ∀ᶠ m : ℕ in atTop,
      Complex.Gamma (zn ((m : ℂ)⁻¹)) = -(m : ℂ) ∧
      inverseGammaBranchResidueInterpolation zn ((m : ℂ)⁻¹) ≠ 0 ∧
      Tendsto
        (fun z : ℂ => (z - zn ((m : ℂ)⁻¹)) * Complex.digamma (Complex.Gamma z))
        (nhdsWithin (zn ((m : ℂ)⁻¹)) {zn ((m : ℂ)⁻¹)}ᶜ)
        (nhds (inverseGammaBranchResidueInterpolation zn ((m : ℂ)⁻¹))) := by
  have hx := tendsto_natCast_inv_complex_nhdsNE
  filter_upwards [zn.gamma_value_on_punctured_neighborhood.comp_tendsto hx,
    hx.eventually zn.residueInterpolation_eq_actual,
    hx.eventually (zn.polygammaCoeffInterpolation_samples 0),
    eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hGamma hActual hSample hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hGamma' : Complex.Gamma (zn ((m : ℂ)⁻¹)) = -(m : ℂ) := by
    simpa using hGamma
  refine ⟨hGamma', ?_, ?_⟩
  · rw [hActual.2]
    exact div_ne_zero (by norm_num) hActual.1
  · simpa [inverseGammaPolygammaCoeffInterpolation] using hSample m hm rfl

theorem ReciprocalGammaPoleBranch.position_first_scaled_limit
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    Tendsto (fun m : ℕ => (m : ℂ) * (zn ((m : ℂ)⁻¹) + (n : ℂ))) atTop
      (nhds (-reciprocalGammaBranchLinearCoeff n)) := by
  obtain ⟨R, hRAn, hbranch⟩ := zn.taylor_two_with_cubic_remainder
  have hx := tendsto_natCast_inv_complex
  have hRcomp : Tendsto (fun m : ℕ => R ((m : ℂ)⁻¹)) atTop (nhds (R 0)) :=
    hRAn.continuousAt.tendsto.comp hx
  have htarget : Tendsto
      (fun m : ℕ => -reciprocalGammaBranchLinearCoeff n +
        reciprocalGammaBranchQuadraticCoeff n * (m : ℂ)⁻¹ +
          ((m : ℂ)⁻¹) ^ 2 * R ((m : ℂ)⁻¹)) atTop
      (nhds (-reciprocalGammaBranchLinearCoeff n)) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.mul hx) |>.add ((hx.pow 2).mul hRcomp) using 1
    · norm_num
  apply htarget.congr'
  filter_upwards [hbranch.comp_tendsto hx,
    eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hmBranch hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [Function.comp_apply] at hmBranch
  rw [hmBranch]
  field_simp [hm0]
  ring

theorem ReciprocalGammaPoleBranch.residue_second_scaled_limit
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    Tendsto (fun m : ℕ => (m : ℂ) ^ 2 *
      inverseGammaBranchResidueInterpolation zn ((m : ℂ)⁻¹)) atTop
      (nhds (reciprocalGammaBranchLinearCoeff n)) := by
  obtain ⟨S, hSAn, hRho⟩ := zn.residueInterpolation_cubic
  have hx := tendsto_natCast_inv_complex
  have hScomp : Tendsto (fun m : ℕ => S ((m : ℂ)⁻¹)) atTop (nhds (S 0)) :=
    hSAn.continuousAt.tendsto.comp hx
  have htarget : Tendsto
      (fun m : ℕ => reciprocalGammaBranchLinearCoeff n -
        2 * reciprocalGammaBranchQuadraticCoeff n * (m : ℂ)⁻¹ +
          ((m : ℂ)⁻¹) ^ 2 * S ((m : ℂ)⁻¹)) atTop
      (nhds (reciprocalGammaBranchLinearCoeff n)) := by
    convert tendsto_const_nhds.sub
      (tendsto_const_nhds.mul hx) |>.add ((hx.pow 2).mul hScomp) using 1
    · norm_num
  apply htarget.congr'
  filter_upwards [hRho.comp_tendsto hx,
    eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hmRho hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [Function.comp_apply] at hmRho
  rw [hmRho]
  field_simp [hm0]

theorem ReciprocalGammaPoleBranch.balanced_next_scaled_limit
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    Tendsto (fun m : ℕ =>
      (m : ℂ) ^ 2 * (zn ((m : ℂ)⁻¹) + (n : ℂ)) +
        (m : ℂ) ^ 3 * inverseGammaBranchResidueInterpolation zn ((m : ℂ)⁻¹))
      atTop (nhds (-reciprocalGammaBranchQuadraticCoeff n)) := by
  obtain ⟨R, hRAn, hbranch⟩ := zn.taylor_two_with_cubic_remainder
  obtain ⟨S, hSAn, hRho⟩ := zn.residueInterpolation_cubic
  have hx := tendsto_natCast_inv_complex
  have hRcomp : Tendsto (fun m : ℕ => R ((m : ℂ)⁻¹)) atTop (nhds (R 0)) :=
    hRAn.continuousAt.tendsto.comp hx
  have hScomp : Tendsto (fun m : ℕ => S ((m : ℂ)⁻¹)) atTop (nhds (S 0)) :=
    hSAn.continuousAt.tendsto.comp hx
  have htarget : Tendsto
      (fun m : ℕ => -reciprocalGammaBranchQuadraticCoeff n +
        (m : ℂ)⁻¹ * (R ((m : ℂ)⁻¹) + S ((m : ℂ)⁻¹))) atTop
      (nhds (-reciprocalGammaBranchQuadraticCoeff n)) := by
    convert tendsto_const_nhds.add (hx.mul (hRcomp.add hScomp)) using 1
    · norm_num
  apply htarget.congr'
  filter_upwards [hbranch.comp_tendsto hx, hRho.comp_tendsto hx,
    eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hmBranch hmRho hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [Function.comp_apply] at hmBranch hmRho
  rw [hmBranch, hmRho]
  field_simp [hm0]
  ring

theorem ReciprocalGammaPoleBranch.digamma_recovered_from_balanced_cluster
    {n : ℕ} (zn : ReciprocalGammaPoleBranch n) :
    Tendsto (fun m : ℕ => -((n.factorial : ℂ) ^ 2) *
      ((m : ℂ) ^ 2 * (zn ((m : ℂ)⁻¹) + (n : ℂ)) +
        (m : ℂ) ^ 3 * inverseGammaBranchResidueInterpolation zn ((m : ℂ)⁻¹)))
      atTop (nhds (Complex.digamma ((n : ℂ) + 1))) := by
  have h := zn.balanced_next_scaled_limit.const_mul (-((n.factorial : ℂ) ^ 2))
  convert h using 1
  simp only [reciprocalGammaBranchQuadraticCoeff]
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfac]

end GaloisForLFunctions
