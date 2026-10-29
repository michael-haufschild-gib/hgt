import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerDecomposition

/-!
# Unconditional complete Weil positivity strictly past the Metzler overlap threshold

This module combines the reference-operator spectral floor, uniform prime-defect coercivity from
the plateau variance reserve, and the overlap-length perturbation bound to cross `c = 1`
unconditionally:

* for every `cStar ∈ [1/2, cZero]` (`cZero = 1 + 10⁻¹⁸ > 1`) and every width sequence `w_N`
  drifting from `cStar / N` by `O(1 / N²)` with `w_N ≤ cZero / N`, `transMetzlerMainMatrix` has
  eventual eigenvalue floor `1 / 25` and uniform `poleDefect` coercivity;
* subtracting the `(2000 * deltaZero + C_short / log(N / 3))` perturbation leaves an eventual
  strictly positive eigenvalue floor `1 / 120` on `normalizedFullWeilHorizonMatrix`;
* consequently `(completeWeilMatrix transMetzlerProfile c N).PosDef` holds eventually for every
  `c ∈ (0, cZero]` (including `c = 1` and `cZero > 1`), as well as at the exact logarithmic
  spacing `atomSpacing N` and at `rhoZero * atomSpacing N` (`rhoZero > 1`), where no unimodular
  gauge makes the atomic Markov Gram matrix Metzler.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix RHTower
open scoped Real RealInnerProductSpace ComplexOrder

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics HTGeometry

/-! ### Uniform coercivity and spectral floor of `transMetzlerMainMatrix` -/

/-- Uniform prime-defect coercivity of `transMetzlerMainMatrix` up to `1 + 1 / 512000`, powered by
the variance charge deficit `1 - q₀ ≥ 1 / 128000` of `transMetzlerProfile`. -/
theorem eventually_transMetzlerMainMatrix_coercive
    (w : ℕ → ℝ) (cStar : ℝ)
    (hc0 : 0 < cStar) (hc1 : cStar ≤ 1 + 1 / 512000)
    (hw : ∀ᶠ N : ℕ in atTop, 0 < w N ∧ w N ≤ 2 / (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (-2100000 : ℝ) * ‖x‖ ^ 2 +
          (1 / 1024000 : ℝ) * poleDefect N (primeHorizonExtension x) ≤
        ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N) x, x⟫ := by
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le
    (show (0 : ℝ) < 1 / 1024000 by norm_num)
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 2, hw] with N hNN₀ hN2 ⟨hw0, hw2⟩ x
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw1 : w N ≤ 1 := hw2.trans ((div_le_one hN0).mpr (by exact_mod_cast hN2))
  have hwN : w N * N ≤ 2 := (le_div_iff₀ hN0).mp hw2
  have hwN_sq : (w N * N) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ w N * N := mul_nonneg hw0.le hN0.le
    nlinarith only [hwN, h0]
  -- Prime form + defect lower bound
  have hp := hN₀ N hNN₀ (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hp
  -- Charge deficit bound: `completeWeilPoleShift transMetzlerProfile cStar ≤ 1 - 1 / 256000`
  have hq0_def := transMetzlerProfile_charge_deficit_ge
  have hq0_nonneg : 0 ≤ completeWeilPoleShift transMetzlerProfile 1 :=
    completeWeilPoleShift_nonneg transMetzlerProfile zero_le_one
  have hα_eq : completeWeilPoleShift transMetzlerProfile cStar =
      cStar * completeWeilPoleShift transMetzlerProfile 1 := by
    unfold completeWeilPoleShift; ring
  have hα_nonneg : 0 ≤ completeWeilPoleShift transMetzlerProfile cStar :=
    completeWeilPoleShift_nonneg transMetzlerProfile hc0.le
  have hα_le : completeWeilPoleShift transMetzlerProfile cStar ≤ 1 - 1 / 256000 := by
    rw [hα_eq]
    nlinarith only [hc0, hc1, hq0_def, hq0_nonneg]
  have hα_coef : completeWeilPoleShift transMetzlerProfile cStar * (1 + 1 / (512000 : ℝ)) ≤
      1 - 1 / 512000 := by
    nlinarith only [hα_le, hα_nonneg]
  -- Center matrix lower bound with `lam = 512000`
  have hcenter := fullWeilCenterMatrix_inner_ge hα_nonneg
    (show (0 : ℝ) < 512000 by norm_num) hN1 x
  have hpsi_le : psiConstant ≤ 4 := by
    unfold psiConstant
    have hlog4 : Real.log 4 < (7 : ℝ) / 5 := by
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
      linarith only [h4, Real.log_two_lt_d9]
    have he_gt2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hdiv : 4 / Real.exp 1 ≤ 2 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith only [he_gt2]
    linarith only [hlog4, hdiv]
  have hcenter_mass : completeWeilPoleShift transMetzlerProfile cStar *
      ((1 + (512000 : ℝ)) * psiConstant + 15) ≤ 2048019 := by
    have hpos_p := psiConstant_pos.le
    nlinarith only [hα_le, hα_nonneg, hpsi_le, hpos_p]
  -- Self finite part lower bound
  have hself_ge : -3 ≤ completeWeilSelfFinitePart transMetzlerProfile cStar := by
    have hcfp : completeWeilSelfFinitePart transMetzlerProfile cStar =
        -Real.log (2 * Real.pi) - Real.log cStar +
          bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) := by
      rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
        Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc0.ne']
      ring
    have h2pi := log_two_pi_lt
    have hlogc : Real.log cStar ≤ 1 :=
      (Real.log_le_sub_one_of_pos hc0).trans (by linarith only [hc1])
    have hb0 : 0 ≤ bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) := by
      refine div_nonneg ?_ integral_transMetzlerProfile_sq_pos.le
      unfold bumpRobin
      exact setIntegral_nonneg measurableSet_Ioc fun y hy =>
        div_nonneg (integral_sub_shift_sq_nonneg y) (by positivity)
    rw [hcfp]
    linarith only [h2pi, hlogc, hb0]
  -- Cross and pole error quadratic bounds
  have hcross := (abs_le.mp (abs_separatedCrossErrorMatrix_inner_le hw0 hw1 N x)).2
  have hpole := (abs_le.mp (abs_poleMomentErrorMatrix_inner_le hw0 hw1 N x)).1
  have hpd0 := poleDefect_nonneg N (primeHorizonExtension x)
  have hnorm0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hdef_mul := mul_le_mul_of_nonneg_right hα_coef hpd0
  have hcm_mul := mul_le_mul_of_nonneg_right hcenter_mass hnorm0
  have hself_mul := mul_le_mul_of_nonneg_right hself_ge hnorm0
  have hcross_num : (1264 * (w N * N) ^ 2) * ‖x‖ ^ 2 ≤ 5056 * ‖x‖ ^ 2 := by
    nlinarith only [hwN_sq, hnorm0]
  have hpole_num : -50 * ‖x‖ ^ 2 ≤ -(12 * (w N * N) ^ 2) * ‖x‖ ^ 2 := by
    nlinarith only [hwN_sq, hnorm0]
  rw [transMetzlerMainMatrix_inner_eq]
  unfold renormalizedPrimeEnergy
  linarith only [hp, hcenter, hdef_mul, hcm_mul, hself_mul, hcross, hcross_num, hpole, hpole_num,
    hnorm0]

/-- Eventual eigenvalue floor `1 / 25` for `transMetzlerMainMatrix (w N) cStar N`: every putative
low eigenvector has bounded prime defect, hence definite finite-Ramanujan coordinate mass, which is
annihilated by the Ramanujan quasimode residuals above `1 / 20 > 1 / 25`. -/
theorem eventually_transMetzlerMainMatrix_eigenvalues_ge
    (w : ℕ → ℝ) (cStar : ℝ)
    (hc0 : 0 < cStar) (hc1 : cStar ≤ 1 + 1 / 512000)
    (hw : ∀ᶠ N : ℕ in atTop, 0 < w N ∧ w N ≤ 2 / (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N,
      (1 : ℝ) / 25 ≤ (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvalues i := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    ((1024000 : ℝ) * (2100001 : ℝ)) (show (0 : ℝ) < 1 / 4 by norm_num)
  have hres_sum : Tendsto (fun N : ℕ =>
      ∑ m ∈ S, (10000 : ℝ) *
        ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
            (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) atTop (𝓝 0) := by
    have hterm : ∀ m ∈ S, Tendsto (fun N : ℕ =>
        (10000 : ℝ) *
          ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
              (normalizedRamanujanHorizonVector m N) -
            completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
              normalizedRamanujanHorizonVector m N‖ ^ 2) atTop (𝓝 0) := by
      intro m hm
      have hr := (tendsto_transMetzlerMainMatrix_ramanujan_residual_norm w cStar hw (hS m hm)).pow 2
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hr.const_mul (10000 : ℝ)
    simpa only [sum_const_zero] using tendsto_finsetSum S hterm
  have hsmall := hres_sum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 18))
  filter_upwards [eventually_transMetzlerMainMatrix_coercive w cStar hc0 hc1 hw,
    eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2, hsmall] with N hcoerc hgram hN2 hsmallN i₀
  by_contra hlt
  push Not at hlt
  have hv_norm : ‖(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀‖ = 1 :=
    (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis.orthonormal.1 i₀
  have hv_supp : ∀ i : PrimeHorizonIndex N,
      (1 : ℝ) / 25 ≤ (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvalues i →
        ⟪(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀,
          (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i⟫ = 0 := by
    intro i hi
    have hne : i₀ ≠ i := fun h => by subst h; linarith only [hlt, hi]
    exact (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis.orthonormal.2 hne
  have hv_energy : ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
      ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀),
      (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀⟫ ≤ 1 / 25 := by
    have h := HTGeometry.hermitianEnergy_le_of_support
      (transMetzlerMainMatrix_isHermitian (w N) cStar N) (1 / 25) _ hv_supp
    rwa [hv_norm, one_pow, mul_one] at h
  have hv_pd : poleDefect N (primeHorizonExtension
      ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀)) ≤
      (1024000 : ℝ) * 2100001 := by
    have hc := hcoerc ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀)
    rw [hv_norm, one_pow, mul_one] at hc
    linarith only [hc, hv_energy]
  -- Finite Ramanujan coordinate mass `≥ 1 / 18`
  obtain ⟨a, ha⟩ := happ N
    (primeHorizonExtension ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀))
    (by rw [sum_primeHorizonExtension_sq, hv_norm]; norm_num) hv_pd
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs_ne : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have ha_vec : ‖(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀ -
      ∑ m : S, (a m * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 1 / 4 := by
    have heq_sum : (∑ m : S, (a m * Real.sqrt (Real.log N)) • normalizedRamanujanHorizonVector m N) =
        ∑ m ∈ S, a m • ramanujanHorizonVector m N := by
      rw [← sum_coe_sort S (fun m => a m • ramanujanHorizonVector m N)]
      refine sum_congr rfl fun m _ => ?_
      rw [normalizedRamanujanHorizonVector, smul_smul]
      congr 1; field_simp [hs_ne]
    rw [heq_sum, EuclideanSpace.real_norm_sq_eq]
    rw [← sum_coe_sort (Icc 1 N) (fun n =>
      (primeHorizonExtension
        ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀) n -
        ∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2)] at ha
    refine (le_of_eq ?_).trans ha
    refine sum_congr rfl fun n _ => ?_
    have hproj : (∑ m ∈ S, a m • ramanujanHorizonVector m N) n =
        ∑ m ∈ S, a m * ramanujanPoleProfile m n := by
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
        (∑ m ∈ S, a m • ramanujanHorizonVector m N) = _
      rw [map_sum]; exact sum_congr rfl fun _ _ => rfl
    simp only [PiLp.sub_apply, hproj, primeHorizonExtension_coe]
  have hmass : (1 : ℝ) / 18 ≤
      ∑ m ∈ S, ⟪(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀,
        normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
    have hcert := HTGeometry.coordinate_mass_ge_of_finite_approximation
      (fun m : S => normalizedRamanujanHorizonVector m N) hgram _ hv_norm
      (fun m : S => a m * Real.sqrt (Real.log N)) ha_vec
    simpa only [sum_coe_sort S (fun m =>
      ⟪(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀,
        normalizedRamanujanHorizonVector m N⟫ ^ 2)] using hcert
  -- Upper bound on coordinate mass from quasimode residuals
  have hmass_le : (∑ m ∈ S, ⟪(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀,
      normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
      ∑ m ∈ S, (10000 : ℝ) *
        ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
            (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    refine sum_le_sum fun m hm => ?_
    have hc1000 : cStar ≤ 1 + 1 / 1000 := hc1.trans (by norm_num)
    have hE := completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
      hc0 hc1000 (hS m hm)
    have hgap : (1 : ℝ) / 100 < completeWeilAdjunctionEnergy transMetzlerProfile cStar m - 1 / 25 := by
      linarith only [hE]
    have hgap_sq : (1 : ℝ) / 10000 ≤
        (completeWeilAdjunctionEnergy transMetzlerProfile cStar m - 1 / 25) ^ 2 := by
      nlinarith only [hgap]
    have hinner := HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq
      (transMetzlerMainMatrix_isHermitian (w N) cStar N) (1 / 25)
      (completeWeilAdjunctionEnergy transMetzlerProfile cStar m)
      (by linarith only [hE]) _ (normalizedRamanujanHorizonVector m N) hv_norm hv_supp
    have hdiv : ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
            (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 /
        (completeWeilAdjunctionEnergy transMetzlerProfile cStar m - 1 / 25) ^ 2 ≤
        (10000 : ℝ) *
          ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
              (normalizedRamanujanHorizonVector m N) -
            completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
              normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      rw [div_le_iff₀ (sq_pos_of_pos (by linarith only [hgap]))]
      have hmul := mul_le_mul_of_nonneg_left hgap_sq
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10000) (sq_nonneg _))
      have hid : ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
              (normalizedRamanujanHorizonVector m N) -
            completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
              normalizedRamanujanHorizonVector m N‖ ^ 2 =
          (10000 * ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
              (normalizedRamanujanHorizonVector m N) -
            completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
              normalizedRamanujanHorizonVector m N‖ ^ 2) * (1 / 10000) := by ring
      linarith only [hid, hmul]
    exact hinner.trans hdiv
  linarith only [hmass, hmass_le, hsmallN]

/-- Eventual quadratic-form lower bound retaining both a positive `‖x‖²` floor and a positive
`poleDefect` reserve on `transMetzlerMainMatrix (w N) cStar N`. -/
theorem eventually_transMetzlerMainMatrix_floor_and_defect
    (w : ℕ → ℝ) (cStar : ℝ)
    (hc0 : 0 < cStar) (hc1 : cStar ≤ 1 + 1 / 512000)
    (hw : ∀ᶠ N : ℕ in atTop, 0 < w N ∧ w N ≤ 2 / (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (1 / 60 : ℝ) * ‖x‖ ^ 2 +
          (1 / 107520000000000 : ℝ) * poleDefect N (primeHorizonExtension x) ≤
        ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N) x, x⟫ := by
  filter_upwards [eventually_transMetzlerMainMatrix_eigenvalues_ge w cStar hc0 hc1 hw,
    eventually_transMetzlerMainMatrix_coercive w cStar hc0 hc1 hw] with N heig hcoerc x
  have hfloor : (1 / 25 : ℝ) * ‖x‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum (transMetzlerMainMatrix_isHermitian (w N) cStar N) x,
      ← (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis.sum_sq_inner_left x,
      mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (heig i) (sq_nonneg _)
  have hc := hcoerc x
  have h1 := mul_le_mul_of_nonneg_left hfloor
    (show (0 : ℝ) ≤ 1 - 1 / 105000000 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hc
    (show (0 : ℝ) ≤ 1 / 105000000 by norm_num)
  have hnorm0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  linarith only [h1, h2, hnorm0]

/-! ### Master positivity theorem up to `cZero = 1 + 10⁻¹⁸ > 1` -/

private theorem posDef_of_quadratic_floor {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) {μ : ℝ} (hμ : 0 < μ)
    (hfloor : ∀ x : EuclideanSpace ℝ I, μ * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫) :
    A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  intro i
  have hb_norm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hf := hfloor (hA.eigenvectorBasis i)
  rw [hb_norm, one_pow, mul_one, HTGeometry.hermitianEnergy_eq_sum hA] at hf
  have hsum_eq : (∑ j : I, hA.eigenvalues j *
      ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis j⟫ ^ 2) = hA.eigenvalues i := by
    have horth (j : I) : ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis j⟫ =
        if i = j then 1 else 0 :=
      (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
    simp only [horth, ite_pow, one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
  rw [hsum_eq] at hf
  exact hμ.trans_le hf

private theorem weilQuad_atomicTest_nonneg_of_posDef {g : ℝ → ℝ} {w : ℝ} {N : ℕ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (hM : 0 < ∫ u, g u ^ 2)
    (hpos : (normalizedFullWeilHorizonMatrix g N).PosDef) (y : ℕ → ℝ) :
    0 ≤ weilQuad (atomicTest N y g) := by
  have hA := normalizedFullWeilHorizonMatrix_isHermitian g N
  have heig : ∀ i : PrimeHorizonIndex N, 0 < hA.eigenvalues i :=
    hA.posDef_iff_eigenvalues_pos.mp hpos
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (normalizedFullWeilHorizonMatrix g N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [normalizedFullWeilHorizonMatrix_inner_eq_weilQuad hg hsupp hw N (horizonProfileVector y N)]
    at hquad
  have htest_eq : atomicTest N (primeHorizonExtension (horizonProfileVector y N)) g =
      atomicTest N y g := by
    funext u
    unfold atomicTest
    refine sum_congr rfl fun n hn => ?_
    have hcoe : primeHorizonExtension (horizonProfileVector y N) n = y n :=
      primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩
    rw [hcoe]
  rw [htest_eq, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hM_neg⟩
  · exact hq
  · linarith only [hM, hM_neg]

/-- Master trans-Metzler positivity theorem: for any `cStar ∈ [1/2, cZero]` and any width sequence
`w_N` satisfying `1 / (2 N) ≤ w_N ≤ cZero / N` and `|w_N * N - cStar| ≤ 2 / N`, the normalized
complete Weil matrix is eventually positive definite with eigenvalue floor `1 / 120`. -/
theorem eventually_normalizedFullWeilHorizonMatrix_posDef_of_width_near
    (w : ℕ → ℝ) (cStar : ℝ)
    (hc_lo : 1 / 2 ≤ cStar) (hc_hi : cStar ≤ cZero)
    (hw : ∀ᶠ N : ℕ in atTop, 1 / (2 * (N : ℝ)) ≤ w N ∧ w N ≤ cZero / (N : ℝ) ∧
      |w N * (N : ℝ) - cStar| ≤ 2 / (N : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile (w N)) N).PosDef := by
  have hc0 : 0 < cStar := by linarith only [hc_lo]
  have hcZero_512 : cZero ≤ 1 + 1 / 512000 := by norm_num [cZero, deltaZero]
  have hc1 : cStar ≤ 1 + 1 / 512000 := hc_hi.trans hcZero_512
  have hw_simple : ∀ᶠ N : ℕ in atTop, 0 < w N ∧ w N ≤ 2 / (N : ℝ) := by
    filter_upwards [hw, eventually_ge_atTop 1] with N ⟨hlo, hhi, -⟩ hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    refine ⟨lt_of_lt_of_le (by positivity) hlo, hhi.trans ?_⟩
    exact div_le_div_of_nonneg_right (by linarith only [hcZero_512]) hN0.le
  obtain ⟨C_short, _, hpert⟩ := exists_perturbation_bound_transMetzler
  have hlog_div : Tendsto (fun N : ℕ => C_short / Real.log ((N : ℝ) / 3)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun N : ℕ => (N : ℝ) / 3) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    exact tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hlin)
  have hsmall := hlog_div.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < (2 : ℝ) * 10⁻¹ ^ 15))
  filter_upwards [eventually_transMetzlerMainMatrix_floor_and_defect w cStar hc0 hc1 hw_simple,
    hw, hsmall, eventually_ge_atTop 27] with N hmain ⟨hw_lo, hw_hi, hdrift⟩ hsmallN hN27
  refine posDef_of_quadratic_floor
    (normalizedFullWeilHorizonMatrix_isHermitian _ N) (by norm_num : (0 : ℝ) < 1 / 120) fun x => ?_
  have hm := hmain x
  have hp := (abs_le.mp (hpert hN27 deltaZero_pos.le (by norm_num [deltaZero]) hc_lo hw_lo
    (by simpa only [cZero] using hw_hi) hdrift x)).1
  have hcoef_pert : 2000 * deltaZero + C_short / Real.log ((N : ℝ) / 3) ≤
      (4 : ℝ) * 10⁻¹ ^ 15 := by
    have h2000 : 2000 * deltaZero ≤ (2 : ℝ) * 10⁻¹ ^ 15 := by norm_num [deltaZero]
    linarith only [h2000, hsmallN]
  have hpd0 := poleDefect_nonneg N (primeHorizonExtension x)
  have hnorm0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hpert_le : (2000 * deltaZero + C_short / Real.log ((N : ℝ) / 3)) *
      (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) ≤
      ((4 : ℝ) * 10⁻¹ ^ 15) * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hcoef_pert (add_nonneg hpd0 hnorm0)
  have hnum_pd : ((4 : ℝ) * 10⁻¹ ^ 15) ≤ 1 / 107520000000000 := by norm_num
  have hnum_x : (1 / 120 : ℝ) + (4 : ℝ) * 10⁻¹ ^ 15 ≤ 1 / 60 := by norm_num
  have hpd_cmp := mul_le_mul_of_nonneg_right hnum_pd hpd0
  have hx_cmp := mul_le_mul_of_nonneg_right hnum_x hnorm0
  linarith only [hm, hp, hpert_le, hpd_cmp, hx_cmp]

/-- Eventual positive definiteness of `completeWeilMatrix transMetzlerProfile c N` at the explicit
trans-Metzler overlap ratio `cZero = 1 + 10⁻¹⁸ > 1`. -/
theorem eventually_completeWeilMatrix_posDef_cZero :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix transMetzlerProfile cZero N).PosDef := by
  refine eventually_normalizedFullWeilHorizonMatrix_posDef_of_width_near
    (fun N => cZero / (N : ℝ)) cZero (by norm_num [cZero, deltaZero]) le_rfl ?_
  filter_upwards [eventually_ge_atTop 1] with N hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨?_, le_rfl, ?_⟩
  · rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (by norm_num [cZero, deltaZero]) hN0.le
  · rw [div_mul_cancel₀ _ hN0.ne', sub_self, abs_zero]
    positivity

/-- Eventual nonnegativity of `weilQuad` on all atomic tests at `cZero = 1 + 10⁻¹⁸ > 1`. -/
theorem eventually_weilQuad_atomicTest_nonneg_cZero :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N y (atomDilate transMetzlerProfile (cZero / N))) := by
  filter_upwards [eventually_completeWeilMatrix_posDef_cZero, eventually_ge_atTop 1] with N hpos hN1 y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : 0 < cZero / (N : ℝ) := div_pos cZero_pos hN0
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : 0 < ∫ u, atomDilate transMetzlerProfile (cZero / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  exact weilQuad_atomicTest_nonneg_of_posDef hg hgsupp hw0.le hM hpos y

/-- Unconditional crossing of the Metzler overlap threshold: there exist a fixed overlap ratio
`c > 1` and a smooth compactly supported nonnegative profile strictly positive on `(0, 1)` whose
complete Weil matrix is eventually positive definite and whose atomic tests have eventually
nonnegative Weil quadratic form. -/
theorem exists_gt_one_eventually_completeWeilMatrix_posDef :
    ∃ c : ℝ, 1 < c ∧ ∃ φ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ u, 0 ≤ φ u) ∧ (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) ∧ (∀ u ∈ Set.Ioo 0 1, 0 < φ u) ∧
      (∀ᶠ N : ℕ in atTop, (completeWeilMatrix φ c N).PosDef) ∧
      (∀ᶠ N : ℕ in atTop, ∀ y : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N y (atomDilate φ (c / N)))) :=
  ⟨cZero, one_lt_cZero, transMetzlerProfile, contDiff_top_transMetzlerProfile,
    hasCompactSupport_transMetzlerProfile, transMetzlerProfile_nonneg,
    fun u hu => transMetzlerProfile_eq_zero hu, fun u hu => transMetzlerProfile_pos hu,
    eventually_completeWeilMatrix_posDef_cZero, eventually_weilQuad_atomicTest_nonneg_cZero⟩

/-- Eventual positive definiteness of `completeWeilMatrix transMetzlerProfile c N` at every fixed
overlap ratio `c ∈ (0, cZero]` (including every `c ∈ (0, 1)`, the touching ratio `c = 1`, and the
trans-Metzler regime `(1, cZero]`). -/
theorem eventually_completeWeilMatrix_posDef_of_mem_Ioc {c : ℝ} (hc : c ∈ Set.Ioc 0 cZero) :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix transMetzlerProfile c N).PosDef := by
  rcases lt_or_ge c (1 / 2) with hlt | hge
  · have hc1 : c < 1 := hlt.trans (by norm_num)
    have hT_ne : ∀ m : ℕ, 0 < m →
        completeWeilAdjunctionEnergy transMetzlerProfile c m ≠ 1 / 25 := by
      intro m hm
      have hgt := completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
        hc.1 (hc1.le.trans (by norm_num)) hm
      linarith only [hgt]
    have hsub_empty : completeWeilEnergySublevel transMetzlerProfile c (1 / 25) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro m hm
      obtain ⟨hm0, hmlt⟩ := (mem_completeWeilEnergySublevel transMetzlerProfile c (1 / 25) m).mp hm
      have hgt := completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
        hc.1 (hc1.le.trans (by norm_num)) hm0
      linarith only [hmlt, hgt]
    filter_upwards [eventually_completeWeil_spectral_count_eq contDiff_transMetzlerProfile
      (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos
      hc.1 hc1 (1 / 25) hT_ne] with N hcard
    rw [hsub_empty, card_empty, card_eq_zero] at hcard
    rw [(completeWeilMatrix_isHermitian transMetzlerProfile c N).posDef_iff_eigenvalues_pos]
    intro i
    by_contra hle
    have hmem : i ∈ completeWeilSpectralSublevel transMetzlerProfile c N (1 / 25) := by
      rw [completeWeilSpectralSublevel, mem_filter]
      exact ⟨mem_univ i, lt_of_le_of_lt (not_lt.mp hle) (by norm_num)⟩
    rw [hcard] at hmem
    exact notMem_empty i hmem
  · refine eventually_normalizedFullWeilHorizonMatrix_posDef_of_width_near
      (fun N => c / (N : ℝ)) c hge hc.2 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    refine ⟨?_, div_le_div_of_nonneg_right hc.2 hN0.le, ?_⟩
    · rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hge hN0.le
    · rw [div_mul_cancel₀ _ hN0.ne', sub_self, abs_zero]
      positivity

/-- Eventual positive definiteness at the touching ratio `c = 1` (width `1 / N`). -/
theorem eventually_completeWeilMatrix_posDef_one :
    ∀ᶠ N : ℕ in atTop, (completeWeilMatrix transMetzlerProfile 1 N).PosDef :=
  eventually_completeWeilMatrix_posDef_of_mem_Ioc ⟨zero_lt_one, one_lt_cZero.le⟩

/-- Eventual positive definiteness and Weil nonnegativity at the exact logarithmic spacing
`atomSpacing N = log(1 + 1 / N)`. -/
theorem eventually_touching_atomSpacing_posDef :
    ∀ᶠ N : ℕ in atTop,
      (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile (atomSpacing N)) N).PosDef ∧
      ∀ y : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N y (atomDilate transMetzlerProfile (atomSpacing N))) := by
  have hpos_ev : ∀ᶠ N : ℕ in atTop,
      (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile (atomSpacing N)) N).PosDef := by
    refine eventually_normalizedFullWeilHorizonMatrix_posDef_of_width_near
      atomSpacing 1 (by norm_num) one_lt_cZero.le ?_
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN1 : 1 ≤ N := by omega
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hlo := inv_succ_le_atomSpacing hN1
    have hhi := atomSpacing_le_inv' hN1
    refine ⟨?_, ?_, ?_⟩
    · refine (le_trans ?_ hlo)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith only [hN2R]
    · exact hhi.trans (div_le_div_of_nonneg_right one_lt_cZero.le hN0.le)
    · have h1 : (N : ℝ) / (N + 1) ≤ atomSpacing N * N := by
        have := mul_le_mul_of_nonneg_right hlo hN0.le
        simpa only [one_div_mul_eq_div] using this
      have h2 : atomSpacing N * N ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hhi hN0.le
        rwa [one_div_mul_cancel hN0.ne'] at this
      rw [abs_le]
      have hgap : (1 : ℝ) - N / (N + 1) ≤ 2 / N := by
        have hstep : (1 : ℝ) - N / (N + 1) = 1 / (N + 1) := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]; ring
        rw [hstep, div_le_div_iff₀ (by positivity) hN0]
        linarith only [hN0]
      have h2N0 : 0 ≤ 2 / (N : ℝ) := by positivity
      exact ⟨by linarith only [h1, hgap], by linarith only [h2, h2N0]⟩
  filter_upwards [hpos_ev, eventually_ge_atTop 1] with N hpos hN1
  have hw0 := atomSpacing_pos hN1
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : 0 < ∫ u, atomDilate transMetzlerProfile (atomSpacing N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  exact ⟨hpos, weilQuad_atomicTest_nonneg_of_posDef hg hgsupp hw0.le hM hpos⟩

/-- Simultaneous complete Weil positive definiteness and unimodular gauge frustration of the atomic
Markov Gram matrix at exact spacing multiple `rhoZero * atomSpacing N` (`rhoZero > 1`). -/
theorem eventually_transMetzler_atomSpacing_posDef_and_frustrated :
    ∀ᶠ N : ℕ in atTop,
      (normalizedFullWeilHorizonMatrix
        (atomDilate transMetzlerProfile (rhoZero * atomSpacing N)) N).PosDef ∧
      (∀ y : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N y
          (atomDilate transMetzlerProfile (rhoZero * atomSpacing N)))) ∧
      ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
        ∀ i j, i ≠ j → 0 ≤ starRingEnd ℂ (γ i) * γ j *
          ((-atomicMarkovGram (ArithmeticLorentzianGeometry.dilate transMetzlerProfile
            (rhoZero * atomSpacing N)) N i j : ℝ) : ℂ) := by
  have hρ_le_c : rhoZero ≤ cZero := by
    unfold rhoZero cZero
    linarith only [deltaZero_pos]
  have hρ_le_two : rhoZero ≤ 2 := by norm_num [rhoZero, deltaZero]
  have hpos_ev : ∀ᶠ N : ℕ in atTop,
      (normalizedFullWeilHorizonMatrix
        (atomDilate transMetzlerProfile (rhoZero * atomSpacing N)) N).PosDef := by
    refine eventually_normalizedFullWeilHorizonMatrix_posDef_of_width_near
      (fun N => rhoZero * atomSpacing N) rhoZero (by linarith only [one_lt_rhoZero]) hρ_le_c ?_
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN1 : 1 ≤ N := by omega
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hN2R : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hlo := inv_succ_le_atomSpacing hN1
    have hhi := atomSpacing_le_inv' hN1
    refine ⟨?_, ?_, ?_⟩
    · have h1 : 1 / (2 * (N : ℝ)) ≤ 1 / ((N : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith only [hN2R]
      have h2 : 1 * atomSpacing N ≤ rhoZero * atomSpacing N :=
        mul_le_mul_of_nonneg_right one_lt_rhoZero.le (atomSpacing_pos hN1).le
      linarith only [h1, hlo, h2]
    · calc rhoZero * atomSpacing N ≤ rhoZero * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hhi rhoZero_pos.le
        _ = rhoZero / N := by ring
        _ ≤ cZero / N := div_le_div_of_nonneg_right hρ_le_c hN0.le
    · have h1 : rhoZero * ((N : ℝ) / (N + 1)) ≤ rhoZero * atomSpacing N * N := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlo rhoZero_pos.le) hN0.le
        linarith only [this, show rhoZero * (1 / ((N : ℝ) + 1)) * N =
          rhoZero * ((N : ℝ) / (N + 1)) by ring]
      have h2 : rhoZero * atomSpacing N * N ≤ rhoZero := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi rhoZero_pos.le) hN0.le
        have hsimp : rhoZero * (1 / (N : ℝ)) * N = rhoZero := by field_simp [hN0.ne']
        rwa [hsimp] at this
      have hgap : rhoZero - rhoZero * ((N : ℝ) / (N + 1)) ≤ 2 / N := by
        have hstep : rhoZero - rhoZero * ((N : ℝ) / (N + 1)) = rhoZero / (N + 1) := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]; ring
        rw [hstep, div_le_div_iff₀ (by positivity) hN0]
        nlinarith only [hρ_le_two, rhoZero_pos, hN0]
      rw [abs_le]
      have h2N0 : 0 ≤ 2 / (N : ℝ) := by positivity
      exact ⟨by linarith only [h1, hgap], by linarith only [h2, h2N0]⟩
  filter_upwards [hpos_ev, transMetzlerProfile_frustrated_of_one_lt one_lt_rhoZero,
    eventually_ge_atTop 1] with N hpos hfrust hN1
  have hw0 := mul_pos rhoZero_pos (atomSpacing_pos hN1)
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : 0 < ∫ u, atomDilate transMetzlerProfile (rhoZero * atomSpacing N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  exact ⟨hpos, weilQuad_atomicTest_nonneg_of_posDef hg hgsupp hw0.le hM hpos, hfrust⟩

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_gt_one_eventually_completeWeilMatrix_posDef
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeilMatrix_posDef_of_mem_Ioc
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_touching_atomSpacing_posDef
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_transMetzler_atomSpacing_posDef_and_frustrated