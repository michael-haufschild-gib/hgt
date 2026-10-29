import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerPositivity

/-!
# The exact reference energy for Trans-Metzler perturbation

At width c/N, retain the center estimate's Young parameter and the exact self
finite part. The resulting coercivity has only an arbitrarily small prime-form
error. While the pole charge is below one, conductor one minimizes all limiting
Ramanujan energies. Bounded-defect compactness and quasimode residuals give every
strict relaxation of that energy as an eventual spectral floor. The actual
conductor-one vector attains it asymptotically.
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix RHTower
open scoped Real RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics HTGeometry

/-- The conductor-one limiting reference energy. -/
def transMetzlerReferenceFloor (c : ℝ) : ℝ :=
  completeWeilSelfFinitePart transMetzlerProfile c + completeWeilPoleShift transMetzlerProfile c

/-- Prime-defect reserve after paying the center term with a Young parameter. -/
def transMetzlerYoungReserve (c lam : ℝ) : ℝ :=
  1 - completeWeilPoleShift transMetzlerProfile c * (1 + 1 / lam)

/-- Mass cost of the center, cross and pole errors at width c/N. -/
def transMetzlerYoungMassLoss (c lam : ℝ) : ℝ :=
  1276 * c^2 + completeWeilPoleShift transMetzlerProfile c *
    ((1 + lam) * psiConstant + 15) - completeWeilSelfFinitePart transMetzlerProfile c

/-- The entire Young family of coercive bounds, retaining the exact overlap and
self finite part. The only vanishing loss is the prime-defect counterterm error. -/
theorem eventually_transMetzlerMainMatrix_young_coercive {c lam ε : ℝ}
    (hc : 0 < c) (hc2 : c ≤ 2) (hlam : 0 < lam) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (transMetzlerYoungReserve c lam - ε) * poleDefect N (primeHorizonExtension x) -
          (transMetzlerYoungMassLoss c lam + ε) * ‖x‖^2 ≤
        ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (c / N) c N) x, x⟫ := by
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 2] with N hNN₀ hN2 x
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw0 : 0 < c / (N : ℝ) := div_pos hc hN0
  have hw1 : c / (N : ℝ) ≤ 1 :=
    (div_le_one hN0).mpr (hc2.trans (by exact_mod_cast hN2))
  have hp := hN₀ N hNN₀ (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hp
  have hcenter := fullWeilCenterMatrix_inner_ge
    (completeWeilPoleShift_nonneg transMetzlerProfile hc.le) hlam hN1 x
  have hcross := (abs_le.mp (abs_separatedCrossErrorMatrix_inner_le hw0 hw1 N x)).2
  have hpole := (abs_le.mp (abs_poleMomentErrorMatrix_inner_le hw0 hw1 N x)).1
  rw [div_mul_cancel₀ _ hN0.ne'] at hcross hpole
  rw [transMetzlerMainMatrix_inner_eq]
  unfold transMetzlerYoungReserve transMetzlerYoungMassLoss renormalizedPrimeEnergy
  linarith only [hp, hcenter, hcross, hpole]

/-- Below unit pole charge, the conductor-one level is the least reference energy. -/
theorem transMetzlerReferenceFloor_le_adjunction {c : ℝ}
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1)
    {m : ℕ} (hm : 0 < m) :
    transMetzlerReferenceFloor c ≤ completeWeilAdjunctionEnergy transMetzlerProfile c m := by
  by_cases hm1 : m = 1
  · subst m
    apply le_of_eq
    rw [completeWeilAdjunctionEnergy, if_pos rfl,
      SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one]
    unfold transMetzlerReferenceFloor
    ring
  · have hgap :=
      (SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_sub_one_ge
        (show 1 < m by omega)).1
    rw [SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one] at hgap
    have hlog := Real.log_two_gt_d9
    rw [completeWeilAdjunctionEnergy, if_neg hm1, add_zero]
    unfold transMetzlerReferenceFloor
    linarith only [hgap, hlog, hcharge]

private theorem eventually_transMetzlerMainMatrix_eigenvalues_ge_of_coercive
    (w : ℕ → ℝ) (cStar f μ a B : ℝ)
    (ha : 0 < a) (hμ : μ < f)
    (hw : ∀ᶠ N : ℕ in atTop, 0 < w N ∧ w N ≤ 2 / (N : ℝ))
    (hmin : ∀ m : ℕ, 0 < m → f ≤ completeWeilAdjunctionEnergy transMetzlerProfile cStar m)
    (hcoercive : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      -B * ‖x‖^2 + a * poleDefect N (primeHorizonExtension x) ≤
        ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N) x, x⟫) :
    ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N,
      μ ≤ (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvalues i := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    ((B + μ) / a) (show (0 : ℝ) < 1 / 4 by norm_num)
  have hres_sum : Tendsto (fun N : ℕ =>
      ∑ m ∈ S, (1 / (f - μ)^2) *
        ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
            (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) atTop (𝓝 0) := by
    have hterm : ∀ m ∈ S, Tendsto (fun N : ℕ =>
        (1 / (f - μ)^2) *
          ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
              (normalizedRamanujanHorizonVector m N) -
            completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
              normalizedRamanujanHorizonVector m N‖ ^ 2) atTop (𝓝 0) := by
      intro m hm
      have hr := (tendsto_transMetzlerMainMatrix_ramanujan_residual_norm w cStar hw (hS m hm)).pow 2
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hr.const_mul (1 / (f - μ)^2)
    simpa only [sum_const_zero] using tendsto_finsetSum S hterm
  have hsmall := hres_sum.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 18))
  filter_upwards [hcoercive,
    eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2, hsmall] with N hcoerc hgram hN2 hsmallN i₀
  by_contra hlt
  push Not at hlt
  have hv_norm : ‖(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀‖ = 1 :=
    (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis.orthonormal.1 i₀
  have hv_supp : ∀ i : PrimeHorizonIndex N,
      μ ≤ (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvalues i →
        ⟪(transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀,
          (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i⟫ = 0 := by
    intro i hi
    have hne : i₀ ≠ i := fun h => by subst h; linarith only [hlt, hi]
    exact (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis.orthonormal.2 hne
  have hv_energy : ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
      ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀),
      (transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀⟫ ≤ μ := by
    have h := HTGeometry.hermitianEnergy_le_of_support
      (transMetzlerMainMatrix_isHermitian (w N) cStar N) μ _ hv_supp
    rwa [hv_norm, one_pow, mul_one] at h
  have hv_pd : poleDefect N (primeHorizonExtension
      ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀)) ≤
      (B + μ) / a := by
    have hc := hcoerc ((transMetzlerMainMatrix_isHermitian (w N) cStar N).eigenvectorBasis i₀)
    rw [hv_norm, one_pow, mul_one] at hc
    apply (le_div_iff₀ ha).mpr
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
      ∑ m ∈ S, (1 / (f - μ)^2) *
        ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
            (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    refine sum_le_sum fun m hm => ?_
    have hE := hmin m (hS m hm)
    have hgap : 0 < completeWeilAdjunctionEnergy transMetzlerProfile cStar m - μ := by
      linarith only [hE, hμ]
    have hgap_sq : (f - μ)^2 ≤
        (completeWeilAdjunctionEnergy transMetzlerProfile cStar m - μ)^2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hE)
        (show 0 ≤ completeWeilAdjunctionEnergy transMetzlerProfile cStar m + f - 2 * μ by
          linarith only [hE, hμ])
      nlinarith only [hp]
    have hinner := HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq
      (transMetzlerMainMatrix_isHermitian (w N) cStar N) μ
      (completeWeilAdjunctionEnergy transMetzlerProfile cStar m)
      (by linarith only [hE, hμ]) _ (normalizedRamanujanHorizonVector m N) hv_norm hv_supp
    have hdiv := div_le_div_of_nonneg_left
      (sq_nonneg ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
        (normalizedRamanujanHorizonVector m N) -
        completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
          normalizedRamanujanHorizonVector m N‖)
      (sq_pos_of_pos (sub_pos.mpr hμ)) hgap_sq
    exact hinner.trans (by simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one] using hdiv)
  linarith only [hmass, hmass_le, hsmallN]


/-- Every strict relaxation of the conductor-one energy eventually bounds all
reference eigenvalues, throughout the positive pole-defect reserve range. -/
theorem eventually_transMetzlerMainMatrix_reference_eigenvalues {c μ : ℝ}
    (hc : 0 < c) (hc2 : c ≤ 2)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1)
    (hμ : μ < transMetzlerReferenceFloor c) :
    ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N,
      μ ≤ (transMetzlerMainMatrix_isHermitian (c / N) c N).eigenvalues i := by
  let r := 1 - completeWeilPoleShift transMetzlerProfile c
  let lam := 2 / r
  let a := transMetzlerYoungReserve c lam
  have hr : 0 < r := sub_pos.mpr hcharge
  have hlam : 0 < lam := div_pos (by norm_num) hr
  have hlinv : 1 / lam = r / 2 := by dsimp only [lam]; field_simp
  have hαr := mul_le_mul_of_nonneg_right hcharge.le hr.le
  have ha : 0 < a := by
    dsimp only [a, transMetzlerYoungReserve]
    rw [hlinv]
    dsimp only [r] at hr hαr ⊢
    nlinarith only [hr, hαr]
  have hw : ∀ᶠ N : ℕ in atTop,
      0 < c / (N : ℝ) ∧ c / N ≤ 2 / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact ⟨div_pos hc hN0, div_le_div_of_nonneg_right hc2 hN0.le⟩
  apply eventually_transMetzlerMainMatrix_eigenvalues_ge_of_coercive
    (fun N => c / N) c (transMetzlerReferenceFloor c) μ (a / 2)
    (transMetzlerYoungMassLoss c lam + a / 2) (half_pos ha) hμ hw
    (fun m hm => transMetzlerReferenceFloor_le_adjunction hcharge hm)
  filter_upwards [eventually_transMetzlerMainMatrix_young_coercive hc hc2 hlam (half_pos ha)]
    with N hN x
  have hx := hN x
  change (a - a / 2) * poleDefect N (primeHorizonExtension x) -
    (transMetzlerYoungMassLoss c lam + a / 2) * ‖x‖^2 ≤ _ at hx
  linarith only [hx]

/-- The exact asymptotic reference floor, expressed as eventual quadratic bounds. -/
theorem eventually_transMetzlerMainMatrix_reference_floor {c μ : ℝ}
    (hc : 0 < c) (hc2 : c ≤ 2)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1)
    (hμ : μ < transMetzlerReferenceFloor c) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      μ * ‖x‖^2 ≤ ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (c / N) c N) x, x⟫ := by
  filter_upwards [eventually_transMetzlerMainMatrix_reference_eigenvalues hc hc2 hcharge hμ]
    with N hN x
  rw [hermitianEnergy_eq_sum (transMetzlerMainMatrix_isHermitian (c / N) c N) x,
    ← (transMetzlerMainMatrix_isHermitian (c / N) c N).eigenvectorBasis.sum_sq_inner_left x,
    mul_sum]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hN i) (sq_nonneg _)


/-- The conductor-one adjunction energy has no Euler-constant offset. -/
theorem transMetzlerReferenceFloor_eq_adjunction (c : ℝ) :
    transMetzlerReferenceFloor c = completeWeilAdjunctionEnergy transMetzlerProfile c 1 := by
  rw [completeWeilAdjunctionEnergy, if_pos rfl,
    SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one]
  unfold transMetzlerReferenceFloor
  ring

/-- The actual conductor-one quasimode attains the reference floor asymptotically. -/
theorem tendsto_transMetzlerMainMatrix_pole_energy {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 2) :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (c / N) c N)
        (normalizedRamanujanHorizonVector 1 N), normalizedRamanujanHorizonVector 1 N⟫)
      atTop (𝓝 (transMetzlerReferenceFloor c)) := by
  have hw : ∀ᶠ N : ℕ in atTop,
      0 < c / (N : ℝ) ∧ c / N ≤ 2 / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact ⟨div_pos hc hN0, div_le_div_of_nonneg_right hc2 hN0.le⟩
  have hr := tendsto_transMetzlerMainMatrix_ramanujan_residual_norm
    (fun N => c / N) c hw (show 0 < (1 : ℕ) by decide)
  have hnorm : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector 1 N‖)
      atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq (show 0 < (1 : ℕ) by decide)).sqrt
  have herr : Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix (c / N) c N)
          (normalizedRamanujanHorizonVector 1 N) -
        completeWeilAdjunctionEnergy transMetzlerProfile c 1 •
          normalizedRamanujanHorizonVector 1 N, normalizedRamanujanHorizonVector 1 N⟫)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => norm_inner_le_norm _ _)
    simpa only [zero_mul] using hr.mul hnorm
  have hmain := (tendsto_normalizedRamanujanHorizonVector_gram
    (show 0 < (1 : ℕ) by decide) (show 0 < (1 : ℕ) by decide)).const_mul
      (completeWeilAdjunctionEnergy transMetzlerProfile c 1)
  rw [transMetzlerReferenceFloor_eq_adjunction]
  simpa only [inner_sub_left, real_inner_smul_left, sub_add_cancel, zero_add,
    if_pos rfl, ite_true, mul_one] using herr.add hmain


/-- The plateau charge is positive and has a strict variance reserve. -/
theorem transMetzlerProfile_charge_bounds :
    (99 : ℝ) / 100 ≤ completeWeilPoleShift transMetzlerProfile 1 ∧
      completeWeilPoleShift transMetzlerProfile 1 < 1 := by
  refine ⟨?_, ?_⟩
  · have hI := integral_transMetzlerProfile_ge
    have hM := integral_transMetzlerProfile_sq_le_one
    rw [completeWeilPoleShift, one_mul, le_div_iff₀ integral_transMetzlerProfile_sq_pos]
    nlinarith only [hI, hM]
  · linarith only [transMetzlerProfile_charge_deficit_ge]

lemma transMetzlerPoleShift_eq_mul (c : ℝ) :
    completeWeilPoleShift transMetzlerProfile c =
      c * completeWeilPoleShift transMetzlerProfile 1 := by
  unfold completeWeilPoleShift
  ring

lemma transMetzlerSelfFinitePart_eq {c : ℝ} (hc : 0 < c) :
    completeWeilSelfFinitePart transMetzlerProfile c =
      -Real.log (2 * Real.pi) - Real.log c +
        bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u^2) := by
  rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc.ne']
  ring

/-- The only varying terms of the reference floor are the logarithm and pole charge. -/
theorem transMetzlerReferenceFloor_eq (c : ℝ) (hc : 0 < c) :
    transMetzlerReferenceFloor c = transMetzlerReferenceFloor 1 - Real.log c +
      (c - 1) * completeWeilPoleShift transMetzlerProfile 1 := by
  unfold transMetzlerReferenceFloor
  rw [transMetzlerSelfFinitePart_eq hc, transMetzlerSelfFinitePart_eq zero_lt_one,
    transMetzlerPoleShift_eq_mul c, Real.log_one]
  ring

/-- Positive pole-defect reserve keeps the reference energy uniformly positive. -/
theorem transMetzlerReferenceFloor_gt {c : ℝ} (hc : 1 ≤ c)
    (hcharge : completeWeilPoleShift transMetzlerProfile c < 1) :
    (1 : ℝ) / 25 < transMetzlerReferenceFloor c := by
  obtain ⟨hq, hq1⟩ := transMetzlerProfile_charge_bounds
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hmul := mul_le_mul_of_nonneg_left hq hc0.le
  rw [transMetzlerPoleShift_eq_mul] at hcharge
  have hcmax : c < 100 / 99 := by linarith only [hmul, hcharge]
  have hcost : (c - 1) * (1 - completeWeilPoleShift transMetzlerProfile 1) ≤ 1 / 9900 := by
    have h := mul_le_mul (show c - 1 ≤ 1 / 99 by linarith only [hcmax])
      (show 1 - completeWeilPoleShift transMetzlerProfile 1 ≤ 1 / 100 by linarith only [hq])
      (sub_nonneg.mpr hq1.le) (by norm_num : (0 : ℝ) ≤ 1 / 99)
    norm_num at h
    exact h
  have hf1 := completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
    zero_lt_one (by norm_num : (1 : ℝ) ≤ 1 + 1 / 1000) (show 0 < (1 : ℕ) by decide)
  rw [← transMetzlerReferenceFloor_eq_adjunction] at hf1
  have hlog := Real.log_le_sub_one_of_pos hc0
  rw [transMetzlerReferenceFloor_eq c hc0]
  linarith only [hf1, hlog, hcost]

/-- The self finite part is negative throughout overlap at least one. -/
theorem transMetzlerSelfFinitePart_neg {c : ℝ} (hc : 1 ≤ c) :
    completeWeilSelfFinitePart transMetzlerProfile c < 0 := by
  have hthreshold := transMetzlerProfile_robinEuler_lt_half
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)] at hthreshold
  have hexp : Real.exp (bumpRobin transMetzlerProfile 1 /
      (∫ u, transMetzlerProfile u^2)) < Real.pi := by linarith only [hthreshold]
  have hquot : bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u^2) <
      Real.log Real.pi := by
    apply Real.exp_lt_exp.mp
    rwa [Real.exp_log Real.pi_pos]
  rw [transMetzlerSelfFinitePart_eq (zero_lt_one.trans_le hc),
    Real.log_mul two_ne_zero Real.pi_pos.ne']
  have hlogc := Real.log_nonneg hc
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  linarith only [hquot, hlogc, hlog2]


end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_transMetzlerMainMatrix_young_coercive

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_transMetzlerMainMatrix_reference_floor

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_transMetzlerMainMatrix_pole_energy

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerReferenceFloor_gt

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerSelfFinitePart_neg
