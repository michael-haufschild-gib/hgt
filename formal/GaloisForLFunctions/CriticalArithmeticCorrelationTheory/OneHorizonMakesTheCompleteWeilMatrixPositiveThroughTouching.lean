import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.RamanujanQuasimodesAreUniformThroughTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive

/-!
# One complete positivity horizon through touching

Uniform arithmetic compactness and norm quasimodes exclude every eigenvalue
below the endpoint conductor-one energy. A smooth near-indicator profile then
gives one positive horizon simultaneously for every ratio in `(0,1]`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity

/-- Strict profile charge keeps conductor one below every excitation through touching. -/
theorem completeWeilAdjunctionEnergy_one_lt_at_touching {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {m : ℕ} (hm : 2 ≤ m) :
    completeWeilAdjunctionEnergy φ c 1 < completeWeilAdjunctionEnergy φ c m := by
  have hα : completeWeilPoleShift φ c < 1 :=
    (completeWeilPoleShift_lt_width hφ hsupp hM hc0).trans_le hc1
  have hlog : 1 ≤ 2 * Real.log 2 := by
    have h := HTGeometry.one_sub_inv_le_log (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith only [h]
  have hgap := (ramanujanAdjunctionEnergy_sub_one_ge hm).1
  rw [completeWeilAdjunctionEnergy, completeWeilAdjunctionEnergy, if_pos rfl,
    if_neg (by omega), add_zero]
  linarith only [hα, hlog, hgap]

private theorem finite_uniform_residuals {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ S : Finset ℕ, (∀ m ∈ S, 0 < m) →
      ∀ᶠ N : ℕ in atTop, ∀ m ∈ S, ∀ c : ℝ, 0 < c → c ≤ 1 →
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro hS
      exact Eventually.of_forall fun N m hm => False.elim (notMem_empty m hm)
  | @insert m S hmS ih =>
      intro hS
      have hm : 0 < m := hS m (mem_insert_self m S)
      have hSS : ∀ k ∈ S, 0 < k := fun k hk => hS k (mem_insert_of_mem hk)
      filter_upwards [eventually_completeWeil_ramanujan_residual_small_uniformly hφ hsupp hM hm hε,
        ih hSS] with N hmN hSN
      intro k hk
      rcases mem_insert.mp hk with hkm | hkS
      · subst k
        exact hmN
      · exact hSN k hkS

/-- Every threshold below the completed endpoint shape bounds every actual
eigenvalue with a single horizon for all ratios through one. -/
theorem eventually_completeWeil_eigenvalues_ge_uniformly_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {b : ℝ}
    (hb : b < bumpRobin φ 1 / (∫ u, φ u ^ 2) + completeWeilPoleShift φ 1 -
      Real.log (2 * Real.pi)) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ i : PrimeHorizonIndex N, b ≤ completeWeilEigenvalue φ c N i := by
  let E := bumpRobin φ 1 / (∫ u, φ u ^ 2) + completeWeilPoleShift φ 1 - Real.log (2 * Real.pi)
  let δ := E - b
  have hδ : 0 < δ := sub_pos.mpr hb
  have hfloor : ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ m : ℕ, 0 < m →
      E ≤ completeWeilAdjunctionEnergy φ c m := by
    intro c hc0 hc1 m hm
    have hg := completed_shape_le_completeWeilAdjunctionEnergy_one hφ.continuous hsupp hM hc0 hc1
    by_cases hm1 : m = 1
    · simpa only [hm1] using hg
    · exact hg.trans (completeWeilAdjunctionEnergy_one_lt_at_touching hφ.continuous hsupp hM
        hc0 hc1 (by omega : 2 ≤ m)).le
  obtain ⟨S, hS, hcert⟩ := exists_finite_ramanujan_coordinate_certificate_uniformly_at_touching
    hφ hsupp hM b
  let ε := δ / (6 * ((S.card : ℝ) + 1))
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hcost : (S.card : ℝ) * ε ^ 2 / δ ^ 2 < 1 / 18 := by
    have heq : (S.card : ℝ) * ε ^ 2 / δ ^ 2 =
        (S.card : ℝ) / (36 * ((S.card : ℝ) + 1) ^ 2) := by
      dsimp only [ε]
      field_simp [hδ.ne', show (S.card : ℝ) + 1 ≠ 0 by positivity]
      ring
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith only [hcard, sq_nonneg (S.card : ℝ)]
  filter_upwards [hcert, finite_uniform_residuals hφ hsupp hM hε S hS] with N hcertN hresN
  intro c hc0 hc1 i
  by_contra hi
  have hi' : (completeWeilMatrix_isHermitian φ c N).eigenvalues i < b := lt_of_not_ge hi
  let hA := completeWeilMatrix_isHermitian φ c N
  let x := hA.eigenvectorBasis i
  have hnorm : ‖x‖ = 1 := by
    have h : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith only [h, norm_nonneg x]
  have hlo : ∀ j, b ≤ hA.eigenvalues j → ⟪x, hA.eigenvectorBasis j⟫ = 0 := by
    intro j hj
    have hij : i ≠ j := by
      intro hij
      subst j
      exact (not_le_of_gt hi') hj
    simpa only [if_neg hij] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  have henergy : completeWeilEnergy φ c N x ≤ b := by
    have h := HTGeometry.hermitianEnergy_le_of_support hA b x hlo
    simpa only [completeWeilEnergy, hnorm, one_pow, mul_one] using h
  have hmass := hcertN c hc0 hc1 x hnorm henergy
  have hsum : (∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
      (S.card : ℝ) * ε ^ 2 / δ ^ 2 := by
    have hterm : ∀ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤ ε ^ 2 / δ ^ 2 := by
      intro m hm
      have hE := hfloor c hc0 hc1 m (hS m hm)
      have hgap : δ ≤ completeWeilAdjunctionEnergy φ c m - b := by
        dsimp only [δ]
        linarith only [hE]
      have hgt : b < completeWeilAdjunctionEnergy φ c m := by
        dsimp only [δ] at hδ
        linarith only [hE, hδ]
      have hlow := HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq hA b
        (completeWeilAdjunctionEnergy φ c m) hgt x (normalizedRamanujanHorizonVector m N) hnorm hlo
      have hr := hresN m hm c hc0 hc1
      have hrsq := mul_self_le_mul_self (norm_nonneg _) hr
      have hgsq := mul_self_le_mul_self hδ.le hgap
      rw [← sq, ← sq] at hrsq hgsq
      calc
        _ ≤ _ := hlow
        _ ≤ ε ^ 2 / (completeWeilAdjunctionEnergy φ c m - b) ^ 2 :=
          div_le_div_of_nonneg_right hrsq (sq_nonneg _)
        _ ≤ ε ^ 2 / δ ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg ε) (sq_pos_of_pos hδ) hgsq
    have h := sum_le_sum hterm
    simpa only [sum_const, nsmul_eq_mul, mul_div_assoc] using h
  linarith only [hmass, hsum, hcost]

/-- A near-unit-mass smooth profile gives one spectral horizon at every ratio through one. -/
theorem exists_near_unit_plateau_uniform_completeWeil_eigenvalue_floor {b ε : ℝ}
    (hb : b < 2 - Real.log (2 * Real.pi)) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ 1 - ε < (∫ u, plateau η u ^ 2) ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
        ∀ i : PrimeHorizonIndex N, b ≤ completeWeilEigenvalue (plateau η) c N i := by
  have hshape := tendsto_plateau_completed_margin.eventually (lt_mem_nhds hb)
  have hmass := tendsto_integral_plateau_sq.eventually
    (lt_mem_nhds (show 1 - ε < 1 by linarith only [hε]))
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1 / 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  obtain ⟨η, hmargin, hmassη, hη2, hη⟩ :=
    (hshape.and (hmass.and (hsmall.and self_mem_nhdsWithin))).exists
  refine ⟨η, hη, hη2, hmassη, ?_⟩
  have hM : 0 < ∫ u, plateau η u ^ 2 :=
    lt_of_lt_of_le (by linarith only [hη2]) (integral_plateau_sq_ge hη hη2.le)
  apply eventually_completeWeil_eigenvalues_ge_uniformly_at_touching (contDiff_plateau η)
    (fun _ hu => plateau_eq_zero hη hu) hM
  simpa only [completeWeilPoleShift, one_mul] using hmargin

/-- The same common horizon bounds the complete form on every coefficient vector. -/
theorem exists_near_unit_plateau_uniform_completeWeilEnergy_floor {b ε : ℝ}
    (hb : b < 2 - Real.log (2 * Real.pi)) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ 1 - ε < (∫ u, plateau η u ^ 2) ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          b * ‖x‖ ^ 2 ≤ completeWeilEnergy (plateau η) c N x := by
  obtain ⟨η, hη, hη2, hmass, hall⟩ :=
    exists_near_unit_plateau_uniform_completeWeil_eigenvalue_floor hb hε
  refine ⟨η, hη, hη2, hmass, ?_⟩
  filter_upwards [hall] with N hN
  intro c hc0 hc1 x
  rw [completeWeilEnergy,
    HTGeometry.hermitianEnergy_eq_sum (completeWeilMatrix_isHermitian (plateau η) c N),
    ← (completeWeilMatrix_isHermitian (plateau η) c N).eigenvectorBasis.sum_sq_inner_left x,
    mul_sum]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hN c hc0 hc1 i) (sq_nonneg _)

/-- One smooth near-unit-mass profile has positive complete matrices at one common
horizon for every ratio up to and including one. -/
theorem exists_near_unit_plateau_uniform_completeWeilMatrix_posDef {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ 1 - ε < (∫ u, plateau η u ^ 2) ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
        (completeWeilMatrix (plateau η) c N).PosDef := by
  let b : ℝ := (2 - Real.log (2 * Real.pi)) / 2
  have hb0 : 0 < b := by
    dsimp only [b]
    linarith only [RHTower.log_two_pi_lt_two]
  have hb : b < 2 - Real.log (2 * Real.pi) := by
    dsimp only [b] at *
    linarith only [hb0]
  obtain ⟨η, hη, hη2, hmass, hall⟩ :=
    exists_near_unit_plateau_uniform_completeWeil_eigenvalue_floor hb hε
  refine ⟨η, hη, hη2, hmass, ?_⟩
  filter_upwards [hall] with N hN
  intro c hc0 hc1
  apply (completeWeilMatrix_isHermitian (plateau η) c N).posDef_iff_eigenvalues_pos.mpr
  intro i
  exact hb0.trans_le (hN c hc0 hc1 i)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_eigenvalues_ge_uniformly_at_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_near_unit_plateau_uniform_completeWeilEnergy_floor
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_near_unit_plateau_uniform_completeWeilMatrix_posDef
