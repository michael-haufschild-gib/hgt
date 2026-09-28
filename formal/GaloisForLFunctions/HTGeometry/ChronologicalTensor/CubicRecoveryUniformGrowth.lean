import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryExponentialRate
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRecoveryEvenReduction

/-!
# Uniform recovery growth

Let `T_d` be the monic degree-`d` weighted optimizer (`T_0 = 1`), `t_d` its norm and `S_d` its root
sum.  Its homogeneous lift `H_d(u,c) = c^d T_d(u/c)` has physical norm `t_d`, and the corrected lift

  `A_d = H_d + S_d c H_{d-1}`

has `c⁰`-coefficient `u^d` and vanishing `c`-coefficient, with physical norm at most
`t_d + S_d t_{d-1} ≤ t_d + (d/4) t_{d-1} =: B_d`.  Multiplying an attained normalized residual of
weight `k+1` by `A_d` gives an admissible residual of weight `k+d+1`; the physical norm is
submultiplicative, so

  `δ_{k+d} ≤ B_d δ_k`  for all `k ≥ 0`, `d ≥ 1`,

and, since `B_d^{1/d} → ρ` and `δ_d/δ_0 ≤ sup_k δ_{k+d}/δ_k`,

  `lim_{d→∞} (sup_k δ_{k+d}/δ_k)^{1/d} = ρ`.
-/

open Set Filter Polynomial
open scoped Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ### Products of homogeneous observations -/

theorem mul_mem_cubicHomogeneousSpace {k l : ℕ} {P Q : Polynomial (Polynomial ℝ)}
    (hP : P ∈ cubicHomogeneousSpace k) (hQ : Q ∈ cubicHomogeneousSpace l) :
    P * Q ∈ cubicHomogeneousSpace (k + l) := by
  rw [cubicHomogeneousSpace_mem] at hP hQ ⊢
  rw [map_mul, hP, hQ, smul_mul_smul_comm, pow_add]

/-- A physical capacity is bounded by any bound on all probe values. -/
theorem cubicHomogeneousCapacity_le_of_forall {k : ℕ} (P : cubicHomogeneousSpace k) {M : ℝ}
    (hM : ∀ g : cubicProbeSection, |cubicPolynomialObservation P.val g| ≤ M) :
    cubicHomogeneousCapacity k P ≤ M :=
  csSup_le (cubicHomogeneousValues_nonempty k P) (by rintro _ ⟨g, rfl⟩; exact hM g)

/-- **Submultiplicativity of the physical norm.** -/
theorem cubicHomogeneousCapacity_mul_le {k l m : ℕ} (P : cubicHomogeneousSpace k)
    (Q : cubicHomogeneousSpace l) (R : cubicHomogeneousSpace m) (hR : R.val = P.val * Q.val) :
    cubicHomogeneousCapacity m R ≤ cubicHomogeneousCapacity k P * cubicHomogeneousCapacity l Q := by
  refine cubicHomogeneousCapacity_le_of_forall R fun g => ?_
  rw [hR, map_mul, Pi.mul_apply, abs_mul]
  exact mul_le_mul (cubicHomogeneousCapacity_bound k P g) (cubicHomogeneousCapacity_bound l Q g)
    (abs_nonneg _) (cubicHomogeneousCapacity_nonneg k P)

/-! ### Coefficients and lifts -/

theorem cubicHomogeneous_coeff {k : ℕ} (P : cubicHomogeneousSpace k) {m : ℕ} (hm : m ≤ k) :
    P.val.coeff m = Polynomial.monomial (k - m)
      (cubicHomogeneousCoordinates k P ⟨k - m, by omega⟩) := by
  have hP := (cubicPolynomialFlow_halfWeight P.val k).mp
    ((cubicHomogeneousSpace_mem k P.val).mp P.property)
  ext n
  rw [Polynomial.coeff_monomial]
  split_ifs with hn
  · subst hn
    change _ = (P.val.coeff (k - (k - m))).coeff (k - m)
    rw [show k - (k - m) = m by omega]
  · exact hP m n (by omega)

/-- The homogeneous lift `c^d R(u/c)` of a polynomial of degree at most `d`. -/
def cubicHomogeneousLift (d : ℕ) (R : Polynomial ℝ) : cubicHomogeneousSpace d :=
  (cubicHomogeneousCoordinatesEquiv d).symm fun i => R.coeff i.val

theorem cubicHomogeneousLift_coordinates (d : ℕ) (R : Polynomial ℝ) (i : Fin (d + 1)) :
    cubicHomogeneousCoordinates d (cubicHomogeneousLift d R) i = R.coeff i.val :=
  congrFun ((cubicHomogeneousCoordinatesEquiv d).apply_symm_apply _) i

theorem cubicDehomogeneousPolynomial_coeff_eq {d : ℕ} {R : Polynomial ℝ} (hR : R.natDegree ≤ d) :
    cubicDehomogeneousPolynomial d (fun i => R.coeff i.val) = R := by
  ext n
  by_cases hn : n < d + 1
  · exact cubicDehomogeneousPolynomial_coefficient d (fun i => R.coeff i.val) ⟨n, hn⟩
  · have hnk : d < n := by omega
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero.mp
      (cubicDehomogeneousPolynomial_degree d _) n hnk,
      Polynomial.natDegree_le_iff_coeff_eq_zero.mp hR n hnk]

/-- **The lift has physical norm equal to the weighted interval norm.** -/
theorem cubicHomogeneousCapacity_lift {d : ℕ} {R : Polynomial ℝ} (hR : R.natDegree ≤ d) :
    cubicHomogeneousCapacity d (cubicHomogeneousLift d R) = cubicWeightedIntervalNorm d R := by
  rw [cubicHomogeneousLift, cubicHomogeneousCapacity_weighted, cubicWeightedPolynomialNorm,
    cubicDehomogeneousPolynomial_coeff_eq hR, cubicWeightedIntervalNorm_changeVariable]

/-! ### The optimizer norms -/

/-- A chosen optimizer of degree `d`. -/
def cubicOptimizer (d : ℕ) : Polynomial ℝ := Classical.choose (exists_isCubicChebyshev d)

theorem cubicOptimizer_spec (d : ℕ) : IsCubicChebyshev d (cubicOptimizer d) :=
  (Classical.choose_spec (exists_isCubicChebyshev d)).1

/-- The optimal weighted norm `t_d`. -/
def cubicOptimalNorm (d : ℕ) : ℝ := cubicWeightedIntervalNorm d (cubicOptimizer d)

theorem cubicOptimalNorm_pos (d : ℕ) : 0 < cubicOptimalNorm d :=
  cubicChebyshev_norm_pos (cubicOptimizer_spec d)

theorem cubicOptimalNorm_eq {d : ℕ} {T : Polynomial ℝ} (hT : IsCubicChebyshev d T) :
    cubicWeightedIntervalNorm d T = cubicOptimalNorm d :=
  le_antisymm (hT.2.2 _ (cubicOptimizer_spec d).1 (cubicOptimizer_spec d).2.1)
    ((cubicOptimizer_spec d).2.2 _ hT.1 hT.2.1)

theorem cubicOptimalNorm_zero : cubicOptimalNorm 0 = 1 := by
  have hT := cubicOptimizer_spec 0
  have h1 : cubicOptimizer 0 = 1 := by
    rw [Polynomial.eq_C_of_natDegree_le_zero hT.1, show (cubicOptimizer 0).coeff 0 = 1 from hT.2.1,
      map_one]
  rw [cubicOptimalNorm, h1]
  refine le_antisymm (csSup_le ((nonempty_Icc.mpr (by norm_num)).image _) ?_) ?_
  · rintro _ ⟨r, _, rfl⟩
    simp
  · refine le_csSup (bddAbove_cubicWeightedIntervalNorm 0 1) ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
    simp

theorem le_cubicWeightedIntervalNorm {m : ℕ} (T : Polynomial ℝ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (1 / 4)) :
    cubicRadialWeight r ^ m * |T.eval r| ≤ cubicWeightedIntervalNorm m T :=
  le_csSup (bddAbove_cubicWeightedIntervalNorm m T) ⟨r, hr, rfl⟩

/-! ### The corrected lift -/

/-- The root sum `S_d` of the chosen optimizer (`S_d = -T_d.coeff (d-1)`). -/
def cubicOptimizerRootSum (d : ℕ) : ℝ := -(cubicOptimizer d).coeff (d - 1)

theorem cubicOptimizerRootSum_le {d : ℕ} (hd : 1 ≤ d) : cubicOptimizerRootSum d ≤ d / 4 := by
  obtain ⟨s, hcard, hroots, -, hcoeff, -⟩ := isCubicChebyshev_roots d hd (cubicOptimizer_spec d)
  rw [cubicOptimizerRootSum, hcoeff, neg_neg]
  calc ∑ r ∈ s, r ≤ ∑ _r ∈ s, (1 / 4 : ℝ) := Finset.sum_le_sum fun r hr => (hroots r hr).2.le
    _ = d / 4 := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring

theorem cubicOptimizerRootSum_nonneg {d : ℕ} (hd : 1 ≤ d) : 0 ≤ cubicOptimizerRootSum d := by
  obtain ⟨s, -, -, -, hcoeff, hpos⟩ := isCubicChebyshev_roots d hd (cubicOptimizer_spec d)
  rw [cubicOptimizerRootSum, hcoeff, neg_neg]; exact hpos.le

/-- The corrected polynomial `T_d + S_d T_{d-1}`. -/
def cubicCorrectedOptimizer (d : ℕ) : Polynomial ℝ :=
  cubicOptimizer d + Polynomial.C (cubicOptimizerRootSum d) * cubicOptimizer (d - 1)

theorem cubicCorrectedOptimizer_natDegree {d : ℕ} (hd : 1 ≤ d) :
    (cubicCorrectedOptimizer d).natDegree ≤ d :=
  natDegree_add_le_of_degree_le (cubicOptimizer_spec d).1
    ((natDegree_C_mul_le _ _).trans ((cubicOptimizer_spec (d - 1)).1.trans (by omega)))

theorem cubicCorrectedOptimizer_coeff_top {d : ℕ} (hd : 1 ≤ d) :
    (cubicCorrectedOptimizer d).coeff d = 1 := by
  rw [cubicCorrectedOptimizer, coeff_add, coeff_C_mul, (cubicOptimizer_spec d).2.1,
    Polynomial.coeff_eq_zero_of_natDegree_lt ((cubicOptimizer_spec (d - 1)).1.trans_lt
      (by omega)), mul_zero, add_zero]

theorem cubicCorrectedOptimizer_coeff_pred (d : ℕ) :
    (cubicCorrectedOptimizer d).coeff (d - 1) = 0 := by
  rw [cubicCorrectedOptimizer, coeff_add, coeff_C_mul, (cubicOptimizer_spec (d - 1)).2.1,
    cubicOptimizerRootSum]
  ring

/-- **The corrected norm bound** `‖T_d + S_d T_{d-1}‖ ≤ t_d + (d/4) t_{d-1}`. -/
theorem cubicWeightedIntervalNorm_corrected_le {d : ℕ} (hd : 1 ≤ d) :
    cubicWeightedIntervalNorm d (cubicCorrectedOptimizer d) ≤
      cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1) := by
  have hS0 := cubicOptimizerRootSum_nonneg hd
  have hS := cubicOptimizerRootSum_le hd
  refine csSup_le ((nonempty_Icc.mpr (by norm_num)).image _) ?_
  rintro _ ⟨r, hr, rfl⟩
  have hW := cubicRadialWeight_bounds ⟨r, hr⟩
  have h1 := le_cubicWeightedIntervalNorm (m := d) (cubicOptimizer d) hr
  have h2 := le_cubicWeightedIntervalNorm (m := d - 1) (cubicOptimizer (d - 1)) hr
  have hpow : cubicRadialWeight r ^ d = cubicRadialWeight r * cubicRadialWeight r ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  have hWd : 0 ≤ cubicRadialWeight r ^ (d - 1) := pow_nonneg hW.1 _
  simp only [cubicCorrectedOptimizer, eval_add, eval_mul, eval_C]
  set W := cubicRadialWeight r with hWdef
  set a := (cubicOptimizer d).eval r with ha
  set b := (cubicOptimizer (d - 1)).eval r with hb
  have hWdn : 0 ≤ W ^ d := pow_nonneg hW.1 d
  have hstep : W ^ d * |a + cubicOptimizerRootSum d * b| ≤
      W ^ d * |a| + cubicOptimizerRootSum d * (W * (W ^ (d - 1) * |b|)) := by
    have htri := abs_add_le a (cubicOptimizerRootSum d * b)
    rw [abs_mul, abs_of_nonneg hS0] at htri
    calc W ^ d * |a + cubicOptimizerRootSum d * b|
        ≤ W ^ d * (|a| + cubicOptimizerRootSum d * |b|) := mul_le_mul_of_nonneg_left htri hWdn
      _ = W ^ d * |a| + cubicOptimizerRootSum d * (W * (W ^ (d - 1) * |b|)) := by
          rw [hpow]; ring
  have hin : W * (W ^ (d - 1) * |b|) ≤ 1 * cubicOptimalNorm (d - 1) :=
    mul_le_mul hW.2 h2 (mul_nonneg hWd (abs_nonneg _)) zero_le_one
  have hsec : cubicOptimizerRootSum d * (W * (W ^ (d - 1) * |b|)) ≤
      d / 4 * (1 * cubicOptimalNorm (d - 1)) :=
    mul_le_mul hS hin (mul_nonneg hW.1 (mul_nonneg hWd (abs_nonneg _))) (by positivity)
  calc W ^ d * |a + cubicOptimizerRootSum d * b|
      ≤ W ^ d * |a| + cubicOptimizerRootSum d * (W * (W ^ (d - 1) * |b|)) := hstep
    _ ≤ cubicOptimalNorm d + d / 4 * (1 * cubicOptimalNorm (d - 1)) := add_le_add h1 hsec
    _ = cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1) := by ring

/-! ### The growth inequality -/

/-- **`δ_{k+d} ≤ (t_d + (d/4) t_{d-1}) δ_k`** for every `k ≥ 0` and `d ≥ 1`. -/
theorem cubicGradedRecoveryGap_add_le (k : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    cubicGradedRecoveryGap (k + d) ≤
      (cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1)) * cubicGradedRecoveryGap k := by
  obtain ⟨R, hR, hRcap⟩ := cubicGradedRecoveryGap_attained k
  set A := cubicHomogeneousLift d (cubicCorrectedOptimizer d) with hA
  have hAcoords_top : cubicHomogeneousCoordinates d A ⟨d, by omega⟩ = 1 := by
    rw [hA, cubicHomogeneousLift_coordinates, cubicCorrectedOptimizer_coeff_top hd]
  have hAcoords_pred : cubicHomogeneousCoordinates d A ⟨d - 1, by omega⟩ = 0 := by
    rw [hA, cubicHomogeneousLift_coordinates, cubicCorrectedOptimizer_coeff_pred d]
  have hA0 : A.val.coeff 0 = Polynomial.monomial d 1 := by
    rw [cubicHomogeneous_coeff A (Nat.zero_le d)]
    simp only [Nat.sub_zero]
    rw [hAcoords_top]
  have hA1 : A.val.coeff 1 = 0 := by
    rw [cubicHomogeneous_coeff A hd, hAcoords_pred, Polynomial.monomial_zero_right]
  have hR1 : R.val.coeff 1 = Polynomial.monomial k 1 := by
    rw [cubicHomogeneous_coeff R (by omega : 1 ≤ k + 1)]
    have hRn : cubicHomogeneousCoordinates (k + 1) R (cubicMissingIndex k) = 1 := hR
    simp only [show k + 1 - 1 = k by omega]
    exact congrArg _ hRn
  -- the product residual
  have hmem : A.val * R.val ∈ cubicHomogeneousSpace (k + d + 1) := by
    have := mul_mem_cubicHomogeneousSpace A.property R.property
    rwa [show d + (k + 1) = k + d + 1 by ring] at this
  set P : cubicHomogeneousSpace (k + d + 1) := ⟨A.val * R.val, hmem⟩ with hP
  have hPcoeff : (A.val * R.val).coeff 1 = Polynomial.monomial (d + k) 1 := by
    rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp only [Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_cons,
      Finset.sum_singleton]
    simp [hA0, hA1, hR1, Polynomial.monomial_mul_monomial]
  have hPnorm : P ∈ cubicNormalizedResiduals (k + d) := by
    change (P.val.coeff (k + d + 1 - (k + d))).coeff (k + d) = 1
    rw [show k + d + 1 - (k + d) = 1 by omega]
    change ((A.val * R.val).coeff 1).coeff (k + d) = 1
    rw [hPcoeff, Polynomial.coeff_monomial, if_pos (by ring)]
  have hgap : cubicGradedRecoveryGap (k + d) ≤ cubicHomogeneousCapacity (k + d + 1) P :=
    (cubicGradedRecoveryGap_isLeast (k + d)).2
      ⟨P, (cubicNormalizedResiduals_mem (k + d) P).mp hPnorm, rfl⟩
  have hprod := cubicHomogeneousCapacity_mul_le A R P rfl
  have hAcap : cubicHomogeneousCapacity d A ≤ cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1) := by
    rw [hA, cubicHomogeneousCapacity_lift (cubicCorrectedOptimizer_natDegree hd)]
    exact cubicWeightedIntervalNorm_corrected_le hd
  rw [hRcap] at hprod
  calc cubicGradedRecoveryGap (k + d) ≤ cubicHomogeneousCapacity (k + d + 1) P := hgap
    _ ≤ cubicHomogeneousCapacity d A * cubicGradedRecoveryGap k := hprod
    _ ≤ (cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1)) * cubicGradedRecoveryGap k :=
        mul_le_mul_of_nonneg_right hAcap (cubicGradedRecoveryGap_positive k).le

/-! ### The uniform root limit -/

/-- The uniform growth `sup_k δ_{k+d}/δ_k`. -/
def cubicRecoveryUniformGrowth (d : ℕ) : ℝ :=
  ⨆ k : ℕ, cubicGradedRecoveryGap (k + d) / cubicGradedRecoveryGap k

theorem cubicRecoveryUniformGrowth_bddAbove {d : ℕ} (hd : 1 ≤ d) :
    BddAbove (Set.range fun k : ℕ => cubicGradedRecoveryGap (k + d) / cubicGradedRecoveryGap k) :=
  ⟨cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1), by
    rintro _ ⟨k, rfl⟩
    rw [div_le_iff₀ (cubicGradedRecoveryGap_positive k)]
    exact cubicGradedRecoveryGap_add_le k hd⟩

theorem cubicRecoveryUniformGrowth_le {d : ℕ} (hd : 1 ≤ d) :
    cubicRecoveryUniformGrowth d ≤ cubicOptimalNorm d + d / 4 * cubicOptimalNorm (d - 1) :=
  ciSup_le fun k => by
    rw [div_le_iff₀ (cubicGradedRecoveryGap_positive k)]
    exact cubicGradedRecoveryGap_add_le k hd

theorem le_cubicRecoveryUniformGrowth {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    cubicGradedRecoveryGap (k + d) / cubicGradedRecoveryGap k ≤ cubicRecoveryUniformGrowth d :=
  le_ciSup (cubicRecoveryUniformGrowth_bddAbove hd) k

theorem cubicRecoveryUniformGrowth_pos {d : ℕ} (hd : 1 ≤ d) : 0 < cubicRecoveryUniformGrowth d :=
  lt_of_lt_of_le (div_pos (cubicGradedRecoveryGap_positive _) (cubicGradedRecoveryGap_positive 0))
    (le_cubicRecoveryUniformGrowth hd 0)

/-- `log(1 + d/4)/d → 0`. -/
theorem tendsto_log_one_add_div_four_div :
    Tendsto (fun d : ℕ => Real.log (1 + (d : ℝ) / 4) / d) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 4 (-4) 1 (by norm_num)).comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 4)))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  simp only [Function.comp_apply, pow_one]
  congr 1; ring

/-- **`lim_{d→∞} (sup_k δ_{k+d}/δ_k)^{1/d} = ρ`.** -/
theorem tendsto_cubicRecoveryUniformGrowth :
    Tendsto (fun d : ℕ => cubicRecoveryUniformGrowth d ^ (1 / (d : ℝ))) atTop
      (𝓝 recoveryRate) := by
  have hρ := recoveryRate_bounds.1
  have ht := tendsto_log_cubicChebyshev_norm cubicOptimizer_spec
  have ht' : Tendsto (fun d : ℕ => Real.log (cubicOptimalNorm d) / d) atTop
      (𝓝 (Real.log recoveryRate)) := ht
  -- `log t_{d-1}/d → log ρ`
  have htpred : Tendsto (fun d : ℕ => Real.log (cubicOptimalNorm (d - 1)) / d) atTop
      (𝓝 (Real.log recoveryRate)) := by
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    have h := ht'.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Nat.add_sub_cancel]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    push_cast
    field_simp
  -- lower bound sequence
  have hlow : Tendsto (fun d : ℕ =>
      Real.log (cubicGradedRecoveryGap d / cubicGradedRecoveryGap 0) / d) atTop
        (𝓝 (Real.log recoveryRate)) := by
    have h := tendsto_log_cubicGradedRecoveryGap.sub
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.log (cubicGradedRecoveryGap 0)))
    rw [sub_zero] at h
    refine h.congr fun d => ?_
    rw [Real.log_div (cubicGradedRecoveryGap_positive d).ne'
      (cubicGradedRecoveryGap_positive 0).ne', sub_div]
  -- upper bound sequence
  have hup : Tendsto (fun d : ℕ => Real.log (1 + (d : ℝ) / 4) / d +
      max (Real.log (cubicOptimalNorm d) / d) (Real.log (cubicOptimalNorm (d - 1)) / d)) atTop
        (𝓝 (Real.log recoveryRate)) := by
    have h := tendsto_log_one_add_div_four_div.add (ht'.max htpred)
    rwa [zero_add, max_self] at h
  have hlog : Tendsto (fun d : ℕ => Real.log (cubicRecoveryUniformGrowth d) / d) atTop
      (𝓝 (Real.log recoveryRate)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      refine div_le_div_of_nonneg_right ?_ hdR.le
      refine Real.log_le_log (div_pos (cubicGradedRecoveryGap_positive _)
        (cubicGradedRecoveryGap_positive 0)) ?_
      have := le_cubicRecoveryUniformGrowth hd 0
      rwa [zero_add] at this
    · filter_upwards [eventually_ge_atTop 1] with d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have ha := cubicOptimalNorm_pos d
      have hb := cubicOptimalNorm_pos (d - 1)
      set M := max (cubicOptimalNorm d) (cubicOptimalNorm (d - 1)) with hM
      have hMpos : 0 < M := lt_max_of_lt_left ha
      have hB : cubicRecoveryUniformGrowth d ≤ (1 + (d : ℝ) / 4) * M := by
        refine (cubicRecoveryUniformGrowth_le hd).trans ?_
        have h1 : cubicOptimalNorm d ≤ M := le_max_left _ _
        have h2 : cubicOptimalNorm (d - 1) ≤ M := le_max_right _ _
        nlinarith
      have hlogB := Real.log_le_log (cubicRecoveryUniformGrowth_pos hd) hB
      rw [Real.log_mul (by positivity) hMpos.ne'] at hlogB
      have hlogM : Real.log M = max (Real.log (cubicOptimalNorm d))
          (Real.log (cubicOptimalNorm (d - 1))) := by
        rw [hM]
        rcases le_total (cubicOptimalNorm d) (cubicOptimalNorm (d - 1)) with h | h
        · rw [max_eq_right h, max_eq_right (Real.log_le_log ha h)]
        · rw [max_eq_left h, max_eq_left (Real.log_le_log hb h)]
      rw [hlogM] at hlogB
      rw [max_div_div_right hdR.le, ← add_div]
      exact div_le_div_of_nonneg_right hlogB hdR.le
  have h := (Real.continuous_exp.tendsto _).comp hlog
  rw [Function.comp_def, Real.exp_log hρ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  rw [Real.rpow_def_of_pos (cubicRecoveryUniformGrowth_pos hd)]
  ring_nf

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
