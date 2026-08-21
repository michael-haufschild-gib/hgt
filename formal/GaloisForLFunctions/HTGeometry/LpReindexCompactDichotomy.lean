import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp

/-!
# The reindexing dichotomy on `ℓ²`

Reindexing `ℓ²(I)` along a bijection of the index set is a unitary.  Its defect from the identity
is compact exactly when the bijection moves only finitely many indices, and it vanishes exactly
when the bijection is the identity.  The noncompact half is a two-separation argument: the
coordinate vectors at moved indices with pairwise disjoint two-element orbits have images at
mutual distance two, so the image of no ball is totally bounded.
-/

namespace GaloisForLFunctions.HTGeometry.LpDiagonal

open scoped ENNReal
open Filter Topology

variable {I : Type*}

/-! ## The reindexing unitary -/

/-- Reindexing `ℓ²(I)` along a bijection of the index set, as a unitary. -/
noncomputable def lpReindex (e : I ≃ I) : LpTwo I ≃ₗᵢ[ℂ] LpTwo I where
  toFun x :=
    ⟨fun i => (x : I → ℂ) (e.symm i), by
      refine memℓp_gen ?_
      have hx : Summable fun i : I => ‖(x : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
        (memℓp_gen_iff (by norm_num)).mp (lp.memℓp x)
      exact e.symm.summable_iff.mpr hx⟩
  invFun y :=
    ⟨fun i => (y : I → ℂ) (e i), by
      refine memℓp_gen ?_
      have hy : Summable fun i : I => ‖(y : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
        (memℓp_gen_iff (by norm_num)).mp (lp.memℓp y)
      exact e.summable_iff.mpr hy⟩
  left_inv x := by
    refine lp.ext ?_
    funext i
    simp
  right_inv y := by
    refine lp.ext ?_
    funext i
    simp
  map_add' x y := by
    refine lp.ext ?_
    funext i
    rfl
  map_smul' c x := by
    refine lp.ext ?_
    funext i
    rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq fun i => ‖(x : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal

@[simp] theorem lpReindex_coe (e : I ≃ I) (x : LpTwo I) (i : I) :
    ((lpReindex e x : LpTwo I) : I → ℂ) i = (x : I → ℂ) (e.symm i) := rfl

/-- The reindexing unitary as a bounded operator. -/
noncomputable def lpReindexCLM (e : I ≃ I) : LpTwo I →L[ℂ] LpTwo I :=
  (lpReindex e).toLinearIsometry.toContinuousLinearMap

@[simp] theorem lpReindexCLM_coe (e : I ≃ I) (x : LpTwo I) (i : I) :
    ((lpReindexCLM e x : LpTwo I) : I → ℂ) i = (x : I → ℂ) (e.symm i) := rfl

/-- Defect of the reindexing unitary from the identity. -/
noncomputable def lpReindexDefect (e : I ≃ I) : LpTwo I →L[ℂ] LpTwo I :=
  lpReindexCLM e - ContinuousLinearMap.id ℂ (LpTwo I)

theorem lpReindexDefect_coe (e : I ≃ I) (x : LpTwo I) (i : I) :
    ((lpReindexDefect e x : LpTwo I) : I → ℂ) i
      = (x : I → ℂ) (e.symm i) - (x : I → ℂ) i := by
  rw [lpReindexDefect]
  simp

/-! ## The vanishing and compactness dichotomies -/

variable [DecidableEq I]

theorem lpReindexDefect_single (e : I ≃ I) (i j : I) :
    ((lpReindexDefect e (lp.single (E := fun _ : I => ℂ) 2 i (1 : ℂ)) : LpTwo I) : I → ℂ) j
      = (if j = e i then (1 : ℂ) else 0) - (if j = i then (1 : ℂ) else 0) := by
  rw [lpReindexDefect_coe]
  simp only [lp.single_apply, Pi.single_apply]
  congr 1
  by_cases h : j = e i
  · subst h
    simp
  · have : e.symm j ≠ i := fun hc => h (by rw [← hc]; simp)
    simp [h, this]

theorem lpReindexDefect_eq_zero_iff (e : I ≃ I) :
    lpReindexDefect e = 0 ↔ ∀ i, e i = i := by
  constructor
  · intro h i
    by_contra hne
    have hval : ((lpReindexDefect e
        (lp.single (E := fun _ : I => ℂ) 2 i (1 : ℂ)) : LpTwo I) : I → ℂ) (e i) = 0 := by
      rw [h]
      simp
    rw [lpReindexDefect_single] at hval
    rw [if_neg (fun hc : e i = i => hne hc)] at hval
    norm_num at hval
  · intro h
    refine ContinuousLinearMap.ext fun x => ?_
    refine lp.ext ?_
    funext i
    rw [lpReindexDefect_coe]
    have hsymm : e.symm i = i := e.symm_apply_eq.2 (h i).symm
    rw [hsymm, sub_self]
    simp

theorem isCompactOperator_lpRankOneOff (j k : I) (a : ℂ) :
    IsCompactOperator (fun v : LpTwo I =>
      lp.single (E := fun _ : I => ℂ) 2 j (a * (v : I → ℂ) k)) := by
  have hc : IsCompactOperator ((lpSingleCLM (I := I) j) ∘
      (a • (lp.evalCLM ℂ (fun _ : I => ℂ) 2 k))) :=
    (isCompactOperator_lpSingleCLM j).comp_clm _
  exact hc

theorem isCompactOperator_offDiagFinset (e : I ≃ I) (S : Finset I) :
    IsCompactOperator (fun v : LpTwo I =>
      ∑ j ∈ S, (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
        - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j))) := by
  classical
  induction S using Finset.induction with
  | empty =>
      have h0 : IsCompactOperator (fun _ : LpTwo I => (0 : LpTwo I)) := isCompactOperator_zero
      have hfun : (fun _ : LpTwo I => (0 : LpTwo I))
          = fun v : LpTwo I => ∑ j ∈ (∅ : Finset I),
            (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
              - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j)) := by
        funext v
        simp
      rwa [hfun] at h0
  | insert a S ha ih =>
      have hone : IsCompactOperator (fun v : LpTwo I =>
          lp.single (E := fun _ : I => ℂ) 2 a ((1 : ℂ) * (v : I → ℂ) (e.symm a))
            - lp.single (E := fun _ : I => ℂ) 2 a ((1 : ℂ) * (v : I → ℂ) a)) :=
        (isCompactOperator_lpRankOneOff (I := I) a (e.symm a) 1).sub
          (isCompactOperator_lpRankOneOff (I := I) a a 1)
      have hstep : IsCompactOperator (fun v : LpTwo I =>
          (lp.single (E := fun _ : I => ℂ) 2 a ((1 : ℂ) * (v : I → ℂ) (e.symm a))
            - lp.single (E := fun _ : I => ℂ) 2 a ((1 : ℂ) * (v : I → ℂ) a)) +
            ∑ j ∈ S, (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
              - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j))) := hone.add ih
      have hfun : (fun v : LpTwo I =>
          (lp.single (E := fun _ : I => ℂ) 2 a ((1 : ℂ) * (v : I → ℂ) (e.symm a))
            - lp.single (E := fun _ : I => ℂ) 2 a ((1 : ℂ) * (v : I → ℂ) a)) +
            ∑ j ∈ S, (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
              - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j)))
          = fun v : LpTwo I => ∑ j ∈ insert a S,
            (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
              - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j)) := by
        funext v
        rw [Finset.sum_insert ha]
      rwa [hfun] at hstep

theorem lpReindexDefect_eq_finsum (e : I ≃ I) (hfin : {i : I | e i ≠ i}.Finite) (v : LpTwo I) :
    lpReindexDefect e v
      = ∑ j ∈ hfin.toFinset,
          (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
            - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j)) := by
  classical
  refine lp.ext ?_
  funext i
  rw [lpReindexDefect_coe, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_apply,
    one_mul]
  by_cases hi : e i = i
  · have hsymm : e.symm i = i := e.symm_apply_eq.2 hi.symm
    rw [hsymm, sub_self]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hne : i ≠ j := by
      intro hc
      subst hc
      exact (hfin.mem_toFinset.1 hj) hi
    simp [hne]
  · have hmem : i ∈ hfin.toFinset := hfin.mem_toFinset.2 hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hcon
      exact absurd hmem hcon

/-- **Finitely supported reindexing has compact defect.** -/
theorem isCompactOperator_lpReindexDefect_of_finite (e : I ≃ I)
    (hfin : {i : I | e i ≠ i}.Finite) : IsCompactOperator (lpReindexDefect e) := by
  have hsum := isCompactOperator_offDiagFinset (I := I) e hfin.toFinset
  have hfun : (fun v : LpTwo I => ∑ j ∈ hfin.toFinset,
      (lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) (e.symm j))
        - lp.single (E := fun _ : I => ℂ) 2 j ((1 : ℂ) * (v : I → ℂ) j)))
      = fun v : LpTwo I => lpReindexDefect e v := by
    funext v
    exact (lpReindexDefect_eq_finsum e hfin v).symm
  rwa [hfun] at hsum

/-! ## Finite coordinate combinations -/

theorem coe_sum_single {J : Type*} [DecidableEq J] (T : Finset J) (f : J → I) (c : J → ℂ)
    (i : I) :
    ((∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (f j) (c j) : LpTwo I) : I → ℂ) i
      = ∑ j ∈ T, (if f j = i then c j else 0) := by
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : f j = i
  · subst h
    simp
  · have h' : i ≠ f j := fun hc => h hc.symm
    simp [h, h']

/-- Pythagoras for a finite coordinate combination indexed injectively. -/
theorem norm_rpow_sum_single {J : Type*} [DecidableEq J] (T : Finset J) (f : J → I)
    (hf : Set.InjOn f T) (c : J → ℂ) :
    ‖(∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (f j) (c j) : LpTwo I)‖ ^ (2 : ℝ)
      = ∑ j ∈ T, ‖c j‖ ^ (2 : ℝ) := by
  classical
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [show ((2 : ℝ)) = (2 : ℝ≥0∞).toReal from h2.symm, lp.norm_rpow_eq_tsum hp]
  rw [tsum_eq_sum (s := T.image f) ?_]
  · rw [Finset.sum_image (fun a ha b hb hab => hf ha hb hab)]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    rw [coe_sum_single, Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      have h : f b ≠ f j := fun hc => hbj (hf hb hj hc)
      simp [h]
    · intro hc
      exact absurd hj hc
  · intro i hi
    rw [coe_sum_single]
    have hz : ∀ j ∈ T, (if f j = i then c j else 0) = 0 := by
      intro j hj
      have : f j ≠ i := fun hc => hi (Finset.mem_image.2 ⟨j, hj, hc⟩)
      simp [this]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    simp

theorem norm_sq_sum_single {J : Type*} [DecidableEq J] (T : Finset J) (f : J → I)
    (hf : Set.InjOn f T) (c : J → ℂ) :
    ‖(∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (f j) (c j) : LpTwo I)‖ ^ 2
      = ∑ j ∈ T, ‖c j‖ ^ 2 := by
  have h := norm_rpow_sum_single T f hf c
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num] at h
  rw [Real.rpow_natCast] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => Real.rpow_natCast _ 2

theorem lpReindexCLM_single (e : I ≃ I) (i : I) (a : ℂ) :
    lpReindexCLM e (lp.single (E := fun _ : I => ℂ) 2 i a)
      = lp.single (E := fun _ : I => ℂ) 2 (e i) a := by
  refine lp.ext ?_
  funext j
  rw [lpReindexCLM_coe]
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : j = e i
  · subst h
    simp
  · have h' : e.symm j ≠ i := fun hc => h (by rw [← hc]; simp)
    simp [h, h']

/-! ## Approximate reflection vectors along a chain -/

/-- Alternating coefficient of the chain vector of length `m + 1`. -/
noncomputable def chainCoeff (m j : ℕ) : ℂ := ((((-1 : ℝ) ^ j / Real.sqrt (m + 1)) : ℝ) : ℂ)

theorem sqrt_pos_of_succ (m : ℕ) : 0 < Real.sqrt ((m : ℝ) + 1) :=
  Real.sqrt_pos.2 (by positivity)

theorem norm_chainCoeff (m j : ℕ) : ‖chainCoeff m j‖ = 1 / Real.sqrt ((m : ℝ) + 1) := by
  rw [chainCoeff, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one,
    one_pow, abs_of_pos (sqrt_pos_of_succ m)]

theorem norm_chainCoeff_sq (m j : ℕ) : ‖chainCoeff m j‖ ^ 2 = 1 / ((m : ℝ) + 1) := by
  rw [norm_chainCoeff, div_pow, one_pow, Real.sq_sqrt (by positivity)]

theorem chainCoeff_sub_succ (m i : ℕ) :
    chainCoeff m i - chainCoeff m (i + 1)
      = ((((2 : ℝ) * (-1) ^ i / Real.sqrt ((m : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [chainCoeff, chainCoeff, ← Complex.ofReal_sub]
  congr 1
  rw [pow_succ]
  ring

theorem norm_chainCoeff_sub_succ_sq (m i : ℕ) :
    ‖chainCoeff m i - chainCoeff m (i + 1)‖ ^ 2 = 4 / ((m : ℝ) + 1) := by
  rw [chainCoeff_sub_succ, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, mul_one, abs_of_pos (sqrt_pos_of_succ m), div_pow,
    Real.sq_sqrt (by positivity)]
  norm_num

/-- Alternating unit vector along an `e`-chain of length `m + 1` starting at `x`. -/
noncomputable def chainVector (e : I ≃ I) (m : ℕ) (x : I) : LpTwo I :=
  ∑ j ∈ Finset.range (m + 1),
    lp.single (E := fun _ : I => ℂ) 2 ((e ^[j]) x) (chainCoeff m j)

theorem sum_norm_sq_chainCoeff (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), ‖chainCoeff m j‖ ^ 2 = 1 := by
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range (m + 1)) => norm_chainCoeff_sq m j,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

theorem norm_sq_chainVector (e : I ≃ I) (m : ℕ) (x : I)
    (hinj : Set.InjOn (fun j : ℕ => (e ^[j]) x) (Finset.range (m + 1))) :
    ‖chainVector e m x‖ ^ 2 = 1 := by
  rw [chainVector, norm_sq_sum_single (Finset.range (m + 1)) (fun j => (e ^[j]) x) hinj
    (chainCoeff m), sum_norm_sq_chainCoeff]

theorem norm_chainVector (e : I ≃ I) (m : ℕ) (x : I)
    (hinj : Set.InjOn (fun j : ℕ => (e ^[j]) x) (Finset.range (m + 1))) :
    ‖chainVector e m x‖ = 1 := by
  have h1 := norm_sq_chainVector e m x hinj
  nlinarith [norm_nonneg (chainVector e m x), h1]

/-- Coefficient of the defect along the extended chain. -/
noncomputable def chainDefectCoeff (m j : ℕ) : ℂ :=
  (if 1 ≤ j then chainCoeff m (j - 1) else 0) - (if j ≤ m then chainCoeff m j else 0)

theorem lpReindexDefect_chainVector (e : I ≃ I) (m : ℕ) (x : I) :
    lpReindexDefect e (chainVector e m x)
      = ∑ j ∈ Finset.range (m + 2),
          lp.single (E := fun _ : I => ℂ) 2 ((e ^[j]) x) (chainDefectCoeff m j) := by
  have hzero : ∀ i : I, lp.single (E := fun _ : I => ℂ) 2 i (0 : ℂ) = 0 := by
    intro i
    refine lp.ext ?_
    funext j
    simp
  have hsub : ∀ (i : I) (a b : ℂ),
      lp.single (E := fun _ : I => ℂ) 2 i a - lp.single (E := fun _ : I => ℂ) 2 i b
        = lp.single (E := fun _ : I => ℂ) 2 i (a - b) := by
    intro i a b
    refine lp.ext ?_
    funext j
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_apply]
    by_cases h : j = i <;> simp [h]
  have hA : lpReindexCLM e (chainVector e m x)
      = ∑ j ∈ Finset.range (m + 2), lp.single (E := fun _ : I => ℂ) 2 ((e ^[j]) x)
          (if 1 ≤ j then chainCoeff m (j - 1) else 0) := by
    rw [chainVector, map_sum]
    rw [Finset.sum_range_succ' (fun j => lp.single (E := fun _ : I => ℂ) 2 ((e ^[j]) x)
      (if 1 ≤ j then chainCoeff m (j - 1) else 0)) (m + 1)]
    have h0 : (if 1 ≤ 0 then chainCoeff m (0 - 1) else (0 : ℂ)) = 0 := by norm_num
    rw [h0, hzero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lpReindexCLM_single, ← Function.iterate_succ_apply' e j x]
    simp
  have hB : chainVector e m x
      = ∑ j ∈ Finset.range (m + 2), lp.single (E := fun _ : I => ℂ) 2 ((e ^[j]) x)
          (if j ≤ m then chainCoeff m j else 0) := by
    rw [Finset.sum_range_succ]
    have hlast : (if m + 1 ≤ m then chainCoeff m (m + 1) else 0) = (0 : ℂ) := by
      rw [if_neg (by omega)]
    rw [hlast, hzero, add_zero, chainVector]
    exact Finset.sum_congr rfl fun j hj => by
      rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  rw [lpReindexDefect, sub_apply, ContinuousLinearMap.id_apply, hA, hB,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => hsub _ _ _

theorem chainDefectCoeff_zero (m : ℕ) : chainDefectCoeff m 0 = -chainCoeff m 0 := by
  rw [chainDefectCoeff, if_neg (by omega), if_pos (Nat.zero_le m), zero_sub]

theorem chainDefectCoeff_last (m : ℕ) : chainDefectCoeff m (m + 1) = chainCoeff m m := by
  rw [chainDefectCoeff, if_pos (by omega), if_neg (by omega), sub_zero]
  norm_num

theorem chainDefectCoeff_mid (m i : ℕ) (hi : i < m) :
    chainDefectCoeff m (i + 1) = chainCoeff m i - chainCoeff m (i + 1) := by
  rw [chainDefectCoeff, if_pos (by omega), if_pos (by omega)]
  norm_num

theorem sum_norm_sq_chainDefectCoeff (m : ℕ) :
    ∑ j ∈ Finset.range (m + 2), ‖chainDefectCoeff m j‖ ^ 2
      = (4 * (m : ℝ) + 2) / ((m : ℝ) + 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => ‖chainDefectCoeff m j‖ ^ 2) m,
    chainDefectCoeff_last, chainDefectCoeff_zero, norm_neg, norm_chainCoeff_sq,
    norm_chainCoeff_sq]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [chainDefectCoeff_mid m i (Finset.mem_range.1 hi), norm_chainCoeff_sub_succ_sq]]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The defect of the chain vector has squared norm `(4m+2)/(m+1)`. -/
theorem norm_sq_lpReindexDefect_chainVector (e : I ≃ I) (m : ℕ) (x : I)
    (hinj : Set.InjOn (fun j : ℕ => (e ^[j]) x) (Finset.range (m + 2))) :
    ‖lpReindexDefect e (chainVector e m x)‖ ^ 2 = (4 * (m : ℝ) + 2) / ((m : ℝ) + 1) := by
  rw [lpReindexDefect_chainVector,
    norm_sq_sum_single (Finset.range (m + 2)) (fun j => (e ^[j]) x) hinj (chainDefectCoeff m),
    sum_norm_sq_chainDefectCoeff]

theorem lp_single_neg (i : I) (a : ℂ) :
    lp.single (E := fun _ : I => ℂ) 2 i (-a) = -lp.single (E := fun _ : I => ℂ) 2 i a := by
  refine lp.ext ?_
  funext j
  simp only [lp.coeFn_neg, Pi.neg_apply, lp.single_apply, Pi.single_apply]
  by_cases h : j = i <;> simp [h]

/-- Pythagoras for the difference of two coordinate combinations along disjoint index families. -/
theorem norm_sq_sum_single_sub {J : Type*} [DecidableEq J] (T : Finset J) (f g : J → I)
    (hf : Set.InjOn f T) (hg : Set.InjOn g T) (hfg : ∀ a ∈ T, ∀ b ∈ T, f a ≠ g b)
    (c d : J → ℂ) :
    ‖(∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (f j) (c j) : LpTwo I)
        - ∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (g j) (d j)‖ ^ 2
      = (∑ j ∈ T, ‖c j‖ ^ 2) + ∑ j ∈ T, ‖d j‖ ^ 2 := by
  classical
  have hcomb : (∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (f j) (c j) : LpTwo I)
      - ∑ j ∈ T, lp.single (E := fun _ : I => ℂ) 2 (g j) (d j)
      = ∑ p ∈ T.disjSum T, lp.single (E := fun _ : I => ℂ) 2
          (Sum.elim f g p) (Sum.elim c (fun j => -(d j)) p) := by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ T) => lp_single_neg (g j) (d j),
      Finset.sum_neg_distrib]
    abel
  have hinj : Set.InjOn (Sum.elim f g) ↑(T.disjSum T) := by
    rintro (a | a) ha (b | b) hb hab
    · have ha' : a ∈ T := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 ha)
      have hb' : b ∈ T := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 hb)
      exact congrArg Sum.inl (hf ha' hb' hab)
    · have ha' : a ∈ T := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 ha)
      have hb' : b ∈ T := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 hb)
      exact absurd hab (hfg a ha' b hb')
    · have ha' : a ∈ T := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 ha)
      have hb' : b ∈ T := Finset.inl_mem_disjSum.1 (Finset.mem_coe.1 hb)
      exact absurd hab.symm (hfg b hb' a ha')
    · have ha' : a ∈ T := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 ha)
      have hb' : b ∈ T := Finset.inr_mem_disjSum.1 (Finset.mem_coe.1 hb)
      exact congrArg Sum.inr (hg ha' hb' hab)
  rw [hcomb, norm_sq_sum_single _ (Sum.elim f g) hinj (Sum.elim c fun j => -(d j)),
    Finset.sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, norm_neg]

theorem norm_sq_sub_chainVector (e : I ≃ I) (m : ℕ) (x y : I)
    (hx : Set.InjOn (fun j : ℕ => (e ^[j]) x) (Finset.range (m + 1)))
    (hy : Set.InjOn (fun j : ℕ => (e ^[j]) y) (Finset.range (m + 1)))
    (hxy : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      (e ^[i]) x ≠ (e ^[j]) y) :
    ‖chainVector e m x - chainVector e m y‖ ^ 2 = 2 := by
  rw [chainVector, chainVector, norm_sq_sum_single_sub (Finset.range (m + 1))
    (fun j => (e ^[j]) x) (fun j => (e ^[j]) y) hx hy hxy (chainCoeff m) (chainCoeff m),
    sum_norm_sq_chainCoeff]
  norm_num

theorem norm_sq_sub_defect_chainVector (e : I ≃ I) (m : ℕ) (x y : I)
    (hx : Set.InjOn (fun j : ℕ => (e ^[j]) x) (Finset.range (m + 2)))
    (hy : Set.InjOn (fun j : ℕ => (e ^[j]) y) (Finset.range (m + 2)))
    (hxy : ∀ i ∈ Finset.range (m + 2), ∀ j ∈ Finset.range (m + 2),
      (e ^[i]) x ≠ (e ^[j]) y) :
    ‖lpReindexDefect e (chainVector e m x) - lpReindexDefect e (chainVector e m y)‖ ^ 2
      = 2 * ((4 * (m : ℝ) + 2) / ((m : ℝ) + 1)) := by
  rw [lpReindexDefect_chainVector, lpReindexDefect_chainVector,
    norm_sq_sum_single_sub (Finset.range (m + 2)) (fun j => (e ^[j]) x) (fun j => (e ^[j]) y)
      hx hy hxy (chainDefectCoeff m) (chainDefectCoeff m), sum_norm_sq_chainDefectCoeff]
  ring

/-! ## Essential norm two -/

set_option maxHeartbeats 2000000 in
/-- **Distance two from every compact operator.**  If the bijection admits, for every chain length
and every finite count, that many pairwise disjoint chains, then the defect stays at distance two
from the compact operators: its essential norm is exactly two. -/
theorem two_le_norm_lpReindexDefect_sub (e : I ≃ I)
    (hch : ∀ m N : ℕ, ∃ x : Fin N → I,
      (∀ k, Set.InjOn (fun j : ℕ => (e ^[j]) (x k)) (Finset.range (m + 2))) ∧
      ∀ k l, k ≠ l → ∀ i ∈ Finset.range (m + 2), ∀ j ∈ Finset.range (m + 2),
        (e ^[i]) (x k) ≠ (e ^[j]) (x l))
    {K : LpTwo I →L[ℂ] LpTwo I} (hK : IsCompactOperator K) :
    2 ≤ ‖lpReindexDefect e - K‖ := by
  classical
  refine le_of_forall_pos_le_add fun ε hεpos => ?_
  set T := lpReindexDefect e with hT
  set d : ℝ := min 1 ε with hd
  have hdpos : 0 < d := lt_min one_pos hεpos
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdε : d ≤ ε := min_le_right _ _
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 / ((m : ℝ) + 1) ≤ d := by
    obtain ⟨m, hm⟩ := exists_nat_gt (2 / d)
    refine ⟨m, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    have : 2 / d < (m : ℝ) := hm
    rw [div_lt_iff₀ hdpos] at this
    nlinarith
  obtain ⟨C, hC, hpre⟩ := hK
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨t, htfin, htcov⟩ :=
    Metric.totallyBounded_iff.1 hC.totallyBounded (d * r / 8) (by positivity)
  obtain ⟨x, hxinj, hxdisj⟩ := hch m (htfin.toFinset.card + 1)
  set u : Fin (htfin.toFinset.card + 1) → LpTwo I := fun k => chainVector e m (x k) with hu
  have hu1 : ∀ k, ‖u k‖ = 1 := fun k =>
    norm_chainVector e m (x k) ((hxinj k).mono (by
      intro j hj
      simp only [Finset.coe_range, Set.mem_Iio] at hj ⊢
      omega))
  set c : ℂ := ((r / 2 : ℝ) : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc, ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hcnorm : ‖c‖ = r / 2 := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmem : ∀ k, K (c • u k) ∈ C := by
    intro k
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, norm_smul, hcnorm, hu1 k, mul_one]
    linarith
  have hcov : ∀ k, ∃ y ∈ t, K (c • u k) ∈ Metric.ball y (d * r / 8) := by
    intro k
    have := htcov (hmem k)
    simpa using this
  choose y hy hyball using hcov
  obtain ⟨k, -, l, -, hkl, hyeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin (htfin.toFinset.card + 1))))
      (t := htfin.toFinset) (by simp) (fun k _ => htfin.mem_toFinset.2 (hy k))
  have hKclose : ‖K (c • u k) - K (c • u l)‖ < d * r / 4 := by
    have h1 := hyball k
    have h2 := hyball l
    rw [Metric.mem_ball] at h1 h2
    rw [hyeq] at h1
    have htri := dist_triangle (K (c • u k)) (y l) (K (c • u l))
    rw [dist_eq_norm] at htri
    have h2' : dist (y l) (K (c • u l)) < d * r / 8 := by rwa [dist_comm] at h2
    linarith [htri, h1, h2']
  have hdisj : ∀ i ∈ Finset.range (m + 2), ∀ j ∈ Finset.range (m + 2),
      (e ^[i]) (x k) ≠ (e ^[j]) (x l) := hxdisj k l hkl
  have hdisj1 : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (m + 1),
      (e ^[i]) (x k) ≠ (e ^[j]) (x l) := by
    intro i hi j hj
    exact hdisj i (by simp only [Finset.mem_range] at hi ⊢; omega)
      j (by simp only [Finset.mem_range] at hj ⊢; omega)
  have hsub2 : ‖u k - u l‖ ^ 2 = 2 :=
    norm_sq_sub_chainVector e m (x k) (x l)
      ((hxinj k).mono (by intro j hj; simp only [Finset.coe_range, Set.mem_Iio] at hj ⊢; omega))
      ((hxinj l).mono (by intro j hj; simp only [Finset.coe_range, Set.mem_Iio] at hj ⊢; omega))
      hdisj1
  have hTsub : ‖T (u k) - T (u l)‖ ^ 2 = 2 * ((4 * (m : ℝ) + 2) / ((m : ℝ) + 1)) :=
    norm_sq_sub_defect_chainVector e m (x k) (x l) (hxinj k) (hxinj l) hdisj
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs
  have hsnorm : ‖s‖ = (Real.sqrt 2)⁻¹ := by
    rw [hs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt 2)⁻¹)]
  set z : LpTwo I := s • (u k - u l) with hz
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hzn : ‖z‖ = 1 := by
    rw [hz, norm_smul, hsnorm]
    have h2 : ‖u k - u l‖ = Real.sqrt 2 := by
      nlinarith [norm_nonneg (u k - u l), hsub2, Real.sqrt_nonneg (2:ℝ), hsq2]
    rw [h2, inv_mul_cancel₀ (by positivity)]
  have hTz : ‖T z‖ ^ 2 = (4 * (m : ℝ) + 2) / ((m : ℝ) + 1) := by
    have hTsub' : ‖T (u k - u l)‖ ^ 2 = 2 * ((4 * (m : ℝ) + 2) / ((m : ℝ) + 1)) := by
      rw [map_sub]
      exact hTsub
    rw [hz, map_smul, norm_smul, hsnorm, mul_pow, hTsub']
    rw [inv_pow, hsq2]
    field_simp
  have hTzge : 2 - d / 2 ≤ ‖T z‖ := by
    have hval : (4 * (m : ℝ) + 2) / ((m : ℝ) + 1) = 4 - 2 / ((m : ℝ) + 1) := by
      have : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have hge : (2 - d / 2) ^ 2 ≤ ‖T z‖ ^ 2 := by
      rw [hTz, hval]
      nlinarith [hm, hdpos, hd1]
    nlinarith [norm_nonneg (T z), hge, hdpos, hd1]
  have hKz : ‖K z‖ ≤ d / 2 := by
    have hkey : K (c • u k) - K (c • u l) = c • K (u k - u l) := by
      rw [map_smul, map_smul, map_sub, smul_sub]
    have hnorm : ‖c‖ * ‖K (u k - u l)‖ < d * r / 4 := by
      rw [← norm_smul, ← hkey]
      exact hKclose
    have hX : ‖K (u k - u l)‖ < d / 2 := by
      rw [hcnorm] at hnorm
      nlinarith [norm_nonneg (K (u k - u l)), hr, hdpos]
    have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [hsq2, Real.sqrt_nonneg (2 : ℝ)]
    have hs1 : ‖s‖ ≤ 1 := by
      rw [hsnorm]
      exact inv_le_one_of_one_le₀ hsqrt2
    calc ‖K z‖ = ‖s‖ * ‖K (u k - u l)‖ := by rw [hz, map_smul, norm_smul]
      _ ≤ 1 * ‖K (u k - u l)‖ := by nlinarith [norm_nonneg (K (u k - u l)), hs1]
      _ ≤ d / 2 := by linarith
  have hfinal : 2 - d ≤ ‖T - K‖ := by
    have h1 : ‖(T - K) z‖ ≤ ‖T - K‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    rw [hzn, mul_one] at h1
    have h2 : ‖(T - K) z‖ = ‖T z - K z‖ := by rw [sub_apply]
    have h3 : ‖T z‖ - ‖K z‖ ≤ ‖T z - K z‖ := norm_sub_norm_le _ _
    rw [h2] at h1
    linarith [hTzge, hKz, h1, h3]
  linarith [hfinal, hdε]

/-! ## The noncompact half -/

/-- From an infinite moved set one can extract a sequence of moved indices whose two-element
orbits are pairwise disjoint. -/
theorem exists_separated_moved (e : I ≃ I) (hinf : {i : I | e i ≠ i}.Infinite) :
    ∃ g : ℕ → I, (∀ k, e (g k) ≠ g k) ∧
      ∀ k l : ℕ, k < l → g l ≠ g k ∧ g l ≠ e (g k) ∧ e (g l) ≠ g k ∧ e (g l) ≠ e (g k) := by
  classical
  have hstep : ∀ S : Finset I, ∃ a : I, e a ≠ a ∧ a ∉ S ∧ e a ∉ S := by
    intro S
    have hbad : ({i : I | e i ≠ i} \ (↑S ∪ e.symm '' ↑S)).Infinite :=
      hinf.sdiff (S.finite_toSet.union (S.finite_toSet.image _))
    obtain ⟨a, ha⟩ := hbad.nonempty
    refine ⟨a, ha.1, fun hc => ha.2 (Set.mem_union_left _ (Finset.mem_coe.2 hc)), fun hc => ?_⟩
    exact ha.2 (Set.mem_union_right _ ⟨e a, Finset.mem_coe.2 hc, e.symm_apply_apply a⟩)
  choose f hf0 hf1 hf2 using hstep
  let F : ℕ → Finset I := fun n =>
    Nat.rec (∅ : Finset I) (fun _ S => insert (f S) (insert (e (f S)) S)) n
  have hsub : ∀ n, F n ⊆ F (n + 1) := by
    intro n x hx
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hmono : Monotone F := monotone_nat_of_le_succ hsub
  have hmemself : ∀ n, f (F n) ∈ F (n + 1) := fun n => Finset.mem_insert_self _ _
  have hmemimg : ∀ n, e (f (F n)) ∈ F (n + 1) := fun n =>
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  refine ⟨fun n => f (F n), fun k => hf0 _, fun k l hkl => ?_⟩
  have hk1 : f (F k) ∈ F l := hmono hkl (hmemself k)
  have hk2 : e (f (F k)) ∈ F l := hmono hkl (hmemimg k)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcon
    have hcon' : f (F l) = f (F k) := hcon
    exact hf1 (F l) (hcon' ▸ hk1)
  · intro hcon
    have hcon' : f (F l) = e (f (F k)) := hcon
    exact hf1 (F l) (hcon' ▸ hk2)
  · intro hcon
    have hcon' : e (f (F l)) = f (F k) := hcon
    exact hf2 (F l) (hcon' ▸ hk1)
  · intro hcon
    have hcon' : e (f (F l)) = e (f (F k)) := hcon
    exact hf2 (F l) (hcon' ▸ hk2)

/-- **Infinitely supported reindexing has noncompact defect.** -/
theorem not_isCompactOperator_lpReindexDefect_of_infinite (e : I ≃ I)
    (hinf : {i : I | e i ≠ i}.Infinite) : ¬ IsCompactOperator (lpReindexDefect e) := by
  classical
  obtain ⟨g, hmov, hsep⟩ := exists_separated_moved e hinf
  intro hcomp
  obtain ⟨K, hK, hpre⟩ := hcomp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  set c : ℂ := ((ε / 2 : ℝ) : ℂ) with hc
  set v : ℕ → LpTwo I := fun k => c • lp.single (E := fun _ : I => ℂ) 2 (g k) (1 : ℂ) with hv
  have hnormc : ‖c‖ = ε / 2 := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hvnorm : ∀ k, ‖v k‖ = ε / 2 := by
    intro k
    rw [hv]
    simp only
    rw [norm_smul, hnormc, lp.norm_single (by norm_num), norm_one, mul_one]
  set y : ℕ → LpTwo I := fun k => lpReindexDefect e (v k) with hy
  have hymem : ∀ k, y k ∈ K := by
    intro k
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, hvnorm]
    linarith
  have hycoe : ∀ k j, ((y k : LpTwo I) : I → ℂ) j
      = c * ((if j = e (g k) then (1 : ℂ) else 0) - (if j = g k then (1 : ℂ) else 0)) := by
    intro k j
    rw [hy]
    simp only
    rw [hv]
    simp only
    rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lpReindexDefect_single]
  have hsepy : ∀ k l : ℕ, k < l → ε / 2 ≤ dist (y k) (y l) := by
    intro k l hkl
    obtain ⟨h1, h2, h3, h4⟩ := hsep k l hkl
    have hval : ((y k - y l : LpTwo I) : I → ℂ) (g k) = -c := by
      rw [lp.coeFn_sub, Pi.sub_apply, hycoe, hycoe]
      rw [if_neg (fun hcon : g k = e (g k) => hmov k hcon.symm), if_pos rfl,
        if_neg (fun hcon : g k = e (g l) => h3 hcon.symm),
        if_neg (fun hcon : g k = g l => h1 hcon.symm)]
      ring
    have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (y k - y l) (g k)
    rw [hval, norm_neg, hnormc] at hle
    rwa [dist_eq_norm]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hymem
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 4) (by linarith)
  have h1 := hN N (le_refl N)
  have h2 := hN (N + 1) (Nat.le_succ N)
  have hd : dist (y (φ N)) (y (φ (N + 1))) < ε / 2 := by
    calc dist (y (φ N)) (y (φ (N + 1)))
        ≤ dist (y (φ N)) a + dist a (y (φ (N + 1))) := dist_triangle _ _ _
      _ < ε / 4 + ε / 4 := by
          rw [dist_comm a]
          exact add_lt_add h1 h2
      _ = ε / 2 := by ring
  have hge := hsepy (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))
  linarith

/-- **The reindexing dichotomy.**  The defect of a reindexing unitary is compact exactly when the
bijection moves only finitely many indices. -/
theorem isCompactOperator_lpReindexDefect_iff (e : I ≃ I) :
    IsCompactOperator (lpReindexDefect e) ↔ {i : I | e i ≠ i}.Finite := by
  constructor
  · intro h
    by_contra hinf
    exact not_isCompactOperator_lpReindexDefect_of_infinite e hinf h
  · exact isCompactOperator_lpReindexDefect_of_finite e

end GaloisForLFunctions.HTGeometry.LpDiagonal
