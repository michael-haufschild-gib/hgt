import Mathlib

/-!
# Bounded diagonal operators on `ℓ²` over an arbitrary index type

Multiplication by a uniformly bounded family `c : I → ℂ` is a bounded operator on
`lp (fun _ : I => ℂ) 2` of norm at most the bound, sending each coordinate vector to its scalar
multiple.  If the family vanishes along the cofinite filter, the operator is compact: the
truncations to the finite sets `{i : 1/(n+1) ≤ ‖c i‖}` are finite sums of rank-one coordinate
operators, and they converge to it in operator norm.

The index type is arbitrary, so this covers diagonal operators indexed by primes, prime powers, or
any other countable or uncountable label set.
-/

namespace GaloisForLFunctions.HTGeometry.LpDiagonal

open scoped ENNReal
open Filter Topology

variable {I : Type*}

/-- The complex `ℓ²` space on an arbitrary index type. -/
abbrev LpTwo (I : Type*) : Type _ := lp (fun _ : I => ℂ) 2

theorem memℓp_diag {c : I → ℂ} {M : ℝ} (hc : ∀ i, ‖c i‖ ≤ M) (v : LpTwo I) :
    Memℓp (fun i => c i * (v : I → ℂ) i) 2 := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hq : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hv : Summable (fun i => ‖(v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp v)
  refine memℓp_gen (Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (hv.mul_left (M ^ 2)))
  rw [hq] at hv ⊢
  rw [Real.rpow_two, Real.rpow_two, norm_mul, mul_pow]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hc i)
  have hci : ‖c i‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (c i), hc i]
  nlinarith [sq_nonneg ‖(v : I → ℂ) i‖, norm_nonneg ((v : I → ℂ) i)]

/-- Multiplication by a bounded family, as a linear map on `ℓ²(I)`. -/
noncomputable def lpDiagLin (c : I → ℂ) (M : ℝ) (hc : ∀ i, ‖c i‖ ≤ M) :
    LpTwo I →ₗ[ℂ] LpTwo I where
  toFun v := ⟨fun i => c i * (v : I → ℂ) i, memℓp_diag hc v⟩
  map_add' v w := by
    refine lp.ext ?_
    funext i
    simp [mul_add]
  map_smul' a v := by
    refine lp.ext ?_
    funext i
    simp [mul_left_comm]

@[simp] theorem lpDiagLin_coe (c : I → ℂ) (M : ℝ) (hc : ∀ i, ‖c i‖ ≤ M) (v : LpTwo I) (i : I) :
    ((lpDiagLin c M hc v : LpTwo I) : I → ℂ) i = c i * (v : I → ℂ) i := rfl

theorem norm_lpDiagLin_le (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M) (v : LpTwo I) :
    ‖lpDiagLin c M hc v‖ ≤ M * ‖v‖ := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hq : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hv : Summable (fun i => ‖(v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (lp.memℓp v)
  have h1 : ‖lpDiagLin c M hc v‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' i, ‖c i * (v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum hp]
    rfl
  have h2 : ‖v‖ ^ (2 : ℝ≥0∞).toReal = ∑' i, ‖(v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    lp.norm_rpow_eq_tsum hp v
  have hbound : ∀ i, ‖c i * (v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ M ^ 2 * ‖(v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal := by
    intro i
    rw [hq, Real.rpow_two, Real.rpow_two, norm_mul, mul_pow]
    have hci : ‖c i‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (c i), hc i]
    nlinarith [sq_nonneg ‖(v : I → ℂ) i‖, norm_nonneg ((v : I → ℂ) i)]
  have hsum2 : Summable (fun i => ‖c i * (v : I → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (memℓp_gen_iff hp).mp (memℓp_diag hc v)
  have hle : ‖lpDiagLin c M hc v‖ ^ (2 : ℝ≥0∞).toReal ≤ M ^ 2 * ‖v‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [h1, h2, ← tsum_mul_left]
    exact hsum2.tsum_le_tsum hbound (hv.mul_left (M ^ 2))
  rw [hq, Real.rpow_two, Real.rpow_two] at hle
  have hfin : ‖lpDiagLin c M hc v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hfin
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at this

/-- **The diagonal operator of a bounded family on `ℓ²(I)`.** -/
noncomputable def lpDiag (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M) :
    LpTwo I →L[ℂ] LpTwo I :=
  (lpDiagLin c M hc).mkContinuous M (norm_lpDiagLin_le c M hM hc)

@[simp] theorem lpDiag_coe (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M)
    (v : LpTwo I) (i : I) :
    ((lpDiag c M hM hc v : LpTwo I) : I → ℂ) i = c i * (v : I → ℂ) i := rfl

theorem norm_lpDiag_le (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M) :
    ‖lpDiag c M hM hc‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

theorem lpDiag_single [DecidableEq I] (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M)
    (i : I) :
    lpDiag c M hM hc (lp.single 2 i (1 : ℂ)) = c i • lp.single 2 i (1 : ℂ) := by
  refine lp.ext ?_
  funext j
  rw [lpDiag_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
  by_cases h : j = i <;> simp [h]



variable [DecidableEq I]

/-- The coordinate injection `ℂ → ℓ²(I)`, as a bounded operator. -/
noncomputable def lpSingleCLM (i : I) : ℂ →L[ℂ] LpTwo I :=
  LinearMap.mkContinuous (lp.lsingle (E := fun _ : I => ℂ) (𝕜 := ℂ) 2 i) 1 (fun a => by
    rw [one_mul]
    show ‖lp.single (E := fun _ : I => ℂ) 2 i a‖ ≤ ‖a‖
    rw [lp.norm_single (by norm_num)])

theorem isCompactOperator_lpSingleCLM (i : I) : IsCompactOperator (lpSingleCLM (I := I) i) :=
  isCompactOperator_of_locallyCompactSpace_rng _

/-- Every diagonal rank-one coordinate operator on `ℓ²(I)` is compact. -/
theorem isCompactOperator_lpRankOne (i : I) (a : ℂ) :
    IsCompactOperator (fun v : LpTwo I =>
      lp.single (E := fun _ : I => ℂ) 2 i (a * (v : I → ℂ) i)) := by
  have hc : IsCompactOperator ((lpSingleCLM (I := I) i) ∘
      (a • (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i))) :=
    (isCompactOperator_lpSingleCLM i).comp_clm _
  have hfun : ((lpSingleCLM (I := I) i) ∘ (a • (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i)))
      = fun v : LpTwo I => lp.single (E := fun _ : I => ℂ) 2 i (a * (v : I → ℂ) i) := rfl
  rwa [hfun] at hc

/-- Finite diagonal truncations are compact. -/
theorem isCompactOperator_lpDiagFinset (c : I → ℂ) (S : Finset I) :
    IsCompactOperator (fun v : LpTwo I =>
      ∑ i ∈ S, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      have h0 : IsCompactOperator (fun _ : LpTwo I => (0 : LpTwo I)) := isCompactOperator_zero
      have hfun : (fun _ : LpTwo I => (0 : LpTwo I))
          = fun v : LpTwo I =>
            ∑ i ∈ (∅ : Finset I), lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i) := by
        funext v
        simp
      rwa [hfun] at h0
  | insert j S hj ih =>
      have hstep0 := (isCompactOperator_lpRankOne (I := I) j (c j)).add ih
      have hstep : IsCompactOperator (fun v : LpTwo I =>
          lp.single (E := fun _ : I => ℂ) 2 j (c j * (v : I → ℂ) j) +
            ∑ i ∈ S, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i)) := hstep0
      have hfun : (fun v : LpTwo I =>
            lp.single (E := fun _ : I => ℂ) 2 j (c j * (v : I → ℂ) j) +
              ∑ i ∈ S, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i))
          = fun v : LpTwo I =>
            ∑ i ∈ insert j S, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i) := by
        funext v
        rw [Finset.sum_insert hj]
      rwa [hfun] at hstep

theorem lpDiag_indicator_eq_sum (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (S : Finset I) (hc : ∀ i, ‖(if i ∈ S then c i else 0 : ℂ)‖ ≤ M) (v : LpTwo I) :
    (lpDiag (fun i => if i ∈ S then c i else 0) M hM hc v : LpTwo I)
      = ∑ i ∈ S, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i) := by
  classical
  refine lp.ext ?_
  funext j
  rw [lpDiag_coe]
  have hrhs : ((∑ i ∈ S, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i) :
      LpTwo I) : I → ℂ) j
      = ∑ i ∈ S, (if j = i then c i * (v : I → ℂ) i else 0) := by
    rw [lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lp.single_apply, Pi.single_apply]
  rw [hrhs]
  by_cases hjS : j ∈ S
  · rw [if_pos hjS, Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro i _ hi
      rw [if_neg (fun h => hi h.symm)]
    · intro hmem
      exact absurd hjS hmem
  · rw [if_neg hjS, zero_mul]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    rw [if_neg]
    intro h
    exact hjS (h ▸ hi)



omit [DecidableEq I] in
theorem finite_setOf_le_norm_of_tendsto_cofinite {c : I → ℂ}
    (hlim : Tendsto (fun i => ‖c i‖) cofinite (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ ‖c i‖}.Finite := by
  have h := hlim (Iio_mem_nhds hε)
  have hfin := Filter.mem_cofinite.mp h
  refine hfin.subset ?_
  intro i hi
  simpa using not_lt.mpr hi

/-- **A diagonal operator whose family vanishes along the cofinite filter is compact.** -/
theorem isCompactOperator_lpDiag (c : I → ℂ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i, ‖c i‖ ≤ M)
    (hlim : Tendsto (fun i => ‖c i‖) cofinite (nhds 0)) :
    IsCompactOperator (lpDiag c M hM hc) := by
  classical
  have hpos : ∀ n : ℕ, (0:ℝ) < 1 / (n + 1) := by
    intro n
    positivity
  set S : ℕ → Finset I := fun n =>
    (finite_setOf_le_norm_of_tendsto_cofinite hlim (hpos n)).toFinset with hS
  have hcut : ∀ (n : ℕ) (i : I), ‖(if i ∈ S n then c i else 0 : ℂ)‖ ≤ M := by
    intro n i
    by_cases h : i ∈ S n
    · rw [if_pos h]; exact hc i
    · rw [if_neg h]; simpa using hM
  have htail : ∀ (n : ℕ) (i : I), ‖(if i ∈ S n then 0 else c i : ℂ)‖ ≤ 1 / (n + 1) := by
    intro n i
    by_cases h : i ∈ S n
    · rw [if_pos h]
      simpa using (hpos n).le
    · rw [if_neg h]
      have : i ∉ {i | 1 / ((n : ℝ) + 1) ≤ ‖c i‖} := by
        simpa [hS] using h
      exact le_of_lt (by simpa using not_le.mp (by simpa using this))
  set T : ℕ → (LpTwo I →L[ℂ] LpTwo I) := fun n =>
    lpDiag (fun i => if i ∈ S n then c i else 0) M hM (hcut n) with hT
  have hTcompact : ∀ n, IsCompactOperator (T n) := by
    intro n
    have h := isCompactOperator_lpDiagFinset (I := I) c (S n)
    have hfun : (fun v : LpTwo I =>
        ∑ i ∈ S n, lp.single (E := fun _ : I => ℂ) 2 i (c i * (v : I → ℂ) i)) = (T n) := by
      funext v
      exact (lpDiag_indicator_eq_sum c M hM (S n) (hcut n) v).symm
    rwa [hfun] at h
  have hdiff : ∀ n, ‖lpDiag c M hM hc - T n‖ ≤ 1 / (n + 1) := by
    intro n
    have hEq : lpDiag c M hM hc - T n
        = lpDiag (fun i => if i ∈ S n then 0 else c i) (1 / (n + 1)) (hpos n).le (htail n) := by
      refine ContinuousLinearMap.ext (fun v => ?_)
      refine lp.ext ?_
      funext i
      rw [sub_apply]
      have hsub : ((lpDiag c M hM hc v - T n v : LpTwo I) : I → ℂ) i
          = c i * (v : I → ℂ) i - (if i ∈ S n then c i else 0) * (v : I → ℂ) i := by
        rw [lp.coeFn_sub, Pi.sub_apply, lpDiag_coe, hT]
        rfl
      rw [hsub, lpDiag_coe]
      by_cases h : i ∈ S n <;> simp [h]
    rw [hEq]
    exact norm_lpDiag_le _ _ _ _
  have htend : Tendsto T atTop (nhds (lpDiag c M hM hc)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← norm_neg]
    simpa using hdiff n
  exact isCompactOperator_of_tendsto htend (Filter.Eventually.of_forall hTcompact)

end GaloisForLFunctions.HTGeometry.LpDiagonal
