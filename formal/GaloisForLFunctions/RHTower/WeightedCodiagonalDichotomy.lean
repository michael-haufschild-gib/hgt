import Mathlib
import GaloisForLFunctions.HTGeometry.DiagonalSummableOfFactors
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.RHTower.ArithmeticSchurExactNormRiggingNoGo

/-!
# The closability dichotomy for weighted Hilbert codiagonals

Let `H` be a nonzero complex Banach space and let `a : ℕ → ℂ` be a scalar weight sequence.  On the
finitely supported vectors of `ℓ²(ℕ; H)` the *weighted codiagonal*

```text
C_a x = ∑_m a_m x_m
```

is a well-defined linear map into `H`.  This module proves that exactly one of two things happens:

* `a ∈ ℓ²`, in which case `C_a` is the restriction of a genuine bounded operator on all of
  `ℓ²(ℕ; H)` whose operator norm is *exactly* `‖a‖₂`; or
* `a ∉ ℓ²`, in which case `C_a` has no closed extension at all: an explicit normalised graph-null
  sequence has vanishing source norm and constant nonzero response.

In particular the unweighted codiagonal `a ≡ 1` is never closable, so no unbounded closed scalar
row can erase infinitely many orthogonal labels while acting by one fixed scalar on each label.
-/

namespace RHTower

open scoped BigOperators
open Filter Topology

/-! ## The algebraic core and its two norms -/

section Core

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
/-- A finitely supported vector lies in every `ℓ^p` space. -/
theorem memℓp_finsupp (x : ℕ →₀ H) : Memℓp (fun i => x i) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_of_ne_finset_zero (s := x.support) fun i hi => ?_
  simp [Finsupp.notMem_support_iff.mp hi]

/-- The algebraic core of `ℓ²(ℕ; H)`: finitely supported vectors, embedded. -/
noncomputable def codiagEmbed : (ℕ →₀ H) →ₗ[ℂ] lp (fun _ : ℕ => H) 2 where
  toFun x := ⟨fun i => x i, memℓp_finsupp x⟩
  map_add' x y := by apply Subtype.ext; funext i; simp
  map_smul' c x := by apply Subtype.ext; funext i; simp

@[simp] theorem codiagEmbed_apply (x : ℕ →₀ H) (i : ℕ) : (codiagEmbed x : ℕ → H) i = x i := rfl

/-- The weighted codiagonal on the algebraic core. -/
noncomputable def codiag (a : ℕ → ℂ) : (ℕ →₀ H) →ₗ[ℂ] H :=
  Finsupp.lsum ℂ fun m => a m • (LinearMap.id : H →ₗ[ℂ] H)

theorem codiag_apply (a : ℕ → ℂ) (x : ℕ →₀ H) :
    codiag a x = ∑ m ∈ x.support, a m • x m := by
  simp [codiag, Finsupp.lsum_apply, Finsupp.sum]

/-- The `ℓ²` norm of a vector of the algebraic core. -/
theorem norm_codiagEmbed_sq (x : ℕ →₀ H) :
    ‖(codiagEmbed x : lp (fun _ : ℕ => H) 2)‖ ^ 2 = ∑ m ∈ x.support, ‖x m‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (codiagEmbed x)
  have h' : ‖(codiagEmbed x : lp (fun _ : ℕ => H) 2)‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 := by
    simpa using h
  rw [h']
  refine tsum_eq_sum fun i hi => ?_
  simp [Finsupp.notMem_support_iff.mp hi]

end Core

/-! ## The square-summable case: an exactly normed bounded operator -/

section Bounded

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
variable {a : ℕ → ℂ}

/-- The `ℓ²` norm of the weight sequence. -/
noncomputable def weightNorm (a : ℕ → ℂ) : ℝ := Real.sqrt (∑' m, ‖a m‖ ^ 2)

theorem weightNorm_nonneg (a : ℕ → ℂ) : 0 ≤ weightNorm a := Real.sqrt_nonneg _

omit [CompleteSpace H] in
theorem summable_norm_smul (ha : Summable fun m => ‖a m‖ ^ 2)
    (x : lp (fun _ : ℕ => H) 2) : Summable fun m => ‖a m • (x : ℕ → H) m‖ := by
  have hx : Summable fun m => ‖(x : ℕ → H) m‖ ^ 2 := by
    have h := lp.memℓp x
    rw [memℓp_gen_iff (by norm_num)] at h
    simpa using h
  have := GaloisForLFunctions.summable_mul_of_summable_sq (a := fun m => ‖a m‖)
    (c := fun m => ‖(x : ℕ → H) m‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ha hx
  simpa [norm_smul] using this

theorem summable_smul (ha : Summable fun m => ‖a m‖ ^ 2) (x : lp (fun _ : ℕ => H) 2) :
    Summable fun m => a m • (x : ℕ → H) m :=
  Summable.of_norm (summable_norm_smul ha x)

/-- The bounded weighted codiagonal on all of `ℓ²(ℕ; H)`, defined by its convergent series. -/
noncomputable def codiagMap (ha : Summable fun m => ‖a m‖ ^ 2) :
    lp (fun _ : ℕ => H) 2 →ₗ[ℂ] H where
  toFun x := ∑' m, a m • (x : ℕ → H) m
  map_add' x y := by
    have h : ∀ m, a m • ((x + y : lp (fun _ : ℕ => H) 2) : ℕ → H) m
        = a m • (x : ℕ → H) m + a m • (y : ℕ → H) m := by
      intro m
      have hc : ((x + y : lp (fun _ : ℕ => H) 2) : ℕ → H) m
          = (x : ℕ → H) m + (y : ℕ → H) m := by rw [lp.coeFn_add]; rfl
      rw [hc, smul_add]
    simp only [h]
    exact (summable_smul ha x).tsum_add (summable_smul ha y)
  map_smul' c x := by
    have h : ∀ m, a m • ((c • x : lp (fun _ : ℕ => H) 2) : ℕ → H) m
        = c • (a m • (x : ℕ → H) m) := by
      intro m
      have hc : ((c • x : lp (fun _ : ℕ => H) 2) : ℕ → H) m = c • (x : ℕ → H) m := by
        rw [lp.coeFn_smul]; rfl
      rw [hc, smul_comm]
    simp only [h, RingHom.id_apply]
    exact tsum_const_smul'' c

theorem codiagMap_apply (ha : Summable fun m => ‖a m‖ ^ 2) (x : lp (fun _ : ℕ => H) 2) :
    codiagMap ha x = ∑' m, a m • (x : ℕ → H) m := rfl

theorem norm_codiagMap_le (ha : Summable fun m => ‖a m‖ ^ 2) (x : lp (fun _ : ℕ => H) 2) :
    ‖codiagMap (H := H) ha x‖ ≤ weightNorm a * ‖x‖ := by
  have hx : Summable fun m => ‖(x : ℕ → H) m‖ ^ 2 := by
    have h := lp.memℓp x
    rw [memℓp_gen_iff (by norm_num)] at h
    simpa using h
  have hnx : ‖x‖ = Real.sqrt (∑' m, ‖(x : ℕ → H) m‖ ^ 2) := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
    have h' : ‖x‖ ^ 2 = ∑' m, ‖(x : ℕ → H) m‖ ^ 2 := by simpa using h
    rw [← h', Real.sqrt_sq (norm_nonneg _)]
  calc ‖codiagMap (H := H) ha x‖ ≤ ∑' m, ‖a m • (x : ℕ → H) m‖ :=
        norm_tsum_le_tsum_norm (summable_norm_smul ha x)
    _ = ∑' m, ‖a m‖ * ‖(x : ℕ → H) m‖ := by simp [norm_smul]
    _ ≤ Real.sqrt (∑' m, ‖a m‖ ^ 2) * Real.sqrt (∑' m, ‖(x : ℕ → H) m‖ ^ 2) :=
        ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt ha hx
    _ = weightNorm a * ‖x‖ := by rw [weightNorm, hnx]

/-- The bounded weighted codiagonal as a continuous linear map. -/
noncomputable def codiagCLM (ha : Summable fun m => ‖a m‖ ^ 2) :
    lp (fun _ : ℕ => H) 2 →L[ℂ] H :=
  (codiagMap ha).mkContinuous (weightNorm a) (norm_codiagMap_le ha)

@[simp] theorem codiagCLM_apply (ha : Summable fun m => ‖a m‖ ^ 2) (x : lp (fun _ : ℕ => H) 2) :
    codiagCLM ha x = ∑' m, a m • (x : ℕ → H) m := rfl

/-- The bounded operator restricts on the algebraic core to the algebraic codiagonal. -/
theorem codiagCLM_codiagEmbed (ha : Summable fun m => ‖a m‖ ^ 2) (x : ℕ →₀ H) :
    codiagCLM ha (codiagEmbed x) = codiag a x := by
  rw [codiagCLM_apply, codiag_apply]
  refine tsum_eq_sum fun i hi => ?_
  rw [codiagEmbed_apply, Finsupp.notMem_support_iff.mp hi, smul_zero]

theorem norm_codiagCLM_le (ha : Summable fun m => ‖a m‖ ^ 2) :
    ‖codiagCLM (H := H) ha‖ ≤ weightNorm a :=
  ContinuousLinearMap.opNorm_le_bound _ (weightNorm_nonneg a) (norm_codiagMap_le ha)

end Bounded

/-! ## The test vectors -/

section TestVectors

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The unnormalised test vector `∑_{m ∈ s} conj(a_m) v e_m`. -/
noncomputable def testVector (a : ℕ → ℂ) (v : H) (s : Finset ℕ) : ℕ →₀ H :=
  ∑ m ∈ s, Finsupp.single m (((starRingEnd ℂ) (a m)) • v)

theorem testVector_apply (a : ℕ → ℂ) (v : H) (s : Finset ℕ) (j : ℕ) :
    testVector a v s j = if j ∈ s then ((starRingEnd ℂ) (a j)) • v else 0 := by
  classical
  rw [testVector, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' s j fun m => ((starRingEnd ℂ) (a m)) • v]

theorem support_testVector_subset (a : ℕ → ℂ) (v : H) (s : Finset ℕ) :
    (testVector a v s).support ⊆ s := by
  intro j hj
  by_contra hjs
  exact (Finsupp.mem_support_iff.mp hj) (by rw [testVector_apply, if_neg hjs])

theorem codiag_testVector (a : ℕ → ℂ) (v : H) (s : Finset ℕ) :
    codiag a (testVector a v s) = ((∑ m ∈ s, ‖a m‖ ^ 2 : ℝ) : ℂ) • v := by
  classical
  rw [codiag_apply,
    Finset.sum_subset (support_testVector_subset a v s) (fun j _ hj => by
      rw [Finsupp.notMem_support_iff.mp hj, smul_zero])]
  have hterm : ∀ m ∈ s, a m • (testVector a v s) m = ((‖a m‖ ^ 2 : ℝ) : ℂ) • v := by
    intro m hm
    rw [testVector_apply, if_pos hm, smul_smul, Complex.mul_conj']
    norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]
  norm_num

theorem norm_codiagEmbed_testVector_sq (a : ℕ → ℂ) (v : H) (s : Finset ℕ) :
    ‖(codiagEmbed (testVector a v s) : lp (fun _ : ℕ => H) 2)‖ ^ 2
      = (∑ m ∈ s, ‖a m‖ ^ 2) * ‖v‖ ^ 2 := by
  classical
  rw [norm_codiagEmbed_sq,
    Finset.sum_subset (support_testVector_subset a v s) (fun j _ hj => by
      rw [Finsupp.notMem_support_iff.mp hj]; simp)]
  rw [Finset.sum_congr rfl (fun m _ => by
    rw [testVector_apply, if_pos ‹m ∈ s›, norm_smul, mul_pow, RCLike.norm_conj]),
    ← Finset.sum_mul]

end TestVectors

/-! ## The exact operator norm -/

section ExactNorm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
variable {a : ℕ → ℂ}

/-- **The operator norm of a square-summable codiagonal is exactly the `ℓ²` norm of its weights.** -/
theorem norm_codiagCLM (ha : Summable fun m => ‖a m‖ ^ 2) {v : H} (hv : ‖v‖ = 1) :
    ‖codiagCLM (H := H) ha‖ = weightNorm a := by
  refine le_antisymm (norm_codiagCLM_le ha) ?_
  have hkey : ∀ s : Finset ℕ, ∑ m ∈ s, ‖a m‖ ^ 2 ≤ ‖codiagCLM (H := H) ha‖ ^ 2 := by
    intro s
    set S : ℝ := ∑ m ∈ s, ‖a m‖ ^ 2 with hS
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hval : codiagCLM (H := H) ha (codiagEmbed (testVector a v s)) = (S : ℂ) • v := by
      rw [codiagCLM_codiagEmbed, codiag_testVector]
    have hnorm : ‖(codiagEmbed (testVector a v s) : lp (fun _ : ℕ => H) 2)‖ = Real.sqrt S := by
      have h := norm_codiagEmbed_testVector_sq a v s
      rw [hv] at h
      have h' : ‖(codiagEmbed (testVector a v s) : lp (fun _ : ℕ => H) 2)‖ ^ 2 = S := by
        rw [h]; ring
      rw [← h', Real.sqrt_sq (norm_nonneg _)]
    have hb := (codiagCLM (H := H) ha).le_opNorm (codiagEmbed (testVector a v s))
    rw [hval, hnorm, norm_smul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hSnn] at hb
    nlinarith [Real.sq_sqrt hSnn, Real.sqrt_nonneg S,
      norm_nonneg (codiagCLM (H := H) ha)]
  have htsum : ∑' m, ‖a m‖ ^ 2 ≤ ‖codiagCLM (H := H) ha‖ ^ 2 :=
    ha.tsum_le_of_sum_range_le fun n => hkey (Finset.range n)
  rw [weightNorm]
  calc Real.sqrt (∑' m, ‖a m‖ ^ 2) ≤ Real.sqrt (‖codiagCLM (H := H) ha‖ ^ 2) :=
        Real.sqrt_le_sqrt htsum
    _ = ‖codiagCLM (H := H) ha‖ := Real.sqrt_sq (norm_nonneg _)

end ExactNorm

/-! ## The non-summable case: no closed extension -/

section NotClosable

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
variable {a : ℕ → ℂ}

/-- The normalised graph-null sequence: `x^{(N)} = S_N⁻¹ ∑_{m<N} conj(a_m) v e_m`. -/
noncomputable def graphNullVector (a : ℕ → ℂ) (v : H) (N : ℕ) : ℕ →₀ H :=
  (((∑ m ∈ Finset.range N, ‖a m‖ ^ 2 : ℝ) : ℂ)⁻¹) • testVector a v (Finset.range N)

omit [CompleteSpace H] in
theorem codiag_graphNullVector (a : ℕ → ℂ) (v : H) {N : ℕ}
    (hN : ∑ m ∈ Finset.range N, ‖a m‖ ^ 2 ≠ 0) :
    codiag a (graphNullVector a v N) = v := by
  set S : ℝ := ∑ m ∈ Finset.range N, ‖a m‖ ^ 2 with hS
  have hSc : ((S : ℂ)) ≠ 0 := by simpa using hN
  rw [graphNullVector, map_smul, codiag_testVector, smul_smul, inv_mul_cancel₀ hSc, one_smul]

omit [CompleteSpace H] in
theorem norm_codiagEmbed_graphNullVector (a : ℕ → ℂ) (v : H) {N : ℕ}
    (hN : 0 < ∑ m ∈ Finset.range N, ‖a m‖ ^ 2) :
    ‖(codiagEmbed (graphNullVector a v N) : lp (fun _ : ℕ => H) 2)‖
      = ‖v‖ / Real.sqrt (∑ m ∈ Finset.range N, ‖a m‖ ^ 2) := by
  set S : ℝ := ∑ m ∈ Finset.range N, ‖a m‖ ^ 2 with hS
  have hSne : (S : ℝ) ≠ 0 := ne_of_gt hN
  have hsq : ‖(codiagEmbed (graphNullVector a v N) : lp (fun _ : ℕ => H) 2)‖ ^ 2
      = ‖v‖ ^ 2 / S := by
    rw [graphNullVector, map_smul, norm_smul, mul_pow, norm_codiagEmbed_testVector_sq,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN.le]
    field_simp
    ring
  have hrhs : (‖v‖ / Real.sqrt S) ^ 2 = ‖v‖ ^ 2 / S := by
    rw [div_pow, Real.sq_sqrt hN.le]
  have hnn : 0 ≤ ‖v‖ / Real.sqrt S := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (codiagEmbed (graphNullVector a v N) : lp (fun _ : ℕ => H) 2)]

/-- **The closability dichotomy, negative half.**  A weight sequence that is not square-summable
gives a codiagonal with no closed extension: the normalised graph-null vectors have vanishing `ℓ²`
norm while their response stays equal to a fixed nonzero vector. -/
theorem not_isSequentiallyClosableBetween_codiag
    (ha : ¬ Summable fun m => ‖a m‖ ^ 2) {v : H} (hv : v ≠ 0) :
    ¬ IsSequentiallyClosableBetween
        ((codiag (H := H) a).restrictScalars ℝ) ((codiagEmbed (H := H)).restrictScalars ℝ) := by
  have hmono : Monotone fun N => ∑ m ∈ Finset.range N, ‖a m‖ ^ 2 := by
    intro m n hmn
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => sq_nonneg _
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  have htop : Tendsto (fun N => ∑ m ∈ Finset.range N, ‖a m‖ ^ 2) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => sq_nonneg _)).mp ha
  have hsqrt : Tendsto (fun N => Real.sqrt (∑ m ∈ Finset.range N, ‖a m‖ ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp htop
  have heventually : ∀ᶠ N in atTop, 0 < ∑ m ∈ Finset.range N, ‖a m‖ ^ 2 :=
    htop.eventually_gt_atTop 0
  have hsrc : Tendsto
      (fun N => ((codiagEmbed (H := H)).restrictScalars ℝ) (graphNullVector a v N))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hzero : Tendsto
        (fun N => ‖v‖ / Real.sqrt (∑ m ∈ Finset.range N, ‖a m‖ ^ 2)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds hsqrt
    refine hzero.congr' ?_
    filter_upwards [heventually] with N hN
    exact (norm_codiagEmbed_graphNullVector a v hN).symm
  have hresp : Tendsto
      (fun N => ((codiag (H := H) a).restrictScalars ℝ) (graphNullVector a v N))
      atTop (nhds v) := by
    refine (tendsto_const_nhds (x := v) (f := atTop (α := ℕ))).congr' ?_
    filter_upwards [heventually] with N hN
    exact (codiag_graphNullVector a v (ne_of_gt hN)).symm
  exact not_isSequentiallyClosableBetween_of_exact_norm_graphNull
    ((codiag (H := H) a).restrictScalars ℝ) ((codiagEmbed (H := H)).restrictScalars ℝ)
    ((codiag (H := H) a).restrictScalars ℝ) ((codiagEmbed (H := H)).restrictScalars ℝ)
    (fun _ => rfl) (fun _ => rfl) (graphNullVector a v) v hsrc hresp hv

end NotClosable

/-! ## The dichotomy -/

section Dichotomy

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- **The closability dichotomy for weighted Hilbert codiagonals.**  On a nonzero complex Banach
space, a scalar-weighted codiagonal defined on the finitely supported vectors of `ℓ²(ℕ; H)` either
has square-summable weights, in which case it is the restriction of a bounded operator of norm
exactly `‖a‖₂`, or it has no closed extension at all. -/
theorem codiagonal_closability_dichotomy (a : ℕ → ℂ) {v : H} (hv : ‖v‖ = 1) :
    (Summable (fun m => ‖a m‖ ^ 2) →
      ∃ T : lp (fun _ : ℕ => H) 2 →L[ℂ] H,
        (∀ x : ℕ →₀ H, T (codiagEmbed x) = codiag a x) ∧ ‖T‖ = weightNorm a) ∧
    ((¬ Summable fun m => ‖a m‖ ^ 2) →
      ¬ IsSequentiallyClosableBetween
          ((codiag (H := H) a).restrictScalars ℝ)
          ((codiagEmbed (H := H)).restrictScalars ℝ)) := by
  refine ⟨fun ha => ⟨codiagCLM ha, codiagCLM_codiagEmbed ha, norm_codiagCLM ha hv⟩, fun ha => ?_⟩
  refine not_isSequentiallyClosableBetween_codiag (v := v) ha ?_
  intro h0
  rw [h0, norm_zero] at hv
  exact zero_ne_one hv

/-- **The unweighted codiagonal is never closable.**  A scalar row that acts by the same fixed
weight on every orthogonal label has no closed extension on the Hilbert direct sum. -/
theorem not_isSequentiallyClosableBetween_unitCodiag {v : H} (hv : v ≠ 0) :
    ¬ IsSequentiallyClosableBetween
        ((codiag (H := H) (fun _ => (1 : ℂ))).restrictScalars ℝ)
        ((codiagEmbed (H := H)).restrictScalars ℝ) := by
  refine not_isSequentiallyClosableBetween_codiag ?_ hv
  intro hs
  have h1 : Summable fun _ : ℕ => (1 : ℝ) := by simpa using hs
  exact zero_ne_one (tendsto_nhds_unique h1.tendsto_atTop_zero tendsto_const_nhds)

end Dichotomy

end RHTower
