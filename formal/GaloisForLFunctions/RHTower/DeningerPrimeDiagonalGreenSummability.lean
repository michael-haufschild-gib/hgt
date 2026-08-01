import GaloisForLFunctions.RHTower.DeningerAllPlaceGreenFormUniformPacketNoGo
import GaloisForLFunctions.RHTower.DeningerTateGraphPrimeDiskEscape
import GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Orthogonal prime Green forms on the graph direct sum

The natural graph-normalized local Green coefficient at a prime is `(log p)⁻²`.  These
coefficients are not `ℓ¹` over the primes, so a scalar majorant cannot construct the global form.
On the orthogonal Hilbert direct sum, however, every finite packet sum has norm equal to at most
the largest coefficient.  Since `(log p)⁻²` tends to zero cofinally, the unordered series of local
forms converges in operator norm.

This closes the prime-diagonal functional-analysis gate, not the arithmetic comparison gate:
identifying the actual Route L source disk with this orthogonal coordinate model, and controlling
Milnor/cup cross-prime incidence, remain separate obligations.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal BigOperators

noncomputable section

variable {ι : Type*}

/-- Real square-summable coordinate space used for graph-orthogonal prime packets. -/
abbrev DeningerRealEllTwo (ι : Type*) := lp (fun _ : ι => ℝ) 2

/-- A uniformly bounded real diagonal preserves square summability. -/
theorem deningerRealDiagonal_memℓp {a : ι → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (x : DeningerRealEllTwo ι) :
    Memℓp (fun i => a i * x i) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖x i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro i
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (ha i) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- Linear map defined by a uniformly bounded real diagonal. -/
def deningerRealDiagonalLinearMap (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) :
    DeningerRealEllTwo ι →ₗ[ℝ] DeningerRealEllTwo ι where
  toFun x := ⟨fun i => a i * x i, deningerRealDiagonal_memℓp hC ha x⟩
  map_add' := by
    intro x y
    ext i
    simp [mul_add]
  map_smul' := by
    intro c x
    ext i
    simp [mul_left_comm]

@[simp] theorem deningerRealDiagonalLinearMap_apply
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerRealEllTwo ι) (i : ι) :
    deningerRealDiagonalLinearMap a hC ha x i = a i * x i := rfl

/-- The real diagonal linear map is bounded by the multiplier supremum. -/
theorem deningerRealDiagonalLinearMap_norm_le
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerRealEllTwo ι) :
    ‖deningerRealDiagonalLinearMap a hC ha x‖ ≤ C * ‖x‖ := by
  have hleft : (0 : ℝ) ≤ ‖deningerRealDiagonalLinearMap a hC ha x‖ := norm_nonneg _
  have hright : (0 : ℝ) ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hdiag :
      ‖deningerRealDiagonalLinearMap a hC ha x‖ ^ (2 : ℝ) =
        ∑' i, ‖deningerRealDiagonalLinearMap a hC ha x i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℝ) (by norm_num)
      (deningerRealDiagonalLinearMap a hC ha x)
  have hx : ‖x‖ ^ (2 : ℝ) = ∑' i, ‖x i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℝ) (by norm_num) x
  have hsumx : Summable fun i => ‖x i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  have hsumdiag : Summable fun i =>
      ‖deningerRealDiagonalLinearMap a hC ha x i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i,
      ‖deningerRealDiagonalLinearMap a hC ha x i‖ ^ (2 : ℝ) ≤
        C ^ (2 : ℝ) * ‖x i‖ ^ (2 : ℝ) := by
    intro i
    rw [deningerRealDiagonalLinearMap_apply, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (ha i) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow :
      ‖deningerRealDiagonalLinearMap a hC ha x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag, Real.mul_rpow hC (norm_nonneg _), hx, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumdiag
      (hsumx.mul_left (C ^ (2 : ℝ)))
  have hleft2 :
      ‖deningerRealDiagonalLinearMap a hC ha x‖ ^ (2 : ℝ) =
        ‖deningerRealDiagonalLinearMap a hC ha x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (C * ‖x‖) ^ (2 : ℝ) = (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Bounded operator defined by a uniformly bounded real diagonal. -/
def deningerRealDiagonalOperator (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) :
    DeningerRealEllTwo ι →L[ℝ] DeningerRealEllTwo ι :=
  LinearMap.mkContinuous (deningerRealDiagonalLinearMap a hC ha) C
    (deningerRealDiagonalLinearMap_norm_le a hC ha)

@[simp] theorem deningerRealDiagonalOperator_apply
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerRealEllTwo ι) (i : ι) :
    deningerRealDiagonalOperator a hC ha x i = a i * x i := rfl

theorem norm_deningerRealDiagonalOperator_le
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ‖deningerRealDiagonalOperator a hC ha‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- Continuous linear passage from a bounded real operator to its inner-product Green form. -/
def deningerOperatorToGreenForm (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    (H →L[ℝ] H) →L[ℝ] H →L[ℝ] H →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ H H (H →L[ℝ] ℝ)) (innerSL ℝ)

@[simp] theorem deningerOperatorToGreenForm_apply_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (x y : H) :
    deningerOperatorToGreenForm H T x y = inner ℝ (T x) y := rfl

/-- Passage from operator to Green form does not increase operator norm. -/
theorem norm_deningerOperatorToGreenForm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) :
    ‖deningerOperatorToGreenForm H T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg T) (norm_nonneg x)) fun y => ?_
  calc
    ‖deningerOperatorToGreenForm H T x y‖ = |inner ℝ (T x) y| := by
      rw [deningerOperatorToGreenForm_apply_apply, Real.norm_eq_abs]
    _ ≤ ‖T x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖y‖ := by
      gcongr
      exact T.le_opNorm x
    _ = ‖T‖ * ‖x‖ * ‖y‖ := by ring

/-- Multiplier supported at one coordinate. -/
def deningerCoordinateWeight [DecidableEq ι] (a : ι → ℝ) (i j : ι) : ℝ :=
  if j = i then a i else 0

/-- Rank-one coordinate operator with nonnegative weight `a i`. -/
def deningerCoordinateOperator [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    DeningerRealEllTwo ι →L[ℝ] DeningerRealEllTwo ι :=
  deningerRealDiagonalOperator (deningerCoordinateWeight a i) (ha i)
    (fun j => by
      by_cases hji : j = i
      · simp [deningerCoordinateWeight, hji, abs_of_nonneg (ha i)]
      · simp [deningerCoordinateWeight, hji, ha i])

@[simp] theorem deningerCoordinateOperator_apply [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι)
    (x : DeningerRealEllTwo ι) (j : ι) :
    deningerCoordinateOperator a ha i x j =
      if j = i then a i * x j else 0 := by
  simp [deningerCoordinateOperator, deningerCoordinateWeight]

/-- Coordinate Green form induced by the rank-one diagonal operator. -/
def deningerCoordinateGreenForm [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    DeningerRealEllTwo ι →L[ℝ] DeningerRealEllTwo ι →L[ℝ] ℝ :=
  deningerOperatorToGreenForm (DeningerRealEllTwo ι)
    (deningerCoordinateOperator a ha i)

@[simp] theorem deningerCoordinateGreenForm_apply_apply [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι)
    (x y : DeningerRealEllTwo ι) :
    deningerCoordinateGreenForm a ha i x y = a i * x i * y i := by
  rw [deningerCoordinateGreenForm, deningerOperatorToGreenForm_apply_apply]
  have hop : deningerCoordinateOperator a ha i x = lp.single 2 i (a i * x i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [deningerCoordinateOperator_apply, hji, lp.single_apply]
  rw [hop, lp.inner_single_left]
  simp
  ring

/-- A coordinate unit packet has its prescribed local Green energy. -/
theorem deningerCoordinateGreenForm_unit_energy [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    deningerCoordinateGreenForm a ha i (lp.single 2 i 1) (lp.single 2 i 1) = a i := by
  rw [deningerCoordinateGreenForm, deningerOperatorToGreenForm_apply_apply]
  have hop : deningerCoordinateOperator a ha i (lp.single 2 i 1) =
      lp.single 2 i (a i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [deningerCoordinateOperator_apply, hji, lp.single_apply]
  rw [hop, lp.inner_single_left, lp.single_apply_self]
  simp

/-- The coordinate Green-form norm is exactly its nonnegative coefficient. -/
theorem norm_deningerCoordinateGreenForm [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    ‖deningerCoordinateGreenForm a ha i‖ = a i := by
  apply le_antisymm
  · exact (norm_deningerOperatorToGreenForm_le
      (deningerCoordinateOperator a ha i)).trans
      (norm_deningerRealDiagonalOperator_le _ (ha i) _)
  · let e : DeningerRealEllTwo ι := lp.single 2 i 1
    have he : ‖e‖ = 1 := by
      simp [e, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    have hinner := (deningerCoordinateGreenForm a ha i e).le_opNorm e
    have houter := (deningerCoordinateGreenForm a ha i).le_opNorm e
    rw [show deningerCoordinateGreenForm a ha i e e = a i by
      simp [e, deningerCoordinateGreenForm_unit_energy],
      Real.norm_eq_abs, abs_of_nonneg (ha i), he, mul_one] at hinner
    rw [he, mul_one] at houter
    exact hinner.trans houter

/-- Coefficient family supported on a finite coordinate set. -/
def deningerFinsetDiagonalWeight [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ s then a i else 0

theorem deningerFinsetDiagonalWeight_norm_le [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ i ∈ s, a i ≤ C) (i : ι) :
    ‖deningerFinsetDiagonalWeight s a i‖ ≤ C := by
  by_cases hi : i ∈ s
  · simp [deningerFinsetDiagonalWeight, hi, abs_of_nonneg (ha i), haC i hi]
  · simp [deningerFinsetDiagonalWeight, hi, hC]

/-- A finite sum of coordinate operators is the corresponding finitely supported diagonal. -/
theorem sum_deningerCoordinateOperator_eq [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ i ∈ s, a i ≤ C) :
    (∑ i ∈ s, deningerCoordinateOperator a ha i) =
      deningerRealDiagonalOperator (deningerFinsetDiagonalWeight s a) hC
        (deningerFinsetDiagonalWeight_norm_le s a ha hC haC) := by
  ext x j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    deningerCoordinateOperator_apply, deningerRealDiagonalOperator_apply]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j]
    · simp [deningerFinsetDiagonalWeight, hj]
    · intro i hi hij
      simp [hij.symm]
    · exact fun h => (h hj).elim
  · simp [deningerFinsetDiagonalWeight, hj]

/-- Orthogonality gives the maximum-coefficient bound for every finite local-form sum. -/
theorem norm_sum_deningerCoordinateGreenForm_le [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (s : Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (hforms : ∀ i ∈ s, ‖deningerCoordinateGreenForm a ha i‖ ≤ C) :
    ‖∑ i ∈ s, deningerCoordinateGreenForm a ha i‖ ≤ C := by
  have haC : ∀ i ∈ s, a i ≤ C := by
    intro i hi
    rw [← norm_deningerCoordinateGreenForm a ha i]
    exact hforms i hi
  rw [show (∑ i ∈ s, deningerCoordinateGreenForm a ha i) =
      deningerOperatorToGreenForm (DeningerRealEllTwo ι)
        (∑ i ∈ s, deningerCoordinateOperator a ha i) by
    simp [deningerCoordinateGreenForm]]
  exact (norm_deningerOperatorToGreenForm_le _).trans
    ((congrArg norm (sum_deningerCoordinateOperator_eq s a ha hC haC)).le.trans
      (norm_deningerRealDiagonalOperator_le _ hC _))

/-- For orthogonal coordinate Green forms, unordered operator-norm summability is exactly
cofinite decay of the coefficients. -/
theorem summable_deningerCoordinateGreenForm_iff [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Summable (deningerCoordinateGreenForm a ha) ↔
      Tendsto a cofinite (𝓝 0) := by
  rw [deningerSummable_iff_norm_tendsto_cofinite_of_max_tail_control
    (deningerCoordinateGreenForm a ha)
    (fun s C hC => norm_sum_deningerCoordinateGreenForm_le a ha s hC)]
  simp [norm_deningerCoordinateGreenForm]

/-! ## Prime graph specialization -/

/-- Graph-normalized local Green coefficient at prime period `log p`. -/
noncomputable def deningerPrimeGraphGreenCoefficient (p : Nat.Primes) : ℝ :=
  (Real.log (p : ℝ) ^ 2)⁻¹

theorem deningerPrimeGraphGreenCoefficient_pos (p : Nat.Primes) :
    0 < deningerPrimeGraphGreenCoefficient p := by
  exact inv_pos.mpr (sq_pos_of_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt)))

/-- Prime graph coefficients vanish cofinally. -/
theorem deningerPrimeGraphGreenCoefficient_tendsto_zero :
    Tendsto deningerPrimeGraphGreenCoefficient cofinite (𝓝 0) := by
  have hlog : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ)) cofinite atTop :=
    Real.tendsto_log_atTop.comp tendsto_prime_coe_real_cofinite_atTop
  have hsq : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ) ^ 2) cofinite atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  exact tendsto_inv_atTop_zero.comp hsq

/-- Embed a finite natural-prime window into the subtype of all primes. -/
def deningerPrimeWindowEmbedding (x : ℝ) (hx : 0 ≤ x) :
    {p // p ∈ windowPrimes 1 x} ↪ Nat.Primes where
  toFun p := ⟨p.1, ((mem_windowPrimes (by norm_num) hx).mp p.2).1⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes => (z : ℕ)) h

/-- Finite prime-subtype window corresponding to `windowPrimes 1 x`. -/
def deningerPrimeWindowFinset (x : ℝ) (hx : 0 ≤ x) : Finset Nat.Primes :=
  (windowPrimes 1 x).attach.map (deningerPrimeWindowEmbedding x hx)

/-- The subtype-window coefficient sum is the established reciprocal-log-square cutoff sum. -/
theorem sum_deningerPrimeWindowGreenCoefficient_eq (x : ℝ) (hx : 0 ≤ x) :
    ∑ p ∈ deningerPrimeWindowFinset x hx, deningerPrimeGraphGreenCoefficient p =
      primeReciprocalLogSqSum x := by
  rw [deningerPrimeWindowFinset, Finset.sum_map]
  simp only [deningerPrimeWindowEmbedding, primeReciprocalLogSqSum,
    deningerPrimeGraphGreenCoefficient, one_div]
  exact Finset.sum_attach (windowPrimes 1 x)
    (fun p : ℕ => (Real.log (p : ℝ) ^ 2)⁻¹)

/-- The positive scalar coefficient family is not summable over primes. -/
theorem not_summable_deningerPrimeGraphGreenCoefficient :
    ¬ Summable deningerPrimeGraphGreenCoefficient := by
  intro hsum
  have hbounded : ∀ x : ℝ, 0 ≤ x →
      primeReciprocalLogSqSum x ≤ ∑' p, deningerPrimeGraphGreenCoefficient p := by
    intro x hx
    rw [← sum_deningerPrimeWindowGreenCoefficient_eq x hx]
    exact hsum.sum_le_tsum (deningerPrimeWindowFinset x hx)
      (fun p _ => (deningerPrimeGraphGreenCoefficient_pos p).le)
  have heventually : ∀ᶠ x : ℝ in atTop,
      (∑' p, deningerPrimeGraphGreenCoefficient p) + 1 ≤
        primeReciprocalLogSqSum x :=
    tendsto_primeReciprocalLogSqSum_atTop.eventually (eventually_ge_atTop _)
  rcases (eventually_atTop.1 heventually) with ⟨b, hb⟩
  let x : ℝ := max b 0
  have hxlarge := hb x (le_max_left _ _)
  have hx : 0 ≤ x := le_max_right _ _
  exact (not_lt_of_ge (hbounded x hx))
    (lt_of_lt_of_le (lt_add_one _) hxlarge)

/-- Local Green form on the prime-orthogonal graph direct sum. -/
noncomputable def deningerPrimeDiagonalGreenForm (p : Nat.Primes) :
    DeningerRealEllTwo Nat.Primes →L[ℝ]
      DeningerRealEllTwo Nat.Primes →L[ℝ] ℝ :=
  deningerCoordinateGreenForm deningerPrimeGraphGreenCoefficient
    (fun q => (deningerPrimeGraphGreenCoefficient_pos q).le) p

/-- Each local prime form has exact norm `(log p)⁻²`. -/
theorem norm_deningerPrimeDiagonalGreenForm (p : Nat.Primes) :
    ‖deningerPrimeDiagonalGreenForm p‖ = (Real.log (p : ℝ) ^ 2)⁻¹ := by
  exact norm_deningerCoordinateGreenForm deningerPrimeGraphGreenCoefficient
    (fun q => (deningerPrimeGraphGreenCoefficient_pos q).le) p

/-- The scalar series of local form norms diverges. -/
theorem not_summable_norm_deningerPrimeDiagonalGreenForm :
    ¬ Summable (fun p => ‖deningerPrimeDiagonalGreenForm p‖) := by
  rw [show (fun p => ‖deningerPrimeDiagonalGreenForm p‖) =
      deningerPrimeGraphGreenCoefficient by
    funext p
    exact norm_deningerPrimeDiagonalGreenForm p]
  exact not_summable_deningerPrimeGraphGreenCoefficient

/-- **Prime-diagonal Green summability.**  The unordered series of graph-normalized prime local
forms converges in operator norm, despite the failure of scalar `ℓ¹` summability. -/
theorem summable_deningerPrimeDiagonalGreenForm :
    Summable deningerPrimeDiagonalGreenForm := by
  exact (summable_deningerCoordinateGreenForm_iff
    deningerPrimeGraphGreenCoefficient
    (fun q => (deningerPrimeGraphGreenCoefficient_pos q).le)).2
    deningerPrimeGraphGreenCoefficient_tendsto_zero

/-- The summed prime-diagonal Green form is a genuine continuous bilinear form. -/
noncomputable def deningerPrimeDiagonalSummedGreenForm :
    DeningerRealEllTwo Nat.Primes →L[ℝ]
      DeningerRealEllTwo Nat.Primes →L[ℝ] ℝ :=
  deningerSummedGreenForm deningerPrimeDiagonalGreenForm

/-- Evaluation of the global prime-diagonal form commutes with the unordered local sum. -/
theorem deningerPrimeDiagonalSummedGreenForm_hasSum_apply_apply
    (x y : DeningerRealEllTwo Nat.Primes) :
    HasSum (fun p => deningerPrimeDiagonalGreenForm p x y)
      (deningerPrimeDiagonalSummedGreenForm x y) :=
  deningerSummedGreenForm_hasSum_apply_apply deningerPrimeDiagonalGreenForm
    summable_deningerPrimeDiagonalGreenForm x y

/-- Exact coordinate formula for the global prime-diagonal Green form. -/
theorem deningerPrimeDiagonalSummedGreenForm_apply_apply
    (x y : DeningerRealEllTwo Nat.Primes) :
    deningerPrimeDiagonalSummedGreenForm x y =
      ∑' p : Nat.Primes,
        deningerPrimeGraphGreenCoefficient p * x p * y p := by
  rw [← (deningerPrimeDiagonalSummedGreenForm_hasSum_apply_apply x y).tsum_eq]
  apply tsum_congr
  intro p
  exact deningerCoordinateGreenForm_apply_apply _ _ _ _ _

/-- The summed orthogonal prime Green energy is nonnegative. -/
theorem deningerPrimeDiagonalSummedGreenForm_nonneg
    (x : DeningerRealEllTwo Nat.Primes) :
    0 ≤ deningerPrimeDiagonalSummedGreenForm x x := by
  rw [deningerPrimeDiagonalSummedGreenForm_apply_apply]
  exact tsum_nonneg fun p => by
    simpa [pow_two, mul_assoc] using mul_nonneg
      (deningerPrimeGraphGreenCoefficient_pos p).le (sq_nonneg (x p))

/-- **Prime-model Green radical classification.**  The global orthogonal prime Green energy
vanishes exactly at the zero vector. -/
theorem deningerPrimeDiagonalSummedGreenForm_self_eq_zero_iff
    (x : DeningerRealEllTwo Nat.Primes) :
    deningerPrimeDiagonalSummedGreenForm x x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    apply lp.ext
    funext p
    have hsum : Summable (fun q => deningerPrimeDiagonalGreenForm q x x) :=
      (deningerPrimeDiagonalSummedGreenForm_hasSum_apply_apply x x).summable
    have hterm_nonneg : ∀ q, 0 ≤ deningerPrimeDiagonalGreenForm q x x := by
      intro q
      rw [deningerPrimeDiagonalGreenForm, deningerCoordinateGreenForm_apply_apply]
      simpa [pow_two, mul_assoc] using mul_nonneg
        (deningerPrimeGraphGreenCoefficient_pos q).le (sq_nonneg (x q))
    have hp_le : deningerPrimeDiagonalGreenForm p x x ≤
        deningerPrimeDiagonalSummedGreenForm x x := by
      rw [← (deningerPrimeDiagonalSummedGreenForm_hasSum_apply_apply x x).tsum_eq]
      exact hsum.le_tsum p (fun q _ => hterm_nonneg q)
    have hp_zero : deningerPrimeDiagonalGreenForm p x x = 0 :=
      le_antisymm (hzero ▸ hp_le) (hterm_nonneg p)
    rw [deningerPrimeDiagonalGreenForm, deningerCoordinateGreenForm_apply_apply] at hp_zero
    have hsquare : x p ^ 2 = 0 := by
      have hmul : deningerPrimeGraphGreenCoefficient p * x p ^ 2 = 0 := by
        simpa [pow_two, mul_assoc] using hp_zero
      exact (mul_eq_zero.mp hmul).resolve_left
        (deningerPrimeGraphGreenCoefficient_pos p).ne'
    exact (sq_eq_zero_iff).mp hsquare
  · rintro rfl
    simp

end

end RHTower
