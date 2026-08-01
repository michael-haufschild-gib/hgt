import GaloisForLFunctions.RHTower.DeningerPrimeDiagonalGreenSummability

/-!
# Prime Green summability with full Hilbert packet fibres

The scalar prime coordinate model does not retain mean-zero packet modes.  This module replaces
each scalar coordinate by an arbitrary real Hilbert fibre `K p`.  The local Green form is the full
fibre inner product weighted by `(log p)⁻²`.  Finite prime sums still obey the maximum-coefficient
operator bound, so the unordered all-prime form converges in operator norm.  Its global energy is
nonnegative and has zero radical on the full Hilbert direct sum.

This is the correct functional-analytic target for a Route L comparison: one block per prime, with
all packet Fourier/transverse modes inside the block.  Constructing the actual arithmetic fibres
and the bounded comparison into this direct sum remains a source theorem.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal BigOperators

noncomputable section

/-- Coefficient-controlled maximum tails give unordered summability even when individual term
norms are not known exactly.  This is the abstract Cauchy engine for block-diagonal families. -/
theorem deningerSummable_of_coefficient_max_tail_control
    {ι F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (f : ι → F) (a : ι → ℝ)
    (hzero : Tendsto a cofinite (𝓝 0))
    (hmax : ∀ (s : Finset ι) (C : ℝ), 0 ≤ C →
      (∀ i ∈ s, a i ≤ C) → ‖∑ i ∈ s, f i‖ ≤ C) :
    Summable f := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have heventually : ∀ᶠ i in cofinite, a i < ε / 2 :=
    hzero.eventually_lt_const hε2
  classical
  refine ⟨heventually.toFinset, fun s hs => ?_⟩
  have haε : ∀ i ∈ s, a i ≤ ε / 2 := by
    intro i hi
    have hiout : i ∉ heventually.toFinset := Finset.disjoint_left.mp hs hi
    have higood : a i < ε / 2 := by
      simpa only [heventually.mem_toFinset, Set.mem_compl_iff,
        Classical.not_not, Set.mem_setOf_eq] using hiout
    exact higood.le
  exact (hmax s (ε / 2) hε2.le haε).trans_lt (half_lt_self hε)

variable {ι : Type*} {K : ι → Type*}
  [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]

/-- Hilbert direct sum of a family of real packet fibres. -/
abbrev DeningerHilbertSum (K : ι → Type*)
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)] :=
  lp K 2

/-- A uniformly bounded real scalar diagonal preserves the Hilbert direct sum. -/
theorem deningerBlockDiagonal_memℓp
    {a : ι → ℝ} {C : ℝ} (_hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerHilbertSum K) :
    Memℓp (fun i => a i • x i) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖x i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro i
  rw [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (ha i) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- Scalar diagonal on a Hilbert direct sum, as a linear map. -/
def deningerBlockDiagonalLinearMap
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    DeningerHilbertSum K →ₗ[ℝ] DeningerHilbertSum K where
  toFun x := ⟨fun i => a i • x i, deningerBlockDiagonal_memℓp hC ha x⟩
  map_add' := by
    intro x y
    ext i
    simp [smul_add]
  map_smul' := by
    intro c x
    ext i
    simp [smul_smul, mul_comm]

@[simp] theorem deningerBlockDiagonalLinearMap_apply
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerHilbertSum K) (i : ι) :
    deningerBlockDiagonalLinearMap a hC ha x i = a i • x i := rfl

/-- The block diagonal linear map is bounded by the scalar multiplier supremum. -/
theorem deningerBlockDiagonalLinearMap_norm_le
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerHilbertSum K) :
    ‖deningerBlockDiagonalLinearMap a hC ha x‖ ≤ C * ‖x‖ := by
  have hleft : (0 : ℝ) ≤ ‖deningerBlockDiagonalLinearMap a hC ha x‖ := norm_nonneg _
  have hright : (0 : ℝ) ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hdiag :
      ‖deningerBlockDiagonalLinearMap a hC ha x‖ ^ (2 : ℝ) =
        ∑' i, ‖deningerBlockDiagonalLinearMap a hC ha x i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := K) (by norm_num)
      (deningerBlockDiagonalLinearMap a hC ha x)
  have hx : ‖x‖ ^ (2 : ℝ) = ∑' i, ‖x i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := K) (by norm_num) x
  have hsumx : Summable fun i => ‖x i‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  have hsumdiag : Summable fun i =>
      ‖deningerBlockDiagonalLinearMap a hC ha x i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i,
      ‖deningerBlockDiagonalLinearMap a hC ha x i‖ ^ (2 : ℝ) ≤
        C ^ (2 : ℝ) * ‖x i‖ ^ (2 : ℝ) := by
    intro i
    rw [deningerBlockDiagonalLinearMap_apply, norm_smul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (ha i) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow :
      ‖deningerBlockDiagonalLinearMap a hC ha x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag, Real.mul_rpow hC (norm_nonneg _), hx, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumdiag
      (hsumx.mul_left (C ^ (2 : ℝ)))
  have hleft2 :
      ‖deningerBlockDiagonalLinearMap a hC ha x‖ ^ (2 : ℝ) =
        ‖deningerBlockDiagonalLinearMap a hC ha x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (C * ‖x‖) ^ (2 : ℝ) = (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Bounded scalar diagonal operator on a Hilbert direct sum. -/
def deningerBlockDiagonalOperator
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    DeningerHilbertSum K →L[ℝ] DeningerHilbertSum K :=
  LinearMap.mkContinuous (deningerBlockDiagonalLinearMap a hC ha) C
    (deningerBlockDiagonalLinearMap_norm_le a hC ha)

@[simp] theorem deningerBlockDiagonalOperator_apply
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    (x : DeningerHilbertSum K) (i : ι) :
    deningerBlockDiagonalOperator a hC ha x i = a i • x i := rfl

theorem norm_deningerBlockDiagonalOperator_le
    (a : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ‖deningerBlockDiagonalOperator (K := K) a hC ha‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- Rank-one-in-the-index, identity-on-the-fibre block operator. -/
def deningerBlockCoordinateOperator [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    DeningerHilbertSum K →L[ℝ] DeningerHilbertSum K :=
  deningerBlockDiagonalOperator (K := K) (deningerCoordinateWeight a i) (ha i)
    (fun j => by
      by_cases hji : j = i
      · simp [deningerCoordinateWeight, hji, abs_of_nonneg (ha i)]
      · simp [deningerCoordinateWeight, hji, ha i])

@[simp] theorem deningerBlockCoordinateOperator_apply [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι)
    (x : DeningerHilbertSum K) (j : ι) :
    deningerBlockCoordinateOperator (K := K) a ha i x j =
      if j = i then a i • x j else 0 := by
  simp [deningerBlockCoordinateOperator, deningerCoordinateWeight]

/-- Full-fibre local Green form in one direct-sum block. -/
def deningerBlockCoordinateGreenForm [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    DeningerHilbertSum K →L[ℝ] DeningerHilbertSum K →L[ℝ] ℝ :=
  deningerOperatorToGreenForm (DeningerHilbertSum K)
    (deningerBlockCoordinateOperator (K := K) a ha i)

@[simp] theorem deningerBlockCoordinateGreenForm_apply_apply [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι)
    (x y : DeningerHilbertSum K) :
    deningerBlockCoordinateGreenForm (K := K) a ha i x y =
      a i * inner ℝ (x i) (y i) := by
  rw [deningerBlockCoordinateGreenForm, deningerOperatorToGreenForm_apply_apply]
  have hop : deningerBlockCoordinateOperator (K := K) a ha i x =
      lp.single 2 i (a i • x i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [deningerBlockCoordinateOperator_apply, hji, lp.single_apply]
  rw [hop, lp.inner_single_left, real_inner_smul_left]

/-- Finitely supported block multiplier. -/
def deningerFinsetBlockWeight [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ s then a i else 0

theorem deningerFinsetBlockWeight_norm_le [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ i ∈ s, a i ≤ C) (i : ι) :
    ‖deningerFinsetBlockWeight s a i‖ ≤ C := by
  by_cases hi : i ∈ s
  · simp [deningerFinsetBlockWeight, hi, abs_of_nonneg (ha i), haC i hi]
  · simp [deningerFinsetBlockWeight, hi, hC]

/-- Finite coordinate-block sum equals the finitely supported block diagonal. -/
theorem sum_deningerBlockCoordinateOperator_eq [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ i ∈ s, a i ≤ C) :
    (∑ i ∈ s, deningerBlockCoordinateOperator (K := K) a ha i) =
      deningerBlockDiagonalOperator (K := K) (deningerFinsetBlockWeight s a) hC
        (deningerFinsetBlockWeight_norm_le s a ha hC haC) := by
  ext x j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    deningerBlockCoordinateOperator_apply, deningerBlockDiagonalOperator_apply]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j]
    · simp [deningerFinsetBlockWeight, hj]
    · intro i hi hij
      simp [hij.symm]
    · exact fun h => (h hj).elim
  · simp [deningerFinsetBlockWeight, hj]

/-- Finite full-fibre coordinate-operator sums obey the maximum coefficient bound. -/
theorem norm_sum_deningerBlockCoordinateOperator_le [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (s : Finset ι) {C : ℝ} (hC : 0 ≤ C) (haC : ∀ i ∈ s, a i ≤ C) :
    ‖∑ i ∈ s, deningerBlockCoordinateOperator (K := K) a ha i‖ ≤ C := by
  rw [sum_deningerBlockCoordinateOperator_eq (K := K) s a ha hC haC]
  exact norm_deningerBlockDiagonalOperator_le (K := K) _ hC _

variable [∀ i, CompleteSpace (K i)]

/-- Cofinite decay of nonnegative block coefficients gives unordered summability of the block
operators.  The proof uses maximum-tail control, not scalar majorization. -/
theorem summable_deningerBlockCoordinateOperator_of_tendsto_zero [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hzero : Tendsto a cofinite (𝓝 0)) :
    Summable (deningerBlockCoordinateOperator (K := K) a ha) :=
  deningerSummable_of_coefficient_max_tail_control
    (deningerBlockCoordinateOperator (K := K) a ha) a hzero
    (fun s _ hC haC =>
      norm_sum_deningerBlockCoordinateOperator_le (K := K) a ha s hC haC)

/-- The continuous operator-to-form map transports block-operator summability to unordered
operator-norm summability of the full-fibre local Green forms. -/
theorem summable_deningerBlockCoordinateGreenForm_of_tendsto_zero [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hzero : Tendsto a cofinite (𝓝 0)) :
    Summable (deningerBlockCoordinateGreenForm (K := K) a ha) := by
  have hops := summable_deningerBlockCoordinateOperator_of_tendsto_zero
    (K := K) a ha hzero
  change Summable (fun i => deningerOperatorToGreenForm (DeningerHilbertSum K)
    (deningerBlockCoordinateOperator (K := K) a ha i))
  exact hops.mapL (deningerOperatorToGreenForm (DeningerHilbertSum K))

/-! ## Full prime-fibre specialization -/

variable {Kp : Nat.Primes → Type*}
  [∀ p, NormedAddCommGroup (Kp p)] [∀ p, InnerProductSpace ℝ (Kp p)]
  [∀ p, CompleteSpace (Kp p)]

/-- Full-fibre local Green form in the `p`-block, weighted by `(log p)⁻²`. -/
def deningerPrimeBlockGreenForm (p : Nat.Primes) :
    DeningerHilbertSum Kp →L[ℝ] DeningerHilbertSum Kp →L[ℝ] ℝ :=
  deningerBlockCoordinateGreenForm (K := Kp) deningerPrimeGraphGreenCoefficient
    (fun q => (deningerPrimeGraphGreenCoefficient_pos q).le) p

/-- The unordered family of full prime-block Green forms converges in operator norm. -/
theorem summable_deningerPrimeBlockGreenForm :
    Summable (deningerPrimeBlockGreenForm (Kp := Kp)) :=
  summable_deningerBlockCoordinateGreenForm_of_tendsto_zero
    (K := Kp) deningerPrimeGraphGreenCoefficient
    (fun q => (deningerPrimeGraphGreenCoefficient_pos q).le)
    deningerPrimeGraphGreenCoefficient_tendsto_zero

/-- Global full-prime-block Green form. -/
def deningerPrimeBlockSummedGreenForm :
    DeningerHilbertSum Kp →L[ℝ] DeningerHilbertSum Kp →L[ℝ] ℝ :=
  ∑' p, deningerPrimeBlockGreenForm (Kp := Kp) p

/-- Exact energy formula for the global full-prime-block form. -/
theorem deningerPrimeBlockSummedGreenForm_self
    (x : DeningerHilbertSum Kp) :
    deningerPrimeBlockSummedGreenForm x x =
      ∑' p : Nat.Primes,
        deningerPrimeGraphGreenCoefficient p * ‖x p‖ ^ 2 := by
  have hsum := (summable_deningerPrimeBlockGreenForm (Kp := Kp)).hasSum
  have happ := hsum.mapL
    ((ContinuousLinearMap.apply ℝ (DeningerHilbertSum Kp →L[ℝ] ℝ)) x)
  have happ' := happ.mapL ((ContinuousLinearMap.apply ℝ ℝ) x)
  calc
    deningerPrimeBlockSummedGreenForm x x =
        ∑' p : Nat.Primes, deningerPrimeBlockGreenForm (Kp := Kp) p x x := by
      exact happ'.tsum_eq.symm
    _ = ∑' p : Nat.Primes,
        deningerPrimeGraphGreenCoefficient p * ‖x p‖ ^ 2 := by
      apply tsum_congr
      intro p
      rw [deningerPrimeBlockGreenForm, deningerBlockCoordinateGreenForm_apply_apply,
        real_inner_self_eq_norm_sq]

/-- The global full-prime-block Green energy is nonnegative. -/
theorem deningerPrimeBlockSummedGreenForm_nonneg
    (x : DeningerHilbertSum Kp) :
    0 ≤ deningerPrimeBlockSummedGreenForm x x := by
  rw [deningerPrimeBlockSummedGreenForm_self]
  exact tsum_nonneg fun p => mul_nonneg
    (deningerPrimeGraphGreenCoefficient_pos p).le (sq_nonneg _)

/-- **Full-prime-block radical classification.**  The global Green energy vanishes exactly at
the zero vector, including every mean-zero/Fourier mode retained inside each packet fibre. -/
theorem deningerPrimeBlockSummedGreenForm_self_eq_zero_iff
    (x : DeningerHilbertSum Kp) :
    deningerPrimeBlockSummedGreenForm x x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    apply lp.ext
    funext p
    have hforms := (summable_deningerPrimeBlockGreenForm (Kp := Kp)).hasSum
    have houter := hforms.mapL
      ((ContinuousLinearMap.apply ℝ (DeningerHilbertSum Kp →L[ℝ] ℝ)) x)
    have hinner := houter.mapL ((ContinuousLinearMap.apply ℝ ℝ) x)
    have hscalar : Summable (fun q => deningerPrimeBlockGreenForm (Kp := Kp) q x x) :=
      hinner.summable
    have hnonneg : ∀ q, 0 ≤ deningerPrimeBlockGreenForm (Kp := Kp) q x x := by
      intro q
      rw [deningerPrimeBlockGreenForm, deningerBlockCoordinateGreenForm_apply_apply,
        real_inner_self_eq_norm_sq]
      exact mul_nonneg (deningerPrimeGraphGreenCoefficient_pos q).le (sq_nonneg _)
    have hp_le : deningerPrimeBlockGreenForm (Kp := Kp) p x x ≤
        deningerPrimeBlockSummedGreenForm x x := by
      calc
        deningerPrimeBlockGreenForm (Kp := Kp) p x x ≤
            ∑' q, deningerPrimeBlockGreenForm (Kp := Kp) q x x :=
          hscalar.le_tsum p (fun q _ => hnonneg q)
        _ = deningerPrimeBlockSummedGreenForm x x := by
          simpa [deningerPrimeBlockSummedGreenForm] using hinner.tsum_eq
    have hp_zero : deningerPrimeBlockGreenForm (Kp := Kp) p x x = 0 :=
      le_antisymm (hzero ▸ hp_le) (hnonneg p)
    rw [deningerPrimeBlockGreenForm, deningerBlockCoordinateGreenForm_apply_apply,
      real_inner_self_eq_norm_sq] at hp_zero
    have hnorm : ‖x p‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hp_zero).resolve_left
        (deningerPrimeGraphGreenCoefficient_pos p).ne'
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hnorm)
  · rintro rfl
    simp

end

end RHTower
