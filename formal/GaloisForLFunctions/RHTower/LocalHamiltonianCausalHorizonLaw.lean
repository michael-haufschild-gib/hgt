import GaloisForLFunctions.RHTower.LocalHorizonQuantumReturnLaw
import GaloisForLFunctions.RHTower.PerfectReturnPathRigidity
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Local Hamiltonian causal-horizon law

For an endpoint probe of a finite self-adjoint nearest-neighbour Hamiltonian,
exact agreement of path data through radius `R` forces agreement of every
endpoint power moment through round-trip order `2R+2`.  Consequently the
physical return amplitudes and probabilities obey dimension-free factorial
remainder bounds.  The amplitude used below is proved to be exactly the
matrix element of the standard operator exponential.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RHTower.ParityForecast

/-- Endpoint support through site `s`. -/
def EndpointSupported {n : ℕ} (s : ℕ) (v : ClockSpace n) : Prop :=
  ∀ i : Fin (n + 1), s < (i : ℕ) →
    inner ℂ
      (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i) v = 0

theorem endpointSupported_fixedClock (n : ℕ) :
    EndpointSupported 0 (fixedClock n) := by
  intro i hi
  unfold fixedClock
  exact
    (EuclideanSpace.basisFun
      (Fin (n + 1)) ℂ).orthonormal.2 (by
        intro hi0
        subst i
        simp at hi)

theorem EndpointSupported.map_nearestNeighbor
    {n s : ℕ} {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hnn : NearestNeighborHamiltonian A)
    {v : ClockSpace n} (hv : EndpointSupported s v) :
    EndpointSupported (s + 1) (A v) := by
  intro i hi
  rw [inner_map_eq_sum_matrix]
  apply Finset.sum_eq_zero
  intro j _hj
  by_cases hjs : (j : ℕ) ≤ s
  · rw [hnn i j (Or.inr (by omega))]
    simp
  · rw [hv j (by omega)]
    simp

/-- Endpoint Krylov iterate, defined without choosing a polynomial representation. -/
def endpointIterate {n : ℕ}
    (A : ClockSpace n →L[ℂ] ClockSpace n) :
    ℕ → ClockSpace n
  | 0 => fixedClock n
  | k + 1 => A (endpointIterate A k)

theorem endpointIterate_supported
    {n : ℕ} {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hnn : NearestNeighborHamiltonian A) :
    ∀ k : ℕ, EndpointSupported k (endpointIterate A k) := by
  intro k
  induction k with
  | zero =>
      exact endpointSupported_fixedClock n
  | succ k ih =>
      exact ih.map_nearestNeighbor hnn

/-- Matrix entries needed by all endpoint walks of round-trip length `2R+2`. -/
def EndpointLocalMatrixEq {n : ℕ}
    (R : ℕ) (A B : ClockSpace n →L[ℂ] ClockSpace n) : Prop :=
  ∀ i j : Fin (n + 1),
    (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
    inner ℂ
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i)
        (A (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j)) =
      inner ℂ
        (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i)
        (B (EuclideanSpace.basisFun (Fin (n + 1)) ℂ j))

theorem endpointLocalMatrixEq_of_prefix
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    (hsize : R + 2 ≤ n + 1)
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hprefix : ∀ i j : Fin (R + 2),
      (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2 →
      inner ℂ
          (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
            (Fin.castLE hsize i))
          (A (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
            (Fin.castLE hsize j))) =
        inner ℂ
          (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
            (Fin.castLE hsize i))
          (B (EuclideanSpace.basisFun (Fin (n + 1)) ℂ
            (Fin.castLE hsize j)))) :
    EndpointLocalMatrixEq R A B := by
  intro i j hij
  by_cases hi : (i : ℕ) < R + 2
  · by_cases hj : (j : ℕ) < R + 2
    · let i' : Fin (R + 2) := ⟨i, hi⟩
      let j' : Fin (R + 2) := ⟨j, hj⟩
      simpa [i', j'] using hprefix i' j' hij
    · have hfar : (i : ℕ) + 1 < (j : ℕ) := by omega
      rw [hAnn i j (Or.inl hfar), hBnn i j (Or.inl hfar)]
  · by_cases hj : (j : ℕ) < R + 2
    · have hfar : (j : ℕ) + 1 < (i : ℕ) := by omega
      rw [hAnn i j (Or.inr hfar), hBnn i j (Or.inr hfar)]
    · omega

theorem endpointIterate_eq_of_local
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hlocal : EndpointLocalMatrixEq R A B) :
    ∀ k ≤ R + 1, endpointIterate A k = endpointIterate B k := by
  intro k hk
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      have hkR : k ≤ R := by omega
      have hprev := ih (by omega)
      rw [endpointIterate, endpointIterate, ← hprev]
      let v := endpointIterate A k
      apply InnerProductSpace.ext_inner_left_basis
        (EuclideanSpace.basisFun
          (Fin (n + 1)) ℂ).toBasis
      intro i
      change
        inner ℂ
            (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i)
            (A v) =
          inner ℂ
            (EuclideanSpace.basisFun (Fin (n + 1)) ℂ i)
            (B v)
      by_cases hi : (i : ℕ) ≤ k + 1
      · rw [inner_map_eq_sum_matrix A i v,
          inner_map_eq_sum_matrix B i v]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hj : (j : ℕ) ≤ k
        · rw [hlocal i j (by omega)]
        · rw [(endpointIterate_supported hAnn k) j (by omega)]
          simp
      · rw [(endpointIterate_supported hAnn k).map_nearestNeighbor
            hAnn i (by omega),
          (endpointIterate_supported hAnn k).map_nearestNeighbor
            hBnn i (by omega)]

/-- The endpoint power moment, expressed by recursive Krylov iteration. -/
def endpointPowerMoment {n : ℕ}
    (A : ClockSpace n →L[ℂ] ClockSpace n)
    (m : ℕ) : ℂ :=
  inner ℂ (fixedClock n) (endpointIterate A m)

theorem inner_endpointIterate_eq_powerMoment_add
    {n : ℕ} {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hA : ContinuousLinearMap.adjoint A = A) :
    ∀ a b : ℕ,
      inner ℂ (endpointIterate A a) (endpointIterate A b) =
        endpointPowerMoment A (a + b) := by
  intro a
  induction a with
  | zero =>
      intro b
      simp [endpointIterate, endpointPowerMoment]
  | succ a ih =>
      intro b
      rw [endpointIterate]
      have hsymm :
          inner ℂ (A (endpointIterate A a))
              (endpointIterate A b) =
            inner ℂ (endpointIterate A a)
              (A (endpointIterate A b)) := by
        rw [← ContinuousLinearMap.adjoint_inner_right, hA]
      rw [hsymm, ← endpointIterate]
      rw [ih (b + 1)]
      exact congrArg (endpointPowerMoment A) (by omega)

/--
**Causal local-moment converse.** Exact path data through radius `R`
determines every endpoint power moment through round-trip order `2R+2`.
-/
theorem endpointPowerMoment_eq_of_local
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hASA : ContinuousLinearMap.adjoint A = A)
    (hBSA : ContinuousLinearMap.adjoint B = B)
    (hlocal : EndpointLocalMatrixEq R A B) :
    ∀ m ≤ 2 * R + 2,
      endpointPowerMoment A m = endpointPowerMoment B m := by
  intro m hm
  by_cases hmshort : m ≤ R + 1
  · unfold endpointPowerMoment
    rw [endpointIterate_eq_of_local hAnn hBnn hlocal m hmshort]
  · let b := m - (R + 1)
    have hRle : R + 1 ≤ m := by omega
    have hb : b ≤ R + 1 := by
      dsimp [b]
      omega
    have hsum : R + 1 + b = m := by
      dsimp [b]
      omega
    rw [← hsum,
      ← inner_endpointIterate_eq_powerMoment_add hASA (R + 1) b,
      ← inner_endpointIterate_eq_powerMoment_add hBSA (R + 1) b]
    rw [endpointIterate_eq_of_local hAnn hBnn hlocal
        (R + 1) (by omega),
      endpointIterate_eq_of_local hAnn hBnn hlocal b hb]

theorem endpointIterate_norm_le
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n) :
    ∀ m : ℕ, ‖endpointIterate A m‖ ≤ ‖A‖ ^ m := by
  intro m
  induction m with
  | zero =>
      simp [endpointIterate, fixedClock_norm]
  | succ m ih =>
      rw [endpointIterate, pow_succ]
      exact (A.le_opNorm _).trans
        (by
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left ih (norm_nonneg A))

theorem endpointPowerMoment_norm_le
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n)
    (m : ℕ) :
    ‖endpointPowerMoment A m‖ ≤ ‖A‖ ^ m := by
  unfold endpointPowerMoment
  calc
    ‖inner ℂ (fixedClock n) (endpointIterate A m)‖
        ≤ ‖fixedClock n‖ * ‖endpointIterate A m‖ :=
      norm_inner_le_norm _ _
    _ = ‖endpointIterate A m‖ := by
      rw [fixedClock_norm, one_mul]
    _ ≤ ‖A‖ ^ m := endpointIterate_norm_le A m

theorem endpointIterate_eq_pow_apply
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n) :
    ∀ m : ℕ, endpointIterate A m = (A ^ m) (fixedClock n) := by
  intro m
  induction m with
  | zero =>
      simp [endpointIterate]
  | succ m ih =>
      rw [endpointIterate, pow_succ']
      simp only [ContinuousLinearMap.mul_apply, ih]

/-- Entire endpoint return amplitude defined by its absolutely convergent power series. -/
def endpointExponentialAmplitude {n : ℕ}
    (A : ClockSpace n →L[ℂ] ClockSpace n)
    (t : ℝ) : ℂ :=
  ∑' m : ℕ,
    (((t : ℂ) * Complex.I) ^ m / m.factorial) *
      endpointPowerMoment A m

theorem endpointExponentialAmplitude_summable
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n)
    (t : ℝ) :
    Summable (fun m : ℕ =>
      (((t : ℂ) * Complex.I) ^ m / m.factorial) *
        endpointPowerMoment A m) := by
  apply Summable.of_norm_bounded
    (g := fun m : ℕ => (|t| * ‖A‖) ^ m / m.factorial)
  · exact Real.summable_pow_div_factorial (|t| * ‖A‖)
  · intro m
    rw [norm_mul, norm_div, norm_pow, norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      RCLike.norm_natCast]
    calc
      |t| ^ m / (m.factorial : ℝ) *
          ‖endpointPowerMoment A m‖
          ≤ |t| ^ m / (m.factorial : ℝ) * ‖A‖ ^ m := by
        gcongr
        exact endpointPowerMoment_norm_le A m
      _ = (|t| * ‖A‖) ^ m / m.factorial := by
        rw [mul_pow]
        field_simp

set_option synthInstance.maxHeartbeats 100000 in
/-- The power-series amplitude is exactly the endpoint matrix element of the
standard operator exponential. -/
theorem endpointExponentialAmplitude_eq_inner_exp
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n)
    (t : ℝ) :
    endpointExponentialAmplitude A t =
      inner ℂ (fixedClock n)
        ((NormedSpace.exp
          (((t : ℂ) * Complex.I) • A)) (fixedClock n)) := by
  let φ :
      (ClockSpace n →L[ℂ] ClockSpace n) →L[ℂ] ℂ :=
    (innerSL ℂ (fixedClock n)).comp
      ((ContinuousLinearMap.apply ℂ (ClockSpace n)) (fixedClock n))
  have hs :=
    NormedSpace.exp_series_hasSum_exp'
      (𝕂 := ℂ) (((t : ℂ) * Complex.I) • A)
  have hmap := hs.map φ φ.continuous
  unfold endpointExponentialAmplitude
  change (∑' m : ℕ,
      (((t : ℂ) * Complex.I) ^ m / m.factorial) *
        endpointPowerMoment A m) =
    φ (NormedSpace.exp (((t : ℂ) * Complex.I) • A))
  rw [← hmap.tsum_eq]
  apply tsum_congr
  intro m
  unfold φ
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply,
    ContinuousLinearMap.smul_apply, smul_pow,
    endpointPowerMoment, endpointIterate_eq_pow_apply,
    inner_smul_right]
  ring

set_option synthInstance.maxHeartbeats 100000 in
theorem endpointExponentialAmplitude_norm_le_one
    {n : ℕ} {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hA : ContinuousLinearMap.adjoint A = A)
    (t : ℝ) :
    ‖endpointExponentialAmplitude A t‖ ≤ 1 := by
  have hskew :
      (((t : ℂ) * Complex.I) • A) ∈
        skewAdjoint (ClockSpace n →L[ℂ] ClockSpace n) := by
    rw [skewAdjoint.mem_iff]
    simp [ContinuousLinearMap.star_eq_adjoint, hA]
    exact neg_smul ((t : ℂ) * Complex.I) A
  letI : NormedAlgebra ℚ
      (ClockSpace n →L[ℂ] ClockSpace n) :=
    .restrictScalars ℚ ℂ (ClockSpace n →L[ℂ] ClockSpace n)
  have hunit :
      NormedSpace.exp (((t : ℂ) * Complex.I) • A) ∈
        unitary (ClockSpace n →L[ℂ] ClockSpace n) :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskew
  rw [endpointExponentialAmplitude_eq_inner_exp]
  calc
    ‖inner ℂ (fixedClock n)
        ((NormedSpace.exp (((t : ℂ) * Complex.I) • A))
          (fixedClock n))‖
        ≤ ‖fixedClock n‖ *
            ‖(NormedSpace.exp (((t : ℂ) * Complex.I) • A))
              (fixedClock n)‖ := norm_inner_le_norm _ _
    _ = 1 := by
      rw [(NormedSpace.exp (((t : ℂ) * Complex.I) • A)).norm_map_of_mem_unitary
        hunit, fixedClock_norm]
      norm_num

/-- Physical endpoint return probability. -/
def endpointExponentialReturnProbability {n : ℕ}
    (A : ClockSpace n →L[ℂ] ClockSpace n)
    (t : ℝ) : ℝ :=
  Complex.normSq (endpointExponentialAmplitude A t)

theorem normSq_sub_normSq_abs_le
    (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |Complex.normSq a - Complex.normSq b| ≤ 2 * ‖a - b‖ := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hsum : ‖a‖ + ‖b‖ ≤ 2 := by linarith
  calc
    |‖a‖ ^ 2 - ‖b‖ ^ 2|
        = |(‖a‖ - ‖b‖) * (‖a‖ + ‖b‖)| := by ring_nf
    _ = |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
      rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ ‖a - b‖ * 2 := by
      gcongr
      exact abs_norm_sub_norm_le a b
    _ = 2 * ‖a - b‖ := by ring

theorem endpointExponentialAmplitude_difference_eq_tail
    {n N : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    (t : ℝ)
    (hmoment : ∀ m < N,
      endpointPowerMoment A m = endpointPowerMoment B m) :
    endpointExponentialAmplitude A t -
        endpointExponentialAmplitude B t =
      ∑' j : ℕ,
        (((t : ℂ) * Complex.I) ^ (j + N) / (j + N).factorial) *
          (endpointPowerMoment A (j + N) -
            endpointPowerMoment B (j + N)) := by
  let fA : ℕ → ℂ := fun m =>
    (((t : ℂ) * Complex.I) ^ m / m.factorial) *
      endpointPowerMoment A m
  let fB : ℕ → ℂ := fun m =>
    (((t : ℂ) * Complex.I) ^ m / m.factorial) *
      endpointPowerMoment B m
  have hsA : Summable fA :=
    endpointExponentialAmplitude_summable A t
  have hsB : Summable fB :=
    endpointExponentialAmplitude_summable B t
  have hhead :
      (∑ m ∈ Finset.range N, fA m) =
        ∑ m ∈ Finset.range N, fB m := by
    apply Finset.sum_congr rfl
    intro m hm
    unfold fA fB
    rw [hmoment m (Finset.mem_range.mp hm)]
  have hsplitA := hsA.sum_add_tsum_nat_add N
  have hsplitB := hsB.sum_add_tsum_nat_add N
  unfold endpointExponentialAmplitude
  change (∑' m, fA m) - ∑' m, fB m = _
  rw [← hsplitA, ← hsplitB, hhead, add_sub_add_left_eq_sub]
  have hsAtail : Summable (fun j : ℕ => fA (j + N)) :=
    hsA.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  have hsBtail : Summable (fun j : ℕ => fB (j + N)) :=
    hsB.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  rw [← hsAtail.tsum_sub hsBtail]
  apply tsum_congr
  intro j
  unfold fA fB
  ring

theorem endpointPowerMoment_sub_norm_le
    {n m : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ) :
    ‖endpointPowerMoment A m - endpointPowerMoment B m‖ ≤
      2 * Λ ^ m := by
  have hAm : ‖A‖ ^ m ≤ Λ ^ m := by
    gcongr
  have hBm : ‖B‖ ^ m ≤ Λ ^ m := by
    gcongr
  calc
    ‖endpointPowerMoment A m - endpointPowerMoment B m‖
        ≤ ‖endpointPowerMoment A m‖ +
            ‖endpointPowerMoment B m‖ := norm_sub_le _ _
    _ ≤ ‖A‖ ^ m + ‖B‖ ^ m :=
      add_le_add (endpointPowerMoment_norm_le A m)
        (endpointPowerMoment_norm_le B m)
    _ ≤ Λ ^ m + Λ ^ m := add_le_add hAm hBm
    _ = 2 * Λ ^ m := by ring

/-- Operator-norm bound for a finite real diagonal Hamiltonian from a
uniform pointwise energy bound. -/
theorem finiteIndexDiagonalHamiltonian_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ i, |energy i| ≤ E) :
    ‖finiteIndexDiagonalHamiltonian energy‖ ≤ E := by
  apply ContinuousLinearMap.opNorm_le_bound _ hE
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hE (norm_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
  simp only [finiteIndexDiagonalHamiltonian_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right
    (sq_le_sq₀ (abs_nonneg _) hE |>.mpr (hbound i))
    (sq_nonneg _)

theorem angularEnergy_abs_le
    {T : ℝ} (hT : 0 < T) (n : ℕ) (j : Fin (n + 1)) :
    |angularEnergy T n j| ≤ Real.pi * n / T := by
  rw [abs_of_nonneg (angularEnergy_nonneg hT n j),
    angularEnergy_eq]
  gcongr
  exact_mod_cast j.is_le

theorem scaledClockHamiltonian_norm_le
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖scaledClockHamiltonian T n‖ ≤ Real.pi * n / T := by
  unfold scaledClockHamiltonian
  apply finiteIndexDiagonalHamiltonian_norm_le
  · positivity
  · exact angularEnergy_abs_le hT n

/-- Every fixed-protocol conjugate inherits the common linear bandwidth
bound of the diagonal clock spectrum. -/
theorem fixedProtocolHamiltonian_norm_le
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ‖fixedProtocolHamiltonian T n U‖ ≤ Real.pi * n / T := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [← U.norm_map (fixedProtocolHamiltonian T n U x),
    fixedProtocolHamiltonian_intertwines]
  calc
    ‖scaledClockHamiltonian T n (U x)‖
        ≤ ‖scaledClockHamiltonian T n‖ * ‖U x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (Real.pi * n / T) * ‖U x‖ := by
      gcongr
      exact scaledClockHamiltonian_norm_le hT n
    _ = (Real.pi * n / T) * ‖x‖ := by rw [U.norm_map]

/-- The factorial gained after `j` additional orders dominates `j` copies
of the first new factor. -/
theorem factorial_mul_pow_succ_le_factorial_add
    (N j : ℕ) :
    N.factorial * (N + 1) ^ j ≤ (N + j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        N.factorial * (N + 1) ^ (j + 1) =
            (N.factorial * (N + 1) ^ j) * (N + 1) := by ring
        _ ≤ (N + j).factorial * (N + 1) :=
          Nat.mul_le_mul_right (N + 1) ih
        _ ≤ (N + j).factorial * (N + j + 1) := by
          exact Nat.mul_le_mul_left _ (by omega)
        _ = (N + (j + 1)).factorial := by
          rw [show N + (j + 1) = (N + j) + 1 by omega,
            Nat.factorial_succ]
          ring

/--
At action at most `N / exp(1)`, the exact exponential tail is at most twice
its first term.  The proof uses the consecutive-term ratio rather than the
coarser Lagrange remainder.
-/
theorem real_exp_sub_sum_le_twice_first_at_critical
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ (N : ℝ) / Real.exp 1) :
    Real.exp x - ∑ m ∈ Finset.range N, x ^ m / m.factorial ≤
      2 * (x ^ N / N.factorial) := by
  have hs : Summable (fun m : ℕ => x ^ m / m.factorial) :=
    Real.summable_pow_div_factorial x
  have hsum : (∑' m : ℕ, x ^ m / m.factorial) = Real.exp x := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail :
      Real.exp x - ∑ m ∈ Finset.range N, x ^ m / m.factorial =
        ∑' j : ℕ, x ^ (j + N) / (j + N).factorial := by
    rw [← hsum]
    linarith
  rw [htail]
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hxmul : x * Real.exp 1 ≤ (N : ℝ) :=
    (le_div_iff₀ he).mp hx
  have hxhalf : x ≤ ((N + 1 : ℕ) : ℝ) / 2 := by
    have h2x : 2 * x ≤ x * Real.exp 1 := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left Real.exp_one_gt_two.le hx0
    have hNle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  have hdenPos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hratio : x / ((N + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hdenPos).2 (by nlinarith)
  let first : ℝ := x ^ N / N.factorial
  let geom : ℕ → ℝ := fun j => first * (1 / 2 : ℝ) ^ j
  have hsGeom : Summable geom := by
    unfold geom
    exact (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left first
  have hterm (j : ℕ) :
      x ^ (j + N) / (j + N).factorial ≤ geom j := by
    have hfacNat :=
      factorial_mul_pow_succ_le_factorial_add N j
    have hfac :
        (N.factorial : ℝ) * (((N + 1 : ℕ) : ℝ) ^ j) ≤
          ((N + j).factorial : ℝ) := by
      exact_mod_cast hfacNat
    have hsmallPos :
        0 < (N.factorial : ℝ) * (((N + 1 : ℕ) : ℝ) ^ j) := by
      positivity
    have hnum : x ^ (j + N) = x ^ N * x ^ j := by
      rw [Nat.add_comm, pow_add]
    rw [hnum]
    calc
      x ^ N * x ^ j / ((j + N).factorial : ℝ) ≤
          x ^ N * x ^ j /
            ((N.factorial : ℝ) * (((N + 1 : ℕ) : ℝ) ^ j)) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hsmallPos
        · simpa [Nat.add_comm] using hfac
      _ = first * (x / ((N + 1 : ℕ) : ℝ)) ^ j := by
        unfold first
        rw [div_pow]
        field_simp
      _ ≤ first * (1 / 2 : ℝ) ^ j := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_left₀ (div_nonneg hx0 hdenPos.le) hratio j
        · unfold first
          positivity
      _ = geom j := by rfl
  calc
    (∑' j : ℕ, x ^ (j + N) / (j + N).factorial) ≤
        ∑' j : ℕ, geom j := by
      exact ((summable_nat_add_iff N).2 hs).tsum_le_tsum hterm hsGeom
    _ = first * 2 := by
      unfold geom
      rw [tsum_mul_left]
      norm_num [tsum_geometric_of_norm_lt_one]
    _ = 2 * (x ^ N / N.factorial) := by
      unfold first
      ring

/-- At the critical action, Stirling's global lower bound controls the
first omitted exponential coefficient by the inverse square-root law. -/
theorem factorial_first_term_le_inv_sqrt_at_critical
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ (N : ℝ) / Real.exp 1) :
    x ^ N / (N.factorial : ℝ) ≤
      1 / Real.sqrt (2 * Real.pi * (N : ℝ)) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : 0 < (N : ℝ) / Real.exp 1 := div_pos hNreal he
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * (N : ℝ)) := by
    positivity
  have hpow :
      x ^ N ≤ ((N : ℝ) / Real.exp 1) ^ N :=
    pow_le_pow_left₀ hx0 hx N
  have hfac :
      Real.sqrt (2 * Real.pi * (N : ℝ)) *
          ((N : ℝ) / Real.exp 1) ^ N ≤
        (N.factorial : ℝ) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Stirling.le_factorial_stirling N
  calc
    x ^ N / (N.factorial : ℝ) ≤
        ((N : ℝ) / Real.exp 1) ^ N / (N.factorial : ℝ) := by
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ ((N : ℝ) / Real.exp 1) ^ N /
          (Real.sqrt (2 * Real.pi * (N : ℝ)) *
            ((N : ℝ) / Real.exp 1) ^ N) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ = 1 / Real.sqrt (2 * Real.pi * (N : ℝ)) := by
      field_simp

/-- Critical exact exponential-tail law. -/
theorem real_exp_sub_sum_le_inv_sqrt_critical
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ (N : ℝ) / Real.exp 1) :
    Real.exp x - ∑ m ∈ Finset.range N, x ^ m / m.factorial ≤
      2 / Real.sqrt (2 * Real.pi * (N : ℝ)) := by
  calc
    _ ≤ 2 * (x ^ N / N.factorial) :=
      real_exp_sub_sum_le_twice_first_at_critical N hN x hx0 hx
    _ ≤ 2 * (1 / Real.sqrt (2 * Real.pi * (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (factorial_first_term_le_inv_sqrt_at_critical N hN x hx0 hx)
        (by norm_num)
    _ = 2 / Real.sqrt (2 * Real.pi * (N : ℝ)) := by ring

/-- Dimension-free factorial tail: matching the first `N` endpoint moments controls
the entire return amplitude, independently of ambient Hilbert-space dimension. -/
theorem endpointExponentialAmplitude_difference_norm_le
    {n N : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    (t : ℝ)
    (hmoment : ∀ m < N,
      endpointPowerMoment A m = endpointPowerMoment B m) :
    ‖endpointExponentialAmplitude A t -
        endpointExponentialAmplitude B t‖ ≤
      2 * (((|t| * Λ) ^ N / N.factorial) *
        Real.exp (|t| * Λ)) := by
  rw [endpointExponentialAmplitude_difference_eq_tail t hmoment]
  let r : ℝ := |t| * Λ
  let d : ℕ → ℂ := fun j =>
    (((t : ℂ) * Complex.I) ^ (j + N) / (j + N).factorial) *
      (endpointPowerMoment A (j + N) -
        endpointPowerMoment B (j + N))
  let g : ℕ → ℝ := fun j =>
    2 * (r ^ (j + N) / (j + N).factorial)
  have hr : 0 ≤ r := mul_nonneg (abs_nonneg t) hΛ
  have hsExp : Summable (fun m : ℕ => r ^ m / m.factorial) :=
    Real.summable_pow_div_factorial r
  have hsG : Summable g := by
    unfold g
    exact (((summable_nat_add_iff N).2 hsExp).mul_left 2)
  have hterm (j : ℕ) : ‖d j‖ ≤ g j := by
    unfold d g r
    rw [norm_mul, norm_div, norm_pow, norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      RCLike.norm_natCast]
    calc
      |t| ^ (j + N) / ((j + N).factorial : ℝ) *
          ‖endpointPowerMoment A (j + N) -
            endpointPowerMoment B (j + N)‖
          ≤ |t| ^ (j + N) / ((j + N).factorial : ℝ) *
              (2 * Λ ^ (j + N)) := by
            gcongr
            exact endpointPowerMoment_sub_norm_le hA hB
      _ = 2 * ((|t| * Λ) ^ (j + N) /
            ((j + N).factorial : ℝ)) := by
        rw [mul_pow]
        ring
  have hsDnorm : Summable (fun j : ℕ => ‖d j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsG
  have hsum : (∑' m : ℕ, r ^ m / m.factorial) = Real.exp r := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp r).tsum_eq
  have hsplit := hsExp.sum_add_tsum_nat_add N
  have htail :
      (∑' j : ℕ, r ^ (j + N) / (j + N).factorial) =
        Real.exp r -
          ∑ m ∈ Finset.range N, r ^ m / m.factorial := by
    rw [← hsum]
    linarith
  change ‖∑' j : ℕ, d j‖ ≤ _
  calc
    ‖∑' j : ℕ, d j‖ ≤ ∑' j : ℕ, ‖d j‖ :=
      norm_tsum_le_tsum_norm hsDnorm
    _ ≤ ∑' j : ℕ, g j := hsDnorm.tsum_le_tsum hterm hsG
    _ = 2 * (Real.exp r -
          ∑ m ∈ Finset.range N, r ^ m / m.factorial) := by
      unfold g
      rw [tsum_mul_left, htail]
    _ ≤ 2 * ((r ^ N / N.factorial) * Real.exp r) := by
      gcongr
      exact real_exp_sub_sum_le_factorial_tail r hr N
    _ = 2 * (((|t| * Λ) ^ N / N.factorial) *
          Real.exp (|t| * Λ)) := by rfl

/--
Exact-tail form of the endpoint response law.  Unlike the convenient
Lagrange bound, this retains the full exponential series tail and remains
informative at action `N / exp(1)`.
-/
theorem endpointExponentialAmplitude_difference_norm_le_exactTail
    {n N : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    (t : ℝ)
    (hmoment : ∀ m < N,
      endpointPowerMoment A m = endpointPowerMoment B m) :
    ‖endpointExponentialAmplitude A t -
        endpointExponentialAmplitude B t‖ ≤
      2 * (Real.exp (|t| * Λ) -
        ∑ m ∈ Finset.range N,
          (|t| * Λ) ^ m / m.factorial) := by
  rw [endpointExponentialAmplitude_difference_eq_tail t hmoment]
  let r : ℝ := |t| * Λ
  let d : ℕ → ℂ := fun j =>
    (((t : ℂ) * Complex.I) ^ (j + N) / (j + N).factorial) *
      (endpointPowerMoment A (j + N) -
        endpointPowerMoment B (j + N))
  let g : ℕ → ℝ := fun j =>
    2 * (r ^ (j + N) / (j + N).factorial)
  have hr : 0 ≤ r := mul_nonneg (abs_nonneg t) hΛ
  have hsExp : Summable (fun m : ℕ => r ^ m / m.factorial) :=
    Real.summable_pow_div_factorial r
  have hsG : Summable g := by
    unfold g
    exact (((summable_nat_add_iff N).2 hsExp).mul_left 2)
  have hterm (j : ℕ) : ‖d j‖ ≤ g j := by
    unfold d g r
    rw [norm_mul, norm_div, norm_pow, norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      RCLike.norm_natCast]
    calc
      |t| ^ (j + N) / ((j + N).factorial : ℝ) *
          ‖endpointPowerMoment A (j + N) -
            endpointPowerMoment B (j + N)‖
          ≤ |t| ^ (j + N) / ((j + N).factorial : ℝ) *
              (2 * Λ ^ (j + N)) := by
            gcongr
            exact endpointPowerMoment_sub_norm_le hA hB
      _ = 2 * ((|t| * Λ) ^ (j + N) /
            ((j + N).factorial : ℝ)) := by
        rw [mul_pow]
        ring
  have hsDnorm : Summable (fun j : ℕ => ‖d j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsG
  have hsum : (∑' m : ℕ, r ^ m / m.factorial) = Real.exp r := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp r).tsum_eq
  have hsplit := hsExp.sum_add_tsum_nat_add N
  have htail :
      (∑' j : ℕ, r ^ (j + N) / (j + N).factorial) =
        Real.exp r -
          ∑ m ∈ Finset.range N, r ^ m / m.factorial := by
    rw [← hsum]
    linarith
  change ‖∑' j : ℕ, d j‖ ≤ _
  calc
    ‖∑' j : ℕ, d j‖ ≤ ∑' j : ℕ, ‖d j‖ :=
      norm_tsum_le_tsum_norm hsDnorm
    _ ≤ ∑' j : ℕ, g j := hsDnorm.tsum_le_tsum hterm hsG
    _ = 2 * (Real.exp r -
          ∑ m ∈ Finset.range N, r ^ m / m.factorial) := by
      unfold g
      rw [tsum_mul_left, htail]
    _ = 2 * (Real.exp (|t| * Λ) -
          ∑ m ∈ Finset.range N,
            (|t| * Λ) ^ m / m.factorial) := by rfl

/--
Critical endpoint response law: at action at most `N / exp(1)`, matching
`N` moments forces inverse-square-root amplitude agreement.
-/
theorem endpointExponentialAmplitude_difference_norm_le_critical
    {n N : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hN : 0 < N)
    (hΛ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    (t : ℝ)
    (hmoment : ∀ m < N,
      endpointPowerMoment A m = endpointPowerMoment B m)
    (hcritical : |t| * Λ ≤ (N : ℝ) / Real.exp 1) :
    ‖endpointExponentialAmplitude A t -
        endpointExponentialAmplitude B t‖ ≤
      4 / Real.sqrt (2 * Real.pi * (N : ℝ)) := by
  calc
    _ ≤ 2 * (Real.exp (|t| * Λ) -
          ∑ m ∈ Finset.range N,
            (|t| * Λ) ^ m / m.factorial) :=
      endpointExponentialAmplitude_difference_norm_le_exactTail
        hΛ hA hB t hmoment
    _ ≤ 2 * (2 / Real.sqrt (2 * Real.pi * (N : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact real_exp_sub_sum_le_inv_sqrt_critical
          N hN (|t| * Λ)
          (mul_nonneg (abs_nonneg t) hΛ) hcritical
      · norm_num
    _ = 4 / Real.sqrt (2 * Real.pi * (N : ℝ)) := by ring

/-- Radius-`R` nearest-neighbour agreement fixes the first `2R+3` Taylor
coefficients and leaves only a factorially small tail. -/
theorem localCausalHorizon_amplitude_bound
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hASA : ContinuousLinearMap.adjoint A = A)
    (hBSA : ContinuousLinearMap.adjoint B = B)
    (hlocal : EndpointLocalMatrixEq R A B)
    (t : ℝ) :
    ‖endpointExponentialAmplitude A t -
        endpointExponentialAmplitude B t‖ ≤
      2 * (((|t| * Λ) ^ (2 * R + 3) / (2 * R + 3).factorial) *
        Real.exp (|t| * Λ)) := by
  apply endpointExponentialAmplitude_difference_norm_le
    hΛ hA hB t
  intro m hm
  exact endpointPowerMoment_eq_of_local hAnn hBnn hASA hBSA hlocal m
    (by omega)

/-- Probability form of the dimension-free local causal-horizon law. -/
theorem localCausalHorizon_probability_bound
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hASA : ContinuousLinearMap.adjoint A = A)
    (hBSA : ContinuousLinearMap.adjoint B = B)
    (hlocal : EndpointLocalMatrixEq R A B)
    (t : ℝ) :
    |endpointExponentialReturnProbability A t -
        endpointExponentialReturnProbability B t| ≤
      4 * (((|t| * Λ) ^ (2 * R + 3) / (2 * R + 3).factorial) *
        Real.exp (|t| * Λ)) := by
  unfold endpointExponentialReturnProbability
  calc
    |Complex.normSq (endpointExponentialAmplitude A t) -
        Complex.normSq (endpointExponentialAmplitude B t)|
        ≤ 2 * ‖endpointExponentialAmplitude A t -
            endpointExponentialAmplitude B t‖ :=
      normSq_sub_normSq_abs_le _ _
        (endpointExponentialAmplitude_norm_le_one hASA t)
        (endpointExponentialAmplitude_norm_le_one hBSA t)
    _ ≤ 2 * (2 * (((|t| * Λ) ^ (2 * R + 3) /
          (2 * R + 3).factorial) * Real.exp (|t| * Λ))) := by
      gcongr
      exact localCausalHorizon_amplitude_bound
        hΛ hA hB hAnn hBnn hASA hBSA hlocal t
    _ = 4 * (((|t| * Λ) ^ (2 * R + 3) /
          (2 * R + 3).factorial) * Real.exp (|t| * Λ)) := by ring

/--
At the critical local action `(2R+3)/exp(1)`, the return-probability
discrepancy is universally inverse-square-root in the round-trip order.
-/
theorem localCausalHorizon_probability_bound_critical
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ) (hB : ‖B‖ ≤ Λ)
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hASA : ContinuousLinearMap.adjoint A = A)
    (hBSA : ContinuousLinearMap.adjoint B = B)
    (hlocal : EndpointLocalMatrixEq R A B)
    (t : ℝ)
    (hcritical :
      |t| * Λ ≤ ((2 * R + 3 : ℕ) : ℝ) / Real.exp 1) :
    |endpointExponentialReturnProbability A t -
        endpointExponentialReturnProbability B t| ≤
      8 / Real.sqrt
        (2 * Real.pi * ((2 * R + 3 : ℕ) : ℝ)) := by
  unfold endpointExponentialReturnProbability
  calc
    |Complex.normSq (endpointExponentialAmplitude A t) -
        Complex.normSq (endpointExponentialAmplitude B t)|
        ≤ 2 * ‖endpointExponentialAmplitude A t -
            endpointExponentialAmplitude B t‖ :=
      normSq_sub_normSq_abs_le _ _
        (endpointExponentialAmplitude_norm_le_one hASA t)
        (endpointExponentialAmplitude_norm_le_one hBSA t)
    _ ≤ 2 * (4 / Real.sqrt
          (2 * Real.pi * ((2 * R + 3 : ℕ) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · apply endpointExponentialAmplitude_difference_norm_le_critical
          (N := 2 * R + 3) (by omega) hΛ hA hB t
        · intro m hm
          exact endpointPowerMoment_eq_of_local
            hAnn hBnn hASA hBSA hlocal m (by omega)
        · exact hcritical
      · norm_num
    _ = 8 / Real.sqrt
          (2 * Real.pi * ((2 * R + 3 : ℕ) : ℝ)) := by ring

/-- A common real energy-origin shift.  Return probabilities are invariant
under this gauge transformation. -/
def energyGaugeShift {n : ℕ} (c : ℝ)
    (A : ClockSpace n →L[ℂ] ClockSpace n) :
    ClockSpace n →L[ℂ] ClockSpace n :=
  A - (c : ℂ) • ContinuousLinearMap.id ℂ (ClockSpace n)

theorem energyGaugeShift_nearestNeighbor
    {n : ℕ} {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hA : NearestNeighborHamiltonian A) (c : ℝ) :
    NearestNeighborHamiltonian (energyGaugeShift c A) := by
  intro i j hfar
  have hij : i ≠ j := by
    intro hij
    subst j
    omega
  unfold energyGaugeShift
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right]
  rw [hA i j hfar, EuclideanSpace.basisFun_inner]
  simp [hij]

theorem energyGaugeShift_selfAdjoint
    {n : ℕ} {A : ClockSpace n →L[ℂ] ClockSpace n}
    (hA : ContinuousLinearMap.adjoint A = A) (c : ℝ) :
    ContinuousLinearMap.adjoint (energyGaugeShift c A) =
      energyGaugeShift c A := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  unfold energyGaugeShift
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right]
  rw [← ContinuousLinearMap.adjoint_inner_right A x y, hA]
  simp

theorem energyGaugeShift_local
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    (hlocal : EndpointLocalMatrixEq R A B) (c : ℝ) :
    EndpointLocalMatrixEq R
      (energyGaugeShift c A) (energyGaugeShift c B) := by
  intro i j hij
  unfold energyGaugeShift
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right]
  rw [hlocal i j hij]

set_option synthInstance.maxHeartbeats 100000 in
theorem energyGaugeShift_exp_apply
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n)
    (c : ℝ) (z : ℂ) (x : ClockSpace n) :
    (NormedSpace.exp (z • energyGaugeShift c A)) x =
      Complex.exp (-z * c) •
        (NormedSpace.exp (z • A)) x := by
  letI : NormedAlgebra ℚ
      (ClockSpace n →L[ℂ] ClockSpace n) :=
    .restrictScalars ℚ ℂ (ClockSpace n →L[ℂ] ClockSpace n)
  let s : ℂ := -z * c
  have hscalar :
      s • ContinuousLinearMap.id ℂ (ClockSpace n) =
        algebraMap ℂ (ClockSpace n →L[ℂ] ClockSpace n) s := by
    ext y
    simp
  have harg :
      z • energyGaugeShift c A =
        s • ContinuousLinearMap.id ℂ (ClockSpace n) + z • A := by
    unfold energyGaugeShift
    rw [smul_sub, smul_smul]
    dsimp [s]
    module
  rw [harg, hscalar,
    NormedSpace.exp_add_of_commute (Algebra.commutes s (z • A)),
    ← NormedSpace.algebraMap_exp_comm]
  simp [s, Complex.exp_eq_exp_ℂ]

theorem energyGaugeShift_returnProbability
    {n : ℕ} (A : ClockSpace n →L[ℂ] ClockSpace n)
    (c t : ℝ) :
    endpointExponentialReturnProbability (energyGaugeShift c A) t =
      endpointExponentialReturnProbability A t := by
  unfold endpointExponentialReturnProbability
  rw [endpointExponentialAmplitude_eq_inner_exp,
    endpointExponentialAmplitude_eq_inner_exp,
    energyGaugeShift_exp_apply]
  rw [inner_smul_right, Complex.normSq_mul]
  have hphase :
      Complex.normSq
          (Complex.exp (-((t : ℂ) * Complex.I) * c)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  rw [hphase, one_mul]

/--
**Gauge-invariant local causal bound.**

The norm certificate may be imposed after any common real energy-origin
shift.  The observable return law and local equality are unchanged.
-/
theorem localCausalHorizon_probability_bound_gauge
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ c : ℝ} (hΛ : 0 ≤ Λ)
    (hA : ‖energyGaugeShift c A‖ ≤ Λ)
    (hB : ‖energyGaugeShift c B‖ ≤ Λ)
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hASA : ContinuousLinearMap.adjoint A = A)
    (hBSA : ContinuousLinearMap.adjoint B = B)
    (hlocal : EndpointLocalMatrixEq R A B)
    (t : ℝ) :
    |endpointExponentialReturnProbability A t -
        endpointExponentialReturnProbability B t| ≤
      4 * (((|t| * Λ) ^ (2 * R + 3) /
        (2 * R + 3).factorial) *
        Real.exp (|t| * Λ)) := by
  have hbound :=
    localCausalHorizon_probability_bound
      hΛ hA hB
      (energyGaugeShift_nearestNeighbor hAnn c)
      (energyGaugeShift_nearestNeighbor hBnn c)
      (energyGaugeShift_selfAdjoint hASA c)
      (energyGaugeShift_selfAdjoint hBSA c)
      (energyGaugeShift_local hlocal c) t
  simpa only [energyGaugeShift_returnProbability] using hbound

/--
Gauge-invariant critical local causal law.  A common centred bandwidth
certificate at action `(2R+3)/exp(1)` forces inverse-square-root agreement.
-/
theorem localCausalHorizon_probability_bound_critical_gauge
    {n R : ℕ} {A B : ClockSpace n →L[ℂ] ClockSpace n}
    {Λ c : ℝ} (hΛ : 0 ≤ Λ)
    (hA : ‖energyGaugeShift c A‖ ≤ Λ)
    (hB : ‖energyGaugeShift c B‖ ≤ Λ)
    (hAnn : NearestNeighborHamiltonian A)
    (hBnn : NearestNeighborHamiltonian B)
    (hASA : ContinuousLinearMap.adjoint A = A)
    (hBSA : ContinuousLinearMap.adjoint B = B)
    (hlocal : EndpointLocalMatrixEq R A B)
    (t : ℝ)
    (hcritical :
      |t| * Λ ≤ ((2 * R + 3 : ℕ) : ℝ) / Real.exp 1) :
    |endpointExponentialReturnProbability A t -
        endpointExponentialReturnProbability B t| ≤
      8 / Real.sqrt
        (2 * Real.pi * ((2 * R + 3 : ℕ) : ℝ)) := by
  have hbound :=
    localCausalHorizon_probability_bound_critical
      hΛ hA hB
      (energyGaugeShift_nearestNeighbor hAnn c)
      (energyGaugeShift_nearestNeighbor hBnn c)
      (energyGaugeShift_selfAdjoint hASA c)
      (energyGaugeShift_selfAdjoint hBSA c)
      (energyGaugeShift_local hlocal c) t hcritical
  simpa only [energyGaugeShift_returnProbability] using hbound

/-- Midpoint of the common clock spectrum. -/
def clockEnergyCenter (T : ℝ) (n : ℕ) : ℝ :=
  Real.pi * n / (2 * T)

def centeredAngularEnergy (T : ℝ) (n : ℕ)
    (j : Fin (n + 1)) : ℝ :=
  angularEnergy T n j - clockEnergyCenter T n

theorem centeredAngularEnergy_abs_le
    {T : ℝ} (hT : 0 < T) (n : ℕ) (j : Fin (n + 1)) :
    |centeredAngularEnergy T n j| ≤ clockEnergyCenter T n := by
  have hE0 : 0 ≤ angularEnergy T n j :=
    angularEnergy_nonneg hT n j
  have hEtop :
      angularEnergy T n j ≤ Real.pi * n / T := by
    rw [← abs_of_nonneg hE0]
    exact angularEnergy_abs_le hT n j
  have hc : 0 ≤ clockEnergyCenter T n := by
    unfold clockEnergyCenter
    positivity
  rw [abs_le]
  constructor
  · unfold centeredAngularEnergy
    linarith
  · unfold centeredAngularEnergy clockEnergyCenter
    calc
      angularEnergy T n j - Real.pi * ↑n / (2 * T)
          ≤ Real.pi * ↑n / T - Real.pi * ↑n / (2 * T) := by
            linarith
      _ = Real.pi * ↑n / (2 * T) := by
        field_simp
        ring

def centeredScaledClockHamiltonian (T : ℝ) (n : ℕ) :
    ClockSpace n →L[ℂ] ClockSpace n :=
  finiteIndexDiagonalHamiltonian (centeredAngularEnergy T n)

theorem centeredScaledClockHamiltonian_eq_shift
    (T : ℝ) (n : ℕ) :
    centeredScaledClockHamiltonian T n =
      energyGaugeShift (clockEnergyCenter T n)
        (scaledClockHamiltonian T n) := by
  ext x j
  simp [centeredScaledClockHamiltonian, centeredAngularEnergy,
    energyGaugeShift, scaledClockHamiltonian,
    finiteIndexDiagonalHamiltonian_apply]
  ring

theorem centeredScaledClockHamiltonian_norm_le
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖centeredScaledClockHamiltonian T n‖ ≤
      clockEnergyCenter T n := by
  unfold centeredScaledClockHamiltonian
  apply finiteIndexDiagonalHamiltonian_norm_le
  · unfold clockEnergyCenter
    positivity
  · exact centeredAngularEnergy_abs_le hT n

theorem fixedProtocolHamiltonian_centered_norm_le
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    (U : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n) :
    ‖energyGaugeShift (clockEnergyCenter T n)
        (fixedProtocolHamiltonian T n U)‖ ≤
      clockEnergyCenter T n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    unfold clockEnergyCenter
    positivity)
  intro x
  rw [← U.norm_map
    (energyGaugeShift (clockEnergyCenter T n)
      (fixedProtocolHamiltonian T n U) x)]
  have hintertwines :
      U (energyGaugeShift (clockEnergyCenter T n)
          (fixedProtocolHamiltonian T n U) x) =
        centeredScaledClockHamiltonian T n (U x) := by
    rw [centeredScaledClockHamiltonian_eq_shift]
    simp only [energyGaugeShift, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      map_sub, map_smul]
    rw [fixedProtocolHamiltonian_intertwines]
  rw [hintertwines]
  calc
    ‖centeredScaledClockHamiltonian T n (U x)‖
        ≤ ‖centeredScaledClockHamiltonian T n‖ * ‖U x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ clockEnergyCenter T n * ‖U x‖ := by
      gcongr
      exact centeredScaledClockHamiltonian_norm_le hT n
    _ = clockEnergyCenter T n * ‖x‖ := by rw [U.norm_map]

/-- The dimensionless factorial remainder appearing in the probability
causal-horizon law. -/
def localCausalFactorialBound (R : ℕ) (Λ t : ℝ) : ℝ :=
  4 * (((|t| * Λ) ^ (2 * R + 3) / (2 * R + 3).factorial) *
    Real.exp (|t| * Λ))

/-- A uniform linear energy--time ceiling turns the factorial causal
remainder into a geometric one.  The constant is explicit and
dimensionless. -/
theorem factorialTail_linear_bound
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx0 : 0 ≤ x)
    (hx :
      x ≤ (N : ℝ) / (2 * Real.exp 1 ^ 2)) :
    4 * ((x ^ N / N.factorial) * Real.exp x) ≤
      4 * (1 / 2 : ℝ) ^ N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hNge : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (N : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi := Real.pi_gt_three
    nlinarith
  have hbase : 0 < (N : ℝ) / Real.exp 1 := div_pos hNreal he
  have hfactorial :
      ((N : ℝ) / Real.exp 1) ^ N ≤ (N.factorial : ℝ) := by
    calc
      ((N : ℝ) / Real.exp 1) ^ N
          ≤ Real.sqrt (2 * Real.pi * (N : ℝ)) *
              ((N : ℝ) / Real.exp 1) ^ N := by
            exact le_mul_of_one_le_left (pow_nonneg hbase.le N) hsqrt
      _ ≤ (N.factorial : ℝ) := Stirling.le_factorial_stirling N
  have hscaled :
      x ≤ ((N : ℝ) / Real.exp 1) *
        (1 / (2 * Real.exp 1)) := by
    calc
      x ≤ (N : ℝ) / (2 * Real.exp 1 ^ 2) := hx
      _ = ((N : ℝ) / Real.exp 1) *
          (1 / (2 * Real.exp 1)) := by field_simp
  have hratio :
      x ^ N / (N.factorial : ℝ) ≤
        (1 / (2 * Real.exp 1) : ℝ) ^ N := by
    calc
      x ^ N / (N.factorial : ℝ)
          ≤ x ^ N / (((N : ℝ) / Real.exp 1) ^ N) := by
            exact div_le_div_of_nonneg_left (pow_nonneg hx0 N)
              (pow_pos hbase N) hfactorial
      _ ≤ ((((N : ℝ) / Real.exp 1) *
              (1 / (2 * Real.exp 1))) ^ N) /
            (((N : ℝ) / Real.exp 1) ^ N) := by
            gcongr
      _ = (1 / (2 * Real.exp 1) : ℝ) ^ N := by
            rw [mul_pow]
            field_simp
  have hxN : x ≤ (N : ℝ) := by
    calc
      x ≤ (N : ℝ) / (2 * Real.exp 1 ^ 2) := hx
      _ ≤ (N : ℝ) := by
        apply div_le_self hNreal.le
        nlinarith [sq_nonneg (Real.exp 1)]
  have hexp : Real.exp x ≤ (Real.exp 1) ^ N := by
    rw [Real.exp_one_pow]
    exact Real.exp_le_exp.mpr hxN
  calc
    4 * ((x ^ N / N.factorial) * Real.exp x)
        ≤ 4 * (((1 / (2 * Real.exp 1) : ℝ) ^ N) *
            ((Real.exp 1) ^ N)) := by
          gcongr
    _ = 4 * (1 / 2 : ℝ) ^ N := by
      rw [← mul_pow]
      field_simp

/-- A stronger linear regime obtained by retaining the exact exponential
base.  The geometric ratio `exp(1) / 3` is strictly below one. -/
theorem factorialTail_linear_bound_exp_three
    (N : ℕ) (hN : 0 < N) (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ (N : ℝ) / (3 * Real.exp 1)) :
    4 * ((x ^ N / N.factorial) * Real.exp x) ≤
      4 * (Real.exp 1 / 3) ^ N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (N : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi := Real.pi_gt_three
    have hNge : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hbase : 0 < (N : ℝ) / Real.exp 1 := div_pos hNreal he
  have hfactorial :
      ((N : ℝ) / Real.exp 1) ^ N ≤ (N.factorial : ℝ) := by
    calc
      ((N : ℝ) / Real.exp 1) ^ N
          ≤ Real.sqrt (2 * Real.pi * (N : ℝ)) *
              ((N : ℝ) / Real.exp 1) ^ N := by
            exact le_mul_of_one_le_left (pow_nonneg hbase.le N) hsqrt
      _ ≤ (N.factorial : ℝ) := Stirling.le_factorial_stirling N
  have hscaled :
      x ≤ ((N : ℝ) / Real.exp 1) * (1 / 3 : ℝ) := by
    calc
      x ≤ (N : ℝ) / (3 * Real.exp 1) := hx
      _ = ((N : ℝ) / Real.exp 1) * (1 / 3 : ℝ) := by field_simp
  have hratio :
      x ^ N / (N.factorial : ℝ) ≤ (1 / 3 : ℝ) ^ N := by
    calc
      x ^ N / (N.factorial : ℝ)
          ≤ x ^ N / (((N : ℝ) / Real.exp 1) ^ N) := by
            exact div_le_div_of_nonneg_left (pow_nonneg hx0 N)
              (pow_pos hbase N) hfactorial
      _ ≤ ((((N : ℝ) / Real.exp 1) * (1 / 3 : ℝ)) ^ N) /
            (((N : ℝ) / Real.exp 1) ^ N) := by
            gcongr
      _ = (1 / 3 : ℝ) ^ N := by
            rw [mul_pow]
            field_simp
  have hxN : x ≤ (N : ℝ) := by
    calc
      x ≤ (N : ℝ) / (3 * Real.exp 1) := hx
      _ ≤ (N : ℝ) := by
        apply div_le_self hNreal.le
        nlinarith
  have hexp : Real.exp x ≤ (Real.exp 1) ^ N := by
    rw [Real.exp_one_pow]
    exact Real.exp_le_exp.mpr hxN
  calc
    4 * ((x ^ N / N.factorial) * Real.exp x)
        ≤ 4 * (((1 / 3 : ℝ) ^ N) * ((Real.exp 1) ^ N)) := by
          gcongr
    _ = 4 * (Real.exp 1 / 3) ^ N := by
      rw [← mul_pow]
      congr 2
      ring

theorem localCausalFactorialBound_tendsto_zero
    (Λ t : ℝ) :
    Filter.Tendsto (fun R : ℕ => localCausalFactorialBound R Λ t)
      Filter.atTop (nhds 0) := by
  let x : ℝ := |t| * Λ
  have hindex :
      Filter.Tendsto (fun R : ℕ => 2 * R + 3)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with R hR
    omega
  have htail :
      Filter.Tendsto
        (fun R : ℕ => x ^ (2 * R + 3) / (2 * R + 3).factorial)
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop x).comp hindex
  unfold localCausalFactorialBound
  convert htail.const_mul (4 * Real.exp (|t| * Λ)) using 1
  · funext R
    ring
  · simp

/-- Persistent nonzero target-time separation through every increasing
local radius is impossible under a common uniform Hamiltonian norm bound. -/
theorem cofinalFutureSeparation_forces_unbounded_norm
    (n : ℕ → ℕ)
    (A B : ∀ R : ℕ, ClockSpace (n R) →L[ℂ] ClockSpace (n R))
    (T ε : ℝ) (hε : 0 < ε)
    (hAnn : ∀ R, NearestNeighborHamiltonian (A R))
    (hBnn : ∀ R, NearestNeighborHamiltonian (B R))
    (hASA : ∀ R, ContinuousLinearMap.adjoint (A R) = A R)
    (hBSA : ∀ R, ContinuousLinearMap.adjoint (B R) = B R)
    (hlocal : ∀ R, EndpointLocalMatrixEq R (A R) (B R))
    (hgap : ∀ R,
      ε ≤
        |endpointExponentialReturnProbability (A R) T -
          endpointExponentialReturnProbability (B R) T|) :
    ¬ ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ R, ‖A R‖ ≤ Λ ∧ ‖B R‖ ≤ Λ := by
  rintro ⟨Λ, hΛ, hbound⟩
  have hupper (R : ℕ) :
      ε ≤ localCausalFactorialBound R Λ T := by
    exact (hgap R).trans
      (localCausalHorizon_probability_bound
        hΛ (hbound R).1 (hbound R).2
        (hAnn R) (hBnn R) (hASA R) (hBSA R) (hlocal R) T)
  have hlim :=
    localCausalFactorialBound_tendsto_zero Λ T
  have heventually :
      ∀ᶠ R : ℕ in Filter.atTop,
        localCausalFactorialBound R Λ T < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨R, hR⟩ := heventually.exists
  exact (not_lt_of_ge (hupper R)) hR

/-- Explicit energy--time threshold for hiding a target-time separation
beyond local radius `R`. -/
def localCausalLinearThreshold (R : ℕ) : ℝ :=
  (2 * R + 3 : ℕ) / (3 * Real.exp 1)

/-- Exact critical centred action scale for a radius-`R` local record. -/
def localCausalCriticalThreshold (R : ℕ) : ℝ :=
  (2 * R + 3 : ℕ) / Real.exp 1

/--
**Linear energy--time necessity.**

If two finite self-adjoint nearest-neighbour systems retain a fixed nonzero
target-time return-probability separation while their exactly common local
radius tends to infinity, then eventually every common per-stage norm bound
must satisfy

`|T| * Λ R > (2R+3) / (3 exp(1))`.

Thus persistent hidden futures require energy times time to grow at least
linearly with hidden distance; mere norm divergence is not enough.
-/
theorem persistentCofinalSeparation_forces_linear_energyTime
    (n : ℕ → ℕ)
    (A B : ∀ R : ℕ, ClockSpace (n R) →L[ℂ] ClockSpace (n R))
    (Λ : ℕ → ℝ)
    (T ε : ℝ) (hε : 0 < ε)
    (hΛ : ∀ R, 0 ≤ Λ R)
    (hA : ∀ R, ‖A R‖ ≤ Λ R)
    (hB : ∀ R, ‖B R‖ ≤ Λ R)
    (hAnn : ∀ R, NearestNeighborHamiltonian (A R))
    (hBnn : ∀ R, NearestNeighborHamiltonian (B R))
    (hASA : ∀ R, ContinuousLinearMap.adjoint (A R) = A R)
    (hBSA : ∀ R, ContinuousLinearMap.adjoint (B R) = B R)
    (hlocal : ∀ R, EndpointLocalMatrixEq R (A R) (B R))
    (hgap : ∀ R,
      ε ≤
        |endpointExponentialReturnProbability (A R) T -
          endpointExponentialReturnProbability (B R) T|) :
    ∀ᶠ R : ℕ in Filter.atTop,
      localCausalLinearThreshold R < |T| * Λ R := by
  have hindex :
      Filter.Tendsto (fun R : ℕ => 2 * R + 3)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with R hR
    omega
  have hgeo :
      Filter.Tendsto
        (fun R : ℕ =>
          4 * (Real.exp 1 / 3) ^ (2 * R + 3))
        Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : (0 : ℝ) ≤ Real.exp 1 / 3)
          (by
            rw [div_lt_one (by norm_num : (0 : ℝ) < 3)]
            exact Real.exp_one_lt_three)).comp hindex).const_mul 4
  have heventually :
      ∀ᶠ R : ℕ in Filter.atTop,
        4 * (Real.exp 1 / 3) ^ (2 * R + 3) < ε :=
    (tendsto_order.1 hgeo).2 ε hε
  filter_upwards [heventually] with R hsmall
  by_contra hnot
  have hx :
      |T| * Λ R ≤ localCausalLinearThreshold R :=
    le_of_not_gt hnot
  have htail :
      localCausalFactorialBound R (Λ R) T ≤
        4 * (Real.exp 1 / 3) ^ (2 * R + 3) := by
    unfold localCausalFactorialBound
    unfold localCausalLinearThreshold at hx
    exact factorialTail_linear_bound_exp_three (2 * R + 3) (by omega)
      (|T| * Λ R) (mul_nonneg (abs_nonneg T) (hΛ R)) hx
  have hcausal :
      |endpointExponentialReturnProbability (A R) T -
          endpointExponentialReturnProbability (B R) T| ≤
        localCausalFactorialBound R (Λ R) T := by
    exact localCausalHorizon_probability_bound
      (hΛ R) (hA R) (hB R)
      (hAnn R) (hBnn R) (hASA R) (hBSA R) (hlocal R) T
  exact (not_lt_of_ge ((hgap R).trans (hcausal.trans htail))) hsmall

/--
**Gauge-invariant linear energy--time necessity.**

The common energy origin may vary with radius.  Persistent hidden return
separation still forces the common centered norm times time to grow at least
linearly.
-/
theorem persistentCofinalSeparation_forces_linear_centeredEnergyTime
    (n : ℕ → ℕ)
    (A B : ∀ R : ℕ, ClockSpace (n R) →L[ℂ] ClockSpace (n R))
    (Λ c : ℕ → ℝ)
    (T ε : ℝ) (hε : 0 < ε)
    (hΛ : ∀ R, 0 ≤ Λ R)
    (hA : ∀ R, ‖energyGaugeShift (c R) (A R)‖ ≤ Λ R)
    (hB : ∀ R, ‖energyGaugeShift (c R) (B R)‖ ≤ Λ R)
    (hAnn : ∀ R, NearestNeighborHamiltonian (A R))
    (hBnn : ∀ R, NearestNeighborHamiltonian (B R))
    (hASA : ∀ R, ContinuousLinearMap.adjoint (A R) = A R)
    (hBSA : ∀ R, ContinuousLinearMap.adjoint (B R) = B R)
    (hlocal : ∀ R, EndpointLocalMatrixEq R (A R) (B R))
    (hgap : ∀ R,
      ε ≤
        |endpointExponentialReturnProbability (A R) T -
          endpointExponentialReturnProbability (B R) T|) :
    ∀ᶠ R : ℕ in Filter.atTop,
      localCausalLinearThreshold R < |T| * Λ R := by
  have hindex :
      Filter.Tendsto (fun R : ℕ => 2 * R + 3)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with R hR
    omega
  have hgeo :
      Filter.Tendsto
        (fun R : ℕ =>
          4 * (Real.exp 1 / 3) ^ (2 * R + 3))
        Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (by positivity : (0 : ℝ) ≤ Real.exp 1 / 3)
          (by
            rw [div_lt_one (by norm_num : (0 : ℝ) < 3)]
            exact Real.exp_one_lt_three)).comp hindex).const_mul 4
  have heventually :
      ∀ᶠ R : ℕ in Filter.atTop,
        4 * (Real.exp 1 / 3) ^ (2 * R + 3) < ε :=
    (tendsto_order.1 hgeo).2 ε hε
  filter_upwards [heventually] with R hsmall
  by_contra hnot
  have hx :
      |T| * Λ R ≤ localCausalLinearThreshold R :=
    le_of_not_gt hnot
  have htail :
      localCausalFactorialBound R (Λ R) T ≤
        4 * (Real.exp 1 / 3) ^ (2 * R + 3) := by
    unfold localCausalFactorialBound
    unfold localCausalLinearThreshold at hx
    exact factorialTail_linear_bound_exp_three (2 * R + 3) (by omega)
      (|T| * Λ R) (mul_nonneg (abs_nonneg T) (hΛ R)) hx
  have hcausal :
      |endpointExponentialReturnProbability (A R) T -
          endpointExponentialReturnProbability (B R) T| ≤
        localCausalFactorialBound R (Λ R) T := by
    exact localCausalHorizon_probability_bound_gauge
      (hΛ R) (hA R) (hB R)
      (hAnn R) (hBnn R) (hASA R) (hBSA R) (hlocal R) T
  exact (not_lt_of_ge ((hgap R).trans (hcausal.trans htail))) hsmall

/--
**Critical gauge-invariant energy--distance necessity.**

At the boundary `|T| Λ R = (2R+3)/exp(1)`, the universal probability
discrepancy decays as the inverse square root of the round-trip order.
Therefore any fixed persistent gap eventually forces strict exceedance of
that critical action.
-/
theorem persistentCofinalSeparation_forces_critical_centeredEnergyTime
    (n : ℕ → ℕ)
    (A B : ∀ R : ℕ, ClockSpace (n R) →L[ℂ] ClockSpace (n R))
    (Λ c : ℕ → ℝ)
    (T ε : ℝ) (hε : 0 < ε)
    (hΛ : ∀ R, 0 ≤ Λ R)
    (hA : ∀ R, ‖energyGaugeShift (c R) (A R)‖ ≤ Λ R)
    (hB : ∀ R, ‖energyGaugeShift (c R) (B R)‖ ≤ Λ R)
    (hAnn : ∀ R, NearestNeighborHamiltonian (A R))
    (hBnn : ∀ R, NearestNeighborHamiltonian (B R))
    (hASA : ∀ R, ContinuousLinearMap.adjoint (A R) = A R)
    (hBSA : ∀ R, ContinuousLinearMap.adjoint (B R) = B R)
    (hlocal : ∀ R, EndpointLocalMatrixEq R (A R) (B R))
    (hgap : ∀ R,
      ε ≤
        |endpointExponentialReturnProbability (A R) T -
          endpointExponentialReturnProbability (B R) T|) :
    ∀ᶠ R : ℕ in Filter.atTop,
      localCausalCriticalThreshold R < |T| * Λ R := by
  have hindex :
      Filter.Tendsto (fun R : ℕ => 2 * R + 3)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with R hR
    omega
  have hindexReal :
      Filter.Tendsto
        (fun R : ℕ => (((2 * R + 3 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hindex
  have hinside :
      Filter.Tendsto
        (fun R : ℕ =>
          2 * Real.pi * (((2 * R + 3 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hindexReal
  have hsqrt :
      Filter.Tendsto
        (fun R : ℕ =>
          Real.sqrt
            (2 * Real.pi * (((2 * R + 3 : ℕ) : ℝ))))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hinside
  have hcriticalBound :
      Filter.Tendsto
        (fun R : ℕ =>
          8 / Real.sqrt
            (2 * Real.pi * (((2 * R + 3 : ℕ) : ℝ))))
        Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hsqrt
  have heventually :
      ∀ᶠ R : ℕ in Filter.atTop,
        8 / Real.sqrt
            (2 * Real.pi * (((2 * R + 3 : ℕ) : ℝ))) < ε :=
    (tendsto_order.1 hcriticalBound).2 ε hε
  filter_upwards [heventually] with R hsmall
  by_contra hnot
  have hthreshold :
      |T| * Λ R ≤
        (((2 * R + 3 : ℕ) : ℝ)) / Real.exp 1 := by
    exact le_of_not_gt (by
      simpa [localCausalCriticalThreshold] using hnot)
  have hcausal :=
    localCausalHorizon_probability_bound_critical_gauge
      (hΛ R) (hA R) (hB R)
      (hAnn R) (hBnn R) (hASA R) (hBSA R)
      (hlocal R) T hthreshold
  exact (not_lt_of_ge ((hgap R).trans hcausal)) hsmall

/-- Target-time probabilities compatible with one finite endpoint-local
Hamiltonian record and one uniformly accurate pre-target return record.
All candidate models are automatically unitarily intertwined with the same
diagonal Hamiltonian, hence have one complete spectrum with multiplicity. -/
def localCompatibleFutureSet
    (R : ℕ) (T H δ : ℝ) (q : ℕ)
    (baseline : FixedEndpointPathModel T (endpointN q) 0) :
    Set ℝ :=
  {p | ∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ M : FixedEndpointPathModel T (endpointN q) θ,
      NearestNeighborHamiltonian M.hamiltonian ∧
      ContinuousLinearMap.adjoint M.hamiltonian = M.hamiltonian ∧
      (∀ x : ClockSpace (endpointN q),
        M.unitary (M.hamiltonian x) =
          scaledClockHamiltonian T (endpointN q) (M.unitary x)) ∧
      EndpointLocalMatrixEq R M.hamiltonian baseline.hamiltonian ∧
      (∀ t : ℝ, |t| ≤ H →
        |M.returnProbability t -
          baseline.returnProbability t| < δ) ∧
      M.returnProbability T = p}

/--
**Complete local future-set law.**

For every finite observed radius, every strict pre-target time window and
every positive tolerance, one finite isospectral nearest-neighbour record
has compatible target-time return set exactly equal to the whole physical
interval `[0,1]`.
-/
theorem exists_localCompatibleFutureSet_eq_Icc
    (R : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ,
      ∃ _horder : 2 * R + 2 < endpointN q,
      ∃ baseline : FixedEndpointPathModel T (endpointN q) 0,
        NearestNeighborHamiltonian baseline.hamiltonian ∧
        ContinuousLinearMap.adjoint baseline.hamiltonian =
          baseline.hamiltonian ∧
        localCompatibleFutureSet R T H δ q baseline =
          Set.Icc (0 : ℝ) 1 := by
  obtain ⟨q, horder, hsize, baseline, hbaselineNN,
      hbaselineSA, hall⟩ :=
    localHorizon_every_future_probability
      R T H hT hH0 hHT hδ
  refine ⟨q, horder, baseline, hbaselineNN, hbaselineSA, ?_⟩
  ext p
  constructor
  · intro hp
    rcases hp with
      ⟨θ, hθ, M, _hMNN, _hMSA, _hintertwines,
        _hlocal, _hwindow, htarget⟩
    have hn : 0 < endpointN q := by simp [endpointN]
    have hpEq : p = θ ^ 2 := by
      rw [← htarget, M.returnProbability_eq hT hθ.1 hθ.2,
        scaledInterpolatedProbability_target hT hn hθ.1]
    constructor
    · rw [hpEq]
      positivity
    · rw [hpEq]
      nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2)]
  · intro hp
    obtain ⟨M, hMNN, hMSA, hintertwines,
        hprefix, hwindow, htarget⟩ := hall p hp
    have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
    have hθ1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
    refine ⟨Real.sqrt p, ⟨hθ0, hθ1⟩, M,
      hMNN, hMSA, hintertwines, ?_, hwindow, htarget⟩
    exact endpointLocalMatrixEq_of_prefix
      hsize hMNN hbaselineNN hprefix

end RHTower.ParityForecast
