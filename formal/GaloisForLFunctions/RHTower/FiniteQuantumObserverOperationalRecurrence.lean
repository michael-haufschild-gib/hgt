import GaloisForLFunctions.RHTower.FiniteQuantumObserverCoherenceLaw

/-!
# Operational consequences of observer recurrence

The quadratic observer distance controls every Hilbert--Schmidt-normalized
linear probe.  For self-adjoint probes this is the ordinary expectation
functional, because the Hilbert--Schmidt pairing equals a matrix trace.

The same estimate is stable under two independently calibrated matrix errors:
their Hilbert--Schmidt radii enter additively.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Squared Hilbert--Schmidt energy of a finite complex matrix. -/
def finiteMatrixHSEnergy {d : ℕ} (A : Fin d → Fin d → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- Hilbert--Schmidt linear probe `⟨sigma,A⟩`. -/
def finiteMatrixHSFunctional {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ) : ℂ :=
  ∑ i, ∑ j, star (sigma i j) * A i j

theorem finiteMatrixHSEnergy_nonneg {d : ℕ}
    (A : Fin d → Fin d → ℂ) :
    0 ≤ finiteMatrixHSEnergy A := by
  unfold finiteMatrixHSEnergy
  positivity

/-- Finite Hilbert--Schmidt Cauchy--Schwarz, in squared form. -/
theorem finiteMatrixHSFunctional_sq_le {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ) :
    ‖finiteMatrixHSFunctional sigma A‖ ^ 2 ≤
      finiteMatrixHSEnergy sigma * finiteMatrixHSEnergy A := by
  let s : Finset (Fin d × Fin d) := Finset.univ
  let f : Fin d × Fin d → ℝ := fun x => ‖sigma x.1 x.2‖
  let g : Fin d × Fin d → ℝ := fun x => ‖A x.1 x.2‖
  have hnorm :
      ‖finiteMatrixHSFunctional sigma A‖ ≤ ∑ x ∈ s, f x * g x := by
    calc
      ‖finiteMatrixHSFunctional sigma A‖
          ≤ ∑ i, ∑ j, ‖star (sigma i j) * A i j‖ := by
            unfold finiteMatrixHSFunctional
            exact le_trans (norm_sum_le _ _) <|
              Finset.sum_le_sum fun i _hi => norm_sum_le _ _
      _ = ∑ x ∈ s, f x * g x := by
            simpa only [s, f, g, norm_mul, norm_star,
              Finset.univ_product_univ] using
              (Finset.sum_product'
                (Finset.univ : Finset (Fin d))
                (Finset.univ : Finset (Fin d))
                (fun i j => ‖sigma i j‖ * ‖A i j‖)).symm
  have hcs :
      (∑ x ∈ s, f x * g x) ^ 2 ≤
        (∑ x ∈ s, f x ^ 2) * ∑ x ∈ s, g x ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hsigma :
      ∑ x ∈ s, f x ^ 2 = finiteMatrixHSEnergy sigma := by
    simpa only [s, f, Finset.univ_product_univ,
      finiteMatrixHSEnergy] using
      (Finset.sum_product'
        (Finset.univ : Finset (Fin d))
        (Finset.univ : Finset (Fin d))
        (fun i j => ‖sigma i j‖ ^ 2))
  have hA :
      ∑ x ∈ s, g x ^ 2 = finiteMatrixHSEnergy A := by
    simpa only [s, g, Finset.univ_product_univ,
      finiteMatrixHSEnergy] using
      (Finset.sum_product'
        (Finset.univ : Finset (Fin d))
        (Finset.univ : Finset (Fin d))
        (fun i j => ‖A i j‖ ^ 2))
  rw [hsigma, hA] at hcs
  exact le_trans ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm) hcs

theorem finiteMatrixHSFunctional_sq_le_of_normalized {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixHSEnergy sigma ≤ 1) :
    ‖finiteMatrixHSFunctional sigma A‖ ^ 2 ≤ finiteMatrixHSEnergy A := by
  calc
    ‖finiteMatrixHSFunctional sigma A‖ ^ 2 ≤
        finiteMatrixHSEnergy sigma * finiteMatrixHSEnergy A :=
      finiteMatrixHSFunctional_sq_le sigma A
    _ ≤ 1 * finiteMatrixHSEnergy A :=
      mul_le_mul_of_nonneg_right hsigma (finiteMatrixHSEnergy_nonneg A)
    _ = finiteMatrixHSEnergy A := one_mul _

theorem finiteMatrixHSFunctional_norm_le_sqrt {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixHSEnergy sigma ≤ 1) :
    ‖finiteMatrixHSFunctional sigma A‖ ≤
      Real.sqrt (finiteMatrixHSEnergy A) := by
  calc
    ‖finiteMatrixHSFunctional sigma A‖ =
        Real.sqrt (‖finiteMatrixHSFunctional sigma A‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (finiteMatrixHSEnergy A) :=
      Real.sqrt_le_sqrt
        (finiteMatrixHSFunctional_sq_le_of_normalized sigma A hsigma)

theorem finiteMatrixHSFunctional_add_sub {d : ℕ}
    (sigma A E₁ E₀ : Fin d → Fin d → ℂ) :
    finiteMatrixHSFunctional sigma
        (fun i j => A i j + E₁ i j - E₀ i j) =
      finiteMatrixHSFunctional sigma A +
        finiteMatrixHSFunctional sigma E₁ -
        finiteMatrixHSFunctional sigma E₀ := by
  simp only [finiteMatrixHSFunctional, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem finiteMatrixHSFunctional_norm_le_of_energy_le_sq {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ) (ν : ℝ)
    (hsigma : finiteMatrixHSEnergy sigma ≤ 1)
    (hν : 0 ≤ ν) (hA : finiteMatrixHSEnergy A ≤ ν ^ 2) :
    ‖finiteMatrixHSFunctional sigma A‖ ≤ ν := by
  calc
    ‖finiteMatrixHSFunctional sigma A‖ ≤
        Real.sqrt (finiteMatrixHSEnergy A) :=
      finiteMatrixHSFunctional_norm_le_sqrt sigma A hsigma
    _ ≤ Real.sqrt (ν ^ 2) := Real.sqrt_le_sqrt hA
    _ = ν := Real.sqrt_sq hν

/-- For a self-adjoint probe, the Hilbert--Schmidt functional is the
ordinary trace pairing. -/
theorem finiteMatrixHSFunctional_eq_trace_mul_of_selfAdjoint {d : ℕ}
    (sigma A : Matrix (Fin d) (Fin d) ℂ)
    (hself : ∀ i j, star (sigma i j) = sigma j i) :
    finiteMatrixHSFunctional sigma A = (sigma * A).trace := by
  change (∑ i, ∑ j, star (sigma i j) * A i j) =
    ∑ i, ∑ j, sigma i j * A j i
  simp_rw [hself]
  rw [Finset.sum_comm]

/-- Entrywise displacement of one observer under a diagonal phase packet. -/
def finiteQuantumObserverDisplacement
    {d : ℕ} {J : Type*}
    (z : Fin d → ℂ) (block : J → Fin d → Fin d → ℂ)
    (a : J) : Fin d → Fin d → ℂ :=
  fun i j => finiteQuantumObserverPhase z i j * block a i j - block a i j

theorem finiteMatrixHSEnergy_quantumObserverDisplacement
    {d : ℕ} {J : Type*}
    (z : Fin d → ℂ) (block : J → Fin d → Fin d → ℂ) (a : J) :
    finiteMatrixHSEnergy
        (finiteQuantumObserverDisplacement z block a) =
      finiteSpectralBlockDistanceSq
        (finiteQuantumObserverPhase z) (block a) := by
  unfold finiteMatrixHSEnergy finiteQuantumObserverDisplacement
    finiteSpectralBlockDistanceSq
  simp only [smul_eq_mul]

/-- Every normalized linear probe is controlled by the complete weighted
observer distance. -/
theorem finiteQuantumObserver_operational_sq_le
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (sigma : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixHSEnergy sigma ≤ 1) :
    lam a *
        ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2 ≤
      finiteQuantumObserverDistanceSq lam z block := by
  have hprobe :
      ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2 ≤
        finiteMatrixHSEnergy
          (finiteQuantumObserverDisplacement z block a) :=
    finiteMatrixHSFunctional_sq_le_of_normalized _ _ hsigma
  calc
    lam a *
        ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2
        ≤ lam a *
          finiteMatrixHSEnergy
            (finiteQuantumObserverDisplacement z block a) :=
      mul_le_mul_of_nonneg_left hprobe (hlam a)
    _ ≤ ∑ b, lam b *
          finiteMatrixHSEnergy
            (finiteQuantumObserverDisplacement z block b) := by
      exact Finset.single_le_sum
        (fun b _hb => mul_nonneg (hlam b)
          (finiteMatrixHSEnergy_nonneg _))
        (Finset.mem_univ a)
    _ = finiteQuantumObserverDistanceSq lam z block := by
      unfold finiteQuantumObserverDistanceSq finiteObserverBlockDistanceSq
      simp_rw [finiteMatrixHSEnergy_quantumObserverDisplacement]

/-- Unsquared operational form for a positively weighted observer. -/
theorem finiteQuantumObserver_operational_norm_le
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (ha : 0 < lam a)
    (sigma : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixHSEnergy sigma ≤ 1) :
    ‖finiteMatrixHSFunctional sigma
        (finiteQuantumObserverDisplacement z block a)‖ ≤
      Real.sqrt
        (finiteQuantumObserverDistanceSq lam z block / lam a) := by
  have hsq :
      ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2 ≤
        finiteQuantumObserverDistanceSq lam z block / lam a := by
    rw [le_div_iff₀ ha]
    simpa only [mul_comm] using
      finiteQuantumObserver_operational_sq_le
        lam z block hlam a sigma hsigma
  calc
    ‖finiteMatrixHSFunctional sigma
        (finiteQuantumObserverDisplacement z block a)‖ =
        Real.sqrt
          (‖finiteMatrixHSFunctional sigma
            (finiteQuantumObserverDisplacement z block a)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt
        (finiteQuantumObserverDistanceSq lam z block / lam a) :=
      Real.sqrt_le_sqrt hsq

/-- Additive calibration robustness for two independent matrix errors. -/
theorem finiteQuantumObserver_operational_noise_le
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (ha : 0 < lam a)
    (sigma E₁ E₀ : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixHSEnergy sigma ≤ 1)
    (ν₁ ν₀ : ℝ) (hν₁ : 0 ≤ ν₁) (hν₀ : 0 ≤ ν₀)
    (hE₁ : finiteMatrixHSEnergy E₁ ≤ ν₁ ^ 2)
    (hE₀ : finiteMatrixHSEnergy E₀ ≤ ν₀ ^ 2) :
    ‖finiteMatrixHSFunctional sigma
        (fun i j =>
          finiteQuantumObserverDisplacement z block a i j +
            E₁ i j - E₀ i j)‖ ≤
      Real.sqrt
          (finiteQuantumObserverDistanceSq lam z block / lam a) +
        ν₁ + ν₀ := by
  rw [finiteMatrixHSFunctional_add_sub]
  calc
    ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a) +
        finiteMatrixHSFunctional sigma E₁ -
        finiteMatrixHSFunctional sigma E₀‖
        ≤ ‖finiteMatrixHSFunctional sigma
            (finiteQuantumObserverDisplacement z block a)‖ +
          ‖finiteMatrixHSFunctional sigma E₁‖ +
          ‖finiteMatrixHSFunctional sigma E₀‖ := by
      exact le_trans (norm_sub_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Real.sqrt
          (finiteQuantumObserverDistanceSq lam z block / lam a) +
        ν₁ + ν₀ := by
      gcongr
      · exact finiteQuantumObserver_operational_norm_le
          lam z block hlam a ha sigma hsigma
      · exact finiteMatrixHSFunctional_norm_le_of_energy_le_sq
          sigma E₁ ν₁ hsigma hν₁ hE₁
      · exact finiteMatrixHSFunctional_norm_le_of_energy_le_sq
          sigma E₀ ν₀ hsigma hν₀ hE₀

/-- A finite matrix is an operator contraction when its action does not
increase the Euclidean energy of any vector. This is the coordinate form of
operator norm at most one. -/
def finiteMatrixOperatorContraction {d : ℕ}
    (sigma : Fin d → Fin d → ℂ) : Prop :=
  ∀ x : Fin d → ℂ,
    (∑ i, ‖∑ j, sigma i j * x j‖ ^ 2) ≤ ∑ j, ‖x j‖ ^ 2

/-- Every operator contraction has Hilbert--Schmidt energy at most the matrix
dimension. -/
theorem finiteMatrixHSEnergy_le_dimension_of_operatorContraction {d : ℕ}
    (sigma : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma) :
    finiteMatrixHSEnergy sigma ≤ d := by
  classical
  have hcol : ∀ j : Fin d, (∑ i, ‖sigma i j‖ ^ 2) ≤ 1 := by
    intro j
    have h := hsigma (fun k => if k = j then 1 else 0)
    have hrhs :
        (∑ k : Fin d, ‖if k = j then (1 : ℂ) else 0‖ ^ 2) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _hb hbj
        simp [hbj]
      · simp
    rw [hrhs] at h
    simpa using h
  unfold finiteMatrixHSEnergy
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, ‖sigma i j‖ ^ 2) ≤ ∑ _j : Fin d, (1 : ℝ) :=
      Finset.sum_le_sum fun j _hj => hcol j
    _ = d := by simp

/-- Identity matrix, used to expose sharpness of the operator-to-Hilbert--
Schmidt conversion. -/
def finiteIdentityMatrix {d : ℕ} : Fin d → Fin d → ℂ :=
  fun i j => if i = j then 1 else 0

theorem finiteIdentityMatrix_operatorContraction {d : ℕ} :
    finiteMatrixOperatorContraction
      (finiteIdentityMatrix (d := d)) := by
  intro x
  simp [finiteIdentityMatrix]

theorem finiteMatrixHSEnergy_identity {d : ℕ} :
    finiteMatrixHSEnergy (finiteIdentityMatrix (d := d)) = d := by
  classical
  have hrow : ∀ i : Fin d,
      (∑ j, ‖finiteIdentityMatrix i j‖ ^ 2) = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [finiteIdentityMatrix]
    · intro b _hb hbi
      simp [finiteIdentityMatrix, Ne.symm hbi]
    · simp
  unfold finiteMatrixHSEnergy
  calc
    (∑ i, ∑ j, ‖finiteIdentityMatrix i j‖ ^ 2) =
        ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hrow i
    _ = d := by simp

theorem finiteMatrixHSFunctional_identity {d : ℕ} :
    finiteMatrixHSFunctional
      (finiteIdentityMatrix (d := d)) finiteIdentityMatrix = d := by
  classical
  simp [finiteMatrixHSFunctional, finiteIdentityMatrix]

/-- The factor `d` in the squared operator-normalized matrix-pairing bound is
attained by the identity pairing. -/
theorem finiteMatrix_operatorContraction_dimension_factor_attained {d : ℕ} :
    ‖finiteMatrixHSFunctional
        (finiteIdentityMatrix (d := d)) finiteIdentityMatrix‖ ^ 2 =
      d * finiteMatrixHSEnergy (finiteIdentityMatrix (d := d)) := by
  rw [finiteMatrixHSFunctional_identity, finiteMatrixHSEnergy_identity]
  simp [sq]

/-- Operator-normalized probe transfer. The factor `d` in squared response is
the unavoidable conversion from operator norm to Hilbert--Schmidt norm. -/
theorem finiteMatrixHSFunctional_sq_le_of_operatorContraction {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma) :
    ‖finiteMatrixHSFunctional sigma A‖ ^ 2 ≤
      d * finiteMatrixHSEnergy A := by
  calc
    ‖finiteMatrixHSFunctional sigma A‖ ^ 2 ≤
        finiteMatrixHSEnergy sigma * finiteMatrixHSEnergy A :=
      finiteMatrixHSFunctional_sq_le sigma A
    _ ≤ d * finiteMatrixHSEnergy A :=
      mul_le_mul_of_nonneg_right
        (finiteMatrixHSEnergy_le_dimension_of_operatorContraction sigma hsigma)
        (finiteMatrixHSEnergy_nonneg A)

theorem finiteMatrixHSFunctional_norm_le_sqrt_of_operatorContraction {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma) :
    ‖finiteMatrixHSFunctional sigma A‖ ≤
      Real.sqrt (d * finiteMatrixHSEnergy A) := by
  calc
    ‖finiteMatrixHSFunctional sigma A‖ =
        Real.sqrt (‖finiteMatrixHSFunctional sigma A‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (d * finiteMatrixHSEnergy A) :=
      Real.sqrt_le_sqrt
        (finiteMatrixHSFunctional_sq_le_of_operatorContraction
          sigma A hsigma)

theorem finiteMatrixHSFunctional_norm_le_of_operatorContraction_energy_le_sq
    {d : ℕ}
    (sigma A : Fin d → Fin d → ℂ) (ν : ℝ)
    (hsigma : finiteMatrixOperatorContraction sigma)
    (hA : finiteMatrixHSEnergy A ≤ ν ^ 2) :
    ‖finiteMatrixHSFunctional sigma A‖ ≤
      Real.sqrt (d * ν ^ 2) := by
  calc
    ‖finiteMatrixHSFunctional sigma A‖ ≤
        Real.sqrt (d * finiteMatrixHSEnergy A) :=
      finiteMatrixHSFunctional_norm_le_sqrt_of_operatorContraction
        sigma A hsigma
    _ ≤ Real.sqrt (d * ν ^ 2) := by
      exact Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg d))

theorem sqrt_natCast_mul_sq (d : ℕ) (ν : ℝ) (hν : 0 ≤ ν) :
    Real.sqrt (d * ν ^ 2) = Real.sqrt d * ν := by
  rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hν]

/-- Every operator-normalized probe is controlled by the complete observer
distance, with the explicit dimension conversion. -/
theorem finiteQuantumObserver_operator_operational_sq_le
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (sigma : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma) :
    lam a *
        ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2 ≤
      d * finiteQuantumObserverDistanceSq lam z block := by
  have hprobe :
      ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2 ≤
        d * finiteMatrixHSEnergy
          (finiteQuantumObserverDisplacement z block a) :=
    finiteMatrixHSFunctional_sq_le_of_operatorContraction _ _ hsigma
  calc
    lam a *
        ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2
        ≤ lam a * (d *
          finiteMatrixHSEnergy
            (finiteQuantumObserverDisplacement z block a)) :=
      mul_le_mul_of_nonneg_left hprobe (hlam a)
    _ = d * (lam a *
          finiteMatrixHSEnergy
            (finiteQuantumObserverDisplacement z block a)) := by ring
    _ ≤ d * ∑ b, lam b *
          finiteMatrixHSEnergy
            (finiteQuantumObserverDisplacement z block b) := by
      gcongr
      exact Finset.single_le_sum
        (fun b _hb => mul_nonneg (hlam b)
          (finiteMatrixHSEnergy_nonneg _))
        (Finset.mem_univ a)
    _ = d * finiteQuantumObserverDistanceSq lam z block := by
      unfold finiteQuantumObserverDistanceSq finiteObserverBlockDistanceSq
      simp_rw [finiteMatrixHSEnergy_quantumObserverDisplacement]

/-- Unsquared operator-normalized probe transfer. -/
theorem finiteQuantumObserver_operator_operational_norm_le
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (ha : 0 < lam a)
    (sigma : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma) :
    ‖finiteMatrixHSFunctional sigma
        (finiteQuantumObserverDisplacement z block a)‖ ≤
      Real.sqrt
        (d * finiteQuantumObserverDistanceSq lam z block / lam a) := by
  have hsq :
      ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a)‖ ^ 2 ≤
        d * finiteQuantumObserverDistanceSq lam z block / lam a := by
    rw [le_div_iff₀ ha]
    simpa only [mul_comm, mul_left_comm] using
      finiteQuantumObserver_operator_operational_sq_le
        lam z block hlam a sigma hsigma
  calc
    ‖finiteMatrixHSFunctional sigma
        (finiteQuantumObserverDisplacement z block a)‖ =
        Real.sqrt
          (‖finiteMatrixHSFunctional sigma
            (finiteQuantumObserverDisplacement z block a)‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt
        (d * finiteQuantumObserverDistanceSq lam z block / lam a) :=
      Real.sqrt_le_sqrt hsq

/-- Operator-normalized probes remain stable under two independently
calibrated Hilbert--Schmidt errors, with the same explicit dimension
conversion. -/
theorem finiteQuantumObserver_operator_operational_noise_le
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (ha : 0 < lam a)
    (sigma E₁ E₀ : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma)
    (ν₁ ν₀ : ℝ)
    (hE₁ : finiteMatrixHSEnergy E₁ ≤ ν₁ ^ 2)
    (hE₀ : finiteMatrixHSEnergy E₀ ≤ ν₀ ^ 2) :
    ‖finiteMatrixHSFunctional sigma
        (fun i j =>
          finiteQuantumObserverDisplacement z block a i j +
            E₁ i j - E₀ i j)‖ ≤
      Real.sqrt
          (d * finiteQuantumObserverDistanceSq lam z block / lam a) +
        Real.sqrt (d * ν₁ ^ 2) + Real.sqrt (d * ν₀ ^ 2) := by
  rw [finiteMatrixHSFunctional_add_sub]
  calc
    ‖finiteMatrixHSFunctional sigma
          (finiteQuantumObserverDisplacement z block a) +
        finiteMatrixHSFunctional sigma E₁ -
        finiteMatrixHSFunctional sigma E₀‖
        ≤ ‖finiteMatrixHSFunctional sigma
            (finiteQuantumObserverDisplacement z block a)‖ +
          ‖finiteMatrixHSFunctional sigma E₁‖ +
          ‖finiteMatrixHSFunctional sigma E₀‖ := by
      exact le_trans (norm_sub_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Real.sqrt
          (d * finiteQuantumObserverDistanceSq lam z block / lam a) +
        Real.sqrt (d * ν₁ ^ 2) + Real.sqrt (d * ν₀ ^ 2) := by
      gcongr
      · exact finiteQuantumObserver_operator_operational_norm_le
          lam z block hlam a ha sigma hsigma
      · exact
          finiteMatrixHSFunctional_norm_le_of_operatorContraction_energy_le_sq
            sigma E₁ ν₁ hsigma hE₁
      · exact
          finiteMatrixHSFunctional_norm_le_of_operatorContraction_energy_le_sq
            sigma E₀ ν₀ hsigma hE₀

/-- Calibration form with nonnegative radii displayed as the sharp
`sqrt d` conversion. -/
theorem finiteQuantumObserver_operator_operational_noise_le_sqrt_dimension
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (z : Fin d → ℂ)
    (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ b, 0 ≤ lam b)
    (a : J) (ha : 0 < lam a)
    (sigma E₁ E₀ : Fin d → Fin d → ℂ)
    (hsigma : finiteMatrixOperatorContraction sigma)
    (ν₁ ν₀ : ℝ) (hν₁ : 0 ≤ ν₁) (hν₀ : 0 ≤ ν₀)
    (hE₁ : finiteMatrixHSEnergy E₁ ≤ ν₁ ^ 2)
    (hE₀ : finiteMatrixHSEnergy E₀ ≤ ν₀ ^ 2) :
    ‖finiteMatrixHSFunctional sigma
        (fun i j =>
          finiteQuantumObserverDisplacement z block a i j +
            E₁ i j - E₀ i j)‖ ≤
      Real.sqrt
          (d * finiteQuantumObserverDistanceSq lam z block / lam a) +
        Real.sqrt d * ν₁ + Real.sqrt d * ν₀ := by
  simpa only [sqrt_natCast_mul_sq d ν₁ hν₁,
    sqrt_natCast_mul_sq d ν₀ hν₀] using
    finiteQuantumObserver_operator_operational_noise_le
      lam z block hlam a ha sigma E₁ E₀ hsigma ν₁ ν₀ hE₁ hE₀

end RHTower
