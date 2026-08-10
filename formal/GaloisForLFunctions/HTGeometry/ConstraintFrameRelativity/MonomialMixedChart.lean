import Mathlib

/-!
# The quadratic-exponent monomial corank-one chart

The source matrix `𝒜_n = [T U e₁ ∣ T² U⁴ e₂ ∣ ⋯ ∣ Tⁿ U^{n²} eₙ ∣ 1]` has all maximal minors
nonzero once `T` and `U` are units, so its column matroid is the uniform matroid `U(n, n+1)`:
dropping the last column gives `∏_j d_j`, and dropping the `k`-th diagonal column gives
`∏_{j ≠ k} d_j`.

Evaluating at `T = ρ e^{i·0}`, `U = e^{iθ}` produces four noncollapsed shadows of one object:

* the Gram matrix `A Aᴴ = diag(ρ², …, ρ^{2n}) + 1 1ᵀ` does not depend on `θ`, and is unchanged by
  any diagonal rephasing of the columns, while the anchored circuit changes sign — the exact
  orientation loss;
* the first logarithmic `U`-prolongation of the maximal minors is the quadratic vector
  `J = (Q, Q - 1, Q - 4, …, Q - n²)`, which is nonconstant and therefore not determined by the
  bare support;
* its class modulo the common projective winding `(1, …, 1)` is nonzero, so the observed phase
  closes while the lifted history does not;
* the least norm of a right inverse is squeezed between `√2 ρ^{-(n-1)}/√(1+ρ²)` and `ρ^{-n}`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset Matrix

/-! ## The maximal minors of the monomial chart -/

variable {R : Type*} [CommRing R]

/-- Dropping the constant column leaves the diagonal minor. -/
theorem det_diagonal_minor {n : ℕ} (d : Fin n → R) :
    (Matrix.diagonal d).det = ∏ j, d j :=
  Matrix.det_diagonal

/-- Dropping the `k`-th diagonal column leaves the complementary product. -/
theorem det_updateCol_one {n : ℕ} (d : Fin n → R) (k : Fin n) :
    (Matrix.updateCol (Matrix.diagonal d) k (fun _ => (1 : R))).det
      = ∏ j ∈ Finset.univ.erase k, d j := by
  classical
  set M : Matrix (Fin n) (Fin n) R :=
    Matrix.updateCol (Matrix.diagonal d) k (fun _ => (1 : R)) with hM
  have hentry : ∀ i j : Fin n,
      M i j = if j = k then 1 else (if i = j then d i else 0) := by
    intro i j
    by_cases hj : j = k
    · subst hj
      simp [hM]
    · simp [hM, hj, Matrix.diagonal_apply]
  rw [Matrix.det_apply']
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · have hprod : ∏ i, M ((1 : Equiv.Perm (Fin n)) i) i
        = ∏ i, (if i = k then (1 : R) else d i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Equiv.Perm.coe_one, id_eq, hentry]
      by_cases hi : i = k <;> simp [hi]
    have hk1 : (if k = k then (1 : R) else d k) = 1 := by simp
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
    rw [hprod, ← Finset.prod_erase_mul Finset.univ (fun i => if i = k then (1 : R) else d i)
      (Finset.mem_univ k), hk1, mul_one]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_neg (Finset.mem_erase.mp hj).1]
  · intro σ _ hσ
    have hex : ∃ i : Fin n, i ≠ k ∧ σ i ≠ i := by
      by_contra hcon
      have hfix : ∀ i : Fin n, i ≠ k → σ i = i := by
        intro i hi
        by_contra hσi
        exact hcon ⟨i, hi, hσi⟩
      have hk : σ k = k := by
        by_contra hkk
        obtain ⟨j, hj⟩ : ∃ j, σ j = k := ⟨σ.symm k, σ.apply_symm_apply k⟩
        have hjk : j ≠ k := by
          intro h
          rw [h] at hj
          exact hkk hj
        rw [hfix j hjk] at hj
        exact hjk hj
      exact hσ (Equiv.ext fun i => by
        by_cases hi : i = k
        · subst hi; simpa using hk
        · simpa using hfix i hi)
    obtain ⟨i, hik, hσi⟩ := hex
    have hzero : ∏ j, M (σ j) j = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hentry]
      simp [hik, fun h : σ i = i => hσi h]
    rw [hzero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (1 : Equiv.Perm (Fin n))) h

/-- **All maximal minors are nonzero.**  The column matroid is uniform. -/
theorem minors_ne_zero {n : ℕ} {d : Fin n → R} [Nontrivial R] [NoZeroDivisors R]
    (hd : ∀ j, d j ≠ 0) :
    (Matrix.diagonal d).det ≠ 0
      ∧ ∀ k : Fin n, (Matrix.updateCol (Matrix.diagonal d) k (fun _ => (1 : R))).det ≠ 0 := by
  classical
  refine ⟨?_, fun k => ?_⟩
  · rw [det_diagonal_minor]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hd j
  · rw [det_updateCol_one]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hd j

/-! ## The evaluated chart, its Gram matrix and orientation loss -/

/-- The evaluated monomial chart `[D ∣ 1]` as an `n × (n+1)` complex matrix. -/
noncomputable def monomialChart (n : ℕ) (ρ θ : ℝ) : Matrix (Fin n) (Fin n ⊕ Unit) ℂ :=
  Matrix.of fun i c =>
    Sum.elim (fun j : Fin n =>
      if i = j then (ρ : ℂ) ^ ((i : ℕ) + 1) * Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I)
      else 0) (fun _ => 1) c

/-- **The Gram matrix is independent of the phase.** -/
theorem gram_monomialChart (n : ℕ) (ρ θ : ℝ) :
    (monomialChart n ρ θ) * (monomialChart n ρ θ)ᴴ
      = Matrix.of fun i j : Fin n =>
        (if i = j then ((ρ : ℂ) ^ (2 * ((i : ℕ) + 1))) else 0) + 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_sum_type, Finset.sum_const, Matrix.conjTranspose_apply,
    monomialChart, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  by_cases hij : i = j
  · subst hij
    have hterm : ∀ l : Fin n,
        (if i = l then (ρ : ℂ) ^ ((i : ℕ) + 1) *
            Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) else 0) *
          star (if i = l then (ρ : ℂ) ^ ((i : ℕ) + 1) *
            Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) else 0)
        = if i = l then ((ρ : ℂ) ^ (2 * ((i : ℕ) + 1))) else 0 := by
      intro l
      by_cases hl : i = l
      · subst hl
        simp only [if_true]
        rw [Complex.star_def, map_mul, ← Complex.exp_conj]
        rw [show (starRingEnd ℂ) ((ρ : ℂ) ^ ((i : ℕ) + 1)) = (ρ : ℂ) ^ ((i : ℕ) + 1) by
          simp]
        rw [show (starRingEnd ℂ) ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I)
            = -((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) by
          simp]
        rw [Complex.exp_neg]
        have hexp : Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) ≠ 0 :=
          Complex.exp_ne_zero _
        field_simp
        ring
      · simp [hl]
    rw [Finset.sum_congr rfl fun l _ => hterm l]
    simp
  · have hterm : ∀ l : Fin n,
        (if i = l then (ρ : ℂ) ^ ((i : ℕ) + 1) *
            Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) else 0) *
          star (if j = l then (ρ : ℂ) ^ ((j : ℕ) + 1) *
            Complex.exp ((((j : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) else 0) = 0 := by
      intro l
      by_cases hl : i = l
      · subst hl
        have : j ≠ i := fun h => hij h.symm
        simp [this]
      · simp [hl]
    rw [Finset.sum_congr rfl fun l _ => hterm l]
    simp [hij]

/-- **Rephasing invariance.**  A diagonal unitary rephasing of the columns leaves the Gram matrix
unchanged. -/
theorem gram_rephase {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) (u : Fin p → ℂ)
    (hu : ∀ c, ‖u c‖ = 1) :
    (A * Matrix.diagonal u) * (A * Matrix.diagonal u)ᴴ = A * Aᴴ := by
  have hpt : ∀ i : Fin p, u i * star (u i) = 1 := by
    intro i
    have h := hu i
    have hsq : Complex.normSq (u i) = 1 := Real.sqrt_eq_one.mp h
    rw [Complex.star_def, Complex.mul_conj, hsq]
    norm_num
  have hS : (Matrix.diagonal u) * (Matrix.diagonal u)ᴴ = (1 : Matrix (Fin p) (Fin p) ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => u i * (star u) i) = fun _ : Fin p => (1 : ℂ) from funext fun i => hpt i]
    exact Matrix.diagonal_one
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc A, hS, Matrix.mul_one]

/-! ## The circuit and its anchored orientation -/

/-- The unique circuit of the chart, normalised to last coordinate one. -/
noncomputable def chartCircuit (n : ℕ) (ρ θ : ℝ) : Fin n ⊕ Unit → ℂ :=
  Sum.elim (fun j : Fin n =>
    -((ρ : ℂ) ^ ((j : ℕ) + 1) *
      Complex.exp ((((j : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I))⁻¹) (fun _ => 1)

/-- **The circuit is annihilated by the chart.** -/
theorem monomialChart_circuit {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    (monomialChart n ρ θ).mulVec (chartCircuit n ρ θ) = 0 := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Fintype.sum_sum_type, monomialChart, chartCircuit, Matrix.of_apply,
    Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Finset.sum_const]
  have hne : ((ρ : ℂ) ^ ((i : ℕ) + 1) *
      Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I)) ≠ 0 := by
    have h1 : (ρ : ℂ) ≠ 0 := by
      simpa using hρ.ne'
    exact mul_ne_zero (pow_ne_zero _ h1) (Complex.exp_ne_zero _)
  have hterm : ∀ l : Fin n,
      (if i = l then (ρ : ℂ) ^ ((i : ℕ) + 1) *
          Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) else 0) *
        (-((ρ : ℂ) ^ ((l : ℕ) + 1) *
          Complex.exp ((((l : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I))⁻¹)
      = if i = l then (-1 : ℂ) else 0 := by
    intro l
    have hρ' : ((ρ : ℂ)) ≠ 0 := by
      simpa using hρ.ne'
    by_cases hl : i = l
    · subst hl
      rw [if_pos rfl, if_pos rfl]
      field_simp
    · simp [hl]
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  simp

/-- **Anchored orientation is not a Gram invariant.**  The anchored circuit coordinate is nonzero,
so rephasing the first column by `-1` — which leaves the Gram matrix fixed — genuinely changes it.
-/
theorem circuit_sign_flip {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    chartCircuit n ρ θ (Sum.inl ⟨0, hn⟩) ≠ - chartCircuit n ρ θ (Sum.inl ⟨0, hn⟩) := by
  have hρ' : ((ρ : ℂ)) ≠ 0 := by
    simpa using hρ.ne'
  have hd : ((ρ : ℂ) ^ (((⟨0, hn⟩ : Fin n) : ℕ) + 1) *
      Complex.exp (((((⟨0, hn⟩ : Fin n) : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hρ') (Complex.exp_ne_zero _)
  have hne : chartCircuit n ρ θ (Sum.inl ⟨0, hn⟩) ≠ 0 := by
    simp only [chartCircuit, Sum.elim_inl, neg_ne_zero]
    exact inv_ne_zero hd
  intro h
  have h2 : (2 : ℂ) * chartCircuit n ρ θ (Sum.inl ⟨0, hn⟩) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h0 | h0
  · norm_num at h0
  · exact hne h0

/-! ## Quantitative aperture inverse loss -/

/-- The distinguished diagonal right inverse of the chart. -/
noncomputable def chartRightInverse (n : ℕ) (ρ θ : ℝ) : Matrix (Fin n ⊕ Unit) (Fin n) ℂ :=
  Matrix.of fun c i =>
    Sum.elim (fun j : Fin n =>
      if j = i then ((ρ : ℂ) ^ ((j : ℕ) + 1) *
        Complex.exp (((((j : ℕ) + 1) ^ 2 * θ : ℝ)) * Complex.I))⁻¹ else 0)
      (fun _ => (0 : ℂ)) c

/-- **The diagonal right inverse.** -/
theorem chart_mul_rightInverse {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    (monomialChart n ρ θ) * (chartRightInverse n ρ θ) = 1 := by
  have hρ' : ((ρ : ℂ)) ≠ 0 := by
    simpa using hρ.ne'
  ext i j
  rw [Matrix.mul_apply]
  simp only [Fintype.sum_sum_type, monomialChart, chartRightInverse, Matrix.of_apply,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const, mul_zero, smul_zero, add_zero]
  have hterm : ∀ l : Fin n,
      (if i = l then (ρ : ℂ) ^ ((i : ℕ) + 1) *
          Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I) else 0) *
        (if l = j then ((ρ : ℂ) ^ ((l : ℕ) + 1) *
          Complex.exp ((((l : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I))⁻¹ else 0)
      = if i = l then (if l = j then (1 : ℂ) else 0) else 0 := by
    intro l
    by_cases hl : i = l
    · subst hl
      by_cases hj : i = j
      · subst hj
        simp only [if_true]
        have hd : ((ρ : ℂ) ^ ((i : ℕ) + 1) *
            Complex.exp ((((i : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I)) ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ hρ') (Complex.exp_ne_zero _)
        field_simp
      · simp [hj]
    · simp [hl]
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- **The distinguished right inverse loses exactly one factor `ρ⁻¹` per aperture step.** -/
theorem sum_normSq_chartRightInverse_le {n : ℕ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (θ : ℝ)
    (y : Fin n → ℂ) :
    ∑ c : Fin n ⊕ Unit, ‖(chartRightInverse n ρ θ).mulVec y c‖ ^ 2
      ≤ ((ρ⁻¹) ^ n) ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
  have hrow : ∀ j : Fin n, (chartRightInverse n ρ θ).mulVec y (Sum.inl j)
      = ((ρ : ℂ) ^ ((j : ℕ) + 1) *
        Complex.exp ((((j : ℕ) + 1) ^ 2 * θ : ℝ) * Complex.I))⁻¹ * y j := by
    intro j
    rw [Matrix.mulVec_apply_eq_sum]
    simp only [chartRightInverse, Matrix.of_apply, Sum.elim_inl]
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hlast : (chartRightInverse n ρ θ).mulVec y (Sum.inr ()) = 0 := by
    rw [Matrix.mulVec_apply_eq_sum]
    simp [chartRightInverse]
  have hsplit : ∑ c : Fin n ⊕ Unit, ‖(chartRightInverse n ρ θ).mulVec y c‖ ^ 2
      = ∑ j : Fin n, ‖(chartRightInverse n ρ θ).mulVec y (Sum.inl j)‖ ^ 2 := by
    rw [Fintype.sum_sum_type]
    simp [hlast]
  rw [hsplit]
  have hbound : ∀ j : Fin n,
      ‖(chartRightInverse n ρ θ).mulVec y (Sum.inl j)‖ ^ 2
        ≤ ((ρ⁻¹) ^ n) ^ 2 * ‖y j‖ ^ 2 := by
    intro j
    rw [hrow j, norm_mul, mul_pow, norm_inv, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hnorm : ‖(ρ : ℂ) ^ ((j : ℕ) + 1)‖ = ρ ^ ((j : ℕ) + 1) := by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    rw [hnorm]
    have hle : (ρ ^ ((j : ℕ) + 1))⁻¹ ≤ (ρ⁻¹) ^ n := by
      rw [← inv_pow]
      refine pow_le_pow_right₀ ?_ ?_
      · rw [one_le_inv_iff₀]
        exact ⟨hρ0, hρ1⟩
      · exact j.isLt
    have hpos : (0 : ℝ) < (ρ ^ ((j : ℕ) + 1))⁻¹ := by positivity
    have hsq : ((ρ ^ ((j : ℕ) + 1))⁻¹) ^ 2 ≤ ((ρ⁻¹) ^ n) ^ 2 := by
      nlinarith [hpos, hle]
    nlinarith [sq_nonneg ‖y j‖, hsq, norm_nonneg (y j)]
  calc ∑ j : Fin n, ‖(chartRightInverse n ρ θ).mulVec y (Sum.inl j)‖ ^ 2
      ≤ ∑ j : Fin n, ((ρ⁻¹) ^ n) ^ 2 * ‖y j‖ ^ 2 := Finset.sum_le_sum fun j _ => hbound j
    _ = ((ρ⁻¹) ^ n) ^ 2 * ∑ i, ‖y i‖ ^ 2 := by rw [Finset.mul_sum]

/-! ## The Rayleigh witness for the inverse lower bound -/

/-- The unit vector orthogonal to the constant column realising the least Gram eigenvalue bound. -/
noncomputable def rayleighWitness (n : ℕ) : Fin n → ℂ := fun i =>
  (if (i : ℕ) = n - 2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)
    + (if (i : ℕ) = n - 1 then -((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

theorem rayleighWitness_apply {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    rayleighWitness n i
      = if (i : ℕ) = n - 2 then ((1 / Real.sqrt 2 : ℝ) : ℂ)
        else if (i : ℕ) = n - 1 then -((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  rw [rayleighWitness]
  by_cases h1 : (i : ℕ) = n - 2
  · have h2 : (i : ℕ) ≠ n - 1 := by omega
    rw [if_pos h1, if_neg h2, add_zero, if_pos h1]
  · by_cases h2 : (i : ℕ) = n - 1
    · rw [if_neg h1, if_pos h2, zero_add, if_neg h1]
    · rw [if_neg h1, if_neg h2, add_zero, if_neg h1]

/-- **The witness is orthogonal to the constant column.** -/
theorem sum_rayleighWitness {n : ℕ} (hn : 2 ≤ n) : ∑ i, rayleighWitness n i = 0 := by
  have ha : (n - 2 : ℕ) < n := by omega
  have hb : (n - 1 : ℕ) < n := by omega
  simp only [rayleighWitness]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, (if (i : ℕ) = n - 2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)
      = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single (⟨n - 2, ha⟩ : Fin n)]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ n - 2 := fun h => hj (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h2 : ∑ i : Fin n, (if (i : ℕ) = n - 1 then -((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)
      = -((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single (⟨n - 1, hb⟩ : Fin n)]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1, h2, add_neg_cancel]

/-- **The witness is a unit vector.** -/
theorem sum_normSq_rayleighWitness {n : ℕ} (hn : 2 ≤ n) :
    ∑ i, ‖rayleighWitness n i‖ ^ 2 = 1 := by
  have ha : (n - 2 : ℕ) < n := by omega
  have hb : (n - 1 : ℕ) < n := by omega
  have hab : (⟨n - 2, ha⟩ : Fin n) ≠ ⟨n - 1, hb⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hpt : ∀ i : Fin n, ‖rayleighWitness n i‖ ^ 2
      = (if i = (⟨n - 2, ha⟩ : Fin n) then (1 / 2 : ℝ) else 0)
        + (if i = (⟨n - 1, hb⟩ : Fin n) then (1 / 2 : ℝ) else 0) := by
    intro i
    have hs : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [rayleighWitness_apply hn]
    by_cases h1 : (i : ℕ) = n - 2
    · have h2 : (i : ℕ) ≠ n - 1 := by omega
      have hi1 : i = (⟨n - 2, ha⟩ : Fin n) := Fin.ext h1
      have hi2 : i ≠ (⟨n - 1, hb⟩ : Fin n) := fun h => h2 (congrArg Fin.val h)
      rw [if_pos h1, if_pos hi1, if_neg hi2, add_zero, hs]
    · by_cases h2 : (i : ℕ) = n - 1
      · have hi1 : i ≠ (⟨n - 2, ha⟩ : Fin n) := fun h => h1 (congrArg Fin.val h)
        have hi2 : i = (⟨n - 1, hb⟩ : Fin n) := Fin.ext h2
        rw [if_neg h1, if_pos h2, if_neg hi1, if_pos hi2, zero_add, norm_neg, hs]
      · have hi1 : i ≠ (⟨n - 2, ha⟩ : Fin n) := fun h => h1 (congrArg Fin.val h)
        have hi2 : i ≠ (⟨n - 1, hb⟩ : Fin n) := fun h => h2 (congrArg Fin.val h)
        rw [if_neg h1, if_neg h2, if_neg hi1, if_neg hi2]
        norm_num
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib]
  simp
  norm_num

/-! ## The prolongation vector and its winding class -/

/-- The first logarithmic `U`-prolongation of the maximal minors. -/
def prolongationVector (n : ℕ) : Fin n ⊕ Unit → ℤ :=
  Sum.elim (fun j : Fin n => (∑ i : Fin n, (((i : ℕ) + 1) ^ 2 : ℤ)) - (((j : ℕ) + 1) ^ 2 : ℤ))
    (fun _ => ∑ i : Fin n, (((i : ℕ) + 1) ^ 2 : ℤ))

/-- **The prolongation vector is nonconstant.**  Its value on the constant column differs from its
value on any diagonal column. -/
theorem prolongationVector_ne {n : ℕ} (hn : 0 < n) :
    prolongationVector n (Sum.inl ⟨0, hn⟩) ≠ prolongationVector n (Sum.inr ()) := by
  simp only [prolongationVector, Sum.elim_inl, Sum.elim_inr]
  intro h
  have : ((((⟨0, hn⟩ : Fin n) : ℕ) + 1) ^ 2 : ℤ) = 0 := by linarith
  simp at this

/-- **The winding class is nonzero modulo the common projective winding.**  No integer shift of the
all-ones vector equals the prolongation vector's difference pattern. -/
theorem prolongationVector_not_constant {n : ℕ} (hn : 1 < n) :
    ¬ ∃ c : ℤ, ∀ x : Fin n ⊕ Unit, prolongationVector n x = c := by
  rintro ⟨c, hc⟩
  have h0 := hc (Sum.inl ⟨0, by omega⟩)
  have h1 := hc (Sum.inr ())
  rw [← h1] at h0
  exact prolongationVector_ne (by omega) h0

end HTGeometry.ConstraintFrameRelativity
