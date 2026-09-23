import GaloisForLFunctions.HTGeometry.ObserverPairDistance
import GaloisForLFunctions.HTGeometry.CompoundKyFan
import GaloisForLFunctions.HTGeometry.TopSumMajorization

/-!
# The distance between observer metrics is a metric

The distance `observerDist P Q = ‖log (√P⁻¹ Q √P⁻¹)‖` obeys the triangle inequality, so the
positive-definite Hermitian forms carry a genuine metric — the nonpositively curved bulk whose
boundary at infinity carries the horizon building.

The proof is spectral and elementary.  Writing `α`, `β`, `γ` for the spectra of the pencils
`(P, Q)`, `(Q, R)`, `(P, R)`, the distance is the Euclidean norm of the logarithms of the
spectrum, so what has to be proved is a majorization: every sum of `k` of the numbers `log γ` is
dominated by the sum of the largest `k` of the `log α` plus the largest `k` of the `log β`, with
equality for `k` the whole dimension.  Passing to the `k`-th compound turns a `k`-fold product of
eigenvalues into a single one, where the comparison of two Hermitian forms is transitive with
multiplicative constants, and the equality for `k = N` is multiplicativity of the determinant.
Karamata's inequality for the square then converts the majorization into the triangle inequality.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Matrix

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The distance in spectral coordinates -/

/-- **The radial distance is the Euclidean norm of the logarithms of the spectrum.** -/
theorem distId_eq_sqrt {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hn : finrank ℂ E = n) :
    distId hA hn = Real.sqrt (∑ i, Real.log (hA.eigenvalues hn i) ^ (2 : ℕ)) := by
  rw [distId, hsNorm_toCLM_diagonal (hA.eigenvectorBasis hn) (logOp_apply_basis hA hn)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## The matrix of an operator in an orthonormal frame -/

/-- The matrix of an operator in an orthonormal frame. -/
noncomputable def obsMat (b : OrthonormalBasis (Fin n) ℂ E) (f : E →ₗ[ℂ] E) :
    Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix b.toBasis b.toBasis f

omit [FiniteDimensional ℂ E] in
theorem obsMat_comp (b : OrthonormalBasis (Fin n) ℂ E) (f g : E →ₗ[ℂ] E) :
    obsMat b (f ∘ₗ g) = obsMat b f * obsMat b g :=
  LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis f g

omit [FiniteDimensional ℂ E] in
theorem obsMat_id (b : OrthonormalBasis (Fin n) ℂ E) :
    obsMat b (LinearMap.id : E →ₗ[ℂ] E) = 1 :=
  LinearMap.toMatrix_id b.toBasis

omit [FiniteDimensional ℂ E] in
/-- **The change-of-frame matrix between two orthonormal frames is unitary.** -/
theorem changeFrame_unitary (b u : OrthonormalBasis (Fin n) ℂ E) :
    u.toBasis.toMatrix ⇑b ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  u.toMatrix_orthonormalBasis_mem_unitary b

omit [FiniteDimensional ℂ E] in
theorem changeFrame_flip (b u : OrthonormalBasis (Fin n) ℂ E) :
    b.toBasis.toMatrix ⇑u = (u.toBasis.toMatrix ⇑b)ᴴ := by
  have h2 : (u.toBasis.toMatrix ⇑b) * (u.toBasis.toMatrix ⇑b)ᴴ = 1 := by
    have := changeFrame_unitary b u
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  have h1 : b.toBasis.toMatrix ⇑u * (u.toBasis.toMatrix ⇑b) = 1 := by
    have := Module.Basis.toMatrix_mul_toMatrix_flip b.toBasis u.toBasis
    rwa [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis] at this
  calc b.toBasis.toMatrix ⇑u
      = b.toBasis.toMatrix ⇑u * ((u.toBasis.toMatrix ⇑b) * (u.toBasis.toMatrix ⇑b)ᴴ) := by
        rw [h2, mul_one]
    _ = (b.toBasis.toMatrix ⇑u * (u.toBasis.toMatrix ⇑b)) * (u.toBasis.toMatrix ⇑b)ᴴ := by
        rw [mul_assoc]
    _ = (u.toBasis.toMatrix ⇑b)ᴴ := by rw [h1, one_mul]

omit [FiniteDimensional ℂ E] in
/-- **An operator diagonal in an orthonormal frame has unitarily diagonal matrix** in any other
orthonormal frame. -/
theorem obsMat_eq_conj_rdiag (b u : OrthonormalBasis (Fin n) ℂ E) {f : E →ₗ[ℂ] E} {w : Fin n → ℝ}
    (hf : ∀ i, f (u i) = ((w i : ℝ) : ℂ) • u i) :
    obsMat b f = (u.toBasis.toMatrix ⇑b)ᴴ * rdiag w * (u.toBasis.toMatrix ⇑b) := by
  have hbase : LinearMap.toMatrix u.toBasis u.toBasis f = rdiag w :=
    toMatrix_diagonal_of_orthonormalBasis u hf
  have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    b.toBasis u.toBasis b.toBasis u.toBasis f
  rw [obsMat, ← hchange, hbase, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis,
    changeFrame_flip b u]

omit [FiniteDimensional ℂ E] in
theorem isHermitian_conj_rdiag (U : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℝ) :
    (Uᴴ * rdiag w * U).IsHermitian := by
  have hstar : (star fun i : Fin n => ((w i : ℝ) : ℂ)) = fun i : Fin n => ((w i : ℝ) : ℂ) := by
    funext i
    simp
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, rdiag, Matrix.diagonal_conjTranspose, hstar, mul_assoc]

/-! ## The relative form of a pair of observer metrics -/

variable {P Q : E →ₗ[ℂ] E}

/-- The inverse square root of an observer metric. -/
noncomputable def invSqrtOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) : E →ₗ[ℂ] E :=
  invOp (isSymmetric_sqrtOp hP hn) hn

theorem isSymmetric_invSqrtOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) :
    (invSqrtOp hP hn).IsSymmetric :=
  isSymmetric_invOp (isSymmetric_sqrtOp hP hn) hn

theorem relOp_eq_comp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) (Q : E →ₗ[ℂ] E) :
    relOp hP hn Q = invSqrtOp hP hn ∘ₗ (Q ∘ₗ invSqrtOp hP hn) := rfl

/-- **The inverse square root conjugates the metric to the reference form.** -/
theorem invSqrt_comp_self (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    invSqrtOp hP hn ∘ₗ (P ∘ₗ invSqrtOp hP hn) = LinearMap.id := by
  have hsq : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hP hn v)).re :=
    fun v hv => inner_sqrtOp_pos hP hn hpos hv
  refine LinearMap.ext fun v => ?_
  show invSqrtOp hP hn (P (invSqrtOp hP hn v)) = v
  rw [invSqrtOp, ← sqrtOp_comp_sqrtOp hP hn hpos,
    invOp_comp (isSymmetric_sqrtOp hP hn) hn hsq,
    comp_invOp (isSymmetric_sqrtOp hP hn) hn hsq]

/-- The invertible frame change attached to an observer metric. -/
noncomputable def invSqrtMat (b : OrthonormalBasis (Fin n) ℂ E) (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) : Matrix (Fin n) (Fin n) ℂ :=
  obsMat b (invSqrtOp hP hn)

theorem isHermitian_invSqrtMat (b : OrthonormalBasis (Fin n) ℂ E) (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) : (invSqrtMat b hP hn).IsHermitian := by
  rw [invSqrtMat, invSqrtOp,
    obsMat_eq_conj_rdiag b ((isSymmetric_sqrtOp hP hn).eigenvectorBasis hn)
      (w := fun i => ((isSymmetric_sqrtOp hP hn).eigenvalues hn i)⁻¹)
      (invOp_apply_basis (isSymmetric_sqrtOp hP hn) hn)]
  exact isHermitian_conj_rdiag _ _

theorem invSqrtMat_mul_self (b : OrthonormalBasis (Fin n) ℂ E) (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    invSqrtMat b hP hn * obsMat b P * invSqrtMat b hP hn = 1 := by
  rw [invSqrtMat, mul_assoc, ← obsMat_comp, ← obsMat_comp, invSqrt_comp_self hP hn hpos,
    obsMat_id]

theorem invSqrtMat_mul_relOp (b : OrthonormalBasis (Fin n) ℂ E) (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (Q : E →ₗ[ℂ] E) :
    invSqrtMat b hP hn * obsMat b Q * invSqrtMat b hP hn = obsMat b (relOp hP hn Q) := by
  rw [relOp_eq_comp, obsMat_comp, obsMat_comp, invSqrtMat, mul_assoc]

/-- **The matrix of a relative form is unitarily diagonal with the spectrum of the pencil.** -/
theorem obsMat_relOp_eq (b : OrthonormalBasis (Fin n) ℂ E) (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hQ : Q.IsSymmetric) :
    obsMat b (relOp hP hn Q)
      = (((isSymmetric_relOp hP hn hQ).eigenvectorBasis hn).toBasis.toMatrix ⇑b)ᴴ
        * rdiag ((isSymmetric_relOp hP hn hQ).eigenvalues hn)
        * (((isSymmetric_relOp hP hn hQ).eigenvectorBasis hn).toBasis.toMatrix ⇑b) :=
  obsMat_eq_conj_rdiag b _ ((isSymmetric_relOp hP hn hQ).apply_eigenvectorBasis hn)

/-! ## Products over subsets and the logarithmic spectrum -/

theorem prod_eq_exp_sum_log {ι : Type*} (t : Finset ι) {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    ∏ i ∈ t, w i = Real.exp (∑ i ∈ t, Real.log (w i)) := by
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hw i)).symm

theorem prod_le_exp_topSum {k : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hk : k ≤ n)
    (s : Set.powersetCard (Fin n) k) :
    ∏ i ∈ (s : Finset (Fin n)), w i ≤ Real.exp (topSum k fun i => Real.log (w i)) := by
  rw [prod_eq_exp_sum_log _ hw, Real.exp_le_exp]
  exact sum_le_topSum hk (Set.powersetCard.card_eq s)

/-! ## The triangle inequality -/

/-- **The triangle inequality for the distance between observer metrics.**  This is the
nonpositive-curvature statement for the space of positive-definite Hermitian forms: with the two
previous facts, that the distance vanishes exactly on the diagonal, it makes the observer-metric
space a metric space. -/
theorem observerDist_triangle {R : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hR : R.IsSymmetric) (hn : finrank ℂ E = n)
    (hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re)
    (hRpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (R v)).re) :
    observerDist hP hn hR ≤ observerDist hP hn hQ + observerDist hQ hn hR := by
  classical
  -- the three relative forms and their spectra
  set hA := isSymmetric_relOp hP hn hQ with hAdef
  set hB := isSymmetric_relOp hQ hn hR with hBdef
  set hC := isSymmetric_relOp hP hn hR with hCdef
  set α := hA.eigenvalues hn with hαdef
  set β := hB.eigenvalues hn with hβdef
  set γ := hC.eigenvalues hn with hγdef
  have hαpos : ∀ i, 0 < α i :=
    eigenvalues_pos hA hn fun v hv => inner_relOp_pos hP hn hPpos hQ hQpos hv
  have hβpos : ∀ i, 0 < β i :=
    eigenvalues_pos hB hn fun v hv => inner_relOp_pos hQ hn hQpos hR hRpos hv
  have hγpos : ∀ i, 0 < γ i :=
    eigenvalues_pos hC hn fun v hv => inner_relOp_pos hP hn hPpos hR hRpos hv
  -- the total sums agree, by multiplicativity of the determinant
  have hdet : ∑ i, Real.log (γ i) = (∑ i, Real.log (α i)) + ∑ i, Real.log (β i) := by
    have hdetC : LinearMap.det (relOp hP hn R)
        = LinearMap.det (invSqrtOp hP hn) * LinearMap.det R * LinearMap.det (invSqrtOp hP hn) := by
      rw [relOp_eq_comp, LinearMap.det_comp, LinearMap.det_comp, mul_assoc]
    have hdetA : LinearMap.det (relOp hP hn Q)
        = LinearMap.det (invSqrtOp hP hn) * LinearMap.det Q * LinearMap.det (invSqrtOp hP hn) := by
      rw [relOp_eq_comp, LinearMap.det_comp, LinearMap.det_comp, mul_assoc]
    have hdetB : LinearMap.det (relOp hQ hn R)
        = LinearMap.det (invSqrtOp hQ hn) * LinearMap.det R * LinearMap.det (invSqrtOp hQ hn) := by
      rw [relOp_eq_comp, LinearMap.det_comp, LinearMap.det_comp, mul_assoc]
    have hunitP : LinearMap.det (invSqrtOp hP hn) * LinearMap.det P
        * LinearMap.det (invSqrtOp hP hn) = 1 := by
      have := congrArg LinearMap.det (invSqrt_comp_self hP hn hPpos)
      rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_id, ← mul_assoc] at this
      exact this
    have hunitQ : LinearMap.det (invSqrtOp hQ hn) * LinearMap.det Q
        * LinearMap.det (invSqrtOp hQ hn) = 1 := by
      have := congrArg LinearMap.det (invSqrt_comp_self hQ hn hQpos)
      rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_id, ← mul_assoc] at this
      exact this
    have hprodC : LinearMap.det (relOp hP hn R)
        = LinearMap.det (relOp hP hn Q) * LinearMap.det (relOp hQ hn R) := by
      rw [hdetC, hdetA, hdetB]
      have : LinearMap.det (invSqrtOp hP hn) * LinearMap.det Q * LinearMap.det (invSqrtOp hP hn)
          * (LinearMap.det (invSqrtOp hQ hn) * LinearMap.det R * LinearMap.det (invSqrtOp hQ hn))
          = (LinearMap.det (invSqrtOp hP hn) * LinearMap.det R * LinearMap.det (invSqrtOp hP hn))
            * (LinearMap.det (invSqrtOp hQ hn) * LinearMap.det Q
              * LinearMap.det (invSqrtOp hQ hn)) := by ring
      rw [this, hunitQ, mul_one]
    rw [hC.det_eq_prod_eigenvalues hn, hA.det_eq_prod_eigenvalues hn,
      hB.det_eq_prod_eigenvalues hn] at hprodC
    have hreal : ∏ i, γ i = (∏ i, α i) * ∏ i, β i := by
      have h2 : ((∏ i, γ i : ℝ) : ℂ) = (((∏ i, α i) * ∏ i, β i : ℝ) : ℂ) := by
        rw [hαdef, hβdef, hγdef]
        push_cast
        exact hprodC
      exact_mod_cast h2
    rw [← Real.log_prod fun i _ => ne_of_gt (hαpos i),
      ← Real.log_prod fun i _ => ne_of_gt (hβpos i),
      ← Real.log_prod fun i _ => ne_of_gt (hγpos i), hreal,
      Real.log_mul (ne_of_gt (Finset.prod_pos fun i _ => hαpos i))
        (ne_of_gt (Finset.prod_pos fun i _ => hβpos i))]
  -- the top sums are dominated, by the multiplicative Ky Fan inequality on the compound
  have htop : ∀ k ≤ n, topSum k (fun i => Real.log (γ i))
      ≤ topSum k (fun i => Real.log (α i)) + topSum k (fun i => Real.log (β i)) := by
    intro k hk
    set b := hP.eigenvectorBasis hn with hbdef
    have hkey : ∀ s : Set.powersetCard (Fin n) k, ∏ i ∈ (s : Finset (Fin n)), γ i
        ≤ Real.exp (topSum k fun i => Real.log (β i))
          * Real.exp (topSum k fun i => Real.log (α i)) := by
      refine prod_le_mul_of_compound
        (P := obsMat b P) (Q := obsMat b Q) (R := obsMat b R)
        (S := invSqrtMat b hP hn) (T := invSqrtMat b hQ hn)
        (isHermitian_invSqrtMat b hP hn) (invSqrtMat_mul_self b hP hn hPpos)
        (by rw [invSqrtMat_mul_relOp, obsMat_relOp_eq b hP hn hQ])
        (changeFrame_unitary b _)
        (by rw [invSqrtMat_mul_relOp, obsMat_relOp_eq b hP hn hR])
        (changeFrame_unitary b _)
        (isHermitian_invSqrtMat b hQ hn) (invSqrtMat_mul_self b hQ hn hQpos)
        (by rw [invSqrtMat_mul_relOp, obsMat_relOp_eq b hQ hn hR])
        (changeFrame_unitary b _)
        (fun s => prod_le_exp_topSum hαpos hk s) (fun s => prod_le_exp_topSum hβpos hk s)
        (le_of_lt (Real.exp_pos _))
    obtain ⟨t, htcard, htsum⟩ := exists_sum_eq_topSum (fun i => Real.log (γ i)) hk
    have := hkey ⟨t, Set.powersetCard.mem_iff.2 htcard⟩
    rw [show ((⟨t, Set.powersetCard.mem_iff.2 htcard⟩ : Set.powersetCard (Fin n) k) :
      Finset (Fin n)) = t from rfl, prod_eq_exp_sum_log t hγpos, htsum, ← Real.exp_add,
      Real.exp_le_exp] at this
    linarith [this]
  -- assemble
  rw [observerDist, observerDist, observerDist, distId_eq_sqrt, distId_eq_sqrt, distId_eq_sqrt,
    ← hAdef, ← hBdef, ← hCdef, ← hαdef, ← hβdef, ← hγdef]
  exact sqrt_sum_sq_le_of_topSum_le htop hdet

end GaloisForLFunctions.HTGeometry
