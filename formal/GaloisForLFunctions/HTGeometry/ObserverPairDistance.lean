import GaloisForLFunctions.HTGeometry.ObserverInverse

/-!
# The distance between two observer metrics

The distance between two observer metrics is the radial distance of the second one measured in the
frame of the first: `dist P Q = ‖log (√P⁻¹ Q √P⁻¹)‖`.  The relative form `√P⁻¹ Q √P⁻¹` is again a
positive-definite Hermitian form, it is the reference form exactly when `Q = P`, and measuring from
the reference metric returns the radial distance.

So the distance separates points, vanishes on the diagonal, and extends the radial distance of the
previous modules to an arbitrary pair of observer metrics.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {P Q : E →ₗ[ℂ] E}

/-! ## The inverse on the other side -/

/-- **The inverse inverts on the other side too.** -/
theorem comp_invOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (v : E) :
    P (invOp hP hn v) = v := by
  have hext : P ∘ₗ (invOp hP hn) = LinearMap.id := by
    refine Basis.ext (hP.eigenvectorBasis hn).toBasis fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, invOp_apply_basis hP hn i,
      map_smul, hP.apply_eigenvectorBasis hn i, smul_smul, LinearMap.id_apply]
    have hne : hP.eigenvalues hn i ≠ 0 := ne_of_gt (eigenvalues_pos hP hn hpos i)
    simp [hne]
  exact congrArg (fun f : E →ₗ[ℂ] E => f v) hext

theorem invOp_ne_zero (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) {v : E} (hv : v ≠ 0) :
    invOp hP hn v ≠ 0 := by
  intro hcon
  refine hv ?_
  have h := comp_invOp hP hn hpos v
  rw [hcon, map_zero] at h
  exact h.symm

/-! ## The square root is positive definite -/

theorem inner_sqrtOp_pos (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) {v : E} (hv : v ≠ 0) :
    0 < (inner ℂ v (sqrtOp hP hn v)).re :=
  inner_self_pos_of_diagonal (hP.eigenvectorBasis hn) (sqrtOp_apply_basis hP hn)
    (fun i => Real.sqrt_pos.2 (eigenvalues_pos hP hn hpos i)) hv

/-! ## The relative form -/

/-- The second observer metric measured in the frame of the first: `√P⁻¹ Q √P⁻¹`. -/
noncomputable def relOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) (Q : E →ₗ[ℂ] E) :
    E →ₗ[ℂ] E :=
  (invOp (isSymmetric_sqrtOp hP hn) hn) ∘ₗ Q ∘ₗ (invOp (isSymmetric_sqrtOp hP hn) hn)

theorem relOp_apply (hP : P.IsSymmetric) (hn : finrank ℂ E = n) (Q : E →ₗ[ℂ] E) (v : E) :
    relOp hP hn Q v = invOp (isSymmetric_sqrtOp hP hn) hn
      (Q (invOp (isSymmetric_sqrtOp hP hn) hn v)) := rfl

/-- **The relative form is Hermitian.** -/
theorem isSymmetric_relOp (hP : P.IsSymmetric) (hn : finrank ℂ E = n) (hQ : Q.IsSymmetric) :
    (relOp hP hn Q).IsSymmetric := by
  intro v w
  have hinv := isSymmetric_invOp (isSymmetric_sqrtOp hP hn) hn
  show inner ℂ (relOp hP hn Q v) w = inner ℂ v (relOp hP hn Q w)
  rw [relOp_apply, relOp_apply, hinv, hQ, ← hinv]

/-- **The relative form is positive definite.** -/
theorem inner_relOp_pos (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (_hQ : Q.IsSymmetric)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) {v : E} (hv : v ≠ 0) :
    0 < (inner ℂ v (relOp hP hn Q v)).re := by
  have hsq : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hP hn v)).re :=
    fun v hv => inner_sqrtOp_pos hP hn hpos hv
  have hne : invOp (isSymmetric_sqrtOp hP hn) hn v ≠ 0 :=
    invOp_ne_zero (isSymmetric_sqrtOp hP hn) hn hsq hv
  have hinv := isSymmetric_invOp (isSymmetric_sqrtOp hP hn) hn
  have hval : inner ℂ v (relOp hP hn Q v)
      = inner ℂ (invOp (isSymmetric_sqrtOp hP hn) hn v)
        (Q (invOp (isSymmetric_sqrtOp hP hn) hn v)) := by
    rw [relOp_apply, ← hinv]
  rw [hval]
  exact hQpos _ hne

/-! ## The distance -/

/-- The distance between two observer metrics. -/
noncomputable def observerDist (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hQ : Q.IsSymmetric) : ℝ :=
  distId (isSymmetric_relOp hP hn hQ) hn

/-- **The relative form of a metric with itself is the reference form.** -/
theorem relOp_self (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    relOp hP hn P = LinearMap.id := by
  have hsq : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hP hn v)).re :=
    fun v hv => inner_sqrtOp_pos hP hn hpos hv
  ext v
  rw [relOp_apply, LinearMap.id_apply]
  have hPv : P (invOp (isSymmetric_sqrtOp hP hn) hn v)
      = sqrtOp hP hn (sqrtOp hP hn (invOp (isSymmetric_sqrtOp hP hn) hn v)) :=
    (sqrtOp_comp_sqrtOp hP hn hpos _).symm
  rw [hPv, invOp_comp (isSymmetric_sqrtOp hP hn) hn hsq,
    comp_invOp (isSymmetric_sqrtOp hP hn) hn hsq]

/-- **A metric is at distance zero from itself.** -/
theorem observerDist_self (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) :
    observerDist hP hn hP = 0 := by
  rw [observerDist, distId_eq_zero_iff _ hn (fun v hv => inner_relOp_pos hP hn hpos hP hpos hv)]
  exact relOp_self hP hn hpos

/-- **The distance separates observer metrics.** -/
theorem observerDist_eq_zero_iff (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (hQ : Q.IsSymmetric)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) :
    observerDist hP hn hQ = 0 ↔ Q = P := by
  have hsq : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hP hn v)).re :=
    fun v hv => inner_sqrtOp_pos hP hn hpos hv
  rw [observerDist,
    distId_eq_zero_iff _ hn (fun v hv => inner_relOp_pos hP hn hpos hQ hQpos hv)]
  constructor
  · intro h
    ext w
    have hw : relOp hP hn Q (sqrtOp hP hn w) = sqrtOp hP hn w := by
      rw [h]
      rfl
    rw [relOp_apply, invOp_comp (isSymmetric_sqrtOp hP hn) hn hsq] at hw
    have hQw : sqrtOp hP hn (invOp (isSymmetric_sqrtOp hP hn) hn (Q w))
        = sqrtOp hP hn (sqrtOp hP hn w) := by rw [hw]
    rw [comp_invOp (isSymmetric_sqrtOp hP hn) hn hsq, sqrtOp_comp_sqrtOp hP hn hpos] at hQw
    exact hQw
  · rintro rfl
    exact relOp_self hP hn hpos

/-- **Measured from the reference metric, the relative form is the metric itself**, so the distance
from the reference metric is the radial distance. -/
theorem relOp_id (hid : (LinearMap.id : E →ₗ[ℂ] E).IsSymmetric) (hn : finrank ℂ E = n)
    (Q : E →ₗ[ℂ] E) : relOp hid hn Q = Q := by
  have hidpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v ((LinearMap.id : E →ₗ[ℂ] E) v)).re := by
    intro v hv
    rw [LinearMap.id_apply]
    simpa using (re_inner_self_pos (𝕜 := ℂ) (x := v)).2 hv
  have hval : ∀ i, hid.eigenvalues hn i = 1 := by
    intro i
    have hne : (hid.eigenvectorBasis hn) i ≠ 0 := (hid.eigenvectorBasis hn).orthonormal.ne_zero i
    have hb := hid.apply_eigenvectorBasis hn i
    rw [LinearMap.id_apply] at hb
    have h1 : ((1 : ℝ) : ℂ) • (hid.eigenvectorBasis hn) i
        = ((hid.eigenvalues hn i : ℝ) : ℂ) • (hid.eigenvectorBasis hn) i := by
      rw [show (((1 : ℝ) : ℂ) • (hid.eigenvectorBasis hn) i)
        = (hid.eigenvectorBasis hn) i from by simp]
      exact hb
    have h2 := smul_left_injective ℂ hne h1
    simpa using h2.symm
  have hsqrt : sqrtOp hid hn = LinearMap.id := by
    refine Basis.ext (hid.eigenvectorBasis hn).toBasis fun i => ?_
    rw [OrthonormalBasis.coe_toBasis, sqrtOp_apply_basis hid hn i, hval i, Real.sqrt_one,
      LinearMap.id_apply]
    simp
  have hinvid : ∀ v : E, invOp (isSymmetric_sqrtOp hid hn) hn v = v := by
    intro v
    have h := comp_invOp (isSymmetric_sqrtOp hid hn) hn
      (fun w hw => inner_sqrtOp_pos hid hn hidpos hw) v
    have h2 : sqrtOp hid hn (invOp (isSymmetric_sqrtOp hid hn) hn v)
        = invOp (isSymmetric_sqrtOp hid hn) hn v :=
      congrArg (fun f : E →ₗ[ℂ] E => f (invOp (isSymmetric_sqrtOp hid hn) hn v)) hsqrt
    rw [h2] at h
    exact h
  ext v
  rw [relOp_apply, hinvid, hinvid]

end GaloisForLFunctions.HTGeometry
