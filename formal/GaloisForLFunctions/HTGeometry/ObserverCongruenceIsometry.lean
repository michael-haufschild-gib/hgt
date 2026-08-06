import GaloisForLFunctions.HTGeometry.ObserverDistanceSymmetry

/-!
# The observer group acts by isometries

The observer group acts on observer metrics by congruence, `P ↦ g* P g`, and that action preserves
the distance:

```text
observerDist (g* P g) (g* Q g) = observerDist P Q.
```

The mechanism is that the relative form of the congruated pair is a *unitary* conjugate of the
relative form of the original pair, by the operator `X = (g* P g)^(-1/2) g* P^(1/2)`.  So the two
relative forms carry the same weights, and the distance — the Euclidean norm of the logarithms of
those weights — is unchanged.  No eigenvalue-uniqueness theory is needed: the conjugated eigenframe
is written down.

With the orbit description of the observer metrics this says that the observer group acts on the
symmetric space by isometries, which is what makes the boundary at infinity a `PGL`-object.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The congruence action -/

/-- The congruence action of the observer group on observer metrics: `P ↦ g* P g`. -/
noncomputable def congrOp (g : E ≃ₗ[ℂ] E) (P : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  LinearMap.adjoint (g : E →ₗ[ℂ] E) ∘ₗ (P ∘ₗ (g : E →ₗ[ℂ] E))

theorem congrOp_apply (g : E ≃ₗ[ℂ] E) (P : E →ₗ[ℂ] E) (v : E) :
    congrOp g P v = LinearMap.adjoint (g : E →ₗ[ℂ] E) (P (g v)) := rfl

theorem inner_congrOp (g : E ≃ₗ[ℂ] E) (P : E →ₗ[ℂ] E) (v w : E) :
    (inner ℂ v (congrOp g P w) : ℂ) = inner ℂ (g v) (P (g w)) := by
  rw [congrOp_apply, LinearMap.adjoint_inner_right]
  simp only [LinearEquiv.coe_coe]

theorem isSymmetric_congrOp (g : E ≃ₗ[ℂ] E) {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) :
    (congrOp g P).IsSymmetric := by
  intro x y
  rw [congrOp_apply, LinearMap.adjoint_inner_left]
  simp only [LinearEquiv.coe_coe]
  rw [hP (g x) (g y), ← inner_congrOp]

theorem inner_congrOp_pos (g : E ≃ₗ[ℂ] E) {P : E →ₗ[ℂ] E}
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) {v : E} (hv : v ≠ 0) :
    0 < (inner ℂ v (congrOp g P v)).re := by
  rw [inner_congrOp]
  refine hpos (g v) fun hcon => hv ?_
  have := congrArg (fun z => g.symm z) hcon
  simpa using this

/-! ## The inverse square root -/

theorem invSqrtOp_comp_invSqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (y : E) :
    invSqrtOp hP hn (invSqrtOp hP hn y) = invOp hP hn y := by
  have hsq : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hP hn v)).re :=
    fun v hv => inner_sqrtOp_pos hP hn hpos hv
  have hy : P (invOp hP hn y) = y := comp_invOp hP hn hpos y
  have hy2 : y = sqrtOp hP hn (sqrtOp hP hn (invOp hP hn y)) := by
    rw [sqrtOp_comp_sqrtOp hP hn hpos, hy]
  conv_lhs => rw [hy2]
  rw [invSqrtOp, invOp_comp (isSymmetric_sqrtOp hP hn) hn hsq,
    invOp_comp (isSymmetric_sqrtOp hP hn) hn hsq]

theorem sqrtOp_invSqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (v : E) :
    sqrtOp hP hn (invSqrtOp hP hn v) = v :=
  comp_invOp (isSymmetric_sqrtOp hP hn) hn (fun _ hw => inner_sqrtOp_pos hP hn hpos hw) v

theorem apply_invSqrtOp {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric) (hn : finrank ℂ E = n)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (v : E) :
    P (invSqrtOp hP hn v) = sqrtOp hP hn v := by
  rw [← sqrtOp_comp_sqrtOp hP hn hpos, sqrtOp_invSqrtOp hP hn hpos]

/-! ## The intertwining operator -/

/-- The operator intertwining the relative form of a pair with that of its congruate. -/
noncomputable def congrIntertwine (g : E ≃ₗ[ℂ] E) {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (_hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) : E →ₗ[ℂ] E :=
  invSqrtOp (isSymmetric_congrOp g hP) hn ∘ₗ
    (LinearMap.adjoint (g : E →ₗ[ℂ] E) ∘ₗ sqrtOp hP hn)

theorem invOp_congrOp_apply (g : E ≃ₗ[ℂ] E) {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (w : E) :
    invOp (isSymmetric_congrOp g hP) hn (LinearMap.adjoint (g : E →ₗ[ℂ] E) (sqrtOp hP hn w))
      = g.symm (invSqrtOp hP hn w) := by
  have hZ : congrOp g P (g.symm (invSqrtOp hP hn w))
      = LinearMap.adjoint (g : E →ₗ[ℂ] E) (sqrtOp hP hn w) := by
    rw [congrOp_apply]
    congr 1
    simp only [LinearEquiv.apply_symm_apply]
    exact apply_invSqrtOp hP hn hpos w
  rw [← hZ, invOp_comp (isSymmetric_congrOp g hP) hn
    (fun v hv => inner_congrOp_pos g hpos hv)]

theorem inner_congrIntertwine (g : E ≃ₗ[ℂ] E) {P : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re) (v w : E) :
    (inner ℂ (congrIntertwine g hP hn hpos v) (congrIntertwine g hP hn hpos w) : ℂ)
      = inner ℂ v w := by
  have hZpos : ∀ u : E, u ≠ 0 → 0 < (inner ℂ u (congrOp g P u)).re :=
    fun u hu => inner_congrOp_pos g hpos hu
  show (inner ℂ (invSqrtOp (isSymmetric_congrOp g hP) hn
      (LinearMap.adjoint (g : E →ₗ[ℂ] E) (sqrtOp hP hn v)))
    (invSqrtOp (isSymmetric_congrOp g hP) hn
      (LinearMap.adjoint (g : E →ₗ[ℂ] E) (sqrtOp hP hn w))) : ℂ) = _
  rw [isSymmetric_invSqrtOp (isSymmetric_congrOp g hP) hn,
    invSqrtOp_comp_invSqrtOp (isSymmetric_congrOp g hP) hn hZpos,
    invOp_congrOp_apply g hP hn hpos, LinearMap.adjoint_inner_left]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [isSymmetric_sqrtOp hP hn, sqrtOp_invSqrtOp hP hn hpos]

/-! ## Congruence invariance of the distance -/

/-- **The observer group acts by isometries.**  Congruence by a symmetry of the observer space
preserves the distance between observer metrics. -/
theorem observerDist_congrOp (g : E ≃ₗ[ℂ] E) {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetric)
    (hn : finrank ℂ E = n) (hQ : Q.IsSymmetric)
    (hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) :
    observerDist (isSymmetric_congrOp g hP) hn (isSymmetric_congrOp g hQ)
      = observerDist hP hn hQ := by
  classical
  set u := (isSymmetric_relOp hP hn hQ).eigenvectorBasis hn with hu
  set α := (isSymmetric_relOp hP hn hQ).eigenvalues hn with hα
  have hαpos : ∀ i, 0 < α i :=
    eigenvalues_pos (isSymmetric_relOp hP hn hQ) hn
      fun v hv => inner_relOp_pos hP hn hPpos hQ hQpos hv
  set X := congrIntertwine g hP hn hPpos with hX
  have hXinner := inner_congrIntertwine g hP hn hPpos
  have horth : Orthonormal ℂ (fun i => X (u i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hXinner]
    exact orthonormal_iff_ite.1 u.orthonormal i j
  set b := orthonormalBasisOfCard hn horth with hb
  have hZpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (congrOp g P v)).re :=
    fun v hv => inner_congrOp_pos g hPpos hv
  have hdiag : ∀ i, relOp (isSymmetric_congrOp g hP) hn (congrOp g Q) (b i)
      = ((α i : ℝ) : ℂ) • b i := by
    intro i
    rw [hb, coe_orthonormalBasisOfCard]
    have hrel : relOp hP hn Q (u i) = ((α i : ℝ) : ℂ) • u i :=
      (isSymmetric_relOp hP hn hQ).apply_eigenvectorBasis hn i
    have hQi : Q (invSqrtOp hP hn (u i)) = ((α i : ℝ) : ℂ) • sqrtOp hP hn (u i) := by
      have h := congrArg (fun z => sqrtOp hP hn z) hrel
      rw [show relOp hP hn Q (u i) = invSqrtOp hP hn (Q (invSqrtOp hP hn (u i))) from rfl,
        sqrtOp_invSqrtOp hP hn hPpos, map_smul] at h
      exact h
    show invSqrtOp (isSymmetric_congrOp g hP) hn
        (congrOp g Q (invSqrtOp (isSymmetric_congrOp g hP) hn (X (u i)))) = _
    rw [hX, congrIntertwine]
    show invSqrtOp (isSymmetric_congrOp g hP) hn
        (congrOp g Q (invSqrtOp (isSymmetric_congrOp g hP) hn
          (invSqrtOp (isSymmetric_congrOp g hP) hn
            (LinearMap.adjoint (g : E →ₗ[ℂ] E) (sqrtOp hP hn (u i)))))) = _
    rw [invSqrtOp_comp_invSqrtOp (isSymmetric_congrOp g hP) hn hZpos,
      invOp_congrOp_apply g hP hn hPpos, congrOp_apply]
    simp only [LinearEquiv.apply_symm_apply]
    rw [hQi, map_smul, map_smul]
    rfl
  rw [observerDist, observerDist,
    distId_eq_sqrt_of_diagonal b hn (isSymmetric_relOp (isSymmetric_congrOp g hP) hn
      (isSymmetric_congrOp g hQ)) hdiag hαpos,
    distId_eq_sqrt (isSymmetric_relOp hP hn hQ) hn, ← hα]

end GaloisForLFunctions.HTGeometry
