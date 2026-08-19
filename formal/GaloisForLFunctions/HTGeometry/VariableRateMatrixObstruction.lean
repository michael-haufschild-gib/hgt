/-
# The quadratic-rate obstruction with the rate carried as a variable

The fixed-shell nonflatness argument meets the quadratic-rate relation with `κ Q(H)` on the right,
where `Q(H) = D^{-1} Tr(H²)` moves with the Hamiltonian.  A constant rate is therefore not enough:
the labeling-orbit obstruction must be built over the polynomial ring in the parameters, with the
rate one of its elements, and specialised afterwards.

Nothing has to be reproved to do that.  The orbit construction already works over any
characteristic-zero integral domain, and `MvPolynomial θ ℂ` is one; what makes the specialisation
legitimate is naturality of the symmetric-polynomial descent, which says that changing the
coefficients commutes with the whole construction.  So the pullback through the characteristic
coefficients still evaluates, at each parameter, to the labeling-orbit obstruction of the root
packet -- now with the rate evaluated there too.

Main results:
* `variableRateObstructionPullback` — the obstruction as a polynomial in the parameters.
* `eval_variableRateObstructionPullback` — its value is the orbit obstruction of the root packet
  at the specialised rate.
* `exists_mem_eval_variableRateObstructionPullback_ne_zero` — one complex witness forces failure
  of every relabeled relation somewhere in every nonempty open set of real parameters.
-/
import GaloisForLFunctions.HTGeometry.QuadraticRateMatrixObstruction
import GaloisForLFunctions.HTGeometry.SymmetricDescentBaseChange

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Pull the labeling-orbit obstruction through the characteristic coefficients of a polynomial
matrix family, with the quadratic rate itself a polynomial in the parameters. -/
def variableRateObstructionPullback {θ I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial θ ℂ)) (c : I → ℂ) (κ : MvPolynomial θ ℂ) : MvPolynomial θ ℂ :=
  MvPolynomial.aeval (matrixCharacteristicElementaryPolynomial M)
    (fieldQuadraticRateCoefficientPolynomial (fun i => MvPolynomial.C (c i)) κ)

/-- **The variable-rate pullback evaluates to the orbit obstruction of the root packet**, with the
rate evaluated at the same parameter. -/
theorem eval_variableRateObstructionPullback {θ I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial θ ℂ)) (c : I → ℂ) (κ : MvPolynomial θ ℂ) (z : θ → ℂ)
    (energy : I → ℂ) (hinj : Function.Injective energy)
    (hroot : ∀ i, matrixCharpolyRelation
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z), energy i) = 0) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (variableRateObstructionPullback M c κ)
      = fieldQuadraticRateOrbitValue c (MvPolynomial.eval₂ (RingHom.id ℂ) z κ) energy := by
  classical
  set φ : MvPolynomial θ ℂ →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) z with hφ
  set F : MvPolynomial (Fin (Fintype.card I)) (MvPolynomial θ ℂ) :=
    fieldQuadraticRateCoefficientPolynomial (fun i => MvPolynomial.C (c i)) κ with hF
  have hstep : MvPolynomial.eval₂ (RingHom.id ℂ) z (variableRateObstructionPullback M c κ)
      = MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i => φ (matrixCharacteristicElementaryPolynomial M i)) (MvPolynomial.map φ F) := by
    have h1 : MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun i => φ (matrixCharacteristicElementaryPolynomial M i)) (MvPolynomial.map φ F)
        = MvPolynomial.eval₂ φ
          (fun i => φ (matrixCharacteristicElementaryPolynomial M i)) F := by
      rw [MvPolynomial.eval₂_map, RingHom.id_comp]
    rw [h1]
    show φ (MvPolynomial.aeval (matrixCharacteristicElementaryPolynomial M) F) = _
    rw [MvPolynomial.aeval_def, Algebra.algebraMap_self,
      MvPolynomial.eval₂_comp_left φ (RingHom.id (MvPolynomial θ ℂ))
        (matrixCharacteristicElementaryPolynomial M) F, RingHom.comp_id]
    rfl
  have hmap : MvPolynomial.map φ F = fieldQuadraticRateCoefficientPolynomial c (φ κ) := by
    rw [hF, map_fieldQuadraticRateCoefficientPolynomial]
    congr 1
    funext i
    simp [hφ]
  have hcoeff : ∀ i : Fin (Fintype.card I),
      φ (matrixCharacteristicElementaryPolynomial M i)
        = MvPolynomial.eval₂ (RingHom.id ℂ) energy (MvPolynomial.esymm I ℂ ((i : ℕ) + 1)) := by
    intro i
    show MvPolynomial.eval₂ (RingHom.id ℂ) z (matrixCharacteristicElementaryPolynomial M i) = _
    rw [eval_matrixCharacteristicElementaryPolynomial,
      matrixCharacteristicElementaryCoefficient_eq_rootPacket _ energy hinj hroot i,
      eval₂_esymm_rat_eq_complex]
  rw [hstep, hmap, funext hcoeff, eval_fieldQuadraticRateCoefficientPolynomial_esymm]
  rw [show MvPolynomial.eval₂ (RingHom.id ℂ) energy (fieldQuadraticRateOrbitPolynomial c (φ κ))
      = MvPolynomial.eval energy (fieldQuadraticRateOrbitPolynomial c (φ κ)) from rfl,
    eval_fieldQuadraticRateOrbitPolynomial]
  rfl

/-- A complex polynomial that is nonzero at one complex point is nonzero somewhere in every
nonempty open set of real points. -/
theorem exists_mem_eval₂_ne_zero_of_exists {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hwitness : ∃ z : Fin m → ℂ, MvPolynomial.eval₂ (RingHom.id ℂ) z P ≠ 0)
    {U : Set (Fin m → ℝ)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) P ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz⟩ := hwitness
  refine hz ?_
  have hre : complexMvPolynomialRealPart P = 0 := by
    refine realMvPolynomial_eq_zero_of_eqOn_zero_isOpen hUopen hUne ?_
    intro p hp
    rw [eval_complexMvPolynomialRealPart, hcon p hp, Complex.zero_re]
  have him : complexMvPolynomialImagPart P = 0 := by
    refine realMvPolynomial_eq_zero_of_eqOn_zero_isOpen hUopen hUne ?_
    intro p hp
    rw [eval_complexMvPolynomialImagPart, hcon p hp, Complex.zero_im]
  have hzero : P = 0 := by
    refine MvPolynomial.ext _ _ fun d => ?_
    refine Complex.ext ?_ ?_
    · rw [← coeff_complexMvPolynomialRealPart, hre]
      simp
    · rw [← coeff_complexMvPolynomialImagPart, him]
      simp
  rw [hzero, MvPolynomial.eval₂_zero]

/-- **One complex witness beats every real open set, at a moving rate.**  If some parameter of the
family carries a full simple root packet on which no relabeling satisfies the quadratic-rate
relation at the rate prescribed there, then inside every nonempty open set of real parameters the
obstruction is somewhere nonzero. -/
theorem exists_mem_eval_variableRateObstructionPullback_ne_zero
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : MvPolynomial (Fin m) ℂ)
    (hwitness : ∃ z : Fin m → ℂ,
      MvPolynomial.eval₂ (RingHom.id ℂ) z (variableRateObstructionPullback M c κ) ≠ 0)
    {U : Set (Fin m → ℝ)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
      (variableRateObstructionPullback M c κ) ≠ 0 :=
  exists_mem_eval₂_ne_zero_of_exists _ hwitness hUopen hUne

/-- **The witness form.**  A single complex parameter carrying a simple root packet at which no
relabeled quadratic-rate relation holds produces, in every nonempty open set of real parameters, a
point whose root packet again satisfies no relabeled relation. -/
theorem exists_mem_forall_relabelled_quadraticRate_ne_zero
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : MvPolynomial (Fin m) ℂ)
    {z₀ : Fin m → ℂ} {energy₀ : I → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z₀), energy₀ i) = 0)
    (hfail : ∀ σ : Equiv.Perm I,
      (∑ j, c (σ.symm j) * energy₀ j) ^ 2
        - MvPolynomial.eval₂ (RingHom.id ℂ) z₀ κ * ∑ j, energy₀ j ^ 2 ≠ 0)
    {U : Set (Fin m → ℝ)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, ∀ (energy : I → ℂ), Function.Injective energy →
      (∀ i, matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p t : ℂ))), energy i) = 0) →
      ∀ σ : Equiv.Perm I,
        (∑ j, c (σ.symm j) * energy j) ^ 2
          - MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) κ * ∑ j, energy j ^ 2 ≠ 0 := by
  have hwitness : ∃ z : Fin m → ℂ,
      MvPolynomial.eval₂ (RingHom.id ℂ) z (variableRateObstructionPullback M c κ) ≠ 0 := by
    refine ⟨z₀, ?_⟩
    rw [eval_variableRateObstructionPullback M c κ z₀ energy₀ hinj₀ hroot₀]
    intro hzero
    obtain ⟨σ, hσ⟩ := (fieldQuadraticRateOrbitValue_eq_zero_iff c
      (MvPolynomial.eval₂ (RingHom.id ℂ) z₀ κ) energy₀).mp hzero
    exact hfail σ hσ
  obtain ⟨p, hp, hne⟩ :=
    exists_mem_eval_variableRateObstructionPullback_ne_zero M c κ hwitness hUopen hUne
  refine ⟨p, hp, fun energy hinj hroot σ hσ => hne ?_⟩
  rw [eval_variableRateObstructionPullback M c κ (fun t => (p t : ℂ)) energy hinj hroot]
  exact (fieldQuadraticRateOrbitValue_eq_zero_iff c _ energy).mpr ⟨σ, hσ⟩

end GaloisForLFunctions.HTGeometry
