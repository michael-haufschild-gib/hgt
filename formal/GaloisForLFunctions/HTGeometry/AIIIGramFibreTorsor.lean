import GaloisForLFunctions.HTGeometry.ColorGramSpecialUnitaryOrbit

/-!
# Rectangular Gram fibres and the `SU(p)`-torsor condition

For `X : Matrix (Fin p) (Fin q) ℂ` the Gram record is `Xᴴ * X`.  Left multiplication by a unitary
matrix preserves it, and this file determines exactly when the induced `SU(p)`-action on a Gram
fibre is a torsor.

* `gram_eq_iff_exists_left_unitary`: equal Gram records are exactly left `U(p)`-orbits, in every
  rectangular size.
* `gram_eq_iff_exists_left_specialUnitary`: for `q < p` the determinant can always be corrected
  along a normal direction, so equal Gram records are already left `SU(p)`-orbits.
* `specialUnitary_fix_regular_eq_one`: for `p = q + 1` the stabilizer of a regular event in
  `SU(q+1)` is trivial.
* `exists_specialUnitary_ne_one_fix_regular`: for `q + 2 ≤ p` a regular event has a nontrivial
  `SU(p)`-stabilizer, namely the reflection in two orthonormal normal directions.

Combining these gives the balance dichotomy: a regular Gram fibre is an `SU(p)`-torsor exactly when
`p = q + 1`, which is exactly the equality `p² + q² = 2pq + 1` of retained and forbidden real
dimensions.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section RectangularOrbit

variable {p q : ℕ}

/-- The inner product after applying a rectangular event is computed by its Gram record. -/
theorem inner_rect_mulVec_eq_gram
    (X : Matrix (Fin p) (Fin q) ℂ) (v w : Fin q → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (X *ᵥ w) = star v ⬝ᵥ ((Xᴴ * X) *ᵥ w) := by
  calc star (X *ᵥ v) ⬝ᵥ (X *ᵥ w)
      = (star v ᵥ* Xᴴ) ⬝ᵥ (X *ᵥ w) := by rw [Matrix.star_mulVec]
    _ = star v ⬝ᵥ (Xᴴ *ᵥ (X *ᵥ w)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = star v ⬝ᵥ ((Xᴴ * X) *ᵥ w) := by rw [Matrix.mulVec_mulVec]

/-- The conjugate-transposed form of the Gram inner-product identity. -/
theorem mulVec_dotProduct_star_eq_gram
    (X : Matrix (Fin p) (Fin q) ℂ) (v w : Fin q → ℂ) :
    (X *ᵥ w) ⬝ᵥ star (X *ᵥ v) = ((Xᴴ * X) *ᵥ w) ⬝ᵥ star v := by
  rw [dotProduct_comm (X *ᵥ w), dotProduct_comm ((Xᴴ * X) *ᵥ w)]
  exact inner_rect_mulVec_eq_gram X v w

/-- Equal Gram records force equal kernels. -/
theorem rect_ker_eq_of_gram_eq
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    LinearMap.ker (Matrix.toEuclideanLin X) = LinearMap.ker (Matrix.toEuclideanLin Y) := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
  rw [← Matrix.conjTranspose_mul_self_mulVec_eq_zero,
    hGram, Matrix.conjTranspose_mul_self_mulVec_eq_zero]

/-- Equal Gram records identify the ranges through the common quotient. -/
def rectRangeEquiv
    (X Y : Matrix (Fin p) (Fin q) ℂ)
    (hker : LinearMap.ker (Matrix.toEuclideanLin X) = LinearMap.ker (Matrix.toEuclideanLin Y)) :
    LinearMap.range (Matrix.toEuclideanLin X) ≃ₗ[ℂ] LinearMap.range (Matrix.toEuclideanLin Y) :=
  (Matrix.toEuclideanLin X).quotKerEquivRange.symm.trans <|
    (Submodule.quotEquivOfEq _ _ hker).trans (Matrix.toEuclideanLin Y).quotKerEquivRange

theorem rectRangeEquiv_apply
    (X Y : Matrix (Fin p) (Fin q) ℂ)
    (hker : LinearMap.ker (Matrix.toEuclideanLin X) = LinearMap.ker (Matrix.toEuclideanLin Y))
    (v : EuclideanSpace ℂ (Fin q)) :
    rectRangeEquiv X Y hker
        ⟨Matrix.toEuclideanLin X v, LinearMap.mem_range_self _ v⟩ =
      ⟨Matrix.toEuclideanLin Y v, LinearMap.mem_range_self _ v⟩ := by
  apply Subtype.ext
  simp [rectRangeEquiv]

/-- Equal Gram records give equal inner products on the images of all vectors. -/
theorem inner_rect_toEuclideanLin_eq_of_gram_eq
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y)
    (v w : EuclideanSpace ℂ (Fin q)) :
    inner ℂ (Matrix.toEuclideanLin X v) (Matrix.toEuclideanLin X w) =
      inner ℂ (Matrix.toEuclideanLin Y v) (Matrix.toEuclideanLin Y w) := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  rw [mulVec_dotProduct_star_eq_gram, hGram, ← mulVec_dotProduct_star_eq_gram]

/-- The isometry from the range of `X` to the ambient space carrying `X` to `Y`. -/
def rectRangeIsometry
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    LinearMap.range (Matrix.toEuclideanLin X) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p) := by
  let hker := rect_ker_eq_of_gram_eq X Y hGram
  let e := rectRangeEquiv X Y hker
  let f : LinearMap.range (Matrix.toEuclideanLin X) →ₗ[ℂ] EuclideanSpace ℂ (Fin p) :=
    (LinearMap.range (Matrix.toEuclideanLin Y)).subtype.comp e.toLinearMap
  refine LinearMap.isometryOfInner (𝕜 := ℂ)
    (E := LinearMap.range (Matrix.toEuclideanLin X))
    (E' := EuclideanSpace ℂ (Fin p)) f ?_
  intro u v
  obtain ⟨u₀, hu₀⟩ := u.property
  obtain ⟨v₀, hv₀⟩ := v.property
  have hu : u = ⟨Matrix.toEuclideanLin X u₀, LinearMap.mem_range_self _ u₀⟩ :=
    Subtype.ext hu₀.symm
  have hv : v = ⟨Matrix.toEuclideanLin X v₀, LinearMap.mem_range_self _ v₀⟩ :=
    Subtype.ext hv₀.symm
  rw [hu, hv]
  change inner ℂ
      ((e ⟨Matrix.toEuclideanLin X u₀, LinearMap.mem_range_self _ u₀⟩ :
        LinearMap.range (Matrix.toEuclideanLin Y)) : EuclideanSpace ℂ (Fin p))
      ((e ⟨Matrix.toEuclideanLin X v₀, LinearMap.mem_range_self _ v₀⟩ :
        LinearMap.range (Matrix.toEuclideanLin Y)) : EuclideanSpace ℂ (Fin p)) =
    inner ℂ (Matrix.toEuclideanLin X u₀) (Matrix.toEuclideanLin X v₀)
  rw [rectRangeEquiv_apply X Y hker, rectRangeEquiv_apply X Y hker]
  exact (inner_rect_toEuclideanLin_eq_of_gram_eq X Y hGram u₀ v₀).symm

theorem rectRangeIsometry_apply
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y)
    (v : EuclideanSpace ℂ (Fin q)) :
    rectRangeIsometry X Y hGram
        ⟨Matrix.toEuclideanLin X v, LinearMap.mem_range_self _ v⟩ =
      Matrix.toEuclideanLin Y v := by
  let hker := rect_ker_eq_of_gram_eq X Y hGram
  change ((LinearMap.range (Matrix.toEuclideanLin Y)).subtype.comp
      (rectRangeEquiv X Y hker).toLinearMap)
      ⟨Matrix.toEuclideanLin X v, LinearMap.mem_range_self _ v⟩ =
    Matrix.toEuclideanLin Y v
  rw [LinearMap.comp_apply]
  exact congrArg Subtype.val (rectRangeEquiv_apply X Y hker v)

/-- The range isometry extended to the full ambient carrier. -/
def rectAmbientIsometry
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    EuclideanSpace ℂ (Fin p) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p) :=
  (rectRangeIsometry X Y hGram).extend

theorem rectAmbientIsometry_comp
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    (rectAmbientIsometry X Y hGram).toLinearMap.comp (Matrix.toEuclideanLin X) =
      Matrix.toEuclideanLin Y := by
  apply LinearMap.ext
  intro v
  change rectAmbientIsometry X Y hGram (Matrix.toEuclideanLin X v) =
    Matrix.toEuclideanLin Y v
  rw [show Matrix.toEuclideanLin X v =
      (⟨Matrix.toEuclideanLin X v, LinearMap.mem_range_self _ v⟩ :
        LinearMap.range (Matrix.toEuclideanLin X)) from rfl,
    rectAmbientIsometry, LinearIsometry.extend_apply, rectRangeIsometry_apply]

/-- A square unitary matrix carrying `X` to `Y` when their Gram records agree. -/
def rectOrbitUnitary
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    Matrix (Fin p) (Fin p) ℂ :=
  Matrix.toEuclideanLin.symm (rectAmbientIsometry X Y hGram).toLinearMap

theorem rectOrbitUnitary_toEuclideanLin
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    Matrix.toEuclideanLin (rectOrbitUnitary X Y hGram) =
      (rectAmbientIsometry X Y hGram).toLinearMap := by
  simp [rectOrbitUnitary]

theorem rectOrbitUnitary_mul
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    rectOrbitUnitary X Y hGram * X = Y := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, rectOrbitUnitary_toEuclideanLin]
  exact rectAmbientIsometry_comp X Y hGram

theorem rectOrbitUnitary_conjTranspose_mul_self
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    (rectOrbitUnitary X Y hGram)ᴴ * rectOrbitUnitary X Y hGram = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    rectOrbitUnitary_toEuclideanLin]
  simpa only [Matrix.toLpLin_one] using
    (rectAmbientIsometry X Y hGram).adjoint_comp_self'

/-- Left multiplication by a matrix with orthonormal columns preserves the Gram record. -/
theorem gram_left_unitary_invariant
    (U : Matrix (Fin p) (Fin p) ℂ) (X : Matrix (Fin p) (Fin q) ℂ)
    (hU : Uᴴ * U = 1) :
    (U * X)ᴴ * (U * X) = Xᴴ * X := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U X, hU,
    Matrix.one_mul]

/-- **Equal Gram records are exactly left `U(p)`-orbits**, in every rectangular size. -/
theorem gram_eq_iff_exists_left_unitary
    (X Y : Matrix (Fin p) (Fin q) ℂ) :
    Xᴴ * X = Yᴴ * Y ↔
      ∃ U : Matrix (Fin p) (Fin p) ℂ, Uᴴ * U = 1 ∧ U * X = Y := by
  constructor
  · intro hGram
    exact ⟨rectOrbitUnitary X Y hGram,
      rectOrbitUnitary_conjTranspose_mul_self X Y hGram,
      rectOrbitUnitary_mul X Y hGram⟩
  · rintro ⟨U, hU, rfl⟩
    exact (gram_left_unitary_invariant U X hU).symm

/-- Hermitian orthogonality to every column is the same as annihilation by the adjoint. -/
theorem star_vecMul_eq_zero_iff_conjTranspose_mulVec_eq_zero
    (X : Matrix (Fin p) (Fin q) ℂ) (v : Fin p → ℂ) :
    star v ᵥ* X = 0 ↔ Xᴴ *ᵥ v = 0 := by
  constructor
  · intro h
    have h2 : star (star v ᵥ* X) = 0 := by rw [h]; simp
    rw [Matrix.star_vecMul, star_star] at h2
    exact h2
  · intro h
    have h2 : star (Xᴴ *ᵥ v) = 0 := by rw [h]; simp
    rw [Matrix.star_mulVec] at h2
    simpa using h2

/-- Below the square case there is always a nonzero direction Hermitian-orthogonal to every
column. -/
theorem exists_ne_zero_star_vecMul_eq_zero (hpq : q < p) (X : Matrix (Fin p) (Fin q) ℂ) :
    ∃ v : Fin p → ℂ, v ≠ 0 ∧ star v ᵥ* X = 0 := by
  set f : (Fin p → ℂ) →ₗ[ℂ] (Fin q → ℂ) := Matrix.mulVecLin Xᴴ with hf
  have hrank : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f)
      = Module.finrank ℂ (Fin p → ℂ) := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank ℂ (Fin p → ℂ) = p := by simp
  have hle : Module.finrank ℂ (LinearMap.range f) ≤ q := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h] at hrank
    simp [hdim] at hrank
    omega
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hvne, ?_⟩
  exact (star_vecMul_eq_zero_iff_conjTranspose_mulVec_eq_zero X v).2 hvmem

/-- A canonical nonzero normal direction of a rectangular event below the square case. -/
def rectNormal (hpq : q < p) (X : Matrix (Fin p) (Fin q) ℂ) : Fin p → ℂ :=
  Classical.choose (exists_ne_zero_star_vecMul_eq_zero hpq X)

theorem rectNormal_ne_zero (hpq : q < p) (X : Matrix (Fin p) (Fin q) ℂ) :
    rectNormal hpq X ≠ 0 :=
  (Classical.choose_spec (exists_ne_zero_star_vecMul_eq_zero hpq X)).1

theorem rectNormal_star_vecMul (hpq : q < p) (X : Matrix (Fin p) (Fin q) ℂ) :
    star (rectNormal hpq X) ᵥ* X = 0 :=
  (Classical.choose_spec (exists_ne_zero_star_vecMul_eq_zero hpq X)).2

/-- A nonzero vector has nonzero Hermitian norm square. -/
theorem rootHermitianNormSq_ne_zero_of_ne_zero {n : Type*} [Fintype n] {v : n → ℂ}
    (hv : v ≠ 0) : rootHermitianNormSq v ≠ 0 := by
  intro h
  exact hv (dotProduct_star_self_eq_zero.1 h)

/-- The determinant-corrected transporter between two events with equal Gram records. -/
def rectSpecialTransporter (hpq : q < p)
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    Matrix (Fin p) (Fin p) ℂ :=
  let U := rectOrbitUnitary X Y hGram
  U * phaseAlongRoot (rectNormal hpq X) (star U.det)

theorem rectSpecialTransporter_mul (hpq : q < p)
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    rectSpecialTransporter hpq X Y hGram * X = Y := by
  simp only [rectSpecialTransporter]
  rw [Matrix.mul_assoc,
    phaseAlongRoot_mul_eq_self_of_orthogonal
      (rectNormal hpq X) X _ (rectNormal_star_vecMul hpq X),
    rectOrbitUnitary_mul X Y hGram]

theorem rectSpecialTransporter_mem_specialUnitary (hpq : q < p)
    (X Y : Matrix (Fin p) (Fin q) ℂ) (hGram : Xᴴ * X = Yᴴ * Y) :
    rectSpecialTransporter hpq X Y hGram ∈ Matrix.specialUnitaryGroup (Fin p) ℂ := by
  set U := rectOrbitUnitary X Y hGram with hU
  set D := phaseAlongRoot (rectNormal hpq X) (star U.det) with hD
  have hUstar : Uᴴ * U = 1 := rectOrbitUnitary_conjTranspose_mul_self X Y hGram
  have hUmem : U ∈ Matrix.unitaryGroup (Fin p) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hUstar
  have hdetUnit := Matrix.det_of_mem_unitary hUmem
  have hphase : star (star U.det) * star U.det = 1 := by
    simpa only [star_star] using hdetUnit.2
  have hnorm : rootHermitianNormSq (rectNormal hpq X) ≠ 0 :=
    rootHermitianNormSq_ne_zero_of_ne_zero (rectNormal_ne_zero hpq X)
  have hDstar : Dᴴ * D = 1 :=
    phaseAlongRoot_conjTranspose_mul_self (rectNormal hpq X) (star U.det) hnorm hphase
  have hDmem : D ∈ Matrix.unitaryGroup (Fin p) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hDstar
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨(Matrix.unitaryGroup (Fin p) ℂ).mul_mem hUmem hDmem, ?_⟩
  simp only [rectSpecialTransporter, Matrix.det_mul]
  rw [phaseAlongRoot_det (rectNormal hpq X) (star U.det) hnorm]
  exact hdetUnit.2

/-- **Below the square case equal Gram records are already left `SU(p)`-orbits.**  No regularity is
needed: the determinant phase can always be absorbed along a normal direction. -/
theorem gram_eq_iff_exists_left_specialUnitary (hpq : q < p)
    (X Y : Matrix (Fin p) (Fin q) ℂ) :
    Xᴴ * X = Yᴴ * Y ↔
      ∃ U : Matrix (Fin p) (Fin p) ℂ,
        U ∈ Matrix.specialUnitaryGroup (Fin p) ℂ ∧ U * X = Y := by
  constructor
  · intro hGram
    exact ⟨rectSpecialTransporter hpq X Y hGram,
      rectSpecialTransporter_mem_specialUnitary hpq X Y hGram,
      rectSpecialTransporter_mul hpq X Y hGram⟩
  · rintro ⟨U, hU, rfl⟩
    have hUnitary := Matrix.specialUnitaryGroup_le_unitaryGroup hU
    have hUstar : Uᴴ * U = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').mp hUnitary
      simpa [Matrix.star_eq_conjTranspose] using h
    exact (gram_left_unitary_invariant U X hUstar).symm

end RectangularOrbit

section Regularity

variable {p q : ℕ}

/-- A rectangular event is *regular* when its columns are linearly independent, equivalently when
its Gram record is positive definite. -/
def GramRegular (X : Matrix (Fin p) (Fin q) ℂ) : Prop := (Xᴴ * X).PosDef

/-- A regular event has injective column map. -/
theorem GramRegular.mulVec_eq_zero {X : Matrix (Fin p) (Fin q) ℂ} (h : GramRegular X)
    {a : Fin q → ℂ} (ha : X *ᵥ a = 0) : a = 0 := by
  by_contra hne
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.1 h).2 hne
  have hzero : (Xᴴ * X) *ᵥ a = 0 := by
    rw [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_zero]
  rw [hzero, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

theorem gramRegular_iff_mulVec_injective (X : Matrix (Fin p) (Fin q) ℂ) :
    GramRegular X ↔ Function.Injective X.mulVec := by
  constructor
  · intro h a b hab
    have : X *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub, hab, sub_self]
    exact sub_eq_zero.1 (h.mulVec_eq_zero this)
  · intro h
    exact Matrix.PosDef.conjTranspose_mul_self X h

/-- The standard rectangular event with orthonormal columns is regular. -/
def standardRectEvent (p q : ℕ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem standardRectEvent_mulVec_apply (hqp : q ≤ p) (a : Fin q → ℂ) (j : Fin q) :
    (standardRectEvent p q *ᵥ a) ⟨j, lt_of_lt_of_le j.isLt hqp⟩ = a j := by
  simp only [Matrix.mulVec, standardRectEvent, Matrix.of_apply, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : ¬ ((j : ℕ) = (b : ℕ)) := by
      intro hcon
      exact hb (Fin.ext hcon.symm)
    simp [this]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon

theorem gramRegular_standardRectEvent (hqp : q ≤ p) : GramRegular (standardRectEvent p q) := by
  rw [gramRegular_iff_mulVec_injective]
  intro a b hab
  funext j
  have := congrArg (fun v => v ⟨j, lt_of_lt_of_le j.isLt hqp⟩) hab
  simpa [standardRectEvent_mulVec_apply hqp] using this

end Regularity

section Frame

variable {q : ℕ}

/-- Complete a `(q+1) × q` event to a square frame by one extra column. -/
def rectFrame (X : Matrix (Fin (q + 1)) (Fin q) ℂ) (n : Fin (q + 1) → ℂ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ :=
  Matrix.of fun i j => Fin.lastCases (n i) (fun j' => X i j') j

@[simp] theorem rectFrame_apply_last (X : Matrix (Fin (q + 1)) (Fin q) ℂ)
    (n : Fin (q + 1) → ℂ) (i : Fin (q + 1)) :
    rectFrame X n i (Fin.last q) = n i := by
  simp [rectFrame]

@[simp] theorem rectFrame_apply_castSucc (X : Matrix (Fin (q + 1)) (Fin q) ℂ)
    (n : Fin (q + 1) → ℂ) (i : Fin (q + 1)) (j : Fin q) :
    rectFrame X n i j.castSucc = X i j := by
  simp [rectFrame]

/-- The frame acts on a vector by splitting off its last coordinate. -/
theorem rectFrame_mulVec (X : Matrix (Fin (q + 1)) (Fin q) ℂ)
    (n : Fin (q + 1) → ℂ) (z : Fin (q + 1) → ℂ) :
    rectFrame X n *ᵥ z = X *ᵥ (fun j => z j.castSucc) + z (Fin.last q) • n := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp [rectFrame, mul_comm]

/-- Replacing the last column of a frame is again a frame. -/
theorem rectFrame_updateCol (X : Matrix (Fin (q + 1)) (Fin q) ℂ)
    (n m : Fin (q + 1) → ℂ) :
    (rectFrame X n).updateCol (Fin.last q) m = rectFrame X m := by
  ext i j
  rw [Matrix.updateCol_apply]
  induction j using Fin.lastCases with
  | last => simp
  | cast j' => simp [Fin.castSucc_lt_last j' |>.ne]

/-- The frame determinant is linear in the completing column. -/
theorem det_rectFrame_smul (X : Matrix (Fin (q + 1)) (Fin q) ℂ)
    (n : Fin (q + 1) → ℂ) (c : ℂ) :
    (rectFrame X (c • n)).det = c * (rectFrame X n).det := by
  have h1 : rectFrame X (c • n) = (rectFrame X n).updateCol (Fin.last q) (c • n) :=
    (rectFrame_updateCol X n (c • n)).symm
  have h2 : (rectFrame X n).updateCol (Fin.last q) n = rectFrame X n :=
    rectFrame_updateCol X n n
  rw [h1, Matrix.det_updateCol_smul, h2]

/-- Left multiplication transports a frame to the frame of the transported data. -/
theorem mul_rectFrame (U : Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ)
    (X : Matrix (Fin (q + 1)) (Fin q) ℂ) (n : Fin (q + 1) → ℂ) :
    U * rectFrame X n = rectFrame (U * X) (U *ᵥ n) := by
  ext i j
  induction j using Fin.lastCases with
  | last => simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  | cast j' => simp [Matrix.mul_apply]

/-- A regular event completed by a nonzero normal direction has invertible frame. -/
theorem rectFrame_det_ne_zero (X : Matrix (Fin (q + 1)) (Fin q) ℂ)
    (n : Fin (q + 1) → ℂ) (hX : GramRegular X) (hn : n ≠ 0)
    (hnormal : star n ᵥ* X = 0) :
    (rectFrame X n).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hzne, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [rectFrame_mulVec] at hz
  set a : Fin q → ℂ := fun j => z j.castSucc with ha
  set c : ℂ := z (Fin.last q) with hc
  have hpair : star n ⬝ᵥ (X *ᵥ a + c • n) = 0 := by rw [hz, dotProduct_zero]
  rw [dotProduct_add, Matrix.dotProduct_mulVec, hnormal, dotProduct_smul] at hpair
  simp only [zero_dotProduct, zero_add, smul_eq_mul] at hpair
  have hnn : star n ⬝ᵥ n ≠ 0 := by
    intro hcon
    exact hn (dotProduct_star_self_eq_zero.1 hcon)
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 hpair with h | h
    · exact h
    · exact absurd h hnn
  have hXa : X *ᵥ a = 0 := by
    have := hz
    rw [hc0, zero_smul, add_zero] at this
    exact this
  have ha0 : a = 0 := hX.mulVec_eq_zero hXa
  apply hzne
  funext j
  induction j using Fin.lastCases with
  | last => simpa [hc] using hc0
  | cast j' => simpa [ha] using congrFun ha0 j'

end Frame

section Freeness

variable {q : ℕ}

/-- A unitary fixing a regular event also fixes its normal directions. -/
theorem star_mulVec_vecMul_eq_zero_of_fix
    {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (X : Matrix (Fin p) (Fin q) ℂ)
    (hUstar : Uᴴ * U = 1) (hfix : U * X = X) (n : Fin p → ℂ)
    (hnormal : star n ᵥ* X = 0) :
    star (U *ᵥ n) ᵥ* X = 0 := by
  have hadj : Uᴴ * X = X := by
    calc Uᴴ * X = Uᴴ * (U * X) := by rw [hfix]
      _ = (Uᴴ * U) * X := by rw [Matrix.mul_assoc]
      _ = X := by rw [hUstar, Matrix.one_mul]
  calc star (U *ᵥ n) ᵥ* X = (star n ᵥ* Uᴴ) ᵥ* X := by rw [Matrix.star_mulVec]
    _ = star n ᵥ* (Uᴴ * X) := by rw [Matrix.vecMul_vecMul]
    _ = star n ᵥ* X := by rw [hadj]
    _ = 0 := hnormal

/-- **Trivial stabilizer in the consecutive case.**  When the ambient dimension exceeds the number
of columns by exactly one, the only special unitary fixing a regular event is the identity. -/
theorem specialUnitary_fix_regular_eq_one
    (X : Matrix (Fin (q + 1)) (Fin q) ℂ) (hX : GramRegular X)
    (U : Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin (q + 1)) ℂ)
    (hfix : U * X = X) :
    U = 1 := by
  have hUnitary := Matrix.specialUnitaryGroup_le_unitaryGroup hU
  have hUstar : Uᴴ * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hUnitary
    simpa [Matrix.star_eq_conjTranspose] using h
  set hpq : q < q + 1 := Nat.lt_succ_self q with hpqdef
  set n : Fin (q + 1) → ℂ := rectNormal hpq X with hn
  have hnne : n ≠ 0 := rectNormal_ne_zero hpq X
  have hnormal : star n ᵥ* X = 0 := rectNormal_star_vecMul hpq X
  have hUnormal : star (U *ᵥ n) ᵥ* X = 0 :=
    star_mulVec_vecMul_eq_zero_of_fix U X hUstar hfix n hnormal
  have hdet : (rectFrame X n).det ≠ 0 := rectFrame_det_ne_zero X n hX hnne hnormal
  have hunit : IsUnit (rectFrame X n) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.2 hdet
  obtain ⟨z, hz⟩ : ∃ z : Fin (q + 1) → ℂ, rectFrame X n *ᵥ z = U *ᵥ n := by
    obtain ⟨F, hF⟩ := hunit
    refine ⟨(↑F⁻¹ : Matrix (Fin (q + 1)) (Fin (q + 1)) ℂ) *ᵥ (U *ᵥ n), ?_⟩
    rw [Matrix.mulVec_mulVec, ← hF]
    simp
  rw [rectFrame_mulVec] at hz
  set a : Fin q → ℂ := fun j => z j.castSucc with ha
  set c : ℂ := z (Fin.last q) with hc
  have hXadj : Xᴴ *ᵥ (U *ᵥ n) = 0 :=
    (star_vecMul_eq_zero_iff_conjTranspose_mulVec_eq_zero X (U *ᵥ n)).1 hUnormal
  have hXn : Xᴴ *ᵥ n = 0 :=
    (star_vecMul_eq_zero_iff_conjTranspose_mulVec_eq_zero X n).1 hnormal
  have hkey : star (X *ᵥ a) ⬝ᵥ (X *ᵥ a) = 0 := by
    have h1 : star (X *ᵥ a) ⬝ᵥ (U *ᵥ n) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hXadj, dotProduct_zero]
    have h2 : star (X *ᵥ a) ⬝ᵥ n = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hXn, dotProduct_zero]
    rw [← hz, dotProduct_add, dotProduct_smul, h2, smul_zero, add_zero] at h1
    exact h1
  have hXa : X *ᵥ a = 0 := dotProduct_star_self_eq_zero.1 hkey
  have hUn : U *ᵥ n = c • n := by
    rw [← hz, hXa, zero_add]
  have hframe : U * rectFrame X n = rectFrame X (c • n) := by
    rw [mul_rectFrame, hfix, hUn]
  have hdets : U.det * (rectFrame X n).det = c * (rectFrame X n).det := by
    rw [← Matrix.det_mul, hframe, det_rectFrame_smul]
  have hUdet : U.det = 1 := hU.2
  rw [hUdet, one_mul] at hdets
  have hc1 : c = 1 := by
    have hone : (1 : ℂ) * (rectFrame X n).det = c * (rectFrame X n).det := by
      rw [one_mul]; exact hdets
    exact (mul_right_cancel₀ hdet hone).symm
  have hfixframe : U * rectFrame X n = rectFrame X n := by
    rw [hframe, hc1, one_smul]
  exact hunit.mul_right_cancel (by rw [Matrix.one_mul]; exact hfixframe)

end Freeness

section NonFreeness

/-- A rank-one outer product acts on a vector by scaling. -/
theorem vecMulVec_mulVec_eq_smul {ι κ : Type*} [Fintype κ] (a : ι → ℂ) (b w : κ → ℂ) :
    Matrix.vecMulVec a b *ᵥ w = (b ⬝ᵥ w) • a := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A phase rotation fixes every vector Hermitian-orthogonal to its root. -/
theorem phaseAlongRoot_mulVec_of_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v w : ι → ℂ) (t : ℂ) (h : star v ⬝ᵥ w = 0) :
    phaseAlongRoot v t *ᵥ w = w := by
  simp only [phaseAlongRoot, phaseByProjection, rankOneOrthogonalProjection,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    vecMulVec_mulVec_eq_smul, h, zero_smul, smul_zero, add_zero]

/-- A phase rotation multiplies its own root by the prescribed phase. -/
theorem phaseAlongRoot_mulVec_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (t : ℂ) (hv : rootHermitianNormSq v ≠ 0) :
    phaseAlongRoot v t *ᵥ v = t • v := by
  have hself : Matrix.vecMulVec ((rootHermitianNormSq v)⁻¹ • v) (star v) *ᵥ v = v := by
    rw [vecMulVec_mulVec_eq_smul, smul_smul]
    have : rootHermitianNormSq v * (rootHermitianNormSq v)⁻¹ = 1 :=
      mul_inv_cancel₀ hv
    simp only [rootHermitianNormSq] at this ⊢
    rw [this, one_smul]
  simp only [phaseAlongRoot, phaseByProjection, rankOneOrthogonalProjection,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hself]
  rw [sub_smul, one_smul]
  abel

/-- Hermitian orthogonality is symmetric. -/
theorem star_dotProduct_comm {ι : Type*} [Fintype ι] (a b : ι → ℂ) (h : star a ⬝ᵥ b = 0) :
    star b ⬝ᵥ a = 0 := by
  have hstar := congrArg star h
  simpa [dotProduct, star_sum, mul_comm] using hstar

variable {p q : ℕ}

/-- Two orthogonal nonzero normal directions exist as soon as the ambient dimension exceeds the
number of columns by at least two. -/
theorem exists_orthogonal_normal_pair (hpq : q + 2 ≤ p) (X : Matrix (Fin p) (Fin q) ℂ) :
    ∃ n₁ n₂ : Fin p → ℂ, n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ star n₁ ᵥ* X = 0 ∧ star n₂ ᵥ* X = 0 ∧
      star n₁ ⬝ᵥ n₂ = 0 := by
  set f : (Fin p → ℂ) →ₗ[ℂ] (Fin q → ℂ) := Matrix.mulVecLin Xᴴ with hf
  have hrank : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f)
      = Module.finrank ℂ (Fin p → ℂ) := LinearMap.finrank_range_add_finrank_ker f
  have hdim : Module.finrank ℂ (Fin p → ℂ) = p := by simp
  have hle : Module.finrank ℂ (LinearMap.range f) ≤ q := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have hkerdim : 2 ≤ Module.finrank ℂ (LinearMap.ker f) := by
    rw [hdim] at hrank
    omega
  have hkerne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h] at hkerdim
    simp at hkerdim
  obtain ⟨v₁, hv₁mem, hv₁ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerne
  have hspan : ∃ v₂ ∈ LinearMap.ker f, ∀ c : ℂ, v₂ ≠ c • v₁ := by
    by_contra hcon
    push Not at hcon
    have hle2 : LinearMap.ker f ≤ (ℂ ∙ v₁) := by
      intro w hw
      obtain ⟨c, hc⟩ := hcon w hw
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₁)
    have := Submodule.finrank_mono (R := ℂ) hle2
    rw [finrank_span_singleton hv₁ne] at this
    omega
  obtain ⟨v₂, hv₂mem, hv₂⟩ := hspan
  set lam : ℂ := (star v₁ ⬝ᵥ v₂) / (star v₁ ⬝ᵥ v₁) with hlam
  set n₂ : Fin p → ℂ := v₂ - lam • v₁ with hn₂
  have hv₁norm : star v₁ ⬝ᵥ v₁ ≠ 0 := by
    intro hcon
    exact hv₁ne (dotProduct_star_self_eq_zero.1 hcon)
  have hn₂mem : n₂ ∈ LinearMap.ker f :=
    Submodule.sub_mem _ hv₂mem (Submodule.smul_mem _ _ hv₁mem)
  have hn₂ne : n₂ ≠ 0 := by
    intro hcon
    exact hv₂ lam (by rw [← sub_eq_zero]; exact hcon)
  refine ⟨v₁, n₂, hv₁ne, hn₂ne, ?_, ?_, ?_⟩
  · exact (star_vecMul_eq_zero_iff_conjTranspose_mulVec_eq_zero X v₁).2 hv₁mem
  · exact (star_vecMul_eq_zero_iff_conjTranspose_mulVec_eq_zero X n₂).2 hn₂mem
  · rw [hn₂, dotProduct_sub, dotProduct_smul, smul_eq_mul, hlam,
      div_mul_cancel₀ _ hv₁norm, sub_self]

/-- **Nontrivial stabilizer beyond the consecutive case.**  When the ambient dimension exceeds the
number of columns by at least two, every event is fixed by a special unitary reflection different
from the identity, so no Gram fibre can be an `SU(p)`-torsor. -/
theorem exists_specialUnitary_ne_one_fix (hpq : q + 2 ≤ p) (X : Matrix (Fin p) (Fin q) ℂ) :
    ∃ W : Matrix (Fin p) (Fin p) ℂ,
      W ∈ Matrix.specialUnitaryGroup (Fin p) ℂ ∧ W ≠ 1 ∧ W * X = X := by
  obtain ⟨n₁, n₂, hn₁, hn₂, hnX₁, hnX₂, horth⟩ := exists_orthogonal_normal_pair hpq X
  have hnorm₁ : rootHermitianNormSq n₁ ≠ 0 := rootHermitianNormSq_ne_zero_of_ne_zero hn₁
  have hnorm₂ : rootHermitianNormSq n₂ ≠ 0 := rootHermitianNormSq_ne_zero_of_ne_zero hn₂
  have hphase : star (-1 : ℂ) * (-1 : ℂ) = 1 := by simp
  set D₁ := phaseAlongRoot n₁ (-1 : ℂ) with hD₁
  set D₂ := phaseAlongRoot n₂ (-1 : ℂ) with hD₂
  have hD₁mem : D₁ ∈ Matrix.unitaryGroup (Fin p) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using
      phaseAlongRoot_conjTranspose_mul_self n₁ (-1 : ℂ) hnorm₁ hphase
  have hD₂mem : D₂ ∈ Matrix.unitaryGroup (Fin p) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using
      phaseAlongRoot_conjTranspose_mul_self n₂ (-1 : ℂ) hnorm₂ hphase
  refine ⟨D₁ * D₂, ?_, ?_, ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨(Matrix.unitaryGroup (Fin p) ℂ).mul_mem hD₁mem hD₂mem, ?_⟩
    rw [Matrix.det_mul, hD₁, hD₂, phaseAlongRoot_det n₁ (-1 : ℂ) hnorm₁,
      phaseAlongRoot_det n₂ (-1 : ℂ) hnorm₂]
    ring
  · intro hone
    have hfix₂ : D₂ *ᵥ n₁ = n₁ :=
      phaseAlongRoot_mulVec_of_orthogonal n₂ n₁ (-1 : ℂ) (star_dotProduct_comm n₁ n₂ horth)
    have hact : (D₁ * D₂) *ᵥ n₁ = -n₁ := by
      rw [← Matrix.mulVec_mulVec, hfix₂, hD₁,
        phaseAlongRoot_mulVec_self n₁ (-1 : ℂ) hnorm₁]
      simp
    rw [hone, Matrix.one_mulVec] at hact
    have : (2 : ℂ) • n₁ = 0 := by
      have h2 : n₁ + n₁ = 0 := by
        have := hact
        rw [eq_neg_iff_add_eq_zero] at this
        exact this
      rw [two_smul]
      exact h2
    have : n₁ = 0 := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      exact (smul_eq_zero.1 this).resolve_left h2
    exact hn₁ this
  · rw [Matrix.mul_assoc, hD₂,
      phaseAlongRoot_mul_eq_self_of_orthogonal n₂ X (-1 : ℂ) hnX₂, hD₁,
      phaseAlongRoot_mul_eq_self_of_orthogonal n₁ X (-1 : ℂ) hnX₁]

end NonFreeness

section Classification

variable {p q : ℕ}

/-- Twice the real dimension of the retained AIII isotropy algebra `s(u(p) ⊕ u(q))` is `p² + q² −
1`, in the normalization where the forbidden block has real dimension `2pq`. -/
def aiiiRetainedDimension (p q : ℕ) : ℕ := p ^ 2 + q ^ 2 - 1

/-- The real dimension of the forbidden AIII block `M_{p,q}(ℂ)`. -/
def aiiiForbiddenDimension (p q : ℕ) : ℕ := 2 * p * q

/-- **Balance is consecutiveness.**  Retained and forbidden AIII dimensions agree exactly when the
two sizes are consecutive. -/
theorem aiii_balance_iff_consecutive (hpq : q < p) :
    aiiiRetainedDimension p q = aiiiForbiddenDimension p q ↔ p = q + 1 := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 1 ≤ d ∧ p = q + d := ⟨p - q, by omega, by omega⟩
  unfold aiiiRetainedDimension aiiiForbiddenDimension
  have hexp : (q + d) ^ 2 + q ^ 2 = 2 * (q + d) * q + d ^ 2 := by ring
  have hd2 : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [hexp]
  set A : ℕ := 2 * (q + d) * q with hA
  constructor
  · intro h
    have hd1 : d ^ 2 = 1 := by omega
    rw [pow_two] at hd1
    have hdle : d ≤ 1 := by
      by_contra hcon
      have hlt : 2 ≤ d := by omega
      have : 2 * 2 ≤ d * d := Nat.mul_le_mul hlt hlt
      omega
    have : d = 1 := le_antisymm hdle hd
    omega
  · intro h
    have hdone : d = 1 := by omega
    subst hdone
    omega

/-- The `SU(p)`-action on the Gram fibre through `X` is a torsor: every event with the same Gram
record is reached by a unique special unitary. -/
def IsGramFibreTorsor (X : Matrix (Fin p) (Fin q) ℂ) : Prop :=
  ∀ Y : Matrix (Fin p) (Fin q) ℂ, Yᴴ * Y = Xᴴ * X →
    ∃! U : Matrix.specialUnitaryGroup (Fin p) ℂ,
      (U : Matrix (Fin p) (Fin p) ℂ) * X = Y

/-- A trivial stabilizer makes the left `SU(p)`-action free. -/
theorem specialUnitary_eq_of_mul_eq (X : Matrix (Fin p) (Fin q) ℂ)
    (hstab : ∀ W : Matrix (Fin p) (Fin p) ℂ,
      W ∈ Matrix.specialUnitaryGroup (Fin p) ℂ → W * X = X → W = 1)
    (U V : Matrix (Fin p) (Fin p) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin p) ℂ)
    (hV : V ∈ Matrix.specialUnitaryGroup (Fin p) ℂ)
    (hUV : U * X = V * X) : U = V := by
  have hVUnitary := Matrix.specialUnitaryGroup_le_unitaryGroup hV
  have hVstar : Vᴴ * V = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hVUnitary
    simpa [Matrix.star_eq_conjTranspose] using h
  have hVmulStar : V * Vᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff).mp hVUnitary
    simpa [Matrix.star_eq_conjTranspose] using h
  have hVstarMem : Vᴴ ∈ Matrix.specialUnitaryGroup (Fin p) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · have hstarMem := Unitary.star_mem hVUnitary
      simpa [Matrix.star_eq_conjTranspose] using hstarMem
    · rw [Matrix.det_conjTranspose, (Matrix.mem_specialUnitaryGroup_iff.1 hV).2, star_one]
  have hW : Vᴴ * U ∈ Matrix.specialUnitaryGroup (Fin p) ℂ :=
    (Matrix.specialUnitaryGroup (Fin p) ℂ).mul_mem hVstarMem hU
  have hWfix : (Vᴴ * U) * X = X := by
    rw [Matrix.mul_assoc, hUV, ← Matrix.mul_assoc, hVstar, Matrix.one_mul]
  have hWone : Vᴴ * U = 1 := hstab _ hW hWfix
  calc U = 1 * U := by rw [Matrix.one_mul]
    _ = (V * Vᴴ) * U := by rw [hVmulStar]
    _ = V * (Vᴴ * U) := by rw [Matrix.mul_assoc]
    _ = V := by rw [hWone, Matrix.mul_one]

/-- **The balanced AIII classification.**  For `p > q ≥ 1` the following are equivalent: retained
and forbidden real dimensions agree; the two sizes are consecutive; every regular Gram fibre is an
`SU(p)`-torsor; some regular Gram fibre is an `SU(p)`-torsor. -/
theorem aiii_balance_tfae (hpq : q < p) :
    List.TFAE
      [ aiiiRetainedDimension p q = aiiiForbiddenDimension p q,
        p = q + 1,
        ∀ X : Matrix (Fin p) (Fin q) ℂ, GramRegular X → IsGramFibreTorsor X,
        ∃ X : Matrix (Fin p) (Fin q) ℂ, GramRegular X ∧ IsGramFibreTorsor X ] := by
  tfae_have 1 ↔ 2 := aiii_balance_iff_consecutive hpq
  tfae_have 2 → 3 := by
    rintro rfl X hX Y hY
    have hGram : Xᴴ * X = Yᴴ * Y := hY.symm
    obtain ⟨U, hUmem, hUX⟩ :=
      (gram_eq_iff_exists_left_specialUnitary hpq X Y).1 hGram
    refine ⟨⟨U, hUmem⟩, hUX, ?_⟩
    rintro ⟨V, hVmem⟩ hV
    apply Subtype.ext
    exact specialUnitary_eq_of_mul_eq X
      (fun W hW hWfix => specialUnitary_fix_regular_eq_one X hX W hW hWfix)
      V U hVmem hUmem (hV.trans hUX.symm)
  tfae_have 3 → 4 := by
    intro h
    exact ⟨standardRectEvent p q, gramRegular_standardRectEvent (le_of_lt hpq),
      h _ (gramRegular_standardRectEvent (le_of_lt hpq))⟩
  tfae_have 4 → 2 := by
    rintro ⟨X, hX, htorsor⟩
    by_contra hne
    have hge : q + 2 ≤ p := by omega
    obtain ⟨W, hWmem, hWne, hWX⟩ := exists_specialUnitary_ne_one_fix hge X
    obtain ⟨U, _, huniq⟩ := htorsor X rfl
    have h1 : (⟨W, hWmem⟩ : Matrix.specialUnitaryGroup (Fin p) ℂ) = U :=
      huniq _ hWX
    have h2 : (1 : Matrix.specialUnitaryGroup (Fin p) ℂ) = U := by
      refine huniq _ ?_
      simp
    exact hWne (by rw [show W = ((⟨W, hWmem⟩ : Matrix.specialUnitaryGroup (Fin p) ℂ) :
      Matrix (Fin p) (Fin p) ℂ) from rfl, h1, ← h2]; rfl)
  tfae_finish

end Classification

end GaloisForLFunctions.HTGeometry
