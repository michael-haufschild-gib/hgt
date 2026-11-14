import GaloisForLFunctions.RepresentationLifting.QuadraticNaturality
import GaloisForLFunctions.RepresentationLifting.RepresentationExt
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# The characteristic-two quadratic two-extension

Every finite matrix representation gives the exact sequence
`0 → W⁽¹⁾ → Sym² W → W ⊗ W → Sym² W → 0`.
The middle image consists of symmetric matrices with zero diagonal. Splitting
at that image gives two short exact sequences and their Yoneda product in Ext².
The product commutes with group restriction and vanishes in dimension at most one.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry
universe u
variable {k G ι : Type u} [CommRing k] [CharP k 2] [Group G] [Fintype ι] [LinearOrder ι]

/-- The action on unordered quadratic coefficients. -/
def quadraticSymmetricRepresentation (ρ : G →* Matrix ι ι k) :
    Representation k G (Sym2 ι → k) where
  toFun g := Matrix.toLin' (symmetricSquareMatrixGeneral (ρ g))
  map_one' := by
    apply LinearMap.ext
    intro q
    obtain ⟨T, rfl⟩ := tensorProjection_surjective q
    change (symmetricSquareMatrixGeneral (ρ 1)).mulVec (tensorProjection T) = tensorProjection T
    rw [map_one, ← tensorProjection_intertwines]
    simp only [tensorSquareAction, LinearMap.coe_mk, AddHom.coe_mk, one_mul,
      Matrix.transpose_one, mul_one]
  map_mul' g h := by
    rw [map_mul, symmetricSquareMatrixGeneral_mul, Matrix.toLin'_mul]
    rfl

/-- The tensor-square action, written as matrix congruence. -/
def quadraticTensorRepresentation (ρ : G →* Matrix ι ι k) :
    Representation k G (Matrix ι ι k) where
  toFun g := tensorSquareAction (ρ g)
  map_one' := by
    apply LinearMap.ext
    intro T
    change ρ 1 * T * (ρ 1).transpose = T
    rw [map_one, one_mul, Matrix.transpose_one, mul_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro T
    change ρ (g * h) * T * (ρ (g * h)).transpose =
      ρ g * (ρ h * T * (ρ h).transpose) * (ρ g).transpose
    rw [map_mul, Matrix.transpose_mul]
    simp only [mul_assoc]

/-- The Frobenius twist obtained by squaring every action coefficient. -/
def quadraticFrobeniusRepresentation (ρ : G →* Matrix ι ι k) :
    Representation k G (ι → k) where
  toFun g := Matrix.toLin' ((ρ g).map (frobenius k 2))
  map_one' := by
    have hone : (1 : Matrix ι ι k).map (frobenius k 2) = 1 :=
      (frobenius k 2).mapMatrix.map_one
    rw [map_one, hone, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

/-- Pure squares form an equivariant copy of the Frobenius twist. -/
def quadraticSquareInclusion (ρ : G →* Matrix ι ι k) :
    Rep.of (quadraticFrobeniusRepresentation ρ) ⟶ Rep.of (quadraticSymmetricRepresentation ρ) :=
  Rep.ofHom ⟨squareDiagonal, fun g => by
    apply LinearMap.ext
    intro x
    exact (squareDiagonal_intertwines (ρ g) x).symm⟩

/-- Tensor multiplication maps onto the symmetric square. -/
def quadraticTensorProjection (ρ : G →* Matrix ι ι k) :
    Rep.of (quadraticTensorRepresentation ρ) ⟶ Rep.of (quadraticSymmetricRepresentation ρ) :=
  Rep.ofHom ⟨tensorProjection, fun g => by
    apply LinearMap.ext
    intro T
    exact tensorProjection_intertwines (ρ g) T⟩

/-- The polarization image: symmetric coefficient matrices with zero diagonal. -/
def quadraticMiddle : Submodule k (Matrix ι ι k) := LinearMap.ker tensorProjection

omit [CharP k 2] [Fintype ι] in
theorem quadraticNorm_square (x : ι → k) : tensorNorm (squareDiagonal x) = 0 := by
  have h : squareDiagonal x ∈ LinearMap.range (squareDiagonal (ι := ι) (R := k)) := ⟨x, rfl⟩
  rw [range_squareDiagonal] at h
  exact h

omit [Fintype ι] in
theorem quadraticProjection_norm (q : Sym2 ι → k) : tensorProjection (tensorNorm q) = 0 := by
  have h : tensorNorm q ∈ LinearMap.range (tensorNorm (ι := ι) (R := k)) := ⟨q, rfl⟩
  rw [range_tensorNorm] at h
  exact h

/-- Congruence preserves the polarization image. -/
def quadraticMiddleRepresentation (ρ : G →* Matrix ι ι k) :
    Representation k G (quadraticMiddle (k := k) (ι := ι)) where
  toFun g :=
    { toFun T := ⟨tensorSquareAction (ρ g) T.1, by
        change tensorProjection (tensorSquareAction (ρ g) T.1) = 0
        rw [tensorProjection_intertwines, T.2, Matrix.mulVec_zero]⟩
      map_add' T U := Subtype.ext (map_add (tensorSquareAction (ρ g)) T.1 U.1)
      map_smul' c T := Subtype.ext (map_smul (tensorSquareAction (ρ g)) c T.1) }
  map_one' := by
    apply LinearMap.ext
    intro T
    apply Subtype.ext
    change quadraticTensorRepresentation ρ 1 T.1 = T.1
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro T
    apply Subtype.ext
    exact LinearMap.congr_fun ((quadraticTensorRepresentation ρ).map_mul g h) T.1

/-- Polarization with its codomain restricted to its image. -/
def quadraticNormToMiddle : (Sym2 ι → k) →ₗ[k] quadraticMiddle (k := k) (ι := ι) where
  toFun q := ⟨tensorNorm q, quadraticProjection_norm q⟩
  map_add' q r := Subtype.ext (map_add tensorNorm q r)
  map_smul' c q := Subtype.ext (map_smul tensorNorm c q)

/-- The equivariant polarization map. -/
def quadraticNormHom (ρ : G →* Matrix ι ι k) :
    Rep.of (quadraticSymmetricRepresentation ρ) ⟶ Rep.of (quadraticMiddleRepresentation ρ) :=
  Rep.ofHom ⟨quadraticNormToMiddle, fun g => by
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact tensorNorm_intertwines (ρ g) q⟩

/-- The polarization image embeds in the tensor square. -/
def quadraticMiddleInclusion (ρ : G →* Matrix ι ι k) :
    Rep.of (quadraticMiddleRepresentation ρ) ⟶ Rep.of (quadraticTensorRepresentation ρ) :=
  Rep.ofHom ⟨(quadraticMiddle (k := k) (ι := ι)).subtype, fun _ => rfl⟩

/-- The pure-square kernel and polarization quotient sequence. -/
def quadraticFirstSequence (ρ : G →* Matrix ι ι k) : ShortComplex (Rep k G) :=
  ShortComplex.mk (quadraticSquareInclusion ρ) (quadraticNormHom ρ) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact quadraticNorm_square x)

/-- The polarization kernel and tensor-multiplication quotient sequence. -/
def quadraticSecondSequence (ρ : G →* Matrix ι ι k) : ShortComplex (Rep k G) :=
  ShortComplex.mk (quadraticMiddleInclusion ρ) (quadraticTensorProjection ρ) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact x.2)

/-- The kernel of polarization is exactly the pure-square subrepresentation. -/
theorem quadraticFirstSequence_shortExact (ρ : G →* Matrix ι ι k) :
    (quadraticFirstSequence ρ).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range squareDiagonal = LinearMap.ker (quadraticNormToMiddle (k := k) (ι := ι))
    rw [range_squareDiagonal]
    ext q
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg Subtype.val h
  · rw [Rep.mono_iff_injective]
    exact squareDiagonal_injective
  · rw [Rep.epi_iff_surjective]
    intro T
    have h : T.1 ∈ LinearMap.range (tensorNorm (ι := ι) (R := k)) := by
      rw [range_tensorNorm]
      exact T.2
    obtain ⟨q, hq⟩ := h
    exact ⟨q, Subtype.ext hq⟩

omit [CharP k 2] in
/-- Tensor multiplication is surjective and has the prescribed middle kernel. -/
theorem quadraticSecondSequence_shortExact (ρ : G →* Matrix ι ι k) :
    (quadraticSecondSequence ρ).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (quadraticMiddle (k := k) (ι := ι)).subtype = LinearMap.ker tensorProjection
    ext T
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro h
      exact ⟨⟨T, h⟩, rfl⟩
  · rw [Rep.mono_iff_injective]
    exact Subtype.val_injective
  · rw [Rep.epi_iff_surjective]
    exact tensorProjection_surjective

/-- The Yoneda class of the characteristic-two quadratic two-extension. -/
def quadraticSequenceClass (ρ : G →* Matrix ι ι k) :
    Ext (Rep.of (quadraticSymmetricRepresentation ρ)) (Rep.of (quadraticFrobeniusRepresentation ρ)) 2 :=
  (quadraticSecondSequence_shortExact ρ).extClass.comp
    (quadraticFirstSequence_shortExact ρ).extClass rfl

/-- Read the pure-square coefficients; generally this map is not equivariant. -/
def quadraticDiagonalRead : (Sym2 ι → k) →ₗ[k] (ι → k) where
  toFun q i := q s(i, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharP k 2] [Fintype ι] in
theorem quadraticDiagonalRead_square (x : ι → k) :
    quadraticDiagonalRead (squareDiagonal x) = x := by
  funext i
  exact squareDiagonal_mk x i i |>.trans (if_pos rfl)

omit [CharP k 2] [Fintype ι] in
theorem square_quadraticDiagonalRead [Subsingleton ι] (q : Sym2 ι → k) :
    squareDiagonal (quadraticDiagonalRead q) = q := by
  funext a
  induction a with
  | _ i j =>
      have h : j = i := Subsingleton.elim _ _
      subst j
      simp only [squareDiagonal_mk, ↓reduceIte]
      rfl

/-- In dimension at most one, reading pure-square coefficients is equivariant. -/
def quadraticRankOneRetraction [Subsingleton ι] (ρ : G →* Matrix ι ι k) :
    Rep.of (quadraticSymmetricRepresentation ρ) ⟶ Rep.of (quadraticFrobeniusRepresentation ρ) :=
  Rep.ofHom ⟨quadraticDiagonalRead, fun g => by
    apply LinearMap.ext
    intro q
    apply squareDiagonal_injective
    change squareDiagonal (quadraticDiagonalRead ((symmetricSquareMatrixGeneral (ρ g)).mulVec q)) =
      squareDiagonal (((ρ g).map (fun a => a ^ 2)).mulVec (quadraticDiagonalRead q))
    rw [square_quadraticDiagonalRead, ← squareDiagonal_intertwines, square_quadraticDiagonalRead]⟩

theorem quadraticRankOneRetraction_inclusion [Subsingleton ι] (ρ : G →* Matrix ι ι k) :
    quadraticSquareInclusion ρ ≫ quadraticRankOneRetraction ρ = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact quadraticDiagonalRead_square x

/-- The quadratic two-extension is trivial in dimension at most one. -/
theorem quadraticSequenceClass_rankOne_zero [Subsingleton ι] (ρ : G →* Matrix ι ι k) :
    quadraticSequenceClass ρ = 0 := by
  have h : (quadraticFirstSequence_shortExact ρ).extClass = 0 :=
    (extClass_zero_iff_retraction _ _).mpr
      ⟨quadraticRankOneRetraction ρ, quadraticRankOneRetraction_inclusion ρ⟩
  unfold quadraticSequenceClass
  rw [h]
  exact Ext.comp_zero _ _ 1 2 rfl

/-- Pullback along any group homomorphism preserves the quadratic Yoneda class. -/
theorem quadraticSequenceClass_restriction {H : Type u} [Group H]
    (ρ : G →* Matrix ι ι k) (f : H →* G) :
    (quadraticSequenceClass ρ).mapExactFunctor (Rep.resFunctor f) =
      quadraticSequenceClass (ρ.comp f) := by
  unfold quadraticSequenceClass
  have h₁ : (quadraticFirstSequence_shortExact ρ).extClass.mapExactFunctor
      (Rep.resFunctor f) = (quadraticFirstSequence_shortExact (ρ.comp f)).extClass :=
    Ext.mapExactFunctor_extClass (Rep.resFunctor f) (quadraticFirstSequence_shortExact ρ)
  have h₂ : (quadraticSecondSequence_shortExact ρ).extClass.mapExactFunctor
      (Rep.resFunctor f) = (quadraticSecondSequence_shortExact (ρ.comp f)).extClass :=
    Ext.mapExactFunctor_extClass (Rep.resFunctor f) (quadraticSecondSequence_shortExact ρ)
  exact (Ext.mapExactFunctor_comp (Rep.resFunctor f) _ _ rfl).trans
    (congrArg₂ (fun (a : Ext (Rep.of (quadraticSymmetricRepresentation (ρ.comp f)))
        (Rep.of (quadraticMiddleRepresentation (ρ.comp f))) 1)
      (b : Ext (Rep.of (quadraticMiddleRepresentation (ρ.comp f)))
        (Rep.of (quadraticFrobeniusRepresentation (ρ.comp f))) 1) => a.comp b rfl) h₂ h₁)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.quadraticFirstSequence_shortExact
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSecondSequence_shortExact
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSequenceClass
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSequenceClass_rankOne_zero
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSequenceClass_restriction
