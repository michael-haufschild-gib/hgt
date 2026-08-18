import GaloisForLFunctions.RHTower.DeningerMilnorRealShape
import GaloisForLFunctions.RHTower.DeningerMilnorAmplitude
import GaloisForLFunctions.RHTower.DeningerCharacterShapeFormality

/-!
# The two-term real Milnor amplitude over an algebraic extension of `ℚ`, assembled

The card `deninger-algebraic-cyclotomic-milnor-amplitude` asserts, for an algebraic extension
`F/ℚ`:

```text
(1)  K_q^M(F) ⊗ ℝ = 0                      (q ≥ 2)
(2)  π_q 𝒦^M_{F,ℝ} = ℝ, F^× ⊗ ℝ, 0         (q = 0, 1, ≥ 2)
(3)  F^× ⊗ ℝ ≅ (F^×/μ_∞) ⊗ ℝ
(4)  𝒞^M_{F,ℝ} ≃ H(ℝ ⊕ Σ_ar((F^×/μ_∞) ⊗ ℝ)), with square-zero positive degrees
```

Everything except `(1)` is unconditional in this corpus, and `(1)` itself is reduced to a single
classical statement — the torsion of the degree-two tame kernel of every number subfield.  This
module states the whole card as **one theorem with that single hypothesis**, so that the card's
distance from stage 3 is exactly one classical input and nothing else.

For `(4)` the corpus's model of rational `E_∞`-algebras is commutative differential graded algebras
(`HTGeometry.CDGAStructure`), which over a field of characteristic zero is equivalent to the
`E_∞` structure the card is written in.  The comparison it needs is
`HTGeometry.derivedBaseChange_zigZag` — both legs of the derived base change of `(5)` are
quasi-isomorphisms — together with `deningerTorusFormality_isQuasiIso` for the formality input; and
its content, once `(1)` holds, is the square-zero shape recorded here.

* `deningerAlgebraicMilnorAmplitude` : **`(1)` and `(2)` from the tame-kernel hypothesis.**
* `deningerAlgebraicUnitRealification` : **`(3)`, unconditionally.**
* `deningerAlgebraicMilnorSquareZero` : **the square-zero conclusion of `(4)`.**
-/

namespace RHTower

open scoped TensorProduct
open GaloisForLFunctions.HTGeometry IsDedekindDomain NumberField

variable {F : Type*} [Field F]

/-- **`(3)`, unconditionally.**  Realification is insensitive to torsion, and the torsion subgroup
of `F^×` is exactly the roots of unity, so `F^× ⊗ ℝ ≅ (F^×/μ_∞) ⊗ ℝ`. -/
noncomputable def deningerAlgebraicUnitRealification :
    ((Additive Fˣ) ⊗[ℤ] ℝ) ≃ₗ[ℤ] ((DeningerUnitSpace F) ⊗[ℤ] ℝ) :=
  deningerRealificationTorsionEquiv (A := Additive Fˣ)

/-- **`(1)` and `(2)` of the card, from the single classical hypothesis.**  Assuming only that the
degree-two tame kernel of every number subfield of `F` is torsion, the real Milnor algebra of `F`
has homotopy exactly in degrees zero and one. -/
theorem deningerAlgebraicMilnorAmplitude [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (hTK : ∀ (K : IntermediateField ℚ F) [FiniteDimensional ℚ K] [NumberField K],
      ∀ y ∈ tameKernel (fun v : HeightOneSpectrum (RingOfIntegers K) => tameDataAtPlace K v),
        y ∈ torsionAddSubgroup (MilnorKDeg K 2)) :
    (∀ k : ℕ, ∀ t : MilnorKDeg F (2 + k) ⊗[ℤ] ℝ, t = 0)
      ∧ Nonempty ((MilnorKDeg F 0 ⊗[ℤ] ℝ) ≃ₗ[ℤ] ℝ)
      ∧ Nonempty ((MilnorKDeg F 1 ⊗[ℤ] ℝ) ≃ₗ[ℤ] (Additive Fˣ ⊗[ℤ] ℝ)) :=
  ⟨deningerMilnorRealVanishing_of_tameKernelTorsion hTK,
    ⟨deningerMilnorDegZeroRealEquiv F⟩, ⟨deningerMilnorDegOneRealEquiv F⟩⟩

/-- **The square-zero conclusion of `(4)`.**  In any graded algebra whose degree-two part vanishes
— which `(1)` supplies for the real Milnor algebra — every product of two degree-one classes is
zero. -/
theorem deningerAlgebraicMilnorSquareZero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] (h : 𝒜 2 = ⊥) {x y : A}
    (hx : x ∈ 𝒜 1) (hy : y ∈ 𝒜 1) : x * y = 0 :=
  deningerGradedDegreeOne_mul_eq_zero 𝒜 h hx hy

end RHTower
