import GaloisForLFunctions.RHTower.DeningerDynSysCharacterPoints
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The class of characters with finite kernel

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §4.

The smallest of the classes of characters used in the paper is `E_f`, consisting of the characters
`χ : κˣ → Cˣ` with finite kernel.  It is an admissible class in the sense of Definition 4.1: it is
invariant under precomposition with a field isomorphism, and `ker (χ ^ ν)` is finite exactly when
`ker χ` is, because `ker (χ ^ ν) / ker χ` embeds into the finite group of `ν`-th roots of unity of
`C`.

Since `E_f` contains every injective character, Corollary 4.4 applies to it; this exhibits a
concrete admissible class for which the projection `X̂ (C)_E → X` is surjective.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory Cardinal

universe u

variable {C : Type u} [Field C]

/-- The kernel of `χ ^ ν` maps to the `ν`-th roots of unity of `C` with kernel `ker χ`. -/
theorem deningerKerPow_quotient_finite {k : Type*} [Field k] (χ : kˣ →* Cˣ) {ν : ℕ}
    (hν : 0 < ν) :
    Finite (MonoidHom.ker (χ ^ ν) ⧸
      ((MonoidHom.ker χ).subgroupOf (MonoidHom.ker (χ ^ ν)))) := by
  classical
  have hle : MonoidHom.ker χ ≤ MonoidHom.ker (χ ^ ν) := by
    intro y hy
    have hy' : χ y = 1 := hy
    show (χ ^ ν) y = 1
    have hpow : (χ ^ ν) y = χ y ^ ν := by simp
    rw [hpow, hy', one_pow]
  -- the induced map to the roots of unity of `C`
  let f : MonoidHom.ker (χ ^ ν) →* Cˣ := χ.comp (MonoidHom.ker (χ ^ ν)).subtype
  have hfker : MonoidHom.ker f = (MonoidHom.ker χ).subgroupOf (MonoidHom.ker (χ ^ ν)) := by
    ext y
    constructor
    · intro hy
      exact hy
    · intro hy
      exact hy
  have hrange : ∀ y : MonoidHom.ker (χ ^ ν), f y ∈ rootsOfUnity ν C := by
    intro y
    rw [mem_rootsOfUnity]
    have hy : (χ ^ ν) (y : kˣ) = 1 := y.2
    have hy' : χ (y : kˣ) ^ ν = 1 := by
      have hpow : (χ ^ ν) (y : kˣ) = χ (y : kˣ) ^ ν := by simp
      rwa [hpow] at hy
    exact hy'
  have : Finite (rootsOfUnity ν C) := by
    haveI : NeZero ν := ⟨hν.ne'⟩
    infer_instance
  refine Finite.of_injective
    (fun z : MonoidHom.ker (χ ^ ν) ⧸ ((MonoidHom.ker χ).subgroupOf (MonoidHom.ker (χ ^ ν))) =>
      (⟨f (Quotient.out z), hrange _⟩ : rootsOfUnity ν C)) ?_
  intro z w hzw
  have hf : f (Quotient.out z) = f (Quotient.out w) := congrArg Subtype.val hzw
  have hmem : (Quotient.out z)⁻¹ * Quotient.out w ∈ MonoidHom.ker f := by
    show f ((Quotient.out z)⁻¹ * Quotient.out w) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  rw [hfker] at hmem
  have := (QuotientGroup.eq (s := (MonoidHom.ker χ).subgroupOf (MonoidHom.ker (χ ^ ν)))).2 hmem
  simpa using this

/-- **Deninger, §4.**  `ker (χ ^ ν)` is finite exactly when `ker χ` is. -/
theorem deningerKer_pow_finite_iff {k : Type*} [Field k] (χ : kˣ →* Cˣ) {ν : ℕ} (hν : 0 < ν) :
    Finite (MonoidHom.ker (χ ^ ν)) ↔ Finite (MonoidHom.ker χ) := by
  classical
  have hle : MonoidHom.ker χ ≤ MonoidHom.ker (χ ^ ν) := by
    intro y hy
    have hy' : χ y = 1 := hy
    show (χ ^ ν) y = 1
    have hpow : (χ ^ ν) y = χ y ^ ν := by simp
    rw [hpow, hy', one_pow]
  constructor
  · intro h
    refine Finite.of_injective (fun y : MonoidHom.ker χ => (⟨(y : kˣ), hle y.2⟩ :
      MonoidHom.ker (χ ^ ν))) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z : MonoidHom.ker (χ ^ ν) => (z : kˣ)) hab)
  · intro h
    haveI := deningerKerPow_quotient_finite (C := C) χ hν
    haveI : Finite ((MonoidHom.ker χ).subgroupOf (MonoidHom.ker (χ ^ ν))) :=
      Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hle).symm.toEquiv
    exact Finite.of_equiv _
      (Subgroup.groupEquivQuotientProdSubgroup
        (s := (MonoidHom.ker χ).subgroupOf (MonoidHom.ker (χ ^ ν)))).symm

/-- **Deninger, §4.**  The admissible class `E_f` of characters with finite kernel. -/
def deningerFiniteKernelClass (C : Type u) [Field C] (N₀ : Submonoid ℕ) :
    DeningerAdmissibleClass C N₀ where
  mem {k} _ χ := Finite (MonoidHom.ker χ)
  comp_iff {k l} _ _ σ χ := by
    constructor
    · intro h
      refine Finite.of_injective
        (fun y : MonoidHom.ker (χ.comp (Units.map (σ : k →* l))) =>
          (⟨Units.map (σ : k →* l) (y : kˣ), y.2⟩ : MonoidHom.ker χ)) ?_
      intro a b hab
      have h1 : Units.map (σ : k →* l) (a : kˣ) = Units.map (σ : k →* l) (b : kˣ) :=
        congrArg Subtype.val hab
      refine Subtype.ext (Units.ext ?_)
      have := congrArg (fun u : lˣ => (u : l)) h1
      simpa using σ.injective this
    · intro h
      refine Finite.of_injective
        (fun y : MonoidHom.ker χ =>
          (⟨Units.map ((σ.symm : l ≃+* k) : l →* k) (y : lˣ), ?_⟩ :
            MonoidHom.ker (χ.comp (Units.map (σ : k →* l))))) ?_
      · show χ (Units.map (σ : k →* l) (Units.map ((σ.symm : l ≃+* k) : l →* k) (y : lˣ))) = 1
        have : Units.map (σ : k →* l) (Units.map ((σ.symm : l ≃+* k) : l →* k) (y : lˣ))
            = (y : lˣ) := by
          refine Units.ext ?_
          simp
        rw [this]
        exact y.2
      · intro a b hab
        have h1 : Units.map ((σ.symm : l ≃+* k) : l →* k) (a : lˣ)
            = Units.map ((σ.symm : l ≃+* k) : l →* k) (b : lˣ) := congrArg Subtype.val hab
        refine Subtype.ext (Units.ext ?_)
        have := congrArg (fun u : kˣ => (u : k)) h1
        simpa using σ.symm.injective this
  pow_iff {k} _ χ ν _ hν := (deningerKer_pow_finite_iff (C := C) χ hν).symm

/-- **Deninger, §4.**  Every injective character has finite kernel, so `E_f` contains all of
them. -/
theorem deningerFiniteKernelClass_mem_of_injective {N₀ : Submonoid ℕ} {k : Type u} [Field k]
    (χ : kˣ →* Cˣ) (hχ : Function.Injective χ) :
    (deningerFiniteKernelClass C N₀).mem χ := by
  have : MonoidHom.ker χ = ⊥ := (MonoidHom.ker_eq_bot_iff χ).2 hχ
  rw [show (deningerFiniteKernelClass C N₀).mem χ = Finite (MonoidHom.ker χ) from rfl, this]
  infer_instance

/-- **Deninger, Corollary 4.4 (`t4ka`), for the class `E_f`.**  The projection to `X` is
surjective on the character points with finite kernel. -/
theorem deningerFiniteKernelClass_fst_surjective {N₀ : Submonoid ℕ} {X : Scheme.{u}}
    [IsAlgClosed C] (hne : ∃ x : Cˣ, x ∉ CommGroup.torsion Cˣ)
    (hcard : ∀ x : X, #(X.residueField x) ≤ #C)
    (hchar : ∀ x : X, ringChar C = 0 ∨ ringChar (X.residueField x) = ringChar C) (x : X) :
    ∃ P ∈ deningerCharPointsIn (deningerFiniteKernelClass C N₀) X, P.1 = x :=
  deningerCharPointsIn_fst_surjective _ (fun χ hχ =>
    deningerFiniteKernelClass_mem_of_injective χ hχ) hne hcard hchar x

end RHTower
