import Mathlib.Algebra.Exact.Basic
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Cofinite divisor splitting for Deninger arithmetic cohomology

For a set `S` of retained prime coordinates, the generic finitely supported
divisor module splits into coordinates inside and outside `S`.  Restriction
to the outside coordinates is surjective, extension from the inside
coordinates is injective, and the resulting sequence is exact.

After unique factorization identifies positive rational numbers with
finitely supported integral prime valuations, this is the algebraic core of
the divisor sequence on `Spec ℤ[S⁻¹]`.  It is independent of zeta zeros, RH,
numerical computation, and any quotient-stack comparison.
-/

namespace RHTower

universe u v

section CofiniteDivisorSplitting

variable {R : Type u} {ι : Type v} [CommRing R]
variable (S : ι → Prop)

/-- Prime coordinates retained by the cofinite open. -/
abbrev DeningerInsidePrime := {i : ι // S i}

/-- Prime coordinates occurring as residues on the cofinite open. -/
abbrev DeningerOutsidePrime := {i : ι // ¬ S i}

/-- Extension by zero from retained prime coordinates to all prime
coordinates. -/
noncomputable def deningerInsideDivisorEmbedding :
    (DeningerInsidePrime S →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.lmapDomain R R
    ((↑) : DeningerInsidePrime S → ι)

/-- Restriction of a generic divisor to residue coordinates outside the
retained set. -/
noncomputable def deningerOutsideResidue :
    (ι →₀ R) →ₗ[R] (DeningerOutsidePrime S →₀ R) :=
  Finsupp.lcomapDomain
    ((↑) : DeningerOutsidePrime S → ι) Subtype.val_injective

/-- Extension by zero gives a canonical section of the outside-residue
map. -/
noncomputable def deningerOutsideResidueSection :
    (DeningerOutsidePrime S →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.lmapDomain R R
    ((↑) : DeningerOutsidePrime S → ι)

@[simp]
theorem deningerOutsideResidue_section
    (x : DeningerOutsidePrime S →₀ R) :
    deningerOutsideResidue (R := R) S
        (deningerOutsideResidueSection (R := R) S x) = x := by
  exact Finsupp.leftInverse_lcomapDomain_mapDomain
    (R := R) (M := R)
    ((↑) : DeningerOutsidePrime S → ι) Subtype.val_injective x

/-- Every finitely supported outside residue profile has a generic divisor
lift, by extension by zero. -/
theorem deningerOutsideResidue_surjective :
    Function.Surjective (deningerOutsideResidue (R := R) S) := by
  intro x
  exact ⟨deningerOutsideResidueSection (R := R) S x,
    deningerOutsideResidue_section (R := R) S x⟩

/-- Extension by zero from the retained coordinates is injective. -/
theorem deningerInsideDivisorEmbedding_injective :
    Function.Injective (deningerInsideDivisorEmbedding (R := R) S) := by
  intro x y h
  ext i
  have hi := congrArg (fun z : ι →₀ R => z i.1) h
  simpa [deningerInsideDivisorEmbedding, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_apply Subtype.val_injective] using hi

/-- The kernel of restriction to outside residues consists exactly of
divisors supported on the retained prime coordinates. -/
theorem deningerCofiniteDivisor_exact :
    Function.Exact
      (deningerInsideDivisorEmbedding (R := R) S)
      (deningerOutsideResidue (R := R) S) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    let y : DeningerInsidePrime S →₀ R :=
      Finsupp.lcomapDomain (R := R) (M := R)
        ((↑) : DeningerInsidePrime S → ι) Subtype.val_injective x
    refine ⟨y, ?_⟩
    ext i
    by_cases hi : S i
    · change
        Finsupp.mapDomain
            ((↑) : DeningerInsidePrime S → ι) y
            ((⟨i, hi⟩ : DeningerInsidePrime S) : ι) =
          x i
      rw [Finsupp.mapDomain_apply Subtype.val_injective]
      simp [y, Finsupp.lcomapDomain_apply]
    · have hxi : x i = 0 := by
        have h := congrArg
          (fun z : DeningerOutsidePrime S →₀ R => z ⟨i, hi⟩) hx
        simpa [deningerOutsideResidue,
          Finsupp.lcomapDomain_apply] using h
      rw [hxi]
      simp [deningerInsideDivisorEmbedding, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_notin_range, hi]
  · rintro ⟨y, rfl⟩
    ext i
    simp [deningerInsideDivisorEmbedding, deningerOutsideResidue,
      Finsupp.lmapDomain_apply, Finsupp.lcomapDomain_apply,
      Finsupp.mapDomain_notin_range, i.property]

/-- Consecutive maps in the cofinite divisor resolution compose to zero. -/
theorem deningerOutsideResidue_comp_insideDivisorEmbedding :
    (deningerOutsideResidue (R := R) S).comp
        (deningerInsideDivisorEmbedding (R := R) S) = 0 := by
  apply LinearMap.ext
  intro x
  exact (deningerCofiniteDivisor_exact (R := R) S).apply_apply_eq_zero x

end CofiniteDivisorSplitting

section FixedPrimeEulerClass

/-- Integral divisor subgroup supported on one ordinary prime. -/
abbrev FixedPrimeKernel (p : Nat.Primes) :=
  DeningerInsidePrime (fun q : Nat.Primes => q = p) →₀ ℤ

/-- Integral divisor group away from one ordinary prime. -/
abbrev FixedPrimeQuotient (p : Nat.Primes) :=
  DeningerOutsidePrime (fun q : Nat.Primes => q = p) →₀ ℤ

/-- The fixed-prime divisor sequence as an additive group extension. -/
noncomputable def deningerFixedPrimeExtension (p : Nat.Primes) :
    AddGroupExtension (FixedPrimeKernel p) (Nat.Primes →₀ ℤ) (FixedPrimeQuotient p) where
  inl := (deningerInsideDivisorEmbedding (R := ℤ) (fun q : Nat.Primes => q = p)).toAddMonoidHom
  rightHom := (deningerOutsideResidue (R := ℤ) (fun q : Nat.Primes => q = p)).toAddMonoidHom
  inl_injective := deningerInsideDivisorEmbedding_injective (R := ℤ) _
  range_inl_eq_ker_rightHom := by
    ext x
    change x ∈ LinearMap.range _ ↔ x ∈ LinearMap.ker _
    rw [LinearMap.exact_iff.mp (deningerCofiniteDivisor_exact (R := ℤ) _)]
  rightHom_surjective := deningerOutsideResidue_surjective (R := ℤ) _

/-- Extension by zero away from `p` is a canonical homomorphic splitting. -/
noncomputable def deningerFixedPrimeSplitting (p : Nat.Primes) :
    (deningerFixedPrimeExtension p).Splitting where
  __ := (deningerOutsideResidueSection (R := ℤ)
    (fun q : Nat.Primes => q = p)).toAddMonoidHom
  rightInverse_rightHom := deningerOutsideResidue_section (R := ℤ) _

/-- The one-prime divisor kernel is canonically the additive group `ℤ`. -/
noncomputable def fixedPrimeKernelEquivInt (p : Nat.Primes) :
    FixedPrimeKernel p ≃+ ℤ where
  toFun x := x ⟨p, rfl⟩
  invFun z := Finsupp.single ⟨p, rfl⟩ z
  left_inv x := by
    apply Finsupp.ext
    intro q
    have hq : q = ⟨p, rfl⟩ := Subtype.ext q.property
    subst q
    simp
  right_inv z := by simp
  map_add' x y := by simp

/-- Factor-set defect of the canonical fixed-prime section. -/
noncomputable def fixedPrimeSectionDefect (p : Nat.Primes)
    (g h : FixedPrimeQuotient p) : FixedPrimeKernel p :=
  Function.invFun (deningerFixedPrimeExtension p).inl
    (deningerFixedPrimeSplitting p g + deningerFixedPrimeSplitting p h -
      deningerFixedPrimeSplitting p (g + h))

/-- A homomorphic section has identically zero factor-set defect. -/
theorem fixedPrimeSectionDefect_eq_zero (p : Nat.Primes)
    (g h : FixedPrimeQuotient p) : fixedPrimeSectionDefect p g h = 0 := by
  have hinv := Function.leftInverse_invFun
    (deningerFixedPrimeExtension p).inl_injective (0 : FixedPrimeKernel p)
  simpa [fixedPrimeSectionDefect] using hinv

/-- Integral Euler factor set associated to the fixed-prime extension. -/
noncomputable def fixedPrimeEulerFactor (p : Nat.Primes) :
    Multiplicative (FixedPrimeQuotient p) × Multiplicative (FixedPrimeQuotient p) → ℤ :=
  fun gh => fixedPrimeKernelEquivInt p
    (fixedPrimeSectionDefect p gh.1.toAdd gh.2.toAdd)

@[simp]
theorem fixedPrimeEulerFactor_eq_zero (p : Nat.Primes)
    (g h : Multiplicative (FixedPrimeQuotient p)) :
    fixedPrimeEulerFactor p (g, h) = 0 := by
  simp [fixedPrimeEulerFactor, fixedPrimeSectionDefect_eq_zero]

/-- The factor set as a degree-two cocycle with trivial integral coefficients. -/
noncomputable def fixedPrimeEulerCocycle (p : Nat.Primes) :
    groupCohomology.cocycles₂
      (Rep.trivial ℤ (Multiplicative (FixedPrimeQuotient p)) ℤ) := by
  refine ⟨fixedPrimeEulerFactor p, ?_⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  simp

theorem fixedPrimeEulerCocycle_eq_zero (p : Nat.Primes) :
    fixedPrimeEulerCocycle p = 0 := by
  ext g h
  exact fixedPrimeEulerFactor_eq_zero p g h

/-- Fixed-prime extension/Euler class in mathlib's group cohomology. -/
noncomputable def fixedPrimeEulerClass (p : Nat.Primes) :
    groupCohomology.H2
      (Rep.trivial ℤ (Multiplicative (FixedPrimeQuotient p)) ℤ) :=
  groupCohomology.H2π _ (fixedPrimeEulerCocycle p)

/-- The split fixed-prime extension has zero Euler class. -/
theorem fixedPrimeEulerClass_eq_zero (p : Nat.Primes) :
    fixedPrimeEulerClass p = 0 := by
  rw [fixedPrimeEulerClass, fixedPrimeEulerCocycle_eq_zero]
  exact map_zero _

/-- Every trivial-coefficient pushforward of the fixed-prime Euler class remains zero. -/
theorem fixedPrimeEulerClass_pushforward_eq_zero
    (p : Nat.Primes) {M : Type} [AddCommGroup M] [Module ℤ M]
    (φ : Rep.res (MonoidHom.id (Multiplicative (FixedPrimeQuotient p)))
        (Rep.trivial ℤ (Multiplicative (FixedPrimeQuotient p)) ℤ) ⟶
      Rep.trivial ℤ (Multiplicative (FixedPrimeQuotient p)) M) :
    groupCohomology.map (MonoidHom.id (Multiplicative (FixedPrimeQuotient p))) φ 2
        (fixedPrimeEulerClass p) = 0 := by
  rw [fixedPrimeEulerClass_eq_zero]
  exact map_zero _

end FixedPrimeEulerClass

end RHTower
