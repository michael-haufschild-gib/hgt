import GaloisForLFunctions.HTGeometry.PaperFormalPolynomialLocus

/-!
# The maximal terminating algebra of a derivation

The polynomial-valued locus of the formal flow is a subalgebra. The ambient
derivation restricts to a locally nilpotent derivation on this algebra, and
the source integrates it to a polynomial additive action. Every compatible
locally nilpotent subalgebra is contained in this one.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

variable {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]

/-- The entire polynomial locus, without choosing finite coordinates or a degree bound. -/
def paperTerminatingCore (D : Derivation k A A) : Subalgebra k A where
  carrier := {a | ∃ P : Polynomial A, paperFormalExponential D a = (P : PowerSeries A)}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro a b ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, by rw [map_add, hP, hQ, Polynomial.coe_add]⟩
  mul_mem' := by
    rintro a b ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P * Q, by rw [map_mul, hP, hQ, Polynomial.coe_mul]⟩
  algebraMap_mem' c := ⟨Polynomial.C (algebraMap k A c), by
    rw [AlgHom.commutes, PowerSeries.algebraMap_apply, Polynomial.coe_C]⟩

/-- Membership has exactly the expected finite-iterate meaning. -/
theorem paperTerminatingCore_mem_iff (D : Derivation k A A) (a : A) :
    a ∈ paperTerminatingCore D ↔ ∃ n : ℕ, (D : A → A)^[n] a = 0 :=
  paperFormalExponential_polynomial_iff D a

/-- The full ambient ring is recovered exactly for locally nilpotent derivations. -/
theorem paperTerminatingCore_eq_top_iff (D : Derivation k A A) :
    paperTerminatingCore D = ⊤ ↔ IsLocallyNilpotent D := by
  constructor
  · intro h a
    apply (paperTerminatingCore_mem_iff D a).mp
    rw [h]
    trivial
  · intro h
    apply le_antisymm le_top
    intro a _
    exact (paperTerminatingCore_mem_iff D a).mpr (h a)

/-- Differentiating a terminating element preserves termination. -/
theorem paperTerminatingCore_derivation_mem (D : Derivation k A A) {a : A}
    (ha : a ∈ paperTerminatingCore D) : D a ∈ paperTerminatingCore D := by
  obtain ⟨n, hn⟩ := (paperTerminatingCore_mem_iff D a).mp ha
  apply (paperTerminatingCore_mem_iff D (D a)).mpr
  refine ⟨n, ?_⟩
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hn, map_zero]

/-- Restrict the actual ambient derivation to its maximal terminating algebra. -/
def paperTerminatingClock (D : Derivation k A A) :
    Derivation k (paperTerminatingCore D) (paperTerminatingCore D) where
  toFun a := ⟨D a, paperTerminatingCore_derivation_mem D a.property⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)
  map_one_eq_zero' := Subtype.ext (by simp)
  leibniz' a b := Subtype.ext (by simp)

@[simp] theorem paperTerminatingClock_coe (D : Derivation k A A)
    (a : paperTerminatingCore D) :
    (paperTerminatingClock D a : A) = D (a : A) := rfl

/-- Restriction agrees with every ambient iterate, not only the first derivative. -/
theorem paperTerminatingClock_iterate_coe (D : Derivation k A A)
    (a : paperTerminatingCore D) (n : ℕ) :
    ((paperTerminatingClock D)^[n] a : A) = (D : A → A)^[n] (a : A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', paperTerminatingClock_coe, ih,
        Function.iterate_succ_apply']

/-- Local nilpotence on the core is proved from its construction. -/
theorem paperTerminatingClock_locallyNilpotent (D : Derivation k A A) :
    IsLocallyNilpotent (paperTerminatingClock D) := by
  intro a
  obtain ⟨n, hn⟩ := (paperTerminatingCore_mem_iff D (a : A)).mp a.property
  refine ⟨n, Subtype.ext ?_⟩
  rw [paperTerminatingClock_iterate_coe]
  exact hn

/-- Every compatible locally nilpotent subalgebra lies in the constructed core. -/
theorem paperTerminatingCore_maximal (D : Derivation k A A) (B : Subalgebra k A)
    (E : Derivation k B B) (hE : IsLocallyNilpotent E)
    (h : ∀ a : B, D (a : A) = (E a : A)) : B ≤ paperTerminatingCore D := by
  intro a ha
  obtain ⟨n, hn⟩ := hE ⟨a, ha⟩
  apply (paperTerminatingCore_mem_iff D a).mpr
  refine ⟨n, ?_⟩
  have he := derivation_iterate_naturality E D B.val h n ⟨a, ha⟩
  rw [hn, map_zero] at he
  exact he

/-- The source integrates the core clock without any ambient local-nilpotence assumption. -/
def paperTerminatingAction (D : Derivation k A A) :
    PolynomialAdditiveAction k (paperTerminatingCore D) :=
  exponentialAction (paperTerminatingClock D) (paperTerminatingClock_locallyNilpotent D)

/-- The polynomial core action is the restriction of the complete ambient formal flow. -/
theorem paperTerminatingAction_formal (D : Derivation k A A)
    (a : paperTerminatingCore D) :
    paperFormalExponential D (a : A) =
      PowerSeries.map (paperTerminatingCore D).val.toRingHom
        ((paperTerminatingAction D).toAlgHom a : PowerSeries (paperTerminatingCore D)) := by
  have he := paperFormalExponential_naturality (paperTerminatingClock D) D
    (paperTerminatingCore D).val (fun b => (paperTerminatingClock_coe D b).symm) a
  rw [paperFormalExponential_eq_additiveAction (paperTerminatingClock D)
    (paperTerminatingClock_locallyNilpotent D) a] at he
  exact he

end

end GaloisForLFunctions.HTGeometry
