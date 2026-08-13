import GaloisForLFunctions.HTGeometry.ConstitutiveCentralAdmissionExchange
import GaloisForLFunctions.HTGeometry.ConstitutiveCompetitivePathVariation
import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern
import GaloisForLFunctions.HTGeometry.TateFractureObstructionBianchiAmplitudeLaw

/-!
# Canonical witnesses for structural proposition interfaces

These predicates describe chosen data and are not globally true.  The theorems below give their
canonical premise-free instances and exact transport boundary where one exists.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Admission -/

/-- The zero compensator is admitted by every additive observer. -/
theorem compensatorAdmitted_zero
    {M A B : Type*} [AddCommGroup A] [AddCommGroup B] (q : A →+ B) :
    CompensatorAdmitted q (fun _ _ : M => 0) := by
  intro x y
  simp

/-- The zero observer admits every compensator. -/
theorem compensatorAdmitted_zeroObserver
    {M A B : Type*} [AddCommGroup A] [AddCommGroup B] (κ : M → M → A) :
    CompensatorAdmitted (0 : A →+ B) κ := by
  intro x y
  simp

/-! ## Closed paths -/

/-- Close a finite path by returning to its first state. -/
def closeConstitutivePath {ι : Type*} : List ι → List ι
  | [] => []
  | i :: xs => i :: (xs ++ [i])

/-- Canonical path closure always produces a closed constitutive path. -/
theorem closeConstitutivePath_closed {ι : Type*} (xs : List ι) :
    ConstitutiveClosedPath (closeConstitutivePath xs) := by
  cases xs with
  | nil => trivial
  | cons i xs => simp [closeConstitutivePath, ConstitutiveClosedPath]

/-! ## Factorization -/

/-- Every observation factors through itself. -/
theorem factorsThrough_self {X Q : Type*} (π : X → Q) :
    FactorsThrough π π := by
  exact ⟨id, by simp⟩

/-- Every constant target factors through every observation. -/
theorem factorsThrough_const {X Q C : Type*} (π : X → Q) (c : C) :
    FactorsThrough π (fun _ => c) := by
  exact ⟨fun _ => c, rfl⟩

/-- Every target factors through the identity observation. -/
theorem factorsThrough_id {X C : Type*} (χ : X → C) :
    FactorsThrough id χ := by
  exact ⟨χ, by simp⟩

/-- For a surjective observation, factorization through the full codomain and through its attained
range are equivalent. -/
theorem factorsThrough_iff_factorsThroughRange_of_surjective
    {X Q C : Type*} (π : X → Q) (hπ : Function.Surjective π) (χ : X → C) :
    FactorsThrough π χ ↔ FactorsThroughRange π χ := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨fun q => d q.1, fun x => rfl⟩
  · rintro ⟨d, hd⟩
    let e : Q → C := fun q => d ⟨q, hπ q⟩
    refine ⟨e, ?_⟩
    funext x
    change χ x = d ⟨π x, hπ (π x)⟩
    exact (hd x).symm

/-! ## Boolean tail orientation -/

/-- Pointwise Boolean complement is eventually opposite with empty exceptional agreement set. -/
theorem primeOrientationsEventuallyOpposite_complement
    {P : Type*} (ε : P → Bool) :
    PrimeOrientationsEventuallyOpposite ε (fun p => !(ε p)) := by
  have hset : {p | ε p = !(ε p)} = (∅ : Set P) := by
    ext p
    cases ε p <;> simp
  rw [PrimeOrientationsEventuallyOpposite, hset]
  exact Set.finite_empty

/-! ## Vertical amplitude -/

/-- A componentwise subsingleton bigraded family has every vertical amplitude bound. -/
theorem hasVerticalAmplitude_of_subsingleton
    {A : ℤ → ℤ → Type*} (hA : ∀ p q, Subsingleton (A p q)) (a b : ℤ) :
    HasVerticalAmplitude A a b := by
  intro p q hout
  exact hA p q

/-- `PUnit` is an unconditional finite-amplitude family. -/
theorem hasVerticalAmplitude_punit (a b : ℤ) :
    HasVerticalAmplitude (fun _ _ => PUnit) a b :=
  hasVerticalAmplitude_of_subsingleton (fun _ _ => inferInstance) a b

/-- A componentwise subsingleton bundled family has every vertical amplitude bound. -/
theorem bundledHasVerticalAmplitude_of_subsingleton
    {k : Type*} [Ring k] {A : ℤ → ℤ → ModuleCat k}
    (hA : ∀ p q, Subsingleton (A p q)) (a b : ℤ) :
    BundledHasVerticalAmplitude A a b := by
  intro p q hout
  exact hA p q

/-- `PUnit` is also an unconditional bundled finite-amplitude family. -/
theorem bundledHasVerticalAmplitude_punit
    (k : Type*) [Ring k] (a b : ℤ) :
    BundledHasVerticalAmplitude (fun _ _ => ModuleCat.of k PUnit) a b :=
  bundledHasVerticalAmplitude_of_subsingleton (fun _ _ => inferInstance) a b

end GaloisForLFunctions.HTGeometry
