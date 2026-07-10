import GaloisForLFunctions.ParameterizedPrimitiveAction
import Mathlib.Order.Zorn

/-!
# Maximal affine differential ideals for additive primitive systems

For the additive unipotent PPV problem, the universal differential solution ring is the
differential-polynomial ring equipped with the affine semilinear actions constructed in
`ParameterizedPrimitiveAction`.  This file performs the Zorn step unconditionally: every proper
affine differential ideal is contained in a maximal proper affine differential ideal.

The proof uses the union property for a nonempty chain of ideals.  Directed suprema preserve
properness, derivation stability, and membership invariance under every affine automorphism.  The
specialized theorem starts from the actual relation ideal of a dependent compatible primitive
tuple.  What remains for the PPV telescoping theorem is the quotient/torsor construction,
preservation of joint constants, and the fixed-field/Galois correspondence.
-/

open scoped Differential

namespace GaloisForLFunctions
noncomputable section

/-- An ideal stable under the total derivation and invariant under every affine difference
automorphism associated to `a`. -/
def IsAffineDifferentialIdeal
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I : Ideal (DifferentialPolynomial κ K)) : Prop :=
  (∀ ⦃P : DifferentialPolynomial κ K⦄, P ∈ I →
      differentialPolynomialOverDerivation κ K P ∈ I) ∧
    ∀ i P, differentialPolynomialAffineHom S a i P ∈ I ↔ P ∈ I

theorem IsAffineDifferentialIdeal.derivation_mem
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    {S : CommutingDifferenceDifferentialField ι C K} {a : ι → κ → K}
    {I : Ideal (DifferentialPolynomial κ K)}
    (hI : IsAffineDifferentialIdeal S a I)
    {P : DifferentialPolynomial κ K} (hP : P ∈ I) :
    differentialPolynomialOverDerivation κ K P ∈ I :=
  hI.1 hP

theorem IsAffineDifferentialIdeal.affine_mem_iff
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    {S : CommutingDifferenceDifferentialField ι C K} {a : ι → κ → K}
    {I : Ideal (DifferentialPolynomial κ K)}
    (hI : IsAffineDifferentialIdeal S a I)
    (i : ι) (P : DifferentialPolynomial κ K) :
    differentialPolynomialAffineHom S a i P ∈ I ↔ P ∈ I :=
  hI.2 i P

/-- A nonempty chain of affine differential ideals has an affine differential ideal as its
supremum. -/
theorem isAffineDifferentialIdeal_sSup_of_chain
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (c : Set (Ideal (DifferentialPolynomial κ K)))
    (hcne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    (hstable : ∀ I ∈ c, IsAffineDifferentialIdeal S a I) :
    IsAffineDifferentialIdeal S a (sSup c) := by
  constructor
  · intro P hP
    obtain ⟨I, hIc, hPI⟩ :=
      (Submodule.mem_sSup_of_directed hcne hc.directedOn).mp hP
    exact le_sSup hIc ((hstable I hIc).derivation_mem hPI)
  · intro i P
    constructor
    · intro hP
      obtain ⟨I, hIc, hPI⟩ :=
        (Submodule.mem_sSup_of_directed hcne hc.directedOn).mp hP
      have hbase : P ∈ I := ((hstable I hIc).affine_mem_iff i P).mp hPI
      exact le_sSup hIc hbase
    · intro hP
      obtain ⟨I, hIc, hPI⟩ :=
        (Submodule.mem_sSup_of_directed hcne hc.directedOn).mp hP
      have haffine : differentialPolynomialAffineHom S a i P ∈ I :=
        ((hstable I hIc).affine_mem_iff i P).mpr hPI
      exact le_sSup hIc haffine

/-- The supremum of a nonempty chain of proper ideals remains proper. -/
theorem sSup_ne_top_of_chain_ne_top
    {R : Type*} [CommRing R]
    (c : Set (Ideal R)) (hcne : c.Nonempty) (hc : IsChain (· ≤ ·) c)
    (hproper : ∀ I ∈ c, I ≠ ⊤) :
    sSup c ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  intro hone
  obtain ⟨I, hIc, h1I⟩ :=
    (Submodule.mem_sSup_of_directed hcne hc.directedOn).mp hone
  have h1not : (1 : R) ∉ I := by
    simpa only [Ideal.ne_top_iff_one] using hproper I hIc
  exact h1not h1I

/-- Every proper affine differential ideal lies in a maximal proper affine differential ideal.
Maximality is relative to ideals carrying the same affine-differential stability, not to all ring
ideals. -/
theorem exists_maximal_affineDifferentialIdeal
    {ι κ C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) (a : ι → κ → K)
    (I₀ : Ideal (DifferentialPolynomial κ K))
    (hI₀proper : I₀ ≠ ⊤) (hI₀stable : IsAffineDifferentialIdeal S a I₀) :
    ∃ M : Ideal (DifferentialPolynomial κ K),
      I₀ ≤ M ∧ M ≠ ⊤ ∧ IsAffineDifferentialIdeal S a M ∧
      ∀ J : Ideal (DifferentialPolynomial κ K),
        M ≤ J → J ≠ ⊤ → IsAffineDifferentialIdeal S a J → J = M := by
  let good : Set (Ideal (DifferentialPolynomial κ K)) :=
    {I | I₀ ≤ I ∧ I ≠ ⊤ ∧ IsAffineDifferentialIdeal S a I}
  have hI₀good : I₀ ∈ good := ⟨le_rfl, hI₀proper, hI₀stable⟩
  have hchain : ∀ c, c ⊆ good → IsChain (· ≤ ·) c → c.Nonempty →
      ∃ ub ∈ good, ∀ I ∈ c, I ≤ ub := by
    intro c hcgood hc hcne
    refine ⟨sSup c, ?_, fun I hIc => le_sSup hIc⟩
    constructor
    · obtain ⟨I, hIc⟩ := hcne
      exact (hcgood hIc).1.trans (le_sSup hIc)
    constructor
    · exact sSup_ne_top_of_chain_ne_top c hcne hc fun I hIc => (hcgood hIc).2.1
    · exact isAffineDifferentialIdeal_sSup_of_chain S a c hcne hc
        fun I hIc => (hcgood hIc).2.2
  obtain ⟨M, hI₀M, hMmax⟩ := zorn_le_nonempty₀ good
    (fun c hcgood hc I hIc => hchain c hcgood hc ⟨I, hIc⟩) I₀ hI₀good
  refine ⟨M, hI₀M, hMmax.1.2.1, hMmax.1.2.2, ?_⟩
  intro J hMJ hJproper hJstable
  by_contra hJM
  have hstrict : M < J := lt_of_le_of_ne hMJ (Ne.symm hJM)
  exact hMmax.not_prop_of_gt hstrict ⟨hI₀M.trans hMJ, hJproper, hJstable⟩

/-- The actual relation ideal of a dependent compatible primitive system is contained in a maximal
proper affine differential ideal.  This is the maximal-invariant-ideal existence step of the
additive unipotent PPV construction, with no PPV existence or fixed-field axiom. -/
theorem dependent_compatiblePrimitiveSystem_exists_maximal_relationIdeal
    {ι κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (SK : CommutingDifferenceDifferentialField ι C K)
    (SL : CommutingDifferenceDifferentialField ι C L)
    (hσ : ∀ i x, SL.aut i (algebraMap K L x) = algebraMap K L (SK.aut i x))
    (y : κ → L) (a : ι → κ → K)
    (hsys : CompatiblePrimitiveExtensionSystem SL y a)
    (hdep : ¬ DifferentialIndependent K y) :
    ∃ M : Ideal (DifferentialPolynomial κ K),
      differentialRelationIdealOver (K := K) y ≤ M ∧
      M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsAffineDifferentialIdeal SK a M ∧
      ∀ J : Ideal (DifferentialPolynomial κ K),
        M ≤ J → J ≠ ⊤ → IsAffineDifferentialIdeal SK a J → J = M := by
  have hrel := dependent_compatiblePrimitiveSystem_relationIdeal
    SK SL hσ y a hsys hdep
  have hrelStable : IsAffineDifferentialIdeal SK a
      (differentialRelationIdealOver (K := K) y) := by
    constructor
    · exact hrel.2.2.1
    · intro i P
      exact differentialPolynomialAffineHom_mem_relationIdealOver_iff
        SK SL hσ y a hsys i P
  obtain ⟨M, hle, hMproper, hMstable, hMmax⟩ :=
    exists_maximal_affineDifferentialIdeal SK a
      (differentialRelationIdealOver (K := K) y) hrel.2.1 hrelStable
  refine ⟨M, hle, ?_, hMproper, hMstable, hMmax⟩
  intro hMbot
  apply hrel.1
  exact le_antisymm (hle.trans_eq hMbot) bot_le

end
end GaloisForLFunctions
