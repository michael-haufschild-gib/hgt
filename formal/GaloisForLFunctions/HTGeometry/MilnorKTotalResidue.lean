import GaloisForLFunctions.HTGeometry.MilnorKGersten

/-!
# The finite-support total residue map in Milnor `K`-theory

For the fraction field `K` of a Dedekind domain `R`, every Milnor `K`-class
has nonzero residue at only finitely many finite places.  The individual
residues therefore assemble into one homomorphism to the dependent direct sum
of local residue groups.  Its kernel is exactly the tame kernel.

This is the Gersten analogue of the restricted localization map required by
Albert--Brauer--Hasse--Noether: it makes the local-to-global carrier explicit
without postulating a global reciprocity or approximation theorem.  Component
surjectivity is formalized elsewhere; simultaneous surjectivity of this total
map is the remaining local-to-global approximation problem.
-/

namespace GaloisForLFunctions.HTGeometry

open Valuation IsLocalRing IsDedekindDomain

section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The direct sum of degree-`n - 1` Milnor `K`-groups of the residue fields
over all finite places of a Dedekind domain. -/
abbrev MilnorTotalResidueTarget (n : ℕ) :=
  Π₀ v : HeightOneSpectrum R,
    MilnorKDeg (ResidueField (v.valuation K).valuationSubring) (n - 1)

/-- All finite-place residues of a Milnor `K`-class, assembled in the
dependent direct sum.  Finite support is supplied by
`finite_milnorResidueAtPlace_ne_zero`. -/
noncomputable def milnorTotalResidue (n : ℕ) :
    MilnorKDeg K n →+ MilnorTotalResidueTarget (R := R) K n := by
  classical
  let f : MilnorKDeg K n → MilnorTotalResidueTarget (R := R) K n := fun x => by
    exact DFinsupp.mk (finite_milnorResidueAtPlace_ne_zero K n x).toFinset
      fun v => milnorResidueAtPlace K v.1 n x
  have hf : ∀ (x : MilnorKDeg K n) (v : HeightOneSpectrum R),
      f x v = milnorResidueAtPlace K v n x := by
    intro x v
    dsimp [f]
    split_ifs with hv
    · rfl
    · symm
      apply Classical.byContradiction
      intro h
      exact hv ((finite_milnorResidueAtPlace_ne_zero K n x).mem_toFinset.mpr h)
  exact
    { toFun := f
      map_zero' := by
        ext v
        change f 0 v = 0
        rw [hf]
        exact map_zero _
      map_add' := by
        intro x y
        ext v
        change f (x + y) v = f x v + f y v
        rw [hf, hf, hf]
        exact (milnorResidueAtPlace K v n).map_add x y }

/-- Evaluation of the total-residue map at a finite place is its defining
local Milnor residue. -/
theorem milnorTotalResidue_apply (n : ℕ) (x : MilnorKDeg K n)
    (v : HeightOneSpectrum R) :
    milnorTotalResidue (R := R) K n x v = milnorResidueAtPlace K v n x := by
  classical
  unfold milnorTotalResidue
  dsimp
  split_ifs with hv
  · rfl
  · symm
    apply Classical.byContradiction
    intro h
    exact hv ((finite_milnorResidueAtPlace_ne_zero K n x).mem_toFinset.mpr h)

/-- A class is killed by the total residue map exactly when it is unramified
at every finite place, i.e. belongs to the tame kernel. -/
theorem milnorTotalResidue_mem_ker_iff (n : ℕ) (x : MilnorKDeg K n) :
    x ∈ (milnorTotalResidue (R := R) K n).ker ↔ x ∈ milnorTameKernel R K n := by
  rw [mem_milnorTameKernel_iff (R := R) K n x]
  constructor
  · intro hx v
    have hzero := congrArg (fun f => f v) hx
    simpa only [milnorTotalResidue_apply, DFinsupp.zero_apply] using hzero
  · intro hx
    apply DFinsupp.ext
    intro v
    rw [milnorTotalResidue_apply]
    simpa only [DFinsupp.zero_apply] using hx v

/-- The tame kernel is the kernel of the finite-support total-residue map. -/
theorem milnorTameKernel_eq_ker_milnorTotalResidue (n : ℕ) :
    milnorTameKernel R K n = (milnorTotalResidue (R := R) K n).ker := by
  ext x
  exact (milnorTotalResidue_mem_ker_iff (R := R) K n x).symm

/-- The global Milnor group, its everywhere-unramified tame kernel, and the restricted direct
sum of finite-place residues are exact. -/
theorem milnorTotalResidue_exact (n : ℕ) :
    Function.Exact (milnorTameKernel R K n).subtype (milnorTotalResidue (R := R) K n) := by
  intro x
  change x ∈ (milnorTotalResidue (R := R) K n).ker ↔ _
  rw [← milnorTameKernel_eq_ker_milnorTotalResidue (R := R) K n]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- The finite-place Hasse criterion for Milnor residues: two global classes have the same
restricted residue profile exactly when their difference is everywhere unramified. -/
theorem milnorTotalResidue_eq_iff_sub_mem_tameKernel (n : ℕ) (x y : MilnorKDeg K n) :
    milnorTotalResidue (R := R) K n x = milnorTotalResidue (R := R) K n y ↔
      x - y ∈ milnorTameKernel R K n := by
  constructor
  · intro hxy
    apply (milnorTotalResidue_mem_ker_iff (R := R) K n (x - y)).mp
    change milnorTotalResidue (R := R) K n (x - y) = 0
    rw [(milnorTotalResidue (R := R) K n).map_sub, hxy, sub_self]
  · intro hxy
    have hzero : milnorTotalResidue (R := R) K n (x - y) = 0 :=
      (milnorTotalResidue_mem_ker_iff (R := R) K n (x - y)).mpr hxy
    rw [(milnorTotalResidue (R := R) K n).map_sub, sub_eq_zero] at hzero
    exact hzero

/-- First-isomorphism form of finite-place Milnor localization: classes modulo the unramified
tame kernel are exactly the residue profiles that occur globally. -/
noncomputable def milnorTotalResidueQuotientTameKernelEquivRange (n : ℕ) :
    MilnorKDeg K n ⧸ milnorTameKernel R K n ≃+
      (milnorTotalResidue (R := R) K n).range :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (milnorTameKernel_eq_ker_milnorTotalResidue (R := R) K n)).trans
    (QuotientAddGroup.quotientKerEquivRange (milnorTotalResidue (R := R) K n))

end

end GaloisForLFunctions.HTGeometry
