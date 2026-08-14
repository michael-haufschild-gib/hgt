import GaloisForLFunctions.HTGeometry.MilnorKTameValuation
import GaloisForLFunctions.HTGeometry.MilnorKTameKernel
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The tame symbols at the finite places of a Dedekind domain

The adic valuation at a height-one prime of a Dedekind domain is integer valued, so it carries the
tame symbol data.  A fixed pair of units of the fraction field is a pair of units of the valuation
ring at all but finitely many places, and there the tame symbol is trivial; so a fixed pair has
nontrivial tame symbol at only finitely many places.

* `tameHomAtPlace` : **the tame symbol at a finite place, on `K_2^M(K)`.**
* `finite_valuation_ne_one` : a unit is a unit of the valuation ring almost everywhere.
* `finite_tame_ne_one` : **a pair of units has trivial tame symbol almost everywhere.**
* `milnorKDegTwo_torsion_of_tameKernelAtPlaces_torsion` : **torsion of the tame kernel at the finite
  places forces torsion of `K_2^M`.**
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsLocalRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The tame symbol data at a finite place. -/
noncomputable def tameDataAtPlace (v : HeightOneSpectrum R) :
    TameData K (ResidueField (v.valuation K).valuationSubring) :=
  tameDataOfValuation (v.valuation K)

/-- **The tame symbol at a finite place, as a homomorphism out of `K_2^M(K)`.** -/
noncomputable def tameHomAtPlace (v : HeightOneSpectrum R) :
    MilnorKDeg K 2 →+ Additive (ResidueField (v.valuation K).valuationSubring)ˣ :=
  tameHomOfValuation (v.valuation K)

/-- **A unit of the fraction field is a unit of the valuation ring at all but finitely many
places.** -/
theorem finite_valuation_ne_one (a : Kˣ) :
    {v : HeightOneSpectrum R | v.valuation K (a : K) ≠ 1}.Finite := by
  refine Set.Finite.subset
    ((HeightOneSpectrum.Support.finite (R := R) (K := K) ((a : Kˣ) : K)).union
      (HeightOneSpectrum.Support.finite (R := R) (K := K) (((a⁻¹ : Kˣ)) : K))) ?_
  intro v hv
  rcases lt_trichotomy (v.valuation K (a : K)) 1 with hlt | heq | hgt
  · refine Or.inr ?_
    show 1 < v.valuation K (((a⁻¹ : Kˣ)) : K)
    refine (Valuation.one_lt_val_iff (v.valuation K) (a⁻¹ : Kˣ).ne_zero).2 ?_
    rwa [Units.val_inv_eq_inv_val, inv_inv]
  · exact absurd heq hv
  · exact Or.inl hgt

/-- **A pair of units has trivial tame symbol at all but finitely many places.** -/
theorem finite_tame_ne_one (a b : Kˣ) :
    {v : HeightOneSpectrum R | (tameDataAtPlace K v).tame a b ≠ 1}.Finite := by
  refine Set.Finite.subset
    ((finite_valuation_ne_one K a).union (finite_valuation_ne_one K b)) ?_
  intro v hv
  by_contra hnot
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hnot
  obtain ⟨hna, hnb⟩ := hnot
  exact hv (TameData.tame_eq_one_of_mem_ker _
    ((tameValHom_mem_ker_iff (v.valuation K) a).2 hna)
    ((tameValHom_mem_ker_iff (v.valuation K) b).2 hnb))

/-- **The tame symbol of a fixed symbol class vanishes at all but finitely many places.** -/
theorem finite_tameHomAtPlace_ne_zero (a b : Kˣ) :
    {v : HeightOneSpectrum R |
      tameHomAtPlace K v (milnorClassDeg K 2 ⟨[a, b], rfl⟩) ≠ 0}.Finite := by
  refine Set.Finite.subset (finite_tame_ne_one K a b) ?_
  intro v hv hone
  refine hv ?_
  show tameHomOfValuation (v.valuation K) (milnorClassDeg K 2 ⟨[a, b], rfl⟩) = 0
  rw [tameHomOfValuation_symbol]
  show Additive.ofMul ((tameDataOfValuation (v.valuation K)).tame a b) = Additive.ofMul 1
  exact congrArg Additive.ofMul hone

/-- **The tame symbol of any degree-two class, not only of a symbol, vanishes at all but finitely
many places.** -/
theorem finite_tameHomAtPlace_ne_zero_all (x : MilnorKDeg K 2) :
    {v : HeightOneSpectrum R | tameHomAtPlace K v x ≠ 0}.Finite :=
  tame_finiteSupport_of_symbols (fun v : HeightOneSpectrum R => tameDataAtPlace K v)
    (fun a b => finite_tameHomAtPlace_ne_zero K a b) x

/-- **Torsion of the tame kernel at the finite places forces torsion of `K_2^M`.**  Every class has
a nonzero multiple in the tame kernel, because its finitely many nonzero tame symbols lie in finite
groups.  For a number field this reduces the torsion of `K_2^M` to the finiteness of the tame
kernel. -/
theorem milnorKDegTwo_torsion_of_tameKernelAtPlaces_torsion
    [∀ v : HeightOneSpectrum R, Finite (ResidueField ((v.valuation K).valuationSubring))ˣ]
    (htame : ∀ y ∈ tameKernel (fun v : HeightOneSpectrum R => tameDataAtPlace K v),
      y ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (x : MilnorKDeg K 2) : x ∈ torsionAddSubgroup (MilnorKDeg K 2) :=
  milnorKDegTwo_torsion_of_tameKernel_torsion (fun v : HeightOneSpectrum R => tameDataAtPlace K v)
    (fun y => finite_tameHomAtPlace_ne_zero_all (R := R) K y) htame x

end GaloisForLFunctions.HTGeometry
