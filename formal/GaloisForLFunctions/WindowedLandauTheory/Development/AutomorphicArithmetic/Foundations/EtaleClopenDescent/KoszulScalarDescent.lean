import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLatticeExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LatticeIdealLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeDiagonalKernel
import GaloisForLFunctions.HTGeometry.RestrictScalarsRegular

/-! Koszul exactness and the top ideal criterion descend together
through a scalar extension that clears denominators. -/

noncomputable section

open GlobalTheory.PD GaloisForLFunctions.HTGeometry
open scoped Pointwise

namespace GlobalTheory.WH

variable {R S V : Type} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
  {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- A denominator invertible modulo the weights permits descent both
of Koszul primitives and of membership in the weight ideal times the lattice. -/
theorem koszul_exact_and_ideal_of_scalar_extension
    (P : Submodule R V) (Q : Submodule S V) (hPQ : P ≤ Q.restrictScalars R)
    (r : ι → R) (r' : ι → S) (hr : (fun l => algebraMap R S (r l)) = r')
    (d : ℤ) {a b : R} (hab : 1 - a * b ∈ Ideal.span (Set.range r))
    (hden : ∀ v ∈ Q, ∃ N : ℕ, a ^ N • v ∈ P)
    (K : V → Prop)
    (hex : ∀ (n : ℤ), n < d → ∀ c : Finset ι → Q,
      (∀ t : Finset ι, (t.card : ℤ) ≠ n → c t = 0) →
      koszulDifferential r' c = 0 → ∃ y : Finset ι → Q,
        (∀ t : Finset ι, (t.card : ℤ) ≠ n - 1 → y t = 0) ∧
          koszulDifferential r' y = c)
    (hker : ∀ v : Q, K (v : V) →
      v ∈ idealMultiple (M := Q) (Ideal.span (Set.range r'))) :
    (∀ (n : ℤ), n < d → ∀ c : Finset ι → P,
      (∀ t : Finset ι, (t.card : ℤ) ≠ n → c t = 0) →
      koszulDifferential r c = 0 → ∃ y : Finset ι → P,
        (∀ t : Finset ι, (t.card : ℤ) ≠ n - 1 → y t = 0) ∧ koszulDifferential r y = c) ∧
    (∀ v : P, K (v : V) → v ∈ idealMultiple (M := P) (Ideal.span (Set.range r))) := by
  subst r'
  let Q₀ := Q.restrictScalars R
  letI : Module S Q₀ := Submodule.module Q
  letI : IsScalarTower R S Q₀ := IsScalarTower.of_algebraMap_smul fun c v =>
    Subtype.ext (IsScalarTower.algebraMap_smul S c (v : V))
  have hdiff (c : Finset ι → Q₀) :
      koszulDifferential (fun l => algebraMap R S (r l)) c = koszulDifferential r c :=
    koszulDifferential_algebraMap r c
  refine ⟨?_, ?_⟩
  · intro n hn
    refine koszul_exact_of_away_lattice hPQ r hab (fun v => hden v v.property) n
      (fun c hc hd => ?_)
    obtain ⟨y, hy, hdy⟩ := hex n hn c hc ((hdiff c).trans hd)
    exact ⟨y, hy, (hdiff y).symm.trans hdy⟩
  · intro v hv
    let v' : Q₀ := ⟨(v : V), hPQ v.property⟩
    let D : Ideal R := Ideal.span (Set.range r)
    have hD : D.map (algebraMap R S) = Ideal.span (Set.range (fun l => algebraMap R S (r l))) := by
      change (Ideal.span (Set.range r)).map (algebraMap R S) = _
      rw [Ideal.map_span, ← Set.range_comp']
    have hdesc : (idealMultiple (M := Q₀) (D.map (algebraMap R S))).restrictScalars R =
        idealMultiple (M := Q₀) D :=
      restrictScalars_map_smul_top (D := S) (N := Q₀) D
    have hvD : v' ∈ idealMultiple (M := Q₀) D := by
      rw [← hdesc]
      change v' ∈ idealMultiple (M := Q₀) (D.map (algebraMap R S))
      rw [hD]
      exact hker v' hv
    have hv' : (v : V) ∈ D • Q₀ :=
      (subtype_mem_ideal_smul_iff D Q₀ (v := v')).mp hvD
    have hvP : (v : V) ∈ D • P :=
      mem_ideal_smul_of_localized_lattice D (P := P) (Q := Q₀) (a := a) (b := b)
        (v := (v : V)) hab (fun w hw => hden w hw) v.property hv'
    exact (subtype_mem_ideal_smul_iff D P (v := v)).mpr hvP

end GlobalTheory.WH
