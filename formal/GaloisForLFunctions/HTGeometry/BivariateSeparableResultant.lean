import GaloisForLFunctions.HTGeometry.BivariateRootCovering
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The fibre resultant of a monic two-variable polynomial
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Resultant of a monic two-variable polynomial against its derivative in the root variable. -/
noncomputable def biResultant {R : Type*} [CommRing R] (f : R[X][X]) : R[X] :=
  Polynomial.resultant f (Polynomial.derivative f) f.natDegree (f.natDegree - 1)

/-- Separability of a monic polynomial over a field, through the resultant. -/
theorem separable_iff_resultant_ne_zero {K : Type*} [Field K] [CharZero K]
    {p : K[X]} (hp : p.Monic) :
    p.Separable ↔ Polynomial.resultant p (Polynomial.derivative p) p.natDegree
      (p.natDegree - 1) ≠ 0 := by
  have hder : (Polynomial.derivative p).natDegree = p.natDegree - 1 :=
    Polynomial.natDegree_derivative p
  rw [Polynomial.Separable, ← Polynomial.isUnit_resultant_iff_isCoprime hp, hder]
  exact ⟨fun h => h.ne_zero, fun h => (isUnit_iff_ne_zero).mpr h⟩

/-- Value of the fibre resultant at a parameter. -/
theorem biResultant_eval {K : Type*} [Field K] [CharZero K]
    {f : K[X][X]} (hf : f.Monic) (s : K) :
    (biResultant f).eval s =
      Polynomial.resultant (biFibre f s) (Polynomial.derivative (biFibre f s))
        (biFibre f s).natDegree ((biFibre f s).natDegree - 1) := by
  have hdeg : (biFibre f s).natDegree = f.natDegree := biFibre_natDegree hf s
  rw [hdeg, biResultant]
  have h := Polynomial.resultant_map_map (f := f) (g := Polynomial.derivative f)
    (m := f.natDegree) (n := f.natDegree - 1) (Polynomial.evalRingHom s)
  rw [← Polynomial.derivative_map] at *
  simpa [biFibre] using h.symm

/-- Over an algebraically closed field, separability of every fibre makes the fibre resultant a
nonzero constant. -/
theorem exists_biResultant_eq_C {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {f : K[X][X]} (hf : f.Monic)
    (hsep : ∀ s : K, (biFibre f s).Separable) :
    ∃ c : K, c ≠ 0 ∧ biResultant f = Polynomial.C c := by
  have hno : ∀ s : K, (biResultant f).eval s ≠ 0 := by
    intro s
    rw [biResultant_eval hf s]
    exact (separable_iff_resultant_ne_zero (biFibre_monic hf s)).mp (hsep s)
  have hne : biResultant f ≠ 0 := by
    intro h
    exact hno 0 (by simp [h])
  have hdeg : (biResultant f).natDegree = 0 := by
    by_contra hdz
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (biResultant f)
      (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdz)).ne'
    exact hno z hz
  refine ⟨(biResultant f).coeff 0, ?_, ?_⟩
  · intro h
    exact hne (by rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, h, map_zero])
  · exact Polynomial.eq_C_of_natDegree_eq_zero hdeg

/-- A nonzero constant fibre resultant makes every fibre separable, over any field. -/
theorem forall_separable_of_biResultant_eq_C {L : Type*} [Field L] [CharZero L]
    {f : L[X][X]} (hf : f.Monic)
    {c : L} (hc : c ≠ 0) (hres : biResultant f = Polynomial.C c) :
    ∀ s : L, (biFibre f s).Separable := by
  intro s
  refine (separable_iff_resultant_ne_zero (biFibre_monic hf s)).mpr ?_
  rw [← biResultant_eval hf s, hres, Polynomial.eval_C]
  exact hc

/-- The fibre resultant commutes with a coefficient ring homomorphism. -/
theorem biResultant_map {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {f : R[X][X]} (hf : f.Monic) :
    biResultant (f.map (Polynomial.mapRingHom φ)) =
      (biResultant f).map φ := by
  have hdeg : (f.map (Polynomial.mapRingHom φ)).natDegree = f.natDegree :=
    hf.natDegree_map _
  rw [biResultant, biResultant, hdeg, Polynomial.derivative_map]
  exact Polynomial.resultant_map_map (f := f) (g := Polynomial.derivative f)
    (m := f.natDegree) (n := f.natDegree - 1) (Polynomial.mapRingHom φ)

end

end GaloisForLFunctions.HTGeometry
