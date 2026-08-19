import GaloisForLFunctions.HTGeometry.ValuationSubringComapDVR
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Residue fields of a pulled-back valuation subring

A valuation subring `B` of `E` pulls back along a field embedding `F → E` to a valuation subring
`O` of `F`, and the inclusion `O → B` is a local homomorphism, so the residue fields form an
extension.  If `E` is algebraic over `F` that extension is algebraic:

```text
isAlgebraic_residueField_comap :
    Algebra.IsAlgebraic F E  →  Algebra.IsAlgebraic (ResidueField (B.comap f)) (ResidueField B)
```

The proof normalizes an algebraic relation for a lift so that its coefficients lie in `O` with at
least one of them a unit — possible because in a valuation ring one of any finitely many elements
divides all the others — and reduces it modulo the maximal ideals.

In characteristic zero this upgrades to separability through `Algebra.IsSeparable.of_integral`,
which is the residue hypothesis of `Algebra.FormallyUnramified.of_map_maximalIdeal`.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Among finitely many elements of a field there is one dividing all the others in a given
valuation subring. -/
theorem exists_max_valuation (O : ValuationSubring F) {s : Finset F} (hs : s.Nonempty) :
    ∃ c ∈ s, ∀ x ∈ s, x / c ∈ O := by
  classical
  obtain ⟨c, hcs, hmax⟩ := s.exists_max_image (fun x => O.valuation x) hs
  refine ⟨c, hcs, fun x hx => ?_⟩
  rcases eq_or_ne c 0 with rfl | hc0
  · have hx0 : x = 0 := by
      have h := hmax x hx
      rw [map_zero] at h
      exact (Valuation.zero_iff _).mp (le_antisymm h zero_le)
    simp [hx0]
  · rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le

noncomputable instance valuationSubringComapAlgebra (B : ValuationSubring E) :
    Algebra (B.comap (algebraMap F E)) B :=
  (valuationSubringComapInclusion (algebraMap F E) B).toAlgebra

instance valuationSubringComapAlgebra_isLocalHom (B : ValuationSubring E) :
    IsLocalHom (algebraMap (B.comap (algebraMap F E)) B) :=
  valuationSubringComapInclusion_isLocalHom (algebraMap F E) B

theorem coe_algebraMap_comap (B : ValuationSubring E) (a : B.comap (algebraMap F E)) :
    ((algebraMap (B.comap (algebraMap F E)) B a : B) : E) = algebraMap F E (a : F) := rfl

theorem isAlgebraic_residueField_comap [Algebra.IsAlgebraic F E] (B : ValuationSubring E) :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField (B.comap (algebraMap F E)))
      (IsLocalRing.ResidueField B) := by
  classical
  constructor
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  set O := B.comap (algebraMap F E) with hO
  obtain ⟨p, hp0, hpb⟩ := Algebra.IsAlgebraic.isAlgebraic (R := F) (A := E) ((b : E))
  have hcoeffs : p.coeffs.Nonempty := by
    rw [Polynomial.coeffs_nonempty_iff]
    exact hp0
  obtain ⟨c, hcs, hdvd⟩ := exists_max_valuation O hcoeffs
  have hc0 : c ≠ 0 := by
    intro h
    subst h
    have := Polynomial.mem_coeffs_iff.mp hcs
    obtain ⟨i, hi, hie⟩ := this
    exact (Polynomial.mem_support_iff.mp hi) hie.symm
  set q : F[X] := p * Polynomial.C c⁻¹ with hq
  have hqcoeff : ∀ i, q.coeff i = p.coeff i / c := by
    intro i
    rw [hq, Polynomial.coeff_mul_C, div_eq_mul_inv]
  have hsub : (↑q.coeffs : Set F) ⊆ O.toSubring := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp (by simpa using hy)
    rw [hqcoeff i]
    by_cases hi : p.coeff i = 0
    · rw [hi, zero_div]; exact O.zero_mem
    · exact hdvd _ (Polynomial.coeff_mem_coeffs hi)
  have hmem : ∀ i, q.coeff i ∈ O := by
    intro i
    by_cases hi : q.coeff i = 0
    · rw [hi]; exact O.zero_mem
    · exact hsub (by simpa using Polynomial.coeff_mem_coeffs hi)
  obtain ⟨i₀, hi₀s, hi₀⟩ := Polynomial.mem_coeffs_iff.mp hcs
  have hq1 : q.coeff i₀ = 1 := by
    rw [hqcoeff i₀, ← hi₀, div_self hc0]
  set z : IsLocalRing.ResidueField B := Ideal.Quotient.mk _ b with hz
  refine ⟨∑ i ∈ q.support, Polynomial.C (IsLocalRing.residue O ⟨q.coeff i, hmem i⟩) *
      Polynomial.X ^ i, ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun r : (IsLocalRing.ResidueField O)[X] => r.coeff i₀) hzero
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Polynomial.coeff_zero] at hcoeff
    rw [if_pos (by
      rw [Polynomial.mem_support_iff, hq1]
      exact one_ne_zero)] at hcoeff
    have hone : (⟨q.coeff i₀, hmem i₀⟩ : O) = 1 := Subtype.ext (by simpa using hq1)
    rw [hone, map_one] at hcoeff
    exact one_ne_zero hcoeff
  · have hstep : ∀ i ∈ q.support,
        Polynomial.aeval z (Polynomial.C (IsLocalRing.residue O ⟨q.coeff i, hmem i⟩) *
          Polynomial.X ^ i)
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
            (algebraMap O B ⟨q.coeff i, hmem i⟩ * b ^ i) := by
      intro i _
      rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, map_mul, map_pow]
      rfl
    have hsum0 : (∑ i ∈ q.support, algebraMap O B ⟨q.coeff i, hmem i⟩ * b ^ i : B) = 0 := by
      apply Subtype.val_injective
      have hcast : ((∑ i ∈ q.support, algebraMap O B ⟨q.coeff i, hmem i⟩ * b ^ i : B) : E)
          = ∑ i ∈ q.support, algebraMap F E (q.coeff i) * (b : E) ^ i := by
        push_cast
        rfl
      rw [hcast, ZeroMemClass.coe_zero]
      have haeval : Polynomial.aeval ((b : E)) q
          = ∑ i ∈ q.support, algebraMap F E (q.coeff i) * (b : E) ^ i := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rw [← haeval, hq, map_mul, hpb, zero_mul]
    calc Polynomial.aeval z (∑ i ∈ q.support,
          Polynomial.C (IsLocalRing.residue O ⟨q.coeff i, hmem i⟩) * Polynomial.X ^ i)
        = ∑ i ∈ q.support, Polynomial.aeval z
            (Polynomial.C (IsLocalRing.residue O ⟨q.coeff i, hmem i⟩) * Polynomial.X ^ i) :=
          map_sum _ _ _
      _ = ∑ i ∈ q.support, Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
            (algebraMap O B ⟨q.coeff i, hmem i⟩ * b ^ i) := Finset.sum_congr rfl hstep
      _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
            (∑ i ∈ q.support, algebraMap O B ⟨q.coeff i, hmem i⟩ * b ^ i) := (map_sum _ _ _).symm
      _ = 0 := by rw [hsum0, map_zero]

end GaloisForLFunctions.HTGeometry
