import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre
import GaloisForLFunctions.HTGeometry.TameInertiaRigidity
import Mathlib.Algebra.Polynomial.Coeff

/-!
# A collision in the critical fibre produces a tangent

Two distinct points of one critical fibre over a discrete valuation ring whose coordinates agree
modulo the maximal ideal differ by a pair `(D, E)` of polynomials with coefficients in that ideal.
Dividing by the largest common power of a uniformizer and reducing gives a pair `(U, V)` over the
residue field which is not both zero, and the two compatibility relations subtract to

```text
X^(m+n) ∣ D (p₂ + Q) + (p₁ + P) E + D E
```

whose quadratic term dies after the division, leaving exactly the linearized relation

```text
X^(m+n) ∣ U (p̄₂ + Q̄) + (p̄₁ + P̄) V .
```

So a collision at the special fibre is the same thing as a vertical tangent at the reduced point —
the hypothesis that the shared-tangent rigidity of `CriticalFibreSharedTangentRigidity` consumes.

The extraction of the common uniformizer power is proved here as well
(`exists_maximal_C_pow_dvd_pair`), together with the cancellation of a nonzero constant from a
horizon divisibility and the criterion for a reduction to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem exists_coeff_ne_zero {D : W[X]} (hD : D ≠ 0) : ∃ i, D.coeff i ≠ 0 := by
  by_contra hcon
  refine hD (Polynomial.ext fun i => ?_)
  have h := not_exists.mp hcon i
  simpa using not_not.mp h

/-- A uniformizer lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_irreducible {π : W} (hπ : Irreducible π) :
    π ∈ IsLocalRing.maximalIdeal W := by
  by_contra hc
  exact hπ.not_isUnit (IsLocalRing.notMem_maximalIdeal.mp hc)

/-- A nonzero polynomial is not divisible by every power of a uniformizer. -/
theorem exists_not_C_pow_dvd {π : W} (hπ : Irreducible π) {D : W[X]} (hD : D ≠ 0) :
    ∃ j : ℕ, ¬ C (π ^ j) ∣ D := by
  obtain ⟨i, hi⟩ := exists_coeff_ne_zero hD
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible hi hπ
  refine ⟨k + 1, fun hdvd => ?_⟩
  have hcoeff : π ^ (k + 1) ∣ D.coeff i := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd i
  have hle : addVal W (π ^ (k + 1)) ≤ addVal W (D.coeff i) := addVal_le_iff_dvd.mpr hcoeff
  rw [hπ.addVal_pow, hu, addVal_def' u hπ k] at hle
  have hcast : k + 1 ≤ k := by exact_mod_cast hle
  omega

/-- **The common uniformizer power of a polynomial pair.**  A pair not both zero is divisible by a
largest power of a uniformizer. -/
theorem exists_maximal_C_pow_dvd_pair {π : W} (hπ : Irreducible π) {D E : W[X]}
    (h : D ≠ 0 ∨ E ≠ 0) :
    ∃ j : ℕ, C (π ^ j) ∣ D ∧ C (π ^ j) ∣ E ∧
      ¬(C (π ^ (j + 1)) ∣ D ∧ C (π ^ (j + 1)) ∣ E) := by
  classical
  have hex : ∃ j : ℕ, ¬(C (π ^ j) ∣ D ∧ C (π ^ j) ∣ E) := by
    rcases h with hD | hE
    · obtain ⟨j, hj⟩ := exists_not_C_pow_dvd hπ hD
      exact ⟨j, fun hc => hj hc.1⟩
    · obtain ⟨j, hj⟩ := exists_not_C_pow_dvd hπ hE
      exact ⟨j, fun hc => hj hc.2⟩
  have hspec := Nat.find_spec hex
  have hzero : (C (π ^ 0) ∣ D ∧ C (π ^ 0) ∣ E) := by simp
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
    · exact absurd (hz ▸ hspec) (not_not.mpr hzero)
    · exact hp
  have hprev : ¬ ¬(C (π ^ (Nat.find hex - 1)) ∣ D ∧ C (π ^ (Nat.find hex - 1)) ∣ E) :=
    Nat.find_min hex (by omega)
  obtain ⟨h1, h2⟩ := not_not.mp hprev
  refine ⟨Nat.find hex - 1, h1, h2, ?_⟩
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  rw [hsucc]
  exact hspec

omit [IsDiscreteValuationRing W] in
/-- Cancelling a nonzero constant from a horizon divisibility. -/
theorem X_pow_dvd_of_C_mul {a : W} (ha : a ≠ 0) {L : ℕ} {F : W[X]}
    (h : (X : W[X]) ^ L ∣ C a * F) : (X : W[X]) ^ L ∣ F := by
  rw [Polynomial.X_pow_dvd_iff] at h ⊢
  intro d hd
  have hcd := h d hd
  rw [Polynomial.coeff_C_mul] at hcd
  exact (mul_eq_zero.mp hcd).resolve_left ha

/-- Reduction of a polynomial vanishes exactly when a uniformizer divides it. -/
theorem map_residue_eq_zero_iff {π : W} (hπ : Irreducible π) (D : W[X]) :
    D.map (IsLocalRing.residue W) = 0 ↔ C π ∣ D := by
  constructor
  · intro h
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
    have hi : IsLocalRing.residue W (D.coeff i) = 0 := by
      have hc := congrArg (fun q => Polynomial.coeff q i) h
      simpa using hc
    exact dvd_of_mem_maximalIdeal hπ (Ideal.Quotient.eq_zero_iff_mem.mp hi)
  · intro h
    refine Polynomial.ext fun i => ?_
    obtain ⟨c, hc⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp h i
    have hzero : IsLocalRing.residue W (D.coeff i) = 0 := by
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      rw [hc]
      exact Ideal.mul_mem_right _ _ (mem_maximalIdeal_of_irreducible hπ)
    simpa using hzero

/-- **A collision produces a tangent.**  Two distinct points of one critical fibre over a discrete
valuation ring whose coordinates agree modulo the maximal ideal give a nonzero low tangent pair over
the residue field, satisfying the linearized compatibility relation at the reduced point. -/
theorem exists_reduced_tangent_of_congruent
    {m n : ℕ} {P Q : W[X]} {π : W} (hπ : Irreducible π)
    (p q : criticalFibre W m n P Q) (hne : p ≠ q)
    (hDdvd : C π ∣ (q.1.1 - p.1.1)) (hEdvd : C π ∣ (q.1.2 - p.1.2)) :
    ∃ U V : (IsLocalRing.ResidueField W)[X],
      (U ≠ 0 ∨ V ≠ 0) ∧ U.degree < (m : ℕ) ∧ V.degree < (n : ℕ) ∧
      (X : (IsLocalRing.ResidueField W)[X]) ^ (m + n) ∣
        U * (p.1.2.map (IsLocalRing.residue W) + Q.map (IsLocalRing.residue W))
          + (p.1.1.map (IsLocalRing.residue W) + P.map (IsLocalRing.residue W)) * V := by
  classical
  have hnz : q.1.1 - p.1.1 ≠ 0 ∨ q.1.2 - p.1.2 ≠ 0 := by
    by_contra hcon
    have h1 : q.1.1 - p.1.1 = 0 := by
      by_contra hh
      exact hcon (Or.inl hh)
    have h2 : q.1.2 - p.1.2 = 0 := by
      by_contra hh
      exact hcon (Or.inr hh)
    exact hne (Subtype.ext (Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm))
  obtain ⟨j, hjD, hjE, hjmax⟩ := exists_maximal_C_pow_dvd_pair hπ hnz
  obtain ⟨D', hD'⟩ := hjD
  obtain ⟨E', hE'⟩ := hjE
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with hz | hp
    · exact absurd ⟨by simpa [hz] using hDdvd, by simpa [hz] using hEdvd⟩ (hz ▸ hjmax)
    · exact hp
  have hπj : (π : W) ^ j ≠ 0 := pow_ne_zero _ hπ.ne_zero
  refine ⟨D'.map (IsLocalRing.residue W), E'.map (IsLocalRing.residue W), ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    have hU : D'.map (IsLocalRing.residue W) = 0 := by
      by_contra hh
      exact hcon (Or.inl hh)
    have hV : E'.map (IsLocalRing.residue W) = 0 := by
      by_contra hh
      exact hcon (Or.inr hh)
    refine hjmax ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := (map_residue_eq_zero_iff hπ D').mp hU
      exact ⟨c, by rw [hD', hc, pow_succ, map_mul]; ring⟩
    · obtain ⟨c, hc⟩ := (map_residue_eq_zero_iff hπ E').mp hV
      exact ⟨c, by rw [hE', hc, pow_succ, map_mul]; ring⟩
  · refine lt_of_le_of_lt (Polynomial.degree_map_le) ?_
    have hdvd : D' ∣ q.1.1 - p.1.1 := ⟨C (π ^ j), by rw [hD']; ring⟩
    rcases eq_or_ne (q.1.1 - p.1.1) 0 with hz | hz
    · have : D' = 0 := by
        have := hD'
        rw [hz] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (by simpa using hπj)
      simp [this]
    · exact lt_of_le_of_lt (Polynomial.degree_le_of_dvd hdvd hz)
        (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt q.2.1 p.2.1))
  · refine lt_of_le_of_lt (Polynomial.degree_map_le) ?_
    have hdvd : E' ∣ q.1.2 - p.1.2 := ⟨C (π ^ j), by rw [hE']; ring⟩
    rcases eq_or_ne (q.1.2 - p.1.2) 0 with hz | hz
    · have : E' = 0 := by
        have := hE'
        rw [hz] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (by simpa using hπj)
      simp [this]
    · exact lt_of_le_of_lt (Polynomial.degree_le_of_dvd hdvd hz)
        (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt q.2.2.1 p.2.2.1))
  · have hkey : (X : W[X]) ^ (m + n) ∣
        (q.1.1 + P) * (q.1.2 + Q) - (p.1.1 + P) * (p.1.2 + Q) := by
      have h1 := q.2.2.2
      have h2 := p.2.2.2
      rw [criticalLowProduct_sub_one] at h1 h2
      have hsub := dvd_sub h1 h2
      convert hsub using 1
      ring
    have hDeq : q.1.1 = p.1.1 + C (π ^ j) * D' := by rw [← hD']; ring
    have hEeq : q.1.2 = p.1.2 + C (π ^ j) * E' := by rw [← hE']; ring
    have hfac : (q.1.1 + P) * (q.1.2 + Q) - (p.1.1 + P) * (p.1.2 + Q)
        = C (π ^ j) * (D' * (p.1.2 + Q) + (p.1.1 + P) * E' + C (π ^ j) * (D' * E')) := by
      rw [hDeq, hEeq]
      ring
    rw [hfac] at hkey
    have hF := X_pow_dvd_of_C_mul hπj hkey
    have hmapped := Polynomial.map_dvd (IsLocalRing.residue W) hF
    have hπ0 : IsLocalRing.residue W π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_maximalIdeal_of_irreducible hπ)
    have hjne : j ≠ 0 := by omega
    simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, hπ0, zero_pow hjne] using hmapped

end GaloisForLFunctions.HTGeometry
