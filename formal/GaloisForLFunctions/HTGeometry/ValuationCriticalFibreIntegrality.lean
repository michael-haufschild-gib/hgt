import GaloisForLFunctions.HTGeometry.LaurentCriticalFibreIntegrality
import GaloisForLFunctions.HTGeometry.ValuationSubringNormalization

/-!
# Critical-fibre integrality over arbitrary valuation subrings

Projective boundary exclusion implies a valuative criterion for the critical factorization fibre.
If two integral tails specialize to the pure critical tails, every coefficient of every affine
factorization point belongs to the valuation subring.  No discreteness or completeness assumption
is used.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- A normalized low polynomial over a valuation subring maps to the inverse-scale multiple of its
original polynomial over the fraction field. -/
theorem map_valuationNormalizedLowPolynomial
    {L : Type*} [Field L] (O : ValuationSubring L)
    {d : ℕ} {A : L[X]} (hA : A.degree < (d : ℕ)) {c : L}
    {w : Fin d ⊕ Unit → O}
    (hw : ∀ i, (w i : L) = affineBlockCoordinates A i / c) :
    (lowPolynomial (fun i => w (Sum.inl i))).map O.subtype = C c⁻¹ * A := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · rw [Polynomial.coeff_map, lowPolynomial_coeff, dif_pos hk,
      Polynomial.coeff_C_mul]
    simpa [div_eq_mul_inv, mul_comm] using hw (Sum.inl (⟨k, hk⟩ : Fin d))
  · rw [Polynomial.coeff_map, lowPolynomial_coeff, dif_neg hk,
      map_zero, Polynomial.coeff_C_mul]
    have hAk : A.coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero A d).mp hA k (Nat.le_of_not_gt hk)
    rw [hAk, mul_zero]

/-- Valuative criterion for the critical factorization fibre with arbitrary marked reductions.  If
the reduced tails are divisible by the corresponding powers of `X` and their marked coefficients
are nonzero, every low coefficient of every factorization point is integral. -/
theorem valuationSubring_criticalFibre_coefficients_mem_of_marked_reduction
    {L : Type*} [Field L] (O : ValuationSubring L)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (US VS : O[X])
    (hUSdvd : (X : (IsLocalRing.ResidueField O)[X]) ^ m ∣
      US.map (IsLocalRing.residue O))
    (hVSdvd : (X : (IsLocalRing.ResidueField O)[X]) ^ n ∣
      VS.map (IsLocalRing.residue O))
    (hUScoeff : (US.map (IsLocalRing.residue O)).coeff m ≠ 0)
    (hVScoeff : (VS.map (IsLocalRing.residue O)).coeff n ≠ 0)
    (p : criticalFibre L m n (US.map O.subtype) (VS.map O.subtype)) :
    (∀ i : Fin m, p.1.1.coeff i ∈ O) ∧
      ∀ j : Fin n, p.1.2.coeff j ∈ O := by
  classical
  let ι : O →+* L := O.subtype
  let ε : O →+* IsLocalRing.ResidueField O := IsLocalRing.residue O
  let U : L[X] := US.map ι
  let V : L[X] := VS.map ι
  let U0 : (IsLocalRing.ResidueField O)[X] := US.map ε
  let V0 : (IsLocalRing.ResidueField O)[X] := VS.map ε
  let A : L[X] := p.1.1
  let B : L[X] := p.1.2
  let xA : Fin m ⊕ Unit → L := affineBlockCoordinates A
  let xB : Fin n ⊕ Unit → L := affineBlockCoordinates B
  obtain ⟨c, hc, wA, iA, _hiAc, hmaxA, hwA, hwiA⟩ :=
    exists_valuationSubring_normalization O xA ⟨Sum.inr (), rfl⟩
  obtain ⟨d, hd, wB, iB, _hiBd, hmaxB, hwB, hwiB⟩ :=
    exists_valuationSubring_normalization O xB ⟨Sum.inr (), rfl⟩
  let Abar : O[X] := lowPolynomial (fun i => wA (Sum.inl i))
  let Bbar : O[X] := lowPolynomial (fun j => wB (Sum.inl j))
  let α : O := wA (Sum.inr ())
  let β : O := wB (Sum.inr ())
  have hmapA : Abar.map ι = C c⁻¹ * A := by
    exact map_valuationNormalizedLowPolynomial O p.2.1 hwA
  have hmapB : Bbar.map ι = C d⁻¹ * B := by
    exact map_valuationNormalizedLowPolynomial O p.2.2.1 hwB
  have hmapα : ι α = c⁻¹ := by
    change (α : L) = c⁻¹
    simpa [α, xA, affineBlockCoordinates] using hwA (Sum.inr ())
  have hmapβ : ι β = d⁻¹ := by
    change (β : L) = d⁻¹
    simpa [β, xB, affineBlockCoordinates] using hwB (Sum.inr ())
  let H : O[X] :=
    homogeneousTruncatedCriticalDefect US VS Abar Bbar α β
  have hmapH : H.map ι = C (c * d)⁻¹ * (criticalLowProduct U V A B - 1) := by
    dsimp only [H, homogeneousTruncatedCriticalDefect]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rw [hmapA, hmapB, hmapα, hmapβ]
    rw [map_mul, hmapα, hmapβ]
    dsimp only [U, V]
    rw [show (c * d)⁻¹ = c⁻¹ * d⁻¹ by ring_nf]
    simp only [criticalLowProduct]
    simp only [map_mul]
    ring
  have hmapHdvd : (X : L[X]) ^ (m + n) ∣ H.map ι := by
    rw [hmapH]
    exact dvd_mul_of_dvd_right p.2.2.2 _
  have hHdvd : (X : O[X]) ^ (m + n) ∣ H := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    apply O.subtype_injective
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp hmapHdvd) k hk
    simpa [ι] using hcoeff
  let A0 : (IsLocalRing.ResidueField O)[X] := Abar.map ε
  let B0 : (IsLocalRing.ResidueField O)[X] := Bbar.map ε
  let α0 : IsLocalRing.ResidueField O := ε α
  let β0 : IsLocalRing.ResidueField O := ε β
  have htrunc0 : (X : (IsLocalRing.ResidueField O)[X]) ^ (m + n) ∣
      homogeneousTruncatedCriticalDefect U0 V0 A0 B0 α0 β0 := by
    have h := Polynomial.map_dvd ε hHdvd
    simpa [H, homogeneousTruncatedCriticalDefect, U0, V0, A0, B0, α0, β0, ε]
      using h
  have htail0 : (X : (IsLocalRing.ResidueField O)[X]) ^ (m + n) ∣ U0 * V0 := by
    have hmul := mul_dvd_mul hUSdvd hVSdvd
    simpa [U0, V0, pow_add] using hmul
  have hboundary : (X : (IsLocalRing.ResidueField O)[X]) ^ (m + n) ∣
      homogeneousCriticalDefect U0 V0 A0 B0 α0 β0 := by
    have hextra : (X : (IsLocalRing.ResidueField O)[X]) ^ (m + n) ∣
        C (α0 * β0) * (U0 * V0) := by
      exact dvd_mul_of_dvd_right htail0 _
    rw [homogeneousCriticalDefect_eq]
    have hid :
        A0 * B0 + A0 * (C β0 * V0) + (C α0 * U0) * B0 +
              C (α0 * β0) * (U0 * V0) - C (α0 * β0) =
          homogeneousTruncatedCriticalDefect U0 V0 A0 B0 α0 β0 +
            C (α0 * β0) * (U0 * V0) := by
      rw [homogeneousTruncatedCriticalDefect]
      ring
    rw [hid]
    exact dvd_add htrunc0 hextra
  have hA0deg : A0.natDegree < m := by
    by_cases hA0 : A0 = 0
    · simpa [hA0] using hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt hA0).2
        (lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _))
  have hB0deg : B0.natDegree < n := by
    by_cases hB0 : B0 = 0
    · simpa [hB0] using hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hB0).2
        (lt_of_le_of_lt Polynomial.degree_map_le (lowPolynomial_degree_lt _))
  have hleft : A0 ≠ 0 ∨ α0 ≠ 0 := by
    rcases iA with i | q
    · left
      intro hzero
      have hcoeff : A0.coeff i = 1 := by
        simp [A0, Abar, lowPolynomial_coeff, hwiA]
      simp [hzero] at hcoeff
    · right
      intro hzero
      have hone : α0 = 1 := by
        simpa [α0, α] using congrArg ε hwiA
      exact zero_ne_one (hzero ▸ hone)
  have hright : B0 ≠ 0 ∨ β0 ≠ 0 := by
    rcases iB with j | q
    · left
      intro hzero
      have hcoeff : B0.coeff j = 1 := by
        simp [B0, Bbar, lowPolynomial_coeff, hwiB]
      simp [hzero] at hcoeff
    · right
      intro hzero
      have hone : β0 = 1 := by
        simpa [β0, β] using congrArg ε hwiB
      exact zero_ne_one (hzero ▸ hone)
  have hU0coeff : U0.coeff m ≠ 0 := by
    dsimp only [U0]
    exact hUScoeff
  have hV0coeff : V0.coeff n ≠ 0 := by
    dsimp only [V0]
    exact hVScoeff
  have hinfinity := critical_biprojective_boundary_exclusion_of_marked_coefficients
    hA0deg hB0deg hU0coeff hV0coeff
    hleft hright
    (by simpa only [homogeneousCriticalDefect] using hboundary)
  have hmemA : ∀ i, xA i ∈ O :=
    valuationSubring_all_mem_of_normalized_coordinate O
      (a := Sum.inr ()) rfl hc hmaxA hwA hinfinity.1
  have hmemB : ∀ i, xB i ∈ O :=
    valuationSubring_all_mem_of_normalized_coordinate O
      (a := Sum.inr ()) rfl hd hmaxB hwB hinfinity.2
  exact ⟨fun i => hmemA (Sum.inl i), fun j => hmemB (Sum.inl j)⟩

/-- Valuative criterion for the pure critical reduction. -/
theorem valuationSubring_criticalFibre_coefficients_mem
    {L : Type*} [Field L] (O : ValuationSubring L)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (US VS : O[X])
    (hUS : US.map (IsLocalRing.residue O) =
      (X : (IsLocalRing.ResidueField O)[X]) ^ m)
    (hVS : VS.map (IsLocalRing.residue O) =
      (X : (IsLocalRing.ResidueField O)[X]) ^ n)
    (p : criticalFibre L m n (US.map O.subtype) (VS.map O.subtype)) :
    (∀ i : Fin m, p.1.1.coeff i ∈ O) ∧
      ∀ j : Fin n, p.1.2.coeff j ∈ O := by
  apply valuationSubring_criticalFibre_coefficients_mem_of_marked_reduction
    O hm hn US VS
  · rw [hUS]
  · rw [hVS]
  · rw [hUS]
    simp
  · rw [hVS]
    simp

end GaloisForLFunctions.HTGeometry
