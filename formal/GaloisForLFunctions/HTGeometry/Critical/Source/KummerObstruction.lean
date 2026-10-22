import GaloisForLFunctions.HTGeometry.Critical.Reciprocal.CoordinateValuation
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.TorusKummerExponents

/-!
# Actual Kummer obstruction in the critical source field

The two actual coordinate divisors give independent integer orders on source-field units.  Hence a
cyclic Kummer relation involving the marked raw and reciprocal coordinates forces both exponents to
be divisible by the cyclic degree.  This is the arithmetic obstruction required by the no-hidden-
blocks argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial


/-- The reciprocal unit in the reindexed reciprocal presentation is the same actual source-field
unit as the corresponding ordinary reciprocal coordinate. -/
theorem criticalSourceRecipReindexedUnit_eq_recipUnit
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1 + 1)) :
    criticalSourceRecipReindexedUnit K hm hn i =
      criticalSourceRecipUnit K hm hn (Fin.cast (by omega) i) := by
  apply Units.ext
  rfl

/-- The raw-coordinate marked divisor does not see the reciprocal coordinate when it is indexed in
the reciprocal rational presentation. -/
theorem criticalSourceRawCoordinateOrderHom_recipReindexed_eq_zero
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    criticalSourceRawCoordinateOrderHom K m n ⟨m, by omega⟩
        (criticalSourceRecipReindexedUnit K (by omega) (by omega) ⟨n, by omega⟩) = 1 := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  let j : Fin (m + n - 1 + 1) := ⟨n, by omega⟩
  change criticalSourceRawCoordinateOrderHom K m n ⟨m, by omega⟩
      (criticalSourceRecipReindexedUnit K hm0 hn0 j) = 1
  rw [criticalSourceRecipReindexedUnit_eq_recipUnit K hm0 hn0 j]
  have hcast : Fin.cast (by omega) j = (⟨n, by omega⟩ : Fin (m + n)) := by
    apply Fin.ext
    rfl
  rw [hcast]
  exact criticalSourceRawCoordinateOrderHom_recip_eq_zero K hm hn

/-- A nonzero ground-field constant is outside every coordinate prime. -/
theorem MvPolynomial.C_unit_not_mem_coordDivisor
    (K : Type*) [Field K] {L : ℕ} (i : Fin L) (c : Kˣ) :
    (MvPolynomial.C (c : K) : MvPolynomial (Fin L) K) ∉
      (coordDivisor (k := K) i).1 := by
  intro hmem
  have hunit : IsUnit (MvPolynomial.C (c : K) : MvPolynomial (Fin L) K) :=
    c.isUnit.map MvPolynomial.C
  rcases hunit with ⟨u, hu⟩
  have hu_mem : (u : MvPolynomial (Fin L) K) ∈ (coordDivisor (k := K) i).1 := by
    simpa [hu] using hmem
  have hone : (1 : MvPolynomial (Fin L) K) ∈ (coordDivisor (k := K) i).1 := by
    have hmul := (coordDivisor (k := K) i).1.mul_mem_left (↑u⁻¹) hu_mem
    simpa using hmul
  exact (coordDivisor (k := K) i).2.1.ne_top
    ((Ideal.eq_top_iff_one (coordDivisor (k := K) i).1).2 hone)

/-- Raw-coordinate divisorial orders vanish on ground-field constants. -/
theorem criticalSourceRawCoordinateOrderHom_groundUnit
    (K : Type*) [Field K] (m n : ℕ) (i : Fin (m + n)) (c : Kˣ) :
    criticalSourceRawCoordinateOrderHom K m n i
        (Units.map (algebraMap K (criticalSourceField K m n)) c) = 1 := by
  let R := criticalRawCoordinateRing K m n
  let F := FractionRing R
  let P : R := MvPolynomial.C (c : K)
  have hP : P ∉ (coordDivisor (k := K) i).1 :=
    MvPolynomial.C_unit_not_mem_coordDivisor K i c
  have hPval := criticalRawCoordinateFieldValuation_algebraMap_eq_one K m n i hP
  have hpre : (criticalSourceFieldEquiv K m n).symm
      (algebraMap K (criticalSourceField K m n) (c : K)) = algebraMap R F P := by
    calc
      _ = algebraMap K F (c : K) := (criticalSourceFieldEquiv K m n).symm.commutes _
      _ = algebraMap R F (algebraMap K R (c : K)) :=
        IsScalarTower.algebraMap_apply K R F (c : K)
      _ = algebraMap R F P := by rfl
  have hval : criticalSourceRawCoordinateValuation K m n i
      (algebraMap K (criticalSourceField K m n) (c : K)) = 1 := by
    rw [criticalSourceRawCoordinateValuation, Valuation.comap_apply]
    change criticalRawCoordinateFieldValuation K m n i
      ((criticalSourceFieldEquiv K m n).symm
        (algebraMap K (criticalSourceField K m n) (c : K))) = 1
    rw [hpre, hPval]
  apply WithZero.coe_injective
  change (↑((criticalSourceRawCoordinateValuation K m n i
    (algebraMap K (criticalSourceField K m n) (c : K))).unzero _)⁻¹ :
      WithZero (Multiplicative ℤ)) = 1
  rw [WithZero.coe_inv, WithZero.coe_unzero, hval]
  simp

/-- Reciprocal-coordinate divisorial orders vanish on ground-field constants. -/
theorem criticalSourceRecipCoordinateOrderHom_groundUnit
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (i : Fin (m + n - 1 + 1)) (c : Kˣ) :
    criticalSourceRecipCoordinateOrderHom K hm hn i
        (Units.map (algebraMap K (criticalSourceField K m n)) c) = 1 := by
  let R := criticalRecipCoordinateRing K m n
  let F := FractionRing R
  let P : R := MvPolynomial.C (c : K)
  have hP : P ∉ (coordDivisor (k := K) i).1 :=
    MvPolynomial.C_unit_not_mem_coordDivisor K i c
  have hPval := criticalRecipCoordinateFieldValuation_algebraMap_eq_one K m n i hP
  have hpre : (criticalSourceRecipFieldEquiv K hm hn).symm
      (algebraMap K (criticalSourceField K m n) (c : K)) = algebraMap R F P := by
    calc
      _ = algebraMap K F (c : K) := (criticalSourceRecipFieldEquiv K hm hn).symm.commutes _
      _ = algebraMap R F (algebraMap K R (c : K)) :=
        IsScalarTower.algebraMap_apply K R F (c : K)
      _ = algebraMap R F P := by rfl
  have hval : criticalSourceRecipCoordinateValuation K hm hn i
      (algebraMap K (criticalSourceField K m n) (c : K)) = 1 := by
    rw [criticalSourceRecipCoordinateValuation, Valuation.comap_apply]
    change criticalRecipCoordinateFieldValuation K m n i
      ((criticalSourceRecipFieldEquiv K hm hn).symm
        (algebraMap K (criticalSourceField K m n) (c : K))) = 1
    rw [hpre, hPval]
  apply WithZero.coe_injective
  change (↑((criticalSourceRecipCoordinateValuation K hm hn i
    (algebraMap K (criticalSourceField K m n) (c : K))).unzero _)⁻¹ :
      WithZero (Multiplicative ℤ)) = 1
  rw [WithZero.coe_inv, WithZero.coe_unzero, hval]
  simp

/-- **Actual two-divisor Kummer obstruction.**  Every Kummer relation in the actual critical source
field with a ground-field constant forces the two marked exponents to be divisible by the cyclic
degree. -/
theorem criticalSource_dvd_exponents_of_kummer_relation
    (K : Type*) [Field K] [CharZero K]
    {m n r : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {a b : ℤ} (z : (criticalSourceField K m n)ˣ) (c : Kˣ)
    (hz : z ^ r =
      Units.map (algebraMap K (criticalSourceField K m n)) c *
        criticalSourceRawUnit K m n ⟨m, by omega⟩ ^ a *
          criticalSourceRecipReindexedUnit K (by omega) (by omega) ⟨n, by omega⟩ ^ b) :
    (r : ℤ) ∣ a ∧ (r : ℤ) ∣ b := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  let i : Fin (m + n) := ⟨m, by omega⟩
  let j : Fin (m + n - 1 + 1) := ⟨n, by omega⟩
  change z ^ r =
      Units.map (algebraMap K (criticalSourceField K m n)) c *
        criticalSourceRawUnit K m n i ^ a *
          criticalSourceRecipReindexedUnit K hm0 hn0 j ^ b at hz
  exact dvd_of_kummer_relation
    (criticalSourceRawCoordinateOrderHom K m n i)
    (criticalSourceRecipCoordinateOrderHom K hm0 hn0 j) hz
    (criticalSourceRawCoordinateOrderHom_groundUnit K m n i c)
    (by simpa [i] using criticalSourceRawCoordinateOrderHom_raw_self K hm0 hn0)
    (by simpa [i, j, hm0, hn0] using
      criticalSourceRawCoordinateOrderHom_recipReindexed_eq_zero K hm hn)
    (criticalSourceRecipCoordinateOrderHom_groundUnit K hm0 hn0 j c)
    (by simpa [i, j, hm0, hn0] using
      criticalSourceRecipCoordinateOrderHom_raw_eq_zero K hm hn)
    (by simpa [j] using criticalSourceRecipCoordinateOrderHom_recip_self K hm0 hn0)

/-- No nontrivial exponent pair modulo `r` can occur in an actual critical source-field Kummer
relation with ground-field constant. -/
theorem criticalSource_not_exists_kummer_relation
    (K : Type*) [Field K] [CharZero K]
    {m n r : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {a b : ℤ}
    (hab : ¬ ((r : ℤ) ∣ a ∧ (r : ℤ) ∣ b)) :
    ¬ ∃ (z : (criticalSourceField K m n)ˣ) (c : Kˣ),
      z ^ r = Units.map (algebraMap K (criticalSourceField K m n)) c *
        criticalSourceRawUnit K m n ⟨m, by omega⟩ ^ a *
          criticalSourceRecipReindexedUnit K (by omega) (by omega) ⟨n, by omega⟩ ^ b := by
  rintro ⟨z, c, hz⟩
  exact hab (criticalSource_dvd_exponents_of_kummer_relation K hm hn z c hz)

end

end GaloisForLFunctions.HTGeometry
