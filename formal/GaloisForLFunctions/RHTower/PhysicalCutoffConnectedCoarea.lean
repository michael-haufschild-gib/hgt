import GaloisForLFunctions.RHTower.PhysicalCutoffAliasResponseJoining

open scoped BigOperators

namespace RHTower

/-- The complementary high-cutoff Boolean sum obeys the same deletion--contraction
recurrence as the low-cutoff sum. -/
theorem truncatedAliasHighSum_insert {R : Type*} [CommRing R]
    {q p H : ℕ} {s : Finset ℕ} (hp : p ∉ s) (ν : ℕ → R) :
    truncatedAliasHighSum q (insert p s) ν H =
      truncatedAliasHighSum q s ν H - ν p * truncatedAliasHighSum (q * p) s ν H := by
  unfold truncatedAliasHighSum
  rw [Finset.sum_powerset_insert hp, sub_eq_add_neg]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t := fun hpin => hp ((Finset.mem_powerset.mp ht) hpin)
  simp only [Finset.prod_insert hpt, Finset.card_insert_of_notMem hpt]
  rw [← Nat.mul_assoc q p (∏ x ∈ t, x)]
  change
    (if H < (q * p) * ∏ x ∈ t, x then
      (-1 : R) ^ (t.card + 1) * (ν p * ∏ x ∈ t, ν x) else 0) =
      -(ν p * (if H < (q * p) * ∏ x ∈ t, x then
        (-1 : R) ^ t.card * ∏ x ∈ t, ν x else 0))
  by_cases hlt : H < (q * p) * ∏ x ∈ t, x
  · simp [hlt, pow_succ]
    ring
  · simp [hlt]

/-- Coarea-oriented high-cutoff Boolean field.  The minus sign records the
orientation inherited from the cutoff boundary. -/
def physicalCutoffCoareaField {R ι : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (χ : ℕ → ι → R) : ι → R :=
  fun x => -truncatedAliasHighSum q s (fun p => χ p x) H

theorem physicalCutoffCoareaField_insert {R ι : Type*} [CommRing R]
    {q p H : ℕ} {s : Finset ℕ} (hp : p ∉ s) (χ : ℕ → ι → R) :
    physicalCutoffCoareaField q H (insert p s) χ =
      fun x => physicalCutoffCoareaField q H s χ x -
        χ p x * physicalCutoffCoareaField (q * p) H s χ x := by
  funext x
  unfold physicalCutoffCoareaField
  rw [truncatedAliasHighSum_insert hp]
  ring

/-- Difference between the coarea field and its low-density Boolean model. -/
def physicalCutoffCoareaAffineDefect {R ι : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (χ : ℕ → ι → R) (θ : ℕ → R) : ι → R :=
  fun x => physicalCutoffCoareaField q H s χ x - truncatedAliasSum q s θ H

/-- Inserting one coordinate transports the affine defect homogeneously and
adds exactly one connected incidence/coarea forcing term. -/
theorem physicalCutoffCoareaAffineDefect_insert {R ι : Type*} [CommRing R]
    {q p H : ℕ} {s : Finset ℕ} (hp : p ∉ s)
    (χ : ℕ → ι → R) (θ : ℕ → R) :
    physicalCutoffCoareaAffineDefect q H (insert p s) χ θ =
      fun x => physicalCutoffCoareaAffineDefect q H s χ θ x -
        θ p * physicalCutoffCoareaAffineDefect (q * p) H s χ θ x -
        (χ p x - θ p) * physicalCutoffCoareaField (q * p) H s χ x := by
  funext x
  unfold physicalCutoffCoareaAffineDefect
  rw [physicalCutoffCoareaField_insert hp, truncatedAliasSum_insert hp]
  ring

/-- Finite weighted trace joining low density to the oriented high response. -/
def physicalCutoffCoareaTrace {R ι : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (χ : ℕ → ι → R) (θ : ℕ → R)
    (u : Finset ι) (weight : ι → R) (J : R) : R :=
  J * truncatedAliasSum q s θ H -
    ∑ x ∈ u, weight x * physicalCutoffCoareaField q H s χ x

/-- Joined trace insertion is homogeneous density transport plus the connected
incidence/coarea forcing.  This is the exact finite source term left by the
failed homogeneous/coercive trace route. -/
theorem physicalCutoffCoareaTrace_insert {R ι : Type*} [CommRing R]
    {q p H : ℕ} {s : Finset ℕ} (hp : p ∉ s)
    (χ : ℕ → ι → R) (θ : ℕ → R)
    (u : Finset ι) (weight : ι → R) (J : R) :
    physicalCutoffCoareaTrace q H (insert p s) χ θ u weight J =
      physicalCutoffCoareaTrace q H s χ θ u weight J -
        θ p * physicalCutoffCoareaTrace (q * p) H s χ θ u weight J +
        ∑ x ∈ u, weight x * (χ p x - θ p) *
          physicalCutoffCoareaField (q * p) H s χ x := by
  unfold physicalCutoffCoareaTrace
  rw [truncatedAliasSum_insert hp, physicalCutoffCoareaField_insert hp]
  ring_nf
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- With no active coordinate, the joined trace is the exact continuum/lattice
zero-mode switch at the physical cutoff. -/
theorem physicalCutoffCoareaTrace_empty {R ι : Type*} [CommRing R]
    (q H : ℕ) (χ : ℕ → ι → R) (θ : ℕ → R)
    (u : Finset ι) (weight : ι → R) (J : R) :
    physicalCutoffCoareaTrace q H ∅ χ θ u weight J =
      if q ≤ H then J else ∑ x ∈ u, weight x := by
  unfold physicalCutoffCoareaTrace physicalCutoffCoareaField
  by_cases hq : q ≤ H
  · have hnlt : ¬ H < q := Nat.not_lt_of_ge hq
    simp [truncatedAliasSum, truncatedAliasHighSum, hq, hnlt]
  · have hlt : H < q := Nat.lt_of_not_ge hq
    simp [truncatedAliasSum, truncatedAliasHighSum, hq, hlt]

/-- Affine defect obtained by substituting the density profile into the coarea
field itself. -/
def physicalCutoffCoareaAffineDrift {R : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (θ : ℕ → R) : R :=
  -truncatedAliasHighSum q s θ H - truncatedAliasSum q s θ H

/-- The cutoff location cancels completely from the affine drift: the result is
the negative complete survival product. -/
theorem physicalCutoffCoareaAffineDrift_eq_neg_survival {R : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (θ : ℕ → R) :
    physicalCutoffCoareaAffineDrift q H s θ = -∏ p ∈ s, (1 - θ p) := by
  unfold physicalCutoffCoareaAffineDrift
  rw [← truncatedAliasSum_add_highSum q H s θ]
  ring

/-- For quadratic-root densities on prime coordinates, affine centering occurs
exactly in the odd-gap parity sector. -/
theorem quadraticCongruencePhysicalCutoffAffineDrift_eq_zero_iff
    (q H : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) (h : ℤ) :
    physicalCutoffCoareaAffineDrift q H s
      (fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ)) = 0 ↔
      2 ∈ s ∧ ¬(2 : ℤ) ∣ h := by
  rw [physicalCutoffCoareaAffineDrift_eq_neg_survival, neg_eq_zero]
  exact quadraticCongruencePrimeSurvivalProduct_eq_zero_iff s hprime h

end RHTower
