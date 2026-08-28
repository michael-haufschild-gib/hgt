import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicParitySymmetrizedPolarityNoGo

/-!
# Additive even-projection obstruction for the holomorphic SC prime reservoir

The canonical additive repair

`Aₘ(z) = (Uₘ(z) + Uₘ(-z)) / 2`

is entire, even, and normalized at the center.  Unlike multiplicative parity
symmetrization, it does not encounter the rank-one reflected-polarity wall.
Instead it exposes an exterior-square obstruction: its exact Boolean-cube
expansion retains precisely the even compounds, and every nonempty even
compound has adverse sign on the negative Gamma-Bockstein packet.  The
quadratic layer alone grows cofinally and forces negative polarity at `z = 1`.

Since normalized centered Xi has positive real polarity there, these additive
even projections cannot converge locally uniformly to normalized Xi.
-/

open Complex Filter Topology Set
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- Additive even projection of the identity-unitized real reservoir determinant. -/
def evenProjectedUnitizedRealReservoirDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℝ) : ℝ :=
  (unitizedRealReservoirDeterminant b +
    unitizedRealReservoirDeterminant (-b)) / 2

/-- Exact compound expansion: additive parity projection retains precisely even degrees. -/
theorem evenProjectedUnitizedRealReservoirDeterminant_eq_even_powerset
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℝ) :
    evenProjectedUnitizedRealReservoirDeterminant b =
      ∑ s ∈ (Finset.univ : Finset ι).powerset with Even s.card,
        (1 - (s.card : ℝ)) * ∏ i ∈ s, b i := by
  classical
  rw [evenProjectedUnitizedRealReservoirDeterminant,
    unitizedRealReservoirDeterminant_eq_sum_powerset,
    unitizedRealReservoirDeterminant_eq_sum_powerset,
    ← Finset.sum_add_distrib, Finset.sum_div]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hnegprod : ∏ i ∈ s, (-b) i =
      (-1 : ℝ) ^ s.card * ∏ i ∈ s, b i := by
    simpa only [Pi.neg_apply] using (Finset.prod_neg (s := s) b)
  rw [hnegprod]
  by_cases heven : Even s.card
  · rw [if_pos heven, heven.neg_one_pow]
    ring
  · have hodd : Odd s.card := (Nat.even_or_odd s.card).resolve_left heven
    rw [if_neg heven, hodd.neg_one_pow]
    ring

/-- A product of an even number of strictly negative coordinates is positive. -/
theorem even_product_pos_of_neg
    {ι : Type*} {b : ι → ℝ} (hb : ∀ i, b i < 0)
    (s : Finset ι) (heven : Even s.card) :
    0 < ∏ i ∈ s, b i := by
  have hpos : 0 < ∏ i ∈ s, -b i :=
    Finset.prod_pos fun i hi => neg_pos.mpr (hb i)
  calc
    ∏ i ∈ s, b i = (-1 : ℝ) ^ s.card * ∏ i ∈ s, -b i := by
      have h := Finset.prod_neg (s := s) (fun i => -b i)
      simpa using h
    _ = ∏ i ∈ s, -b i := by rw [heven.neg_one_pow, one_mul]
    _ > 0 := hpos

/-- On a negative packet, the exterior-square layer already upper-bounds the full even
projection: all remaining nonempty even layers have the same adverse sign. -/
theorem evenProjectedUnitizedRealReservoirDeterminant_le_one_sub_pairMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ i, b i < 0) :
    evenProjectedUnitizedRealReservoirDeterminant b ≤
      1 - ∑ s ∈ (Finset.univ : Finset ι).powersetCard 2,
        ∏ i ∈ s, b i := by
  classical
  rw [evenProjectedUnitizedRealReservoirDeterminant_eq_even_powerset]
  let E := ((Finset.univ : Finset ι).powerset).filter (fun s => Even s.card)
  let P := (Finset.univ : Finset ι).powersetCard 2
  let term : Finset ι → ℝ := fun s =>
    (1 - (s.card : ℝ)) * ∏ i ∈ s, b i
  have hempty : (∅ : Finset ι) ∈ E := by simp [E]
  have hPsub : P ⊆ E.erase ∅ := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hzero
      subst s
      simp at hs
    · simp [E, hs.2]
  have hmass : ∑ s ∈ P, -term s ≤ ∑ s ∈ E.erase ∅, -term s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hPsub
    intro s hsE hsnot
    have hsEin : s ∈ E := Finset.mem_of_mem_erase hsE
    have hsne : s ≠ ∅ := (Finset.mem_erase.mp hsE).1
    have hseven : Even s.card := (Finset.mem_filter.mp hsEin).2
    have hcard : 1 ≤ s.card :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hsne)
    have hprod := even_product_pos_of_neg hb s hseven
    dsimp [term]
    have hcardR : (1 : ℝ) ≤ s.card := by exact_mod_cast hcard
    nlinarith
  have hsplit : ∑ s ∈ E, term s = term ∅ + ∑ s ∈ E.erase ∅, term s := by
    calc
      ∑ s ∈ E, term s = (∑ s ∈ E.erase ∅, term s) + term ∅ := by
        exact (Finset.sum_erase_add E term hempty).symm
      _ = term ∅ + ∑ s ∈ E.erase ∅, term s := add_comm _ _
  have hpair : ∑ s ∈ P, term s =
      -(∑ s ∈ P, ∏ i ∈ s, b i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hscard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
    dsimp [term]
    rw [hscard]
    norm_num
  change ∑ s ∈ E, term s ≤ _
  rw [hsplit]
  have hemptyterm : term ∅ = 1 := by simp [term]
  have htail : ∑ s ∈ E.erase ∅, term s ≤ ∑ s ∈ P, term s := by
    simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using hmass
  have htail' : ∑ s ∈ E.erase ∅, term s ≤
      -(∑ s ∈ (Finset.univ : Finset ι).powersetCard 2,
        ∏ i ∈ s, b i) := by
    calc
      ∑ s ∈ E.erase ∅, term s ≤ ∑ s ∈ P, term s := htail
      _ = -(∑ s ∈ P, ∏ i ∈ s, b i) := hpair
      _ = -(∑ s ∈ (Finset.univ : Finset ι).powersetCard 2,
          ∏ i ∈ s, b i) := rfl
  rw [hemptyterm]
  linarith

/-- Every Gamma-Bockstein unit weight has a fixed positive floor. -/
theorem primeGammaBocksteinUnitWeight_ge_one_third (p : Nat.Primes) :
    (1 / 3 : ℝ) ≤ primeGammaBocksteinUnitWeight p := by
  rw [primeGammaBocksteinUnitWeight]
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have hden : 0 < (p.1 : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hden]
  nlinarith

/-- Cofinal exterior-square mass of the prime Bockstein packet exceeds the center term. -/
theorem primeBockstein_pairMass_gt_one
    {m : ℕ} (hm : 2 ≤ m) :
    1 < ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
      ∏ i ∈ s, preDivisorRiggedPrimeRealBocksteinVector m i := by
  classical
  let P := (Finset.univ : Finset (Fin (m + 3))).powersetCard 2
  have hlocal : ∀ s ∈ P, (1 / 9 : ℝ) ≤
      ∏ i ∈ s, preDivisorRiggedPrimeRealBocksteinVector m i := by
    intro s hs
    have hscard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
    have hprodneg :
        ∏ i ∈ s, preDivisorRiggedPrimeRealBocksteinVector m i =
          (-1 : ℝ) ^ s.card *
            ∏ i ∈ s, primeGammaBocksteinUnitWeight (nthPrimePoint i) := by
      calc
        ∏ i ∈ s, preDivisorRiggedPrimeRealBocksteinVector m i =
            ∏ i ∈ s, -primeGammaBocksteinUnitWeight (nthPrimePoint i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [preDivisorRiggedPrimeRealBocksteinVector,
            primeGammaCofinalBocksteinCoefficient_one_eq_neg_weight]
        _ = (-1 : ℝ) ^ s.card *
            ∏ i ∈ s, primeGammaBocksteinUnitWeight (nthPrimePoint i) := by
          simpa using (Finset.prod_neg (s := s)
            (fun i => primeGammaBocksteinUnitWeight (nthPrimePoint i)))
    rw [hprodneg, hscard]
    norm_num
    calc
      (1 / 9 : ℝ) = ∏ _i ∈ s, (1 / 3 : ℝ) := by
        simp [hscard, pow_two]
        norm_num
      _ ≤ ∏ i ∈ s, primeGammaBocksteinUnitWeight (nthPrimePoint i) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          norm_num
        · intro i hi
          exact primeGammaBocksteinUnitWeight_ge_one_third _
  have hlower := Finset.sum_le_sum hlocal
  have hconst : 1 < ∑ _s ∈ P, (1 / 9 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hPcard : P.card = (m + 3).choose 2 := by simp [P]
    rw [hPcard]
    rw [Nat.cast_choose_two]
    push_cast
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    norm_num
    ring_nf
    nlinarith
  exact hconst.trans_le (by simpa [P] using hlower)

/-- The additive even projection of every sufficiently large prime packet is negative at one. -/
theorem evenProjected_primeBockstein_neg
    {m : ℕ} (hm : 2 ≤ m) :
    evenProjectedUnitizedRealReservoirDeterminant
      (preDivisorRiggedPrimeRealBocksteinVector m) < 0 := by
  have hupper :=
    evenProjectedUnitizedRealReservoirDeterminant_le_one_sub_pairMass
      (preDivisorRiggedPrimeRealBocksteinVector_neg m)
  have hmass := primeBockstein_pairMass_gt_one hm
  linarith

/-- Canonical additive even projection of the holomorphic unitized SC determinant. -/
def preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection
    (m : ℕ) (z : ℂ) : ℂ :=
  (preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m z +
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m (-z)) / 2

theorem preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_zero
    (m : ℕ) :
    preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m 0 = 1 := by
  simp [preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection,
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_zero]

theorem preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_even
    (m : ℕ) (z : ℂ) :
    preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m (-z) =
      preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m z := by
  simp [preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection, add_comm]

theorem differentiable_preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection
    (m : ℕ) :
    Differentiable ℂ
      (preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m) := by
  unfold preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection
  exact
    ((differentiable_preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m).add
      ((differentiable_preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m).comp
        differentiable_neg)).div_const 2

theorem preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_one_re_neg
    {m : ℕ} (hm : 2 ≤ m) :
    (preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m 1).re < 0 := by
  have hone :=
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal m (1 : ℝ)
  have hnegone :=
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal m (-1 : ℝ)
  norm_num at hone hnegone
  rw [preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection, hone, hnegone]
  have hbneg :
      (fun i : Fin (m + 3) =>
        -primeGammaCofinalBocksteinCoefficient 1 (nthPrimePoint i)) =
        -(preDivisorRiggedPrimeRealBocksteinVector m) := by
    funext i
    rfl
  rw [hbneg]
  norm_num
  change evenProjectedUnitizedRealReservoirDeterminant
    (preDivisorRiggedPrimeRealBocksteinVector m) < 0
  exact evenProjected_primeBockstein_neg hm

/-- **Additive even-projection no-go.**  The canonical additive parity repair is entire,
even, and center-normalized, but its cofinal exterior-square polarity is incompatible with
normalized centered Xi. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_additiveEvenProjection :
    ¬ TendstoLocallyUniformly
      preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hconvOn : TendstoLocallyUniformlyOn
      preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection
      (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hpoint := hconvOn.tendsto_at (Set.mem_univ (1 : ℂ))
  have hre : Tendsto
      (fun m =>
        (preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m 1).re)
      atTop (nhds (XiC (1 : ℂ) / XiC 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hpoint
  have hevent : ∀ᶠ m : ℕ in atTop,
      (preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection m 1).re ≤ 0 := by
    filter_upwards [eventually_ge_atTop 2] with m hm
    exact
      (preDivisorRiggedPrimeHolomorphicAdditiveEvenProjection_one_re_neg hm).le
  have hle : (XiC (1 : ℂ) / XiC 0).re ≤ 0 := le_of_tendsto hre hevent
  exact (not_lt_of_ge hle) normalizedXiC_one_re_pos

end
end RHTower
