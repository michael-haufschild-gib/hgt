import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

open scoped BigOperators

namespace RHTower

/-- Boolean alias sum retained below a multiplicative physical cutoff. -/
def truncatedAliasSum {R : Type*} [CommRing R]
    (q : ℕ) (s : Finset ℕ) (ν : ℕ → R) (H : ℕ) : R :=
  ∑ t ∈ s.powerset,
    if q * ∏ p ∈ t, p ≤ H then
      (-1 : R) ^ t.card * ∏ p ∈ t, ν p
    else 0

/-- Complementary high-conductor tail of `truncatedAliasSum`. -/
def truncatedAliasHighSum {R : Type*} [CommRing R]
    (q : ℕ) (s : Finset ℕ) (ν : ℕ → R) (H : ℕ) : R :=
  ∑ t ∈ s.powerset,
    if H < q * ∏ p ∈ t, p then
      (-1 : R) ^ t.card * ∏ p ∈ t, ν p
    else 0

/-- Exact deletion-contraction recursion for a newly inserted inactive coordinate. -/
theorem truncatedAliasSum_insert {R : Type*} [CommRing R]
    {q p H : ℕ} {s : Finset ℕ} (hp : p ∉ s) (ν : ℕ → R) :
    truncatedAliasSum q (insert p s) ν H =
      truncatedAliasSum q s ν H - ν p * truncatedAliasSum (q * p) s ν H := by
  unfold truncatedAliasSum
  rw [Finset.sum_powerset_insert hp, sub_eq_add_neg]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t := fun hpin => hp ((Finset.mem_powerset.mp ht) hpin)
  simp only [Finset.prod_insert hpt, Finset.card_insert_of_notMem hpt]
  rw [← Nat.mul_assoc q p (∏ x ∈ t, x)]
  change
    (if (q * p) * ∏ x ∈ t, x ≤ H then
      (-1 : R) ^ (t.card + 1) * (ν p * ∏ x ∈ t, ν x) else 0) =
      -(ν p * (if (q * p) * ∏ x ∈ t, x ≤ H then
        (-1 : R) ^ t.card * ∏ x ∈ t, ν x else 0))
  by_cases hle : (q * p) * ∏ x ∈ t, x ≤ H
  · simp [hle, pow_succ]
    ring
  · simp [hle]

/-- The low- and high-conductor pieces partition the full Boolean Euler product exactly. -/
theorem truncatedAliasSum_add_highSum {R : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (ν : ℕ → R) :
    truncatedAliasSum q s ν H + truncatedAliasHighSum q s ν H =
      ∏ p ∈ s, (1 - ν p) := by
  unfold truncatedAliasSum truncatedAliasHighSum
  rw [← Finset.sum_add_distrib]
  calc
    (∑ t ∈ s.powerset,
      ((if q * ∏ p ∈ t, p ≤ H then
          (-1 : R) ^ t.card * ∏ p ∈ t, ν p else 0) +
        if H < q * ∏ p ∈ t, p then
          (-1 : R) ^ t.card * ∏ p ∈ t, ν p else 0)) =
        ∑ t ∈ s.powerset, (-1 : R) ^ t.card * ∏ p ∈ t, ν p := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases hle : q * ∏ p ∈ t, p ≤ H
      · simp [hle, not_lt_of_ge hle]
      · have hlt : H < q * ∏ p ∈ t, p := Nat.lt_of_not_ge hle
        simp [hle, hlt]
    _ = ∏ p ∈ s, (1 - ν p) := by
      simpa using (Finset.prod_sub (fun _ : ℕ => (1 : R)) ν s).symm

/-- If the cutoff retains exactly the empty subset and the singletons, its signed alias sum is
the first-order inclusion-exclusion expression `1 - ∑ p, ν p`. -/
theorem truncatedAliasSum_eq_one_sub_sum_of_rank_le_one {R : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (ν : ℕ → R)
    (hcut : ∀ t ∈ s.powerset,
      (q * ∏ p ∈ t, p ≤ H ↔ t.card ≤ 1)) :
    truncatedAliasSum q s ν H = 1 - ∑ p ∈ s, ν p := by
  unfold truncatedAliasSum
  have hfilter :
      s.powerset.filter (fun t => t.card ≤ 1) = insert ∅ (s.powersetCard 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hts, hcard⟩
      rcases Nat.eq_zero_or_pos t.card with hzero | hpos
      · exact Or.inl (Finset.card_eq_zero.mp hzero)
      · exact Or.inr ⟨hts, Nat.le_antisymm hcard hpos⟩
    · rintro (rfl | ⟨hts, hcard⟩)
      · simp
      · exact ⟨hts, hcard.le⟩
  calc
    (∑ t ∈ s.powerset,
      if q * ∏ p ∈ t, p ≤ H then
        (-1 : R) ^ t.card * ∏ p ∈ t, ν p else 0) =
        ∑ t ∈ s.powerset,
          if t.card ≤ 1 then (-1 : R) ^ t.card * ∏ p ∈ t, ν p else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [if_congr (hcut t ht) rfl rfl]
    _ = ∑ t ∈ s.powerset.filter (fun t => t.card ≤ 1),
          (-1 : R) ^ t.card * ∏ p ∈ t, ν p := by
      rw [Finset.sum_filter]
    _ = 1 - ∑ p ∈ s, ν p := by
      rw [hfilter, Finset.sum_insert (by simp), Finset.powersetCard_one, Finset.sum_map]
      simp [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- A rank-one cutoff can have negative mass even when every local density and every complete
survival factor is strictly positive. -/
theorem truncatedAliasSum_rank_le_one_sign_failure
    (q H : ℕ) (s : Finset ℕ) (ν : ℕ → ℝ)
    (hcut : ∀ t ∈ s.powerset,
      (q * ∏ p ∈ t, p ≤ H ↔ t.card ≤ 1))
    (hν : ∀ p ∈ s, 0 < ν p ∧ ν p < 1)
    (hmass : 1 < ∑ p ∈ s, ν p) :
    truncatedAliasSum q s ν H < 0 ∧ 0 < ∏ p ∈ s, (1 - ν p) := by
  constructor
  · rw [truncatedAliasSum_eq_one_sub_sum_of_rank_le_one q H s ν hcut]
    linarith
  · apply Finset.prod_pos
    intro p hp
    exact sub_pos.mpr (hν p hp).2

/-- Low physical-cutoff weight of an outer Boolean packet. -/
def physicalCutoffAliasLowWeight {R : Type*} [CommRing R]
    (q H : ℕ) (s t : Finset ℕ) (θ : ℕ → R) : R :=
  (∏ p ∈ t, θ p) *
    truncatedAliasSum (q * ∏ p ∈ t, p) (s \ t) θ H

/-- Complementary high physical-cutoff weight of an outer Boolean packet. -/
def physicalCutoffAliasHighWeight {R : Type*} [CommRing R]
    (q H : ℕ) (s t : Finset ℕ) (θ : ℕ → R) : R :=
  (∏ p ∈ t, θ p) *
    truncatedAliasHighSum (q * ∏ p ∈ t, p) (s \ t) θ H

/-- Complete active/survival Bernoulli weight of an outer Boolean packet. -/
def completeAliasWeight {R : Type*} [CommRing R]
    (s t : Finset ℕ) (θ : ℕ → R) : R :=
  (∏ p ∈ t, θ p) * ∏ p ∈ s \ t, (1 - θ p)

/-- **Coordinatewise cutoff joining.** Low and high weights rejoin to the complete weight before
any estimate is taken. -/
theorem physicalCutoffAliasLowWeight_add_highWeight
    {R : Type*} [CommRing R]
    (q H : ℕ) (s t : Finset ℕ) (θ : ℕ → R) :
    physicalCutoffAliasLowWeight q H s t θ +
        physicalCutoffAliasHighWeight q H s t θ =
      completeAliasWeight s t θ := by
  unfold physicalCutoffAliasLowWeight physicalCutoffAliasHighWeight completeAliasWeight
  rw [← mul_add, truncatedAliasSum_add_highSum]

/-- Complete alias weights have total mass one. -/
theorem sum_completeAliasWeight {R : Type*} [CommRing R]
    (s : Finset ℕ) (θ : ℕ → R) :
    ∑ t ∈ s.powerset, completeAliasWeight s t θ = 1 := by
  unfold completeAliasWeight
  rw [← Finset.prod_add]
  simp

/-- Adding a fresh coordinate preserves the total low-cutoff mass. -/
theorem sum_physicalCutoffAliasLowWeight_insert
    {R : Type*} [CommRing R]
    {q H p : ℕ} {s : Finset ℕ} (hp : p ∉ s) (θ : ℕ → R) :
    (∑ t ∈ (insert p s).powerset,
        physicalCutoffAliasLowWeight q H (insert p s) t θ) =
      ∑ t ∈ s.powerset, physicalCutoffAliasLowWeight q H s t θ := by
  rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hts : t ⊆ s := Finset.mem_powerset.mp ht
  have hpt : p ∉ t := fun hpin => hp (hts hpin)
  have hdiff0 : (insert p s) \ t = insert p (s \ t) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  have hdiff1 : (insert p s) \ insert p t = s \ t := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  have hpdiff : p ∉ s \ t := by simp [hp]
  unfold physicalCutoffAliasLowWeight
  rw [hdiff0, hdiff1, truncatedAliasSum_insert hpdiff]
  simp only [Finset.prod_insert hpt]
  rw [← Nat.mul_assoc q p (∏ x ∈ t, x)]
  ring_nf

/-- The low-cutoff weights carry the empty-packet indicator as total signed mass. -/
theorem sum_physicalCutoffAliasLowWeight {R : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (θ : ℕ → R) :
    (∑ t ∈ s.powerset, physicalCutoffAliasLowWeight q H s t θ) =
      if q ≤ H then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [physicalCutoffAliasLowWeight, truncatedAliasSum]
  | @insert p s hp ih =>
      rw [sum_physicalCutoffAliasLowWeight_insert hp θ, ih]

/-- The high-cutoff weights carry the complementary empty-packet indicator. -/
theorem sum_physicalCutoffAliasHighWeight {R : Type*} [CommRing R]
    (q H : ℕ) (s : Finset ℕ) (θ : ℕ → R) :
    (∑ t ∈ s.powerset, physicalCutoffAliasHighWeight q H s t θ) =
      if H < q then 1 else 0 := by
  have htotal :
      (∑ t ∈ s.powerset, physicalCutoffAliasLowWeight q H s t θ) +
          (∑ t ∈ s.powerset, physicalCutoffAliasHighWeight q H s t θ) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ t ∈ s.powerset,
          (physicalCutoffAliasLowWeight q H s t θ +
            physicalCutoffAliasHighWeight q H s t θ)) =
          ∑ t ∈ s.powerset, completeAliasWeight s t θ := by
            apply Finset.sum_congr rfl
            intro t _ht
            rw [physicalCutoffAliasLowWeight_add_highWeight]
      _ = 1 := sum_completeAliasWeight s θ
  rw [sum_physicalCutoffAliasLowWeight] at htotal
  by_cases hqH : q ≤ H
  · have hnot : ¬H < q := Nat.not_lt_of_ge hqH
    simpa [hqH, hnot] using htotal
  · have hHq : H < q := Nat.lt_of_not_ge hqH
    simpa [hqH, hHq] using htotal

/-- **Joined-response theorem.** Low and high cutoff pieces applied to the same response are
exactly the complete alias response.  No positivity is needed for this identity. -/
theorem physicalCutoffAliasResponse_join
    {R E : Type*} [CommRing R] [AddCommMonoid E] [Module R E]
    (q H : ℕ) (s : Finset ℕ) (θ : ℕ → R) (response : Finset ℕ → E) :
    (∑ t ∈ s.powerset, physicalCutoffAliasLowWeight q H s t θ • response t) +
        (∑ t ∈ s.powerset, physicalCutoffAliasHighWeight q H s t θ • response t) =
      ∑ t ∈ s.powerset, completeAliasWeight s t θ • response t := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [← add_smul, physicalCutoffAliasLowWeight_add_highWeight]

/-- Root-density specialization of the joined-response theorem. -/
theorem quadraticCongruencePhysicalCutoffAliasResponse_join
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (q H : ℕ) (s : Finset ℕ) (h : ℤ) (response : Finset ℕ → E) :
    (∑ t ∈ s.powerset,
        physicalCutoffAliasLowWeight q H s t
          (fun n => (quadraticCongruenceRootCountTotal n h : ℝ) / (n : ℝ)) • response t) +
      (∑ t ∈ s.powerset,
        physicalCutoffAliasHighWeight q H s t
          (fun n => (quadraticCongruenceRootCountTotal n h : ℝ) / (n : ℝ)) • response t) =
      ∑ t ∈ s.powerset,
        quadraticCongruenceAliasSurvivalWeight s t h • response t := by
  rw [physicalCutoffAliasResponse_join]
  rfl

/-- **Joined physical-cutoff contraction.** Although either cutoff half can be signed, their
common-response sum is the complete positive root-density probability average and has sharp
source-independent norm one. -/
theorem quadraticCongruencePhysicalCutoffAliasResponse_join_norm_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (q H : ℕ) (s : Finset ℕ) (hnz : ∀ n ∈ s, n ≠ 0) (h : ℤ)
    (response : Finset ℕ → E) (C : ℝ)
    (hresponse : ∀ t ∈ s.powerset, ‖response t‖ ≤ C) :
    ‖(∑ t ∈ s.powerset,
        physicalCutoffAliasLowWeight q H s t
          (fun n => (quadraticCongruenceRootCountTotal n h : ℝ) / (n : ℝ)) • response t) +
      (∑ t ∈ s.powerset,
        physicalCutoffAliasHighWeight q H s t
          (fun n => (quadraticCongruenceRootCountTotal n h : ℝ) / (n : ℝ)) • response t)‖ ≤ C := by
  rw [quadraticCongruencePhysicalCutoffAliasResponse_join]
  exact quadraticCongruenceAliasSurvivalContraction s hnz h response C hresponse

end RHTower
