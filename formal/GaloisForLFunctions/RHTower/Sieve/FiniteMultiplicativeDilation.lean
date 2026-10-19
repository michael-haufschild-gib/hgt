import GaloisForLFunctions.RHTower.Sieve.LocalEulerConstruction
import GaloisForLFunctions.RHTower.RetainedPrimeMobiusEulerIdentity
import GaloisForLFunctions.RHTower.Sieve.DistanceLocalChanges
import GaloisForLFunctions.HTGeometry.FiniteFourierTopCoefficient

/-!
# Multiplicative expansions of the existing dilation operator

Lemma 18.2 of *Ordinary two-point correlations of multiplicative functions* gives
an expansion indexed by subsets of the dilating primes. We construct its local
Euler factors explicitly and prove the exact identity for `primeSourceDilation`.

Allowing complex coefficients gives a shorter expansion: if the positive dilation
has `r` distinct prime factors, `r + 1` roots of unity suffice. All components are
normalized multiplicative functions, preserve local data outside those primes,
and remain 1-bounded for unit-disc source data. The coefficient absolute mass is
one, which is optimal even among arbitrary bounded-component exact expansions.

Consequently one phase component dominates any finite weighted dilation sum with
no loss. Its pretentious distance differs from the source by a uniform finite-prime
budget. These are exact finite identities and inequalities; no analytic premise
or asymptotic correlation estimate is used.
-/

open Finset
namespace RHTower.Sieve
noncomputable section

/-- The normalized local lift of a prime-power dilation; `a + 1` is always positive. -/
def dilationLiftLocal (A : ℕ → ℕ → ℂ) (a p k : ℕ) : ℂ :=
  if k = 0 then 1 else if (a + 1).factorization p ≤ k then
    normalizedPrimePowerValue A p (k - (a + 1).factorization p) else 0

/-- The normalized local factor supported only at exponent zero. -/
def dilationZeroLocal (k : ℕ) : ℂ := if k = 0 then 1 else 0

/-- Local data for one signed multiplicative component of a dilation. -/
def dilationComponentData (A : ℕ → ℕ → ℂ) (a : ℕ) (E : Finset ℕ) (p k : ℕ) : ℂ :=
  if p ∈ (a + 1).primeFactors then
    if p ∈ E then dilationZeroLocal k else dilationLiftLocal A a p k
  else A p k

/-- Explicit normalized multiplicative components indexed by subsets of the dilating primes. -/
def dilationComponent (A : ℕ → ℕ → ℂ) (a : ℕ) (E : Finset ℕ) : ArithmeticFunction ℂ :=
  localEuler (dilationComponentData A a E)

theorem dilationComponent_isMultiplicative (A : ℕ → ℕ → ℂ) (a : ℕ) (E : Finset ℕ) :
    (dilationComponent A a E).IsMultiplicative := localEuler_isMultiplicative _

private theorem normalized_dilationComponentData (A : ℕ → ℕ → ℂ)
    (a : ℕ) (E : Finset ℕ) (p k : ℕ) :
    normalizedPrimePowerValue (dilationComponentData A a E) p k =
      if p ∈ (a + 1).primeFactors then
        if p ∈ E then dilationZeroLocal k else dilationLiftLocal A a p k
      else normalizedPrimePowerValue A p k := by
  by_cases hk : k = 0 <;> by_cases hp : p ∈ (a + 1).primeFactors <;>
    by_cases hE : p ∈ E <;>
    simp [normalizedPrimePowerValue, dilationComponentData, dilationLiftLocal,
      dilationZeroLocal, hk, hp, hE]

/-- Exact prime-power data; every prime outside the dilation retains the original local values. -/
theorem dilationComponent_prime_pow (A : ℕ → ℕ → ℂ) (a : ℕ) (E : Finset ℕ)
    (p : Nat.Primes) (k : ℕ) :
    dilationComponent A a E ((p : ℕ) ^ k) =
      if (p : ℕ) ∈ (a + 1).primeFactors then
        if (p : ℕ) ∈ E then dilationZeroLocal k else dilationLiftLocal A a p k
      else normalizedPrimePowerValue A p k := by
  rw [dilationComponent, localEuler_prime_pow]
  change normalizedPrimePowerValue (dilationComponentData A a E) p k = _
  exact normalized_dilationComponentData A a E p k

private def dilationProduct (A : ℕ → ℕ → ℂ) (a n : ℕ) : ℂ :=
  (∏ p ∈ (a + 1).primeFactors,
    (dilationLiftLocal A a p (n.factorization p) - dilationZeroLocal (n.factorization p))) *
  ∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
    normalizedPrimePowerValue A p (n.factorization p)

private theorem dilationComponent_eq_product (A : ℕ → ℕ → ℂ) (a n : ℕ)
    (E : Finset ℕ) (hE : E ⊆ (a + 1).primeFactors) (hn : n ≠ 0) :
    dilationComponent A a E n =
      (∏ p ∈ (a + 1).primeFactors \ E, dilationLiftLocal A a p (n.factorization p)) *
      (∏ p ∈ E, dilationZeroLocal (n.factorization p)) *
      ∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
        normalizedPrimePowerValue A p (n.factorization p) := by
  rw [dilationComponent, localEuler_eq_prod_on_union _ n (a + 1).primeFactors, if_neg hn]
  simp_rw [normalized_dilationComponentData]
  rw [← prod_sdiff (subset_union_left : (a + 1).primeFactors ⊆
    (a + 1).primeFactors ∪ n.primeFactors)]
  have hset : ((a + 1).primeFactors ∪ n.primeFactors) \ (a + 1).primeFactors =
      n.primeFactors \ (a + 1).primeFactors := by
    ext p
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hset]
  have hout : (∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
      if p ∈ (a + 1).primeFactors then
        if p ∈ E then dilationZeroLocal (n.factorization p)
        else dilationLiftLocal A a p (n.factorization p)
      else normalizedPrimePowerValue A p (n.factorization p)) =
      ∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
        normalizedPrimePowerValue A p (n.factorization p) := by
    apply prod_congr rfl
    intro p hp
    rw [if_neg (mem_sdiff.mp hp).2]
  rw [hout]
  have hin : (∏ p ∈ (a + 1).primeFactors,
      if p ∈ (a + 1).primeFactors then
        if p ∈ E then dilationZeroLocal (n.factorization p)
        else dilationLiftLocal A a p (n.factorization p)
      else normalizedPrimePowerValue A p (n.factorization p)) =
      (∏ p ∈ (a + 1).primeFactors \ E, dilationLiftLocal A a p (n.factorization p)) *
      ∏ p ∈ E, dilationZeroLocal (n.factorization p) := by
    rw [← prod_sdiff hE]
    congr 1
    · apply prod_congr rfl
      intro p hp
      simp only [if_pos (mem_sdiff.mp hp).1, if_neg (mem_sdiff.mp hp).2]
    · apply prod_congr rfl
      intro p hp
      simp only [if_pos (hE hp), if_pos hp]
  rw [hin]
  ring

private theorem sum_dilationComponent_eq_product (A : ℕ → ℕ → ℂ) (a n : ℕ)
    (hn : n ≠ 0) :
    (∑ E ∈ (a + 1).primeFactors.powerset, (-1 : ℂ) ^ E.card * dilationComponent A a E n) =
      dilationProduct A a n := by
  calc
    _ = (∑ E ∈ (a + 1).primeFactors.powerset,
        (-1 : ℂ) ^ E.card *
          (∏ p ∈ (a + 1).primeFactors \ E, dilationLiftLocal A a p (n.factorization p)) *
          ∏ p ∈ E, dilationZeroLocal (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
          normalizedPrimePowerValue A p (n.factorization p) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro E hE
      rw [dilationComponent_eq_product A a n E (mem_powerset.mp hE) hn]
      ring
    _ = _ := by rw [← prod_sub]; rfl

private theorem dilationProduct_eq_source (A : ℕ → ℕ → ℂ) (a n : ℕ) (hn : n ≠ 0) :
    dilationProduct A a n = primeSourceDilation (a + 1) (localEuler A) n := by
  by_cases hdiv : a + 1 ∣ n
  · rw [primeSourceDilation, if_pos hdiv]
    have hquot : n / (a + 1) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv) (Nat.succ_pos a)).ne'
    have hquotdvd : n / (a + 1) ∣ n := ⟨a + 1, (Nat.div_mul_cancel hdiv).symm⟩
    have hquotFactors : (n / (a + 1)).primeFactors ⊆
        (a + 1).primeFactors ∪ n.primeFactors :=
      (Nat.primeFactors_mono hquotdvd hn).trans subset_union_right
    rw [localEuler_eq_prod_on_union A (n / (a + 1))
      ((a + 1).primeFactors ∪ n.primeFactors), if_neg hquot,
      union_eq_left.mpr hquotFactors]
    have hfac (p : ℕ) : (n / (a + 1)).factorization p =
        n.factorization p - (a + 1).factorization p := by
      rw [Nat.factorization_div hdiv]
      rfl
    simp_rw [hfac]
    rw [← prod_sdiff (subset_union_left : (a + 1).primeFactors ⊆
      (a + 1).primeFactors ∪ n.primeFactors)]
    have hset : ((a + 1).primeFactors ∪ n.primeFactors) \ (a + 1).primeFactors =
        n.primeFactors \ (a + 1).primeFactors := by
      ext p
      simp only [mem_sdiff, mem_union]
      tauto
    rw [hset]
    have hlocal : (∏ p ∈ (a + 1).primeFactors,
        (dilationLiftLocal A a p (n.factorization p) - dilationZeroLocal (n.factorization p))) =
        ∏ p ∈ (a + 1).primeFactors,
          normalizedPrimePowerValue A p (n.factorization p - (a + 1).factorization p) := by
      apply prod_congr rfl
      intro p hp
      have ha : (a + 1).factorization p ≠ 0 :=
        Finsupp.mem_support_iff.mp (by simpa using hp)
      have hle : (a + 1).factorization p ≤ n.factorization p :=
        (Nat.factorization_le_iff_dvd (Nat.succ_ne_zero a) hn).mpr hdiv p
      have hk : n.factorization p ≠ 0 := by omega
      simp [dilationLiftLocal, dilationZeroLocal, hk, hle]
    have hout : (∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
        normalizedPrimePowerValue A p (n.factorization p)) =
        ∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
          normalizedPrimePowerValue A p (n.factorization p - (a + 1).factorization p) := by
      apply prod_congr rfl
      intro p hp
      have ha : (a + 1).factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa using (mem_sdiff.mp hp).2)
      rw [ha, Nat.sub_zero]
    rw [dilationProduct, hlocal, hout]
    exact mul_comm _ _
  · rw [primeSourceDilation, if_neg hdiv]
    have hnot : ¬ ∀ p : ℕ, (a + 1).factorization p ≤ n.factorization p := by
      intro h
      exact hdiv ((Nat.factorization_le_iff_dvd (Nat.succ_ne_zero a) hn).mp
        (Finsupp.le_def.mpr h))
    push Not at hnot
    obtain ⟨p, hp⟩ := hnot
    have hmem : p ∈ (a + 1).primeFactors := by
      have ha : (a + 1).factorization p ≠ 0 := by omega
      simpa using Finsupp.mem_support_iff.mpr ha
    have hz : dilationLiftLocal A a p (n.factorization p) -
        dilationZeroLocal (n.factorization p) = 0 := by
      by_cases hk : n.factorization p = 0 <;>
        simp [dilationLiftLocal, dilationZeroLocal, hk, Nat.not_le.mpr hp]
    rw [dilationProduct, prod_eq_zero hmem hz, zero_mul]

/-- The existing dilation operator is a signed sum of normalized multiplicative components. -/
theorem primeSourceDilation_eq_signed_components (A : ℕ → ℕ → ℂ) (a n : ℕ) :
    primeSourceDilation (a + 1) (localEuler A) n =
      ∑ E ∈ (a + 1).primeFactors.powerset,
        (-1 : ℂ) ^ E.card * dilationComponent A a E n := by
  by_cases hn : n = 0
  · subst n
    simp [primeSourceDilation, dilationComponent]
  · rw [sum_dilationComponent_eq_product A a n hn, dilationProduct_eq_source A a n hn]

private theorem norm_localEuler_le_one_of_local (A : ℕ → ℕ → ℂ)
    (hA : ∀ p k, ‖A p k‖ ≤ 1) (n : ℕ) : ‖localEuler A n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n; simp
  · change ‖if n = 0 then 0 else ∏ p ∈ n.primeFactors, A p (n.factorization p)‖ ≤ 1
    rw [if_neg hn, norm_prod]
    exact prod_le_one (fun _ _ => norm_nonneg _) (fun p _ => hA p _)

/-- Bounded local data produce a globally 1-bounded normalized multiplicative source. -/
theorem norm_localEuler_unitDisk_le_one
    (A : ℕ → ℕ → {z : ℂ // ‖z‖ ≤ 1}) (n : ℕ) :
    ‖localEuler (fun p k => (A p k : ℂ)) n‖ ≤ 1 :=
  norm_localEuler_le_one_of_local _ (fun p k => (A p k).property) n

private theorem norm_normalizedPrimePowerValue_unitDisk_le_one
    (A : ℕ → ℕ → {z : ℂ // ‖z‖ ≤ 1}) (p k : ℕ) :
    ‖normalizedPrimePowerValue (fun p k => (A p k : ℂ)) p k‖ ≤ 1 := by
  by_cases hk : k = 0
  · simp [normalizedPrimePowerValue, hk]
  · simpa [normalizedPrimePowerValue, hk] using (A p k).property

private theorem norm_dilationLiftLocal_unitDisk_le_one
    (A : ℕ → ℕ → {z : ℂ // ‖z‖ ≤ 1}) (a p k : ℕ) :
    ‖dilationLiftLocal (fun p k => (A p k : ℂ)) a p k‖ ≤ 1 := by
  unfold dilationLiftLocal
  split_ifs
  · simp
  · exact norm_normalizedPrimePowerValue_unitDisk_le_one A p _
  · simp

/-- Every term in the signed expansion is 1-bounded when the source local data are. -/
theorem norm_dilationComponent_unitDisk_le_one
    (A : ℕ → ℕ → {z : ℂ // ‖z‖ ≤ 1}) (a : ℕ) (E : Finset ℕ) (n : ℕ) :
    ‖dilationComponent (fun p k => (A p k : ℂ)) a E n‖ ≤ 1 := by
  apply norm_localEuler_le_one_of_local
  intro p k
  unfold dilationComponentData
  split_ifs
  · by_cases hk : k = 0 <;> simp [dilationZeroLocal, hk]
  · exact norm_dilationLiftLocal_unitDisk_le_one A a p k
  · exact (A p k).property

/-- A phase rotates each positive local exponent at a dilating prime. -/
def dilationPhaseData (A : ℕ → ℕ → ℂ) (a : ℕ) (z : ℂ) (p k : ℕ) : ℂ :=
  if p ∈ (a + 1).primeFactors then
    if k = 0 then 1 else z * dilationLiftLocal A a p k
  else A p k

/-- A normalized multiplicative component in the shorter Fourier expansion. -/
def dilationPhaseComponent (A : ℕ → ℕ → ℂ) (a : ℕ) (z : ℂ) : ArithmeticFunction ℂ :=
  localEuler (dilationPhaseData A a z)

theorem dilationPhaseComponent_isMultiplicative (A : ℕ → ℕ → ℂ) (a : ℕ) (z : ℂ) :
    (dilationPhaseComponent A a z).IsMultiplicative := localEuler_isMultiplicative _

private theorem normalized_dilationPhaseData (A : ℕ → ℕ → ℂ)
    (a : ℕ) (z : ℂ) (p k : ℕ) :
    normalizedPrimePowerValue (dilationPhaseData A a z) p k =
      if p ∈ (a + 1).primeFactors then
        dilationZeroLocal k + z * (dilationLiftLocal A a p k - dilationZeroLocal k)
      else normalizedPrimePowerValue A p k := by
  by_cases hk : k = 0 <;> by_cases hp : p ∈ (a + 1).primeFactors <;>
    simp [normalizedPrimePowerValue, dilationPhaseData, dilationZeroLocal,
      dilationLiftLocal, hk, hp]

/-- Outside the dilating primes, every prime-power value is unchanged. -/
theorem dilationPhaseComponent_prime_pow (A : ℕ → ℕ → ℂ) (a : ℕ) (z : ℂ)
    (p : Nat.Primes) (k : ℕ) :
    dilationPhaseComponent A a z ((p : ℕ) ^ k) =
      if (p : ℕ) ∈ (a + 1).primeFactors then
        dilationZeroLocal k + z * (dilationLiftLocal A a p k - dilationZeroLocal k)
      else normalizedPrimePowerValue A p k := by
  rw [dilationPhaseComponent, localEuler_prime_pow]
  change normalizedPrimePowerValue (dilationPhaseData A a z) p k = _
  exact normalized_dilationPhaseData A a z p k

private theorem dilationPhaseComponent_eq_product (A : ℕ → ℕ → ℂ)
    (a n : ℕ) (z : ℂ) (hn : n ≠ 0) :
    dilationPhaseComponent A a z n =
      (∏ p ∈ (a + 1).primeFactors,
        (dilationZeroLocal (n.factorization p) + z *
          (dilationLiftLocal A a p (n.factorization p) -
            dilationZeroLocal (n.factorization p)))) *
      ∏ p ∈ n.primeFactors \ (a + 1).primeFactors,
        normalizedPrimePowerValue A p (n.factorization p) := by
  rw [dilationPhaseComponent, localEuler_eq_prod_on_union _ n (a + 1).primeFactors,
    if_neg hn]
  simp_rw [normalized_dilationPhaseData]
  rw [← prod_sdiff (subset_union_left : (a + 1).primeFactors ⊆
    (a + 1).primeFactors ∪ n.primeFactors)]
  have hset : ((a + 1).primeFactors ∪ n.primeFactors) \ (a + 1).primeFactors =
      n.primeFactors \ (a + 1).primeFactors := by
    ext p
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hset, mul_comm]
  congr 1
  · apply prod_congr rfl
    intro p hp
    rw [if_pos hp]
  · apply prod_congr rfl
    intro p hp
    rw [if_neg (mem_sdiff.mp hp).2]

/-- Fourier projection replaces the signed subset expansion by only `ω(a+1)+1` terms. -/
theorem primeSourceDilation_eq_fourier_components (A : ℕ → ℕ → ℂ) (a n : ℕ) :
    primeSourceDilation (a + 1) (localEuler A) n =
      ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        GaloisForLFunctions.HTGeometry.topFourierWeight (a + 1).primeFactors.card h *
          dilationPhaseComponent A a (ZMod.stdAddChar h) n := by
  by_cases hn : n = 0
  · subst n
    simp [primeSourceDilation, dilationPhaseComponent]
  · rw [← dilationProduct_eq_source A a n hn, dilationProduct]
    rw [GaloisForLFunctions.HTGeometry.prod_eq_topFourier_average
      (a + 1).primeFactors (fun p => dilationZeroLocal (n.factorization p))]
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro h _
    rw [dilationPhaseComponent_eq_product A a n _ hn]
    unfold GaloisForLFunctions.HTGeometry.topFourierWeight
    ring

/-- Unit phases preserve the source's unit-disc bound. -/
theorem norm_dilationPhaseComponent_unitDisk_le_one
    (A : ℕ → ℕ → {z : ℂ // ‖z‖ ≤ 1}) (a n : ℕ) (z : Circle) :
    ‖dilationPhaseComponent (fun p k => (A p k : ℂ)) a (z : ℂ) n‖ ≤ 1 := by
  apply norm_localEuler_le_one_of_local
  intro p k
  unfold dilationPhaseData
  split_ifs
  · simp
  · simpa only [norm_mul, Circle.norm_coe, one_mul] using
      norm_dilationLiftLocal_unitDisk_le_one A a p k
  · exact (A p k).property

/-- The complete Fourier expansion has absolute coefficient mass one. -/
theorem sum_norm_dilationFourierWeight (a : ℕ) :
    (∑ h : ZMod ((a + 1).primeFactors.card + 1),
      ‖GaloisForLFunctions.HTGeometry.topFourierWeight (a + 1).primeFactors.card h‖) = 1 :=
  GaloisForLFunctions.HTGeometry.sum_norm_topFourierWeight _

/-- Arbitrary finite weighted samples inherit the exact short Fourier expansion. -/
theorem sum_primeSourceDilation_eq_fourier_components {I : Type*}
    (A : ℕ → ℕ → ℂ) (a : ℕ) (S : Finset I) (ν : I → ℕ) (w : I → ℂ) :
    (∑ i ∈ S, w i * primeSourceDilation (a + 1) (localEuler A) (ν i)) =
      ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        GaloisForLFunctions.HTGeometry.topFourierWeight (a + 1).primeFactors.card h *
          ∑ i ∈ S, w i * dilationPhaseComponent A a (ZMod.stdAddChar h) (ν i) := by
  simp_rw [primeSourceDilation_eq_fourier_components, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro i _
  ring

/-- A dilation correlation is bounded by the corresponding weighted phase correlations. -/
theorem norm_sum_primeSourceDilation_le_fourier_norm_sum {I : Type*}
    (A : ℕ → ℕ → ℂ) (a : ℕ) (S : Finset I) (ν : I → ℕ) (w : I → ℂ) :
    ‖∑ i ∈ S, w i * primeSourceDilation (a + 1) (localEuler A) (ν i)‖ ≤
      ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        ‖GaloisForLFunctions.HTGeometry.topFourierWeight (a + 1).primeFactors.card h‖ *
          ‖∑ i ∈ S, w i * dilationPhaseComponent A a (ZMod.stdAddChar h) (ν i)‖ := by
  rw [sum_primeSourceDilation_eq_fourier_components]
  calc
    _ ≤ ∑ h : ZMod ((a + 1).primeFactors.card + 1),
        ‖GaloisForLFunctions.HTGeometry.topFourierWeight (a + 1).primeFactors.card h *
          ∑ i ∈ S, w i * dilationPhaseComponent A a (ZMod.stdAddChar h) (ν i)‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul]

/-- One phase component always dominates a given finite dilation correlation, with no loss. -/
theorem exists_dilationPhaseComponent_norm_sum_ge {I : Type*}
    (A : ℕ → ℕ → ℂ) (a : ℕ) (S : Finset I) (ν : I → ℕ) (w : I → ℂ) :
    ∃ h : ZMod ((a + 1).primeFactors.card + 1),
      ‖∑ i ∈ S, w i * primeSourceDilation (a + 1) (localEuler A) (ν i)‖ ≤
        ‖∑ i ∈ S, w i * dilationPhaseComponent A a (ZMod.stdAddChar h) (ν i)‖ := by
  obtain ⟨h, _, hmax⟩ := Finset.exists_max_image
    (univ : Finset (ZMod ((a + 1).primeFactors.card + 1)))
    (fun h => ‖∑ i ∈ S, w i * dilationPhaseComponent A a (ZMod.stdAddChar h) (ν i)‖)
    univ_nonempty
  refine ⟨h, (norm_sum_primeSourceDilation_le_fourier_norm_sum A a S ν w).trans ?_⟩
  calc
    _ ≤ ∑ j : ZMod ((a + 1).primeFactors.card + 1),
        ‖GaloisForLFunctions.HTGeometry.topFourierWeight (a + 1).primeFactors.card j‖ *
          ‖∑ i ∈ S, w i * dilationPhaseComponent A a (ZMod.stdAddChar h) (ν i)‖ := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hmax j hj) (norm_nonneg _)
    _ = _ := by rw [← sum_mul, sum_norm_dilationFourierWeight, one_mul]

/-- Pretentious distance only reads the prime entries of local Euler data. -/
theorem mulDistSq_localEuler (A : ℕ → ℕ → ℂ) (t : ℝ) (N : ℕ) :
    mulDistSq (localEuler A) t (Nat.primesLE N) =
      mulDistSq (fun p => A p 1) t (Nat.primesLE N) := by
  unfold mulDistSq
  apply sum_congr rfl
  intro p hp
  rw [localEuler_prime A ⟨p, Nat.prime_of_mem_primesLE hp⟩]

/-- The Fourier components change distance only through the finite dilating-prime set. -/
theorem abs_mulDistSq_dilationPhaseComponent_sub_le
    (A : ℕ → ℕ → ℂ) (a : ℕ) (z : ℂ) (t : ℝ) (N : ℕ) :
    |mulDistSq (dilationPhaseComponent A a z) t (Nat.primesLE N) -
      mulDistSq (localEuler A) t (Nat.primesLE N)| ≤
      ∑ p ∈ (a + 1).primeFactors, ‖A p 1 - z * dilationLiftLocal A a p 1‖ / (p : ℝ) := by
  change |mulDistSq (localEuler (dilationPhaseData A a z)) t (Nat.primesLE N) -
    mulDistSq (localEuler A) t (Nat.primesLE N)| ≤ _
  rw [mulDistSq_localEuler, mulDistSq_localEuler]
  have hdata : (fun p => dilationPhaseData A a z p 1) =
      finiteValuePatch (a + 1).primeFactors (fun p => A p 1)
        (fun p => z * dilationLiftLocal A a p 1) := by
    funext p
    simp [dilationPhaseData, finiteValuePatch]
  rw [hdata]
  exact abs_mulDistSq_patch_sub_le _ _ t (Nat.primesLE N) (a + 1).primeFactors

/-- For unit-disc data, every Fourier component has the same uniform finite distance budget. -/
theorem abs_mulDistSq_dilationPhaseComponent_unitDisk_sub_le
    (A : ℕ → ℕ → {z : ℂ // ‖z‖ ≤ 1}) (a : ℕ) (z : Circle) (t : ℝ) (N : ℕ) :
    |mulDistSq (dilationPhaseComponent (fun p k => (A p k : ℂ)) a (z : ℂ))
        t (Nat.primesLE N) -
      mulDistSq (localEuler (fun p k => (A p k : ℂ))) t (Nat.primesLE N)| ≤
      2 * ∑ p ∈ (a + 1).primeFactors, 1 / (p : ℝ) := by
  refine (abs_mulDistSq_dilationPhaseComponent_sub_le _ a z t N).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  have hnorm : ‖(A p 1 : ℂ) - (z : ℂ) *
      dilationLiftLocal (fun p k => (A p k : ℂ)) a p 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Circle.norm_coe, one_mul]
    linarith [(A p 1).property, norm_dilationLiftLocal_unitDisk_le_one A a p 1]
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg p : (0 : ℝ) ≤ p)

/-- Any bounded-component approximation must pay at least one in coefficient mass plus error.
At the dilation point the source is exactly one, so mass one is optimal for an exact expansion. -/
theorem dilation_approximation_mass_lower_bound {I : Type*}
    (A : ℕ → ℕ → ℂ) (a : ℕ) (S : Finset I) (w : I → ℂ)
    (F : I → ℕ → {z : ℂ // ‖z‖ ≤ 1}) :
    1 ≤ ‖primeSourceDilation (a + 1) (localEuler A) (a + 1) -
      ∑ i ∈ S, w i * (F i (a + 1) : ℂ)‖ + ∑ i ∈ S, ‖w i‖ := by
  have hvalue : primeSourceDilation (a + 1) (localEuler A) (a + 1) = 1 := by
    simp [primeSourceDilation]
  rw [hvalue]
  have hsum : ‖∑ i ∈ S, w i * (F i (a + 1) : ℂ)‖ ≤ ∑ i ∈ S, ‖w i‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply sum_le_sum
    intro i _
    rw [norm_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (F i (a + 1)).property (norm_nonneg (w i))
  have htri := norm_add_le
    ((1 : ℂ) - ∑ i ∈ S, w i * (F i (a + 1) : ℂ))
    (∑ i ∈ S, w i * (F i (a + 1) : ℂ))
  simp only [sub_add_cancel, norm_one] at htri
  linarith

end
end RHTower.Sieve
