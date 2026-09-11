import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanTransposeRepair

/-!
# Quantitative negative-mass cost of a complete coherent repair

For a genuine normalized fixed-left Big-Witt row, subtract one complete
coherent packet with arbitrary profile and finite prime set. Its retained
anchor mass lies between `1 - 2 * (K + delta)` and `1 + delta`, where `K`
is the reciprocal raw-mass source budget and `delta` is the total negative
real edge mass. A selected-half cut identity proves the upper removal bound;
incoming edges prove its matching lower bound.

The original reciprocal reader pays at most `A / 2` per unit of negative
mass. Vanishing negative mass forces prime retention and excludes zero energy
for `A > 0`. Conversely, erasing unit reciprocal energy forces an eventual
negative-mass floor `1 / (p + 4)`, including for the actual coherent-star
corrected row. These source laws do not supply a physical-reader agreement
or a source negative-mass estimate for that comparison, and do not prove RH.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

/-- At least half of a finite set of prime labels can be selected above that half-size. -/
theorem primeFinset_exists_large_half (s : Finset Nat.Primes) (hs : s.Nonempty) :
    ∃ t ⊆ s, 0 < t.card ∧ s.card ≤ 2 * t.card ∧
      ∀ q ∈ t, t.card ≤ (q : ℕ) := by
  classical
  let m := (s.card + 1) / 2
  have hs0 : 0 < s.card := Finset.card_pos.mpr hs
  have hm : 0 < m := by dsimp [m]; omega
  have hbad : (s.filter (fun q : Nat.Primes => (q : ℕ) < m)).card ≤ m - 1 := by
    have h : (s.filter (fun q : Nat.Primes => (q : ℕ) < m)).card ≤ (Finset.Icc 1 (m - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun q : Nat.Primes => (q : ℕ))
      · intro q hq
        have hlt := (Finset.mem_filter.mp hq).2
        exact Finset.mem_Icc.mpr ⟨q.2.pos, by change (q : ℕ) ≤ m - 1; omega⟩
      · intro p hp q hq hpq
        exact Subtype.ext hpq
    simpa using h
  have hpartition := s.card_filter_add_card_filter_not (fun q => (q : ℕ) < m)
  simp only [not_lt] at hpartition
  have hgood : m ≤ (s.filter (fun q : Nat.Primes => m ≤ (q : ℕ))).card := by
    dsimp [m] at *
    omega
  obtain ⟨t,ht,hcard⟩ := Finset.exists_subset_card_eq hgood
  refine ⟨t, (Finset.filter_subset _ _).trans' ht, ?_, ?_, ?_⟩
  · omega
  · dsimp [m] at hcard
    omega
  · intro q hq
    rw [hcard]
    exact (Finset.mem_filter.mp (ht hq)).2

/-- The selected side of a complete potential cut controls the total potential mass. -/
theorem finitePotential_cut_balance (s t : Finset Nat.Primes) (ht : t ⊆ s)
    (a : Nat.Primes → ℝ) :
    (t.card : ℝ) * (∑ q ∈ s, a q) - (s.card : ℝ) * (∑ q ∈ t, a q) ≤
      ∑ q ∈ s, ∑ r ∈ s, max (a r - a q) 0 := by
  classical
  calc
    _ = ∑ q ∈ t, ∑ r ∈ s, (a r - a q) := by
      simp [Finset.sum_sub_distrib, Finset.mul_sum, nsmul_eq_mul]
    _ ≤ ∑ q ∈ t, ∑ r ∈ s, max (a r - a q) 0 := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum (fun r hr => le_max_left _ _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun q hq hqt => Finset.sum_nonneg (fun r hr => le_max_right _ _))

/-- A reciprocal row and a complete potential have a quantitative negative-mass cost. -/
theorem finitePotential_reciprocal_removal_bound
    (s : Finset Nat.Primes) (w a : Nat.Primes → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ q ∈ s, w q ≤ K / (q : ℕ)) :
    (∑ q ∈ s, a q) ≤ 2 * (K +
      (∑ q ∈ s, max (a q - w q) 0) +
      (∑ q ∈ s, ∑ r ∈ s, max (a r - a q) 0)) := by
  classical
  rcases s.eq_empty_or_nonempty with he | hs
  · simp [he, hK]
  obtain ⟨t,ht,ht0,hcard,hlabels⟩ := primeFinset_exists_large_half s hs
  have htR : (0 : ℝ) < t.card := by exact_mod_cast ht0
  have htsR : (s.card : ℝ) ≤ 2 * t.card := by exact_mod_cast hcard
  have hsR : (1 : ℝ) ≤ s.card := by exact_mod_cast (Finset.card_pos.mpr hs)
  have hout0 : 0 ≤ ∑ q ∈ s, max (a q - w q) 0 :=
    Finset.sum_nonneg (fun q hq => le_max_right _ _)
  have hleaf0 : 0 ≤ ∑ q ∈ s, ∑ r ∈ s, max (a r - a q) 0 :=
    Finset.sum_nonneg (fun q hq => Finset.sum_nonneg (fun r hr => le_max_right _ _))
  have hweights : (∑ q ∈ t, w q) ≤ K := by
    calc
      _ ≤ ∑ q ∈ t, K / (t.card : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        apply (hw q (ht hq)).trans
        exact div_le_div_of_nonneg_left hK htR (by exact_mod_cast hlabels q hq)
      _ = K := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp
  have hselected : (∑ q ∈ t, a q) ≤ K + ∑ q ∈ s, max (a q - w q) 0 := by
    calc
      _ ≤ ∑ q ∈ t, (w q + max (a q - w q) 0) := by
        apply Finset.sum_le_sum
        intro q hq
        have h := le_max_left (a q - w q) 0
        linarith
      _ = (∑ q ∈ t, w q) + ∑ q ∈ t, max (a q - w q) 0 := Finset.sum_add_distrib
      _ ≤ K + ∑ q ∈ s, max (a q - w q) 0 := add_le_add hweights
        (Finset.sum_le_sum_of_subset_of_nonneg ht (fun q hq hqt => le_max_right _ _))
  have hcut := finitePotential_cut_balance s t ht a
  have hbound := mul_le_mul_of_nonneg_left hselected (Nat.cast_nonneg s.card)
  have hleaf := mul_le_mul_of_nonneg_right hsR hleaf0
  have hsize := mul_le_mul_of_nonneg_right htsR (add_nonneg (add_nonneg hK hout0) hleaf0)
  nlinarith

/-- Total negative real mass on the literal ordered prime edges. -/
def deningerBigWittNegativeRealMass
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) : ℝ :=
  ∑ i ∈ f.support, max (-(f i).re) 0

theorem deningerBigWittNegativeRealMass_nonneg
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    0 ≤ deningerBigWittNegativeRealMass f :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- Extend the off-diagonal real edge reader by zero on the diagonal. -/
def deningerBigWittEdgeRe (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (p q : Nat.Primes) : ℝ :=
  if h : p ≠ q then (f ⟨(p,q),h⟩).re else 0

def deningerBigWittEdgeNegative (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (p q : Nat.Primes) : ℝ := max (-deningerBigWittEdgeRe f p q) 0

theorem deningerBigWittNegativeRealMass_finset_le
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (s : Finset DeningerCalderonWittCrossPrimePacketIndex) :
    (∑ i ∈ s, max (-(f i).re) 0) ≤ deningerBigWittNegativeRealMass f := by
  classical
  have heq : deningerBigWittNegativeRealMass f =
      ∑ i ∈ f.support ∪ s, max (-(f i).re) 0 := by
    exact Finsupp.sum_of_support_subset f Finset.subset_union_left (fun _ (z : ℂ) => max (-z.re) 0) (by intros; simp)
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun i hi his => le_max_right _ _)

set_option backward.isDefEq.respectTransparency false in
theorem deningerBigWittEdgeNegative_square_le
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (s : Finset Nat.Primes) :
    (∑ p ∈ s, ∑ q ∈ s, deningerBigWittEdgeNegative f p q) ≤
      deningerBigWittNegativeRealMass f := by
  classical
  let t : Finset DeningerCalderonWittCrossPrimePacketIndex :=
    (s ×ˢ s).subtype (fun i : Nat.Primes × Nat.Primes => i.1 ≠ i.2)
  have heq : (∑ i ∈ t, max (-(f i).re) 0) =
      ∑ p ∈ s, ∑ q ∈ s, deningerBigWittEdgeNegative f p q := by
    trans ∑ i ∈ t, deningerBigWittEdgeNegative f i.1.1 i.1.2
    · apply Finset.sum_congr rfl
      intro i hi
      simp [deningerBigWittEdgeNegative, deningerBigWittEdgeRe, i.2]
    · change (∑ i ∈ (s ×ˢ s).subtype (fun i : Nat.Primes × Nat.Primes => i.1 ≠ i.2),
        deningerBigWittEdgeNegative f i.1.1 i.1.2) = _
      rw [Finset.sum_subtype_eq_sum_filter
        (fun i : Nat.Primes × Nat.Primes => deningerBigWittEdgeNegative f i.1 i.2),
        Finset.sum_filter]
      have hfun : (fun i : Nat.Primes × Nat.Primes => if i.1 ≠ i.2 then
          deningerBigWittEdgeNegative f i.1 i.2 else 0) =
          fun i => deningerBigWittEdgeNegative f i.1 i.2 := by
        funext i
        by_cases h : i.1 = i.2 <;>
          simp [h, deningerBigWittEdgeNegative, deningerBigWittEdgeRe]
      rw [hfun, Finset.sum_product]
  rw [← heq]
  exact deningerBigWittNegativeRealMass_finset_le f t

/-- Anchor-to-leaf and leaf-to-leaf negative masses use disjoint ordered edges. -/
theorem deningerBigWittEdgeNegative_anchor_leaf_le
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (s : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ s) :
    (∑ q ∈ s.erase p, deningerBigWittEdgeNegative f p q) +
      (∑ q ∈ s.erase p, ∑ r ∈ s.erase p, deningerBigWittEdgeNegative f q r) ≤
        deningerBigWittNegativeRealMass f := by
  classical
  have hrow (q : Nat.Primes) :
      (∑ r ∈ s.erase p, deningerBigWittEdgeNegative f q r) ≤
        ∑ r ∈ s, deningerBigWittEdgeNegative f q r :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun r hr hrp => le_max_right _ _)
  calc
    _ ≤ (∑ q ∈ s, deningerBigWittEdgeNegative f p q) +
        (∑ q ∈ s.erase p, ∑ r ∈ s, deningerBigWittEdgeNegative f q r) :=
      add_le_add (hrow p) (Finset.sum_le_sum (fun q hq => hrow q))
    _ = ∑ q ∈ s, ∑ r ∈ s, deningerBigWittEdgeNegative f q r := by
      rw [add_comm, Finset.sum_erase_add _ _ hp]
    _ ≤ _ := deningerBigWittEdgeNegative_square_le f s

/-- A complete coherent correction must pay negative edge mass to remove a reciprocal row. -/
theorem coherentRepair_removed_mass_le_negative_mass
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (p : Nat.Primes)
    (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ i, i.1.1 ≠ p → (f i).re = 0)
    (hrow : ∀ q (hpq : p ≠ q), (f ⟨(p,q),hpq⟩).re ≤ K / (q : ℕ))
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    (deningerBigWittLeftPrimeMarginal
      (deningerBigWittCrossPairFiniteRightLegPacket a s) p).re ≤
        2 * (K + deningerBigWittNegativeRealMass
          (f - deningerBigWittCrossPairFiniteRightLegPacket a s)) := by
  classical
  let g := f - deningerBigWittCrossPairFiniteRightLegPacket a s
  have hδ := deningerBigWittNegativeRealMass_nonneg g
  by_cases hp : p ∈ s
  · let t : Nat.Primes → ℝ := fun q => (a p).re - (a q).re
    have hout (q : Nat.Primes) (hq : q ∈ s.erase p) :
        max (t q - deningerBigWittEdgeRe f p q) 0 = deningerBigWittEdgeNegative g p q := by
      have hqp := (Finset.mem_erase.mp hq).1
      have hqs := (Finset.mem_erase.mp hq).2
      simp only [deningerBigWittEdgeNegative, deningerBigWittEdgeRe, dif_pos (Ne.symm hqp),
        g, Finsupp.sub_apply, Complex.sub_re, deningerBigWittCrossPairFiniteRightLegPacket_apply,
        hp, hqs, and_self, if_true, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re, t]
      congr 1
      ring
    have hleaf (q : Nat.Primes) (hq : q ∈ s.erase p)
        (r : Nat.Primes) (hr : r ∈ s.erase p) :
        max (t r - t q) 0 = deningerBigWittEdgeNegative g q r := by
      by_cases hqr : q = r
      · simp [hqr, deningerBigWittEdgeNegative, deningerBigWittEdgeRe]
      have hqp := (Finset.mem_erase.mp hq).1
      have hqs := (Finset.mem_erase.mp hq).2
      have hrs := (Finset.mem_erase.mp hr).2
      simp only [deningerBigWittEdgeNegative, deningerBigWittEdgeRe, dif_pos hqr,
        g, Finsupp.sub_apply, Complex.sub_re, hf (⟨(q,r),hqr⟩ : DeningerCalderonWittCrossPrimePacketIndex) hqp,
        deningerBigWittCrossPairFiniteRightLegPacket_apply,
        hqs, hrs, and_self, if_true, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re, t]
      congr 1
      ring
    have hcost : (∑ q ∈ s.erase p, max (t q - deningerBigWittEdgeRe f p q) 0) +
        (∑ q ∈ s.erase p, ∑ r ∈ s.erase p, max (t r - t q) 0) ≤
          deningerBigWittNegativeRealMass g := by
      have heq₁ := Finset.sum_congr rfl hout
      have heq₂ := Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (hleaf q hq))
      rw [heq₁, heq₂]
      exact deningerBigWittEdgeNegative_anchor_leaf_le g s p hp
    have hbound := finitePotential_reciprocal_removal_bound (s.erase p)
      (deningerBigWittEdgeRe f p) t K hK (by
        intro q hq
        rw [deningerBigWittEdgeRe, dif_pos (Ne.symm (Finset.mem_erase.mp hq).1)]
        exact hrow q _)
    rw [deningerBigWittLeftPrimeMarginal_coherent_re_sum_erase a s p hp]
    change (∑ q ∈ s.erase p, t q) ≤ 2 * (K + deningerBigWittNegativeRealMass g)
    linarith
  · have hm : (deningerBigWittLeftPrimeMarginal
        (deningerBigWittCrossPairFiniteRightLegPacket a s) p).re = 0 := by
      simp [deningerBigWittLeftPrimeMarginal_coherent, hp]
    rw [hm]
    exact mul_nonneg (by norm_num) (add_nonneg hK hδ)

set_option backward.isDefEq.respectTransparency false in
/-- Incoming negative mass bounds negative removal of the anchor. -/
theorem coherentRepair_neg_removed_mass_le_negative_mass
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (p : Nat.Primes)
    (hf : ∀ i, i.1.1 ≠ p → (f i).re = 0)
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    -(deningerBigWittLeftPrimeMarginal
      (deningerBigWittCrossPairFiniteRightLegPacket a s) p).re ≤
        deningerBigWittNegativeRealMass (f - deningerBigWittCrossPairFiniteRightLegPacket a s) := by
  classical
  let g := f - deningerBigWittCrossPairFiniteRightLegPacket a s
  by_cases hp : p ∈ s
  · rw [deningerBigWittLeftPrimeMarginal_coherent_re_sum_erase a s p hp, ← Finset.sum_neg_distrib]
    calc
      _ ≤ ∑ q ∈ s.erase p, deningerBigWittEdgeNegative g q p := by
        apply Finset.sum_le_sum
        intro q hq
        have hqp := (Finset.mem_erase.mp hq).1
        have hqs := (Finset.mem_erase.mp hq).2
        have heq : deningerBigWittEdgeRe g q p = (a p).re - (a q).re := by
          rw [deningerBigWittEdgeRe, dif_pos hqp]
          change (f (⟨(q,p),hqp⟩ : DeningerCalderonWittCrossPrimePacketIndex) -
            deningerBigWittCrossPairFiniteRightLegPacket a s
              (⟨(q,p),hqp⟩ : DeningerCalderonWittCrossPrimePacketIndex)).re = _
          rw [Complex.sub_re, hf _ hqp, deningerBigWittCrossPairFiniteRightLegPacket_apply,
            if_pos ⟨hqs,hp⟩, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re]
          ring
        rw [deningerBigWittEdgeNegative, heq]
        exact le_max_left _ _
      _ ≤ ∑ q ∈ s.erase p, ∑ r ∈ s, deningerBigWittEdgeNegative g q r := by
        apply Finset.sum_le_sum
        intro q hq
        exact Finset.single_le_sum (f := fun r => deningerBigWittEdgeNegative g q r)
          (fun r hr => le_max_right _ _) hp
      _ ≤ ∑ q ∈ s, ∑ r ∈ s, deningerBigWittEdgeNegative g q r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun q hq hqp => Finset.sum_nonneg (fun r hr => le_max_right _ _))
      _ ≤ _ := deningerBigWittEdgeNegative_square_le g s
  · simpa [deningerBigWittLeftPrimeMarginal_coherent, hp] using
      deningerBigWittNegativeRealMass_nonneg g

/-- The genuine row retains its anchor up to its source budget and negative real mass. -/
theorem deningerBigWittWoldSignedRepair_retained_mass_bounds (a n : ℕ)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    let g := deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
      deningerBigWittCrossPairFiniteRightLegPacket b s
    1 - 2 * (deningerBigWittWoldCoherentRemovalBudget a n + deningerBigWittNegativeRealMass g) ≤
      (deningerBigWittLeftPrimeMarginal g (nthPrimeSubtype a)).re ∧
    (deningerBigWittLeftPrimeMarginal g (nthPrimeSubtype a)).re ≤
      1 + deningerBigWittNegativeRealMass g := by
  dsimp only
  have hu := coherentRepair_removed_mass_le_negative_mass
    (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) (nthPrimeSubtype a)
    (deningerBigWittWoldCoherentRemovalBudget a n)
    (deningerBigWittWoldCoherentRemovalBudget_nonneg a n)
    (deningerBigWittWoldNormalizedPacket_re_zero_off_left a n)
    (deningerBigWittWoldNormalizedPacket_re_le_reciprocal a n) b s
  have hl := coherentRepair_neg_removed_mass_le_negative_mass
    (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) (nthPrimeSubtype a)
    (deningerBigWittWoldNormalizedPacket_re_zero_off_left a n) b s
  rw [deningerBigWittLeftPrimeMarginal_sub,
    deningerBigWittLeftPrimeMarginal_woldFixedLeftRightEdgeNormalizedPacket,
    Finsupp.sub_apply, Finsupp.single_eq_same, Complex.sub_re, Complex.one_re]
  constructor <;> linarith

/-- Small total negative real mass suffices for prime retention within one complete repair. -/
theorem tendsto_deningerBigWittWoldSignedRepair_retained_mass (a : ℕ)
    (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hneg : Tendsto (fun n => deningerBigWittNegativeRealMass
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))) atTop (nhds 0)) :
    Tendsto (fun n => (deningerBigWittLeftPrimeMarginal
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n)) (nthPrimeSubtype a)).re)
      atTop (nhds 1) := by
  let δ := fun n => deningerBigWittNegativeRealMass
    (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
      deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => 1 - 2 * (deningerBigWittWoldCoherentRemovalBudget a n + δ n))
    (h := fun n => 1 + δ n)
  · simpa using hconst.sub (((tendsto_deningerBigWittWoldCoherentRemovalBudget a).add hneg).const_mul 2)
  · simpa using hconst.add hneg
  · intro n
    exact (deningerBigWittWoldSignedRepair_retained_mass_bounds a n (b n) (s n)).1
  · intro n
    exact (deningerBigWittWoldSignedRepair_retained_mass_bounds a n (b n) (s n)).2

/-- Signed edge mass has a controlled cost for the original reciprocal energy reader. -/
theorem primeLabelledEnergyReporter_re_anchor_negative_mass_bound
    (A : ℝ) (hA : 0 ≤ A) (p : Nat.Primes)
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    (A / (p : ℕ)) * (deningerBigWittLeftPrimeMarginal f p).re -
      (A / 2) * deningerBigWittNegativeRealMass f ≤
        (primeLabelledEnergyReporter (fun q => A / (q : ℕ)) f).re := by
  classical
  have hm : primeLabelledEnergyReporter (fun q => if q = p then 1 else 0) f =
      deningerBigWittLeftPrimeMarginal f p := by
    rw [primeLabelledEnergyReporter_eq_marginal, finitePrimeMarginalEnergy_indicator]
  rw [← hm, primeLabelledEnergyReporter_re_sum, primeLabelledEnergyReporter_re_sum,
    deningerBigWittNegativeRealMass, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ max (-(f i).re) 0 := le_max_right _ _
  have hA2 : 0 ≤ A / 2 := div_nonneg hA (by norm_num)
  have hcost := mul_nonneg hA2 hn
  by_cases hip : i.1.1 = p
  · simp only [hip, if_true, one_mul]
    linarith
  · simp only [hip, if_false, zero_mul, mul_zero, zero_sub]
    have hc : 0 ≤ A / (i.1.1 : ℕ) := div_nonneg hA (by positivity)
    have hcle : A / (i.1.1 : ℕ) ≤ A / 2 :=
      div_le_div_of_nonneg_left hA (by norm_num) (by exact_mod_cast i.1.1.2.two_le)
    have hx : -(f i).re ≤ max (-(f i).re) 0 := le_max_left _ _
    have hxmul := mul_le_mul_of_nonneg_left hx hc
    have hcmul := mul_le_mul_of_nonneg_right hcle hn
    linarith

/-- A quantitative lower bound before any assumption on the negative-mass limit. -/
theorem deningerBigWittWoldSignedRepair_energy_lower (A : ℝ) (hA : 0 ≤ A) (a n : ℕ)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    let g := deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
      deningerBigWittCrossPairFiniteRightLegPacket b s
    (A / (nthPrimeSubtype a : ℕ)) *
      (1 - 2 * (deningerBigWittWoldCoherentRemovalBudget a n + deningerBigWittNegativeRealMass g)) -
      (A / 2) * deningerBigWittNegativeRealMass g ≤
        (primeLabelledEnergyReporter (fun q => A / (q : ℕ)) g).re := by
  dsimp only
  calc
    _ ≤ (A / (nthPrimeSubtype a : ℕ)) * (deningerBigWittLeftPrimeMarginal
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket b s) (nthPrimeSubtype a)).re -
      (A / 2) * deningerBigWittNegativeRealMass
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittCrossPairFiniteRightLegPacket b s) := by
      apply sub_le_sub_right
      exact mul_le_mul_of_nonneg_left
        (deningerBigWittWoldSignedRepair_retained_mass_bounds a n b s).1
        (div_nonneg hA (by positivity))
    _ ≤ _ := primeLabelledEnergyReporter_re_anchor_negative_mass_bound A hA (nthPrimeSubtype a) _

/-- Vanishing negative real mass and one joint complete repair cannot erase positive energy. -/
theorem deningerBigWittWoldSignedRepair_not_tendsto_energy_zero
    (A : ℝ) (hA : 0 < A) (a : ℕ)
    (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hneg : Tendsto (fun n => deningerBigWittNegativeRealMass
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))) atTop (nhds 0)) :
    ¬ Tendsto (fun n => primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))) atTop (nhds 0) := by
  intro hE
  have hEre : Tendsto (fun n => (primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))).re) atTop (nhds 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp hE
  have hmass := tendsto_deningerBigWittWoldSignedRepair_retained_mass a b s hneg
  have hlower := (hmass.const_mul (A / (nthPrimeSubtype a : ℕ))).sub (hneg.const_mul (A / 2))
  simp only [mul_one, mul_zero, sub_zero] at hlower
  have hbad := le_of_tendsto_of_tendsto' hlower hEre (fun n =>
    primeLabelledEnergyReporter_re_anchor_negative_mass_bound A hA.le (nthPrimeSubtype a) _)
  exact (not_le_of_gt (div_pos hA (nthPrimeSubtype_pos a))) hbad

/-- Exact cost inequality for erasing the unit reciprocal reader. -/
theorem deningerBigWittWoldSignedRepair_negative_mass_energy_tradeoff (a n : ℕ)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    let g := deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
      deningerBigWittCrossPairFiniteRightLegPacket b s
    1 - 2 * deningerBigWittWoldCoherentRemovalBudget a n -
      (nthPrimeSubtype a : ℝ) * (primeLabelledEnergyReporter (fun q => 1 / (q : ℕ)) g).re ≤
      (2 + (nthPrimeSubtype a : ℝ) / 2) * deningerBigWittNegativeRealMass g := by
  dsimp only
  have h := deningerBigWittWoldSignedRepair_energy_lower 1 (by norm_num) a n b s
  dsimp only at h
  have hp := nthPrimeSubtype_pos a
  have hm := mul_le_mul_of_nonneg_left h hp.le
  have hcancel : (nthPrimeSubtype a : ℝ) * (1 / (nthPrimeSubtype a : ℕ)) = 1 := by
    field_simp
  rw [mul_sub, ← mul_assoc, hcancel, one_mul] at hm
  nlinarith [hm]

/-- Erasing the original reciprocal energy with one complete repair forces persistent negative mass. -/
theorem deningerBigWittWoldSignedRepair_eventually_negative_mass_lower (a : ℕ)
    (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hE : Tendsto (fun n => primeLabelledEnergyReporter (fun q => 1 / (q : ℕ))
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))) atTop (nhds 0)) :
    ∀ᶠ n in atTop, 1 / ((nthPrimeSubtype a : ℝ) + 4) ≤ deningerBigWittNegativeRealMass
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n)) := by
  have hEre : Tendsto (fun n => (primeLabelledEnergyReporter (fun q => 1 / (q : ℕ))
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))).re) atTop (nhds 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp hE
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlim := (hc.sub ((tendsto_deningerBigWittWoldCoherentRemovalBudget a).const_mul 2)).sub
    (hEre.const_mul (nthPrimeSubtype a : ℝ))
  simp only [mul_zero, sub_zero] at hlim
  have hevent := hlim.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  filter_upwards [hevent] with n hn
  have hbound := deningerBigWittWoldSignedRepair_negative_mass_energy_tradeoff a n (b n) (s n)
  dsimp only at hbound hn
  have hp : 0 < (nthPrimeSubtype a : ℝ) + 4 := by positivity
  apply (div_le_iff₀ hp).mpr
  nlinarith

/-- The explicit graph-invisible coherent-star correction carries a persistent negative edge cost. -/
theorem deningerBigWittCoherentStarCorrectedRow_eventually_negative_mass_lower (a : ℕ) :
    ∀ᶠ n in atTop, 1 / ((nthPrimeSubtype a : ℝ) + 4) ≤
      deningerBigWittNegativeRealMass (deningerBigWittCoherentStarCorrectedRow a n) := by
  classical
  choose b hb using fun n => deningerBigWittCoherentStar_is_complete (nthPrimeSubtype a)
    (deningerBigWittCoherentStarPrimeSet (nthPrimeSubtype a) n)
  have heq (n : ℕ) : deningerBigWittCoherentStarCorrectedRow a n =
      deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n)
          (deningerBigWittCoherentStarPrimeSet (nthPrimeSubtype a) n) := by
    rw [deningerBigWittCoherentStarCorrectedRow, deningerBigWittCoherentStarSequence, hb n]
  have hE := tendsto_deningerBigWittCoherentStarCorrectedRow_energy 1 a
  simp_rw [heq] at hE
  have h := deningerBigWittWoldSignedRepair_eventually_negative_mass_lower a b
    (deningerBigWittCoherentStarPrimeSet (nthPrimeSubtype a)) hE
  simpa only [← heq] using h

end
end RHTower.HedenmalmThetaSource
