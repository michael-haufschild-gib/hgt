import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSpatialL2
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeLayerExtraction
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTFixedCutoffCount
import GaloisForLFunctions.RHTower.Sieve.MaynardTwoAlternativeGapReceiver

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

/-- Reindexed even-cell fibre of an arbitrary finite cell family. -/
def maynardEvenCellFibre (B : Finset ℕ) (K : ℕ) : Finset ℕ :=
  (Finset.range K).filter fun i => 2 * i ∈ B

/-- Reindexed odd-cell fibre of an arbitrary finite cell family. -/
def maynardOddCellFibre (B : Finset ℕ) (K : ℕ) : Finset ℕ :=
  (Finset.range K).filter fun i => 2 * i + 1 ∈ B

/-- Original even-index cells of a finite family. -/
def maynardEvenCells (B : Finset ℕ) : Finset ℕ :=
  B.filter fun m => m % 2 = 0

/-- Original odd-index cells of a finite family. -/
def maynardOddCells (B : Finset ℕ) : Finset ℕ :=
  B.filter fun m => ¬(m % 2 = 0)

theorem maynardEvenCells_union_maynardOddCells (B : Finset ℕ) :
    maynardEvenCells B ∪ maynardOddCells B = B := by
  classical
  ext m
  simp only [maynardEvenCells, maynardOddCells, Finset.mem_union,
    Finset.mem_filter]
  tauto

theorem disjoint_maynardEvenCells_maynardOddCells (B : Finset ℕ) :
    Disjoint (maynardEvenCells B) (maynardOddCells B) := by
  classical
  exact Finset.disjoint_left.mpr fun m he ho =>
    (Finset.mem_filter.mp ho).2 (Finset.mem_filter.mp he).2

/-- Reindexed and original even cells have identical cardinality below `2K`. -/
theorem card_maynardEvenCellFibre_eq_card_maynardEvenCells
    {B : Finset ℕ} {K : ℕ} (hB : B ⊆ Finset.range (2 * K)) :
    (maynardEvenCellFibre B K).card = (maynardEvenCells B).card := by
  classical
  apply Finset.card_nbij (fun i => 2 * i)
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).2, by simp⟩
  · intro i hi j hj hij
    exact Nat.mul_left_cancel (by omega) hij
  · intro m hm
    have hmB := (Finset.mem_filter.mp hm).1
    have hmEven := (Finset.mem_filter.mp hm).2
    have hmRange := Finset.mem_range.mp (hB hmB)
    refine ⟨m / 2, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        omega
      · have htwo : 2 * (m / 2) = m := by omega
        simpa only [htwo] using hmB
    · have htwo : 2 * (m / 2) = m := by omega
      exact htwo

/-- Reindexed and original odd cells have identical cardinality below `2K`. -/
theorem card_maynardOddCellFibre_eq_card_maynardOddCells
    {B : Finset ℕ} {K : ℕ} (hB : B ⊆ Finset.range (2 * K)) :
    (maynardOddCellFibre B K).card = (maynardOddCells B).card := by
  classical
  apply Finset.card_nbij (fun i => 2 * i + 1)
  · intro i hi
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).2, by simp [Nat.add_mod]⟩
  · intro i hi j hj hij
    have hmul : 2 * i = 2 * j := Nat.add_right_cancel hij
    exact Nat.mul_left_cancel (by omega) hmul
  · intro m hm
    have hmB := (Finset.mem_filter.mp hm).1
    have hmOdd := (Finset.mem_filter.mp hm).2
    have hmRange := Finset.mem_range.mp (hB hmB)
    refine ⟨m / 2, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        omega
      · have hodd : 2 * (m / 2) + 1 = m := by omega
        simpa only [hodd] using hmB
    · have hodd : 2 * (m / 2) + 1 = m := by omega
      exact hodd

/-- A fixed-ambient physical packet is exactly the sum of its even- and odd-cell packets. -/
theorem maynardFixedAmbientPhysicalDefectPacket_eq_even_add_odd
    (B : Finset ℕ) {a : ℝ → ℂ} (ha : Continuous a)
    {lambda N R H : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) :
    maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1 =
      maynardFixedAmbientPhysicalDefectPacket (maynardEvenCells B)
          a lambda N R H 1 +
        maynardFixedAmbientPhysicalDefectPacket (maynardOddCells B)
          a lambda N R H 1 := by
  calc
    maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1 =
        maynardFixedAmbientPhysicalDefectPacket
          (maynardEvenCells B ∪ maynardOddCells B)
            a lambda N R H 1 := by
      rw [maynardEvenCells_union_maynardOddCells B]
    _ = _ := maynardFixedAmbientPhysicalDefectPacket_union
      (disjoint_maynardEvenCells_maynardOddCells B)
        ha hlambda hN hR hH

/-- If a packet is large, at least one parity packet retains half its norm. -/
theorem large_maynardFixedAmbientPhysicalDefectPacket_even_or_odd
    (B : Finset ℕ) {a : ℝ → ℂ} (ha : Continuous a)
    {lambda N R H D : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hlarge : D ≤
      ‖maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1‖) :
    D / 2 ≤
        ‖maynardFixedAmbientPhysicalDefectPacket (maynardEvenCells B)
          a lambda N R H 1‖ ∨
      D / 2 ≤
        ‖maynardFixedAmbientPhysicalDefectPacket (maynardOddCells B)
          a lambda N R H 1‖ := by
  rw [maynardFixedAmbientPhysicalDefectPacket_eq_even_add_odd
    B ha hlambda hN hR hH] at hlarge
  by_contra hnone
  push Not at hnone
  have htriangle := norm_add_le
    (maynardFixedAmbientPhysicalDefectPacket (maynardEvenCells B)
      a lambda N R H 1)
    (maynardFixedAmbientPhysicalDefectPacket (maynardOddCells B)
      a lambda N R H 1)
  linarith

/-- Pointwise `L¹` companion to spatial equation-(111).  A source bounded by `V` on selected
cells produces a fixed-ambient physical packet of norm at most `2 V · card`. -/
theorem norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
    {S : Finset ℕ} {a : ℝ → ℂ}
    {lambda N R H V : ℝ} (hlambda : 0 < lambda)
    (hN : 0 < N) (hR : 0 < R) (hH : 0 < H) (hV0 : 0 ≤ V)
    (hV : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ V) :
    ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖ ≤
      2 * V * (S.card : ℝ) := by
  have hbase : 0 < lambda * N := mul_pos hlambda hN
  have hRscaled : 0 < lambda * R := mul_pos hlambda hR
  have hHscaled : 0 < lambda * H := mul_pos hlambda hH
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖∑ m ∈ S, a ((m : ℝ) + u) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
        2 * V * (S.card : ℝ) := by
    intro u hu
    calc
      ‖∑ m ∈ S, a ((m : ℝ) + u) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
          ∑ m ∈ S, ‖a ((m : ℝ) + u) *
            (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
                ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I) -
              routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
                ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _m ∈ S, 2 * V := by
        apply Finset.sum_le_sum
        intro m hm
        have hKR0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
          hbase hRscaled
          (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
        have hKH0 := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
          hbase hHscaled
          (s := (1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) (by simp)
        have hKR : ‖routeTNormalizedSmoothWindowMellin
            (lambda * N) (lambda * R)
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
          simpa using hKR0
        have hKH : ‖routeTNormalizedSmoothWindowMellin
            (lambda * N) (lambda * H)
            ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤ 1 := by
          simpa using hKH0
        rw [norm_mul]
        calc
          ‖a ((m : ℝ) + u)‖ *
              ‖routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
                  ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I)) -
                routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
                  ((1 : ℂ) + ((((m : ℝ) + u : ℝ) : ℂ) * I))‖ ≤
              V * 2 := by
            apply mul_le_mul (hV m hm u hu)
            · exact (norm_sub_le _ _).trans (by linarith)
            · exact norm_nonneg _
            · exact hV0
          _ = 2 * V := by ring
      _ = 2 * V * (S.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [maynardFixedAmbientPhysicalDefectPacket]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := 2 * V * (S.card : ℝ))
    (f := fun u : ℝ =>
      ∑ m ∈ S, a ((m : ℝ) + u) *
        (routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * R)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin (lambda * N) (lambda * H)
            ((1 : ℂ) + (((m : ℝ) + u : ℝ) : ℂ) * I))) (by
      intro u hu
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact hpoint u ⟨hu.1.le, hu.2⟩)
  simpa using hint

/-- Pointwise packet bound on any subfamily of one exact amplitude band. -/
theorem norm_maynardFixedAmbientPhysicalDefectPacket_amplitudeBand_subset_le
    {U S : Finset ℕ} {a : ℝ → ℂ} {c : ℕ → ℝ}
    {lambda N R H V : ℝ}
    (hlambda : 0 < lambda) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hV : 0 < V)
    (hS : S ⊆ maynardUnitCellAmplitudeBand U a c V)
    (hmax : ∀ m ∈ U, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ ‖a (c m)‖) :
    ‖maynardFixedAmbientPhysicalDefectPacket S a lambda N R H 1‖ ≤
      4 * V * (S.card : ℝ) := by
  have hsource : ∀ m ∈ S, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
    intro m hm u hu
    have hmBand := hS hm
    have hmU :=
      maynardUnitCellAmplitudeBand_subset U a c V hmBand
    exact (hmax m hmU u hu).trans
      (maynardUnitCellAmplitudeBand_upper
        (U := U) (A := a) (c := c) hmBand)
  have hbound :=
    norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
      hlambda hN hR hH (show 0 ≤ 2 * V by positivity) hsource
  calc
    _ ≤ 2 * (2 * V) * (S.card : ℝ) := hbound
    _ = 4 * V * (S.card : ℝ) := by ring

/-- A sufficiently large parity packet rules out the first Maynard alternative and forces the
amplitude-cancelling second alternative. -/
theorem routeT_second_alternative_of_large_amplitudeBand_packet
    {q : ℕ} {packet D R T x alpha V : ℝ}
    (hV : 0 < V) (hlog : 0 ≤ Real.log T)
    (hpacket : D ≤ packet) (hupper : packet ≤ 4 * V * R)
    (hthreshold :
      4 * V * x ^ (1 - alpha) ≤ D * (Real.log T) ^ q)
    (halt : IsRouteTMaynardTwoAlternative q R T x alpha) :
    R ≤ T * x ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hlogPow : 0 ≤ (Real.log T) ^ q := pow_nonneg hlog q
  have hscale : 0 < 4 * V := mul_pos (by norm_num) hV
  have hlarge : x ^ (1 - alpha) ≤ R * (Real.log T) ^ q := by
    have hscaled : 4 * V * x ^ (1 - alpha) ≤
        4 * V * (R * (Real.log T) ^ q) := by
      calc
      4 * V * x ^ (1 - alpha) ≤
          D * (Real.log T) ^ q := hthreshold
      _ ≤ packet * (Real.log T) ^ q :=
        mul_le_mul_of_nonneg_right hpacket hlogPow
      _ ≤ (4 * V * R) * (Real.log T) ^ q :=
        mul_le_mul_of_nonneg_right hupper hlogPow
      _ = 4 * V * (R * (Real.log T) ^ q) := by ring
    rw [mul_comm (4 * V) (x ^ (1 - alpha)),
      mul_comm (4 * V) (R * (Real.log T) ^ q)] at hscaled
    exact (mul_le_mul_iff_left₀ hscale).mp hscaled
  exact routeT_second_alternative_of_large_error hlarge halt

/-- Exact parity-fibre cardinal decomposition for a family below `2K`. -/
theorem card_eq_card_maynardEvenCellFibre_add_card_maynardOddCellFibre
    {B : Finset ℕ} {K : ℕ} (hB : B ⊆ Finset.range (2 * K)) :
    B.card = (maynardEvenCellFibre B K).card +
      (maynardOddCellFibre B K).card := by
  classical
  have hfilter :
      (Finset.range (2 * K)).filter (fun m => m ∈ B) = B := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro hm
      exact ⟨Finset.mem_range.mp (hB hm), hm⟩
  have hcard :
      B.card = ∑ m ∈ Finset.range (2 * K),
        if m ∈ B then (1 : ℕ) else 0 := by
    calc
      B.card = ((Finset.range (2 * K)).filter (fun m => m ∈ B)).card := by
        rw [hfilter]
      _ = ∑ m ∈ Finset.range (2 * K),
          if m ∈ B then (1 : ℕ) else 0 := by
        rw [Finset.card_filter]
  rw [hcard]
  calc
    (∑ m ∈ Finset.range (2 * K), if m ∈ B then (1 : ℕ) else 0) =
        (∑ m ∈ {m ∈ Finset.range (2 * K) | m % 2 = 0},
          if m ∈ B then (1 : ℕ) else 0) +
        ∑ m ∈ {m ∈ Finset.range (2 * K) | ¬(m % 2 = 0)},
          if m ∈ B then (1 : ℕ) else 0 := by
      exact (Finset.sum_filter_add_sum_filter_not
        (Finset.range (2 * K)) (fun m => m % 2 = 0)
          (fun m => if m ∈ B then (1 : ℕ) else 0)).symm
    _ = (∑ i ∈ Finset.range K, if 2 * i ∈ B then (1 : ℕ) else 0) +
        ∑ i ∈ Finset.range K,
          if 2 * i + 1 ∈ B then (1 : ℕ) else 0 := by
      rw [sum_filter_even_eq_sum_range, sum_filter_odd_eq_sum_range]
      have heven : (2 * K + 1) / 2 = K := by omega
      have hodd : (2 * K) / 2 = K := by omega
      rw [heven, hodd]
    _ = (maynardEvenCellFibre B K).card +
        (maynardOddCellFibre B K).card := by
      simp [maynardEvenCellFibre, maynardOddCellFibre]

/-- Reindexing one parity of unit-cell representatives produces a globally one-spaced sequence. -/
theorem unitCellRepresentative_parity_gap
    {c : ℕ → ℝ}
    (hc : ∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1))
    (p i : ℕ) :
    c (2 * i + p) + 1 ≤ c (2 * (i + 1) + p) := by
  have hlo := (hc (2 * (i + 1) + p)).1
  have hhi := (hc (2 * i + p)).2
  push_cast at hlo hhi
  linarith

/-- Parity transport for the fixed-cutoff selected-cell capstone.  Any finite family of literal
unit-cell representatives below `2K` is the disjoint sum of two receiver-ready spaced fibres.
The two fibres may land in different Maynard alternatives, so the unconditional output is their
sum. -/
theorem exists_eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_count :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      3 / 4 ≤ alpha → 0 < V →
      ∀ (B : Finset ℕ), B ⊆ Finset.range (2 * K) →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ B, T ≤ c m ∧ c m ≤ 2 * T) →
      (∀ m ∈ B,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (c m : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - 1) ≤ V) →
      ((B.card : ℝ) ≤
        2 * (maynardHarmonicFactor K 1 *
              T ^ (mu * (1 - alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha) +
            maynardHarmonicFactor K 1 *
              T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha))) := by
  obtain ⟨A, hcount⟩ :=
    exists_eventually_routeT_selectedCell_fixedCutoff_all_amplitude
  refine ⟨A, ?_⟩
  filter_upwards [hcount, eventually_gt_atTop (1 : ℝ)] with T hcountT hT
  intro L X K mu N0 alpha V hX hL hXL hXscale hcut hmuLo hmuHi
    halpha hV B hB c hc hband haggregate hreserve
  let S0 : Finset ℕ := maynardEvenCellFibre B K
  let S1 : Finset ℕ := maynardOddCellFibre B K
  let lam0 : ℕ → ℝ := fun i => c (2 * i)
  let lam1 : ℕ → ℝ := fun i => c (2 * i + 1)
  have hS0 : S0 ⊆ Finset.range K := by
    exact Finset.filter_subset _ _
  have hS1 : S1 ⊆ Finset.range K := by
    exact Finset.filter_subset _ _
  have hmem0 : ∀ i ∈ S0, 2 * i ∈ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmem1 : ∀ i ∈ S1, 2 * i + 1 ∈ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hband0 : ∀ i ∈ S0, T ≤ lam0 i ∧ lam0 i ≤ 2 * T := by
    intro i hi
    exact hband (2 * i) (hmem0 i hi)
  have hband1 : ∀ i ∈ S1, T ≤ lam1 i ∧ lam1 i ≤ 2 * T := by
    intro i hi
    exact hband (2 * i + 1) (hmem1 i hi)
  have hgap0 : ∀ i, lam0 i + 1 ≤ lam0 (i + 1) := by
    intro i
    exact unitCellRepresentative_parity_gap hc 0 i
  have hgap1 : ∀ i, lam1 i + 1 ≤ lam1 (i + 1) := by
    intro i
    exact unitCellRepresentative_parity_gap hc 1 i
  have hdiam0 : ∀ r ∈ S0, ∀ s ∈ S0, |lam0 s - lam0 r| ≤ T := by
    intro r hr s hs
    have hrb := hband0 r hr
    have hsb := hband0 s hs
    rw [abs_le]
    constructor <;> linarith
  have hdiam1 : ∀ r ∈ S1, ∀ s ∈ S1, |lam1 s - lam1 r| ≤ T := by
    intro r hr s hs
    have hrb := hband1 r hr
    have hsb := hband1 s hs
    rw [abs_le]
    constructor <;> linarith
  have haggregate0 : ∀ i ∈ S0,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam0 i : ℝ) * Complex.I)‖ := by
    intro i hi
    exact haggregate (2 * i) (hmem0 i hi)
  have haggregate1 : ∀ i ∈ S1,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam1 i : ℝ) * Complex.I)‖ := by
    intro i hi
    exact haggregate (2 * i + 1) (hmem1 i hi)
  have hcount0 := hcountT hX hL hXL hXscale hcut hmuLo hmuHi
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
    (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * T)
    S0 hS0 lam0 hband0 hgap0 hdiam0 haggregate0 hreserve
  have hcount1 := hcountT hX hL hXL hXscale hcut hmuLo hmuHi
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
    (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * T)
    S1 hS1 lam1 hband1 hgap1 hdiam1 haggregate1 hreserve
  let F : ℝ := maynardHarmonicFactor K 1 *
    T ^ (mu * (1 - alpha) -
      routeTSelectedCellAmplitudeReserve A T alpha)
  let G : ℝ := maynardHarmonicFactor K 1 *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
      routeTSelectedCellAmplitudeReserve A T alpha)
  have hF : 0 ≤ F := by
    exact mul_nonneg (maynardHarmonicFactor_pos K (by norm_num)).le
      (Real.rpow_nonneg (by linarith : 0 ≤ T) _)
  have hG : 0 ≤ G := by
    exact mul_nonneg (maynardHarmonicFactor_pos K (by norm_num)).le
      (Real.rpow_nonneg (by linarith : 0 ≤ T) _)
  have h0 : (S0.card : ℝ) ≤ F + G := by
    rcases hcount0 with hfirst | hsecond
    · exact hfirst.trans (le_add_of_nonneg_right hG)
    · exact hsecond.trans (le_add_of_nonneg_left hF)
  have h1 : (S1.card : ℝ) ≤ F + G := by
    rcases hcount1 with hfirst | hsecond
    · exact hfirst.trans (le_add_of_nonneg_right hG)
    · exact hsecond.trans (le_add_of_nonneg_left hF)
  have hcardNat :=
    card_eq_card_maynardEvenCellFibre_add_card_maynardOddCellFibre hB
  have hcardNat' : B.card = S0.card + S1.card := by
    simpa only [S0, S1] using hcardNat
  have hcard : (B.card : ℝ) = (S0.card : ℝ) + (S1.card : ℝ) := by
    rw [hcardNat', Nat.cast_add]
  calc
    (B.card : ℝ) = (S0.card : ℝ) + (S1.card : ℝ) := hcard
    _ ≤ (F + G) + (F + G) := add_le_add h0 h1
    _ = 2 * (maynardHarmonicFactor K 1 *
              T ^ (mu * (1 - alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha) +
            maynardHarmonicFactor K 1 *
              T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha)) := by
      dsimp only [F, G]
      ring

/-- Receiver-normalized parity transport.  Both parity fibres retain their own Maynard
first-or-second alternative, so a later large-error argument can eliminate the first branch
without losing the `V²` cancellation on the surviving fibre. -/
theorem eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_twoAlternative
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      3 / 4 ≤ alpha → 0 < V → (K : ℝ) ≤ T →
      ∀ (B : Finset ℕ), B ⊆ Finset.range (2 * K) →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ B, T ≤ c m ∧ c m ≤ 2 * T) →
      (∀ m ∈ B,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (c m : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - 1) ≤ V) →
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre B K).card : ℝ) T (T ^ mu) alpha ∧
        IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre B K).card : ℝ) T (T ^ mu) alpha := by
  obtain ⟨A, hcount⟩ :=
    exists_eventually_routeT_selectedCell_fixedCutoff_all_amplitude
  filter_upwards [hcount,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A q,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A 0,
    eventually_gt_atTop (1 : ℝ)] with T hcountT hcostQ hcost0 hT
  intro L X K mu N0 alpha V hX hL hXL hXscale hcut hmuLo hmuHi
    halpha hV hK B hB c hc hband haggregate hreserve
  let S0 : Finset ℕ := maynardEvenCellFibre B K
  let S1 : Finset ℕ := maynardOddCellFibre B K
  let lam0 : ℕ → ℝ := fun i => c (2 * i)
  let lam1 : ℕ → ℝ := fun i => c (2 * i + 1)
  have hS0 : S0 ⊆ Finset.range K := Finset.filter_subset _ _
  have hS1 : S1 ⊆ Finset.range K := Finset.filter_subset _ _
  have hmem0 : ∀ i ∈ S0, 2 * i ∈ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmem1 : ∀ i ∈ S1, 2 * i + 1 ∈ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hband0 : ∀ i ∈ S0, T ≤ lam0 i ∧ lam0 i ≤ 2 * T := by
    intro i hi
    exact hband (2 * i) (hmem0 i hi)
  have hband1 : ∀ i ∈ S1, T ≤ lam1 i ∧ lam1 i ≤ 2 * T := by
    intro i hi
    exact hband (2 * i + 1) (hmem1 i hi)
  have hgap0 : ∀ i, lam0 i + 1 ≤ lam0 (i + 1) := by
    intro i
    exact unitCellRepresentative_parity_gap hc 0 i
  have hgap1 : ∀ i, lam1 i + 1 ≤ lam1 (i + 1) := by
    intro i
    exact unitCellRepresentative_parity_gap hc 1 i
  have hdiam0 : ∀ r ∈ S0, ∀ s ∈ S0, |lam0 s - lam0 r| ≤ T := by
    intro r hr s hs
    have hrb := hband0 r hr
    have hsb := hband0 s hs
    rw [abs_le]
    constructor <;> linarith
  have hdiam1 : ∀ r ∈ S1, ∀ s ∈ S1, |lam1 s - lam1 r| ≤ T := by
    intro r hr s hs
    have hrb := hband1 r hr
    have hsb := hband1 s hs
    rw [abs_le]
    constructor <;> linarith
  have haggregate0 : ∀ i ∈ S0,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam0 i : ℝ) * Complex.I)‖ := by
    intro i hi
    exact haggregate (2 * i) (hmem0 i hi)
  have haggregate1 : ∀ i ∈ S1,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam1 i : ℝ) * Complex.I)‖ := by
    intro i hi
    exact haggregate (2 * i + 1) (hmem1 i hi)
  have hraw0 := hcountT hX hL hXL hXscale hcut hmuLo hmuHi
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
    (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * T)
    S0 hS0 lam0 hband0 hgap0 hdiam0 haggregate0 hreserve
  have hraw1 := hcountT hX hL hXL hXscale hcut hmuLo hmuHi
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
    (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * T)
    S1 hS1 lam1 hband1 hgap1 hdiam1 haggregate1 hreserve
  have hreservePos : 0 < routeTSelectedCellAmplitudeReserve A T alpha :=
    routeTSelectedCellAmplitudeReserve_pos hT
  have normalize :
      ∀ {R : ℝ},
      (R ≤ maynardHarmonicFactor K 1 *
            T ^ (mu * (1 - alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha) ∨
        R ≤ maynardHarmonicFactor K 1 *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha)) →
      IsRouteTMaynardTwoAlternative q R T (T ^ mu) alpha := by
    intro R hraw
    apply routeT_two_alternative_of_reserved_height_count
      hT rfl hreservePos
    rcases hraw with hfirst | hsecond
    · left
      exact maynard_count_receiver_margin_general hT.le hfirst
        (hcostQ alpha K 1 hK (by norm_num))
    · right
      have hsecond' := maynard_count_receiver_margin_general
        (q := 0) hT.le hsecond (hcost0 alpha K 1 hK (by norm_num))
      simpa using hsecond'
  constructor
  · simpa only [S0] using normalize hraw0
  · simpa only [S1] using normalize hraw1

/-- An exact dyadic amplitude band of the fixed left-base packet automatically satisfies both
receiver-normalized parity alternatives at its adaptive amplitude. -/
theorem eventually_routeT_leftWindowRelevant_amplitudeBand_twoAlternative
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 V : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < V →
      heathBrownEligibleBoxCost L X 60 *
          (N0 / (2 ^ (2 * 60) : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
      (K : ℝ) ≤ T →
      ∀ (U : Finset ℕ), U ⊆ Finset.range (2 * K) →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ U, T ≤ c m ∧ c m ≤ 2 * T) →
      let a : ℝ → ℂ := fun y =>
        heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0 ((1 : ℂ) + (y : ℝ) * Complex.I)
      let B := maynardUnitCellAmplitudeBand U a c V
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre B K).card : ℝ) T (T ^ mu)
            (routeTAdaptiveCellAmplitude L X 60 N0 V) ∧
        IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre B K).card : ℝ) T (T ^ mu)
            (routeTAdaptiveCellAmplitude L X 60 N0 V) := by
  filter_upwards [
    eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_twoAlternative q
  ] with T hreceiver
  intro L X K mu N0 V hX hL hXL hXscale hcut hmuLo hmuHi
    hD hV hlow hK U hU c hc hordinate
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate
      L X 60 T (mu / 120) N0 ((1 : ℂ) + (y : ℝ) * Complex.I)
  let B : Finset ℕ := maynardUnitCellAmplitudeBand U a c V
  have hB : B ⊆ Finset.range (2 * K) :=
    (maynardUnitCellAmplitudeBand_subset U a c V).trans hU
  have halpha : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X 60 N0 V :=
    routeTAdaptiveCellAmplitude_threeQuarter_le L X 60
      (by norm_num) hX hD hV hlow
  have hband : ∀ m ∈ B, T ≤ c m ∧ c m ≤ 2 * T := by
    intro m hm
    exact hordinate m (maynardUnitCellAmplitudeBand_subset U a c V hm)
  have haggregate : ∀ m ∈ B,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (c m : ℝ) * Complex.I)‖ := by
    intro m hm
    exact maynardUnitCellAmplitudeBand_lower
      (U := U) (A := a) (c := c) hm
  have hreserve : ∀ box : HeathBrownBoxChoice L X 60,
      IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
      IsHeathBrownBoxWindowRelevant N0 X 60 box →
      heathBrownEligibleBoxCost L X 60 *
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (routeTAdaptiveCellAmplitude L X 60 N0 V - 1) ≤ V := by
    intro box helig hwin
    exact routeTAdaptiveCellAmplitude_windowRelevant_reserve
      L X 60 (by norm_num) hX hD hV box hwin
  simpa only [a, B] using
    (hreceiver hX.le hL hXL hXscale hcut hmuLo hmuHi
      halpha hV hK B hB c hc hband haggregate hreserve)

end RHTower.Sieve
