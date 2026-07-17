import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization

open Filter Topology
open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Finite source-marked Gibbs Gram energy.  Positive source energies are amplified as the
integer inverse temperature grows. -/
def finiteSourceGibbsGramEnergy
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (k : ℕ) (q : J → ℂ) : ℝ :=
  ∑ p, base p * Real.exp ((k : ℝ) * energy p) *
    ‖∑ j, q j * c j p‖ ^ 2

/-- Tropical normalization of a finite Gibbs Gram form at a proposed support radius. -/
def finiteSourceGibbsGramEnergyNormalized
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (k : ℕ) (q : J → ℂ) : ℝ :=
  ∑ p, base p * Real.exp ((k : ℝ) * (energy p - radius)) *
    ‖∑ j, q j * c j p‖ ^ 2

/-- Gram energy carried by one exposed energy level. -/
def finiteSourceEnergyLevelGramEnergy
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (level : ℝ)
    (q : J → ℂ) : ℝ :=
  ∑ p, if energy p = level then
    base p * ‖∑ j, q j * c j p‖ ^ 2 else 0

/-- Gram energy on a cumulative upper energy face. -/
def finiteSourceSuperlevelGramEnergy
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (level : ℝ)
    (q : J → ℂ) : ℝ :=
  ∑ p, if level ≤ energy p then
    base p * ‖∑ j, q j * c j p‖ ^ 2 else 0

/-- The tropical normalization is exactly multiplication by the inverse leading exponential. -/
theorem finiteSourceGibbsGramEnergyNormalized_eq
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (k : ℕ) (q : J → ℂ) :
    finiteSourceGibbsGramEnergyNormalized c base energy radius k q =
      Real.exp (-(k : ℝ) * radius) *
        finiteSourceGibbsGramEnergy c base energy k q := by
  rw [finiteSourceGibbsGramEnergyNormalized, finiteSourceGibbsGramEnergy,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show (k : ℝ) * (energy p - radius) =
      (-(k : ℝ) * radius) + (k : ℝ) * energy p by ring,
    Real.exp_add]
  ring

private theorem tendsto_exp_nat_mul_sub_of_le
    {x radius : ℝ} (hupper : x ≤ radius) :
    Tendsto (fun k : ℕ => Real.exp ((k : ℝ) * (x - radius))) atTop
      (nhds (if x = radius then 1 else 0)) := by
  by_cases h : x = radius
  · simp [h]
  · have hneg : x - radius < 0 := sub_neg.mpr (lt_of_le_of_ne hupper h)
    have hlin : Tendsto (fun k : ℕ => (k : ℝ) * (x - radius)) atTop atBot :=
      tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg hneg
    simpa only [Function.comp_apply, if_neg h] using
      (Real.tendsto_exp_atBot.comp hlin)

/-- **Exposed-face zero-temperature limit.**  Tropical normalization of a finite positive Gibbs
Gram ray converges to the Gram form supported exactly on the maximum-energy face. -/
theorem tendsto_finiteSourceGibbsGramEnergyNormalized_exposedFace
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius : ℝ)
    (hupper : ∀ p, energy p ≤ radius) (q : J → ℂ) :
    Tendsto
      (fun k : ℕ => finiteSourceGibbsGramEnergyNormalized
        c base energy radius k q)
      atTop (nhds (finiteSourceEnergyLevelGramEnergy c base energy radius q)) := by
  simp only [finiteSourceGibbsGramEnergyNormalized, finiteSourceEnergyLevelGramEnergy]
  apply tendsto_finset_sum
  intro p hp
  have hfactor := tendsto_exp_nat_mul_sub_of_le (hupper p)
  by_cases hlevel : energy p = radius
  · simp only [hlevel, if_pos]
    simpa using hfactor.const_mul
      (base p * ‖∑ j, q j * c j p‖ ^ 2)
  · simp only [hlevel, if_neg]
    convert hfactor.const_mul
      (base p * ‖∑ j, q j * c j p‖ ^ 2) using 1
    · funext k
      ring
    · simp [hlevel]

/-- The exposed-level Gram radical consists exactly of coefficient combinations vanishing on the
exposed face. -/
theorem finiteSourceEnergyLevelGramEnergy_eq_zero_iff
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (level : ℝ)
    (hbase : ∀ p, 0 < base p) (q : J → ℂ) :
    finiteSourceEnergyLevelGramEnergy c base energy level q = 0 ↔
      ∀ p, energy p = level → ∑ j, q j * c j p = 0 := by
  classical
  rw [finiteSourceEnergyLevelGramEnergy]
  constructor
  · intro hzero p hp
    have hterms : ∀ r ∈ (Finset.univ : Finset P),
        0 ≤ if energy r = level then
          base r * ‖∑ j, q j * c j r‖ ^ 2 else 0 := by
      intro r hr
      split_ifs
      · exact mul_nonneg (hbase r).le (sq_nonneg _)
      · exact le_rfl
    have hpzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hzero p
      (Finset.mem_univ p)
    simp only [hp, if_pos] at hpzero
    have hnorm : ‖∑ j, q j * c j p‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hpzero).resolve_left (hbase p).ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · intro h
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hlevel : energy p = level
    · simp [hlevel, h p hlevel]
    · simp [hlevel]

/-- The cumulative superlevel radical consists exactly of combinations vanishing on the selected
upper energy set. -/
theorem finiteSourceSuperlevelGramEnergy_eq_zero_iff
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (level : ℝ)
    (hbase : ∀ p, 0 < base p) (q : J → ℂ) :
    finiteSourceSuperlevelGramEnergy c base energy level q = 0 ↔
      ∀ p, level ≤ energy p → ∑ j, q j * c j p = 0 := by
  classical
  rw [finiteSourceSuperlevelGramEnergy]
  constructor
  · intro hzero p hp
    have hterms : ∀ r ∈ (Finset.univ : Finset P),
        0 ≤ if level ≤ energy r then
          base r * ‖∑ j, q j * c j r‖ ^ 2 else 0 := by
      intro r hr
      split_ifs
      · exact mul_nonneg (hbase r).le (sq_nonneg _)
      · exact le_rfl
    have hpzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hzero p
      (Finset.mem_univ p)
    simp only [hp, if_pos] at hpzero
    have hnorm : ‖∑ j, q j * c j p‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hpzero).resolve_left (hbase p).ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · intro h
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hlevel : level ≤ energy p
    · simp [hlevel, h p hlevel]
    · simp [hlevel]

/-- **Canonical radical flag.**  Raising the energy threshold removes coordinates and can only
enlarge the Gram radical. -/
theorem finiteSourceSuperlevelGramEnergy_radical_mono
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ)
    (hbase : ∀ p, 0 < base p) {lower upper : ℝ} (hlevels : lower ≤ upper)
    (q : J → ℂ)
    (hzero : finiteSourceSuperlevelGramEnergy c base energy lower q = 0) :
    finiteSourceSuperlevelGramEnergy c base energy upper q = 0 := by
  rw [finiteSourceSuperlevelGramEnergy_eq_zero_iff
    c base energy lower hbase q] at hzero
  rw [finiteSourceSuperlevelGramEnergy_eq_zero_iff
    c base energy upper hbase q]
  intro p hp
  exact hzero p (hlevels.trans hp)

/-- Energy-origin shifts leave the tropically normalized Gram ray exactly unchanged. -/
theorem finiteSourceGibbsGramEnergyNormalized_add_const
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (radius shift : ℝ)
    (k : ℕ) (q : J → ℂ) :
    finiteSourceGibbsGramEnergyNormalized c base
        (fun p => energy p + shift) (radius + shift) k q =
      finiteSourceGibbsGramEnergyNormalized c base energy radius k q := by
  rw [finiteSourceGibbsGramEnergyNormalized, finiteSourceGibbsGramEnergyNormalized]
  apply Finset.sum_congr rfl
  intro p hp
  congr 3
  ring

/-- Energy-origin shifts leave the exposed boundary Gram form exactly unchanged. -/
theorem finiteSourceEnergyLevelGramEnergy_add_const
    {J P : Type*} [Fintype J] [Fintype P]
    (c : J → P → ℂ) (base energy : P → ℝ) (level shift : ℝ)
    (q : J → ℂ) :
    finiteSourceEnergyLevelGramEnergy c base (fun p => energy p + shift)
        (level + shift) q =
      finiteSourceEnergyLevelGramEnergy c base energy level q := by
  classical
  rw [finiteSourceEnergyLevelGramEnergy, finiteSourceEnergyLevelGramEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  have hiff : energy p + shift = level + shift ↔ energy p = level := by
    constructor
    · exact add_right_cancel
    · intro h
      rw [h]
  simp only [hiff]

/-- The maximum-energy face of an additive product marking is exactly the product of the two
maximum-energy faces. -/
theorem finiteTensorEnergy_eq_add_radius_iff
    {P Q : Type*} (energyP : P → ℝ) (energyQ : Q → ℝ)
    (radiusP radiusQ : ℝ)
    (hupperP : ∀ p, energyP p ≤ radiusP)
    (hupperQ : ∀ q, energyQ q ≤ radiusQ)
    (p : P) (q : Q) :
    finiteTensorEnergy energyP energyQ (p, q) = radiusP + radiusQ ↔
      energyP p = radiusP ∧ energyQ q = radiusQ := by
  simp only [finiteTensorEnergy]
  constructor
  · intro h
    constructor <;> linarith [hupperP p, hupperQ q]
  · rintro ⟨hp, hq⟩
    rw [hp, hq]

/-! ## Purity reads the size of the exposed face -/

/-- Cardinality of the exposed maximum-energy face. -/
def finiteSourceExposedFaceCard
    {P : Type*} [Fintype P] (energy : P → ℝ) (radius : ℝ) : ℕ :=
  (Finset.univ.filter fun p => energy p = radius).card

/-- Tropically normalized finite source partition. -/
def finiteSourceGibbsPartitionNormalized
    {P : Type*} [Fintype P] (energy : P → ℝ) (radius : ℝ) (k : ℕ) : ℝ :=
  ∑ p, Real.exp ((k : ℝ) * (energy p - radius))

/-- The normalized source partition is the canonical Gibbs partition for the negative source
energy after removal of its leading exponential. -/
theorem finiteSourceGibbsPartitionNormalized_eq
    {P : Type*} [Fintype P]
    (energy : P → ℝ) (radius : ℝ) (k : ℕ) :
    finiteSourceGibbsPartitionNormalized energy radius k =
      Real.exp (-(k : ℝ) * radius) *
        finiteGibbsPartition (k : ℝ) (fun p => -energy p) := by
  rw [finiteSourceGibbsPartitionNormalized, finiteGibbsPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Real.exp_add]
  congr 1
  ring

/-- Every nonempty finite normalized source partition is positive. -/
theorem finiteSourceGibbsPartitionNormalized_pos
    {P : Type*} [Fintype P] [Nonempty P]
    (energy : P → ℝ) (radius : ℝ) (k : ℕ) :
    0 < finiteSourceGibbsPartitionNormalized energy radius k := by
  rw [finiteSourceGibbsPartitionNormalized]
  apply Finset.sum_pos
  · intro p hp
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- The normalized partition converges to the number of points on the exposed face. -/
theorem tendsto_finiteSourceGibbsPartitionNormalized_exposedFaceCard
    {P : Type*} [Fintype P]
    (energy : P → ℝ) (radius : ℝ) (hupper : ∀ p, energy p ≤ radius) :
    Tendsto (finiteSourceGibbsPartitionNormalized energy radius)
      atTop (nhds (finiteSourceExposedFaceCard energy radius : ℝ)) := by
  change Tendsto
    (fun k : ℕ => ∑ p, Real.exp ((k : ℝ) * (energy p - radius)))
    atTop (nhds (finiteSourceExposedFaceCard energy radius : ℝ))
  have hsum := tendsto_finset_sum (Finset.univ : Finset P) (fun p hp =>
    tendsto_exp_nat_mul_sub_of_le (hupper p))
  convert hsum using 1
  simp [finiteSourceExposedFaceCard]

/-- Exact cancellation of the leading source energy in the order-two replica ratio. -/
theorem finiteGibbsPurity_neg_energy_eq_normalizedPartitionRatio
    {P : Type*} [Fintype P] [Nonempty P]
    (energy : P → ℝ) (radius : ℝ) (k : ℕ) :
    finiteGibbsPurity (k : ℝ) (fun p => -energy p) =
      finiteSourceGibbsPartitionNormalized energy radius (2 * k) /
        finiteSourceGibbsPartitionNormalized energy radius k ^ 2 := by
  rw [finiteGibbsPurity_eq_partitionRatio]
  have hk := finiteSourceGibbsPartitionNormalized_eq energy radius k
  have h2k := finiteSourceGibbsPartitionNormalized_eq energy radius (2 * k)
  have hZkpos : 0 < finiteGibbsPartition (k : ℝ) (fun p => -energy p) :=
    finiteGibbsPartition_pos _ _
  have hZ2kpos : 0 < finiteGibbsPartition (2 * (k : ℝ)) (fun p => -energy p) :=
    finiteGibbsPartition_pos _ _
  have hAkpos := finiteSourceGibbsPartitionNormalized_pos energy radius k
  have hA2kpos := finiteSourceGibbsPartitionNormalized_pos energy radius (2 * k)
  rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by norm_num] at hZ2kpos ⊢
  rw [show ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) by norm_num] at h2k
  have hexp : Real.exp (-(2 * (k : ℝ)) * radius) =
      Real.exp (-(k : ℝ) * radius) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hk, h2k, hexp]
  field_simp [ne_of_gt hZkpos, ne_of_gt hZ2kpos, Real.exp_ne_zero]
  <;> norm_num [Nat.cast_mul]
  <;> ring

/-- **Purity--face law.**  The zero-temperature Rényi-2 purity is the reciprocal cardinality of
the exposed maximum-energy face.  Hence purity measures degeneracy while the limiting Gram radical
measures the face's coefficient-relation geometry. -/
theorem tendsto_finiteGibbsPurity_neg_energy_exposedFaceCard
    {P : Type*} [Fintype P] [Nonempty P]
    (energy : P → ℝ) (radius : ℝ)
    (hupper : ∀ p, energy p ≤ radius)
    (hexposed : ∃ p, energy p = radius) :
    Tendsto
      (fun k : ℕ => finiteGibbsPurity (k : ℝ) (fun p => -energy p))
      atTop (nhds ((finiteSourceExposedFaceCard energy radius : ℝ)⁻¹)) := by
  have hA := tendsto_finiteSourceGibbsPartitionNormalized_exposedFaceCard
    energy radius hupper
  have htwo : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    omega
  have hA2 := hA.comp htwo
  have hcardPosNat : 0 < finiteSourceExposedFaceCard energy radius := by
    obtain ⟨p, hp⟩ := hexposed
    unfold finiteSourceExposedFaceCard
    refine Finset.card_pos.mpr ⟨p, ?_⟩
    simp [hp]
  have hcardNe : (finiteSourceExposedFaceCard energy radius : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPosNat)
  have hratio := hA2.div (hA.pow 2) (pow_ne_zero 2 hcardNe)
  convert hratio using 1
  · funext k
    exact finiteGibbsPurity_neg_energy_eq_normalizedPartitionRatio
      energy radius k
  · field_simp

/-- **Thermofield coherence--face law.**  At zero temperature, the total off-diagonal squared
mass of the canonical thermofield projector converges to one minus the reciprocal cardinality
of the exposed maximum-energy face.  Thus the same face degeneracy that fixes the limiting
Renyi-two purity fixes the surviving thermofield transition mass. -/
theorem tendsto_offDiagonal_sq_finiteKMSWightmanWeight_neg_energy_exposedFaceCard
    {P : Type*} [Fintype P] [Nonempty P] [DecidableEq P]
    (energy : P → ℝ) (radius : ℝ)
    (hupper : ∀ p, energy p ≤ radius)
    (hexposed : ∃ p, energy p = radius) :
    Tendsto
      (fun k : ℕ =>
        ∑ a, ∑ b ∈ Finset.univ.erase a,
          finiteKMSWightmanWeight (k : ℝ) (fun p => -energy p) a b ^ 2)
      atTop
      (nhds (1 - (finiteSourceExposedFaceCard energy radius : ℝ)⁻¹)) := by
  classical
  have hpurity := tendsto_finiteGibbsPurity_neg_energy_exposedFaceCard
    energy radius hupper hexposed
  have hoff : Tendsto
      (fun k : ℕ => 1 - finiteGibbsPurity (k : ℝ) (fun p => -energy p))
      atTop
      (nhds (1 - (finiteSourceExposedFaceCard energy radius : ℝ)⁻¹)) :=
    tendsto_const_nhds.sub hpurity
  convert hoff using 1
  funext k
  exact sum_offDiagonal_sq_finiteKMSWightmanWeight_eq_one_sub_purity
    (k : ℝ) (fun p => -energy p)

/-- Energy-origin gauge invariance of the exposed-face cardinal. -/
theorem finiteSourceExposedFaceCard_add_const
    {P : Type*} [Fintype P]
    (energy : P → ℝ) (radius shift : ℝ) :
    finiteSourceExposedFaceCard (fun p => energy p + shift) (radius + shift) =
      finiteSourceExposedFaceCard energy radius := by
  classical
  unfold finiteSourceExposedFaceCard
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact add_right_cancel
  · intro h
    rw [h]

/-- Exposed-face cardinality is multiplicative for additive product source markings. -/
theorem finiteSourceExposedFaceCard_tensor
    {P Q : Type*} [Fintype P] [Fintype Q]
    (energyP : P → ℝ) (energyQ : Q → ℝ) (radiusP radiusQ : ℝ)
    (hupperP : ∀ p, energyP p ≤ radiusP)
    (hupperQ : ∀ q, energyQ q ≤ radiusQ) :
    finiteSourceExposedFaceCard (finiteTensorEnergy energyP energyQ)
        (radiusP + radiusQ) =
      finiteSourceExposedFaceCard energyP radiusP *
        finiteSourceExposedFaceCard energyQ radiusQ := by
  classical
  rw [finiteSourceExposedFaceCard, finiteSourceExposedFaceCard,
    finiteSourceExposedFaceCard]
  let faceP : Finset P := Finset.univ.filter fun p => energyP p = radiusP
  let faceQ : Finset Q := Finset.univ.filter fun q => energyQ q = radiusQ
  have hface :
      (Finset.univ.filter fun x : P × Q =>
        finiteTensorEnergy energyP energyQ x = radiusP + radiusQ) =
        faceP ×ˢ faceQ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      faceP, faceQ]
    exact finiteTensorEnergy_eq_add_radius_iff
      energyP energyQ radiusP radiusQ hupperP hupperQ x.1 x.2
  rw [hface, Finset.card_product]

/-- Tropically normalized source partitions factor under additive products. -/
theorem finiteSourceGibbsPartitionNormalized_tensor
    {P Q : Type*} [Fintype P] [Fintype Q]
    (energyP : P → ℝ) (energyQ : Q → ℝ) (radiusP radiusQ : ℝ) (k : ℕ) :
    finiteSourceGibbsPartitionNormalized (finiteTensorEnergy energyP energyQ)
        (radiusP + radiusQ) k =
      finiteSourceGibbsPartitionNormalized energyP radiusP k *
        finiteSourceGibbsPartitionNormalized energyQ radiusQ k := by
  rw [finiteSourceGibbsPartitionNormalized, Fintype.sum_prod_type,
    finiteSourceGibbsPartitionNormalized, finiteSourceGibbsPartitionNormalized]
  calc
    (∑ p, ∑ q,
        Real.exp ((k : ℝ) *
          (finiteTensorEnergy energyP energyQ (p, q) - (radiusP + radiusQ)))) =
        ∑ p, ∑ q,
          Real.exp ((k : ℝ) * (energyP p - radiusP)) *
            Real.exp ((k : ℝ) * (energyQ q - radiusQ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Real.exp_add]
      congr 1
      simp only [finiteTensorEnergy]
      ring
    _ = (∑ p, Real.exp ((k : ℝ) * (energyP p - radiusP))) *
        ∑ q, Real.exp ((k : ℝ) * (energyQ q - radiusQ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

/-- Tensor product of two coefficient packets. -/
def finiteTensorCoefficient
    {JP JQ P Q : Type*}
    (cP : JP → P → ℂ) (cQ : JQ → Q → ℂ) :
    JP × JQ → P × Q → ℂ :=
  fun ij pq => cP ij.1 pq.1 * cQ ij.2 pq.2

/-- Decomposable coefficient vector on a tensor packet. -/
def finiteTensorCoefficientVector
    {JP JQ : Type*} (u : JP → ℂ) (v : JQ → ℂ) : JP × JQ → ℂ :=
  fun ij => u ij.1 * v ij.2

/-- Evaluation of a decomposable tensor coefficient vector factors pointwise. -/
theorem sum_finiteTensorCoefficientVector_mul_finiteTensorCoefficient
    {JP JQ P Q : Type*} [Fintype JP] [Fintype JQ]
    (cP : JP → P → ℂ) (cQ : JQ → Q → ℂ)
    (u : JP → ℂ) (v : JQ → ℂ) (p : P) (q : Q) :
    ∑ ij, finiteTensorCoefficientVector u v ij *
        finiteTensorCoefficient cP cQ ij (p, q) =
      (∑ i, u i * cP i p) * (∑ j, v j * cQ j q) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [finiteTensorCoefficientVector, finiteTensorCoefficient]
  ring

/-- **Monoidal normalized Gram law.**  The tropically normalized Gibbs Gram energy of a
decomposable tensor packet factors at every temperature. -/
theorem finiteSourceGibbsGramEnergyNormalized_tensor
    {JP JQ P Q : Type*}
    [Fintype JP] [Fintype JQ] [Fintype P] [Fintype Q]
    (cP : JP → P → ℂ) (cQ : JQ → Q → ℂ)
    (baseP energyP : P → ℝ) (baseQ energyQ : Q → ℝ)
    (radiusP radiusQ : ℝ) (k : ℕ) (u : JP → ℂ) (v : JQ → ℂ) :
    finiteSourceGibbsGramEnergyNormalized
        (finiteTensorCoefficient cP cQ)
        (fun pq => baseP pq.1 * baseQ pq.2)
        (finiteTensorEnergy energyP energyQ) (radiusP + radiusQ) k
        (finiteTensorCoefficientVector u v) =
      finiteSourceGibbsGramEnergyNormalized cP baseP energyP radiusP k u *
        finiteSourceGibbsGramEnergyNormalized cQ baseQ energyQ radiusQ k v := by
  rw [finiteSourceGibbsGramEnergyNormalized, Fintype.sum_prod_type,
    finiteSourceGibbsGramEnergyNormalized, finiteSourceGibbsGramEnergyNormalized]
  calc
    (∑ p, ∑ q,
      (baseP p * baseQ q) *
          Real.exp ((k : ℝ) *
            (finiteTensorEnergy energyP energyQ (p, q) - (radiusP + radiusQ))) *
        ‖∑ ij, finiteTensorCoefficientVector u v ij *
          finiteTensorCoefficient cP cQ ij (p, q)‖ ^ 2) =
      ∑ p, ∑ q,
        (baseP p * Real.exp ((k : ℝ) * (energyP p - radiusP)) *
          ‖∑ i, u i * cP i p‖ ^ 2) *
        (baseQ q * Real.exp ((k : ℝ) * (energyQ q - radiusQ)) *
          ‖∑ j, v j * cQ j q‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_finiteTensorCoefficientVector_mul_finiteTensorCoefficient,
        norm_mul, mul_pow]
      have hexp :
          Real.exp ((k : ℝ) *
              (finiteTensorEnergy energyP energyQ (p, q) - (radiusP + radiusQ))) =
            Real.exp ((k : ℝ) * (energyP p - radiusP)) *
              Real.exp ((k : ℝ) * (energyQ q - radiusQ)) := by
        rw [← Real.exp_add]
        congr 1
        simp only [finiteTensorEnergy]
        ring
      rw [hexp]
      ring
    _ = (∑ p, baseP p * Real.exp ((k : ℝ) * (energyP p - radiusP)) *
          ‖∑ i, u i * cP i p‖ ^ 2) *
        ∑ q, baseQ q * Real.exp ((k : ℝ) * (energyQ q - radiusQ)) *
          ‖∑ j, v j * cQ j q‖ ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

/-- The exposed boundary Gram form of a decomposable tensor packet is the product of the two
exposed boundary Gram forms. -/
theorem finiteSourceEnergyLevelGramEnergy_tensor
    {JP JQ P Q : Type*}
    [Fintype JP] [Fintype JQ] [Fintype P] [Fintype Q]
    (cP : JP → P → ℂ) (cQ : JQ → Q → ℂ)
    (baseP energyP : P → ℝ) (baseQ energyQ : Q → ℝ)
    (radiusP radiusQ : ℝ)
    (hupperP : ∀ p, energyP p ≤ radiusP)
    (hupperQ : ∀ q, energyQ q ≤ radiusQ)
    (u : JP → ℂ) (v : JQ → ℂ) :
    finiteSourceEnergyLevelGramEnergy
        (finiteTensorCoefficient cP cQ)
        (fun pq => baseP pq.1 * baseQ pq.2)
        (finiteTensorEnergy energyP energyQ) (radiusP + radiusQ)
        (finiteTensorCoefficientVector u v) =
      finiteSourceEnergyLevelGramEnergy cP baseP energyP radiusP u *
        finiteSourceEnergyLevelGramEnergy cQ baseQ energyQ radiusQ v := by
  rw [finiteSourceEnergyLevelGramEnergy, Fintype.sum_prod_type,
    finiteSourceEnergyLevelGramEnergy, finiteSourceEnergyLevelGramEnergy]
  calc
    (∑ p, ∑ q, if finiteTensorEnergy energyP energyQ (p, q) = radiusP + radiusQ
      then (baseP p * baseQ q) *
        ‖∑ ij, finiteTensorCoefficientVector u v ij *
          finiteTensorCoefficient cP cQ ij (p, q)‖ ^ 2 else 0) =
      ∑ p, ∑ q,
        (if energyP p = radiusP then
          baseP p * ‖∑ i, u i * cP i p‖ ^ 2 else 0) *
        (if energyQ q = radiusQ then
          baseQ q * ‖∑ j, v j * cQ j q‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp only [finiteTensorEnergy_eq_add_radius_iff
        energyP energyQ radiusP radiusQ hupperP hupperQ,
        sum_finiteTensorCoefficientVector_mul_finiteTensorCoefficient, norm_mul, mul_pow]
      by_cases hpface : energyP p = radiusP <;>
        by_cases hqface : energyQ q = radiusQ <;> simp [hpface, hqface] <;> ring
    _ = (∑ p, if energyP p = radiusP then
          baseP p * ‖∑ i, u i * cP i p‖ ^ 2 else 0) *
        ∑ q, if energyQ q = radiusQ then
          baseQ q * ‖∑ j, v j * cQ j q‖ ^ 2 else 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

end

end HTGeometry
