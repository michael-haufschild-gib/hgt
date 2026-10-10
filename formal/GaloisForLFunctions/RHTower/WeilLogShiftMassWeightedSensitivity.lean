import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalMass
import GaloisForLFunctions.RHTower.WeilLogShiftMomentFiberSensitivity

/-! The exact absolute mass strengthens sensitivity and coordinate-reading cost. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalMixture_mass_pairing (r k : ℕ) (a b : ℝ)
    (y : Fin (r + 2) → ℝ) :
    |(∑ i, finiteWeilCanonicalMixture r k a i * y i) -
      (∑ i, finiteWeilCanonicalMixture r k b i * y i)| *
        finiteWeilAbsMass (finiteWeilCanonicalCluster r k) =
      (∑ i, |finiteWeilCanonicalMixture r k a i - finiteWeilCanonicalMixture r k b i|) *
        |∑ i, finiteWeilCanonicalCluster r k i * y i| := by
  have hs := finiteWeil_profile_scale_bounds _ (finiteWeilCanonicalCluster_spec r k).1
    (finiteWeilCanonicalCluster_sum_zero r k)
  have hmass : finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≠ 0 := by
    have := finiteWeil_zero_sum_unit_mass _ (finiteWeilCanonicalCluster_spec r k).1
      (finiteWeilCanonicalCluster_sum_zero r k)
    linarith
  have hp : (∑ i, finiteWeilCanonicalPositiveProfile r k i * y i) -
      (∑ i, finiteWeilCanonicalNegativeProfile r k i * y i) =
        (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
          ∑ i, finiteWeilCanonicalCluster r k i * y i :=
    finiteWeil_profile_pairing _ y
  rw [finiteWeilCanonicalMixture_pairing, hp, abs_mul, abs_mul, abs_of_pos hs.1,
    finiteWeilCanonicalMixture_abs_distance]
  calc
    _ = ((2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
          finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
          (|a - b| * |∑ i, finiteWeilCanonicalCluster r k i * y i|) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hmass]; ring

/-- Exact sensitivity identity on the entire probability moment fiber. -/
theorem finiteWeilMomentFiber_mass_pairing (r k : ℕ) (v z : Fin (r + 2) → ℝ)
    (hv : finiteWeilCanonicalMomentFiber r k v) (hz : finiteWeilCanonicalMomentFiber r k z)
    (y : Fin (r + 2) → ℝ) :
    |(∑ i, v i * y i) - (∑ i, z i * y i)| *
        finiteWeilAbsMass (finiteWeilCanonicalCluster r k) =
      (∑ i, |v i - z i|) * |∑ i, finiteWeilCanonicalCluster r k i * y i| := by
  obtain ⟨a, ha, _⟩ := (finiteWeilCanonicalMomentFiber_iff r k v).mp hv
  obtain ⟨b, hb, _⟩ := (finiteWeilCanonicalMomentFiber_iff r k z).mp hz
  rw [ha.2.2, hb.2.2]
  exact finiteWeilCanonicalMixture_mass_pairing r k a b y

/-- Retain the absolute-mass factor instead of weakening it to its lower bound two. -/
theorem exists_finiteWeilGram_mass_weighted_fiber_sensitivity :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      ∀ v z : Fin (r + 2) → ℝ,
        finiteWeilCanonicalMomentFiber r k v → finiteWeilCanonicalMomentFiber r k z →
        ∀ w : FiniteWeilGramTest,
          |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
            (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
              (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) *
                finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≤
                  (∑ i, |v i - z i|) * B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_canonical_cluster_sensitivity
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth v z hv hz w => ?_⟩
  let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  let d : s → ℝ := Function.extend e (finiteWeilCanonicalCluster r k) (fun _ => 0)
  let y : Fin (r + 2) → ℝ := fun i => finiteWeilGramCoefficientVector s w (e i)
  let q : ℝ := ((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r
  let D : ℝ := ∑ i, |v i - z i|
  have hform : finiteWeilGramForm s w d = ∑ i, finiteWeilCanonicalCluster r k i * y i := by
    simpa only [finiteWeilGramCoefficientVector_pairing, mul_comm] using
      finiteWeil_extend_pairing e he (finiteWeilCanonicalCluster r k)
        (finiteWeilGramCoefficientVector s w)
  have hc := (hbound r s k hmem hwidth).2.2 w
  rw [hform] at hc
  have hid := finiteWeilMomentFiber_mass_pairing r k v z hv hz y
  change |(∑ i, v i * y i) - (∑ i, z i * y i)| * q *
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≤ D * B * finiteWeilGramTailCost 1 w
  calc
    _ = (|(∑ i, v i * y i) - (∑ i, z i * y i)| *
        finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) * q := by ring
    _ = D * (|∑ i, finiteWeilCanonicalCluster r k i * y i| * q) := by
      rw [hid]
      dsimp [D]
      ring
    _ ≤ D * (B * finiteWeilGramTailCost 1 w) :=
      mul_le_mul_of_nonneg_left hc (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    _ = _ := by ring

/-- An actual coordinate reader exists, and every reader pays the retained-mass cost. -/
theorem exists_finiteWeilGram_mass_weighted_coordinate_cost :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ w : FiniteWeilGramTest,
        (∀ a : ℝ, (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) →
        finiteWeilAbsMass (finiteWeilCanonicalCluster r k) *
          (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤ 2 * B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_mass_weighted_fiber_sensitivity
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth =>
    ⟨exists_finiteWeilGram_reads_mixture_coordinate r s k hmem, fun w hw => ?_⟩⟩
  have hc := hbound r s k hmem hwidth
    (finiteWeilCanonicalMixture r k 1) (finiteWeilCanonicalMixture r k 0)
    (finiteWeilCanonicalMixture_mem r k 1 (by norm_num) le_rfl)
    (finiteWeilCanonicalMixture_mem r k 0 le_rfl (by norm_num)) w
  rw [hw 1, hw 0, finiteWeilCanonicalMixture_abs_distance] at hc
  calc
    _ = (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) *
        finiteWeilAbsMass (finiteWeilCanonicalCluster r k) := mul_comm _ _
    _ ≤ _ := by simpa only [sub_zero, abs_one, mul_one, one_mul] using hc

end RHTower
