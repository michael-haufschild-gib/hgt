import GaloisForLFunctions.HTGeometry.Lattices.LatticeBallCounting

/-!
# The covered-volume density of a lattice ball packing

For disjoint open unit balls centered at a full lattice, the fraction of a
large observation ball covered by the union tends to unit-ball volume divided
by covolume. Centers inside radius `R - 1` give a lower bound; centers inside
`R + 1` give an upper bound. Lattice-point asymptotics and the negligible
fixed-width boundary strip identify both limits.
-/

open MeasureTheory Metric Set Bornology Module Filter
open scoped Pointwise Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry.LatticePackingDensity
open LatticeBallCounting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The region covered by open unit balls centered at the lattice. -/
def region : Set E := ⋃ v : L, ball (v : E) 1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [DiscreteTopology L] [IsZLattice ℝ L] in
theorem measurableSet_region : MeasurableSet (region L) :=
  (isOpen_iUnion fun _ => isOpen_ball).measurableSet

/-- Finitely many lattice centers in a bounded observation ball. -/
def centers (r : ℝ) : Finset E := (ArtinMertens.finite_inter_lattice L
  (Y := ball (0 : E) r) isBounded_ball).toFinset

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem mem_centers (r : ℝ) (v : E) : v ∈ centers L r ↔ ‖v‖ < r ∧ v ∈ L := by
  simp [centers, mem_ball, dist_zero_right]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem card_centers (r : ℝ) : (centers L r).card = ballCount L r :=
  (Set.ncard_eq_toFinset_card _ _).symm

/-- Unit balls whose centers lie inside radius `r`. -/
def finiteRegion (r : ℝ) : Set E := ⋃ v ∈ centers L r, ball v 1

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem finiteRegion_subset_ball (r : ℝ) : finiteRegion L r ⊆ ball (0 : E) (r + 1) := by
  rintro x hx
  obtain ⟨v, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hv, hx⟩ := Set.mem_iUnion.mp hx
  have hcenter := (mem_centers L r v).mp hv
  have ht := dist_triangle x v (0 : E)
  simp only [mem_ball, dist_zero_right] at hx ht ⊢
  linarith only [hx, hcenter.1, ht]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem finiteRegion_subset_region (r : ℝ) : finiteRegion L r ⊆ region L := by
  rintro x hx
  obtain ⟨v, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hv, hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨v, ((mem_centers L r v).mp hv).2⟩, hx⟩

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem region_inter_ball_subset (r : ℝ) :
    region L ∩ ball (0 : E) r ⊆ finiteRegion L (r + 1) := by
  rintro x ⟨hx, hball⟩
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
  have ht := dist_triangle (v : E) x (0 : E)
  simp only [mem_ball, dist_zero_right] at hball hv
  rw [dist_comm (v : E) x, dist_zero_right, dist_zero_right] at ht
  have hc : (v : E) ∈ centers L (r + 1) :=
    (mem_centers L (r + 1) v).mpr ⟨by linarith only [ht, hv, hball], v.property⟩
  exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hc, hv⟩⟩

variable (hpack : Pairwise (fun v w : L => Disjoint (ball (v : E) 1) (ball (w : E) 1)))

omit [IsZLattice ℝ L] in
include hpack in
/-- Disjointness turns the finite union volume into a lattice-point count. -/
theorem finiteRegion_volume (r : ℝ) :
    volume.real (finiteRegion L r) = (ballCount L r : ℝ) * volume.real (ball (0 : E) 1) := by
  have hdisj : (centers L r : Set E).PairwiseDisjoint (fun v => ball v 1) := by
    intro v hv w hw hvw
    exact hpack (show (⟨v, ((mem_centers L r v).mp hv).2⟩ : L) ≠
      ⟨w, ((mem_centers L r w).mp hw).2⟩ from fun h => hvw (congrArg Subtype.val h))
  rw [finiteRegion, measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball)
    (fun _ _ => isBounded_ball.measure_lt_top.ne)]
  have hvol (v : E) : volume.real (ball v 1) = volume.real (ball (0 : E) 1) := by
    simp only [measureReal_def, volume.addHaar_ball_of_pos v (r := 1) zero_lt_one,
      one_pow, ENNReal.ofReal_one, one_mul]
  simp only [hvol, Finset.sum_const, nsmul_eq_mul, card_centers]

omit [IsZLattice ℝ L] in
include hpack in
/-- Inner and outer center counts bound the volume covered in a ball. -/
theorem covered_volume_bounds (n : ℕ) :
    (ballCount L n : ℝ) * volume.real (ball (0 : E) 1) ≤
      volume.real (region L ∩ ball (0 : E) (n + 1)) ∧
    volume.real (region L ∩ ball (0 : E) (n + 1)) ≤
      (ballCount L (n + 2) : ℝ) * volume.real (ball (0 : E) 1) := by
  constructor
  · rw [← finiteRegion_volume L hpack]
    exact measureReal_mono (fun x hx =>
      ⟨finiteRegion_subset_region L n hx, finiteRegion_subset_ball L n hx⟩)
      ((isBounded_ball.subset Set.inter_subset_right).measure_lt_top.ne)
  · rw [← finiteRegion_volume L hpack]
    have hs : region L ∩ ball (0 : E) (n + 1) ⊆ finiteRegion L (n + 2) := by
      simpa only [add_assoc, one_add_one_eq_two] using region_inter_ball_subset L (n + 1)
    exact measureReal_mono hs
      ((isBounded_ball.subset (finiteRegion_subset_ball L (n + 2))).measure_lt_top.ne)

/-- Fraction of an observation ball occupied by the packing. -/
def densityAt (r : ℝ) : ℝ :=
  volume.real (region L ∩ ball (0 : E) r) / volume.real (ball (0 : E) r)

theorem unitBall_volume_pos : 0 < volume.real (ball (0 : E) 1) := by
  exact ENNReal.toReal_pos (measure_ball_pos volume 0 zero_lt_one).ne'
    isBounded_ball.measure_lt_top.ne

theorem ball_volume {r : ℝ} (hr : 0 < r) :
    volume.real (ball (0 : E) r) = r^finrank ℝ E * volume.real (ball (0 : E) 1) := by
  rw [measureReal_def, volume.addHaar_ball_of_pos 0 hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rfl

include hpack in
theorem tendsto_normalized_covered_volume :
    Tendsto (fun n : ℕ => volume.real (region L ∩ ball (0 : E) (n + 1)) /
      (n + 1 : ℝ)^finrank ℝ E) atTop
      (𝓝 ((volume.real (ball (0 : E) 1) / ZLattice.covolume L) *
        volume.real (ball (0 : E) 1))) := by
  have hlo := (tendsto_ballCount_shift L 0 1).mul_const (volume.real (ball (0 : E) 1))
  have hhi := (tendsto_ballCount_shift L 2 1).mul_const (volume.real (ball (0 : E) 1))
  simp only [Nat.cast_zero, Nat.cast_one, add_zero, div_mul_eq_mul_div] at hlo
  simp only [Nat.cast_one, Nat.cast_ofNat, div_mul_eq_mul_div] at hhi
  simp only [div_mul_eq_mul_div]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (covered_volume_bounds L hpack n).1 (by positivity)
  · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (covered_volume_bounds L hpack n).2 (by positivity)

include hpack in
/-- The occupied fraction along integer observation radii. -/
theorem tendsto_density :
    Tendsto (fun n : ℕ => densityAt L n) atTop
      (𝓝 (volume.real (ball (0 : E) 1) / ZLattice.covolume L)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have h := (tendsto_normalized_covered_volume L hpack).div_const
    (volume.real (ball (0 : E) 1))
  rw [mul_div_cancel_right₀ _ (unitBall_volume_pos (E := E)).ne'] at h
  convert h using 1
  funext n
  rw [densityAt, Nat.cast_add, Nat.cast_one, ball_volume (by positivity), div_div]

include hpack in
/-- The occupied fraction converges along all real observation radii. -/
theorem tendsto_density_real :
    Tendsto (densityAt L) atTop
      (𝓝 (volume.real (ball (0 : E) 1) / ZLattice.covolume L)) := by
  have hnat : Tendsto (fun n : ℕ => volume.real (region L ∩ ball (0 : E) n) /
      (n : ℝ)^finrank ℝ E) atTop
      (𝓝 ((volume.real (ball (0 : E) 1) / ZLattice.covolume L) *
        volume.real (ball (0 : E) 1))) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_normalized_covered_volume L hpack
  have hm : Monotone (fun r : ℝ => volume.real (region L ∩ ball (0 : E) r)) := by
    intro r s hrs
    exact measureReal_mono (fun x hx => ⟨hx.1, ball_subset_ball hrs hx.2⟩)
      ((isBounded_ball.subset Set.inter_subset_right).measure_lt_top.ne)
  have h := (tendsto_real_div_pow_of_nat hm (fun _ => ENNReal.toReal_nonneg) hnat).div_const
    (volume.real (ball (0 : E) 1))
  rw [mul_div_cancel_right₀ _ (unitBall_volume_pos (E := E)).ne'] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [densityAt, ball_volume hr, div_div]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem densityAt_le_one (r : ℝ) : densityAt L r ≤ 1 := by
  by_cases hr : 0 < r
  · have hv : 0 < volume.real (ball (0 : E) r) := by
      rw [ball_volume hr]
      exact mul_pos (pow_pos hr _) (unitBall_volume_pos (E := E))
    apply (div_le_one hv).mpr
    exact measureReal_mono Set.inter_subset_right isBounded_ball.measure_lt_top.ne
  · simp only [densityAt, ball_eq_empty.mpr (le_of_not_gt hr), Set.inter_empty,
      measureReal_empty, div_zero, zero_le_one]

include hpack in
/-- A lattice packing cannot occupy more than the ambient volume. -/
theorem unitBall_div_covolume_le_one :
    volume.real (ball (0 : E) 1) / ZLattice.covolume L ≤ 1 :=
  le_of_tendsto (tendsto_density L hpack) (Eventually.of_forall fun n => densityAt_le_one L n)

#print axioms covered_volume_bounds
#print axioms tendsto_density
#print axioms tendsto_density_real
end GaloisForLFunctions.HTGeometry.LatticePackingDensity
