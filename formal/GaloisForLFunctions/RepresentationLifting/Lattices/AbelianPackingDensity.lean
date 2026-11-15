import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianRealLattice
import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianPackingMinimum
import GaloisForLFunctions.HTGeometry.Lattices.LatticePackingDensity
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Sharp sphere packing for finite abelian augmentation squares

The integral energy bound gives pairwise disjoint open unit balls in the
actual Euclidean lattice. The rectangle witness attains distance two, proving
that radius one is maximal whenever the label group has at least four elements.
The occupied-volume fraction converges along all real observation radii to
unit-ball volume divided by `sqrt(|G|^3)`, with an explicit Gamma-function formula.
-/

open MeasureTheory Metric Module Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry HTGeometry.LatticePackingDensity
variable (G : Type) [CommGroup G] [Fintype G]

theorem abelianAugmentationRealMap_dist_sq (v w : AbelianAugmentationLattice G) :
    dist (abelianAugmentationRealMap G v) (abelianAugmentationRealMap G w)^2 =
      (cyclicMovingEnergy G (v - w) : ℝ) :=
  abelianMovingRealMap_dist_sq G v w

theorem abelianAugmentationRealMap_separated (v w : AbelianAugmentationLattice G)
    (hvw : v ≠ w) : 2 ≤ dist (abelianAugmentationRealMap G v) (abelianAugmentationRealMap G w) := by
  have h := abelianAugmentation_energy_ge_four G (v-w) (sub_ne_zero.mpr hvw)
  have hr : (4 : ℝ) ≤ (cyclicMovingEnergy G (v-w) : ℝ) := by exact_mod_cast h
  rw [← abelianAugmentationRealMap_dist_sq] at hr
  nlinarith only [hr, dist_nonneg (x := abelianAugmentationRealMap G v)
    (y := abelianAugmentationRealMap G w)]

theorem abelianAugmentation_distance_two_exists (hn : 4 ≤ Fintype.card G) :
    ∃ v w : AbelianAugmentationLattice G, v ≠ w ∧
      dist (abelianAugmentationRealMap G v) (abelianAugmentationRealMap G w) = 2 := by
  obtain ⟨v, hv⟩ := abelianAugmentation_energy_four_exists G hn
  have hs := abelianAugmentationRealMap_dist_sq G v 0
  simp only [Submodule.coe_zero, sub_zero, hv, Int.cast_ofNat] at hs
  have hd : dist (abelianAugmentationRealMap G v) (abelianAugmentationRealMap G 0) = 2 := by
    nlinarith only [hs, dist_nonneg (x := abelianAugmentationRealMap G v)
      (y := abelianAugmentationRealMap G 0)]
  refine ⟨v, 0, ?_, hd⟩
  intro he
  rw [he, dist_self] at hd
  norm_num at hd

/-- Radius one is the exact maximum for disjoint balls with these lattice centers. -/
theorem abelianAugmentation_balls_disjoint_iff (hn : 4 ≤ Fintype.card G) (r : ℝ) :
    Pairwise (fun v w : AbelianAugmentationLattice G =>
      Disjoint (ball (abelianAugmentationRealMap G v) r)
        (ball (abelianAugmentationRealMap G w) r)) ↔ r ≤ 1 := by
  constructor
  · intro h
    by_contra hr
    have hr' : 0 < r := lt_trans (by norm_num) (lt_of_not_ge hr)
    obtain ⟨v, w, hvw, hd⟩ := abelianAugmentation_distance_two_exists G hn
    have hs := (disjoint_ball_ball_iff hr' hr').mp (h hvw)
    rw [hd] at hs
    linarith only [hs, hr]
  · intro hr v w hvw
    apply Metric.ball_disjoint_ball
    have hs := abelianAugmentationRealMap_separated G v w hvw
    linarith only [hr, hs]

theorem abelianAugmentationRealLattice_separated
    (v w : abelianAugmentationRealLattice G) (hvw : v ≠ w) :
    2 ≤ dist (v : AbelianRealHyperplane G) (w : AbelianRealHyperplane G) := by
  obtain ⟨a, ha, hav⟩ := v.property
  obtain ⟨b, hb, hbw⟩ := w.property
  have hab : (⟨a, ha⟩ : AbelianAugmentationLattice G) ≠ ⟨b, hb⟩ := by
    intro h
    apply hvw
    apply Subtype.ext
    rw [← hav, ← hbw]
    have he : a = b := congrArg (fun z : AbelianAugmentationLattice G => z.val) h
    exact congrArg (abelianMovingRealMap G) he
  have hs := abelianAugmentationRealMap_separated G ⟨a,ha⟩ ⟨b,hb⟩ hab
  change 2 ≤ dist (abelianMovingRealMap G a) (abelianMovingRealMap G b) at hs
  rw [hav, hbw] at hs
  exact hs

/-- An integral augmentation-square vector regarded as a point of its real lattice. -/
def abelianAugmentationRealCenter (v : AbelianAugmentationLattice G) :
    abelianAugmentationRealLattice G :=
  ⟨abelianAugmentationRealMap G v, ⟨v.val, v.property, rfl⟩⟩

theorem abelianAugmentationRealCenter_injective :
    Function.Injective (abelianAugmentationRealCenter G) := by
  intro v w h
  have he : abelianAugmentationRealMap G v = abelianAugmentationRealMap G w :=
    congrArg (fun z : abelianAugmentationRealLattice G => (z : AbelianRealHyperplane G)) h
  exact abelianAugmentationRealMap_injective G he

/-- Radius one is the exact maximum for the actual embedded lattice. -/
theorem abelianAugmentationRealLattice_balls_disjoint_iff
    (hn : 4 ≤ Fintype.card G) (r : ℝ) :
    Pairwise (fun v w : abelianAugmentationRealLattice G =>
      Disjoint (ball (v : AbelianRealHyperplane G) r)
        (ball (w : AbelianRealHyperplane G) r)) ↔ r ≤ 1 := by
  constructor
  · intro h
    by_contra hr
    have hr' : 0 < r := lt_trans (by norm_num) (lt_of_not_ge hr)
    obtain ⟨v, w, hvw, hd⟩ := abelianAugmentation_distance_two_exists G hn
    have hne : abelianAugmentationRealCenter G v ≠ abelianAugmentationRealCenter G w :=
      fun he => hvw (abelianAugmentationRealCenter_injective G he)
    have hs := (disjoint_ball_ball_iff hr' hr').mp (h hne)
    change r+r ≤ dist (abelianAugmentationRealMap G v) (abelianAugmentationRealMap G w) at hs
    rw [hd] at hs
    linarith only [hs, hr]
  · intro hr v w hvw
    apply Metric.ball_disjoint_ball
    have hs := abelianAugmentationRealLattice_separated G v w hvw
    linarith only [hr, hs]

theorem abelianAugmentationRealLattice_unitBalls_disjoint :
    Pairwise (fun v w : abelianAugmentationRealLattice G =>
      Disjoint (ball (v : AbelianRealHyperplane G) 1) (ball (w : AbelianRealHyperplane G) 1)) := by
  intro v w hvw
  apply Metric.ball_disjoint_ball
  simpa only [one_add_one_eq_two] using abelianAugmentationRealLattice_separated G v w hvw

variable [DecidableEq G]

theorem abelianAugmentation_density_limit :
    Tendsto (fun r : ℝ => densityAt (abelianAugmentationRealLattice G) r) atTop
      (𝓝 (volume.real (ball (0 : AbelianRealHyperplane G) 1) /
        Real.sqrt ((Fintype.card G : ℝ)^3))) := by
  have h := tendsto_density_real (abelianAugmentationRealLattice G)
    (abelianAugmentationRealLattice_unitBalls_disjoint G)
  rwa [abelianAugmentationRealLattice_covolume_sqrt] at h

theorem abelianRealHyperplane_rank :
    finrank ℝ (AbelianRealHyperplane G) + 1 = Fintype.card G := by
  rw [EuclideanZeroSum.finrank_space G (1 : G)]
  exact card_subtype_ne_succ (1 : G)

/-- Unit-ball volume in the group-coordinate zero-sum hyperplane. -/
theorem abelianAugmentation_unitBall_volume (hn : 2 ≤ Fintype.card G) :
    volume.real (ball (0 : AbelianRealHyperplane G) 1) =
      (Real.sqrt Real.pi)^(Fintype.card G - 1) /
        Real.Gamma (((Fintype.card G - 1 : ℕ) : ℝ) / 2 + 1) := by
  have hr : finrank ℝ (AbelianRealHyperplane G) = Fintype.card G - 1 := by
    have h := abelianRealHyperplane_rank G
    omega
  letI : Nontrivial (AbelianRealHyperplane G) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hr]; omega)
  rw [measureReal_def, InnerProductSpace.volume_ball, hr,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal]
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

/-- Density of the radius-one packing from a finite abelian group. -/
def abelianPackingDensity : ℝ :=
  (Real.sqrt Real.pi)^(Fintype.card G - 1) /
    (Real.Gamma (((Fintype.card G - 1 : ℕ) : ℝ) / 2 + 1) *
      Real.sqrt ((Fintype.card G : ℝ)^3))

theorem abelianPackingDensity_eq (hn : 2 ≤ Fintype.card G) :
    abelianPackingDensity G = volume.real (ball (0 : AbelianRealHyperplane G) 1) /
      ZLattice.covolume (abelianAugmentationRealLattice G) := by
  rw [abelianAugmentation_unitBall_volume G hn, abelianAugmentationRealLattice_covolume_sqrt, div_div]
  rfl

/-- The explicit Gamma quotient is the limit of actual occupied-volume fractions. -/
theorem abelianPackingDensity_limit (hn : 2 ≤ Fintype.card G) :
    Tendsto (fun r : ℝ => densityAt (abelianAugmentationRealLattice G) r) atTop
      (𝓝 (abelianPackingDensity G)) := by
  rw [abelianPackingDensity_eq G hn]
  exact tendsto_density_real _ (abelianAugmentationRealLattice_unitBalls_disjoint G)

theorem abelianPackingDensity_pos (hn : 2 ≤ Fintype.card G) : 0 < abelianPackingDensity G := by
  rw [abelianPackingDensity_eq G hn]
  exact div_pos (unitBall_volume_pos (E := AbelianRealHyperplane G))
    (ZLattice.covolume_pos (abelianAugmentationRealLattice G) volume)

theorem abelianPackingDensity_le_one (hn : 2 ≤ Fintype.card G) : abelianPackingDensity G ≤ 1 := by
  rw [abelianPackingDensity_eq G hn]
  exact unitBall_div_covolume_le_one _ (abelianAugmentationRealLattice_unitBalls_disjoint G)

#print axioms abelianAugmentationRealLattice_balls_disjoint_iff
#print axioms abelianPackingDensity_limit
#print axioms abelianAugmentation_balls_disjoint_iff
#print axioms abelianAugmentation_density_limit
end GaloisForLFunctions.RepresentationLifting
