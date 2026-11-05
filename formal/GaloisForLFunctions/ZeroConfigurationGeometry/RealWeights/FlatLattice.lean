import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.Readout
import GaloisForLFunctions.SquareRootThreshold.NyquistResolutionOfTheWeilForm

/-!
# Flat images with arbitrarily many small atoms

The simple on-line lattice has density proportional to its lattice parameter.
Reciprocal-density weights keep every fixed-aperture image equal to the same
flat inner product while allowing arbitrarily many atoms in a unit interval.
Absolute Lorentzian summability is retained.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold _root_.RHTower

/-- A fixed flat window image admits arbitrarily many positive, real-weighted atoms
in a unit height interval. The atom weight is the reciprocal of twice the lattice parameter. -/
theorem exists_arbitrarily_many_flat_lattice_atoms (a : ℝ) (N : ℕ) :
    ∃ (L : ℝ) (hL : 0 < L), a ≤ L ∧ 0 < (2 * L)⁻¹ ∧ (2 * L)⁻¹ < 1 ∧
      (∃ s : Finset ℂ, s.card = N ∧
        ∀ z ∈ s, z ∈ (simpleHalfLatticeConfig hL).carrier ∧ 0 < z.im ∧ z.im ≤ 1) ∧
      ∀ (f g : ℝ → ℂ), ContDiff ℝ 2 f → Continuous g →
        tsupport f ⊆ Icc (-a) a → tsupport g ⊆ Icc (-a) a →
        (((2 * L : ℝ) : ℂ)⁻¹ * (simpleHalfLatticeConfig hL).W f g) =
          ∫ t, f t * conj (g t) := by
  classical
  set L := max a (π * ((N : ℝ) + 1)) with hLdef
  have hbig : π * ((N : ℝ) + 1) ≤ L := le_max_right _ _
  have hL : 0 < L := (by positivity : 0 < π * ((N : ℝ) + 1)).trans_le hbig
  have hLa : a ≤ L := le_max_left _ _
  have hL3 : 3 < L := by
    have hh : π ≤ π * ((N : ℝ) + 1) := by
      have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith only [hn, Real.pi_pos]
    exact Real.pi_gt_three.trans_le (hh.trans hbig)
  refine ⟨L, hL, hLa, by positivity, ?_, ?_, ?_⟩
  · rw [inv_lt_one₀ (by positivity : 0 < 2 * L)]
    linarith only [hL3]
  · let p : Fin N → ℂ := fun k => verticalLatticePoint (2 * L) 0 ((k.val : ℤ) + 1)
    have hp : Function.Injective p := by
      intro k j h
      have hh := verticalLatticePoint_injective (mul_pos two_pos hL) 0 h
      apply Fin.ext
      exact_mod_cast add_right_cancel hh
    refine ⟨Finset.univ.map ⟨p, hp⟩, ?_, ?_⟩
    · simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    · intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hz
      refine ⟨⟨(k.val : ℤ) + 1, rfl⟩, ?_⟩
      have him : (p k).im = ((k.val : ℝ) + 1) * (π / L) := by
        simp only [p, verticalLatticePoint, Int.cast_add, Int.cast_natCast, Int.cast_one]
        field_simp
      change 0 < (p k).im ∧ (p k).im ≤ 1
      rw [him]
      refine ⟨by positivity, ?_⟩
      have hk : (k.val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt k.isLt
      rw [← mul_div_assoc, div_le_iff₀ hL, one_mul]
      calc ((k.val : ℝ) + 1) * π ≤ (N : ℝ) * π :=
            mul_le_mul_of_nonneg_right hk Real.pi_pos.le
        _ ≤ π * ((N : ℝ) + 1) := by linarith only [Real.pi_pos]
        _ ≤ L := hbig
  · intro f g hf hg hfs hgs
    have hfsL := hfs.trans (Icc_subset_Icc (neg_le_neg hLa) hLa)
    have hgsL := hgs.trans (Icc_subset_Icc (neg_le_neg hLa) hLa)
    have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    rw [W_simpleHalfLatticeConfig hL hf hg hfsL hgsL]
    push_cast
    field_simp

/-- Each simple lattice atom has reciprocal-density weight. -/
def flatLatticeWeight {L : ℝ} (hL : 0 < L) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ (simpleHalfLatticeConfig hL).carrier then (2 * L)⁻¹ else 0

private theorem flatLatticeWeight_cast {L : ℝ} (hL : 0 < L) (z : ℂ) :
    (flatLatticeWeight hL z : ℂ) = (((2 * L : ℝ) : ℂ)⁻¹) *
      multDiff (simpleHalfLatticeConfig hL) emptyZeroConfig z := by
  classical
  rw [multDiff_emptyZeroConfig]
  by_cases hz : z ∈ (simpleHalfLatticeConfig hL).carrier
  · rw [flatLatticeWeight, if_pos hz, Set.indicator_of_mem hz]
    have hm : (simpleHalfLatticeConfig hL).mult z = 1 := rfl
    rw [hm, Nat.cast_one, mul_one, Complex.ofReal_inv]
  · rw [flatLatticeWeight, if_neg hz, Set.indicator_of_notMem hz,
      Complex.ofReal_zero, mul_zero]

/-- Reciprocal-density lattice weights have finite absolute Lorentzian mass. -/
theorem summable_flatLatticeWeight {L : ℝ} (hL : 0 < L) :
    Summable fun z => |flatLatticeWeight hL z| / (1 + Complex.normSq (gammaOf z)) := by
  classical
  have hs : Summable fun z =>
      ‖multDiff (simpleHalfLatticeConfig hL) emptyZeroConfig z‖ /
        (1 + Complex.normSq (gammaOf z)) := by
    have hh := summable_indicator_tempered (simpleHalfLatticeConfig hL)
      (temperedConfig_simpleHalfLatticeConfig hL)
    refine hh.congr fun z => ?_
    rw [multDiff_emptyZeroConfig]
    by_cases hz : z ∈ (simpleHalfLatticeConfig hL).carrier
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
  have hh : Summable fun z => ‖(flatLatticeWeight hL z : ℂ)‖ /
      (1 + Complex.normSq (gammaOf z)) :=
    (hs.mul_left ‖(((2 * L : ℝ) : ℂ)⁻¹)‖).congr fun z => by
      rw [flatLatticeWeight_cast, norm_mul]
      ring
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hh

/-- The weighted image is exactly the normalized simple-lattice Weil form. -/
theorem weightedImage_flatLatticeWeight {L : ℝ} (hL : 0 < L) (f g : ℝ → ℂ) :
    weightedImage (fun z => (flatLatticeWeight hL z : ℂ)) f g =
      (((2 * L : ℝ) : ℂ)⁻¹) * (simpleHalfLatticeConfig hL).W f g := by
  unfold weightedImage
  simp_rw [flatLatticeWeight_cast, mul_assoc, multDiff_emptyZeroConfig]
  rw [tsum_mul_left, ← W_eq_tsum_indicator]

/-- A fixed flat camera image admits arbitrarily many positive atoms in a unit interval,
even with all atom weights below one and finite absolute Lorentzian mass. -/
theorem exists_real_weighted_flat_image_with_many_atoms (a : ℝ) (N : ℕ) :
    ∃ w : ℂ → ℝ,
      (∀ z, 0 ≤ w z ∧ w z < 1) ∧
      (∀ z, w z ≠ 0 → z.re = 1 / 2) ∧
      (Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z))) ∧
      (∃ s : Finset ℂ, s.card = N ∧ ∀ z ∈ s, 0 < w z ∧ 0 < z.im ∧ z.im ≤ 1) ∧
      ∀ f g : ℝ → ℂ, ApertureWindow a f → ApertureWindow a g →
        weightedImage (fun z => (w z : ℂ)) f g = ∫ t, f t * conj (g t) := by
  classical
  obtain ⟨L, hL, _, hwpos, hwsmall, ⟨s, hsN, hs⟩, hflat⟩ :=
    exists_arbitrarily_many_flat_lattice_atoms a N
  refine ⟨flatLatticeWeight hL, ?_, ?_, summable_flatLatticeWeight hL, ?_, ?_⟩
  · intro z
    unfold flatLatticeWeight
    split_ifs
    · exact ⟨hwpos.le, hwsmall⟩
    · norm_num
  · intro z hz
    have hzmem : z ∈ (simpleHalfLatticeConfig hL).carrier := by
      by_contra hn
      exact hz (by simp only [flatLatticeWeight, if_neg hn])
    change ∃ k : ℤ, verticalLatticePoint (2 * L) 0 k = z at hzmem
    obtain ⟨k, rfl⟩ := hzmem
    simp only [verticalLatticePoint, add_zero]
  · refine ⟨s, hsN, fun z hz => ?_⟩
    obtain ⟨hzmem, hzim, hzim1⟩ := hs z hz
    refine ⟨?_, hzim, hzim1⟩
    rw [flatLatticeWeight, if_pos hzmem]
    exact hwpos
  · intro f g hf hg
    rw [weightedImage_flatLatticeWeight]
    exact hflat f g hf.1 hg.1.continuous hf.2 hg.2

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_arbitrarily_many_flat_lattice_atoms

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.summable_flatLatticeWeight
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weightedImage_flatLatticeWeight
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_real_weighted_flat_image_with_many_atoms
