import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRetraction

/-!
# The cubic retract is a diamond boundary

An explicit homeomorphism identifies the middle-gap-zero retract with
{(x,y) : |x|+|y|=1}. The inverse reconstructs nonnegative gap pairs from
positive and negative parts. Combined with CubicRetraction this identifies
the ring retained by the strong deformation of the physical norming complex.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


def cubicDiamond : Set (ℝ × ℝ) := {z | |z.1|+|z.2|=1}
def cubicRingCoordinates (g : Fin 5 → ℝ) : ℝ × ℝ := (g 0-g 1,g 3-g 4)
def cubicDiamondProbe (z : ℝ × ℝ) : Fin 5 → ℝ :=
  ![(|z.1|+z.1)/2,(|z.1|-z.1)/2,0,(|z.2|+z.2)/2,(|z.2|-z.2)/2]

theorem cubicDiamondProbe_nonneg (z : ℝ × ℝ) (q : Fin 5) :
    0 ≤ cubicDiamondProbe z q := by
  fin_cases q
  · change 0 ≤ (|z.1|+z.1)/2
    linarith only [neg_le_abs z.1]
  · change 0 ≤ (|z.1|-z.1)/2
    linarith only [le_abs_self z.1]
  · exact le_rfl
  · change 0 ≤ (|z.2|+z.2)/2
    linarith only [neg_le_abs z.2]
  · change 0 ≤ (|z.2|-z.2)/2
    linarith only [le_abs_self z.2]

theorem cubicDiamondProbe_mem : MapsTo cubicDiamondProbe cubicDiamond cubicRingSection := by
  intro z hz
  refine ⟨⟨cubicDiamondProbe_nonneg z,?_,?_,?_,?_,?_⟩,rfl⟩
  · change (|z.1|+z.1)/2+(|z.1|-z.1)/2+0+(|z.2|+z.2)/2+(|z.2|-z.2)/2=1
    change |z.1|+|z.2|=1 at hz
    linarith only [hz]
  · change ((|z.1|+z.1)/2)*((|z.1|-z.1)/2)=0
    nlinarith only [sq_abs z.1]
  · exact mul_zero _
  · exact zero_mul _
  · change ((|z.2|+z.2)/2)*((|z.2|-z.2)/2)=0
    nlinarith only [sq_abs z.2]

theorem cubicRingCoordinates_mem : MapsTo cubicRingCoordinates cubicRingSection cubicDiamond := by
  intro g hg
  rcases hg with ⟨⟨hnn,hsum,h01,h12,h23,h34⟩,h2⟩
  have hx : |g 0-g 1|=g 0+g 1 := by
    rcases mul_eq_zero.mp h01 with h | h
    · simp [h,abs_of_nonneg (hnn 1)]
    · simp [h,abs_of_nonneg (hnn 0)]
  have hy : |g 3-g 4|=g 3+g 4 := by
    rcases mul_eq_zero.mp h34 with h | h
    · simp [h,abs_of_nonneg (hnn 4)]
    · simp [h,abs_of_nonneg (hnn 3)]
  change |g 0-g 1|+|g 3-g 4|=1
  rw [hx,hy]
  linarith only [hsum,h2]

theorem cubicRingCoordinates_rightInverse (z : ℝ × ℝ) :
    cubicRingCoordinates (cubicDiamondProbe z)=z := by
  apply Prod.ext
  · change (|z.1|+z.1)/2-(|z.1|-z.1)/2=z.1
    ring
  · change (|z.2|+z.2)/2-(|z.2|-z.2)/2=z.2
    ring

theorem cubicRingCoordinates_leftInverse :
    Set.EqOn (fun g => cubicDiamondProbe (cubicRingCoordinates g)) id cubicRingSection := by
  intro g hg
  rcases hg with ⟨⟨hnn,hsum,h01,h12,h23,h34⟩,h2⟩
  have hx : |g 0-g 1|=g 0+g 1 := by
    rcases mul_eq_zero.mp h01 with h | h
    · simp [h,abs_of_nonneg (hnn 1)]
    · simp [h,abs_of_nonneg (hnn 0)]
  have hy : |g 3-g 4|=g 3+g 4 := by
    rcases mul_eq_zero.mp h34 with h | h
    · simp [h,abs_of_nonneg (hnn 4)]
    · simp [h,abs_of_nonneg (hnn 3)]
  ext q
  fin_cases q
  · change (|g 0-g 1|+(g 0-g 1))/2=g 0
    rw [hx]
    ring
  · change (|g 0-g 1|-(g 0-g 1))/2=g 1
    rw [hx]
    ring
  · exact h2.symm
  · change (|g 3-g 4|+(g 3-g 4))/2=g 3
    rw [hy]
    ring
  · change (|g 3-g 4|-(g 3-g 4))/2=g 4
    rw [hy]
    ring

theorem cubicRingCoordinates_continuous : Continuous cubicRingCoordinates := by
  unfold cubicRingCoordinates
  fun_prop

theorem cubicDiamondProbe_continuous : Continuous cubicDiamondProbe := by
  apply continuous_pi
  intro q
  fin_cases q <;> simp only [cubicDiamondProbe]
  all_goals fun_prop

def cubicRingDiamond : cubicRingSection ≃ₜ cubicDiamond where
  toFun g := ⟨cubicRingCoordinates g.val,cubicRingCoordinates_mem g.property⟩
  invFun z := ⟨cubicDiamondProbe z.val,cubicDiamondProbe_mem z.property⟩
  left_inv g := Subtype.ext (cubicRingCoordinates_leftInverse g.property)
  right_inv z := Subtype.ext (cubicRingCoordinates_rightInverse z.val)
  continuous_toFun := (cubicRingCoordinates_continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (cubicDiamondProbe_continuous.comp continuous_subtype_val).subtype_mk _

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
