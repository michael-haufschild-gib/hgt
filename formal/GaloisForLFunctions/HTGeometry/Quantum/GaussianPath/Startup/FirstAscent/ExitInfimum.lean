import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Locating the first exit from an affordable set -/
open Set
namespace GaloisForLFunctions.HTGeometry.FirstAscent

/-- If all times through a are affordable and the interval immediately
above b is unaffordable, the infimum of the actual exit times lies in [a,b]. -/
theorem first_exit_bracket (P : ℝ→Prop) {a b T : ℝ} (hb : 0 ≤ b) (hT : b<T)
    (hl : ∀ t ∈ Icc 0 a, P t) (hu : ∀ t ∈ Icc 0 T, P t → t ≤ b) :
    sInf {t : ℝ | 0 ≤ t ∧ ¬P t} ∈ Icc a b := by
  let bad := {t : ℝ | 0 ≤ t ∧ ¬P t}
  have he (t : ℝ) (ht : b<t) (htT : t ≤ T) : t∈bad := by
    have ht0 := hb.trans ht.le
    exact ⟨ht0,fun hp => ht.not_ge (hu t ⟨ht0,htT⟩ hp)⟩
  have hne : bad.Nonempty := ⟨T,he T hT le_rfl⟩
  have hbd : BddBelow bad := ⟨0,fun _ h => h.1⟩
  change a ≤ sInf bad ∧ sInf bad ≤ b
  constructor
  · apply le_csInf hne
    intro t ht
    exact le_of_not_gt fun hh => ht.2 (hl t ⟨ht.1,hh.le⟩)
  · by_contra! hh
    let v := (b+min (sInf bad) T)/2
    have hpos : b<min (sInf bad) T := lt_min hh hT
    have hv : b<v := by dsimp only [v]; linarith only [hpos]
    have hmin : v<min (sInf bad) T := by dsimp only [v]; linarith only [hpos]
    have h := csInf_le hbd (he v hv (hmin.le.trans (min_le_right ..)))
    exact (hmin.trans_le (min_le_left ..)).not_ge h

end GaloisForLFunctions.HTGeometry.FirstAscent
