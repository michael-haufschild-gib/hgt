import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWWeakSourceOpticalWard

open Complex
open scoped InnerProductSpace
open RHTower.D4BMModularCore RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMQuadraticMixedSource

namespace RHTower.D4BMPWCrossWeakWardScratch

noncomputable section
set_option autoImplicit false

theorem cross_parameter_factor (q : XiZeroCopy) :
    parameter q true - star (parameter q false) =
      (((q.1 : ℂ) + star (q.1 : ℂ)) - 1) *
        (-6 + 4 * ((q.1 : ℂ) - star (q.1 : ℂ))) := by
  simp only [parameter, branchParameter, resolventParameter,
    if_neg (by decide : false ≠ true)]
  simp [star_mul, star_add, star_sub]
  ring

theorem cross_weak_ward (q : XiZeroCopy) :
    inner ℂ (embedding (weakResponse q false)) (forcingVector q true) -
      inner ℂ (forcingVector q false) (embedding (weakResponse q true)) =
    (star (parameter q false) - parameter q true) *
      inner ℂ (embedding (weakResponse q false)) (embedding (weakResponse q true)) := by
  have hp := weakResponse_spec q true (weakResponse q false)
  have hm := weakResponse_spec q false (weakResponse q true)
  have hm' :
      inner ℂ (weakResponse q false) (weakResponse q true) -
        (1 - star (parameter q false)) *
          inner ℂ (embedding (weakResponse q false)) (embedding (weakResponse q true)) =
      -inner ℂ (forcingVector q false) (embedding (weakResponse q true)) := by
    have h := congrArg (starRingEnd ℂ) hm
    simpa [CStarModule.star_inner, inner_conj_symm] using h
  linear_combination hp - hm'

def crossOverlap (q : XiZeroCopy) : ℂ :=
  inner ℂ (embedding (weakResponse q false)) (embedding (weakResponse q true))

def crossCurrent (q : XiZeroCopy) : ℂ :=
  inner ℂ (embedding (weakResponse q false)) (forcingVector q true) -
    inner ℂ (forcingVector q false) (embedding (weakResponse q true))

theorem crossCurrent_factor (q : XiZeroCopy) :
    crossCurrent q =
      -(((q.1 : ℂ) + star (q.1 : ℂ)) - 1) *
        (-6 + 4 * ((q.1 : ℂ) - star (q.1 : ℂ))) * crossOverlap q := by
  unfold crossCurrent crossOverlap
  calc
    _ = (star (parameter q false) - parameter q true) *
      inner ℂ (embedding (weakResponse q false)) (embedding (weakResponse q true)) :=
        cross_weak_ward q
    _ = -(parameter q true - star (parameter q false)) *
      inner ℂ (embedding (weakResponse q false)) (embedding (weakResponse q true)) := by ring
    _ = _ := by rw [cross_parameter_factor]; ring

theorem cross_factor_ne_zero (q : XiZeroCopy) :
    (-6 + 4 * ((q.1 : ℂ) - star (q.1 : ℂ))) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp [Complex.sub_re, Complex.mul_re] at hr

theorem center_factor_eq_zero_iff (q : XiZeroCopy) :
    (((q.1 : ℂ) + star (q.1 : ℂ)) - 1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp [Complex.add_re, Complex.sub_re] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp [Complex.add_re, Complex.sub_re, h]
      ring
    · simp [Complex.add_im, Complex.sub_im]

theorem crossCurrent_zero_iff (q : XiZeroCopy) :
    crossCurrent q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 ∨ crossOverlap q = 0 := by
  constructor
  · intro h
    rw [crossCurrent_factor] at h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left
        exact (center_factor_eq_zero_iff q).mp (neg_eq_zero.mp h)
      · exact False.elim ((cross_factor_ne_zero q) h)
    · exact Or.inr h
  · rintro (h | h)
    · have hc := (center_factor_eq_zero_iff q).mpr h
      calc
        crossCurrent q =
            -(((q.1 : ℂ) + star (q.1 : ℂ)) - 1) *
              (-6 + 4 * ((q.1 : ℂ) - star (q.1 : ℂ))) * crossOverlap q :=
          crossCurrent_factor q
        _ = 0 := by rw [hc]; ring
    · simp [crossCurrent_factor, h]

end
end RHTower.D4BMPWCrossWeakWardScratch
