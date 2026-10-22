import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedOnsetRealTilt
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMClearedOnsetPulseTransform
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-! The prescribed onset survives sufficiently high original physical QNM overtones. -/
namespace RHTower.D4BMJointSource
open Complex D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- Both original QNM branches, with their original overtone index. -/
def physicalOvertoneFrequency (q : XiZeroCopy) (side : Bool) (n : ℕ) : ℂ :=
  if side then -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)
    else -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)

theorem physicalOvertoneFrequency_eq (q : XiZeroCopy) (side : Bool) (n : ℕ) :
    physicalOvertoneFrequency q side n = physicalFundamentalFrequency q side-2*(n:ℂ) := by
  cases side <;> simp only [physicalOvertoneFrequency,physicalFundamentalFrequency,
    Bool.false_eq_true,↓reduceIte,thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  all_goals norm_num; ring_nf; simp only [Complex.I_sq]; ring

theorem physicalOvertoneFrequency_sub_sourceRate_ne_zero
    (q : XiZeroCopy) (branch side : Bool) (n : ℕ) :
    physicalOvertoneFrequency q side n-2*physicalRate q branch ≠ 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  rw [physicalOvertoneFrequency_eq,physicalFundamentalFrequency_eq]
  cases side <;> cases branch <;> simp only [Bool.false_eq_true,↓reduceIte,physicalRate]
  all_goals
    intro hz
    have hh := congrArg Complex.im hz
    norm_num [Complex.mul_im,Complex.div_im] at hh
    apply hi
    linarith

/-- The temporal factor is exactly the same pulse, evaluated on the actual overtone ladder. -/
theorem physicalOvertone_clearedOnset_eq (q : XiZeroCopy) (branch side : Bool) (n : ℕ) :
    clearedOnset (physicalRate q branch) (physicalOvertoneFrequency q side n) =
      onsetPulseTransform (2*physicalRate q branch-physicalFundamentalFrequency q side+2*(n:ℂ)) := by
  rw [clearedOnset_eq_onsetPulseTransform,physicalOvertoneFrequency_eq]
  congr 1
  ring

/-- No duration is selected: for every actual copy and each original branch/side choice,
both fixed onset factors are nonzero at all sufficiently high physical overtones. -/
theorem physicalOvertone_fixedOnset_eventually_ne_zero (q : XiZeroCopy) (branch side : Bool) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n →
      clearedOnset (physicalRate q branch) (physicalOvertoneFrequency q side n) ≠ 0 ∧
      continuedOnset (physicalRate q branch) (physicalOvertoneFrequency q side n) ≠ 0 := by
  obtain ⟨N,hN⟩ := onsetPulseTransform_overtone_eventually_ne_zero
    (2*physicalRate q branch-physicalFundamentalFrequency q side)
  refine ⟨N,fun n hn => ?_⟩
  have hc : clearedOnset (physicalRate q branch) (physicalOvertoneFrequency q side n) ≠ 0 := by
    rw [physicalOvertone_clearedOnset_eq]
    exact hN n hn
  refine ⟨hc,?_⟩
  let w := physicalOvertoneFrequency q side n
  let s := physicalRate q branch
  have hs : w-2*s ≠ 0 := physicalOvertoneFrequency_sub_sourceRate_ne_zero q branch side n
  have he : clearedOnset s w = (w-2*s)*continuedOnset s w := by
    unfold clearedOnset continuedOnset
    field_simp [hs]
  intro hz
  apply hc
  change clearedOnset s w=0
  rw [he,hz,mul_zero]

/-- One overtone threshold works simultaneously for the four original physical choices. -/
theorem physicalOvertone_all_fixedOnsets_eventually_ne_zero (q : XiZeroCopy) :
    ∃ N : ℕ, ∀ n : ℕ, N≤n → ∀ branch side : Bool,
      clearedOnset (physicalRate q branch) (physicalOvertoneFrequency q side n) ≠ 0 ∧
      continuedOnset (physicalRate q branch) (physicalOvertoneFrequency q side n) ≠ 0 := by
  classical
  choose N hN using physicalOvertone_fixedOnset_eventually_ne_zero q
  refine ⟨max (max (N false false) (N false true)) (max (N true false) (N true true)),?_⟩
  intro n hn branch side
  cases branch <;> cases side <;> apply hN _ _ n <;> omega

end
end RHTower.D4BMJointSource
