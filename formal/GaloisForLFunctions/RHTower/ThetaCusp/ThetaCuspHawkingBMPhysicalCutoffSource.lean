import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceSmooth
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCutoff

/-! The exact noncompact source converted into compact smooth physical transposition tests. -/

open Complex Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMJointSource
noncomputable section

/-- The literal reduced source restricted by the strict physical compact window. -/
def physicalCutoffSource (n : ℕ) (s a : ℂ) (p : ℝ × ℝ) : ℂ :=
  (physicalWindow n p : ℂ) * timeReducedCoefficient s a p.1 p.2

theorem physicalCutoffSource_smooth (n : ℕ) (s a : ℂ) :
    ContDiff ℝ ∞ (physicalCutoffSource n s a) := by
  unfold physicalCutoffSource
  exact (Complex.ofRealCLM.contDiff.comp (physicalWindow_smooth n)).mul
    (timeReducedCoefficient_smooth s a)

theorem physicalCutoffSource_hasCompactSupport (n : ℕ) (s a : ℂ) :
    HasCompactSupport (physicalCutoffSource n s a) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc)
  intro p hp
  by_cases hp1 : p.1 ∈ Icc (-(n : ℝ) - 1) ((n : ℝ) + 1)
  · have hp2 : p.2 ∉ Icc (-(n : ℝ) - 1) ((n : ℝ) + 1) := fun h => hp ⟨hp1, h⟩
    unfold physicalCutoffSource physicalWindow
    rw [compactWindow_zero_of_outside n hp2]
    simp
  · unfold physicalCutoffSource physicalWindow
    rw [compactWindow_zero_of_outside n hp1]
    simp

theorem physicalCutoffSource_tsupport_subset_physical (n : ℕ) (s a : ℂ) :
    tsupport (physicalCutoffSource n s a) ⊆ {p : ℝ × ℝ | p.2 < 0} := by
  let S : Set (ℝ × ℝ) := {p | p.2 ≤ physicalBoundary n}
  have hsupp : Function.support (physicalCutoffSource n s a) ⊆ S := by
    intro p hp
    by_contra hbound
    have hgt : physicalBoundary n < p.2 := lt_of_not_ge hbound
    have hzero : physicalCutoffSource n s a p = 0 := by
      unfold physicalCutoffSource
      rw [physicalWindow_zero_above_boundary n p hgt]
      simp
    exact hp hzero
  have hclosed : IsClosed S := isClosed_le continuous_snd continuous_const
  intro p hp
  have hbound : p ∈ S := closure_minimal hsupp hclosed hp
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  exact lt_of_le_of_lt hbound (neg_lt_zero.mpr (inv_pos.mpr hn))

/-- The compact physical tests recover the literal source at every physical event. -/
theorem physicalCutoffSource_eventually_eq (s a : ℂ) (p : ℝ × ℝ) (hp : p.2 < 0) :
    ∀ᶠ n in atTop, physicalCutoffSource n s a p = timeReducedCoefficient s a p.1 p.2 := by
  filter_upwards [physicalWindow_eventually_eq_one p hp] with n hn
  unfold physicalCutoffSource
  rw [hn]
  simp

end
end RHTower.D4BMJointSource
