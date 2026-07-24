import GaloisForLFunctions.RHTower.XiDefectPersistentLocalLoopUniversalityLaw
import GaloisForLFunctions.RHTower.XiDescentFarFieldAllRungLoopDrainUniversalityLaw

/-!
# Xi persistent-loop critical-half-strip confinement

A persistently nontrivial descended rung-one Xi loop cannot enter the Euler-product far field:
there every sufficiently small loop has trivial deck character at every dyadic rung.  Intersecting
the two local radii confines the loop observable itself, without first assuming an Xi zero.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Persistent-loop upper-wall universality law.** A persistently nontrivial descended
rung-one Xi loop forces `Re ρ ≤ 1`, without any Xi-zero hypothesis. -/
theorem persistentXiDefectLoop_re_le_one
    (ρ : ℂ) (hpersistent : PersistentXiDefectLoop ρ) :
    ρ.re ≤ 1 := by
  by_contra hnot
  have hfar : 1 < ρ.re := lt_of_not_ge hnot
  obtain ⟨Rp, hRp, hp⟩ := hpersistent
  obtain ⟨Rf, hRf, hf⟩ :=
    xiDescent_farField_allRungLocalLoopDrain hfar 1
  let r : ℝ := min Rp Rf / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrp : r < Rp := by
    dsimp [r]
    have hmin : 0 < min Rp Rf := lt_min hRp hRf
    nlinarith [min_le_left Rp Rf]
  have hrf : r < Rf := by
    dsimp [r]
    have hmin : 0 < min Rp Rf := lt_min hRp hRf
    nlinarith [min_le_right Rp Rf]
  have hne := hp r hr hrp
  have heq := (hf r hr hrf).2.1
  exact hne (by simpa using heq)

/-- **Xi persistent-loop critical-half-strip confinement law.** Once its base lies right of the
critical line, persistent descended rung-one monodromy is confined to
`1/2 < Re ρ ≤ 1`. -/
theorem persistentXiDefectLoop_criticalHalfStripConfinementUniversality
    (ρ : ℂ) (hright : ρ ∈ rightHalf)
    (hpersistent : PersistentXiDefectLoop ρ) :
    ρ.re ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
  ⟨mem_rightHalf.mp hright, persistentXiDefectLoop_re_le_one ρ hpersistent⟩

end

end RHTower
