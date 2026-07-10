import GaloisForLFunctions.RHTower.NoCrossColumnHealing

/-!
# Explicit pole provider for the no-extension interface

The abstract `NoExtensionAt` hypothesis is realized by the elementary reciprocal column on its
punctured plane.  If an analytic element agreed with the reciprocal off the pole, continuity would
make `(z-b)g(z)` tend to zero at `b`, while the punctured identity makes the same product tend to
one.  The existing no-healing theorem then transfers this concrete obstruction across the
nonvanishing entire exponential column.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The simple reciprocal column with pole at `b`. -/
def simplePoleAt (b z : ℂ) : ℂ := 1 / (z - b)

/-- The simple pole supplies a genuine, unconditional `NoExtensionAt` provider on the punctured
plane. -/
theorem simplePoleAt_noExtensionAt (b : ℂ) :
    NoExtensionAt (simplePoleAt b) ({b}ᶜ : Set ℂ) b := by
  rintro ⟨U, g, hUopen, hbU, hgan, hgeq⟩
  have hsub : Tendsto (fun z : ℂ => z - b) (nhds b) (nhds 0) := by
    have hc : Continuous (fun z : ℂ => z - b) := continuous_id.sub continuous_const
    simpa using hc.tendsto b
  have hg : Tendsto g (nhds b) (nhds (g b)) := (hgan b hbU).continuousAt
  have hprod : Tendsto (fun z : ℂ => (z - b) * g z) (nhds b) (nhds 0) := by
    simpa using hsub.mul hg
  have hpunc : Tendsto (fun z : ℂ => (z - b) * g z)
      (nhdsWithin b ({b}ᶜ : Set ℂ)) (nhds 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hUopen.mem_nhds hbU), self_mem_nhdsWithin] with z hzU hzb
    have hzmem : z ∈ U ∩ ({b}ᶜ : Set ℂ) := ⟨hzU, by simpa using hzb⟩
    rw [hgeq z hzmem, simplePoleAt]
    have hne : z - b ≠ 0 := sub_ne_zero.mpr hzb
    field_simp
  exact one_ne_zero
    (tendsto_nhds_unique (hprod.mono_left nhdsWithin_le_nhds) hpunc).symm

/-- A simple pole multiplied by the nonvanishing entire exponential partner. -/
def expOverSimplePole (b z : ℂ) : ℂ := simplePoleAt b z * Complex.exp z

/-- Concrete no-healing capstone: the exponential column cannot heal the simple pole. -/
theorem expOverSimplePole_noExtensionAt (b : ℂ) :
    NoExtensionAt (expOverSimplePole b) ({b}ᶜ : Set ℂ) b := by
  apply no_healing (Φ := simplePoleAt b) (Ψ := Complex.exp)
      (F := expOverSimplePole b)
  · intro z hz
    rfl
  · exact simplePoleAt_noExtensionAt b
  · refine ⟨Set.univ, Complex.exp, isOpen_univ, Set.mem_univ b, ?_,
      Complex.exp_ne_zero b, ?_⟩
    · intro z hz
      exact analyticAt_id.cexp
    · intro z hz
      rfl

end

end RHTower
