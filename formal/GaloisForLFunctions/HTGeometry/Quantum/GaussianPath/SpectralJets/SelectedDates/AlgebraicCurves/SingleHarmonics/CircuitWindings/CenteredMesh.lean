import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.PhysicalMesh

/-! # Enclosing arcs after subtracting circuit eigenline phases -/

open Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open AntipodalHorizons
noncomputable section

/-- Per-level phase corrections in turns, relative to the same reference
level as the spectral frequencies. -/
def centerOffset {k : ℕ} (i j : Level k) (d : Level k→ℝ) : UnitAddTorus (Outside i j) :=
  fun l => ((d j-d l.val:ℝ):UnitAddCircle)

/-- A common short arc after correcting the spectral lines at a true visit
forces a slightly wider corrected arc at the preceding mesh observation. -/
theorem centered_prior_spread (k : ℕ) (i j : Level k) [Nonempty (Outside i j)]
    (x : Coupling k) (d : Level k→ℝ) (n : ℕ) {q s δ r : ℝ}
    (hr : 0≤r) (hq : q≤s) (hδ : s-q≤δ) :
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    E j < E i → (∀ l, E j ≤ E l ∧ E l ≤ E i) →
    (fun l => ((date E i j n s*(-E l/(2*π))-d l:ℝ):UnitAddCircle))∈enclosingUnitArc r →
      centerOffset i j d+spectators k i j n q x∈enclosingUnitArc (r+δ) := by
  intro E he hall hfit
  have hg := sub_pos.mpr he
  have hf (l : Outside i j) : gapFrequency k i j x l∈Icc (-1:ℝ) 0 := by
    have h := hall l.val
    exact ⟨neg_le_neg ((div_le_one hg).mpr (sub_le_sub_right h.2 _)),
      neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr h.1) hg.le)⟩
  apply mesh_encloses Subtype.val _ hf _ j hr hq hδ hfit
  intro l
  change ((d j-d l.val:ℝ):UnitAddCircle)+((2*π*((n:ℝ)+(1/2+q))*gapFrequency k i j x l/(2*π):ℝ):UnitAddCircle)=
    ((date E i j n s*(-E l.val/(2*π))-d l.val:ℝ):UnitAddCircle)-
    ((date E i j n s*(-E j/(2*π))-d j:ℝ):UnitAddCircle)+(((q-s)*gapFrequency k i j x l:ℝ):UnitAddCircle)
  rw [←AddCircle.coe_add,←AddCircle.coe_sub,←AddCircle.coe_add]
  congr 1
  change d j-d l.val+2*π*((n:ℝ)+(1/2+q))*(-((E l.val-E j)/(E i-E j)))/(2*π)=
    (((n:ℝ)+(1/2+s))*(2*π/(E i-E j))*(-E l.val/(2*π))-d l.val-
    (((n:ℝ)+(1/2+s))*(2*π/(E i-E j))*(-E j/(2*π))-d j))+
    (q-s)*(-((E l.val-E j)/(E i-E j)))
  field_simp [hg.ne',Real.pi_ne_zero]
  ring

#print axioms centered_prior_spread
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
