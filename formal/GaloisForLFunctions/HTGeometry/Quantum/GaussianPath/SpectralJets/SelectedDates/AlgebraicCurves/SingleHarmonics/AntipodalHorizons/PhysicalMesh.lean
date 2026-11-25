import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.SpectatorLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.ArcMesh

/-! # Covering every scalar visit after an antipode of the full spectral width -/

open Set Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open EmptyVisitFlux
noncomputable section

/-- Physical date q spectral periods after the nth antipode. -/
def date {I : Type*} (E : I→ℝ) (i j : I) (n : ℕ) (q : ℝ) :=
  ((n:ℝ)+(1/2+q))*(2*π/(E i-E j))

/-- When the selected gap is the full width, a scalar visit forces a
short enclosing arc at the preceding time-mesh observation. -/
theorem prior_spread (k : ℕ) (i j : Level k) [Nonempty (Outside i j)] (x : Coupling k)
    (n : ℕ) {q s δ r : ℝ} (hr : 0≤r) (hq : q≤s) (hδ : s-q≤δ) :
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    E j < E i → (∀ l, E j≤E l ∧ E l≤E i) →
    flow (fun l => -E l/(2*π)) (date E i j n s) ∈ enclosingUnitArc r →
      spectators k i j n q x ∈ enclosingUnitArc (r+δ) := by
  intro E he hall hfit
  have hg := sub_pos.mpr he
  have hf (l : Outside i j) : gapFrequency k i j x l∈Icc (-1:ℝ) 0 := by
    have h := hall l.val
    exact ⟨neg_le_neg ((div_le_one hg).mpr (sub_le_sub_right h.2 _)),
      neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr h.1) hg.le)⟩
  apply mesh_encloses Subtype.val _ hf _ j hr hq hδ hfit
  intro l
  change ((2*π*((n:ℝ)+(1/2+q))*gapFrequency k i j x l/(2*π):ℝ):UnitAddCircle)=
    ((date E i j n s*(-E l.val/(2*π)):ℝ):UnitAddCircle)-
    ((date E i j n s*(-E j/(2*π)):ℝ):UnitAddCircle)+(((q-s)*gapFrequency k i j x l:ℝ):UnitAddCircle)
  rw [←AddCircle.coe_sub,←AddCircle.coe_add]
  congr 1
  change 2*π*((n:ℝ)+(1/2+q))*(-((E l.val-E j)/(E i-E j)))/(2*π)=_
  dsimp only [date,gapFrequency]
  change _=(((n:ℝ)+(1/2+s))*(2*π/(E i-E j))*(-E l.val/(2*π))-
    ((n:ℝ)+(1/2+s))*(2*π/(E i-E j))*(-E j/(2*π)))+(q-s)*(-((E l.val-E j)/(E i-E j)))
  field_simp [hg.ne',Real.pi_ne_zero]
  ring

/-- An interval of M mesh steps requires only M+1 tests, including both
endpoints. The grid spacing is in units of the actual full spectral period. -/
theorem grid_covers (k : ℕ) (i j : Level k) [Nonempty (Outside i j)] (x : Coupling k)
    (n M : ℕ) {δ r : ℝ} (hd : 0<δ) (hr : 0≤r) :
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    E j<E i → (∀ l, E j≤E l ∧ E l≤E i) →
    (∃ s ∈ Icc (0:ℝ) ((M:ℝ)*δ), flow (fun l => -E l/(2*π)) (date E i j n s) ∈ enclosingUnitArc r) →
    ∃ h : Fin (M+1), spectators k i j n ((h.val:ℝ)*δ) x∈enclosingUnitArc (r+δ) := by
  intro E he hall ⟨s,hs,hvisit⟩
  have hpos := div_nonneg hs.1 hd.le
  let m := ⌊s/δ⌋₊
  have hlo : (m:ℝ)*δ≤s := (le_div_iff₀ hd).mp (Nat.floor_le hpos)
  have hhi := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (s/δ))
  have hM : (m:ℝ)≤M := (Nat.floor_le hpos).trans ((div_le_iff₀ hd).mpr hs.2)
  have hm : m≤M := by exact_mod_cast hM
  exact ⟨⟨m,Nat.lt_succ_of_le hm⟩,prior_spread k i j x n hr hlo
    (by dsimp only [m]; linarith only [hhi]) he hall hvisit⟩

#print axioms grid_covers
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
