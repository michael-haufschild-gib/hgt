import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SeamTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.LengthScales

/-! # Exponential tail on the common spatial boundary -/

open MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- A fixed amount of seam energy per packet fails with exponentially
small probability in the packet count, independently of packet length. -/
theorem exists_seam_rate :
    ∃ B>0, ∀ {n L : ℕ}, 0<L →
      let q := ((n+2:ℕ):ℝ)/L
      let T := seamNeighbourhood (SpectralGapMass.Bulk.PeriodicCuts.labels (n:=n) L none)
      let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
      1≤q → μ.real {x | B*q≤energyOn T x} ≤ exp (-q) := by
  have hs : 0<sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hl : 0≤log (sqrt 2) := log_nonneg (by norm_num)
  let B := 4*(1032*log (sqrt 2)+1)
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro n L hL q T μ hq
  let j := 516*((n+2)/L+1)
  have hj := (packet_number (n:=n) hL).2.2
  have hdim : (j:ℝ)≤1032*q := by
    dsimp only [j]
    rw [Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hj,hq]
  have hp := periodic_seam_tail n L (B*q)
  apply le_of_mul_le_mul_left _ (exp_pos (B*q/4))
  apply hp.trans
  change (sqrt 2)^j≤exp (B*q/4)*exp (-q)
  rw [←exp_log hs,←exp_nat_mul,←exp_add,exp_le_exp]
  have hd := mul_le_mul_of_nonneg_right hdim hl
  dsimp only [B]
  linarith only [hd]

/-- Discard only total energy and longitudinal field at this stage. They
obey a strong law on the nested prefixes and cost no grid union factor. -/
def globalBounds (n : ℕ) (F E : ℝ) : Set (PathLabel n→ℝ) :=
  {x | F≤∑ i : Fin (n+2), |x (.inl (i,2))|} ∩ {x | energyOn univ x≤E}

theorem measurable_globalBounds (n : ℕ) (F E : ℝ) : MeasurableSet (globalBounds n F E) := by
  exact (measurableSet_le measurable_const (by fun_prop)).inter
    (measurableSet_le (by unfold energyOn; fun_prop) measurable_const)

theorem split_probability {n s : ℕ} (T : Finset (PathLabel n)) (F E B e t : ℝ) :
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    μ.real (affordableDraw n s e t ∩ globalBounds n F E) ≤
      μ.real (affordableDraw n s e t ∩ drawBounds T F E B)+μ.real {x | B≤energyOn T x} := by
  intro μ
  apply (measureReal_mono (μ:=μ) (s₂:=((affordableDraw n s e t ∩ drawBounds T F E B) ∪
    {x | B≤energyOn T x})) ?_).trans (measureReal_union_le ..)
  rintro x ⟨hx,he⟩
  rcases le_total (energyOn T x) B with h|h
  · exact Or.inl ⟨hx,he,h⟩
  · exact Or.inr h

#print axioms exists_seam_rate
#print axioms split_probability
end
end GaloisForLFunctions.HTGeometry.BlockDilations
