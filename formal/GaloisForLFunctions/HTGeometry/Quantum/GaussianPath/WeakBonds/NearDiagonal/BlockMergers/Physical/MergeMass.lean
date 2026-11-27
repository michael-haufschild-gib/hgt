import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.SeedMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.SumSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.ProductMass

/-! # Probability retained at one balanced physical merger -/
open Set MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- The nine new bond coefficients are independent of both child Hamiltonians. -/
def seamBox (δ : ℝ) : Set (Fin 3×Fin 3→ℝ) := univ.pi fun _ => Icc (-δ) δ

def gapMass (n : ℕ) := (standardLaw (PathLabel n)).real (gapEvent n (gapScale (n+2)))

/-- Product levels separated at twice the parent scale survive a seam
whose nine Pauli coefficients each cost at most a twentieth of that scale. -/
theorem balanced_merge_mass (l r : ℕ) (hl : l≤r) (hr : r≤l+1) :
    gapMass l*gapMass r*(standardLaw (Fin 3×Fin 3)).real (seamBox (gapScale (l+r+4)/20)) ≤
      (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))*gapMass (l+r+2) := by
  let K := l+r+4
  let g := gapScale (r+2)
  let d := g/(8*(gridCount l r:ℝ))
  let B := seamBox (gapScale K/20)
  let F : Set ((PathLabel l→ℝ)×(PathLabel r→ℝ)) := {p | ∀ u v : Fin (2^(l+2))×Fin (2^(r+2)),
    u≠v → d≤|(energies l p.1 u.1+energies r p.2 u.2)-(energies l p.1 v.1+energies r p.2 v.2)|}
  let μ := (standardLaw (PathLabel l)).prod (standardLaw (PathLabel r))
  let ν := standardLaw (Fin 3×Fin 3)
  let c := (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))
  have hc : 0≤c := by dsimp only [c]; positivity
  have hs : 2*gapScale K≤d := parent_spacing l r hr
  have hd : 0<d := (mul_pos two_pos (gapScale_pos K)).trans_le hs
  have hprod := product_gap_mass (standardLaw (PathLabel l)) (energies l) (energies r)
    (measurable_energies l) (measurable_energies r) energies_scale (gapScale_pos (r+2))
  change (standardLaw (PathLabel l)).real (gapEvent l g)*gapMass r ≤ c*μ.real F at hprod
  have hleft : gapMass l≤(standardLaw (PathLabel l)).real (gapEvent l g) := by
    apply measureReal_mono
    intro x hx i j hij
    exact (gapScale_antitone (Nat.add_le_add_right hl 2)).trans (hx i j hij)
  have hF : MeasurableSet F := by
    let a (u : Fin (2^(l+2))×Fin (2^(r+2))) := fun p : (PathLabel l→ℝ)×(PathLabel r→ℝ) =>
      energies l p.1 u.1 + energies r p.2 u.2
    have h u : Measurable (a u) :=
      ((measurable_energies l _).comp measurable_fst).add ((measurable_energies r _).comp measurable_snd)
    simp only [F,setOf_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (((h u).sub (h v)).abs)
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hjoined : μ.real F*ν.real B≤gapMass (l+r+2) := by
    rw [show μ.real F*ν.real B=(μ.prod ν).real (F×ˢB) by
      simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul]]
    rw [←(extractBlocks_law l r).measureReal_preimage (hF.prod hB).nullMeasurableSet]
    apply measureReal_mono
    intro x hx i j hij
    have hcoeff t : |(extractBlocks l r x).2 t| ≤ gapScale K/20 :=
      abs_le.mpr (hx.2 t (mem_univ t))
    have hj := physical_merge_gap l r x hd hx.1 (fun t => (hcoeff t).trans (by linarith only [hs])) i j hij
    exact (show gapScale K≤d/2 by linarith only [hs]).trans hj
  calc gapMass l*gapMass r*ν.real B
        ≤ (c*μ.real F)*ν.real B := mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right hleft measureReal_nonneg).trans hprod) measureReal_nonneg
       _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hjoined hc

#print axioms balanced_merge_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
