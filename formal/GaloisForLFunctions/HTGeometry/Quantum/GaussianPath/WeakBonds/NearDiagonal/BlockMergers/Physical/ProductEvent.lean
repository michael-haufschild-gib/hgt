import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.SeedMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.ProductMass

/-! # Retained product gaps and independent restrictions on the joining bond -/
open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

def gapMass (n : ℕ) := (standardLaw (PathLabel n)).real (gapEvent n (gapScale (n+2)))

/-- The nine joining coefficients can be restricted independently of both blocks. -/
def seamBox (δ : ℝ) : Set (Fin 3×Fin 3→ℝ) := univ.pi fun _ => Icc (-δ) δ

/-- All paired energies of the two independent child Hamiltonians are separated by g. -/
def productEvent (l r : ℕ) (g : ℝ) : Set ((PathLabel l→ℝ)×(PathLabel r→ℝ)) :=
  {p | ∀ u v : Fin (2^(l+2))×Fin (2^(r+2)), u≠v →
    g≤|(energies l p.1 u.1+energies r p.2 u.2)-(energies l p.1 v.1+energies r p.2 v.2)|}

theorem measurable_productEvent (l r : ℕ) (g : ℝ) : MeasurableSet (productEvent l r g) := by
  let a (u : Fin (2^(l+2))×Fin (2^(r+2))) := fun p : (PathLabel l→ℝ)×(PathLabel r→ℝ) =>
    energies l p.1 u.1 + energies r p.2 u.2
  have h u : Measurable (a u) :=
    ((measurable_energies l _).comp measurable_fst).add ((measurable_energies r _).comp measurable_snd)
  simp only [productEvent,setOf_forall]
  exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (((h u).sub (h v)).abs)

theorem retained_product_mass (l r : ℕ) (hl : l≤r) (hr : r≤l+1) :
    let μ := (standardLaw (PathLabel l)).prod (standardLaw (PathLabel r))
    gapMass l*gapMass r ≤ (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))*
      μ.real (productEvent l r (2*gapScale (l+r+4))) := by
  intro μ
  let g := gapScale (r+2)
  let d := g/(8*(gridCount l r:ℝ))
  let c := (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))
  have hc : 0≤c := by dsimp only [c]; positivity
  have h := product_gap_mass (standardLaw (PathLabel l)) (energies l) (energies r)
    (measurable_energies l) (measurable_energies r) energies_scale (gapScale_pos (r+2))
  change (standardLaw (PathLabel l)).real (gapEvent l g)*gapMass r ≤ c*μ.real (productEvent l r d) at h
  have hleft : gapMass l≤(standardLaw (PathLabel l)).real (gapEvent l g) := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx i j hij
    exact (gapScale_antitone (Nat.add_le_add_right hl 2)).trans (hx i j hij)
  have hsub : productEvent l r d ⊆ productEvent l r (2*gapScale (l+r+4)) :=
    fun _ hx i j hij => (parent_spacing l r hr).trans (hx i j hij)
  exact ((mul_le_mul_of_nonneg_right hleft measureReal_nonneg).trans h).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hc)

/-- Transfer a product lower bound into any full-chain event forced by
the retained product spacing and the independently restricted joining bond. -/
theorem joined_event_mass (l r : ℕ) (hl : l≤r) (hr : r≤l+1) (δ : ℝ) (E : Set (PathLabel (l+r+2)→ℝ))
    (he : ∀ x, (extractBlocks l r x).1∈productEvent l r (2*gapScale (l+r+4)) →
      (extractBlocks l r x).2∈seamBox δ → x∈E) :
    gapMass l*gapMass r*(standardLaw (Fin 3×Fin 3)).real (seamBox δ) ≤
      (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))*(standardLaw (PathLabel (l+r+2))).real E := by
  let μ := (standardLaw (PathLabel l)).prod (standardLaw (PathLabel r))
  let ν := standardLaw (Fin 3×Fin 3)
  let F := productEvent l r (2*gapScale (l+r+4))
  let B := seamBox δ
  let c := (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))
  have hc : 0≤c := by dsimp only [c]; positivity
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hjoined : μ.real F*ν.real B≤(standardLaw (PathLabel (l+r+2))).real E := by
    rw [show μ.real F*ν.real B=(μ.prod ν).real (F×ˢB) by
      simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul]]
    rw [←(extractBlocks_law l r).measureReal_preimage ((measurable_productEvent ..).prod hB).nullMeasurableSet]
    exact measureReal_mono (fun x hx => he x hx.1 hx.2)
  calc gapMass l*gapMass r*ν.real B ≤ (c*μ.real F)*ν.real B :=
         mul_le_mul_of_nonneg_right (retained_product_mass l r hl hr) measureReal_nonneg
       _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hjoined hc

#print axioms joined_event_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
