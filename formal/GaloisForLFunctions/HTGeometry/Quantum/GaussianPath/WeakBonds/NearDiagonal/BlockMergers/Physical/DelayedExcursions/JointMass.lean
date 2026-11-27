import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.DelayedExcursions.CappedBlocks

/-! # Gaussian mass of two affordable blocks with a separated joint spectrum -/
open Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- Dilation and the nine independent joining coefficients have a price
independent of further scale-invariant conditions on either child. -/
private theorem seam_price : ∃ ρ ∈ Ioc (0:ℝ) 1, ∀ l r : ℕ, ∀ z ∈ Ioc (0:ℝ) 1,
    let c := (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))
    ρ^(l+r+4)*z^9*c ≤ (standardLaw (Fin 3×Fin 3)).real (seamBox (gapScale (l+r+4)/20*z)) := by
  obtain ⟨ρ,hρ,h⟩ := priced_join_mass
  obtain ⟨C,_,hg⟩ := hierarchical_gap_mass
  have hp (n : ℕ) : 0 < gapMass n := (exp_pos _).trans_le (hg n)
  refine ⟨ρ,hρ,?_⟩
  intro l r z hz c
  let b := (standardLaw (Fin 3×Fin 3)).real (seamBox (gapScale (l+r+4)/20*z))
  let a := gapMass l*gapMass r
  have ha : 0 < a := mul_pos (hp l) (hp r)
  have hc : 0 < c := mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (by positivity)
  have h' := h l r z hz (a*b/c) (div_nonneg (mul_nonneg ha.le measureReal_nonneg) hc.le)
    (by change a*b ≤ c*(a*b/c); exact le_of_eq (by field_simp))
  have hh := (le_div_iff₀ hc).mp h'
  apply le_of_mul_le_mul_left (a:=a) _ ha
  calc a*(ρ^(l+r+4)*z^9*c) = (ρ^(l+r+4)*gapMass l*gapMass r*z^9)*c := by dsimp only [a]; ring
       _ ≤ a*b := hh

/-- Both blocks keep their own all-time gate caps and every pair of
sum levels stays separated. The joining coefficients occupy an independent box. -/
def joinedCaps (l r : ℕ) (ε δ : ℝ) : Set (PathLabel (l+r+2)→ℝ) :=
  extractBlocks l r ⁻¹' (((capEvent l ε ×ˢ capEvent r ε) ∩
    productEvent l r (2*gapScale (l+r+4))) ×ˢ seamBox δ)

theorem measurable_joinedCaps (l r : ℕ) (ε δ : ℝ) : MeasurableSet (joinedCaps l r ε δ) :=
  ((((measurable_capEvent l ε).prod (measurable_capEvent r ε)).inter (measurable_productEvent ..)).prod
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc)).preimage (extractBlocks_law l r).measurable

theorem joined_caps_mass : ∃ ρ ∈ Ioc (0:ℝ) 1, ∀ l r : ℕ, l ≤ r → r ≤ l+1 → ∀ ε : ℝ, ∀ z ∈ Ioc (0:ℝ) 1,
    ρ^(l+r+4)*z^9*(standardLaw (PathLabel l)).real (separatedCap l ε)*
      (standardLaw (PathLabel r)).real (separatedCap r ε) ≤
      (standardLaw (PathLabel (l+r+2))).real (joinedCaps l r ε (gapScale (l+r+4)/20*z)) := by
  obtain ⟨ρ,hρ,h⟩ := seam_price
  refine ⟨ρ,hρ,?_⟩
  intro l r hl hr ε z hz
  let F := (capEvent l ε ×ˢ capEvent r ε) ∩ productEvent l r (2*gapScale (l+r+4))
  let B := seamBox (gapScale (l+r+4)/20*z)
  let μ := (standardLaw (PathLabel l)).prod (standardLaw (PathLabel r))
  let ν := standardLaw (Fin 3×Fin 3)
  let a := ρ^(l+r+4)*z^9
  let c := (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))
  have hF : MeasurableSet F := ((measurable_capEvent l ε).prod (measurable_capEvent r ε)).inter (measurable_productEvent l r _)
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  change _ ≤ (standardLaw _).real (extractBlocks l r ⁻¹' (F×ˢB))
  rw [(extractBlocks_law l r).measureReal_preimage (hF.prod hB).nullMeasurableSet]
  have he : (μ.prod ν).real (F×ˢB)=μ.real F*ν.real B := by
    simp only [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul]
  rw [he,mul_assoc]
  calc _ ≤ a*(c*μ.real F) := mul_le_mul_of_nonneg_left (capped_product_mass l r hl hr ε)
                                 (mul_nonneg (pow_nonneg hρ.1.le _) (pow_nonneg hz.1.le _))
       _ = μ.real F*(a*c) := by ring
       _ ≤ μ.real F*ν.real B := mul_le_mul_of_nonneg_left (h l r z hz) measureReal_nonneg

#print axioms joined_caps_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
