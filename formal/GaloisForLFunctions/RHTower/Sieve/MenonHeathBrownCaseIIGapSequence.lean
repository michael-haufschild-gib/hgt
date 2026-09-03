import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIColoring

/-!
# Receiver-ready ordinate sequence for one Menon Case-II color

On one color fibre every selected perturbation lies in the same frequency cell.  Replacing all
off-fibre perturbations by that cell's lower endpoint gives a globally defined sequence.  A base
gap of `2 * Δ` then leaves an exact gap of `Δ`, while every on-fibre ordinate remains the literal
Perron-selected ordinate.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Set

/-- Fibre of a finite Case-II coloring over the original finite set. -/
def menonHeathBrownCaseIIColorFibre
    {L X cells : ℕ} (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (label : MenonHeathBrownCaseIILabel L X cells) : Finset ℕ :=
  S.filter fun r => color r = label

/-- Selected within-cell perturbation on the fibre, continued by the fixed lower cell endpoint. -/
def menonHeathBrownCaseIIFibrePerturbation
    {L X cells : ℕ} (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (selectedY : ℕ → ℝ) (V Δ : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) (r : ℕ) : ℝ :=
  if r ∈ menonHeathBrownCaseIIColorFibre S color label then selectedY r
  else -V + (label.cell : ℝ) * Δ

/-- Globally defined receiver ordinate attached to one fixed color. -/
def menonHeathBrownCaseIISelectedOrdinate
    {L X cells : ℕ} (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (selectedY : ℕ → ℝ) (tau : ℕ → ℝ) (V Δ : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) (r : ℕ) : ℝ :=
  tau r + menonHeathBrownCaseIIFibrePerturbation
    S color selectedY V Δ label r

/-- Core amplitude obtained after paying the exact box-cardinality and degree-three scalar cost. -/
def menonHeathBrownCaseIICoreThreshold (L X : ℕ) (Q : ℝ) : ℝ :=
  Q / ((Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8)

/-- The continued perturbation stays in the fixed color's literal cell at every index. -/
theorem menonHeathBrownCaseIIFibrePerturbation_mem_cell
    {L X a cells : ℕ} {T0 t sigma V Δ Q : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hΔ : 0 < Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (label : MenonHeathBrownCaseIILabel L X cells) (r : ℕ) :
    menonHeathBrownCaseIIFibrePerturbation S color selectedY V Δ label r ∈
      Set.Icc (-V + (label.cell : ℝ) * Δ)
        (-V + ((label.cell : ℝ) + 1) * Δ) := by
  by_cases hr : r ∈ menonHeathBrownCaseIIColorFibre S color label
  · rw [menonHeathBrownCaseIIFibrePerturbation, if_pos hr]
    have hmem := Finset.mem_filter.mp hr
    have hselected := hselection r hmem.1
    rw [hmem.2] at hselected
    exact hselected.1
  · rw [menonHeathBrownCaseIIFibrePerturbation, if_neg hr]
    constructor
    · exact le_rfl
    · nlinarith

/-- A `2Δ`-spaced base sequence remains globally `Δ`-spaced after fixed-cell perturbation. -/
theorem menonHeathBrownCaseIISelectedOrdinate_gap
    {L X a cells : ℕ} {T0 t sigma V Δ Q : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hΔ : 0 < Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hbase : ∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1))
    (label : MenonHeathBrownCaseIILabel L X cells) :
    ∀ r : ℕ,
      menonHeathBrownCaseIISelectedOrdinate S color selectedY tau V Δ label r + Δ ≤
        menonHeathBrownCaseIISelectedOrdinate S color selectedY tau V Δ label (r + 1) := by
  intro r
  have hr := menonHeathBrownCaseIIFibrePerturbation_mem_cell
    hΔ hselection label r
  have hrnext := menonHeathBrownCaseIIFibrePerturbation_mem_cell
    hΔ hselection label (r + 1)
  have hrUpper :
      menonHeathBrownCaseIIFibrePerturbation S color selectedY V Δ label r ≤
        -V + (label.cell : ℝ) * Δ + Δ := by
    calc
      menonHeathBrownCaseIIFibrePerturbation S color selectedY V Δ label r ≤
          -V + ((label.cell : ℝ) + 1) * Δ := hr.2
      _ = -V + (label.cell : ℝ) * Δ + Δ := by ring
  dsimp only [menonHeathBrownCaseIISelectedOrdinate]
  linarith [hbase r, hrnext.1]

/-- The fixed grid cell, hence every continued perturbation, lies in `[-V,V]`. -/
theorem menonHeathBrownCaseIIFibrePerturbation_mem_symmetric
    {L X a cells : ℕ} {T0 t sigma V Δ Q : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hΔ : 0 < Δ) (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (label : MenonHeathBrownCaseIILabel L X cells) (r : ℕ) :
    menonHeathBrownCaseIIFibrePerturbation S color selectedY V Δ label r ∈
      Set.Icc (-V) V := by
  have hr := menonHeathBrownCaseIIFibrePerturbation_mem_cell
    hΔ hselection label r
  have hcell0 : (0 : ℝ) ≤ (label.cell : ℝ) := by positivity
  have hcellTop : ((label.cell : ℕ) + 1 : ℝ) ≤ (cells : ℝ) := by
    exact_mod_cast label.cell.isLt
  constructor
  · exact hr.1.trans' (by nlinarith)
  · calc
      menonHeathBrownCaseIIFibrePerturbation S color selectedY V Δ label r ≤
          -V + ((label.cell : ℝ) + 1) * Δ := hr.2
      _ ≤ -V + (cells : ℝ) * Δ := by
        gcongr
      _ = V := by linarith

/-- A base band narrowed by the perturbation radius becomes the exact receiver band. -/
theorem menonHeathBrownCaseIISelectedOrdinate_mem_band
    {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hΔ : 0 < Δ) (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hbaseBand : ∀ r : ℕ, T + V ≤ tau r ∧ tau r ≤ 2 * T - V)
    (label : MenonHeathBrownCaseIILabel L X cells) (r : ℕ) :
    T ≤ menonHeathBrownCaseIISelectedOrdinate
        S color selectedY tau V Δ label r ∧
      menonHeathBrownCaseIISelectedOrdinate
        S color selectedY tau V Δ label r ≤ 2 * T := by
  have hperturb := menonHeathBrownCaseIIFibrePerturbation_mem_symmetric
    hΔ hgrid hselection label r
  rw [Set.mem_Icc] at hperturb
  dsimp only [menonHeathBrownCaseIISelectedOrdinate]
  constructor <;> linarith [(hbaseBand r).1, (hbaseBand r).2]

/-- On its color fibre, the continued sequence is exactly the selected Perron ordinate. -/
theorem menonHeathBrownCaseIISelectedOrdinate_eq_on_fibre
    {L X cells : ℕ} {S : Finset ℕ}
    {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ} {V Δ : ℝ}
    {label : MenonHeathBrownCaseIILabel L X cells} {r : ℕ}
    (hr : r ∈ menonHeathBrownCaseIIColorFibre S color label) :
    menonHeathBrownCaseIISelectedOrdinate S color selectedY tau V Δ label r =
      tau r + selectedY r := by
  rw [menonHeathBrownCaseIISelectedOrdinate,
    menonHeathBrownCaseIIFibrePerturbation, if_pos hr]

/-- Every member of a color fibre retains the complete pointwise selection certificate. -/
theorem isMenonHeathBrownCaseIISelection_on_colorFibre
    {L X a cells : ℕ} {T0 t sigma V Δ Q : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (label : MenonHeathBrownCaseIILabel L X cells)
    {r : ℕ} (hr : r ∈ menonHeathBrownCaseIIColorFibre S color label) :
    IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
      (selectedY r) label := by
  have hmem := Finset.mem_filter.mp hr
  simpa only [hmem.2] using hselection r hmem.1

/-- On one color fibre, the selected core exceeds the exact normalized threshold at the globally
continued receiver ordinate. -/
theorem menonHeathBrownCaseIICoreThreshold_le_on_colorFibre
    {L X a cells : ℕ} {T0 t sigma V Δ Q : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (label : MenonHeathBrownCaseIILabel L X cells)
    {r : ℕ} (hr : r ∈ menonHeathBrownCaseIIColorFibre S color label) :
    menonHeathBrownCaseIICoreThreshold L X Q ≤
      ‖heathBrownDyadicCoreProduct L X 3 label.box.m
        label.box.a label.box.b label.box.q
        ((sigma : ℂ) +
          (menonHeathBrownCaseIISelectedOrdinate
            S color selectedY tau V Δ label r : ℝ) * Complex.I)‖ := by
  have hselected := isMenonHeathBrownCaseIISelection_on_colorFibre
    hselection label hr
  have hcardNat : 0 < Fintype.card (HeathBrownBoxChoice L X 3) :=
    Fintype.card_pos_iff.mpr (nonempty_heathBrownBoxChoice L X 3 (by norm_num))
  have hcost : 0 < (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 := by
    positivity
  rw [menonHeathBrownCaseIICoreThreshold, div_le_iff₀ hcost]
  rw [menonHeathBrownCaseIISelectedOrdinate_eq_on_fibre hr]
  simpa only [add_comm, mul_assoc, mul_comm, mul_left_comm] using
    hselected.2.2.2.1

end RHTower.Sieve
