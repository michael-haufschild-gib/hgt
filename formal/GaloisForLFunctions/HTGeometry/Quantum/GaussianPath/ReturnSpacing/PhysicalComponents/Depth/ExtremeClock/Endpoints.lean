import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.ClockCell

/-! # Explicit lower and upper offsets of each physical return cell -/
open Finset Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
noncomputable section
variable {I : Type*} [Fintype I]

def rising (θ : I→ℝ) : Finset (I×I) := univ.filter fun p => θ p.2 < θ p.1

def lower (θ : I→ℝ) (h : (rising θ).Nonempty) (n : ℤ) (r : ℝ) :=
  (rising θ).sup' h fun p => (residual (n*θ p.2)-residual (n*θ p.1)-r)/(θ p.1-θ p.2)

def upper (θ : I→ℝ) (h : (rising θ).Nonempty) (n : ℤ) (r : ℝ) :=
  (rising θ).inf' h fun p => (residual (n*θ p.2)-residual (n*θ p.1)+r)/(θ p.1-θ p.2)

/-- The exact physical offsets require only two finite extrema over the
distinct slopes. Repeated slopes give identical residues on this clock. -/
theorem offsets_eq_Icc (θ : I→ℝ) (h : (rising θ).Nonempty) (n : ℤ) {r : ℝ} (hr : 0≤r) :
    offsets θ n r=Icc (lower θ h n r) (upper θ h n r) := by
  let y (i : I) := residual (n*θ i)
  let lo (p : I×I) := (y p.2-y p.1-r)/(θ p.1-θ p.2)
  let hi (p : I×I) := (y p.2-y p.1+r)/(θ p.1-θ p.2)
  have pos (p : I×I) (hp : p∈rising θ) : 0 < θ p.1-θ p.2 := sub_pos.mpr (mem_filter.mp hp).2
  ext z
  constructor
  · intro hz
    constructor
    · apply sup'_le
      intro p hp
      apply (div_le_iff₀ (pos p hp)).mpr
      have hh := hz p.2 p.1
      change y p.2+z*θ p.2-(y p.1+z*θ p.1)≤r at hh
      linarith only [hh]
    · apply le_inf'
      intro p hp
      apply (le_div_iff₀ (pos p hp)).mpr
      have hh := hz p.1 p.2
      change y p.1+z*θ p.1-(y p.2+z*θ p.2)≤r at hh
      linarith only [hh]
  · intro hz i j
    change y i+z*θ i-(y j+z*θ j)≤r
    rcases lt_trichotomy (θ i) (θ j) with hl|he|hg
    · have hp : (j,i)∈rising θ := mem_filter.mpr ⟨mem_univ _,hl⟩
      have hh := (div_le_iff₀ (pos _ hp)).mp ((le_sup' lo hp).trans hz.1)
      change y i-y j-r≤z*(θ j-θ i) at hh
      linarith only [hh]
    · simp only [y,he,sub_self,hr]
    · have hp : (i,j)∈rising θ := mem_filter.mpr ⟨mem_univ _,hg⟩
      have hh := (le_div_iff₀ (pos _ hp)).mp (hz.2.trans (inf'_le hi hp))
      change z*(θ i-θ j)≤y j-y i+r at hh
      linarith only [hh]

end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
