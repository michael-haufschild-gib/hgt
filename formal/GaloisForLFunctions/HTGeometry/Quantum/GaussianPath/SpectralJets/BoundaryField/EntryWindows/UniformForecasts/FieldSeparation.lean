import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FirstReturnDates
import Mathlib.Data.Fintype.Lattice

/-! # Two field values that uniformly separate spectral gap forecasts -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows.UniformForecasts
noncomputable section

/-- Two disjoint finite lists admit a single radius such that every point
is at least that far from one entire list. -/
theorem separated_lists {I J : Type*} [Finite I] [Finite J] (f : I→ℝ) (g : J→ℝ)
    (h : ∀ i j, f i≠g j) :
    ∃ r> (0:ℝ), ∀ b : ℝ, (∀ i, r≤ |b-f i|) ∨ (∀ j, r≤ |b-g j|) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI => exact ⟨1,zero_lt_one,fun _ => Or.inl (fun i => isEmptyElim i)⟩
  | inr hI =>
    cases isEmpty_or_nonempty J with
    | inl hJ => exact ⟨1,zero_lt_one,fun _ => Or.inr (fun j => isEmptyElim j)⟩
    | inr hJ =>
      let d (p : I×J) := |f p.1-g p.2|
      obtain ⟨p,hm⟩ := Finite.exists_min d
      have hp : 0<d p := abs_pos.mpr (sub_ne_zero.mpr (h _ _))
      refine ⟨d p/2,half_pos hp,fun b => ?_⟩
      by_cases hb : ∀ i, d p/2≤ |b-f i|
      · exact Or.inl hb
      · push_neg at hb
        obtain ⟨i,hi⟩ := hb
        refine Or.inr fun j => ?_
        have ht := abs_sub_le (f i) b (g j)
        rw [abs_sub_comm (f i) b] at ht
        have hmin : d p≤ |f i-g j| := hm (i,j)
        linarith only [hmin,ht,hi]

/-- Given a baseline setting and any open interval of alternative settings,
one field value in the interval separates its entire off-diagonal gap list
from the baseline list by a positive margin. Every possible forecast gap
therefore fails by this margin at one of the same two settings. -/
theorem gaussian_two_field_gap_witnesses :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ a l u : ℝ, l<u →
      ∃ z∈Ioo l u, ∃ r> (0:ℝ), ∀ b : ℝ,
        (∀ i j, i≠j → r≤ |b-((boundaryHermitian ω k a).eigenvalues i-(boundaryHermitian ω k a).eigenvalues j)|) ∨
        (∀ i j, i≠j → r≤ |b-((boundaryHermitian ω k z).eigenvalues i-(boundaryHermitian ω k z).eigenvalues j)|) := by
  filter_upwards [gaussian_boundary_frequency_avoidance] with ω hω k a l u hlu
  let I := Fin (k+3)→Bool
  let P := {p : I×I // p.1≠p.2}
  let g (v : ℝ) (p : P) := (boundaryHermitian ω k v).eigenvalues p.val.1-
    (boundaryHermitian ω k v).eigenvalues p.val.2
  obtain ⟨B,hB,hfree⟩ := hω k (range (g a)) (countable_range _)
  obtain ⟨z,hz,hout⟩ : ∃ z∈Ioo l u, z∉B := by
    by_contra hh
    have hsub : Ioo l u⊆B := fun y hy => by
      by_contra h
      exact hh ⟨y,hy,h⟩
    have hzero := measure_mono_null hsub (hB.measure_zero volume)
    rw [Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hzero
    exact (sub_pos.mpr hlu).not_ge hzero
  have hdisjoint (i j : P) : g a i≠g z j := by
    obtain ⟨m,hm,hbal,hgap⟩ := gap_packet (boundaryHermitian ω k z).eigenvalues j.property
    exact fun he => hfree z hout m hm hbal ⟨i,he.trans hgap.symm⟩
  obtain ⟨r,hr,hb⟩ := separated_lists (g a) (g z) hdisjoint
  refine ⟨z,hz,r,hr,fun b => (hb b).imp (fun h i j hij => h ⟨(i,j),hij⟩)
    (fun h i j hij => h ⟨(i,j),hij⟩)⟩

#print axioms gaussian_two_field_gap_witnesses
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows.UniformForecasts
