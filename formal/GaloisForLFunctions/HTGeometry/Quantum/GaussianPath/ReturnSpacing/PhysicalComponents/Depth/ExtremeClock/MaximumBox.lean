import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.ClockCell

/-! # The exact transverse box of maximum-duration scalar visits -/
open Set
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
noncomputable section

/-- A cell fills the whole possible visit interval exactly when each
centered spectator phase fits the narrower of its two endpoint margins. -/
theorem maximal_offsets_iff {I : Type*} (θ : I→ℝ) (p q : I) (hp : θ p=1) (hq : θ q=0)
    (n : ℤ) {r : ℝ} (hr : 0≤r) :
    offsets θ n r = Icc (-r) r ↔
      ∀ i, |residual (n*θ i)| ≤ r*min (θ i) (1-θ i) := by
  let y (i : I) := residual (n*θ i)
  have yp : y p=0 := by simp only [y,hp,mul_one,residual_int]
  have yq : y q=0 := by
    simpa only [y,hq,mul_zero,Int.cast_zero] using residual_int 0
  have hr' : -r≤r := (neg_nonpos.mpr hr).trans hr
  constructor
  · intro he i
    have h₁ : r∈offsets θ n r := he.symm ▸ right_mem_Icc.mpr hr'
    have h₂ : -r∈offsets θ n r := he.symm ▸ left_mem_Icc.mpr hr'
    change ∀ i j, y i+r*θ i-(y j+r*θ j)≤r at h₁
    change ∀ i j, y i+ -r*θ i-(y j+ -r*θ j)≤r at h₂
    have a := h₁ p i
    have b := h₁ i q
    have c := h₂ q i
    have d := h₂ i p
    simp only [yp,yq,hp,hq,mul_zero,mul_one,zero_add,sub_zero,zero_sub,neg_mul] at a b c d
    rw [mul_min_of_nonneg _ _ hr]
    exact le_min (abs_le.mpr ⟨by linarith only [a],by linarith only [d]⟩)
      (abs_le.mpr ⟨by linarith only [c],by linarith only [b]⟩)
  · intro hx
    apply Subset.antisymm (offsets_bound hp hq n r)
    intro z hz i j
    have bounds (k : I) : |y k|≤r*θ k ∧ |y k|≤r*(1-θ k) :=
      ⟨(hx k).trans (mul_le_mul_of_nonneg_left (min_le_left ..) hr),
        (hx k).trans (mul_le_mul_of_nonneg_left (min_le_right ..) hr)⟩
    obtain ⟨a,b⟩ := abs_le.mp (bounds i).1
    obtain ⟨c,d⟩ := abs_le.mp (bounds i).2
    obtain ⟨e,f⟩ := abs_le.mp (bounds j).1
    obtain ⟨g,h⟩ := abs_le.mp (bounds j).2
    change y i+z*θ i-(y j+z*θ j)≤r
    rcases le_total (θ j) (θ i) with hs|hs
    · linarith only [d,e,mul_le_mul_of_nonneg_right hz.2 (sub_nonneg.mpr hs)]
    · linarith only [b,g,mul_le_mul_of_nonpos_right hz.1 (sub_nonpos.mpr hs)]

#print axioms maximal_offsets_iff
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
