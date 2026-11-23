import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.AngularMetric
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.QuantileMatching

/-! # Seventeen separated spectral points from a finite angular grid -/
open Set
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

private theorem bin_occupied {I : Type*} [Fintype I] (x : I → ℝ) {a b : ℝ}
    (hc : countBelow x a < countBelow x b) : ∃ j, x j ∈ Ico a b := by
  classical
  by_contra h
  apply hc.not_ge (Finset.card_le_card ?_)
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge fun hh => h ⟨j,hh,hj'⟩⟩

/-- A discrepancy below one quarter of one bin guarantees a point close
to each seventeenth root of unity. The selected points are separated in
chord distance even across the angular origin. -/
theorem seventeen_phases_of_cdf {I : Type*} [Fintype I] (x : I → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hc : ∀ j : Fin 17409,
      |(countBelow x (j.val/17408):ℝ)/D-j.val/17408| < 1/(4*17408)) :
    ∃ f : Fin 17 → I, ∀ i j, i ≠ j →
      (21/100:ℝ) ≤ ‖expTurns (x (f i))-expTurns (x (f j))‖ := by
  have hw (i : Fin 17) : ∃ j, x j ∈ Ico (i.val/17:ℝ) (i.val/17+1/17408) := by
    let l : Fin 17409 := ⟨i.val*1024,by have := i.isLt; omega⟩
    let r : Fin 17409 := ⟨i.val*1024+1,by have := i.isLt; omega⟩
    have hl : (l.val:ℝ)/17408=i.val/17 := by dsimp only [l]; push_cast; ring
    have hr : (r.val:ℝ)/17408=i.val/17+1/17408 := by dsimp only [r]; push_cast; ring
    have h₁ := (abs_lt.mp (hc l)).2
    have h₂ := (abs_lt.mp (hc r)).1
    rw [hl] at h₁
    rw [hr] at h₂
    apply bin_occupied x
    by_contra! h
    have hd := div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr h) hD
    linarith only [h₁,h₂,hd]
  choose f hf using hw
  let z (i : Fin 17) := expTurns (x (f i))
  let v (i : Fin 17) := expTurns (i.val/17)
  have hclose (i : Fin 17) : ‖z i-v i‖ ≤ 8/17408 := by
    have h := hf i
    have he : |x (f i)-i.val/17| ≤ 1/17408 := by rw [abs_of_nonneg (sub_nonneg.mpr h.1)]; linarith only [h.2]
    exact (expTurns_lip ..).trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans (by linarith only [Real.pi_lt_four]))
  refine ⟨f,?_⟩
  intro i j hij
  have h := root_separation i j hij
  have h₁ := norm_sub_le_norm_sub_add_norm_sub (v i) (z i) (v j)
  have h₂ := norm_sub_le_norm_sub_add_norm_sub (z i) (z j) (v j)
  rw [norm_sub_rev (v i) (z i)] at h₁
  change (4:ℝ)/17 ≤ ‖v i-v j‖ at h
  change (21/100:ℝ) ≤ ‖z i-z j‖
  linarith only [h,h₁,h₂,hclose i,hclose j]

#print axioms seventeen_phases_of_cdf
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
