import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.PathIntervals

/-! # Long-window occupation supplied by disjoint product intervals -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section
open SharpOccupation EmptyVisitFlux

/-- A continuous entry flux L yields eventual occupation at least hL/4
after adding one product step of duration up to h to every entry. -/
theorem product_fraction_of_flux {n : ℕ} (u : PathShell n) {δ h ε : ℝ}
    (hδ : 0<δ) (hs : δ<sqrt 2) (hh : 0≤h) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let E := fun j => -H.2.isHermitian.eigenvalues j
    let M := ∑ l : PathLabel n, |u l|
    let J := Fintype.card (PathLabel n)
    let x := physicalArc δ
    let rate := x^(2^(n+2)-2:ℕ)*pairTurnRate E
    MaximallyProjectiveEnergy E → 0<rate → h*(M/π) ≤ 1-2*x → δ+M^2*h^2 ≤ ε →
      ∀ᶠ T : ℝ in atTop, h*rate/4 ≤ visitFraction H J ε 0 T := by
  intro H E M J x rate hi hrate hgap herror
  have hx := (physicalArc_spec hδ hs).1
  have hd : Fintype.card (Fin (n+2) → Bool) = 2^(n+2) := by simp
  have hcount := entry_count_rate E hi hx.1 hx.2
  rw [hd] at hcount
  obtain ⟨A,hA⟩ := eventually_atTop.mp (hcount.eventually_const_lt (half_lt_self hrate))
  filter_upwards [eventually_ge_atTop (max A 0+2*h+1)] with T hT
  have hta : A ≤ T-h := by linarith only [hT,le_max_left A 0,hh]
  have hth : 0<T-h := by linarith only [hT,le_max_right A 0,hh]
  have ht : 0<T := by linarith only [hth,hh]
  have hhalf : T/2≤T-h := by linarith only [hT,le_max_right A 0]
  have hc := (lt_div_iff₀ hth).mp (hA _ hta)
  have hpack := path_entry_intervals u hδ hs hh (T-h) hgap
  rw [sub_add_cancel] at hpack
  have hsub : visitSet H J (δ+M^2*h^2) ∩ Icc 0 T ⊆ visitSet H J ε ∩ Icc 0 T := by
    apply inter_subset_inter_left
    rintro t ⟨z,hz,C,hC,he⟩
    exact ⟨z,hz,C,hC,he.trans herror⟩
  have hle := measureReal_mono (μ := volume) hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  change h*rate/4 ≤ _/(T-0)
  rw [sub_zero,le_div_iff₀ ht]
  calc
    _ = rate/2*(T/2)*h := by ring
    _ ≤ rate/2*(T-h)*h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf (half_pos hrate).le) hh
    _ ≤ _ := ((mul_le_mul_of_nonneg_right hc.le hh).trans hpack).trans hle

#print axioms product_fraction_of_flux
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
