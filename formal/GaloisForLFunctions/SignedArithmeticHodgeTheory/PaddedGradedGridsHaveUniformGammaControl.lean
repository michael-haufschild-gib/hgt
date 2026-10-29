import GaloisForLFunctions.SignedArithmeticHodgeTheory.GradedIntervalAveragesHaveUniformGammaControl

/-!
# Zero-padded graded grids preserve homogeneous Gamma control

Consecutive width ratios control every separated pair through its intervening
neighbors. Zero means on the first and last cells remove the exposed boundary
rows. The remaining exterior rows have the width-scale gap required by the
uniform averaged-kernel comparison.
-/

noncomputable section
open MeasureTheory Set Filter
open RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open ArithmeticCastelnuovoSeveri.IntervalVariance
open HTGeometry

private theorem outside_interval_chain (L : ℕ → ℝ) (N : ℕ) (y : ℝ)
    (hne : ∀ k, y ≠ L k) (hout : ∀ k < N, y ∉ Ioo (L k) (L (k + 1))) :
    y < L 0 ∨ L N < y := by
  induction N with
  | zero => exact lt_or_gt_of_ne (hne 0)
  | succ N ih =>
    rcases ih (fun k hk => hout k (by omega)) with hl | hr
    · exact Or.inl hl
    · right
      by_contra h
      have hy : y < L (N + 1) := lt_of_le_of_ne (le_of_not_gt h) (hne (N + 1))
      exact hout N (by omega) ⟨hr, hy⟩

/-- The complement of a finite interval chain is its two exterior half-lines up to null endpoints. -/
theorem ae_exterior_finite_interval_chain (L : ℕ → ℝ) (N : ℕ) :
    ∀ᵐ y ∂volume.restrict (⋃ i : Fin N, Ioo (L i) (L ((i : ℕ) + 1)))ᶜ,
      y < L 0 ∨ L N < y := by
  have hne : ∀ᵐ y ∂volume, ∀ k : ℕ, y ≠ L k :=
    ae_all_iff.mpr fun k => Measure.ae_ne volume (L k)
  have hF : MeasurableSet (⋃ i : Fin N, Ioo (L i) (L ((i : ℕ) + 1)))ᶜ :=
    (MeasurableSet.iUnion fun _ => measurableSet_Ioo).compl
  filter_upwards [ae_restrict_mem hF, ae_restrict_of_ae hne] with y hy hny
  exact outside_interval_chain L N y hny fun k hk hi =>
    hy (mem_iUnion.mpr ⟨⟨k, hk⟩, hi⟩)

/-- A finite graded grid with zero boundary means has a uniform Gamma averaging bound. -/
theorem levyEnergy_padded_grid_average_le (L : ℕ → ℝ) (N : ℕ)
    (hN : 2 ≤ N) (hL : StrictMono L)
    (hw : ∀ k, L (k + 1) - L k ≤ 1)
    (hadj : ∀ k, L (k + 1) - L k ≤ 3 * (L (k + 2) - L (k + 1)) ∧
      L (k + 2) - L (k + 1) ≤ 3 * (L (k + 1) - L k))
    (f g : ℝ → ℝ)
    (hfv : BoundedVariationOn f univ) (hfc : HasCompactSupport f)
    (hgv : BoundedVariationOn g univ) (hgc : HasCompactSupport g)
    (hg : ∀ k < N, ∀ x ∈ Ioo (L k) (L (k + 1)),
      g x = intervalMean (L k) (L (k + 1)) f)
    (hfz : ∀ y, y < L 0 ∨ L N < y → f y = 0)
    (hgz : ∀ y, y < L 0 ∨ L N < y → g y = 0)
    (hfirst : intervalMean (L 0) (L 1) f = 0)
    (hlast : intervalMean (L (N - 1)) (L N) f = 0) :
    levyEnergy g ≤ stoppingGammaKernelConstant * levyEnergy f := by
  have hsep (i j : Fin N) (hij : i ≠ j) :
      L ((i : ℕ) + 1) ≤ L j ∨ L ((j : ℕ) + 1) ≤ L i := by
    have hn : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inl (hL.monotone (by omega))
    · exact Or.inr (hL.monotone (by omega))
  have htouch (i j : Fin N) (h : L ((i : ℕ) + 1) = L j) :
      L ((i : ℕ) + 1) - L i ≤ 3 * (L ((j : ℕ) + 1) - L j) ∧
        L ((j : ℕ) + 1) - L j ≤ 3 * (L ((i : ℕ) + 1) - L i) := by
    have he : (i : ℕ) + 1 = (j : ℕ) := hL.injective h
    rw [← he]
    exact hadj i
  have hgap (i j : Fin N) (h : L ((i : ℕ) + 1) < L j) :
      L ((i : ℕ) + 1) - L i ≤ 3 * (L j - L ((i : ℕ) + 1)) ∧
        L ((j : ℕ) + 1) - L j ≤ 3 * (L j - L ((i : ℕ) + 1)) := by
    have hij : (i : ℕ) + 1 < (j : ℕ) := by
      by_contra hn
      exact (not_lt_of_ge (hL.monotone (by omega : (j : ℕ) ≤ (i : ℕ) + 1))) h
    have hleft := hL.monotone (show (i : ℕ) + 2 ≤ (j : ℕ) by omega)
    have hright := hL.monotone (show (i : ℕ) + 1 ≤ (j : ℕ) - 1 by omega)
    have ha := (hadj (i : ℕ)).1
    have hb := (hadj ((j : ℕ) - 1)).2
    rw [show (j : ℕ) - 1 + 1 = (j : ℕ) by omega,
      show (j : ℕ) - 1 + 2 = (j : ℕ) + 1 by omega] at hb
    constructor <;> linarith only [hleft, hright, ha, hb]
  have hext (i : Fin N) (hi : intervalMean (L i) (L ((i : ℕ) + 1)) f ≠ 0) :
      ∀ᵐ y ∂volume.restrict (⋃ i : Fin N, Ioo (L i) (L ((i : ℕ) + 1)))ᶜ,
        L ((i : ℕ) + 1) + (L ((i : ℕ) + 1) - L i) / 3 ≤ y ∨
          y + (L ((i : ℕ) + 1) - L i) / 3 ≤ L i := by
    have hi0 : 0 < (i : ℕ) := by
      by_contra hn
      have he : (i : ℕ) = 0 := by omega
      exact hi (by simpa only [he, Nat.zero_add] using hfirst)
    have hiN : (i : ℕ) + 1 < N := by
      by_contra hn
      have he : (i : ℕ) = N - 1 := by have := i.isLt; omega
      exact hi (by simpa only [he, Nat.sub_add_cancel (by omega : 1 ≤ N)] using hlast)
    have hl := hL.monotone (show 0 ≤ (i : ℕ) - 1 from Nat.zero_le _)
    have hr := hL.monotone (show (i : ℕ) + 2 ≤ N by omega)
    have ha := (hadj ((i : ℕ) - 1)).2
    have hb := (hadj (i : ℕ)).1
    rw [show (i : ℕ) - 1 + 1 = (i : ℕ) by omega,
      show (i : ℕ) - 1 + 2 = (i : ℕ) + 1 by omega] at ha
    filter_upwards [ae_exterior_finite_interval_chain L N] with y hy
    rcases hy with hy | hy
    · right
      linarith only [hl, ha, hy]
    · left
      linarith only [hr, hb, hy]
  exact levyEnergy_interval_average_le (fun i : Fin N => L i)
    (fun i : Fin N => L ((i : ℕ) + 1)) f g
    (fun i => hL (by omega)) (fun i => hw i) hsep htouch hgap
    hfv hfc hgv hgc (fun i x hx => hg i i.isLt x hx)
    ((ae_exterior_finite_interval_chain L N).mono fun y hy => hfz y hy)
    ((ae_exterior_finite_interval_chain L N).mono fun y hy => hgz y hy) hext

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.levyEnergy_padded_grid_average_le
