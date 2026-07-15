import GaloisForLFunctions.HTGeometry.MagnitudeAtomBounds
import GaloisForLFunctions.HTGeometry.MagnitudePolynomialExponentialDomination

/-!
# Quantitative bounds for balanced witness atoms

The balanced source tuple `q + δ` has valuation at most `D * b (q + max δ)`.  Past a fixed
threshold, one further superlacunary step dominates that whole valuation.  These are the upper
bounds used to localize the nonzero-weight valuation minimizer.
-/

open Filter Finset

namespace GaloisForLFunctions

noncomputable section

def magnitudeOffsetMax {D : ℕ} (δ : Fin D → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin D)).sup δ

theorem offset_le_magnitudeOffsetMax {D : ℕ} (δ : Fin D → ℕ) (i : Fin D) :
    δ i ≤ magnitudeOffsetMax δ :=
  Finset.le_sup (f := δ) (Finset.mem_univ i)

/-- A ratio-divergent eventually positive sequence is strictly increasing on a tail. -/
theorem exists_eventually_strictMono {b : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) :
    ∃ N : ℕ, ∀ p q, N ≤ p → p < q → b p < b q := by
  obtain ⟨Nm, hmono⟩ := exists_eventually_monotone hpos hratio
  obtain ⟨Ni, hinc⟩ :=
    Filter.eventually_atTop.mp (increments_ratio_tendsto_atTop hpos hratio).1
  refine ⟨max Nm Ni, fun p q hp hpq => ?_⟩
  have hNm : Nm ≤ p := (le_max_left _ _).trans hp
  have hNi : Ni ≤ p := (le_max_right _ _).trans hp
  have hstep : b p < b (p + 1) := by
    have := hinc p hNi
    linarith
  have htail : b (p + 1) ≤ b q :=
    hmono (p + 1) q (by omega) (Nat.succ_le_iff.mpr hpq)
  exact hstep.trans_le htail

/-- The balanced key has valuation at most `D * b(q+B)`, and one further value of `b` eventually
dominates this upper bound. -/
theorem exists_eventually_balancedKey_valuation_le_succ {b : ℕ → ℝ}
    (hbpos : ∀ n, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop)
    {D : ℕ} (δ : Fin D → ℕ) :
    ∃ Q₀ : ℕ, ∀ q ≥ Q₀,
      (key (fun i => q + δ i)).sum (fun n k => (k : ℝ) * b n) ≤
          (D : ℝ) * b (q + magnitudeOffsetMax δ) ∧
        (D : ℝ) * b (q + magnitudeOffsetMax δ) ≤
          b (q + magnitudeOffsetMax δ + 1) := by
  have hpos : ∀ᶠ n in atTop, 0 < b n := Filter.Eventually.of_forall hbpos
  obtain ⟨Nm, hmono⟩ := exists_eventually_monotone hpos hratio
  obtain ⟨Nr, hratioD⟩ :=
    Filter.eventually_atTop.mp (hratio.eventually_ge_atTop (D : ℝ))
  refine ⟨max Nm Nr, fun q hq => ?_⟩
  have hqNm : Nm ≤ q := (le_max_left _ _).trans hq
  have hqNr : Nr ≤ q := (le_max_right _ _).trans hq
  constructor
  · rw [valuation_eq_key_sum]
    calc
      ∑ i : Fin D, b (q + δ i)
          ≤ ∑ _i : Fin D, b (q + magnitudeOffsetMax δ) := by
            apply Finset.sum_le_sum
            intro i _
            apply hmono (q + δ i) (q + magnitudeOffsetMax δ)
            · omega
            · exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
      _ = (D : ℝ) * b (q + magnitudeOffsetMax δ) := by
            simp [Finset.card_univ]
  · have hr := hratioD (q + magnitudeOffsetMax δ) (by omega)
    rw [le_div_iff₀ (hbpos (q + magnitudeOffsetMax δ))] at hr
    exact hr

end

end GaloisForLFunctions
