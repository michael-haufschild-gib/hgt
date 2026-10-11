import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearWindow

/-!
# Vanishing of the heat Hankel determinants at positive heat time

The determinants `Δ_N(a) = det (M_{i+j}(a))_{i,j<N}` are continuous in the heat time `a > 0`, and by
the linear window `Δ_N(a) > 0` for `a N ≤ κ` (`heatMomentDet_pos_of_mul_le`).

* **Blow-up law** (`exists_heatMomentDet_eq_zero_of_not_riemannHypothesis`).  If RH fails, then for
  every heat time `a₀ > 0` some determinant vanishes at a time `a ∈ (κ/N, a₀]`.  Zeros of the
  determinants (blow-up times of the associated Toda lattice) therefore accumulate at `a = 0`, but the
  `N`-th one never occurs before `κ/N`.
* **Criterion** (`riemannHypothesis_iff_heatMomentDet_ne_zero`).  RH holds iff no heat Hankel
  determinant vanishes at any positive heat time.

Proof: if RH fails, Sylvester's criterion at `a₀` gives some `Δ_N(a₀) ≤ 0`
(`riemannHypothesis_iff_heatMomentDet_pos`).  Since `Δ_N(κ/N) > 0`, the intermediate value theorem
gives a zero in `(κ/N, a₀]`.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry (leadingMatrix)

namespace RHTower

noncomputable section

/-- The heat Hankel determinant `Δ_N(a)`. -/
def heatMomentDet (N : ℕ) (a : ℝ) : ℝ := (leadingMatrix (heatMomentArray a) N).det

theorem continuousAt_heatMomentArray {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    ContinuousAt (fun x : ℝ => heatMomentArray x i j) a := by
  have hd := (hasDerivAt_xiHeatMoment (i + j) (τ₀ := (a : ℂ)) (by simpa using ha)).continuousAt
  exact Complex.continuous_re.continuousAt.comp (hd.comp Complex.continuous_ofReal.continuousAt)

theorem continuousOn_heatMomentDet (N : ℕ) : ContinuousOn (heatMomentDet N) (Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h := continuousAt_heatMomentArray x.2 i j
  exact h.comp continuous_subtype_val.continuousAt

/-- **Blow-up law.**  If RH fails, then below every heat time some Hankel determinant vanishes, and
the `N`-th one only after `κ/N`. -/
theorem exists_heatMomentDet_eq_zero_of_not_riemannHypothesis (hRH : ¬RiemannHypothesis)
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : ℝ, routeUCompletedPrimeGammaAperture / N < a ∧ a ≤ a₀ ∧
      heatMomentDet N a = 0 := by
  have hκ := routeUCompletedPrimeGammaAperture_pos
  obtain ⟨N, hN⟩ : ∃ N, heatMomentDet N a₀ ≤ 0 := by
    by_contra h
    push Not at h
    exact hRH ((riemannHypothesis_iff_heatMomentDet_pos ha₀).2 h)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp [heatMomentDet, leadingMatrix] at hN
      exact absurd hN (by norm_num)
    · exact h
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  set c := routeUCompletedPrimeGammaAperture / N with hc
  have hc0 : 0 < c := div_pos hκ hNR
  have hcpos : 0 < heatMomentDet N c :=
    heatMomentDet_pos_of_mul_le hc0 (by rw [hc, div_mul_cancel₀ _ hNR.ne'])
  have hca : c < a₀ := by
    by_contra h
    push Not at h
    have : 0 < heatMomentDet N a₀ :=
      heatMomentDet_pos_of_mul_le ha₀ (by
        calc a₀ * N ≤ c * N := mul_le_mul_of_nonneg_right h hNR.le
          _ = routeUCompletedPrimeGammaAperture := by rw [hc, div_mul_cancel₀ _ hNR.ne'])
    linarith
  have hcont : ContinuousOn (heatMomentDet N) (Icc c a₀) :=
    (continuousOn_heatMomentDet N).mono fun x hx => lt_of_lt_of_le hc0 hx.1
  obtain ⟨a, ha, hza⟩ := intermediate_value_Icc' hca.le hcont ⟨hN, hcpos.le⟩
  refine ⟨N, hN0, a, lt_of_le_of_ne ha.1 ?_, ha.2, hza⟩
  rintro rfl
  linarith

/-- **RH as zero-freeness of the heat Hankel determinants.** -/
theorem riemannHypothesis_iff_heatMomentDet_ne_zero :
    RiemannHypothesis ↔ ∀ N : ℕ, ∀ a : ℝ, 0 < a → heatMomentDet N a ≠ 0 := by
  constructor
  · intro hRH N a ha
    exact ((riemannHypothesis_iff_heatMomentDet_pos ha).1 hRH N).ne'
  · intro h
    by_contra hRH
    obtain ⟨N, -, a, hca, -, hz⟩ := exists_heatMomentDet_eq_zero_of_not_riemannHypothesis hRH one_pos
    have hκ := routeUCompletedPrimeGammaAperture_pos
    exact h N a (lt_of_le_of_lt (div_nonneg hκ.le (Nat.cast_nonneg N)) hca) hz

end

end RHTower
