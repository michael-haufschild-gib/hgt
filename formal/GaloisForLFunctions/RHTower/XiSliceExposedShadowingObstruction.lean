import GaloisForLFunctions.RHTower.XiSliceCoeffNearDoublePositivity
import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction
import GaloisForLFunctions.RHTower.XiSlicePolyaFrequencyDensityZeroOne

/-!
# A false Riemann hypothesis forces weakly shadowed exposed zeros at low order

Call an off-line zero `z` of `Ξ` *exposed at a height `t`* when `|Re z − t| < |Im z|`.

**Per-zero form** (`exists_weakly_shadowed_near_offLine_zero`).  At heights arbitrarily close to
the ordinate of every off-line zero, some order `1 ≤ k < max(K, κ log t)` is weakly shadowed.
Here the zero itself is exposed, contributing at most `2/(Im z)²` to the mass.  When its own pair is
the only exposed family at `t`, taking `D = |Im z|` shows that fewer than `7k − 1` critical zeros
lie within `|Im z|` of `t`.  Off-line zeros repel dense clusters of critical zeros, at the scale of
their own displacement.

**Theorem** (`exists_weakly_shadowed_exposed_of_not_riemannHypothesis`).  There are constants `K`
and `κ` with the following property.  If the Riemann hypothesis fails, there is a height `t ≥ 0`
with `Ξ(t) ≠ 0` and an order `1 ≤ k < max(K, κ log t)` at which the exposed zeros are *weakly
shadowed*: for every set `C₀` of `m ≥ k` critical zero copies within distance `D` of `t`, some
finite family of exposed off-line copies carries `3k D² Σ (Im z)²/|z − t|⁴ > m − k + 1`.

This combines the finite-order falsification certificate (`XiSliceFiniteOrderReduction`) with the
cone and near-double law (`xiSliceCoeff_re_pos_of_exposed_nearDouble`).  Every off-line
configuration that is strongly shadowed at every height and every order `k < max(K, κ log t)` is
therefore excluded unconditionally.  Off-line zeros cannot hide behind clusters of critical zeros.

The certificate height may lie on a zero of `Ξ`; the negative coefficient persists on a
neighbourhood (`continuous_xiSliceCoeff`), which contains heights off the discrete zero set.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A negative low-order slice coefficient persists at nearby heights off the zeros of `Ξ`. -/
theorem exists_near_height_re_xiSliceCoeff_neg {K κ t : ℝ} {k : ℕ} (ht0 : 0 ≤ t)
    (hk : (k : ℝ) < max K (κ * Real.log t)) (hre : (xiSliceCoeff t (2 * k)).re < 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, t < s ∧ s < t + ε ∧ XiC s ≠ 0 ∧ (xiSliceCoeff s (2 * k)).re < 0 ∧
      (k : ℝ) < max K (κ * Real.log s) := by
  -- a neighbourhood on which the coefficient stays negative and the order bound holds
  obtain ⟨η, hη, hηε, hηprop⟩ : ∃ η > 0, η ≤ ε ∧ ∀ s, t < s → s < t + η →
      (xiSliceCoeff s (2 * k)).re < 0 ∧ (k : ℝ) < max K (κ * Real.log s) := by
    have hc : ContinuousAt (fun s : ℝ => (xiSliceCoeff s (2 * k)).re) t :=
      (Complex.continuous_re.comp (continuous_xiSliceCoeff (2 * k))).continuousAt
    obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (gt_mem_nhds hre))
    rcases lt_or_ge (k : ℝ) K with hkK | hkK
    · refine ⟨min ε₁ ε, lt_min hε₁ hε, min_le_right _ _, fun s hs1 hs2 =>
        ⟨h₁ ?_, lt_max_of_lt_left hkK⟩⟩
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left ε₁ ε]
    · have hkl : (k : ℝ) < κ * Real.log t := by
        rcases lt_max_iff.mp hk with h | h
        · linarith
        · exact h
      have ht : t ≠ 0 := by
        rintro rfl
        rw [Real.log_zero, mul_zero] at hkl
        exact absurd hkl (not_lt.mpr (Nat.cast_nonneg k))
      have hlc : ContinuousAt (fun s : ℝ => κ * Real.log s) t :=
        (Real.continuousAt_log ht).const_mul κ
      obtain ⟨ε₂, hε₂, h₂⟩ := Metric.eventually_nhds_iff.mp (hlc.eventually (lt_mem_nhds hkl))
      refine ⟨min (min ε₁ ε₂) ε, lt_min (lt_min hε₁ hε₂) hε, min_le_right _ _,
        fun s hs1 hs2 => ⟨h₁ ?_, lt_max_of_lt_right (h₂ ?_)⟩⟩
      · rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_left (min ε₁ ε₂) ε, min_le_left ε₁ ε₂]
      · rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [min_le_left (min ε₁ ε₂) ε, min_le_right ε₁ ε₂]
  -- a height in that neighbourhood off the zeros of `Ξ`
  have hXi0 : XiC 0 ≠ 0 := by
    have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
    rw [this]
    exact xi_ne_zero_of_real _
  have hfinXi := zeros_finite_closedBall XiC_differentiable hXi0 (|t| + η + 1)
  have hfinR : ((fun x : ℝ => (x : ℂ)) ⁻¹' {w ∈ closedBall (0 : ℂ) (|t| + η + 1) | XiC w = 0}).Finite :=
    hfinXi.preimage (Complex.ofReal_injective.injOn)
  obtain ⟨s, ⟨hs1, hs2⟩, hsnot⟩ :=
    ((Set.Ioo_infinite (by linarith : t < t + η)).sdiff hfinR).nonempty
  have hs : XiC s ≠ 0 := by
    intro h0
    apply hsnot
    refine ⟨?_, h0⟩
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have := neg_abs_le t
    have := le_abs_self t
    constructor <;> linarith
  obtain ⟨hres, hks⟩ := hηprop s hs1 hs2
  exact ⟨s, hs1, by linarith, hs, hres, hks⟩

/-- At a height off the zeros of `Ξ`, a negative slice coefficient of order `k` forces weak
shadowing of the exposed zeros at order `k ≥ 1`. -/
theorem weakly_shadowed_of_re_xiSliceCoeff_neg {s : ℝ} (hs : XiC s ≠ 0) {k : ℕ}
    (hres : (xiSliceCoeff s (2 * k)).re < 0) :
    1 ≤ k ∧ ∀ C₀ : Finset XiZeroCopy, (∀ q ∈ C₀, XiCopyCritical q) → k ≤ C₀.card →
      ∀ D : ℝ, (∀ q ∈ C₀, ‖xiSpectralPoint q - s‖ ≤ D) →
        ∃ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
            |(xiSpectralPoint q).re - s| < |(xiSpectralPoint q).im|) ∧
          (C₀.card : ℝ) - k + 1 < 3 * k * (D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
            ‖xiSpectralPoint q - s‖ ^ 4) := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd hres (not_lt.mpr (xiSliceCoeff_zero_re_pos hs).le)
    · exact h
  refine ⟨hk1, fun C₀ hC₀ hk₀ D hD => ?_⟩
  by_contra hno
  push Not at hno
  exact absurd hres (not_lt.mpr
    (xiSliceCoeff_re_pos_of_exposed_nearDouble_card hs hk1 C₀ hC₀ hk₀ hD hno).le)

/-- **Weak shadowing is forced by a false Riemann hypothesis.** -/
theorem exists_weakly_shadowed_exposed_of_not_riemannHypothesis :
    ∃ K κ : ℝ, ¬ RiemannHypothesis →
      ∃ t : ℝ, 0 ≤ t ∧ XiC t ≠ 0 ∧ ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) < max K (κ * Real.log t) ∧
        ∀ C₀ : Finset XiZeroCopy, (∀ q ∈ C₀, XiCopyCritical q) → k ≤ C₀.card →
          ∀ D : ℝ, (∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D) →
            ∃ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
                |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) ∧
              (C₀.card : ℝ) - k + 1 < 3 * k * (D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
                ‖xiSpectralPoint q - t‖ ^ 4) := by
  obtain ⟨K, κ, hcert⟩ := exists_not_riemannHypothesis_iff_low_order_xiSliceCoeff_not_nonneg
  refine ⟨K, κ, fun hRH => ?_⟩
  obtain ⟨t, ht0, k, hk, hneg⟩ := hcert.mp hRH
  have hre : (xiSliceCoeff t (2 * k)).re < 0 := by
    by_contra hge
    push Not at hge
    exact hneg (Complex.nonneg_iff.mpr ⟨hge, (xiSliceCoeff_im_eq_zero t (2 * k)).symm⟩)
  obtain ⟨s, hs1, -, hs, hres, hks⟩ := exists_near_height_re_xiSliceCoeff_neg ht0 hk hre one_pos
  obtain ⟨hk1, hw⟩ := weakly_shadowed_of_re_xiSliceCoeff_neg hs hres
  exact ⟨s, by linarith, hs, k, hk1, hks, hw⟩

/-- **Every off-line zero is weakly shadowed near its own ordinate.**  There are `K` and `κ` such
that for every zero `ρ` of `ξ` off the critical line with `Im ρ ≥ 0` and every `ε > 0` there is a
height `t ∈ (Im ρ, Im ρ + ε)` with `Ξ(t) ≠ 0` and an order `1 ≤ k < max(K, κ log t)` at which
the exposed zeros at `t` are weakly shadowed. -/
theorem exists_weakly_shadowed_near_offLine_zero :
    ∃ K κ : ℝ, ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≠ 1 / 2 → 0 ≤ ρ.im → ∀ ε > 0,
      ∃ t : ℝ, ρ.im < t ∧ t < ρ.im + ε ∧ XiC t ≠ 0 ∧ ∃ k : ℕ, 1 ≤ k ∧
        (k : ℝ) < max K (κ * Real.log t) ∧
        ∀ C₀ : Finset XiZeroCopy, (∀ q ∈ C₀, XiCopyCritical q) → k ≤ C₀.card →
          ∀ D : ℝ, (∀ q ∈ C₀, ‖xiSpectralPoint q - t‖ ≤ D) →
            ∃ F : Finset XiZeroCopy, (∀ q ∈ F, ¬ XiCopyCritical q ∧
                |(xiSpectralPoint q).re - t| < |(xiSpectralPoint q).im|) ∧
              (C₀.card : ℝ) - k + 1 < 3 * k * (D ^ 2 * ∑ q ∈ F, (xiSpectralPoint q).im ^ 2 /
                ‖xiSpectralPoint q - t‖ ^ 4) := by
  obtain ⟨K, κ, hpos⟩ := exists_xiSliceCoeff_pos_high_order
  refine ⟨K, κ, fun ρ hρ hne hγ ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_not_nonneg_xiSliceCoeff_of_offLine hρ hne
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : (k : ℝ) < max K (κ * Real.log ρ.im) := by
      by_contra hge
      push Not at hge
      exact hn (hpos ρ.im hγ k hge).le
    have hre : (xiSliceCoeff ρ.im (2 * k)).re < 0 := by
      by_contra hge
      push Not at hge
      exact hn (Complex.nonneg_iff.mpr ⟨hge, (xiSliceCoeff_im_eq_zero ρ.im (2 * k)).symm⟩)
    obtain ⟨s, hs1, hs2, hs, hres, hks⟩ := exists_near_height_re_xiSliceCoeff_neg hγ hk hre hε
    obtain ⟨hk1, hw⟩ := weakly_shadowed_of_re_xiSliceCoeff_neg hs hres
    exact ⟨s, hs1, hs2, hs, k, hk1, hks, hw⟩
  · exact absurd (by rw [xiSliceCoeff_odd_eq_zero]) hn

end

end RHTower
