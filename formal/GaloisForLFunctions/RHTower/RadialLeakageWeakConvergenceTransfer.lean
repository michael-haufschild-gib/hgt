import GaloisForLFunctions.RHTower.RadialLeakageWeakConvergence

/-!
# Exact Scheffé transfer for finite-aperture radial leakage densities

The finite density here is literally the card's equation `(4)`,
`λ ‖q(λx)‖² / d`.  Once its a.e. pointwise PSWF asymptotic and exact total-mass limit are supplied,
Scheffé's lemma gives `L¹` convergence to `nuInfinityDensity`; hence integrals converge against every
bounded measurable test.  The transfer is unconditional and does not take weak convergence as a
hypothesis.  It leaves only the actual PSWF density asymptotic and mass identification as analytic
inputs.
-/

open MeasureTheory Filter Set GaloisForLFunctions

noncomputable section

namespace RHTower

def nuLambdaDensity (lam d : ℝ) (q : ℝ → ℂ) (x : ℝ) : ℝ :=
  lam * ‖q (lam * x)‖ ^ 2 / d

theorem nuLambdaDensity_nonneg {lam d : ℝ} (hlam : 0 ≤ lam) (hd : 0 < d)
    (q : ℝ → ℂ) (x : ℝ) :
    0 ≤ nuLambdaDensity lam d q x := by
  exact div_nonneg (mul_nonneg hlam (sq_nonneg _)) hd.le

theorem nuLambdaDensity_tendsto_L1
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 ≤ lam i ∧ 0 < d i)
    (hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x)))
    (hmass : Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
        l (nhds (4 / 11))) :
    Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ),
        |nuLambdaDensity (lam i) (d i) (q i) x - nuInfinityDensity x|)
      l (nhds 0) := by
  have hfnn : ∀ᶠ i in l,
      0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] nuLambdaDensity (lam i) (d i) (q i) := by
    filter_upwards [hparam] with i hi
    exact Eventually.of_forall fun x => nuLambdaDensity_nonneg hi.1 hi.2 (q i) x
  have hmass' : Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
      l (nhds (∫ x in Ioi (1 : ℝ), nuInfinityDensity x)) := by
    rw [integral_Ioi_one_nuInfinityDensity]
    exact hmass
  exact tendsto_integral_abs_sub_of_tendsto_integral hfnn hint
    nuInfinityDensity_nonneg_ae integrableOn_Ioi_one_nuInfinityDensity hae hmass'

theorem nuLambdaDensity_tendsto_bounded_test
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 ≤ lam i ∧ 0 < d i)
    (hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x)))
    (hmass : Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
        l (nhds (4 / 11)))
    {w : ℝ → ℝ} {C : ℝ}
    (hw : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))), ‖w x‖ ≤ C)
    (hwm : AEStronglyMeasurable w (volume.restrict (Ioi (1 : ℝ)))) :
    Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), w x * nuLambdaDensity (lam i) (d i) (q i) x)
      l (nhds (∫ x in Ioi (1 : ℝ), w x * nuInfinityDensity x)) := by
  exact tendsto_integral_smul_of_tendsto_integral_abs_sub hw hwm hint
    integrableOn_Ioi_one_nuInfinityDensity
    (nuLambdaDensity_tendsto_L1 hparam hint hae hmass)

/-- Every tail of the limiting finite measure has the exact scaled arcsine mass. -/
theorem integral_Ioi_nuInfinityDensity {a : ℝ} (ha : 1 ≤ a) :
    ∫ x in Ioi a, nuInfinityDensity x
      = (8 / (11 * Real.pi)) * Real.arcsin (1 / a) := by
  rw [show nuInfinityDensity = fun x => (8 / (11 * Real.pi)) *
    radialLeakageDensity x by rfl, integral_const_mul,
    integral_Ioi_radialLeakageDensity ha]

/-- The exact arcsine tail law is inherited by the finite leakage densities.  This is the
indicator-test specialization of `nuLambdaDensity_tendsto_bounded_test`; no weak-convergence
hypothesis is assumed. -/
theorem nuLambdaDensity_tendsto_indicator_tail
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 ≤ lam i ∧ 0 < d i)
    (hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x)))
    (hmass : Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
        l (nhds (4 / 11)))
    {k : ℝ} (hk : 1 ≤ k) :
    Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ),
        (Ioi k).indicator (fun _ => (1 : ℝ)) x *
          nuLambdaDensity (lam i) (d i) (q i) x)
      l (nhds ((8 / (11 * Real.pi)) * Real.arcsin (1 / k))) := by
  have htest := nuLambdaDensity_tendsto_bounded_test hparam hint hae hmass
    (w := (Ioi k).indicator (fun _ => (1 : ℝ)))
    (C := 1)
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ Ioi k
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx])
    ((measurable_const.indicator measurableSet_Ioi).aestronglyMeasurable)
  have hsub : Ioi k ⊆ Ioi (1 : ℝ) := fun x hx => lt_of_le_of_lt hk hx
  have htail :
      ∫ x in Ioi (1 : ℝ),
          (Ioi k).indicator (fun _ => (1 : ℝ)) x * nuInfinityDensity x
        = ∫ x in Ioi k, nuInfinityDensity x := by
    calc
      ∫ x in Ioi (1 : ℝ),
          (Ioi k).indicator (fun _ => (1 : ℝ)) x * nuInfinityDensity x
          = ∫ x, (Ioi (1 : ℝ)).indicator
              (fun x => (Ioi k).indicator (fun _ => (1 : ℝ)) x *
                nuInfinityDensity x) x := by
              rw [integral_indicator measurableSet_Ioi]
      _ = ∫ x, (Ioi k).indicator nuInfinityDensity x := by
            apply integral_congr_ae
            exact Eventually.of_forall fun x => by
              by_cases hx : x ∈ Ioi k
              · have hx1 : x ∈ Ioi (1 : ℝ) := hsub hx
                simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx1]
              · simp [Set.indicator_of_notMem hx]
      _ = ∫ x in Ioi k, nuInfinityDensity x := by
            rw [integral_indicator measurableSet_Ioi]
  rw [htail, integral_Ioi_nuInfinityDensity hk] at htest
  exact htest

/-- The card's exact radial Gram diagonal `(8/(11πk)) arcsin(1/k)` follows from the finite
density asymptotic and mass convergence, including the dilation factor `1/k`. -/
theorem nuLambdaDensity_tendsto_radialGramDiagonal
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 ≤ lam i ∧ 0 < d i)
    (hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x)))
    (hmass : Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
        l (nhds (4 / 11)))
    {k : ℝ} (hk : 1 ≤ k) :
    Tendsto (fun i =>
      (1 / k) * ∫ x in Ioi (1 : ℝ),
        (Ioi k).indicator (fun _ => (1 : ℝ)) x *
          nuLambdaDensity (lam i) (d i) (q i) x)
      l (nhds (8 / (11 * Real.pi * k) * Real.arcsin (1 / k))) := by
  have h := (nuLambdaDensity_tendsto_indicator_tail hparam hint hae hmass hk).const_mul (1 / k)
  convert h using 1
  ring_nf

end RHTower

end
