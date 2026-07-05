/-
The center-uniform four-phase sublevel bound, part I: the conditional
inverse-√ averaging.  Identical to `inv_sqrt_average` except the singular
domination is required only where the center modulus exceeds the split
height — the form the moving three-phase constants satisfy (below the
split height the constant cap is the only available bound, and there the
one-phase law pays for it).
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBFourPhase

namespace RHTower
namespace Sublevel

open MeasureTheory

theorem inv_sqrt_average' {D c' : ℂ} {M K sstar : ℝ} {f : ℝ → ENNReal}
    (hD : D ≠ 0) (hK : 0 ≤ K) (hs : 0 < sstar)
    (hs2 : 2 * sstar ≤ ‖D‖)
    (hfM : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi), f η ≤ ENNReal.ofReal M)
    (hfK : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      sstar ≤ ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ →
      f η ≤ ENNReal.ofReal
        (K / Real.sqrt ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖)) :
    ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi), f η
      ≤ ENNReal.ofReal M * ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖)
        + ENNReal.ofReal (K / Real.sqrt sstar)
          * ENNReal.ofReal (2 * Real.pi) := by
  classical
  have hcont : Continuous fun η : ℝ =>
      ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ :=
    (continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)))).norm
  set E1 : Set ℝ := {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
      ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ ≤ sstar} with hE1
  set E2 : Set ℝ := {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
      sstar ≤ ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖} with hE2
  have hE1m : MeasurableSet E1 := by
    apply IsClosed.measurableSet
    exact isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hE2m : MeasurableSet E2 := by
    apply IsClosed.measurableSet
    exact isClosed_Icc.inter (isClosed_le continuous_const hcont)
  have hpt : ∀ η ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      f η ≤ E1.indicator (fun _ => ENNReal.ofReal M) η
        + E2.indicator (fun _ => ENNReal.ofReal (K / Real.sqrt sstar)) η := by
    intro η hη
    rcases le_total ‖c' + D * Complex.exp ((η : ℂ) * Complex.I)‖ sstar
      with hle | hge
    · refine le_trans (hfM η hη) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem
        (show η ∈ E1 from ⟨hη, hle⟩) (fun _ => ENNReal.ofReal M)).symm) ?_
      exact le_self_add
    · refine le_trans (hfK η hη hge) ?_
      have hmono : K / Real.sqrt ‖c' + D * Complex.exp ((η : ℂ)
            * Complex.I)‖ ≤ K / Real.sqrt sstar := by
        apply div_le_div_of_nonneg_left hK (Real.sqrt_pos.mpr hs)
        exact Real.sqrt_le_sqrt hge
      refine le_trans (ENNReal.ofReal_le_ofReal hmono) ?_
      refine le_trans (le_of_eq (Set.indicator_of_mem
        (show η ∈ E2 from ⟨hη, hge⟩)
        (fun _ => ENNReal.ofReal (K / Real.sqrt sstar))).symm) ?_
      exact le_add_self
  refine le_trans (setLIntegral_mono' measurableSet_Icc hpt) ?_
  refine le_trans (setLIntegral_le_lintegral _ _) ?_
  rw [lintegral_add_left (measurable_const.indicator hE1m),
    lintegral_indicator hE1m, lintegral_indicator hE2m,
    setLIntegral_const, setLIntegral_const]
  have hv1 : volume E1 ≤ ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖) :=
    one_phase_smallball_uniform hD hs.le hs2
  have hv2 : volume E2 ≤ ENNReal.ofReal (2 * Real.pi) := by
    refine le_trans (measure_mono (fun η h => h.1)) ?_
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    linarith [Real.pi_pos]
  exact add_le_add (mul_le_mul_right hv1 _) (mul_le_mul_right hv2 _)

end Sublevel
end RHTower

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **The center-uniform four-phase sublevel law.**  The 4D sublevel
measure of a four-phase circle sum at ANY center `w` is bounded by three
explicit terms: the constant cap paid on the fourth arm's singular set,
the √-capped singular constant on the bulk, and the center-free constants
on the full circle.  The `1/√‖c‖` singularity of the three-phase constants
is averaged out by the fourth phase. -/
theorem four_phase_sublevel_uniform {A B C D w : ℂ} {r σ0 sstar : ℝ}
    {J : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hρB : ‖B‖ < ‖A‖) (hr0 : 0 < r) (hr2 : 2 * r ≤ ‖A‖ - ‖B‖)
    (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3)
    (hJ : ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) * ‖B‖))
        ≤ σ0 * causticKappa ‖A‖ ‖B‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖D‖) :
    (volume.prod (volume.prod (volume.prod volume)))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
              Set.Icc (0 : ℝ) (2 * Real.pi)))) ∩
        {q : ℝ × ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((q.1 : ℂ) * Complex.I)
            + C * Complex.exp ((q.2.1 : ℂ) * Complex.I)
            + B * Complex.exp ((q.2.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((q.2.2.2 : ℂ) * Complex.I)‖ ≤ r})
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3)
          * ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖)
        + ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)
            * ((J : ℝ) * (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖)))
            + 2 * ((2 * Real.pi * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
                / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
              * (2 * Real.pi * Real.sqrt ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
                / ‖C‖))))
            / Real.sqrt sstar)
          * ENNReal.ofReal (2 * Real.pi)
        + ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)
            * ((J : ℝ) * (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * Real.sqrt 2)
            + 2 * Real.pi * (2 * Real.pi
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3
                  * causticKappa ‖A‖ ‖B‖ / 2) (1 / 2)))))
          * ENNReal.ofReal (2 * Real.pi) := by
  classical
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hC0 : (0 : ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  have hρ0 : (0 : ℝ) < ‖A‖ := lt_of_le_of_lt (norm_nonneg B) hρB
  have hκ : (0 : ℝ) < causticKappa ‖A‖ ‖B‖ := by
    rw [causticKappa]
    have hGpos : (0 : ℝ) < (‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2 := by
      nlinarith
    have hpb : (0 : ℝ) < ‖A‖ + ‖B‖ := by linarith
    positivity
  have hY0 : (0 : ℝ) ≤ r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖) :=
    div_nonneg (by positivity)
      (mul_pos (by linarith : (0 : ℝ) < (‖A‖ - ‖B‖) / 2) hb0).le
  have hK0 : (0 : ℝ) ≤ 2 * (Real.pi * r / ‖A‖)
      * ((J : ℝ) * (8 * Real.pi ^ 2
        * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
        * Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖)))
      + 2 * ((2 * Real.pi * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
          / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
        * (2 * Real.pi * Real.sqrt ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
          / ‖C‖)))) := by positivity
  rw [four_phase_fubini A B C D w r]
  have hcap : ∀ η : ℝ, (volume.prod (volume.prod volume))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
        {p : ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((η : ℂ) * Complex.I)
            + C * Complex.exp ((p.1 : ℂ) * Complex.I)
            + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r})
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3) := by
    intro η
    refine le_trans (measure_mono Set.inter_subset_left) ?_
    rw [Measure.prod_prod, Measure.prod_prod, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.pi_pos]
  have hsing : ∀ η : ℝ,
      sstar ≤ ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ →
      (volume.prod (volume.prod volume))
        ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
              Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
          {p : ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((η : ℂ) * Complex.I)
              + C * Complex.exp ((p.1 : ℂ) * Complex.I)
              + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
              + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r})
        ≤ ENNReal.ofReal ((2 * (Real.pi * r / ‖A‖)
            * ((J : ℝ) * (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖)))
            + 2 * ((2 * Real.pi * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
                / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
              * (2 * Real.pi * Real.sqrt ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
                / ‖C‖))))
            / Real.sqrt ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖)
          + 2 * (Real.pi * r / ‖A‖)
            * ((J : ℝ) * (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * Real.sqrt 2)
            + 2 * Real.pi * (2 * Real.pi
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3
                  * causticKappa ‖A‖ ‖B‖ / 2) (1 / 2))))) := by
    intro η hge
    have hc0 : w + D * Complex.exp ((η : ℂ) * Complex.I) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hge
      linarith
    have hx0 : (0 : ℝ) < ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ :=
      lt_of_lt_of_le hss hge
    refine le_trans (three_phase_sublevel_r2log hA hB hC hc0 hρB hr0 hr2
      hσ0 hσ0G hJ hHσ0) ?_
    have hn : ∀ x : ℝ, J • ENNReal.ofReal x
        = ENNReal.ofReal ((J : ℝ) * x) := by
      intro x
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast J,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg J)]
    rw [hn, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have e₁ : Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖
          * (‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ * ‖C‖)))
        = Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖))
          / Real.sqrt ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ := by
      rw [show 2 / (causticKappa ‖A‖ ‖B‖
          * (‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ * ‖C‖))
          = (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖))
            / ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ from by
          field_simp]
      exact Real.sqrt_div (by positivity) _
    have e₂ : Real.sqrt (2 * ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
          / (2 * (‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ * ‖C‖))))
        = Real.sqrt ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r)) / ‖C‖)
          / Real.sqrt ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ := by
      rw [show 2 * ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
          / (2 * (‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ * ‖C‖)))
          = ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r)) / ‖C‖)
            / ‖w + D * Complex.exp ((η : ℂ) * Complex.I)‖ from by
          field_simp]
      exact Real.sqrt_div (by positivity) _
    rw [e₁, e₂]
    exact le_of_eq (by ring)
  set K' : ℝ := 2 * (Real.pi * r / ‖A‖)
      * ((J : ℝ) * (8 * Real.pi ^ 2
        * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖)) * Real.sqrt 2)
      + 2 * Real.pi * (2 * Real.pi
        * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
        / Real.sqrt (min (((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3
            * causticKappa ‖A‖ ‖B‖ / 2) (1 / 2)))) with hK'def
  refine le_trans (setLIntegral_mono' measurableSet_Icc
    (fun η _ => (le_tsub_add : _ ≤ _ - ENNReal.ofReal K'
      + ENNReal.ofReal K'))) ?_
  rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  have havg := inv_sqrt_average' (c' := w) (D := D)
    (M := (2 * Real.pi) ^ 3)
    (f := fun η => (volume.prod (volume.prod volume))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
        {p : ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((η : ℂ) * Complex.I)
            + C * Complex.exp ((p.1 : ℂ) * Complex.I)
            + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r})
        - ENNReal.ofReal K')
    hD hK0 hss hss2
    (fun η _ => le_trans tsub_le_self (hcap η))
    (fun η _ hge => tsub_le_iff_right.mpr (le_trans (hsing η hge)
      (le_of_eq (ENNReal.ofReal_add (by positivity) (by positivity)))))
  refine add_le_add havg ?_
  rw [Real.volume_Icc, sub_zero]

end Sublevel
end RHTower

namespace RHTower
namespace SteinhausModel

open MeasureTheory

/-- **The block marginal**: the Steinhaus small-ball event of a
prime-supported block sum is measured by the FINITE product of uniform
phases over the block. -/
theorem block_marginal {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (a : ℕ → ℝ) (w : ℂ) (t : ℝ) :
    steinhausMeasure {ω : Omega | ‖w + ∑ p ∈ s, (a p : ℂ) * X p ω‖ ≤ t}
      = (Measure.pi fun _ : ↥s => volume.restrict (Set.Icc (0 : ℝ) 1))
          {x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a (p : ℕ) : ℂ)
            * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I
              * ((x p : ℝ) : ℂ))‖ ≤ t} := by
  have hE'm : MeasurableSet {x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach,
      (a (p : ℕ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I
        * ((x p : ℝ) : ℂ))‖ ≤ t} := by
    apply IsClosed.measurableSet
    apply isClosed_le _ continuous_const
    apply Continuous.norm
    apply Continuous.add continuous_const
    apply continuous_finsetSum
    intro p _
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_apply p))))
  have hset : {ω : Omega | ‖w + ∑ p ∈ s, (a p : ℂ) * X p ω‖ ≤ t}
      = s.restrict ⁻¹' {x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach,
          (a (p : ℕ) : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ)
            * Complex.I * ((x p : ℝ) : ℂ))‖ ≤ t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have hsum : ∑ p ∈ s, (a p : ℂ) * X p ω
        = ∑ p ∈ s.attach, (a (p : ℕ) : ℂ)
          * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I
            * ((s.restrict ω p : ℝ) : ℂ)) := by
      rw [← Finset.sum_attach s (fun p => (a p : ℂ) * X p ω)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [X_prime (hs (p : ℕ) p.2) ω]
      rfl
    rw [hsum]
  rw [hset, steinhausMeasure,
    ← Measure.map_apply (Finset.measurable_restrict s) hE'm,
    MeasureTheory.Measure.infinitePi_map_restrict]

end SteinhausModel
end RHTower

namespace RHTower
namespace SteinhausModel

open MeasureTheory

/-- The lintegral form of the phase rescale: integrating `g(2πy)` over the
uniform phase equals `(2π)⁻¹` times the integral of `g` over `[0, 2π]`. -/
theorem lintegral_two_pi_rescale {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ y in Set.Icc (0 : ℝ) 1, g (2 * Real.pi * y)
      = ENNReal.ofReal (2 * Real.pi)⁻¹
          * ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi), g θ := by
  rw [← lintegral_map hg (by fun_prop), map_two_pi_smul,
    lintegral_smul_measure]
  rfl

end SteinhausModel
end RHTower
