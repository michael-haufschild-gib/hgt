import GaloisForLFunctions.HTGeometry.KleinGordonBandSwitchedWork

/-!
# The band work accounting approximates the true one

The classical balance of statement 287 is an exact identity about the compressed equation. What makes
it a statement about the original one is that both of its sides converge as the cut-off grows.

Both do, and for the same reason: an operator family that is uniformly bounded and strongly continuous
has compressions that converge strongly at each time, so along any convergent curve of states
`W_R(s)z_R → W(s)z`. Applied to the solution this gives the potential term, applied to the derivative
family it gives the work density; the state converges by statement 258 and the work density stays
bounded by a constant on the interval, so dominated convergence closes the second one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section AdiabaticLimit

variable {W Wd : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **The compressions act correctly along any convergent curve of states.** -/
theorem tendsto_kgBandOpT_apply_of_tendsto (hL0 : 0 ≤ L) (hVb : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    {z : ℝ → Lp ℂ 2 (volume : Measure E)} {z₀ : Lp ℂ 2 (volume : Measure E)}
    (hz : Tendsto z atTop (𝓝 z₀)) (s : ℝ) :
    Tendsto (fun R : ℝ => kgBandOpT Wd R s (z R)) atTop (𝓝 (Wd s z₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzn := (tendsto_iff_norm_sub_tendsto_zero).mp hz
  have hop := (tendsto_iff_norm_sub_tendsto_zero).mp (tendsto_kgBandOpT_apply Wd s z₀)
  have hle : ∀ R : ℝ, ‖kgBandOpT Wd R s (z R) - Wd s z₀‖
      ≤ L * ‖z R - z₀‖ + ‖kgBandOpT Wd R s z₀ - Wd s z₀‖ := by
    intro R
    have hsplit : kgBandOpT Wd R s (z R) - Wd s z₀
        = kgBandOpT Wd R s (z R - z₀) + (kgBandOpT Wd R s z₀ - Wd s z₀) := by
      rw [map_sub]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (kgBandOpT Wd R s).le_of_opNorm_le (norm_kgBandOpT_le hL0 hVb R s) _
  have hsum : Tendsto (fun R : ℝ => L * ‖z R - z₀‖ + ‖kgBandOpT Wd R s z₀ - Wd s z₀‖)
      atTop (𝓝 0) := by
    simpa using (hzn.const_mul L).add hop
  exact squeeze_zero (fun _ => norm_nonneg _) hle hsum

/-- **The potential term converges.** -/
theorem tendsto_re_inner_kgBandOpT_source (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (hL0 : 0 ≤ L) (hVb : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (x y : Lp ℂ 2 (volume : Measure E)) (s : ℝ) :
    Tendsto (fun R : ℝ => RCLike.re (inner ℂ (kgBandOpT Wd R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
      (𝓝 (RCLike.re (inner ℂ (Wd s (kgFieldMildT W x y s)) (kgFieldMildT W x y s)))) := by
  have hsol := tendsto_kgFieldMildT_band hb0 hWb hWs x y s
  have hsrc := tendsto_kgBandOpT_apply_of_tendsto hL0 hVb hsol s
  exact ((RCLike.reCLM (K := ℂ)).continuous.tendsto _).comp (hsrc.inner hsol)

/-- **The adiabatic energy of the band solution converges.** -/
theorem tendsto_kgAdiabaticEnergy_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (g y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => kgAdiabaticEnergy (kgBandOpT W R) (kgLowPassOp R g)
        (kgLowPassOp R y) t) atTop (𝓝 (kgAdiabaticEnergy W g y t)) := by
  have halign : ∀ R : ℝ, kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgLowPassOp R g))
        (kgLowPassOp R y)
      = kgFieldMildT (kgBandOpT W R) (kgLowPassOp R (kgFreqInvOp g)) (kgLowPassOp R y) := by
    intro R
    rw [kgLowPassOp_kgFreqInvOp]
  have hstate : Tendsto (fun R : ℝ =>
      ‖kgFieldStateT (kgBandOpT W R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ (2 : ℕ)) atTop
      (𝓝 (‖kgFieldStateT W g y t‖ ^ (2 : ℕ))) :=
    ((tendsto_kgFieldStateT_band hb0 hWb hWs g y t).norm).pow 2
  have hpot : Tendsto (fun R : ℝ => RCLike.re (inner ℂ (kgBandOpT W R t
        (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgLowPassOp R g)) (kgLowPassOp R y) t))
      (kgFieldMildT (kgBandOpT W R) (kgFreqInvOp (kgLowPassOp R g)) (kgLowPassOp R y) t))) atTop
      (𝓝 (RCLike.re (inner ℂ (W t (kgFieldMildT W (kgFreqInvOp g) y t))
        (kgFieldMildT W (kgFreqInvOp g) y t)))) := by
    have h := tendsto_re_inner_kgBandOpT_source hb0 hWb hWs hb0 hWb (kgFreqInvOp g) y t
    exact h.congr fun R => by rw [halign R]
  exact hstate.sub hpot

set_option maxHeartbeats 1000000 in
/-- **The accumulated work of the band solution converges.** -/
theorem tendsto_integral_work_band (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r z)
    (hL0 : 0 ≤ L) (hVb : ∀ r : ℝ, ‖Wd r‖ ≤ L)
    (hVs : ∀ z : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => Wd r z)
    (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ s in (0 : ℝ)..t, RCLike.re (inner ℂ (kgBandOpT Wd R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, RCLike.re (inner ℂ (Wd s (kgFieldMildT W x y s))
        (kgFieldMildT W x y s)))) := by
  set K : ℝ := L * ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) ^ (2 : ℕ) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hbound : IntervalIntegrable (fun _ : ℝ => K) volume 0 t := intervalIntegrable_const
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable
      (fun s : ℝ => RCLike.re (inner ℂ (kgBandOpT Wd R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s)))
      (volume.restrict (Set.uIoc 0 t)) := by
    intro R
    have hcu : Continuous (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y)) :=
      continuous_kgFieldMildT hb0 (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) _ _
    have hVu : Continuous fun s : ℝ => kgBandOpT Wd R s
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s) :=
      continuous_of_strong_comp (norm_kgBandOpT_le hL0 hVb R)
        (continuous_kgBandOpT_apply hVs R) continuous_id hcu
    exact ((RCLike.reCLM (K := ℂ)).continuous.comp (hVu.inner hcu)).aestronglyMeasurable
  have hdom : ∀ R : ℝ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖RCLike.re (inner ℂ (kgBandOpT Wd R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))‖ ≤ K := by
    intro R
    filter_upwards with s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    set u : Lp ℂ 2 (volume : Measure E) :=
      kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s with hu
    have h3 : ‖u‖ ≤ (‖kgLowPassOp (E := E) R x‖ + ‖kgLowPassOp (E := E) R y‖)
        * Real.exp (b * |s|) :=
      norm_kgFieldMildT_le hb0 (norm_kgBandOpT_le hb0 hWb R)
        (continuous_kgBandOpT_apply hWs R) _ _ s
    have h4 : ‖kgLowPassOp (E := E) R x‖ ≤ ‖x‖ := norm_kgLowPassOp_apply_le R x
    have h5 : ‖kgLowPassOp (E := E) R y‖ ≤ ‖y‖ := norm_kgLowPassOp_apply_le R y
    have h6 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h7 : ‖u‖ ≤ (‖x‖ + ‖y‖) * Real.exp (b * |t|) := by
      refine h3.trans ?_
      exact mul_le_mul (by linarith) h6 (Real.exp_pos _).le (by positivity)
    have hcs : ‖RCLike.re (inner ℂ (kgBandOpT Wd R s u) u)‖
        ≤ ‖kgBandOpT Wd R s u‖ * ‖u‖ := by
      refine le_trans (RCLike.abs_re_le_norm _) ?_
      exact norm_inner_le_norm (𝕜 := ℂ) _ _
    have hop : ‖kgBandOpT Wd R s u‖ ≤ L * ‖u‖ :=
      (kgBandOpT Wd R s).le_of_opNorm_le (norm_kgBandOpT_le hL0 hVb R s) _
    have hM0 : (0 : ℝ) ≤ (‖x‖ + ‖y‖) * Real.exp (b * |t|) := by positivity
    have hfin : ‖kgBandOpT Wd R s u‖ * ‖u‖ ≤ K := by
      have hsq : ‖u‖ * ‖u‖ ≤ ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) ^ (2 : ℕ) := by
        nlinarith [norm_nonneg u, h7]
      calc ‖kgBandOpT Wd R s u‖ * ‖u‖ ≤ (L * ‖u‖) * ‖u‖ :=
            mul_le_mul_of_nonneg_right hop (norm_nonneg _)
        _ = L * (‖u‖ * ‖u‖) := by ring
        _ ≤ L * ((‖x‖ + ‖y‖) * Real.exp (b * |t|)) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hsq hL0
    exact hcs.trans hfin
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Tendsto (fun R : ℝ => RCLike.re (inner ℂ (kgBandOpT Wd R s
          (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))
        (kgFieldMildT (kgBandOpT W R) (kgLowPassOp R x) (kgLowPassOp R y) s))) atTop
        (𝓝 (RCLike.re (inner ℂ (Wd s (kgFieldMildT W x y s)) (kgFieldMildT W x y s)))) := by
    filter_upwards with s _
    exact tendsto_re_inner_kgBandOpT_source hb0 hWb hWs hL0 hVb x y s
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => K) (l := (atTop : Filter ℝ))
    (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbound hlim

end AdiabaticLimit

end GaloisForLFunctions.HTGeometry
