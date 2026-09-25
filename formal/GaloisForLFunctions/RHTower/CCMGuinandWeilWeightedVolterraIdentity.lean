import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCesaroAnchoredMoment

/-!
# Source-faithful Volterra identity for completed prime--polar windows

One cutoff integration of any smooth literal weighted prime-minus-polar cumulative source
is exactly its moving triangular reporter. Both channels remain coupled throughout.
-/

open MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private theorem integral_integral_eq_endpoint_mul_sub_moment
    {g : ℝ → ℝ} {b H : ℝ} (hbH : b ≤ H)
    (hg : IntervalIntegrable g volume b H) :
    (∫ s in b..H, ∫ h in b..s, g h) =
      H * (∫ h in b..H, g h) - ∫ h in b..H, h * g h := by
  let A : ℝ → ℝ := fun s => ∫ h in b..s, g h
  let G : ℝ → ℝ := fun s => s
  have hAac : AbsolutelyContinuousOnInterval A b H :=
    hg.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b H by simp [hbH])
  have hGcd : ContDiff ℝ 1 G := by fun_prop
  have hGac : AbsolutelyContinuousOnInterval G b H :=
    hGcd.contDiffOn.absolutelyContinuousOnInterval
  have hibp := hGac.integral_mul_deriv_eq_deriv_mul hAac
  have hleft : (∫ s in b..H, G s * deriv A s) =
      ∫ s in b..H, s * g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hmem
    have hd : HasDerivAt A (g s) s :=
      hs (uIoc_subset_uIcc hmem) b (by simp [hbH])
    rw [hd.deriv]
  have hright : (∫ s in b..H, deriv G s * A s) =
      ∫ s in b..H, A s := by
    apply intervalIntegral.integral_congr
    intro s _
    have hd : deriv G s = 1 := (hasDerivAt_id s).deriv
    change deriv G s * A s = A s
    rw [hd, one_mul]
  have hAb : A b = 0 := by simp [A]
  rw [hleft, hright, hAb, mul_zero, sub_zero] at hibp
  dsimp only [A, G] at hibp ⊢
  linarith

/-- First Volterra primitive of the literal smooth weighted prime-minus-polar window equals
its triangular window, with prime and polar channels kept in the same identity. -/
theorem integral_ccmPrimePolarWeightedWindow_eq_triangular
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H)
    {F F' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF'cont : ContinuousOn F' (Set.Icc b H)) :
    (∫ t in b..H, ccmGuinandWeilPrimePolarWeightedWindow b t F) =
      ccmGuinandWeilPrimePolarWeightedWindow b H
        (fun h => (H - h) * F h) := by
  let E := criticalMellinCompletedError
  let g : ℝ → ℝ := fun h => E h * F' h
  have hFcont : ContinuousOn F (Set.Icc b H) := by
    intro x hx
    exact (hF x hx).continuousAt.continuousWithinAt
  have hFcontU : ContinuousOn F (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hFcont
  have hF'contU : ContinuousOn F' (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hF'cont
  have hEint : IntervalIntegrable E volume b H :=
    intervalIntegrable_criticalMellinCompletedError_on_Icc hbH
  have hEFint : IntervalIntegrable (fun h => E h * F h) volume b H :=
    hEint.mul_continuousOn hFcontU
  have hg : IntervalIntegrable g volume b H :=
    hEint.mul_continuousOn hF'contU
  have hprimInt : IntervalIntegrable
      (fun t => ∫ h in b..t, g h) volume b H :=
    (hg.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b H by simp [hbH])).continuousOn.intervalIntegrable
  have hQflux :
      (∫ t in b..H, ccmGuinandWeilPrimePolarWeightedWindow b t F) =
        (H - b) * F b * E b -
          (∫ t in b..H, E t * F t) +
            H * (∫ h in b..H, g h) - ∫ h in b..H, h * g h := by
    calc
      _ = ∫ t in b..H,
          (F b * E b - F t * E t + ∫ h in b..t, g h) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ∈ Set.Icc b H := by
              simpa only [Set.uIcc_of_le hbH] using ht
            have hcontT : ContinuousOn F' (Set.Icc b t) :=
              hF'cont.mono (by
                intro x hx
                exact ⟨hx.1, hx.2.trans ht'.2⟩)
            have hcontTU : ContinuousOn F' (Set.uIcc b t) := by
              simpa only [Set.uIcc_of_le ht'.1] using hcontT
            have hflux := ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
              hb ht'.1 (F := F) (F' := F')
              (fun x hx => hF x ⟨hx.1, hx.2.trans ht'.2⟩)
              hcontTU.intervalIntegrable hcontT
            simpa only [E, g] using hflux
      _ = _ := by
        have hFEint : IntervalIntegrable (fun t => F t * E t) volume b H :=
          hEFint.congr (fun t _ => by ring)
        rw [intervalIntegral.integral_add
          (intervalIntegrable_const.sub hFEint) hprimInt,
          intervalIntegral.integral_sub intervalIntegrable_const hFEint,
          intervalIntegral.integral_const,
          integral_integral_eq_endpoint_mul_sub_moment hbH hg]
        have hcomm : (∫ t in b..H, F t * E t) =
            ∫ t in b..H, E t * F t := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        rw [hcomm]
        ring
  let G : ℝ → ℝ := fun h => (H - h) * F h
  let G' : ℝ → ℝ := fun h => (H - h) * F' h - F h
  have hG : ∀ x ∈ Set.Icc b H, HasDerivAt G (G' x) x := by
    intro x hx
    have hlinear : HasDerivAt (fun y : ℝ => H - y) (-1) x :=
      (hasDerivAt_id x).const_sub H
    exact (hlinear.mul (hF x hx)).congr_deriv (by
      dsimp [G']; ring)
  have hG'cont : ContinuousOn G' (Set.Icc b H) := by
    dsimp only [G']
    exact (((continuous_const.sub continuous_id).continuousOn.mul hF'cont).sub hFcont)
  have hG'contU : ContinuousOn G' (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hG'cont
  have hG'int : IntervalIntegrable G' volume b H := hG'contU.intervalIntegrable
  have hfluxG := ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
    hb hbH hG hG'int hG'cont
  have hHgi : IntervalIntegrable (fun h => H * g h) volume b H := hg.const_mul H
  have hhgi : IntervalIntegrable (fun h => h * g h) volume b H := by
    have htmp : IntervalIntegrable (fun h => g h * h) volume b H :=
      hg.mul_continuousOn continuous_id.continuousOn
    exact htmp.congr (fun h _ => by ring)
  have hGflux :
      ccmGuinandWeilPrimePolarWeightedWindow b H G =
        (H - b) * F b * E b -
          (∫ h in b..H, E h * F h) +
            H * (∫ h in b..H, g h) - ∫ h in b..H, h * g h := by
    rw [hfluxG]
    have hEG : (fun h => E h * G' h) =
        (fun h => H * g h - h * g h - E h * F h) := by
      funext h
      dsimp [E, G', g]
      ring
    rw [hEG]
    rw [intervalIntegral.integral_sub (hHgi.sub hhgi) hEFint,
      intervalIntegral.integral_sub hHgi hhgi,
      intervalIntegral.integral_const_mul]
    dsimp [G]
    ring
  simpa only [G] using hQflux.trans hGflux.symm

end

end RHTower
