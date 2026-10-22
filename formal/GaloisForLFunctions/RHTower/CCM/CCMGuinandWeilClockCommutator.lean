import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilWeightedVolterraIdentity

open MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private theorem integral_deriv_mul_primitive
    {b H : ℝ} (hbH : b ≤ H) {m m' g : ℝ → ℝ}
    (hmAC : AbsolutelyContinuousOnInterval m b H)
    (hm : ∀ x ∈ Set.Icc b H, HasDerivAt m (m' x) x)
    (hg : IntervalIntegrable g volume b H) :
    (∫ t in b..H, m' t * (∫ h in b..t, g h)) =
      m H * (∫ h in b..H, g h) - ∫ h in b..H, m h * g h := by
  let A : ℝ → ℝ := fun t => ∫ h in b..t, g h
  have hAac : AbsolutelyContinuousOnInterval A b H :=
    hg.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b H by simp [hbH])
  have hmul := hmAC.integral_mul_deriv_eq_deriv_mul hAac
  have hleft : (∫ t in b..H, m t * deriv A t) =
      ∫ t in b..H, m t * g t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hg.ae_hasDerivAt_integral] with t ht hmem
    have hd : HasDerivAt A (g t) t :=
      ht (uIoc_subset_uIcc hmem) b (by simp [hbH])
    rw [hd.deriv]
  have hright : (∫ t in b..H, deriv m t * A t) =
      ∫ t in b..H, m' t * A t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc b H := by simpa only [Set.uIcc_of_le hbH] using ht
    change deriv m t * A t = m' t * A t
    rw [(hm t ht').deriv]
  have hAb : A b = 0 := by simp [A]
  rw [hleft, hright, hAb, mul_zero, sub_zero] at hmul
  dsimp only [A] at hmul ⊢
  linarith

/-- Multiplying the literal completed prime--polar source by a smooth clock is the
Volterra commutator of that clock with the unclocked cumulative source. -/
theorem ccmPrimePolarWeightedWindow_clockCommutator
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H)
    {F F' m m' : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc b H, HasDerivAt F (F' x) x)
    (hF'cont : ContinuousOn F' (Set.Icc b H))
    (hm : ∀ x ∈ Set.Icc b H, HasDerivAt m (m' x) x)
    (hm'cont : ContinuousOn m' (Set.Icc b H))
    (hmAC : AbsolutelyContinuousOnInterval m b H) :
    ccmGuinandWeilPrimePolarWeightedWindow b H (fun h => m h * F h) =
      m H * ccmGuinandWeilPrimePolarWeightedWindow b H F -
        ∫ t in b..H, m' t * ccmGuinandWeilPrimePolarWeightedWindow b t F := by
  let E := criticalMellinCompletedError
  let g : ℝ → ℝ := fun h => E h * F' h
  let A : ℝ → ℝ := fun t => ∫ h in b..t, g h
  have hFcont : ContinuousOn F (Set.Icc b H) := by
    intro x hx
    exact (hF x hx).continuousAt.continuousWithinAt
  have hmcont : ContinuousOn m (Set.Icc b H) := by
    intro x hx
    exact (hm x hx).continuousAt.continuousWithinAt
  have hF'contU : ContinuousOn F' (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hF'cont
  have hm'contU : ContinuousOn m' (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hm'cont
  have hFcontU : ContinuousOn F (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hFcont
  have hmcontU : ContinuousOn m (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hmcont
  have hEint : IntervalIntegrable E volume b H :=
    intervalIntegrable_criticalMellinCompletedError_on_Icc hbH
  have hg : IntervalIntegrable g volume b H :=
    hEint.mul_continuousOn hF'contU
  have hEFint : IntervalIntegrable (fun t => E t * F t) volume b H :=
    hEint.mul_continuousOn hFcontU
  have hm'gInt : IntervalIntegrable (fun t => m' t * E t * F t) volume b H := by
    have h := hEFint.mul_continuousOn hm'contU
    exact h.congr (fun t _ => by ring)
  have hmgInt : IntervalIntegrable (fun t => m t * g t) volume b H := by
    have h := hg.mul_continuousOn hmcontU
    exact h.congr (fun t _ => by ring)
  have hAac : AbsolutelyContinuousOnInterval A b H :=
    hg.absolutelyContinuousOnInterval_intervalIntegral
      (show b ∈ Set.uIcc b H by simp [hbH])
  have hm'Int : IntervalIntegrable m' volume b H := hm'contU.intervalIntegrable
  have hm'AInt : IntervalIntegrable (fun t => m' t * A t) volume b H :=
    (hAac.continuousOn.intervalIntegrable).mul_continuousOn hm'contU |>.congr
      (fun t _ => by ring)
  have hFTC : (∫ t in b..H, m' t) = m H - m b :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hm x (by simpa only [Set.uIcc_of_le hbH] using hx)) hm'Int
  have hprod : ∀ x ∈ Set.Icc b H,
      HasDerivAt (fun t => m t * F t) (m' x * F x + m x * F' x) x := by
    intro x hx
    exact (hm x hx).mul (hF x hx)
  have hprod'cont : ContinuousOn
      (fun x => m' x * F x + m x * F' x) (Set.Icc b H) :=
    (hm'cont.mul hFcont).add (hmcont.mul hF'cont)
  have hprod'contU : ContinuousOn
      (fun x => m' x * F x + m x * F' x) (Set.uIcc b H) := by
    simpa only [Set.uIcc_of_le hbH] using hprod'cont
  have hfluxF := ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
    hb hbH hF hF'contU.intervalIntegrable hF'cont
  have hfluxMF := ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
    hb hbH hprod
      hprod'contU.intervalIntegrable
      hprod'cont
  have hfluxAll : ∀ t ∈ Set.Icc b H,
      ccmGuinandWeilPrimePolarWeightedWindow b t F =
        F b * E b - F t * E t + A t := by
    intro t ht
    have hF'contT : ContinuousOn F' (Set.Icc b t) :=
      hF'cont.mono (by intro x hx; exact ⟨hx.1, hx.2.trans ht.2⟩)
    have hF'contTU : ContinuousOn F' (Set.uIcc b t) := by
      simpa only [Set.uIcc_of_le ht.1] using hF'contT
    have hflux := ccmGuinandWeilPrimePolarWeightedWindow_eq_completedErrorFlux
      hb ht.1 (F := F) (F' := F')
      (fun x hx => hF x ⟨hx.1, hx.2.trans ht.2⟩)
      hF'contTU.intervalIntegrable
      hF'contT
    simpa only [E, g, A] using hflux
  have hqInt :
      (∫ t in b..H, m' t * ccmGuinandWeilPrimePolarWeightedWindow b t F) =
        F b * E b * (m H - m b) -
          (∫ t in b..H, m' t * E t * F t) +
          m H * (∫ t in b..H, g t) - ∫ t in b..H, m t * g t := by
    calc
      _ = ∫ t in b..H, m' t * (F b * E b - F t * E t + A t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc b H := by simpa only [Set.uIcc_of_le hbH] using ht
        change m' t * ccmGuinandWeilPrimePolarWeightedWindow b t F =
          m' t * (F b * E b - F t * E t + A t)
        rw [hfluxAll t ht']
      _ = _ := by
        have hAterm : IntervalIntegrable (fun t => m' t * A t) volume b H := hm'AInt
        have hconstTerm : IntervalIntegrable
            (fun t => m' t * (F b * E b)) volume b H := hm'Int.mul_const _
        have hdiffTerm : IntervalIntegrable
            (fun t => m' t * (F b * E b - F t * E t)) volume b H := by
          exact (hconstTerm.sub hm'gInt).congr (fun t _ => by ring)
        have hint := integral_deriv_mul_primitive hbH hmAC hm hg
        rw [show (fun t => m' t * (F b * E b - F t * E t + A t)) =
            (fun t => m' t * (F b * E b - F t * E t) + m' t * A t) by
              funext t; ring,
          intervalIntegral.integral_add hdiffTerm hAterm,
          show (fun t => m' t * (F b * E b - F t * E t)) =
            (fun t => (F b * E b) * m' t - m' t * E t * F t) by
              funext t; ring,
          intervalIntegral.integral_sub (hm'Int.const_mul _) hm'gInt,
          intervalIntegral.integral_const_mul, hFTC]
        change (∫ t in b..H, m' t * A t) =
          m H * (∫ t in b..H, g t) - ∫ t in b..H, m t * g t at hint
        rw [hint]
        ring
  have hMFint : IntervalIntegrable
      (fun t => E t * (m' t * F t + m t * F' t)) volume b H := by
    have htmp : ContinuousOn (fun t => m' t * F t + m t * F' t) (Set.uIcc b H) := by
      simpa only [Set.uIcc_of_le hbH] using hprod'cont
    exact hEint.mul_continuousOn htmp
  have hsplit :
      (∫ t in b..H, E t * (m' t * F t + m t * F' t)) =
        (∫ t in b..H, m' t * E t * F t) +
          ∫ t in b..H, m t * g t := by
    have heq : (fun t => E t * (m' t * F t + m t * F' t)) =
        (fun t => m' t * E t * F t + m t * g t) := by
      funext t; dsimp [g]; ring
    rw [heq, intervalIntegral.integral_add hm'gInt hmgInt]
  rw [hfluxMF, hfluxF, hqInt, hsplit]
  dsimp only [g]
  ring

end

end RHTower
