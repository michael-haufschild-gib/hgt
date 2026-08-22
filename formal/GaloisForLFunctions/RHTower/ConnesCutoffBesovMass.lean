import GaloisForLFunctions.RHTower.ConnesFracConvDecay
import GaloisForLFunctions.RHTower.ConnesLogExcessTail
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# §VII (48): the cut-off excess of `C_{α,v} * η` has rapidly decreasing `L¹` mass

§VII (48) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `‖ε_Λ (C_{α,v} * η)‖₁ = O(Λ^{-N})`  for every `N`.

`ConnesLogExcessTail` computed the model integral `∫_T^∞ (log x − log T)x^{-δ-1}dx = T^{-δ}/δ²`;
`ConnesFracConvDecay` showed `‖(C_{α,v}*η)(x)‖ ≤ A_k(1+|x|)^{-k}` for every `k`.  Combining them
gives (48): the logarithmic excess `ε_Λ` costs one power of `|x|`, every further power is free,
and the mass is therefore `O(Λ^{-(k-1)})` for every `k`.

The whole-line integral is folded onto the half line by `integral_comp_abs` — legitimate because
both `ε_Λ` and the majorant depend on `x` only through `|x|`.
-/

open MeasureTheory Real Set Filter Topology
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem connes_cutoffExcess_measurable (L : ℝ) : Measurable (connesCutoffExcess L) := by
  unfold connesCutoffExcess
  exact ((Real.measurable_log.comp measurable_abs).sub measurable_const).max measurable_const

/-- The cut-off excess is dominated by `|x|`: it vanishes on the unit ball, and beyond it `log`
grows more slowly than the identity. -/
theorem connes_cutoffExcess_le_abs {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    connesCutoffExcess L x ≤ |x| := by
  rcases le_or_gt |x| 1 with hx | hx
  · have hlog : Real.log |x| ≤ 0 := by
      rcases eq_or_ne x 0 with hx0 | hx0
      · subst hx0; simp
      · exact Real.log_nonpos (abs_nonneg x) hx
    have hz : connesCutoffExcess L x = 0 := by
      rw [connesCutoffExcess, max_eq_right (by linarith)]
    rw [hz]
    exact abs_nonneg x
  · have hx0 : (0 : ℝ) < |x| := lt_trans zero_lt_one hx
    have hlog : Real.log |x| ≤ |x| - 1 := Real.log_le_sub_one_of_pos hx0
    rw [connesCutoffExcess]
    exact max_le (by linarith) (abs_nonneg x)

/-- Integrability of the logarithmic-excess power kernel on the tail. -/
theorem connes_logExcess_integrableOn {T : ℝ} (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x : ℝ => (Real.log x - Real.log T) * x ^ (-δ - 1)) (Ioi T) volume := by
  have hcomp : IntegrableOn
      (fun u : ℝ => (Real.log (T * u) - Real.log T) * (T * u) ^ (-δ - 1))
      (Ioi (1 : ℝ)) volume := by
    have hbase := _root_.RHTower.integrableOn_rpow_mul_log_Ioi_one hδ
    have hbase' : IntegrableOn
        (fun u : ℝ => T ^ (-δ - 1) * (u ^ (-δ - 1) * Real.log u)) (Ioi (1 : ℝ)) volume :=
      hbase.const_mul (T ^ (-δ - 1))
    refine MeasureTheory.IntegrableOn.congr_fun hbase' ?_ measurableSet_Ioi
    intro u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    have hlog : Real.log (T * u) = Real.log T + Real.log u :=
      Real.log_mul (ne_of_gt hT) (ne_of_gt hu0)
    have hpow : (T * u) ^ (-δ - 1) = T ^ (-δ - 1) * u ^ (-δ - 1) :=
      Real.mul_rpow hT.le hu0.le
    show T ^ (-δ - 1) * (u ^ (-δ - 1) * Real.log u)
      = (Real.log (T * u) - Real.log T) * (T * u) ^ (-δ - 1)
    rw [hlog, hpow]
    ring
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => (Real.log x - Real.log T) * x ^ (-δ - 1)) 1 hT).mp hcomp
  rwa [mul_one] at h

/-- The folded majorant of (48). -/
def connesExcessMajorant (L : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  max (Real.log s - L) 0 * (1 + |s|) ^ (-(k : ℝ))

theorem connesExcessMajorant_nonneg (L : ℝ) (k : ℕ) (s : ℝ) :
    0 ≤ connesExcessMajorant L k s :=
  mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

theorem connesExcessMajorant_measurable (L : ℝ) (k : ℕ) :
    Measurable (connesExcessMajorant L k) := by
  unfold connesExcessMajorant
  refine ((Real.measurable_log.sub measurable_const).max measurable_const).mul ?_
  have hc : Continuous fun s : ℝ => (1 + |s|) ^ (-(k : ℝ)) := by
    refine Continuous.rpow_const (by fun_prop) fun s => Or.inl (by positivity)
  exact hc.measurable

theorem connes_excess_eq_majorant_abs (L : ℝ) (k : ℕ) (x : ℝ) :
    connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)) = connesExcessMajorant L k |x| := by
  rw [connesCutoffExcess, connesExcessMajorant, abs_abs]

theorem connesExcessMajorant_integrable {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (hk : 3 ≤ k) :
    Integrable (fun x : ℝ => connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) volume := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hdom : Integrable (fun s : ℝ => (1 + ‖s‖) ^ (-((k : ℝ) - 1))) volume := by
    refine integrable_one_add_norm (E := ℝ) ?_
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have hmeas : Measurable (fun x : ℝ => connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) := by
    refine (connes_cutoffExcess_measurable L).mul ?_
    have hc : Continuous fun s : ℝ => (1 + |s|) ^ (-(k : ℝ)) := by
      refine Continuous.rpow_const (by fun_prop) fun s => Or.inl (by positivity)
    exact hc.measurable
  refine MeasureTheory.Integrable.mono' hdom hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  have hb : (0 : ℝ) < 1 + |s| := by positivity
  have hnn : (0 : ℝ) ≤ connesCutoffExcess L s * (1 + |s|) ^ (-(k : ℝ)) :=
    mul_nonneg (connesCutoffExcess_nonneg _ _) (Real.rpow_nonneg hb.le _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs]
  have h1 : connesCutoffExcess L s ≤ 1 + |s| := by
    have := connes_cutoffExcess_le_abs hL s
    linarith
  have hpow : (1 + |s|) ^ (-(k : ℝ)) = (1 + |s|) ^ (-((k : ℝ) - 1)) * (1 + |s|)⁻¹ := by
    rw [show (-(k : ℝ)) = (-((k : ℝ) - 1)) + (-1 : ℝ) by ring, Real.rpow_add hb,
      Real.rpow_neg_one]
  rw [hpow]
  calc connesCutoffExcess L s * ((1 + |s|) ^ (-((k : ℝ) - 1)) * (1 + |s|)⁻¹)
      ≤ (1 + |s|) * ((1 + |s|) ^ (-((k : ℝ) - 1)) * (1 + |s|)⁻¹) := by
        refine mul_le_mul_of_nonneg_right h1 ?_
        have : (0 : ℝ) ≤ (1 + |s|) ^ (-((k : ℝ) - 1)) := Real.rpow_nonneg hb.le _
        positivity
    _ = (1 + |s|) ^ (-((k : ℝ) - 1)) := by field_simp

/-- **§VII (48), the explicit bound.** -/
theorem connes_cutoff_besov_mass_le {α : ℝ}
    {ψ : ℝ → ℝ} (η : 𝓢(ℝ, ℂ)) {k : ℕ} (hk : 3 ≤ k) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x : ℝ, ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ A * (1 + |x|) ^ (-(k : ℝ)))
    {T : ℝ} (hT : 1 < T) :
    (∫ x : ℝ, connesCutoffExcess (Real.log T) x *
        ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖)
      ≤ 2 * A * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2) := by
  have hT0 : (0 : ℝ) < T := lt_trans zero_lt_one hT
  set L : ℝ := Real.log T with hL
  have hLnn : (0 : ℝ) ≤ L := Real.log_nonneg hT.le
  set δ : ℝ := (k : ℝ) - 1 with hδdef
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ : (0 : ℝ) < δ := by rw [hδdef]; linarith
  have hexp : (-δ - 1 : ℝ) = -(k : ℝ) := by rw [hδdef]; ring
  have hMint := connesExcessMajorant_integrable hLnn hk (L := L)
  -- step 1
  have hstep1 : (∫ x : ℝ, connesCutoffExcess L x *
      ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖)
      ≤ ∫ x : ℝ, A * (connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (connesCutoffExcess_nonneg _ _) (norm_nonneg _))
      (hMint.const_mul A) (Filter.Eventually.of_forall fun x => ?_)
    have := mul_le_mul_of_nonneg_left (hA x) (connesCutoffExcess_nonneg L x)
    calc connesCutoffExcess L x * ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
        ≤ connesCutoffExcess L x * (A * (1 + |x|) ^ (-(k : ℝ))) := this
      _ = A * (connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) := by ring
  -- step 2: fold
  have hfold : (∫ x : ℝ, connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
      = 2 * ∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s := by
    have hcongr : (fun x : ℝ => connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
        = fun x : ℝ => connesExcessMajorant L k |x| :=
      funext (connes_excess_eq_majorant_abs L k)
    rw [hcongr]
    exact integral_comp_abs (f := connesExcessMajorant L k)
  -- step 3: the half line integral is a tail integral
  have hzero : ∀ s ∈ Ioc (0 : ℝ) T, connesExcessMajorant L k s = 0 := by
    intro s hs
    have hlog : Real.log s ≤ L := by
      rw [hL]
      exact Real.log_le_log hs.1 hs.2
    rw [connesExcessMajorant, max_eq_right (by linarith), zero_mul]
  have hmajT : IntegrableOn
      (fun s : ℝ => (Real.log s - Real.log T) * s ^ (-(k : ℝ))) (Ioi T) volume := by
    have h := connes_logExcess_integrableOn hT0 hδ
    rw [hexp] at h
    exact h
  have hMTint : IntegrableOn (connesExcessMajorant L k) (Ioi T) volume := by
    refine MeasureTheory.Integrable.mono' hmajT
      ((connesExcessMajorant_measurable L k).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsT : T < s := hs
    have hs0 : (0 : ℝ) < s := lt_trans hT0 hsT
    have habs : |s| = s := abs_of_pos hs0
    have hlow : (1 + s) ^ (-(k : ℝ)) ≤ s ^ (-(k : ℝ)) := by
      have hsk : (0 : ℝ) < s ^ ((k : ℝ)) := Real.rpow_pos_of_pos hs0 _
      have h1k : (0 : ℝ) < (1 + s) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
      have hmono : s ^ ((k : ℝ)) ≤ (1 + s) ^ ((k : ℝ)) :=
        Real.rpow_le_rpow hs0.le (by linarith) (by positivity)
      rw [Real.rpow_neg hs0.le, Real.rpow_neg (by linarith), inv_le_inv₀ h1k hsk]
      exact hmono
    have hnn : (0 : ℝ) ≤ connesExcessMajorant L k s := connesExcessMajorant_nonneg L k s
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, connesExcessMajorant, habs,
      max_eq_left (by
        have : Real.log T ≤ Real.log s := Real.log_le_log hT0 hsT.le
        rw [hL]; linarith)]
    exact mul_le_mul_of_nonneg_left hlow (by rw [hL]; linarith [Real.log_le_log hT0 hsT.le])
  have hMOint : IntegrableOn (connesExcessMajorant L k) (Ioc (0 : ℝ) T) volume := by
    refine (integrable_zero ℝ ℝ _).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hzero s hs).symm
  have hsplitAdd : (∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s)
      = (∫ s in Ioc (0 : ℝ) T, connesExcessMajorant L k s)
        + ∫ s in Ioi T, connesExcessMajorant L k s := by
    have hun : Ioi (0 : ℝ) = Ioc (0 : ℝ) T ∪ Ioi T :=
      (Ioc_union_Ioi_eq_Ioi hT0.le).symm
    rw [hun]
    exact MeasureTheory.setIntegral_union
      (Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'))
      (measurableSet_Ioi : MeasurableSet (Ioi T)) hMOint hMTint
  have hsplit : (∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s)
      = ∫ s in Ioi T, connesExcessMajorant L k s := by
    rw [hsplitAdd, setIntegral_congr_fun measurableSet_Ioc (fun s hs => hzero s hs)]
    simp
  have hleT : (∫ s in Ioi T, connesExcessMajorant L k s)
      ≤ ∫ s in Ioi T, (Real.log s - Real.log T) * s ^ (-(k : ℝ)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun s => connesExcessMajorant_nonneg L k s) hmajT ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsT : T < s := hs
    have hs0 : (0 : ℝ) < s := lt_trans hT0 hsT
    have habs : |s| = s := abs_of_pos hs0
    have hlogle : Real.log T ≤ Real.log s := Real.log_le_log hT0 hsT.le
    have hlow : (1 + s) ^ (-(k : ℝ)) ≤ s ^ (-(k : ℝ)) := by
      have hsk : (0 : ℝ) < s ^ ((k : ℝ)) := Real.rpow_pos_of_pos hs0 _
      have hmono : s ^ ((k : ℝ)) ≤ (1 + s) ^ ((k : ℝ)) :=
        Real.rpow_le_rpow hs0.le (by linarith) (by positivity)
      rw [Real.rpow_neg hs0.le, Real.rpow_neg (by linarith)]
      have h1k : (0 : ℝ) < (1 + s) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
      rw [inv_le_inv₀ h1k hsk]
      exact hmono
    rw [connesExcessMajorant, habs, max_eq_left (by rw [hL]; linarith)]
    exact mul_le_mul_of_nonneg_left hlow (by rw [hL]; linarith)
  have hval : (∫ s in Ioi T, (Real.log s - Real.log T) * s ^ (-(k : ℝ)))
      = T ^ (-δ) / δ ^ 2 := by
    have h := connes_logExcess_tail_powerIntegral hT0 hδ
    rw [hexp] at h
    exact h
  rw [MeasureTheory.integral_const_mul, hfold] at hstep1
  have hchain : (∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s) ≤ T ^ (-δ) / δ ^ 2 := by
    rw [hsplit]
    exact le_trans hleT (le_of_eq hval)
  calc (∫ x : ℝ, connesCutoffExcess L x *
        ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖)
      ≤ A * (2 * ∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s) := hstep1
    _ ≤ A * (2 * (T ^ (-δ) / δ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hA0
        linarith
    _ = 2 * A * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2) := by rw [hδdef]; ring

/-- **§VII (48).**  The `L¹` mass of `ε_Λ (C_{α,v} * η)` decays faster than every power of `Λ`. -/
theorem connes_cutoff_besov_mass_rapidDecay {α : ℝ} (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (η : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Tendsto (fun T : ℝ => T ^ N *
        ∫ x : ℝ, connesCutoffExcess (Real.log T) x *
          ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖) atTop (𝓝 0) := by
  set k : ℕ := N + 3 with hk
  obtain ⟨A, hA0, hA⟩ := connes_fracConv_decay hα1 hψ0 hψ1 hψsupp η k
  have hk3 : 3 ≤ k := by rw [hk]; omega
  have hkR : ((k : ℕ) : ℝ) = (N : ℝ) + 3 := by rw [hk]; push_cast; ring
  set δ : ℝ := (k : ℝ) - 1 with hδdef
  have hδ2 : δ = (N : ℝ) + 2 := by rw [hδdef, hkR]; ring
  have hlim : Tendsto (fun T : ℝ => (2 * A / δ ^ 2) * T ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T : ℝ => T ^ (-(2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    simpa using h0.const_mul (2 * A / δ ^ 2)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    refine mul_nonneg (by positivity) ?_
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (connesCutoffExcess_nonneg _ _) (norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := lt_trans zero_lt_one hT
    have hb := connes_cutoff_besov_mass_le η hk3 hA0 hA hT
    have hstep : T ^ N * ∫ x : ℝ, connesCutoffExcess (Real.log T) x *
        ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
        ≤ T ^ N * (2 * A * (T ^ (-δ) / δ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hδdef]
      exact hb
    refine le_trans hstep (le_of_eq ?_)
    have hcomb : (T : ℝ) ^ N * T ^ (-δ) = T ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast T N, ← Real.rpow_add hT0]
      congr 1
      rw [hδ2]
      ring
    calc T ^ N * (2 * A * (T ^ (-δ) / δ ^ 2))
        = (2 * A / δ ^ 2) * ((T : ℝ) ^ N * T ^ (-δ)) := by ring
      _ = (2 * A / δ ^ 2) * T ^ (-(2 : ℝ)) := by rw [hcomb]

end

end GaloisForLFunctions.RHTower
