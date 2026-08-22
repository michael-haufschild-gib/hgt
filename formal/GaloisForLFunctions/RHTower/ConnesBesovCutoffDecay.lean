import GaloisForLFunctions.RHTower.ConnesTwoSidedPowerTail

/-!
# §VII (42): `‖ε_Λ η‖_{(1,α,v)} = O(Λ^{-N})`

§VII (42) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

This is the assembly of the four preceding estimates.  Writing `C = C_{α,v}`,

  `C * (ε_Λ η) = ε_Λ · (C * η) + [C, ε_Λ] η`

(`ConnesFracCommutator.connes_fracConv_cutoff_split`), the first summand has `L¹` mass
`O(Λ^{-N})` by (48) and the second is supported in `X_Λ` and bounded there by
`c'_α |x|^{-α} Sup_{|ε| ≤ 1}|η(x+ε)|` by (46), which the thickened Schwartz bound turns into
`c |x|^{-(α+m)}` for every `m`.  The two-sided power tail then contributes `O(Λ^{1-α-m})`.

Both halves are majorised *simultaneously*, by one integrable function, so the argument never
needs measurability of `C * η` itself.
-/

open MeasureTheory Real Set Filter Topology
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The mass of the folded excess majorant. -/
theorem connes_excessMajorant_mass_le {k : ℕ} (hk : 3 ≤ k) {T : ℝ} (hT : 1 < T) :
    (∫ x : ℝ, connesCutoffExcess (Real.log T) x * (1 + |x|) ^ (-(k : ℝ)))
      ≤ 2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2) := by
  have hT0 : (0 : ℝ) < T := lt_trans zero_lt_one hT
  set L : ℝ := Real.log T with hL
  have hLnn : (0 : ℝ) ≤ L := Real.log_nonneg hT.le
  set δ : ℝ := (k : ℝ) - 1 with hδdef
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδ : (0 : ℝ) < δ := by rw [hδdef]; linarith
  have hexp : (-δ - 1 : ℝ) = -(k : ℝ) := by rw [hδdef]; ring
  have hfold : (∫ x : ℝ, connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
      = 2 * ∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s := by
    have hcongr : (fun x : ℝ => connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
        = fun x : ℝ => connesExcessMajorant L k |x| :=
      funext (connes_excess_eq_majorant_abs L k)
    rw [hcongr]
    exact integral_comp_abs (f := connesExcessMajorant L k)
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
  have hpow : ∀ s : ℝ, T < s → (1 + s) ^ (-(k : ℝ)) ≤ s ^ (-(k : ℝ)) := by
    intro s hsT
    have hs0 : (0 : ℝ) < s := lt_trans hT0 hsT
    have hsk : (0 : ℝ) < s ^ ((k : ℝ)) := Real.rpow_pos_of_pos hs0 _
    have h1k : (0 : ℝ) < (1 + s) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hmono : s ^ ((k : ℝ)) ≤ (1 + s) ^ ((k : ℝ)) :=
      Real.rpow_le_rpow hs0.le (by linarith) (by positivity)
    rw [Real.rpow_neg hs0.le, Real.rpow_neg (by linarith), inv_le_inv₀ h1k hsk]
    exact hmono
  have hMTint : IntegrableOn (connesExcessMajorant L k) (Ioi T) volume := by
    refine MeasureTheory.Integrable.mono' hmajT
      ((connesExcessMajorant_measurable L k).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsT : T < s := hs
    have hs0 : (0 : ℝ) < s := lt_trans hT0 hsT
    have habs : |s| = s := abs_of_pos hs0
    have hlogle : Real.log T ≤ Real.log s := Real.log_le_log hT0 hsT.le
    have hnn : (0 : ℝ) ≤ connesExcessMajorant L k s := connesExcessMajorant_nonneg L k s
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, connesExcessMajorant, habs,
      max_eq_left (by rw [hL]; linarith)]
    exact mul_le_mul_of_nonneg_left (hpow s hsT) (by rw [hL]; linarith)
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
    rw [connesExcessMajorant, habs, max_eq_left (by rw [hL]; linarith)]
    exact mul_le_mul_of_nonneg_left (hpow s hsT) (by rw [hL]; linarith)
  have hval : (∫ s in Ioi T, (Real.log s - Real.log T) * s ^ (-(k : ℝ)))
      = T ^ (-δ) / δ ^ 2 := by
    have h := connes_logExcess_tail_powerIntegral hT0 hδ
    rw [hexp] at h
    exact h
  rw [hfold, hδdef] at *
  have hchain : (∫ s in Ioi (0 : ℝ), connesExcessMajorant L k s)
      ≤ T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2 := by
    rw [hsplit]
    exact le_trans hleT (le_of_eq hval)
  linarith

/-- **§VII (46) with the thickened Schwartz bound.**  Beyond radius `2` the commutator is
dominated by a pure power. -/
theorem connes_fracCommutator_power_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (L : ℝ) (η : 𝓢(ℝ, ℂ)) (m : ℕ) {x : ℝ}
    (hx : 2 ≤ |x|) :
    ‖connesFracCommutator α ψ L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ ((∫ y : ℝ, connesLogShiftKernel α y) *
          (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η)) * |x| ^ (-(α + (m : ℝ))) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
    linarith
  have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le (by norm_num) hx
  have hcnn : (0 : ℝ) ≤ ∫ y : ℝ, connesLogShiftKernel α y := by
    refine integral_nonneg fun y => ?_
    rw [connesLogShiftKernel]
    positivity
  have hσ : (0 : ℝ) ≤ (SchwartzMap.seminorm ℂ m 0) η := apply_nonneg _ η
  have h1 := connes_fracCommutator_norm_le hα0 hα1 hψc hψ0 hψ1 hψsupp L η hx0
  have h2 := connesUnitSup_schwartz_le η m hx
  have hxm : (0 : ℝ) < |x| ^ m := pow_pos hxpos m
  have hrpow : |x| ^ (-(α + (m : ℝ))) = |x| ^ (-α) * (|x| ^ m)⁻¹ := by
    rw [show (-(α + (m : ℝ))) = (-α) + (-(m : ℝ)) by ring, Real.rpow_add hxpos,
      Real.rpow_neg hxpos.le (m : ℝ), Real.rpow_natCast]
  calc ‖connesFracCommutator α ψ L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ connesUnitSup ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x *
          ((|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y) := h1
    _ ≤ (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η / |x| ^ m) *
          ((|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y) := by
        refine mul_le_mul_of_nonneg_right h2 ?_
        exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hcnn
    _ = ((∫ y : ℝ, connesLogShiftKernel α y) *
          (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η)) * (|x| ^ (-α) * (|x| ^ m)⁻¹) := by
        field_simp
    _ = ((∫ y : ℝ, connesLogShiftKernel α y) *
          (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η)) * |x| ^ (-(α + (m : ℝ))) := by
        rw [hrpow]

/-- **§VII (42), the explicit bound.** -/
theorem connes_besov_cutoff_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (η : 𝓢(ℝ, ℂ))
    {k m : ℕ} (hk : 3 ≤ k) (hm : 2 ≤ m) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x : ℝ, ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ A * (1 + |x|) ^ (-(k : ℝ)))
    {T : ℝ} (hT : 3 ≤ T) :
    (∫ x : ℝ, ‖connesFracConv α ψ
        (fun y => (connesCutoffExcess (Real.log T) y : ℂ) *
          ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖)
      ≤ A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2))
        + ((∫ y : ℝ, connesLogShiftKernel α y) *
            (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η)) *
          (2 * ((T - 1) ^ (1 - (α + (m : ℝ))) / ((α + (m : ℝ)) - 1))) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) < T := by linarith
  set L : ℝ := Real.log T with hL
  have hLnn : (0 : ℝ) ≤ L := Real.log_nonneg hT1.le
  have hexpL : Real.exp L = T := Real.exp_log hT0
  set R : ℝ := T - 1 with hR
  have hR2 : (2 : ℝ) ≤ R := by rw [hR]; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  set p : ℝ := α + (m : ℝ) with hp
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp1 : (1 : ℝ) < p := by rw [hp]; linarith
  set c : ℝ := (∫ y : ℝ, connesLogShiftKernel α y) *
    (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η) with hc
  have hcnn : (0 : ℝ) ≤ c := by
    have h1 : (0 : ℝ) ≤ ∫ y : ℝ, connesLogShiftKernel α y := by
      refine integral_nonneg fun y => ?_
      rw [connesLogShiftKernel]
      positivity
    have h2 : (0 : ℝ) ≤ (SchwartzMap.seminorm ℂ m 0) η := apply_nonneg _ η
    rw [hc]
    positivity
  set g : ℝ → ℝ := fun x =>
    A * (connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
      + c * Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x with hg
  have hind_int : Integrable
      (Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p))) volume := by
    rw [MeasureTheory.integrable_indicator_iff (connes_absTail_measurableSet R)]
    exact connes_absRpow_tail_integrable hp1 hR0
  have hM_int : Integrable
      (fun x : ℝ => connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) volume :=
    connesExcessMajorant_integrable hLnn hk
  have hgint : Integrable g volume := (hM_int.const_mul A).add (hind_int.const_mul c)
  have hbound : ∀ x : ℝ, x ≠ 0 →
      ‖connesFracConv α ψ
        (fun y => (connesCutoffExcess L y : ℂ) * ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖ ≤ g x := by
    intro x hx
    have hsplit := connes_fracConv_cutoff_split hα0 hα1 hψc hψ0 hψ1 hψsupp L η hx
    have htri : ‖connesFracConv α ψ
        (fun y => (connesCutoffExcess L y : ℂ) * ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖
        ≤ connesCutoffExcess L x *
            ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
          + ‖connesFracCommutator α ψ L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (connesCutoffExcess_nonneg L x)]
    have hfirst : connesCutoffExcess L x *
        ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
        ≤ A * (connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) := by
      have := mul_le_mul_of_nonneg_left (hA x) (connesCutoffExcess_nonneg L x)
      calc connesCutoffExcess L x * ‖connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
          ≤ connesCutoffExcess L x * (A * (1 + |x|) ^ (-(k : ℝ))) := this
        _ = A * (connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ))) := by ring
    have hsecond : ‖connesFracCommutator α ψ L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
        ≤ c * Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x := by
      by_cases hmem : R ≤ |x|
      · have hx2 : (2 : ℝ) ≤ |x| := le_trans hR2 hmem
        rw [Set.indicator_of_mem (show x ∈ {x : ℝ | R ≤ |x|} from hmem)]
        have := connes_fracCommutator_power_le hα0 hα1 hψc hψ0 hψ1 hψsupp L η m hx2
        rwa [← hc, ← hp] at this
      · have hle : |x| ≤ Real.exp L - 1 := by
          rw [hexpL]
          have : |x| < R := not_le.mp hmem
          rw [hR] at this
          linarith
        rw [connes_fracCommutator_eq_zero hψsupp hLnn _ hle,
          Set.indicator_of_notMem (show x ∉ {x : ℝ | R ≤ |x|} from hmem)]
        simp
    show ‖connesFracConv α ψ
        (fun y => (connesCutoffExcess L y : ℂ) * ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖
      ≤ A * (connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
        + c * Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x
    linarith
  have hmono : (∫ x : ℝ, ‖connesFracConv α ψ
      (fun y => (connesCutoffExcess L y : ℂ) * ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖)
      ≤ ∫ x : ℝ, g x := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => norm_nonneg _) hgint ?_
    filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := (0 : ℝ)))] with x hx
    exact hbound x (by simpa using hx)
  have hgval : (∫ x : ℝ, g x)
      = A * (∫ x : ℝ, connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
        + c * ∫ x : ℝ, Set.indicator {x : ℝ | R ≤ |x|} (fun x : ℝ => |x| ^ (-p)) x := by
    rw [hg, MeasureTheory.integral_add (hM_int.const_mul A) (hind_int.const_mul c),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hMbound := connes_excessMajorant_mass_le hk hT1
  have htailval := connes_absRpow_tail_value hp1 hR0
  rw [hgval, htailval] at hmono
  have hstep : A * (∫ x : ℝ, connesCutoffExcess L x * (1 + |x|) ^ (-(k : ℝ)))
      ≤ A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2)) :=
    mul_le_mul_of_nonneg_left hMbound hA0
  linarith

/-- **§VII (42).**  `‖ε_Λ η‖_{(1,α,v)} = O(Λ^{-N})` for every `N`. -/
theorem connes_besov_cutoff_rapidDecay {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (η : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Tendsto (fun T : ℝ => T ^ N *
        ∫ x : ℝ, ‖connesFracConv α ψ
          (fun y => (connesCutoffExcess (Real.log T) y : ℂ) *
            ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖) atTop (𝓝 0) := by
  set k : ℕ := N + 3 with hkdef
  set m : ℕ := N + 2 with hmdef
  obtain ⟨A, hA0, hA⟩ := connes_fracConv_decay hα1 hψ0 hψ1 hψsupp η k
  have hk : 3 ≤ k := by rw [hkdef]; omega
  have hm : 2 ≤ m := by rw [hmdef]; omega
  have hkR : ((k : ℕ) : ℝ) = (N : ℝ) + 3 := by rw [hkdef]; push_cast; ring
  have hmR : ((m : ℕ) : ℝ) = (N : ℝ) + 2 := by rw [hmdef]; push_cast; ring
  set p : ℝ := α + (m : ℝ) with hp
  have hp1 : (1 : ℝ) < p := by rw [hp, hmR]; linarith
  set c : ℝ := (∫ y : ℝ, connesLogShiftKernel α y) *
    (2 ^ m * (SchwartzMap.seminorm ℂ m 0) η) with hc
  have hcnn : (0 : ℝ) ≤ c := by
    have h1 : (0 : ℝ) ≤ ∫ y : ℝ, connesLogShiftKernel α y := by
      refine integral_nonneg fun y => ?_
      rw [connesLogShiftKernel]
      positivity
    have h2 : (0 : ℝ) ≤ (SchwartzMap.seminorm ℂ m 0) η := apply_nonneg _ η
    rw [hc]
    positivity
  -- first limit
  have hlim1 : Tendsto (fun T : ℝ =>
      T ^ N * (A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2)))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun T : ℝ => (2 * A / ((k : ℝ) - 1) ^ 2) * T ^ (-(2 : ℝ)))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun T : ℝ => T ^ (-(2 : ℝ))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by norm_num)
      simpa using h0.const_mul (2 * A / ((k : ℝ) - 1) ^ 2)
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hcomb : (T : ℝ) ^ N * T ^ (-((k : ℝ) - 1)) = T ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast T N, ← Real.rpow_add hT]
      congr 1
      rw [hkR]
      ring
    calc (2 * A / ((k : ℝ) - 1) ^ 2) * T ^ (-(2 : ℝ))
        = (2 * A / ((k : ℝ) - 1) ^ 2) * ((T : ℝ) ^ N * T ^ (-((k : ℝ) - 1))) := by
          rw [hcomb]
      _ = T ^ N * (A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2))) := by ring
  -- second limit
  have hlim2 : Tendsto (fun T : ℝ =>
      (2 * c / (p - 1)) * 2 ^ (p - 1) * T ^ (-(1 + α))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T : ℝ => T ^ (-(1 + α))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    simpa using h0.const_mul ((2 * c / (p - 1)) * 2 ^ (p - 1))
  have hsum := hlim1.add hlim2
  rw [add_zero] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    refine mul_nonneg (by positivity) ?_
    exact integral_nonneg fun x => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hb := connes_besov_cutoff_le hα0 hα1 hψc hψ0 hψ1 hψsupp η hk hm hA0 hA hT
    rw [← hc, ← hp] at hb
    have hstep : T ^ N * ∫ x : ℝ, ‖connesFracConv α ψ
        (fun y => (connesCutoffExcess (Real.log T) y : ℂ) *
          ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x‖
        ≤ T ^ N * (A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2))
          + c * (2 * ((T - 1) ^ (1 - p) / (p - 1)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    refine le_trans hstep ?_
    have htail : (T - 1) ^ (1 - p) ≤ 2 ^ (p - 1) * T ^ (1 - p) := by
      have hhalf : T / 2 ≤ T - 1 := by linarith
      have hq : (0 : ℝ) < p - 1 := by linarith
      have hb1 : (0 : ℝ) < T / 2 := by linarith
      have hb2 : (0 : ℝ) < T - 1 := by linarith
      have hmono : (T / 2) ^ (p - 1) ≤ (T - 1) ^ (p - 1) :=
        Real.rpow_le_rpow hb1.le hhalf hq.le
      have hpos1 : (0 : ℝ) < (T / 2) ^ (p - 1) := Real.rpow_pos_of_pos hb1 _
      have hpos2 : (0 : ℝ) < (T - 1) ^ (p - 1) := Real.rpow_pos_of_pos hb2 _
      have hinv : ((T - 1) ^ (p - 1))⁻¹ ≤ ((T / 2) ^ (p - 1))⁻¹ := by
        rw [inv_le_inv₀ hpos2 hpos1]
        exact hmono
      have hrw1 : (T - 1) ^ (1 - p) = ((T - 1) ^ (p - 1))⁻¹ := by
        rw [show (1 - p : ℝ) = -(p - 1) by ring, Real.rpow_neg hb2.le]
      have hrw2 : ((T / 2) ^ (p - 1))⁻¹ = 2 ^ (p - 1) * T ^ (1 - p) := by
        rw [Real.div_rpow hT0.le (by norm_num : (0:ℝ) ≤ 2),
          show (1 - p : ℝ) = -(p - 1) by ring, Real.rpow_neg hT0.le]
        field_simp
      rw [hrw1, ← hrw2]
      exact hinv
    have hq : (0 : ℝ) < p - 1 := by linarith
    have hcomb : T ^ (1 - p) = T ^ (-(1 + α)) * T ^ (-((N : ℝ))) := by
      rw [← Real.rpow_add hT0]
      congr 1
      rw [hp, hmR]
      ring
    have hTNr : (T : ℝ) ^ N = T ^ ((N : ℝ)) := (Real.rpow_natCast T N).symm
    have hcancel : (T : ℝ) ^ N * T ^ (-((N : ℝ))) = 1 := by
      rw [hTNr, ← Real.rpow_add hT0, add_neg_cancel, Real.rpow_zero]
    have hfin : (T - 1) ^ (1 - p) ≤ 2 ^ (p - 1) * (T ^ (-(1 + α)) * T ^ (-((N : ℝ)))) := by
      rw [← hcomb]; exact htail
    have hcnn' : (0 : ℝ) ≤ 2 * c / (p - 1) := by positivity
    have hTNnn : (0 : ℝ) ≤ (T : ℝ) ^ N := by positivity
    have hcterm : (T : ℝ) ^ N * (c * (2 * ((T - 1) ^ (1 - p) / (p - 1))))
        ≤ (2 * c / (p - 1)) * 2 ^ (p - 1) * T ^ (-(1 + α)) := by
      calc (T : ℝ) ^ N * (c * (2 * ((T - 1) ^ (1 - p) / (p - 1))))
          = (2 * c / (p - 1)) * ((T : ℝ) ^ N * (T - 1) ^ (1 - p)) := by
            field_simp
        _ ≤ (2 * c / (p - 1)) *
              ((T : ℝ) ^ N * (2 ^ (p - 1) * (T ^ (-(1 + α)) * T ^ (-((N : ℝ)))))) := by
            refine mul_le_mul_of_nonneg_left ?_ hcnn'
            exact mul_le_mul_of_nonneg_left hfin hTNnn
        _ = (2 * c / (p - 1)) * 2 ^ (p - 1) * T ^ (-(1 + α)) *
              ((T : ℝ) ^ N * T ^ (-((N : ℝ)))) := by ring
        _ = (2 * c / (p - 1)) * 2 ^ (p - 1) * T ^ (-(1 + α)) := by
            rw [hcancel, mul_one]
    have hdist : (T : ℝ) ^ N * (A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2))
        + c * (2 * ((T - 1) ^ (1 - p) / (p - 1))))
        = (T : ℝ) ^ N * (A * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2)))
          + (T : ℝ) ^ N * (c * (2 * ((T - 1) ^ (1 - p) / (p - 1)))) := by ring
    rw [hdist]
    linarith [hcterm]

end

end GaloisForLFunctions.RHTower
