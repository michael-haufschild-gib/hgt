import GaloisForLFunctions.RHTower.SuzukiCoalescingXiSourceRate

/-!
# The movable Xi carrier and its antipodal blow-up

Normalizing the Xi Donoghue function at the movable anchor `ic` and passing to its Cayley transform
gives a carrier whose reciprocal Cayley quotient is exactly the ratio of the positive-ray Xi
logarithmic derivative at the anchor to the Xi logarithmic derivative at the evaluation point.

Multiplying by the deterministic source factor `z²/c` cancels the anchor and leaves a positive
multiple of the Xi reciprocal logarithmic derivative: the coalescing defect base is compatible with
the surviving two-angle target category.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- `(10)`: the movable Xi Donoghue function, normalized at the anchor `ic`. -/
def suzukiXiMovableDonoghue (c : ℝ) (z : ℂ) : ℂ :=
  Complex.I * logDeriv xi (1 / 2 + (-Complex.I * z)) / (xiRealLogDeriv c : ℂ)

/-- `(10)`: the movable Xi carrier, the Cayley transform of the normalized Donoghue function. -/
def suzukiXiMovableCayley (c : ℝ) (z : ℂ) : ℂ :=
  (suzukiXiMovableDonoghue c z - Complex.I) / (suzukiXiMovableDonoghue c z + Complex.I)

/-- The positive-ray Xi logarithmic derivative is strictly positive. -/
theorem xiRealLogDeriv_pos {c : ℝ} (hc : 0 < c) : 0 < xiRealLogDeriv c := by
  rw [xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hc]
  exact mul_pos hc (re_xiShiftedReciprocalMoment_pos (pow_pos hc 2) (by norm_num))

theorem ofReal_xiRealLogDeriv_ne_zero {c : ℝ} (hc : 0 < c) :
    ((xiRealLogDeriv c : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (xiRealLogDeriv_pos hc).ne'

set_option maxHeartbeats 1000000 in
/-- **`(20)`: the exact Cayley identity.**  The reciprocal Cayley quotient of the movable carrier is
the ratio of the anchor value to the evaluation value of the Xi logarithmic derivative. -/
theorem suzukiXiMovableCayley_quotient {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hL : logDeriv xi (1 / 2 + (-Complex.I * z)) ≠ 0)
    (hsum : logDeriv xi (1 / 2 + (-Complex.I * z)) + ((xiRealLogDeriv c : ℝ) : ℂ) ≠ 0) :
    (1 - suzukiXiMovableCayley c z) / (1 + suzukiXiMovableCayley c z)
      = ((xiRealLogDeriv c : ℝ) : ℂ) / logDeriv xi (1 / 2 + (-Complex.I * z)) := by
  have hLc : ((xiRealLogDeriv c : ℝ) : ℂ) ≠ 0 := ofReal_xiRealLogDeriv_ne_zero hc
  set A : ℂ := logDeriv xi (1 / 2 + (-Complex.I * z)) with hAdef
  set Lc : ℂ := ((xiRealLogDeriv c : ℝ) : ℂ) with hLcdef
  have hmne : Complex.I * A / Lc ≠ 0 :=
    div_ne_zero (mul_ne_zero Complex.I_ne_zero hL) hLc
  have hmI : Complex.I * A / Lc + Complex.I ≠ 0 := by
    intro h
    apply hsum
    have h' : Complex.I * A + Complex.I * Lc = 0 := by
      field_simp at h
      linear_combination h
    have hI : Complex.I * (A + Lc) = 0 := by linear_combination h'
    exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
  have hone_sub : 1 - suzukiXiMovableCayley c z
      = 2 * Complex.I / (Complex.I * A / Lc + Complex.I) := by
    rw [suzukiXiMovableCayley, suzukiXiMovableDonoghue, ← hAdef, ← hLcdef]
    field_simp
    ring
  have hone_add : 1 + suzukiXiMovableCayley c z
      = 2 * (Complex.I * A / Lc) / (Complex.I * A / Lc + Complex.I) := by
    rw [suzukiXiMovableCayley, suzukiXiMovableDonoghue, ← hAdef, ← hLcdef]
    field_simp
    ring
  rw [hone_sub, hone_add]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **`(21)`: the antipodal blow-up retains the Xi meromorphic target.**  The deterministic factor
`z²/c` cancels the anchor and leaves a positive multiple of the Xi reciprocal logarithmic
derivative. -/
theorem tendsto_suzukiXiMovableCayley_blowup {z : ℂ}
    (hL : logDeriv xi (1 / 2 + (-Complex.I * z)) ≠ 0) :
    Tendsto (fun c : ℝ => z ^ 2 / (c : ℂ) *
        ((1 - suzukiXiMovableCayley c z) / (1 + suzukiXiMovableCayley c z)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((normalizedPrimeArchMoment 0 : ℂ) * z ^ 2
        / logDeriv xi (1 / 2 + (-Complex.I * z)))) := by
  have hc2 : Tendsto (fun c : ℝ => c ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun c : ℝ => c ^ 2) 0 := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · exact Filter.Eventually.of_forall fun c => sq_nonneg c
  have hm0 : Tendsto (fun c : ℝ => ((xiShiftedReciprocalMoment (c ^ 2) 0).re : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (normalizedPrimeArchMoment 0)) := by
    have h := (Complex.continuous_re.tendsto (normalizedPrimeArchMoment 0 : ℂ)).comp
      ((tendsto_xiShiftedReciprocalMoment_nhdsGE_zero 0).comp hc2)
    simpa [Function.comp_def] using h
  have hm0C : Tendsto (fun c : ℝ => (((xiShiftedReciprocalMoment (c ^ 2) 0).re : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((normalizedPrimeArchMoment 0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hm0
  -- the anchor value vanishes in the limit
  have hLc0 : Tendsto (fun c : ℝ => ((xiRealLogDeriv c : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun c : ℝ => ((c : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun c : ℝ => ((c : ℝ) : ℂ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ))
      exact h.mono_left nhdsWithin_le_nhds
    have h := hid.mul hm0C
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : (0 : ℝ) < c := hc
    rw [xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hcpos]
    push_cast
    ring
  have hsumev : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      logDeriv xi (1 / 2 + (-Complex.I * z)) + ((xiRealLogDeriv c : ℝ) : ℂ) ≠ 0 := by
    have h : Tendsto (fun c : ℝ =>
        logDeriv xi (1 / 2 + (-Complex.I * z)) + ((xiRealLogDeriv c : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (logDeriv xi (1 / 2 + (-Complex.I * z)))) := by
      have h0 : Tendsto (fun c : ℝ =>
          logDeriv xi (1 / 2 + (-Complex.I * z)) + ((xiRealLogDeriv c : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 (logDeriv xi (1 / 2 + (-Complex.I * z)) + 0)) :=
        tendsto_const_nhds.add hLc0
      rwa [add_zero] at h0
    exact h.eventually (eventually_ne_nhds hL)
  have hlim : Tendsto (fun c : ℝ =>
      (((xiShiftedReciprocalMoment (c ^ 2) 0).re : ℝ) : ℂ) * z ^ 2
        / logDeriv xi (1 / 2 + (-Complex.I * z)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((normalizedPrimeArchMoment 0 : ℂ) * z ^ 2
        / logDeriv xi (1 / 2 + (-Complex.I * z)))) :=
    (hm0C.mul tendsto_const_nhds).div_const _
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hsumev] with c hc hsum
  have hcpos : (0 : ℝ) < c := hc
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  rw [suzukiXiMovableCayley_quotient hcpos hL hsum,
    xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hcpos]
  push_cast
  field_simp

/-- **`(21)` in the card's display.**  The limit is a positive multiple of
`z² ξ(1/2−iz) / ξ'(1/2−iz)`. -/
theorem tendsto_suzukiXiMovableCayley_blowup_ratio {z : ℂ}
    (hxi : xi (1 / 2 + (-Complex.I * z)) ≠ 0)
    (hderiv : deriv xi (1 / 2 + (-Complex.I * z)) ≠ 0) :
    Tendsto (fun c : ℝ => z ^ 2 / (c : ℂ) *
        ((1 - suzukiXiMovableCayley c z) / (1 + suzukiXiMovableCayley c z)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((normalizedPrimeArchMoment 0 : ℂ) * (z ^ 2 * xi (1 / 2 + (-Complex.I * z))
        / deriv xi (1 / 2 + (-Complex.I * z))))) := by
  have hL : logDeriv xi (1 / 2 + (-Complex.I * z)) ≠ 0 := by
    rw [logDeriv_apply]
    exact div_ne_zero hderiv hxi
  have h := tendsto_suzukiXiMovableCayley_blowup hL
  have hval : (normalizedPrimeArchMoment 0 : ℂ) * z ^ 2
      / logDeriv xi (1 / 2 + (-Complex.I * z))
      = (normalizedPrimeArchMoment 0 : ℂ) * (z ^ 2 * xi (1 / 2 + (-Complex.I * z))
        / deriv xi (1 / 2 + (-Complex.I * z))) := by
    rw [logDeriv_apply]
    field_simp
  rwa [hval] at h

end RHTower
