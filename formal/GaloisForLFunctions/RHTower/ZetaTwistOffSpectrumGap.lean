import GaloisForLFunctions.RHTower.ZetaTwistGapGeometry

/-!
# The shift-spectrum gap is wrong off the spectrum

For the zeta function the factorially normalized shifted standard twists at a real shift `α₀`
have growth constant `1/(2π Δ)`, where `Δ` is the distance from `α₀` to the nearest *other*
singular shift, and the singular shifts are all the integers — including `0`, where the untwisted
series carries the pole of `ζ` (`hadamardLimsup_zetaTwistShift_eq_infDist`).

The shift spectrum `{d (m/q)^{1/d} : a(m) ≠ 0}` of `ζ` is `{1, 2, 3, …}`: it omits `0`.  Hence for
`0 < α₀ < 1/2` the growth constant is `1/(2π α₀)`, while the distance to the shift spectrum is
`1 - α₀`.  The radius law with the gap measured to the shift spectrum alone therefore fails at every
such base point (`zetaTwist_growth_ne_shiftSpectrumGap`).  The correct gap is the distance to the
full singular set of the twist family.
-/

open Complex HurwitzZeta Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The shift spectrum of the zeta function is the set of positive integers, so from a base point
below `1` the distance to the rest of it is the distance to `1`. -/
theorem infDist_shiftSpectrum_oneCoeff {α : ℝ} (h1 : α < 1) :
    Metric.infDist α (shiftSpectrum oneCoeff 1 1 \ {α}) = 1 - α := by
  have hval : ∀ m : ℕ, (1 : ℝ) * ((m : ℝ) / 1) ^ (1 / (1 : ℝ)) = m := fun m => by
    rw [div_one, div_one, Real.rpow_one, one_mul]
  have hmem1 : (1 : ℝ) ∈ shiftSpectrum oneCoeff 1 1 \ {α} := by
    refine ⟨⟨1, one_pos, one_ne_zero, ?_⟩, ?_⟩
    · rw [hval]
      norm_num
    · rw [Set.mem_singleton_iff]
      exact (ne_of_lt h1).symm
  refine le_antisymm ?_ ?_
  · have h := Metric.infDist_le_dist_of_mem (x := α) hmem1
    rwa [Real.dist_eq, abs_of_neg (by linarith), neg_sub] at h
  · refine (Metric.le_infDist ⟨_, hmem1⟩).2 fun β hβ => ?_
    obtain ⟨⟨m, hm, -, rfl⟩, -⟩ := hβ
    rw [hval, Real.dist_eq]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_neg (by linarith)]
    linarith

/-- The zeta twist gap at `-α` for `0 < α < 1/2` is `α`: the nearest singular shift is `0`. -/
theorem twistGap_neg_of_lt_half {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : twistGap (-α) = α := by
  have hfract : Int.fract α = α := Int.fract_eq_self.2 ⟨h0.le, by linarith⟩
  have hne : Int.fract (-α) ≠ 0 := by
    rw [Int.fract_neg (by rw [hfract]; exact h0.ne'), hfract]
    linarith
  rw [twistGap_of_fract_ne_zero hne, Int.fract_neg (by rw [hfract]; exact h0.ne'), hfract,
    sub_sub_cancel]
  exact min_eq_right (by linarith)

/-- **The shift-spectrum radius law fails off the spectrum.**  For the zeta function, every base
point `0 < α₀ < 1/2` and every `s₀` off the natural numbers, the growth constant of the shifted
standard twists `F_{α₀}(s₀ - k)/k!` is *not* `1/(2π dist(α₀, Spec \ {α₀}))`. -/
theorem zetaTwist_growth_ne_shiftSpectrumGap {α₀ : ℝ} (h0 : 0 < α₀) (h1 : α₀ < 1 / 2) {s₀ : ℂ}
    (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) :
    hadamardLimsup (fun k : ℕ => zetaStandardTwist (-α₀) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ)) ≠
      ENNReal.ofReal
        (1 / (2 * Real.pi * Metric.infDist α₀ (shiftSpectrum oneCoeff 1 1 \ {α₀}))) := by
  have hlaw := hadamardLimsup_zetaTwistShift (s₀ := s₀) (-α₀) hs
  rw [twistGap_neg_of_lt_half h0 h1] at hlaw
  change hadamardLimsup (fun k : ℕ =>
    expZeta (((-α₀ : ℝ)) : UnitAddCircle) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ)) ≠ _
  rw [hlaw, infDist_shiftSpectrum_oneCoeff (by linarith)]
  intro h
  have hpi := Real.pi_pos
  have ha : 0 ≤ 1 / (2 * Real.pi * α₀) := by positivity
  have hb : 0 ≤ 1 / (2 * Real.pi * (1 - α₀)) := by
    have : 0 < 1 - α₀ := by linarith
    positivity
  have heq := (ENNReal.ofReal_eq_ofReal_iff ha hb).1 h
  have hne1 : 2 * Real.pi * α₀ ≠ 0 := by positivity
  have hne2 : 2 * Real.pi * (1 - α₀) ≠ 0 := by
    have : 0 < 1 - α₀ := by linarith
    positivity
  rw [div_eq_div_iff hne1 hne2, one_mul, one_mul] at heq
  have : α₀ = 1 - α₀ := by
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    have := mul_left_cancel₀ h2pi (by linarith [heq] : 2 * Real.pi * α₀ = 2 * Real.pi * (1 - α₀))
    exact this
  linarith

/-- The concrete instance: base point `α₀ = 1/10`, critical-line point `s₀ = 1/2`.  The growth
constant is `5/π`, while the shift-spectrum gap `9/10` would predict `5/(9π)`. -/
theorem zetaTwist_growth_ne_shiftSpectrumGap_tenth :
    hadamardLimsup (fun k : ℕ =>
        zetaStandardTwist (-(1 / 10)) ((1 / 2 : ℂ) - (k : ℂ)) / (Nat.factorial k : ℂ)) ≠
      ENNReal.ofReal
        (1 / (2 * Real.pi * Metric.infDist (1 / 10 : ℝ)
          (shiftSpectrum oneCoeff 1 1 \ {1 / 10}))) := by
  refine zetaTwist_growth_ne_shiftSpectrumGap (by norm_num) (by norm_num) fun m hm => ?_
  have h := congrArg Complex.re hm
  simp only [Complex.div_ofNat_re, Complex.one_re, Complex.natCast_re] at h
  have hm' : (m : ℝ) = 1 / 2 := by linarith
  have : (2 : ℝ) * m = 1 := by linarith
  have hnat : 2 * m = 1 := by exact_mod_cast this
  omega

end RHTower
