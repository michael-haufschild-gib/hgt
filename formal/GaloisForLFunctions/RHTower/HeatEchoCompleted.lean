import GaloisForLFunctions.RHTower.HeatEnergyTangent

/-!
# The echo coefficient in completed form

The subleading heat-aperture echo coefficient is one half of the archimedean factor of the
completed zeta function at `1 - s`.  On the critical line this identifies the echo exactly as one
half of the completed amplitude and its conjugate.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

theorem sin_pi_mul_half_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 2) :
    Complex.sin (↑Real.pi * s / 2) ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.sin_ne_zero_iff]
  intro k hcon
  have hre : (↑Real.pi * s / 2 : ℂ).re = ((k : ℂ) * ↑Real.pi).re := by rw [hcon]
  simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im] at hre
  norm_num at hre
  have hk : (k : ℝ) = s.re / 2 := by
    field_simp at hre
    linarith
  have hk2 : (k : ℝ) < 1 := by rw [hk]; linarith
  have hk1 : (0 : ℝ) < (k : ℝ) := by rw [hk]; linarith
  have hkA : k < 1 := by exact_mod_cast hk2
  have hkB : 0 < k := by exact_mod_cast hk1
  omega

/-- Euler's reflection formula in the form used by the echo coefficient. -/
theorem sin_mul_gamma_half {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 2) :
    Complex.sin (↑Real.pi * s / 2) * Complex.Gamma (s / 2)
      * Complex.Gamma (1 - s / 2) = ↑Real.pi := by
  have hz := sin_pi_mul_half_ne_zero h0 h1
  have h := Complex.Gamma_mul_Gamma_one_sub (s / 2)
  rw [show (↑Real.pi * (s / 2) : ℂ) = ↑Real.pi * s / 2 by ring] at h
  have h' : Complex.sin (↑Real.pi * s / 2)
      * (Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2))
      = Complex.sin (↑Real.pi * s / 2)
        * (↑Real.pi / Complex.sin (↑Real.pi * s / 2)) := by rw [h]
  have hcancel : Complex.sin (↑Real.pi * s / 2)
      * (↑Real.pi / Complex.sin (↑Real.pi * s / 2)) = (↑Real.pi : ℂ) := by
    field_simp
  rw [hcancel] at h'
  linear_combination h'

/-- Legendre duplication at `(1-s)/2`. -/
theorem gamma_duplication_one_sub {s : ℂ} :
    Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 - s / 2)
      = Complex.Gamma (1 - s) * (2 : ℂ) ^ s * ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_add_half ((1 - s) / 2)
  rw [show ((1 - s) / 2 + 1 / 2 : ℂ) = 1 - s / 2 by ring,
    show (2 * ((1 - s) / 2) : ℂ) = 1 - s by ring,
    show ((1 : ℂ) - (1 - s)) = s by ring] at h
  exact h

/-- **The completed form `(9a)` of the echo coefficient.** -/
theorem heatEchoC_eq_completed {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 2) :
    heatEchoC s
      = 1 / 2 * ((Real.pi : ℝ) : ℂ) ^ ((s - 1) / 2) * Complex.Gamma ((1 - s) / 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hr : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpi).ne'
  have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ)
      = ((Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpi.le]
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have hT : (2 : ℂ) ^ ((s - 1) / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2ne)
  have hGm : Complex.Gamma (1 - s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hcon
    have hre : (1 - s / 2 : ℂ).re = -(m : ℝ) := by rw [hcon]; simp
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re] at hre
    norm_num at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have h4 : ((((4 * Real.pi : ℝ)) : ℂ)) ^ ((s - 1) / 2)
      = (2 : ℂ) ^ ((s - 1) / 2) * (2 : ℂ) ^ ((s - 1) / 2)
        * ((Real.pi : ℝ) : ℂ) ^ ((s - 1) / 2) := by
    have hsplit : ((((4 * Real.pi : ℝ)) : ℂ)) = (((4 : ℝ)) : ℂ) * ((Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    have hfour : (((4 : ℝ)) : ℂ) = (((2 : ℝ)) : ℂ) * (((2 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hsplit, Complex.mul_cpow_ofReal_nonneg (by norm_num) hpi.le, hfour,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num)]
    norm_num
  have h2s : (2 : ℂ) ^ s = (2 : ℂ) ^ ((s - 1) / 2) * (2 : ℂ) ^ ((s - 1) / 2) * 2 := by
    have e1 : (2 : ℂ) ^ ((s - 1) / 2) * (2 : ℂ) ^ ((s - 1) / 2) = (2 : ℂ) ^ (s - 1) := by
      rw [← Complex.cpow_add _ _ h2ne]
      congr 1
      ring
    have e2 : (2 : ℂ) ^ (s - 1) * 2 = (2 : ℂ) ^ s := by
      have e3 : (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (1 : ℂ) = (2 : ℂ) ^ (s - 1 + 1) :=
        (Complex.cpow_add _ _ h2ne).symm
      rw [Complex.cpow_one] at e3
      rw [e3]
      congr 1
      ring
    rw [e1, e2]
  have hGam : Complex.Gamma (1 - s)
      = Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 - s / 2)
        / ((2 : ℂ) ^ s * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
    rw [gamma_duplication_one_sub]
    field_simp
  have hrefl := sin_mul_gamma_half h0 h1
  rw [heatEchoC, show ((s - 1 + 1) / 2 : ℂ) = s / 2 by ring, hGam, h4, h2s]
  rw [show ((1 : ℂ) - s / 2) = (2 - s) / 2 by ring,
    show (↑Real.pi * s / 2 : ℂ) = s * ↑Real.pi / 2 by ring] at hrefl ⊢
  field_simp
  linear_combination Complex.Gamma ((1 - s) / 2) * hrefl
    - Complex.Gamma ((1 - s) / 2) * hsq

/-- **The critical-line identification `(11a)`.**  On `Re s = 1/2` the conjugate echo coefficient
is exactly one half of the archimedean factor of the completed zeta function at `s`. -/
theorem conj_heatEchoC_of_critical {s : ℂ} (hc : s.re = 1 / 2) :
    (starRingEnd ℂ) (heatEchoC s)
      = 1 / 2 * ((Real.pi : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
  have h0 : (0 : ℝ) < s.re := by rw [hc]; norm_num
  have h1 : s.re < 2 := by rw [hc]; norm_num
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    refine Complex.ext ?_ ?_
    · rw [Complex.conj_re, Complex.sub_re, Complex.one_re, hc]
      norm_num
    · rw [Complex.conj_im, Complex.sub_im, Complex.one_im]
      ring
  have harg : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact ne_of_lt Real.pi_pos
  have hcpow : (starRingEnd ℂ) (((Real.pi : ℝ) : ℂ) ^ ((s - 1) / 2))
      = ((Real.pi : ℝ) : ℂ) ^ (-s / 2) := by
    have h := Complex.cpow_conj ((Real.pi : ℝ) : ℂ) ((s - 1) / 2) harg
    rw [Complex.conj_ofReal] at h
    rw [← h, map_div₀, map_sub, map_one, hconj, map_ofNat]
    congr 1
    ring
  rw [heatEchoC_eq_completed h0 h1, map_mul, map_mul, hcpow, ← Complex.Gamma_conj,
    show (starRingEnd ℂ) ((1 - s) / 2) = s / 2 by
      rw [map_div₀, map_sub, map_one, hconj, map_ofNat]
      ring,
    map_div₀, map_one, map_ofNat]

/-- **The polyhomogeneous finite part `(12)`.**  Removing the four nonzero-power channels of `(7)`
leaves exactly the completed intensity `|ζ(s)|²`. -/
theorem tendsto_heatEnergy_finitePart {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    Tendsto (fun x : ℝ => heatEnergy s x
        - (heatEnergyPrincipal s x - ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ)) := by
  have h := (tendsto_heatEnergy_sub_principal h0 h1).add_const
    (((‖riemannZeta s‖ ^ 2 : ℝ) : ℂ))
  rw [zero_add] at h
  refine h.congr fun x => ?_
  ring

end RHTower
