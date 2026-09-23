import GaloisForLFunctions.HTGeometry.HillBoundsTwoSided

/-!
# The fundamental pair of the Hill equation, and its propagator

The two canonical solutions — position one with velocity zero, and position zero with velocity one —
form a fundamental pair. Their Wronskian is constant along the equation and equals one at the initial
time, hence everywhere; and the propagator from one time to another,

`P(t,s) = S(t)C(s) - C(t)S(s)`,

is the combination a Duhamel formula needs: it is separated in the two time variables, it vanishes at
`t = s`, and its `t`-derivative there is the Wronskian.

For the massive frequency both members carry the bounds of the energy estimate, uniformly in the
spatial frequency: the cosine costs nothing, the sine gains one power of the frequency.
-/

namespace GaloisForLFunctions.HTGeometry

section Generic

variable {ω dω : ℝ → ℝ} {M : ℝ}

/-- The member of the fundamental pair with datum `(1, 0)`. -/
noncomputable def hillCos (ω : ℝ → ℝ) : ℝ → ℝ := hillSolution ω (1, 0)

/-- Its velocity. -/
noncomputable def hillCosDeriv (ω : ℝ → ℝ) : ℝ → ℝ := hillSolutionDeriv ω (1, 0)

/-- The member of the fundamental pair with datum `(0, 1)`. -/
noncomputable def hillSin (ω : ℝ → ℝ) : ℝ → ℝ := hillSolution ω (0, 1)

/-- Its velocity. -/
noncomputable def hillSinDeriv (ω : ℝ → ℝ) : ℝ → ℝ := hillSolutionDeriv ω (0, 1)

theorem hasDerivAt_hillCos (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (t : ℝ) :
    HasDerivAt (hillCos ω) (hillCosDeriv ω t) t :=
  hasDerivAt_hillSolution hω hM1 hM (1, 0) t

theorem hasDerivAt_hillCosDeriv (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (t : ℝ) : HasDerivAt (hillCosDeriv ω) (-(ω t ^ (2 : ℕ)) * hillCos ω t) t :=
  hasDerivAt_hillSolutionDeriv hω hM1 hM (1, 0) t

theorem hasDerivAt_hillSin (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (t : ℝ) :
    HasDerivAt (hillSin ω) (hillSinDeriv ω t) t :=
  hasDerivAt_hillSolution hω hM1 hM (0, 1) t

theorem hasDerivAt_hillSinDeriv (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (t : ℝ) : HasDerivAt (hillSinDeriv ω) (-(ω t ^ (2 : ℕ)) * hillSin ω t) t :=
  hasDerivAt_hillSolutionDeriv hω hM1 hM (0, 1) t

theorem continuous_hillCos (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    Continuous (hillCos ω) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_hillCos hω hM1 hM t).continuousAt

theorem continuous_hillSin (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    Continuous (hillSin ω) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_hillSin hω hM1 hM t).continuousAt

theorem hillCos_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    hillCos ω 0 = 1 := hillSolution_zero hω hM1 hM (1, 0)

theorem hillCosDeriv_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    hillCosDeriv ω 0 = 0 := hillSolutionDeriv_zero hω hM1 hM (1, 0)

theorem hillSin_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    hillSin ω 0 = 0 := hillSolution_zero hω hM1 hM (0, 1)

theorem hillSinDeriv_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    hillSinDeriv ω 0 = 1 := hillSolutionDeriv_zero hω hM1 hM (0, 1)

/-! ## The Wronskian -/

/-- A real function with vanishing derivative everywhere is constant. -/
theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} (h : ∀ x : ℝ, HasDerivAt f 0 x) (a b : ℝ) :
    f a = f b := by
  refine is_const_of_fderiv_eq_zero (fun x => (h x).differentiableAt) (fun x => ?_) a b
  have hx := (h x).hasFDerivAt.fderiv
  rw [hx]
  ext
  simp

/-- **The Wronskian of the fundamental pair is one.** -/
theorem hillWronskian_eq_one (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (t : ℝ) :
    hillCos ω t * hillSinDeriv ω t - hillSin ω t * hillCosDeriv ω t = 1 := by
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun q : ℝ => hillCos ω q * hillSinDeriv ω q - hillSin ω q * hillCosDeriv ω q)
        0 r := by
    intro r
    have hC := hasDerivAt_hillCos hω hM1 hM r
    have hC' := hasDerivAt_hillCosDeriv hω hM1 hM r
    have hS := hasDerivAt_hillSin hω hM1 hM r
    have hS' := hasDerivAt_hillSinDeriv hω hM1 hM r
    have hmain := (hC.mul hS').sub (hS.mul hC')
    refine hmain.congr_deriv ?_
    ring
  have hconst := const_of_hasDerivAt_zero hderiv t 0
  rw [hconst, hillCos_zero hω hM1 hM, hillSinDeriv_zero hω hM1 hM, hillSin_zero hω hM1 hM,
    hillCosDeriv_zero hω hM1 hM]
  ring

/-! ## The propagator -/

/-- The propagator of the equation from `s` to `t`. -/
noncomputable def hillProp (ω : ℝ → ℝ) (t s : ℝ) : ℝ :=
  hillSin ω t * hillCos ω s - hillCos ω t * hillSin ω s

theorem hillProp_self (ω : ℝ → ℝ) (t : ℝ) : hillProp ω t t = 0 := by
  rw [hillProp]
  ring

theorem hillProp_zero_right (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) (t : ℝ) :
    hillProp ω t 0 = hillSin ω t := by
  rw [hillProp, hillCos_zero hω hM1 hM, hillSin_zero hω hM1 hM]
  ring

end Generic

/-! ## The massive pair -/

section Massive

variable {c dc : ℝ → ℝ} {m K C S s : ℝ}

/-- **The sine member gains one power of the frequency**, uniformly in it. -/
theorem mul_abs_hillSin_massive_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (t : ℝ) :
    massiveFreq m c s t * |hillSin (massiveFreq m c s) t| ≤ Real.exp (K * |t|) := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c s r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc s
  have hsplit := mul_abs_le_sqrt_hillEnergy
    (ω := massiveFreq m c s) (u := hillSolution (massiveFreq m c s) (0, 1))
    (du := hillSolutionDeriv (massiveFreq m c s) (0, 1))
    (fun r => massiveFreq_pos hm c s r) t
  have hsqrt := sqrt_hillEnergy_le_abs (fun r => hasDerivAt_massiveFreq hm hcd s r)
    (hasDerivAt_hillSolution hcont hM1 hMb (0, 1))
    (hasDerivAt_hillSolutionDeriv hcont hM1 hMb (0, 1))
    (fun r => hillEquation (massiveFreq m c s) (0, 1) r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) t
  rw [hillEnergy_sin_zero hcont hM1 hMb, Real.sqrt_one, one_mul] at hsqrt
  exact hsplit.trans hsqrt

/-- **Its velocity is bounded, uniformly in the frequency.** -/
theorem abs_hillSinDeriv_massive_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (t : ℝ) :
    |hillSinDeriv (massiveFreq m c s) t| ≤ Real.exp (K * |t|) := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c s r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc s
  have hsplit := abs_deriv_le_sqrt_hillEnergy
    (ω := massiveFreq m c s) (u := hillSolution (massiveFreq m c s) (0, 1))
    (du := hillSolutionDeriv (massiveFreq m c s) (0, 1)) t
  have hsqrt := sqrt_hillEnergy_le_abs (fun r => hasDerivAt_massiveFreq hm hcd s r)
    (hasDerivAt_hillSolution hcont hM1 hMb (0, 1))
    (hasDerivAt_hillSolutionDeriv hcont hM1 hMb (0, 1))
    (fun r => hillEquation (massiveFreq m c s) (0, 1) r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) t
  rw [hillEnergy_sin_zero hcont hM1 hMb, Real.sqrt_one, one_mul] at hsqrt
  exact hsplit.trans hsqrt

/-- **The sine member itself**, bounded by the reciprocal of the frequency. -/
theorem abs_hillSin_massive_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (t : ℝ) :
    |hillSin (massiveFreq m c s) t| ≤ (massiveFreq m c s t)⁻¹ * Real.exp (K * |t|) := by
  have hpos := massiveFreq_pos hm c s t
  have hmain := mul_abs_hillSin_massive_le hm hc hcd hcpos hK hC hs (S := S) t
  rw [← le_div_iff₀' hpos] at hmain
  refine hmain.trans_eq ?_
  rw [div_eq_inv_mul]

/-- **The cosine member**, bounded by the ratio of the speeds. -/
theorem abs_hillCos_massive_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (t : ℝ) :
    |hillCos (massiveFreq m c s) t| ≤ max 1 (c 0 / c t) * Real.exp (K * |t|) :=
  abs_hillSolution_massive_le_abs (S := S) hm hc hcd hcpos hK hC hs t

/-- **Its velocity costs one power of the frequency.** -/
theorem abs_hillCosDeriv_massive_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (t : ℝ) :
    |hillCosDeriv (massiveFreq m c s) t| ≤ massiveFreq m c s 0 * Real.exp (K * |t|) :=
  abs_hillSolutionDeriv_massive_le_abs (S := S) hm hc hcd hcpos hK hC hs t

end Massive

end GaloisForLFunctions.HTGeometry
