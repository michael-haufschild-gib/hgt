import GaloisForLFunctions.HTGeometry.HillFundamentalPair
import GaloisForLFunctions.HTGeometry.HillFlowTwoSidedStability
import GaloisForLFunctions.HTGeometry.KleinGordonSymbol

/-!
# The propagator of the massive Hill fibre, as a symbol in the frequency

The Duhamel formula of the driven evolution multiplies the source by the propagator of the free
fibre. Read as a function of the spatial frequency it is a *symbol*: bounded on every window of
times, continuous in the frequency, and — this is what the Banach-space formulation needs —
Lipschitz in each time variable with a constant that does not see the frequency.

Both statements come from the same two facts: the sine member of the fundamental pair gains one power
of the frequency, and the ratio of the frequency at two times is the ratio of the speeds. The mass
and the spatial frequency cancel out of every bound.
-/

namespace GaloisForLFunctions.HTGeometry

section Symbol

variable {E : Type*} [NormedAddCommGroup E]
variable {m K C cmin : ℝ} {c dc : ℝ → ℝ}

/-- The propagator of the fibre at frequency `ξ`, from `s` to `t`. -/
noncomputable def hillPropSymbol (m : ℝ) (c : ℝ → ℝ) (t s : ℝ) (ξ : E) : ℝ :=
  hillProp (massiveFreq m c ‖ξ‖) t s

/-- Its derivative in the first time. -/
noncomputable def hillPropSymbolTimeDeriv (m : ℝ) (c : ℝ → ℝ) (t s : ℝ) (ξ : E) : ℝ :=
  hillSinDeriv (massiveFreq m c ‖ξ‖) t * hillCos (massiveFreq m c ‖ξ‖) s -
    hillCosDeriv (massiveFreq m c ‖ξ‖) t * hillSin (massiveFreq m c ‖ξ‖) s

/-- Its derivative in the second time. -/
noncomputable def hillPropSymbolBaseDeriv (m : ℝ) (c : ℝ → ℝ) (t s : ℝ) (ξ : E) : ℝ :=
  hillSin (massiveFreq m c ‖ξ‖) t * hillCosDeriv (massiveFreq m c ‖ξ‖) s -
    hillCos (massiveFreq m c ‖ξ‖) t * hillSinDeriv (massiveFreq m c ‖ξ‖) s

/-- The damped free symbol: the cosine member, divided by the initial frequency. -/
noncomputable def hillCoscSymbol (m : ℝ) (c : ℝ → ℝ) (t : ℝ) (ξ : E) : ℝ :=
  hillCos (massiveFreq m c ‖ξ‖) t / massiveFreq m c ‖ξ‖ 0

/-- Its time derivative. -/
noncomputable def hillCoscSymbolDeriv (m : ℝ) (c : ℝ → ℝ) (t : ℝ) (ξ : E) : ℝ :=
  hillCosDeriv (massiveFreq m c ‖ξ‖) t / massiveFreq m c ‖ξ‖ 0

/-! ## The size of the fibre -/

/-- The speed ratio that controls every bound. -/
noncomputable def hillSpeedRatio (c : ℝ → ℝ) (cmin : ℝ) : ℝ := max 1 (c 0 / cmin)

theorem one_le_hillSpeedRatio (c : ℝ → ℝ) (cmin : ℝ) : 1 ≤ hillSpeedRatio c cmin :=
  le_max_left _ _

theorem hillSpeedRatio_nonneg (c : ℝ → ℝ) (cmin : ℝ) : 0 ≤ hillSpeedRatio c cmin :=
  le_trans zero_le_one (one_le_hillSpeedRatio c cmin)

theorem max_le_hillSpeedRatio (hcmin : 0 < cmin) (hcpos : ∀ r, 0 < c r) (hclow : ∀ r, cmin ≤ c r)
    (t : ℝ) : max 1 (c 0 / c t) ≤ hillSpeedRatio c cmin :=
  max_le_max le_rfl (div_le_div_of_nonneg_left (le_of_lt (hcpos 0)) hcmin (hclow t))

theorem abs_hillCos_le_ratio (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (t : ℝ) (ξ : E) :
    |hillCos (massiveFreq m c ‖ξ‖) t| ≤ hillSpeedRatio c cmin * Real.exp (K * |t|) := by
  refine (abs_hillCos_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t).trans ?_
  exact mul_le_mul_of_nonneg_right (max_le_hillSpeedRatio hcmin hcpos hclow t)
    (le_of_lt (Real.exp_pos _))

theorem abs_hillSin_le_inv (hm : 0 < m) (hc : Continuous c) (hcd : ∀ t, HasDerivAt c (dc t) t)
    (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t) (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t : ℝ)
    (ξ : E) : |hillSin (massiveFreq m c ‖ξ‖) t| ≤ m⁻¹ * Real.exp (K * |t|) := by
  refine (abs_hillSin_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t).trans ?_
  have hpos := massiveFreq_pos hm c ‖ξ‖ t
  have hle : m ≤ massiveFreq m c ‖ξ‖ t := by
    have hsq : m ^ 2 ≤ massiveFreq m c ‖ξ‖ t ^ 2 := by
      rw [massiveFreq_sq hm]
      nlinarith [sq_nonneg (c t * ‖ξ‖)]
    nlinarith [le_of_lt hpos, le_of_lt hm]
  have hinv : (massiveFreq m c ‖ξ‖ t)⁻¹ ≤ m⁻¹ := inv_anti₀ hm hle
  exact mul_le_mul_of_nonneg_right hinv (le_of_lt (Real.exp_pos _))

/-- **The cosine velocity, measured against the sine, is a speed ratio.** -/
theorem abs_hillCosDeriv_mul_abs_hillSin_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (t s : ℝ) (ξ : E) :
    |hillCosDeriv (massiveFreq m c ‖ξ‖) t| * |hillSin (massiveFreq m c ‖ξ‖) s| ≤
      hillSpeedRatio c cmin * (Real.exp (K * |t|) * Real.exp (K * |s|)) := by
  have hspos := massiveFreq_pos hm c ‖ξ‖ s
  have h1 := abs_hillCosDeriv_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t
  have h2 := mul_abs_hillSin_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl s
  have hratio := massiveFreq_le_mul (m := m) hcpos ‖ξ‖ s
  have hEt : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  have hEs : (0 : ℝ) ≤ Real.exp (K * |s|) := le_of_lt (Real.exp_pos _)
  have hstep : |hillCosDeriv (massiveFreq m c ‖ξ‖) t| * |hillSin (massiveFreq m c ‖ξ‖) s| ≤
      (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)) *
        |hillSin (massiveFreq m c ‖ξ‖) s| :=
    mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  refine hstep.trans ?_
  have hsin : massiveFreq m c ‖ξ‖ s * |hillSin (massiveFreq m c ‖ξ‖) s| ≤ Real.exp (K * |s|) := h2
  have hmain : (massiveFreq m c ‖ξ‖ 0 * Real.exp (K * |t|)) * |hillSin (massiveFreq m c ‖ξ‖) s| ≤
      (max 1 (c 0 / c s) * massiveFreq m c ‖ξ‖ s * Real.exp (K * |t|)) *
        |hillSin (massiveFreq m c ‖ξ‖) s| := by
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right hratio hEt
  refine hmain.trans ?_
  have hrewrite : (max 1 (c 0 / c s) * massiveFreq m c ‖ξ‖ s * Real.exp (K * |t|)) *
      |hillSin (massiveFreq m c ‖ξ‖) s|
      = (max 1 (c 0 / c s) * Real.exp (K * |t|)) *
        (massiveFreq m c ‖ξ‖ s * |hillSin (massiveFreq m c ‖ξ‖) s|) := by ring
  rw [hrewrite]
  have hfac : (0 : ℝ) ≤ max 1 (c 0 / c s) * Real.exp (K * |t|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hEt
  refine le_trans (mul_le_mul_of_nonneg_left hsin hfac) ?_
  have hratio' : max 1 (c 0 / c s) ≤ hillSpeedRatio c cmin :=
    max_le_hillSpeedRatio hcmin hcpos hclow s
  have hstep2 : (max 1 (c 0 / c s) * Real.exp (K * |t|)) * Real.exp (K * |s|)
      ≤ (hillSpeedRatio c cmin * Real.exp (K * |t|)) * Real.exp (K * |s|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hratio' hEt) hEs
  refine hstep2.trans_eq ?_
  ring

/-! ## The bounds -/

/-- **The propagator symbol is bounded on every window of times, uniformly in the frequency.** -/
theorem abs_hillPropSymbol_le (hm : 0 < m) (hc : Continuous c) (hcd : ∀ t, HasDerivAt c (dc t) t)
    (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (t s : ℝ) (ξ : E) :
    |hillPropSymbol m c t s ξ| ≤
      2 * (hillSpeedRatio c cmin * m⁻¹) * (Real.exp (K * |t|) * Real.exp (K * |s|)) := by
  have hEt : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  have hEs : (0 : ℝ) ≤ Real.exp (K * |s|) := le_of_lt (Real.exp_pos _)
  have hSt := abs_hillSin_le_inv (C := C) hm hc hcd hcpos hK hC t ξ
  have hSs := abs_hillSin_le_inv (C := C) hm hc hcd hcpos hK hC s ξ
  have hCt := abs_hillCos_le_ratio (C := C) hm hc hcd hcpos hK hC hcmin hclow t ξ
  have hCs := abs_hillCos_le_ratio (C := C) hm hc hcd hcpos hK hC hcmin hclow s ξ
  have hterm1 : |hillSin (massiveFreq m c ‖ξ‖) t| * |hillCos (massiveFreq m c ‖ξ‖) s| ≤
      (m⁻¹ * Real.exp (K * |t|)) * (hillSpeedRatio c cmin * Real.exp (K * |s|)) :=
    mul_le_mul hSt hCs (abs_nonneg _) (mul_nonneg (le_of_lt (inv_pos.mpr hm)) hEt)
  have hterm2 : |hillCos (massiveFreq m c ‖ξ‖) t| * |hillSin (massiveFreq m c ‖ξ‖) s| ≤
      (hillSpeedRatio c cmin * Real.exp (K * |t|)) * (m⁻¹ * Real.exp (K * |s|)) :=
    mul_le_mul hCt hSs (abs_nonneg _) (mul_nonneg (hillSpeedRatio_nonneg c cmin) hEt)
  have hsplit : |hillPropSymbol m c t s ξ| ≤
      |hillSin (massiveFreq m c ‖ξ‖) t| * |hillCos (massiveFreq m c ‖ξ‖) s| +
        |hillCos (massiveFreq m c ‖ξ‖) t| * |hillSin (massiveFreq m c ‖ξ‖) s| := by
    rw [hillPropSymbol, hillProp]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
  refine hsplit.trans ?_
  have hsum := add_le_add hterm1 hterm2
  refine hsum.trans_eq ?_
  ring

/-- **The damped free symbol is bounded on every window of times.** -/
theorem abs_hillCoscSymbol_le (hm : 0 < m) (hc : Continuous c) (hcd : ∀ t, HasDerivAt c (dc t) t)
    (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (t : ℝ) (ξ : E) :
    |hillCoscSymbol m c t ξ| ≤ hillSpeedRatio c cmin * m⁻¹ * Real.exp (K * |t|) := by
  have hpos := massiveFreq_pos hm c ‖ξ‖ 0
  have hCt := abs_hillCos_le_ratio (C := C) hm hc hcd hcpos hK hC hcmin hclow t ξ
  have hle : m ≤ massiveFreq m c ‖ξ‖ 0 := by
    have hsq : m ^ 2 ≤ massiveFreq m c ‖ξ‖ 0 ^ 2 := by
      rw [massiveFreq_sq hm]
      nlinarith [sq_nonneg (c 0 * ‖ξ‖)]
    nlinarith [le_of_lt hpos, le_of_lt hm]
  have hinv : (massiveFreq m c ‖ξ‖ 0)⁻¹ ≤ m⁻¹ := inv_anti₀ hm hle
  rw [hillCoscSymbol, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hstep : |hillCos (massiveFreq m c ‖ξ‖) t| ≤
      hillSpeedRatio c cmin * m⁻¹ * Real.exp (K * |t|) * massiveFreq m c ‖ξ‖ 0 := by
    refine hCt.trans ?_
    have hm' : m * m⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hm)
    have hkey : m ≤ massiveFreq m c ‖ξ‖ 0 := hle
    have hE : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
    have hR : (0 : ℝ) ≤ hillSpeedRatio c cmin := hillSpeedRatio_nonneg c cmin
    have hinvpos : (0 : ℝ) < m⁻¹ := inv_pos.mpr hm
    nlinarith [mul_nonneg hR hE, mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg hR hE)
      (le_of_lt hinvpos))]
  exact hstep


/-! ## The derivatives in the two times -/

theorem hasDerivAt_hillPropSymbol_time (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (s : ℝ) (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => hillPropSymbol m c r s ξ)
      (hillPropSymbolTimeDeriv m c t s ξ) t := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc ‖ξ‖
  have hS := (hasDerivAt_hillSin hcont hM1 hMb t).mul_const (hillCos (massiveFreq m c ‖ξ‖) s)
  have hCd := (hasDerivAt_hillCos hcont hM1 hMb t).mul_const (hillSin (massiveFreq m c ‖ξ‖) s)
  exact hS.sub hCd

theorem hasDerivAt_hillPropSymbol_base (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t : ℝ) (ξ : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => hillPropSymbol m c t r ξ)
      (hillPropSymbolBaseDeriv m c t s ξ) s := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc ‖ξ‖
  have hC' := (hasDerivAt_hillCos hcont hM1 hMb s).const_mul (hillSin (massiveFreq m c ‖ξ‖) t)
  have hS' := (hasDerivAt_hillSin hcont hM1 hMb s).const_mul (hillCos (massiveFreq m c ‖ξ‖) t)
  exact hC'.sub hS'

theorem hasDerivAt_hillCoscSymbol (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (ξ : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => hillCoscSymbol m c r ξ) (hillCoscSymbolDeriv m c t ξ) t := by
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c ‖ξ‖ r ^ 2 ≤ max 1 (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) := fun r =>
    (massiveFreq_sq_le hm hC le_rfl r).trans (le_max_right _ _)
  have hcont := continuous_massiveFreq (m := m) hc ‖ξ‖
  exact (hasDerivAt_hillCos hcont hM1 hMb t).div_const (massiveFreq m c ‖ξ‖ 0)

/-! ## The bounds on the derivatives -/

theorem abs_hillPropSymbolTimeDeriv_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (t s : ℝ) (ξ : E) :
    |hillPropSymbolTimeDeriv m c t s ξ| ≤
      2 * hillSpeedRatio c cmin * (Real.exp (K * |t|) * Real.exp (K * |s|)) := by
  have hEt : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  have hEs : (0 : ℝ) ≤ Real.exp (K * |s|) := le_of_lt (Real.exp_pos _)
  have hSd := abs_hillSinDeriv_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t
  have hCs := abs_hillCos_le_ratio (C := C) hm hc hcd hcpos hK hC hcmin hclow s ξ
  have hcross := abs_hillCosDeriv_mul_abs_hillSin_le (C := C) hm hc hcd hcpos hK hC hcmin hclow
    t s ξ
  have hterm1 : |hillSinDeriv (massiveFreq m c ‖ξ‖) t| * |hillCos (massiveFreq m c ‖ξ‖) s| ≤
      Real.exp (K * |t|) * (hillSpeedRatio c cmin * Real.exp (K * |s|)) :=
    mul_le_mul hSd hCs (abs_nonneg _) hEt
  have hsplit : |hillPropSymbolTimeDeriv m c t s ξ| ≤
      |hillSinDeriv (massiveFreq m c ‖ξ‖) t| * |hillCos (massiveFreq m c ‖ξ‖) s| +
        |hillCosDeriv (massiveFreq m c ‖ξ‖) t| * |hillSin (massiveFreq m c ‖ξ‖) s| := by
    rw [hillPropSymbolTimeDeriv]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
  refine hsplit.trans ?_
  have hsum := add_le_add hterm1 hcross
  refine hsum.trans_eq ?_
  ring

theorem abs_hillPropSymbolBaseDeriv_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (t s : ℝ) (ξ : E) :
    |hillPropSymbolBaseDeriv m c t s ξ| ≤
      2 * hillSpeedRatio c cmin * (Real.exp (K * |t|) * Real.exp (K * |s|)) := by
  have hEt : (0 : ℝ) ≤ Real.exp (K * |t|) := le_of_lt (Real.exp_pos _)
  have hEs : (0 : ℝ) ≤ Real.exp (K * |s|) := le_of_lt (Real.exp_pos _)
  have hSd := abs_hillSinDeriv_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl s
  have hCt := abs_hillCos_le_ratio (C := C) hm hc hcd hcpos hK hC hcmin hclow t ξ
  have hcross := abs_hillCosDeriv_mul_abs_hillSin_le (C := C) hm hc hcd hcpos hK hC hcmin hclow
    s t ξ
  have hterm2 : |hillCos (massiveFreq m c ‖ξ‖) t| * |hillSinDeriv (massiveFreq m c ‖ξ‖) s| ≤
      (hillSpeedRatio c cmin * Real.exp (K * |t|)) * Real.exp (K * |s|) :=
    mul_le_mul hCt hSd (abs_nonneg _) (mul_nonneg (hillSpeedRatio_nonneg c cmin) hEt)
  have hterm1 : |hillSin (massiveFreq m c ‖ξ‖) t| * |hillCosDeriv (massiveFreq m c ‖ξ‖) s| ≤
      hillSpeedRatio c cmin * (Real.exp (K * |s|) * Real.exp (K * |t|)) := by
    rw [mul_comm]
    exact hcross
  have hsplit : |hillPropSymbolBaseDeriv m c t s ξ| ≤
      |hillSin (massiveFreq m c ‖ξ‖) t| * |hillCosDeriv (massiveFreq m c ‖ξ‖) s| +
        |hillCos (massiveFreq m c ‖ξ‖) t| * |hillSinDeriv (massiveFreq m c ‖ξ‖) s| := by
    rw [hillPropSymbolBaseDeriv]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
  refine hsplit.trans ?_
  have hsum := add_le_add hterm1 hterm2
  refine hsum.trans_eq ?_
  ring

theorem abs_hillCoscSymbolDeriv_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t : ℝ) (ξ : E) :
    |hillCoscSymbolDeriv m c t ξ| ≤ Real.exp (K * |t|) := by
  have hpos := massiveFreq_pos hm c ‖ξ‖ 0
  have hCd := abs_hillCosDeriv_massive_le (S := ‖ξ‖) hm hc hcd hcpos hK hC le_rfl t
  rw [hillCoscSymbolDeriv, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine hCd.trans_eq ?_
  ring

/-! ## Continuity in the frequency -/

theorem continuous_hillCos_freq (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (t : ℝ) : Continuous fun ξ : E => hillCos (massiveFreq m c ‖ξ‖) t := by
  have hfibre : Continuous fun σ : ℝ => hillFlow (massiveFreq m c σ) (1, 0) t :=
    continuous_iff_continuousAt.mpr fun σ₀ =>
      continuousAt_hillFlow_massive_all (C := C) hm hc hC (1, 0) t σ₀
  exact (continuous_fst.comp hfibre).comp continuous_norm

theorem continuous_hillSin_freq (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (t : ℝ) : Continuous fun ξ : E => hillSin (massiveFreq m c ‖ξ‖) t := by
  have hfibre : Continuous fun σ : ℝ => hillFlow (massiveFreq m c σ) (0, 1) t :=
    continuous_iff_continuousAt.mpr fun σ₀ =>
      continuousAt_hillFlow_massive_all (C := C) hm hc hC (0, 1) t σ₀
  exact (continuous_fst.comp hfibre).comp continuous_norm

theorem continuous_hillPropSymbol_freq (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t s : ℝ) :
    Continuous fun ξ : E => hillPropSymbol m c t s ξ := by
  have h1 : Continuous fun ξ : E =>
      hillSin (massiveFreq m c ‖ξ‖) t * hillCos (massiveFreq m c ‖ξ‖) s :=
    (continuous_hillSin_freq (C := C) hm hc hC t).mul
      (continuous_hillCos_freq (C := C) hm hc hC s)
  have h2 : Continuous fun ξ : E =>
      hillCos (massiveFreq m c ‖ξ‖) t * hillSin (massiveFreq m c ‖ξ‖) s :=
    (continuous_hillCos_freq (C := C) hm hc hC t).mul
      (continuous_hillSin_freq (C := C) hm hc hC s)
  exact h1.sub h2

theorem continuous_massiveFreq_freq (m : ℝ) (c : ℝ → ℝ) (t : ℝ) :
    Continuous fun ξ : E => massiveFreq m c ‖ξ‖ t := by
  have hscale : Continuous fun σ : ℝ => massiveFreq m c σ t := by
    show Continuous fun σ : ℝ => Real.sqrt (m ^ 2 + (c t * σ) ^ 2)
    exact Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
  exact hscale.comp continuous_norm

theorem continuous_hillCoscSymbol_freq (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (t : ℝ) :
    Continuous fun ξ : E => hillCoscSymbol m c t ξ := by
  refine (continuous_hillCos_freq (C := C) hm hc hC t).div
    (continuous_massiveFreq_freq (E := E) m c 0) ?_
  intro ξ
  exact ne_of_gt (massiveFreq_pos hm c ‖ξ‖ 0)

end Symbol

end GaloisForLFunctions.HTGeometry
