import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingFragmentPhase
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingBlaschkeFragmentation

/-!
# The fragmented carrier is an anchor times a repeated half-plane pole

Composing the centred disc section with the anchor chart returns a half-plane factor: its zero is
the chart preimage of the section's zero,

`z₀ = b_c⁻¹(r ζ) = i c (1 + r ζ)/(1 - r ζ)`,

which lies in the open upper half plane, and

`B(b_c(z)) = λ · (z - z₀)/(z - z̄₀)`,   `λ = ζ̄ (r ζ - 1)/(1 - r ζ̄)`.

Both factorisations are linear in `z`, so the identity reduces to the defining relation of the pole.
Along the real axis the fragmented carrier is therefore a unimodular constant times the exponential
of the composite phase `polePhase 0 c + N · polePhase (Re z₀) (Im z₀)`, and the Clark level count
applies to the literal carrier: the constant `λ^N` moves the two antipodal levels but not their
positions.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions.HTGeometry

/-- The chart preimage of the section's zero: the pole of the composite half-plane factor. -/
def suzukiFragmentPole (c r : ℝ) (ζ : ℂ) : ℂ :=
  suzukiCoalescingCayleyInv c ((r : ℂ) * ζ)

/-- The unimodular constant of the composite factor. -/
def suzukiFragmentUnit (r : ℝ) (ζ : ℂ) : ℂ :=
  (starRingEnd ℂ) ζ * ((r : ℂ) * ζ - 1) / (1 - (r : ℂ) * (starRingEnd ℂ) ζ)

theorem norm_r_smul_lt_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖(r : ℂ) * ζ‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hζ, mul_one]
  exact hr1

/-- The pole lies in the open upper half plane. -/
theorem suzukiFragmentPole_im_pos {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ} (hc : 0 < c)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < (suzukiFragmentPole c r ζ).im :=
  suzukiCoalescingCayleyInv_im_pos hc (norm_r_smul_lt_one hζ hr0 hr1)

theorem one_sub_r_smul_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 : ℂ) - (r : ℂ) * ζ ≠ 0 := by
  intro hzero
  have h : (r : ℂ) * ζ = 1 := by linear_combination -hzero
  have hn := congrArg norm h
  rw [norm_one] at hn
  exact absurd hn (ne_of_lt (norm_r_smul_lt_one hζ hr0 hr1))

theorem one_sub_r_smul_conj_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) ζ ≠ 0 := by
  refine one_sub_r_smul_ne_zero ?_ hr0 hr1
  rw [Complex.norm_conj, hζ]

/-- The defining relation of the pole, cleared of denominators. -/
theorem suzukiFragmentPole_mul {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    suzukiFragmentPole c r ζ * (1 - (r : ℂ) * ζ) = (c : ℂ) * I * (1 + (r : ℂ) * ζ) := by
  have hne : (1 : ℂ) - (r : ℂ) * ζ ≠ 0 := one_sub_r_smul_ne_zero hζ hr0 hr1
  rw [suzukiFragmentPole, suzukiCoalescingCayleyInv,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  field_simp

/-- The conjugate relation. -/
theorem suzukiFragmentPole_conj_mul {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (starRingEnd ℂ) (suzukiFragmentPole c r ζ) * (1 - (r : ℂ) * (starRingEnd ℂ) ζ)
      = -((c : ℂ) * I * (1 + (r : ℂ) * (starRingEnd ℂ) ζ)) := by
  have h := congrArg (starRingEnd ℂ) (suzukiFragmentPole_mul (c := c) hζ hr0 hr1)
  simp only [map_mul, map_sub, map_add, map_one, Complex.conj_I, Complex.conj_ofReal] at h
  rw [h]
  ring

/-- On the real axis the chart denominator never vanishes. -/
theorem real_add_c_I_ne_zero {c : ℝ} (hc : 0 < c) (x : ℝ) : (x : ℂ) + (c : ℂ) * I ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp at him
  exact absurd him (ne_of_gt hc)

/-- On the real axis the composite denominator never vanishes. -/
theorem real_sub_conj_pole_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ} (hc : 0 < c)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    (x : ℂ) - (starRingEnd ℂ) (suzukiFragmentPole c r ζ) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.conj_im, Complex.zero_im] at him
  have hpos := suzukiFragmentPole_im_pos hζ hc hr0 hr1
  linarith

/-- Numerator factorisation: linear in `x`, with the pole as root. -/
theorem comp_cayley_num {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    (r : ℂ) * ζ * ((x : ℂ) + (c : ℂ) * I) - ((x : ℂ) - (c : ℂ) * I)
      = ((r : ℂ) * ζ - 1) * ((x : ℂ) - suzukiFragmentPole c r ζ) := by
  linear_combination -suzukiFragmentPole_mul (c := c) hζ hr0 hr1

/-- Denominator factorisation: linear in `x`, with the conjugate pole as root. -/
theorem comp_cayley_den {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ((x : ℂ) + (c : ℂ) * I)
        - (r : ℂ) * (starRingEnd ℂ) ζ * ((x : ℂ) - (c : ℂ) * I)
      = (1 - (r : ℂ) * (starRingEnd ℂ) ζ)
        * ((x : ℂ) - (starRingEnd ℂ) (suzukiFragmentPole c r ζ)) := by
  linear_combination suzukiFragmentPole_conj_mul (c := c) hζ hr0 hr1

/-- **The composite is a half-plane factor.**  The centred section pulled back through the anchor
chart is the factor with pole `z₀`, up to a unimodular constant. -/
theorem suzukiCenteredBlaschkeSection_comp_cayley {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ}
    (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    suzukiCenteredBlaschkeSection ζ r (suzukiCoalescingCayley c (x : ℂ))
      = suzukiFragmentUnit r ζ
        * (((x : ℂ) - suzukiFragmentPole c r ζ)
            / ((x : ℂ) - (starRingEnd ℂ) (suzukiFragmentPole c r ζ))) := by
  have hB := real_add_c_I_ne_zero hc x
  have hζ'' : (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) ζ ≠ 0 :=
    one_sub_r_smul_conj_ne_zero hζ hr0 hr1
  have hpole := real_sub_conj_pole_ne_zero hζ hc hr0 hr1 x
  have hQ : ((x : ℂ) + (c : ℂ) * I)
      - (r : ℂ) * (starRingEnd ℂ) ζ * ((x : ℂ) - (c : ℂ) * I) ≠ 0 := by
    rw [comp_cayley_den hζ hr0 hr1 x]
    exact mul_ne_zero hζ'' hpole
  have hnum : (r : ℂ) * ζ - ((x : ℂ) - (c : ℂ) * I) / ((x : ℂ) + (c : ℂ) * I)
      = ((r : ℂ) * ζ * ((x : ℂ) + (c : ℂ) * I) - ((x : ℂ) - (c : ℂ) * I))
        / ((x : ℂ) + (c : ℂ) * I) := by
    field_simp
  have hden : 1 - (r : ℂ) * (starRingEnd ℂ) ζ
        * (((x : ℂ) - (c : ℂ) * I) / ((x : ℂ) + (c : ℂ) * I))
      = (((x : ℂ) + (c : ℂ) * I)
          - (r : ℂ) * (starRingEnd ℂ) ζ * ((x : ℂ) - (c : ℂ) * I))
        / ((x : ℂ) + (c : ℂ) * I) := by
    field_simp
  have hcancel : ((r : ℂ) * ζ * ((x : ℂ) + (c : ℂ) * I) - ((x : ℂ) - (c : ℂ) * I))
        / ((x : ℂ) + (c : ℂ) * I)
        / ((((x : ℂ) + (c : ℂ) * I)
            - (r : ℂ) * (starRingEnd ℂ) ζ * ((x : ℂ) - (c : ℂ) * I)) / ((x : ℂ) + (c : ℂ) * I))
      = ((r : ℂ) * ζ * ((x : ℂ) + (c : ℂ) * I) - ((x : ℂ) - (c : ℂ) * I))
        / (((x : ℂ) + (c : ℂ) * I)
            - (r : ℂ) * (starRingEnd ℂ) ζ * ((x : ℂ) - (c : ℂ) * I)) := by
    field_simp
  rw [suzukiCenteredBlaschkeSection_eq_paperFormula, suzukiCoalescingCayley, hnum, hden,
    hcancel, comp_cayley_num (c := c) hζ hr0 hr1 x, comp_cayley_den (c := c) hζ hr0 hr1 x,
    suzukiFragmentUnit]
  field_simp

/-- The composite factor, written through its boundary phase. -/
theorem suzukiCenteredBlaschkeSection_comp_cayley_eq_exp {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ}
    (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    suzukiCenteredBlaschkeSection ζ r (suzukiCoalescingCayley c (x : ℂ))
      = suzukiFragmentUnit r ζ
        * Complex.exp ((polePhase (suzukiFragmentPole c r ζ).re
            (suzukiFragmentPole c r ζ).im x : ℂ) * I) := by
  rw [suzukiCenteredBlaschkeSection_comp_cayley hζ hc hr0 hr1 x]
  congr 1
  have hsplit : suzukiFragmentPole c r ζ
      = ((suzukiFragmentPole c r ζ).re : ℂ) + ((suzukiFragmentPole c r ζ).im : ℂ) * I :=
    (Complex.re_add_im _).symm
  have hconj : (starRingEnd ℂ) (suzukiFragmentPole c r ζ)
      = ((suzukiFragmentPole c r ζ).re : ℂ) - ((suzukiFragmentPole c r ζ).im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hconj]
  nth_rewrite 1 [hsplit]
  exact polePhase_eq_exp (suzukiFragmentPole_im_pos hζ hc hr0 hr1)

/-- **The fragmented carrier on the real axis.**  It is a unimodular constant times the exponential
of the composite phase, so its Clark levels are exactly the levels counted by `(38)`. -/
theorem suzukiFragmentedDiskCarrier_comp_cayley {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r : ℝ}
    (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) (x : ℝ) :
    suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c (x : ℂ))
      = suzukiFragmentUnit r ζ ^ N
        * Complex.exp ((suzukiFragmentPhase c (suzukiFragmentPole c r ζ).re
            (suzukiFragmentPole c r ζ).im N x : ℂ) * I) := by
  rw [suzukiFragmentedDiskCarrier,
    suzukiCenteredBlaschkeSection_comp_cayley_eq_exp hζ hc hr0 hr1 x,
    suzukiCoalescingCayley_eq_exp_polePhase hc x, mul_pow, ← Complex.exp_nat_mul,
    ← mul_assoc, mul_comm (Complex.exp ((polePhase 0 c x : ℂ) * I))
      (suzukiFragmentUnit r ζ ^ N), mul_assoc, ← Complex.exp_add, suzukiFragmentPhase]
  congr 2
  push_cast
  ring

/-! ## The foot descends to the physical point -/

/-- The pole in closed form. -/
theorem suzukiFragmentPole_eq (c r : ℝ) (ζ : ℂ) :
    suzukiFragmentPole c r ζ = (c : ℂ) * I * ((1 + (r : ℂ) * ζ) / (1 - (r : ℂ) * ζ)) := by
  rw [suzukiFragmentPole, suzukiCoalescingCayleyInv,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  ring

/-- The anchor chart never takes the value one on the real axis. -/
theorem suzukiCoalescingCayley_ne_one {c : ℝ} (hc : 0 < c) (x : ℝ) :
    suzukiCoalescingCayley c (x : ℂ) ≠ 1 := by
  intro hone
  have hB := real_add_c_I_ne_zero hc x
  rw [suzukiCoalescingCayley, div_eq_one_iff_eq hB] at hone
  have him := congrArg Complex.im hone
  simp at him
  linarith

/-- The chart inverse undoes the chart on the real axis, where the corpus's upper-half-plane
version does not apply. -/
theorem suzukiCoalescingCayleyInv_cayley_real {c : ℝ} (hc : 0 < c) (x : ℝ) :
    suzukiCoalescingCayleyInv c (suzukiCoalescingCayley c (x : ℂ)) = (x : ℂ) := by
  have hB := real_add_c_I_ne_zero hc x
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have hcI : (c : ℂ) * I ≠ 0 := mul_ne_zero hcne Complex.I_ne_zero
  have hden : (1 : ℂ) - suzukiCoalescingCayley c (x : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (suzukiCoalescingCayley_ne_one hc x))
  rw [suzukiCoalescingCayleyInv, GaloisForLFunctions.RHTower.suzukiUpperCayleyInv,
    suzukiCoalescingCayley] at *
  field_simp
  ring

/-- **The foot of the pole descends to the physical point.**  As the section deepens, the pole of
the composite factor tends to the chart preimage of its centre. -/
theorem tendsto_suzukiFragmentPole {c : ℝ} {ζ : ℂ} (hζ1 : ζ ≠ 1) :
    Filter.Tendsto (fun r : ℝ => suzukiFragmentPole c r ζ) (nhds 1)
      (nhds (suzukiCoalescingCayleyInv c ζ)) := by
  have hne : (1 : ℂ) - ((1 : ℝ) : ℂ) * ζ ≠ 0 := by
    push_cast
    rw [one_mul]
    exact sub_ne_zero.mpr (Ne.symm hζ1)
  have hcont : ContinuousAt
      (fun r : ℝ => (c : ℂ) * I * ((1 + (r : ℂ) * ζ) / (1 - (r : ℂ) * ζ))) 1 := by
    refine ContinuousAt.mul continuousAt_const (ContinuousAt.div ?_ ?_ hne)
    · fun_prop
    · fun_prop
  have hval : (c : ℂ) * I * ((1 + ((1 : ℝ) : ℂ) * ζ) / (1 - ((1 : ℝ) : ℂ) * ζ))
      = suzukiCoalescingCayleyInv c ζ := by
    rw [suzukiCoalescingCayleyInv, GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
    push_cast
    ring
  rw [← hval]
  simp only [suzukiFragmentPole_eq]
  exact hcont

/-- The foot and the depth of the pole converge to the physical point and to zero. -/
theorem tendsto_suzukiFragmentPole_of_cayley {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Filter.Tendsto (fun r : ℝ => suzukiFragmentPole c r (suzukiCoalescingCayley c (x : ℂ)))
      (nhds 1) (nhds ((x : ℂ))) := by
  have h := tendsto_suzukiFragmentPole (c := c) (suzukiCoalescingCayley_ne_one hc x)
  rwa [suzukiCoalescingCayleyInv_cayley_real hc x] at h

/-- **`(38)` for the literal carrier.**  Inside any real interval containing the foot of the pole,
the fragmented carrier returns to its left-endpoint value `M + 1` times and reaches the antipodal
value `M` times, and the two families strictly interlace, for every `M` the phase gain pays for.
With `(42)` and the radial budget `(41)` this is `N - O(1)` crossings of each Clark level. -/
theorem exists_interlacing_suzukiFragmentedDiskCarrier_levels
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r α β : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hα : α < (suzukiFragmentPole c r ζ).re) (hβ : (suzukiFragmentPole c r ζ).re < β)
    (N : ℕ) {M : ℕ}
    (hM : 2 * Real.pi * M ≤ 2 * Real.pi * N
      - 2 * (N : ℝ) * (suzukiFragmentPole c r ζ).im
        * (1 / (β - (suzukiFragmentPole c r ζ).re)
            + 1 / ((suzukiFragmentPole c r ζ).re - α))) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ M, x k ∈ Set.Icc α β ∧
        suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c ((x k : ℝ) : ℂ))
          = suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c ((α : ℝ) : ℂ))) ∧
      (∀ k, k < M → x' k ∈ Set.Icc α β ∧
        suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c ((x' k : ℝ) : ℂ))
          = -suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c ((α : ℝ) : ℂ))) ∧
      (∀ k, k < M → x k < x' k ∧ x' k < x (k + 1)) := by
  obtain ⟨x, x', hx, hx', hint⟩ :=
    exists_interlacing_suzukiFragment_levels (c := c) (u := (suzukiFragmentPole c r ζ).re)
      (v := (suzukiFragmentPole c r ζ).im) hc (suzukiFragmentPole_im_pos hζ hc hr0 hr1)
      hα hβ N hM
  refine ⟨x, x', fun k hk => ⟨(hx k hk).1, ?_⟩, fun k hk => ⟨(hx' k hk).1, ?_⟩, hint⟩
  · rw [suzukiFragmentedDiskCarrier_comp_cayley hζ hc hr0 hr1 N,
      suzukiFragmentedDiskCarrier_comp_cayley hζ hc hr0 hr1 N, (hx k hk).2]
  · rw [suzukiFragmentedDiskCarrier_comp_cayley hζ hc hr0 hr1 N,
      suzukiFragmentedDiskCarrier_comp_cayley hζ hc hr0 hr1 N, (hx' k hk).2]
    ring

/-! ## The literal Clark levels -/

/-- The constant of the composite factor is unimodular. -/
theorem norm_suzukiFragmentUnit {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖suzukiFragmentUnit r ζ‖ = 1 := by
  have hne : (1 : ℂ) - (r : ℂ) * ζ ≠ 0 := one_sub_r_smul_ne_zero hζ hr0 hr1
  have hconj : (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) ζ
      = (starRingEnd ℂ) (1 - (r : ℂ) * ζ) := by
    simp only [map_sub, map_one, map_mul, Complex.conj_ofReal]
  rw [suzukiFragmentUnit, norm_div, norm_mul, Complex.norm_conj, hζ, one_mul, hconj,
    Complex.norm_conj, norm_sub_rev]
  exact div_self (norm_ne_zero_iff.mpr hne)

/-- **The literal Clark levels of the fragmented carrier.**  With one extra full turn of gain, the
carrier attains the value `1` at `M + 1` points of `[α, β]` and the value `-1` at `M` points, and
the two families strictly interlace.  The values are absolute, not relative to an endpoint. -/
theorem exists_interlacing_suzukiFragmentedDiskCarrier_clark
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {c r α β : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hα : α < (suzukiFragmentPole c r ζ).re) (hβ : (suzukiFragmentPole c r ζ).re < β)
    (N : ℕ) {M : ℕ}
    (hM : 2 * Real.pi * ((M : ℝ) + 1) ≤ 2 * Real.pi * N
      - 2 * (N : ℝ) * (suzukiFragmentPole c r ζ).im
        * (1 / (β - (suzukiFragmentPole c r ζ).re)
            + 1 / ((suzukiFragmentPole c r ζ).re - α))) :
    ∃ x x' : ℕ → ℝ,
      (∀ k ≤ M, x k ∈ Set.Icc α β ∧
        suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c ((x k : ℝ) : ℂ)) = 1) ∧
      (∀ k, k < M → x' k ∈ Set.Icc α β ∧
        suzukiFragmentedDiskCarrier ζ r N (suzukiCoalescingCayley c ((x' k : ℝ) : ℂ)) = -1) ∧
      (∀ k, k < M → x k < x' k ∧ x' k < x (k + 1)) := by
  have hαβ : α ≤ β := le_of_lt (lt_trans hα hβ)
  have hv := suzukiFragmentPole_im_pos hζ hc hr0 hr1
  have hunit := norm_suzukiFragmentUnit hζ hr0 hr1
  have hpow : ‖suzukiFragmentUnit r ζ ^ N‖ = 1 := by
    rw [norm_pow, hunit, one_pow]
  have hne : suzukiFragmentUnit r ζ ^ N ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hpow
    norm_num at hpow
  have hw : ‖(suzukiFragmentUnit r ζ ^ N)⁻¹‖ = 1 := by
    rw [norm_inv, hpow, inv_one]
  have hgain := suzukiFragmentPhase_gain_ge (c := c) (u := (suzukiFragmentPole c r ζ).re)
    (v := (suzukiFragmentPole c r ζ).im) (α := α) (β := β) hc hv hα hβ N
  obtain ⟨x, x', hx, hx', hint⟩ :=
    GaloisForLFunctions.HTGeometry.exists_interlacing_levels_of_gain_two_turns (N := M) hαβ
      (continuous_suzukiFragmentPhase hc hv (suzukiFragmentPole c r ζ).re N).continuousOn
      ((strictMono_suzukiFragmentPhase hc hv (suzukiFragmentPole c r ζ).re N).strictMonoOn _)
      (by linarith) hw
  refine ⟨x, x', fun k hk => ⟨(hx k hk).1, ?_⟩, fun k hk => ⟨(hx' k hk).1, ?_⟩, hint⟩
  · rw [suzukiFragmentedDiskCarrier_comp_cayley hζ hc hr0 hr1 N, (hx k hk).2]
    exact mul_inv_cancel₀ hne
  · rw [suzukiFragmentedDiskCarrier_comp_cayley hζ hc hr0 hr1 N, (hx' k hk).2, mul_neg,
      mul_inv_cancel₀ hne]

end RHTower
