import Mathlib

/-!
# The prime-log jump shell and its essential-phase packet

For `0 < A < B` the *jump shell* is the indicator of the symmetric annulus `A < |x| < B`; it is the
difference of the two normalized interval windows exposed by dividing a theta translation anomaly by
the Xi conormal at two distinct primes, with `A = (log p)/2` and `B = (log q)/2`.

Modulating the shell by a cosine and subtracting the shell average produces the *essential-phase
jump packet*

```text
u_κ(x) = 1_{A<|x|<B}(x) · (cos (κ x) − μ_κ),
μ_κ = (sin (κ B) − sin (κ A)) / (κ (B − A)),
```

an even, compactly supported, real function, vanishing at the origin and of zero mean — an exact
two-condition Poisson source test in the jump class rather than the smooth class.  As `κ → ∞` the
correction `μ_κ` vanishes and the squared norm tends to the shell half-width `B − A`.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

/-- The symmetric annulus `A < |x| < B`, as the union of the two intervals it consists of. -/
def jumpShellSet (A B : ℝ) : Set ℝ := Ioo (-B) (-A) ∪ Ioo A B

theorem measurableSet_jumpShellSet (A B : ℝ) : MeasurableSet (jumpShellSet A B) :=
  (measurableSet_Ioo).union measurableSet_Ioo

theorem mem_jumpShellSet_iff {A B : ℝ} (hA : 0 < A) (x : ℝ) :
    x ∈ jumpShellSet A B ↔ A < |x| ∧ |x| < B := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hx : x < 0 := by linarith
      rw [abs_of_neg hx]
      constructor <;> linarith
    · have hx : 0 < x := by linarith
      rw [abs_of_pos hx]
      exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy x 0 with hx | hx | hx
    · left
      rw [abs_of_neg hx] at h1 h2
      constructor <;> linarith
    · exfalso
      rw [hx] at h1
      simp at h1
      linarith
    · right
      rw [abs_of_pos hx] at h1 h2
      exact ⟨h1, h2⟩

theorem jumpShellSet_disjoint {A B : ℝ} (hA : 0 < A) :
    Disjoint (Ioo (-B) (-A)) (Ioo A B) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx⟩ ⟨hx', -⟩
  linarith

/-- The jump shell: the indicator function of the annulus. -/
noncomputable def jumpShell (A B : ℝ) : ℝ → ℝ := (jumpShellSet A B).indicator 1

theorem jumpShell_neg {A B : ℝ} (hA : 0 < A) (x : ℝ) :
    jumpShell A B (-x) = jumpShell A B x := by
  classical
  simp only [jumpShell, Set.indicator_apply]
  by_cases hx : x ∈ jumpShellSet A B
  · have : -x ∈ jumpShellSet A B := by
      rw [mem_jumpShellSet_iff hA] at hx ⊢
      simpa using hx
    simp [hx, this]
  · have : -x ∉ jumpShellSet A B := by
      rw [mem_jumpShellSet_iff hA] at hx ⊢
      simpa using hx
    simp [hx, this]

theorem jumpShell_zero {A B : ℝ} (hA : 0 < A) : jumpShell A B 0 = 0 := by
  classical
  have h0 : (0 : ℝ) ∉ jumpShellSet A B := by
    rw [mem_jumpShellSet_iff hA]
    rintro ⟨h1, -⟩
    rw [abs_zero] at h1
    linarith
  simp [jumpShell, h0]

/-- The shell average of the modulating cosine. -/
noncomputable def jumpMean (A B κ : ℝ) : ℝ :=
  (Real.sin (κ * B) - Real.sin (κ * A)) / (κ * (B - A))

/-- The essential-phase jump packet. -/
noncomputable def jumpPacket (A B κ : ℝ) : ℝ → ℝ :=
  fun x => jumpShell A B x * (Real.cos (κ * x) - jumpMean A B κ)

theorem jumpPacket_neg {A B : ℝ} (hA : 0 < A) (κ x : ℝ) :
    jumpPacket A B κ (-x) = jumpPacket A B κ x := by
  simp only [jumpPacket, jumpShell_neg hA]
  rw [show κ * -x = -(κ * x) by ring, Real.cos_neg]

theorem jumpPacket_zero {A B : ℝ} (hA : 0 < A) (κ : ℝ) : jumpPacket A B κ 0 = 0 := by
  simp [jumpPacket, jumpShell_zero hA]

/-! ### The shell integrals -/

section Integrals

variable {A B κ : ℝ}

theorem integrableOn_jumpShellSet {f : ℝ → ℝ} (hf : Continuous f) (hA : 0 < A) (_hAB : A < B) :
    IntegrableOn f (jumpShellSet A B) := by
  have h1 : IntegrableOn f (Icc (-B) B) := hf.integrableOn_Icc
  refine h1.mono_set ?_
  rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith

theorem integrable_jumpShell_mul {f : ℝ → ℝ} (hf : Continuous f) (hA : 0 < A) (hAB : A < B) :
    Integrable (fun x => jumpShell A B x * f x) := by
  classical
  have h1 : (fun x => jumpShell A B x * f x) = (jumpShellSet A B).indicator f := by
    funext x
    by_cases hx : x ∈ jumpShellSet A B <;> simp [jumpShell, hx]
  rw [h1]
  exact (integrableOn_jumpShellSet hf hA hAB).integrable_indicator
    (measurableSet_jumpShellSet A B)

theorem integral_jumpShell_mul (hA : 0 < A) (hAB : A < B) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, jumpShell A B x * f x = (∫ x in (-B)..(-A), f x) + ∫ x in A..B, f x := by
  classical
  have h1 : (fun x => jumpShell A B x * f x) = (jumpShellSet A B).indicator f := by
    funext x
    by_cases hx : x ∈ jumpShellSet A B <;> simp [jumpShell, hx]
  have hint : ∀ a b : ℝ, IntegrableOn f (Ioo a b) := by
    intro a b
    exact (hf.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  have hIoo : ∀ a b : ℝ, a ≤ b → ∫ x in Ioo a b, f x = ∫ x in a..b, f x := by
    intro a b hab
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [h1, MeasureTheory.integral_indicator (measurableSet_jumpShellSet A B)]
  show ∫ x in (Ioo (-B) (-A) ∪ Ioo A B), f x = _
  rw [MeasureTheory.setIntegral_union (jumpShellSet_disjoint hA) measurableSet_Ioo
      (hint _ _) (hint _ _),
    hIoo _ _ (by linarith), hIoo _ _ (by linarith)]

theorem integral_jumpShell (hA : 0 < A) (hAB : A < B) :
    ∫ x, jumpShell A B x = 2 * (B - A) := by
  have h := integral_jumpShell_mul (A := A) (B := B) hA hAB (f := fun _ => (1 : ℝ))
    continuous_const
  simp only [mul_one] at h
  rw [h]
  simp
  ring

theorem intervalIntegral_cos_mul (hκ : κ ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.cos (κ * x) = (Real.sin (κ * b) - Real.sin (κ * a)) / κ := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hκ, integral_cos, smul_eq_mul]
  field_simp

/-- The shell-modulated cosine integral. -/
theorem integral_jumpShell_mul_cos (hA : 0 < A) (hAB : A < B) (hκ : κ ≠ 0) :
    ∫ x, jumpShell A B x * Real.cos (κ * x)
      = 2 * (Real.sin (κ * B) - Real.sin (κ * A)) / κ := by
  have hcont : Continuous fun x : ℝ => Real.cos (κ * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rw [integral_jumpShell_mul hA hAB hcont, intervalIntegral_cos_mul hκ,
    intervalIntegral_cos_mul hκ,
    show κ * -A = -(κ * A) by ring, show κ * -B = -(κ * B) by ring,
    Real.sin_neg, Real.sin_neg]
  field_simp
  ring

/-- **`(8)`.**  The essential-phase jump packet has zero mean. -/
theorem integral_jumpPacket_eq_zero (hA : 0 < A) (hAB : A < B) (hκ : κ ≠ 0) :
    ∫ x, jumpPacket A B κ x = 0 := by
  have hAB' : B - A ≠ 0 := by linarith
  have hcont : Continuous fun x : ℝ => Real.cos (κ * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsplit : (fun x => jumpPacket A B κ x)
      = fun x => jumpShell A B x * Real.cos (κ * x)
        - jumpMean A B κ * (jumpShell A B x * 1) := by
    funext x
    simp only [jumpPacket, mul_one]
    ring
  have hint1 : Integrable (fun x => jumpShell A B x * Real.cos (κ * x)) :=
    integrable_jumpShell_mul hcont hA hAB
  have hint2 : Integrable (fun x => jumpShell A B x * (1 : ℝ)) :=
    integrable_jumpShell_mul continuous_const hA hAB
  rw [hsplit, MeasureTheory.integral_sub hint1 (hint2.const_mul _),
    MeasureTheory.integral_const_mul]
  simp only [mul_one]
  rw [integral_jumpShell hA hAB, integral_jumpShell_mul_cos hA hAB hκ, jumpMean]
  field_simp
  ring

/-- **`(9)`, first half.**  The shell average of the modulating cosine vanishes at high
frequency. -/
theorem tendsto_jumpMean_atTop (hAB : A < B) :
    Filter.Tendsto (fun κ : ℝ => jumpMean A B κ) Filter.atTop (nhds 0) := by
  have hD : 0 < B - A := by linarith
  have hbound : ∀ κ : ℝ, 0 < κ → ‖jumpMean A B κ‖ ≤ 2 / (κ * (B - A)) := by
    intro κ hκ
    have hden : 0 < κ * (B - A) := mul_pos hκ hD
    have hnum : |Real.sin (κ * B) - Real.sin (κ * A)| ≤ 2 := by
      rw [abs_le]
      constructor
      · have h3 := Real.neg_one_le_sin (κ * B)
        have h4 := Real.sin_le_one (κ * A)
        linarith
      · have h3 := Real.sin_le_one (κ * B)
        have h4 := Real.neg_one_le_sin (κ * A)
        linarith
    rw [Real.norm_eq_abs, jumpMean, abs_div, abs_of_pos hden]
    gcongr
  have hlim : Filter.Tendsto (fun κ : ℝ => 2 / (κ * (B - A))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun κ : ℝ => κ * (B - A)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const hD Filter.tendsto_id
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_gt_atTop 0] with κ hκ
  exact hbound κ hκ

theorem jumpShell_sq (A B : ℝ) (x : ℝ) : (jumpShell A B x) ^ 2 = jumpShell A B x := by
  classical
  by_cases hx : x ∈ jumpShellSet A B <;> simp [jumpShell, hx]

/-- The exact squared mass of the jump packet. -/
theorem integral_jumpPacket_sq (hA : 0 < A) (hAB : A < B) (hκ : κ ≠ 0) :
    ∫ x, (jumpPacket A B κ x) ^ 2
      = (B - A) + (Real.sin (2 * κ * B) - Real.sin (2 * κ * A)) / (2 * κ)
        - 2 * (B - A) * (jumpMean A B κ) ^ 2 := by
  have hκ2 : (2 : ℝ) * κ ≠ 0 := by simpa using hκ
  have hcont : Continuous fun x : ℝ => Real.cos (κ * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcont2 : Continuous fun x : ℝ => Real.cos (2 * κ * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hexp : (fun x => (jumpPacket A B κ x) ^ 2)
      = fun x => (1 / 2 : ℝ) * (jumpShell A B x * 1)
        + (1 / 2 : ℝ) * (jumpShell A B x * Real.cos (2 * κ * x))
        - (2 * jumpMean A B κ) * (jumpShell A B x * Real.cos (κ * x))
        + (jumpMean A B κ) ^ 2 * (jumpShell A B x * 1) := by
    funext x
    have hsq := jumpShell_sq A B x
    have hcos : (Real.cos (κ * x)) ^ 2 = 1 / 2 + Real.cos (2 * (κ * x)) / 2 := Real.cos_sq _
    simp only [jumpPacket, mul_one]
    rw [show (2 : ℝ) * κ * x = 2 * (κ * x) by ring]
    linear_combination ((Real.cos (κ * x) - jumpMean A B κ) ^ 2) * hsq
      + (jumpShell A B x) * hcos
  have hi1 : Integrable (fun x => jumpShell A B x * (1 : ℝ)) :=
    integrable_jumpShell_mul continuous_const hA hAB
  have hi2 : Integrable (fun x => jumpShell A B x * Real.cos (2 * κ * x)) :=
    integrable_jumpShell_mul hcont2 hA hAB
  have hi3 : Integrable (fun x => jumpShell A B x * Real.cos (κ * x)) :=
    integrable_jumpShell_mul hcont hA hAB
  have hs1 : Integrable (fun x => (1 / 2 : ℝ) * (jumpShell A B x * 1)) := hi1.const_mul _
  have hs2 : Integrable (fun x => (1 / 2 : ℝ) * (jumpShell A B x * Real.cos (2 * κ * x))) :=
    hi2.const_mul _
  have hs3 : Integrable
      (fun x => (2 * jumpMean A B κ) * (jumpShell A B x * Real.cos (κ * x))) := hi3.const_mul _
  have hs4 : Integrable (fun x => (jumpMean A B κ) ^ 2 * (jumpShell A B x * 1)) := hi1.const_mul _
  have hs12 : Integrable (fun x => (1 / 2 : ℝ) * (jumpShell A B x * 1)
      + (1 / 2 : ℝ) * (jumpShell A B x * Real.cos (2 * κ * x))) := hs1.add hs2
  have hs123 : Integrable (fun x => (1 / 2 : ℝ) * (jumpShell A B x * 1)
      + (1 / 2 : ℝ) * (jumpShell A B x * Real.cos (2 * κ * x))
      - (2 * jumpMean A B κ) * (jumpShell A B x * Real.cos (κ * x))) := hs12.sub hs3
  rw [hexp, MeasureTheory.integral_add hs123 hs4, MeasureTheory.integral_sub hs12 hs3,
    MeasureTheory.integral_add hs1 hs2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [mul_one]
  rw [integral_jumpShell hA hAB, integral_jumpShell_mul_cos hA hAB hκ2,
    integral_jumpShell_mul_cos hA hAB hκ]
  rw [jumpMean]
  field_simp
  ring

/-- **`(9)`, second half.**  The squared mass of the jump packet tends to the shell half-width. -/
theorem tendsto_integral_jumpPacket_sq (hA : 0 < A) (hAB : A < B) :
    Filter.Tendsto (fun κ : ℝ => ∫ x, (jumpPacket A B κ x) ^ 2) Filter.atTop
      (nhds (B - A)) := by
  have hD : 0 < B - A := by linarith
  -- the two correction terms vanish
  have hcorr1 : Filter.Tendsto
      (fun κ : ℝ => (Real.sin (2 * κ * B) - Real.sin (2 * κ * A)) / (2 * κ))
      Filter.atTop (nhds 0) := by
    have hbound : ∀ κ : ℝ, 0 < κ →
        ‖(Real.sin (2 * κ * B) - Real.sin (2 * κ * A)) / (2 * κ)‖ ≤ 2 / (2 * κ) := by
      intro κ hκ
      have hden : 0 < 2 * κ := by linarith
      have hnum : |Real.sin (2 * κ * B) - Real.sin (2 * κ * A)| ≤ 2 := by
        rw [abs_le]
        constructor
        · have h3 := Real.neg_one_le_sin (2 * κ * B)
          have h4 := Real.sin_le_one (2 * κ * A)
          linarith
        · have h3 := Real.sin_le_one (2 * κ * B)
          have h4 := Real.neg_one_le_sin (2 * κ * A)
          linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
      gcongr
    have hlim : Filter.Tendsto (fun κ : ℝ => 2 / (2 * κ)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun κ : ℝ => 2 * κ) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
      exact Filter.Tendsto.div_atTop tendsto_const_nhds h1
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Filter.eventually_gt_atTop 0] with κ hκ
    exact hbound κ hκ
  have hcorr2 : Filter.Tendsto (fun κ : ℝ => 2 * (B - A) * (jumpMean A B κ) ^ 2)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_jumpMean_atTop (A := A) (B := B) hAB).pow 2
    simpa using (h.const_mul (2 * (B - A)))
  have hmain : Filter.Tendsto
      (fun κ : ℝ => (B - A) + (Real.sin (2 * κ * B) - Real.sin (2 * κ * A)) / (2 * κ)
        - 2 * (B - A) * (jumpMean A B κ) ^ 2) Filter.atTop (nhds (B - A)) := by
    have := ((tendsto_const_nhds (x := B - A) (f := Filter.atTop (α := ℝ))).add hcorr1).sub hcorr2
    simpa using this
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with κ hκ
  exact (integral_jumpPacket_sq hA hAB (by linarith)).symm

end Integrals

end GaloisForLFunctions.RHTower
