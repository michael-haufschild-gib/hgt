import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardPrimeDensity

/-!
# The discarded Harman terms with two prime cofactors: section bounds

The part of the discarded second Buchstab term with `m = p₃ p₄`, `q₂ ≤ p₃ ≤ p₄`, has density
`∫ dα₂/α₂ · S(α₂)`, where the section

`S(α₂) = ∫ dα₁/α₁ ∫_{α₂}^{(1+κ-α₁-α₂)/2} dα₃ / (α₃ (1 - α₁ - α₂ - α₃))`

runs over the same `α₁`-range as the prime-cofactor term, cut at `α₁ ≤ 1 + κ - 3α₂`.  The
innermost integral is `(log((L+κ)/(L-κ)) + log((L-α₂)/α₂))/L` with `L = 1 - α₁ - α₂`.  After
`α₁ = 1 - (2+β)α₂` the second part becomes `∫ log β / ((1+β)(1-(2+β)α₂)) dβ`, which on a strip
`a ≤ α₂ ≤ b` lies below the chord between its values at `a` and `b` (convexity of
`x ↦ 1/(1 - (2+β)x)`), each bounded by affine envelopes on `β`-cells.
-/

namespace RHTower.Sieve

open Real intervalIntegral

noncomputable section

/-- Upper end of the `α₁`-section when the cofactor is a product of two primes. -/
def harmanDiscardHighTwo (κ α₂ : ℝ) : ℝ := min (1 / 2 + κ) (1 + κ - 3 * α₂)

/-- Integral over the smaller cofactor prime. -/
def harmanDiscardTwoPrimeInner (κ α₁ α₂ : ℝ) : ℝ :=
  ∫ α₃ in α₂..((1 + κ - α₁ - α₂) / 2), 1 / (α₃ * (1 - α₁ - α₂ - α₃))

/-- The `α₁`-section of the two-prime-cofactor density. -/
def harmanDiscardTwoPrimeSection (κ α₂ : ℝ) : ℝ :=
  ∫ α₁ in harmanDiscardLow κ α₂..harmanDiscardHighTwo κ α₂, harmanDiscardTwoPrimeInner κ α₁ α₂ / α₁

/-- The integrand after the substitution `α₁ = 1 - (2+β)α₂`. -/
def harmanTwoPrimeKernel (α₂ β : ℝ) : ℝ := log β / ((1 + β) * (1 - (2 + β) * α₂))

theorem harmanDiscardTwoPrimeInner_eq {κ α₁ α₂ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h0 : 2 / 11 ≤ α₂) (h1 : α₁ ≤ 1 + κ - 3 * α₂) :
    harmanDiscardTwoPrimeInner κ α₁ α₂ =
      (log ((1 - α₁ - α₂ + κ) / (1 - α₁ - α₂ - κ))
        + log ((1 - α₁ - α₂ - α₂) / α₂)) / (1 - α₁ - α₂) := by
  set L := 1 - α₁ - α₂ with hL
  have hL0 : 2 * α₂ - κ ≤ L := by rw [hL]; linarith
  have hLpos : 0 < L := by linarith
  have hc : α₂ ≤ (1 + κ - α₁ - α₂) / 2 := by linarith
  have hderiv : ∀ t ∈ Set.uIcc α₂ ((1 + κ - α₁ - α₂) / 2),
      HasDerivAt (fun t => (log t - log (L - t)) / L) (1 / (t * (1 - α₁ - α₂ - t))) t := by
    intro t ht
    rw [Set.uIcc_of_le hc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 0 < L - t := by rw [hL]; linarith [ht.2]
    have h1 := Real.hasDerivAt_log ht0.ne'
    have h2 := ((hasDerivAt_id t).const_sub L).log ht1.ne'
    have h3 := (h1.sub h2).div_const L
    refine h3.congr_deriv ?_
    have hne1 : L - t ≠ 0 := ht1.ne'
    have hne2 : 1 - α₁ - α₂ - t ≠ 0 := by rw [hL] at hne1; linarith
    have hne3 : L ≠ 0 := hLpos.ne'
    simp only [id]
    rw [hL] at hne1 hne3 ⊢
    field_simp
    ring
  have hcont : ContinuousOn (fun t => 1 / (t * (1 - α₁ - α₂ - t)))
      (Set.uIcc α₂ ((1 + κ - α₁ - α₂) / 2)) := by
    rw [Set.uIcc_of_le hc]
    refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)) ?_
    intro t ht
    have : 0 < t := by linarith [ht.1]
    have : 0 < 1 - α₁ - α₂ - t := by linarith [ht.2]
    positivity
  unfold harmanDiscardTwoPrimeInner
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hLk : 0 < L - κ := by linarith
  have e1 : L - (1 + κ - α₁ - α₂) / 2 = (L - κ) / 2 := by rw [hL]; ring
  have e2 : (1 + κ - α₁ - α₂) / 2 = (L + κ) / 2 := by rw [hL]; ring
  have hLa : 0 < L - α₂ := by linarith
  have ha0 : 0 < α₂ := by linarith
  rw [e1, e2, Real.log_div (x := L + κ) (y := 2) (by linarith) (by norm_num),
    Real.log_div (x := L - κ) (y := 2) (by linarith) (by norm_num),
    Real.log_div (x := L + κ) (y := L - κ) (by linarith) (by linarith),
    Real.log_div (x := L - α₂) (y := α₂) (by linarith) (by linarith)]
  ring

theorem harmanDiscardLow_le_highTwo {κ α₂ : ℝ} (hκ : 0 ≤ κ) (h0 : 0 ≤ α₂)
    (h1 : α₂ ≤ (1 + κ) / 4) :
    harmanDiscardLow κ α₂ ≤ harmanDiscardHighTwo κ α₂ := by
  unfold harmanDiscardLow harmanDiscardHighTwo
  refine max_le (le_min (by linarith) (by linarith)) ?_
  exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))

/-- The section splits into a `κ`-perturbation of size at most `30κ` and the main integral. -/
theorem harmanDiscardTwoPrimeSection_le {κ α₂ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h0 : 2 / 11 ≤ α₂) (h1 : α₂ ≤ (1 + κ) / 4) :
    harmanDiscardTwoPrimeSection κ α₂ ≤ 30 * κ +
      ∫ α₁ in harmanDiscardLow κ α₂..harmanDiscardHighTwo κ α₂,
        log ((1 - α₁ - 2 * α₂) / α₂) / (α₁ * (1 - α₁ - α₂)) := by
  set lo := harmanDiscardLow κ α₂ with hlo
  set hi := harmanDiscardHighTwo κ α₂ with hhi
  have hlh : lo ≤ hi := harmanDiscardLow_le_highTwo hκ (by linarith) h1
  have hlo1 : α₂ ≤ lo := le_max_left _ _
  have hhi1 : hi ≤ 1 + κ - 3 * α₂ := min_le_right _ _
  have hhi2 : hi ≤ 1 / 2 + κ := min_le_left _ _
  set T1 : ℝ → ℝ := fun α₁ => log ((1 - α₁ - α₂ + κ) / (1 - α₁ - α₂ - κ)) / ((1 - α₁ - α₂) * α₁)
    with hT1
  set T2 : ℝ → ℝ := fun α₁ => log ((1 - α₁ - 2 * α₂) / α₂) / (α₁ * (1 - α₁ - α₂)) with hT2
  have heq : Set.EqOn (fun α₁ => harmanDiscardTwoPrimeInner κ α₁ α₂ / α₁) (fun α₁ => T1 α₁ + T2 α₁)
      (Set.uIcc lo hi) := by
    intro α₁ hα
    rw [Set.uIcc_of_le hlh] at hα
    have hα1 : α₂ ≤ α₁ := hlo1.trans hα.1
    have hα2 : α₁ ≤ 1 + κ - 3 * α₂ := hα.2.trans hhi1
    simp only [hT1, hT2]
    rw [harmanDiscardTwoPrimeInner_eq hκ hκ1 h0 hα2,
      show 1 - α₁ - α₂ - α₂ = 1 - α₁ - 2 * α₂ by ring]
    have hL : 0 < 1 - α₁ - α₂ := by linarith
    have ha : 0 < α₁ := by linarith
    field_simp
  have hcT1 : ContinuousOn T1 (Set.Icc lo hi) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.log ?_ ?_
      · exact (ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => by
          have := hx.2; linarith))
      · intro x hx
        have h1' : 0 < 1 - x - α₂ - κ := by linarith [hx.2]
        have h2' : 0 < 1 - x - α₂ + κ := by linarith [hx.2]
        exact (div_pos h2' h1').ne'
    · fun_prop
    · intro x hx
      have : 0 < 1 - x - α₂ := by linarith [hx.2]
      have : 0 < x := by linarith [hx.1]
      positivity
  have hcT2 : ContinuousOn T2 (Set.Icc lo hi) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine ContinuousOn.log ?_ ?_
      · exact (ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => by linarith))
      · intro x hx
        have : 0 < 1 - x - 2 * α₂ := by linarith [hx.2]
        have : 0 < α₂ := by linarith
        positivity
    · fun_prop
    · intro x hx
      have : 0 < 1 - x - α₂ := by linarith [hx.2]
      have : 0 < x := by linarith [hx.1]
      positivity
  have hbound : ∀ x ∈ Set.Icc lo hi, T1 x ≤ 90 * κ := by
    intro x hx
    have hx0 : 2 / 11 ≤ x := by linarith [hx.1]
    have hL : 7 / 20 ≤ 1 - x - α₂ - κ := by linarith [hx.2]
    have hLpos : 0 < 1 - x - α₂ - κ := by linarith
    have hlog : log ((1 - x - α₂ + κ) / (1 - x - α₂ - κ)) ≤ 2 * κ / (1 - x - α₂ - κ) := by
      have := Real.log_le_sub_one_of_pos
        (show 0 < (1 - x - α₂ + κ) / (1 - x - α₂ - κ) from div_pos (by linarith) hLpos)
      have e : (1 - x - α₂ + κ) / (1 - x - α₂ - κ) - 1 = 2 * κ / (1 - x - α₂ - κ) := by
        field_simp; ring
      linarith
    have hden : 7 / 20 * (2 / 11) ≤ (1 - x - α₂) * x := by
      have : 7 / 20 ≤ 1 - x - α₂ := by linarith
      nlinarith
    have hq : 2 * κ / (1 - x - α₂ - κ) ≤ 2 * κ / (7 / 20) :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) hL
    simp only [hT1]
    calc log ((1 - x - α₂ + κ) / (1 - x - α₂ - κ)) / ((1 - x - α₂) * x)
        ≤ (2 * κ / (7 / 20)) / ((1 - x - α₂) * x) := by
          apply div_le_div_of_nonneg_right (hlog.trans hq) (by positivity)
      _ ≤ (2 * κ / (7 / 20)) / (7 / 20 * (2 / 11)) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = 4400 / 49 * κ := by ring
      _ ≤ 90 * κ := by nlinarith
  unfold harmanDiscardTwoPrimeSection
  rw [integral_congr heq, integral_add (hcT1.intervalIntegrable_of_Icc hlh)
    (hcT2.intervalIntegrable_of_Icc hlh)]
  have hI1 : ∫ x in lo..hi, T1 x ≤ 30 * κ := by
    calc ∫ x in lo..hi, T1 x ≤ ∫ _ in lo..hi, 90 * κ :=
          integral_mono_on hlh (hcT1.intervalIntegrable_of_Icc hlh) intervalIntegrable_const hbound
      _ = (hi - lo) * (90 * κ) := by rw [integral_const, smul_eq_mul]
      _ ≤ 30 * κ := by
          have : hi - lo ≤ 1 / 3 := by linarith
          nlinarith
  linarith

/-- The substitution `α₁ = 1 - (2+β)α₂` turns the main part of the section into an integral of
`harmanTwoPrimeKernel α₂` over `β`. -/
theorem harmanTwoPrimeMain_eq {κ α₂ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h0 : 2 / 11 ≤ α₂) (h1 : α₂ ≤ (1 + κ) / 4) :
    ∫ α₁ in harmanDiscardLow κ α₂..harmanDiscardHighTwo κ α₂,
        log ((1 - α₁ - 2 * α₂) / α₂) / (α₁ * (1 - α₁ - α₂)) =
      ∫ β in (1 - 2 * α₂ - harmanDiscardHighTwo κ α₂) / α₂..(1 - 2 * α₂ - harmanDiscardLow κ α₂) / α₂,
        harmanTwoPrimeKernel α₂ β := by
  set lo := harmanDiscardLow κ α₂ with hlo
  set hi := harmanDiscardHighTwo κ α₂ with hhi
  have hlh : lo ≤ hi := harmanDiscardLow_le_highTwo hκ (by linarith) h1
  have hlo1 : α₂ ≤ lo := le_max_left _ _
  have hhi1 : hi ≤ 1 + κ - 3 * α₂ := min_le_right _ _
  have ha0 : 0 < α₂ := by linarith
  set F : ℝ → ℝ := fun α₁ => log ((1 - α₁ - 2 * α₂) / α₂) / (α₁ * (1 - α₁ - α₂)) with hF
  have hsub := intervalIntegral.integral_comp_mul_add (a := (1 - 2 * α₂ - hi) / α₂)
    (b := (1 - 2 * α₂ - lo) / α₂) F (neg_ne_zero.2 ha0.ne') (1 - 2 * α₂)
  have e1 : -α₂ * ((1 - 2 * α₂ - hi) / α₂) + (1 - 2 * α₂) = hi := by field_simp; ring
  have e2 : -α₂ * ((1 - 2 * α₂ - lo) / α₂) + (1 - 2 * α₂) = lo := by field_simp; ring
  rw [e1, e2, integral_symm lo hi, smul_eq_mul, inv_neg, neg_mul_neg] at hsub
  have hβ : (1 - 2 * α₂ - hi) / α₂ ≤ (1 - 2 * α₂ - lo) / α₂ :=
    div_le_div_of_nonneg_right (by linarith) ha0.le
  have hcongr : Set.EqOn (fun x => F (-α₂ * x + (1 - 2 * α₂))) (fun x => harmanTwoPrimeKernel α₂ x / α₂)
      (Set.uIcc ((1 - 2 * α₂ - hi) / α₂) ((1 - 2 * α₂ - lo) / α₂)) := by
    intro x hx
    rw [Set.uIcc_of_le hβ] at hx
    have hx0 : α₂ - κ ≤ α₂ * x := by
      have := hx.1
      rw [div_le_iff₀ ha0] at this
      linarith
    have hxpos : 0 < x := by
      by_contra hneg
      have hle : x ≤ 0 := not_lt.mp hneg
      nlinarith
    have hxb : α₂ * x ≤ 1 - 3 * α₂ := by
      have := hx.2
      rw [le_div_iff₀ ha0] at this
      linarith
    simp only [hF, harmanTwoPrimeKernel]
    rw [show 1 - (-α₂ * x + (1 - 2 * α₂)) - 2 * α₂ = α₂ * x by ring,
      mul_div_cancel_left₀ x ha0.ne',
      show 1 - (-α₂ * x + (1 - 2 * α₂)) - α₂ = α₂ * (1 + x) by ring,
      show -α₂ * x + (1 - 2 * α₂) = 1 - (2 + x) * α₂ by ring]
    have h1x : 0 < 1 + x := by linarith
    have h2x : 0 < 1 - (2 + x) * α₂ := by nlinarith
    field_simp
  rw [integral_congr hcongr, intervalIntegral.integral_div] at hsub
  have := hsub
  field_simp at this
  linarith

theorem continuousOn_harmanTwoPrimeKernel {α₂ c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc₂ : (2 + c₂) * α₂ < 1) (hα : 0 ≤ α₂) :
    ContinuousOn (harmanTwoPrimeKernel α₂) (Set.Icc c₁ c₂) := by
  unfold harmanTwoPrimeKernel
  refine ContinuousOn.div ?_ (by fun_prop) ?_
  · exact continuousOn_id.log (fun x hx => (show (0 : ℝ) < x by linarith [hx.1]).ne')
  · intro x hx
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have h2 : 0 < 1 - (2 + x) * α₂ := by nlinarith [hx.2]
    positivity

/-- The kernel is negative below `β = 1` and positive above; so the `β`-integral over
`[βₕ, βₗ]` with `0 < βₕ ≤ 1` is at most the integral over `[1, B]` for any `B ≥ βₗ`. -/
theorem integral_harmanTwoPrimeKernel_le {α₂ βh βl B : ℝ} (h0 : 0 < α₂) (hβh0 : 0 < βh)
    (hβh1 : βh ≤ 1) (hβhl : βh ≤ βl) (hβlB : βl ≤ B) (hB1 : 1 ≤ B) (hBα : (2 + B) * α₂ < 1) :
    ∫ β in βh..βl, harmanTwoPrimeKernel α₂ β ≤ ∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel α₂ β := by
  have hc : ContinuousOn (harmanTwoPrimeKernel α₂) (Set.Icc βh B) :=
    continuousOn_harmanTwoPrimeKernel hβh0 hBα h0.le
  have ii : ∀ x y, βh ≤ x → x ≤ y → y ≤ B →
      IntervalIntegrable (harmanTwoPrimeKernel α₂) MeasureTheory.volume x y :=
    fun x y hx hxy hy => (hc.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  have hden : ∀ β ∈ Set.Icc βh B, 0 < (1 + β) * (1 - (2 + β) * α₂) := by
    intro β hβ
    have h1 : 0 < 1 + β := by linarith [hβ.1]
    have h2 : 0 < 1 - (2 + β) * α₂ := by nlinarith [hβ.2]
    positivity
  have hneg : ∀ x y, βh ≤ x → x ≤ y → y ≤ 1 → ∫ β in x..y, harmanTwoPrimeKernel α₂ β ≤ 0 := by
    intro x y hx hxy hy
    have := integral_nonneg (μ := MeasureTheory.volume) hxy (f := fun β => -harmanTwoPrimeKernel α₂ β)
      (fun β hβ => by
        have hβ0 : 0 < β := by linarith [hβ.1]
        have hlog : log β ≤ 0 := Real.log_nonpos hβ0.le (by linarith [hβ.2])
        have hd := hden β ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
        simp only [harmanTwoPrimeKernel]
        have : log β / ((1 + β) * (1 - (2 + β) * α₂)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog hd.le
        linarith)
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hpos : ∀ x y, 1 ≤ x → x ≤ y → y ≤ B → 0 ≤ ∫ β in x..y, harmanTwoPrimeKernel α₂ β := by
    intro x y hx hxy hy
    refine integral_nonneg hxy (fun β hβ => ?_)
    have hlog : 0 ≤ log β := Real.log_nonneg (by linarith [hβ.1])
    exact div_nonneg hlog (hden β ⟨by linarith [hβ.1], by linarith [hβ.2]⟩).le
  rcases le_total βl 1 with hl | hl
  · linarith [hneg βh βl le_rfl hβhl hl, hpos 1 B le_rfl hB1 le_rfl]
  · rw [← integral_add_adjacent_intervals (ii βh 1 le_rfl hβh1 hB1) (ii 1 βl hβh1 hl hβlB),
      ← integral_add_adjacent_intervals (ii 1 βl hβh1 hl hβlB) (ii βl B (hβhl) hβlB le_rfl)]
    linarith [hneg βh 1 le_rfl hβh1 le_rfl, hpos βl B hl hβlB le_rfl]

/-- On a strip `a ≤ α₂ ≤ b` the kernel integral lies below the chord through its values at the
ends (convexity of `x ↦ 1/(1 - (2+β)x)`). -/
theorem integral_harmanTwoPrimeKernel_le_chord {a b α₂ B : ℝ} (ha : 0 < a) (hab : a < b)
    (hα : α₂ ∈ Set.Icc a b) (hB1 : 1 ≤ B) (hBb : (2 + B) * b < 1) :
    ∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel α₂ β ≤
      ((b - α₂) * (∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel a β)
        + (α₂ - a) * (∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel b β)) / (b - a) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hcont : ∀ c, 0 ≤ c → c ≤ b → ContinuousOn (harmanTwoPrimeKernel c) (Set.Icc 1 B) :=
    fun c hc0 hcb => continuousOn_harmanTwoPrimeKernel one_pos
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcb (by linarith)) hBb) hc0
  have ia := (hcont a ha.le hab.le).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hB1
  have ib := (hcont b (by linarith) le_rfl).intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hB1
  have iα := (hcont α₂ (by linarith [hα.1]) hα.2).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) hB1
  have hlin : ((b - α₂) * (∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel a β)
        + (α₂ - a) * (∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel b β)) / (b - a) =
      ∫ β in (1 : ℝ)..B, ((b - α₂) * harmanTwoPrimeKernel a β
        + (α₂ - a) * harmanTwoPrimeKernel b β) / (b - a) := by
    rw [intervalIntegral.integral_div, integral_add (ia.const_mul _) (ib.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hlin]
  refine integral_mono_on hB1 iα (((ia.const_mul _).add (ib.const_mul _)).div_const _) ?_
  intro β hβ
  have hβ1 : 1 ≤ β := hβ.1
  have hlog : 0 ≤ log β / (1 + β) := div_nonneg (Real.log_nonneg hβ1) (by linarith)
  have ta : 0 < 1 - (2 + β) * a := by nlinarith [hβ.2]
  have tb : 0 < 1 - (2 + β) * b := by nlinarith [hβ.2]
  have tx : 0 < 1 - (2 + β) * α₂ := by nlinarith [hβ.2, hα.2]
  have hch := one_div_le_chord (a := 1 - (2 + β) * b) (b := 1 - (2 + β) * a)
    (x := 1 - (2 + β) * α₂) tb (by nlinarith [hα.2]) (by nlinarith [hα.1])
  have e : ((1 - (2 + β) * b) + (1 - (2 + β) * a) - (1 - (2 + β) * α₂))
      / ((1 - (2 + β) * b) * (1 - (2 + β) * a))
      = ((b - α₂) / (1 - (2 + β) * a) + (α₂ - a) / (1 - (2 + β) * b)) / (b - a) := by
    field_simp
    ring
  rw [e] at hch
  have hk : ∀ c, harmanTwoPrimeKernel c β = log β / (1 + β) * (1 / (1 - (2 + β) * c)) := by
    intro c; unfold harmanTwoPrimeKernel; field_simp
  rw [hk α₂, hk a, hk b]
  have := mul_le_mul_of_nonneg_left hch hlog
  calc log β / (1 + β) * (1 / (1 - (2 + β) * α₂))
      ≤ log β / (1 + β) * (((b - α₂) / (1 - (2 + β) * a) + (α₂ - a) / (1 - (2 + β) * b))
          / (b - a)) := this
    _ = ((b - α₂) * (log β / (1 + β) * (1 / (1 - (2 + β) * a)))
          + (α₂ - a) * (log β / (1 + β) * (1 / (1 - (2 + β) * b)))) / (b - a) := by
        field_simp

/-- The three-affine envelope bound for the kernel on a `β`-cell. -/
noncomputable def harmanTwoPrimeCellBound (c c₁ c₂ m U : ℝ) : ℝ :=
  let p := U - 1
  let q := 1 / m
  let r := (1 + c₁ + c₂) / ((1 + c₁) * (1 + c₂))
  let s := -1 / ((1 + c₁) * (1 + c₂))
  let t₁ := 1 - (2 + c₁) * c
  let t₂ := 1 - (2 + c₂) * c
  let u := (1 - 2 * c - c * (c₁ + c₂)) / (t₁ * t₂)
  let v := c / (t₁ * t₂)
  p * r * u * (c₂ - c₁) + (p * r * v + p * s * u + q * r * u) * (c₂ ^ 2 - c₁ ^ 2) / 2
    + (p * s * v + q * r * v + q * s * u) * (c₂ ^ 3 - c₁ ^ 3) / 3
    + q * s * v * (c₂ ^ 4 - c₁ ^ 4) / 4

theorem integral_harmanTwoPrimeKernel_cell_le {c c₁ c₂ m U : ℝ} (hc : 0 ≤ c) (h1 : 1 ≤ c₁)
    (h12 : c₁ < c₂) (hm : 0 < m) (hU : log m ≤ U) (hc2 : (2 + c₂) * c < 1) :
    ∫ β in c₁..c₂, harmanTwoPrimeKernel c β ≤ harmanTwoPrimeCellBound c c₁ c₂ m U := by
  unfold harmanTwoPrimeCellBound
  simp only
  rw [← integral_affine_mul_affine_mul_affine]
  have hcont := continuousOn_harmanTwoPrimeKernel (α₂ := c) (c₁ := c₁) (c₂ := c₂) (by linarith)
    hc2 hc
  refine integral_mono_on h12.le (hcont.intervalIntegrable_of_Icc h12.le)
    ((by fun_prop : Continuous fun x : ℝ => (U - 1 + 1 / m * x)
      * ((1 + c₁ + c₂) / ((1 + c₁) * (1 + c₂)) + -1 / ((1 + c₁) * (1 + c₂)) * x)
      * ((1 - 2 * c - c * (c₁ + c₂)) / ((1 - (2 + c₁) * c) * (1 - (2 + c₂) * c))
        + c / ((1 - (2 + c₁) * c) * (1 - (2 + c₂) * c)) * x)).intervalIntegrable _ _) ?_
  intro β hβ
  have hβ0 : 0 < β := by linarith [hβ.1]
  have hlog0 : 0 ≤ log β := Real.log_nonneg (by linarith [hβ.1])
  have htan : log β ≤ U - 1 + 1 / m * β := by
    have := log_le_tangent_of_le hβ0 hm hU
    have e : (β - m) / m = 1 / m * β - 1 := by field_simp
    linarith
  have t1 : 0 < 1 - (2 + c₁) * c := by nlinarith
  have t2 : 0 < 1 - (2 + c₂) * c := by linarith
  have tβ : 0 < 1 - (2 + β) * c := by nlinarith [hβ.2]
  have hch2 := one_div_le_chord (a := 1 + c₁) (b := 1 + c₂) (x := 1 + β) (by linarith)
    (by linarith [hβ.1]) (by linarith [hβ.2])
  have e2 : (1 + c₁ + (1 + c₂) - (1 + β)) / ((1 + c₁) * (1 + c₂))
      = (1 + c₁ + c₂) / ((1 + c₁) * (1 + c₂)) + -1 / ((1 + c₁) * (1 + c₂)) * β := by
    field_simp; ring
  rw [e2] at hch2
  have hch3 := one_div_le_chord (a := 1 - (2 + c₂) * c) (b := 1 - (2 + c₁) * c)
    (x := 1 - (2 + β) * c) t2 (by nlinarith [hβ.2]) (by nlinarith [hβ.1])
  have e3 : (1 - (2 + c₂) * c + (1 - (2 + c₁) * c) - (1 - (2 + β) * c))
      / ((1 - (2 + c₂) * c) * (1 - (2 + c₁) * c))
      = (1 - 2 * c - c * (c₁ + c₂)) / ((1 - (2 + c₁) * c) * (1 - (2 + c₂) * c))
        + c / ((1 - (2 + c₁) * c) * (1 - (2 + c₂) * c)) * β := by
    field_simp; ring
  rw [e3] at hch3
  have hf2 : 0 < 1 / (1 + β) := by
    have : 0 < 1 + β := by linarith
    positivity
  have hf3 : 0 < 1 / (1 - (2 + β) * c) := by positivity
  have hk : harmanTwoPrimeKernel c β = log β * (1 / (1 + β)) * (1 / (1 - (2 + β) * c)) := by
    unfold harmanTwoPrimeKernel; field_simp
  rw [hk]
  have hT : 0 ≤ U - 1 + 1 / m * β := le_trans hlog0 htan
  calc log β * (1 / (1 + β)) * (1 / (1 - (2 + β) * c))
      ≤ (U - 1 + 1 / m * β) * (1 / (1 + β)) * (1 / (1 - (2 + β) * c)) := by
        gcongr
    _ ≤ (U - 1 + 1 / m * β)
          * ((1 + c₁ + c₂) / ((1 + c₁) * (1 + c₂)) + -1 / ((1 + c₁) * (1 + c₂)) * β)
          * (1 / (1 - (2 + β) * c)) := by gcongr
    _ ≤ _ := by
        have h2' : 0 ≤ (1 + c₁ + c₂) / ((1 + c₁) * (1 + c₂)) + -1 / ((1 + c₁) * (1 + c₂)) * β :=
          le_trans hf2.le hch2
        gcongr

/-- The section on a strip `a ≤ α₂ ≤ b`: at most `30κ` plus the chord through upper bounds for
the kernel integrals at the two ends, up to a common `β`-cut `B`. -/
theorem harmanDiscardTwoPrimeSection_le_strip {κ a b B Ga Gb α₂ : ℝ} (hκ : 0 ≤ κ)
    (hκ1 : κ ≤ 1 / 1000) (ha : 2 / 11 ≤ a) (hab : a < b) (hb : b ≤ (1 + κ) / 4)
    (hα : α₂ ∈ Set.Icc a b) (hB1 : 1 ≤ B) (hBb : (2 + B) * b < 1)
    (hBlo : 1 ≤ (3 + B) * a ∨ (3 / 4 + κ ≤ (2 + B) * a ∧ κ ≤ (B - 2) * a))
    (hGa : ∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel a β ≤ Ga)
    (hGb : ∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel b β ≤ Gb) :
    harmanDiscardTwoPrimeSection κ α₂ ≤ 30 * κ + ((b - α₂) * Ga + (α₂ - a) * Gb) / (b - a) := by
  have h0 : 2 / 11 ≤ α₂ := ha.trans hα.1
  have h1 : α₂ ≤ (1 + κ) / 4 := hα.2.trans hb
  have ha0 : 0 < α₂ := by linarith
  have hsplit := harmanDiscardTwoPrimeSection_le hκ hκ1 h0 h1
  rw [harmanTwoPrimeMain_eq hκ hκ1 h0 h1] at hsplit
  set lo := harmanDiscardLow κ α₂ with hlo
  set hi := harmanDiscardHighTwo κ α₂ with hhi
  have hlh : lo ≤ hi := harmanDiscardLow_le_highTwo hκ ha0.le h1
  have hlo1 : α₂ ≤ lo := le_max_left _ _
  have hlo2 : min (1 / 4 - κ) (1 - κ - 4 * α₂) ≤ lo := le_max_right _ _
  have hhi1 : hi ≤ 1 + κ - 3 * α₂ := min_le_right _ _
  have hhi3 : 1 - 3 * α₂ ≤ hi := le_min (by linarith) (by linarith)
  have hβh0 : 0 < (1 - 2 * α₂ - hi) / α₂ := div_pos (by linarith) ha0
  have hβh1 : (1 - 2 * α₂ - hi) / α₂ ≤ 1 := by
    rw [div_le_one ha0]; linarith
  have hβhl : (1 - 2 * α₂ - hi) / α₂ ≤ (1 - 2 * α₂ - lo) / α₂ :=
    div_le_div_of_nonneg_right (by linarith) ha0.le
  have hβlB : (1 - 2 * α₂ - lo) / α₂ ≤ B := by
    rw [div_le_iff₀ ha0]
    rcases hBlo with h | ⟨h2, h3⟩
    · have : 1 ≤ (3 + B) * α₂ := h.trans (mul_le_mul_of_nonneg_left hα.1 (by linarith))
      nlinarith
    · have hB2 : 2 ≤ B := by
        by_contra hneg
        have : B - 2 < 0 := by linarith [not_le.mp hneg]
        nlinarith
      have h2' : 3 / 4 + κ ≤ (2 + B) * α₂ :=
        h2.trans (mul_le_mul_of_nonneg_left hα.1 (by linarith))
      have h3' : κ ≤ (B - 2) * α₂ := h3.trans (mul_le_mul_of_nonneg_left hα.1 (by linarith))
      have : 1 - (2 + B) * α₂ ≤ min (1 / 4 - κ) (1 - κ - 4 * α₂) :=
        le_min (by linarith) (by nlinarith)
      nlinarith
  have hBα : (2 + B) * α₂ < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hα.2 (by linarith)) hBb
  have hr := integral_harmanTwoPrimeKernel_le ha0 hβh0 hβh1 hβhl hβlB hB1 hBα
  have hch := integral_harmanTwoPrimeKernel_le_chord (by linarith) hab hα hB1 hBb
  have hba : 0 < b - a := sub_pos.2 hab
  have hmono : ((b - α₂) * (∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel a β)
        + (α₂ - a) * (∫ β in (1 : ℝ)..B, harmanTwoPrimeKernel b β)) / (b - a)
      ≤ ((b - α₂) * Ga + (α₂ - a) * Gb) / (b - a) := by
    apply div_le_div_of_nonneg_right _ hba.le
    have := mul_le_mul_of_nonneg_left hGa (sub_nonneg.2 hα.2)
    have := mul_le_mul_of_nonneg_left hGb (sub_nonneg.2 hα.1)
    linarith
  linarith

/-- The kernel on the wedge `[Bb, Bmax]` of a strip is at most its value bound at the corner. -/
theorem harmanTwoPrimeKernel_le_corner {x β Bb Bmax b U : ℝ} (hx0 : 0 ≤ x) (hxb : x ≤ b)
    (hβ1 : Bb ≤ β) (hβ2 : β ≤ Bmax) (hB1 : 1 ≤ Bb) (hBm : (2 + Bmax) * b < 1)
    (hU : log Bmax ≤ U) :
    harmanTwoPrimeKernel x β ≤ U / ((1 + Bb) * (1 - (2 + Bmax) * b)) := by
  have hβ0 : 0 < β := by linarith
  have hlog0 : 0 ≤ log β := Real.log_nonneg (by linarith)
  have hlogU : log β ≤ U := (Real.log_le_log hβ0 hβ2).trans hU
  have h1 : 0 < 1 - (2 + Bmax) * b := by linarith
  have h2 : 1 - (2 + Bmax) * b ≤ 1 - (2 + β) * x := by
    have : (2 + β) * x ≤ (2 + Bmax) * b :=
      mul_le_mul (by linarith) hxb hx0 (by linarith)
    linarith
  have h3 : 1 + Bb ≤ 1 + β := by linarith
  have hpos : 0 < (1 + β) * (1 - (2 + β) * x) := mul_pos (by linarith) (by linarith)
  unfold harmanTwoPrimeKernel
  calc log β / ((1 + β) * (1 - (2 + β) * x))
      ≤ U / ((1 + β) * (1 - (2 + β) * x)) :=
        div_le_div_of_nonneg_right hlogU hpos.le
    _ ≤ U / ((1 + Bb) * (1 - (2 + Bmax) * b)) := by
        apply div_le_div_of_nonneg_left (hlog0.trans hlogU) (by positivity)
        exact mul_le_mul h3 h2 h1.le (by linarith)

/-- The section on a strip, with the moving `β`-cut split into a fixed range `[1, Bb]` (chord
between the strip ends) and a thin wedge `[Bb, Bb + λ(1/α₂ - 1/b)]` (bounded at its corner). -/
theorem harmanDiscardTwoPrimeSection_le_wedge {κ a b Bb lam Ga Gb U α₂ : ℝ} (hκ : 0 ≤ κ)
    (hκ1 : κ ≤ 1 / 1000) (ha : 2 / 11 ≤ a) (hab : a < b) (hb : b ≤ (1 + κ) / 4)
    (hα : α₂ ∈ Set.Icc a b) (hB1 : 1 ≤ Bb) (hlam : 0 ≤ lam)
    (hBb : (2 + (Bb + lam * (1 / a - 1 / b))) * b < 1)
    (hlo : ∀ x ∈ Set.Icc a b, 1 - (2 + Bb) * x - lam * (1 - x / b) ≤ harmanDiscardLow κ x)
    (hU : log (Bb + lam * (1 / a - 1 / b)) ≤ U)
    (hGa : ∫ β in (1 : ℝ)..Bb, harmanTwoPrimeKernel a β ≤ Ga)
    (hGb : ∫ β in (1 : ℝ)..Bb, harmanTwoPrimeKernel b β ≤ Gb) :
    harmanDiscardTwoPrimeSection κ α₂ ≤ 30 * κ + ((b - α₂) * Ga + (α₂ - a) * Gb) / (b - a)
      + U / ((1 + Bb) * (1 - (2 + (Bb + lam * (1 / a - 1 / b))) * b)) * lam * (b - α₂)
        / (a * b) := by
  have h0 : 2 / 11 ≤ α₂ := ha.trans hα.1
  have h1 : α₂ ≤ (1 + κ) / 4 := hα.2.trans hb
  have ha0 : 0 < α₂ := by linarith
  have ha0' : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hsplit := harmanDiscardTwoPrimeSection_le hκ hκ1 h0 h1
  rw [harmanTwoPrimeMain_eq hκ hκ1 h0 h1] at hsplit
  set lo := harmanDiscardLow κ α₂ with hlo'
  set hi := harmanDiscardHighTwo κ α₂ with hhi
  set Bmax := Bb + lam * (1 / a - 1 / b) with hBmax
  set B' := Bb + lam * (1 / α₂ - 1 / b) with hB'
  have hlh : lo ≤ hi := harmanDiscardLow_le_highTwo hκ ha0.le h1
  have hhi1 : hi ≤ 1 + κ - 3 * α₂ := min_le_right _ _
  have hhi3 : 1 - 3 * α₂ ≤ hi := le_min (by linarith) (by linarith)
  have hinv1 : 1 / α₂ - 1 / b ≤ 1 / a - 1 / b := by
    have := one_div_le_one_div_of_le ha0' hα.1; linarith
  have hinv0 : 0 ≤ 1 / α₂ - 1 / b := by
    have := one_div_le_one_div_of_le ha0 hα.2; linarith
  have hBB' : Bb ≤ B' := by have := mul_nonneg hlam hinv0; linarith
  have hB'm : B' ≤ Bmax := by have := mul_le_mul_of_nonneg_left hinv1 hlam; linarith
  have hβh0 : 0 < (1 - 2 * α₂ - hi) / α₂ := div_pos (by linarith) ha0
  have hβh1 : (1 - 2 * α₂ - hi) / α₂ ≤ 1 := by rw [div_le_one ha0]; linarith
  have hβhl : (1 - 2 * α₂ - hi) / α₂ ≤ (1 - 2 * α₂ - lo) / α₂ :=
    div_le_div_of_nonneg_right (by linarith) ha0.le
  have hβlB : (1 - 2 * α₂ - lo) / α₂ ≤ B' := by
    rw [div_le_iff₀ ha0]
    have hl := hlo α₂ hα
    have e : 1 - (2 + Bb) * α₂ - lam * (1 - α₂ / b) = 1 - 2 * α₂ - B' * α₂ := by
      rw [hB']; field_simp; ring
    rw [e] at hl
    linarith
  have hBα : (2 + B') * α₂ < 1 := by
    have : (2 + B') * α₂ ≤ (2 + Bmax) * b :=
      mul_le_mul (by linarith) hα.2 ha0.le (by linarith)
    linarith
  have hBmb : (2 + Bmax) * b < 1 := hBb
  have hr := integral_harmanTwoPrimeKernel_le ha0 hβh0 hβh1 hβhl hβlB (hB1.trans hBB') hBα
  have hc : ContinuousOn (harmanTwoPrimeKernel α₂) (Set.Icc 1 B') :=
    continuousOn_harmanTwoPrimeKernel one_pos hBα ha0.le
  have i1 : IntervalIntegrable (harmanTwoPrimeKernel α₂) MeasureTheory.volume 1 Bb :=
    (hc.mono (Set.Icc_subset_Icc le_rfl hBB')).intervalIntegrable_of_Icc hB1
  have i2 : IntervalIntegrable (harmanTwoPrimeKernel α₂) MeasureTheory.volume Bb B' :=
    (hc.mono (Set.Icc_subset_Icc hB1 le_rfl)).intervalIntegrable_of_Icc hBB'
  rw [← integral_add_adjacent_intervals i1 i2] at hr
  set Kmax := U / ((1 + Bb) * (1 - (2 + Bmax) * b)) with hKmax
  have hwedge : ∫ β in Bb..B', harmanTwoPrimeKernel α₂ β ≤ (B' - Bb) * Kmax := by
    calc ∫ β in Bb..B', harmanTwoPrimeKernel α₂ β ≤ ∫ _ in Bb..B', Kmax :=
          integral_mono_on hBB' i2 intervalIntegrable_const (fun β hβ =>
            harmanTwoPrimeKernel_le_corner ha0.le hα.2 hβ.1 (hβ.2.trans hB'm) hB1 hBmb hU)
      _ = (B' - Bb) * Kmax := by rw [integral_const, smul_eq_mul]
  have hK0 : 0 ≤ Kmax := by
    have hU0 : 0 ≤ U := (Real.log_nonneg (by linarith)).trans hU
    have : 0 < 1 - (2 + Bmax) * b := by linarith
    positivity
  have hB'b : B' - Bb ≤ lam * (b - α₂) / (a * b) := by
    have e : B' - Bb = lam * (b - α₂) / (α₂ * b) := by rw [hB']; field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_left (mul_nonneg hlam (sub_nonneg.2 hα.2)) (by positivity)
    exact mul_le_mul_of_nonneg_right hα.1 hb0.le
  have hdiff : 0 ≤ 1 / a - 1 / b := by
    have := one_div_le_one_div_of_le ha0' hab.le; linarith
  have hBbm : Bb ≤ Bmax := by have := mul_nonneg hlam hdiff; linarith
  have hBbb : (2 + Bb) * b < 1 := by
    have : (2 + Bb) * b ≤ (2 + Bmax) * b := mul_le_mul_of_nonneg_right (by linarith) hb0.le
    linarith
  have hch := integral_harmanTwoPrimeKernel_le_chord (a := a) (b := b) (α₂ := α₂) (B := Bb)
    ha0' hab hα hB1 hBbb
  have hba : 0 < b - a := sub_pos.2 hab
  have hmono : ((b - α₂) * (∫ β in (1 : ℝ)..Bb, harmanTwoPrimeKernel a β)
        + (α₂ - a) * (∫ β in (1 : ℝ)..Bb, harmanTwoPrimeKernel b β)) / (b - a)
      ≤ ((b - α₂) * Ga + (α₂ - a) * Gb) / (b - a) := by
    apply div_le_div_of_nonneg_right _ hba.le
    have := mul_le_mul_of_nonneg_left hGa (sub_nonneg.2 hα.2)
    have := mul_le_mul_of_nonneg_left hGb (sub_nonneg.2 hα.1)
    linarith
  have hwedge2 : (B' - Bb) * Kmax ≤ Kmax * lam * (b - α₂) / (a * b) := by
    have := mul_le_mul_of_nonneg_right hB'b hK0
    have e : lam * (b - α₂) / (a * b) * Kmax = Kmax * lam * (b - α₂) / (a * b) := by ring
    linarith
  linarith

theorem harmanDiscardLow_wedge_one {κ a b : ℝ} (hκ1 : κ ≤ 1 / 1000) (hb0 : 0 < b)
    (hb : b ≤ 3 / 16) :
    ∀ x ∈ Set.Icc a b, 1 - (2 + ((3 / 4 + κ) / b - 2)) * x - (3 / 4 + κ) * (1 - x / b)
      ≤ harmanDiscardLow κ x := by
  intro x hx
  rw [harmanDiscardLow_eq_one hκ1 (hx.2.trans hb)]
  have e : 1 - (2 + ((3 / 4 + κ) / b - 2)) * x - (3 / 4 + κ) * (1 - x / b) = 1 / 4 - κ := by
    field_simp; ring
  rw [e]

theorem harmanDiscardLow_wedge_two {κ a b : ℝ} (hb0 : 0 < b) (ha : 3 / 16 ≤ a)
    (hb : b ≤ (1 - κ) / 5) :
    ∀ x ∈ Set.Icc a b, 1 - (2 + (2 + κ / b)) * x - κ * (1 - x / b) ≤ harmanDiscardLow κ x := by
  intro x hx
  rw [harmanDiscardLow_eq_two (ha.trans hx.1) (hx.2.trans hb)]
  have e : 1 - (2 + (2 + κ / b)) * x - κ * (1 - x / b) = 1 - κ - 4 * x := by
    field_simp; ring
  rw [e]

theorem harmanDiscardLow_wedge_self {κ a b : ℝ} (hb0 : 0 < b) (ha : (1 - κ) / 5 ≤ a) :
    ∀ x ∈ Set.Icc a b, 1 - (2 + (1 / b - 3)) * x - 1 * (1 - x / b) ≤ harmanDiscardLow κ x := by
  intro x hx
  rw [harmanDiscardLow_eq_self (ha.trans hx.1)]
  have e : 1 - (2 + (1 / b - 3)) * x - 1 * (1 - x / b) = x := by field_simp; ring
  rw [e]

/-- Beyond `α₂ = 1/4` the two-prime-cofactor section is only the `κ`-perturbation. -/
theorem harmanDiscardTwoPrimeSection_le_tail {κ α₂ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h0 : 1 / 4 ≤ α₂) (h1 : α₂ ≤ (1 + κ) / 4) :
    harmanDiscardTwoPrimeSection κ α₂ ≤ 30 * κ := by
  have h0' : 2 / 11 ≤ α₂ := by linarith
  have ha0 : 0 < α₂ := by linarith
  have hsplit := harmanDiscardTwoPrimeSection_le hκ hκ1 h0' h1
  rw [harmanTwoPrimeMain_eq hκ hκ1 h0' h1] at hsplit
  set lo := harmanDiscardLow κ α₂ with hlo
  set hi := harmanDiscardHighTwo κ α₂ with hhi
  have hlh : lo ≤ hi := harmanDiscardLow_le_highTwo hκ ha0.le h1
  have hlo1 : α₂ ≤ lo := le_max_left _ _
  have hhi1 : hi ≤ 1 + κ - 3 * α₂ := min_le_right _ _
  have hhi3 : 1 - 3 * α₂ ≤ hi := le_min (by linarith) (by linarith)
  have hβh0 : 0 < (1 - 2 * α₂ - hi) / α₂ := div_pos (by linarith) ha0
  have hβh1 : (1 - 2 * α₂ - hi) / α₂ ≤ 1 := by rw [div_le_one ha0]; linarith
  have hβhl : (1 - 2 * α₂ - hi) / α₂ ≤ (1 - 2 * α₂ - lo) / α₂ :=
    div_le_div_of_nonneg_right (by linarith) ha0.le
  have hβl1 : (1 - 2 * α₂ - lo) / α₂ ≤ 1 := by rw [div_le_one ha0]; linarith
  have hr := integral_harmanTwoPrimeKernel_le ha0 hβh0 hβh1 hβhl hβl1 le_rfl (by linarith)
  rw [intervalIntegral.integral_same] at hr
  linarith

/-- The affine upper envelope of the section on a strip (`harmanDiscardTwoPrimeSection_le_wedge`). -/
def harmanTwoPrimeStripEnvelope (κ a b Bb lam Ga Gb U x : ℝ) : ℝ :=
  30 * κ + ((b - x) * Ga + (x - a) * Gb) / (b - a)
    + U / ((1 + Bb) * (1 - (2 + (Bb + lam * (1 / a - 1 / b))) * b)) * lam * (b - x) / (a * b)

theorem harmanTwoPrimeStripEnvelope_affine {κ a b Bb lam Ga Gb U : ℝ} (hab : a < b) (x : ℝ) :
    harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U x =
      harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0
        + (harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 1
          - harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0) * x := by
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  unfold harmanTwoPrimeStripEnvelope
  field_simp
  ring

theorem integral_harmanTwoPrimeStripEnvelope_div_le {κ a b Bb lam Ga Gb U : ℝ} (ha : 0 < a)
    (hab : a < b) (hA : 0 ≤ harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U a)
    (hB : 0 ≤ harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U b) :
    ∫ x in a..b, harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U x / x ≤
      harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0 * ((a + b) / (a * b)) * (b - a)
        + (harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0 * (-1 / (a * b))
          + (harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 1
            - harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0) * ((a + b) / (a * b)))
          * (b ^ 2 - a ^ 2) / 2
        + (harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 1
          - harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0) * (-1 / (a * b))
          * (b ^ 3 - a ^ 3) / 3 := by
  have e : ∀ x, harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U x =
      harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0
        + (harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 1
          - harmanTwoPrimeStripEnvelope κ a b Bb lam Ga Gb U 0) * x :=
    harmanTwoPrimeStripEnvelope_affine hab
  rw [e a] at hA
  rw [e b] at hB
  rw [integral_congr (fun x _ => by rw [e x])]
  exact integral_affine_div_le_chord ha hab.le hA hB

end

end RHTower.Sieve
