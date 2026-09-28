import GaloisForLFunctions.RHTower.Sieve.AffineEnvelopeQuadrature

/-!
# The discarded Harman terms with a prime cofactor: density bound

In Matomäki–Teräväinen's minorant, the discarded second Buchstab term counts
`n = q₁ q₂ m` with primes `X^{2/11} ≤ q₂ < q₁ < 2X^{1/2}`, `q₁ ≥ X^{1/4-2ε}` or
`q₁ q₂⁴ ≥ X^{1-2ε}`, and `m` free of prime factors below `q₂`.  With `αᵢ = log qᵢ / log y`, the
part with `m` prime has density

`∫∫ dα₁ dα₂ / (α₁ α₂ (1 - α₁ - α₂))`

over `2/11 ≤ α₂ ≤ α₁ ≤ 1/2`, `α₁ + 2α₂ ≤ 1`, `α₁ ≥ 1/4` or `α₁ + 4α₂ ≥ 1`.  The boundaries are
enlarged by `κ ≥ 0`.  The inner integral is `log(α₁/(1-α₂-α₁))/(1-α₂)` between the section ends;
the outer integral splits at `α₂ = 3/16`, `(1-κ)/5`, `1/4` into four pieces.  On each of 13 cells the
section is below `(A + Bα₂)/(1 - α₂)` (tangent of the concave logarithms, chords of the convex
ones), and the envelope integrals against `dα₂/α₂` sum to at most `0.8896` at `κ = 10⁻⁶`.
-/

namespace RHTower.Sieve

open Real intervalIntegral

noncomputable section

/-- Lower end of the `α₁`-section. -/
def harmanDiscardLow (κ α₂ : ℝ) : ℝ := max α₂ (min (1 / 4 - κ) (1 - κ - 4 * α₂))

/-- Upper end of the `α₁`-section. -/
def harmanDiscardHigh (κ α₂ : ℝ) : ℝ := min (1 / 2 + κ) (1 + κ - 2 * α₂)

/-- The inner integral over `α₁`. -/
def harmanDiscardPrimeInner (κ α₂ : ℝ) : ℝ :=
  ∫ α₁ in harmanDiscardLow κ α₂..harmanDiscardHigh κ α₂, 1 / (α₁ * (1 - α₁ - α₂))

/-- Density of the discarded terms `n = q₁ q₂ p` with `p` prime. -/
def harmanDiscardPrimeDensity (κ : ℝ) : ℝ :=
  ∫ α₂ in (2 / 11 : ℝ)..((1 + κ) / 3), harmanDiscardPrimeInner κ α₂ / α₂

/-- The primitive of the inner integrand. -/
def harmanLogitPrimitive (α₂ t : ℝ) : ℝ := log t - log (1 - α₂ - t)

theorem harmanDiscardLow_le_high {κ α₂ : ℝ} (hκ : 0 ≤ κ) (h1 : α₂ ≤ (1 + κ) / 3) :
    harmanDiscardLow κ α₂ ≤ harmanDiscardHigh κ α₂ := by
  unfold harmanDiscardLow harmanDiscardHigh
  refine max_le (le_min (by linarith) (by linarith)) ?_
  exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_left _ _).trans (by linarith))

theorem harmanDiscardPrimeInner_eq {κ α₂ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h0 : 2 / 11 ≤ α₂) (h1 : α₂ ≤ (1 + κ) / 3) :
    harmanDiscardPrimeInner κ α₂ =
      (harmanLogitPrimitive α₂ (harmanDiscardHigh κ α₂)
        - harmanLogitPrimitive α₂ (harmanDiscardLow κ α₂)) / (1 - α₂) := by
  have hlh := harmanDiscardLow_le_high hκ h1
  have hlo : α₂ ≤ harmanDiscardLow κ α₂ := le_max_left _ _
  have hhi : harmanDiscardHigh κ α₂ ≤ 1 + κ - 2 * α₂ := min_le_right _ _
  have hα : 0 < 1 - α₂ := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (harmanDiscardLow κ α₂) (harmanDiscardHigh κ α₂),
      HasDerivAt (fun t => (log t - log (1 - α₂ - t)) / (1 - α₂)) (1 / (t * (1 - t - α₂))) t := by
    intro t ht
    rw [Set.uIcc_of_le hlh] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : 0 < 1 - α₂ - t := by linarith [ht.2]
    have h1 := Real.hasDerivAt_log ht0.ne'
    have h2 := ((hasDerivAt_id t).const_sub (1 - α₂)).log ht1.ne'
    have h3 := (h1.sub h2).div_const (1 - α₂)
    refine h3.congr_deriv ?_
    have hne1 : 1 - α₂ - t ≠ 0 := ht1.ne'
    have hne2 : 1 - t - α₂ ≠ 0 := by linarith
    have hne3 : 1 - α₂ ≠ 0 := hα.ne'
    simp only [id]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => 1 / (t * (1 - t - α₂)))
      (Set.uIcc (harmanDiscardLow κ α₂) (harmanDiscardHigh κ α₂)) := by
    rw [Set.uIcc_of_le hlh]
    refine continuousOn_const.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id |>.sub
      continuousOn_const)) ?_
    intro t ht
    have : 0 < t := by linarith [ht.1]
    have : 0 < 1 - t - α₂ := by linarith [ht.2]
    positivity
  unfold harmanDiscardPrimeInner
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  unfold harmanLogitPrimitive
  ring

/-- The section numerator on `[2/11, 3/16]`. -/
def harmanPrimePhiOne (κ α : ℝ) : ℝ :=
  log (1 / 2 + κ) - log (1 / 2 - κ - α) - log (1 / 4 - κ) + log (3 / 4 + κ - α)

/-- The section numerator on `[3/16, (1-κ)/5]`. -/
def harmanPrimePhiTwo (κ α : ℝ) : ℝ :=
  log (1 / 2 + κ) - log (1 / 2 - κ - α) - log (1 - κ - 4 * α) + log (3 * α + κ)

/-- The section numerator on `[(1-κ)/5, 1/4]`. -/
def harmanPrimePhiThree (κ α : ℝ) : ℝ :=
  log (1 / 2 + κ) - log (1 / 2 - κ - α) - log α + log (1 - 2 * α)

/-- The section numerator on `[1/4, (1+κ)/3]`. -/
def harmanPrimePhiFour (κ α : ℝ) : ℝ :=
  log (1 + κ - 2 * α) - log (α - κ) - log α + log (1 - 2 * α)

theorem harmanDiscardLow_eq_one {κ α : ℝ} (hκ1 : κ ≤ 1 / 1000) (h : α ≤ 3 / 16) :
    harmanDiscardLow κ α = 1 / 4 - κ := by
  unfold harmanDiscardLow
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

theorem harmanDiscardLow_eq_two {κ α : ℝ} (h1 : 3 / 16 ≤ α) (h2 : α ≤ (1 - κ) / 5) :
    harmanDiscardLow κ α = 1 - κ - 4 * α := by
  unfold harmanDiscardLow
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem harmanDiscardLow_eq_self {κ α : ℝ} (h1 : (1 - κ) / 5 ≤ α) :
    harmanDiscardLow κ α = α := by
  unfold harmanDiscardLow
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem harmanDiscardHigh_eq_half {κ α : ℝ} (h : α ≤ 1 / 4) :
    harmanDiscardHigh κ α = 1 / 2 + κ := by
  unfold harmanDiscardHigh
  exact min_eq_left (by linarith)

theorem harmanDiscardHigh_eq_four {κ α : ℝ} (h : 1 / 4 ≤ α) :
    harmanDiscardHigh κ α = 1 + κ - 2 * α := by
  unfold harmanDiscardHigh
  exact min_eq_right (by linarith)

/-- The logit weight `1/(α(1-α)) = 1/α + 1/(1-α)`. -/
theorem div_one_sub_div_eq_logit {c α : ℝ} (h0 : α ≠ 0) (h1 : 1 - α ≠ 0) :
    c / (1 - α) / α = c * (1 / α + 1 / (1 - α)) := by
  field_simp
  ring

theorem harmanDiscardPrime_integrand_eq_one {κ α : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h0 : 2 / 11 ≤ α) (h1 : α ≤ 3 / 16) :
    harmanDiscardPrimeInner κ α / α = harmanPrimePhiOne κ α * (1 / α + 1 / (1 - α)) := by
  rw [harmanDiscardPrimeInner_eq hκ hκ1 h0 (by linarith), harmanDiscardLow_eq_one hκ1 h1,
    harmanDiscardHigh_eq_half (by linarith),
    div_one_sub_div_eq_logit (by linarith) (by linarith)]
  unfold harmanLogitPrimitive harmanPrimePhiOne
  rw [show 1 - α - (1 / 2 + κ) = 1 / 2 - κ - α by ring,
    show 1 - α - (1 / 4 - κ) = 3 / 4 + κ - α by ring]
  ring

theorem harmanDiscardPrime_integrand_eq_two {κ α : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h1 : 3 / 16 ≤ α) (h2 : α ≤ (1 - κ) / 5) :
    harmanDiscardPrimeInner κ α / α = harmanPrimePhiTwo κ α * (1 / α + 1 / (1 - α)) := by
  rw [harmanDiscardPrimeInner_eq hκ hκ1 (by linarith) (by linarith),
    harmanDiscardLow_eq_two h1 h2, harmanDiscardHigh_eq_half (by linarith),
    div_one_sub_div_eq_logit (by linarith) (by linarith)]
  unfold harmanLogitPrimitive harmanPrimePhiTwo
  rw [show 1 - α - (1 / 2 + κ) = 1 / 2 - κ - α by ring,
    show 1 - α - (1 - κ - 4 * α) = 3 * α + κ by ring]
  ring

theorem harmanDiscardPrime_integrand_eq_three {κ α : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h1 : (1 - κ) / 5 ≤ α) (h2 : α ≤ 1 / 4) :
    harmanDiscardPrimeInner κ α / α = harmanPrimePhiThree κ α * (1 / α + 1 / (1 - α)) := by
  rw [harmanDiscardPrimeInner_eq hκ hκ1 (by linarith) (by linarith),
    harmanDiscardLow_eq_self h1, harmanDiscardHigh_eq_half h2,
    div_one_sub_div_eq_logit (by linarith) (by linarith)]
  unfold harmanLogitPrimitive harmanPrimePhiThree
  rw [show 1 - α - (1 / 2 + κ) = 1 / 2 - κ - α by ring, show 1 - α - α = 1 - 2 * α by ring]
  ring

theorem harmanDiscardPrime_integrand_eq_four {κ α : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (h1 : 1 / 4 ≤ α) (h2 : α ≤ (1 + κ) / 3) :
    harmanDiscardPrimeInner κ α / α = harmanPrimePhiFour κ α * (1 / α + 1 / (1 - α)) := by
  rw [harmanDiscardPrimeInner_eq hκ hκ1 (by linarith) h2,
    harmanDiscardLow_eq_self (by linarith), harmanDiscardHigh_eq_four h1,
    div_one_sub_div_eq_logit (by linarith) (by linarith)]
  unfold harmanLogitPrimitive harmanPrimePhiFour
  rw [show 1 - α - (1 + κ - 2 * α) = α - κ by ring, show 1 - α - α = 1 - 2 * α by ring]
  ring

theorem continuousOn_harmanPrimePhiOne {κ a b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (hb : b ≤ 1 / 4) :
    ContinuousOn (harmanPrimePhiOne κ) (Set.Icc a b) := by
  unfold harmanPrimePhiOne
  refine ((ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_) continuousOn_const).add ?_)
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 / 2 - κ - α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)
  · exact ((by fun_prop : Continuous fun α : ℝ => 3 / 4 + κ - α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)

theorem continuousOn_harmanPrimePhiTwo {κ a b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (ha : 0 < a) (hb : b ≤ (1 - κ) / 5) :
    ContinuousOn (harmanPrimePhiTwo κ) (Set.Icc a b) := by
  unfold harmanPrimePhiTwo
  refine ((ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_) ?_).add ?_)
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 / 2 - κ - α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 - κ - 4 * α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)
  · exact ((by fun_prop : Continuous fun α : ℝ => 3 * α + κ).continuousOn).log
      (fun x hx => by have := hx.1; linarith)

theorem continuousOn_harmanPrimePhiThree {κ a b : ℝ} (hκ1 : κ ≤ 1 / 1000) (ha : 0 < a)
    (hb : b ≤ 1 / 4) :
    ContinuousOn (harmanPrimePhiThree κ) (Set.Icc a b) := by
  unfold harmanPrimePhiThree
  refine ((ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_) ?_).add ?_)
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 / 2 - κ - α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)
  · exact continuousOn_id.log (fun x hx => (show (0 : ℝ) < x by linarith [hx.1]).ne')
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 - 2 * α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)

theorem continuousOn_harmanPrimePhiFour {κ a b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (ha : 1 / 10 ≤ a)
    (hb : b ≤ (1 + κ) / 3) :
    ContinuousOn (harmanPrimePhiFour κ) (Set.Icc a b) := by
  unfold harmanPrimePhiFour
  refine ((ContinuousOn.sub (ContinuousOn.sub ?_ ?_) ?_).add ?_)
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 + κ - 2 * α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)
  · exact ((by fun_prop : Continuous fun α : ℝ => α - κ).continuousOn).log
      (fun x hx => by have := hx.1; linarith)
  · exact continuousOn_id.log (fun x hx => (show (0 : ℝ) < x by linarith [hx.1]).ne')
  · exact ((by fun_prop : Continuous fun α : ℝ => 1 - 2 * α).continuousOn).log
      (fun x hx => by have := hx.2; linarith)

theorem continuousOn_logit_weight {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn (fun α : ℝ => 1 / α + 1 / (1 - α)) (Set.Icc a b) := by
  refine ContinuousOn.add ?_ ?_
  · exact continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
  · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun x hx => by have := hx.2; linarith)

theorem inner_eq_phi_div_of_integrand_eq {inner Φ x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (h : inner / x = Φ * (1 / x + 1 / (1 - x))) : inner = Φ / (1 - x) := by
  have h1 : 1 - x ≠ 0 := by linarith
  have := h
  field_simp at this ⊢
  linarith

/-- Envelope constant for `harmanPrimePhiThree` on a cell. -/
def harmanPrimeThreeEnvConst (a b m U0 La1 Lb1 La2 Lb2 Um : ℝ) : ℝ :=
  U0 - chordConst La1 Lb1 a b - chordConst La2 Lb2 a b + tangentConst Um 1 (-2) m

/-- Envelope slope for `harmanPrimePhiThree` on a cell. -/
def harmanPrimeThreeEnvSlope (a b m La1 Lb1 La2 Lb2 : ℝ) : ℝ :=
  -chordSlope La1 Lb1 a b - chordSlope La2 Lb2 a b + tangentSlope 1 (-2) m

theorem harmanPrimePhiThree_le_env {κ a b m x U0 La1 Lb1 La2 Lb2 Um : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 4) (hm : m ≤ b) (hx : x ∈ Set.Icc a b)
    (hκb : κ < 1 / 4)
    (hU0 : log (1 / 2 + κ) ≤ U0) (hLa1 : La1 ≤ log (1 / 2 - κ - a))
    (hLb1 : Lb1 ≤ log (1 / 2 - κ - b)) (hLa2 : La2 ≤ log a) (hLb2 : Lb2 ≤ log b)
    (hUm : log (1 - 2 * m) ≤ Um) :
    harmanPrimePhiThree κ x ≤ harmanPrimeThreeEnvConst a b m U0 La1 Lb1 La2 Lb2 Um
      + harmanPrimeThreeEnvSlope a b m La1 Lb1 La2 Lb2 * x := by
  have h1 := neg_log_affine_le_chord' (p := 1 / 2 - κ) (q := -1) (La := La1) (Lb := Lb1) hab
    hx.1 hx.2 (by linarith) (by linarith)
    (by rw [show 1 / 2 - κ + -1 * a = 1 / 2 - κ - a by ring]; exact hLa1)
    (by rw [show 1 / 2 - κ + -1 * b = 1 / 2 - κ - b by ring]; exact hLb1)
  have h2 := neg_log_affine_le_chord' (p := 0) (q := 1) (La := La2) (Lb := Lb2) hab hx.1 hx.2
    (by linarith) (by linarith) (by rw [show (0 : ℝ) + 1 * a = a by ring]; exact hLa2)
    (by rw [show (0 : ℝ) + 1 * b = b by ring]; exact hLb2)
  have h3 := log_affine_le_tangent' (p := 1) (q := -2) (m := m) (x := x) (U := Um)
    (by linarith [hx.2]) (by linarith) (by rw [show (1 : ℝ) + -2 * m = 1 - 2 * m by ring]; exact hUm)
  rw [show 1 / 2 - κ + -1 * x = 1 / 2 - κ - x by ring] at h1
  rw [show (0 : ℝ) + 1 * x = x by ring] at h2
  rw [show (1 : ℝ) + -2 * x = 1 - 2 * x by ring] at h3
  unfold harmanPrimePhiThree harmanPrimeThreeEnvConst harmanPrimeThreeEnvSlope
  linarith

/-- The prime-cofactor section on a cell of the third piece is below `(A + Bα)/(1-α)`. -/
theorem harmanDiscardPrimeInner_le_three_cell {κ a b m U0 La1 Lb1 La2 Lb2 Um : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000) (ha : (1 - κ) / 5 ≤ a) (hab : a < b) (hb : b ≤ 1 / 4)
    (hm : m ≤ b)
    (hU0 : log (1 / 2 + κ) ≤ U0) (hLa1 : La1 ≤ log (1 / 2 - κ - a))
    (hLb1 : Lb1 ≤ log (1 / 2 - κ - b)) (hLa2 : La2 ≤ log a) (hLb2 : Lb2 ≤ log b)
    (hUm : log (1 - 2 * m) ≤ Um) :
    ∀ x ∈ Set.Icc a b, harmanDiscardPrimeInner κ x ≤
      (harmanPrimeThreeEnvConst a b m U0 La1 Lb1 La2 Lb2 Um
        + harmanPrimeThreeEnvSlope a b m La1 Lb1 La2 Lb2 * x) / (1 - x) := by
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 := by linarith [hx.2]
  rw [inner_eq_phi_div_of_integrand_eq hx0 hx1
    (harmanDiscardPrime_integrand_eq_three hκ hκ1 (ha.trans hx.1) (hx.2.trans hb))]
  exact div_le_div_of_nonneg_right (harmanPrimePhiThree_le_env (by linarith) hab hb hm hx
    (by linarith) hU0 hLa1 hLb1 hLa2 hLb2 hUm) (by linarith)

/-- Envelope constant for `harmanPrimePhiOne` on a cell. -/
def harmanPrimeOneEnvConst (κ a b m U0 L4 La1 Lb1 Um : ℝ) : ℝ :=
  U0 - L4 - chordConst La1 Lb1 a b + tangentConst Um (3 / 4 + κ) (-1) m

/-- Envelope slope for `harmanPrimePhiOne` on a cell. -/
def harmanPrimeOneEnvSlope (κ a b m La1 Lb1 : ℝ) : ℝ :=
  -chordSlope La1 Lb1 a b + tangentSlope (3 / 4 + κ) (-1) m

/-- The prime-cofactor section on a cell of the first piece is below `(A + Bα)/(1-α)`. -/
theorem harmanDiscardPrimeInner_le_one_cell {κ a b m U0 L4 La1 Lb1 Um : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000) (ha : 2 / 11 ≤ a) (hab : a < b) (hb : b ≤ 3 / 16)
    (hm : m ≤ b)
    (hU0 : log (1 / 2 + κ) ≤ U0) (hL4 : L4 ≤ log (1 / 4 - κ))
    (hLa1 : La1 ≤ log (1 / 2 - κ - a)) (hLb1 : Lb1 ≤ log (1 / 2 - κ - b))
    (hUm : log (3 / 4 + κ - m) ≤ Um) :
    ∀ x ∈ Set.Icc a b, harmanDiscardPrimeInner κ x ≤
      (harmanPrimeOneEnvConst κ a b m U0 L4 La1 Lb1 Um
        + harmanPrimeOneEnvSlope κ a b m La1 Lb1 * x) / (1 - x) := by
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 := by linarith [hx.2]
  rw [inner_eq_phi_div_of_integrand_eq hx0 hx1
    (harmanDiscardPrime_integrand_eq_one hκ hκ1 (ha.trans hx.1) (hx.2.trans hb))]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have h1 := neg_log_affine_le_chord' (p := 1 / 2 - κ) (q := -1) (La := La1) (Lb := Lb1) hab
    hx.1 hx.2 (by linarith) (by linarith)
    (by rw [show 1 / 2 - κ + -1 * a = 1 / 2 - κ - a by ring]; exact hLa1)
    (by rw [show 1 / 2 - κ + -1 * b = 1 / 2 - κ - b by ring]; exact hLb1)
  have h3 := log_affine_le_tangent' (p := 3 / 4 + κ) (q := -1) (m := m) (x := x) (U := Um)
    (by linarith [hx.2]) (by linarith)
    (by rw [show 3 / 4 + κ + -1 * m = 3 / 4 + κ - m by ring]; exact hUm)
  rw [show 1 / 2 - κ + -1 * x = 1 / 2 - κ - x by ring] at h1
  rw [show 3 / 4 + κ + -1 * x = 3 / 4 + κ - x by ring] at h3
  unfold harmanPrimePhiOne harmanPrimeOneEnvConst harmanPrimeOneEnvSlope
  linarith

/-- Envelope constant for `harmanPrimePhiTwo` on a cell. -/
def harmanPrimeTwoEnvConst (κ a b m U0 La1 Lb1 La3 Lb3 Um : ℝ) : ℝ :=
  U0 - chordConst La1 Lb1 a b - chordConst La3 Lb3 a b + tangentConst Um κ 3 m

/-- Envelope slope for `harmanPrimePhiTwo` on a cell. -/
def harmanPrimeTwoEnvSlope (κ a b m La1 Lb1 La3 Lb3 : ℝ) : ℝ :=
  -chordSlope La1 Lb1 a b - chordSlope La3 Lb3 a b + tangentSlope κ 3 m

/-- The prime-cofactor section on a cell of the second piece is below `(A + Bα)/(1-α)`. -/
theorem harmanDiscardPrimeInner_le_two_cell {κ a b m U0 La1 Lb1 La3 Lb3 Um : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000) (ha : 3 / 16 ≤ a) (hab : a < b) (hb : b ≤ (1 - κ) / 5)
    (hm : a ≤ m)
    (hU0 : log (1 / 2 + κ) ≤ U0)
    (hLa1 : La1 ≤ log (1 / 2 - κ - a)) (hLb1 : Lb1 ≤ log (1 / 2 - κ - b))
    (hLa3 : La3 ≤ log (1 - κ - 4 * a)) (hLb3 : Lb3 ≤ log (1 - κ - 4 * b))
    (hUm : log (3 * m + κ) ≤ Um) :
    ∀ x ∈ Set.Icc a b, harmanDiscardPrimeInner κ x ≤
      (harmanPrimeTwoEnvConst κ a b m U0 La1 Lb1 La3 Lb3 Um
        + harmanPrimeTwoEnvSlope κ a b m La1 Lb1 La3 Lb3 * x) / (1 - x) := by
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 := by linarith [hx.2]
  rw [inner_eq_phi_div_of_integrand_eq hx0 hx1
    (harmanDiscardPrime_integrand_eq_two hκ hκ1 (ha.trans hx.1) (hx.2.trans hb))]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have hb5 : 0 < 1 - κ - 4 * b := by linarith
  have h1 := neg_log_affine_le_chord' (p := 1 / 2 - κ) (q := -1) (La := La1) (Lb := Lb1) hab
    hx.1 hx.2 (by linarith) (by linarith)
    (by rw [show 1 / 2 - κ + -1 * a = 1 / 2 - κ - a by ring]; exact hLa1)
    (by rw [show 1 / 2 - κ + -1 * b = 1 / 2 - κ - b by ring]; exact hLb1)
  have h2 := neg_log_affine_le_chord' (p := 1 - κ) (q := -4) (La := La3) (Lb := Lb3) hab
    hx.1 hx.2 (by linarith) (by linarith)
    (by rw [show 1 - κ + -4 * a = 1 - κ - 4 * a by ring]; exact hLa3)
    (by rw [show 1 - κ + -4 * b = 1 - κ - 4 * b by ring]; exact hLb3)
  have h3 := log_affine_le_tangent' (p := κ) (q := 3) (m := m) (x := x) (U := Um)
    (by linarith [hx.1]) (by linarith)
    (by rw [show κ + 3 * m = 3 * m + κ by ring]; exact hUm)
  rw [show 1 / 2 - κ + -1 * x = 1 / 2 - κ - x by ring] at h1
  rw [show 1 - κ + -4 * x = 1 - κ - 4 * x by ring] at h2
  rw [show κ + 3 * x = 3 * x + κ by ring] at h3
  unfold harmanPrimePhiTwo harmanPrimeTwoEnvConst harmanPrimeTwoEnvSlope
  linarith

/-- Envelope constant for `harmanPrimePhiFour` on a cell. -/
def harmanPrimeFourEnvConst (κ a b m Um1 La5 Lb5 La2 Lb2 Um2 : ℝ) : ℝ :=
  tangentConst Um1 (1 + κ) (-2) m - chordConst La5 Lb5 a b - chordConst La2 Lb2 a b
    + tangentConst Um2 1 (-2) m

/-- Envelope slope for `harmanPrimePhiFour` on a cell. -/
def harmanPrimeFourEnvSlope (κ a b m La5 Lb5 La2 Lb2 : ℝ) : ℝ :=
  tangentSlope (1 + κ) (-2) m - chordSlope La5 Lb5 a b - chordSlope La2 Lb2 a b
    + tangentSlope 1 (-2) m

/-- The prime-cofactor section on a cell of the fourth piece is below `(A + Bα)/(1-α)`. -/
theorem harmanDiscardPrimeInner_le_four_cell {κ a b m Um1 La5 Lb5 La2 Lb2 Um2 : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000) (ha : 1 / 4 ≤ a) (hab : a < b) (hb : b ≤ (1 + κ) / 3)
    (hm : m ≤ b)
    (hUm1 : log (1 + κ - 2 * m) ≤ Um1)
    (hLa5 : La5 ≤ log (a - κ)) (hLb5 : Lb5 ≤ log (b - κ))
    (hLa2 : La2 ≤ log a) (hLb2 : Lb2 ≤ log b)
    (hUm2 : log (1 - 2 * m) ≤ Um2) :
    ∀ x ∈ Set.Icc a b, harmanDiscardPrimeInner κ x ≤
      (harmanPrimeFourEnvConst κ a b m Um1 La5 Lb5 La2 Lb2 Um2
        + harmanPrimeFourEnvSlope κ a b m La5 Lb5 La2 Lb2 * x) / (1 - x) := by
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 := by linarith [hx.2]
  rw [inner_eq_phi_div_of_integrand_eq hx0 hx1
    (harmanDiscardPrime_integrand_eq_four hκ hκ1 (ha.trans hx.1) (hx.2.trans hb))]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  have h1 := log_affine_le_tangent' (p := 1 + κ) (q := -2) (m := m) (x := x) (U := Um1)
    (by linarith [hx.2]) (by linarith)
    (by rw [show 1 + κ + -2 * m = 1 + κ - 2 * m by ring]; exact hUm1)
  have h2 := neg_log_affine_le_chord' (p := -κ) (q := 1) (La := La5) (Lb := Lb5) hab
    hx.1 hx.2 (by linarith) (by linarith)
    (by rw [show -κ + 1 * a = a - κ by ring]; exact hLa5)
    (by rw [show -κ + 1 * b = b - κ by ring]; exact hLb5)
  have h3 := neg_log_affine_le_chord' (p := 0) (q := 1) (La := La2) (Lb := Lb2) hab
    hx.1 hx.2 (by linarith) (by linarith)
    (by rw [show (0 : ℝ) + 1 * a = a by ring]; exact hLa2)
    (by rw [show (0 : ℝ) + 1 * b = b by ring]; exact hLb2)
  have h4 := log_affine_le_tangent' (p := 1) (q := -2) (m := m) (x := x) (U := Um2)
    (by linarith [hx.2]) (by linarith)
    (by rw [show (1 : ℝ) + -2 * m = 1 - 2 * m by ring]; exact hUm2)
  rw [show 1 + κ + -2 * x = 1 + κ - 2 * x by ring] at h1
  rw [show -κ + 1 * x = x - κ by ring] at h2
  rw [show (0 : ℝ) + 1 * x = x by ring] at h3
  rw [show (1 : ℝ) + -2 * x = 1 - 2 * x by ring] at h4
  unfold harmanPrimePhiFour harmanPrimeFourEnvConst harmanPrimeFourEnvSlope
  linarith

/-- The integral of the cell envelope `(A + Bα)/((1-α)α)`, through the chords of `1/α` and
`1/(1-α)`. -/
theorem integral_affine_div_one_sub_div_le {a b A B : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b < 1) (hA : 0 ≤ A + B * a) (hB : 0 ≤ A + B * b) :
    ∫ x in a..b, (A + B * x) / (1 - x) / x ≤ logitCellBound A B a b := by
  have heq : Set.EqOn (fun x => (A + B * x) / (1 - x) / x)
      (fun x => (A + B * x) * (1 / x + 1 / (1 - x))) (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact div_one_sub_div_eq_logit (by linarith [hx.1]) (by linarith [hx.2])
  rw [integral_congr heq]
  exact integral_mul_logit_weight_le ha hab hb (by fun_prop) (fun x _ => le_rfl) hA hB

theorem harmanDiscardPrimeDensity_eq {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000) :
    harmanDiscardPrimeDensity κ =
      (∫ α in (2 / 11 : ℝ)..(3 / 16), harmanPrimePhiOne κ α * (1 / α + 1 / (1 - α)))
      + (∫ α in (3 / 16 : ℝ)..((1 - κ) / 5), harmanPrimePhiTwo κ α * (1 / α + 1 / (1 - α)))
      + (∫ α in ((1 - κ) / 5 : ℝ)..(1 / 4), harmanPrimePhiThree κ α * (1 / α + 1 / (1 - α)))
      + (∫ α in (1 / 4 : ℝ)..((1 + κ) / 3), harmanPrimePhiFour κ α * (1 / α + 1 / (1 - α))) := by
  set F : ℝ → ℝ := fun α => harmanDiscardPrimeInner κ α / α with hF
  have e1 : Set.EqOn F (fun α => harmanPrimePhiOne κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc (2 / 11) (3 / 16)) := by
    intro α hα
    rw [Set.uIcc_of_le (by norm_num)] at hα
    exact harmanDiscardPrime_integrand_eq_one hκ hκ1 hα.1 hα.2
  have e2 : Set.EqOn F (fun α => harmanPrimePhiTwo κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc (3 / 16) ((1 - κ) / 5)) := by
    intro α hα
    rw [Set.uIcc_of_le (by linarith)] at hα
    exact harmanDiscardPrime_integrand_eq_two hκ hκ1 hα.1 hα.2
  have e3 : Set.EqOn F (fun α => harmanPrimePhiThree κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc ((1 - κ) / 5) (1 / 4)) := by
    intro α hα
    rw [Set.uIcc_of_le (by linarith)] at hα
    exact harmanDiscardPrime_integrand_eq_three hκ hκ1 hα.1 hα.2
  have e4 : Set.EqOn F (fun α => harmanPrimePhiFour κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc (1 / 4) ((1 + κ) / 3)) := by
    intro α hα
    rw [Set.uIcc_of_le (by linarith)] at hα
    exact harmanDiscardPrime_integrand_eq_four hκ hκ1 hα.1 hα.2
  have c1 : ContinuousOn (fun α => harmanPrimePhiOne κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc (2 / 11) (3 / 16)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact (continuousOn_harmanPrimePhiOne hκ hκ1 (by norm_num)).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))
  have c2 : ContinuousOn (fun α => harmanPrimePhiTwo κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc (3 / 16) ((1 - κ) / 5)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact (continuousOn_harmanPrimePhiTwo hκ hκ1 (by norm_num) le_rfl).mul
      (continuousOn_logit_weight (by norm_num) (by linarith))
  have c3 : ContinuousOn (fun α => harmanPrimePhiThree κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc ((1 - κ) / 5) (1 / 4)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact (continuousOn_harmanPrimePhiThree hκ1 (by linarith) le_rfl).mul
      (continuousOn_logit_weight (by linarith) (by norm_num))
  have c4 : ContinuousOn (fun α => harmanPrimePhiFour κ α * (1 / α + 1 / (1 - α)))
      (Set.uIcc (1 / 4) ((1 + κ) / 3)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact (continuousOn_harmanPrimePhiFour hκ hκ1 (by norm_num) le_rfl).mul
      (continuousOn_logit_weight (by norm_num) (by linarith))
  have i1 : IntervalIntegrable F MeasureTheory.volume (2 / 11) (3 / 16) :=
    (c1.congr e1).intervalIntegrable
  have i2 : IntervalIntegrable F MeasureTheory.volume (3 / 16) ((1 - κ) / 5) :=
    (c2.congr e2).intervalIntegrable
  have i3 : IntervalIntegrable F MeasureTheory.volume ((1 - κ) / 5) (1 / 4) :=
    (c3.congr e3).intervalIntegrable
  have i4 : IntervalIntegrable F MeasureTheory.volume (1 / 4) ((1 + κ) / 3) :=
    (c4.congr e4).intervalIntegrable
  unfold harmanDiscardPrimeDensity
  rw [← integral_add_adjacent_intervals (i1.trans (i2.trans i3)) i4,
    ← integral_add_adjacent_intervals (i1.trans i2) i3,
    ← integral_add_adjacent_intervals i1 i2,
    integral_congr e1, integral_congr e2, integral_congr e3, integral_congr e4]

/-- The envelope of the prime-cofactor section on cell 0. -/
def harmanDiscardPrimeCellEnvelope0 (x : ℝ) : ℝ :=
  (harmanPrimeOneEnvConst (1 / 1000000) (2 / 11) (3 / 16) (((2 / 11) + (3 / 16)) / 2)
      (logUpperInv 0 (1 / 2 + 1 / 1000000)) (logLowerInv 2 (1 / 4 - 1 / 1000000))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (2 / 11)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (3 / 16)))
      (logUpperInv 0 (3 / 4 + 1 / 1000000 - (((2 / 11) + (3 / 16)) / 2)))
    + harmanPrimeOneEnvSlope (1 / 1000000) (2 / 11) (3 / 16) (((2 / 11) + (3 / 16)) / 2)
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (2 / 11)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (3 / 16))) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope0 :
    ∀ x ∈ Set.Icc (2 / 11 : ℝ) (3 / 16),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope0 x :=
  harmanDiscardPrimeInner_le_one_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 0 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 0 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope0 :
    ∫ x in (2 / 11 : ℝ)..(3 / 16), harmanDiscardPrimeCellEnvelope0 x / x ≤ 4819963 / 100000000 := by
  unfold harmanDiscardPrimeCellEnvelope0
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeOneEnvConst, harmanPrimeOneEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeOneEnvConst, harmanPrimeOneEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeOneEnvConst, harmanPrimeOneEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 1. -/
def harmanDiscardPrimeCellEnvelope1 (x : ℝ) : ℝ :=
  (harmanPrimeTwoEnvConst (1 / 1000000) (3 / 16) ((1 - 1 / 1000000) / 5)
      (((3 / 16) + ((1 - 1 / 1000000) / 5)) / 2) (logUpperInv 0 (1 / 2 + 1 / 1000000))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (3 / 16)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - ((1 - 1 / 1000000) / 5)))
      (logLowerInv 2 (1 - 1 / 1000000 - 4 * (3 / 16)))
      (logLowerInv 2 (1 - 1 / 1000000 - 4 * ((1 - 1 / 1000000) / 5)))
      (logUpperInv 0 (3 * (((3 / 16) + ((1 - 1 / 1000000) / 5)) / 2) + 1 / 1000000))
    + harmanPrimeTwoEnvSlope (1 / 1000000) (3 / 16) ((1 - 1 / 1000000) / 5)
      (((3 / 16) + ((1 - 1 / 1000000) / 5)) / 2) (logLowerInv 1 (1 / 2 - 1 / 1000000 - (3 / 16)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - ((1 - 1 / 1000000) / 5)))
      (logLowerInv 2 (1 - 1 / 1000000 - 4 * (3 / 16)))
      (logLowerInv 2 (1 - 1 / 1000000 - 4 * ((1 - 1 / 1000000) / 5))) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope1 :
    ∀ x ∈ Set.Icc (3 / 16 : ℝ) ((1 - 1 / 1000000) / 5),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope1 x :=
  harmanDiscardPrimeInner_le_two_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 0 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (log_le_logUpperInv 0 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope1 :
    ∫ x in (3 / 16 : ℝ)..((1 - 1 / 1000000) / 5), harmanDiscardPrimeCellEnvelope1 x / x
      ≤ 11567647 / 100000000 := by
  unfold harmanDiscardPrimeCellEnvelope1
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeTwoEnvConst, harmanPrimeTwoEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeTwoEnvConst, harmanPrimeTwoEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeTwoEnvConst, harmanPrimeTwoEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 2. -/
def harmanDiscardPrimeCellEnvelope2 (x : ℝ) : ℝ :=
  (harmanPrimeThreeEnvConst ((1 - 1 / 1000000) / 5) (17 / 80)
      ((((1 - 1 / 1000000) / 5) + (17 / 80)) / 2) (logUpperInv 0 (1 / 2 + 1 / 1000000))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - ((1 - 1 / 1000000) / 5)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (17 / 80))) (logLowerInv 2 ((1 - 1 / 1000000) / 5))
      (logLowerInv 2 (17 / 80))
      (logUpperInv 0 (1 - 2 * ((((1 - 1 / 1000000) / 5) + (17 / 80)) / 2)))
    + harmanPrimeThreeEnvSlope ((1 - 1 / 1000000) / 5) (17 / 80)
      ((((1 - 1 / 1000000) / 5) + (17 / 80)) / 2)
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - ((1 - 1 / 1000000) / 5)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (17 / 80))) (logLowerInv 2 ((1 - 1 / 1000000) / 5))
      (logLowerInv 2 (17 / 80)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope2 :
    ∀ x ∈ Set.Icc ((1 - 1 / 1000000) / 5 : ℝ) (17 / 80),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope2 x :=
  harmanDiscardPrimeInner_le_three_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 0 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (log_le_logUpperInv 0 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope2 :
    ∫ x in ((1 - 1 / 1000000) / 5 : ℝ)..(17 / 80), harmanDiscardPrimeCellEnvelope2 x / x
      ≤ 12070031 / 100000000 := by
  unfold harmanDiscardPrimeCellEnvelope2
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 3. -/
def harmanDiscardPrimeCellEnvelope3 (x : ℝ) : ℝ :=
  (harmanPrimeThreeEnvConst (17 / 80) (9 / 40) (((17 / 80) + (9 / 40)) / 2)
      (logUpperInv 0 (1 / 2 + 1 / 1000000)) (logLowerInv 1 (1 / 2 - 1 / 1000000 - (17 / 80)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (9 / 40))) (logLowerInv 2 (17 / 80))
      (logLowerInv 2 (9 / 40)) (logUpperInv 0 (1 - 2 * (((17 / 80) + (9 / 40)) / 2)))
    + harmanPrimeThreeEnvSlope (17 / 80) (9 / 40) (((17 / 80) + (9 / 40)) / 2)
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (17 / 80)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (9 / 40))) (logLowerInv 2 (17 / 80))
      (logLowerInv 2 (9 / 40)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope3 :
    ∀ x ∈ Set.Icc (17 / 80 : ℝ) (9 / 40),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope3 x :=
  harmanDiscardPrimeInner_le_three_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 0 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (log_le_logUpperInv 0 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope3 :
    ∫ x in (17 / 80 : ℝ)..(9 / 40), harmanDiscardPrimeCellEnvelope3 x / x ≤ 1391259 / 12500000 := by
  unfold harmanDiscardPrimeCellEnvelope3
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 4. -/
def harmanDiscardPrimeCellEnvelope4 (x : ℝ) : ℝ :=
  (harmanPrimeThreeEnvConst (9 / 40) (19 / 80) (((9 / 40) + (19 / 80)) / 2)
      (logUpperInv 0 (1 / 2 + 1 / 1000000)) (logLowerInv 1 (1 / 2 - 1 / 1000000 - (9 / 40)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (19 / 80))) (logLowerInv 2 (9 / 40))
      (logLowerInv 2 (19 / 80)) (logUpperInv 0 (1 - 2 * (((9 / 40) + (19 / 80)) / 2)))
    + harmanPrimeThreeEnvSlope (9 / 40) (19 / 80) (((9 / 40) + (19 / 80)) / 2)
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (9 / 40)))
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (19 / 80))) (logLowerInv 2 (9 / 40))
      (logLowerInv 2 (19 / 80)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope4 :
    ∀ x ∈ Set.Icc (9 / 40 : ℝ) (19 / 80),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope4 x :=
  harmanDiscardPrimeInner_le_three_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 0 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (log_le_logUpperInv 0 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope4 :
    ∫ x in (9 / 40 : ℝ)..(19 / 80), harmanDiscardPrimeCellEnvelope4 x / x ≤ 5153789 / 50000000 := by
  unfold harmanDiscardPrimeCellEnvelope4
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 5. -/
def harmanDiscardPrimeCellEnvelope5 (x : ℝ) : ℝ :=
  (harmanPrimeThreeEnvConst (19 / 80) (1 / 4) (((19 / 80) + (1 / 4)) / 2)
      (logUpperInv 0 (1 / 2 + 1 / 1000000)) (logLowerInv 1 (1 / 2 - 1 / 1000000 - (19 / 80)))
      (logLowerInv 2 (1 / 2 - 1 / 1000000 - (1 / 4))) (logLowerInv 2 (19 / 80))
      (logLowerInv 2 (1 / 4)) (logUpperInv 0 (1 - 2 * (((19 / 80) + (1 / 4)) / 2)))
    + harmanPrimeThreeEnvSlope (19 / 80) (1 / 4) (((19 / 80) + (1 / 4)) / 2)
      (logLowerInv 1 (1 / 2 - 1 / 1000000 - (19 / 80)))
      (logLowerInv 2 (1 / 2 - 1 / 1000000 - (1 / 4))) (logLowerInv 2 (19 / 80))
      (logLowerInv 2 (1 / 4)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope5 :
    ∀ x ∈ Set.Icc (19 / 80 : ℝ) (1 / 4),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope5 x :=
  harmanDiscardPrimeInner_le_three_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 0 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (log_le_logUpperInv 0 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope5 :
    ∫ x in (19 / 80 : ℝ)..(1 / 4), harmanDiscardPrimeCellEnvelope5 x / x ≤ 9582647 / 100000000 := by
  unfold harmanDiscardPrimeCellEnvelope5
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeThreeEnvConst, harmanPrimeThreeEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 6. -/
def harmanDiscardPrimeCellEnvelope6 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (1 / 4) (21 / 80) (((1 / 4) + (21 / 80)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((1 / 4) + (21 / 80)) / 2)))
      (logLowerInv 2 ((1 / 4) - 1 / 1000000)) (logLowerInv 1 ((21 / 80) - 1 / 1000000))
      (logLowerInv 2 (1 / 4)) (logLowerInv 1 (21 / 80))
      (logUpperInv 1 (1 - 2 * (((1 / 4) + (21 / 80)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (1 / 4) (21 / 80) (((1 / 4) + (21 / 80)) / 2)
      (logLowerInv 2 ((1 / 4) - 1 / 1000000)) (logLowerInv 1 ((21 / 80) - 1 / 1000000))
      (logLowerInv 2 (1 / 4)) (logLowerInv 1 (21 / 80)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope6 :
    ∀ x ∈ Set.Icc (1 / 4 : ℝ) (21 / 80),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope6 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 2 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope6 :
    ∫ x in (1 / 4 : ℝ)..(21 / 80), harmanDiscardPrimeCellEnvelope6 x / x ≤ 4223821 / 50000000 := by
  unfold harmanDiscardPrimeCellEnvelope6
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 7. -/
def harmanDiscardPrimeCellEnvelope7 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (21 / 80) (11 / 40) (((21 / 80) + (11 / 40)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((21 / 80) + (11 / 40)) / 2)))
      (logLowerInv 1 ((21 / 80) - 1 / 1000000)) (logLowerInv 1 ((11 / 40) - 1 / 1000000))
      (logLowerInv 1 (21 / 80)) (logLowerInv 1 (11 / 40))
      (logUpperInv 1 (1 - 2 * (((21 / 80) + (11 / 40)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (21 / 80) (11 / 40) (((21 / 80) + (11 / 40)) / 2)
      (logLowerInv 1 ((21 / 80) - 1 / 1000000)) (logLowerInv 1 ((11 / 40) - 1 / 1000000))
      (logLowerInv 1 (21 / 80)) (logLowerInv 1 (11 / 40)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope7 :
    ∀ x ∈ Set.Icc (21 / 80 : ℝ) (11 / 40),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope7 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope7 :
    ∫ x in (21 / 80 : ℝ)..(11 / 40), harmanDiscardPrimeCellEnvelope7 x / x ≤ 432209 / 6250000 := by
  unfold harmanDiscardPrimeCellEnvelope7
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 8. -/
def harmanDiscardPrimeCellEnvelope8 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (11 / 40) (23 / 80) (((11 / 40) + (23 / 80)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((11 / 40) + (23 / 80)) / 2)))
      (logLowerInv 1 ((11 / 40) - 1 / 1000000)) (logLowerInv 1 ((23 / 80) - 1 / 1000000))
      (logLowerInv 1 (11 / 40)) (logLowerInv 1 (23 / 80))
      (logUpperInv 1 (1 - 2 * (((11 / 40) + (23 / 80)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (11 / 40) (23 / 80) (((11 / 40) + (23 / 80)) / 2)
      (logLowerInv 1 ((11 / 40) - 1 / 1000000)) (logLowerInv 1 ((23 / 80) - 1 / 1000000))
      (logLowerInv 1 (11 / 40)) (logLowerInv 1 (23 / 80)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope8 :
    ∀ x ∈ Set.Icc (11 / 40 : ℝ) (23 / 80),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope8 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope8 :
    ∫ x in (11 / 40 : ℝ)..(23 / 80), harmanDiscardPrimeCellEnvelope8 x / x
      ≤ 1094439 / 20000000 := by
  unfold harmanDiscardPrimeCellEnvelope8
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 9. -/
def harmanDiscardPrimeCellEnvelope9 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (23 / 80) (3 / 10) (((23 / 80) + (3 / 10)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((23 / 80) + (3 / 10)) / 2)))
      (logLowerInv 1 ((23 / 80) - 1 / 1000000)) (logLowerInv 1 ((3 / 10) - 1 / 1000000))
      (logLowerInv 1 (23 / 80)) (logLowerInv 1 (3 / 10))
      (logUpperInv 1 (1 - 2 * (((23 / 80) + (3 / 10)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (23 / 80) (3 / 10) (((23 / 80) + (3 / 10)) / 2)
      (logLowerInv 1 ((23 / 80) - 1 / 1000000)) (logLowerInv 1 ((3 / 10) - 1 / 1000000))
      (logLowerInv 1 (23 / 80)) (logLowerInv 1 (3 / 10)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope9 :
    ∀ x ∈ Set.Icc (23 / 80 : ℝ) (3 / 10),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope9 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope9 :
    ∫ x in (23 / 80 : ℝ)..(3 / 10), harmanDiscardPrimeCellEnvelope9 x / x ≤ 2048981 / 50000000 := by
  unfold harmanDiscardPrimeCellEnvelope9
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 10. -/
def harmanDiscardPrimeCellEnvelope10 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (3 / 10) (5 / 16) (((3 / 10) + (5 / 16)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((3 / 10) + (5 / 16)) / 2)))
      (logLowerInv 1 ((3 / 10) - 1 / 1000000)) (logLowerInv 1 ((5 / 16) - 1 / 1000000))
      (logLowerInv 1 (3 / 10)) (logLowerInv 1 (5 / 16))
      (logUpperInv 1 (1 - 2 * (((3 / 10) + (5 / 16)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (3 / 10) (5 / 16) (((3 / 10) + (5 / 16)) / 2)
      (logLowerInv 1 ((3 / 10) - 1 / 1000000)) (logLowerInv 1 ((5 / 16) - 1 / 1000000))
      (logLowerInv 1 (3 / 10)) (logLowerInv 1 (5 / 16)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope10 :
    ∀ x ∈ Set.Icc (3 / 10 : ℝ) (5 / 16),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope10 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope10 :
    ∫ x in (3 / 10 : ℝ)..(5 / 16), harmanDiscardPrimeCellEnvelope10 x / x ≤ 1387311 / 50000000 := by
  unfold harmanDiscardPrimeCellEnvelope10
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 11. -/
def harmanDiscardPrimeCellEnvelope11 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (5 / 16) (13 / 40) (((5 / 16) + (13 / 40)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((5 / 16) + (13 / 40)) / 2)))
      (logLowerInv 1 ((5 / 16) - 1 / 1000000)) (logLowerInv 1 ((13 / 40) - 1 / 1000000))
      (logLowerInv 1 (5 / 16)) (logLowerInv 1 (13 / 40))
      (logUpperInv 1 (1 - 2 * (((5 / 16) + (13 / 40)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (5 / 16) (13 / 40) (((5 / 16) + (13 / 40)) / 2)
      (logLowerInv 1 ((5 / 16) - 1 / 1000000)) (logLowerInv 1 ((13 / 40) - 1 / 1000000))
      (logLowerInv 1 (5 / 16)) (logLowerInv 1 (13 / 40)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope11 :
    ∀ x ∈ Set.Icc (5 / 16 : ℝ) (13 / 40),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope11 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope11 :
    ∫ x in (5 / 16 : ℝ)..(13 / 40), harmanDiscardPrimeCellEnvelope11 x / x ≤ 742799 / 50000000 := by
  unfold harmanDiscardPrimeCellEnvelope11
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]

/-- The envelope of the prime-cofactor section on cell 12. -/
def harmanDiscardPrimeCellEnvelope12 (x : ℝ) : ℝ :=
  (harmanPrimeFourEnvConst (1 / 1000000) (13 / 40) ((1 + 1 / 1000000) / 3)
      (((13 / 40) + ((1 + 1 / 1000000) / 3)) / 2)
      (logUpperInv 1 (1 + 1 / 1000000 - 2 * (((13 / 40) + ((1 + 1 / 1000000) / 3)) / 2)))
      (logLowerInv 1 ((13 / 40) - 1 / 1000000))
      (logLowerInv 1 (((1 + 1 / 1000000) / 3) - 1 / 1000000)) (logLowerInv 1 (13 / 40))
      (logLowerInv 1 ((1 + 1 / 1000000) / 3))
      (logUpperInv 1 (1 - 2 * (((13 / 40) + ((1 + 1 / 1000000) / 3)) / 2)))
    + harmanPrimeFourEnvSlope (1 / 1000000) (13 / 40) ((1 + 1 / 1000000) / 3)
      (((13 / 40) + ((1 + 1 / 1000000) / 3)) / 2) (logLowerInv 1 ((13 / 40) - 1 / 1000000))
      (logLowerInv 1 (((1 + 1 / 1000000) / 3) - 1 / 1000000)) (logLowerInv 1 (13 / 40))
      (logLowerInv 1 ((1 + 1 / 1000000) / 3)) * x) / (1 - x)

theorem harmanDiscardPrimeInner_le_cellEnvelope12 :
    ∀ x ∈ Set.Icc (13 / 40 : ℝ) ((1 + 1 / 1000000) / 3),
      harmanDiscardPrimeInner (1 / 1000000) x ≤ harmanDiscardPrimeCellEnvelope12 x :=
  harmanDiscardPrimeInner_le_four_cell (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (log_le_logUpperInv 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (logLowerInv_le_log 1 (by norm_num))
    (log_le_logUpperInv 1 (by norm_num))

theorem integral_harmanDiscardPrimeCellEnvelope12 :
    ∫ x in (13 / 40 : ℝ)..((1 + 1 / 1000000) / 3), harmanDiscardPrimeCellEnvelope12 x / x
      ≤ 282579 / 100000000 := by
  unfold harmanDiscardPrimeCellEnvelope12
  refine (integral_affine_div_one_sub_div_le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])
    (by norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, chordConst, chordSlope,
      tangentConst, tangentSlope, logLower, logUpper, logLowerInv, logUpperInv, logSeriesLower,
      logSeriesUpper])).trans ?_
  norm_num [harmanPrimeFourEnvConst, harmanPrimeFourEnvSlope, logitCellBound, logitWeightConst,
    logitWeightSlope, chordConst, chordSlope, tangentConst, tangentSlope, logLower, logUpper,
    logLowerInv, logUpperInv, logSeriesLower, logSeriesUpper]


theorem integral_harmanPrimePhi_cell0_le :
    ∫ x in (2 / 11 : ℝ)..(3 / 16), harmanPrimePhiOne (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 4819963 / 100000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiOne (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiOne (1 / 1000000)) (Set.Icc (2 / 11) (3 / 16))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope0
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_one (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope0 x hx) hx0.le

theorem integral_harmanPrimePhi_cell1_le :
    ∫ x in (3 / 16 : ℝ)..((1 - 1 / 1000000) / 5), harmanPrimePhiTwo (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 11567647 / 100000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiTwo (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiTwo (1 / 1000000)) (Set.Icc (3 / 16) ((1 - 1 / 1000000) / 5))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope1
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_two (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope1 x hx) hx0.le

theorem integral_harmanPrimePhi_cell2_le :
    ∫ x in ((1 - 1 / 1000000) / 5 : ℝ)..(17 / 80), harmanPrimePhiThree (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 12070031 / 100000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiThree (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiThree (1 / 1000000)) (Set.Icc ((1 - 1 / 1000000) / 5) (17 / 80))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope2
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_three (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope2 x hx) hx0.le

theorem integral_harmanPrimePhi_cell3_le :
    ∫ x in (17 / 80 : ℝ)..(9 / 40), harmanPrimePhiThree (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 1391259 / 12500000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiThree (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiThree (1 / 1000000)) (Set.Icc (17 / 80) (9 / 40))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope3
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_three (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope3 x hx) hx0.le

theorem integral_harmanPrimePhi_cell4_le :
    ∫ x in (9 / 40 : ℝ)..(19 / 80), harmanPrimePhiThree (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 5153789 / 50000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiThree (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiThree (1 / 1000000)) (Set.Icc (9 / 40) (19 / 80))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope4
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_three (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope4 x hx) hx0.le

theorem integral_harmanPrimePhi_cell5_le :
    ∫ x in (19 / 80 : ℝ)..(1 / 4), harmanPrimePhiThree (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 9582647 / 100000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiThree (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiThree (1 / 1000000)) (Set.Icc (19 / 80) (1 / 4))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope5
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_three (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope5 x hx) hx0.le

theorem integral_harmanPrimePhi_cell6_le :
    ∫ x in (1 / 4 : ℝ)..(21 / 80), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 4223821 / 50000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (1 / 4) (21 / 80))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope6
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope6 x hx) hx0.le

theorem integral_harmanPrimePhi_cell7_le :
    ∫ x in (21 / 80 : ℝ)..(11 / 40), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 432209 / 6250000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (21 / 80) (11 / 40))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope7
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope7 x hx) hx0.le

theorem integral_harmanPrimePhi_cell8_le :
    ∫ x in (11 / 40 : ℝ)..(23 / 80), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 1094439 / 20000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (11 / 40) (23 / 80))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope8
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope8 x hx) hx0.le

theorem integral_harmanPrimePhi_cell9_le :
    ∫ x in (23 / 80 : ℝ)..(3 / 10), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 2048981 / 50000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (23 / 80) (3 / 10))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope9
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope9 x hx) hx0.le

theorem integral_harmanPrimePhi_cell10_le :
    ∫ x in (3 / 10 : ℝ)..(5 / 16), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 1387311 / 50000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (3 / 10) (5 / 16))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope10
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope10 x hx) hx0.le

theorem integral_harmanPrimePhi_cell11_le :
    ∫ x in (5 / 16 : ℝ)..(13 / 40), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 742799 / 50000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (5 / 16) (13 / 40))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope11
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope11 x hx) hx0.le

theorem integral_harmanPrimePhi_cell12_le :
    ∫ x in (13 / 40 : ℝ)..((1 + 1 / 1000000) / 3), harmanPrimePhiFour (1 / 1000000) x * (1 / x + 1 / (1 - x))
      ≤ 282579 / 100000000 := by
  refine le_trans (integral_mono_on (by norm_num)
    ((((continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) (by norm_num)) :
      ContinuousOn (harmanPrimePhiFour (1 / 1000000)) (Set.Icc (13 / 40) ((1 + 1 / 1000000) / 3))).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))).intervalIntegrable_of_Icc
        (by norm_num))
    ((ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => by have := hx.2; norm_num at this ⊢; linarith)) continuousOn_id
      (fun x hx => by have := hx.1; norm_num at this ⊢; linarith)).intervalIntegrable_of_Icc
        (by norm_num)) (fun x hx => ?_)) integral_harmanDiscardPrimeCellEnvelope12
  have hx0 : 0 < x := by have := hx.1; norm_num at this ⊢; linarith
  have hx1 : x < 1 := by have := hx.2; norm_num at this ⊢; linarith
  rw [← harmanDiscardPrime_integrand_eq_four (by norm_num) (by norm_num) (by have := hx.1; norm_num at this ⊢; linarith)
    (by have := hx.2; norm_num at this ⊢; linarith)]
  exact div_le_div_of_nonneg_right (harmanDiscardPrimeInner_le_cellEnvelope12 x hx) hx0.le


/-- The discarded prime-cofactor density is below `0.8896`. -/
theorem harmanDiscardPrimeDensity_le :
    harmanDiscardPrimeDensity (1 / 1000000) ≤ 8896 / 10000 := by
  rw [harmanDiscardPrimeDensity_eq (by norm_num) (by norm_num)]
  have c3 : ContinuousOn (fun α => harmanPrimePhiThree (1 / 1000000) α * (1 / α + 1 / (1 - α)))
      (Set.Icc ((1 - 1 / 1000000) / 5) (1 / 4)) :=
    (continuousOn_harmanPrimePhiThree (by norm_num) (by norm_num) le_rfl).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))
  have c4 : ContinuousOn (fun α => harmanPrimePhiFour (1 / 1000000) α * (1 / α + 1 / (1 - α)))
      (Set.Icc (1 / 4) ((1 + 1 / 1000000) / 3)) :=
    (continuousOn_harmanPrimePhiFour (by norm_num) (by norm_num) (by norm_num) le_rfl).mul
      (continuousOn_logit_weight (by norm_num) (by norm_num))
  have i3 : ∀ x y : ℝ, (1 - 1 / 1000000) / 5 ≤ x → x ≤ y → y ≤ 1 / 4 →
      IntervalIntegrable (fun α => harmanPrimePhiThree (1 / 1000000) α * (1 / α + 1 / (1 - α)))
        MeasureTheory.volume x y := fun x y hx hxy hy =>
    (c3.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  have i4 : ∀ x y : ℝ, 1 / 4 ≤ x → x ≤ y → y ≤ (1 + 1 / 1000000) / 3 →
      IntervalIntegrable (fun α => harmanPrimePhiFour (1 / 1000000) α * (1 / α + 1 / (1 - α)))
        MeasureTheory.volume x y := fun x y hx hxy hy =>
    (c4.mono (Set.Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  rw [← integral_add_adjacent_intervals
      (i3 ((1 - 1 / 1000000) / 5) (17 / 80) (by norm_num) (by norm_num) (by norm_num))
      (i3 (17 / 80) (1 / 4) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i3 (17 / 80) (9 / 40) (by norm_num) (by norm_num) (by norm_num))
      (i3 (9 / 40) (1 / 4) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i3 (9 / 40) (19 / 80) (by norm_num) (by norm_num) (by norm_num))
      (i3 (19 / 80) (1 / 4) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i4 (1 / 4) (21 / 80) (by norm_num) (by norm_num) (by norm_num))
      (i4 (21 / 80) ((1 + 1 / 1000000) / 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i4 (21 / 80) (11 / 40) (by norm_num) (by norm_num) (by norm_num))
      (i4 (11 / 40) ((1 + 1 / 1000000) / 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i4 (11 / 40) (23 / 80) (by norm_num) (by norm_num) (by norm_num))
      (i4 (23 / 80) ((1 + 1 / 1000000) / 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i4 (23 / 80) (3 / 10) (by norm_num) (by norm_num) (by norm_num))
      (i4 (3 / 10) ((1 + 1 / 1000000) / 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i4 (3 / 10) (5 / 16) (by norm_num) (by norm_num) (by norm_num))
      (i4 (5 / 16) ((1 + 1 / 1000000) / 3) (by norm_num) (by norm_num) (by norm_num)),
    ← integral_add_adjacent_intervals
      (i4 (5 / 16) (13 / 40) (by norm_num) (by norm_num) (by norm_num))
      (i4 (13 / 40) ((1 + 1 / 1000000) / 3) (by norm_num) (by norm_num) (by norm_num))]
  linarith [integral_harmanPrimePhi_cell0_le, integral_harmanPrimePhi_cell1_le, integral_harmanPrimePhi_cell2_le,
    integral_harmanPrimePhi_cell3_le, integral_harmanPrimePhi_cell4_le, integral_harmanPrimePhi_cell5_le,
    integral_harmanPrimePhi_cell6_le, integral_harmanPrimePhi_cell7_le, integral_harmanPrimePhi_cell8_le,
    integral_harmanPrimePhi_cell9_le, integral_harmanPrimePhi_cell10_le, integral_harmanPrimePhi_cell11_le,
    integral_harmanPrimePhi_cell12_le]

end

end RHTower.Sieve
