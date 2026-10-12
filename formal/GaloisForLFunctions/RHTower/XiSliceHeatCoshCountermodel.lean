import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage

/-!
# A countermodel: heated positivity at rate `δ` cannot see an off-line pair at offset `δ`

Let `F(z) = ((z − t₀)² + δ²) · √2 sin(L(z − t₀)/2 + π/4)`.  Its real zeros are uniformly spaced at
`2π/L` (the zero density of `Ξ` at height `t` with `L = log t`), and it has one off-line pair `t₀ ± iδ`.
Its slice at `t₀` is

  `g(x) = F(t₀ + ix) F(t₀ − ix) = (δ² − x²)² cosh(Lx)`        (`coshModel`),

which vanishes at `x = ±δ`, so `g` is not absolutely monotone at `0`.

**Theorem** (`hasSum_coshModelHeat`).  For `λ > 0` and `L ≥ 0`, the heated slice
`H(x) = E[g(x + √λ Z)]` (`coshModelHeat`) is

  `H(x) = ½ e^{λL²/2} (e^{Lx} P(x + λL) + e^{−Lx} P(λL − x))`,  `P(c) = (c² − δ²)² + λ(6c² − 2δ²) + 3λ²`,

and if `λL ≥ δ` every Taylor coefficient of `H` at `0` is nonnegative.

So heated positivity at heat `λ = κ/L` is compatible with an off-line pair at every offset `δ ≤ κ`.
With `L = log t`, the everywhere heat rate `κ` of the WD slice can exclude off-line zeros only at
offsets above `κ`.  The Lindelöf tier `κ = ½` excludes none, and so does the proved rate `κ = 1 + δ`.

Proof.  Tilting the Gaussian, `E[e^{±LU} p(x + U)] = e^{λL²/2} E[p(x ± λL + U)]`, and the quartic
Gaussian average is `E[(δ² − (c + U)²)²] = P(c)` (moments `1, 0, λ, 0, 3λ²`).  For `κ = λL ≥ δ`,
`P(x + κ) = q₀ + q₁x + q₂x² + q₃x³ + x⁴` with
`q₀ = D² + λ(6κ² − 2δ²) + 3λ²`, `q₁ = 4κD + 12λκ`, `q₂ = 4κ² + 2D + 6λ`, `q₃ = 4κ`, `D = κ² − δ²`.
All of these are `≥ 0`, and `e^{Lx}` has nonnegative coefficients.
-/

open MeasureTheory Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- The slice of the cosh model. -/
def coshModel (δ L x : ℝ) : ℝ := (δ ^ 2 - x ^ 2) ^ 2 * Real.cosh (L * x)

/-- The heated slice of the cosh model: the Gaussian average with variance `λ`. -/
def coshModelHeat (δ L lam x : ℝ) : ℝ := ∫ u : ℝ, gaussDensity (lam / 2) u * coshModel δ L (x + u)

/-- The heated quartic `P(c) = (c² − δ²)² + λ(6c² − 2δ²) + 3λ²`. -/
def coshModelQuartic (δ lam c : ℝ) : ℝ := (c ^ 2 - δ ^ 2) ^ 2 + lam * (6 * c ^ 2 - 2 * δ ^ 2) + 3 * lam ^ 2

theorem coshModel_offset (δ L : ℝ) : coshModel δ L δ = 0 := by simp [coshModel]

/-- The quartic Gaussian average: `E[(δ² − (c + U)²)²] = P(c)` for `U` of variance `λ`. -/
theorem integrable_and_integral_gaussDensity_quartic {lam : ℝ} (hlam : 0 < lam) (δ c : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * (δ ^ 2 - (c + u) ^ 2) ^ 2) ∧
      ∫ u : ℝ, gaussDensity (lam / 2) u * (δ ^ 2 - (c + u) ^ 2) ^ 2 = coshModelQuartic δ lam c := by
  have ht : 0 < lam / 2 := by positivity
  have hI : ∀ k : ℕ, Integrable (fun u : ℝ => gaussDensity (lam / 2) u * u ^ k) :=
    integrable_gaussDensity_mul_pow ht
  have hm0 : ∫ u : ℝ, gaussDensity (lam / 2) u * u ^ 0 = 1 := by
    have h := integral_gaussDensity_mul_pow_even ht 0
    simpa using h
  have hm1 : ∫ u : ℝ, gaussDensity (lam / 2) u * u ^ 1 = 0 := by
    simpa using integral_gaussDensity_mul_pow_odd (lam / 2) 0
  have hm2 : ∫ u : ℝ, gaussDensity (lam / 2) u * u ^ 2 = lam := by
    have h := integral_gaussDensity_mul_pow_even ht 1
    simp at h; rw [h]; ring
  have hm3 : ∫ u : ℝ, gaussDensity (lam / 2) u * u ^ 3 = 0 := by
    simpa using integral_gaussDensity_mul_pow_odd (lam / 2) 1
  have hm4 : ∫ u : ℝ, gaussDensity (lam / 2) u * u ^ 4 = 3 * lam ^ 2 := by
    have h := integral_gaussDensity_mul_pow_even ht 2
    simp [Nat.factorial] at h; rw [h]; ring
  set a : ℕ → ℝ := fun k => if k = 0 then (δ ^ 2 - c ^ 2) ^ 2 else if k = 1 then
    -(4 * c * (δ ^ 2 - c ^ 2)) else if k = 2 then 4 * c ^ 2 - 2 * (δ ^ 2 - c ^ 2) else if k = 3 then
    4 * c else 1 with hadef
  have hfun : (fun u : ℝ => gaussDensity (lam / 2) u * (δ ^ 2 - (c + u) ^ 2) ^ 2)
      = fun u => ∑ k ∈ Finset.range 5, a k * (gaussDensity (lam / 2) u * u ^ k) := by
    funext u
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hadef]
    norm_num
    ring
  have hint : Integrable fun u : ℝ => ∑ k ∈ Finset.range 5, a k * (gaussDensity (lam / 2) u * u ^ k) :=
    integrable_finsetSum _ fun k _ => (hI k).const_mul _
  refine ⟨hfun ▸ hint, ?_⟩
  rw [hfun, integral_finsetSum _ fun k _ => (hI k).const_mul _]
  simp only [integral_const_mul, Finset.sum_range_succ, Finset.sum_range_zero, hm0, hm1, hm2, hm3,
    hm4, hadef]
  unfold coshModelQuartic
  norm_num
  ring

/-- **Gaussian tilt.**  `E[e^{LU} (δ² − (x + U)²)²] = e^{λL²/2} P(x + λL)`. -/
theorem integrable_and_integral_gaussDensity_tilt_quartic {lam : ℝ} (hlam : 0 < lam) (δ L x : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * (Real.exp (L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2))
      ∧ ∫ u : ℝ, gaussDensity (lam / 2) u * (Real.exp (L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2)
        = Real.exp (lam * L ^ 2 / 2) * coshModelQuartic δ lam (x + lam * L) := by
  have ht : 0 < lam / 2 := by positivity
  obtain ⟨hint, hval⟩ := integrable_and_integral_gaussDensity_quartic hlam δ (x + lam * L)
  have hpt : ∀ u : ℝ, gaussDensity (lam / 2) u * (Real.exp (L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2)
      = Real.exp (lam * L ^ 2 / 2) * (gaussDensity (lam / 2) (u - lam * L)
        * (δ ^ 2 - (x + lam * L + (u - lam * L)) ^ 2) ^ 2) := by
    intro u
    have e : gaussDensity (lam / 2) u * Real.exp (L * u)
        = Real.exp (lam * L ^ 2 / 2) * gaussDensity (lam / 2) (u - lam * L) := by
      unfold gaussDensity
      have hexp : -(u ^ 2 / (4 * (lam / 2))) + L * u
          = lam * L ^ 2 / 2 + -((u - lam * L) ^ 2 / (4 * (lam / 2))) := by
        field_simp; ring
      calc (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (4 * (lam / 2))))
            * Real.exp (L * u)
          = (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ))
            * Real.exp (-(u ^ 2 / (4 * (lam / 2))) + L * u) := by rw [mul_assoc, ← Real.exp_add]
        _ = (4 * Real.pi * (lam / 2)) ^ (-(1 / 2 : ℝ))
            * Real.exp (lam * L ^ 2 / 2 + -((u - lam * L) ^ 2 / (4 * (lam / 2)))) := by rw [hexp]
        _ = _ := by rw [Real.exp_add]; ring
    rw [show x + lam * L + (u - lam * L) = x + u by ring, ← mul_assoc, e]
    ring
  have hfun : (fun u : ℝ => gaussDensity (lam / 2) u * (Real.exp (L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2))
      = fun u => Real.exp (lam * L ^ 2 / 2) * ((fun v => gaussDensity (lam / 2) v
        * (δ ^ 2 - (x + lam * L + v) ^ 2) ^ 2) (u - lam * L)) := funext hpt
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint.comp_sub_right _).const_mul _
  · rw [hfun, integral_const_mul, integral_sub_right_eq_self
      (fun v => gaussDensity (lam / 2) v * (δ ^ 2 - (x + lam * L + v) ^ 2) ^ 2), hval]

theorem coshModelQuartic_neg (δ lam c : ℝ) : coshModelQuartic δ lam (-c) = coshModelQuartic δ lam c := by
  unfold coshModelQuartic; ring

/-- **Closed form of the heated cosh model.** -/
theorem coshModelHeat_eq {lam : ℝ} (hlam : 0 < lam) (δ L x : ℝ) :
    coshModelHeat δ L lam x = Real.exp (lam * L ^ 2 / 2) / 2 *
      (Real.exp (L * x) * coshModelQuartic δ lam (x + lam * L)
        + Real.exp (-(L * x)) * coshModelQuartic δ lam (lam * L - x)) := by
  obtain ⟨h1, v1⟩ := integrable_and_integral_gaussDensity_tilt_quartic hlam δ L x
  obtain ⟨h2, v2⟩ := integrable_and_integral_gaussDensity_tilt_quartic hlam δ (-L) x
  have hpt : ∀ u : ℝ, gaussDensity (lam / 2) u * coshModel δ L (x + u)
      = Real.exp (L * x) / 2 * (gaussDensity (lam / 2) u * (Real.exp (L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2))
        + Real.exp (-(L * x)) / 2 * (gaussDensity (lam / 2) u
          * (Real.exp (-L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2)) := by
    intro u
    unfold coshModel
    rw [Real.cosh_eq, show L * (x + u) = L * x + L * u by ring, Real.exp_add,
      show -(L * x + L * u) = -(L * x) + -L * u by ring, Real.exp_add]
    ring
  unfold coshModelHeat
  rw [show (fun u : ℝ => gaussDensity (lam / 2) u * coshModel δ L (x + u))
      = fun u => Real.exp (L * x) / 2 * (gaussDensity (lam / 2) u
        * (Real.exp (L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2))
        + Real.exp (-(L * x)) / 2 * (gaussDensity (lam / 2) u
          * (Real.exp (-L * u) * (δ ^ 2 - (x + u) ^ 2) ^ 2)) from funext hpt,
    integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul, v1, v2]
  rw [show (-L) ^ 2 = L ^ 2 by ring, show x + lam * -L = -(lam * L - x) by ring, coshModelQuartic_neg]
  ring

/-- The coefficients of `P(x + κ) = Σ_{j ≤ 4} q_j x^j`. -/
def coshModelShiftCoeff (δ lam κ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then (κ ^ 2 - δ ^ 2) ^ 2 + lam * (6 * κ ^ 2 - 2 * δ ^ 2) + 3 * lam ^ 2
  else if j = 1 then 4 * κ * (κ ^ 2 - δ ^ 2) + 12 * lam * κ
  else if j = 2 then 4 * κ ^ 2 + 2 * (κ ^ 2 - δ ^ 2) + 6 * lam
  else if j = 3 then 4 * κ else if j = 4 then 1 else 0

theorem coshModelQuartic_add_eq_sum (δ lam κ x : ℝ) :
    coshModelQuartic δ lam (x + κ) = ∑ j ∈ Finset.range 5, coshModelShiftCoeff δ lam κ j * x ^ j := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coshModelShiftCoeff, coshModelQuartic]
  norm_num
  ring

theorem coshModelShiftCoeff_nonneg {δ lam κ : ℝ} (hδ : 0 ≤ δ) (hlam : 0 ≤ lam) (hκ : δ ≤ κ)
    (j : ℕ) : 0 ≤ coshModelShiftCoeff δ lam κ j := by
  have hD : 0 ≤ κ ^ 2 - δ ^ 2 := by nlinarith
  have hκ0 : 0 ≤ κ := le_trans hδ hκ
  unfold coshModelShiftCoeff
  split_ifs
  · have : 0 ≤ 6 * κ ^ 2 - 2 * δ ^ 2 := by nlinarith
    positivity
  · have := mul_nonneg hκ0 hD; positivity
  · positivity
  · positivity
  · norm_num
  · exact le_rfl

/-- The coefficients of `e^{Lx} P(x + κ)`. -/
def coshModelSeriesCoeff (δ L lam κ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 5,
    if j ≤ n then coshModelShiftCoeff δ lam κ j * (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0

theorem hasSum_exp_mul_coshModelQuartic (δ L lam κ x : ℝ) :
    HasSum (fun n : ℕ => coshModelSeriesCoeff δ L lam κ n * x ^ n)
      (Real.exp (L * x) * coshModelQuartic δ lam (x + κ)) := by
  have hj : ∀ j : ℕ, HasSum (fun n : ℕ => (if j ≤ n then (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0)
      * x ^ n) (x ^ j * Real.exp (L * x)) := by
    intro j
    have hexp : HasSum (fun m : ℕ => (L * x) ^ m / (m.factorial : ℝ)) (Real.exp (L * x)) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp (L * x)
    have h := hexp.mul_left (x ^ j)
    have hinj : Function.Injective (fun m : ℕ => m + j) := fun a b h => by simpa using h
    have hzero : ∀ n ∉ Set.range (fun m : ℕ => m + j),
        (if j ≤ n then (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0) * x ^ n = 0 := by
      intro n hn
      have : ¬ j ≤ n := fun hjn => hn ⟨n - j, by simp only; omega⟩
      rw [if_neg this, zero_mul]
    rw [← hinj.hasSum_iff hzero]
    refine h.congr_fun fun m => ?_
    simp only [Function.comp_def, show j ≤ m + j from Nat.le_add_left j m, if_true,
      Nat.add_sub_cancel, mul_pow, pow_add]
    ring
  have hall : HasSum (fun n : ℕ => ∑ j ∈ Finset.range 5, coshModelShiftCoeff δ lam κ j *
      ((if j ≤ n then (L ^ (n - j) / ((n - j).factorial : ℝ)) else 0) * x ^ n))
      (∑ j ∈ Finset.range 5, coshModelShiftCoeff δ lam κ j * (x ^ j * Real.exp (L * x))) :=
    hasSum_sum fun j _ => (hj j).mul_left (coshModelShiftCoeff δ lam κ j)
  have hval : Real.exp (L * x) * ∑ j ∈ Finset.range 5, coshModelShiftCoeff δ lam κ j * x ^ j
      = ∑ j ∈ Finset.range 5, coshModelShiftCoeff δ lam κ j * (x ^ j * Real.exp (L * x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [coshModelQuartic_add_eq_sum, hval]
  refine hall.congr_fun fun n => ?_
  simp only [coshModelSeriesCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **The countermodel.**  For `λ > 0`, `L ≥ 0`, `δ ≥ 0` and `λL ≥ δ`, the heated cosh model has a
power series at `0` with nonnegative coefficients, although `coshModel δ L δ = 0`. -/
theorem hasSum_coshModelHeat {δ L lam : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hκ : δ ≤ lam * L) :
    ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ ∀ x : ℝ, HasSum (fun n : ℕ => a n * x ^ n) (coshModelHeat δ L lam x) := by
  set κ := lam * L with hκdef
  set c := coshModelSeriesCoeff δ L lam κ with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (coshModelShiftCoeff_nonneg hδ hlam.le hκ j) (by positivity)
    · exact le_rfl
  refine ⟨fun n => Real.exp (lam * L ^ 2 / 2) / 2 * (c n + (-1) ^ n * c n), fun n => ?_, fun x => ?_⟩
  · have h1 : 0 ≤ c n + (-1) ^ n * c n := by
      rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> linarith [hc0 n]
    positivity
  · have h1 := hasSum_exp_mul_coshModelQuartic δ L lam κ x
    have h2 := hasSum_exp_mul_coshModelQuartic δ L lam κ (-x)
    rw [coshModelHeat_eq hlam]
    have e : Real.exp (L * -x) * coshModelQuartic δ lam (-x + κ)
        = Real.exp (-(L * x)) * coshModelQuartic δ lam (lam * L - x) := by
      rw [show L * -x = -(L * x) by ring, show -x + κ = lam * L - x by rw [hκdef]; ring]
    rw [e] at h2
    refine ((h1.add h2).mul_left (Real.exp (lam * L ^ 2 / 2) / 2)).congr_fun fun n => ?_
    rw [neg_pow]
    ring

end

end RHTower.DeBruijn
