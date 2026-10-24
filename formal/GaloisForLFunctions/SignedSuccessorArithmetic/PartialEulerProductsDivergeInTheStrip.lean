import GaloisForLFunctions.PNTPlus.Consequences
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Partial Euler products diverge in the strip

For `0 ≤ σ < 1` the squared partial Euler product
`∏_{p ∈ S} |1 − p^{−σ} p^{iτ}|²` over a finite set of primes is unbounded in `S`, uniformly on
whole height intervals. The mechanism is the pole of `ζ` at `1`, not its zeros:

* on a prime window `x < p ≤ λx` the phases `τ log p` differ from `τ log x` by at most `τ log λ`,
  so at the heights `τ₁ = (2πj + π)/log x` and within `1/(10 log λx)` of them every factor has
  `cos(τ log p) ≤ −1/2` and is at least `1 + p^{−σ}` (`cos_le_of_aligned`);
* the prime number theorem (`chebyshev_asymptotic`, `θ ~ id`) puts `≍ x/log x` primes in the
  window (`eventually_theta_window_ge`), so the product is at least
  `≍ x^{1−σ}/log x` there, which beats the width `≍ 1/log x` of the aligned interval
  (`exists_aligned_window`).

Hence for every integrable weight `w ≥ 0` that is continuous and positive at one nonzero height,
the spectral hypercube form `∫ w(τ) ∏_{p ∈ S} |1 − p^{−σ+iτ}|² dτ` is unbounded over finite sets of
primes (`spectralHypercube_unbounded`). This is the Mellin form of the hypercube Dirichlet form
`Σ_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{−σ} K(d₁/d₂)` with `σ = 1/2 + ε`: below the abscissa of
absolute convergence its unboundedness is forced by the coherent distribution of the primes alone.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Real Finset Filter Asymptotics MeasureTheory
open scoped Chebyshev

/-- `|1 − p^{−σ} e^{iτ log p}|² = 1 − 2 p^{−σ} cos(τ log p) + p^{−2σ}`. -/
noncomputable def eulerFactorSq (σ τ : ℝ) (p : ℕ) : ℝ :=
  1 - 2 * (p : ℝ) ^ (-σ) * cos (τ * log p) + ((p : ℝ) ^ (-σ)) ^ 2

theorem eulerFactorSq_nonneg (σ τ : ℝ) (p : ℕ) : 0 ≤ eulerFactorSq σ τ p := by
  unfold eulerFactorSq
  nlinarith [sq_nonneg (1 - (p : ℝ) ^ (-σ) * cos (τ * log p)),
    sq_nonneg ((p : ℝ) ^ (-σ) * sin (τ * log p)), sin_sq_add_cos_sq (τ * log p)]

theorem eulerFactorSq_neg (σ τ : ℝ) (p : ℕ) : eulerFactorSq σ (-τ) p = eulerFactorSq σ τ p := by
  simp [eulerFactorSq, neg_mul, cos_neg]

theorem one_add_le_eulerFactorSq {σ τ : ℝ} {p : ℕ} (hcos : cos (τ * log p) ≤ -1 / 2) :
    1 + (p : ℝ) ^ (-σ) ≤ eulerFactorSq σ τ p := by
  unfold eulerFactorSq
  have ha : 0 ≤ (p : ℝ) ^ (-σ) := rpow_nonneg (Nat.cast_nonneg p) _
  nlinarith [sq_nonneg ((p : ℝ) ^ (-σ))]

theorem eulerFactorSq_le_four {σ : ℝ} (hσ : 0 ≤ σ) (τ : ℝ) {p : ℕ} (hp : 1 ≤ p) :
    eulerFactorSq σ τ p ≤ 4 := by
  unfold eulerFactorSq
  have ha : 0 ≤ (p : ℝ) ^ (-σ) := rpow_nonneg (Nat.cast_nonneg p) _
  have ha1 : (p : ℝ) ^ (-σ) ≤ 1 :=
    rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by linarith)
  nlinarith [neg_one_le_cos (τ * log p), cos_le_one (τ * log p)]

theorem continuous_eulerFactorSq (σ : ℝ) (p : ℕ) : Continuous fun τ => eulerFactorSq σ τ p := by
  unfold eulerFactorSq; fun_prop

/-- The squared partial Euler product over a finite set of primes. -/
noncomputable def eulerProductSq (σ τ : ℝ) (S : Finset ℕ) : ℝ := ∏ p ∈ S, eulerFactorSq σ τ p

theorem eulerProductSq_nonneg (σ τ : ℝ) (S : Finset ℕ) : 0 ≤ eulerProductSq σ τ S :=
  prod_nonneg fun p _ => eulerFactorSq_nonneg σ τ p

theorem continuous_eulerProductSq (σ : ℝ) (S : Finset ℕ) :
    Continuous fun τ => eulerProductSq σ τ S :=
  continuous_finsetProd S fun p _ => continuous_eulerFactorSq σ p

theorem one_add_sum_le_prod_one_add (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ S, 0 ≤ a p) :
    1 + ∑ p ∈ S, a p ≤ ∏ p ∈ S, (1 + a p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert q S hq ih =>
    rw [sum_insert hq, prod_insert hq]
    have hS := ih fun p hp => ha p (mem_insert_of_mem hp)
    have hq0 := ha q (mem_insert_self q S)
    have hsum : 0 ≤ ∑ p ∈ S, a p := sum_nonneg fun p hp => ha p (mem_insert_of_mem hp)
    nlinarith

/-- On aligned heights the product is at least one plus the prime mass. -/
theorem one_add_sum_le_eulerProductSq {σ τ : ℝ} {S : Finset ℕ}
    (h : ∀ p ∈ S, cos (τ * log p) ≤ -1 / 2) :
    1 + ∑ p ∈ S, (p : ℝ) ^ (-σ) ≤ eulerProductSq σ τ S :=
  (one_add_sum_le_prod_one_add S _ fun p _ => rpow_nonneg (Nat.cast_nonneg p) _).trans
    (prod_le_prod (fun p _ => by positivity) fun p hp => one_add_le_eulerFactorSq (h p hp))

/-! ## Prime windows -/

/-- The primes in `(x, λx]`. -/
noncomputable def primeWindow (x lam : ℝ) : Finset ℕ := (Ioc ⌊x⌋₊ ⌊lam * x⌋₊).filter Nat.Prime

theorem mem_primeWindow {x lam : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p ∈ primeWindow x lam) :
    x < p ∧ (p : ℝ) ≤ lam * x ∧ p.Prime := by
  simp only [primeWindow, mem_filter, mem_Ioc] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨(Nat.floor_lt hx).mp h1, ?_, h3⟩
  have hlx : 0 ≤ lam * x := by
    by_contra hneg
    push Not at hneg
    rw [Nat.floor_of_nonpos hneg.le] at h2
    exact absurd h2 (by have := h3.pos; omega)
  exact (Nat.le_floor_iff hlx).mp h2

/-- `θ(λx) − θ(x)` is the logarithmic mass of the window. -/
theorem theta_sub_theta_eq_sum {x lam : ℝ} (hxl : x ≤ lam * x) :
    θ (lam * x) - θ x = ∑ p ∈ primeWindow x lam, log p := by
  rw [Chebyshev.theta, Chebyshev.theta, primeWindow, sum_filter, sum_filter, sum_filter,
    ← sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) (Nat.floor_le_floor hxl)]
  ring

/-- The window mass of `p^{−σ}` is at least `(λx)^{−σ} (θ(λx) − θ(x)) / log(λx)`. -/
theorem sum_rpow_primeWindow_ge {σ x lam : ℝ} (hσ : 0 ≤ σ) (hx : 1 < x) (hlam : 1 < lam) :
    (lam * x) ^ (-σ) * (θ (lam * x) - θ x) / log (lam * x) ≤
      ∑ p ∈ primeWindow x lam, (p : ℝ) ^ (-σ) := by
  have hlx : 1 < lam * x := by nlinarith
  have hlog : 0 < log (lam * x) := log_pos hlx
  rw [theta_sub_theta_eq_sum (by nlinarith), mul_sum, sum_div]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨hxp, hpl, hpp⟩ := mem_primeWindow (by linarith) hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (lam * x) ^ (-σ) ≤ (p : ℝ) ^ (-σ) := by
    rw [rpow_neg (by linarith), rpow_neg hp0.le]
    exact inv_anti₀ (rpow_pos_of_pos hp0 σ) (rpow_le_rpow hp0.le hpl hσ)
  have h2 : log p ≤ log (lam * x) := log_le_log hp0 hpl
  have h3 : 0 ≤ log p := log_nonneg (by exact_mod_cast hpp.one_lt.le)
  rw [div_le_iff₀ hlog]
  have : 0 ≤ (p : ℝ) ^ (-σ) := rpow_nonneg hp0.le _
  have : 0 ≤ (lam * x) ^ (-σ) := rpow_nonneg (by linarith) _
  nlinarith

/-- **The prime number theorem in windows.** For `λ > 1`, eventually
`θ(λx) − θ(x) ≥ (λ − 1) x / 2`. -/
theorem eventually_theta_window_ge {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ x in atTop, (lam - 1) / 2 * x ≤ θ (lam * x) - θ x := by
  have hasy := chebyshev_asymptotic
  set ε := (lam - 1) / (4 * (lam + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos <;> linarith
  have h1 := hasy.isLittleO.def hε0
  have hmul : Tendsto (fun x : ℝ => lam * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h2 := hmul.eventually h1
  filter_upwards [h1, h2, eventually_gt_atTop (0 : ℝ)] with x hx hlx hx0
  simp only [Pi.sub_apply, id, norm_eq_abs] at hx hlx
  rw [abs_of_pos hx0] at hx
  rw [abs_of_pos (show (0 : ℝ) < lam * x by nlinarith)] at hlx
  have a1 := (abs_le.mp hx).2
  have a2 := (abs_le.mp hlx).1
  have : ε * (lam + 1) = (lam - 1) / 4 := by
    rw [hε]; field_simp
  nlinarith

/-! ## Alignment -/

/-- On a prime window the phases at an aligned height stay within `1/5` of `π` modulo `2π`. -/
theorem cos_le_of_aligned {x lam τ₁ τ : ℝ} {j : ℤ} (hx : 1 < x) (hlam : 1 < lam)
    (hτ₁ : τ₁ * log x = 2 * π * j + π) (hτ₁0 : 0 ≤ τ₁) (hτ₁lam : τ₁ * log lam ≤ 1 / 10)
    (hτ : |τ - τ₁| * log (lam * x) ≤ 1 / 10) {p : ℕ} (hxp : x < p) (hpl : (p : ℝ) ≤ lam * x) :
    cos (τ * log p) ≤ -1 / 2 := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hlogp : log x < log p := log_lt_log (by linarith) hxp
  have hlogp' : log p ≤ log (lam * x) := log_le_log hp0 hpl
  have hlx : log (lam * x) = log lam + log x := log_mul (by linarith) (by linarith)
  have hlogp0 : 0 < log p := lt_of_le_of_lt (log_nonneg hx.le) hlogp
  set δ := τ * log p - (2 * π * j + π) with hδ
  have hdecomp : δ = τ₁ * (log p - log x) + (τ - τ₁) * log p := by
    rw [hδ, ← hτ₁]; ring
  have hA : |τ₁ * (log p - log x)| ≤ 1 / 10 := by
    rw [abs_of_nonneg (mul_nonneg hτ₁0 (by linarith))]
    have : log p - log x ≤ log lam := by linarith
    nlinarith
  have hB : |(τ - τ₁) * log p| ≤ 1 / 10 := by
    rw [abs_mul, abs_of_pos hlogp0]
    nlinarith [abs_nonneg (τ - τ₁)]
  have hδb : |δ| ≤ 1 / 5 := by
    rw [hdecomp]; linarith [abs_add_le (τ₁ * (log p - log x)) ((τ - τ₁) * log p)]
  have hcos : cos (τ * log p) = -cos δ := by
    have : τ * log p = δ + π + j * (2 * π) := by rw [hδ]; ring
    rw [this, cos_add_int_mul_two_pi, cos_add_pi]
  have hcosδ : 1 - δ ^ 2 / 2 ≤ cos δ := one_sub_sq_div_two_le_cos
  have hδ2 : δ ^ 2 ≤ 1 / 25 := by
    have := abs_le.mp hδb
    nlinarith
  linarith

/-- An aligned height `τ₁ = (2πj + π)/log x` in `(τ₀ − 2π/log x, τ₀]`. -/
theorem exists_aligned_height {x : ℝ} (hx : 1 < x) (τ₀ : ℝ) :
    ∃ (j : ℤ) (τ₁ : ℝ), τ₁ * log x = 2 * π * j + π ∧ τ₁ ≤ τ₀ ∧ τ₀ - 2 * π / log x < τ₁ := by
  have hlogx : 0 < log x := log_pos hx
  set j : ℤ := ⌊(τ₀ * log x - π) / (2 * π)⌋
  have hj1 : (j : ℝ) ≤ (τ₀ * log x - π) / (2 * π) := Int.floor_le _
  have hj2 : (τ₀ * log x - π) / (2 * π) < j + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ (by positivity)] at hj1
  rw [div_lt_iff₀ (by positivity)] at hj2
  refine ⟨j, (2 * π * j + π) / log x, by field_simp, ?_, ?_⟩
  · rw [div_le_iff₀ hlogx]; linarith only [hj1]
  · rw [lt_div_iff₀ hlogx]
    have e : (τ₀ - 2 * π / log x) * log x = τ₀ * log x - 2 * π := by field_simp
    rw [e]
    linarith only [hj2]

/-- On an aligned window the squared Euler product is at least `c x^{1−σ} / log(λx)` with
`c = (λ − 1) λ^{−σ} / 2`. -/
theorem eulerProductSq_window_ge {σ x lam τ₁ τ : ℝ} {j : ℤ} (hσ : 0 ≤ σ) (hx : 1 < x)
    (hlam : 1 < lam) (htheta : (lam - 1) / 2 * x ≤ θ (lam * x) - θ x)
    (hτ₁ : τ₁ * log x = 2 * π * j + π) (hτ₁0 : 0 ≤ τ₁) (hτ₁lam : τ₁ * log lam ≤ 1 / 10)
    (hτ : |τ - τ₁| * log (lam * x) ≤ 1 / 10) :
    (lam - 1) / 2 * lam ^ (-σ) * x ^ (1 - σ) / log (lam * x) ≤
      eulerProductSq σ τ (primeWindow x lam) := by
  have hcos : ∀ p ∈ primeWindow x lam, cos (τ * log p) ≤ -1 / 2 := fun p hp => by
    obtain ⟨hxp, hpl, _⟩ := mem_primeWindow (by linarith) hp
    exact cos_le_of_aligned hx hlam hτ₁ hτ₁0 hτ₁lam hτ hxp hpl
  have hprod := one_add_sum_le_eulerProductSq (σ := σ) hcos
  have hwin := sum_rpow_primeWindow_ge hσ hx hlam (σ := σ)
  have hloglamx : 0 < log (lam * x) := log_pos (by nlinarith)
  have hpow : (lam * x) ^ (-σ) * ((lam - 1) / 2 * x) = (lam - 1) / 2 * lam ^ (-σ) * x ^ (1 - σ) := by
    rw [mul_rpow (by linarith) (by linarith), show (1 - σ) = 1 + (-σ) by ring,
      rpow_add (by linarith), rpow_one]
    ring
  have hstep : (lam * x) ^ (-σ) * ((lam - 1) / 2 * x) / log (lam * x) ≤
      (lam * x) ^ (-σ) * (θ (lam * x) - θ x) / log (lam * x) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htheta (rpow_nonneg (by nlinarith) _)) hloglamx.le
  rw [hpow] at hstep
  have hs : 0 ≤ ∑ p ∈ primeWindow x lam, (p : ℝ) ^ (-σ) :=
    sum_nonneg fun p _ => rpow_nonneg (Nat.cast_nonneg p) _
  linarith only [hstep, hwin, hprod, hs]

/-- The arithmetic of the final comparison: `M ≤ ρ · c X / L` once `80(|M|+1) ℓ² ≤ c X`,
`0 < L ≤ 2ℓ`, `ρ = 1/(10 L)`. -/
theorem le_rho_mul_of_growth {M c X L ℓ : ℝ} (hL : 0 < L) (hLℓ : L ≤ 2 * ℓ)
    (hgrowth : 80 * (|M| + 1) * ℓ ^ 2 ≤ c * X) :
    M ≤ 1 / (10 * L) * (c * X / L) := by
  rw [div_mul_div_comm, one_mul, le_div_iff₀ (by positivity)]
  have hL2 : 10 * L * L ≤ 40 * ℓ ^ 2 := by
    have : L * L ≤ (2 * ℓ) * (2 * ℓ) := mul_le_mul hLℓ hLℓ hL.le (by linarith)
    nlinarith only [this]
  have hML : M * (10 * L * L) ≤ |M| * (10 * L * L) :=
    mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
  have h2 : |M| * (10 * L * L) ≤ |M| * (40 * ℓ ^ 2) := mul_le_mul_of_nonneg_left hL2 (abs_nonneg M)
  have h3 : |M| * (40 * ℓ ^ 2) ≤ 80 * (|M| + 1) * ℓ ^ 2 := by
    nlinarith only [sq_nonneg ℓ, abs_nonneg M]
  linarith only [hML, h2, h3, hgrowth]

/-- The large-`x` conditions used to build an aligned window. -/
theorem eventually_window_conditions {σ : ℝ} (hσ1 : σ < 1) {η lam c M : ℝ} (hη : 0 < η)
    (hlam : 1 < lam) (hc : 0 < c) :
    ∀ᶠ x in atTop, 1 < x ∧ lam ≤ x ∧ (lam - 1) / 2 * x ≤ θ (lam * x) - θ x ∧
      2 * π / log x ≤ η / 2 ∧ 1 / (10 * log (lam * x)) ≤ η / 2 ∧
      80 * (|M| + 1) * log x ^ 2 ≤ c * x ^ (1 - σ) := by
  have hlog := tendsto_log_atTop
  have hA : ∀ᶠ x in atTop, 2 * π / log x ≤ η / 2 := by
    filter_upwards [hlog.eventually_ge_atTop (4 * π / η), hlog.eventually_gt_atTop 0] with x hx hx0
    rw [div_le_iff₀ hx0]
    rw [div_le_iff₀ hη] at hx
    nlinarith only [hx, hη, pi_pos]
  have hB : ∀ᶠ x in atTop, 1 / (10 * log (lam * x)) ≤ η / 2 := by
    have hmul : Tendsto (fun x : ℝ => log (lam * x)) atTop atTop :=
      hlog.comp (tendsto_id.const_mul_atTop (by linarith))
    filter_upwards [hmul.eventually_ge_atTop (1 / (5 * η)), hmul.eventually_gt_atTop 0]
      with x hx hx0
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hx
    nlinarith only [hx, hη, hx0]
  have hC : ∀ᶠ x in atTop, 80 * (|M| + 1) * log x ^ 2 ≤ c * x ^ (1 - σ) := by
    have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by linarith : (0 : ℝ) < 1 - σ)).def
      (show (0 : ℝ) < c / (80 * (|M| + 1)) by positivity)
    filter_upwards [hlo, eventually_gt_atTop 1] with x hx hx1
    have hlogx : 0 < log x := log_pos hx1
    rw [norm_of_nonneg (rpow_nonneg hlogx.le _), rpow_two,
      norm_of_nonneg (rpow_nonneg (by linarith) _)] at hx
    have := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 80 * (|M| + 1))
    rwa [← mul_assoc, mul_div_cancel₀ _ (by positivity)] at this
  filter_upwards [eventually_gt_atTop 1, eventually_ge_atTop lam, eventually_theta_window_ge hlam,
    hA, hB, hC] with x h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **Aligned windows.** For `0 ≤ σ < 1`, every height interval `[τ₀ − η, τ₀ + η]` with
`0 < η < τ₀` contains an interval of half-width `ρ` on which `ρ · ∏_{p ∈ S} |1 − p^{−σ+iτ}|² ≥ M`,
for a suitable window `S` of primes. -/
theorem exists_aligned_window {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {τ₀ η : ℝ} (hη : 0 < η)
    (hητ : η < τ₀) (M : ℝ) :
    ∃ (S : Finset ℕ) (τ₁ ρ : ℝ), (∀ p ∈ S, p.Prime) ∧ 0 < ρ ∧ τ₀ - η ≤ τ₁ - ρ ∧
      τ₁ + ρ ≤ τ₀ + η ∧ ∀ τ ∈ Set.Icc (τ₁ - ρ) (τ₁ + ρ), M ≤ ρ * eulerProductSq σ τ S := by
  have hK0 : 0 < τ₀ + η := by linarith
  set lam := exp (1 / (10 * (τ₀ + η))) with hlamdef
  have hlam : 1 < lam := one_lt_exp_iff.mpr (by positivity)
  have hloglam : log lam = 1 / (10 * (τ₀ + η)) := log_exp _
  set c := (lam - 1) / 2 * lam ^ (-σ)
  have hc0 : 0 < c := by
    have := rpow_pos_of_pos (by linarith : (0 : ℝ) < lam) (-σ)
    have : 0 < (lam - 1) / 2 := by linarith
    positivity
  obtain ⟨x, hx1, hxlam, htheta, hspace, hrho, hgrowth⟩ :=
    (eventually_window_conditions hσ1 (M := M) hη hlam hc0).exists
  obtain ⟨j, τ₁, hτ₁x, hτ₁le, hτ₁ge⟩ := exists_aligned_height hx1 τ₀
  have hloglamx : 0 < log (lam * x) := log_pos (by nlinarith)
  set ρ := 1 / (10 * log (lam * x)) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hτ₁0 : 0 ≤ τ₁ := by linarith only [hτ₁ge, hspace, hητ, hη]
  have hτ₁lam : τ₁ * log lam ≤ 1 / 10 := by
    rw [hloglam, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hτ₁le, hη]
  have hlog2 : log (lam * x) ≤ 2 * log x := by
    rw [log_mul (by linarith) (by linarith)]
    linarith only [log_le_log (by linarith) hxlam]
  refine ⟨primeWindow x lam, τ₁, ρ, fun p hp => (mem_primeWindow (by linarith) hp).2.2, hρ0,
    by linarith only [hτ₁ge, hspace, hrho, hη], by linarith only [hτ₁le, hrho, hη], fun τ hτ => ?_⟩
  have hτρ : |τ - τ₁| * log (lam * x) ≤ 1 / 10 := by
    have : |τ - τ₁| ≤ ρ := abs_le.mpr ⟨by linarith only [hτ.1], by linarith only [hτ.2]⟩
    calc |τ - τ₁| * log (lam * x) ≤ ρ * log (lam * x) :=
          mul_le_mul_of_nonneg_right this hloglamx.le
      _ = 1 / 10 := by rw [hρdef]; field_simp
  have hmain := eulerProductSq_window_ge hσ0 hx1 hlam htheta hτ₁x hτ₁0 hτ₁lam hτρ
  exact (le_rho_mul_of_growth hloglamx hlog2 hgrowth).trans
    (mul_le_mul_of_nonneg_left hmain hρ0.le)

/-! ## The spectral hypercube form -/

/-- **The spectral hypercube form diverges below the abscissa one.** Let `0 ≤ σ < 1` and let
`w ≥ 0` be integrable, continuous at a height `τ₀ > 0`, with `w(τ₀) > 0`. Then
`∫ w(τ) ∏_{p ∈ S} |1 − p^{−σ+iτ}|² dτ` is unbounded over finite sets of primes. -/
theorem spectralHypercube_unbounded {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {w : ℝ → ℝ}
    (hwi : Integrable w) (hw0 : ∀ τ, 0 ≤ w τ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hwc : ContinuousAt w τ₀) (hwτ₀ : 0 < w τ₀) (M : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ M ≤ ∫ τ, w τ * eulerProductSq σ τ S := by
  -- `w ≥ w(τ₀)/2` near `τ₀`
  obtain ⟨η₁, hη₁, hnear⟩ := Metric.continuousAt_iff.mp hwc (w τ₀ / 2) (by linarith)
  set η := min (η₁ / 2) (τ₀ / 2) with hηdef
  have hη : 0 < η := by positivity
  have hητ : η < τ₀ := by rw [hηdef]; linarith [min_le_right (η₁ / 2) (τ₀ / 2)]
  have hwlow : ∀ τ ∈ Set.Icc (τ₀ - η) (τ₀ + η), w τ₀ / 2 ≤ w τ := by
    intro τ hτ
    have hd : dist τ τ₀ < η₁ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hτ.1, hτ.2, min_le_left (η₁ / 2) (τ₀ / 2)]
    have := hnear hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  obtain ⟨S, τ₁, ρ, hSp, hρ, hlo, hhi, hbig⟩ :=
    exists_aligned_window hσ0 hσ1 hη hητ (2 * |M| / w τ₀ + 1)
  refine ⟨S, hSp, ?_⟩
  have hint : Integrable (fun τ => w τ * eulerProductSq σ τ S) := by
    refine (hwi.mul_bdd (continuous_eulerProductSq σ S).aestronglyMeasurable
      (c := 4 ^ S.card) (Eventually.of_forall fun τ => ?_))
    rw [norm_of_nonneg (eulerProductSq_nonneg σ τ S), eulerProductSq]
    calc ∏ p ∈ S, eulerFactorSq σ τ p ≤ ∏ _p ∈ S, (4 : ℝ) :=
          prod_le_prod (fun p _ => eulerFactorSq_nonneg σ τ p)
            fun p hp => eulerFactorSq_le_four hσ0 τ (hSp p hp).one_lt.le
      _ = 4 ^ S.card := by simp
  have hset : ∫ τ in Set.Icc (τ₁ - ρ) (τ₁ + ρ), w τ * eulerProductSq σ τ S ≤
      ∫ τ, w τ * eulerProductSq σ τ S :=
    setIntegral_le_integral hint
      (Eventually.of_forall fun τ => mul_nonneg (hw0 τ) (eulerProductSq_nonneg σ τ S))
  have hconst : ∫ τ in Set.Icc (τ₁ - ρ) (τ₁ + ρ), w τ₀ / 2 * ((2 * |M| / w τ₀ + 1) / ρ) ≤
      ∫ τ in Set.Icc (τ₁ - ρ) (τ₁ + ρ), w τ * eulerProductSq σ τ S := by
    refine setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc
      fun τ hτ => ?_
    have hτw : τ ∈ Set.Icc (τ₀ - η) (τ₀ + η) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have h1 := hwlow τ hτw
    have h2 : (2 * |M| / w τ₀ + 1) / ρ ≤ eulerProductSq σ τ S := by
      exact (div_le_iff₀ hρ).mpr ((hbig τ hτ).trans_eq (mul_comm _ _))
    exact mul_le_mul h1 h2 (by positivity) (hw0 τ)
  have hval : ∫ τ in Set.Icc (τ₁ - ρ) (τ₁ + ρ), w τ₀ / 2 * ((2 * |M| / w τ₀ + 1) / ρ) =
      2 * ρ * (w τ₀ / 2 * ((2 * |M| / w τ₀ + 1) / ρ)) := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  have hcalc : 2 * ρ * (w τ₀ / 2 * ((2 * |M| / w τ₀ + 1) / ρ)) = 2 * |M| + w τ₀ := by
    field_simp
  have : M ≤ 2 * |M| + w τ₀ := by linarith [le_abs_self M, abs_nonneg M]
  linarith

end GaloisForLFunctions.SignedSuccessorArithmetic
