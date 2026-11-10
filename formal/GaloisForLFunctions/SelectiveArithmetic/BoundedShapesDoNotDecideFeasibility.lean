import GaloisForLFunctions.SelectiveArithmetic.InTheMeanOverTheHeightsTheContactsCancel
import GaloisForLFunctions.SelectiveArithmetic.AHeightIsAConductorOfTheTwistedContacts
import GaloisForLFunctions.SelectiveArithmetic.AnIsolatedPairShowsAtTheRungOfItsDepth

/-!
# Bounded shapes do not decide feasibility

The sign of a system has been used in two forms: on every test of an aperture (`Feasible`), and
on packets of bounded shape, `𝔚(f) ≥ c (∫ f² − ∫ f'²)`. Cancellation of the contacts buys the
second form. This module separates the two.

**Theorem** (`exists_shape_positive_not_feasible`). For every `η > 0` and every conductor with
`log q` large there is a dominated system `w` such that at the aperture
`a = log log q + log 2 + η`
* `𝔚_{w,q}(f) ≥ ½ log q (∫ f² − ∫ f'²)` for every `C³` packet `f` vanishing off `(−a, a)`, and
* `w` is not feasible at `(q, a)`.

The system is aligned with a height `t₀` of the size of a power of `log q`:
`w(n) = Λ(n) cos(t₀ log n)`.

**Mechanism.** The symbol of the aligned system at the frequency `τ` is the archimedean symbol
minus `D(t₀ − τ) + D(t₀ + τ)`, `D` the contact polynomial of the primes
(`two_mul_sum_twisted_aligned`). A mean value over the heights gives a `t₀` at which `D` is at
most `log q / 8` on an interval of radius `τ₁ = 4e^{η/2}(2 + 2a)` around `t₀`, and at which the
Riesz mean of `Λ(n) cos²(t₀ log n)` keeps half of the Riesz mean of the primes. Outside the
interval the size `2 Σ Λ(n)/√n ≤ (log q / 4) τ₁²` is paid by `τ²`. So the symbol plus `log q` is
at least `(¾ log q − A₀) − (log q / 4) τ²`, which is the sign on bounded shapes
(`systemForm_aligned_ge`). At the height `t₀` the twisted contacts of the system are
`Λ(n) cos²(t₀ log n)`: their Riesz mean has no cancellation, and a feasible system has
square-root cancellation of its twisted Riesz means at every height. The sizes are balanced by
`K a¹² < e^{a}` (`grid_budget`, `receiver_budget`).

So the sign on packets of bounded shape reads the contacts at the height zero only; a producer of
feasibility has to control every height.
-/

open Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### The symbol of a system aligned with a height -/

/-- **Product formula.** The contacts of the system aligned with `t`, twisted by `τ`, add up to
the contact polynomial of the primes at the heights `t − τ` and `t + τ`. -/
theorem two_mul_sum_twisted_aligned (t τ : ℝ) (N : ℕ) :
    2 * ∑ n ∈ Finset.Icc 2 N, twistedWeight (alignedWeight t) τ n / Real.sqrt n =
      contactPoly N (t - τ) + contactPoly N (t + τ) := by
  unfold contactPoly
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold twistedWeight alignedWeight
  rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
  ring

/-- **The sign on bounded shapes of an aligned system.** If the contact polynomial satisfies
`D(t − τ) + D(t + τ) ≤ c (1 + τ²)` at every `τ`, the form of the system aligned with `t` is at
least `(log q − A₀ − c) ∫ f² − c ∫ f'²` on `C³` packets. -/
theorem systemForm_aligned_ge {a q t c : ℝ}
    (hD : ∀ τ : ℝ, contactPoly ⌊Real.exp (2 * a)⌋₊ (t - τ) +
      contactPoly ⌊Real.exp (2 * a)⌋₊ (t + τ) ≤ c * (1 + τ ^ 2))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (h0 : ∀ u, a ≤ |u| → f u = 0) :
    (Real.log q - archConstant - c) * (∫ u, f u ^ 2) - c * ∫ u, deriv f u ^ 2 ≤
      systemForm (alignedWeight t) q a (fun u => (f u : ℂ)) := by
  have hF : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet (hf.of_le (by norm_num))
  have hFs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  have hSb : ∀ τ : ℝ, (Real.log q - archConstant - c) - c * τ ^ 2 ≤
      _root_.RHTower.weilAtomSymbol (alignedWeight t) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
        Real.log q := by
    intro τ
    rw [weilAtomSymbol_eq_twisted, two_mul_sum_twisted_aligned]
    have h1 := neg_archConstant_le_archimedeanWeilSymbol τ
    have h2 := hD τ
    linarith
  have hS := _root_.RHTower.integrable_normSq_paperFT_mul_weilAtomSymbol_of hF hFs
    (alignedWeight t)
  have hB : Integrable fun τ : ℝ => Real.log q * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 :=
    (_root_.RHTower.integrable_normSq_paperFT hF hFs).const_mul _
  have hSint : Integrable fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
      (_root_.RHTower.weilAtomSymbol (alignedWeight t) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
        Real.log q) := by
    have e : (fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          (_root_.RHTower.weilAtomSymbol (alignedWeight t) ⌊Real.exp (2 * a)⌋₊
            (τ / (2 * π)) + Real.log q)) =
        fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
            _root_.RHTower.weilAtomSymbol (alignedWeight t) ⌊Real.exp (2 * a)⌋₊
              (τ / (2 * π)) +
          Real.log q * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 := by
      funext τ
      ring
    rw [e]
    exact hS.add hB
  have h := integral_normSq_paperFT_mul_ge hf h0 hSint hSb
  unfold systemForm
  linarith

/-- The Riesz mean of the primes on the window, from the second integer on. -/
theorem riesz_window_eq (a : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp (2 * a)⌋₊,
        (Λ n : ℝ) * Real.log (Real.exp (2 * a) / n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n) := by
  have h1 : ∑ n ∈ Finset.Icc 1 ⌊Real.exp (2 * a)⌋₊,
        (Λ n : ℝ) * Real.log (Real.exp (2 * a) / n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (Λ n : ℝ) * Real.log (Real.exp (2 * a) / n) := by
    refine (Finset.sum_subset (fun n hn => ?_) fun n hn hn2 => ?_).symm
    · rw [Finset.mem_Icc] at hn ⊢
      omega
    · have : n = 1 := by
        rw [Finset.mem_Icc] at hn hn2
        omega
      subst this
      simp
  rw [h1]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
  rw [Real.log_div (Real.exp_pos _).ne' hn0.ne', Real.log_exp]

/-! ### The two budgets -/

/-- **The budget of the grid.** With `E = 2e₂x = e^{a}`, `s = 2 + 2a`, the radius `τ₁ = 4e₁s`
and the slope bound `L̄ = 2aEs² + 1`: once `4345298944 e₁ e₂² a¹² ≤ E ε`, the mean-value bound of
the contact polynomial on the grid is below `(x/16)²`. -/
theorem grid_budget {a s E x e₁ e₂ ε τ₁ Lb : ℝ} (ha : 1 ≤ a) (hs : s = 2 + 2 * a)
    (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂) (hE : 2 * e₂ * x = E) (hx : 16 ≤ x) (hε : 0 < ε)
    (hτ₁ : τ₁ = 4 * e₁ * s) (hLb : Lb = 2 * a * (E * s ^ 2) + 1)
    (hbig : 4345298944 * e₁ * e₂ ^ 2 * a ^ 12 ≤ E * ε) :
    2 * ((2 * (16 * τ₁ * Lb / x + 1) + 1) * (2 * a * s ^ 2 + 1)) / ε ≤ (x / 16) ^ 2 := by
  have ha0 : 0 ≤ a := by linarith
  have he₁0 : 0 < e₁ := by linarith
  have he₂0 : 0 < e₂ := by linarith
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hs4a : s ≤ 4 * a := by rw [hs]; linarith
  have hE0 : 0 < E := by rw [← hE]; positivity
  have hE1 : 1 ≤ E := by
    rw [← hE]
    have := mul_le_mul he₂ hx (by norm_num) he₂0.le
    linarith
  -- `L̄ ≤ s³ E`
  have hEs : 1 ≤ E * s ^ 2 := one_le_mul_of_one_le_of_one_le hE1 (one_le_pow₀ hs1)
  have hs3 : s ^ 3 * E = 2 * a * (E * s ^ 2) + 2 * (E * s ^ 2) := by
    linear_combination (E * s ^ 2) * hs
  have hLble : Lb ≤ s ^ 3 * E := by
    rw [hLb, hs3]
    linarith
  -- the number of grid points
  have hquot : 16 * τ₁ * Lb / x ≤ 128 * e₁ * e₂ * s ^ 4 := by
    rw [div_le_iff₀ hx0, hτ₁]
    have h1 := mul_le_mul_of_nonneg_left hLble (by positivity : (0 : ℝ) ≤ 64 * e₁ * s)
    rw [← hE] at h1
    linarith
  have hone : 1 ≤ e₁ * e₂ * s ^ 4 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he₁ he₂) (one_le_pow₀ hs1)
  have hfac1 : 2 * (16 * τ₁ * Lb / x + 1) + 1 ≤ 259 * (e₁ * e₂ * s ^ 4) := by linarith
  have hfac2 : 2 * a * s ^ 2 + 1 ≤ s ^ 3 := by
    have e : s ^ 3 = 2 * a * s ^ 2 + 2 * s ^ 2 := by linear_combination (s ^ 2) * hs
    have h1 : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs1
    rw [e]
    linarith
  have hprod : (2 * (16 * τ₁ * Lb / x + 1) + 1) * (2 * a * s ^ 2 + 1) ≤
      259 * (e₁ * e₂ * s ^ 4) * s ^ 3 :=
    mul_le_mul hfac1 hfac2 (by positivity) (by positivity)
  -- `s⁷ ≤ 16384 a¹²`
  have hs7 : s ^ 7 ≤ 16384 * a ^ 12 := by
    have h1 : s ^ 7 ≤ (4 * a) ^ 7 := pow_le_pow_left₀ hs0.le hs4a 7
    have h2 : a ^ 7 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
    have e : (4 * a) ^ 7 = 16384 * a ^ 7 := by ring
    rw [e] at h1
    linarith
  -- the mass side
  have hA : 2172649472 * e₁ * e₂ * a ^ 12 ≤ x * ε := by
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < 2 * e₂)
    rw [← hE] at hbig
    linarith
  have hx2 : x ≤ x ^ 2 := by
    nlinarith [mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ x - 1)]
  rw [div_le_iff₀ hε]
  have h1 : 2 * ((2 * (16 * τ₁ * Lb / x + 1) + 1) * (2 * a * s ^ 2 + 1)) ≤
      518 * (e₁ * e₂) * s ^ 7 := by
    have e : 259 * (e₁ * e₂ * s ^ 4) * s ^ 3 = 259 * (e₁ * e₂) * s ^ 7 := by ring
    rw [e] at hprod
    linarith
  have h2 : 518 * (e₁ * e₂) * s ^ 7 ≤ 518 * (e₁ * e₂) * (16384 * a ^ 12) :=
    mul_le_mul_of_nonneg_left hs7 (by positivity)
  have h3 : x * ε ≤ x ^ 2 * ε := mul_le_mul_of_nonneg_right hx2 hε.le
  have e2 : (x / 16) ^ 2 * ε = x ^ 2 * ε / 256 := by ring
  rw [e2]
  linarith

/-- **The budget of the receiver.** With `E = 2e₂x`, `κ₂ e₂ = 1`: once
`(31 + 8C) a¹² < ½ (κ₁ − κ₂) E`, the bound of the twisted Riesz mean of a feasible system at a
height of size `E⁸` is below `½ κ₁ E²`. -/
theorem receiver_budget {a E x e₂ κ₁ κ₂ C l4 : ℝ} (ha : 1 ≤ a) (haE : a ≤ E) (hE0 : 0 < E)
    (he₂ : 1 ≤ e₂) (hE : 2 * e₂ * x = E) (hκ₂ : κ₂ * e₂ = 1) (hκ₂0 : 0 ≤ κ₂)
    (hl4 : l4 ≤ 2) (hC : 0 ≤ C)
    (hbig : (31 + 8 * C) * a ^ 12 < (κ₁ - κ₂) / 2 * E) :
    (x + (l4 + 8 * a)) * (E + 2 * a) + C * (1 + a) ^ 3 * E < κ₁ / 2 * E ^ 2 := by
  have ha0 : 0 ≤ a := by linarith
  have hxκ : x = κ₂ * E / 2 := by linear_combination (κ₂ / 2) * hE - x * hκ₂
  have hκ₂1 : κ₂ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left he₂ hκ₂0
    linarith
  have hxle : x ≤ E / 2 := by
    have := mul_le_mul_of_nonneg_right hκ₂1 hE0.le
    rw [hxκ]
    linarith
  have h1 : x * E = κ₂ / 2 * E ^ 2 := by
    rw [hxκ]
    ring
  have h2 : 2 * a * x ≤ a * E := by
    have := mul_le_mul_of_nonneg_left hxle (by linarith : (0 : ℝ) ≤ 2 * a)
    linarith
  have h3 : (l4 + 8 * a) * (E + 2 * a) ≤ 30 * a * E :=
    (mul_le_mul (by linarith : l4 + 8 * a ≤ 10 * a) (by linarith : E + 2 * a ≤ 3 * E)
      (by linarith) (by linarith)).trans (le_of_eq (by ring))
  have ha3 : a ^ 3 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
  have ha12 : a ≤ a ^ 12 := le_self_pow₀ ha (by norm_num)
  have hp3 : (1 + a) ^ 3 ≤ 8 * a ^ 12 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + a) (by linarith : 1 + a ≤ 2 * a) 3
    have e : (2 * a) ^ 3 = 8 * a ^ 3 := by ring
    rw [e] at h
    linarith
  have h4 : C * (1 + a) ^ 3 * E ≤ C * (8 * a ^ 12) * E :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp3 hC) hE0.le
  have h5 : a * E ≤ a ^ 12 * E := mul_le_mul_of_nonneg_right ha12 hE0.le
  have h6 := mul_lt_mul_of_pos_right hbig hE0
  linarith

/-! ### The aligned system at a quiet height -/

/-- **The separation at given sizes.** With `x = log q`, `E = e^{a} = 2e^{η}x`, `s = 2 + 2a`,
the radius `τ₁`, the slope bound `L̄`, the grid budget, the receiver budget and the Riesz mean of
the primes at `E²`: some system aligned with a height has the sign on bounded shapes at the
aperture `a` and is not feasible there. -/
theorem aligned_shape_positive_not_feasible_of {η C₃ q a x E s ε τ₁ Lb : ℝ}
    (hrecv : ∀ t : ℝ, Feasible q a (alignedWeight t) →
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistedWeight (alignedWeight t) t n * (2 * a - Real.log n)| ≤
        (x + Real.log (2 + |t|)) * (E + 2 * a) + C₃ * (1 + a) ^ 3 * E)
    (ha1 : 1 ≤ a) (hx : x = Real.log q) (hE : E = Real.exp a) (hs : s = 2 + 2 * a)
    (hε : ε = (1 - Real.exp (-η / 4)) / 4) (hη : 0 < η)
    (hτ₁ : τ₁ = 4 * Real.exp (η / 2) * s) (hLb : Lb = 2 * a * (E * s ^ 2) + 1)
    (hxE : 2 * Real.exp η * x = E) (h16 : 16 ≤ x) (hA : archConstant ≤ x / 4)
    (hTε : 1 / E ^ 8 ≤ ε) (hsE : 2 * s ≤ E)
    (hgrid : 2 * ((2 * (16 * τ₁ * Lb / x + 1) + 1) * (2 * a * s ^ 2 + 1)) / ε ≤ (x / 16) ^ 2)
    (hrec : (x + (Real.log 4 + 8 * a)) * (E + 2 * a) + C₃ * (1 + a) ^ 3 * E <
      Real.exp (-η / 2) / 2 * E ^ 2)
    (hR : Real.exp (-η / 4) * E ^ 2 ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n)) :
    ∃ t : ℝ, (∀ {f : ℝ → ℝ}, ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
        x / 2 * ((∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2) ≤
          systemForm (alignedWeight t) q a (fun u => (f u : ℂ))) ∧
      ¬ Feasible q a (alignedWeight t) := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs4 : 4 ≤ s := by rw [hs]; linarith
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hE1 : 1 ≤ E := by linarith
  have he4 : Real.exp (-η / 4) < 1 := by
    have : Real.exp (-η / 4) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at this
  have he4pos : 0 < Real.exp (-η / 4) := Real.exp_pos _
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  -- the window
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊Real.exp (2 * a)⌋₊ := ⟨_, rfl⟩
  rw [← hNdef] at hR hrecv
  have hN : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_exp (by linarith))
  -- the sizes of the contact polynomial
  have hP : contactMass N ≤ E * s ^ 2 := by
    rw [hNdef, hE, hs]
    exact contactMass_le ha0
  have hQ : contactEnergy N ≤ 2 * a * s ^ 2 := by
    rw [hNdef, hs]
    exact contactEnergy_le ha0
  have hL : contactSlope N ≤ Lb := by
    have h := contactSlope_le ha0
    rw [hNdef, hLb, hE, hs]
    linarith
  -- the heights
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = E ^ 8 := ⟨_, rfl⟩
  have hET : E ≤ T := by
    rw [hTdef]
    exact le_self_pow₀ hE1 (by norm_num)
  have hT2 : 2 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hTε' : 1 / T ≤ ε := by
    rw [hTdef]
    exact hTε
  have hsmall : 4 * (N : ℝ) * contactMass N ^ 2 ≤ T := by
    have h := four_mul_window_mass_sq_le ha0
    rw [← hNdef] at h
    have hE4 : Real.exp (4 * a) = E ^ 4 := by
      rw [hE, show (4 : ℝ) * a = a + a + a + a by ring, Real.exp_add, Real.exp_add,
        Real.exp_add]
      ring
    rw [hE4, ← hs] at h
    have h2 : (2 * s) ^ 4 ≤ E ^ 4 := pow_le_pow_left₀ (by linarith) hsE 4
    have e : (2 * s) ^ 4 = 16 * s ^ 4 := by ring
    rw [e] at h2
    have h3 : 4 * s ^ 4 ≤ E ^ 4 := by linarith [pow_nonneg hs0.le 4]
    have h4 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hE0.le 4)
    rw [hTdef]
    linarith
  -- the Riesz weights
  have hr : ∀ n ∈ Finset.Icc 2 N, 0 ≤ (Λ n : ℝ) * (2 * a - Real.log n) := by
    intro n hn
    rw [hNdef] at hn
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
    have hlog : Real.log n ≤ 2 * a :=
      (Real.log_le_log hn0 (cast_le_exp_of_mem hn)).trans_eq (Real.log_exp _)
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by linarith)
  have hRpos : 0 < ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) * (2 * a - Real.log n) :=
    lt_of_lt_of_le (by positivity) hR
  -- the grid
  have hτ₁0 : 0 ≤ τ₁ := by
    rw [hτ₁]
    positivity
  have hLb0 : 0 < Lb := by
    rw [hLb]
    positivity
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = x / (16 * Lb) := ⟨_, rfl⟩
  have hh0 : 0 < h := by
    rw [hh]
    positivity
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌈16 * τ₁ * Lb / x⌉₊ := ⟨_, rfl⟩
  have hquot0 : 0 ≤ 16 * τ₁ * Lb / x := by positivity
  have hM1 : (M : ℝ) ≤ 16 * τ₁ * Lb / x + 1 := by
    rw [hM]
    exact (Nat.ceil_lt_add_one hquot0).le
  have hM2 : 16 * τ₁ * Lb / x ≤ (M : ℝ) := by
    rw [hM]
    exact Nat.le_ceil _
  have hLbh : Lb * h = x / 16 := by
    rw [hh, mul_div_assoc', mul_comm Lb x, mul_div_mul_right _ _ hLb0.ne']
  have hMh : τ₁ ≤ M * h := by
    have h1 := (div_le_iff₀ hx0).mp hM2
    rw [hh, mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith
  -- a quiet height that keeps half of the Riesz mean
  obtain ⟨t, ht, hG, hgr⟩ := exists_height_contactPoly_small hN hT2 M h
    (fun n => (Λ n : ℝ) * (2 * a - Real.log n)) hr hRpos hε0 hε1 hsmall
  refine ⟨t, ?_, ?_⟩
  · -- the sign on bounded shapes
    have hBud : 2 * ((2 * (M : ℝ) + 1) * (contactEnergy N + 1)) / ε ≤ (x / 16) ^ 2 := by
      have hQ0 := contactEnergy_nonneg N
      have hnum : (2 * (M : ℝ) + 1) * (contactEnergy N + 1) ≤
          (2 * (16 * τ₁ * Lb / x + 1) + 1) * (2 * a * s ^ 2 + 1) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum zero_le_two)
        hε0.le).trans hgrid
    have hgridabs : ∀ k ∈ Finset.range (2 * M + 1),
        |contactPoly N (t + ((k : ℝ) - M) * h)| ≤ x / 16 := fun k hk =>
      abs_le.mpr (abs_le_of_sq_le_sq' ((hgr k hk).trans hBud) (by linarith))
    have hslope : contactSlope N * h ≤ x / 16 := by
      have h1 := mul_le_mul_of_nonneg_right hL hh0.le
      rw [hLbh] at h1
      exact h1
    have hsup : ∀ σ : ℝ, |σ| ≤ τ₁ → |contactPoly N (t + σ)| ≤ x / 8 := by
      intro σ hσ
      have h1 := abs_contactPoly_le_of_grid hh0 hgridabs (hσ.trans hMh)
      linarith
    have hτ₁sq : x / 4 * τ₁ ^ 2 = 2 * (E * s ^ 2) := by
      have he : Real.exp (η / 2) ^ 2 = Real.exp η := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [hτ₁]
      linear_combination (4 * x * s ^ 2) * he + (2 * s ^ 2) * hxE
    have hD : ∀ τ : ℝ, contactPoly N (t - τ) + contactPoly N (t + τ) ≤
        x / 4 * (1 + τ ^ 2) := by
      intro τ
      by_cases hτ : |τ| ≤ τ₁
      · have h1 := (abs_le.mp (hsup (-τ) (by rwa [abs_neg]))).2
        have h2 := (abs_le.mp (hsup τ hτ)).2
        rw [← sub_eq_add_neg] at h1
        have h3 : 0 ≤ x / 4 * τ ^ 2 := by positivity
        linarith
      · push Not at hτ
        have h1 := (abs_le.mp (abs_contactPoly_le N (t - τ))).2
        have h2 := (abs_le.mp (abs_contactPoly_le N (t + τ))).2
        have h3 : τ₁ ^ 2 ≤ τ ^ 2 := by
          have := pow_le_pow_left₀ hτ₁0 hτ.le 2
          rwa [sq_abs] at this
        have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ x / 4)
        linarith
    intro f hf h0
    have hD' : ∀ τ : ℝ, contactPoly ⌊Real.exp (2 * a)⌋₊ (t - τ) +
        contactPoly ⌊Real.exp (2 * a)⌋₊ (t + τ) ≤ x / 4 * (1 + τ ^ 2) := by
      rw [← hNdef]
      exact hD
    have hform := systemForm_aligned_ge (q := q) hD' hf h0
    rw [← hx] at hform
    have hI0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hI1 : 0 ≤ ∫ u, deriv f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have h5 := mul_nonneg (by linarith : (0 : ℝ) ≤ x / 4 - archConstant) hI0
    have h6 := mul_nonneg (by linarith : (0 : ℝ) ≤ x / 4) hI1
    linarith
  · -- not feasible: the twisted Riesz mean at the own height has no cancellation
    intro hfe
    have h1 := hrecv t hfe
    have hsum : ∑ n ∈ Finset.Icc 2 N,
          twistedWeight (alignedWeight t) t n * (2 * a - Real.log n) =
        ∑ n ∈ Finset.Icc 2 N,
          (Λ n : ℝ) * (2 * a - Real.log n) * Real.cos (t * Real.log n) ^ 2 :=
      Finset.sum_congr rfl fun n _ => by
        unfold twistedWeight alignedWeight
        ring
    rw [hsum] at h1
    have hG' : (1 / 2 - 1 / T - ε) * ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) * (2 * a - Real.log n) ≤
        ∑ n ∈ Finset.Icc 2 N,
          (Λ n : ℝ) * (2 * a - Real.log n) * Real.cos (t * Real.log n) ^ 2 := hG
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ,
        R = ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) * (2 * a - Real.log n) := ⟨_, rfl⟩
    obtain ⟨Gt, hGt⟩ : ∃ Gt : ℝ, Gt = ∑ n ∈ Finset.Icc 2 N,
        (Λ n : ℝ) * (2 * a - Real.log n) * Real.cos (t * Real.log n) ^ 2 := ⟨_, rfl⟩
    rw [← hRdef] at hG' hR
    rw [← hGt] at hG' h1
    have hcoef : Real.exp (-η / 4) / 2 ≤ 1 / 2 - 1 / T - ε := by
      rw [hε] at hTε' ⊢
      linarith
    have hlow : Real.exp (-η / 2) / 2 * E ^ 2 ≤ Gt := by
      have e2 : Real.exp (-η / 2) = Real.exp (-η / 4) * Real.exp (-η / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hR0 : 0 ≤ R := le_trans (by positivity) hR
      have h2 := mul_le_mul_of_nonneg_right hcoef hR0
      have h3 := mul_le_mul_of_nonneg_left hR
        (by positivity : (0 : ℝ) ≤ Real.exp (-η / 4) / 2)
      rw [e2]
      calc Real.exp (-η / 4) * Real.exp (-η / 4) / 2 * E ^ 2
          = Real.exp (-η / 4) / 2 * (Real.exp (-η / 4) * E ^ 2) := by ring
        _ ≤ Real.exp (-η / 4) / 2 * R := h3
        _ ≤ (1 / 2 - 1 / T - ε) * R := h2
        _ ≤ Gt := hG'
    have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
    have hlogt : Real.log (2 + |t|) ≤ Real.log 4 + 8 * a := by
      rw [abs_of_pos ht0]
      have hlogT : Real.log (E ^ 8) = 8 * a := by
        rw [Real.log_pow, hE, Real.log_exp]
        norm_num
      have h8 : 0 < E ^ 8 := by positivity
      rw [← hlogT, ← Real.log_mul (by norm_num) h8.ne']
      refine Real.log_le_log (by linarith) ?_
      have h9 := ht.2
      rw [hTdef] at h9 hT2
      linarith
    have hup : |Gt| ≤ (x + (Real.log 4 + 8 * a)) * (E + 2 * a) + C₃ * (1 + a) ^ 3 * E := by
      refine h1.trans ?_
      have := mul_le_mul_of_nonneg_right
        (by linarith : x + Real.log (2 + |t|) ≤ x + (Real.log 4 + 8 * a))
        (by linarith : (0 : ℝ) ≤ E + 2 * a)
      linarith
    linarith [le_abs_self Gt]

/-! ### The separation -/

/-- **Bounded shapes do not decide feasibility.** For every `η > 0` and every conductor with
`log q` large there is a dominated system that, at the aperture `a = log log q + log 2 + η`,
satisfies `𝔚_{w,q}(f) ≥ ½ log q (∫ f² − ∫ f'²)` on every `C³` packet vanishing off `(−a, a)`
and is not feasible. -/
theorem exists_shape_positive_not_feasible {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℝ, ∀ q : ℝ, M₀ ≤ Real.log q → ∃ w : ℕ → ℝ, Dominated w ∧
      (∀ {f : ℝ → ℝ}, ContDiff ℝ 3 f →
        (∀ u, Real.log (Real.log q) + Real.log 2 + η ≤ |u| → f u = 0) →
        Real.log q / 2 * ((∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2) ≤
          systemForm w q (Real.log (Real.log q) + Real.log 2 + η) (fun u => (f u : ℂ))) ∧
      ¬ Feasible q (Real.log (Real.log q) + Real.log 2 + η) w := by
  -- constants
  obtain ⟨e₁, he₁def⟩ : ∃ e₁ : ℝ, e₁ = Real.exp (η / 2) := ⟨_, rfl⟩
  obtain ⟨e₂, he₂def⟩ : ∃ e₂ : ℝ, e₂ = Real.exp η := ⟨_, rfl⟩
  have he₁ : 1 ≤ e₁ := by
    rw [he₁def]
    exact Real.one_le_exp (by linarith)
  have he₂ : 1 ≤ e₂ := by
    rw [he₂def]
    exact Real.one_le_exp hη.le
  have he₁0 : 0 < e₁ := by linarith
  have he₂0 : 0 < e₂ := by linarith
  have he4 : Real.exp (-η / 4) < 1 := by
    have : Real.exp (-η / 4) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at this
  have he4pos : 0 < Real.exp (-η / 4) := Real.exp_pos _
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 - Real.exp (-η / 4)) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    linarith
  have hκ : 0 < Real.exp (-η / 2) - Real.exp (-η) := by
    have : Real.exp (-η) < Real.exp (-η / 2) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_riesz_ge (η := 1 - Real.exp (-η / 4)) (by linarith)
    (by linarith)
  obtain ⟨C₃, hC₃⟩ := exists_twisted_riesz_le_of_feasible
  -- one inequality `K a¹² < e^{a}` for all sizes
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * e₂ * (16 + 4 * |archConstant|) + 1 / ε + 8 +
      4345298944 * e₁ * e₂ ^ 2 / ε +
      2 * (31 + 8 * |C₃|) / (Real.exp (-η / 2) - Real.exp (-η)) + Y₀ := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (eventually_pow_twelve_lt_exp K (c := 1) one_pos)
  refine ⟨Real.exp (max a₀ 1), fun q hq => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.log q := ⟨_, rfl⟩
  rw [← hx] at hq ⊢
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hq
  have hlogx : max a₀ 1 ≤ Real.log x := by
    rw [← Real.log_exp (max a₀ 1)]
    exact Real.log_le_log (Real.exp_pos _) hq
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.log x + Real.log 2 + η := ⟨_, rfl⟩
  rw [← ha]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha1 : 1 ≤ a := by linarith [le_max_right a₀ 1]
  have haa₀ : a₀ ≤ a := by linarith [le_max_left a₀ 1]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp a := ⟨_, rfl⟩
  have hE0 : 0 < E := by
    rw [hE]
    exact Real.exp_pos _
  have hxE : 2 * e₂ * x = E := by
    rw [hE, ha, he₂def, Real.exp_add, Real.exp_add, Real.exp_log hx0,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  have hmaster : K * a ^ 12 < E := by
    have h := ha₀ a haa₀
    rwa [one_mul, ← hE] at h
  have ha12 : 1 ≤ a ^ 12 := one_le_pow₀ ha1
  have hK1 : 0 ≤ 2 * e₂ * (16 + 4 * |archConstant|) := by positivity
  have hK2 : 0 ≤ 1 / ε := by positivity
  have hK4 : 0 ≤ 4345298944 * e₁ * e₂ ^ 2 / ε := by positivity
  have hK5 : 0 ≤ 2 * (31 + 8 * |C₃|) / (Real.exp (-η / 2) - Real.exp (-η)) :=
    div_nonneg (by positivity) hκ.le
  have hK6 : 0 ≤ Y₀ := by linarith
  have hpart : ∀ c : ℝ, c ≤ K → c * a ^ 12 < E := fun c hcK =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcK (by positivity)) hmaster
  have hpart' : ∀ c : ℝ, 0 ≤ c → c ≤ K → c < E := fun c hc hcK =>
    lt_of_le_of_lt (le_mul_of_one_le_right hc ha12) (hpart c hcK)
  -- the sizes
  have h16' : 16 + 4 * |archConstant| < x := by
    have h1 := hpart' _ hK1 (by rw [hK]; linarith)
    rw [← hxE] at h1
    exact lt_of_mul_lt_mul_left h1 (by positivity)
  have h16 : 16 ≤ x := by linarith [abs_nonneg archConstant]
  have hA : archConstant ≤ x / 4 := by linarith [le_abs_self archConstant]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 2 + 2 * a := ⟨_, rfl⟩
  have ha12' : a ≤ a ^ 12 := le_self_pow₀ ha1 (by norm_num)
  have hsE : 2 * s ≤ E := by
    have h3 := hpart 8 (by rw [hK]; linarith)
    rw [hs]
    linarith
  have hE1 : 1 ≤ E := by
    rw [hs] at hsE
    linarith
  have hE8 : E ≤ E ^ 8 := le_self_pow₀ hE1 (by norm_num)
  have hTε : 1 / E ^ 8 ≤ ε := by
    have h2 := hpart' _ hK2 (by rw [hK]; linarith)
    have h3 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / ε) (h2.le.trans hE8)
    rwa [one_div_one_div] at h3
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : ℝ, τ₁ = 4 * Real.exp (η / 2) * s := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = 2 * a * (E * s ^ 2) + 1 := ⟨_, rfl⟩
  have hgrid : 2 * ((2 * (16 * τ₁ * Lb / x + 1) + 1) * (2 * a * s ^ 2 + 1)) / ε ≤
      (x / 16) ^ 2 := by
    have h4 := hpart _ (by rw [hK]; linarith : 4345298944 * e₁ * e₂ ^ 2 / ε ≤ K)
    rw [div_mul_eq_mul_div, div_lt_iff₀ hε0] at h4
    exact grid_budget ha1 hs he₁ he₂ hxE h16 hε0 (by rw [hτ₁, he₁def]) hLb h4.le
  have hκ₂ : Real.exp (-η) * e₂ = 1 := by
    rw [he₂def, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hl4 : Real.log 4 ≤ 2 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [e]
    linarith [Real.log_two_lt_d9]
  have hrec : (x + (Real.log 4 + 8 * a)) * (E + 2 * a) + |C₃| * (1 + a) ^ 3 * E <
      Real.exp (-η / 2) / 2 * E ^ 2 := by
    have h5 := hpart _
      (by rw [hK]; linarith : 2 * (31 + 8 * |C₃|) / (Real.exp (-η / 2) - Real.exp (-η)) ≤ K)
    rw [div_mul_eq_mul_div, div_lt_iff₀ hκ] at h5
    have haE : a ≤ E := by
      rw [hE]
      linarith [Real.add_one_le_exp a]
    exact receiver_budget ha1 haE hE0 he₂ hxE hκ₂ (Real.exp_pos _).le hl4 (abs_nonneg C₃)
      (by linarith)
  -- the Riesz mean of the primes at `E²`
  have hE2 : Real.exp (2 * a) = E ^ 2 := by
    rw [hE, sq, ← Real.exp_add]
    congr 1
    ring
  have hR : Real.exp (-η / 4) * E ^ 2 ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) * (2 * a - Real.log n) := by
    have h6 := hpart' Y₀ hK6 (by rw [hK]; linarith)
    have hEE : E ≤ E ^ 2 := le_self_pow₀ hE1 (by norm_num)
    have hYE : Y₀ ≤ Real.exp (2 * a) := by
      rw [hE2]
      linarith
    have h := hY₀ _ hYE
    rw [riesz_window_eq, sub_sub_cancel] at h
    rw [← hE2]
    exact h
  -- the receiver at every height, for the aligned systems
  have hrecv : ∀ t : ℝ, Feasible q a (alignedWeight t) →
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistedWeight (alignedWeight t) t n * (2 * a - Real.log n)| ≤
        (x + Real.log (2 + |t|)) * (E + 2 * a) + |C₃| * (1 + a) ^ 3 * E := by
    intro t hfe
    have h := hC₃ (by rw [← hx]; exact hx0.le) ha1 (dominated_alignedWeight t) hfe t
    rw [← hx, ← hE] at h
    refine h.trans ?_
    have h0 : 0 ≤ (1 + a) ^ 3 * E := by positivity
    have h7 := mul_le_mul_of_nonneg_right (le_abs_self C₃) h0
    linarith
  obtain ⟨t, hpos, hneg⟩ := aligned_shape_positive_not_feasible_of (C₃ := |C₃|) hrecv ha1 hx hE
    hs hε hη hτ₁ hLb (by rw [← he₂def]; exact hxE) h16 hA hTε hsE hgrid hrec hR
  exact ⟨alignedWeight t, dominated_alignedWeight t, fun hf h0 => hpos hf h0, hneg⟩

end GaloisForLFunctions.SelectiveArithmetic
