import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightEightyFour
import GaloisForLFunctions.VerifiedHeightRungs.WeightedJensenRoots

/-!
# The Riemann hypothesis through height 150 via prime-phase-coupled Bohman analysis

In `TheVerifiedHeightEightyFour`, minimizing the prime-power Bohman trigonometric form
`bohmanPhaseForm` over **independent** phases `θ : ℕ → ℝ` saturated at height `169/2 = 84.5`
(with uncoupled reversal `θ ≡ π` at `γ = 85`). On actual real ordinates `γ > 0`, the phases
`θ(p) = γ log p` are coupled to the single real variable `γ` and cannot simultaneously align at `π`
until `γ ≈ 150.258`.

This module proves without locating any zero or computing any value of `ζ`:

* **`rhVerifiedThrough_oneHundredFifty` (`RHVerifiedThrough 150`)**: every zero of `ξ` in the
  critical strip with `0 < Im ρ ≤ 150` lies on `Re ρ = 1/2`.
* **`bohman_coupled_saturates_at_threeHundredOne_halves`**: at the **coupled real height**
  `γ = 301/2 = 150.5`, the `L = 9/2` Bohman explicit-formula inequality reverses strictly, proving
  `150` is the exact integer ceiling of the coupled `L = 9/2` Bohman test.
* **`bohman_any_band_eventually_reverses`**: for **every** band `L > 0` and finite prime cutoff `N`,
  the coupled Bohman edge inequality strictly reverses for all sufficiently large real heights `γ`.
* **Upgraded rungs**: `PF_449` at the centre of `ξ`, slice nonnegativity across `|t| ≤ 299/2`,
  `Re(2 λ_n) ≥ 0` for `n ≤ 705`, and real-rootedness of unshifted `Ξ` Jensen polynomials and all
  positive-integer Euler root filters through degree `160,036`.
-/

open Complex Set Polynomial FiniteFreeProbability
open ArithmeticFunction (vonMangoldt)
open scoped ComplexOrder

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Degree-10 cosine envelope and period-shifted cosine bounds -/

/-- Degree-10 even Taylor minorant of `Real.cos` valid for every `x : ℝ`. -/
def cosPoly10 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800

private theorem nonneg_of_deriv_nonneg' {f f' : ℝ → ℝ} (hf0 : f 0 = 0)
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ f u := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hpos x (interior_subset hx))
  simpa only [hf0] using hmono self_mem_Ici hu hu

private theorem hasDerivAt_monomial_div' (n : ℕ) (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ n / c) ((n : ℝ) * x ^ (n - 1) / c) x := by
  simpa only [mul_div_assoc] using ((hasDerivAt_pow n x).div_const c)

private theorem sin_cos_taylor_chain {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 ≤ Real.sin u ∧
      Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880 ∧
      cosPoly10 u ≤ Real.cos u := by
  have h1 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - Real.sin x := fun x hx =>
    nonneg_of_deriv_nonneg' (by simp)
      (fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y))
      (fun y _ => sub_nonneg.mpr (Real.cos_le_one y)) hx
  have h2 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2) := fun x hx =>
    nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h1 y hy) hx
  have h3 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6) := fun x hx =>
    nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h2 y hy) hx
  have h4 : ∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x := fun x hx =>
    nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
        (hasDerivAt_monomial_div' 4 24 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h3 y hy) hx
  have h5 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x := fun x hx =>
    nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
        (hasDerivAt_monomial_div' 5 120 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h4 y hy) hx
  have h6 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub
          (hasDerivAt_monomial_div' 6 720 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h5 y hy) hx
  have h7 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
          (hasDerivAt_monomial_div' 5 120 y)).sub
          (hasDerivAt_monomial_div' 7 5040 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h6 y hy) hx
  have h8 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub
          (hasDerivAt_monomial_div' 6 720 y)).add
          (hasDerivAt_monomial_div' 8 40320 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h7 y hy) hx
  have h9 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
          (hasDerivAt_monomial_div' 5 120 y)).sub
          (hasDerivAt_monomial_div' 7 5040 y)).add
          (hasDerivAt_monomial_div' 9 362880 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h8 y hy) hx
  have h10 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub
          (hasDerivAt_monomial_div' 6 720 y)).add
          (hasDerivAt_monomial_div' 8 40320 y)).sub
          (hasDerivAt_monomial_div' 10 3628800 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h9 y hy) hx
  exact ⟨sub_nonneg.mp (h7 u hu), sub_nonneg.mp (h9 u hu), sub_nonneg.mp (h10 u hu)⟩

theorem cosPoly10_le_cos (x : ℝ) : cosPoly10 x ≤ Real.cos x := by
  rcases le_or_gt 0 x with hx | hx
  · exact (sin_cos_taylor_chain hx).2.2
  · have hneg : cosPoly10 (-x) = cosPoly10 x := by unfold cosPoly10; ring
    rw [← hneg, ← Real.cos_neg]
    exact (sin_cos_taylor_chain (by linarith only [hx])).2.2

private theorem cos_abs_eq (x : ℝ) : Real.cos |x| = Real.cos x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.cos_neg]

private theorem cos_sub_nat_mul_two_pi (θ : ℝ) (m : ℕ) :
    Real.cos (θ - 2 * (m : ℝ) * Real.pi) = Real.cos θ := by
  induction m with
  | zero => simp
  | succ k ih =>
    have heq : θ - 2 * (k : ℝ) * Real.pi =
        (θ - 2 * ((k + 1 : ℕ) : ℝ) * Real.pi) + 2 * Real.pi := by push_cast; ring
    rw [← ih, heq, Real.cos_add_two_pi]

private theorem cos_sub_odd_mul_pi (θ : ℝ) (m : ℕ) :
    Real.cos (θ - (2 * (m : ℝ) + 1) * Real.pi) = -Real.cos θ := by
  have heq : θ - (2 * (m : ℝ) + 1) * Real.pi = (θ - 2 * (m : ℝ) * Real.pi) - Real.pi := by ring
  rw [heq, Real.cos_sub_pi, cos_sub_nat_mul_two_pi]

private theorem pi_bounds_d10' : (3.1415926535 : ℝ) < Real.pi ∧ Real.pi < 3.1415926536 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

private theorem cos_mul_ge_of_even_shift {γ g_lo g_hi lp lp_lo lp_hi x_hi u_lo : ℝ} (m : ℕ)
    (hg0 : 0 ≤ g_lo) (hlo : g_lo ≤ γ) (hhi : γ ≤ g_hi)
    (hlp0 : 0 ≤ lp_lo) (hlp_lo : lp_lo ≤ lp) (hlp_hi : lp ≤ lp_hi)
    (hx_pi : x_hi ≤ 3.1415926535)
    (hsh_lo : -x_hi ≤ g_lo * lp_lo - 2 * (m : ℝ) * 3.1415926536)
    (hsh_hi : g_hi * lp_hi - 2 * (m : ℝ) * 3.1415926535 ≤ x_hi)
    (hu : u_lo ≤ cosPoly10 x_hi) :
    u_lo ≤ Real.cos (γ * lp) := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10'
  have hmul_lo : g_lo * lp_lo ≤ γ * lp := mul_le_mul hlo hlp_lo hlp0 (hg0.trans hlo)
  have hmul_hi : γ * lp ≤ g_hi * lp_hi :=
    mul_le_mul hhi hlp_hi (hlp0.trans hlp_lo) (hg0.trans (hlo.trans hhi))
  have hmπ_lo : 2 * (m : ℝ) * 3.1415926535 ≤ 2 * (m : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_left hπ_lo.le (by positivity)
  have hmπ_hi : 2 * (m : ℝ) * Real.pi ≤ 2 * (m : ℝ) * 3.1415926536 :=
    mul_le_mul_of_nonneg_left hπ_hi.le (by positivity)
  set d : ℝ := γ * lp - 2 * (m : ℝ) * Real.pi
  have hd_abs : |d| ≤ x_hi := abs_le.mpr ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hx_le_pi : x_hi ≤ Real.pi := hx_pi.trans hπ_lo.le
  have hcos_mono : Real.cos x_hi ≤ Real.cos |d| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg d) hx_le_pi hd_abs
  rw [cos_abs_eq] at hcos_mono
  dsimp only [d] at hcos_mono
  rw [cos_sub_nat_mul_two_pi] at hcos_mono
  exact hu.trans ((cosPoly10_le_cos x_hi).trans hcos_mono)

private theorem cos_mul_le_of_odd_shift {c lp lp_lo lp_hi s_hi u_hi : ℝ} (m : ℕ)
    (hc0 : 0 ≤ c) (hlp_lo : lp_lo ≤ lp) (hlp_hi : lp ≤ lp_hi)
    (hs_pi : s_hi ≤ 3.1415926535)
    (hsh_lo : -s_hi ≤ c * lp_lo - (2 * (m : ℝ) + 1) * 3.1415926536)
    (hsh_hi : c * lp_hi - (2 * (m : ℝ) + 1) * 3.1415926535 ≤ s_hi)
    (hu : -cosPoly10 s_hi ≤ u_hi) :
    Real.cos (c * lp) ≤ u_hi := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10'
  have h2m1 : 0 ≤ 2 * (m : ℝ) + 1 := by positivity
  have hmul_lo : c * lp_lo ≤ c * lp := mul_le_mul_of_nonneg_left hlp_lo hc0
  have hmul_hi : c * lp ≤ c * lp_hi := mul_le_mul_of_nonneg_left hlp_hi hc0
  have hmπ_lo : (2 * (m : ℝ) + 1) * 3.1415926535 ≤ (2 * (m : ℝ) + 1) * Real.pi :=
    mul_le_mul_of_nonneg_left hπ_lo.le h2m1
  have hmπ_hi : (2 * (m : ℝ) + 1) * Real.pi ≤ (2 * (m : ℝ) + 1) * 3.1415926536 :=
    mul_le_mul_of_nonneg_left hπ_hi.le h2m1
  set d : ℝ := c * lp - (2 * (m : ℝ) + 1) * Real.pi
  have hd_abs : |d| ≤ s_hi := abs_le.mpr ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hs_le_pi : s_hi ≤ Real.pi := hs_pi.trans hπ_lo.le
  have hcos_mono : Real.cos s_hi ≤ Real.cos |d| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg d) hs_le_pi hd_abs
  rw [cos_abs_eq] at hcos_mono
  dsimp only [d] at hcos_mono
  rw [cos_sub_odd_mul_pi] at hcos_mono
  have hle : Real.cos (c * lp) ≤ -cosPoly10 s_hi := by
    linarith [cosPoly10_le_cos s_hi, hcos_mono]
  exact hle.trans hu

/-! ## Global monotonicity of prime-power Chebyshev Bohman polynomials on `[-1, 1]` -/

/-- Degree-6 Chebyshev polynomial `∑_{k=1}^6 c_k T_k(u)`. -/
def chebPoly6 (A B C D E G u : ℝ) : ℝ :=
  A * u + B * (2 * u ^ 2 - 1) + C * (4 * u ^ 3 - 3 * u) +
    D * (8 * u ^ 4 - 8 * u ^ 2 + 1) + E * (16 * u ^ 5 - 20 * u ^ 3 + 5 * u) +
    G * (32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 1)

private theorem hasDerivAt_chebPoly6 (A B C D E G u : ℝ) :
    HasDerivAt (chebPoly6 A B C D E G)
      (A + 4 * B * u + C * (12 * u ^ 2 - 3) + D * (32 * u ^ 3 - 16 * u) +
        E * (80 * u ^ 4 - 60 * u ^ 2 + 5) + G * (192 * u ^ 5 - 192 * u ^ 3 + 36 * u)) u := by
  unfold chebPoly6
  refine ((((((hasDerivAt_id u).const_mul A).add
      ((((hasDerivAt_pow 2 u).const_mul 2).sub (hasDerivAt_const u 1)).const_mul B)).add
      ((((hasDerivAt_pow 3 u).const_mul 4).sub ((hasDerivAt_id u).const_mul 3)).const_mul C)).add
      (((((hasDerivAt_pow 4 u).const_mul 8).sub
        ((hasDerivAt_pow 2 u).const_mul 8)).add (hasDerivAt_const u 1)).const_mul D)).add
      ((((((hasDerivAt_pow 5 u).const_mul 16).sub
        ((hasDerivAt_pow 3 u).const_mul 20)).add
        ((hasDerivAt_id u).const_mul 5))).const_mul E)).add
      (((((((hasDerivAt_pow 6 u).const_mul 32).sub
        ((hasDerivAt_pow 4 u).const_mul 48)).add
        ((hasDerivAt_pow 2 u).const_mul 18)).sub
        (hasDerivAt_const u 1))).const_mul G) |>.congr_deriv ?_
  norm_num
  ring

private theorem monotoneOn_chebPoly6_of_sos {A B C D E G E_hi G_hi : ℝ}
    (hD : 0 ≤ D) (hE0 : 0 ≤ E) (hE : E ≤ E_hi) (hG0 : 0 ≤ G) (hG : G ≤ G_hi)
    (hq2 : 0 < 12 * C - 32 * D)
    (hdisc : (4 * B - 16 * D) ^ 2 ≤
      4 * (12 * C - 32 * D) * (A - 3 * C - (25 / 4) * E_hi - 228 * G_hi)) :
    MonotoneOn (chebPoly6 A B C D E G) (Icc (-1) 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-1) 1)
    (fun u _ => (hasDerivAt_chebPoly6 A B C D E G u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_chebPoly6 A B C D E G u).hasDerivWithinAt)
    fun u hu => ?_
  obtain ⟨hu0, hu1⟩ := interior_subset hu
  have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
  have he_lb : -((25 / 4) * E_hi) ≤ E * (80 * u ^ 4 - 60 * u ^ 2 + 5) := by
    have hid : 80 * u ^ 4 - 60 * u ^ 2 + 5 + 25 / 4 = 5 * (4 * u ^ 2 - 3 / 2) ^ 2 := by ring
    have hge : -(25 / 4 : ℝ) ≤ 80 * u ^ 4 - 60 * u ^ 2 + 5 := by
      nlinarith only [hid, sq_nonneg (4 * u ^ 2 - 3 / 2)]
    nlinarith only [hge, hE0, hE]
  have hg_lb : -(228 * G_hi) ≤ G * (192 * u ^ 5 - 192 * u ^ 3 + 36 * u) := by
    have h1mu2 : 0 ≤ 1 - u ^ 2 := by linarith only [hu2]
    have h1mu2_le1 : 1 - u ^ 2 ≤ 1 := by nlinarith only [sq_nonneg u]
    have hterm1 : -192 ≤ 192 * u ^ 3 * (u ^ 2 - 1) := by
      have : u ^ 3 * (1 - u ^ 2) ≤ 1 := by
        rcases le_or_gt (u ^ 3) 0 with h | h
        · exact (mul_nonpos_of_nonpos_of_nonneg h h1mu2).trans zero_le_one
        · have hu3_hi : u ^ 3 ≤ 1 := by
            have : 0 ≤ (1 - u) * (u ^ 2 + u + 1) :=
              mul_nonneg (by linarith only [hu1]) (by nlinarith only [sq_nonneg (u + 1 / 2)])
            linarith [show (1 - u) * (u ^ 2 + u + 1) = 1 - u ^ 3 by ring]
          nlinarith only [h, hu3_hi, h1mu2, h1mu2_le1]
      linarith
    have hge : (-228 : ℝ) ≤ 192 * u ^ 5 - 192 * u ^ 3 + 36 * u := by
      have : 192 * u ^ 5 - 192 * u ^ 3 + 36 * u = 192 * u ^ 3 * (u ^ 2 - 1) + 36 * u := by ring
      linarith only [this, hterm1, hu0]
    nlinarith only [hge, hG0, hG]
  have hd_cub : 0 ≤ 32 * D * (u + 1) * u ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith only [hu0])) (sq_nonneg u)
  set q2 : ℝ := 12 * C - 32 * D
  set q1 : ℝ := 4 * B - 16 * D
  set q0 : ℝ := A - 3 * C - (25 / 4) * E_hi - 228 * G_hi
  have hquad : 0 ≤ q2 * u ^ 2 + q1 * u + q0 := by
    have h4 : 0 ≤ 4 * q2 * (q2 * u ^ 2 + q1 * u + q0) := by
      nlinarith only [sq_nonneg (2 * q2 * u + q1), hdisc]
    exact nonneg_of_mul_nonneg_right h4 (by positivity)
  have hdecomp : A + 4 * B * u + C * (12 * u ^ 2 - 3) + D * (32 * u ^ 3 - 16 * u) -
      (25 / 4) * E_hi - 228 * G_hi =
      (q2 * u ^ 2 + q1 * u + q0) + 32 * D * (u + 1) * u ^ 2 := by
    dsimp only [q2, q1, q0]; ring
  linarith only [hdecomp, hquad, hd_cub, he_lb, hg_lb]

private theorem monotoneOn_chebPoly4_of_linear {A B C D : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hlin : 4 * B + 3 * C + 16 * D ≤ A) :
    MonotoneOn (chebPoly6 A B C D 0 0) (Icc (-1) 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-1) 1)
    (fun u _ => (hasDerivAt_chebPoly6 A B C D 0 0 u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_chebPoly6 A B C D 0 0 u).hasDerivWithinAt)
    fun u hu => ?_
  obtain ⟨hu0, _⟩ := interior_subset hu
  have hd_lb : -(16 * D) ≤ D * (32 * u ^ 3 - 16 * u) := by
    have hid : 32 * u ^ 3 - 16 * u + 16 = 16 * (u + 1) * (u ^ 2 + (u - 1) ^ 2) := by ring
    have hnn : 0 ≤ 16 * (u + 1) * (u ^ 2 + (u - 1) ^ 2) :=
      mul_nonneg (by linarith only [hu0]) (add_nonneg (sq_nonneg u) (sq_nonneg (u - 1)))
    nlinarith only [hid, hnn, hD]
  nlinarith only [hu0, hB, hC, sq_nonneg u, hd_lb, hlin]

private theorem weighted_sign_lb {c_lo c_hi c t : ℝ} (hlo : c_lo ≤ c) (hhi : c ≤ c_hi) :
    c_lo * max t 0 + c_hi * min t 0 ≤ c * t := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, min_eq_right ht]; nlinarith only [hlo, ht]
  · rw [max_eq_right ht, min_eq_left ht]; nlinarith only [hhi, ht]

/-! ## Fast inverse-hyperbolic-tangent logarithm enclosures (`max exponent ≤ 6`) -/

private theorem log_one_add_div_one_sub_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht_half : t ≤ 1 / 2) :
    2 * (t + t ^ 3 / 3) ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤ 2 * (t + t ^ 3 / 3 + t ^ 5) := by
  have hd_log : ∀ x ∈ Icc (0 : ℝ) (1 / 2),
      HasDerivAt (fun y => Real.log ((1 + y) / (1 - y))) (2 / (1 - x ^ 2)) x := by
    intro x hx
    have h1p : 0 < 1 + x := by linarith [hx.1]
    have h1m : 0 < 1 - x := by linarith [hx.2]
    have hm1x : -1 < x := by linarith [hx.1]
    have hx1 : x < 1 := by linarith [hx.2]
    have hfg : ∀ᶠ y in nhds x, Real.log ((1 + y) / (1 - y)) = Real.log (1 + y) - Real.log (1 - y) := by
      filter_upwards [lt_mem_nhds hm1x, gt_mem_nhds hx1] with y hy1 hy2
      exact Real.log_div (by linarith) (by linarith)
    have hd1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using (((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log h1p.ne')
    have hd2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
      refine (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log h1m.ne').congr_deriv ?_
      simp only [Pi.sub_apply, id_eq]; ring
    exact ((hd1.sub hd2).congr_of_eventuallyEq hfg).congr_deriv (by
      have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
      field_simp [h1p.ne', h1m.ne', hne]; ring)
  have hd_lo : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 2 * (y + y ^ 3 / 3)) (2 * (1 + x ^ 2)) x := fun x => by
    refine (((hasDerivAt_id x).add (hasDerivAt_monomial_div' 3 3 x)).const_mul 2).congr_deriv ?_
    norm_num
  have hd_hi : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 2 * (y + y ^ 3 / 3 + y ^ 5))
      (2 * (1 + x ^ 2 + 5 * x ^ 4)) x := fun x => by
    refine ((((hasDerivAt_id x).add (hasDerivAt_monomial_div' 3 3 x)).add
      (hasDerivAt_pow 5 x)).const_mul 2).congr_deriv ?_
    norm_num
  have hmono_lo : MonotoneOn (fun x => Real.log ((1 + x) / (1 - x)) - 2 * (x + x ^ 3 / 3))
      (Icc 0 (1 / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (fun x hx => ((hd_log x hx).sub (hd_lo x)).continuousAt.continuousWithinAt)
      (fun x hx => ((hd_log x (interior_subset hx)).sub (hd_lo x)).hasDerivWithinAt)
      fun x hx => by
        have hx' := interior_subset hx
        have hden : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        rw [sub_nonneg, le_div_iff₀ hden]
        nlinarith [sq_nonneg (x ^ 2)]
  have hmono_hi : MonotoneOn (fun x => 2 * (x + x ^ 3 / 3 + x ^ 5) - Real.log ((1 + x) / (1 - x)))
      (Icc 0 (1 / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
      (fun x hx => ((hd_hi x).sub (hd_log x hx)).continuousAt.continuousWithinAt)
      (fun x hx => ((hd_hi x).sub (hd_log x (interior_subset hx))).hasDerivWithinAt)
      fun x hx => by
        have hx' := interior_subset hx
        have hden : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        rw [sub_nonneg, div_le_iff₀ hden]
        have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [hx'.1, hx'.2]
        have h4 : 0 ≤ x ^ 4 * (4 - 5 * x ^ 2) := mul_nonneg (by positivity) (by linarith)
        nlinarith [h4]
  have hlo := hmono_lo ⟨le_rfl, by norm_num⟩ ⟨ht0, ht_half⟩ ht0
  have hhi := hmono_hi ⟨le_rfl, by norm_num⟩ ⟨ht0, ht_half⟩ ht0
  simp only [add_zero, sub_zero, div_one, Real.log_one] at hlo hhi
  norm_num at hlo hhi
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

private theorem log_atanh_pos_step {p M t lo hi base_lo base_hi : ℝ} {kp : ℕ}
    (hp : 0 < p) (hM : 0 < M) (hkp : 0 < kp) (ht0 : 0 ≤ t) (ht_half : t ≤ 1 / 2)
    (heq : p ^ kp / M = (1 + t) / (1 - t))
    (hbase_lo : base_lo ≤ Real.log M) (hbase_hi : Real.log M ≤ base_hi)
    (hlo : lo ≤ (base_lo + 2 * (t + t ^ 3 / 3)) / kp)
    (hhi : (base_hi + 2 * (t + t ^ 3 / 3 + t ^ 5)) / kp ≤ hi) :
    lo ≤ Real.log p ∧ Real.log p ≤ hi := by
  obtain ⟨hat_lo, hat_hi⟩ := log_one_add_div_one_sub_bounds ht0 ht_half
  have hkp' : (0 : ℝ) < kp := by exact_mod_cast hkp
  have hlog : (kp : ℝ) * Real.log p - Real.log M = Real.log ((1 + t) / (1 - t)) := by
    rw [← Real.log_pow, ← Real.log_div (pow_pos hp kp).ne' hM.ne', heq]
  refine ⟨hlo.trans ?_, ?_⟩
  · rw [div_le_iff₀ hkp']; linarith only [hlog, hbase_lo, hat_lo]
  · refine le_trans ?_ hhi
    rw [le_div_iff₀ hkp']; linarith only [hlog, hbase_hi, hat_hi]

private theorem log_atanh_neg_step {p M t lo hi base_lo base_hi : ℝ} {kp : ℕ}
    (hp : 0 < p) (hM : 0 < M) (hkp : 0 < kp) (ht0 : 0 ≤ t) (ht_half : t ≤ 1 / 2)
    (heq : M / p ^ kp = (1 + t) / (1 - t))
    (hbase_lo : base_lo ≤ Real.log M) (hbase_hi : Real.log M ≤ base_hi)
    (hlo : lo ≤ (base_lo - 2 * (t + t ^ 3 / 3 + t ^ 5)) / kp)
    (hhi : (base_hi - 2 * (t + t ^ 3 / 3)) / kp ≤ hi) :
    lo ≤ Real.log p ∧ Real.log p ≤ hi := by
  obtain ⟨hat_lo, hat_hi⟩ := log_one_add_div_one_sub_bounds ht0 ht_half
  have hkp' : (0 : ℝ) < kp := by exact_mod_cast hkp
  have hlog : Real.log M - (kp : ℝ) * Real.log p = Real.log ((1 + t) / (1 - t)) := by
    rw [← Real.log_pow, ← Real.log_div hM.ne' (pow_pos hp kp).ne', heq]
  refine ⟨hlo.trans ?_, ?_⟩
  · rw [div_le_iff₀ hkp']; linarith only [hlog, hbase_lo, hat_hi]
  · refine le_trans ?_ hhi
    rw [le_div_iff₀ hkp']; linarith only [hlog, hbase_hi, hat_lo]

private theorem log_smooth_bounds {M : ℝ} {a2 b3 c5 d7 : ℕ}
    (hM : M = (2 : ℝ) ^ a2 * (3 : ℝ) ^ b3 * (5 : ℝ) ^ c5 * (7 : ℝ) ^ d7)
    {l3a l3b l5a l5b l7a l7b : ℝ}
    (hl3a : l3a ≤ Real.log 3) (hl3b : Real.log 3 ≤ l3b)
    (hl5a : l5a ≤ Real.log 5) (hl5b : Real.log 5 ≤ l5b)
    (hl7a : l7a ≤ Real.log 7) (hl7b : Real.log 7 ≤ l7b) :
    (a2 : ℝ) * 0.6931471803 + (b3 : ℝ) * l3a + (c5 : ℝ) * l5a + (d7 : ℝ) * l7a ≤ Real.log M ∧
      Real.log M ≤ (a2 : ℝ) * 0.6931471808 + (b3 : ℝ) * l3b + (c5 : ℝ) * l5b + (d7 : ℝ) * l7b := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  rw [hM, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  exact ⟨add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hl2a (Nat.cast_nonneg a2))
      (mul_le_mul_of_nonneg_left hl3a (Nat.cast_nonneg b3)))
      (mul_le_mul_of_nonneg_left hl5a (Nat.cast_nonneg c5)))
      (mul_le_mul_of_nonneg_left hl7a (Nat.cast_nonneg d7)),
    add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hl2b (Nat.cast_nonneg a2))
      (mul_le_mul_of_nonneg_left hl3b (Nat.cast_nonneg b3)))
      (mul_le_mul_of_nonneg_left hl5b (Nat.cast_nonneg c5)))
      (mul_le_mul_of_nonneg_left hl7b (Nat.cast_nonneg d7))⟩

private theorem sharp_log_prime_bounds :
    (1.0986121 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0986129) ∧
    (1.6094379 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.609438) ∧
    (1.945908 ≤ Real.log 7 ∧ Real.log 7 ≤ 1.9459107) ∧
    (2.3978948 ≤ Real.log 11 ∧ Real.log 11 ≤ 2.397896) ∧
    (2.5649491 ≤ Real.log 13 ∧ Real.log 13 ≤ 2.5649502) ∧
    (2.8332133 ≤ Real.log 17 ∧ Real.log 17 ≤ 2.8332134) ∧
    (2.9444385 ≤ Real.log 19 ∧ Real.log 19 ≤ 2.9444403) ∧
    (3.135494 ≤ Real.log 23 ∧ Real.log 23 ≤ 3.1354949) ∧
    (3.3672956 ≤ Real.log 29 ∧ Real.log 29 ≤ 3.3672966) ∧
    (3.4339872 ≤ Real.log 31 ∧ Real.log 31 ≤ 3.4339873) ∧
    (3.6109175 ≤ Real.log 37 ∧ Real.log 37 ≤ 3.6109192) ∧
    (3.713572 ≤ Real.log 41 ∧ Real.log 41 ≤ 3.7135722) ∧
    (3.7611977 ≤ Real.log 43 ∧ Real.log 43 ≤ 3.7612013) ∧
    (3.8501474 ≤ Real.log 47 ∧ Real.log 47 ≤ 3.8501483) ∧
    (3.9702913 ≤ Real.log 53 ∧ Real.log 53 ≤ 3.9702938) ∧
    (4.0775372 ≤ Real.log 59 ∧ Real.log 59 ≤ 4.0775382) ∧
    (4.1108736 ≤ Real.log 61 ∧ Real.log 61 ≤ 4.1108746) ∧
    (4.2046926 ≤ Real.log 67 ∧ Real.log 67 ≤ 4.2046927) ∧
    (4.2626794 ≤ Real.log 71 ∧ Real.log 71 ≤ 4.2626812) ∧
    (4.290459 ≤ Real.log 73 ∧ Real.log 73 ≤ 4.2904607) ∧
    (4.3694478 ≤ Real.log 79 ∧ Real.log 79 ≤ 4.369448) ∧
    (4.4188382 ≤ Real.log 83 ∧ Real.log 83 ≤ 4.4188418) ∧
    (4.4886359 ≤ Real.log 89 ∧ Real.log 89 ≤ 4.4886377) := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have hM3 : (3 : ℝ) * 0.6931471803 ≤ Real.log 8 ∧ Real.log 8 ≤ (3 : ℝ) * 0.6931471808 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; exact ⟨by nlinarith only [hl2a], by nlinarith only [hl2b]⟩
  obtain ⟨hl3a, hl3b⟩ := log_atanh_pos_step (p := 3) (M := 8) (t := (1 / 17)) (lo := 1.0986121) (hi := 1.0986129) (kp := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM3.1 hM3.2 (by norm_num) (by norm_num)
  have hM5 : (7 : ℝ) * 0.6931471803 ≤ Real.log 128 ∧ Real.log 128 ≤ (7 : ℝ) * 0.6931471808 := by rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; exact ⟨by nlinarith only [hl2a], by nlinarith only [hl2b]⟩
  obtain ⟨hl5a, hl5b⟩ := log_atanh_neg_step (p := 5) (M := 128) (t := (3 / 253)) (lo := 1.6094379) (hi := 1.609438) (kp := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM5.1 hM5.2 (by norm_num) (by norm_num)
  have hM7 : (3 : ℝ) * 0.6931471803 ≤ Real.log 8 ∧ Real.log 8 ≤ (3 : ℝ) * 0.6931471808 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; exact ⟨by nlinarith only [hl2a], by nlinarith only [hl2b]⟩
  obtain ⟨hl7a, hl7b⟩ := log_atanh_neg_step (p := 7) (M := 8) (t := (1 / 15)) (lo := 1.945908) (hi := 1.9459107) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM7.1 hM7.2 (by norm_num) (by norm_num)
  refine ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 12) (a2 := 2) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 11) (M := 12) (t := (1 / 23)) (lo := 2.3978948) (hi := 2.397896) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 12) (a2 := 2) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 13) (M := 12) (t := 0.04) (lo := 2.5649491) (hi := 2.5649502) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 16) (a2 := 4) (b3 := 0) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 17) (M := 16) (t := (1 / 33)) (lo := 2.8332133) (hi := 2.8332134) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 18) (a2 := 1) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 19) (M := 18) (t := (1 / 37)) (lo := 2.9444385) (hi := 2.9444403) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 24) (a2 := 3) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 23) (M := 24) (t := (1 / 47)) (lo := 3.135494) (hi := 3.1354949) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 30) (a2 := 1) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 29) (M := 30) (t := (1 / 59)) (lo := 3.3672956) (hi := 3.3672966) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 32) (a2 := 5) (b3 := 0) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 31) (M := 32) (t := (1 / 63)) (lo := 3.4339872) (hi := 3.4339873) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 36) (a2 := 2) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 37) (M := 36) (t := (1 / 73)) (lo := 3.6109175) (hi := 3.6109192) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 40) (a2 := 3) (b3 := 0) (c5 := 1) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 41) (M := 40) (t := (1 / 81)) (lo := 3.713572) (hi := 3.7135722) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 42) (a2 := 1) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 43) (M := 42) (t := (1 / 85)) (lo := 3.7611977) (hi := 3.7612013) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 48) (a2 := 4) (b3 := 1) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 47) (M := 48) (t := (1 / 95)) (lo := 3.8501474) (hi := 3.8501483) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 54) (a2 := 1) (b3 := 3) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 53) (M := 54) (t := (1 / 107)) (lo := 3.9702913) (hi := 3.9702938) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 60) (a2 := 2) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 59) (M := 60) (t := (1 / 119)) (lo := 4.0775372) (hi := 4.0775382) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 60) (a2 := 2) (b3 := 1) (c5 := 1) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 61) (M := 60) (t := (1 / 121)) (lo := 4.1108736) (hi := 4.1108746) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 64) (a2 := 6) (b3 := 0) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 67) (M := 64) (t := (3 / 131)) (lo := 4.2046926) (hi := 4.2046927) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 72) (a2 := 3) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 71) (M := 72) (t := (1 / 143)) (lo := 4.2626794) (hi := 4.2626812) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 72) (a2 := 3) (b3 := 2) (c5 := 0) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_pos_step (p := 73) (M := 72) (t := (1 / 145)) (lo := 4.290459) (hi := 4.2904607) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 80) (a2 := 4) (b3 := 0) (c5 := 1) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 79) (M := 80) (t := (1 / 159)) (lo := 4.3694478) (hi := 4.369448) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 84) (a2 := 2) (b3 := 1) (c5 := 0) (d7 := 1) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 83) (M := 84) (t := (1 / 167)) (lo := 4.4188382) (hi := 4.4188418) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)
  · obtain ⟨hM_lo, hM_hi⟩ := log_smooth_bounds (M := 90) (a2 := 1) (b3 := 2) (c5 := 1) (d7 := 0) (by norm_num) hl3a hl3b hl5a hl5b hl7a hl7b; exact log_atanh_neg_step (p := 89) (M := 90) (t := (1 / 179)) (lo := 4.4886359) (hi := 4.4886377) (kp := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hM_lo hM_hi (by norm_num) (by norm_num)

private theorem hasDerivAt_sin_sub_mul_cos' (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin y - y * Real.cos y) (x * Real.sin x) x := by
  refine ((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv ?_
  dsimp only [id]; ring

private theorem monotoneOn_sin_sub_mul_cos' :
    MonotoneOn (fun u : ℝ => Real.sin u - u * Real.cos u) (Icc 0 Real.pi) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi)
    (fun x _ => (hasDerivAt_sin_sub_mul_cos' x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_sin_sub_mul_cos' x).hasDerivWithinAt)
    fun x hx => by
      have hx' : x ∈ Ioo 0 Real.pi := by rwa [interior_Icc] at hx
      exact mul_nonneg hx'.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hx'.1.le hx'.2.le)

private theorem bohmanP9_le_and_le_bohmanP11' {u : ℝ} (hu : 0 ≤ u) :
    bohmanP9 u ≤ Real.sin u - u * Real.cos u ∧ Real.sin u - u * Real.cos u ≤ bohmanP11 u := by
  have hd9 : ∀ x : ℝ, HasDerivAt bohmanP9
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)) x := fun x => by
    unfold bohmanP9
    refine ((((hasDerivAt_monomial_div' 3 3 x).sub
        (hasDerivAt_monomial_div' 5 30 x)).add
        (hasDerivAt_monomial_div' 7 840 x)).sub
        (hasDerivAt_monomial_div' 9 45360 x)).congr_deriv (by norm_num; ring)
  have hd11 : ∀ x : ℝ, HasDerivAt bohmanP11
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880)) x := fun x => by
    unfold bohmanP11
    refine ((hd9 x).add (hasDerivAt_monomial_div' 11 3991680 x)).congr_deriv (by norm_num; ring)
  have hlo := nonneg_of_deriv_nonneg' (by simp [bohmanP9])
    (fun x => ((hasDerivAt_sin_sub_mul_cos' x).sub (hd9 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_cos_taylor_chain hx).1)) hu
  have hhi := nonneg_of_deriv_nonneg' (by simp [bohmanP11, bohmanP9])
    (fun x => ((hd11 x).sub (hasDerivAt_sin_sub_mul_cos' x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_cos_taylor_chain hx).2.1)) hu
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

private theorem bohmanFn_eq_sin_sub_mul_cos' {L x : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    bohmanFn L x =
      (Real.sin (Real.pi * (1 - x / L)) -
        Real.pi * (1 - x / L) * Real.cos (Real.pi * (1 - x / L))) / Real.pi := by
  rw [bohmanFn_of_nonneg_of_le hL hx0 hxL]
  set u : ℝ := Real.pi * (1 - x / L)
  have hu_eq : Real.pi * x / L = Real.pi - u := by dsimp only [u]; ring
  have h1x : 1 - x / L = u / Real.pi := by
    have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
    dsimp only [u]; field_simp [hπ]
  rw [hu_eq, h1x, Real.cos_pi_sub, Real.sin_pi_sub]
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hπ]; ring

private theorem bohman_coeff_bounds' {p pk k lp_lo lp_hi u_lo u_hi c_lo c_hi : ℝ}
    (hpk : 0 < pk) (hk : 0 < k) (hlp0 : 0 ≤ lp_lo)
    (hlp_lo : lp_lo ≤ Real.log p) (hlp_hi : Real.log p ≤ lp_hi)
    (hk_hi : k * lp_hi ≤ 9 / 2) (hu_lo0 : 0 ≤ u_lo)
    (hu_lo : u_lo ≤ 3.1415926535 * (1 - k * lp_hi / (9 / 2)))
    (hu_hi : 3.1415926536 * (1 - k * lp_lo / (9 / 2)) ≤ u_hi)
    (hu_hi_pi : u_hi ≤ 3.1415926535)
    (h_clo : c_lo ≤ lp_lo / pk * (bohmanP9 u_lo / 3.1415926536))
    (h_chi : lp_hi / pk * (bohmanP11 u_hi / 3.1415926535) ≤ c_hi) :
    c_lo ≤ Real.log p / pk * bohmanFn (9 / 2) (k * Real.log p) ∧
      Real.log p / pk * bohmanFn (9 / 2) (k * Real.log p) ≤ c_hi := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10'
  have hπ_pos := Real.pi_pos
  have hlp_nonneg : 0 ≤ Real.log p := hlp0.trans hlp_lo
  have hkx0 : 0 ≤ k * Real.log p := mul_nonneg hk.le hlp_nonneg
  have hkxL : k * Real.log p ≤ 9 / 2 := (mul_le_mul_of_nonneg_left hlp_hi hk.le).trans hk_hi
  set u : ℝ := Real.pi * (1 - k * Real.log p / (9 / 2))
  have h1_lo : 0 ≤ 1 - k * lp_hi / (9 / 2) := by linarith
  have h1_le : 1 - k * lp_hi / (9 / 2) ≤ 1 - k * Real.log p / (9 / 2) := by
    have := mul_le_mul_of_nonneg_left hlp_hi hk.le; linarith
  have h1_ge : 1 - k * Real.log p / (9 / 2) ≤ 1 - k * lp_lo / (9 / 2) := by
    have := mul_le_mul_of_nonneg_left hlp_lo hk.le; linarith
  have hu_ge_lo : u_lo ≤ u := hu_lo.trans (mul_le_mul hπ_lo.le h1_le h1_lo hπ_pos.le)
  have hu_le_hi : u ≤ u_hi :=
    (mul_le_mul hπ_hi.le h1_ge (by linarith) (by norm_num)).trans hu_hi
  have hu0 : 0 ≤ u := hu_lo0.trans hu_ge_lo
  have hu_hi_lt_pi : u_hi ≤ Real.pi := hu_hi_pi.trans hπ_lo.le
  have hu_pi : u ≤ Real.pi := hu_le_hi.trans hu_hi_lt_pi
  have hH_lo : bohmanP9 u_lo ≤ Real.sin u - u * Real.cos u :=
    (bohmanP9_le_and_le_bohmanP11' hu_lo0).1.trans
      (monotoneOn_sin_sub_mul_cos' ⟨hu_lo0, hu_ge_lo.trans hu_pi⟩ ⟨hu0, hu_pi⟩ hu_ge_lo)
  have hH_hi : Real.sin u - u * Real.cos u ≤ bohmanP11 u_hi :=
    (monotoneOn_sin_sub_mul_cos' ⟨hu0, hu_pi⟩ ⟨hu_lo0.trans (hu_ge_lo.trans hu_le_hi), hu_hi_lt_pi⟩
      hu_le_hi).trans (bohmanP9_le_and_le_bohmanP11' (hu_lo0.trans (hu_ge_lo.trans hu_le_hi))).2
  have hW_eq := bohmanFn_eq_sin_sub_mul_cos' (L := 9 / 2) (x := k * Real.log p) (by norm_num) hkx0 hkxL
  have hW_nonneg : 0 ≤ bohmanFn (9 / 2) (k * Real.log p) := bohmanFn_nonneg (by norm_num) _
  have hW_lo : bohmanP9 u_lo / 3.1415926536 ≤ bohmanFn (9 / 2) (k * Real.log p) := by
    rw [hW_eq]
    by_cases hp9 : 0 ≤ bohmanP9 u_lo
    · exact (div_le_div_of_nonneg_left hp9 hπ_pos hπ_hi.le).trans
        (div_le_div_of_nonneg_right hH_lo hπ_pos.le)
    · exact (div_nonpos_of_nonpos_of_nonneg (not_le.mp hp9).le (by norm_num)).trans
        (by rw [← hW_eq]; exact hW_nonneg)
  have hW_hi : bohmanFn (9 / 2) (k * Real.log p) ≤ bohmanP11 u_hi / 3.1415926535 := by
    rw [hW_eq]
    have hH0 : 0 ≤ Real.sin u - u * Real.cos u := by
      have := mul_nonneg hW_nonneg hπ_pos.le
      rw [hW_eq, div_mul_cancel₀ _ hπ_pos.ne'] at this; exact this
    exact (div_le_div_of_nonneg_right hH_hi hπ_pos.le).trans
      (div_le_div_of_nonneg_left (hH0.trans hH_hi) (by norm_num) hπ_lo.le)
  refine ⟨h_clo.trans ?_, ?_⟩
  · by_cases hw0 : 0 ≤ bohmanP9 u_lo / 3.1415926536
    · exact mul_le_mul (div_le_div_of_nonneg_right hlp_lo hpk.le) hW_lo hw0
        (div_nonneg hlp_nonneg hpk.le)
    · exact (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hlp0 hpk.le) (not_le.mp hw0).le).trans
        (mul_nonneg (div_nonneg hlp_nonneg hpk.le) hW_nonneg)
  · exact (mul_le_mul (div_le_div_of_nonneg_right hlp_hi hpk.le) hW_hi hW_nonneg
      (div_nonneg (hlp_nonneg.trans hlp_hi) hpk.le)).trans h_chi

private theorem all_prime_bohman_coeff_bounds' :
    (0.3096269 ≤ Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) ∧ Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) ≤ 0.3109196) ∧
    (0.1133596 ≤ Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) ∧ Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) ≤ 0.1134315) ∧
    (0.0329179 ≤ Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) ∧ Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) ≤ 0.0329207) ∧
    (0.0069486 ≤ Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) ∧ Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) ≤ 0.0069489) ∧
    (0.0008209 ≤ Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) ∧ Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) ≤ 0.0008210) ∧
    (0.0000154 ≤ Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) ∧ Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) ≤ 0.0000155) ∧
    (0.2797659 ≤ Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) ∧ Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) ≤ 0.2802868) ∧
    (0.0411017 ≤ Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) ∧ Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) ≤ 0.0411443) ∧
    (0.0023832 ≤ Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) ∧ Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) ≤ 0.0023895) ∧
    (0.0000005 ≤ Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) ∧ Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) ≤ 0.0000006) ∧
    (0.1816415 ≤ Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) ∧ Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) ≤ 0.1818962) ∧
    (0.0044971 ≤ Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) ∧ Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) ≤ 0.0045154) ∧
    (0.1196666 ≤ Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) ∧ Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) ≤ 0.1198266) ∧
    (0.0003159 ≤ Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) ∧ Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) ≤ 0.0003188) ∧
    (0.0585011 ≤ Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) ∧ Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) ≤ 0.0585794) ∧
    (0.0427132 ≤ Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) ∧ Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) ≤ 0.0428245) ∧
    (0.0242427 ≤ Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) ∧ Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) ≤ 0.0242863) ∧
    (0.0186189 ≤ Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) ∧ Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) ≤ 0.0187489) ∧
    (0.0113990 ≤ Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) ∧ Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) ≤ 0.0114201) ∧
    (0.0056981 ≤ Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) ∧ Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) ≤ 0.0057307) ∧
    (0.0045777 ≤ Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) ∧ Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) ≤ 0.0045883) ∧
    (0.0023761 ≤ Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) ∧ Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) ≤ 0.0023836) ∧
    (0.0015372 ≤ Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) ∧ Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) ≤ 0.0015452) ∧
    (0.0012316 ≤ Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) ∧ Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) ≤ 0.0012449) ∧
    (0.0007923 ≤ Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) ∧ Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) ≤ 0.0008002) ∧
    (0.0003936 ≤ Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) ∧ Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) ≤ 0.0003977) ∧
    (0.0001846 ≤ Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) ∧ Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) ≤ 0.0001869) ∧
    (0.0001420 ≤ Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) ∧ Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) ≤ 0.0001440) ∧
    (0.0000578 ≤ Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) ∧ Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) ≤ 0.0000588) ∧
    (0.0000288 ≤ Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) ∧ Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) ≤ 0.0000294) ∧
    (0.0000193 ≤ Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) ∧ Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) ≤ 0.0000197) ∧
    (0.0000043 ≤ Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) ∧ Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) ≤ 0.0000045) ∧
    (0.0000009 ≤ Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) ∧ Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) ≤ 0.0000011) ∧
    (0.0000000 ≤ Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) ∧ Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) ≤ 0.0000001) := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, ⟨hl47a, hl47b⟩, ⟨hl53a, hl53b⟩, ⟨hl59a, hl59b⟩, ⟨hl61a, hl61b⟩, ⟨hl67a, hl67b⟩, ⟨hl71a, hl71b⟩, ⟨hl73a, hl73b⟩, ⟨hl79a, hl79b⟩, ⟨hl83a, hl83b⟩, ⟨hl89a, hl89b⟩⟩ := sharp_log_prime_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bohman_coeff_bounds' (u_lo := 2.65768) (u_hi := 2.65769) (by norm_num) (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 2.17377) (u_hi := 2.17378) (by norm_num) (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.68986) (u_hi := 1.68987) (by norm_num) (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.20596) (u_hi := 1.20597) (by norm_num) (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.72205) (u_hi := 0.72206) (by norm_num) (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.23814) (u_hi := 0.23815) (by norm_num) (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 2.37442) (u_hi := 2.37465) (by norm_num) (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.60724) (u_hi := 1.60770) (by norm_num) (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.84007) (u_hi := 0.84075) (by norm_num) (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.07290) (u_hi := 0.07381) (by norm_num) (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 2.01767) (u_hi := 2.01824) (by norm_num) (by norm_num) (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.89376) (u_hi := 0.89488) (by norm_num) (by norm_num) (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.78292) (u_hi := 1.78353) (by norm_num) (by norm_num) (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.42426) (u_hi := 0.42547) (by norm_num) (by norm_num) (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.46752) (u_hi := 1.46809) (by norm_num) (by norm_num) (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.35010) (u_hi := 1.35114) (by norm_num) (by norm_num) (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.16326) (u_hi := 1.16389) (by norm_num) (by norm_num) (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 1.08498) (u_hi := 1.08728) (by norm_num) (by norm_num) (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.95248) (u_hi := 0.95302) (by norm_num) (by norm_num) (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.78979) (u_hi := 0.79119) (by norm_num) (by norm_num) (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.74404) (u_hi := 0.74457) (by norm_num) (by norm_num) (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.62017) (u_hi := 0.62078) (by norm_num) (by norm_num) (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.54834) (u_hi := 0.54924) (by norm_num) (by norm_num) (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.51466) (u_hi := 0.51640) (by norm_num) (by norm_num) (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.45321) (u_hi := 0.45464) (by norm_num) (by norm_num) (by norm_num) hl47a hl47b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.36892) (u_hi := 0.37013) (by norm_num) (by norm_num) (by norm_num) hl53a hl53b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.29397) (u_hi := 0.29508) (by norm_num) (by norm_num) (by norm_num) hl59a hl59b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.27151) (u_hi := 0.27272) (by norm_num) (by norm_num) (by norm_num) hl61a hl61b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.20587) (u_hi := 0.20693) (by norm_num) (by norm_num) (by norm_num) hl67a hl67b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.16555) (u_hi := 0.16646) (by norm_num) (by norm_num) (by norm_num) hl71a hl71b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.14596) (u_hi := 0.14661) (by norm_num) (by norm_num) (by norm_num) hl73a hl73b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.09086) (u_hi := 0.09152) (by norm_num) (by norm_num) (by norm_num) hl79a hl79b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.05504) (u_hi := 0.05669) (by norm_num) (by norm_num) (by norm_num) hl83a hl83b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds' (u_lo := 0.00770) (u_hi := 0.00893) (by norm_num) (by norm_num) (by norm_num) hl89a hl89b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)

private theorem cos_chebyshev_six' (θ : ℝ) :
    let u := Real.cos θ
    Real.cos (2 * θ) = 2 * u ^ 2 - 1 ∧
      Real.cos (3 * θ) = 4 * u ^ 3 - 3 * u ∧
      Real.cos (4 * θ) = 8 * u ^ 4 - 8 * u ^ 2 + 1 ∧
      Real.cos (5 * θ) = 16 * u ^ 5 - 20 * u ^ 3 + 5 * u ∧
      Real.cos (6 * θ) = 32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 1 := by
  dsimp only
  have h2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have h3 : Real.cos (3 * θ) = 4 * Real.cos θ ^ 3 - 3 * Real.cos θ := Real.cos_three_mul θ
  have hrec : ∀ k : ℝ, Real.cos ((k + 1) * θ) =
      2 * Real.cos θ * Real.cos (k * θ) - Real.cos ((k - 1) * θ) := fun k => by
    have ha := Real.cos_add (k * θ) θ
    have hs := Real.cos_sub (k * θ) θ
    rw [show k * θ + θ = (k + 1) * θ by ring] at ha
    rw [show k * θ - θ = (k - 1) * θ by ring] at hs
    linarith only [ha, hs]
  have h4 : Real.cos (4 * θ) = 8 * Real.cos θ ^ 4 - 8 * Real.cos θ ^ 2 + 1 := by
    have hr := hrec 3; norm_num at hr; rw [hr, h3, h2]; ring
  have h5 : Real.cos (5 * θ) = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by
    have hr := hrec 4; norm_num at hr; rw [hr, h4, h3]; ring
  have h6 : Real.cos (6 * θ) = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by
    have hr := hrec 5; norm_num at hr; rw [hr, h5, h4]; ring
  exact ⟨h2, h3, h4, h5, h6⟩

private def bohmanTerm2 (θ : ℝ) : ℝ :=
  Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) * Real.cos θ +
    Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) * Real.cos (2 * θ) +
    Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) * Real.cos (3 * θ) +
    Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) * Real.cos (4 * θ) +
    Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) * Real.cos (5 * θ) +
    Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) * Real.cos (6 * θ)

private def bohmanTerm3 (θ : ℝ) : ℝ :=
  Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) * Real.cos θ +
    Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) * Real.cos (2 * θ) +
    Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) * Real.cos (3 * θ) +
    Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) * Real.cos (4 * θ)

private def bohmanTerm5 (θ : ℝ) : ℝ :=
  Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) * Real.cos θ +
    Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) * Real.cos (2 * θ)

private def bohmanTerm7 (θ : ℝ) : ℝ :=
  Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) * Real.cos θ +
    Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) * Real.cos (2 * θ)

/-- Nonnegative excess of each prime `p ≤ 47` above its phase-free `θ = π` rational floor. -/
def bohmanExcess (p : ℕ) (θ : ℝ) : ℝ :=
  if p = 2 then bohmanTerm2 θ - (-0.3109196 + 0.1133596 - 0.0329207 + 0.0069486 - 0.0008210 + 0.0000154)
  else if p = 3 then bohmanTerm3 θ - (-0.2802868 + 0.0411017 - 0.0023895 + 0.0000005)
  else if p = 5 then bohmanTerm5 θ - (-0.1818962 + 0.0044971)
  else if p = 7 then bohmanTerm7 θ - (-0.1198266 + 0.0003159)
  else if p = 11 then Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) * Real.cos θ + 0.0585794
  else if p = 13 then Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) * Real.cos θ + 0.0428245
  else if p = 17 then Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) * Real.cos θ + 0.0242863
  else if p = 19 then Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) * Real.cos θ + 0.0187489
  else if p = 23 then Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) * Real.cos θ + 0.0114201
  else if p = 29 then Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) * Real.cos θ + 0.0057307
  else if p = 31 then Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) * Real.cos θ + 0.0045883
  else if p = 37 then Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) * Real.cos θ + 0.0023836
  else if p = 41 then Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) * Real.cos θ + 0.0015452
  else if p = 43 then Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) * Real.cos θ + 0.0012449
  else if p = 47 then Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) * Real.cos θ + 0.0008002
  else 0

private theorem neg_ub_le_mul_cos' {c ub θ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ ub) :
    -ub ≤ c * Real.cos θ := by
  have := Real.neg_one_le_cos θ; nlinarith only [this, hc0, hc]

/-- **Master phase-excess decomposition of `bohmanPhaseForm`.** -/
theorem bohmanPhaseForm_ge_sum_excess (θ : ℕ → ℝ) :
    -(0.935816 : ℝ) +
      (bohmanExcess 2 (θ 2) + bohmanExcess 3 (θ 3) + bohmanExcess 5 (θ 5) + bohmanExcess 7 (θ 7) +
        bohmanExcess 11 (θ 11) + bohmanExcess 13 (θ 13) + bohmanExcess 17 (θ 17) +
        bohmanExcess 19 (θ 19) + bohmanExcess 23 (θ 23) + bohmanExcess 29 (θ 29) +
        bohmanExcess 31 (θ 31) + bohmanExcess 37 (θ 37) + bohmanExcess 41 (θ 41) +
        bohmanExcess 43 (θ 43) + bohmanExcess 47 (θ 47)) ≤ bohmanPhaseForm θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -,
    ⟨b53l, b53u⟩, ⟨b59l, b59u⟩, ⟨b61l, b61u⟩, ⟨b67l, b67u⟩, ⟨b71l, b71u⟩,
    ⟨b73l, b73u⟩, ⟨b79l, b79u⟩, ⟨b83l, b83u⟩, ⟨b89l, b89u⟩⟩ := all_prime_bohman_coeff_bounds'
  have s53 := neg_ub_le_mul_cos' (θ := θ 53) (by linarith only [b53l]) b53u
  have s59 := neg_ub_le_mul_cos' (θ := θ 59) (by linarith only [b59l]) b59u
  have s61 := neg_ub_le_mul_cos' (θ := θ 61) (by linarith only [b61l]) b61u
  have s67 := neg_ub_le_mul_cos' (θ := θ 67) (by linarith only [b67l]) b67u
  have s71 := neg_ub_le_mul_cos' (θ := θ 71) (by linarith only [b71l]) b71u
  have s73 := neg_ub_le_mul_cos' (θ := θ 73) (by linarith only [b73l]) b73u
  have s79 := neg_ub_le_mul_cos' (θ := θ 79) (by linarith only [b79l]) b79u
  have s83 := neg_ub_le_mul_cos' (θ := θ 83) (by linarith only [b83l]) b83u
  have s89 := neg_ub_le_mul_cos' (θ := θ 89) (by linarith only [b89l]) b89u
  unfold bohmanPhaseForm bohmanExcess bohmanTerm2 bohmanTerm3 bohmanTerm5 bohmanTerm7
  simp only [↓reduceIte, Nat.reduceEqDiff]
  linarith only [s53, s59, s61, s67, s71, s73, s79, s83, s89]

private theorem monotoneOn_bohman2 :
    MonotoneOn (chebPoly6
      (Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2))
      (Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2))
      (Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2))
      (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
      (Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2))
      (Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2))) (Icc (-1) 1) := by
  obtain ⟨⟨b2_1l, -⟩, ⟨b2_2l, b2_2u⟩, ⟨b2_3l, b2_3u⟩, ⟨b2_4l, b2_4u⟩, ⟨b2_5l, b2_5u⟩,
    ⟨b2_6l, b2_6u⟩, -⟩ := all_prime_bohman_coeff_bounds'
  refine monotoneOn_chebPoly6_of_sos (E_hi := 0.0008210) (G_hi := 0.0000155)
    (by linarith only [b2_4l]) (by linarith only [b2_5l]) b2_5u
    (by linarith only [b2_6l]) b2_6u (by linarith only [b2_3l, b2_4u]) ?_
  set q1 := 4 * (Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2)) -
    16 * (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
  set q2 := 12 * (Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2)) -
    32 * (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
  set q0 := Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) -
    3 * (Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2)) -
    (25 / 4) * 0.0008210 - 228 * 0.0000155
  have hq1_0 : 0 ≤ q1 := by dsimp only [q1]; linarith only [b2_2l, b2_4u]
  have hq1_hi : q1 ≤ 0.34255 := by dsimp only [q1]; linarith only [b2_2u, b2_4l]
  have hq2_lo : (0.17265 : ℝ) ≤ q2 := by dsimp only [q2]; linarith only [b2_3l, b2_4u]
  have hq0_lo : (0.20219 : ℝ) ≤ q0 := by dsimp only [q0]; linarith only [b2_1l, b2_3u]
  have hsq := pow_le_pow_left₀ hq1_0 hq1_hi 2
  have hm := mul_le_mul hq2_lo hq0_lo (by norm_num) (by linarith only [hq2_lo])
  norm_num at hsq hm ⊢
  linarith only [hsq, hm]

private theorem monotoneOn_bohman3 :
    MonotoneOn (chebPoly6
      (Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3))
      (Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3))
      (Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3))
      (Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3)) 0 0) (Icc (-1) 1) := by
  obtain ⟨-, -, -, -, -, -, ⟨b3_1l, -⟩, ⟨b3_2l, b3_2u⟩, ⟨b3_3l, b3_3u⟩, ⟨b3_4l, b3_4u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  exact monotoneOn_chebPoly4_of_linear (by linarith only [b3_2l]) (by linarith only [b3_3l])
    (by linarith only [b3_4l]) (by linarith only [b3_1l, b3_2u, b3_3u, b3_4u])

private theorem monotoneOn_bohman5 :
    MonotoneOn (chebPoly6
      (Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5))
      (Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5)) 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨b5_1l, -⟩, ⟨b5_2l, b5_2u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  exact monotoneOn_chebPoly4_of_linear (by linarith only [b5_2l]) le_rfl le_rfl
    (by linarith only [b5_1l, b5_2u])

private theorem monotoneOn_bohman7 :
    MonotoneOn (chebPoly6
      (Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7))
      (Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7)) 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨b7_1l, -⟩, ⟨b7_2l, b7_2u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  exact monotoneOn_chebPoly4_of_linear (by linarith only [b7_2l]) le_rfl le_rfl
    (by linarith only [b7_1l, b7_2u])

private theorem bohmanExcess2_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.3096269 * max u_lo 0 + 0.3109196 * min u_lo 0) +
      (0.1133596 * max (2 * u_lo ^ 2 - 1) 0 + 0.1134315 * min (2 * u_lo ^ 2 - 1) 0) +
      (0.0329179 * max (4 * u_lo ^ 3 - 3 * u_lo) 0 + 0.0329207 * min (4 * u_lo ^ 3 - 3 * u_lo) 0) +
      (0.0069486 * max (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0 +
        0.0069489 * min (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0) +
      (0.0008209 * max (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo) 0 +
        0.0008210 * min (16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo) 0) +
      (0.0000154 * max (32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1) 0 +
        0.0000155 * min (32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1) 0) -
      (-0.3109196 + 0.1133596 - 0.0329207 + 0.0069486 - 0.0008210 + 0.0000154)) :
    g ≤ bohmanExcess 2 θ := by
  obtain ⟨⟨b1l, b1u⟩, ⟨b2l, b2u⟩, ⟨b3l, b3u⟩, ⟨b4l, b4u⟩, ⟨b5l, b5u⟩, ⟨b6l, b6u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  obtain ⟨c2, c3, c4, c5, c6⟩ := cos_chebyshev_six' θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman2 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly6
      (Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2))
      (Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2))
      (Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2))
      (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
      (Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2))
      (Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2)) (Real.cos θ) = bohmanTerm2 θ := by
    unfold chebPoly6 bohmanTerm2; rw [c2, c3, c4, c5, c6]
  rw [hterm] at hmono
  unfold chebPoly6 at hmono
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  have w3 := weighted_sign_lb b3l b3u (t := 4 * u_lo ^ 3 - 3 * u_lo)
  have w4 := weighted_sign_lb b4l b4u (t := 8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1)
  have w5 := weighted_sign_lb b5l b5u (t := 16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo)
  have w6 := weighted_sign_lb b6l b6u (t := 32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1)
  unfold bohmanExcess; simp only [↓reduceIte]
  linarith only [hg, w1, w2, w3, w4, w5, w6, hmono]

private theorem bohmanExcess3_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.2797659 * max u_lo 0 + 0.2802868 * min u_lo 0) +
      (0.0411017 * max (2 * u_lo ^ 2 - 1) 0 + 0.0411443 * min (2 * u_lo ^ 2 - 1) 0) +
      (0.0023832 * max (4 * u_lo ^ 3 - 3 * u_lo) 0 + 0.0023895 * min (4 * u_lo ^ 3 - 3 * u_lo) 0) +
      (0.0000005 * max (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0 +
        0.0000006 * min (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0) -
      (-0.2802868 + 0.0411017 - 0.0023895 + 0.0000005)) :
    g ≤ bohmanExcess 3 θ := by
  obtain ⟨-, -, -, -, -, -, ⟨b1l, b1u⟩, ⟨b2l, b2u⟩, ⟨b3l, b3u⟩, ⟨b4l, b4u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  obtain ⟨c2, c3, c4, -, -⟩ := cos_chebyshev_six' θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman3 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly6
      (Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3))
      (Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3))
      (Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3))
      (Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3)) 0 0 (Real.cos θ) = bohmanTerm3 θ := by
    unfold chebPoly6 bohmanTerm3; rw [c2, c3, c4]; ring
  rw [hterm] at hmono
  unfold chebPoly6 at hmono
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  have w3 := weighted_sign_lb b3l b3u (t := 4 * u_lo ^ 3 - 3 * u_lo)
  have w4 := weighted_sign_lb b4l b4u (t := 8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1)
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  linarith only [hg, w1, w2, w3, w4, hmono]

private theorem bohmanExcess5_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.1816415 * max u_lo 0 + 0.1818962 * min u_lo 0) +
      (0.0044971 * max (2 * u_lo ^ 2 - 1) 0 + 0.0045154 * min (2 * u_lo ^ 2 - 1) 0) -
      (-0.1818962 + 0.0044971)) :
    g ≤ bohmanExcess 5 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨b1l, b1u⟩, ⟨b2l, b2u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  have c2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman5 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly6
      (Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5))
      (Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5)) 0 0 0 0 (Real.cos θ) = bohmanTerm5 θ := by
    unfold chebPoly6 bohmanTerm5; rw [c2]; ring
  rw [hterm] at hmono
  unfold chebPoly6 at hmono
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  linarith only [hg, w1, w2, hmono]

private theorem bohmanExcess7_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.1196666 * max u_lo 0 + 0.1198266 * min u_lo 0) +
      (0.0003159 * max (2 * u_lo ^ 2 - 1) 0 + 0.0003188 * min (2 * u_lo ^ 2 - 1) 0) -
      (-0.1198266 + 0.0003159)) :
    g ≤ bohmanExcess 7 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨b1l, b1u⟩, ⟨b2l, b2u⟩, -⟩ :=
    all_prime_bohman_coeff_bounds'
  have c2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman7 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly6
      (Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7))
      (Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7)) 0 0 0 0 (Real.cos θ) = bohmanTerm7 θ := by
    unfold chebPoly6 bohmanTerm7; rw [c2]; ring
  rw [hterm] at hmono
  unfold chebPoly6 at hmono
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  linarith only [hg, w1, w2, hmono]

private theorem linear_excess_ge {c c_lo c_hi u_lo g θ : ℝ}
    (hclo0 : 0 ≤ c_lo) (hlo : c_lo ≤ c) (hhi : c ≤ c_hi)
    (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ) (hg : g ≤ c_lo * (1 + u_lo)) :
    g ≤ c * Real.cos θ + c_hi := by
  have h1 : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have h2 : c_lo * (1 + Real.cos θ) ≤ c * Real.cos θ + c_hi := by
    have : c * Real.cos θ + c_hi - c_lo * (1 + Real.cos θ) =
        (c - c_lo) * (1 + Real.cos θ) + (c_hi - c) := by ring
    nlinarith only [this, hlo, hhi, h1]
  have h3 : c_lo * (1 + u_lo) ≤ c_lo * (1 + Real.cos θ) :=
    mul_le_mul_of_nonneg_left (by linarith only [hu]) hclo0
  exact hg.trans (h3.trans h2)

private theorem bohmanExcess11_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0585011 * (1 + u_lo)) : g ≤ bohmanExcess 11 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess13_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0427132 * (1 + u_lo)) : g ≤ bohmanExcess 13 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess17_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0242427 * (1 + u_lo)) : g ≤ bohmanExcess 17 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess19_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0186189 * (1 + u_lo)) : g ≤ bohmanExcess 19 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess23_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0113990 * (1 + u_lo)) : g ≤ bohmanExcess 23 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess29_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0056981 * (1 + u_lo)) : g ≤ bohmanExcess 29 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess31_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0045777 * (1 + u_lo)) : g ≤ bohmanExcess 31 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess37_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0023761 * (1 + u_lo)) : g ≤ bohmanExcess 37 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess41_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0015372 * (1 + u_lo)) : g ≤ bohmanExcess 41 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess43_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0012316 * (1 + u_lo)) : g ≤ bohmanExcess 43 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess47_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0007923 * (1 + u_lo)) : g ≤ bohmanExcess 47 θ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨bl, bu⟩, -⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess_all_nonneg (θ : ℕ → ℝ) :
    0 ≤ bohmanExcess 2 (θ 2) ∧ 0 ≤ bohmanExcess 3 (θ 3) ∧ 0 ≤ bohmanExcess 5 (θ 5) ∧ 0 ≤ bohmanExcess 7 (θ 7) ∧ 0 ≤ bohmanExcess 11 (θ 11) ∧ 0 ≤ bohmanExcess 13 (θ 13) ∧ 0 ≤ bohmanExcess 17 (θ 17) ∧ 0 ≤ bohmanExcess 19 (θ 19) ∧ 0 ≤ bohmanExcess 23 (θ 23) ∧ 0 ≤ bohmanExcess 29 (θ 29) ∧ 0 ≤ bohmanExcess 31 (θ 31) ∧ 0 ≤ bohmanExcess 37 (θ 37) ∧ 0 ≤ bohmanExcess 41 (θ 41) ∧ 0 ≤ bohmanExcess 43 (θ 43) ∧ 0 ≤ bohmanExcess 47 (θ 47) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bohmanExcess2_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess3_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess5_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess7_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess11_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess13_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess17_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess19_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess23_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess29_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess31_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess37_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess41_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess43_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)
  · exact bohmanExcess47_ge (u_lo := -1) le_rfl (Real.neg_one_le_cos _) (by norm_num)

private theorem bohmanPhaseForm_coupled_ge_sum_excess (γ : ℝ) :
    -(0.935816 : ℝ) + (bohmanExcess 2 (γ * Real.log 2) + bohmanExcess 3 (γ * Real.log 3) + bohmanExcess 5 (γ * Real.log 5) + bohmanExcess 7 (γ * Real.log 7) + bohmanExcess 11 (γ * Real.log 11) + bohmanExcess 13 (γ * Real.log 13) + bohmanExcess 17 (γ * Real.log 17) + bohmanExcess 19 (γ * Real.log 19) + bohmanExcess 23 (γ * Real.log 23) + bohmanExcess 29 (γ * Real.log 29) + bohmanExcess 31 (γ * Real.log 31) + bohmanExcess 37 (γ * Real.log 37) + bohmanExcess 41 (γ * Real.log 41) + bohmanExcess 43 (γ * Real.log 43) + bohmanExcess 47 (γ * Real.log 47)) ≤
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) := by
  simpa only [Nat.cast_ofNat] using bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))

private theorem bohmanExcess_coupled_all_nonneg (γ : ℝ) :
    0 ≤ bohmanExcess 2 (γ * Real.log 2) ∧ 0 ≤ bohmanExcess 3 (γ * Real.log 3) ∧ 0 ≤ bohmanExcess 5 (γ * Real.log 5) ∧ 0 ≤ bohmanExcess 7 (γ * Real.log 7) ∧ 0 ≤ bohmanExcess 11 (γ * Real.log 11) ∧ 0 ≤ bohmanExcess 13 (γ * Real.log 13) ∧ 0 ≤ bohmanExcess 17 (γ * Real.log 17) ∧ 0 ≤ bohmanExcess 19 (γ * Real.log 19) ∧ 0 ≤ bohmanExcess 23 (γ * Real.log 23) ∧ 0 ≤ bohmanExcess 29 (γ * Real.log 29) ∧ 0 ≤ bohmanExcess 31 (γ * Real.log 31) ∧ 0 ≤ bohmanExcess 37 (γ * Real.log 37) ∧ 0 ≤ bohmanExcess 41 (γ * Real.log 41) ∧ 0 ≤ bohmanExcess 43 (γ * Real.log 43) ∧ 0 ≤ bohmanExcess 47 (γ * Real.log 47) := by
  simpa only [Nat.cast_ofNat] using bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))


private theorem exp_nine_bounds' : (89 : ℝ) ^ 2 ≤ Real.exp 9 ∧ Real.exp 9 ≤ (91 : ℝ) ^ 2 := by
  have he9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he9]
  exact ⟨(by norm_num : (89 : ℝ) ^ 2 ≤ 2.7182818283 ^ 9).trans
      (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 9),
    (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 9).trans (by norm_num)⟩

private theorem nine_halves_le_log' {n : ℕ} (hn : 91 ≤ n) : (9 / 2 : ℝ) ≤ Real.log n := by
  have hn' : (91 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn']
  rw [Real.le_log_iff_exp_le hn0]
  have hsq : Real.exp (9 / 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (9 / 2) = 9 by norm_num]
    exact exp_nine_bounds'.2.trans (pow_le_pow_left₀ (by norm_num) hn' 2)
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hn0.le (by norm_num : 2 ≠ 0)).mp hsq

private theorem exp_neg_nine_quarters_bounds' :
    (0.105399 : ℝ) ≤ Real.exp (-(9 / 2 / 2)) ∧ Real.exp (-(9 / 2 / 2)) ≤ 0.105400 := by
  have he9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  have he9_lo : (2.7182818283 : ℝ) ^ 9 ≤ Real.exp 9 := by
    rw [he9]; exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 9
  have he9_hi : Real.exp 9 ≤ (2.7182818286 : ℝ) ^ 9 := by
    rw [he9]; exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 9
  have he4 : Real.exp (-(9 / 2 / 2)) ^ 4 = (Real.exp 9)⁻¹ := by
    rw [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * -(9 / 2 / 2) = -9 by norm_num, Real.exp_neg]
  have hlo4 : (0.105399 : ℝ) ^ 4 ≤ Real.exp (-(9 / 2 / 2)) ^ 4 := by
    rw [he4, le_inv_comm₀ (by norm_num) (Real.exp_pos 9)]
    exact he9_hi.trans (by norm_num)
  have hhi4 : Real.exp (-(9 / 2 / 2)) ^ 4 ≤ (0.105400 : ℝ) ^ 4 := by
    rw [he4, inv_le_comm₀ (Real.exp_pos 9) (by norm_num)]
    exact (by norm_num : (0.105400 ^ 4 : ℝ)⁻¹ ≤ 2.7182818283 ^ 9).trans he9_lo
  exact ⟨(pow_le_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 4 ≠ 0)).mp hlo4,
    (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 4 ≠ 0)).mp hhi4⟩

private theorem le_log_of_two_pow_le' {p : ℝ} {k m : ℕ} (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ p ^ k) : (m : ℝ) / k * Real.log 2 ≤ Real.log p := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']; linarith only [hl]

private theorem log_le_of_pow_le_two_pow' {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : p ^ k ≤ (2 : ℝ) ^ m) : Real.log p ≤ (m : ℝ) / k * Real.log 2 := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']; linarith only [hl]

private theorem log_pi_lb_sharp' : (1.144498 : ℝ) ≤ Real.log Real.pi := by
  have hpow : (2 : ℝ) ^ 71 ≤ Real.pi ^ 43 :=
    (by norm_num : (2 : ℝ) ^ 71 ≤ 3.14159265 ^ 43).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith [pi_bounds_d10'.1]) 43)
  have h := le_log_of_two_pow_le' (p := Real.pi) (k := 43) (m := 71) (by norm_num) hpow
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢; linarith only [h, hl2]

private theorem bohman_budget_left_bounds' :
    (2.236881 : ℝ) ≤ 4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
          ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ∧
      4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
          ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ≤ 2.236883 := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10'
  obtain ⟨he_lo, he_hi⟩ := exp_neg_nine_quarters_bounds'
  have hπ2_lo : 3.1415926535 ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) hπ_lo.le 2
  have hπ2_hi : Real.pi ^ 2 ≤ 3.1415926536 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hπ_hi.le 2
  have hden_lo : (9 / 2 : ℝ) ^ 2 + 4 * 3.1415926535 ^ 2 ≤ (9 / 2) ^ 2 + 4 * Real.pi ^ 2 := by
    linarith only [hπ2_lo]
  have hden_hi : (9 / 2 : ℝ) ^ 2 + 4 * Real.pi ^ 2 ≤ (9 / 2) ^ 2 + 4 * 3.1415926536 ^ 2 := by
    linarith only [hπ2_hi]
  have ht1_lo : 4 * (9 / 2 : ℝ) ^ 2 / ((9 / 2) ^ 2 + 4 * 3.1415926536 ^ 2) ≤
      4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden_hi
  have ht1_hi : 4 * (9 / 2 : ℝ) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ≤
      4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * 3.1415926535 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden_lo
  have hnum_lo : 64 * 3.1415926535 ^ 2 * (9 / 2) * (1 + 0.105399) ≤
      64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) :=
    mul_le_mul (by linarith only [hπ2_lo]) (by linarith only [he_lo]) (by norm_num) (by positivity)
  have hnum_hi : 64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) ≤
      64 * 3.1415926536 ^ 2 * (9 / 2) * (1 + 0.105400) :=
    mul_le_mul (by linarith only [hπ2_hi]) (by linarith only [he_hi]) (by positivity) (by norm_num)
  have ht2_lo : 64 * 3.1415926535 ^ 2 * (9 / 2) * (1 + 0.105399) /
        ((9 / 2) ^ 2 + 4 * 3.1415926536 ^ 2) ^ 2 ≤
      64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
        ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) hden_hi 2)).trans
      (div_le_div_of_nonneg_right hnum_lo (by positivity))
  have ht2_hi : 64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
        ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ≤
      64 * 3.1415926536 ^ 2 * (9 / 2) * (1 + 0.105400) /
        ((9 / 2) ^ 2 + 4 * 3.1415926535 ^ 2) ^ 2 :=
    (div_le_div_of_nonneg_right hnum_hi (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) hden_lo 2))
  exact ⟨(by norm_num : (2.236881 : ℝ) ≤ _).trans (add_le_add ht1_lo ht2_lo),
    (add_le_add ht1_hi ht2_hi).trans (by norm_num)⟩

private theorem bohman_arch_lt_smooth {γ g_lo g_hi M logM4_hi ub : ℝ} {a2 b c d : ℕ}
    (hg0 : 0 < g_lo) (hlo : g_lo ≤ γ) (hhi : γ ≤ g_hi) (hM : 0 < M)
    (hM_eq : M / 4 = (2 : ℝ) ^ a2 * (3 : ℝ) ^ b * (5 : ℝ) ^ c * (7 : ℝ) ^ d)
    (hlogM : (a2 : ℝ) * 0.6931471808 + (b : ℝ) * 1.0986129 +
      (c : ℝ) * 1.609438 + (d : ℝ) * 1.9459107 ≤ logM4_hi)
    (hub : 1 / 4 * (logM4_hi + (9 + g_hi ^ 2 - M) / M) - 1.144498 / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * g_lo ^ 2) + 1200 / ((9 / 2) ^ 3 * g_lo ^ 4) < ub) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) < ub := by
  have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨-, hl3b⟩, ⟨-, hl5b⟩, ⟨-, hl7b⟩, -⟩ := sharp_log_prime_bounds
  have hlogM4 : Real.log (M / 4) ≤ logM4_hi := by
    rw [hM_eq, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    have m2 := mul_le_mul_of_nonneg_left hl2b (Nat.cast_nonneg a2)
    have m3 := mul_le_mul_of_nonneg_left hl3b (Nat.cast_nonneg b)
    have m5 := mul_le_mul_of_nonneg_left hl5b (Nat.cast_nonneg c)
    have m7 := mul_le_mul_of_nonneg_left hl7b (Nat.cast_nonneg d)
    linarith only [m2, m3, m5, m7, hlogM]
  have hγ_le : 9 / 4 + γ ^ 2 / 4 ≤ (9 + g_hi ^ 2) / 4 := by
    have := pow_le_pow_left₀ (hg0.le.trans hlo) hhi 2; linarith
  have hsplit : (9 + g_hi ^ 2) / 4 = (M / 4) * ((9 + g_hi ^ 2) / M) := by
    field_simp [hM.ne']
  have hpos_ghi : 0 < 9 + g_hi ^ 2 := by positivity
  have hlog_tot : Real.log (9 / 4 + γ ^ 2 / 4) ≤ logM4_hi + (9 + g_hi ^ 2 - M) / M := by
    calc Real.log (9 / 4 + γ ^ 2 / 4)
        ≤ Real.log ((9 + g_hi ^ 2) / 4) := Real.log_le_log (by positivity) hγ_le
      _ = Real.log (M / 4) + Real.log ((9 + g_hi ^ 2) / M) := by
          rw [hsplit, Real.log_mul (by positivity) (by positivity)]
      _ ≤ logM4_hi + ((9 + g_hi ^ 2) / M - 1) :=
          add_le_add hlogM4 (Real.log_le_sub_one_of_pos (div_pos hpos_ghi hM))
      _ = logM4_hi + (9 + g_hi ^ 2 - M) / M := by field_simp [hM.ne']
  have hπ := log_pi_lb_sharp'
  have ht1 : 18 / ((9 / 2 : ℝ) ^ 2 * γ ^ 2) ≤ 18 / ((9 / 2) ^ 2 * g_lo ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0.le hlo 2) (by norm_num))
  have ht2 : 1200 / ((9 / 2 : ℝ) ^ 3 * γ ^ 4) ≤ 1200 / ((9 / 2) ^ 3 * g_lo ^ 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0.le hlo 4) (by norm_num))
  linarith only [hlog_tot, hπ, ht1, ht2, hub]

/-! ## 41-interval coupled prime-phase exclusion across `(169/2, 150]` -/

private theorem bohman_interval_0 {γ : ℝ} (hlo : (169 / 2) ≤ γ) (hhi : γ ≤ 88.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := (169 / 2)) (g_hi := 88.140625) (M := 7776) (logM4_hi := 7.5725062) (ub := 1.321884) (a2 := 3) (b := 5) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.8493) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := (169 / 2)) (g_hi := 88.140625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.5848) 15 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.02194 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.8493)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_1 {γ : ℝ} (hlo : 88.140625 ≤ γ) (hhi : γ ≤ 93.53125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 88.140625) (g_hi := 93.53125) (M := 8748) (logM4_hi := 7.6902904) (ub := 1.351523) (a2 := 0) (b := 7) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.4156) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 88.140625) (g_hi := 93.53125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9992) 10 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.05078 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.4156)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_2 {γ : ℝ} (hlo : 93.53125 ≤ γ) (hhi : γ ≤ 95.234375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 93.53125) (g_hi := 95.234375) (M := 9072) (logM4_hi := 7.7266568) (ub := 1.360523) (a2 := 2) (b := 4) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, hn3, -, hn7, -, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.7877) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 93.53125) (g_hi := 95.234375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.4775) 24 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.03519 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.7877)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5622) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 93.53125) (g_hi := 95.234375) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.1676) 36 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0256 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.5622)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn3, hn7, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_3 {γ : ℝ} (hlo : 95.234375 ≤ γ) (hhi : γ ≤ 96.984375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, ⟨hl19a, hl19b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 95.234375) (g_hi := 96.984375) (M := 9408) (logM4_hi := 7.7630232) (ub := 1.369615) (a2 := 4) (b := 1) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, hn5, hn7, hn11, hn13, hn17, -, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.5795) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 95.234375) (g_hi := 96.984375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.1887) 17 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06791 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.5795)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9499) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 95.234375) (g_hi := 96.984375) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 2.8215) 45 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00092 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.9499)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn11, hn13, hn17, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_4 {γ : ℝ} (hlo : 96.984375 ≤ γ) (hhi : γ ≤ 99.609375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 96.984375) (g_hi := 99.609375) (M := 10000) (logM4_hi := 7.8240465) (ub := 1.382958) (a2 := 2) (b := 0) (c := 4) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.3146) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 96.984375) (g_hi := 99.609375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8907) 11 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06367 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.3146)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8664) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 96.984375) (g_hi := 99.609375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.6181) 17 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01932 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.8664)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_5 {γ : ℝ} (hlo : 99.609375 ≤ γ) (hhi : γ ≤ 102.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 99.609375) (g_hi := 102.140625) (M := 10500) (logM4_hi := 7.8728377) (ub := 1.395487) (a2 := 0) (b := 1) (c := 3) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.1127) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 99.609375) (g_hi := 102.140625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.6836) 11 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09547 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.1127)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_6 {γ : ℝ} (hlo : 102.140625 ≤ γ) (hhi : γ ≤ 104.75) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 102.140625) (g_hi := 104.75) (M := 10976) (logM4_hi := 7.9171738) (ub := 1.408081) (a2 := 3) (b := 0) (c := 0) (d := 3) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, hn5, -, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.4003) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 102.140625) (g_hi := 104.75) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.9825) 18 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10365 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.4003)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9332) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 102.140625) (g_hi := 104.75) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.7724) 32 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00791 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9332)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_7 {γ : ℝ} (hlo : 104.75 ≤ γ) (hhi : γ ≤ 106.59375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 104.75) (g_hi := 106.59375) (M := 11340) (logM4_hi := 7.9498004) (ub := 1.416795) (a2 := 0) (b := 4) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.3331) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 104.75) (g_hi := 106.59375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.9102) 27 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11328 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.3331)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9398) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 104.75) (g_hi := 106.59375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.7912) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00387 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.9398)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_8 {γ : ℝ} (hlo : 106.59375 ≤ γ) (hhi : γ ≤ 111.046875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 106.59375) (g_hi := 111.046875) (M := 12348) (logM4_hi := 8.034958) (ub := 1.43724) (a2 := 0) (b := 2) (c := 0) (d := 3) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.0032) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 106.59375) (g_hi := 111.046875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.5738) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11713 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.0032)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.866) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 106.59375) (g_hi := 111.046875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.6172) 19 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01938 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.866)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_9 {γ : ℝ} (hlo : 111.046875 ≤ γ) (hhi : γ ≤ 111.375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, -, -, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.046875) (g_hi := 111.375) (M := 12348) (logM4_hi := 8.034958) (ub := 1.438711) (a2 := 0) (b := 2) (c := 0) (d := 3) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, hn7, hn11, hn13, -, -, hn23, hn29, -, -, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.2285) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.046875) (g_hi := 111.375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8012) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.07613 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.2285)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.1797 ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.046875) (g_hi := 111.375) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.39) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02858 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := 0.1797) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.3514 ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.046875) (g_hi := 111.375) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.2116) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02515 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := 0.3514) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.4148 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.046875) (g_hi := 111.375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.1429) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00335 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.4148) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.3619) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.046875) (g_hi := 111.375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.9409) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00291 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := (-0.3619)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9877) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 111.046875) (g_hi := 111.375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.9776) 19 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00168 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.9877)) (by norm_num) hu_5 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn23, hn29, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5]

private theorem bohman_interval_10 {γ : ℝ} (hlo : 111.375 ≤ γ) (hhi : γ ≤ 111.4375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, -, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.375) (g_hi := 111.4375) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.438991) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, hn7, hn11, hn13, -, -, -, -, -, -, -, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.2705) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8445) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06987 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.2705)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0035 ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.5671) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02431 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := 0.0035) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.1742 ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.3956) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02185 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := 0.1742) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.6864 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.8141) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0077 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.6864) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9641 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 0.2681) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00465 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.9641) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.3784) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.9587) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00353 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := (-0.3784)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9849) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.9614) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00246 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9849)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.4612 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 1.0913) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00223 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.4612) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.8786) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.6429) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00137 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.8786)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.4791) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.0702) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00063 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := (-0.4791)) (by norm_num) hu_9 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn11, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9]

private theorem bohman_interval_11 {γ : ℝ} (hlo : 111.4375 ≤ γ) (hhi : γ ≤ 111.46875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, -, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.4375) (g_hi := 111.46875) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.43913) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, hn7, hn11, hn13, -, -, -, -, -, -, -, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.2913) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8662) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.0669 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.2913)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0849) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.6556) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02217 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.0849)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.083 ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.4876) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02015 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := 0.083) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.8255 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.5995) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00834 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.8255) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.9616) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.8608) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00629 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9616)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.1767) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.7483) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00468 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := (-0.1767)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.9282 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 0.3809) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00457 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.9282) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.7685) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.4469) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00262 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.7685)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.6529 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 0.8592) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00253 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.6529) (by norm_num) hu_8 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn11, hn13, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8]

private theorem bohman_interval_12 {γ : ℝ} (hlo : 111.46875 ≤ γ) (hhi : γ ≤ 111.5) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.46875) (g_hi := 111.5) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.43927) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, hn7, -, hn13, -, -, -, -, -, -, -, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.3119) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8878) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06404 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.3119)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1727) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.7442) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02004 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.1727)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.009) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.5796) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01844 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.009)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9463) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.8105) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00881 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9463)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.8811 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.4922) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0086 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.8811) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.0723) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.643) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00527 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := (-0.0723)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.8804 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 0.4938) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00445 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.8804) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.7021) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.3489) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00338 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.7021)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.7362 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 0.7432) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00265 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.7362) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.9685) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.8868) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00183 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.9685)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.1464) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.7176) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00104 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := (-0.1464)) (by norm_num) hu_10 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10]

private theorem bohman_interval_13 {γ : ℝ} (hlo : 111.5 ≤ γ) (hhi : γ ≤ 111.53125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.5) (g_hi := 111.53125) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.439409) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, -, -, hn13, -, -, -, -, -, -, -, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.3324) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9095) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06127 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.3324)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2591) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.8327) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01795 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.2591)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.1008) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.6716) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01673 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.1008)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9287) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.7602) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01172 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9287)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9267 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.3849) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0088 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.9267) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.0328 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.5378) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00587 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := 0.0328) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.8214 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 0.6066) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00431 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.8214) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.6291) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.2509) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00421 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.6291)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9467) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.8118) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.0031 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.9467)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.8096 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 0.6271) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00277 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.8096) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.9813) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.9429) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.0022 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9813)) (by norm_num) hu_10 (by norm_num)
  linarith only [harch, hmaster, hn3, hn13, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10]

private theorem bohman_interval_14 {γ : ℝ} (hlo : 111.53125 ≤ γ) (hhi : γ ≤ 111.578125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.53125) (g_hi := 111.578125) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.439618) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, -, -, hn13, -, -, -, -, -, -, -, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.3629) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.942) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.05729 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.3629)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9087) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.7099) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01502 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9087)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3847) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.9655) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0149 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.3847)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.2367) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.8096) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0142 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.2367)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9616 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.2776) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00896 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.9616) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.1376 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.4326) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00647 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := 0.1376) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.55) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.153) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00511 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.55)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.9197) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.7369) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00468 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.9197)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.7136 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 0.7759) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00406 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.7136) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.9673) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.8821) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00386 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9673)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.8721 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 0.5111) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00286 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.8721) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.088 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.578125) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.4825) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00132 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := 0.088) (by norm_num) hu_11 (by norm_num)
  linarith only [harch, hmaster, hn3, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11]

private theorem bohman_interval_15 {γ : ℝ} (hlo : 111.578125 ≤ γ) (hhi : γ ≤ 111.65625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.578125) (g_hi := 111.65625) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.439967) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, -, -, -, -, -, -, -, -, -, -, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.4128) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9961) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.05111 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.4128)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8745) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.6345) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0207 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.8745)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.578) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 2.1869) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01022 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.578)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4521) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 2.0397) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01019 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.4521)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9883 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.152) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00909 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.9883) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8696) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.6245) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00761 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.8696)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.2916 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.2747) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00734 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := 0.2916) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.9397) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.7909) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00714 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9397)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.4218) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.006) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00658 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.4218)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.4905 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.058) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00353 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.4905) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.9436 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 0.337) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00297 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.9436) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.9539) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.8345) 46 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00195 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.9539)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.2614 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 111.578125) (g_hi := 111.65625) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.3062) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00154 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := 0.2614) (by norm_num) hu_12 (by norm_num)
  linarith only [harch, hmaster, hn3, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11, hg_12]

private theorem bohman_interval_16 {γ : ℝ} (hlo : 111.65625 ≤ γ) (hhi : γ ≤ 111.859375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.65625) (g_hi := 111.859375) (M := 12500) (logM4_hi := 8.0471901) (ub := 1.440875) (a2 := 0) (b := 0) (c := 5) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.5365) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.1369) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.03735 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.5365)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8066) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.5087) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.03202 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.8066)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.8766) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.6388) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01463 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.8766)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7622) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.4372) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0139 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.7622)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.1892) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 1.761) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00923 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.1892)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.5303 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.0117) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0087 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := 0.5303) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.6602 ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 0.8495) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00758 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := 0.6602) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.8743) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.6341) 46 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00535 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.8743)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.7596 ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 0.7078) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00269 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := 0.7596) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.8761) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 2.6378) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00229 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.8761)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.5298 ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.0123) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00187 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := 0.5298) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.2191) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.7915) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00184 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := (-0.2191)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.9295) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 2.7624) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00169 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.9295)) (by norm_num) hu_12 (by norm_num)
  have hu_13 : (-0.9907) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 111.65625) (g_hi := 111.859375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.9969) 20 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_13 : 0.00127 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.9907)) (by norm_num) hu_13 (by norm_num)
  linarith only [harch, hmaster, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11, hg_12, hg_13]

private theorem bohman_interval_17 {γ : ℝ} (hlo : 111.859375 ≤ γ) (hhi : γ ≤ 113.671875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.859375) (g_hi := 113.671875) (M := 12960) (logM4_hi := 8.0833313) (ub := 1.448906) (a2 := 3) (b := 4) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, -, -, -, -, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.5739) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 111.859375) (g_hi := 113.671875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.1818) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.07145 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.5739)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6234) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 111.859375) (g_hi := 113.671875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.2436) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04472 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.6234)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7352) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 111.859375) (g_hi := 113.671875) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.3965) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01548 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.7352)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9337) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 111.859375) (g_hi := 113.671875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.7738) 20 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00933 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.9337)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8226) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 111.859375) (g_hi := 113.671875) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.5363) 46 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00756 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.8226)) (by norm_num) hu_4 (by norm_num)
  linarith only [harch, hmaster, hn2, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4]

private theorem bohman_interval_18 {γ : ℝ} (hlo : 113.671875 ≤ γ) (hhi : γ ≤ 115.96875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 113.671875) (g_hi := 115.96875) (M := 13440) (logM4_hi := 8.1196977) (ub := 1.458899) (a2 := 5) (b := 1) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.1697) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 113.671875) (g_hi := 115.96875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.7412) 20 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.15639 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.1697)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9694) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 113.671875) (g_hi := 115.96875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.8902) 13 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00193 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.9694)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_19 {γ : ℝ} (hlo : 115.96875 ≤ γ) (hhi : γ ≤ 119.78125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 115.96875) (g_hi := 119.78125) (M := 14336) (logM4_hi := 8.1842355) (ub := 1.475059) (a2 := 9) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.2239 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 115.96875) (g_hi := 119.78125) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.3448) 13 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.176 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := 0.2239) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_20 {γ : ℝ} (hlo : 119.78125 ≤ γ) (hhi : γ ≤ 122) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 119.78125) (g_hi := 122) (M := 15000) (logM4_hi := 8.2295122) (ub := 1.484232) (a2 := 1) (b := 1) (c := 4) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, -, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.4148) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 119.78125) (g_hi := 122) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.9984) 31 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09897 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.4148)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4911) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 119.78125) (g_hi := 122) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.084) 21 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.08499 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.4911)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_21 {γ : ℝ} (hlo : 122 ≤ γ) (hhi : γ ≤ 123.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨-, -, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, -, -, -, ⟨hl31a, hl31b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 122) (g_hi := 123.140625) (M := 15120) (logM4_hi := 8.2374819) (ub := 1.488876) (a2 := 2) (b := 3) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, hn3, hn5, -, -, -, hn17, hn19, hn23, hn29, -, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.2087 ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.140625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.3604) 38 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14418 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := 0.2087) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1196) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.140625) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 1.6905) 50 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.03759 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.1196)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9311) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.140625) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.7667) 47 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00402 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.9311)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4408) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.140625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.0271) 67 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00254 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := (-0.4408)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn2, hn3, hn5, hn17, hn19, hn23, hn29, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_22 {γ : ℝ} (hlo : 123.140625 ≤ γ) (hhi : γ ≤ 123.6875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, -, ⟨hl19a, hl19b⟩, -, ⟨hl29a, hl29b⟩, -, ⟨hl37a, hl37b⟩, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 123.140625) (g_hi := 123.6875) (M := 15360) (logM4_hi := 8.2532285) (ub := 1.491088) (a2 := 8) (b := 1) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, -, -, hn13, hn17, -, hn23, -, hn31, -, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.346) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.9239) 38 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.07779 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.346)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.2864 ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 1.2802) 47 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.07524 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := 0.2864) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.2708) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.8449) 58 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01356 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.2708)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8625) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.6102) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00921 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.8625)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.9654) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.8749) 32 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00567 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9654)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.2297) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.8024) 66 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00437 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := (-0.2297)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.1147 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.4557) 71 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00263 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.1147) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.982) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 123.140625) (g_hi := 123.6875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.9464) 22 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00248 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.982)) (by norm_num) hu_7 (by norm_num)
  linarith only [harch, hmaster, hn13, hn17, hn23, hn31, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7]

private theorem bohman_interval_23 {γ : ℝ} (hlo : 123.6875 ≤ γ) (hhi : γ ≤ 124.90625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, -, -, ⟨hl17a, hl17b⟩, -, ⟨hl23a, hl23b⟩, -, ⟨hl31a, hl31b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 123.6875) (g_hi := 124.90625) (M := 15552) (logM4_hi := 8.2656534) (ub := 1.495989) (a2 := 4) (b := 5) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, hn7, hn11, hn13, -, hn19, -, hn29, -, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.4115) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 123.6875) (g_hi := 124.90625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.9947) 32 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09955 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.4115)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6998) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 123.6875) (g_hi := 124.90625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3456) 22 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0463 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.6998)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6135) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 123.6875) (g_hi := 124.90625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.2311) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02975 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.6135)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4414) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 123.6875) (g_hi := 124.90625) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 2.0278) 56 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01353 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.4414)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.4925) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 123.6875) (g_hi := 124.90625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.0856) 62 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00577 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.4925)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8106) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 123.6875) (g_hi := 124.90625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 2.5155) 68 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00085 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := (-0.8106)) (by norm_num) hu_5 (by norm_num)
  linarith only [harch, hmaster, hn7, hn11, hn13, hn19, hn29, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5]

private theorem bohman_interval_24 {γ : ℝ} (hlo : 124.90625 ≤ γ) (hhi : γ ≤ 127.96875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 124.90625) (g_hi := 127.96875) (M := 16384) (logM4_hi := 8.3177663) (ub := 1.508089) (a2 := 12) (b := 0) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.1833 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 124.90625) (g_hi := 127.96875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.3863) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.16377 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := 0.1833) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.7087) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 124.90625) (g_hi := 127.96875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.3582) 22 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04478 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.7087)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_25 {γ : ℝ} (hlo : 127.96875 ≤ γ) (hhi : γ ≤ 129.921875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 127.96875) (g_hi := 129.921875) (M := 16800) (logM4_hi := 8.3428413) (ub := 1.51566) (a2 := 3) (b := 1) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, -, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.1845) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 127.96875) (g_hi := 129.921875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.7562) 33 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.13962 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.1845)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4968) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 127.96875) (g_hi := 129.921875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.0905) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04154 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.4968)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6754) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 127.96875) (g_hi := 129.921875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.3121) 40 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03854 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.6754)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn3, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_26 {γ : ℝ} (hlo : 129.921875 ≤ γ) (hhi : γ ≤ 130.71875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, -, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 129.921875) (g_hi := 130.71875) (M := 17280) (logM4_hi := 8.3710128) (ub := 1.518725) (a2 := 5) (b := 3) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hn31, -, -, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.2075) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.7797) 23 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.1472 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.2075)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0487) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.6194) 61 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0177 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.0487)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6502) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.2784) 53 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01493 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.6502)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.1093 ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 1.4611) 65 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01263 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := 0.1093) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8786) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.6429) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00806 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.8786)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8676) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.6204) 50 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00773 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.8676)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8632) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 2.6117) 59 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.0033 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.8632)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.6942) ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 2.3378) 70 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00173 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := (-0.6942)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.0577) ≤ Real.cos (γ * Real.log 41) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 41) (lp_lo := 3.713572) (lp_hi := 3.7135722) (x_hi := 1.6284) 77 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00143 ≤ bohmanExcess 41 (γ * Real.log 41) := bohmanExcess41_ge (u_lo := (-0.0577)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.0006) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.5712) 78 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00122 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := (-0.0006)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.5067) ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 2.1019) 75 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00116 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := (-0.5067)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.9961) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 3.0388) 33 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00062 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9961)) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.9962) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 129.921875) (g_hi := 130.71875) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 3.0398) 40 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00044 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9962)) (by norm_num) hu_12 (by norm_num)
  linarith only [harch, hmaster, hn31, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11, hg_12]

private theorem bohman_interval_27 {γ : ℝ} (hlo : 130.71875 ≤ γ) (hhi : γ ≤ 132.875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 130.71875) (g_hi := 132.875) (M := 17640) (logM4_hi := 8.3916325) (ub := 1.526887) (a2 := 1) (b := 2) (c := 1) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.1053 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 130.71875) (g_hi := 132.875) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.4651) 23 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.23004 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := 0.1053) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_28 {γ : ℝ} (hlo : 132.875 ≤ γ) (hhi : γ ≤ 133.890625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 132.875) (g_hi := 133.890625) (M := 17920) (logM4_hi := 8.4073791) (ub := 1.53069) (a2 := 7) (b := 0) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, hn7, -, hn13, -, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.2858) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.8605) 34 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.12162 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.2858)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.249) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 1.8223) 51 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04392 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.249)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5442) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.146) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03656 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.5442)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8472) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.5809) 23 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02226 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.8472)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.7027) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 2.3497) 60 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00719 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.7027)) (by norm_num) hu_4 (by norm_num)
  linarith only [harch, hmaster, hn7, hn13, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4]

private theorem bohman_interval_29 {γ : ℝ} (hlo : 133.890625 ≤ γ) (hhi : γ ≤ 134.5625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 133.890625) (g_hi := 134.5625) (M := 18144) (logM4_hi := 8.419804) (ub := 1.533191) (a2 := 3) (b := 4) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, hn7, -, -, hn17, -, -, -, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.1283 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.442) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14849 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := 0.1283) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6084) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.2246) 51 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02289 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.6084)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5498) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.1527) 55 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01921 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.5498)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.0374) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.6081) 63 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01791 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.0374)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.3989 ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 1.1603) 67 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01593 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := 0.3989) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.0304 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.5402) 72 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00586 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := 0.0304) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9811) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.5625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.9419) 34 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00309 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9811)) (by norm_num) hu_6 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn17, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6]

private theorem bohman_interval_30 {γ : ℝ} (hlo : 134.5625 ≤ γ) (hhi : γ ≤ 137.625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 134.5625) (g_hi := 137.625) (M := 18900) (logM4_hi := 8.4606255) (ub := 1.544438) (a2 := 0) (b := 3) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.4113 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 134.5625) (g_hi := 137.625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.1468) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.24501 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := 0.4113) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_31 {γ : ℝ} (hlo : 137.625 ≤ γ) (hhi : γ ≤ 138.84375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, ⟨hl7a, hl7b⟩, -, -, -, -, ⟨hl23a, hl23b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 137.625) (g_hi := 138.84375) (M := 19200) (logM4_hi := 8.4763721) (ub := 1.548843) (a2 := 6) (b := 1) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, -, hn11, hn13, hn17, hn19, -, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.1678) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.84375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.7392) 24 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.15685 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.1678)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4086) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.84375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9915) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05162 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.4086)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7181) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.84375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.3715) 43 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03346 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.7181)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4322) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.84375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.0176) 69 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00646 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.4322)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn5, hn11, hn13, hn17, hn19, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_32 {γ : ℝ} (hlo : 138.84375 ≤ γ) (hhi : γ ≤ 139.625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, -, -, -, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 138.84375) (g_hi := 139.625) (M := 19440) (logM4_hi := 8.488797) (ub := 1.551646) (a2 := 2) (b := 5) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, -, -, -, -, hn19, hn23, hn29, -, -, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.0496 ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.521) 43 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.12511 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := 0.0496) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.225) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 1.7976) 53 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04532 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.225)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.4295) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.0146) 57 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02435 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.4295)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8559) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.5975) 24 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02092 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.8559)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.9187) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.7344) 36 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01337 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9187)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.8207) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.533) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01229 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.8207)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.7812) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 2.4669) 63 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00529 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.7812)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.3689) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.9485) 76 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00287 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := (-0.3689)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.0507 ≤ Real.cos (γ * Real.log 37) := cos_mul_ge_of_even_shift (g_lo := 138.84375) (g_hi := 139.625) (lp := Real.log 37) (lp_lo := 3.6109175) (lp_hi := 3.6109192) (x_hi := 1.5199) 80 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00248 ≤ bohmanExcess 37 (γ * Real.log 37) := bohmanExcess37_ge (u_lo := 0.0507) (by norm_num) hu_8 (by norm_num)
  linarith only [harch, hmaster, hn19, hn23, hn29, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8]

private theorem bohman_interval_33 {γ : ℝ} (hlo : 139.625 ≤ γ) (hhi : γ ≤ 140.359375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, -, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, -, -, -, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 139.625) (g_hi := 140.359375) (M := 19600) (logM4_hi := 8.4969919) (ub := 1.554269) (a2 := 2) (b := 0) (c := 2) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, -, -, hn11, -, -, hn19, -, -, hn31, hn37, hn41, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.0934 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.4771) 36 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.18991 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := 0.0934) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2982) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 1.8734) 57 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02996 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.2982)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.254) ≤ Real.cos (γ * Real.log 17) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 17) (lp_lo := 2.8332133) (lp_hi := 2.8332134) (x_hi := 1.8275) 63 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01807 ≤ bohmanExcess 17 (γ * Real.log 17) := bohmanExcess17_ge (u_lo := (-0.254)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.1768 ≤ Real.cos (γ * Real.log 29) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 29) (lp_lo := 3.3672956) (lp_hi := 3.3672966) (x_hi := 1.3929) 75 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00669 ≤ bohmanExcess 29 (γ * Real.log 29) := bohmanExcess29_ge (u_lo := 0.1768) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.4432) ≤ Real.cos (γ * Real.log 23) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 23) (lp_lo := 3.135494) (lp_hi := 3.1354949) (x_hi := 2.0298) 70 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00633 ≤ bohmanExcess 23 (γ * Real.log 23) := bohmanExcess23_ge (u_lo := (-0.4432)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9827) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.95) 43 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00204 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9827)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9965) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 3.0421) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.0002 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.9965)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.8726) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 139.625) (g_hi := 140.359375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 2.6305) 84 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00014 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := (-0.8726)) (by norm_num) hu_7 (by norm_num)
  linarith only [harch, hmaster, hn3, hn11, hn19, hn31, hn37, hn41, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7]

private theorem bohman_interval_34 {γ : ℝ} (hlo : 140.359375 ≤ γ) (hhi : γ ≤ 141.34375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, -, ⟨hl19a, hl19b⟩, -, -, ⟨hl31a, hl31b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 140.359375) (g_hi := 141.34375) (M := 20000) (logM4_hi := 8.5171937) (ub := 1.557757) (a2 := 3) (b := 0) (c := 4) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, -, hn7, -, hn13, hn17, -, hn23, hn29, -, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.2775 ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 140.359375) (g_hi := 141.34375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 1.2895) 36 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.22397 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := 0.2775) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0824 ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 140.359375) (g_hi := 141.34375) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.4882) 66 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02014 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := 0.0824) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.915) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 140.359375) (g_hi := 141.34375) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.7251) 54 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00496 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.915)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9666) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 140.359375) (g_hi := 141.34375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.8793) 25 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00463 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.9666)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.2401) ≤ Real.cos (γ * Real.log 31) := cos_mul_ge_of_even_shift (g_lo := 140.359375) (g_hi := 141.34375) (lp := Real.log 31) (lp_lo := 3.4339872) (lp_hi := 3.4339873) (x_hi := 1.8131) 77 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00346 ≤ bohmanExcess 31 (γ * Real.log 31) := bohmanExcess31_ge (u_lo := (-0.2401)) (by norm_num) hu_4 (by norm_num)
  linarith only [harch, hmaster, hn2, hn7, hn13, hn17, hn23, hn29, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4]

private theorem bohman_interval_35 {γ : ℝ} (hlo : 141.34375 ≤ γ) (hhi : γ ≤ 142.984375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, ⟨hl7a, hl7b⟩, -, ⟨hl13a, hl13b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 141.34375) (g_hi := 142.984375) (M := 20480) (logM4_hi := 8.54091) (ub := 1.563524) (a2 := 10) (b := 0) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, hn5, -, hn11, -, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.2252) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 141.34375) (g_hi := 142.984375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.7978) 25 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14297 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.2252)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2027) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 141.34375) (g_hi := 142.984375) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 1.7748) 44 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.09491 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.2027)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6836) ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 141.34375) (g_hi := 142.984375) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 2.3232) 58 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0135 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := (-0.6836)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8354) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 141.34375) (g_hi := 142.984375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.5591) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01119 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.8354)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn5, hn11, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_36 {γ : ℝ} (hlo : 142.984375 ≤ γ) (hhi : γ ≤ 145) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 142.984375) (g_hi := 145) (M := 21000) (logM4_hi := 8.5659849) (ub := 1.57052) (a2 := 1) (b := 1) (c := 3) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, hn7, -, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.1482 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 142.984375) (g_hi := 145) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.4219) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.15385 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := 0.1482) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6043) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 142.984375) (g_hi := 145) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.2194) 25 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0633 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.6043)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7054) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 142.984375) (g_hi := 145) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.3535) 37 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04905 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.7054)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9104) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 142.984375) (g_hi := 145) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 2.7139) 55 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00523 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.9104)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn7, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_37 {γ : ℝ} (hlo : 145 ≤ γ) (hhi : γ ≤ 146.640625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, -, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 145) (g_hi := 146.640625) (M := 21504) (logM4_hi := 8.5897012) (ub := 1.576142) (a2 := 8) (b := 1) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, hn3, hn5, -, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.4421 ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 145) (g_hi := 146.640625) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.1127) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.25867 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := 0.4421) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8605) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 145) (g_hi := 146.640625) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.6064) 45 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01654 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.8605)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_38 {γ : ℝ} (hlo : 146.640625 ≤ γ) (hhi : γ ≤ 147.484375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, ⟨hl19a, hl19b⟩, -, -, -, -, -, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 146.640625) (g_hi := 147.484375) (M := 21600) (logM4_hi := 8.5941564) (ub := 1.579015) (a2 := 3) (b := 3) (c := 2) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨-, -, -, hn7, -, -, hn17, -, hn23, hn29, hn31, hn37, hn41, -, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : (-0.1266) ≤ Real.cos (γ * Real.log 2) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 2) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.6976) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09297 ≤ bohmanExcess 2 (γ * Real.log 2) := bohmanExcess2_ge (u_lo := (-0.1266)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6375) ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 2.2618) 26 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05726 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := (-0.6375)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.2682 ≤ Real.cos (γ * Real.log 13) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 13) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (x_hi := 1.2991) 60 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.05415 ≤ bohmanExcess 13 (γ * Real.log 13) := bohmanExcess13_ge (u_lo := 0.2682) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.2215) ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 1.794) 56 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04553 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := (-0.2215)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.1937) ≤ Real.cos (γ * Real.log 19) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 19) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (x_hi := 1.7656) 69 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.015 ≤ bohmanExcess 19 (γ * Real.log 19) := bohmanExcess19_ge (u_lo := (-0.1937)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9257) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.7522) 38 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01221 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.9257)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.2257) ≤ Real.cos (γ * Real.log 43) := cos_mul_ge_of_even_shift (g_lo := 146.640625) (g_hi := 147.484375) (lp := Real.log 43) (lp_lo := 3.7611977) (lp_hi := 3.7612013) (x_hi := 1.7983) 88 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00094 ≤ bohmanExcess 43 (γ * Real.log 43) := bohmanExcess43_ge (u_lo := (-0.2257)) (by norm_num) hu_6 (by norm_num)
  linarith only [harch, hmaster, hn7, hn17, hn23, hn29, hn31, hn37, hn41, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6]

private theorem bohman_interval_39 {γ : ℝ} (hlo : 147.484375 ≤ γ) (hhi : γ ≤ 149.953125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 147.484375) (g_hi := 149.953125) (M := 22500) (logM4_hi := 8.6349779) (ub := 1.587305) (a2 := 0) (b := 2) (c := 4) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, -, -, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.1917 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 147.484375) (g_hi := 149.953125) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.3778) 26 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.25576 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := 0.1917) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8464) ≤ Real.cos (γ * Real.log 5) := cos_mul_ge_of_even_shift (g_lo := 147.484375) (g_hi := 149.953125) (lp := Real.log 5) (lp_lo := 1.6094379) (lp_hi := 1.609438) (x_hi := 2.5794) 38 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02537 ≤ bohmanExcess 5 (γ * Real.log 5) := bohmanExcess5_ge (u_lo := (-0.8464)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9319) ≤ Real.cos (γ * Real.log 7) := cos_mul_ge_of_even_shift (g_lo := 147.484375) (g_hi := 149.953125) (lp := Real.log 7) (lp_lo := 1.945908) (lp_hi := 1.9459107) (x_hi := 2.769) 46 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00806 ≤ bohmanExcess 7 (γ * Real.log 7) := bohmanExcess7_ge (u_lo := (-0.9319)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn2, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_40 {γ : ℝ} (hlo : 149.953125 ≤ γ) (hhi : γ ≤ 150) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, ⟨hl11a, hl11b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 149.953125) (g_hi := 150) (M := 22500) (logM4_hi := 8.6349779) (ub := 1.58746) (a2 := 0) (b := 2) (c := 4) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_coupled_ge_sum_excess γ
  obtain ⟨hn2, -, hn5, hn7, -, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_coupled_all_nonneg γ
  have hu_0 : 0.1409 ≤ Real.cos (γ * Real.log 3) := cos_mul_ge_of_even_shift (g_lo := 149.953125) (g_hi := 150) (lp := Real.log 3) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (x_hi := 1.4293) 26 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.24048 ≤ bohmanExcess 3 (γ * Real.log 3) := bohmanExcess3_ge (u_lo := 0.1409) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0276 ≤ Real.cos (γ * Real.log 11) := cos_mul_ge_of_even_shift (g_lo := 149.953125) (g_hi := 150) (lp := Real.log 11) (lp_lo := 2.3978948) (lp_hi := 2.397896) (x_hi := 1.543) 57 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0601 ≤ bohmanExcess 11 (γ * Real.log 11) := bohmanExcess11_ge (u_lo := 0.0276) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_coupled_lt_on_band {γ : ℝ} (hlo : 169 / 2 ≤ γ) (hhi : γ ≤ 150) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  rcases le_or_gt γ 88.140625 with h0 | h0
  · exact bohman_interval_0 hlo h0
  rcases le_or_gt γ 93.53125 with h1 | h1
  · exact bohman_interval_1 h0.le h1
  rcases le_or_gt γ 95.234375 with h2 | h2
  · exact bohman_interval_2 h1.le h2
  rcases le_or_gt γ 96.984375 with h3 | h3
  · exact bohman_interval_3 h2.le h3
  rcases le_or_gt γ 99.609375 with h4 | h4
  · exact bohman_interval_4 h3.le h4
  rcases le_or_gt γ 102.140625 with h5 | h5
  · exact bohman_interval_5 h4.le h5
  rcases le_or_gt γ 104.75 with h6 | h6
  · exact bohman_interval_6 h5.le h6
  rcases le_or_gt γ 106.59375 with h7 | h7
  · exact bohman_interval_7 h6.le h7
  rcases le_or_gt γ 111.046875 with h8 | h8
  · exact bohman_interval_8 h7.le h8
  rcases le_or_gt γ 111.375 with h9 | h9
  · exact bohman_interval_9 h8.le h9
  rcases le_or_gt γ 111.4375 with h10 | h10
  · exact bohman_interval_10 h9.le h10
  rcases le_or_gt γ 111.46875 with h11 | h11
  · exact bohman_interval_11 h10.le h11
  rcases le_or_gt γ 111.5 with h12 | h12
  · exact bohman_interval_12 h11.le h12
  rcases le_or_gt γ 111.53125 with h13 | h13
  · exact bohman_interval_13 h12.le h13
  rcases le_or_gt γ 111.578125 with h14 | h14
  · exact bohman_interval_14 h13.le h14
  rcases le_or_gt γ 111.65625 with h15 | h15
  · exact bohman_interval_15 h14.le h15
  rcases le_or_gt γ 111.859375 with h16 | h16
  · exact bohman_interval_16 h15.le h16
  rcases le_or_gt γ 113.671875 with h17 | h17
  · exact bohman_interval_17 h16.le h17
  rcases le_or_gt γ 115.96875 with h18 | h18
  · exact bohman_interval_18 h17.le h18
  rcases le_or_gt γ 119.78125 with h19 | h19
  · exact bohman_interval_19 h18.le h19
  rcases le_or_gt γ 122 with h20 | h20
  · exact bohman_interval_20 h19.le h20
  rcases le_or_gt γ 123.140625 with h21 | h21
  · exact bohman_interval_21 h20.le h21
  rcases le_or_gt γ 123.6875 with h22 | h22
  · exact bohman_interval_22 h21.le h22
  rcases le_or_gt γ 124.90625 with h23 | h23
  · exact bohman_interval_23 h22.le h23
  rcases le_or_gt γ 127.96875 with h24 | h24
  · exact bohman_interval_24 h23.le h24
  rcases le_or_gt γ 129.921875 with h25 | h25
  · exact bohman_interval_25 h24.le h25
  rcases le_or_gt γ 130.71875 with h26 | h26
  · exact bohman_interval_26 h25.le h26
  rcases le_or_gt γ 132.875 with h27 | h27
  · exact bohman_interval_27 h26.le h27
  rcases le_or_gt γ 133.890625 with h28 | h28
  · exact bohman_interval_28 h27.le h28
  rcases le_or_gt γ 134.5625 with h29 | h29
  · exact bohman_interval_29 h28.le h29
  rcases le_or_gt γ 137.625 with h30 | h30
  · exact bohman_interval_30 h29.le h30
  rcases le_or_gt γ 138.84375 with h31 | h31
  · exact bohman_interval_31 h30.le h31
  rcases le_or_gt γ 139.625 with h32 | h32
  · exact bohman_interval_32 h31.le h32
  rcases le_or_gt γ 140.359375 with h33 | h33
  · exact bohman_interval_33 h32.le h33
  rcases le_or_gt γ 141.34375 with h34 | h34
  · exact bohman_interval_34 h33.le h34
  rcases le_or_gt γ 142.984375 with h35 | h35
  · exact bohman_interval_35 h34.le h35
  rcases le_or_gt γ 145 with h36 | h36
  · exact bohman_interval_36 h35.le h36
  rcases le_or_gt γ 146.640625 with h37 | h37
  · exact bohman_interval_37 h36.le h37
  rcases le_or_gt γ 147.484375 with h38 | h38
  · exact bohman_interval_38 h37.le h38
  rcases le_or_gt γ 149.953125 with h39 | h39
  · exact bohman_interval_39 h38.le h39
  exact bohman_interval_40 h39.le hhi

/-- **The Riemann hypothesis through height `150` via prime-phase-coupled Bohman analysis.**
Every zero of `ξ` in the critical strip with `0 < Im ρ ≤ 150` lies on `Re ρ = 1/2`, proved without
locating any zero or computing any value of `ζ`. -/
theorem rhVerifiedThrough_oneHundredFifty : RHVerifiedThrough 150 := by
  intro ρ hzero hre0 hre1 him0 him150
  rcases le_or_gt ρ.im (169 / 2) with hle | hgt
  · exact rhVerifiedThrough_oneHundredSixtyNine_halves hzero hre0 hre1 him0 hle
  · by_contra hoff
    let rhoSupport : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : XiZeroCopy := by
      have hpos := xi_divisor_pos_on_support rhoSupport
      have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by omega
      exact ⟨rhoSupport, ⟨0, hn⟩⟩
    have hqre : (q.1 : ℂ).re ≠ 1 / 2 := hoff
    have hqim : (q.1 : ℂ).im = ρ.im := rfl
    have hLγ : 4 * Real.pi < (9 / 2) * ρ.im := by
      have := Real.pi_lt_four; linarith only [this, hgt]
    have hb := bohman_budget_at_edge (L := 9 / 2) (N := 91) (by norm_num)
      (fun _ hn => nine_halves_le_log' hn) q hqre hqim (by linarith only [hgt]) hLγ
    rw [bohman_prime_sum_eq_phaseForm] at hb
    have hleft := bohman_budget_left_bounds'.1
    have hstrict := bohman_coupled_lt_on_band hgt.le him150
    linarith only [hb, hleft, hstrict]

/-! ## Exact coupled real-height saturation at `γ = 301/2 = 150.5` and universal finite-band ceiling -/

private theorem mul_cos_le_ub {c ub θ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ ub) :
    c * Real.cos θ ≤ ub := by
  have := Real.cos_le_one θ; nlinarith only [this, hc0, hc]

/-- **Exact coupled real-height saturation at `γ = 301/2 = 150.5` (`L = 9/2`).**
Unlike `bohman_phaseFree_saturates_at_eightyFive` (which sets independent phases `θ ≡ π`),
evaluating at the **actual coupled real height `γ = 301/2`** strictly reverses the `L = 9/2` Bohman
explicit-formula inequality even without the positive `O(1/1215 + 1/γ²)` archimedean constants,
proving `150` is the exact integer ceiling of the coupled `L = 9/2` Bohman test. -/
theorem bohman_coupled_saturates_at_threeHundredOne_halves :
    4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
          ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 <
      1 / 4 * Real.log (9 / 4 + (301 / 2) ^ 2 / 4) - Real.log Real.pi / 2 -
        ∑ n ∈ Finset.range 91,
          vonMangoldt n / n * bohmanFn (9 / 2) (Real.log n) * Real.cos ((301 / 2) * Real.log n) := by
  rw [bohman_prime_sum_eq_phaseForm]
  have hleft_ub := bohman_budget_left_bounds'.2
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, ⟨hl19a, hl19b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  obtain ⟨⟨cb_2_1_l, -⟩, ⟨cb_2_2_l, cb_2_2_u⟩, ⟨cb_2_3_l, cb_2_3_u⟩, ⟨cb_2_4_l, -⟩, ⟨cb_2_5_l, cb_2_5_u⟩, ⟨cb_2_6_l, cb_2_6_u⟩, ⟨cb_3_1_l, -⟩, ⟨cb_3_2_l, -⟩, ⟨cb_3_3_l, cb_3_3_u⟩, ⟨cb_3_4_l, cb_3_4_u⟩, ⟨cb_5_1_l, -⟩, ⟨cb_5_2_l, cb_5_2_u⟩, ⟨cb_7_1_l, -⟩, ⟨cb_7_2_l, cb_7_2_u⟩, ⟨cb_11_1_l, -⟩, ⟨cb_13_1_l, -⟩, ⟨cb_17_1_l, cb_17_1_u⟩, ⟨cb_19_1_l, -⟩, ⟨cb_23_1_l, cb_23_1_u⟩, ⟨cb_29_1_l, cb_29_1_u⟩, ⟨cb_31_1_l, cb_31_1_u⟩, ⟨cb_37_1_l, cb_37_1_u⟩, ⟨cb_41_1_l, cb_41_1_u⟩, ⟨cb_43_1_l, cb_43_1_u⟩, ⟨cb_47_1_l, cb_47_1_u⟩, ⟨cb_53_1_l, cb_53_1_u⟩, ⟨cb_59_1_l, cb_59_1_u⟩, ⟨cb_61_1_l, cb_61_1_u⟩, ⟨cb_67_1_l, cb_67_1_u⟩, ⟨cb_71_1_l, cb_71_1_u⟩, ⟨cb_73_1_l, cb_73_1_u⟩, ⟨cb_79_1_l, cb_79_1_u⟩, ⟨cb_83_1_l, cb_83_1_u⟩, ⟨cb_89_1_l, cb_89_1_u⟩⟩ := all_prime_bohman_coeff_bounds'
  have hcu_0 : Real.cos ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ)) ≤ (-0.7982) := by rw [show ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ)) = 150.5 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.6462) 16 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl2a) (by simpa only [Nat.cast_ofNat] using hl2b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_0 : Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) * Real.cos ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ)) ≤ (-0.247143) := by nlinarith only [cb_2_1_l, hcu_0]
  have hcu_1 : Real.cos (2 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.2754 := by rw [show (2 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 301 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 301) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 1.8496) 33 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl2a) (by simpa only [Nat.cast_ofNat] using hl2b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_1 : Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.031241 := by nlinarith only [cb_2_2_l, cb_2_2_u, hcu_1]
  have hcu_2 : Real.cos (3 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.3595 := by rw [show (3 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 451.5 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 451.5) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 1.9384) 49 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl2a) (by simpa only [Nat.cast_ofNat] using hl2b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_2 : Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) * Real.cos (3 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.011836 := by nlinarith only [cb_2_3_l, cb_2_3_u, hcu_2]
  have hcu_3 : Real.cos (4 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ (-0.8485) := by rw [show (4 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) = 602 * Real.log ((2 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 602) (lp := Real.log ((2 : ℕ) : ℝ)) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.5574) 66 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl2a) (by simpa only [Nat.cast_ofNat] using hl2b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_3 : Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) * Real.cos (4 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ (-0.005894) := by nlinarith only [cb_2_4_l, hcu_3]
  have ht_4 : Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) * Real.cos (5 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.0008210 := mul_cos_le_ub (by linarith only [cb_2_5_l]) cb_2_5_u
  have ht_5 : Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) * Real.cos (6 * ((301 / 2 : ℝ) * Real.log ((2 : ℕ) : ℝ))) ≤ 0.0000155 := mul_cos_le_ub (by linarith only [cb_2_6_l]) cb_2_6_u
  have hcu_6 : Real.cos ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ)) ≤ (-0.3961) := by rw [show ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ)) = 150.5 * Real.log ((3 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((3 : ℕ) : ℝ)) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (s_hi := 1.1634) 26 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl3a) (by simpa only [Nat.cast_ofNat] using hl3b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_6 : Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) * Real.cos ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ)) ≤ (-0.110814) := by nlinarith only [cb_3_1_l, hcu_6]
  have hcu_7 : Real.cos (2 * ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ (-0.6854) := by rw [show (2 * ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ))) = 301 * Real.log ((3 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 301) (lp := Real.log ((3 : ℕ) : ℝ)) (lp_lo := 1.0986121) (lp_hi := 1.0986129) (s_hi := 0.8154) 52 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl3a) (by simpa only [Nat.cast_ofNat] using hl3b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_7 : Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ (-0.02817) := by nlinarith only [cb_3_2_l, hcu_7]
  have ht_8 : Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) * Real.cos (3 * ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ 0.0023895 := mul_cos_le_ub (by linarith only [cb_3_3_l]) cb_3_3_u
  have ht_9 : Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) * Real.cos (4 * ((301 / 2 : ℝ) * Real.log ((3 : ℕ) : ℝ))) ≤ 0.0000006 := mul_cos_le_ub (by linarith only [cb_3_4_l]) cb_3_4_u
  have hcu_10 : Real.cos ((301 / 2 : ℝ) * Real.log ((5 : ℕ) : ℝ)) ≤ (-0.9497) := by rw [show ((301 / 2 : ℝ) * Real.log ((5 : ℕ) : ℝ)) = 150.5 * Real.log ((5 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((5 : ℕ) : ℝ)) (lp_lo := 1.6094379) (lp_hi := 1.609438) (s_hi := 0.3179) 38 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl5a) (by simpa only [Nat.cast_ofNat] using hl5b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_10 : Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) * Real.cos ((301 / 2 : ℝ) * Real.log ((5 : ℕ) : ℝ)) ≤ (-0.172503) := by nlinarith only [cb_5_1_l, hcu_10]
  have ht_11 : Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log ((5 : ℕ) : ℝ))) ≤ 0.0045154 := mul_cos_le_ub (by linarith only [cb_5_2_l]) cb_5_2_u
  have hcu_12 : Real.cos ((301 / 2 : ℝ) * Real.log ((7 : ℕ) : ℝ)) ≤ (-0.7701) := by rw [show ((301 / 2 : ℝ) * Real.log ((7 : ℕ) : ℝ)) = 150.5 * Real.log ((7 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((7 : ℕ) : ℝ)) (lp_lo := 1.945908) (lp_hi := 1.9459107) (s_hi := 0.6916) 46 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl7a) (by simpa only [Nat.cast_ofNat] using hl7b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_12 : Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) * Real.cos ((301 / 2 : ℝ) * Real.log ((7 : ℕ) : ℝ)) ≤ (-0.092154) := by nlinarith only [cb_7_1_l, hcu_12]
  have ht_13 : Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log ((7 : ℕ) : ℝ))) ≤ 0.0003188 := mul_cos_le_ub (by linarith only [cb_7_2_l]) cb_7_2_u
  have hcu_14 : Real.cos ((301 / 2 : ℝ) * Real.log ((11 : ℕ) : ℝ)) ≤ (-0.9209) := by rw [show ((301 / 2 : ℝ) * Real.log ((11 : ℕ) : ℝ)) = 150.5 * Real.log ((11 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((11 : ℕ) : ℝ)) (lp_lo := 2.3978948) (lp_hi := 2.397896) (s_hi := 0.4001) 57 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl11a) (by simpa only [Nat.cast_ofNat] using hl11b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_14 : Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) * Real.cos ((301 / 2 : ℝ) * Real.log ((11 : ℕ) : ℝ)) ≤ (-0.053872) := by nlinarith only [cb_11_1_l, hcu_14]
  have hcu_15 : Real.cos ((301 / 2 : ℝ) * Real.log ((13 : ℕ) : ℝ)) ≤ (-0.9243) := by rw [show ((301 / 2 : ℝ) * Real.log ((13 : ℕ) : ℝ)) = 150.5 * Real.log ((13 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((13 : ℕ) : ℝ)) (lp_lo := 2.5649491) (lp_hi := 2.5649502) (s_hi := 0.3912) 61 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl13a) (by simpa only [Nat.cast_ofNat] using hl13b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_15 : Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) * Real.cos ((301 / 2 : ℝ) * Real.log ((13 : ℕ) : ℝ)) ≤ (-0.039478) := by nlinarith only [cb_13_1_l, hcu_15]
  have ht_16 : Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) * Real.cos ((301 / 2 : ℝ) * Real.log ((17 : ℕ) : ℝ)) ≤ 0.0242863 := mul_cos_le_ub (by linarith only [cb_17_1_l]) cb_17_1_u
  have hcu_17 : Real.cos ((301 / 2 : ℝ) * Real.log ((19 : ℕ) : ℝ)) ≤ (-0.9848) := by rw [show ((301 / 2 : ℝ) * Real.log ((19 : ℕ) : ℝ)) = 150.5 * Real.log ((19 : ℕ) : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp := Real.log ((19 : ℕ) : ℝ)) (lp_lo := 2.9444385) (lp_hi := 2.9444403) (s_hi := 0.1739) 70 (by norm_num) (by simpa only [Nat.cast_ofNat] using hl19a) (by simpa only [Nat.cast_ofNat] using hl19b) (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_17 : Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) * Real.cos ((301 / 2 : ℝ) * Real.log ((19 : ℕ) : ℝ)) ≤ (-0.018334) := by nlinarith only [cb_19_1_l, hcu_17]
  have ht_18 : Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) * Real.cos ((301 / 2 : ℝ) * Real.log ((23 : ℕ) : ℝ)) ≤ 0.0114201 := mul_cos_le_ub (by linarith only [cb_23_1_l]) cb_23_1_u
  have ht_19 : Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) * Real.cos ((301 / 2 : ℝ) * Real.log ((29 : ℕ) : ℝ)) ≤ 0.0057307 := mul_cos_le_ub (by linarith only [cb_29_1_l]) cb_29_1_u
  have ht_20 : Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) * Real.cos ((301 / 2 : ℝ) * Real.log ((31 : ℕ) : ℝ)) ≤ 0.0045883 := mul_cos_le_ub (by linarith only [cb_31_1_l]) cb_31_1_u
  have ht_21 : Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) * Real.cos ((301 / 2 : ℝ) * Real.log ((37 : ℕ) : ℝ)) ≤ 0.0023836 := mul_cos_le_ub (by linarith only [cb_37_1_l]) cb_37_1_u
  have ht_22 : Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) * Real.cos ((301 / 2 : ℝ) * Real.log ((41 : ℕ) : ℝ)) ≤ 0.0015452 := mul_cos_le_ub (by linarith only [cb_41_1_l]) cb_41_1_u
  have ht_23 : Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) * Real.cos ((301 / 2 : ℝ) * Real.log ((43 : ℕ) : ℝ)) ≤ 0.0012449 := mul_cos_le_ub (by linarith only [cb_43_1_l]) cb_43_1_u
  have ht_24 : Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) * Real.cos ((301 / 2 : ℝ) * Real.log ((47 : ℕ) : ℝ)) ≤ 0.0008002 := mul_cos_le_ub (by linarith only [cb_47_1_l]) cb_47_1_u
  have ht_25 : Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) * Real.cos ((301 / 2 : ℝ) * Real.log ((53 : ℕ) : ℝ)) ≤ 0.0003977 := mul_cos_le_ub (by linarith only [cb_53_1_l]) cb_53_1_u
  have ht_26 : Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) * Real.cos ((301 / 2 : ℝ) * Real.log ((59 : ℕ) : ℝ)) ≤ 0.0001869 := mul_cos_le_ub (by linarith only [cb_59_1_l]) cb_59_1_u
  have ht_27 : Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) * Real.cos ((301 / 2 : ℝ) * Real.log ((61 : ℕ) : ℝ)) ≤ 0.0001440 := mul_cos_le_ub (by linarith only [cb_61_1_l]) cb_61_1_u
  have ht_28 : Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) * Real.cos ((301 / 2 : ℝ) * Real.log ((67 : ℕ) : ℝ)) ≤ 0.0000588 := mul_cos_le_ub (by linarith only [cb_67_1_l]) cb_67_1_u
  have ht_29 : Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) * Real.cos ((301 / 2 : ℝ) * Real.log ((71 : ℕ) : ℝ)) ≤ 0.0000294 := mul_cos_le_ub (by linarith only [cb_71_1_l]) cb_71_1_u
  have ht_30 : Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) * Real.cos ((301 / 2 : ℝ) * Real.log ((73 : ℕ) : ℝ)) ≤ 0.0000197 := mul_cos_le_ub (by linarith only [cb_73_1_l]) cb_73_1_u
  have ht_31 : Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) * Real.cos ((301 / 2 : ℝ) * Real.log ((79 : ℕ) : ℝ)) ≤ 0.0000045 := mul_cos_le_ub (by linarith only [cb_79_1_l]) cb_79_1_u
  have ht_32 : Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) * Real.cos ((301 / 2 : ℝ) * Real.log ((83 : ℕ) : ℝ)) ≤ 0.0000011 := mul_cos_le_ub (by linarith only [cb_83_1_l]) cb_83_1_u
  have ht_33 : Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) * Real.cos ((301 / 2 : ℝ) * Real.log ((89 : ℕ) : ℝ)) ≤ 0.0000001 := mul_cos_le_ub (by linarith only [cb_89_1_l]) cb_89_1_u
  have hlog_rev : 2 * Real.log 3 + 4 * Real.log 5 + 637 / 90637 ≤
      Real.log (9 / 4 + (301 / 2 : ℝ) ^ 2 / 4) := by
    have heq : (9 / 4 + (301 / 2 : ℝ) ^ 2 / 4) = (3 ^ 2 * 5 ^ 4 : ℝ) * (90637 / 90000) := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 90000 / 90637 by norm_num)
    have hinv_eq : Real.log (90637 / 90000 : ℝ) = -Real.log (90000 / 90637) := by
      rw [← Real.log_inv]; norm_num
    rw [hinv_eq]; norm_num at hinv ⊢; linarith only [hinv]
  have hlog_pi_ub : Real.log Real.pi ≤ 38 / 23 * 0.6931471808 := by
    have hpow : Real.pi ^ 23 ≤ (2 : ℝ) ^ 38 :=
      (pow_le_pow_left₀ Real.pi_pos.le pi_bounds_d10'.2.le 23).trans (by norm_num)
    have h := log_le_of_pow_le_two_pow' Real.pi_pos (k := 23) (m := 38) (by norm_num) hpow
    norm_num at h ⊢; linarith only [h, hl2b]
  unfold bohmanPhaseForm
  linarith only [hleft_ub, hlog_rev, hlog_pi_ub, hl3a, hl5a, ht_0, ht_1, ht_2, ht_3, ht_4, ht_5, ht_6, ht_7, ht_8, ht_9, ht_10, ht_11, ht_12, ht_13, ht_14, ht_15, ht_16, ht_17, ht_18, ht_19, ht_20, ht_21, ht_22, ht_23, ht_24, ht_25, ht_26, ht_27, ht_28, ht_29, ht_30, ht_31, ht_32, ht_33]

/-- **Universal finite-band ceiling law:** for **every** band `L > 0` and finite prime cutoff `N`,
there exists a threshold `T_max > 0` above which the coupled Bohman explicit-formula inequality
strictly reverses at **every** real height `γ ≥ T_max` (even without the positive `O(1/1215 + 1/γ²)`
archimedean constants). Consequently, no fixed-band compactly supported positive-definite test can
certify all heights without sending `L → ∞`. -/
theorem bohman_any_band_eventually_reverses (L : ℝ) (hL : 0 < L) (N : ℕ) :
    ∃ T_max : ℝ, 0 < T_max ∧ ∀ γ : ℝ, T_max ≤ γ →
      4 * L ^ 2 / (L ^ 2 + 4 * Real.pi ^ 2) +
          64 * Real.pi ^ 2 * L * (1 + Real.exp (-(L / 2))) /
            (L ^ 2 + 4 * Real.pi ^ 2) ^ 2 <
        1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 -
          ∑ n ∈ Finset.range N,
            vonMangoldt n / n * bohmanFn L (Real.log n) * Real.cos (γ * Real.log n) := by
  set C_lhs : ℝ := 4 * L ^ 2 / (L ^ 2 + 4 * Real.pi ^ 2) +
    64 * Real.pi ^ 2 * L * (1 + Real.exp (-(L / 2))) / (L ^ 2 + 4 * Real.pi ^ 2) ^ 2
  set B_N : ℝ := ∑ n ∈ Finset.range N, vonMangoldt n / (n : ℝ)
  set M_req : ℝ := C_lhs + Real.log Real.pi / 2 + B_N + 1
  set T_max : ℝ := max 1 (2 * Real.exp (2 * M_req))
  refine ⟨T_max, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun γ hγ => ?_⟩
  have hγ_exp : 2 * Real.exp (2 * M_req) ≤ γ := (le_max_right _ _).trans hγ
  have hsum_le : ∑ n ∈ Finset.range N,
      vonMangoldt n / (n : ℝ) * bohmanFn L (Real.log n) * Real.cos (γ * Real.log n) ≤ B_N := by
    refine Finset.sum_le_sum fun n _ => ?_
    have hv0 : 0 ≤ vonMangoldt n / (n : ℝ) := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    have hw_nn : 0 ≤ bohmanFn L (Real.log n) := bohmanFn_nonneg hL _
    have hw_le1 : bohmanFn L (Real.log n) ≤ 1 := bohmanFn_le_one hL _
    have hcos_le1 : Real.cos (γ * Real.log n) ≤ 1 := Real.cos_le_one _
    calc vonMangoldt n / (n : ℝ) * bohmanFn L (Real.log n) * Real.cos (γ * Real.log n)
        ≤ vonMangoldt n / (n : ℝ) * bohmanFn L (Real.log n) * 1 :=
          mul_le_mul_of_nonneg_left hcos_le1 (mul_nonneg hv0 hw_nn)
      _ ≤ vonMangoldt n / (n : ℝ) * 1 * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw_le1 hv0) zero_le_one
      _ = vonMangoldt n / (n : ℝ) := by ring
  have hsq : Real.exp (4 * M_req) < 9 / 4 + γ ^ 2 / 4 := by
    have h1 : Real.exp (2 * M_req) ^ 2 ≤ (γ / 2) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) 2
    have h2 : Real.exp (2 * M_req) ^ 2 = Real.exp (4 * M_req) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2] at h1; linarith
  have hlog : 4 * M_req < Real.log (9 / 4 + γ ^ 2 / 4) := by
    rw [← Real.log_exp (4 * M_req)]
    exact Real.log_lt_log (Real.exp_pos _) hsq
  dsimp only [M_req] at hlog
  linarith only [hsum_le, hlog]

/-! ## Upgraded Pólya frequency, slice, Li, and Jensen rungs at height `150` -/

/-- At verified height `150`, the Taylor coefficients of `ξ` at the centre form a `PF_449` sequence
(upgraded from `PF_252` at height `84.5`). -/
theorem xi_centre_pfSeq_fourHundredFortyNine :
    PFSeq 449 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_rhVerifiedThrough (T := 150) (by norm_num)
    rhVerifiedThrough_oneHundredFifty (by norm_num) (by norm_num)

/-- Every Taylor coefficient of `ξ(1/2 + x + i t) ξ(1/2 - x + i t)` is nonnegative on `|t| ≤ 299/2`
(upgraded from `|t| ≤ 84` at height `84.5`). -/
theorem xiSliceCoeff_nonneg_of_abs_le_twoHundredNinetyNine_halves {t : ℝ} (ht : |t| ≤ 299 / 2)
    (n : ℕ) : 0 ≤ xiSliceCoeff t n :=
  xiSliceCoeff_nonneg_of_rhVerifiedThrough (T := 150) (t := t) (by linarith only [ht])
    rhVerifiedThrough_oneHundredFifty n

/-- The Li coefficients satisfy `Re(2 λ_n) ≥ 0` for all `n ≤ 705` (upgraded from `n ≤ 397` at
height `84.5`). -/
theorem re_xiLiPaired_nonneg_of_le_sevenHundredFive {n : ℕ} (hn : n ≤ 705) :
    0 ≤ (xiLiPaired n).re := by
  have hn' : (n : ℝ) ≤ 705 := by exact_mod_cast hn
  exact re_xiLiPaired_nonneg_of_rhVerifiedThrough (T := 150) (by norm_num)
    rhVerifiedThrough_oneHundredFifty (by linarith only [hn'])

/-- Exact largest Jensen degree paid by width `8999/24000` at coupled Bohman verified height `150`. -/
theorem jensen_sector_at_oneHundredFifty_iff (d : ℕ) :
    ((d : ℝ) - 1) * (8999 / 24000 : ℝ) ^ 2 ≤ 150 ^ 2 ↔ d ≤ 160036 := by
  constructor
  · intro h
    by_contra! hd
    have hn : 160037 ≤ d := by omega
    have h' : (160037 : ℝ) ≤ d := by exact_mod_cast hn
    norm_num at h ⊢
    linarith
  · intro h
    have h' : (d : ℝ) ≤ 160036 := by exact_mod_cast h
    norm_num
    linarith

/-- Unshifted `Ξ` Jensen polynomials have only real zeros through degree `160,036` (upgraded from
`50,787` at height `84.5`). -/
theorem jensenNonrealCount_eq_zero_through_160036 (d : Fin 160037) :
    jensenNonrealCount d.val = 0 := by
  apply jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width (T := 150) (by norm_num)
    rhVerifiedThrough_oneHundredFifty
  have h := (jensen_sector_at_oneHundredFifty_iff d).2 (by omega)
  rcases le_or_gt ((d.val : ℝ) - 1) 0 with hd | hd
  · exact (mul_nonpos_of_nonpos_of_nonneg hd (sq_nonneg _)).trans (sq_nonneg _)
  · exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ _root_.GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
        zetaZeroWidth_le_8999_div_24000 2) hd.le).trans h

/-- All positive-integer Euler root filters preserve real-rootedness of `xiJensenReal` through
degree `160,036` (upgraded from `50,787`). -/
theorem weightedXiJensen_splits_through_160036 (w : List ℕ) (d : Fin 160037) :
    (eulerWord w (xiJensenReal d.val)).Splits := by
  have h := weightedXiJensen_nonreal_le w d
  rw [jensenNonrealCount_eq_zero_through_160036 d, nonrealRootCount] at h
  have hc := Polynomial.card_roots' (eulerWord w (xiJensenReal d))
  rw [splits_iff_card_roots]
  omega

#print axioms rhVerifiedThrough_oneHundredFifty
#print axioms bohman_coupled_saturates_at_threeHundredOne_halves
#print axioms bohman_any_band_eventually_reverses
#print axioms xi_centre_pfSeq_fourHundredFortyNine
#print axioms xiSliceCoeff_nonneg_of_abs_le_twoHundredNinetyNine_halves
#print axioms re_xiLiPaired_nonneg_of_le_sevenHundredFive
#print axioms jensenNonrealCount_eq_zero_through_160036
#print axioms weightedXiJensen_splits_through_160036

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
