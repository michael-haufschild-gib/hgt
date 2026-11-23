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
  positive-integer Euler root filters through degree `160,037`.
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

private theorem cosPoly10_le_cos_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
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
  have h10 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - cosPoly10 x :=
    fun x hx => nonneg_of_deriv_nonneg' (by unfold cosPoly10; norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub
          (hasDerivAt_monomial_div' 6 720 y)).add
          (hasDerivAt_monomial_div' 8 40320 y)).sub
          (hasDerivAt_monomial_div' 10 3628800 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h9 y hy) hx
  exact sub_nonneg.mp (h10 u hu)

theorem cosPoly10_le_cos (x : ℝ) : cosPoly10 x ≤ Real.cos x := by
  rcases le_or_gt 0 x with hx | hx
  · exact cosPoly10_le_cos_of_nonneg hx
  · have hneg : cosPoly10 (-x) = cosPoly10 x := by unfold cosPoly10; ring
    rw [← hneg, ← Real.cos_neg]
    exact cosPoly10_le_cos_of_nonneg (by linarith only [hx])

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
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
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
  rw [cos_abs_eq, d, cos_sub_nat_mul_two_pi] at hcos_mono
  exact hu.trans ((cosPoly10_le_cos x_hi).trans hcos_mono)

private theorem cos_mul_le_of_odd_shift {c lp lp_lo lp_hi s_hi u_hi : ℝ} (m : ℕ)
    (hc0 : 0 ≤ c) (hlp0 : 0 ≤ lp_lo) (hlp_lo : lp_lo ≤ lp) (hlp_hi : lp ≤ lp_hi)
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
  rw [cos_abs_eq, d, cos_sub_odd_mul_pi] at hcos_mono
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
      ((((hasDerivAt_pow 4 u).const_mul 8).sub
        (((hasDerivAt_pow 2 u).const_mul 8).sub (hasDerivAt_const u 1))).const_mul D)).add
      ((((((hasDerivAt_pow 5 u).const_mul 16).sub
        ((hasDerivAt_pow 3 u).const_mul 20)).add
        ((hasDerivAt_id u).const_mul 5))).const_mul E)).add
      (((((((hasDerivAt_pow 6 u).const_mul 32).sub
        ((hasDerivAt_pow 4 u).const_mul 48)).add
        ((hasDerivAt_pow 2 u).const_mul 18)).sub
        (hasDerivAt_const u 1))).const_mul G) |>.congr_deriv ?_
  dsimp only [id]
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
  have hu' : u ∈ Icc (-1) 1 := interior_subset hu
  obtain ⟨hu0, hu1⟩ := hu'
  have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
  have he_lb : -((25 / 4) * E_hi) ≤ E * (80 * u ^ 4 - 60 * u ^ 2 + 5) := by
    have hid : 80 * u ^ 4 - 60 * u ^ 2 + 5 + 25 / 4 = 5 * (4 * u ^ 2 - 3 / 2) ^ 2 := by ring
    have hge : -(25 / 4 : ℝ) ≤ 80 * u ^ 4 - 60 * u ^ 2 + 5 := by
      nlinarith only [hid, sq_nonneg (4 * u ^ 2 - 3 / 2)]
    nlinarith only [hge, hE0, hE]
  have hg_lb : -(228 * G_hi) ≤ G * (192 * u ^ 5 - 192 * u ^ 3 + 36 * u) := by
    have hu3_lo : -1 ≤ u ^ 3 := by
      have : 0 ≤ (u + 1) * (u ^ 2 - u + 1) :=
        mul_nonneg (by linarith only [hu0]) (by nlinarith only [sq_nonneg (u - 1 / 2)])
      linarith [show (u + 1) * (u ^ 2 - u + 1) = u ^ 3 + 1 by ring]
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

private theorem weighted_sign_ub {c_lo c_hi c t : ℝ} (hlo : c_lo ≤ c) (hhi : c ≤ c_hi) :
    c * t ≤ c_hi * max t 0 + c_lo * min t 0 := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, min_eq_right ht]; nlinarith only [hhi, ht]
  · rw [max_eq_right ht, min_eq_left ht]; nlinarith only [hlo, ht]

/-! ## Tightened logarithm and Bohman harmonic enclosures -/

private theorem le_log_of_two_pow_le' {p : ℝ} {k m : ℕ} (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ p ^ k) : (m : ℝ) / k * Real.log 2 ≤ Real.log p := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith only [hl]

private theorem log_le_of_pow_le_two_pow' {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : p ^ k ≤ (2 : ℝ) ^ m) : Real.log p ≤ (m : ℝ) / k * Real.log 2 := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']
  linarith only [hl]

private theorem log_prime_bounds' {p : ℝ} (hp : 0 < p) {k1 m1 k2 m2 : ℕ}
    (hk1 : 0 < k1) (hk2 : 0 < k2) (h1 : (2 : ℝ) ^ m1 ≤ p ^ k1) (h2 : p ^ k2 ≤ (2 : ℝ) ^ m2)
    {lo hi : ℝ} (hlo : lo ≤ (m1 : ℝ) / k1 * 0.6931471803)
    (hhi : (m2 : ℝ) / k2 * 0.6931471808 ≤ hi) :
    lo ≤ Real.log p ∧ Real.log p ≤ hi := by
  have hb1 := le_log_of_two_pow_le' hk1 h1
  have hb2 := log_le_of_pow_le_two_pow' hp hk2 h2
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hpos1 : 0 ≤ (m1 : ℝ) / k1 := by positivity
  have hpos2 : 0 ≤ (m2 : ℝ) / k2 := by positivity
  exact ⟨hlo.trans ((mul_le_mul_of_nonneg_left hl2a.le hpos1).trans hb1),
    hb2.trans ((mul_le_mul_of_nonneg_left hl2b.le hpos2).trans hhi)⟩

private theorem sharp_log_prime_bounds :
    (1.0985728 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0986619) ∧
    (1.6094307 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.6095113) ∧
    (1.9458994 ≤ Real.log 7 ∧ Real.log 7 ≤ 1.9459466) ∧
    (2.3977758 ≤ Real.log 11 ∧ Real.log 11 ≤ 2.3979146) ∧
    (2.5646445 ≤ Real.log 13 ∧ Real.log 13 ≤ 2.5650861) ∧
    (2.8331549 ≤ Real.log 17 ∧ Real.log 17 ≤ 2.8332392) ∧
    (2.9443944 ≤ Real.log 19 ∧ Real.log 19 ≤ 2.9444434) ∧
    (3.1354442 ≤ Real.log 23 ∧ Real.log 23 ≤ 3.1356659) ∧
    (3.3667148 ≤ Real.log 29 ∧ Real.log 29 ≤ 3.3673538) ∧
    (3.4339401 ≤ Real.log 31 ∧ Real.log 31 ≤ 3.4339888) ∧
    (3.6108132 ≤ Real.log 37 ∧ Real.log 37 ≤ 3.6109222) ∧
    (3.7132884 ≤ Real.log 41 ∧ Real.log 41 ≤ 3.7136164) ∧
    (3.7611756 ≤ Real.log 43 ∧ Real.log 43 ≤ 3.7612638) ∧
    (3.8501175 ≤ Real.log 47 ∧ Real.log 47 ≤ 3.8501705) ∧
    (3.9698429 ≤ Real.log 53 ∧ Real.log 53 ≤ 3.970911) ∧
    (4.0773363 ≤ Real.log 59 ∧ Real.log 59 ≤ 4.0782846) ∧
    (4.1105239 ≤ Real.log 61 ∧ Real.log 61 ≤ 4.1110799) ∧
    (4.2040883 ≤ Real.log 67 ∧ Real.log 67 ≤ 4.2050929) ∧
    (4.2621177 ≤ Real.log 71 ∧ Real.log 71 ≤ 4.2628552) ∧
    (4.290342 ≤ Real.log 73 ∧ Real.log 73 ≤ 4.2909112) ∧
    (4.3693027 ≤ Real.log 79 ∧ Real.log 79 ≤ 4.369841) ∧
    (4.4188132 ≤ Real.log 83 ∧ Real.log 83 ≤ 4.4204481) ∧
    (4.4881279 ≤ Real.log 89 ∧ Real.log 89 ≤ 4.4889532) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact log_prime_bounds' (p := 3) (by norm_num) (k1 := 53) (m1 := 84) (k2 := 147) (m2 := 233) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 1.0985728) (hi := 1.0986619) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 5) (by norm_num) (k1 := 146) (m1 := 339) (k2 := 59) (m2 := 137) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 1.6094307) (hi := 1.6095113) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 7) (by norm_num) (k1 := 109) (m1 := 306) (k2 := 135) (m2 := 379) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 1.9458994) (hi := 1.9459466) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 11) (by norm_num) (k1 := 135) (m1 := 467) (k2 := 37) (m2 := 128) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 2.3977758) (hi := 2.3979146) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 13) (by norm_num) (k1 := 10) (m1 := 37) (k2 := 157) (m2 := 581) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 2.5646445) (hi := 2.5650861) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 17) (by norm_num) (k1 := 103) (m1 := 421) (k2 := 80) (m2 := 327) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 2.8331549) (hi := 2.8332392) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 19) (by norm_num) (k1 := 117) (m1 := 497) (k2 := 121) (m2 := 514) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 2.9443944) (hi := 2.9444434) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 23) (by norm_num) (k1 := 149) (m1 := 674) (k2 := 21) (m2 := 95) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.1354442) (hi := 3.1356659) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 29) (by norm_num) (k1 := 7) (m1 := 34) (k2 := 155) (m2 := 753) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.3667148) (hi := 3.3673538) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 31) (by norm_num) (k1 := 109) (m1 := 540) (k2 := 131) (m2 := 649) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.4339401) (hi := 3.4339888) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 37) (by norm_num) (k1 := 43) (m1 := 224) (k2 := 148) (m2 := 771) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.6108132) (hi := 3.6109222) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 41) (by norm_num) (k1 := 14) (m1 := 75) (k2 := 151) (m2 := 809) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.7132884) (hi := 3.7136164) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 43) (by norm_num) (k1 := 61) (m1 := 331) (k2 := 129) (m2 := 700) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.7611756) (hi := 3.7612638) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 47) (by norm_num) (k1 := 110) (m1 := 611) (k2 := 119) (m2 := 661) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.8501175) (hi := 3.8501705) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 53) (by norm_num) (k1 := 11) (m1 := 63) (k2 := 59) (m2 := 338) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 3.9698429) (hi := 3.970911) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 59) (by norm_num) (k1 := 17) (m1 := 100) (k2 := 43) (m2 := 253) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.0773363) (hi := 4.0782846) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 61) (by norm_num) (k1 := 43) (m1 := 255) (k2 := 29) (m2 := 172) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.1105239) (hi := 4.1110799) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 67) (by norm_num) (k1 := 46) (m1 := 279) (k2 := 15) (m2 := 91) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.2040883) (hi := 4.2050929) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 71) (by norm_num) (k1 := 47) (m1 := 289) (k2 := 20) (m2 := 123) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.2621177) (hi := 4.2628552) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 73) (by norm_num) (k1 := 58) (m1 := 359) (k2 := 21) (m2 := 130) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.290342) (hi := 4.2909112) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 79) (by norm_num) (k1 := 56) (m1 := 353) (k2 := 23) (m2 := 145) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.3693027) (hi := 4.369841) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 83) (by norm_num) (k1 := 8) (m1 := 51) (k2 := 53) (m2 := 338) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.4188132) (hi := 4.4204481) (by norm_num) (by norm_num)
  · exact log_prime_bounds' (p := 89) (by norm_num) (k1 := 40) (m1 := 259) (k2 := 21) (m2 := 136) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (lo := 4.4881279) (hi := 4.4889532) (by norm_num) (by norm_num)

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

private theorem sin_taylor_bounds_of_nonneg' {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 ≤ Real.sin u ∧
      Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880 ∧
      u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880 - u ^ 11 / 39916800 ≤
        Real.sin u := by
  have h6 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) := by
    intro x hx
    have h1 : ∀ z : ℝ, 0 ≤ z → 0 ≤ z - Real.sin z := fun z hz =>
      nonneg_of_deriv_nonneg' (by simp)
        (fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y))
        (fun y _ => sub_nonneg.mpr (Real.cos_le_one y)) hz
    have h2 : ∀ z : ℝ, 0 ≤ z → 0 ≤ Real.cos z - (1 - z ^ 2 / 2) := fun z hz =>
      nonneg_of_deriv_nonneg' (by norm_num)
        (fun y => ((Real.hasDerivAt_cos y).sub
          ((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y))).congr_deriv
          (by norm_num; ring)) (fun y hy => h1 y hy) hz
    have h3 : ∀ z : ℝ, 0 ≤ z → 0 ≤ Real.sin z - (z - z ^ 3 / 6) := fun z hz =>
      nonneg_of_deriv_nonneg' (by norm_num)
        (fun y => ((Real.hasDerivAt_sin y).sub
          ((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y))).congr_deriv
          (by norm_num; ring)) (fun y hy => h2 y hy) hz
    have h4 : ∀ z : ℝ, 0 ≤ z → 0 ≤ 1 - z ^ 2 / 2 + z ^ 4 / 24 - Real.cos z := fun z hz =>
      nonneg_of_deriv_nonneg' (by norm_num)
        (fun y => ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
          (by norm_num; ring)) (fun y hy => h3 y hy) hz
    have h5 : ∀ z : ℝ, 0 ≤ z → 0 ≤ z - z ^ 3 / 6 + z ^ 5 / 120 - Real.sin z := fun z hz =>
      nonneg_of_deriv_nonneg' (by norm_num)
        (fun y => ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
          (hasDerivAt_monomial_div' 5 120 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
          (by norm_num; ring)) (fun y hy => h4 y hy) hz
    exact nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub
          (hasDerivAt_monomial_div' 6 720 y))).congr_deriv
        (by norm_num; ring)) (fun y hy => h5 y hy) hx
  have h7 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
          (hasDerivAt_monomial_div' 5 120 y)).sub
          (hasDerivAt_monomial_div' 7 5040 y))).congr_deriv
        (by norm_num; ring)) (fun y hy => h6 y hy) hx
  have h8 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div' 2 2 y)).add
          (hasDerivAt_monomial_div' 4 24 y)).sub
          (hasDerivAt_monomial_div' 6 720 y)).add
          (hasDerivAt_monomial_div' 8 40320 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring)) (fun y hy => h7 y hy) hx
  have h9 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
          (hasDerivAt_monomial_div' 5 120 y)).sub
          (hasDerivAt_monomial_div' 7 5040 y)).add
          (hasDerivAt_monomial_div' 9 362880 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring)) (fun y hy => h8 y hy) hx
  have h10 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - cosPoly10 x :=
    fun x hx => sub_nonneg.mpr (cosPoly10_le_cos_of_nonneg hx)
  have h11 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ Real.sin x -
        (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) :=
    fun x hx => nonneg_of_deriv_nonneg' (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((((hasDerivAt_id y).sub (hasDerivAt_monomial_div' 3 6 y)).add
          (hasDerivAt_monomial_div' 5 120 y)).sub
          (hasDerivAt_monomial_div' 7 5040 y)).add
          (hasDerivAt_monomial_div' 9 362880 y)).sub
          (hasDerivAt_monomial_div' 11 39916800 y))).congr_deriv
        (by unfold cosPoly10; norm_num; ring)) (fun y hy => h10 y hy) hx
  exact ⟨sub_nonneg.mp (h7 u hu), sub_nonneg.mp (h9 u hu), sub_nonneg.mp (h11 u hu)⟩

private theorem bohmanP9_P11_P13_bounds {u : ℝ} (hu : 0 ≤ u) :
    bohmanP9 u ≤ Real.sin u - u * Real.cos u ∧
      Real.sin u - u * Real.cos u ≤ bohmanP11 u ∧
      bohmanP13 u ≤ Real.sin u - u * Real.cos u := by
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
  have hd13 : ∀ x : ℝ, HasDerivAt bohmanP13
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800)) x :=
    fun x => by
      unfold bohmanP13
      refine ((hd11 x).sub (hasDerivAt_monomial_div' 13 518918400 x)).congr_deriv (by norm_num; ring)
  have hlo := nonneg_of_deriv_nonneg' (by simp [bohmanP9])
    (fun x => ((hasDerivAt_sin_sub_mul_cos' x).sub (hd9 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_taylor_bounds_of_nonneg' hx).1)) hu
  have hhi := nonneg_of_deriv_nonneg' (by simp [bohmanP11, bohmanP9])
    (fun x => ((hd11 x).sub (hasDerivAt_sin_sub_mul_cos' x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_taylor_bounds_of_nonneg' hx).2.1)) hu
  have hlo13 := nonneg_of_deriv_nonneg' (by simp [bohmanP13, bohmanP11, bohmanP9])
    (fun x => ((hasDerivAt_sin_sub_mul_cos' x).sub (hd13 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_taylor_bounds_of_nonneg' hx).2.2)) hu
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi, sub_nonneg.mp hlo13⟩

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
    (bohmanP9_P11_P13_bounds hu_lo0).1.trans
      (monotoneOn_sin_sub_mul_cos' ⟨hu_lo0, hu_ge_lo.trans hu_pi⟩ ⟨hu0, hu_pi⟩ hu_ge_lo)
  have hH_hi : Real.sin u - u * Real.cos u ≤ bohmanP11 u_hi :=
    (monotoneOn_sin_sub_mul_cos' ⟨hu0, hu_pi⟩ ⟨hu_lo0.trans (hu_ge_lo.trans hu_le_hi), hu_hi_lt_pi⟩
      hu_le_hi).trans (bohmanP9_P11_P13_bounds (hu_lo0.trans (hu_ge_lo.trans hu_le_hi))).2.1
  have hW_eq := bohmanFn_eq_sin_sub_mul_cos' (L := 9 / 2) (x := k * Real.log p) (by norm_num) hkx0 hkxL
  have hW_nonneg : 0 ≤ bohmanFn (9 / 2) (k * Real.log p) := bohmanFn_nonneg (by norm_num) _
  have hW_lo : bohmanP9 u_lo / 3.1415926536 ≤ bohmanFn (9 / 2) (k * Real.log p) := by
    rw [hW_eq]
    by_cases hp9 : 0 ≤ bohmanP9 u_lo
    · exact (div_le_div_of_nonneg_left hp9 hπ_pos hπ_hi.le).trans
        (div_le_div_of_nonneg_right hH_lo hπ_pos.le)
    · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp9) (by norm_num)).trans
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
    · exact (mul_nonpos_of_nonpos_of_nonneg (div_nonneg hlp0 hpk.le) (le_of_not_ge hw0)).trans
        (mul_nonneg (div_nonneg hlp_nonneg hpk.le) hW_nonneg)
  · exact (mul_le_mul (div_le_div_of_nonneg_right hlp_hi hpk.le) hW_hi hW_nonneg
      (div_nonneg (hlp_nonneg.trans hlp_hi) hpk.le)).trans h_chi

private theorem bohman_coeff_lb_p13' {p lp_lo lp_hi u_lo c_lo : ℝ}
    (hp : 0 < p) (hlp0 : 0 ≤ lp_lo)
    (hlp_lo : lp_lo ≤ Real.log p) (hlp_hi : Real.log p ≤ lp_hi)
    (hk_hi : 1 * lp_hi ≤ 9 / 2) (hu_lo0 : 0 ≤ u_lo)
    (hu_lo : u_lo ≤ 3.1415926535 * (1 - 1 * lp_hi / (9 / 2)))
    (h_clo : c_lo ≤ lp_lo / p * (bohmanP13 u_lo / 3.1415926536))
    (hp13_pos : 0 ≤ bohmanP13 u_lo) :
    c_lo ≤ Real.log p / p * bohmanFn (9 / 2) (1 * Real.log p) := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10'
  have hπ_pos := Real.pi_pos
  have hlp_nonneg : 0 ≤ Real.log p := hlp0.trans hlp_lo
  set u : ℝ := Real.pi * (1 - 1 * Real.log p / (9 / 2))
  have h1_lo : 0 ≤ 1 - 1 * lp_hi / (9 / 2) := by linarith
  have h1_le : 1 - 1 * lp_hi / (9 / 2) ≤ 1 - 1 * Real.log p / (9 / 2) := by linarith
  have hu_ge_lo : u_lo ≤ u := hu_lo.trans (mul_le_mul hπ_lo.le h1_le h1_lo hπ_pos.le)
  have hu0 : 0 ≤ u := hu_lo0.trans hu_ge_lo
  have hu_pi : u ≤ Real.pi := by
    dsimp only [u]; exact mul_le_of_le_one_right hπ_pos.le (by linarith)
  have hH_lo : bohmanP13 u_lo ≤ Real.sin u - u * Real.cos u :=
    (bohmanP9_P11_P13_bounds hu_lo0).2.2.trans
      (monotoneOn_sin_sub_mul_cos' ⟨hu_lo0, hu_ge_lo.trans hu_pi⟩ ⟨hu0, hu_pi⟩ hu_ge_lo)
  have hW_eq := bohmanFn_eq_sin_sub_mul_cos' (L := 9 / 2) (x := 1 * Real.log p)
    (by norm_num) (by linarith) (by linarith)
  have hW_lo : bohmanP13 u_lo / 3.1415926536 ≤ bohmanFn (9 / 2) (1 * Real.log p) := by
    rw [hW_eq]
    exact (div_le_div_of_nonneg_left hp13_pos hπ_pos hπ_hi.le).trans
      (div_le_div_of_nonneg_right hH_lo hπ_pos.le)
  exact h_clo.trans (mul_le_mul (div_le_div_of_nonneg_right hlp_lo hp.le) hW_lo
    (div_nonneg hp13_pos (by norm_num)) (div_nonneg hlp_nonneg hp.le))

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
  have hl2a := Real.log_two_gt_d9.le
  have hl2b := Real.log_two_lt_d9.le
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _,
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
  obtain ⟨⟨b2_1l, _⟩, ⟨b2_2l, b2_2u⟩, ⟨b2_3l, b2_3u⟩, ⟨b2_4l, b2_4u⟩, ⟨b2_5l, b2_5u⟩,
    ⟨b2_6l, b2_6u⟩, _⟩ := all_prime_bohman_coeff_bounds'
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
  obtain ⟨_, _, _, _, _, _, ⟨b3_1l, _⟩, ⟨b3_2l, b3_2u⟩, ⟨b3_3l, b3_3u⟩, ⟨b3_4l, b3_4u⟩, _⟩ :=
    all_prime_bohman_coeff_bounds'
  exact monotoneOn_chebPoly4_of_linear (by linarith only [b3_2l]) (by linarith only [b3_3l])
    (by linarith only [b3_4l]) (by linarith only [b3_1l, b3_2u, b3_3u, b3_4u])

private theorem monotoneOn_bohman5 :
    MonotoneOn (chebPoly6
      (Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5))
      (Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5)) 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨b5_1l, _⟩, ⟨b5_2l, b5_2u⟩, _⟩ :=
    all_prime_bohman_coeff_bounds'
  exact monotoneOn_chebPoly4_of_linear (by linarith only [b5_2l]) le_rfl le_rfl
    (by linarith only [b5_1l, b5_2u])

private theorem monotoneOn_bohman7 :
    MonotoneOn (chebPoly6
      (Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7))
      (Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7)) 0 0 0 0) (Icc (-1) 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨b7_1l, _⟩, ⟨b7_2l, b7_2u⟩, _⟩ :=
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
  obtain ⟨⟨b1l, b1u⟩, ⟨b2l, b2u⟩, ⟨b3l, b3u⟩, ⟨b4l, b4u⟩, ⟨b5l, b5u⟩, ⟨b6l, b6u⟩, _⟩ :=
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
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  have w3 := weighted_sign_lb b3l b3u (t := 4 * u_lo ^ 3 - 3 * u_lo)
  have w4 := weighted_sign_lb b4l b4u (t := 8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1)
  have w5 := weighted_sign_lb b5l b5u (t := 16 * u_lo ^ 5 - 20 * u_lo ^ 3 + 5 * u_lo)
  have w6 := weighted_sign_lb b6l b6u (t := 32 * u_lo ^ 6 - 48 * u_lo ^ 4 + 18 * u_lo ^ 2 - 1)
  unfold bohmanExcess; simp only [↓reduceIte]
  unfold chebPoly6 at hmono
  linarith only [hg, w1, w2, w3, w4, w5, w6, hmono, hterm]

private theorem bohmanExcess3_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.2797659 * max u_lo 0 + 0.2802868 * min u_lo 0) +
      (0.0411017 * max (2 * u_lo ^ 2 - 1) 0 + 0.0411443 * min (2 * u_lo ^ 2 - 1) 0) +
      (0.0023832 * max (4 * u_lo ^ 3 - 3 * u_lo) 0 + 0.0023895 * min (4 * u_lo ^ 3 - 3 * u_lo) 0) +
      (0.0000005 * max (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0 +
        0.0000006 * min (8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1) 0) -
      (-0.2802868 + 0.0411017 - 0.0023895 + 0.0000005)) :
    g ≤ bohmanExcess 3 θ := by
  obtain ⟨_, _, _, _, _, _, ⟨b1l, b1u⟩, ⟨b2l, b2u⟩, ⟨b3l, b3u⟩, ⟨b4l, b4u⟩, _⟩ :=
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
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  have w3 := weighted_sign_lb b3l b3u (t := 4 * u_lo ^ 3 - 3 * u_lo)
  have w4 := weighted_sign_lb b4l b4u (t := 8 * u_lo ^ 4 - 8 * u_lo ^ 2 + 1)
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  unfold chebPoly6 at hmono
  linarith only [hg, w1, w2, w3, w4, hmono, hterm]

private theorem bohmanExcess5_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.1816415 * max u_lo 0 + 0.1818962 * min u_lo 0) +
      (0.0044971 * max (2 * u_lo ^ 2 - 1) 0 + 0.0045154 * min (2 * u_lo ^ 2 - 1) 0) -
      (-0.1818962 + 0.0044971)) :
    g ≤ bohmanExcess 5 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨b1l, b1u⟩, ⟨b2l, b2u⟩, _⟩ :=
    all_prime_bohman_coeff_bounds'
  have c2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman5 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly6
      (Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5))
      (Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5)) 0 0 0 0 (Real.cos θ) = bohmanTerm5 θ := by
    unfold chebPoly6 bohmanTerm5; rw [c2]; ring
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  unfold chebPoly6 at hmono
  linarith only [hg, w1, w2, hmono, hterm]

private theorem bohmanExcess7_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤
      (0.1196666 * max u_lo 0 + 0.1198266 * min u_lo 0) +
      (0.0003159 * max (2 * u_lo ^ 2 - 1) 0 + 0.0003188 * min (2 * u_lo ^ 2 - 1) 0) -
      (-0.1198266 + 0.0003159)) :
    g ≤ bohmanExcess 7 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨b1l, b1u⟩, ⟨b2l, b2u⟩, _⟩ :=
    all_prime_bohman_coeff_bounds'
  have c2 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hu1 : u_lo ≤ 1 := hu.trans (Real.cos_le_one θ)
  have hmono := monotoneOn_bohman7 ⟨hu0, hu1⟩ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩ hu
  have hterm : chebPoly6
      (Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7))
      (Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7)) 0 0 0 0 (Real.cos θ) = bohmanTerm7 θ := by
    unfold chebPoly6 bohmanTerm7; rw [c2]; ring
  have w1 := weighted_sign_lb b1l b1u (t := u_lo)
  have w2 := weighted_sign_lb b2l b2u (t := 2 * u_lo ^ 2 - 1)
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  unfold chebPoly6 at hmono
  linarith only [hg, w1, w2, hmono, hterm]

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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess13_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0427132 * (1 + u_lo)) : g ≤ bohmanExcess 13 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess17_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0242427 * (1 + u_lo)) : g ≤ bohmanExcess 17 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess19_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0186189 * (1 + u_lo)) : g ≤ bohmanExcess 19 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess23_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0113990 * (1 + u_lo)) : g ≤ bohmanExcess 23 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess29_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0056981 * (1 + u_lo)) : g ≤ bohmanExcess 29 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess31_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0045777 * (1 + u_lo)) : g ≤ bohmanExcess 31 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess37_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0023761 * (1 + u_lo)) : g ≤ bohmanExcess 37 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess41_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0015372 * (1 + u_lo)) : g ≤ bohmanExcess 41 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess43_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0012316 * (1 + u_lo)) : g ≤ bohmanExcess 43 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
  unfold bohmanExcess; simp only [↓reduceIte, Nat.reduceEqDiff]
  exact linear_excess_ge (by norm_num) bl bu hu0 hu hg

private theorem bohmanExcess47_ge {u_lo g θ : ℝ} (hu0 : -1 ≤ u_lo) (hu : u_lo ≤ Real.cos θ)
    (hg : g ≤ 0.0007923 * (1 + u_lo)) : g ≤ bohmanExcess 47 θ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨bl, bu⟩, _⟩ := all_prime_bohman_coeff_bounds'
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
    (hlogM : (a2 : ℝ) * 0.6931471808 + (b : ℝ) * 1.0986619 +
      (c : ℝ) * 1.6095113 + (d : ℝ) * 1.9459466 ≤ logM4_hi)
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

/-! ## 42-interval coupled prime-phase exclusion across `(169/2, 150]` -/

private theorem bohman_interval_0 {γ : ℝ} (hlo : 84.5 ≤ γ) (hhi : γ ≤ 88.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 84.5) (g_hi := 88.140625) (M := 7840) (logM4_hi := 7.5808462) (ub := 1.321927) (a2 := 3) (b := 0) (c := 1) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.8516) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 84.5) (g_hi := 88.140625) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.5891) 15 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.02158 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.8516)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_1 {γ : ℝ} (hlo : 88.140625 ≤ γ) (hhi : γ ≤ 93.53125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 88.140625) (g_hi := 93.53125) (M := 8820) (logM4_hi := 7.6987284) (ub := 1.351589) (a2 := 0) (b := 2) (c := 1) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.4156) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 88.140625) (g_hi := 93.53125) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9992) 10 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.05078 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.4156)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_2 {γ : ℝ} (hlo : 93.53125 ≤ γ) (hhi : γ ≤ 95.234375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 93.53125) (g_hi := 95.234375) (M := 8960) (logM4_hi := 7.7143411) (ub := 1.360571) (a2 := 6) (b := 0) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.792) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 93.53125) (g_hi := 95.234375) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.4845) 24 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.03447 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.792)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5637) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 93.53125) (g_hi := 95.234375) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.1694) 36 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02551 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.5637)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn3, hn7, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_3 {γ : ℝ} (hlo : 95.234375 ≤ γ) (hhi : γ ≤ 96.96875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 95.234375) (g_hi := 96.96875) (M := 9408) (logM4_hi := 7.763144) (ub := 1.369564) (a2 := 4) (b := 1) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.5825) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 95.234375) (g_hi := 96.96875) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.1924) 17 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06735 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.5825)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9344) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 95.234375) (g_hi := 96.96875) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 2.7758) 45 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00121 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.9344)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9899) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 95.234375) (g_hi := 96.96875) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.991) 48 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0001 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.9899)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn11, hn13, hn17, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_4 {γ : ℝ} (hlo : 96.96875 ≤ γ) (hhi : γ ≤ 99.59375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 96.96875) (g_hi := 99.59375) (M := 9800) (logM4_hi := 7.8040631) (ub := 1.382949) (a2 := 1) (b := 0) (c := 2) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.325) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 96.96875) (g_hi := 99.59375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9016) 11 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06226 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.325)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8603) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 96.96875) (g_hi := 99.59375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.6059) 17 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02025 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.8603)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_5 {γ : ℝ} (hlo : 99.59375 ≤ γ) (hhi : γ ≤ 102.140625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 99.59375) (g_hi := 102.140625) (M := 10368) (logM4_hi := 7.8603837) (ub := 1.395538) (a2 := 5) (b := 4) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.1127) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 99.59375) (g_hi := 102.140625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.6836) 11 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09547 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.1127)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_6 {γ : ℝ} (hlo : 102.140625 ≤ γ) (hhi : γ ≤ 104.75) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 102.140625) (g_hi := 104.75) (M := 10976) (logM4_hi := 7.9172815) (ub := 1.408108) (a2 := 3) (b := 0) (c := 0) (d := 3) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.405) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 102.140625) (g_hi := 104.75) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.9876) 18 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10266 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.405)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.9345) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 102.140625) (g_hi := 104.75) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.7761) 32 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.00775 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9345)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_7 {γ : ℝ} (hlo : 104.75 ≤ γ) (hhi : γ ≤ 106.578125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 104.75) (g_hi := 106.578125) (M := 11520) (logM4_hi := 7.9657183) (ub := 1.416785) (a2 := 6) (b := 2) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.3166) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 104.75) (g_hi := 106.578125) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 1.8928) 27 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11619 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.3166)) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn2, hn3, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_8 {γ : ℝ} (hlo : 106.578125 ≤ γ) (hhi : γ ≤ 111.03125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 106.578125) (g_hi := 111.03125) (M := 12288) (logM4_hi := 8.0301339) (ub := 1.437183) (a2 := 10) (b := 1) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.0077 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 106.578125) (g_hi := 111.03125) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.5629) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11949 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.0077) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.86) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 106.578125) (g_hi := 111.03125) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.6054) 19 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02029 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.86)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_9 {γ : ℝ} (hlo : 111.03125 ≤ γ) (hhi : γ ≤ 111.375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, -, -, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, -, -, ⟨hl47a, hl47b⟩, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.03125) (g_hi := 111.375) (M := 12288) (logM4_hi := 8.0301339) (ub := 1.438732) (a2 := 10) (b := 1) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.2285) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8012) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.07613 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.2285)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.1768 ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.3929) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02851 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := 0.1768) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.3511 ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.2119) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02514 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := 0.3511) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.352 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 1.2109) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0032 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.352) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.4161) ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 1.9998) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00266 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := (-0.4161)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9886) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.9831) 19 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00156 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.9886)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.0143 ≤ Real.cos (γ * Real.log (47 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.03125) (g_hi := 111.375) (lp_lo := 3.8501175) (lp_hi := 3.8501705) (x_hi := 1.5563) 68 (by norm_num) hlo hhi (by norm_num) hl47a hl47b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00079 ≤ bohmanExcess 47 (γ * Real.log (47 : ℝ)) := bohmanExcess47_ge (u_lo := 0.0143) (by norm_num) hu_6 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn23, hn29, hn41, hn43, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6]

private theorem bohman_interval_10 {γ : ℝ} (hlo : 111.375 ≤ γ) (hhi : γ ≤ 111.4375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, -, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.375) (g_hi := 111.4375) (M := 12288) (logM4_hi := 8.0301339) (ub := 1.439015) (a2 := 10) (b := 1) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.2705) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8445) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06987 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.2705)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0006 ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.57) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02424 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := 0.0006) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.1739 ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.3959) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02184 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := 0.1739) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.6825 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.8194) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00769 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.6825) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.964 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 0.2684) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00465 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.964) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.4375) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 2.0234) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00319 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.4375)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.985) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.9622) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00245 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.985)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : 0.4329 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 1.1229) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00219 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.4329) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.8812) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.6484) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00134 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.8812)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.4812) ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.375) (g_hi := 111.4375) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 2.0726) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00062 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := (-0.4812)) (by norm_num) hu_9 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn11, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9]

private theorem bohman_interval_11 {γ : ℝ} (hlo : 111.4375 ≤ γ) (hhi : γ ≤ 111.46875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, -, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.4375) (g_hi := 111.46875) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.439155) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.2913) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8662) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.0669 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.2913)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0877) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.6585) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0221 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.0877)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : 0.0827 ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.4879) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02014 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := 0.0827) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.8225 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.6048) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00833 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.8225) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.9618) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.8616) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00626 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.9618)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.928 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 0.3813) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00457 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.928) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.24) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.813) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00432 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.24)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.7721) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.4525) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00258 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.7721)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.6286 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 0.8908) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00249 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.6286) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.2638) ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.4375) (g_hi := 111.46875) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.8376) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00089 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := (-0.2638)) (by norm_num) hu_9 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn11, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9]

private theorem bohman_interval_12 {γ : ℝ} (hlo : 111.46875 ≤ γ) (hhi : γ ≤ 111.5) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.46875) (g_hi := 111.5) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.439293) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.3119) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.8878) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06404 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.3119)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1755) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.7471) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01997 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.1755)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.0094) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.58) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01843 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.0094)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9466) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.8113) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00876 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.9466)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.8787 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.4974) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00859 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.8787) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.1367) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.7078) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0049 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.1367)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.8802 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 0.4941) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00445 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.8802) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.7061) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.3545) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00334 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.7061)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.7144 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 0.7748) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00262 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.7144) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.9718) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.9) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00163 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.9718)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.1488) ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.72) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00103 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := (-0.1488)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.9919) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.46875) (g_hi := 111.5) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 3.0047) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00095 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9919)) (by norm_num) hu_11 (by norm_num)
  linarith only [harch, hmaster, hn3, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11]

private theorem bohman_interval_13 {γ : ℝ} (hlo : 111.5 ≤ γ) (hhi : γ ≤ 111.53125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.5) (g_hi := 111.53125) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.439432) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.3324) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9095) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.06127 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.3324)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2619) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.8356) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01788 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.2619)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.1012) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.672) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01672 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.1012)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.929) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.761) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01167 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.929)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9247 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.3901) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.0088 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.9247) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.0319) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.6026) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0055 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.0319)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.8212 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 0.607) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00431 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.8212) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.6334) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.2565) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00416 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.6334)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.951) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.8251) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00285 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.951)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.7906 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 0.6587) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00274 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.7906) (by norm_num) hu_9 (by norm_num)
  have hu_10 : (-0.9815) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.9439) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00218 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9815)) (by norm_num) hu_10 (by norm_num)
  have hu_11 : (-0.0318) ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5) (g_hi := 111.53125) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.6025) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00118 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := (-0.0318)) (by norm_num) hu_11 (by norm_num)
  linarith only [harch, hmaster, hn3, hn13, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11]

private theorem bohman_interval_14 {γ : ℝ} (hlo : 111.53125 ≤ γ) (hhi : γ ≤ 111.5625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.53125) (g_hi := 111.5625) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.439571) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.3528) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9312) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.05859 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.3528)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3462) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.9241) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01583 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.3462)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.1922) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.764) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01503 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.1922)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9091) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.7107) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01496 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.9091)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9601 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.2828) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00896 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.9601) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.0732 ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.4974) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0061 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := 0.0732) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.5546) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.1585) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00506 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.5546)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.9249) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.7502) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00438 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.9249)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.7518 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 0.7198) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00415 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.7518) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.9676) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.883) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00383 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9676)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.8562 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.53125) (g_hi := 111.5625) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 0.5427) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00284 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.8562) (by norm_num) hu_10 (by norm_num)
  linarith only [harch, hmaster, hn3, hn13, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10]

private theorem bohman_interval_15 {γ : ℝ} (hlo : 111.5625 ≤ γ) (hhi : γ ≤ 111.625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.5625) (g_hi := 111.625) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.439849) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.393) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9745) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.05352 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.393)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8868) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.6604) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01865 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.8868)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.506) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 2.1012) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01196 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.506)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.3685) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.948) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01174 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.3685)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.9845 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.1755) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00907 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.9845) (by norm_num) hu_4 (by norm_num)
  have hu_5 : 0.1776 ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.3921) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0067 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := 0.1776) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8937) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.6753) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.0062 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.8937)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.4705) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.0605) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00602 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.4705)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9501) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.8222) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.0059 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9501)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.5852 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 0.9455) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00375 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.5852) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.9102 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 0.4266) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00292 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.9102) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.2018 ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.3674) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00147 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := 0.2018) (by norm_num) hu_11 (by norm_num)
  have hu_12 : (-0.9738) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.5625) (g_hi := 111.625) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.9085) 46 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.0011 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.9738)) (by norm_num) hu_12 (by norm_num)
  linarith only [harch, hmaster, hn3, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11, hg_12]

private theorem bohman_interval_16 {γ : ℝ} (hlo : 111.625 ≤ γ) (hhi : γ ≤ 111.75) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.625) (g_hi := 111.75) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.440406) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.4711) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.0611) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.04436 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.4711)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8358) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.5598) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02714 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.8358)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9048) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.7006) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01128 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9048)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8164) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.5254) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01073 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.8164)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.8896 ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 0.4741) 61 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00864 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := 0.8896) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.2897) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 1.8646) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00808 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.2897)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.3792 ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.1817) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00784 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := 0.3792) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.6784) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 2.3161) 52 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00597 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.6784)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.7739) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 2.4554) 50 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00547 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.7739)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : (-0.9241) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.7482) 46 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00323 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.9241)) (by norm_num) hu_9 (by norm_num)
  have hu_10 : 0.9532 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 0.3066) 66 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_10 : 0.00299 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.9532) (by norm_num) hu_10 (by norm_num)
  have hu_11 : 0.173 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 1.3968) 64 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_11 : 0.00277 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.173) (by norm_num) hu_11 (by norm_num)
  have hu_12 : 0.4244 ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.625) (g_hi := 111.75) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.1323) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_12 : 0.00174 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := 0.4244) (by norm_num) hu_12 (by norm_num)
  linarith only [harch, hmaster, hn3, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9, hg_10, hg_11, hg_12]

private theorem bohman_interval_17 {γ : ℝ} (hlo : 111.75 ≤ γ) (hhi : γ ≤ 112.4375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, -, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, -, -, -, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 111.75) (g_hi := 112.4375) (M := 12544) (logM4_hi := 8.0507764) (ub := 1.443477) (a2 := 6) (b := 0) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.709) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.3586) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.04844 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.709)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.7752) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.4574) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02667 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.7752)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6093) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.2257) 43 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02284 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.6093)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.0979 ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 1.4726) 56 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0125 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := 0.0979) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8234) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.5377) 12 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01209 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.8234)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.7561) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.4277) 46 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0104 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.7561)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.0552) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.6259) 60 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00537 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.0552)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.9714) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.8983) 20 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00396 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.9714)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.3552) ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 111.75) (g_hi := 112.4375) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.9338) 67 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00078 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := (-0.3552)) (by norm_num) hu_8 (by norm_num)
  linarith only [harch, hmaster, hn17, hn19, hn31, hn37, hn41, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8]

private theorem bohman_interval_18 {γ : ℝ} (hlo : 112.4375 ≤ γ) (hhi : γ ≤ 114.546875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 112.4375) (g_hi := 114.546875) (M := 12960) (logM4_hi := 8.0836006) (ub := 1.452825) (a2 := 3) (b := 4) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.5495) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 112.4375) (g_hi := 114.546875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.1523) 29 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.07564 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.5495)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5417) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 112.4375) (g_hi := 114.546875) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.1431) 20 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.07509 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.5417)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9898) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 112.4375) (g_hi := 114.546875) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.9908) 35 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00119 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9898)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn2, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_19 {γ : ℝ} (hlo : 114.546875 ≤ γ) (hhi : γ ≤ 116.1875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 114.546875) (g_hi := 116.1875) (M := 13440) (logM4_hi := 8.1198559) (ub := 1.459882) (a2 := 5) (b := 1) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.4046) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 114.546875) (g_hi := 116.1875) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.9872) 20 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.10274 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.4046)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5456) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 114.546875) (g_hi := 116.1875) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.1477) 44 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02657 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.5456)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6542) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 114.546875) (g_hi := 116.1875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.2837) 13 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.026 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.6542)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.7778) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 114.546875) (g_hi := 116.1875) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 2.4615) 52 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00537 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.7778)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn13, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_20 {γ : ℝ} (hlo : 116.1875 ≤ γ) (hhi : γ ≤ 119.78125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 116.1875) (g_hi := 119.78125) (M := 14336) (logM4_hi := 8.1842714) (ub := 1.475068) (a2 := 9) (b := 0) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.2239 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 116.1875) (g_hi := 119.78125) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.3448) 13 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.176 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.2239) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_21 {γ : ℝ} (hlo : 119.78125 ≤ γ) (hhi : γ ≤ 122) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 119.78125) (g_hi := 122) (M := 14700) (logM4_hi := 8.2095778) (ub := 1.484314) (a2 := 0) (b := 1) (c := 2) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.4157) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 119.78125) (g_hi := 122) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 1.9993) 31 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09882 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.4157)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4964) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 119.78125) (g_hi := 122) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.09) 21 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.08394 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.4964)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9675) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 119.78125) (g_hi := 122) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.8827) 13 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00205 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.9675)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_22 {γ : ℝ} (hlo : 122 ≤ γ) (hhi : γ ≤ 123.125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨-, -, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, -, -, -, ⟨hl31a, hl31b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 122) (g_hi := 123.125) (M := 15360) (logM4_hi := 8.2533508) (ub := 1.48886) (a2 := 8) (b := 1) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.2076 ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.125) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 1.3615) 38 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14405 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := 0.2076) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.0963) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.125) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 1.6671) 50 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.03858 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.0963)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9363) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.125) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.7812) 47 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00371 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.9363)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.446) ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 122) (g_hi := 123.125) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 2.0329) 67 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00252 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := (-0.446)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn2, hn3, hn5, hn17, hn19, hn23, hn29, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_23 {γ : ℝ} (hlo : 123.125 ≤ γ) (hhi : γ ≤ 123.671875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, -, ⟨hl19a, hl19b⟩, -, ⟨hl29a, hl29b⟩, -, ⟨hl37a, hl37b⟩, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 123.125) (g_hi := 123.671875) (M := 15360) (logM4_hi := 8.2533508) (ub := 1.491056) (a2 := 8) (b := 1) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.3216) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 1.898) 38 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.08071 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.3216)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.3199 ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 1.245) 47 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.0772 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := 0.3199) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.3199) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.8963) 58 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01265 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.3199)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8679) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.621) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00882 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.8679)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.1852) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.7569) 66 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00463 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.1852)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.972) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.9009) 32 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00458 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.972)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : 0.0457 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.125) (g_hi := 123.671875) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 1.5249) 71 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00247 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.0457) (by norm_num) hu_6 (by norm_num)
  linarith only [harch, hmaster, hn3, hn13, hn17, hn23, hn31, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6]

private theorem bohman_interval_24 {γ : ℝ} (hlo : 123.671875 ≤ γ) (hhi : γ ≤ 124.828125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, -, -, ⟨hl17a, hl17b⟩, -, ⟨hl23a, hl23b⟩, -, ⟨hl31a, hl31b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 123.671875) (g_hi := 124.828125) (M := 15680) (logM4_hi := 8.2739934) (ub := 1.495714) (a2 := 4) (b := 0) (c := 1) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.4351) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.671875) (g_hi := 124.828125) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.0208) 32 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09544 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.4351)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.7154) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.671875) (g_hi := 124.828125) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.3677) 22 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04364 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.7154)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.622) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.671875) (g_hi := 124.828125) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.2419) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02896 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.622)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.2368) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.671875) (g_hi := 124.828125) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.8097) 56 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01849 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.2368)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.2873) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.671875) (g_hi := 124.828125) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 1.862) 62 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00811 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.2873)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.844) ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 123.671875) (g_hi := 124.828125) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 2.5749) 68 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0007 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := (-0.844)) (by norm_num) hu_5 (by norm_num)
  linarith only [harch, hmaster, hn7, hn11, hn13, hn19, hn29, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5]

private theorem bohman_interval_25 {γ : ℝ} (hlo : 124.828125 ≤ γ) (hhi : γ ≤ 127.859375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 124.828125) (g_hi := 127.859375) (M := 16384) (logM4_hi := 8.3177663) (ub := 1.507663) (a2 := 12) (b := 0) (c := 0) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.1298 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 124.828125) (g_hi := 127.859375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.4405) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14889 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.1298) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.6239) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 124.828125) (g_hi := 127.859375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.2443) 22 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05972 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.6239)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_26 {γ : ℝ} (hlo : 127.859375 ≤ γ) (hhi : γ ≤ 129.875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 127.859375) (g_hi := 129.875) (M := 16800) (logM4_hi := 8.3430728) (ub := 1.515537) (a2 := 3) (b := 1) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.1194) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 127.859375) (g_hi := 129.875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 1.6903) 33 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.15128 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.1194)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4683) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 127.859375) (g_hi := 129.875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.058) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04468 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.4683)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.8168) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 127.859375) (g_hi := 129.875) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.5261) 40 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02173 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.8168)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn3, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_27 {γ : ℝ} (hlo : 129.875 ≤ γ) (hhi : γ ≤ 130.640625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, -, -, -, ⟨hl41a, hl41b⟩, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 129.875) (g_hi := 130.640625) (M := 17280) (logM4_hi := 8.3712331) (ub := 1.518485) (a2 := 5) (b := 3) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.2625) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.8363) 23 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.13421 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.2625)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.1799 ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.3898) 61 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02195 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := 0.1799) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5014) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.0958) 53 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02128 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.5014)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.3261 ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 1.2385) 65 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.0151 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := 0.3261) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8513) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.5887) 14 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01002 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.8513)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9242) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.7483) 50 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00442 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.9242)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.977) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.9226) 33 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00376 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.977)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.9699) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.8924) 40 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00355 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9699)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9256) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 2.7521) 59 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00179 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.9256)) (by norm_num) hu_8 (by norm_num)
  have hu_9 : 0.0285 ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 129.875) (g_hi := 130.640625) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 1.5421) 77 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_9 : 0.00157 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := 0.0285) (by norm_num) hu_9 (by norm_num)
  linarith only [harch, hmaster, hn29, hn31, hn37, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8, hg_9]

private theorem bohman_interval_28 {γ : ℝ} (hlo : 130.640625 ≤ γ) (hhi : γ ≤ 132.875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 130.640625) (g_hi := 132.875) (M := 17920) (logM4_hi := 8.4074883) (ub := 1.526939) (a2 := 7) (b := 0) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.0989 ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 130.640625) (g_hi := 132.875) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.4716) 23 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.22819 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := 0.0989) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn2, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_29 {γ : ℝ} (hlo : 132.875 ≤ γ) (hhi : γ ≤ 133.890625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, -, ⟨hl17a, hl17b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 132.875) (g_hi := 133.890625) (M := 17920) (logM4_hi := 8.4074883) (ub := 1.530717) (a2 := 7) (b := 0) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.2952) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 1.8703) 34 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.11996 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.2952)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2643) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 1.8381) 51 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04302 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.2643)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.5442) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.146) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03656 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.5442)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8507) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.5874) 23 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02172 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.8507)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.7052) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 2.3532) 60 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00713 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.7052)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9794) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 132.875) (g_hi := 133.890625) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.9336) 41 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00243 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9794)) (by norm_num) hu_5 (by norm_num)
  linarith only [harch, hmaster, hn13, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5]

private theorem bohman_interval_30 {γ : ℝ} (hlo : 133.890625 ≤ γ) (hhi : γ ≤ 134.546875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 133.890625) (g_hi := 134.546875) (M := 17920) (logM4_hi := 8.4074883) (ub := 1.533174) (a2 := 7) (b := 0) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.1283 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.442) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14849 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.1283) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.5802) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.1896) 51 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02454 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.5802)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.0433) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.614) 63 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.0178 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.0433)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.5834) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.1935) 55 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01778 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.5834)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : 0.3928 ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 1.167) 67 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01586 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := 0.3928) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.0472) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.6179) 72 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.00541 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.0472)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.9779) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 133.890625) (g_hi := 134.546875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.9266) 34 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00361 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.9779)) (by norm_num) hu_6 (by norm_num)
  linarith only [harch, hmaster, hn3, hn7, hn17, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6]

private theorem bohman_interval_31 {γ : ℝ} (hlo : 134.546875 ≤ γ) (hhi : γ ≤ 137.625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  have harch := bohman_arch_lt_smooth (g_lo := 134.546875) (g_hi := 137.625) (M := 18816) (logM4_hi := 8.4562912) (ub := 1.544473) (a2 := 5) (b := 1) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.4113 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 134.546875) (g_hi := 137.625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.1468) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.24501 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.4113) (by norm_num) hu_0 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0]

private theorem bohman_interval_32 {γ : ℝ} (hlo : 137.625 ≤ γ) (hhi : γ ≤ 138.828125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, ⟨hl7a, hl7b⟩, -, -, -, -, ⟨hl23a, hl23b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 137.625) (g_hi := 138.828125) (M := 19208) (logM4_hi := 8.4769337) (ub := 1.548822) (a2 := 1) (b := 0) (c := 0) (d := 4) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.1576) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.828125) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.7289) 24 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.15938 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.1576)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.3987) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.828125) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.9807) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05282 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.3987)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7189) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.828125) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.3727) 43 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.03336 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.7189)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.4384) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 137.625) (g_hi := 138.828125) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.0244) 69 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00639 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.4384)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn5, hn11, hn13, hn17, hn19, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_33 {γ : ℝ} (hlo : 138.828125 ≤ γ) (hhi : γ ≤ 139.609375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, -, -, -, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 138.828125) (g_hi := 139.609375) (M := 19600) (logM4_hi := 8.4972103) (ub := 1.551646) (a2 := 2) (b := 0) (c := 2) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.075 ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 1.4956) 43 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.12816 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := 0.075) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1909) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 1.7627) 53 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.04732 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.1909)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.8506) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.5872) 24 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02174 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.8506)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.5023) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.0969) 57 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.02124 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.5023)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.8145) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.5222) 15 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01276 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.8145)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9288) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.7606) 36 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0117 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.9288)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.8128) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 2.5192) 63 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.00452 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.8128)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.3188) ≤ Real.cos (γ * Real.log (31 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (x_hi := 1.8951) 76 (by norm_num) hlo hhi (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.0031 ≤ bohmanExcess 31 (γ * Real.log (31 : ℝ)) := bohmanExcess31_ge (u_lo := (-0.3188)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : 0.1065 ≤ Real.cos (γ * Real.log (37 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 138.828125) (g_hi := 139.609375) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (x_hi := 1.4639) 80 (by norm_num) hlo hhi (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00261 ≤ bohmanExcess 37 (γ * Real.log (37 : ℝ)) := bohmanExcess37_ge (u_lo := 0.1065) (by norm_num) hu_8 (by norm_num)
  linarith only [harch, hmaster, hn19, hn23, hn29, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8]

private theorem bohman_interval_34 {γ : ℝ} (hlo : 139.609375 ≤ γ) (hhi : γ ≤ 140.328125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨-, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, -, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 139.609375) (g_hi := 140.328125) (M := 19600) (logM4_hi := 8.4972103) (ub := 1.554212) (a2 := 2) (b := 0) (c := 2) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.0674 ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 139.609375) (g_hi := 140.328125) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 1.5032) 36 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.18515 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := 0.0674) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.2393) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 139.609375) (g_hi := 140.328125) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 1.8123) 57 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.03248 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.2393)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.1711) ≤ Real.cos (γ * Real.log (17 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 139.609375) (g_hi := 140.328125) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (x_hi := 1.7426) 63 (by norm_num) hlo hhi (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.02008 ≤ bohmanExcess 17 (γ * Real.log (17 : ℝ)) := bohmanExcess17_ge (u_lo := (-0.1711)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : 0.2715 ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 139.609375) (g_hi := 140.328125) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 1.2957) 75 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.00723 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := 0.2715) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.4926) ≤ Real.cos (γ * Real.log (23 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 139.609375) (g_hi := 140.328125) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (x_hi := 2.0857) 70 (by norm_num) hlo hhi (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.00577 ≤ bohmanExcess 23 (γ * Real.log (23 : ℝ)) := bohmanExcess23_ge (u_lo := (-0.4926)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9704) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 139.609375) (g_hi := 140.328125) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.8942) 43 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.0035 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9704)) (by norm_num) hu_5 (by norm_num)
  linarith only [harch, hmaster, hn2, hn3, hn11, hn19, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5]

private theorem bohman_interval_35 {γ : ℝ} (hlo : 140.328125 ≤ γ) (hhi : γ ≤ 141.3125) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, -, -, ⟨hl19a, hl19b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 140.328125) (g_hi := 141.3125) (M := 20160) (logM4_hi := 8.5253706) (ub := 1.557709) (a2 := 4) (b := 2) (c := 1) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.3156 ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 140.328125) (g_hi := 141.3125) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 1.2495) 36 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.23109 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := 0.3156) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0616 ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 140.328125) (g_hi := 141.3125) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.509) 66 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01975 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := 0.0616) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9763) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 140.328125) (g_hi := 141.3125) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.9191) 25 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00327 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.9763)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.9484) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 140.328125) (g_hi := 141.3125) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 2.8168) 54 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.003 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.9484)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn2, hn7, hn13, hn17, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_36 {γ : ℝ} (hlo : 141.3125 ≤ γ) (hhi : γ ≤ 142.9375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, -, ⟨hl7a, hl7b⟩, -, ⟨hl13a, hl13b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 141.3125) (g_hi := 142.9375) (M := 20480) (logM4_hi := 8.5409833) (ub := 1.563379) (a2 := 10) (b := 0) (c := 1) (d := 0) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.2639) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 141.3125) (g_hi := 142.9375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.8377) 25 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.13389 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.2639)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.1178) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 141.3125) (g_hi := 142.9375) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 1.6887) 44 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.10507 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.1178)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.6066) ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 141.3125) (g_hi := 142.9375) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 2.2224) 58 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.01679 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := (-0.6066)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.8472) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 141.3125) (g_hi := 142.9375) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 2.5808) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.01032 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.8472)) (by norm_num) hu_3 (by norm_num)
  linarith only [harch, hmaster, hn5, hn11, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2, hg_3]

private theorem bohman_interval_37 {γ : ℝ} (hlo : 142.9375 ≤ γ) (hhi : γ ≤ 144.875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 142.9375) (g_hi := 144.875) (M := 21168) (logM4_hi := 8.5741734) (ub := 1.570152) (a2 := 2) (b := 3) (c := 0) (d := 2) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.116 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 142.9375) (g_hi := 144.875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.4544) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.14526 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.116) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.4957) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 142.9375) (g_hi := 144.875) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.0892) 25 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.08408 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.4957)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.7576) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 142.9375) (g_hi := 144.875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.43) 37 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.04024 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.7576)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_38 {γ : ℝ} (hlo : 144.875 ≤ γ) (hhi : γ ≤ 146.625) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨-, -, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 144.875) (g_hi := 146.625) (M := 21504) (logM4_hi := 8.5897861) (ub := 1.57611) (a2 := 8) (b := 1) (c := 0) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.4518 ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 144.875) (g_hi := 146.625) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.1019) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.26313 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := 0.4518) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8474) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 144.875) (g_hi := 146.625) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.5812) 45 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.01809 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.8474)) (by norm_num) hu_1 (by norm_num)
  linarith only [harch, hmaster, hn3, hn5, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1]

private theorem bohman_interval_39 {γ : ℝ} (hlo : 146.625 ≤ γ) (hhi : γ ≤ 147.46875) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  have hl2a := Real.log_two_gt_d9.le; have hl2b := Real.log_two_lt_d9.le
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, -, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, -, ⟨hl19a, hl19b⟩, -, ⟨hl29a, hl29b⟩, -, -, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 146.625) (g_hi := 147.46875) (M := 21952) (logM4_hi := 8.6104287) (ub := 1.578992) (a2 := 4) (b := 0) (c := 0) (d := 3) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : (-0.1158) ≤ Real.cos (γ * Real.log (2 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (x_hi := 1.6867) 16 (by norm_num) hlo hhi (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.09491 ≤ bohmanExcess 2 (γ * Real.log (2 : ℝ)) := bohmanExcess2_ge (u_lo := (-0.1158)) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.2874 ≤ Real.cos (γ * Real.log (13 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (x_hi := 1.2791) 60 (by norm_num) hlo hhi (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05497 ≤ bohmanExcess 13 (γ * Real.log (13 : ℝ)) := bohmanExcess13_ge (u_lo := 0.2874) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.655) ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 2.2847) 26 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.05413 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := (-0.655)) (by norm_num) hu_2 (by norm_num)
  have hu_3 : (-0.1874) ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 1.7592) 56 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_3 : 0.04752 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := (-0.1874)) (by norm_num) hu_3 (by norm_num)
  have hu_4 : (-0.2449) ≤ Real.cos (γ * Real.log (19 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (x_hi := 1.8181) 69 (by norm_num) hlo hhi (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_4 : 0.01404 ≤ bohmanExcess 19 (γ * Real.log (19 : ℝ)) := bohmanExcess19_ge (u_lo := (-0.2449)) (by norm_num) hu_4 (by norm_num)
  have hu_5 : (-0.9353) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.7784) 38 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_5 : 0.01063 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.9353)) (by norm_num) hu_5 (by norm_num)
  have hu_6 : (-0.1771) ≤ Real.cos (γ * Real.log (43 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (x_hi := 1.7487) 88 (by norm_num) hlo hhi (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_6 : 0.001 ≤ bohmanExcess 43 (γ * Real.log (43 : ℝ)) := bohmanExcess43_ge (u_lo := (-0.1771)) (by norm_num) hu_6 (by norm_num)
  have hu_7 : (-0.5694) ≤ Real.cos (γ * Real.log (41 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (x_hi := 2.1764) 87 (by norm_num) hlo hhi (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_7 : 0.00065 ≤ bohmanExcess 41 (γ * Real.log (41 : ℝ)) := bohmanExcess41_ge (u_lo := (-0.5694)) (by norm_num) hu_7 (by norm_num)
  have hu_8 : (-0.9159) ≤ Real.cos (γ * Real.log (29 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 146.625) (g_hi := 147.46875) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (x_hi := 2.7272) 79 (by norm_num) hlo hhi (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_8 : 0.00046 ≤ bohmanExcess 29 (γ * Real.log (29 : ℝ)) := bohmanExcess29_ge (u_lo := (-0.9159)) (by norm_num) hu_8 (by norm_num)
  linarith only [harch, hmaster, hn7, hn17, hn23, hn31, hn37, hn47, hg_0, hg_1, hg_2, hg_3, hg_4, hg_5, hg_6, hg_7, hg_8]

private theorem bohman_interval_40 {γ : ℝ} (hlo : 147.46875 ≤ γ) (hhi : γ ≤ 149.9375) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 147.46875) (g_hi := 149.9375) (M := 22400) (logM4_hi := 8.6307053) (ub := 1.5873) (a2 := 5) (b := 0) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.2013 ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 147.46875) (g_hi := 149.9375) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.368) 26 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.2587 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := 0.2013) (by norm_num) hu_0 (by norm_num)
  have hu_1 : (-0.8387) ≤ Real.cos (γ * Real.log (5 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 147.46875) (g_hi := 149.9375) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (x_hi := 2.5652) 38 (by norm_num) hlo hhi (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.02666 ≤ bohmanExcess 5 (γ * Real.log (5 : ℝ)) := bohmanExcess5_ge (u_lo := (-0.8387)) (by norm_num) hu_1 (by norm_num)
  have hu_2 : (-0.9225) ≤ Real.cos (γ * Real.log (7 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 147.46875) (g_hi := 149.9375) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (x_hi := 2.744) 46 (by norm_num) hlo hhi (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_2 : 0.00918 ≤ bohmanExcess 7 (γ * Real.log (7 : ℝ)) := bohmanExcess7_ge (u_lo := (-0.9225)) (by norm_num) hu_2 (by norm_num)
  linarith only [harch, hmaster, hn2, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47, hg_0, hg_1, hg_2]

private theorem bohman_interval_41 {γ : ℝ} (hlo : 149.9375 ≤ γ) (hhi : γ ≤ 150) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) -
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) < 2.236881 := by
  obtain ⟨⟨hl3a, hl3b⟩, -, -, ⟨hl11a, hl11b⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have harch := bohman_arch_lt_smooth (g_lo := 149.9375) (g_hi := 150) (M := 22400) (logM4_hi := 8.6307053) (ub := 1.587508) (a2 := 5) (b := 0) (c := 2) (d := 1) (by norm_num) hlo hhi (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmaster := bohmanPhaseForm_ge_sum_excess (fun p => γ * Real.log (p : ℝ))
  obtain ⟨hn2, hn3, hn5, hn7, hn11, hn13, hn17, hn19, hn23, hn29, hn31, hn37, hn41, hn43, hn47⟩ := bohmanExcess_all_nonneg (fun p => γ * Real.log (p : ℝ))
  have hu_0 : 0.1336 ≤ Real.cos (γ * Real.log (3 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 149.9375) (g_hi := 150) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (x_hi := 1.4366) 26 (by norm_num) hlo hhi (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_0 : 0.23833 ≤ bohmanExcess 3 (γ * Real.log (3 : ℝ)) := bohmanExcess3_ge (u_lo := 0.1336) (by norm_num) hu_0 (by norm_num)
  have hu_1 : 0.0248 ≤ Real.cos (γ * Real.log (11 : ℝ)) := cos_mul_ge_of_even_shift (g_lo := 149.9375) (g_hi := 150) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (x_hi := 1.5458) 57 (by norm_num) hlo hhi (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have hg_1 : 0.05994 ≤ bohmanExcess 11 (γ * Real.log (11 : ℝ)) := bohmanExcess11_ge (u_lo := 0.0248) (by norm_num) hu_1 (by norm_num)
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
  rcases le_or_gt γ 96.96875 with h3 | h3
  · exact bohman_interval_3 h2.le h3
  rcases le_or_gt γ 99.59375 with h4 | h4
  · exact bohman_interval_4 h3.le h4
  rcases le_or_gt γ 102.140625 with h5 | h5
  · exact bohman_interval_5 h4.le h5
  rcases le_or_gt γ 104.75 with h6 | h6
  · exact bohman_interval_6 h5.le h6
  rcases le_or_gt γ 106.578125 with h7 | h7
  · exact bohman_interval_7 h6.le h7
  rcases le_or_gt γ 111.03125 with h8 | h8
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
  rcases le_or_gt γ 111.5625 with h14 | h14
  · exact bohman_interval_14 h13.le h14
  rcases le_or_gt γ 111.625 with h15 | h15
  · exact bohman_interval_15 h14.le h15
  rcases le_or_gt γ 111.75 with h16 | h16
  · exact bohman_interval_16 h15.le h16
  rcases le_or_gt γ 112.4375 with h17 | h17
  · exact bohman_interval_17 h16.le h17
  rcases le_or_gt γ 114.546875 with h18 | h18
  · exact bohman_interval_18 h17.le h18
  rcases le_or_gt γ 116.1875 with h19 | h19
  · exact bohman_interval_19 h18.le h19
  rcases le_or_gt γ 119.78125 with h20 | h20
  · exact bohman_interval_20 h19.le h20
  rcases le_or_gt γ 122 with h21 | h21
  · exact bohman_interval_21 h20.le h21
  rcases le_or_gt γ 123.125 with h22 | h22
  · exact bohman_interval_22 h21.le h22
  rcases le_or_gt γ 123.671875 with h23 | h23
  · exact bohman_interval_23 h22.le h23
  rcases le_or_gt γ 124.828125 with h24 | h24
  · exact bohman_interval_24 h23.le h24
  rcases le_or_gt γ 127.859375 with h25 | h25
  · exact bohman_interval_25 h24.le h25
  rcases le_or_gt γ 129.875 with h26 | h26
  · exact bohman_interval_26 h25.le h26
  rcases le_or_gt γ 130.640625 with h27 | h27
  · exact bohman_interval_27 h26.le h27
  rcases le_or_gt γ 132.875 with h28 | h28
  · exact bohman_interval_28 h27.le h28
  rcases le_or_gt γ 133.890625 with h29 | h29
  · exact bohman_interval_29 h28.le h29
  rcases le_or_gt γ 134.546875 with h30 | h30
  · exact bohman_interval_30 h29.le h30
  rcases le_or_gt γ 137.625 with h31 | h31
  · exact bohman_interval_31 h30.le h31
  rcases le_or_gt γ 138.828125 with h32 | h32
  · exact bohman_interval_32 h31.le h32
  rcases le_or_gt γ 139.609375 with h33 | h33
  · exact bohman_interval_33 h32.le h33
  rcases le_or_gt γ 140.328125 with h34 | h34
  · exact bohman_interval_34 h33.le h34
  rcases le_or_gt γ 141.3125 with h35 | h35
  · exact bohman_interval_35 h34.le h35
  rcases le_or_gt γ 142.9375 with h36 | h36
  · exact bohman_interval_36 h35.le h36
  rcases le_or_gt γ 144.875 with h37 | h37
  · exact bohman_interval_37 h36.le h37
  rcases le_or_gt γ 146.625 with h38 | h38
  · exact bohman_interval_38 h37.le h38
  rcases le_or_gt γ 147.46875 with h39 | h39
  · exact bohman_interval_39 h38.le h39
  rcases le_or_gt γ 149.9375 with h40 | h40
  · exact bohman_interval_40 h39.le h40
  exact bohman_interval_41 h40.le hhi

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
  obtain ⟨⟨hl3a, hl3b⟩, ⟨hl5a, hl5b⟩, ⟨hl7a, hl7b⟩, ⟨hl11a, hl11b⟩, ⟨hl13a, hl13b⟩, ⟨hl17a, hl17b⟩, ⟨hl19a, hl19b⟩, ⟨hl23a, hl23b⟩, ⟨hl29a, hl29b⟩, ⟨hl31a, hl31b⟩, ⟨hl37a, hl37b⟩, ⟨hl41a, hl41b⟩, ⟨hl43a, hl43b⟩, ⟨hl47a, hl47b⟩, -, -, -, -, -, -, -, -, -⟩ := sharp_log_prime_bounds
  have b2_1l : (0.3108480 : ℝ) ≤ Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) :=
    bohman_coeff_lb_p13' (u_lo := 2.65768) (by norm_num) (by norm_num) hl2a hl2b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  have b3_1l : (0.2801437 : ℝ) ≤ Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) :=
    bohman_coeff_lb_p13' (u_lo := 2.37442) (by norm_num) (by norm_num) hl3a hl3b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  have b5_1l : (0.1816976 : ℝ) ≤ Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) :=
    bohman_coeff_lb_p13' (u_lo := 2.01767) (by norm_num) (by norm_num) hl5a hl5b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  have b7_1l : (0.1196791 : ℝ) ≤ Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) :=
    bohman_coeff_lb_p13' (u_lo := 1.78292) (by norm_num) (by norm_num) hl7a hl7b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  obtain ⟨⟨cb_2_1_l, cb_2_1_u⟩, ⟨cb_2_2_l, cb_2_2_u⟩, ⟨cb_2_3_l, cb_2_3_u⟩, ⟨cb_2_4_l, cb_2_4_u⟩, ⟨cb_2_5_l, cb_2_5_u⟩, ⟨cb_2_6_l, cb_2_6_u⟩, ⟨cb_3_1_l, cb_3_1_u⟩, ⟨cb_3_2_l, cb_3_2_u⟩, ⟨cb_3_3_l, cb_3_3_u⟩, ⟨cb_3_4_l, cb_3_4_u⟩, ⟨cb_5_1_l, cb_5_1_u⟩, ⟨cb_5_2_l, cb_5_2_u⟩, ⟨cb_7_1_l, cb_7_1_u⟩, ⟨cb_7_2_l, cb_7_2_u⟩, ⟨cb_11_1_l, cb_11_1_u⟩, ⟨cb_13_1_l, cb_13_1_u⟩, ⟨cb_17_1_l, cb_17_1_u⟩, ⟨cb_19_1_l, cb_19_1_u⟩, ⟨cb_23_1_l, cb_23_1_u⟩, ⟨cb_29_1_l, cb_29_1_u⟩, ⟨cb_31_1_l, cb_31_1_u⟩, ⟨cb_37_1_l, cb_37_1_u⟩, ⟨cb_41_1_l, cb_41_1_u⟩, ⟨cb_43_1_l, cb_43_1_u⟩, ⟨cb_47_1_l, cb_47_1_u⟩, ⟨cb_53_1_l, cb_53_1_u⟩, ⟨cb_59_1_l, cb_59_1_u⟩, ⟨cb_61_1_l, cb_61_1_u⟩, ⟨cb_67_1_l, cb_67_1_u⟩, ⟨cb_71_1_l, cb_71_1_u⟩, ⟨cb_73_1_l, cb_73_1_u⟩, ⟨cb_79_1_l, cb_79_1_u⟩, ⟨cb_83_1_l, cb_83_1_u⟩, ⟨cb_89_1_l, cb_89_1_u⟩⟩ := all_prime_bohman_coeff_bounds'
  have hcu_0 : Real.cos ((301 / 2 : ℝ) * Real.log (2 : ℝ)) ≤ (-0.7982) := by rw [show ((301 / 2 : ℝ) * Real.log (2 : ℝ)) = 150.5 * Real.log (2 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.6462) 16 (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_0 : Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) * Real.cos ((301 / 2 : ℝ) * Real.log (2 : ℝ)) ≤ (-0.248117) := by nlinarith only [b2_1l, cb_2_1_u, hcu_0]
  have hcu_1 : Real.cos (2 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ 0.2754 := by rw [show (2 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) = 301 * Real.log (2 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 301) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 1.8496) 33 (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_1 : Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ 0.031241 := by nlinarith only [cb_2_2_l, cb_2_2_u, hcu_1]
  have hcu_2 : Real.cos (3 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ 0.3595 := by rw [show (3 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) = 451.5 * Real.log (2 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 451.5) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 1.9384) 49 (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_2 : Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) * Real.cos (3 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ 0.011836 := by nlinarith only [cb_2_3_l, cb_2_3_u, hcu_2]
  have hcu_3 : Real.cos (4 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ (-0.8485) := by rw [show (4 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) = 602 * Real.log (2 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 602) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.5574) 66 (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_3 : Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) * Real.cos (4 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ (-0.005894) := by nlinarith only [cb_2_4_l, cb_2_4_u, hcu_3]
  have hcu_4 : Real.cos (5 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ 0.9975 := by rw [show (5 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) = 752.5 * Real.log (2 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 752.5) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 3.0529) 83 (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_4 : Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) * Real.cos (5 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ 0.00082 := by nlinarith only [cb_2_5_l, cb_2_5_u, hcu_4]
  have hcu_5 : Real.cos (6 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ (-0.7416) := by rw [show (6 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) = 903 * Real.log (2 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 903) (lp_lo := 0.6931471803) (lp_hi := 0.6931471808) (s_hi := 0.7351) 99 (by norm_num) (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_5 : Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) * Real.cos (6 * ((301 / 2 : ℝ) * Real.log (2 : ℝ))) ≤ (-0.00001) := by nlinarith only [cb_2_6_l, cb_2_6_u, hcu_5]
  have hcu_6 : Real.cos ((301 / 2 : ℝ) * Real.log (3 : ℝ)) ≤ (-0.3906) := by rw [show ((301 / 2 : ℝ) * Real.log (3 : ℝ)) = 150.5 * Real.log (3 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (s_hi := 1.1694) 26 (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_6 : Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) * Real.cos ((301 / 2 : ℝ) * Real.log (3 : ℝ)) ≤ (-0.109423) := by nlinarith only [b3_1l, cb_3_1_u, hcu_6]
  have hcu_7 : Real.cos (2 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) ≤ (-0.6746) := by rw [show (2 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) = 301 * Real.log (3 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 301) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (s_hi := 0.8302) 52 (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_7 : Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) ≤ (-0.027726) := by nlinarith only [cb_3_2_l, cb_3_2_u, hcu_7]
  have hcu_8 : Real.cos (3 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) ≤ 0.9481 := by rw [show (3 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) = 451.5 * Real.log (3 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 451.5) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (s_hi := 2.816) 78 (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_8 : Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) * Real.cos (3 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) ≤ 0.002267 := by nlinarith only [cb_3_3_l, cb_3_3_u, hcu_8]
  have hcu_9 : Real.cos (4 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) ≤ (-0.0352) := by rw [show (4 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) = 602 * Real.log (3 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 602) (lp_lo := 1.0985728) (lp_hi := 1.0986619) (s_hi := 1.5354) 105 (by norm_num) (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_9 : Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) * Real.cos (4 * ((301 / 2 : ℝ) * Real.log (3 : ℝ))) ≤ 0.000001 := by nlinarith only [cb_3_4_l, cb_3_4_u, hcu_9]
  have hcu_10 : Real.cos ((301 / 2 : ℝ) * Real.log (5 : ℝ)) ≤ (-0.9462) := by rw [show ((301 / 2 : ℝ) * Real.log (5 : ℝ)) = 150.5 * Real.log (5 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (s_hi := 0.329) 38 (by norm_num) (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_10 : Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) * Real.cos ((301 / 2 : ℝ) * Real.log (5 : ℝ)) ≤ (-0.171921) := by nlinarith only [b5_1l, cb_5_1_u, hcu_10]
  have hcu_11 : Real.cos (2 * ((301 / 2 : ℝ) * Real.log (5 : ℝ))) ≤ 0.8064 := by rw [show (2 * ((301 / 2 : ℝ) * Real.log (5 : ℝ))) = 301 * Real.log (5 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 301) (lp_lo := 1.6094307) (lp_hi := 1.6095113) (s_hi := 2.5084) 77 (by norm_num) (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_11 : Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log (5 : ℝ))) ≤ 0.003643 := by nlinarith only [cb_5_2_l, cb_5_2_u, hcu_11]
  have hcu_12 : Real.cos ((301 / 2 : ℝ) * Real.log (7 : ℝ)) ≤ (-0.7666) := by rw [show ((301 / 2 : ℝ) * Real.log (7 : ℝ)) = 150.5 * Real.log (7 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (s_hi := 0.697) 46 (by norm_num) (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_12 : Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) * Real.cos ((301 / 2 : ℝ) * Real.log (7 : ℝ)) ≤ (-0.091744) := by nlinarith only [b7_1l, cb_7_1_u, hcu_12]
  have hcu_13 : Real.cos (2 * ((301 / 2 : ℝ) * Real.log (7 : ℝ))) ≤ 0.1905 := by rw [show (2 * ((301 / 2 : ℝ) * Real.log (7 : ℝ))) = 301 * Real.log (7 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 301) (lp_lo := 1.9458994) (lp_hi := 1.9459466) (s_hi := 1.7623) 93 (by norm_num) (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_13 : Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) * Real.cos (2 * ((301 / 2 : ℝ) * Real.log (7 : ℝ))) ≤ 0.000062 := by nlinarith only [cb_7_2_l, cb_7_2_u, hcu_13]
  have hcu_14 : Real.cos ((301 / 2 : ℝ) * Real.log (11 : ℝ)) ≤ (-0.9138) := by rw [show ((301 / 2 : ℝ) * Real.log (11 : ℝ)) = 150.5 * Real.log (11 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 2.3977758) (lp_hi := 2.3979146) (s_hi := 0.418) 57 (by norm_num) (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_14 : Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) * Real.cos ((301 / 2 : ℝ) * Real.log (11 : ℝ)) ≤ (-0.053457) := by nlinarith only [cb_11_1_l, cb_11_1_u, hcu_14]
  have hcu_15 : Real.cos ((301 / 2 : ℝ) * Real.log (13 : ℝ)) ≤ (-0.9059) := by rw [show ((301 / 2 : ℝ) * Real.log (13 : ℝ)) = 150.5 * Real.log (13 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 2.5646445) (lp_hi := 2.5650861) (s_hi := 0.437) 61 (by norm_num) (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_15 : Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) * Real.cos ((301 / 2 : ℝ) * Real.log (13 : ℝ)) ≤ (-0.038692) := by nlinarith only [cb_13_1_l, cb_13_1_u, hcu_15]
  have hcu_16 : Real.cos ((301 / 2 : ℝ) * Real.log (17 : ℝ)) ≤ 0.6572 := by rw [show ((301 / 2 : ℝ) * Real.log (17 : ℝ)) = 150.5 * Real.log (17 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 2.8331549) (lp_hi := 2.8332392) (s_hi := 2.2876) 67 (by norm_num) (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_16 : Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) * Real.cos ((301 / 2 : ℝ) * Real.log (17 : ℝ)) ≤ 0.015962 := by nlinarith only [cb_17_1_l, cb_17_1_u, hcu_16]
  have hcu_17 : Real.cos ((301 / 2 : ℝ) * Real.log (19 : ℝ)) ≤ (-0.9847) := by rw [show ((301 / 2 : ℝ) * Real.log (19 : ℝ)) = 150.5 * Real.log (19 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 2.9443944) (lp_hi := 2.9444434) (s_hi := 0.1743) 70 (by norm_num) (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_17 : Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) * Real.cos ((301 / 2 : ℝ) * Real.log (19 : ℝ)) ≤ (-0.018333) := by nlinarith only [cb_19_1_l, cb_19_1_u, hcu_17]
  have hcu_18 : Real.cos ((301 / 2 : ℝ) * Real.log (23 : ℝ)) ≤ 0.7992 := by rw [show ((301 / 2 : ℝ) * Real.log (23 : ℝ)) = 150.5 * Real.log (23 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.1354442) (lp_hi := 3.1356659) (s_hi := 2.4963) 75 (by norm_num) (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_18 : Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) * Real.cos ((301 / 2 : ℝ) * Real.log (23 : ℝ)) ≤ 0.009128 := by nlinarith only [cb_23_1_l, cb_23_1_u, hcu_18]
  have hcu_19 : Real.cos ((301 / 2 : ℝ) * Real.log (29 : ℝ)) ≤ (-0.5481) := by rw [show ((301 / 2 : ℝ) * Real.log (29 : ℝ)) = 150.5 * Real.log (29 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.3667148) (lp_hi := 3.3673538) (s_hi := 0.9905) 80 (by norm_num) (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_19 : Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) * Real.cos ((301 / 2 : ℝ) * Real.log (29 : ℝ)) ≤ (-0.003122) := by nlinarith only [cb_29_1_l, cb_29_1_u, hcu_19]
  have hcu_20 : Real.cos ((301 / 2 : ℝ) * Real.log (31 : ℝ)) ≤ (-0.0156) := by rw [show ((301 / 2 : ℝ) * Real.log (31 : ℝ)) = 150.5 * Real.log (31 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.4339401) (lp_hi := 3.4339888) (s_hi := 1.555) 82 (by norm_num) (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_20 : Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) * Real.cos ((301 / 2 : ℝ) * Real.log (31 : ℝ)) ≤ (-0.00007) := by nlinarith only [cb_31_1_l, cb_31_1_u, hcu_20]
  have hcu_21 : Real.cos ((301 / 2 : ℝ) * Real.log (37 : ℝ)) ≤ (-0.9975) := by rw [show ((301 / 2 : ℝ) * Real.log (37 : ℝ)) = 150.5 * Real.log (37 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.6108132) (lp_hi := 3.6109222) (s_hi := 0.0683) 86 (by norm_num) (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_21 : Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) * Real.cos ((301 / 2 : ℝ) * Real.log (37 : ℝ)) ≤ (-0.002369) := by nlinarith only [cb_37_1_l, cb_37_1_u, hcu_21]
  have hcu_22 : Real.cos ((301 / 2 : ℝ) * Real.log (41 : ℝ)) ≤ 0.9548 := by rw [show ((301 / 2 : ℝ) * Real.log (41 : ℝ)) = 150.5 * Real.log (41 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.7132884) (lp_hi := 3.7136164) (s_hi := 2.8375) 88 (by norm_num) (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_22 : Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) * Real.cos ((301 / 2 : ℝ) * Real.log (41 : ℝ)) ≤ 0.001477 := by nlinarith only [cb_41_1_l, cb_41_1_u, hcu_22]
  have hcu_23 : Real.cos ((301 / 2 : ℝ) * Real.log (43 : ℝ)) ≤ 0.8422 := by rw [show ((301 / 2 : ℝ) * Real.log (43 : ℝ)) = 150.5 * Real.log (43 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.7611756) (lp_hi := 3.7612638) (s_hi := 2.5715) 90 (by norm_num) (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_23 : Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) * Real.cos ((301 / 2 : ℝ) * Real.log (43 : ℝ)) ≤ 0.00105 := by nlinarith only [cb_43_1_l, cb_43_1_u, hcu_23]
  have hcu_24 : Real.cos ((301 / 2 : ℝ) * Real.log (47 : ℝ)) ≤ 0.1805 := by rw [show ((301 / 2 : ℝ) * Real.log (47 : ℝ)) = 150.5 * Real.log (47 : ℝ) by ring]; exact cos_mul_le_of_odd_shift (c := 150.5) (lp_lo := 3.8501175) (lp_hi := 3.8501705) (s_hi := 1.7521) 92 (by norm_num) (by norm_num) hl47a hl47b (by norm_num) (by norm_num) (by norm_num) (by unfold cosPoly10; norm_num)
  have ht_24 : Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) * Real.cos ((301 / 2 : ℝ) * Real.log (47 : ℝ)) ≤ 0.000146 := by nlinarith only [cb_47_1_l, cb_47_1_u, hcu_24]
  have ht_25 : Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) * Real.cos ((301 / 2 : ℝ) * Real.log (53 : ℝ)) ≤ 0.0003977 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (53 : ℝ)); nlinarith only [cb_53_1_l, cb_53_1_u, hc]
  have ht_26 : Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) * Real.cos ((301 / 2 : ℝ) * Real.log (59 : ℝ)) ≤ 0.0001869 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (59 : ℝ)); nlinarith only [cb_59_1_l, cb_59_1_u, hc]
  have ht_27 : Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) * Real.cos ((301 / 2 : ℝ) * Real.log (61 : ℝ)) ≤ 0.0001440 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (61 : ℝ)); nlinarith only [cb_61_1_l, cb_61_1_u, hc]
  have ht_28 : Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) * Real.cos ((301 / 2 : ℝ) * Real.log (67 : ℝ)) ≤ 0.0000588 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (67 : ℝ)); nlinarith only [cb_67_1_l, cb_67_1_u, hc]
  have ht_29 : Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) * Real.cos ((301 / 2 : ℝ) * Real.log (71 : ℝ)) ≤ 0.0000294 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (71 : ℝ)); nlinarith only [cb_71_1_l, cb_71_1_u, hc]
  have ht_30 : Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) * Real.cos ((301 / 2 : ℝ) * Real.log (73 : ℝ)) ≤ 0.0000197 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (73 : ℝ)); nlinarith only [cb_73_1_l, cb_73_1_u, hc]
  have ht_31 : Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) * Real.cos ((301 / 2 : ℝ) * Real.log (79 : ℝ)) ≤ 0.0000045 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (79 : ℝ)); nlinarith only [cb_79_1_l, cb_79_1_u, hc]
  have ht_32 : Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) * Real.cos ((301 / 2 : ℝ) * Real.log (83 : ℝ)) ≤ 0.0000011 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (83 : ℝ)); nlinarith only [cb_83_1_l, cb_83_1_u, hc]
  have ht_33 : Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) * Real.cos ((301 / 2 : ℝ) * Real.log (89 : ℝ)) ≤ 0.0000001 := by have hc := Real.cos_le_one ((301 / 2 : ℝ) * Real.log (89 : ℝ)); nlinarith only [cb_89_1_l, cb_89_1_u, hc]
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
  have hγ_pos : 0 < γ := (mul_pos two_pos (Real.exp_pos _)).trans_le hγ_exp
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
    rw [h2] at h1
    linarith
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
    ((d : ℝ) - 1) * (8999 / 24000 : ℝ) ^ 2 ≤ 150 ^ 2 ↔ d ≤ 160037 := by
  constructor
  · intro h
    by_contra! hd
    have hn : 160038 ≤ d := by omega
    have h' : (160038 : ℝ) ≤ d := by exact_mod_cast hn
    linarith
  · intro h
    have h' : (d : ℝ) ≤ 160037 := by exact_mod_cast h
    linarith

/-- Unshifted `Ξ` Jensen polynomials have only real zeros through degree `160,037` (upgraded from
`50,787` at height `84.5`). -/
theorem jensenNonrealCount_eq_zero_through_160037 (d : Fin 160038) :
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
degree `160,037` (upgraded from `50,787`). -/
theorem weightedXiJensen_splits_through_160037 (w : List ℕ) (d : Fin 160038) :
    (eulerWord w (xiJensenReal d.val)).Splits := by
  have h := weightedXiJensen_nonreal_le w d
  rw [jensenNonrealCount_eq_zero_through_160037 d, nonrealRootCount] at h
  have hc := Polynomial.card_roots' (eulerWord w (xiJensenReal d))
  rw [splits_iff_card_roots]
  omega

#print axioms rhVerifiedThrough_oneHundredFifty
#print axioms bohman_coupled_saturates_at_threeHundredOne_halves
#print axioms bohman_any_band_eventually_reverses
#print axioms xi_centre_pfSeq_fourHundredFortyNine
#print axioms xiSliceCoeff_nonneg_of_abs_le_twoHundredNinetyNine_halves
#print axioms re_xiLiPaired_nonneg_of_le_sevenHundredFive
#print axioms jensenNonrealCount_eq_zero_through_160037
#print axioms weightedXiJensen_splits_through_160037

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
