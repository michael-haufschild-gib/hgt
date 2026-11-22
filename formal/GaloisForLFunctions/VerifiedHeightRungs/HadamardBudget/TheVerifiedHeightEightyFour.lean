import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheBohmanBudgetAtTheEdge
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven

/-!
# The Riemann hypothesis through height 84.5 via the Bohman kernel

Replacing the Fejér triangle (`L = 3`, `O(1/γ)` archimedean tail, verified height `67`, pushed to `70`
at `L = 7/2`) with the positive-definite Bohman kernel `bohmanFn (9 / 2)` (`N = 91`, `O(1 / (L² γ²))`
archimedean tail) certifies without locating any zero or computing any value of `ζ`:

* **`rhVerifiedThrough_oneHundredSixtyNine_halves` (`RHVerifiedThrough (169 / 2)`)** and
  **`rhVerifiedThrough_eightyFour` (`RHVerifiedThrough 84`)**: every zero of `ξ` in the critical
  strip with `0 < Im ρ ≤ 84.5` lies on `Re ρ = 1/2`.
* **`bohman_phaseFree_saturates_at_eightyFive`**: for independent prime phases `θ : ℕ → ℝ`, the
  phase-free Bohman inequality at `L = 9/2` already reverses strictly at `γ = 85` (witnessed at
  phase `π` on every prime), establishing `84` as the integer ceiling at band `9/2`.
* **Upgraded rungs**: `PF_252` at the centre of `ξ`, slice nonnegativity across `|t| ≤ 84`, and
  `Re(2 λ_n) ≥ 0` for `n ≤ 397`.
-/

open Complex Set
open ArithmeticFunction (vonMangoldt)
open scoped ComplexOrder

namespace GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget

open _root_.RHTower GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Alternating polynomial envelope for `sin u - u cos u` -/

/-- Degree-9 lower Taylor polynomial for `sin u - u cos u` on `u ≥ 0`. -/
def bohmanP9 (u : ℝ) : ℝ :=
  u ^ 3 / 3 - u ^ 5 / 30 + u ^ 7 / 840 - u ^ 9 / 45360

/-- Degree-11 upper Taylor polynomial for `sin u - u cos u` on `u ≥ 0`. -/
def bohmanP11 (u : ℝ) : ℝ :=
  bohmanP9 u + u ^ 11 / 3991680

/-- Degree-13 lower Taylor polynomial for `sin u - u cos u` on `u ≥ 0`. -/
def bohmanP13 (u : ℝ) : ℝ :=
  bohmanP11 u - u ^ 13 / 518918400

private theorem nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf0 : f 0 = 0)
    (hd : ∀ x : ℝ, HasDerivAt f (f' x) x) (hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ f' x)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ f u := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hpos x (interior_subset hx))
  simpa only [hf0] using hmono self_mem_Ici hu hu

private theorem hasDerivAt_monomial_div (n : ℕ) (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ n / c) ((n : ℝ) * x ^ (n - 1) / c) x := by
  simpa only [mul_div_assoc] using ((hasDerivAt_pow n x).div_const c)

private theorem sin_taylor_bounds_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 ≤ Real.sin u ∧
      Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880 := by
  have h1 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - Real.sin x := fun x hx =>
    nonneg_of_deriv_nonneg (by simp)
      (fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y))
      (fun y _ => sub_nonneg.mpr (Real.cos_le_one y)) hx
  have h2 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2) := fun x hx =>
    nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div 2 2 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h1 y hy) hx
  have h3 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6) := fun x hx =>
    nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((hasDerivAt_id y).sub (hasDerivAt_monomial_div 3 6 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h2 y hy) hx
  have h4 : ∀ x : ℝ, 0 ≤ x → 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x := fun x hx =>
    nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div 2 2 y)).add
        (hasDerivAt_monomial_div 4 24 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h3 y hy) hx
  have h5 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x := fun x hx =>
    nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div 3 6 y)).add
        (hasDerivAt_monomial_div 5 120 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h4 y hy) hx
  have h6 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) :=
    fun x hx => nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div 2 2 y)).add
          (hasDerivAt_monomial_div 4 24 y)).sub
          (hasDerivAt_monomial_div 6 720 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h5 y hy) hx
  have h7 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) :=
    fun x hx => nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((hasDerivAt_id y).sub (hasDerivAt_monomial_div 3 6 y)).add
          (hasDerivAt_monomial_div 5 120 y)).sub
          (hasDerivAt_monomial_div 7 5040 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h6 y hy) hx
  have h8 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x :=
    fun x hx => nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div 2 2 y)).add
          (hasDerivAt_monomial_div 4 24 y)).sub
          (hasDerivAt_monomial_div 6 720 y)).add
          (hasDerivAt_monomial_div 8 40320 y)).sub (Real.hasDerivAt_cos y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h7 y hy) hx
  have h9 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x :=
    fun x hx => nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((((((hasDerivAt_id y).sub (hasDerivAt_monomial_div 3 6 y)).add
          (hasDerivAt_monomial_div 5 120 y)).sub
          (hasDerivAt_monomial_div 7 5040 y)).add
          (hasDerivAt_monomial_div 9 362880 y)).sub (Real.hasDerivAt_sin y)).congr_deriv
        (by norm_num; ring))
      (fun y hy => h8 y hy) hx
  exact ⟨sub_nonneg.mp (h7 u hu), sub_nonneg.mp (h9 u hu)⟩

private theorem sin_taylor11_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880 - u ^ 11 / 39916800 ≤
      Real.sin u := by
  have h9 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - Real.sin x :=
    fun x hx => sub_nonneg.mpr (sin_taylor_bounds_of_nonneg hx).2
  have h10 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) :=
    fun x hx => nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((Real.hasDerivAt_cos y).sub
        ((((((hasDerivAt_const y 1).sub (hasDerivAt_monomial_div 2 2 y)).add
          (hasDerivAt_monomial_div 4 24 y)).sub
          (hasDerivAt_monomial_div 6 720 y)).add
          (hasDerivAt_monomial_div 8 40320 y)).sub
          (hasDerivAt_monomial_div 10 3628800 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h9 y hy) hx
  have h11 : ∀ x : ℝ, 0 ≤ x →
      0 ≤ Real.sin x -
        (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) :=
    fun x hx => nonneg_of_deriv_nonneg (by norm_num)
      (fun y => ((Real.hasDerivAt_sin y).sub
        ((((((hasDerivAt_id y).sub (hasDerivAt_monomial_div 3 6 y)).add
          (hasDerivAt_monomial_div 5 120 y)).sub
          (hasDerivAt_monomial_div 7 5040 y)).add
          (hasDerivAt_monomial_div 9 362880 y)).sub
          (hasDerivAt_monomial_div 11 39916800 y))).congr_deriv
        (by norm_num; ring))
      (fun y hy => h10 y hy) hx
  exact sub_nonneg.mp (h11 u hu)

private theorem hasDerivAt_sin_sub_mul_cos (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin y - y * Real.cos y) (x * Real.sin x) x := by
  refine ((Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x))).congr_deriv ?_
  dsimp only [id]; ring

private theorem bohmanP13_le {u : ℝ} (hu : 0 ≤ u) :
    bohmanP13 u ≤ Real.sin u - u * Real.cos u := by
  have hd13 : ∀ x : ℝ, HasDerivAt bohmanP13
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800)) x :=
    fun x => by
      unfold bohmanP13 bohmanP11 bohmanP9
      refine ((((((hasDerivAt_monomial_div 3 3 x).sub
          (hasDerivAt_monomial_div 5 30 x)).add
          (hasDerivAt_monomial_div 7 840 x)).sub
          (hasDerivAt_monomial_div 9 45360 x)).add
          (hasDerivAt_monomial_div 11 3991680 x)).sub
          (hasDerivAt_monomial_div 13 518918400 x)).congr_deriv ?_
      norm_num; ring
  have hlo := nonneg_of_deriv_nonneg (by simp [bohmanP13, bohmanP11, bohmanP9])
    (fun x => ((hasDerivAt_sin_sub_mul_cos x).sub (hd13 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_taylor11_le_of_nonneg hx))) hu
  exact sub_nonneg.mp hlo

private theorem bohmanP9_le_and_le_bohmanP11 {u : ℝ} (hu : 0 ≤ u) :
    bohmanP9 u ≤ Real.sin u - u * Real.cos u ∧ Real.sin u - u * Real.cos u ≤ bohmanP11 u := by
  have hd9 : ∀ x : ℝ, HasDerivAt bohmanP9
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)) x := fun x => by
    unfold bohmanP9
    refine ((((hasDerivAt_monomial_div 3 3 x).sub
        (hasDerivAt_monomial_div 5 30 x)).add
        (hasDerivAt_monomial_div 7 840 x)).sub
        (hasDerivAt_monomial_div 9 45360 x)).congr_deriv ?_
    norm_num; ring
  have hd11 : ∀ x : ℝ, HasDerivAt bohmanP11
      (x * (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880)) x := fun x => by
    unfold bohmanP11
    refine ((hd9 x).add (hasDerivAt_monomial_div 11 3991680 x)).congr_deriv ?_
    norm_num; ring
  have hlo := nonneg_of_deriv_nonneg (by simp [bohmanP9])
    (fun x => ((hasDerivAt_sin_sub_mul_cos x).sub (hd9 x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_taylor_bounds_of_nonneg hx).1)) hu
  have hhi := nonneg_of_deriv_nonneg (by simp [bohmanP11, bohmanP9])
    (fun x => ((hd11 x).sub (hasDerivAt_sin_sub_mul_cos x)).congr_deriv (by ring))
    (fun x hx => mul_nonneg hx (sub_nonneg.mpr (sin_taylor_bounds_of_nonneg hx).2)) hu
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

private theorem monotoneOn_sin_sub_mul_cos :
    MonotoneOn (fun u : ℝ => Real.sin u - u * Real.cos u) (Icc 0 Real.pi) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 Real.pi)
    (fun x _ => (hasDerivAt_sin_sub_mul_cos x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_sin_sub_mul_cos x).hasDerivWithinAt)
    fun x hx => by
      have hx' : x ∈ Ioo 0 Real.pi := by rwa [interior_Icc] at hx
      exact mul_nonneg hx'.1.le (Real.sin_nonneg_of_nonneg_of_le_pi hx'.1.le hx'.2.le)

private theorem bohmanFn_eq_sin_sub_mul_cos {L x : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
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
  field_simp [hπ]
  ring

private theorem pi_bounds_d10 : (3.1415926535 : ℝ) < Real.pi ∧ Real.pi < 3.1415926536 :=
  ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩

/-- Two-sided rational enclosure of a prime-power Bohman harmonic weight at band `L = 9/2`. -/
private theorem bohman_coeff_bounds {p pk k lp_lo lp_hi u_lo u_hi c_lo c_hi : ℝ}
    (hpk : 0 < pk) (hk : 0 < k) (hlp0 : 0 ≤ lp_lo)
    (hlp_lo : lp_lo ≤ Real.log p) (hlp_hi : Real.log p ≤ lp_hi)
    (hk_hi : k * lp_hi ≤ 9 / 2)
    (hu_lo0 : 0 ≤ u_lo)
    (hu_lo : u_lo ≤ 3.1415926535 * (1 - k * lp_hi / (9 / 2)))
    (hu_hi : 3.1415926536 * (1 - k * lp_lo / (9 / 2)) ≤ u_hi)
    (hu_hi_pi : u_hi ≤ 3.1415926535)
    (h_clo : c_lo ≤ lp_lo / pk * (bohmanP9 u_lo / 3.1415926536))
    (h_chi : lp_hi / pk * (bohmanP11 u_hi / 3.1415926535) ≤ c_hi) :
    c_lo ≤ Real.log p / pk * bohmanFn (9 / 2) (k * Real.log p) ∧
      Real.log p / pk * bohmanFn (9 / 2) (k * Real.log p) ≤ c_hi := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10
  have hπ_pos := Real.pi_pos
  have hlp_nonneg : 0 ≤ Real.log p := hlp0.trans hlp_lo
  have hkx0 : 0 ≤ k * Real.log p := mul_nonneg hk.le hlp_nonneg
  have hkxL : k * Real.log p ≤ 9 / 2 :=
    (mul_le_mul_of_nonneg_left hlp_hi hk.le).trans hk_hi
  set u : ℝ := Real.pi * (1 - k * Real.log p / (9 / 2))
  have h1_lo : 0 ≤ 1 - k * lp_hi / (9 / 2) := by linarith
  have h1_le : 1 - k * lp_hi / (9 / 2) ≤ 1 - k * Real.log p / (9 / 2) := by
    have := mul_le_mul_of_nonneg_left hlp_hi hk.le; linarith
  have h1_ge : 1 - k * Real.log p / (9 / 2) ≤ 1 - k * lp_lo / (9 / 2) := by
    have := mul_le_mul_of_nonneg_left hlp_lo hk.le; linarith
  have hu_ge_lo : u_lo ≤ u := by
    refine hu_lo.trans ?_
    dsimp only [u]
    exact mul_le_mul hπ_lo.le h1_le h1_lo hπ_pos.le
  have hu_le_hi : u ≤ u_hi := by
    refine le_trans ?_ hu_hi
    dsimp only [u]
    exact mul_le_mul hπ_hi.le h1_ge (by linarith) (by norm_num)
  have hu0 : 0 ≤ u := hu_lo0.trans hu_ge_lo
  have hu_hi_lt_pi : u_hi ≤ Real.pi := hu_hi_pi.trans hπ_lo.le
  have hu_pi : u ≤ Real.pi := hu_le_hi.trans hu_hi_lt_pi
  have hH_lo : bohmanP9 u_lo ≤ Real.sin u - u * Real.cos u :=
    (bohmanP9_le_and_le_bohmanP11 hu_lo0).1.trans
      (monotoneOn_sin_sub_mul_cos ⟨hu_lo0, hu_ge_lo.trans hu_pi⟩ ⟨hu0, hu_pi⟩ hu_ge_lo)
  have hH_hi : Real.sin u - u * Real.cos u ≤ bohmanP11 u_hi :=
    (monotoneOn_sin_sub_mul_cos ⟨hu0, hu_pi⟩ ⟨hu_lo0.trans (hu_ge_lo.trans hu_le_hi), hu_hi_lt_pi⟩
      hu_le_hi).trans (bohmanP9_le_and_le_bohmanP11 (hu_lo0.trans (hu_ge_lo.trans hu_le_hi))).2
  have hW_eq := bohmanFn_eq_sin_sub_mul_cos (L := 9 / 2) (x := k * Real.log p) (by norm_num) hkx0 hkxL
  have hW_nonneg : 0 ≤ bohmanFn (9 / 2) (k * Real.log p) :=
    bohmanFn_nonneg (by norm_num) _
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
      rw [hW_eq, div_mul_cancel₀ _ hπ_pos.ne'] at this
      exact this
    exact (div_le_div_of_nonneg_right hH_hi hπ_pos.le).trans
      (div_le_div_of_nonneg_left (hH0.trans hH_hi) (by norm_num) hπ_lo.le)
  refine ⟨h_clo.trans ?_, ?_⟩
  · by_cases hw0 : 0 ≤ bohmanP9 u_lo / 3.1415926536
    · exact mul_le_mul (div_le_div_of_nonneg_right hlp_lo hpk.le) hW_lo hw0
        (div_nonneg hlp_nonneg hpk.le)
    · exact (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hlp0 hpk.le) (le_of_not_ge hw0)).trans
        (mul_nonneg (div_nonneg hlp_nonneg hpk.le) hW_nonneg)
  · exact (mul_le_mul (div_le_div_of_nonneg_right hlp_hi hpk.le) hW_hi hW_nonneg
      (div_nonneg (hlp_nonneg.trans hlp_hi) hpk.le)).trans h_chi

/-! ## Minimum over the phase of `p = 2` through harmonic `6` -/

/-- Degree-6 Chebyshev phase certificate for `p = 2` (`2, 4, 8, 16, 32, 64`), reducing the quintic
quotient `(S(u) - S(-1)) / (u + 1)` via `8 u² (u - 1) - (-8 u² + 6 u - 2) = 2 (u + 1) (2 u - 1)² ≥ 0`
to a positive-definite quadratic. -/
theorem family_two_six {A B C D E G u : ℝ} (hu0 : -1 ≤ u) (hu1 : u ≤ 1)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hG : 0 ≤ G)
    (ha2 : 0 < 4 * C - 8 * D)
    (hdisc : (2 * B - 4 * C + 6 * D) ^ 2 ≤
      4 * (4 * C - 8 * D) * (A - 2 * B + C - 2 * D - 36 * G)) :
    -A + B - C + D - E + G ≤
      A * u + B * (2 * u ^ 2 - 1) + C * (4 * u ^ 3 - 3 * u) +
        D * (8 * u ^ 4 - 8 * u ^ 2 + 1) + E * (16 * u ^ 5 - 20 * u ^ 3 + 5 * u) +
        G * (32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 1) := by
  have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
  have he5 : 0 ≤ E * (16 * u ^ 5 - 20 * u ^ 3 + 5 * u + 1) := by
    have hid5 : 16 * u ^ 5 - 20 * u ^ 3 + 5 * u + 1 = (u + 1) * (4 * u ^ 2 - 2 * u - 1) ^ 2 := by ring
    rw [hid5]
    exact mul_nonneg hE (mul_nonneg (by linarith only [hu0]) (sq_nonneg _))
  have hg6 : -(36 * G * (u + 1)) ≤ G * (32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 2) := by
    have hid6 : 32 * u ^ 6 - 48 * u ^ 4 + 18 * u ^ 2 - 2 =
        2 * (u + 1) * (u - 1) * (4 * u ^ 2 - 1) ^ 2 := by ring
    rw [hid6]
    have hsq9 : (4 * u ^ 2 - 1) ^ 2 ≤ 9 := by nlinarith only [sq_nonneg u, hu2]
    have hprod18 : (1 - u) * (4 * u ^ 2 - 1) ^ 2 ≤ 18 := by
      have h1u : 0 ≤ 1 - u := by linarith only [hu1]
      have h1u2 : 1 - u ≤ 2 := by linarith only [hu0]
      nlinarith only [hsq9, h1u, h1u2, sq_nonneg (4 * u ^ 2 - 1)]
    have hu_p1 : 0 ≤ u + 1 := by linarith only [hu0]
    nlinarith only [mul_le_mul_of_nonneg_left hprod18 (mul_nonneg hG hu_p1)]
  set q2 : ℝ := 4 * C - 8 * D
  set q1 : ℝ := 2 * B - 4 * C + 6 * D
  set q0 : ℝ := A - 2 * B + C - 2 * D - 36 * G
  have hquad : 0 ≤ q2 * u ^ 2 + q1 * u + q0 := by
    have h4 : 0 ≤ 4 * q2 * (q2 * u ^ 2 + q1 * u + q0) := by
      nlinarith only [sq_nonneg (2 * q2 * u + q1), hdisc]
    exact nonneg_of_mul_nonneg_right h4 (by positivity)
  have hcubic : 0 ≤ 2 * D * (u + 1) * (2 * u - 1) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith only [hu0])) (sq_nonneg _)
  have hmain4 : 0 ≤ A * (u + 1) + B * (2 * u ^ 2 - 2) + C * (4 * u ^ 3 - 3 * u + 1) +
      D * (8 * u ^ 4 - 8 * u ^ 2) - 36 * G * (u + 1) := by
    have hid4 : A * (u + 1) + B * (2 * u ^ 2 - 2) + C * (4 * u ^ 3 - 3 * u + 1) +
        D * (8 * u ^ 4 - 8 * u ^ 2) - 36 * G * (u + 1) =
        (u + 1) * (q2 * u ^ 2 + q1 * u + q0 + 2 * D * (u + 1) * (2 * u - 1) ^ 2) := by
      dsimp only [q2, q1, q0]; ring
    rw [hid4]
    exact mul_nonneg (by linarith only [hu0]) (add_nonneg hquad hcubic)
  linarith only [hmain4, he5, hg6]

/-! ## Two-sided logarithm and exponential bounds for all primes `< 91` -/

private theorem le_log_of_two_pow_le {p : ℝ} {k m : ℕ} (hk : 0 < k)
    (h : (2 : ℝ) ^ m ≤ p ^ k) : (m : ℝ) / k * Real.log 2 ≤ Real.log p := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith only [hl]

private theorem log_le_of_pow_le_two_pow {p : ℝ} (hp : 0 < p) {k m : ℕ} (hk : 0 < k)
    (h : p ^ k ≤ (2 : ℝ) ^ m) : Real.log p ≤ (m : ℝ) / k * Real.log 2 := by
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']
  linarith only [hl]

private theorem log_prime_bounds {p : ℝ} (hp : 0 < p) {k1 m1 k2 m2 : ℕ}
    (hk1 : 0 < k1) (hk2 : 0 < k2) (h1 : (2 : ℝ) ^ m1 ≤ p ^ k1) (h2 : p ^ k2 ≤ (2 : ℝ) ^ m2)
    {lo hi : ℝ} (hlo : lo ≤ (m1 : ℝ) / k1 * 0.6931471803)
    (hhi : (m2 : ℝ) / k2 * 0.6931471808 ≤ hi) :
    lo ≤ Real.log p ∧ Real.log p ≤ hi := by
  have hb1 := le_log_of_two_pow_le hk1 h1
  have hb2 := log_le_of_pow_le_two_pow hp hk2 h2
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hpos1 : 0 ≤ (m1 : ℝ) / k1 := by positivity
  have hpos2 : 0 ≤ (m2 : ℝ) / k2 := by positivity
  exact ⟨hlo.trans ((mul_le_mul_of_nonneg_left hl2a.le hpos1).trans hb1),
    hb2.trans ((mul_le_mul_of_nonneg_left hl2b.le hpos2).trans hhi)⟩

private theorem exp_nine_bounds : (89 : ℝ) ^ 2 ≤ Real.exp 9 ∧ Real.exp 9 ≤ (91 : ℝ) ^ 2 := by
  have he9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he9]
  exact ⟨(by norm_num : (89 : ℝ) ^ 2 ≤ 2.7182818283 ^ 9).trans
      (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 9),
    (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 9).trans (by norm_num)⟩

private theorem nine_halves_le_log {n : ℕ} (hn : 91 ≤ n) : (9 / 2 : ℝ) ≤ Real.log n := by
  have hn' : (91 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn']
  rw [Real.le_log_iff_exp_le hn0]
  have hsq : Real.exp (9 / 2) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (9 / 2) = 9 by norm_num]
    exact exp_nine_bounds.2.trans (pow_le_pow_left₀ (by norm_num) hn' 2)
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hn0.le (by norm_num : 2 ≠ 0)).mp hsq

private theorem exp_neg_nine_quarters_bounds :
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

private theorem log_pi_lb_sharp : (1.144498 : ℝ) ≤ Real.log Real.pi := by
  have hpow : (2 : ℝ) ^ 71 ≤ Real.pi ^ 43 :=
    (by norm_num : (2 : ℝ) ^ 71 ≤ 3.14159265 ^ 43).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith [pi_bounds_d10.1]) 43)
  have h := le_log_of_two_pow_le (p := Real.pi) (k := 43) (m := 71) (by norm_num) hpow
  have hl2 := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith only [h, hl2]

/-! ## Explicit prime-phase form at band `9/2` (`N = 91`) -/

/-- Exact Bohman prime-power trigonometric form at `L = 9/2` (`N = 91`), parameterized by an
arbitrary phase `θ p` at each prime `p ≤ 89`. -/
def bohmanPhaseForm (θ : ℕ → ℝ) : ℝ :=
  (Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) * Real.cos (θ 2) +
    Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) * Real.cos (2 * θ 2) +
    Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) * Real.cos (3 * θ 2) +
    Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) * Real.cos (4 * θ 2) +
    Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) * Real.cos (5 * θ 2) +
    Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) * Real.cos (6 * θ 2)) +
  (Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) * Real.cos (θ 3) +
    Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) * Real.cos (2 * θ 3) +
    Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) * Real.cos (3 * θ 3) +
    Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) * Real.cos (4 * θ 3)) +
  (Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) * Real.cos (θ 5) +
    Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) * Real.cos (2 * θ 5)) +
  (Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) * Real.cos (θ 7) +
    Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) * Real.cos (2 * θ 7)) +
  (Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) * Real.cos (θ 11) +
    Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) * Real.cos (θ 13) +
    Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) * Real.cos (θ 17) +
    Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) * Real.cos (θ 19) +
    Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) * Real.cos (θ 23) +
    Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) * Real.cos (θ 29) +
    Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) * Real.cos (θ 31) +
    Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) * Real.cos (θ 37) +
    Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) * Real.cos (θ 41) +
    Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) * Real.cos (θ 43) +
    Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) * Real.cos (θ 47) +
    Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) * Real.cos (θ 53) +
    Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) * Real.cos (θ 59) +
    Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) * Real.cos (θ 61) +
    Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) * Real.cos (θ 67) +
    Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) * Real.cos (θ 71) +
    Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) * Real.cos (θ 73) +
    Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) * Real.cos (θ 79) +
    Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) * Real.cos (θ 83) +
    Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) * Real.cos (θ 89))

private theorem Λ_zero_mul {n a b : ℕ} (heq : n = a * b) (hc : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : vonMangoldt n = 0 :=
  heq ▸ GaloisForLFunctions.BezoutValuationIncidence.vonMangoldt_mul_eq_zero_of_coprime hc ha hb

private theorem Λ_prime_pow {n p k : ℕ} (heq : n = p ^ k) (hp : p.Prime) (hk : k ≠ 0) :
    vonMangoldt n = Real.log p := by
  rw [heq, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

private theorem bohman_block0 (γ : ℝ) :
    ∑ n ∈ Finset.range 30,
        vonMangoldt n / n * bohmanFn (9 / 2) (Real.log n) * Real.cos (γ * Real.log n) =
      Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) * Real.cos (γ * Real.log 2) +
      Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) * Real.cos (γ * Real.log 3) +
      Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) * Real.cos (2 * (γ * Real.log 2)) +
      Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) * Real.cos (γ * Real.log 5) +
      Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) * Real.cos (γ * Real.log 7) +
      Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) * Real.cos (3 * (γ * Real.log 2)) +
      Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) * Real.cos (2 * (γ * Real.log 3)) +
      Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) * Real.cos (γ * Real.log 11) +
      Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) * Real.cos (γ * Real.log 13) +
      Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) * Real.cos (4 * (γ * Real.log 2)) +
      Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) * Real.cos (γ * Real.log 17) +
      Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) * Real.cos (γ * Real.log 19) +
      Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) * Real.cos (γ * Real.log 23) +
      Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) * Real.cos (2 * (γ * Real.log 5)) +
      Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) * Real.cos (3 * (γ * Real.log 3)) +
      Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) * Real.cos (γ * Real.log 29) := by
  have z0 : vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
  have z1 : vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  have z6 : vonMangoldt 6 = 0 := Λ_zero_mul (a := 2) (b := 3) rfl (by norm_num) (by norm_num) (by norm_num)
  have z10 : vonMangoldt 10 = 0 := Λ_zero_mul (a := 2) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z12 : vonMangoldt 12 = 0 := Λ_zero_mul (a := 3) (b := 4) rfl (by norm_num) (by norm_num) (by norm_num)
  have z14 : vonMangoldt 14 = 0 := Λ_zero_mul (a := 2) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z15 : vonMangoldt 15 = 0 := Λ_zero_mul (a := 3) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z18 : vonMangoldt 18 = 0 := Λ_zero_mul (a := 2) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z20 : vonMangoldt 20 = 0 := Λ_zero_mul (a := 4) (b := 5) rfl (by norm_num) (by norm_num) (by norm_num)
  have z21 : vonMangoldt 21 = 0 := Λ_zero_mul (a := 3) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z22 : vonMangoldt 22 = 0 := Λ_zero_mul (a := 2) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z24 : vonMangoldt 24 = 0 := Λ_zero_mul (a := 3) (b := 8) rfl (by norm_num) (by norm_num) (by norm_num)
  have z26 : vonMangoldt 26 = 0 := Λ_zero_mul (a := 2) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z28 : vonMangoldt 28 = 0 := Λ_zero_mul (a := 4) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have p2 : vonMangoldt 2 = Real.log 2 := Λ_prime_pow (p := 2) (k := 1) rfl (by norm_num) (by norm_num)
  have p3 : vonMangoldt 3 = Real.log 3 := Λ_prime_pow (p := 3) (k := 1) rfl (by norm_num) (by norm_num)
  have p4 : vonMangoldt 4 = Real.log 2 := Λ_prime_pow (p := 2) (k := 2) rfl (by norm_num) (by norm_num)
  have p5 : vonMangoldt 5 = Real.log 5 := Λ_prime_pow (p := 5) (k := 1) rfl (by norm_num) (by norm_num)
  have p7 : vonMangoldt 7 = Real.log 7 := Λ_prime_pow (p := 7) (k := 1) rfl (by norm_num) (by norm_num)
  have p8 : vonMangoldt 8 = Real.log 2 := Λ_prime_pow (p := 2) (k := 3) rfl (by norm_num) (by norm_num)
  have p9 : vonMangoldt 9 = Real.log 3 := Λ_prime_pow (p := 3) (k := 2) rfl (by norm_num) (by norm_num)
  have p11 : vonMangoldt 11 = Real.log 11 := Λ_prime_pow (p := 11) (k := 1) rfl (by norm_num) (by norm_num)
  have p13 : vonMangoldt 13 = Real.log 13 := Λ_prime_pow (p := 13) (k := 1) rfl (by norm_num) (by norm_num)
  have p16 : vonMangoldt 16 = Real.log 2 := Λ_prime_pow (p := 2) (k := 4) rfl (by norm_num) (by norm_num)
  have p17 : vonMangoldt 17 = Real.log 17 := Λ_prime_pow (p := 17) (k := 1) rfl (by norm_num) (by norm_num)
  have p19 : vonMangoldt 19 = Real.log 19 := Λ_prime_pow (p := 19) (k := 1) rfl (by norm_num) (by norm_num)
  have p23 : vonMangoldt 23 = Real.log 23 := Λ_prime_pow (p := 23) (k := 1) rfl (by norm_num) (by norm_num)
  have p25 : vonMangoldt 25 = Real.log 5 := Λ_prime_pow (p := 5) (k := 2) rfl (by norm_num) (by norm_num)
  have p27 : vonMangoldt 27 = Real.log 3 := Λ_prime_pow (p := 3) (k := 3) rfl (by norm_num) (by norm_num)
  have p29 : vonMangoldt 29 = Real.log 29 := Λ_prime_pow (p := 29) (k := 1) rfl (by norm_num) (by norm_num)
  have l4 : Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l9 : Real.log 9 = 2 * Real.log 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l16 : Real.log 16 = 4 * Real.log 2 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have l25 : Real.log 25 = 2 * Real.log 5 := by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l27 : Real.log 27 = 3 * Real.log 3 := by rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
    Nat.cast_one, z0, z1, z6, z10, z12, z14, z15, z18, z20, z21, z22, z24, z26, z28,
    p2, p3, p4, p5, p7, p8, p9, p11, p13, p16, p17, p19, p23, p25, p27, p29,
    zero_div, zero_mul, zero_add, add_zero, one_mul, l4, l8, l9, l16, l25, l27]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman_block1 (γ : ℝ) :
    ∑ n ∈ Finset.range 30,
        vonMangoldt (30 + n) / ((30 + n : ℕ) : ℝ) *
          bohmanFn (9 / 2) (Real.log ((30 + n : ℕ) : ℝ)) *
          Real.cos (γ * Real.log ((30 + n : ℕ) : ℝ)) =
      Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) * Real.cos (γ * Real.log 31) +
      Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) * Real.cos (5 * (γ * Real.log 2)) +
      Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) * Real.cos (γ * Real.log 37) +
      Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) * Real.cos (γ * Real.log 41) +
      Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) * Real.cos (γ * Real.log 43) +
      Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) * Real.cos (γ * Real.log 47) +
      Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) * Real.cos (2 * (γ * Real.log 7)) +
      Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) * Real.cos (γ * Real.log 53) +
      Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) * Real.cos (γ * Real.log 59) := by
  have z30 : vonMangoldt 30 = 0 := Λ_zero_mul (a := 2) (b := 15) rfl (by norm_num) (by norm_num) (by norm_num)
  have z33 : vonMangoldt 33 = 0 := Λ_zero_mul (a := 3) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z34 : vonMangoldt 34 = 0 := Λ_zero_mul (a := 2) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z35 : vonMangoldt 35 = 0 := Λ_zero_mul (a := 5) (b := 7) rfl (by norm_num) (by norm_num) (by norm_num)
  have z36 : vonMangoldt 36 = 0 := Λ_zero_mul (a := 4) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z38 : vonMangoldt 38 = 0 := Λ_zero_mul (a := 2) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z39 : vonMangoldt 39 = 0 := Λ_zero_mul (a := 3) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z40 : vonMangoldt 40 = 0 := Λ_zero_mul (a := 5) (b := 8) rfl (by norm_num) (by norm_num) (by norm_num)
  have z42 : vonMangoldt 42 = 0 := Λ_zero_mul (a := 2) (b := 21) rfl (by norm_num) (by norm_num) (by norm_num)
  have z44 : vonMangoldt 44 = 0 := Λ_zero_mul (a := 4) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z45 : vonMangoldt 45 = 0 := Λ_zero_mul (a := 5) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z46 : vonMangoldt 46 = 0 := Λ_zero_mul (a := 2) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z48 : vonMangoldt 48 = 0 := Λ_zero_mul (a := 3) (b := 16) rfl (by norm_num) (by norm_num) (by norm_num)
  have z50 : vonMangoldt 50 = 0 := Λ_zero_mul (a := 2) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z51 : vonMangoldt 51 = 0 := Λ_zero_mul (a := 3) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z52 : vonMangoldt 52 = 0 := Λ_zero_mul (a := 4) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z54 : vonMangoldt 54 = 0 := Λ_zero_mul (a := 2) (b := 27) rfl (by norm_num) (by norm_num) (by norm_num)
  have z55 : vonMangoldt 55 = 0 := Λ_zero_mul (a := 5) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z56 : vonMangoldt 56 = 0 := Λ_zero_mul (a := 7) (b := 8) rfl (by norm_num) (by norm_num) (by norm_num)
  have z57 : vonMangoldt 57 = 0 := Λ_zero_mul (a := 3) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z58 : vonMangoldt 58 = 0 := Λ_zero_mul (a := 2) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have p31 : vonMangoldt 31 = Real.log 31 := Λ_prime_pow (p := 31) (k := 1) rfl (by norm_num) (by norm_num)
  have p32 : vonMangoldt 32 = Real.log 2 := Λ_prime_pow (p := 2) (k := 5) rfl (by norm_num) (by norm_num)
  have p37 : vonMangoldt 37 = Real.log 37 := Λ_prime_pow (p := 37) (k := 1) rfl (by norm_num) (by norm_num)
  have p41 : vonMangoldt 41 = Real.log 41 := Λ_prime_pow (p := 41) (k := 1) rfl (by norm_num) (by norm_num)
  have p43 : vonMangoldt 43 = Real.log 43 := Λ_prime_pow (p := 43) (k := 1) rfl (by norm_num) (by norm_num)
  have p47 : vonMangoldt 47 = Real.log 47 := Λ_prime_pow (p := 47) (k := 1) rfl (by norm_num) (by norm_num)
  have p49 : vonMangoldt 49 = Real.log 7 := Λ_prime_pow (p := 7) (k := 2) rfl (by norm_num) (by norm_num)
  have p53 : vonMangoldt 53 = Real.log 53 := Λ_prime_pow (p := 53) (k := 1) rfl (by norm_num) (by norm_num)
  have p59 : vonMangoldt 59 = Real.log 59 := Λ_prime_pow (p := 59) (k := 1) rfl (by norm_num) (by norm_num)
  have l32 : Real.log 32 = 5 * Real.log 2 := by rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have l49 : Real.log 49 = 2 * Real.log 7 := by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat,
    z30, z33, z34, z35, z36, z38, z39, z40, z42, z44, z45, z46, z48, z50, z51, z52, z54, z55,
    z56, z57, z58, p31, p32, p37, p41, p43, p47, p49, p53, p59,
    zero_div, zero_mul, zero_add, add_zero, one_mul, l32, l49]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

private theorem bohman_block2 (γ : ℝ) :
    ∑ n ∈ Finset.range 31,
        vonMangoldt (60 + n) / ((60 + n : ℕ) : ℝ) *
          bohmanFn (9 / 2) (Real.log ((60 + n : ℕ) : ℝ)) *
          Real.cos (γ * Real.log ((60 + n : ℕ) : ℝ)) =
      Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) * Real.cos (γ * Real.log 61) +
      Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) * Real.cos (6 * (γ * Real.log 2)) +
      Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) * Real.cos (γ * Real.log 67) +
      Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) * Real.cos (γ * Real.log 71) +
      Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) * Real.cos (γ * Real.log 73) +
      Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) * Real.cos (γ * Real.log 79) +
      Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) * Real.cos (4 * (γ * Real.log 3)) +
      Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) * Real.cos (γ * Real.log 83) +
      Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) * Real.cos (γ * Real.log 89) := by
  have z60 : vonMangoldt 60 = 0 := Λ_zero_mul (a := 4) (b := 15) rfl (by norm_num) (by norm_num) (by norm_num)
  have z62 : vonMangoldt 62 = 0 := Λ_zero_mul (a := 2) (b := 31) rfl (by norm_num) (by norm_num) (by norm_num)
  have z63 : vonMangoldt 63 = 0 := Λ_zero_mul (a := 7) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z65 : vonMangoldt 65 = 0 := Λ_zero_mul (a := 5) (b := 13) rfl (by norm_num) (by norm_num) (by norm_num)
  have z66 : vonMangoldt 66 = 0 := Λ_zero_mul (a := 2) (b := 33) rfl (by norm_num) (by norm_num) (by norm_num)
  have z68 : vonMangoldt 68 = 0 := Λ_zero_mul (a := 4) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z69 : vonMangoldt 69 = 0 := Λ_zero_mul (a := 3) (b := 23) rfl (by norm_num) (by norm_num) (by norm_num)
  have z70 : vonMangoldt 70 = 0 := Λ_zero_mul (a := 2) (b := 35) rfl (by norm_num) (by norm_num) (by norm_num)
  have z72 : vonMangoldt 72 = 0 := Λ_zero_mul (a := 8) (b := 9) rfl (by norm_num) (by norm_num) (by norm_num)
  have z74 : vonMangoldt 74 = 0 := Λ_zero_mul (a := 2) (b := 37) rfl (by norm_num) (by norm_num) (by norm_num)
  have z75 : vonMangoldt 75 = 0 := Λ_zero_mul (a := 3) (b := 25) rfl (by norm_num) (by norm_num) (by norm_num)
  have z76 : vonMangoldt 76 = 0 := Λ_zero_mul (a := 4) (b := 19) rfl (by norm_num) (by norm_num) (by norm_num)
  have z77 : vonMangoldt 77 = 0 := Λ_zero_mul (a := 7) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z78 : vonMangoldt 78 = 0 := Λ_zero_mul (a := 2) (b := 39) rfl (by norm_num) (by norm_num) (by norm_num)
  have z80 : vonMangoldt 80 = 0 := Λ_zero_mul (a := 5) (b := 16) rfl (by norm_num) (by norm_num) (by norm_num)
  have z82 : vonMangoldt 82 = 0 := Λ_zero_mul (a := 2) (b := 41) rfl (by norm_num) (by norm_num) (by norm_num)
  have z84 : vonMangoldt 84 = 0 := Λ_zero_mul (a := 3) (b := 28) rfl (by norm_num) (by norm_num) (by norm_num)
  have z85 : vonMangoldt 85 = 0 := Λ_zero_mul (a := 5) (b := 17) rfl (by norm_num) (by norm_num) (by norm_num)
  have z86 : vonMangoldt 86 = 0 := Λ_zero_mul (a := 2) (b := 43) rfl (by norm_num) (by norm_num) (by norm_num)
  have z87 : vonMangoldt 87 = 0 := Λ_zero_mul (a := 3) (b := 29) rfl (by norm_num) (by norm_num) (by norm_num)
  have z88 : vonMangoldt 88 = 0 := Λ_zero_mul (a := 8) (b := 11) rfl (by norm_num) (by norm_num) (by norm_num)
  have z90 : vonMangoldt 90 = 0 := Λ_zero_mul (a := 2) (b := 45) rfl (by norm_num) (by norm_num) (by norm_num)
  have p61 : vonMangoldt 61 = Real.log 61 := Λ_prime_pow (p := 61) (k := 1) rfl (by norm_num) (by norm_num)
  have p64 : vonMangoldt 64 = Real.log 2 := Λ_prime_pow (p := 2) (k := 6) rfl (by norm_num) (by norm_num)
  have p67 : vonMangoldt 67 = Real.log 67 := Λ_prime_pow (p := 67) (k := 1) rfl (by norm_num) (by norm_num)
  have p71 : vonMangoldt 71 = Real.log 71 := Λ_prime_pow (p := 71) (k := 1) rfl (by norm_num) (by norm_num)
  have p73 : vonMangoldt 73 = Real.log 73 := Λ_prime_pow (p := 73) (k := 1) rfl (by norm_num) (by norm_num)
  have p79 : vonMangoldt 79 = Real.log 79 := Λ_prime_pow (p := 79) (k := 1) rfl (by norm_num) (by norm_num)
  have p81 : vonMangoldt 81 = Real.log 3 := Λ_prime_pow (p := 3) (k := 4) rfl (by norm_num) (by norm_num)
  have p83 : vonMangoldt 83 = Real.log 83 := Λ_prime_pow (p := 83) (k := 1) rfl (by norm_num) (by norm_num)
  have p89 : vonMangoldt 89 = Real.log 89 := Λ_prime_pow (p := 89) (k := 1) rfl (by norm_num) (by norm_num)
  have l64 : Real.log 64 = 6 * Real.log 2 := by rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have l81 : Real.log 81 = 4 * Real.log 3 := by rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]; norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat,
    z60, z62, z63, z65, z66, z68, z69, z70, z72, z74, z75, z76, z77, z78, z80, z82, z84, z85,
    z86, z87, z88, z90, p61, p64, p67, p71, p73, p79, p81, p83, p89,
    zero_div, zero_mul, zero_add, add_zero, one_mul, l64, l81]
  simp only [show ∀ (k a : ℝ), γ * (k * a) = k * (γ * a) from fun k a => by ring]

theorem bohman_prime_sum_eq_phaseForm (γ : ℝ) :
    ∑ n ∈ Finset.range 91,
        vonMangoldt n / n * bohmanFn (9 / 2) (Real.log n) * Real.cos (γ * Real.log n) =
      bohmanPhaseForm (fun p => γ * Real.log (p : ℝ)) := by
  let g (n : ℕ) : ℝ :=
    vonMangoldt n / n * bohmanFn (9 / 2) (Real.log n) * Real.cos (γ * Real.log n)
  change ∑ n ∈ Finset.range 91, g n = _
  rw [show (91 : ℕ) = 60 + 31 from rfl, Finset.sum_range_add,
    show (60 : ℕ) = 30 + 30 from rfl, Finset.sum_range_add]
  dsimp only [g]
  rw [bohman_block0, bohman_block1, bohman_block2]
  unfold bohmanPhaseForm
  norm_num
  ring

/-! ## Chebyshev expansion and global phase-free floor of `bohmanPhaseForm` -/

private theorem cos_chebyshev_six (θ : ℝ) :
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
    have hr := hrec 3
    norm_num at hr
    rw [hr, h3, h2]; ring
  have h5 : Real.cos (5 * θ) = 16 * Real.cos θ ^ 5 - 20 * Real.cos θ ^ 3 + 5 * Real.cos θ := by
    have hr := hrec 4
    norm_num at hr
    rw [hr, h4, h3]; ring
  have h6 : Real.cos (6 * θ) = 32 * Real.cos θ ^ 6 - 48 * Real.cos θ ^ 4 + 18 * Real.cos θ ^ 2 - 1 := by
    have hr := hrec 5
    norm_num at hr
    rw [hr, h5, h4]; ring
  exact ⟨h2, h3, h4, h5, h6⟩

private theorem all_prime_bohman_coeff_bounds :
    (0.3096269 ≤ Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) ∧
      Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) ≤ 0.3109196) ∧
    (0.1133596 ≤ Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) ∧
      Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2) ≤ 0.1134315) ∧
    (0.0329179 ≤ Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) ∧
      Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) ≤ 0.0329207) ∧
    (0.0069486 ≤ Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) ∧
      Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2) ≤ 0.0069489) ∧
    (0.0008209 ≤ Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) ∧
      Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2) ≤ 0.0008210) ∧
    (0.0000154 ≤ Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) ∧
      Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2) ≤ 0.0000155) ∧
    (0.2797659 ≤ Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) ∧
      Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) ≤ 0.2802868) ∧
    (0.0411017 ≤ Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) ∧
      Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) ≤ 0.0411443) ∧
    (0.0023832 ≤ Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) ∧
      Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) ≤ 0.0023895) ∧
    (0.0000005 ≤ Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) ∧
      Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3) ≤ 0.0000006) ∧
    (0.1816415 ≤ Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) ∧
      Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) ≤ 0.1818962) ∧
    (0.0044971 ≤ Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) ∧
      Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5) ≤ 0.0045154) ∧
    (0.1196666 ≤ Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) ∧
      Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) ≤ 0.1198266) ∧
    (0.0003159 ≤ Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) ∧
      Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7) ≤ 0.0003188) ∧
    (0.0585011 ≤ Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) ∧
      Real.log 11 / 11 * bohmanFn (9 / 2) (1 * Real.log 11) ≤ 0.0585794) ∧
    (0.0427132 ≤ Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) ∧
      Real.log 13 / 13 * bohmanFn (9 / 2) (1 * Real.log 13) ≤ 0.0428245) ∧
    (0.0242427 ≤ Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) ∧
      Real.log 17 / 17 * bohmanFn (9 / 2) (1 * Real.log 17) ≤ 0.0242863) ∧
    (0.0186189 ≤ Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) ∧
      Real.log 19 / 19 * bohmanFn (9 / 2) (1 * Real.log 19) ≤ 0.0187489) ∧
    (0.0113990 ≤ Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) ∧
      Real.log 23 / 23 * bohmanFn (9 / 2) (1 * Real.log 23) ≤ 0.0114201) ∧
    (0.0056981 ≤ Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) ∧
      Real.log 29 / 29 * bohmanFn (9 / 2) (1 * Real.log 29) ≤ 0.0057307) ∧
    (0.0045777 ≤ Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) ∧
      Real.log 31 / 31 * bohmanFn (9 / 2) (1 * Real.log 31) ≤ 0.0045883) ∧
    (0.0023761 ≤ Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) ∧
      Real.log 37 / 37 * bohmanFn (9 / 2) (1 * Real.log 37) ≤ 0.0023836) ∧
    (0.0015372 ≤ Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) ∧
      Real.log 41 / 41 * bohmanFn (9 / 2) (1 * Real.log 41) ≤ 0.0015452) ∧
    (0.0012316 ≤ Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) ∧
      Real.log 43 / 43 * bohmanFn (9 / 2) (1 * Real.log 43) ≤ 0.0012449) ∧
    (0.0007923 ≤ Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) ∧
      Real.log 47 / 47 * bohmanFn (9 / 2) (1 * Real.log 47) ≤ 0.0008002) ∧
    (0.0003936 ≤ Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) ∧
      Real.log 53 / 53 * bohmanFn (9 / 2) (1 * Real.log 53) ≤ 0.0003977) ∧
    (0.0001846 ≤ Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) ∧
      Real.log 59 / 59 * bohmanFn (9 / 2) (1 * Real.log 59) ≤ 0.0001869) ∧
    (0.0001420 ≤ Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) ∧
      Real.log 61 / 61 * bohmanFn (9 / 2) (1 * Real.log 61) ≤ 0.0001440) ∧
    (0.0000578 ≤ Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) ∧
      Real.log 67 / 67 * bohmanFn (9 / 2) (1 * Real.log 67) ≤ 0.0000588) ∧
    (0.0000288 ≤ Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) ∧
      Real.log 71 / 71 * bohmanFn (9 / 2) (1 * Real.log 71) ≤ 0.0000294) ∧
    (0.0000193 ≤ Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) ∧
      Real.log 73 / 73 * bohmanFn (9 / 2) (1 * Real.log 73) ≤ 0.0000197) ∧
    (0.0000043 ≤ Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) ∧
      Real.log 79 / 79 * bohmanFn (9 / 2) (1 * Real.log 79) ≤ 0.0000045) ∧
    (0.0000009 ≤ Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) ∧
      Real.log 83 / 83 * bohmanFn (9 / 2) (1 * Real.log 83) ≤ 0.0000011) ∧
    (0.0000000 ≤ Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) ∧
      Real.log 89 / 89 * bohmanFn (9 / 2) (1 * Real.log 89) ≤ 0.0000001) := by
  have hl2a := Real.log_two_gt_d9.le
  have hl2b := Real.log_two_lt_d9.le
  obtain ⟨hl3a, hl3b⟩ := log_prime_bounds (p := 3) (by norm_num) (k1 := 53) (m1 := 84)
    (k2 := 41) (m2 := 65) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.098572) (hi := 1.098892) (by norm_num) (by norm_num)
  obtain ⟨hl5a, hl5b⟩ := log_prime_bounds (p := 5) (by norm_num) (k1 := 28) (m1 := 65)
    (k2 := 31) (m2 := 72) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.609091) (hi := 1.609891) (by norm_num) (by norm_num)
  obtain ⟨hl7a, hl7b⟩ := log_prime_bounds (p := 7) (by norm_num) (k1 := 31) (m1 := 87)
    (k2 := 26) (m2 := 73) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.945284) (hi := 1.946145) (by norm_num) (by norm_num)
  obtain ⟨hl11a, hl11b⟩ := log_prime_bounds (p := 11) (by norm_num) (k1 := 24) (m1 := 83)
    (k2 := 37) (m2 := 128) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 2.39713) (hi := 2.39792) (by norm_num) (by norm_num)
  obtain ⟨hl13a, hl13b⟩ := log_prime_bounds (p := 13) (by norm_num) (k1 := 10) (m1 := 37)
    (k2 := 47) (m2 := 174) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 2.56464) (hi := 2.56612) (by norm_num) (by norm_num)
  obtain ⟨hl17a, hl17b⟩ := log_prime_bounds (p := 17) (by norm_num) (k1 := 23) (m1 := 94)
    (k2 := 34) (m2 := 139) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 2.83286) (hi := 2.83375) (by norm_num) (by norm_num)
  obtain ⟨hl19a, hl19b⟩ := log_prime_bounds (p := 19) (by norm_num) (k1 := 53) (m1 := 225)
    (k2 := 4) (m2 := 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 2.94260) (hi := 2.94588) (by norm_num) (by norm_num)
  obtain ⟨hl23a, hl23b⟩ := log_prime_bounds (p := 23) (by norm_num) (k1 := 44) (m1 := 199)
    (k2 := 21) (m2 := 95) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.13491) (hi := 3.13567) (by norm_num) (by norm_num)
  obtain ⟨hl29a, hl29b⟩ := log_prime_bounds (p := 29) (by norm_num) (k1 := 7) (m1 := 34)
    (k2 := 50) (m2 := 243) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.36671) (hi := 3.36870) (by norm_num) (by norm_num)
  obtain ⟨hl31a, hl31b⟩ := log_prime_bounds (p := 31) (by norm_num) (k1 := 43) (m1 := 213)
    (k2 := 22) (m2 := 109) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.43349) (hi := 3.43423) (by norm_num) (by norm_num)
  obtain ⟨hl37a, hl37b⟩ := log_prime_bounds (p := 37) (by norm_num) (k1 := 43) (m1 := 224)
    (k2 := 19) (m2 := 99) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.61081) (hi := 3.61167) (by norm_num) (by norm_num)
  obtain ⟨hl41a, hl41b⟩ := log_prime_bounds (p := 41) (by norm_num) (k1 := 14) (m1 := 75)
    (k2 := 39) (m2 := 209) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.71328) (hi := 3.71456) (by norm_num) (by norm_num)
  obtain ⟨hl43a, hl43b⟩ := log_prime_bounds (p := 43) (by norm_num) (k1 := 40) (m1 := 217)
    (k2 := 7) (m2 := 38) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.76032) (hi := 3.76280) (by norm_num) (by norm_num)
  obtain ⟨hl47a, hl47b⟩ := log_prime_bounds (p := 47) (by norm_num) (k1 := 38) (m1 := 211)
    (k2 := 9) (m2 := 50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.84879) (hi := 3.85082) (by norm_num) (by norm_num)
  obtain ⟨hl53a, hl53b⟩ := log_prime_bounds (p := 53) (by norm_num) (k1 := 11) (m1 := 63)
    (k2 := 37) (m2 := 212) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 3.96984) (hi := 3.97155) (by norm_num) (by norm_num)
  obtain ⟨hl59a, hl59b⟩ := log_prime_bounds (p := 59) (by norm_num) (k1 := 17) (m1 := 100)
    (k2 := 26) (m2 := 153) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.07733) (hi := 4.07891) (by norm_num) (by norm_num)
  obtain ⟨hl61a, hl61b⟩ := log_prime_bounds (p := 61) (by norm_num) (k1 := 14) (m1 := 83)
    (k2 := 29) (m2 := 172) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.10937) (hi := 4.11108) (by norm_num) (by norm_num)
  obtain ⟨hl67a, hl67b⟩ := log_prime_bounds (p := 67) (by norm_num) (k1 := 31) (m1 := 188)
    (k2 := 15) (m2 := 91) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.20360) (hi := 4.20510) (by norm_num) (by norm_num)
  obtain ⟨hl71a, hl71b⟩ := log_prime_bounds (p := 71) (by norm_num) (k1 := 27) (m1 := 166)
    (k2 := 20) (m2 := 123) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.26157) (hi := 4.26286) (by norm_num) (by norm_num)
  obtain ⟨hl73a, hl73b⟩ := log_prime_bounds (p := 73) (by norm_num) (k1 := 37) (m1 := 229)
    (k2 := 21) (m2 := 130) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.29001) (hi := 4.29092) (by norm_num) (by norm_num)
  obtain ⟨hl79a, hl79b⟩ := log_prime_bounds (p := 79) (by norm_num) (k1 := 33) (m1 := 208)
    (k2 := 23) (m2 := 145) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.36892) (hi := 4.36985) (by norm_num) (by norm_num)
  obtain ⟨hl83a, hl83b⟩ := log_prime_bounds (p := 83) (by norm_num) (k1 := 8) (m1 := 51)
    (k2 := 37) (m2 := 236) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.41881) (hi := 4.42116) (by norm_num) (by norm_num)
  obtain ⟨hl89a, hl89b⟩ := log_prime_bounds (p := 89) (by norm_num) (k1 := 19) (m1 := 123)
    (k2 := 21) (m2 := 136) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 4.48721) (hi := 4.48896) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bohman_coeff_bounds (u_lo := 2.65768) (u_hi := 2.65769) (by norm_num) (by norm_num)
      (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 2.17377) (u_hi := 2.17378) (by norm_num) (by norm_num)
      (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.68986) (u_hi := 1.68987) (by norm_num) (by norm_num)
      (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.20596) (u_hi := 1.20597) (by norm_num) (by norm_num)
      (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.72205) (u_hi := 0.72206) (by norm_num) (by norm_num)
      (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.23814) (u_hi := 0.23815) (by norm_num) (by norm_num)
      (by norm_num) hl2a hl2b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 2.37442) (u_hi := 2.37465) (by norm_num) (by norm_num)
      (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.60724) (u_hi := 1.60770) (by norm_num) (by norm_num)
      (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.84007) (u_hi := 0.84075) (by norm_num) (by norm_num)
      (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.07290) (u_hi := 0.07381) (by norm_num) (by norm_num)
      (by norm_num) hl3a hl3b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 2.01767) (u_hi := 2.01824) (by norm_num) (by norm_num)
      (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.89376) (u_hi := 0.89488) (by norm_num) (by norm_num)
      (by norm_num) hl5a hl5b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.78292) (u_hi := 1.78353) (by norm_num) (by norm_num)
      (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.42426) (u_hi := 0.42547) (by norm_num) (by norm_num)
      (by norm_num) hl7a hl7b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.46752) (u_hi := 1.46809) (by norm_num) (by norm_num)
      (by norm_num) hl11a hl11b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.35010) (u_hi := 1.35114) (by norm_num) (by norm_num)
      (by norm_num) hl13a hl13b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.16326) (u_hi := 1.16389) (by norm_num) (by norm_num)
      (by norm_num) hl17a hl17b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 1.08498) (u_hi := 1.08728) (by norm_num) (by norm_num)
      (by norm_num) hl19a hl19b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.95248) (u_hi := 0.95302) (by norm_num) (by norm_num)
      (by norm_num) hl23a hl23b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.78979) (u_hi := 0.79119) (by norm_num) (by norm_num)
      (by norm_num) hl29a hl29b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.74404) (u_hi := 0.74457) (by norm_num) (by norm_num)
      (by norm_num) hl31a hl31b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.62017) (u_hi := 0.62078) (by norm_num) (by norm_num)
      (by norm_num) hl37a hl37b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.54834) (u_hi := 0.54924) (by norm_num) (by norm_num)
      (by norm_num) hl41a hl41b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.51466) (u_hi := 0.51640) (by norm_num) (by norm_num)
      (by norm_num) hl43a hl43b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.45321) (u_hi := 0.45464) (by norm_num) (by norm_num)
      (by norm_num) hl47a hl47b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.36892) (u_hi := 0.37013) (by norm_num) (by norm_num)
      (by norm_num) hl53a hl53b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.29397) (u_hi := 0.29508) (by norm_num) (by norm_num)
      (by norm_num) hl59a hl59b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.27151) (u_hi := 0.27272) (by norm_num) (by norm_num)
      (by norm_num) hl61a hl61b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.20587) (u_hi := 0.20693) (by norm_num) (by norm_num)
      (by norm_num) hl67a hl67b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.16555) (u_hi := 0.16646) (by norm_num) (by norm_num)
      (by norm_num) hl71a hl71b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.14596) (u_hi := 0.14661) (by norm_num) (by norm_num)
      (by norm_num) hl73a hl73b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.09086) (u_hi := 0.09152) (by norm_num) (by norm_num)
      (by norm_num) hl79a hl79b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.05504) (u_hi := 0.05669) (by norm_num) (by norm_num)
      (by norm_num) hl83a hl83b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)
  · exact bohman_coeff_bounds (u_lo := 0.00770) (u_hi := 0.00893) (by norm_num) (by norm_num)
      (by norm_num) hl89a hl89b (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by unfold bohmanP9; norm_num) (by unfold bohmanP11 bohmanP9; norm_num)

private theorem neg_ub_le_mul_cos {c ub θ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ ub) :
    -ub ≤ c * Real.cos θ := by
  have := Real.neg_one_le_cos θ
  nlinarith only [this, hc0, hc]

/-- **Phase-free lower bound across all independent prime phases `θ : ℕ → ℝ`.** -/
theorem bohmanPhaseForm_ge (θ : ℕ → ℝ) :
    -(0.935816 : ℝ) ≤ bohmanPhaseForm θ := by
  obtain ⟨⟨b2_1l, b2_1u⟩, ⟨b2_2l, b2_2u⟩, ⟨b2_3l, b2_3u⟩, ⟨b2_4l, b2_4u⟩, ⟨b2_5l, b2_5u⟩,
    ⟨b2_6l, b2_6u⟩, ⟨b3_1l, b3_1u⟩, ⟨b3_2l, b3_2u⟩, ⟨b3_3l, b3_3u⟩, ⟨b3_4l, b3_4u⟩,
    ⟨b5_1l, b5_1u⟩, ⟨b5_2l, b5_2u⟩, ⟨b7_1l, b7_1u⟩, ⟨b7_2l, b7_2u⟩,
    ⟨b11l, b11u⟩, ⟨b13l, b13u⟩, ⟨b17l, b17u⟩, ⟨b19l, b19u⟩, ⟨b23l, b23u⟩, ⟨b29l, b29u⟩,
    ⟨b31l, b31u⟩, ⟨b37l, b37u⟩, ⟨b41l, b41u⟩, ⟨b43l, b43u⟩, ⟨b47l, b47u⟩, ⟨b53l, b53u⟩,
    ⟨b59l, b59u⟩, ⟨b61l, b61u⟩, ⟨b67l, b67u⟩, ⟨b71l, b71u⟩, ⟨b73l, b73u⟩, ⟨b79l, b79u⟩,
    ⟨b83l, b83u⟩, ⟨b89l, b89u⟩⟩ := all_prime_bohman_coeff_bounds
  unfold bohmanPhaseForm
  obtain ⟨c2_2, c2_3, c2_4, c2_5, c2_6⟩ := cos_chebyshev_six (θ 2)
  obtain ⟨c3_2, c3_3, c3_4, -, -⟩ := cos_chebyshev_six (θ 3)
  have c5_2 : Real.cos (2 * θ 5) = 2 * Real.cos (θ 5) ^ 2 - 1 := Real.cos_two_mul _
  have c7_2 : Real.cos (2 * θ 7) = 2 * Real.cos (θ 7) ^ 2 - 1 := Real.cos_two_mul _
  rw [c2_2, c2_3, c2_4, c2_5, c2_6, c3_2, c3_3, c3_4, c5_2, c7_2]
  have hf2 := family_two_six
    (A := Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2))
    (B := Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2))
    (C := Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2))
    (D := Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
    (E := Real.log 2 / 32 * bohmanFn (9 / 2) (5 * Real.log 2))
    (G := Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2))
    (u := Real.cos (θ 2)) (Real.neg_one_le_cos _) (Real.cos_le_one _)
    (by linarith only [b2_4l]) (by linarith only [b2_5l]) (by linarith only [b2_6l])
    (by linarith only [b2_3l, b2_4u])
    (by
      set q1 := 2 * (Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2)) -
        4 * (Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2)) +
        6 * (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
      set q2 := 4 * (Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2)) -
        8 * (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2))
      set q0 := Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) -
        2 * (Real.log 2 / 4 * bohmanFn (9 / 2) (2 * Real.log 2)) +
        Real.log 2 / 8 * bohmanFn (9 / 2) (3 * Real.log 2) -
        2 * (Real.log 2 / 16 * bohmanFn (9 / 2) (4 * Real.log 2)) -
        36 * (Real.log 2 / 64 * bohmanFn (9 / 2) (6 * Real.log 2))
      have hq1_0 : 0 ≤ q1 := by dsimp only [q1]; linarith only [b2_2l, b2_3u, b2_4l]
      have hq1_hi : q1 ≤ 0.1369 := by dsimp only [q1]; linarith only [b2_2u, b2_3l, b2_4u]
      have hq2_lo : (0.0760 : ℝ) ≤ q2 := by dsimp only [q2]; linarith only [b2_3l, b2_4u]
      have hq0_lo : (0.1012 : ℝ) ≤ q0 := by
        dsimp only [q0]; linarith only [b2_1l, b2_2u, b2_3l, b2_4u, b2_6u]
      have hsq := pow_le_pow_left₀ hq1_0 hq1_hi 2
      have hm := mul_le_mul hq2_lo hq0_lo (by norm_num) (by linarith only [hq2_lo])
      norm_num at hsq hm ⊢
      linarith only [hsq, hm])
  have hf3 := family_two
    (A := Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3))
    (B := Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3))
    (C := Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3))
    (D := Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3))
    (u := Real.cos (θ 3)) (Real.neg_one_le_cos _) (Real.cos_le_one _)
    (by linarith only [b3_3l]) (by linarith only [b3_4l])
    (by
      have hB0 : 0 ≤ Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) := by linarith only [b3_2l]
      have hC0 : (0.00238 : ℝ) ≤ Real.log 3 / 27 * bohmanFn (9 / 2) (3 * Real.log 3) := by
        linarith only [b3_3l]
      have he0 : (0.2386 : ℝ) ≤ Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) -
          Real.log 3 / 9 * bohmanFn (9 / 2) (2 * Real.log 3) -
          16 * (Real.log 3 / 81 * bohmanFn (9 / 2) (4 * Real.log 3)) := by
        linarith only [b3_1l, b3_2u, b3_4u]
      have hsq := pow_le_pow_left₀ hB0 b3_2u 2
      have hm := mul_le_mul hC0 he0 (by norm_num) (by linarith only [hC0])
      norm_num at hsq hm ⊢
      linarith only [hsq, hm])
  have hf5 := family_three
    (E := Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5))
    (F := Real.log 5 / 25 * bohmanFn (9 / 2) (2 * Real.log 5))
    (u := Real.cos (θ 5)) (Real.neg_one_le_cos _)
    (by linarith only [b5_2l]) (by linarith only [b5_1l, b5_2u])
  have hf7 := family_three
    (E := Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7))
    (F := Real.log 7 / 49 * bohmanFn (9 / 2) (2 * Real.log 7))
    (u := Real.cos (θ 7)) (Real.neg_one_le_cos _)
    (by linarith only [b7_2l]) (by linarith only [b7_1l, b7_2u])
  have s11 := neg_ub_le_mul_cos (θ := θ 11) (by linarith only [b11l]) b11u
  have s13 := neg_ub_le_mul_cos (θ := θ 13) (by linarith only [b13l]) b13u
  have s17 := neg_ub_le_mul_cos (θ := θ 17) (by linarith only [b17l]) b17u
  have s19 := neg_ub_le_mul_cos (θ := θ 19) (by linarith only [b19l]) b19u
  have s23 := neg_ub_le_mul_cos (θ := θ 23) (by linarith only [b23l]) b23u
  have s29 := neg_ub_le_mul_cos (θ := θ 29) (by linarith only [b29l]) b29u
  have s31 := neg_ub_le_mul_cos (θ := θ 31) (by linarith only [b31l]) b31u
  have s37 := neg_ub_le_mul_cos (θ := θ 37) (by linarith only [b37l]) b37u
  have s41 := neg_ub_le_mul_cos (θ := θ 41) (by linarith only [b41l]) b41u
  have s43 := neg_ub_le_mul_cos (θ := θ 43) (by linarith only [b43l]) b43u
  have s47 := neg_ub_le_mul_cos (θ := θ 47) (by linarith only [b47l]) b47u
  have s53 := neg_ub_le_mul_cos (θ := θ 53) (by linarith only [b53l]) b53u
  have s59 := neg_ub_le_mul_cos (θ := θ 59) (by linarith only [b59l]) b59u
  have s61 := neg_ub_le_mul_cos (θ := θ 61) (by linarith only [b61l]) b61u
  have s67 := neg_ub_le_mul_cos (θ := θ 67) (by linarith only [b67l]) b67u
  have s71 := neg_ub_le_mul_cos (θ := θ 71) (by linarith only [b71l]) b71u
  have s73 := neg_ub_le_mul_cos (θ := θ 73) (by linarith only [b73l]) b73u
  have s79 := neg_ub_le_mul_cos (θ := θ 79) (by linarith only [b79l]) b79u
  have s83 := neg_ub_le_mul_cos (θ := θ 83) (by linarith only [b83l]) b83u
  have s89 := neg_ub_le_mul_cos (θ := θ 89) (by linarith only [b89l]) b89u
  linarith only [hf2, hf3, hf5, hf7, b2_1u, b2_2l, b2_3u, b2_4l, b2_5u, b2_6l,
    b3_1u, b3_2l, b3_3u, b3_4l, b5_1u, b5_2l, b7_1u, b7_2l,
    s11, s13, s17, s19, s23, s29, s31, s37, s41, s43, s47, s53, s59, s61, s67, s71, s73, s79,
    s83, s89]

theorem bohman_poly_ge (γ : ℝ) :
    -(0.935816 : ℝ) ≤ ∑ n ∈ Finset.range 91,
      vonMangoldt n / n * bohmanFn (9 / 2) (Real.log n) * Real.cos (γ * Real.log n) := by
  rw [bohman_prime_sum_eq_phaseForm]
  exact bohmanPhaseForm_ge _

/-! ## Edge LHS lower bound, archimedean upper bound on `(67, 169/2]`, and RH through `84.5` -/

private theorem bohman_budget_left_bounds :
    (2.236881 : ℝ) ≤ 4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
          ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ∧
      4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) +
        64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
          ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 ≤ 2.236883 := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10
  obtain ⟨he_lo, he_hi⟩ := exp_neg_nine_quarters_bounds
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
  constructor
  · exact (by norm_num : (2.236881 : ℝ) ≤
      4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * 3.1415926536 ^ 2) +
        64 * 3.1415926535 ^ 2 * (9 / 2) * (1 + 0.105399) /
          ((9 / 2) ^ 2 + 4 * 3.1415926536 ^ 2) ^ 2).trans (add_le_add ht1_lo ht2_lo)
  · exact (add_le_add ht1_hi ht2_hi).trans (by norm_num)

private theorem bohman_arch_lt {γ : ℝ} (h67 : 67 ≤ γ) (h845 : γ ≤ 169 / 2) :
    1 / 4 * Real.log (9 / 4 + γ ^ 2 / 4) - Real.log Real.pi / 2 + 1 / 1215 +
      18 / ((9 / 2) ^ 2 * γ ^ 2) + 1200 / ((9 / 2) ^ 3 * γ ^ 4) < 1.300950 := by
  have hlog_le : Real.log (9 / 4 + γ ^ 2 / 4) ≤ Real.log (28597 / 16) :=
    Real.log_le_log (by positivity) (by nlinarith only [h67, h845])
  obtain ⟨-, hl7b⟩ := log_prime_bounds (p := 7) (by norm_num) (k1 := 31) (m1 := 87)
    (k2 := 26) (m2 := 73) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.945284) (hi := 1.946145) (by norm_num) (by norm_num)
  have hl2b := Real.log_two_lt_d9.le
  have hlog_split : Real.log (28597 / 16 : ℝ) =
      Real.log 7 + 8 * Real.log 2 + Real.log (28597 / 28672) := by
    rw [show (28597 / 16 : ℝ) = (7 * 2 ^ 8) * (28597 / 28672) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hnear1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 28597 / 28672 by norm_num)
  have hπ := log_pi_lb_sharp
  have ht1 : 18 / ((9 / 2 : ℝ) ^ 2 * γ ^ 2) ≤ 18 / ((9 / 2) ^ 2 * 67 ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h67 2) (by norm_num))
  have ht2 : 1200 / ((9 / 2 : ℝ) ^ 3 * γ ^ 4) ≤ 1200 / ((9 / 2) ^ 3 * 67 ^ 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h67 4) (by norm_num))
  rw [hlog_split] at hlog_le
  norm_num at hnear1 ht1 ht2 ⊢
  linarith only [hlog_le, hl7b, hl2b, hnear1, hπ, ht1, ht2]

/-- **The Riemann hypothesis through height `169/2 = 84.5`.** Every zero of `ξ` in the critical
strip with `0 < Im ρ ≤ 169/2` lies on `Re ρ = 1/2`. -/
theorem rhVerifiedThrough_oneHundredSixtyNine_halves : RHVerifiedThrough (169 / 2) := by
  intro ρ hzero hre0 hre1 him0 him_top
  rcases le_or_gt ρ.im 67 with hle67 | hgt67
  · exact rhVerifiedThrough_sixtySeven hzero hre0 hre1 him0 hle67
  · by_contra hoff
    let rhoSupport : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : XiZeroCopy := by
      have hpos := xi_divisor_pos_on_support rhoSupport
      have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rhoSupport : ℂ)) := by omega
      exact ⟨rhoSupport, ⟨0, hn⟩⟩
    have hqre : (q.1 : ℂ).re ≠ 1 / 2 := hoff
    have hqim : (q.1 : ℂ).im = ρ.im := rfl
    have hLγ : 4 * Real.pi < (9 / 2) * ρ.im := by
      have := Real.pi_lt_four
      linarith only [this, hgt67]
    have hb := bohman_budget_at_edge (L := 9 / 2) (N := 91) (by norm_num)
      (fun _ hn => nine_halves_le_log hn) q hqre hqim (by linarith only [hgt67]) hLγ
    have hpoly := bohman_poly_ge ρ.im
    have hleft := bohman_budget_left_bounds.1
    have harch := bohman_arch_lt hgt67.le him_top
    linarith only [hb, hpoly, hleft, harch]

/-- **The Riemann hypothesis through integer height `84`.** -/
theorem rhVerifiedThrough_eightyFour : RHVerifiedThrough 84 := fun _ hzero hre0 hre1 him0 him84 =>
  rhVerifiedThrough_oneHundredSixtyNine_halves hzero hre0 hre1 him0 (by linarith only [him84])

/-! ## Exact phase-free saturation at integer height `85` -/

private theorem bohman_coeff_lb_p13 {p lp_lo lp_hi u_lo c_lo : ℝ}
    (hp : 0 < p) (hlp0 : 0 ≤ lp_lo)
    (hlp_lo : lp_lo ≤ Real.log p) (hlp_hi : Real.log p ≤ lp_hi)
    (hk_hi : 1 * lp_hi ≤ 9 / 2)
    (hu_lo0 : 0 ≤ u_lo)
    (hu_lo : u_lo ≤ 3.1415926535 * (1 - 1 * lp_hi / (9 / 2)))
    (h_clo : c_lo ≤ lp_lo / p * (bohmanP13 u_lo / 3.1415926536))
    (hp13_pos : 0 ≤ bohmanP13 u_lo) :
    c_lo ≤ Real.log p / p * bohmanFn (9 / 2) (1 * Real.log p) := by
  obtain ⟨hπ_lo, hπ_hi⟩ := pi_bounds_d10
  have hπ_pos := Real.pi_pos
  have hlp_nonneg : 0 ≤ Real.log p := hlp0.trans hlp_lo
  set u : ℝ := Real.pi * (1 - 1 * Real.log p / (9 / 2))
  have h1_lo : 0 ≤ 1 - 1 * lp_hi / (9 / 2) := by linarith
  have h1_le : 1 - 1 * lp_hi / (9 / 2) ≤ 1 - 1 * Real.log p / (9 / 2) := by linarith
  have hu_ge_lo : u_lo ≤ u :=
    hu_lo.trans (mul_le_mul hπ_lo.le h1_le h1_lo hπ_pos.le)
  have hu0 : 0 ≤ u := hu_lo0.trans hu_ge_lo
  have hu_pi : u ≤ Real.pi := by
    dsimp only [u]
    exact mul_le_of_le_one_right hπ_pos.le (by linarith)
  have hH_lo : bohmanP13 u_lo ≤ Real.sin u - u * Real.cos u :=
    (bohmanP13_le hu_lo0).trans
      (monotoneOn_sin_sub_mul_cos ⟨hu_lo0, hu_ge_lo.trans hu_pi⟩ ⟨hu0, hu_pi⟩ hu_ge_lo)
  have hW_eq := bohmanFn_eq_sin_sub_mul_cos (L := 9 / 2) (x := 1 * Real.log p)
    (by norm_num) (by linarith) (by linarith)
  have hW_lo : bohmanP13 u_lo / 3.1415926536 ≤ bohmanFn (9 / 2) (1 * Real.log p) := by
    rw [hW_eq]
    exact (div_le_div_of_nonneg_left hp13_pos hπ_pos hπ_hi.le).trans
      (div_le_div_of_nonneg_right hH_lo hπ_pos.le)
  exact h_clo.trans (mul_le_mul (div_le_div_of_nonneg_right hlp_lo hp.le) hW_lo
    (div_nonneg hp13_pos (by norm_num)) (div_nonneg hlp_nonneg hp.le))

/-- **Phase-free saturation at height `85` (`L = 9/2`).** Evaluating `bohmanPhaseForm` at phase `π`
on every prime (`cos(k π) = (-1)^k`) reverses the Bohman edge inequality strictly at `γ = 85`,
even without the positive `O(1/1215 + 1/γ²)` archimedean constants. -/
theorem bohman_phaseFree_saturates_at_eightyFive :
    ∃ θ : ℕ → ℝ,
      4 * (9 / 2) ^ 2 / ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) +
          64 * Real.pi ^ 2 * (9 / 2) * (1 + Real.exp (-(9 / 2 / 2))) /
            ((9 / 2) ^ 2 + 4 * Real.pi ^ 2) ^ 2 <
        1 / 4 * Real.log (9 / 4 + 85 ^ 2 / 4) - Real.log Real.pi / 2 -
          bohmanPhaseForm θ := by
  refine ⟨fun _ => Real.pi, ?_⟩
  have hleft_ub := bohman_budget_left_bounds.2
  have hl2a := Real.log_two_gt_d9.le
  have hl2b := Real.log_two_lt_d9.le
  obtain ⟨hl3a, hl3b⟩ := log_prime_bounds (p := 3) (by norm_num) (k1 := 53) (m1 := 84)
    (k2 := 41) (m2 := 65) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.098572) (hi := 1.098892) (by norm_num) (by norm_num)
  obtain ⟨hl5a, hl5b⟩ := log_prime_bounds (p := 5) (by norm_num) (k1 := 28) (m1 := 65)
    (k2 := 31) (m2 := 72) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.609091) (hi := 1.609891) (by norm_num) (by norm_num)
  obtain ⟨hl7a, hl7b⟩ := log_prime_bounds (p := 7) (by norm_num) (k1 := 31) (m1 := 87)
    (k2 := 26) (m2 := 73) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lo := 1.945284) (hi := 1.946145) (by norm_num) (by norm_num)
  have b2_1l : (0.3108480 : ℝ) ≤ Real.log 2 / 2 * bohmanFn (9 / 2) (1 * Real.log 2) :=
    bohman_coeff_lb_p13 (u_lo := 2.65768) (by norm_num) (by norm_num) hl2a hl2b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  have b3_1l : (0.2801437 : ℝ) ≤ Real.log 3 / 3 * bohmanFn (9 / 2) (1 * Real.log 3) :=
    bohman_coeff_lb_p13 (u_lo := 2.37442) (by norm_num) (by norm_num) hl3a hl3b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  have b5_1l : (0.1816976 : ℝ) ≤ Real.log 5 / 5 * bohmanFn (9 / 2) (1 * Real.log 5) :=
    bohman_coeff_lb_p13 (u_lo := 2.01767) (by norm_num) (by norm_num) hl5a hl5b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  have b7_1l : (0.1196791 : ℝ) ≤ Real.log 7 / 7 * bohmanFn (9 / 2) (1 * Real.log 7) :=
    bohman_coeff_lb_p13 (u_lo := 1.78292) (by norm_num) (by norm_num) hl7a hl7b (by norm_num)
      (by norm_num) (by norm_num) (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
      (by unfold bohmanP13 bohmanP11 bohmanP9; norm_num)
  obtain ⟨-, ⟨-, b2_2u⟩, ⟨b2_3l, -⟩, ⟨-, b2_4u⟩, ⟨b2_5l, -⟩,
    ⟨-, b2_6u⟩, -, ⟨-, b3_2u⟩, ⟨b3_3l, -⟩, ⟨-, b3_4u⟩,
    -, ⟨-, b5_2u⟩, -, ⟨-, b7_2u⟩,
    ⟨b11l, -⟩, ⟨b13l, -⟩, ⟨b17l, -⟩, ⟨b19l, -⟩, ⟨b23l, -⟩, ⟨b29l, -⟩,
    ⟨b31l, -⟩, ⟨b37l, -⟩, ⟨b41l, -⟩, ⟨b43l, -⟩, ⟨b47l, -⟩, ⟨b53l, -⟩,
    ⟨b59l, -⟩, ⟨b61l, -⟩, ⟨b67l, -⟩, ⟨b71l, -⟩, ⟨b73l, -⟩, ⟨b79l, -⟩,
    ⟨b83l, -⟩, ⟨b89l, -⟩⟩ := all_prime_bohman_coeff_bounds
  obtain ⟨c2_2, c2_3, c2_4, c2_5, c2_6⟩ := cos_chebyshev_six Real.pi
  have hc2 : Real.cos (2 * Real.pi) = 1 := by rw [c2_2, Real.cos_pi]; norm_num
  have hc3 : Real.cos (3 * Real.pi) = -1 := by rw [c2_3, Real.cos_pi]; norm_num
  have hc4 : Real.cos (4 * Real.pi) = 1 := by rw [c2_4, Real.cos_pi]; norm_num
  have hc5 : Real.cos (5 * Real.pi) = -1 := by rw [c2_5, Real.cos_pi]; norm_num
  have hc6 : Real.cos (6 * Real.pi) = 1 := by rw [c2_6, Real.cos_pi]; norm_num
  have hform_ub : bohmanPhaseForm (fun _ => Real.pi) ≤ -0.934633 := by
    unfold bohmanPhaseForm
    rw [hc2, hc3, hc4, hc5, hc6, Real.cos_pi]
    linarith only [b2_1l, b2_2u, b2_3l, b2_4u, b2_5l, b2_6u,
      b3_1l, b3_2u, b3_3l, b3_4u, b5_1l, b5_2u, b7_1l, b7_2u,
      b11l, b13l, b17l, b19l, b23l, b29l, b31l, b37l, b41l, b43l, b47l, b53l, b59l,
      b61l, b67l, b71l, b73l, b79l, b83l, b89l]
  have hlog85 : 6 * Real.log 3 + Real.log 5 - Real.log 2 - 28 / 3617 ≤
      Real.log (9 / 4 + (85 : ℝ) ^ 2 / 4) := by
    have heq : (9 / 4 + (85 : ℝ) ^ 2 / 4) = (3 ^ 6 * 5 / 2) * (3617 / 3645) := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3645 / 3617 by norm_num)
    have hinv_eq : Real.log (3617 / 3645 : ℝ) = -Real.log (3645 / 3617) := by
      rw [← Real.log_inv]; norm_num
    rw [hinv_eq]
    norm_num at hinv ⊢
    linarith only [hinv]
  have hlog_pi_ub : Real.log Real.pi ≤ 38 / 23 * 0.6931471808 := by
    have hpow : Real.pi ^ 23 ≤ (2 : ℝ) ^ 38 :=
      (pow_le_pow_left₀ Real.pi_pos.le pi_bounds_d10.2.le 23).trans (by norm_num)
    have h := log_le_of_pow_le_two_pow Real.pi_pos (k := 23) (m := 38) (by norm_num) hpow
    norm_num at h ⊢
    linarith only [h, hl2b]
  linarith only [hleft_ub, hform_ub, hlog85, hlog_pi_ub, hl2b, hl3a, hl5a]

/-! ## Upgraded Pólya frequency, slice, and Li rungs -/

/-- At verified height `169/2 = 84.5`, the Taylor coefficients of `ξ` at the centre form a
`PF_252` sequence (upgraded from `PF_200` at height `67`). -/
theorem xi_centre_pfSeq_twoHundredFiftyTwo :
    PFSeq 252 (evenTaylorRe (fun x => xi (1 / 2 + x))) :=
  xi_centre_pfSeq_of_rhVerifiedThrough (T := 169 / 2) (by norm_num)
    rhVerifiedThrough_oneHundredSixtyNine_halves (by norm_num) (by norm_num)

/-- Every Taylor coefficient of `ξ(1/2 + x + i t) ξ(1/2 - x + i t)` is nonnegative on `|t| ≤ 84`
(upgraded from `|t| ≤ 133/2` at height `67`). -/
theorem xiSliceCoeff_nonneg_of_abs_le_eightyFour {t : ℝ} (ht : |t| ≤ 84) (n : ℕ) :
    0 ≤ xiSliceCoeff t n :=
  xiSliceCoeff_nonneg_of_rhVerifiedThrough (T := 169 / 2) (t := t) (by linarith only [ht])
    rhVerifiedThrough_oneHundredSixtyNine_halves n

/-- The Li coefficients satisfy `Re(2 λ_n) ≥ 0` for all `n ≤ 397` (upgraded from `n ≤ 314` at
height `67`). -/
theorem re_xiLiPaired_nonneg_of_le_threeHundredNinetySeven {n : ℕ} (hn : n ≤ 397) :
    0 ≤ (xiLiPaired n).re := by
  have hn' : (n : ℝ) ≤ 397 := by exact_mod_cast hn
  exact re_xiLiPaired_nonneg_of_rhVerifiedThrough (T := 169 / 2) (by norm_num)
    rhVerifiedThrough_oneHundredSixtyNine_halves (by linarith only [hn'])

#print axioms rhVerifiedThrough_oneHundredSixtyNine_halves
#print axioms rhVerifiedThrough_eightyFour
#print axioms bohman_phaseFree_saturates_at_eightyFive

end

end GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget
