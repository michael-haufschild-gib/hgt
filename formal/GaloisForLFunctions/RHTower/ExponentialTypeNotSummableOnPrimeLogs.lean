import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths
import GaloisForLFunctions.RHTower.WeightedEulerPaleyWienerVanishing
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# An entire function of small exponential type is not summable over the prime logarithms

Let `Φ ≢ 0` be entire with `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}`, and let `1/2 ≤ σ` with `3ρ < 1 − σ`.  Then the
partial sums `Σ_{p<N} p^{−σ} ‖Φ(log p)‖` over the primes are unbounded
(`exists_primeLogWeightedSum_gt`).  This is the prime-sum lower bound of the Pechersky density
lemma: for the Hilbert-space vectors `p^{−z}` on a disc of radius `ρ` about a point of real part
`σ`, the pairing with a nonzero vector is `p^{−σ}` times an entire function of exponential type
`ρ` at `log p`.

The proof has three steps.
* **Largeness along a sequence** (`exists_ge_exp_le_norm_of_exponentialType`): `Φ` cannot satisfy
  `‖Φ x‖ < e^{−(ρ+δ)x}` for all large real `x`, since `Φ(w) e^{(ρ+δ/2)w}` would then decay
  exponentially on both real rays and vanish by the Paley–Wiener two-ray theorem
  (`eq_zero_of_two_ray_exponential_decay`).
* **Propagation by the Cauchy estimate** (`norm_ge_on_window_of_exponentialType`): on a window of
  length `η ≍ e^{−(2ρ+δ)x}` to the right of such a point `x`, the derivative bound
  `‖Φ'‖ ≤ C e^{ρ(x+2)}` keeps `‖Φ‖ ≥ ½ e^{−(ρ+δ)x}`.
* **Prime mass in the window** (`window_sum_ge_theta_window`): the primes with `log p` in the
  window `(x, x + η]` lie in `(y, y + ηy]` with `y = e^x`, where they carry Chebyshev mass at least
  `ηy/4` (`exists_theta_window_lower_seven_twelfths`, since `ηy = c·y^{1−2ρ−δ}` and
  `1 − 2ρ − δ > 7/12`); the window therefore contributes at least `c y^{1−σ−3ρ−2δ}/log(2y)` to the
  prime sum, which is unbounded.
-/

open Complex Filter Topology Set Finset
open scoped Real

noncomputable section

namespace RHTower

/-! ## Largeness along a sequence -/

/-- **An entire function of exponential type `ρ` is at least `e^{−(ρ+δ)x}` at arbitrarily large
real `x`.**  Otherwise `Φ(w) e^{(ρ+δ/2) w}` decays exponentially on both real rays and vanishes by
the Paley–Wiener two-ray theorem. -/
theorem exists_ge_exp_le_norm_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    (hne : Φ ≠ 0) {δ : ℝ} (hδ : 0 < δ) (X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧ Real.exp (-((ρ + δ) * x)) ≤ ‖Φ x‖ := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hC : 0 ≤ C := by
    have h := hgrow 0
    simp only [norm_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  set X' : ℝ := max X 0 with hX'
  have hX'0 : 0 ≤ X' := le_max_right _ _
  set g : ℂ → ℂ := fun w => Φ w * Complex.exp (((ρ + δ / 2 : ℝ) : ℂ) * w) with hg
  have hgdiff : Differentiable ℂ g :=
    hΦ.mul (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hgnorm : ∀ w, ‖g w‖ = ‖Φ w‖ * Real.exp ((ρ + δ / 2) * w.re) := fun w => by
    rw [hg]
    simp only
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  set C₂ : ℝ := max 1 (C * Real.exp ((2 * ρ + δ) * X')) with hC₂
  have hC₂C : C ≤ C₂ := by
    refine le_trans ?_ (le_max_right _ _)
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp ((2 * ρ + δ) * X') := by
          gcongr
          exact Real.one_le_exp (by positivity)
  have hgrow' : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp ((2 * ρ + δ / 2) * ‖z‖) := fun z => by
    rw [hgnorm]
    calc ‖Φ z‖ * Real.exp ((ρ + δ / 2) * z.re)
        ≤ (C * Real.exp (ρ * ‖z‖)) * Real.exp ((ρ + δ / 2) * ‖z‖) := by
          gcongr
          · exact hgrow z
          · exact Complex.re_le_norm z
      _ = C * Real.exp ((2 * ρ + δ / 2) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖g x‖ ≤ C₂ * Real.exp (-(δ / 2 * x)) := fun x hx => by
    rw [hgnorm, Complex.ofReal_re]
    rcases le_or_gt X' x with hXx | hXx
    · have h1 := (hcon x (le_trans (le_max_left _ _) hXx)).le
      calc ‖Φ x‖ * Real.exp ((ρ + δ / 2) * x)
          ≤ Real.exp (-((ρ + δ) * x)) * Real.exp ((ρ + δ / 2) * x) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 * Real.exp (-(δ / 2 * x)) := by
            rw [← Real.exp_add, one_mul]
            congr 1
            ring
        _ ≤ C₂ * Real.exp (-(δ / 2 * x)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · have hx' : ‖(x : ℂ)‖ ≤ X' := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx]
        exact hXx.le
      have hΦb : ‖Φ x‖ ≤ C * Real.exp (ρ * X') :=
        (hgrow x).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx' hρ)) hC)
      have hexp : Real.exp ((ρ + δ / 2) * x) ≤ Real.exp ((ρ + δ / 2) * X') :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hXx.le (by positivity))
      have hexp' : Real.exp (-(δ / 2 * X')) ≤ Real.exp (-(δ / 2 * x)) :=
        Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hXx.le (by positivity)))
      calc ‖Φ x‖ * Real.exp ((ρ + δ / 2) * x)
          ≤ (C * Real.exp (ρ * X')) * Real.exp ((ρ + δ / 2) * X') :=
            mul_le_mul hΦb hexp (Real.exp_pos _).le (by positivity)
        _ = C * Real.exp ((2 * ρ + δ) * X') * Real.exp (-(δ / 2 * X')) := by
            rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
            congr 2
            ring
        _ ≤ C₂ * Real.exp (-(δ / 2 * x)) :=
            mul_le_mul (le_max_right _ _) hexp' (Real.exp_pos _).le (by positivity)
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ C₂ * Real.exp (δ / 2 * x) := fun x hx => by
    rw [hgnorm, Complex.ofReal_re]
    calc ‖Φ x‖ * Real.exp ((ρ + δ / 2) * x)
        ≤ (C * Real.exp (ρ * ‖(x : ℂ)‖)) * Real.exp ((ρ + δ / 2) * x) := by
          gcongr
          exact hgrow x
      _ = C * Real.exp (δ / 2 * x) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx, mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ C₂ * Real.exp (δ / 2 * x) := by gcongr
  have hg0 : g = 0 := eq_zero_of_two_ray_exponential_decay hgdiff hC (by positivity)
    (half_pos hδ) hgrow' hplus hminus
  apply hne
  funext w
  have h := congrFun hg0 w
  rw [hg] at h
  simp only [Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at h
  exact h

/-! ## Propagation by the Cauchy estimate -/

/-- Cauchy's estimate on the unit disc about a nonnegative real point. -/
theorem norm_deriv_le_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    {c : ℝ} (hc : 0 ≤ c) :
    ‖deriv Φ c‖ ≤ C * Real.exp (ρ * (c + 1)) := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (c : ℂ))
    (C := C * Real.exp (ρ * (c + 1))) one_pos hΦ.diffContOnCl fun z hz => ?_
  · simpa using h
  · rw [mem_sphere_iff_norm] at hz
    have hz' : ‖z‖ ≤ c + 1 := by
      calc ‖z‖ ≤ ‖(c : ℂ)‖ + ‖z - c‖ := norm_le_insert' _ _
        _ = c + 1 := by rw [hz, Complex.norm_real, Real.norm_of_nonneg hc]
    calc ‖Φ z‖ ≤ C * Real.exp (ρ * ‖z‖) := hgrow z
      _ ≤ C * Real.exp (ρ * (c + 1)) := by gcongr

/-- **Propagation of a lower bound to a window.**  If `‖Φ x‖ ≥ m₀` at a nonnegative real `x` and
the window length `η ≤ 1` satisfies `C e^{ρ(x+2)} η ≤ m₀/2`, then `‖Φ‖ ≥ m₀/2` on `[x, x + η]`. -/
theorem norm_ge_on_window_of_exponentialType {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖))
    {x η m₀ : ℝ} (hx : 0 ≤ x) (hη1 : η ≤ 1) (hm₀ : m₀ ≤ ‖Φ x‖)
    (hηD : C * Real.exp (ρ * (x + 2)) * η ≤ m₀ / 2) :
    ∀ t ∈ Icc x (x + η), m₀ / 2 ≤ ‖Φ t‖ := by
  intro t ht
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => Φ s)
    (f' := fun s : ℝ => deriv Φ s) (a := x) (b := x + η) (C := C * Real.exp (ρ * (x + 2)))
    (fun s _ => ((hΦ (s : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
    (fun s hs => ?_) t ht
  · have h1 : ‖Φ t - Φ x‖ ≤ m₀ / 2 := by
      calc ‖Φ t - Φ x‖ ≤ C * Real.exp (ρ * (x + 2)) * (t - x) := hmvt
        _ ≤ C * Real.exp (ρ * (x + 2)) * η := by
            gcongr
            linarith [ht.2]
        _ ≤ m₀ / 2 := hηD
    have h2 := norm_sub_norm_le (Φ x) (Φ t)
    rw [norm_sub_rev] at h2
    linarith
  · have hs0 : 0 ≤ s := le_trans hx hs.1
    calc ‖deriv Φ s‖ ≤ C * Real.exp (ρ * (s + 1)) :=
          norm_deriv_le_of_exponentialType hΦ hC hρ hgrow hs0
      _ ≤ C * Real.exp (ρ * (x + 2)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hρ)) hC

/-! ## Prime mass in a window -/

/-- The weighted prime sum `Σ_{p < N} p^{−σ} ‖Φ(log p)‖`. -/
def primeLogWeightedSum (Φ : ℂ → ℂ) (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, if n.Prime then (n : ℝ) ^ (-σ) * ‖Φ (Real.log n)‖ else 0

theorem primeLogWeightedSum_nonneg (Φ : ℂ → ℂ) {σ : ℝ} (N : ℕ) :
    0 ≤ primeLogWeightedSum Φ σ N :=
  sum_nonneg fun n _ => by
    split_ifs
    · positivity
    · exact le_rfl

/-- The Chebyshev mass of a window `(y, y + L]` is the sum of `log p` over its primes. -/
theorem theta_sub_theta_eq_sum_Ioc {y L : ℝ} (hL : 0 ≤ L) :
    Chebyshev.theta (y + L) - Chebyshev.theta y
      = ∑ p ∈ Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊, if p.Prime then Real.log p else 0 := by
  have hfl : ⌊y⌋₊ ≤ ⌊y + L⌋₊ := Nat.floor_le_floor (by linarith)
  unfold Chebyshev.theta
  rw [sum_filter, sum_filter, ← sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  ring

/-- Every prime of the window `(⌊y⌋₊, ⌊y + L⌋₊]` lies in `(y, y + L]`. -/
theorem window_mem_bounds {y L : ℝ} (hyL : 0 ≤ y + L) {p : ℕ}
    (hp : p ∈ Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊) :
    y < p ∧ (p : ℝ) ≤ y + L := by
  rw [Finset.mem_Ioc] at hp
  constructor
  · calc y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
      _ ≤ p := by exact_mod_cast hp.1
  · calc (p : ℝ) ≤ ⌊y + L⌋₊ := by exact_mod_cast hp.2
      _ ≤ y + L := Nat.floor_le hyL

/-- **Window lower bound.**  If `‖Φ(log p)‖ ≥ m` for every prime `p ∈ (y, y + L]`, the window
contributes at least `(y+L)^{−σ} m (θ(y+L) − θ(y)) / log(y+L)` to the prime sum. -/
theorem window_sum_ge_theta_window (Φ : ℂ → ℂ) {σ y L m : ℝ} (hσ : 0 ≤ σ) (hyL : 1 < y + L)
    (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hlow : ∀ p : ℕ, p.Prime → y < p → (p : ℝ) ≤ y + L → m ≤ ‖Φ (Real.log p)‖) :
    (y + L) ^ (-σ) * m / Real.log (y + L) * (Chebyshev.theta (y + L) - Chebyshev.theta y)
      ≤ ∑ p ∈ Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊,
          if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0 := by
  have hlog : 0 < Real.log (y + L) := Real.log_pos hyL
  rw [theta_sub_theta_eq_sum_Ioc hL, mul_sum]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := window_mem_bounds (by linarith) hp
  split_ifs with hprime
  · have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogle : Real.log p ≤ Real.log (y + L) := Real.log_le_log hp0 hp2
    have hrpow : (y + L) ^ (-σ) ≤ (p : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hp0 hp2 (by linarith)
    have hΦp := hlow p hprime hp1 hp2
    calc (y + L) ^ (-σ) * m / Real.log (y + L) * Real.log p
        = ((y + L) ^ (-σ) * m) * (Real.log p / Real.log (y + L)) := by ring
      _ ≤ ((p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖) * 1 := by
          gcongr
          exact (div_le_one hlog).mpr hlogle
      _ = (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ := mul_one _
  · simp

/-- The window sum is dominated by the full prime sum up to `⌊y + L⌋₊`. -/
theorem window_sum_le_primeLogWeightedSum (Φ : ℂ → ℂ) (σ : ℝ) (a b : ℕ) :
    (∑ p ∈ Finset.Ioc a b, if p.Prime then (p : ℝ) ^ (-σ) * ‖Φ (Real.log p)‖ else 0)
      ≤ primeLogWeightedSum Φ σ (b + 1) := by
  unfold primeLogWeightedSum
  refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
  · intro p hp
    rw [Finset.mem_Ioc] at hp
    rw [Finset.mem_range]
    omega
  · split_ifs
    · positivity
    · exact le_rfl

/-! ## The prime sums are unbounded -/

/-- **The prime-sum lower bound.**  For `Φ ≢ 0` entire with `‖Φ ξ‖ ≤ C e^{ρ‖ξ‖}` and
`1/2 ≤ σ`, `3ρ < 1 − σ`, the sums `Σ_{p<N} p^{−σ} ‖Φ(log p)‖` are unbounded. -/
theorem exists_primeLogWeightedSum_gt {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    {C ρ σ : ℝ} (hρ : 0 ≤ ρ) (hgrow : ∀ ξ : ℂ, ‖Φ ξ‖ ≤ C * Real.exp (ρ * ‖ξ‖)) (hne : Φ ≠ 0)
    (hσ : 1 / 2 ≤ σ) (hρσ : 3 * ρ < 1 - σ) (M : ℝ) :
    ∃ N : ℕ, M < primeLogWeightedSum Φ σ N := by
  -- the growth constant is positive, since `Φ ≢ 0`
  have hC : 0 < C := by
    by_contra hC
    simp only [not_lt] at hC
    apply hne
    funext ξ
    have h := hgrow ξ
    have h2 : C * Real.exp (ρ * ‖ξ‖) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    exact norm_le_zero_iff.mp (le_trans h h2)
  have hσ0 : 0 ≤ σ := by linarith
  -- the exponents
  set δ : ℝ := min ((1 - σ - 3 * ρ) / 4) (1 / 24) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ (1 - σ - 3 * ρ) / 4 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 24 := min_le_right _ _
  clear_value δ
  set β : ℝ := 1 - 2 * ρ - δ with hβ
  clear_value β
  set α : ℝ := (7 / 12 + β) / 2 with hα
  clear_value α
  have hρ6 : ρ < 1 / 6 := by linarith
  have hβ7 : 7 / 12 < β := by rw [hβ]; linarith
  have hα7 : 7 / 12 < α := by rw [hα]; linarith
  have hαβ : α < β := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα, hβ]; linarith
  set e : ℝ := 1 - σ - 3 * ρ - 2 * δ with he
  clear_value e
  have he0 : 0 < e := by rw [he]; linarith
  -- the prime-mass window theorem
  obtain ⟨X₁, hX₁1, hθ⟩ := exists_theta_window_lower_seven_twelfths hα7 hα1
  -- constants
  set c₁ : ℝ := Real.exp (-(2 * ρ)) / (2 * C) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  clear_value c₁
  set c₂ : ℝ := c₁ * (2 : ℝ) ^ (-σ) / 8 with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  clear_value c₂
  set c₃ : ℝ := c₂ * (e / 2) * (2 : ℝ) ^ (-(e / 2)) with hc₃
  have hc₃0 : 0 < c₃ := by positivity
  clear_value c₃
  -- the five thresholds in `y`
  have hev : ∀ᶠ y : ℝ in atTop, X₁ ≤ y ∧ 1 ≤ y ∧ c₁ ≤ y ^ (2 * ρ + δ) ∧
      (2 : ℝ) ^ (α + 1) / c₁ ≤ y ^ (β - α) ∧ (M + 1) / c₃ ≤ y ^ (e / 2) := by
    refine (eventually_ge_atTop X₁).and ((eventually_ge_atTop 1).and
      (((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop c₁).and
      (((tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _).and
      ((tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _))))
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hev
  -- a large point where `Φ` is not small
  obtain ⟨x, hxY, hΦx⟩ := exists_ge_exp_le_norm_of_exponentialType hΦ hρ hgrow hne hδ0 (max Y₀ 0)
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hxY
  set y : ℝ := Real.exp x with hy
  have hy0 : 0 < y := Real.exp_pos x
  have hxy : x + 1 ≤ y := by
    rw [hy]
    exact Real.add_one_le_exp x
  clear_value y
  have hyY : Y₀ ≤ y := by
    calc Y₀ ≤ max Y₀ 0 := le_max_left _ _
      _ ≤ x := hxY
      _ ≤ y := by linarith [hxy]
  obtain ⟨hyX₁, hy1, hyc₁, hyαβ, hyM⟩ := hY₀ y hyY
  have hlogy : Real.log y = x := by rw [hy]; exact Real.log_exp x
  -- the window length in the logarithmic variable
  set η : ℝ := c₁ * y ^ (-(2 * ρ + δ)) with hη
  have hη0 : 0 < η := by positivity
  clear_value η
  have hη1 : η ≤ 1 := by
    rw [hη, Real.rpow_neg hy0.le]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact hyc₁
  -- the propagated lower bound on the window
  have hηD : C * Real.exp (ρ * (x + 2)) * η ≤ Real.exp (-((ρ + δ) * x)) / 2 := by
    have hpow : y ^ (-(2 * ρ + δ)) = Real.exp (-((2 * ρ + δ) * x)) := by
      rw [Real.rpow_def_of_pos hy0, hlogy]
      congr 1
      ring
    rw [hη, hpow, hc₁]
    rw [show C * Real.exp (ρ * (x + 2)) * (Real.exp (-(2 * ρ)) / (2 * C) *
        Real.exp (-((2 * ρ + δ) * x)))
        = (Real.exp (ρ * (x + 2)) * Real.exp (-(2 * ρ)) * Real.exp (-((2 * ρ + δ) * x))) / 2 by
          field_simp]
    rw [← Real.exp_add, ← Real.exp_add]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply le_of_eq
    congr 1
    ring
  have hwin := norm_ge_on_window_of_exponentialType hΦ hC.le hρ hgrow hx0 hη1 hΦx hηD
  -- the window of primes
  set L : ℝ := η * y with hL
  have hL0 : 0 < L := by positivity
  clear_value L
  have hLy : L ≤ y := by
    rw [hL]
    calc η * y ≤ 1 * y := by gcongr
      _ = y := one_mul y
  have hLpow : L = c₁ * y ^ β := by
    rw [hL, hη, hβ, mul_assoc]
    congr 1
    rw [show (1 : ℝ) - 2 * ρ - δ = -(2 * ρ + δ) + 1 by ring, Real.rpow_add hy0, Real.rpow_one]
  -- primes of the window have `log p` in `[x, x + η]`
  have hlow : ∀ p : ℕ, p.Prime → y < p → (p : ℝ) ≤ y + L →
      Real.exp (-((ρ + δ) * x)) / 2 ≤ ‖Φ (Real.log p)‖ := by
    intro p hp hp1 hp2
    refine hwin (Real.log p) ⟨?_, ?_⟩
    · rw [← hlogy]
      exact (Real.log_lt_log hy0 hp1).le
    · calc Real.log p ≤ Real.log (y + L) := Real.log_le_log (by linarith) hp2
        _ = Real.log y + Real.log (1 + η) := by
            rw [hL, show y + η * y = y * (1 + η) by ring, Real.log_mul hy0.ne' (by positivity)]
        _ ≤ x + η := by
            rw [hlogy]
            linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + η)]
  -- the Chebyshev mass of the window
  have hθwin : L / 4 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
    have h1 := hθ y L hyX₁ hL0.le
    have h2 : (y + L) ^ α ≤ L / 2 := by
      calc (y + L) ^ α ≤ (2 * y) ^ α := by
            gcongr
            linarith
        _ = (2 : ℝ) ^ α * y ^ α := Real.mul_rpow (by norm_num) hy0.le
        _ ≤ L / 2 := by
            rw [hLpow]
            have h3 : (2 : ℝ) ^ (α + 1) / c₁ * y ^ α ≤ y ^ (β - α) * y ^ α := by
              gcongr
            rw [← Real.rpow_add hy0, sub_add_cancel] at h3
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at h3
            have h4 : (2 : ℝ) ^ α * y ^ α = ((2 : ℝ) ^ α * 2 / c₁ * y ^ α) * c₁ / 2 := by
              field_simp
            rw [h4]
            calc (2 : ℝ) ^ α * 2 / c₁ * y ^ α * c₁ / 2 ≤ y ^ β * c₁ / 2 := by gcongr
              _ = c₁ * y ^ β / 2 := by ring
    linarith
  -- assemble the lower bound
  have hsum := window_sum_ge_theta_window Φ hσ0 (by linarith) hL0.le (by positivity) hlow
  have hfull := window_sum_le_primeLogWeightedSum Φ σ ⌊y⌋₊ ⌊y + L⌋₊
  refine ⟨⌊y + L⌋₊ + 1, lt_of_lt_of_le ?_ (le_trans hsum hfull)⟩
  -- the explicit power lower bound
  have hyL2 : y + L ≤ 2 * y := by linarith
  have hlog2 : 0 < Real.log (y + L) := Real.log_pos (by linarith)
  have hlog2' : Real.log (y + L) ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hyL2
  have hlog3 : Real.log (2 * y) ≤ (2 * y) ^ (e / 2) / (e / 2) :=
    Real.log_le_rpow_div (by positivity) (by positivity)
  have hrp : (2 * y) ^ (-σ) ≤ (y + L) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hyL2 (by linarith)
  have hm : Real.exp (-((ρ + δ) * x)) / 2 = y ^ (-(ρ + δ)) / 2 := by
    rw [Real.rpow_def_of_pos hy0, hlogy]
    congr 2
    ring
  -- `(y+L)^{-σ} m / log(y+L) · θ-window ≥ c₂ y^e / log(2y) ≥ c₃ y^{e/2} ≥ M + 1`
  have hpos1 : 0 < (y + L) ^ (-σ) * (Real.exp (-((ρ + δ) * x)) / 2) := by positivity
  calc M < M + 1 := by linarith
    _ ≤ c₃ * y ^ (e / 2) := by
        rw [mul_comm]
        exact (div_le_iff₀ hc₃0).mp hyM
    _ = c₂ * y ^ e / ((2 * y) ^ (e / 2) / (e / 2)) := by
        rw [hc₃, Real.mul_rpow (by norm_num) hy0.le]
        have hye : y ^ e = y ^ (e / 2) * y ^ (e / 2) := by
          rw [← Real.rpow_add hy0]
          congr 1
          ring
        rw [hye]
        field_simp
        rw [Real.rpow_neg (by norm_num)]
        field_simp
    _ ≤ c₂ * y ^ e / Real.log (2 * y) := by
        gcongr
        exact Real.log_pos (by linarith)
    _ ≤ c₂ * y ^ e / Real.log (y + L) := by
        gcongr
    _ = ((2 * y) ^ (-σ) * (y ^ (-(ρ + δ)) / 2)) / Real.log (y + L) * (c₁ * y ^ β / 4) := by
        rw [hc₂, Real.mul_rpow (by norm_num) hy0.le, he]
        have hye : y ^ (1 - σ - 3 * ρ - 2 * δ) = y ^ (-σ) * y ^ (-(ρ + δ)) * y ^ β := by
          rw [← Real.rpow_add hy0, ← Real.rpow_add hy0, hβ]
          congr 1
          ring
        rw [hye]
        ring
    _ ≤ ((y + L) ^ (-σ) * (Real.exp (-((ρ + δ) * x)) / 2)) / Real.log (y + L)
          * (Chebyshev.theta (y + L) - Chebyshev.theta y) := by
        rw [hm, ← hLpow]
        gcongr
    _ = (y + L) ^ (-σ) * (Real.exp (-((ρ + δ) * x)) / 2) / Real.log (y + L)
          * (Chebyshev.theta (y + L) - Chebyshev.theta y) := rfl

end RHTower
