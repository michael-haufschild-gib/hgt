import GaloisForLFunctions.RHTower.JointAncestryShellAmplitudeAbscissaDuality
import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge
import GaloisForLFunctions.RHTower.JointAncestryShellPowerSumCriterion
import GaloisForLFunctions.RHTower.JointAncestryConstantVectorDyadicShellDetection

/-!
# The unconditional constant-vector producer on dyadic shells

**Theorem** (`exists_eventually_jasConstShellSmallPositive`).  There is `κ > 0` such that for every
large `N` the level-one constant-vector tests on the shell `(N, 2N]` are positive at all amplitudes

`|z| ≤ κ log N/√N = κ / E_{1/2}(N)`.

No zero-free region and no half-plane bound is assumed.  This is the unconditional form of
`eventually_jasConstShellSmallPositive`, which needs `|Re ρ − ½| ≤ β' < ½`.

**Proof.**
* *Uniform angle without a half-plane.*  For `s = ½ + δ + iγ` with `|δ| ≤ ½` and `|γ| ≥ η > 0`,
  `Re(s(1−s)) = ¼ − δ² + γ² ≥ γ²` and `|s(1−s)| ≤ γ² + |γ| + 1`.  So
  `Re(1/(s(1−s))) ≥ η²/(η² + η + 1)·|1/(s(1−s))|`
  (`unconditional_angle_re_one_div`).  The ordinate gap `η` is the unconditional separation of
  the Xi divisor from the real axis (`exists_xiDivisorSupport_abs_im_lower_bound`).
* *Shell sums.*  Every zero has `Re ρ < 1`, so each factor deviates from `1` by at most
  `2|u| p^{−1/2}`, and `Σ_{N<p≤2N} p^{−1/2} ≤ C E_{1/2}(N)`.  At amplitude `κ/E_{1/2}(N)` the kernel
  error is at most `2Cκ`, which is below the angle for small `κ`.

**Reading.**  The shell detector of a zero at distance `δ` from the line fires at amplitude
`≍ log N·N^{−δ}`.  The duality `forall_abs_re_sub_half_le_iff_frequently_small_positive` makes
positivity at `N^{−β}` on infinitely many shells equivalent (without a chain) to the strip
`|Re ρ − ½| ≤ β`.  The unconditional producer therefore sits exactly at the trivial strip
`β = ½`, with a gain of one logarithm.  Every power gain is a zero-free strip.

**Radius law** (`eventually_shell_radius_law`).  If an off-line zero has the largest distance `δ*`,
the positivity radius of the shell tests is `N^{−δ*+o(1)}`: for every `ε > 0` and large `N` they are
positive below `N^{−(δ*+ε)}` and negative somewhere below `N^{−(δ*−ε)}`.  Under RH the radius is
infinite.  So the radius exponent reads the abscissa exactly, and
`exists_eventually_shell_radius_sandwich` places the radius between the unconditional
`κ log N/√N` and `N^{−β}` for every `β < δ*`.
-/

open Complex Filter
open scoped ComplexConjugate Topology

namespace RHTower

noncomputable section

/-- **Uniform angle without a half-plane bound.**  In the closed strip, at ordinate at least
`η > 0`, `Re(1/(s(1−s))) ≥ η²/(η² + η + 1) |1/(s(1−s))|`. -/
theorem unconditional_angle_re_one_div {η : ℝ} (hη : 0 < η) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2)
    (him : η ≤ |s.im|) :
    η ^ 2 / (η ^ 2 + η + 1) * ‖1 / (s * (1 - s))‖ ≤ (1 / (s * (1 - s))).re := by
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v = s * (1 - s) := ⟨_, rfl⟩
  rw [← hv]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = s.re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = s.im := ⟨_, rfl⟩
  have hvre : v.re = 1 / 4 - δ ^ 2 + γ ^ 2 := by
    rw [hv, hδ, hγ]; simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]; ring
  have hvim : v.im = -(2 * δ * γ) := by
    rw [hv, hδ, hγ]; simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]; ring
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by
    rw [hδ]; have := abs_le.mp hs; nlinarith [this.1, this.2]
  have hγη : η ≤ |γ| := hγ ▸ him
  have hγ2 : η ^ 2 ≤ γ ^ 2 := by
    rw [← sq_abs γ]; exact pow_le_pow_left₀ hη.le hγη 2
  have hvre0 : γ ^ 2 ≤ v.re := by rw [hvre]; linarith
  have hv0 : v ≠ 0 := by
    intro h
    have : v.re = 0 := by rw [h]; simp
    nlinarith [sq_nonneg η]
  -- `|v| ≤ γ² + |γ| + 1`
  have hvnorm : ‖v‖ ≤ γ ^ 2 + |γ| + 1 := by
    have h1 : ‖v‖ ≤ |v.re| + |v.im| := Complex.norm_le_abs_re_add_abs_im v
    have h2 : |v.re| ≤ γ ^ 2 + 1 / 4 := by
      rw [hvre, abs_le]; constructor <;> nlinarith [sq_nonneg δ]
    have h3 : |v.im| ≤ |γ| := by
      rw [hvim, abs_neg, abs_mul, abs_mul]
      have : |δ| ≤ 1 / 2 := by rw [hδ]; exact hs
      have h2' : |(2 : ℝ)| = 2 := abs_two
      rw [h2']
      nlinarith [abs_nonneg γ, abs_nonneg δ]
    linarith
  -- `γ² ≥ c (γ² + |γ| + 1)` with `c = η²/(η² + η + 1)`
  have hc : η ^ 2 / (η ^ 2 + η + 1) * (γ ^ 2 + |γ| + 1) ≤ γ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h4 : η ^ 2 * |γ| ≤ γ ^ 2 * η := by
      rw [← sq_abs γ]
      nlinarith [mul_nonneg (mul_nonneg hη.le (abs_nonneg γ)) (sub_nonneg.mpr hγη)]
    nlinarith
  have hnorm1 : ‖1 / v‖ = 1 / ‖v‖ := by rw [norm_div, norm_one]
  have hre1 : (1 / v).re = v.re / ‖v‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hnorm1, hre1]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [show v.re / ‖v‖ ^ 2 = (v.re / ‖v‖) * (1 / ‖v‖) by field_simp]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [le_div_iff₀ hvpos]
  have hc0 : 0 ≤ η ^ 2 / (η ^ 2 + η + 1) := by positivity
  calc η ^ 2 / (η ^ 2 + η + 1) * ‖v‖ ≤ η ^ 2 / (η ^ 2 + η + 1) * (γ ^ 2 + |γ| + 1) :=
        mul_le_mul_of_nonneg_left hvnorm hc0
    _ ≤ γ ^ 2 := hc
    _ ≤ v.re := hvre0

theorem unconditional_angle_xiZeroCopy {η : ℝ} (hη : 0 < η)
    (hgap : ∀ ρ : XiDivisorSupport, η ≤ |(ρ : ℂ).im|) (q : XiZeroCopy) :
    η ^ 2 / (η ^ 2 + η + 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re :=
  unconditional_angle_re_one_div hη (abs_re_sub_half_lt_half_xiZeroCopy q).le (hgap q.1)

/-- **The unconditional constant-vector producer.**  For some `κ > 0` and every large `N`, the
level-one constant-vector tests on `(N, 2N]` are positive at all amplitudes
`|z| ≤ κ/E_{1/2}(N) = κ log N/√N`. -/
theorem exists_eventually_jasConstShellSmallPositive :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop,
      JasConstShellSmallPositive N (κ / jasMainScale (1 / 2) N) := by
  obtain ⟨η, hη, hgap⟩ := exists_xiDivisorSupport_abs_im_lower_bound
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (η ^ 2 / (η ^ 2 + η + 1)) 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact lt_min (by positivity) one_pos
  have hc1 : c ≤ 1 := by rw [hc]; exact min_le_right _ _
  have hcw : ∀ q : XiZeroCopy, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := fun q =>
    (mul_le_mul_of_nonneg_right (by rw [hc]; exact min_le_left _ _) (norm_nonneg _)).trans
      (unconditional_angle_xiZeroCopy hη hgap q)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * (1 / (1 - 1 / 2) + 1) := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; norm_num
  refine ⟨c / (4 * C), by positivity, ?_⟩
  have ev1 : ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum (1 / 2) (2 * N) ≤ C * jasMainScale (1 / 2) N := by
    filter_upwards [tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le_main (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) one_pos), eventually_ge_atTop 2] with N hN hN2
    have h0 : (0 : ℝ) ≤ 1 / (1 - 1 / 2) + 1 := by norm_num
    have h1 := mul_le_mul_of_nonneg_left
      (jasMainScale_two_mul_le (show (0 : ℝ) ≤ 1 / 2 by norm_num) hN2) h0
    have e : C * jasMainScale (1 / 2) N = (1 / (1 - 1 / 2) + 1) * (2 * jasMainScale (1 / 2) N) := by
      rw [hC]; ring
    rw [e]; linarith
  filter_upwards [ev1, eventually_ge_atTop 2] with N hN1 hN2 z hz
  have hE0 : 0 < jasMainScale (1 / 2) N := jasMainScale_pos hN2
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c / (4 * C) / jasMainScale (1 / 2) N := ⟨_, rfl⟩
  rw [← hr] at hz
  have hrE : r * (C * jasMainScale (1 / 2) N) = c / 4 := by
    rw [hr]; field_simp
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  rw [← hu]
  have hun : ‖u‖ ≤ ‖z‖ := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg _) (by nlinarith [norm_nonneg z])
  have hu2 : ‖u‖ ≤ r := hun.trans hz
  have hkern : ∀ (v : ℂ), ‖v‖ ≤ r → ∀ q : XiZeroCopy,
      ‖jasConstKernel (jasPrimeWindow N (2 * N)) 1 v (q.1 : ℂ) - 1‖ ≤ c := by
    intro v hv q
    obtain ⟨-, hb2⟩ := jasConst_set_bounds (P := jasPrimeWindow N (2 * N)) (σ := 1) (δ := 1 / 2)
      (by norm_num) v (abs_re_sub_half_lt_half_xiZeroCopy q).le
    have hS := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) (1 / 2)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hb2
    have hsum0 : 0 ≤ ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(1 / 2) * Real.log p) :=
      Finset.sum_nonneg fun p _ => (Real.exp_pos _).le
    have hx : ∑ p ∈ jasPrimeWindow N (2 * N), ‖jasConstFactor 1 v p (q.1 : ℂ) - 1‖ ≤ c / 2 := by
      refine hb2.trans ?_
      have h1 : 2 * ‖v‖ * ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(1 / 2) * Real.log p) ≤
          2 * r * (C * jasMainScale (1 / 2) N) :=
        mul_le_mul (by linarith) (hS.trans hN1) hsum0 (by linarith)
      linarith
    refine (norm_jasConstKernel_sub_one_le _ 1 v _).trans ?_
    have h3 : Real.exp (c / 2) - 1 ≤ c := by
      have h4 : Real.exp (c / 2) ≤ 1 + 2 * (c / 2) := by
        have := Real.exp_bound' (x := c / 2) (by positivity) (by linarith) (n := 1) one_pos
        simp at this
        nlinarith [Real.exp_pos (c / 2)]
      linarith
    exact (sub_le_sub_right (Real.exp_le_exp.mpr hx) 1).trans h3
  have hcu : ‖conj u‖ ≤ r := by rw [Complex.norm_conj]; exact hu2
  have hterm : ∀ q : XiZeroCopy, 0 ≤ (jasConstPairTerm (jasPrimeWindow N (2 * N)) 1 u
      (q.1 : ℂ)).re := fun q =>
    re_jasConstPairTerm_nonneg_of_small (hcw q) (hkern u hu2 q) (hkern (conj u) hcu q)
  rw [Complex.re_tsum (summable_jasConstPairTerm _ 1 u)]
  exact tsum_nonneg hterm

/-! ## The radius law -/

/-- **The shell positivity radius is `N^{−δ*+o(1)}`.**  If an off-line zero has the largest
distance `δ*` from the critical line, then for every `ε > 0` and every large `N` the constant-vector
tests on `(N, 2N]` are positive at all amplitudes `|z| ≤ N^{−(δ*+ε)}` and negative at some amplitude
`|z| ≤ N^{−(δ*−ε)}`. -/
theorem eventually_shell_radius_law (q₀ : XiZeroCopy) (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      JasConstShellSmallPositive N ((N : ℝ) ^ (-(|(q₀.1 : ℂ).re - 1 / 2| + ε))) ∧
        ¬ JasConstShellSmallPositive N ((N : ℝ) ^ (-(|(q₀.1 : ℂ).re - 1 / 2| - ε))) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(q₀.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  rw [← hδ] at hmax ⊢
  have hδ0 : 0 < δ := by rw [hδ]; exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : δ < 1 / 2 := hδ ▸ abs_re_sub_half_lt_half_xiZeroCopy q₀
  have hpos := eventually_jasConstShellSmallPositive (β' := δ) (β := δ + ε) hδ0 hδ1
    (by linarith) hmax
  have hneg := eventually_exists_small_neg_shell_of_maximal_offLine q₀ hoff
    (hδ ▸ hmax) (σ := 1) (β := δ - ε) (by rw [← hδ]; linarith) (by rw [← hδ]; linarith)
    (by rw [← hδ]; linarith)
  filter_upwards [hpos, hneg] with N hN1 hN2
  refine ⟨hN1, fun h => ?_⟩
  obtain ⟨z, hz, hlt⟩ := hN2
  exact absurd (h z hz) (not_le.mpr hlt)

/-- **Sandwich.**  Under a maximal off-line zero at distance `δ*`, for every `β < δ*` and every
large `N` the positivity radius lies in `[κ log N/√N, N^{−β}]`, with the unconditional `κ` of
`exists_eventually_jasConstShellSmallPositive`. -/
theorem exists_eventually_shell_radius_sandwich (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ β : ℝ, β < |(q₀.1 : ℂ).re - 1 / 2| → ∀ᶠ N : ℕ in atTop,
      JasConstShellSmallPositive N (κ / jasMainScale (1 / 2) N) ∧
        ¬ JasConstShellSmallPositive N ((N : ℝ) ^ (-β)) := by
  obtain ⟨κ, hκ, hev⟩ := exists_eventually_jasConstShellSmallPositive
  refine ⟨κ, hκ, fun β hβ => ?_⟩
  have hneg := eventually_exists_small_neg_shell_of_maximal_offLine q₀ hoff hmax (σ := 1) (β := β)
    (by linarith [abs_re_sub_half_lt_half_xiZeroCopy q₀]) (by linarith [abs_pos.mpr (sub_ne_zero.mpr hoff)])
    (by linarith)
  filter_upwards [hev, hneg] with N hN1 hN2
  refine ⟨hN1, fun h => ?_⟩
  obtain ⟨z, hz, hlt⟩ := hN2
  exact absurd (h z hz) (not_le.mpr hlt)

end

end RHTower
