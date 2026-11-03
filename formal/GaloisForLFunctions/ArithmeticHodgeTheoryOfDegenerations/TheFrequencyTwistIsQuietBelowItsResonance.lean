import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsDiagonalInTheRamanujanBasis
import GaloisForLFunctions.RHTower.Sieve.DirichletKernelBound

/-!
# The frequency twist is quiet below its resonance

The twist `χ_α(n) = cos(2πnα)` of a real frequency `α` is not periodic when `α` is irrational, but
it has the two properties the twisted second-order theory uses:

* **Bounded partial sums** (`abs_sum_range_freqTwist_le`): `|Σ_{j<n} cos(2πjα)| ≤ 1/|sin πα|`
  (geometric sums), so twisted Riemann sums are `O(1/N)` and the pole terms `O(N^{−2})`.
* **Kuzmin–Landau with a rotation** (`norm_partial_rot_le`): for `u = {α} ∈ (0, 1)` and
  `0 ≤ τ ≤ π n₀ (1 − u)`, the phases `(n₀ + j)α + τ log(n₀ + j)/2π` have increments in
  `[(1 − u)/2, 1 − u]` modulo the integers, monotone in `j`, so the partial sums of
  `e((n₀ + j)α) (n₀ + j)^{iτ}` are bounded uniformly in the length.
* **The quiet region** (`exists_freqLow_energy_le`): below `N e^{−A} min(u, 1 − u)` the block of a
  window twisted by `χ_α` has `|D_x(τ)| ≤ K/√N` and energy `O(N^{−1/2})`; unlike a periodic twist
  there is no `1/τ` loss, since a single frequency has a single resonance.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The frequency twist `n ↦ cos(2πnα)`. -/
def freqTwist (α : ℝ) (n : ℕ) : ℝ := Real.cos (2 * Real.pi * n * α)

theorem abs_freqTwist_le (α : ℝ) (n : ℕ) : |freqTwist α n| ≤ 1 := Real.abs_cos_le_one _

/-- `e(α) ≠ 1` off the integers. -/
theorem cexp_two_pi_ne_one {α : ℝ} (hα : Real.sin (Real.pi * α) ≠ 0) :
    Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, Complex.intCast_re, Complex.intCast_im, zero_mul,
    Complex.re_ofNat, Complex.im_ofNat] at him
  have hk' : α = k := by
    have hπ := Real.pi_pos
    simp at him
    nlinarith
  apply hα
  rw [hk', mul_comm]
  exact Real.sin_int_mul_pi k

/-- **The partial sums of a frequency twist are bounded**: `|Σ_{j<n} cos(2πjα)| ≤ 1/|sin πα|`. -/
theorem abs_sum_range_freqTwist_le {α : ℝ} (hα : Real.sin (Real.pi * α) ≠ 0) (n : ℕ) :
    |∑ j ∈ range n, freqTwist α j| ≤ 1 / |Real.sin (Real.pi * α)| := by
  have hb := RHTower.Sieve.norm_sum_exp_le (cexp_two_pi_ne_one hα) n
  rw [show 2 * Real.pi * α / 2 = Real.pi * α by ring] at hb
  have e : ∑ j ∈ range n, freqTwist α j =
      (∑ j ∈ range n, Complex.exp (((j * (2 * Real.pi * α) : ℝ) : ℂ) * Complex.I)).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [Complex.exp_ofReal_mul_I_re, freqTwist]
    congr 1
    ring
  rw [e]
  exact (Complex.abs_re_le_norm _).trans hb

/-- `log(x + 1) − log x ≤ 1/x`. -/
theorem log_succ_sub_log_le {x : ℝ} (hx : 0 < x) : Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [← Real.log_div (by linarith) hx.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- Concavity of the logarithm on consecutive points. -/
theorem log_add_two_sub_le {x : ℝ} (hx : 0 < x) :
    Real.log (x + 2) - Real.log (x + 1) ≤ Real.log (x + 1) - Real.log x := by
  have h1 : Real.log (x + 2) + Real.log x ≤ Real.log (x + 1) + Real.log (x + 1) := by
    rw [← Real.log_mul (by linarith) hx.ne', ← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  linarith

/-- **Kuzmin–Landau with a rotation.** For `u = {α} ∈ (0, 1)`, `0 < δ ≤ min((1 − u)/2, u)` and
`0 ≤ τ ≤ π n₀ (1 − u)`, the partial sums of `e((n₀ + j)α + τ log(n₀ + j)/2π)` are at most
`3/(2δ) + 1`. -/
theorem norm_partial_rot_le {α : ℝ} (hu0 : 0 < Int.fract α) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ (1 - Int.fract α) / 2) (hδ2 : δ ≤ Int.fract α) {n₀ : ℕ}
    (hn₀ : 1 ≤ n₀) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ Real.pi * n₀ * (1 - Int.fract α)) (k : ℕ) :
    ‖∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * α) +
        τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 3 / (2 * δ) + 1 := by
  set u := Int.fract α with hu
  have hu1 : u < 1 := Int.fract_lt_one α
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  set ψ : ℕ → ℝ := fun j => ((⌊α⌋ : ℝ) + 1) * j -
    ((((n₀ + j : ℕ) : ℝ)) * α + τ * Real.log ((n₀ + j : ℕ) : ℝ) / (2 * Real.pi)) with hψ
  -- each term is the conjugate of a Kuzmin–Landau term
  have hterm : ∀ j : ℕ, Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * α) +
      τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      conj (Complex.exp (((2 * Real.pi * ψ j : ℝ) : ℂ) * Complex.I)) := by
    intro j
    have key : (((2 * Real.pi * ψ j : ℝ) : ℂ) * Complex.I) =
        ((((⌊α⌋ + 1) * j : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) +
          (-((((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * α) +
            τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      simp only [hψ]; push_cast; field_simp; ring
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  have hsum : ∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * α) +
      τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      conj (∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * ψ j : ℝ) : ℂ) * Complex.I)) := by
    rw [map_sum]
    exact sum_congr rfl fun j _ => hterm j
  rw [hsum, RCLike.norm_conj]
  -- the increments `1 − u − ε_m`
  set ε : ℕ → ℝ := fun m => τ / (2 * Real.pi) *
    (Real.log ((n₀ + m : ℕ) + 1 : ℝ) - Real.log ((n₀ + m : ℕ) : ℝ)) with hε
  have hinc : ∀ m, ψ (m + 1) - ψ m = 1 - u - ε m := by
    intro m
    have hfl : ((⌊α⌋ : ℤ) : ℝ) = α - u := by rw [hu, Int.self_sub_fract]
    simp only [hψ, hε]
    push_cast
    rw [show (n₀ : ℝ) + (m + 1) = (n₀ + m) + 1 by ring, hfl]
    field_simp
    ring
  have hε0 : ∀ m, 0 ≤ ε m := fun m => by
    simp only [hε]
    have : Real.log ((n₀ + m : ℕ) : ℝ) ≤ Real.log ((n₀ + m : ℕ) + 1 : ℝ) :=
      Real.log_le_log (by positivity) (by linarith)
    have : 0 ≤ τ / (2 * Real.pi) := by positivity
    nlinarith
  have hεle : ∀ m, ε m ≤ (1 - u) / 2 := fun m => by
    simp only [hε]
    have hx : (0 : ℝ) < ((n₀ + m : ℕ) : ℝ) := by positivity
    have h1 := log_succ_sub_log_le hx
    have h2 : 1 / ((n₀ + m : ℕ) : ℝ) ≤ 1 / (n₀ : ℝ) :=
      one_div_le_one_div_of_le hn0 (by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hτ' : τ / (2 * Real.pi) ≤ n₀ * (1 - u) / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hτ0' : 0 ≤ τ / (2 * Real.pi) := by positivity
    have hd : Real.log ((n₀ + m : ℕ) + 1 : ℝ) - Real.log ((n₀ + m : ℕ) : ℝ) ≤ 1 / (n₀ : ℝ) :=
      h1.trans h2
    have hd0 : 0 ≤ Real.log ((n₀ + m : ℕ) + 1 : ℝ) - Real.log ((n₀ + m : ℕ) : ℝ) := by
      have : Real.log ((n₀ + m : ℕ) : ℝ) ≤ Real.log ((n₀ + m : ℕ) + 1 : ℝ) :=
        Real.log_le_log hx (by linarith)
      linarith
    calc τ / (2 * Real.pi) * (Real.log ((n₀ + m : ℕ) + 1 : ℝ) - Real.log ((n₀ + m : ℕ) : ℝ))
        ≤ (n₀ * (1 - u) / 2) * (1 / (n₀ : ℝ)) := mul_le_mul hτ' hd hd0 (by nlinarith)
      _ = (1 - u) / 2 := by field_simp
  have hεmono : ∀ m, ε (m + 1) ≤ ε m := fun m => by
    simp only [hε]
    have hx : (0 : ℝ) < ((n₀ + m : ℕ) : ℝ) := by positivity
    have h := log_add_two_sub_le hx
    have h' : Real.log (((n₀ + m : ℕ) : ℝ) + 1 + 1) - Real.log (((n₀ + m : ℕ) : ℝ) + 1) ≤
        Real.log (((n₀ + m : ℕ) : ℝ) + 1) - Real.log ((n₀ + m : ℕ) : ℝ) := by
      rw [show ((n₀ + m : ℕ) : ℝ) + 1 + 1 = ((n₀ + m : ℕ) : ℝ) + 2 by ring]; exact h
    have : 0 ≤ τ / (2 * Real.pi) := by positivity
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at h' ⊢
    nlinarith [mul_le_mul_of_nonneg_left h' this]
  refine RHTower.Sieve.kuzminLandau_band ψ k hδ0 (fun m _ => ?_) (fun m _ => ?_) (fun m _ => ?_)
  · rw [hinc]; linarith [hεle m]
  · rw [hinc]; linarith [hε0 m]
  · rw [hinc, hinc]; linarith [hεmono m]

/-- **Kuzmin–Landau for a frequency twist.** For `u = {α} ∈ (0, 1)`, `0 < δ ≤ min(u, 1 − u)/2` and
`0 ≤ τ ≤ π n₀ min(u, 1 − u)`, the partial sums of `cos(2π(n₀ + j)α) (n₀ + j)^{iτ}` are at most
`3/(2δ) + 1`: the cosine is the mean of the rotations by `α` and `−α`. -/
theorem norm_partial_freqTwist_cpow_le {α : ℝ} (hu0 : 0 < Int.fract α) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ min (Int.fract α) (1 - Int.fract α) / 2) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ Real.pi * n₀ * min (Int.fract α) (1 - Int.fract α)) (k : ℕ) :
    ‖∑ j ∈ range (k + 1), (freqTwist α (n₀ + j) : ℂ) *
        Complex.exp (((τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      3 / (2 * δ) + 1 := by
  set u := Int.fract α with hu
  have hu1 : u < 1 := Int.fract_lt_one α
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  have hm1 : min u (1 - u) ≤ u := min_le_left _ _
  have hm2 : min u (1 - u) ≤ 1 - u := min_le_right _ _
  have hfr : Int.fract (-α) = 1 - u := Int.fract_neg (by rw [← hu]; exact hu0.ne')
  -- the two rotations
  have hA₁ := norm_partial_rot_le hu0 hδ0 (by linarith) (by linarith) hn₀ hτ0
    (by nlinarith) k
  have hA₂ := norm_partial_rot_le (α := -α) (by rw [hfr]; linarith) hδ0 (by rw [hfr]; linarith)
    (by rw [hfr]; linarith) hn₀ hτ0 (by rw [hfr]; nlinarith) k
  have hsplit : ∑ j ∈ range (k + 1), (freqTwist α (n₀ + j) : ℂ) *
      Complex.exp (((τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      (∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * α) +
          τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
        ∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * -α) +
          τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [freqTwist, Complex.ofReal_cos, Complex.cos, add_div, add_mul, div_mul_eq_mul_div,
      div_mul_eq_mul_div, ← Complex.exp_add, ← Complex.exp_add, add_div]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  rw [hsplit, norm_div, Complex.norm_ofNat]
  have := norm_add_le (∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * α) +
          τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
    (∑ j ∈ range (k + 1), Complex.exp (((2 * Real.pi * (((n₀ + j : ℕ) : ℝ) * -α) +
          τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))
  linarith

/-- **A frequency block below its resonance**: for `|τ| ≤ π N e^{−A} min(u, 1 − u)`,
`|D_x(τ)| ≤ (3/(2δ) + 1)(L e^{3A/2} + B e^{A/2})/√N`, `δ = min(u, 1 − u)/2`. -/
theorem norm_dirichletPoly_freqTwist_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {α : ℝ}
    (hu0 : 0 < Int.fract α) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) * min (Int.fract α) (1 - Int.fract α)) :
    ‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ≤
      (3 / (2 * (min (Int.fract α) (1 - Int.fract α) / 2)) + 1) *
        ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
  set m₀ := min (Int.fract α) (1 - Int.fract α) with hm₀
  have hm₀0 : 0 < m₀ := lt_min hu0 (by linarith [Int.fract_lt_one α])
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) * m₀ →
      ‖dirichletPoly N (twistedWeights h (freqTwist α) N) t‖ ≤
        (3 / (2 * (m₀ / 2)) + 1) *
          ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
    intro t ht htN
    set n₀ := windowStart A N with hn₀
    have h1 := one_le_windowStart hN A
    have h2 : n₀ ≤ N := windowStart_le hA
    have htn : t ≤ Real.pi * n₀ * m₀ := by
      refine htN.trans ?_
      have hw := le_windowStart A N
      rw [← hn₀] at hw
      have hpm : 0 ≤ Real.pi * m₀ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hw hpm]
    rw [dirichletPoly_twisted_eq_range hsupp hA _ hN]
    refine (norm_sum_mul_le_of_partial (fun j => horizonWeights h N (n₀ + j))
      (fun j => (freqTwist α (n₀ + j) : ℂ) * Complex.exp (((t * Real.log (n₀ + j) : ℝ) : ℂ) *
        Complex.I)) (N - n₀) (B := 3 / (2 * (m₀ / 2)) + 1) fun k _ => ?_).trans ?_
    · have := norm_partial_freqTwist_cpow_le hu0 (by positivity) le_rfl h1 ht htn k
      push_cast at this ⊢
      exact this
    · exact mul_le_mul_of_nonneg_left (variation_horizonWeights_le hsupp hA hB hL hN)
        (by positivity)
  rcases le_or_gt 0 τ with hpos | hneg
  · rw [abs_of_nonneg hpos] at hτ
    exact key τ hpos hτ
  · have := key (-τ) (by linarith) (by rw [abs_of_neg hneg] at hτ; exact hτ)
    rwa [norm_dirichletPoly_neg] at this

/-- **The quiet region of a frequency twist**: with `A' = A − log min(u, 1 − u)`, the energy of
the block on `|τ| ≤ N e^{−A'}` is `O(N^{−1/2})`. -/
theorem exists_freqLow_energy_le {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {α : ℝ} (hu0 : 0 < Int.fract α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A - Real.log (min (Int.fract α) (1 - Int.fract α))))))
          ((N : ℝ) * Real.exp (-(A - Real.log (min (Int.fract α) (1 - Int.fract α))))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N := by
  set m₀ := min (Int.fract α) (1 - Int.fract α) with hm₀
  have hm₀0 : 0 < m₀ := lt_min hu0 (by linarith [Int.fract_lt_one α])
  have hm₀1 : m₀ ≤ 1 := (min_le_right _ _).trans (by linarith [Int.fract_nonneg α])
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have := hL 1 0; norm_num at this; linarith [abs_nonneg (h 1 - h 0)]
  set K := 3 / (2 * (m₀ / 2)) + 1 with hK
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  have hK0 : 0 ≤ K := by positivity
  have hV0 : 0 ≤ V := by positivity
  refine ⟨2 * (Cφ * (K * V) ^ 2), by positivity, fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hexp : Real.exp (-(A - Real.log m₀)) = Real.exp (-A) * m₀ := by
    rw [show -(A - Real.log m₀) = -A + Real.log m₀ by ring, Real.exp_add, Real.exp_log hm₀0]
  set T₀ := (N : ℝ) * Real.exp (-(A - Real.log m₀)) with hT₀
  have hT₀0 : 0 ≤ T₀ := by positivity
  have hT₀N : T₀ ≤ N := by
    rw [hT₀, hexp]
    have : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have : Real.exp (-A) * m₀ ≤ 1 := by nlinarith [Real.exp_pos (-A)]
    nlinarith
  have hφb : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := fun τ => by
    have := hdecay (c / N * τ)
    rw [show ((c / N * τ : ℝ) : ℂ) = ((c / N : ℝ) : ℂ) * (τ : ℂ) by push_cast; ring] at this
    refine this.trans ?_
    have : (1 + |(c / N * τ)|) ^ (-q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
    nlinarith
  have hpt : ∀ τ ∈ Set.Icc (-T₀) T₀, ‖‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ^ 2 / N)‖ ≤
        Cφ * ((K * V) ^ 2 / (N : ℝ) ^ 2) := by
    intro τ hτ
    have hτ' : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) * m₀ := by
      refine (abs_le.mpr hτ).trans ?_
      rw [hT₀, hexp]
      have := Real.pi_gt_three
      have : 0 ≤ (N : ℝ) * (Real.exp (-A) * m₀) := by positivity
      nlinarith
    have hD := norm_dirichletPoly_freqTwist_le hsupp hA hB hL hu0 hN hτ'
    rw [← hm₀, ← hK, ← hV] at hD
    have hD2 : ‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ^ 2 / N ≤
        (K * V) ^ 2 / (N : ℝ) ^ 2 := by
      have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
      rw [div_le_div_iff₀ hN0 (by positivity)]
      calc ‖dirichletPoly N (twistedWeights h (freqTwist α) N) τ‖ ^ 2 * (N : ℝ) ^ 2
          ≤ (K * (V / Real.sqrt N)) ^ 2 * (N : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (K * V) ^ 2 * N := by
            rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]; field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hφb τ) hD2 (by positivity) hCφ
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-T₀) T₀)
    measure_Icc_lt_top hpt
  rw [Real.volume_real_Icc_of_le (by linarith)] at hI
  refine (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hI.trans ?_))
  have h1 : Cφ * ((K * V) ^ 2 / (N : ℝ) ^ 2) * (T₀ - -T₀) ≤ 2 * (Cφ * (K * V) ^ 2) / N := by
    have : Cφ * ((K * V) ^ 2 / (N : ℝ) ^ 2) * (T₀ - -T₀) =
        2 * (Cφ * (K * V) ^ 2) * (T₀ / (N : ℝ) ^ 2) := by ring
    rw [this, div_eq_mul_inv (2 * (Cφ * (K * V) ^ 2))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    calc T₀ ≤ N := hT₀N
      _ = (N : ℝ)⁻¹ * (N : ℝ) ^ 2 := by field_simp
  refine h1.trans (div_le_div_of_nonneg_left (by positivity) hsN ?_)
  calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := le_mul_of_one_le_left hsN.le hsN1
    _ = N := Real.mul_self_sqrt hN0.le

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
