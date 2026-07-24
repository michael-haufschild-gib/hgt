import Mathlib
import GaloisForLFunctions.RHTower.SquaredXiRadialJetSourceAlignment

/-!
# Radial-derivative identity for squared-Xi jets: analytic core

The squared-radial jet identity (equation (4) of the source-alignment card) applies the operator
`D = (1/(2w)) d/dw` iteratively to `F(w) = L(1/2+w)/w` and re-expresses `D^n F` through the shifted
derivatives `L^(j)(1/2+w)` weighted by the reverse-Bessel magnitudes.  This file formalizes the exact
calculus content of the induction step (equation (6)) for an arbitrary smooth `L`, unconditionally:
the chain rule for a shifted iterated derivative and the single-term product rule
`d/dw [w^m L^(j)(1/2+w)] = m w^(m-1) L^(j)(1/2+w) + w^m L^(j+1)(1/2+w)`.
-/

open scoped Topology

namespace RHTower

/-- The radial operator `D f = f'/(2w)`. -/
noncomputable def radialOp (f : ℝ → ℝ) (w : ℝ) : ℝ := deriv f w / (2 * w)

/-- The radial profile `F(w) = L(1/2+w)/w`. -/
noncomputable def radialProfile (L : ℝ → ℝ) (w : ℝ) : ℝ := L (1 / 2 + w) / w

/-- Chain rule for a shifted iterated derivative: `d/dw [L^(j)(c+w)] = L^(j+1)(c+w)`. -/
theorem deriv_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (j : ℕ) (c w : ℝ) :
    deriv (fun v => iteratedDeriv j L (c + v)) w = iteratedDeriv (j + 1) L (c + w) := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (c + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  rw [show (fun v => iteratedDeriv j L (c + v)) = (iteratedDeriv j L) ∘ (fun v => c + v) from rfl,
    deriv_comp w hd (by fun_prop), ← iteratedDeriv_succ]
  simp

/-- **Single-term radial derivative (equation (6) core).**  For a smooth `L`,
`d/dw [w^m · L^(j)(1/2+w)] = m·w^(m-1)·L^(j)(1/2+w) + w^m·L^(j+1)(1/2+w)`. -/
theorem deriv_pow_mul_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (m j : ℕ) (w : ℝ) :
    deriv (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v)) w =
      (m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w) := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (1 / 2 + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  have hg : DifferentiableAt ℝ (fun v => iteratedDeriv j L (1 / 2 + v)) w :=
    hd.comp w (by fun_prop)
  have hpow : HasDerivAt (fun v : ℝ => v ^ m) ((m : ℝ) * w ^ (m - 1)) w := by
    simpa using hasDerivAt_pow m w
  have hshift : HasDerivAt (fun v => iteratedDeriv j L (1 / 2 + v))
      (iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hg.hasDerivAt
    rwa [deriv_iteratedDeriv_shift hL j (1 / 2) w] at h
  have hmul : HasDerivAt (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v))
      ((m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hpow.mul hshift
    convert h using 1
  exact hmul.deriv

/-- HasDerivAt form of the single-term radial derivative. -/
theorem hasDerivAt_pow_mul_iteratedDeriv_shift
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (m j : ℕ) (w : ℝ) :
    HasDerivAt (fun v => v ^ m * iteratedDeriv j L (1 / 2 + v))
      ((m : ℝ) * w ^ (m - 1) * iteratedDeriv j L (1 / 2 + w) +
        w ^ m * iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
  have hd : DifferentiableAt ℝ (iteratedDeriv j L) (1 / 2 + w) :=
    (hL.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
  have hg : DifferentiableAt ℝ (fun v => iteratedDeriv j L (1 / 2 + v)) w :=
    hd.comp w (by fun_prop)
  have hpow : HasDerivAt (fun v : ℝ => v ^ m) ((m : ℝ) * w ^ (m - 1)) w := by
    simpa using hasDerivAt_pow m w
  have hshift : HasDerivAt (fun v => iteratedDeriv j L (1 / 2 + v))
      (iteratedDeriv (j + 1) L (1 / 2 + w)) w := by
    have h := hg.hasDerivAt
    rwa [deriv_iteratedDeriv_shift hL j (1 / 2) w] at h
  have h := hpow.mul hshift
  convert h using 1

/-- Radial jet sum with abstract real coefficients (for a fixed order): `∑_{j≤N} c j·w^j·L^(j)(1/2+w)`. -/
noncomputable def jetSum (L : ℝ → ℝ) (c : ℕ → ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), c j * (w ^ j * iteratedDeriv j L (1 / 2 + w))

/-- The derivative of the radial jet sum is the coefficientwise single-term derivative. -/
theorem hasDerivAt_jetSum
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (c : ℕ → ℝ) (N : ℕ) (w : ℝ) :
    HasDerivAt (fun v => jetSum L c N v)
      (∑ j ∈ Finset.range (N + 1), c j *
        ((j : ℝ) * w ^ (j - 1) * iteratedDeriv j L (1 / 2 + w) +
          w ^ j * iteratedDeriv (j + 1) L (1 / 2 + w))) w := by
  have h := HasDerivAt.sum (fun j (_ : j ∈ Finset.range (N + 1)) =>
    (hasDerivAt_pow_mul_iteratedDeriv_shift hL j j w).const_mul (c j))
  have hfe : (∑ j ∈ Finset.range (N + 1),
      fun v => c j * (v ^ j * iteratedDeriv j L (1 / 2 + v))) = fun v => jetSum L c N v := by
    funext v; simp only [jetSum, Finset.sum_apply]
  rwa [hfe] at h

/-- Signed radial-jet coefficient `(-1)^(n-j)·b_{n,j}`. -/
noncomputable def jetCoeff (n j : ℕ) : ℝ :=
  (-1) ^ (n - j) * (squaredRadialJetWeight n j : ℝ)

theorem jetCoeff_succ_zero (n : ℕ) :
    jetCoeff (n + 1) 0 = -(2 * (n : ℝ) + 1) * jetCoeff n 0 := by
  rw [jetCoeff, jetCoeff, Nat.sub_zero, Nat.sub_zero, squaredRadialJetWeight_succ_zero, pow_succ]
  push_cast
  ring

theorem jetCoeff_succ_top (n : ℕ) :
    jetCoeff (n + 1) (n + 1) = jetCoeff n n := by
  have hz : squaredRadialJetWeight n (n + 1) = 0 :=
    squaredRadialJetWeight_eq_zero_of_lt n (n + 1) (by omega)
  simp only [jetCoeff, Nat.sub_self, pow_zero, one_mul, squaredRadialJetWeight_succ_succ, hz,
    mul_zero, zero_add]

theorem jetCoeff_succ_mid (n i : ℕ) (hi : i < n) :
    jetCoeff n (i + 1) * ((i + 1 : ℝ) - (2 * n + 1)) + jetCoeff n i = jetCoeff (n + 1) (i + 1) := by
  have h2 : i ≤ 2 * n := by omega
  have hcast : ((2 * n - i : ℕ) : ℝ) = 2 * (n : ℝ) - i := by
    rw [Nat.cast_sub h2]; push_cast; ring
  have he1 : n - i = (n - (i + 1)) + 1 := by omega
  have he2 : (n + 1) - (i + 1) = (n - (i + 1)) + 1 := by omega
  rw [jetCoeff, jetCoeff, jetCoeff, squaredRadialJetWeight_succ_succ, he1, he2]
  simp only [pow_succ]
  push_cast [hcast]
  ring

/-- **Signed-coefficient sum recurrence (combinatorial core of identity (4)).**  Assembles the
pointwise `jetCoeff` recurrences: `∑_{j≤n} jetCoeff n j·(j·t j + t(j+1)) − (2n+1)·∑_{j≤n} jetCoeff n j·t j
= ∑_{j≤n+1} jetCoeff (n+1) j·t j`, for any sequence `t`. -/
theorem jetCoeff_sum_recurrence (n : ℕ) (t : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n + 1), jetCoeff n j * ((j : ℝ) * t j + t (j + 1)))
      - (2 * (n : ℝ) + 1) * (∑ j ∈ Finset.range (n + 1), jetCoeff n j * t j)
      = ∑ j ∈ Finset.range (n + 2), jetCoeff (n + 1) j * t j := by
  have hL : (∑ j ∈ Finset.range (n + 1), jetCoeff n j * ((j : ℝ) * t j + t (j + 1)))
        - (2 * (n : ℝ) + 1) * (∑ j ∈ Finset.range (n + 1), jetCoeff n j * t j)
      = (∑ j ∈ Finset.range (n + 1), jetCoeff n j * ((j : ℝ) - (2 * n + 1)) * t j)
        + (∑ j ∈ Finset.range (n + 1), jetCoeff n j * t (j + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hL, Finset.sum_range_succ' (fun j => jetCoeff n j * ((j : ℝ) - (2 * n + 1)) * t j) n,
    Finset.sum_range_succ (fun j => jetCoeff n j * t (j + 1)) n,
    Finset.sum_range_succ' (fun j => jetCoeff (n + 1) j * t j) (n + 1),
    Finset.sum_range_succ (fun i => jetCoeff (n + 1) (i + 1) * t (i + 1)) n]
  -- boundary rewrites
  have hz : jetCoeff n 0 * ((0 : ℝ) - (2 * n + 1)) * t 0 = jetCoeff (n + 1) 0 * t 0 := by
    rw [jetCoeff_succ_zero]; ring
  have htop : jetCoeff n n * t (n + 1) = jetCoeff (n + 1) (n + 1) * t (n + 1) := by
    rw [jetCoeff_succ_top]
  -- interior sums equal
  have hmid : ∑ i ∈ Finset.range n, (jetCoeff n (i + 1) * ((i + 1 : ℝ) - (2 * n + 1)) * t (i + 1)
        + jetCoeff n i * t (i + 1))
      = ∑ i ∈ Finset.range n, jetCoeff (n + 1) (i + 1) * t (i + 1) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.mp hi
    rw [← jetCoeff_succ_mid n i hi']
    ring
  rw [Finset.sum_add_distrib] at hmid
  push_cast at hz hmid ⊢
  linarith [hz, htop, hmid]

/-- **Calculus connection.**  Multiplying the jet-sum derivative by `w` clears the power shift:
`w·(jetSum L c n)′(w) = ∑_{j≤n} c j·(j·w^j·L^(j)(1/2+w) + w^(j+1)·L^(j+1)(1/2+w))`. -/
theorem w_mul_deriv_jetSum
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (c : ℕ → ℝ) (n : ℕ) (w : ℝ) :
    w * deriv (fun v => jetSum L c n v) w =
      ∑ j ∈ Finset.range (n + 1), c j *
        ((j : ℝ) * (w ^ j * iteratedDeriv j L (1 / 2 + w)) +
          w ^ (j + 1) * iteratedDeriv (j + 1) L (1 / 2 + w)) := by
  rw [(hasDerivAt_jetSum hL c n w).deriv, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hbridge : w * ((j : ℝ) * w ^ (j - 1)) = (j : ℝ) * w ^ j := by
    rcases j with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; ring
  rw [pow_succ]
  linear_combination (c j * iteratedDeriv j L (1 / 2 + w)) * hbridge

/-- **Radial-jet recurrence.**  `w·(jetSum_n)′(w) − (2n+1)·jetSum_n(w) = jetSum_{n+1}(w)`, connecting
the radial operator step to the coefficient recurrence (with `jetSum_n = jetSum L (jetCoeff n) n`). -/
theorem jetSum_recurrence
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (n : ℕ) (w : ℝ) :
    w * deriv (fun v => jetSum L (jetCoeff n) n v) w
        - (2 * (n : ℝ) + 1) * jetSum L (jetCoeff n) n w
      = jetSum L (jetCoeff (n + 1)) (n + 1) w := by
  rw [w_mul_deriv_jetSum hL (jetCoeff n) n w]
  simp only [jetSum]
  exact jetCoeff_sum_recurrence n (fun j => w ^ j * iteratedDeriv j L (1 / 2 + w))

open Filter Topology

/-- **Radial-derivative identity (equation (4)).**  For a smooth `L`, iterating the radial
operator `D = (1/(2w)) d/dw` on `F(w) = L(1/2+w)/w` gives, for `w > 0`,
`D^n F(w) = jetSum_n(w) / (2^n w^(2n+1))`. -/
theorem radialOp_iterate_eq
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (n : ℕ) :
    ∀ w : ℝ, 0 < w →
      (radialOp)^[n] (radialProfile L) w =
        jetSum L (jetCoeff n) n w / ((2 : ℝ) ^ n * w ^ (2 * n + 1)) := by
  induction n with
  | zero =>
    intro w hw
    simp [Function.iterate_zero, radialProfile, jetSum, jetCoeff,
      iteratedDeriv_zero, squaredRadialJetWeight_zero_zero]
  | succ n ih =>
    intro w hw
    have hw0 : w ≠ 0 := ne_of_gt hw
    rw [Function.iterate_succ_apply', radialOp]
    have heq : (radialOp)^[n] (radialProfile L) =ᶠ[𝓝 w]
        (fun v => jetSum L (jetCoeff n) n v / ((2 : ℝ) ^ n * v ^ (2 * n + 1))) := by
      filter_upwards [Ioi_mem_nhds hw] with v hv using ih v hv
    rw [heq.deriv_eq]
    have hnum := hasDerivAt_jetSum hL (jetCoeff n) n w
    have hden : HasDerivAt (fun v => (2 : ℝ) ^ n * v ^ (2 * n + 1))
        ((2 : ℝ) ^ n * ((2 * n + 1 : ℕ) * w ^ (2 * n + 1 - 1))) w :=
      (hasDerivAt_pow (2 * n + 1) w).const_mul ((2 : ℝ) ^ n)
    have hdne : (2 : ℝ) ^ n * w ^ (2 * n + 1) ≠ 0 := by positivity
    have hrec := jetSum_recurrence hL n w
    rw [show deriv (fun v => jetSum L (jetCoeff n) n v / ((2 : ℝ) ^ n * v ^ (2 * n + 1))) w
          = (deriv (fun v => jetSum L (jetCoeff n) n v) w * ((2 : ℝ) ^ n * w ^ (2 * n + 1))
              - jetSum L (jetCoeff n) n w * deriv (fun v => (2 : ℝ) ^ n * v ^ (2 * n + 1)) w)
            / ((2 : ℝ) ^ n * w ^ (2 * n + 1)) ^ 2
        from deriv_div hnum.differentiableAt hden.differentiableAt hdne,
      hden.deriv, show 2 * n + 1 - 1 = 2 * n from by omega, ← hrec, pow_succ (2 : ℝ) n,
      show 2 * (n + 1) + 1 = 2 * n + 1 + 2 from by ring, pow_add w (2 * n + 1) 2]
    field_simp
    push_cast
    ring

/-- **Positive rescaling (equation (5)).**  `(-1)^n·2^n·w^(2n+1)·D^n F(w) =
∑_{j≤n} (-1)^j·b_{n,j}·w^j·L^(j)(1/2+w)`, the RH-compatible alternating-sign form. -/
theorem radialJet_positive_rescaling
    {L : ℝ → ℝ} (hL : ContDiff ℝ (⊤ : WithTop ℕ∞) L) (n : ℕ) (w : ℝ) (hw : 0 < w) :
    (-1 : ℝ) ^ n * (2 : ℝ) ^ n * w ^ (2 * n + 1) * (radialOp)^[n] (radialProfile L) w
      = ∑ j ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ j * (squaredRadialJetWeight n j : ℝ) * w ^ j * iteratedDeriv j L (1 / 2 + w) := by
  have hne : (2 : ℝ) ^ n * w ^ (2 * n + 1) ≠ 0 := by positivity
  rw [radialOp_iterate_eq hL n w hw,
    show (-1 : ℝ) ^ n * 2 ^ n * w ^ (2 * n + 1) *
        (jetSum L (jetCoeff n) n w / (2 ^ n * w ^ (2 * n + 1)))
      = (-1 : ℝ) ^ n * jetSum L (jetCoeff n) n w by field_simp,
    jetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsign : (-1 : ℝ) ^ n * (-1) ^ (n - j) = (-1) ^ j := by
    rw [← pow_add, show n + (n - j) = 2 * (n - j) + j from by omega, pow_add, pow_mul]
    norm_num
  rw [jetCoeff, ← hsign]
  ring

end RHTower
