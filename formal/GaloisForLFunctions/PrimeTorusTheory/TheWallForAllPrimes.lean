import GaloisForLFunctions.PrimeTorusTheory.PrimeByPrimePaymentCannotUseTheGammaFactor
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# The wall for all primes

`agler_wall` used finitely many prime coordinates. On `Re s > σ₀ ≥ ½` the wall holds with all of them, because `Σ_p p^{−2σ}` converges there: the prime terms of the test on `(1, −1)` are dominated by a summable series, and one time sequence returns every prime (`exists_returns_all`).

**Theorem** (`agler_wall_all_primes`). Let `S`, `G` be functions on `Re s > σ₀`, with `|G| < 1`, both tending to `0` vertically. If

`1 − S(s) conj S(s') = Σ_p (1 − p^{−s} conj p^{−s'}) K_p(s,s') + (1 − G(s) conj G(s')) K_∞(s,s')`,

with `2`-positive kernels and the series convergent at every pair of points, then `|S| ≤ |G|`.

**The Euler factor cannot be paid.** The Euler factor of the Eisenstein scattering function is `E(s) = ζ(2s − 1)/ζ(2s)`, and `E(3) > 1`. So `S = G·E` has no decomposition with coordinate `G` (`no_decomposition_euler`). This is not vacuous: `S = E(s)/(s + 3)` is Schur on `Re s > 2` and decays vertically (`euler_test`).

**Sharpness.** `S` always has the decomposition with coordinate `G = S` itself, with `K_p = 0`, `K_∞ = 1` (`selfDecomposition`). So a coordinate system that returns can only certify through an archimedean coordinate that already carries `S`, and then the primes pay for nothing.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

local notation "conj" => starRingEnd ℂ

/-- The half-plane `Re s > σ₀`. -/
abbrev Plane (σ₀ : ℝ) : Type := {s : ℂ // σ₀ < s.re}

variable {σ₀ : ℝ}

theorem half_lt_re [Fact ((1 : ℝ) / 2 ≤ σ₀)] (s : Plane σ₀) : (1 : ℝ) / 2 < s.1.re :=
  lt_of_le_of_lt (Fact.out : (1 : ℝ) / 2 ≤ σ₀) s.2

/-- The vertical translate of a point. -/
def vshift' (s : Plane σ₀) (τ : ℝ) : Plane σ₀ :=
  ⟨s.1 + (τ : ℂ) * I, by simpa using s.2⟩

/-- The prime coordinate on `Re s > ½`. -/
def allPrimeCoord (p : Nat.Primes) (s : Plane σ₀) : ℂ := ((p : ℕ) : ℂ) ^ (-s.1)

theorem norm_allPrimeCoord (p : Nat.Primes) (s : Plane σ₀) :
    ‖allPrimeCoord p s‖ = ((p : ℕ) : ℝ) ^ (-s.1.re) := by
  unfold allPrimeCoord
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]

theorem norm_allPrimeCoord_vshift (p : Nat.Primes) (s : Plane σ₀) (τ : ℝ) :
    ‖allPrimeCoord p (vshift' s τ)‖ = ‖allPrimeCoord p s‖ := by
  rw [norm_allPrimeCoord, norm_allPrimeCoord]
  simp [vshift']

/-- `p^{−2σ} ≤ ½` on `Re s > ½`. -/
theorem norm_allPrimeCoord_sq_le [Fact ((1 : ℝ) / 2 ≤ σ₀)] (p : Nat.Primes) (s : Plane σ₀) :
    ‖allPrimeCoord p s‖ ^ 2 ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hσ : (1 : ℝ) / 2 < s.1.re := half_lt_re s
  rw [norm_allPrimeCoord, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hexp : -s.1.re * ((2 : ℕ) : ℝ) ≤ -1 := by
    push_cast
    linarith
  calc
    ((p : ℕ) : ℝ) ^ (-s.1.re * ((2 : ℕ) : ℝ)) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, one_div]
      exact inv_anti₀ (by norm_num) hp2

theorem norm_allPrimeCoord_lt [Fact ((1 : ℝ) / 2 ≤ σ₀)] (p : Nat.Primes) (s : Plane σ₀) : ‖allPrimeCoord p s‖ < 1 := by
  have h := norm_allPrimeCoord_sq_le p s
  have h0 := norm_nonneg (allPrimeCoord p s)
  nlinarith

/-- The series `Σ_p p^{−2σ}` converges on `Re s > ½`. -/
theorem summable_norm_allPrimeCoord_sq [Fact ((1 : ℝ) / 2 ≤ σ₀)] (s : Plane σ₀) :
    Summable fun p : Nat.Primes => ‖allPrimeCoord p s‖ ^ 2 := by
  have hσ : (1 : ℝ) < 2 * s.1.re := by
    have : (1 : ℝ) / 2 < s.1.re := half_lt_re s
    linarith
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (-(2 * s.1.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcomp := hsum.comp_injective (Nat.Primes.coe_nat_injective)
  refine hcomp.congr fun p => ?_
  simp only [Function.comp]
  rw [norm_allPrimeCoord, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

/-- **All primes return along one time sequence.** -/
theorem exists_returns_all :
    ∃ τ : ℕ → ℝ, Tendsto τ atTop atTop ∧ ∀ p : Nat.Primes,
      Tendsto (fun j => cexp (-(((τ j * Real.log (p : ℕ) : ℝ) : ℂ) * I))) atTop (𝓝 1) := by
  classical
  -- For each `j`: a time at least `j` returning the primes up to `j` to within `1/(j + 1)`.
  have hstep : ∀ j : ℕ, ∃ t : ℝ, (j : ℝ) ≤ t ∧ ∀ p : Nat.Primes, (p : ℕ) ≤ j →
      ‖cexp (-(((t * Real.log (p : ℕ) : ℝ) : ℂ) * I)) - 1‖ < 1 / ((j : ℝ) + 1) := by
    intro j
    obtain ⟨τ, hτ, hret⟩ := exists_returns (Finset.range (j + 1))
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hev : ∀ᶠ i in atTop, ∀ n ∈ Finset.range (j + 1),
        ‖cexp (-(((τ i * Real.log n : ℝ) : ℂ) * I)) - 1‖ < 1 / ((j : ℝ) + 1) := by
      refine (Finset.eventually_all _).mpr fun n hn => ?_
      have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp (hret n hn)).eventually (gt_mem_nhds hpos)
      exact h1
    obtain ⟨i, hi1, hi2⟩ := (hev.and (hτ.eventually_ge_atTop (j : ℝ))).exists
    refine ⟨τ i, hi2, fun p hp => hi1 p (Finset.mem_range.mpr (by omega))⟩
  choose τ hτ1 hτ2 using hstep
  refine ⟨τ, tendsto_atTop_mono hτ1 tendsto_natCast_atTop_atTop, fun p => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (p : ℕ)] with j hj
  exact (hτ2 j p hj).le

/-- A decomposition of `S` in all prime coordinates and an archimedean coordinate. -/
structure AglerDecompositionAll (S G : Plane σ₀ → ℂ) where
  /-- The conductance of the prime `p`. -/
  K : Nat.Primes → Plane σ₀ → Plane σ₀ → ℂ
  /-- The conductance of the archimedean coordinate. -/
  K₀ : Plane σ₀ → Plane σ₀ → ℂ
  psd : ∀ p, TwoPositive (K p)
  psd₀ : TwoPositive K₀
  hasSum : ∀ x y, HasSum (fun p => (1 - allPrimeCoord p x * conj (allPrimeCoord p y)) * K p x y)
    (1 - S x * conj (S y) - (1 - G x * conj (G y)) * K₀ x y)

variable [Fact ((1 : ℝ) / 2 ≤ σ₀)] {S G : Plane σ₀ → ℂ}

omit [Fact ((1 : ℝ) / 2 ≤ σ₀)] in
/-- The real diagonal series of the decomposition, with nonnegative terms. -/
theorem AglerDecompositionAll.hasSum_diag (D : AglerDecompositionAll S G) (x : Plane σ₀) :
    HasSum (fun p => (1 - ‖allPrimeCoord p x‖ ^ 2) * (D.K p x x).re)
      (1 - ‖S x‖ ^ 2 - (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re) := by
  have h := Complex.hasSum_re (D.hasSum x x)
  have e1 : ∀ p, ((1 - allPrimeCoord p x * conj (allPrimeCoord p x)) * D.K p x x).re =
      (1 - ‖allPrimeCoord p x‖ ^ 2) * (D.K p x x).re := by
    intro p
    rw [one_sub_mul_conj, Complex.re_ofReal_mul]
  have e2 : (1 - S x * conj (S x) - (1 - G x * conj (G x)) * D.K₀ x x).re =
      1 - ‖S x‖ ^ 2 - (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re := by
    rw [Complex.sub_re, one_sub_mul_conj, one_sub_mul_conj, Complex.ofReal_re, Complex.re_ofReal_mul]
  simp_rw [e1] at h
  rwa [e2] at h

theorem AglerDecompositionAll.coord_le (D : AglerDecompositionAll S G) (p : Nat.Primes)
    (hG : ∀ x, ‖G x‖ < 1) (x : Plane σ₀) :
    (1 - ‖allPrimeCoord p x‖ ^ 2) * (D.K p x x).re ≤ 1 := by
  have hs := D.hasSum_diag x
  have hnn : ∀ q, 0 ≤ (1 - ‖allPrimeCoord q x‖ ^ 2) * (D.K q x x).re := fun q =>
    mul_nonneg (by nlinarith [norm_allPrimeCoord_lt q x, norm_nonneg (allPrimeCoord q x)])
      ((D.psd q).diag_re_nonneg x)
  have h1 := le_hasSum hs p fun q _ => hnn q
  have h2 : 0 ≤ (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re :=
    mul_nonneg (by nlinarith [hG x, norm_nonneg (G x)]) (D.psd₀.diag_re_nonneg x)
  nlinarith [sq_nonneg ‖S x‖]

theorem AglerDecompositionAll.arch_le (D : AglerDecompositionAll S G) (x : Plane σ₀) :
    (1 - ‖G x‖ ^ 2) * (D.K₀ x x).re ≤ 1 - ‖S x‖ ^ 2 := by
  have hs := D.hasSum_diag x
  have hnn : ∀ q, 0 ≤ (1 - ‖allPrimeCoord q x‖ ^ 2) * (D.K q x x).re := fun q =>
    mul_nonneg (by nlinarith [norm_allPrimeCoord_lt q x, norm_nonneg (allPrimeCoord q x)])
      ((D.psd q).diag_re_nonneg x)
  have := hs.nonneg hnn
  linarith

omit [Fact ((1 : ℝ) / 2 ≤ σ₀)] in
/-- The prime terms of the test vector, as a real series. -/
theorem AglerDecompositionAll.hasSum_test (D : AglerDecompositionAll S G) (x₁ x₂ : Plane σ₀) :
    HasSum (fun p => (form2 (D.K p x₁ x₁) (D.K p x₁ x₂) (D.K p x₂ x₁) (D.K p x₂ x₂) 1 (-1) -
        form2 (D.K p x₁ x₁) (D.K p x₁ x₂) (D.K p x₂ x₁) (D.K p x₂ x₂)
          (allPrimeCoord p x₁) (-allPrimeCoord p x₂)).re)
      (-‖S x₁ - S x₂‖ ^ 2 -
        (form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) 1 (-1) -
          form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) (G x₁) (-G x₂)).re) := by
  have h11 := D.hasSum x₁ x₁
  have h12 := D.hasSum x₁ x₂
  have h21 := D.hasSum x₂ x₁
  have h22 := D.hasSum x₂ x₂
  have hcomb := Complex.hasSum_re (((h11.sub h12).sub (h21.sub h22)))
  have hterm : ∀ p, ((1 - allPrimeCoord p x₁ * conj (allPrimeCoord p x₁)) * D.K p x₁ x₁ -
      (1 - allPrimeCoord p x₁ * conj (allPrimeCoord p x₂)) * D.K p x₁ x₂ -
      ((1 - allPrimeCoord p x₂ * conj (allPrimeCoord p x₁)) * D.K p x₂ x₁ -
        (1 - allPrimeCoord p x₂ * conj (allPrimeCoord p x₂)) * D.K p x₂ x₂)).re =
      (form2 (D.K p x₁ x₁) (D.K p x₁ x₂) (D.K p x₂ x₁) (D.K p x₂ x₂) 1 (-1) -
        form2 (D.K p x₁ x₁) (D.K p x₁ x₂) (D.K p x₂ x₁) (D.K p x₂ x₂)
          (allPrimeCoord p x₁) (-allPrimeCoord p x₂)).re := fun p => by
    rw [form2_test]
  simp_rw [hterm] at hcomb
  have hc : ((-‖S x₁ - S x₂‖ ^ 2 : ℝ) : ℂ) =
      (1 - S x₁ * conj (S x₁)) - (1 - S x₁ * conj (S x₂)) -
        ((1 - S x₂ * conj (S x₁)) - (1 - S x₂ * conj (S x₂))) := by
    have := Complex.mul_conj (S x₁ - S x₂)
    rw [Complex.normSq_eq_norm_sq] at this
    rw [Complex.ofReal_neg, ← this]
    simp only [map_sub]
    ring
  have hval : (1 - S x₁ * conj (S x₁) - (1 - G x₁ * conj (G x₁)) * D.K₀ x₁ x₁ -
      (1 - S x₁ * conj (S x₂) - (1 - G x₁ * conj (G x₂)) * D.K₀ x₁ x₂) -
      ((1 - S x₂ * conj (S x₁) - (1 - G x₂ * conj (G x₁)) * D.K₀ x₂ x₁) -
        (1 - S x₂ * conj (S x₂) - (1 - G x₂ * conj (G x₂)) * D.K₀ x₂ x₂))).re =
      -‖S x₁ - S x₂‖ ^ 2 -
        (form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) 1 (-1) -
          form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) (G x₁) (-G x₂)).re := by
    have hR : (-‖S x₁ - S x₂‖ ^ 2 : ℝ) =
        ((1 - S x₁ * conj (S x₁)) - (1 - S x₁ * conj (S x₂)) -
          ((1 - S x₂ * conj (S x₁)) - (1 - S x₂ * conj (S x₂)))).re := by
      rw [← hc, Complex.ofReal_re]
    rw [hR, ← form2_test, ← Complex.sub_re]
    congr 1
    ring
  rwa [hval] at hcomb

/-- The two-point inequality with all primes. -/
theorem two_point_inequality_all (D : AglerDecompositionAll S G) (hG : ∀ x, ‖G x‖ < 1)
    (x₁ x₂ : Plane σ₀) (hsum : Summable fun p : Nat.Primes =>
      ‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 /
        ((1 - ‖allPrimeCoord p x₁‖ ^ 2) * (1 - ‖allPrimeCoord p x₂‖ ^ 2)))
    {α : ℝ} (hα : α ≠ 0) :
    ‖S x₁ - S x₂‖ ^ 2 ≤
      ∑' p : Nat.Primes, ‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 /
        ((1 - ‖allPrimeCoord p x₁‖ ^ 2) * (1 - ‖allPrimeCoord p x₂‖ ^ 2)) +
      (1 + α ^ 2) * (‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2)) +
      (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2)) := by
  have hden : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  have hprime : ∀ p : Nat.Primes,
      -(‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 /
        ((1 - ‖allPrimeCoord p x₁‖ ^ 2) * (1 - ‖allPrimeCoord p x₂‖ ^ 2))) ≤
      (form2 (D.K p x₁ x₁) (D.K p x₁ x₂) (D.K p x₂ x₁) (D.K p x₂ x₂) 1 (-1) -
        form2 (D.K p x₁ x₁) (D.K p x₁ x₂) (D.K p x₂ x₁) (D.K p x₂ x₂)
          (allPrimeCoord p x₁) (-allPrimeCoord p x₂)).re := by
    intro p
    refine le_trans ?_ (prime_term_lower (D.psd p x₁ x₂) (norm_allPrimeCoord_lt p x₁))
    have hd1 := hden _ (norm_allPrimeCoord_lt p x₁)
    have hd2 := hden _ (norm_allPrimeCoord_lt p x₂)
    have hDle := D.coord_le p hG x₂
    have hnn : 0 ≤ ‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 := by positivity
    rw [neg_le_neg_iff, div_le_div_iff₀ hd1 (mul_pos hd1 hd2)]
    have h3 : ‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 * (D.K p x₂ x₂).re *
        (1 - ‖allPrimeCoord p x₂‖ ^ 2) ≤ ‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 := by
      nlinarith
    nlinarith
  have htest := D.hasSum_test x₁ x₂
  have hS : -∑' p : Nat.Primes, ‖allPrimeCoord p x₁ - allPrimeCoord p x₂‖ ^ 2 /
      ((1 - ‖allPrimeCoord p x₁‖ ^ 2) * (1 - ‖allPrimeCoord p x₂‖ ^ 2)) ≤
      -‖S x₁ - S x₂‖ ^ 2 -
        (form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) 1 (-1) -
          form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) (G x₁) (-G x₂)).re := by
    rw [← tsum_neg]
    exact hasSum_le hprime hsum.neg.hasSum htest
  have harch : -((1 + α ^ 2) * (‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2)) +
      (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2))) ≤
      (form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) 1 (-1) -
        form2 (D.K₀ x₁ x₁) (D.K₀ x₁ x₂) (D.K₀ x₂ x₁) (D.K₀ x₂ x₂) (G x₁) (-G x₂)).re := by
    have hd1 := hden _ (hG x₁)
    have hd2 := hden _ (hG x₂)
    have hY := re_form2_add_le (D.psd₀ x₁ x₂) (G x₁) 0 0 (-G x₂) hα
    simp only [add_zero, zero_add] at hY
    rw [re_form2_zero_right, re_form2_zero_left, norm_neg] at hY
    have hA : (D.K₀ x₁ x₁).re ≤ (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2) := by
      rw [le_div_iff₀ hd1]
      have := D.arch_le x₁
      linarith
    have hB : (D.K₀ x₂ x₂).re ≤ 1 / (1 - ‖G x₂‖ ^ 2) := by
      rw [le_div_iff₀ hd2]
      have := D.arch_le x₂
      nlinarith [sq_nonneg ‖S x₂‖]
    have h1 : ‖G x₁‖ ^ 2 * (D.K₀ x₁ x₁).re ≤ ‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hA (by positivity)
    have h2 : ‖G x₂‖ ^ 2 * (D.K₀ x₂ x₂).re ≤ ‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hB (sq_nonneg ‖G x₂‖)
      rwa [mul_one_div] at this
    have h3 := D.psd₀ x₁ x₂ 1 (-1)
    rw [Complex.sub_re]
    have h4 : (1 + α ^ 2) * (‖G x₁‖ ^ 2 * (D.K₀ x₁ x₁).re) ≤
        (1 + α ^ 2) * (‖G x₁‖ ^ 2 * (1 - ‖S x₁‖ ^ 2) / (1 - ‖G x₁‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 * (D.K₀ x₂ x₂).re) ≤
        (1 + (α⁻¹) ^ 2) * (‖G x₂‖ ^ 2 / (1 - ‖G x₂‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  linarith

/-- The return error of a prime is at most `16 p^{−2σ}`, uniformly along vertical translates. -/
theorem return_error_le (p : Nat.Primes) (s : Plane σ₀) (τ : ℝ) :
    ‖allPrimeCoord p s - allPrimeCoord p (vshift' s τ)‖ ^ 2 /
        ((1 - ‖allPrimeCoord p s‖ ^ 2) * (1 - ‖allPrimeCoord p (vshift' s τ)‖ ^ 2)) ≤
      16 * ‖allPrimeCoord p s‖ ^ 2 := by
  rw [norm_allPrimeCoord_vshift]
  have h1 := norm_allPrimeCoord_sq_le p s
  have hd : 1 / 2 ≤ 1 - ‖allPrimeCoord p s‖ ^ 2 := by linarith
  have hdd : 1 / 4 ≤ (1 - ‖allPrimeCoord p s‖ ^ 2) * (1 - ‖allPrimeCoord p s‖ ^ 2) := by nlinarith
  have hnum : ‖allPrimeCoord p s - allPrimeCoord p (vshift' s τ)‖ ^ 2 ≤ 4 * ‖allPrimeCoord p s‖ ^ 2 := by
    have h2 := norm_sub_le (allPrimeCoord p s) (allPrimeCoord p (vshift' s τ))
    rw [norm_allPrimeCoord_vshift] at h2
    have h3 : ‖allPrimeCoord p s - allPrimeCoord p (vshift' s τ)‖ ≤ 2 * ‖allPrimeCoord p s‖ := by
      linarith
    have := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg ‖allPrimeCoord p s‖]

omit [Fact ((1 : ℝ) / 2 ≤ σ₀)] in
/-- A prime coordinate along a vertical translate. -/
theorem allPrimeCoord_vshift (p : Nat.Primes) (s : Plane σ₀) (τ : ℝ) :
    allPrimeCoord p (vshift' s τ) =
      allPrimeCoord p s * cexp (-(((τ * Real.log (p : ℕ) : ℝ) : ℂ) * I)) := by
  unfold allPrimeCoord vshift'
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [neg_add, Complex.cpow_add _ _ hp0]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **The Agler wall with all primes.** -/
theorem agler_wall_all_primes (D : AglerDecompositionAll S G) (hG : ∀ x, ‖G x‖ < 1)
    (hGv : ∀ s, Tendsto (fun τ => G (vshift' s τ)) atTop (𝓝 0))
    (hSv : ∀ s, Tendsto (fun τ => S (vshift' s τ)) atTop (𝓝 0)) (s : Plane σ₀) :
    ‖S s‖ ≤ ‖G s‖ := by
  obtain ⟨τ, hτ, hret⟩ := exists_returns_all
  have hden : ∀ w : ℂ, ‖w‖ < 1 → 0 < 1 - ‖w‖ ^ 2 := fun w hw => by nlinarith [norm_nonneg w]
  have hS0 := (hSv s).comp hτ
  have hG0 := (hGv s).comp hτ
  set W := ‖G s‖ ^ 2 * (1 - ‖S s‖ ^ 2) / (1 - ‖G s‖ ^ 2) with hW
  have hdom : Summable fun p : Nat.Primes => 16 * ‖allPrimeCoord p s‖ ^ 2 :=
    (summable_norm_allPrimeCoord_sq s).mul_left 16
  have hstep : ∀ α : ℝ, α ≠ 0 → ‖S s‖ ^ 2 ≤ (1 + α ^ 2) * W := by
    intro α hα
    have hL : Tendsto (fun j => ‖S s - S (vshift' s (τ j))‖ ^ 2) atTop (𝓝 (‖S s‖ ^ 2)) := by
      have := ((tendsto_const_nhds (x := S s)).sub hS0).norm.pow 2
      simpa using this
    have hP : Tendsto (fun j => ∑' p : Nat.Primes,
        ‖allPrimeCoord p s - allPrimeCoord p (vshift' s (τ j))‖ ^ 2 /
          ((1 - ‖allPrimeCoord p s‖ ^ 2) * (1 - ‖allPrimeCoord p (vshift' s (τ j))‖ ^ 2)))
        atTop (𝓝 0) := by
      have hzero : (0 : ℝ) = ∑' _p : Nat.Primes, (0 : ℝ) := by simp
      rw [hzero]
      refine tendsto_tsum_of_dominated_convergence hdom (fun p => ?_) (Eventually.of_forall fun j p => ?_)
      · -- Each prime returns.
        have hmod : ∀ j, ‖allPrimeCoord p (vshift' s (τ j))‖ = ‖allPrimeCoord p s‖ := fun j =>
          norm_allPrimeCoord_vshift p s (τ j)
        simp_rw [hmod]
        have hc : Tendsto (fun j => allPrimeCoord p (vshift' s (τ j))) atTop (𝓝 (allPrimeCoord p s)) := by
          have := (hret p).const_mul (allPrimeCoord p s)
          rw [mul_one] at this
          exact this.congr fun j => (allPrimeCoord_vshift p s (τ j)).symm
        have h1 : Tendsto (fun j => ‖allPrimeCoord p s - allPrimeCoord p (vshift' s (τ j))‖ ^ 2) atTop (𝓝 0) := by
          have := ((tendsto_const_nhds (x := allPrimeCoord p s)).sub hc).norm.pow 2
          simpa using this
        have h2 := h1.div_const ((1 - ‖allPrimeCoord p s‖ ^ 2) * (1 - ‖allPrimeCoord p s‖ ^ 2))
        rwa [zero_div] at h2
      · rw [Real.norm_of_nonneg]
        · exact return_error_le p s (τ j)
        · refine div_nonneg (by positivity) (mul_nonneg ?_ ?_)
          · exact (hden _ (norm_allPrimeCoord_lt p s)).le
          · exact (hden _ (norm_allPrimeCoord_lt p _)).le
    have hA : Tendsto (fun j => (1 + (α⁻¹) ^ 2) *
        (‖G (vshift' s (τ j))‖ ^ 2 / (1 - ‖G (vshift' s (τ j))‖ ^ 2))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => ‖G (vshift' s (τ j))‖ ^ 2) atTop (𝓝 0) := by
        have := hG0.norm.pow 2
        simpa using this
      have h2 : Tendsto (fun j => 1 - ‖G (vshift' s (τ j))‖ ^ 2) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub h1
      have h3 := (h1.div h2 (by norm_num)).const_mul (1 + (α⁻¹) ^ 2)
      simpa using h3
    have hR := (hP.add (tendsto_const_nhds (x := (1 + α ^ 2) * W))).add hA
    have hle := le_of_tendsto_of_tendsto' hL hR fun j =>
      two_point_inequality_all D hG s (vshift' s (τ j))
        (Summable.of_nonneg_of_le (fun p => div_nonneg (by positivity)
          (mul_nonneg (hden _ (norm_allPrimeCoord_lt p s)).le (hden _ (norm_allPrimeCoord_lt p _)).le))
          (fun p => return_error_le p s (τ j)) hdom) hα
    simpa using hle
  have hW0 : ‖S s‖ ^ 2 ≤ W := by
    have hlim : Tendsto (fun n : ℕ => (1 + (1 / ((n : ℝ) + 1)) ^ 2) * W) atTop (𝓝 ((1 + 0 ^ 2) * W)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact ((tendsto_const_nhds.add (this.pow 2))).mul_const W
    have hle : ‖S s‖ ^ 2 ≤ (1 + 0 ^ 2) * W :=
      ge_of_tendsto' hlim fun n => hstep _ (by positivity)
    simpa using hle
  have hd := hden _ (hG s)
  rw [hW, le_div_iff₀ hd] at hW0
  have hsq : ‖S s‖ ^ 2 ≤ ‖G s‖ ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hsq (norm_nonneg _) |>.2

/-- `S` is always paid by the coordinate `G = S` itself, with no prime conductance. -/
def selfDecomposition (S : Plane σ₀ → ℂ) : AglerDecompositionAll S S where
  K := fun _ _ _ => 0
  K₀ := fun _ _ => 1
  psd := fun _ x y u v => by simp [form2]
  psd₀ := by
    have h := twoPositive_rankOne (fun _ : Plane σ₀ => (1 : ℂ))
    simpa using h
  hasSum := fun x y => by
    simp [hasSum_zero]

/-- The Euler factor `ζ(2s − 1)/ζ(2s)` of the Eisenstein scattering function. -/
def eulerFactor (s : Plane σ₀) : ℂ := riemannZeta (2 * s.1 - 1) / riemannZeta (2 * s.1)

/-- The point `s = 3`. -/
def pointThree (hσ : σ₀ < 3) : Plane σ₀ := ⟨3, by simpa using hσ⟩

omit [Fact ((1 : ℝ) / 2 ≤ σ₀)] in
/-- The Euler factor at `s = 3` exceeds `1`: `ζ(5) > ζ(6)`. -/
theorem one_lt_norm_eulerFactor (hσ : σ₀ < 3) : 1 < ‖eulerFactor (pointThree hσ)‖ := by
  have hval : ∀ k : ℕ, 1 < k → riemannZeta (k : ℂ) = ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) := by
    intro k hk
    rw [zeta_nat_eq_tsum_of_gt_one hk, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    push_cast
    rfl
  have h5 := hval 5 (by norm_num)
  have h6 := hval 6 (by norm_num)
  have e : eulerFactor (pointThree hσ) = riemannZeta ((5 : ℕ) : ℂ) / riemannZeta ((6 : ℕ) : ℂ) := by
    unfold eulerFactor pointThree
    norm_num
  have hs5 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 5 := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs6 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 6 := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hle : ∀ n : ℕ, 1 / (n : ℝ) ^ 6 ≤ 1 / (n : ℝ) ^ 5 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 (by norm_num))
  have hlt : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ 6 < 1 / ((2 : ℕ) : ℝ) ^ 5 := by norm_num
  have hAB := hs6.tsum_lt_tsum hle hlt hs5
  have hB : 0 < ∑' n : ℕ, 1 / (n : ℝ) ^ 6 :=
    hs6.tsum_pos (fun n => by positivity) 2 (by norm_num)
  rw [e, h5, h6, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (hB.le.trans hAB.le) hB.le), one_lt_div hB]
  exact hAB

/-- **The Euler factor cannot be paid prime by prime.** If `G` is a coordinate, nonzero at `s = 3`, and `S = G·E` decays vertically, there is no decomposition in the prime coordinates and `G`. -/
theorem no_decomposition_euler (hσ : σ₀ < 3) (hG : ∀ x, ‖G x‖ < 1)
    (hGv : ∀ s, Tendsto (fun τ => G (vshift' s τ)) atTop (𝓝 0))
    (hSv : ∀ s, Tendsto (fun τ => G (vshift' s τ) * eulerFactor (vshift' s τ)) atTop (𝓝 0))
    (h3 : G (pointThree hσ) ≠ 0) :
    IsEmpty (AglerDecompositionAll (fun s => G s * eulerFactor s) G) := by
  refine ⟨fun D => ?_⟩
  have h := agler_wall_all_primes D hG hGv hSv (pointThree hσ)
  rw [norm_mul] at h
  have hpos : 0 < ‖G (pointThree hσ)‖ := norm_pos_iff.mpr h3
  have hE := one_lt_norm_eulerFactor hσ
  nlinarith

instance : Fact ((1 : ℝ) / 2 ≤ 2) := ⟨by norm_num⟩

/-- The Gamma-like coordinate of the second test. -/
def eulerTestG (s : Plane 2) : ℂ := 1 / (s.1 + 3)

/-- The function of the second test: the Euler factor over the coordinate. -/
def eulerTestS (s : Plane 2) : ℂ := eulerTestG s * eulerFactor s

theorem norm_eulerFactor_le (s : Plane 2) : ‖eulerFactor s‖ ≤ 2 := by
  have hs : (2 : ℝ) < s.1.re := s.2
  have h1 : ‖riemannZeta (2 * s.1 - 1)‖ ≤ 1 + 1 / ((3 : ℝ) - 1) :=
    RHTower.norm_riemannZeta_le_of_le_re (by norm_num) (by simp; linarith)
  have h2 : ‖(riemannZeta (2 * s.1))⁻¹‖ ≤ 1 + 1 / ((4 : ℝ) - 1) :=
    RHTower.norm_inv_riemannZeta_le_of_le_re (by norm_num) (by simp; linarith)
  unfold eulerFactor
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (1 + 1 / ((3 : ℝ) - 1)) * (1 + 1 / ((4 : ℝ) - 1)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

theorem norm_eulerTestG_lt (s : Plane 2) : ‖eulerTestG s‖ < 1 / 5 := by
  have hs : (2 : ℝ) < s.1.re := s.2
  have hre : 5 < ‖s.1 + 3‖ := by
    have := Complex.re_le_norm (s.1 + 3)
    simp only [Complex.add_re, Complex.re_ofNat] at this
    linarith
  unfold eulerTestG
  rw [norm_div, norm_one]
  exact one_div_lt_one_div_of_lt (by norm_num) hre

theorem tendsto_eulerTestG (s : Plane 2) :
    Tendsto (fun τ => eulerTestG (vshift' s τ)) atTop (𝓝 0) :=
  tendsto_firstTestG ⟨s.1, by have := s.2; linarith⟩

/-- **The second test.** `E(s)/(s + 3)` is Schur on `Re s > 2` and decays vertically, yet it has no decomposition in all the prime coordinates and `1/(s + 3)`. -/
theorem euler_test :
    (∀ s, ‖eulerTestS s‖ < 1) ∧ (∀ s, Tendsto (fun τ => eulerTestS (vshift' s τ)) atTop (𝓝 0)) ∧
      IsEmpty (AglerDecompositionAll eulerTestS eulerTestG) := by
  have hS : ∀ s, ‖eulerTestS s‖ ≤ 2 * ‖eulerTestG s‖ := fun s => by
    unfold eulerTestS
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_eulerFactor_le s) (norm_nonneg _)
  have hG : ∀ s, ‖eulerTestG s‖ < 1 := fun s => (norm_eulerTestG_lt s).trans (by norm_num)
  have hSv : ∀ s, Tendsto (fun τ => eulerTestS (vshift' s τ)) atTop (𝓝 0) := fun s => by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := ((tendsto_eulerTestG s).norm.const_mul 2)
    simp only [norm_zero, mul_zero] at h
    exact squeeze_zero (fun _ => norm_nonneg _) (fun τ => hS _) h
  refine ⟨fun s => ?_, hSv, ?_⟩
  · have := hS s
    have := norm_eulerTestG_lt s
    linarith
  · refine no_decomposition_euler (by norm_num) hG tendsto_eulerTestG hSv ?_
    unfold eulerTestG pointThree
    norm_num

end

end GaloisForLFunctions.PrimeTorusTheory
