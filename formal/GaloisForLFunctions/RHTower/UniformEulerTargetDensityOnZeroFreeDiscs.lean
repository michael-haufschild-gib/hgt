import GaloisForLFunctions.RHTower.FiniteEulerProductUniversalityOnDiscs
import GaloisForLFunctions.RHTower.PrimeTorusPhaseSecondMomentAndBlockIndependence

/-!
# Euler-target return heights: lower density bounded below uniformly in the cutoff

Universality of the finite Euler products `E_y` on a zero-free disc gives, for each cutoff `y`,
heights of positive lower density at which `E_y(· + iτ)` approximates `ζ` on the disc.  Here the
density constant is made independent of `y` for all large `y`.

The mechanism is the product structure of Haar measure on the prime torus.  Fix a base cutoff
`y₁` and the open set `A` of phases of the primes `p ≤ y₁` at which `E_{y₁}` is within `ε/2` of
`ζ`.  For `y ≥ y₁`,
`E_y(ω, z) = E_{y₁}(ω, z) · exp(Σ_{y₁<p≤y} ω_p p^{−z} + remainders)`,
and the linear prime sum is a random sum in the Hardy space of the disc whose Haar second moment
is `Σ ‖u_p‖²`, small for `y₁` large.  Chebyshev gives Haar measure at least `1/2` to the event
`B_y` that this sum is small; `B_y` depends only on the primes in `(y₁, y]`, so it is independent of
`A`, and `A ∩ B_y` lies in the target phases at stage `y`.  Hence the target phases at stage `y`
have Haar measure at least `Haar(A)/2`, uniformly in `y`, and the Kronecker–Weyl law transfers
this to the lower density of the return heights
(`exists_uniform_pos_density_eulerTargetReturnSet_zeta`).
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-! ## Prime blocks -/

theorem primesLE_subset_primesLE_of_le {y₁ y : ℕ} (h : y₁ ≤ y) : primesLE y₁ ⊆ primesLE y := by
  intro p hp
  rw [mem_primesLE] at hp ⊢
  exact hp.trans h

/-- A nonnegative sum over the primes in `(y₁, y]` is at most the sum over all integers in
`(y₁, y]`. -/
theorem sum_primesLE_sdiff_le_sum_Ico {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (y₁ y : ℕ) :
    ∑ p ∈ primesLE y \ primesLE y₁, F p ≤ ∑ n ∈ Finset.Ico (y₁ + 1) (y + 1), F n := by
  have hmap := Finset.sum_map (primesLE y \ primesLE y₁) ⟨Subtype.val, Subtype.val_injective⟩ F
  simp only [Function.Embedding.coeFn_mk] at hmap
  rw [← hmap]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hF n
  intro n hn
  rw [Finset.mem_map] at hn
  obtain ⟨p, hp, hpn⟩ := hn
  simp only [Function.Embedding.coeFn_mk] at hpn
  subst hpn
  rw [Finset.mem_sdiff, mem_primesLE, mem_primesLE] at hp
  rw [Finset.mem_Ico]
  omega

/-- The phased Euler product at stage `y` is the product at stage `y₁ ≤ y` times the block of the
primes in `(y₁, y]`. -/
theorem eulerPhaseProduct_eq_mul_block {y₁ y : ℕ} (h : y₁ ≤ y) (ω : Nat.Primes → Circle) (z : ℂ) :
    eulerPhaseProduct y ω z = eulerPhaseProduct y₁ ω z *
      ∏ p ∈ primesLE y \ primesLE y₁, (1 - (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z))⁻¹ := by
  unfold eulerPhaseProduct
  exact (Finset.prod_sdiff (primesLE_subset_primesLE_of_le h)).symm.trans (mul_comm _ _)

theorem prod_inv_one_sub_eq_exp_sum_of_ne_zero {ι : Type*} {S : Finset ι} {w : ι → ℂ}
    (hw : ∀ i ∈ S, 1 - w i ≠ 0) :
    ∏ i ∈ S, (1 - w i)⁻¹ = Complex.exp (∑ i ∈ S, -Complex.log (1 - w i)) := by
  rw [Complex.exp_sum]
  refine prod_congr rfl fun i hi => ?_
  rw [Complex.exp_neg, Complex.exp_log (hw i hi)]

/-- A block of Euler factors is the exponential of the linear prime sum plus the remainders. -/
theorem eulerBlock_eq_exp (B : Finset Nat.Primes) (ω : Nat.Primes → Circle) {z : ℂ}
    (hz : 0 < z.re) :
    ∏ p ∈ B, (1 - (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z))⁻¹
      = Complex.exp (∑ p ∈ B, (ω p : ℂ) * ((p : ℕ) : ℂ) ^ (-z)
          + ∑ p ∈ B, eulerLogRemainder (ω p : ℂ) z (p : ℕ)) := by
  rw [prod_inv_one_sub_eq_exp_sum_of_ne_zero fun p _ => one_sub_phase_cpow_ne_zero p (ω p) hz,
    ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  unfold eulerLogRemainder
  ring

theorem eulerRemainderConstant_nonneg {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 :=
  div_nonneg (inv_nonneg.mpr (by linarith [two_rpow_neg_lt_one hσ])) two_pos.le

/-- The remainders of a block are bounded by the `p^{−2σ}` tail. -/
theorem norm_sum_eulerLogRemainder_block_le (B : Finset Nat.Primes) (ω : Nat.Primes → Circle)
    {z : ℂ} {σ : ℝ} (hσ : 0 < σ) (hz : σ ≤ z.re) :
    ‖∑ p ∈ B, eulerLogRemainder (ω p : ℂ) z (p : ℕ)‖
      ≤ ∑ p ∈ B, (1 - (2 : ℝ) ^ (-σ))⁻¹ / 2 * ((p : ℕ) : ℝ) ^ (-(2 * σ)) :=
  (norm_sum_le _ _).trans (sum_le_sum fun p _ =>
    norm_eulerLogRemainder_le (Circle.norm_coe _) p.2.two_le hσ hz)

/-! ## The linear prime sum in the Hardy space -/

/-- The Hardy-space prime vectors `u_p = (q ↦ p^{−(z₀+ρq)})`, indexed by the primes. -/
def primeVectorOf (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (p : Nat.Primes) : HardyDisk :=
  primeVector z₀ hρ p.2.pos

theorem norm_primeVectorOf_sq_le (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (p : Nat.Primes) :
    ‖primeVectorOf z₀ hρ p‖ ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-(2 * (z₀.re - ρ))) := by
  have h := norm_primeVector_sq_le z₀ hρ p.2.pos
  rw [show 2 * ρ - 2 * z₀.re = -(2 * (z₀.re - ρ)) by ring] at h
  exact h

/-- Evaluation is linear: the random prime sum evaluates to `Σ_p ω_p p^{−(z₀+ρq)}`. -/
theorem hardyFun_torusPrimePhaseSum (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (B : Finset Nat.Primes)
    (x : UnitAddTorus Nat.Primes) {q : ℂ} (hq : ‖q‖ < 1) :
    hardyFun (torusPrimePhaseSum B (primeVectorOf z₀ hρ) x) q
      = ∑ p ∈ B, torusPrimePhase p x * ((p : ℕ) : ℂ) ^ (-(z₀ + ρ * q)) := by
  rw [← GaloisForLFunctions.HTGeometry.inner_hardyKernel hq, torusPrimePhaseSum, inner_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [inner_smul_right, GaloisForLFunctions.HTGeometry.inner_hardyKernel hq, primeVectorOf,
    hardyFun_primeVector]

/-- Sup bound on the disc of radius `r₁ < 1` by the Hardy norm of the random sum. -/
theorem norm_sum_torusPhase_cpow_le (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (B : Finset Nat.Primes)
    (x : UnitAddTorus Nat.Primes) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {q : ℂ}
    (hq : ‖q‖ ≤ r₁) :
    ‖∑ p ∈ B, torusPrimePhase p x * ((p : ℕ) : ℂ) ^ (-(z₀ + ρ * q))‖
      ≤ Real.sqrt ((1 - r₁ ^ 2)⁻¹) * ‖torusPrimePhaseSum B (primeVectorOf z₀ hρ) x‖ := by
  rw [← hardyFun_torusPrimePhaseSum z₀ hρ B x (lt_of_le_of_lt hq hr₁)]
  exact norm_hardyFun_le_of_norm_le _ hr₁0 hr₁ hq

/-! ## Stability of the target under the added primes -/

/-- **Stability.**  On the disc `|z − z₀| ≤ ρ r₁`, if the base product `E_{y₁}(ω, ·)` is within
`ε/2` of `g`, `‖g‖ ≤ M`, the random linear sum of the primes in `(y₁, y]` has Hardy norm `< δ`,
the remainder tail is `≤ δ`, `(K₁ + 1) δ ≤ 1` and `2 (M + ε/2) (K₁ + 1) δ ≤ ε/4` with
`K₁ = (1 − r₁²)^{−1/2}`, then `E_y(ω, ·)` is within `ε` of `g` on the disc. -/
theorem norm_eulerPhaseProduct_sub_lt_of_block (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ₁ : 0 < z₀.re - ρ) {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {y₁ y : ℕ} (hy : y₁ ≤ y)
    (x : UnitAddTorus Nat.Primes) {g : ℂ → ℂ} {ε M δ : ℝ}
    (hM : ∀ z ∈ closedBall z₀ (ρ * r₁), ‖g z‖ ≤ M)
    (hbase : ∀ z ∈ closedBall z₀ (ρ * r₁),
      ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z - g z‖ < ε / 2)
    (hsum : ‖torusPrimePhaseSum (primesLE y \ primesLE y₁) (primeVectorOf z₀ hρ.le) x‖ < δ)
    (hrem : ∑ n ∈ Finset.Ico (y₁ + 1) (y + 1),
      (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 * (n : ℝ) ^ (-(2 * (z₀.re - ρ))) ≤ δ)
    (hδ1 : (Real.sqrt ((1 - r₁ ^ 2)⁻¹) + 1) * δ ≤ 1)
    (hδ2 : 2 * (M + ε / 2) * ((Real.sqrt ((1 - r₁ ^ 2)⁻¹) + 1) * δ) ≤ ε / 4)
    (hε : 0 < ε) :
    ∀ z ∈ closedBall z₀ (ρ * r₁),
      ‖eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) z - g z‖ < ε := by
  intro z hz
  set B := primesLE y \ primesLE y₁ with hB
  set K₁ := Real.sqrt ((1 - r₁ ^ 2)⁻¹) with hK₁
  have hK₁0 : 0 ≤ K₁ := Real.sqrt_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hsum.le
  -- the point of the disc in the disc coordinate
  have hzre : z₀.re - ρ ≤ z.re := by
    have h1 := re_ge_of_mem_closedBall_center hz
    have h2 : ρ * r₁ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hr₁.le hρ.le
    linarith
  have hzpos : 0 < z.re := by linarith
  have hq : ‖(z - z₀) / ρ‖ ≤ r₁ := by
    have hzn : ‖z - z₀‖ ≤ ρ * r₁ := by rwa [mem_closedBall, dist_eq_norm] at hz
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_le_iff₀ hρ]
    linarith
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hz' : z₀ + ρ * ((z - z₀) / ρ) = z := by
    rw [mul_div_cancel₀ _ hρ']
    ring
  -- the block exponent and its bound
  set S : ℂ := ∑ p ∈ B, ((unitTorusHomeomorphCircles Nat.Primes x p : Circle) : ℂ)
      * ((p : ℕ) : ℂ) ^ (-z)
    + ∑ p ∈ B, eulerLogRemainder ((unitTorusHomeomorphCircles Nat.Primes x p : Circle) : ℂ) z (p : ℕ)
    with hS
  have hlin : ‖∑ p ∈ B, ((unitTorusHomeomorphCircles Nat.Primes x p : Circle) : ℂ)
      * ((p : ℕ) : ℂ) ^ (-z)‖ ≤ K₁ * δ := by
    have h := norm_sum_torusPhase_cpow_le z₀ hρ.le B x hr₁0 hr₁ hq
    rw [hz'] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsum.le hK₁0)
  have hremB : ‖∑ p ∈ B, eulerLogRemainder
      ((unitTorusHomeomorphCircles Nat.Primes x p : Circle) : ℂ) z (p : ℕ)‖ ≤ δ := by
    refine (norm_sum_eulerLogRemainder_block_le B _ hσ₁ hzre).trans ?_
    exact (sum_primesLE_sdiff_le_sum_Ico
      (F := fun n : ℕ => (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 * (n : ℝ) ^ (-(2 * (z₀.re - ρ))))
      (fun n => mul_nonneg (eulerRemainderConstant_nonneg hσ₁) (by positivity)) y₁ y).trans hrem
  have hSle : ‖S‖ ≤ (K₁ + 1) * δ := by
    rw [hS]
    calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
      _ ≤ K₁ * δ + δ := add_le_add hlin hremB
      _ = (K₁ + 1) * δ := by ring
  -- the factorisation through the base stage
  have hfac : eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) z
      = eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z * Complex.exp S := by
    rw [eulerPhaseProduct_eq_mul_block hy, eulerBlock_eq_exp B _ hzpos]
  have hbasez := hbase z hz
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z hz)
  have hEbound : ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z‖
      ≤ M + ε / 2 := by
    calc ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z‖
        = ‖(eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z - g z) + g z‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z - g z‖ + ‖g z‖ :=
          norm_add_le _ _
      _ ≤ ε / 2 + M := add_le_add hbasez.le (hM z hz)
      _ = M + ε / 2 := by ring
  have hexp : ‖Complex.exp S - 1‖ ≤ 2 * ((K₁ + 1) * δ) :=
    (Complex.norm_exp_sub_one_le (hSle.trans hδ1)).trans (by gcongr)
  calc ‖eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) z - g z‖
      = ‖(eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z - g z)
          + eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z
            * (Complex.exp S - 1)‖ := by
        congr 1
        rw [hfac]
        ring
    _ ≤ ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z - g z‖
          + ‖eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z‖
            * ‖Complex.exp S - 1‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
    _ ≤ ε / 2 + (M + ε / 2) * (2 * ((K₁ + 1) * δ)) :=
        add_le_add hbasez.le (mul_le_mul hEbound hexp (norm_nonneg _) (by linarith))
    _ = ε / 2 + 2 * (M + ε / 2) * ((K₁ + 1) * δ) := by ring
    _ ≤ ε / 2 + ε / 4 := by linarith
    _ < ε := by linarith

/-! ## Uniform lower density of the Euler-target heights -/

/-- **Positive lower density of the Euler-target heights, uniformly in the cutoff.**  On the disc
`|z − z₀| ≤ ρ r₁` inside a zero-free disc `|z − z₀| < ρ R₂`, `R₂ > 1`, lying in `Re z < 1`, there
are `c > 0` and `y₁` such that for every `y ≥ y₁` the heights at which `E_y(· + iτ)` is within `ε`
of `ζ` on the disc have lower density at least `c`. -/
theorem exists_uniform_pos_density_eulerTargetReturnSet_zeta (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hσ : 1 / 2 ≤ z₀.re) (hρσ₁ : 2 * ρ - 2 * z₀.re < -1) (hρσ₂ : 3 * ρ < 1 - z₀.re)
    {R₂ : ℝ} (hR₂ : 1 < R₂) (hR₂1 : z₀.re + ρ * R₂ < 1)
    (hζ : ∀ z ∈ ball z₀ (ρ * R₂), riemannZeta z ≠ 0)
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∃ y₁ : ℕ, ∀ y, y₁ ≤ y → ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (eulerTargetReturnSet y riemannZeta (closedBall z₀ (ρ * r₁)) ε ∩ Icc 0 T) := by
  have hK : IsCompact (closedBall z₀ (ρ * r₁)) := isCompact_closedBall _ _
  have hσ₁ : 1 / 2 < z₀.re - ρ := by linarith
  have hre : ∀ z ∈ closedBall z₀ (ρ * r₁), 0 < z.re := fun z hz => by
    have h1 := re_ge_of_mem_closedBall_center hz
    have h2 : ρ * r₁ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hr₁.le hρ.le
    linarith
  have hne1 : ∀ z ∈ closedBall z₀ (ρ * r₁), z ≠ 1 := by
    intro z hz h1
    subst h1
    rw [mem_closedBall, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (1 - z₀)
    rw [Complex.sub_re, Complex.one_re] at h
    have h2 : ρ * r₁ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hr₁.le hρ.le
    linarith [(abs_le.mp h).2]
  have hζc : ContinuousOn riemannZeta (closedBall z₀ (ρ * r₁)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).continuousAt.continuousWithinAt
  -- a bound for `ζ` on the disc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hζc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (mem_closedBall_self (by positivity)))
  -- the constants
  set K₁ : ℝ := Real.sqrt ((1 - r₁ ^ 2)⁻¹) with hK₁
  have hK₁0 : 0 ≤ K₁ := Real.sqrt_nonneg _
  have hK₁1 : 0 < K₁ + 1 := by linarith
  set A₀ : ℝ := M + ε / 2 + 1 with hA₀
  have hA₀pos : 0 < A₀ := by rw [hA₀]; linarith
  have hA₀ne : A₀ ≠ 0 := hA₀pos.ne'
  set δ : ℝ := min ((K₁ + 1)⁻¹) (ε / (8 * A₀ * (K₁ + 1))) with hδ
  have hδpos : 0 < δ := lt_min (inv_pos.mpr hK₁1) (div_pos hε (by positivity))
  have hδ1 : (K₁ + 1) * δ ≤ 1 := by
    calc (K₁ + 1) * δ ≤ (K₁ + 1) * (K₁ + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left (by rw [hδ]; exact min_le_left _ _) hK₁1.le
      _ = 1 := mul_inv_cancel₀ hK₁1.ne'
  have hδ2 : 2 * (M + ε / 2) * ((K₁ + 1) * δ) ≤ ε / 4 := by
    have h1 : (K₁ + 1) * δ ≤ ε / (8 * A₀) := by
      calc (K₁ + 1) * δ ≤ (K₁ + 1) * (ε / (8 * A₀ * (K₁ + 1))) :=
            mul_le_mul_of_nonneg_left (by rw [hδ]; exact min_le_right _ _) hK₁1.le
        _ = ε / (8 * A₀) := by field_simp
    have h2 : M + ε / 2 ≤ A₀ := by rw [hA₀]; linarith
    calc 2 * (M + ε / 2) * ((K₁ + 1) * δ) ≤ 2 * A₀ * (ε / (8 * A₀)) :=
          mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = ε / 4 := by field_simp; ring
  -- the tails
  set C : ℝ := max ((1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2) 1 with hC
  have hC0 : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCrem : (1 - (2 : ℝ) ^ (-(z₀.re - ρ)))⁻¹ / 2 ≤ C := le_max_left _ _
  set δ' : ℝ := min δ (δ ^ 2 / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'le2 : δ' ≤ δ ^ 2 / 2 := min_le_right _ _
  obtain ⟨y₀, -, hy₀⟩ := exists_remainder_tail_le hσ₁ hC0 hδ'pos 0
  -- the base phases, at a stage `y₁ ≥ y₀`
  obtain ⟨y₁, hy₁, c₁, hc₁, hev₁⟩ := exists_pos_density_eulerTargetReturnSet_zeta z₀ hρ hσ hρσ₁
    hρσ₂ hR₂ hR₂1 hζ hr₁0 hr₁ (half_pos hε) y₀
  have hne : (eulerTargetReturnSet y₁ riemannZeta (closedBall z₀ (ρ * r₁)) (ε / 2)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    obtain ⟨T, hT, hTpos⟩ := (hev₁.and (eventually_gt_atTop (0 : ℝ))).exists
    rw [hemp, Set.empty_inter, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hT
    exact absurd hT (not_le.mpr (mul_pos hc₁ hTpos))
  obtain ⟨τ₀, hτ₀⟩ := hne
  -- the base event `A`: phases of the primes `≤ y₁` approximating `ζ` within `ε/2`
  set A : Set (UnitAddTorus Nat.Primes) := unitTorusHomeomorphCircles Nat.Primes ⁻¹'
    eulerPhaseTargetSet y₁ riemannZeta (closedBall z₀ (ρ * r₁)) (ε / 2) with hA
  have hAopen : IsOpen A :=
    (Homeomorph.isOpen_preimage _).mpr (isOpen_eulerPhaseTargetSet y₁ hK hre hζc _)
  have hAne : A.Nonempty := by
    refine ⟨(unitTorusHomeomorphCircles Nat.Primes).symm (circlePhaseFlow primeFrequency τ₀), ?_⟩
    rw [hA, Set.mem_preimage, Homeomorph.apply_symm_apply]
    simp only [eulerPhaseTargetSet, Set.mem_setOf_eq]
    intro z hz
    rw [eulerPhaseProduct_circlePhaseFlow]
    exact hτ₀ z hz
  have hApos : 0 < (torusHaar Nat.Primes A).toReal :=
    ENNReal.toReal_pos (hAopen.measure_pos _ hAne).ne' (measure_ne_top _ _)
  refine ⟨(torusHaar Nat.Primes A).toReal / 4, by positivity, y₁, fun y hy => ?_⟩
  -- the block event `B_y`: the random linear sum of the primes in `(y₁, y]` is small
  set Bl : Finset Nat.Primes := primesLE y \ primesLE y₁ with hBl
  set u : Nat.Primes → HardyDisk := primeVectorOf z₀ hρ.le with hu
  set By : Set (UnitAddTorus Nat.Primes) := {x | ‖torusPrimePhaseSum Bl u x‖ < δ} with hBy
  have hByopen : IsOpen By := isOpen_lt (continuous_torusPrimePhaseSum Bl u).norm continuous_const
  have htail : ∀ N, ∑ n ∈ Finset.Ico (y₁ + 1) N, C * (n : ℝ) ^ (-(2 * (z₀.re - ρ))) ≤ δ' := by
    intro N
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_left (by omega)) fun n _ _ => by positivity) (hy₀ N)
  -- Chebyshev: `Haar(B_y) ≥ 1/2`
  have hsumsq : ∑ p ∈ Bl, ‖u p‖ ^ 2 ≤ δ ^ 2 / 2 := by
    calc ∑ p ∈ Bl, ‖u p‖ ^ 2 ≤ ∑ p ∈ Bl, C * ((p : ℕ) : ℝ) ^ (-(2 * (z₀.re - ρ))) :=
          sum_le_sum fun p _ => (norm_primeVectorOf_sq_le z₀ hρ.le p).trans
            (le_mul_of_one_le_left (by positivity) hC1)
      _ ≤ ∑ n ∈ Finset.Ico (y₁ + 1) (y + 1), C * (n : ℝ) ^ (-(2 * (z₀.re - ρ))) :=
          sum_primesLE_sdiff_le_sum_Ico
            (F := fun n : ℕ => C * (n : ℝ) ^ (-(2 * (z₀.re - ρ)))) (fun n => by positivity) y₁ y
      _ ≤ δ' := htail _
      _ ≤ δ ^ 2 / 2 := hδ'le2
  have hBy_half : ENNReal.ofReal (1 / 2) ≤ torusHaar Nat.Primes By := by
    have hcompl : torusHaar Nat.Primes Byᶜ ≤ ENNReal.ofReal (1 / 2) := by
      have hc : Byᶜ = {x | δ ≤ ‖torusPrimePhaseSum Bl u x‖} := by
        ext x
        simp [hBy, not_lt]
      rw [hc]
      refine (measure_torusPrimePhaseSum_ge_le Bl u hδpos).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h1 : torusHaar Nat.Primes By = 1 - torusHaar Nat.Primes Byᶜ := by
      rw [← prob_compl_eq_one_sub hByopen.measurableSet.compl, compl_compl]
    rw [h1]
    calc ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
          rw [ENNReal.ofReal_div_of_pos (two_pos : (0 : ℝ) < 2), ENNReal.ofReal_one,
            ENNReal.ofReal_ofNat, one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - torusHaar Nat.Primes Byᶜ := tsub_le_tsub_left hcompl 1
  -- `A` and `B_y` are cylinders over disjoint blocks of primes, hence independent
  have hAdet : ∀ x, blockExtendTorus (primesLE y₁) (torusBlockRestrict (primesLE y₁) x) ∈ A
      ↔ x ∈ A := by
    intro x
    have hprod : ∀ z, eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes
        (blockExtendTorus (primesLE y₁) (torusBlockRestrict (primesLE y₁) x))) z
        = eulerPhaseProduct y₁ (unitTorusHomeomorphCircles Nat.Primes x) z := by
      intro z
      unfold eulerPhaseProduct
      refine prod_congr rfl fun p hp => ?_
      rw [unitTorusHomeomorphCircles_apply_congr (blockExtendTorus_torusBlockRestrict_apply _ x hp)]
    simp only [hA, Set.mem_preimage, eulerPhaseTargetSet, Set.mem_setOf_eq, hprod]
  have hBdet : ∀ x, blockExtendTorus Bl (torusBlockRestrict Bl x) ∈ By ↔ x ∈ By := by
    intro x
    simp only [hBy, Set.mem_setOf_eq]
    rw [torusPrimePhaseSum_congr u fun p hp => blockExtendTorus_torusBlockRestrict_apply Bl x hp]
  have hAB : torusHaar Nat.Primes (A ∩ By) = torusHaar Nat.Primes A * torusHaar Nat.Primes By := by
    rw [eq_setOf_torusBlockRestrict_mem_of_determined hAdet,
      eq_setOf_torusBlockRestrict_mem_of_determined hBdet]
    exact torusHaar_inter_eq_mul_of_disjoint_blocks Finset.disjoint_sdiff
      (isOpen_blockExtendTorus_preimage _ hAopen).measurableSet
      (isOpen_blockExtendTorus_preimage _ hByopen).measurableSet
  -- `A ∩ B_y` lies in the target phases at stage `y`
  have hsub : A ∩ By ⊆ unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      eulerPhaseTargetSet y riemannZeta (closedBall z₀ (ρ * r₁)) ε := by
    rintro x ⟨hxA, hxB⟩
    rw [Set.mem_preimage]
    show ∀ z ∈ closedBall z₀ (ρ * r₁),
      ‖eulerPhaseProduct y (unitTorusHomeomorphCircles Nat.Primes x) z - riemannZeta z‖ < ε
    refine norm_eulerPhaseProduct_sub_lt_of_block z₀ hρ (by linarith) hr₁0 hr₁ hy x hM hxA hxB
      ?_ hδ1 hδ2 hε
    refine le_trans ?_ ((htail (y + 1)).trans hδ'le)
    refine sum_le_sum fun n _ => ?_
    exact mul_le_mul_of_nonneg_right hCrem (by positivity)
  -- the target phases at stage `y` have Haar measure at least `Haar(A)/2`
  have hUy : (torusHaar Nat.Primes A).toReal / 4
      < (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          eulerPhaseTargetSet y riemannZeta (closedBall z₀ (ρ * r₁)) ε)).toReal := by
    have h1 : torusHaar Nat.Primes A * ENNReal.ofReal (1 / 2)
        ≤ torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          eulerPhaseTargetSet y riemannZeta (closedBall z₀ (ρ * r₁)) ε) := by
      calc torusHaar Nat.Primes A * ENNReal.ofReal (1 / 2)
          ≤ torusHaar Nat.Primes A * torusHaar Nat.Primes By := by gcongr
        _ = torusHaar Nat.Primes (A ∩ By) := hAB.symm
        _ ≤ _ := measure_mono hsub
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h2
    linarith
  rw [eulerTargetReturnSet_eq_preimage]
  exact eventually_ofReal_mul_le_volume_preimage_primeFlow
    (isOpen_eulerPhaseTargetSet y hK hre hζc ε) hUy

end RHTower
