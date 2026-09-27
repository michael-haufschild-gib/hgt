import GaloisForLFunctions.RHTower.TruncatedRiemannKernelWeilEnergy


/-!
# The near radical of the level-`a` Weil form has dimension `≍ e^{2a}`

**Theorem** (`zeta_weil_near_radical_dimension`, unconditional).  For all large `a` the Hodge-class
tests (`C²`, supported in `[-a,a]`, `f̂(±i/2) = 0`) contain a subspace `V` with
`dim V ≥ e^{2a-2}/20` and `‖W(f,f)‖ ≤ exp(-e^{2a-2}) ∫|f|²` for every `f ∈ V`.

So at least `e^{2a-2}/20` eigenvalues of the level-`a` Weil form lie in `(-∞, exp(-e^{2a-2})]`.
Numerically (Connes–Consani) the count is about `2e^{2a}`, with eigenvectors close to
`E(prolate)`; this module proves the order of magnitude.

Construction: `V` is the kernel of the two polar functionals inside
`{(∑_{i ≤ K} a_i Φ^{(i)}) χ_a}`, `K ≈ e^{2a-2}/10`.  Every `Φ^{(i)}` lies in the exact radical, so
the Weil energy is that of the tail beyond `|u| = a - 1`.  Near the cusp the combination is a weighted
polynomial of degree `≤ K + 2` in `e^{2u}`.  Lagrange extrapolation bounds the tail, and a Remez
inequality bounds the bulk from below (`CuspSeriesBulkTailBounds`).  Their ratio is
`(128e²)^{2k} e^{-3πY₀/2}` up to polynomial factors, with `Y₀ = e^{2a-2}`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- The zero-sum constant `S_Z = ∑_ρ m_ρ/(1 + |γ_ρ|²)`. -/
def zetaInvSqSum : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))

theorem zetaInvSqSum_nonneg : 0 ≤ zetaInvSqSum :=
  tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)

/-- **Energy-to-mass ratio of a truncated radical combination.**  With `Y₀ = e^{2(L-1)} ≥ 40`,
`k = K + 2`, `k + 1 ≤ Y₀/10`:
`‖W(f_a, f_a)‖ ≤ 20 S_Z (1+2Λ)² (K_t²/K_b) ∫|f_a|²`. -/
theorem norm_W_nearRadicalTest_le_ratio {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (hY₀ : 40 ≤ Real.exp (2 * (L - 1))) (hkY : ((K + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10) :
    ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖ ≤
      20 * zetaInvSqSum * (1 + 2 * Λ) ^ 2 *
        ((28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) * Real.exp (2 * (L - 1)) ^ 2 *
            Real.exp (-π * Real.exp (2 * (L - 1)))) ^ 2 /
          (Real.exp (-π * Real.exp (2 * (L - 1)) / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2))))) *
        ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 := by
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hYpos : 0 < Y₀ := Real.exp_pos _
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ 0)
  set Kt := 28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) * Y₀ ^ 2 * Real.exp (-π * Y₀)
    with hKt
  set Kb := Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2))) with hKb
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  have hKb0 : 0 < Kb := by rw [hKb]; positivity
  obtain ⟨z₁, hz₁, h₁⟩ := exists_bulk_max (kernelPoly fun i => (a i).re) hYpos
  obtain ⟨z₂, hz₂, h₂⟩ := exists_bulk_max (kernelPoly fun i => (a i).im) hYpos
  obtain ⟨z₃, hz₃, h₃⟩ := exists_bulk_max (kernelPoly (parityCoeff fun i => (a i).re)) hYpos
  obtain ⟨z₄, hz₄, h₄⟩ := exists_bulk_max (kernelPoly (parityCoeff fun i => (a i).im)) hYpos
  set M₁ := |(kernelPoly fun i => (a i).re).eval z₁|
  set M₂ := |(kernelPoly fun i => (a i).im).eval z₂|
  set M₃ := |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃|
  set M₄ := |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄|
  have hm1 : 0 ≤ M₁ := abs_nonneg _
  have hm2 : 0 ≤ M₂ := abs_nonneg _
  have hm3 : 0 ≤ M₃ := abs_nonneg _
  have hm4 : 0 ≤ M₄ := abs_nonneg _
  have hpt := nearRadicalTail_pointwise_le L a hΛ (by linarith) hkY h₁ h₂ h₃ h₄
  have hE := nearRadicalTail_integrals_le L a hΛ (C := (1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄)) hpt
  have hW := norm_W_nearRadicalTest_le L a hΛ
  rw [← zetaInvSqSum] at hW
  have hbulk := integral_norm_sq_nearRadicalTest_ge L a hY₀ hkY hz₁ hz₂ hz₃ hz₄ h₁ h₂ h₃ h₄
  have hS := zetaInvSqSum_nonneg
  set E := (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
    ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|) with hEdef
  have hE0 : 0 ≤ E := add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)
  have hsq : (M₁ + M₂ + M₃ + M₄) ^ 2 ≤ 4 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2) := by
    nlinarith [sq_nonneg (M₁ - M₂), sq_nonneg (M₁ - M₃), sq_nonneg (M₁ - M₄),
      sq_nonneg (M₂ - M₃), sq_nonneg (M₂ - M₄), sq_nonneg (M₃ - M₄)]
  have hE2 : E ^ 2 ≤ 16 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2) := by
    have h1 : E ^ 2 ≤ (2 * ((1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄))) ^ 2 :=
      pow_le_pow_left₀ hE0 hE 2
    calc E ^ 2 ≤ (2 * ((1 + 2 * Λ) * Kt * (M₁ + M₂ + M₃ + M₄))) ^ 2 := h1
      _ = 4 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (M₁ + M₂ + M₃ + M₄) ^ 2 := by ring
      _ ≤ 4 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (4 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2)) := by gcongr
      _ = _ := by ring
  have hMsq : M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2 ≤ (∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2) / Kb := by
    rw [le_div_iff₀ hKb0]; linarith
  calc ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖
      ≤ (5 / 4) * zetaInvSqSum * E ^ 2 := hW
    _ ≤ (5 / 4) * zetaInvSqSum *
          (16 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * (M₁ ^ 2 + M₂ ^ 2 + M₃ ^ 2 + M₄ ^ 2)) := by gcongr
    _ ≤ (5 / 4) * zetaInvSqSum *
          (16 * (1 + 2 * Λ) ^ 2 * Kt ^ 2 * ((∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2) / Kb)) := by
        gcongr
    _ = 20 * zetaInvSqSum * (1 + 2 * Λ) ^ 2 * (Kt ^ 2 / Kb) *
          ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 := by ring


/-- The constant of the final ratio. -/
def nearRadicalConst (S Λ : ℝ) : ℝ := 20 * S * (1 + 2 * Λ) ^ 2 * 137984

/-- **Super-exponential smallness of the ratio.**  If `k + 1 ≤ Y₀/10`, `Y₀ ≥ 100` and
`Y₀ ≥ log(720 C + 1)` with `C = 20 S (1+2Λ)² · 137984`, then
`20 S (1+2Λ)² K_t²/K_b ≤ e^{-Y₀}`. -/
theorem nearRadical_ratio_le {k : ℕ} {Y₀ S Λ : ℝ} (hS : 0 ≤ S) (hΛ : 0 ≤ Λ)
    (hkY : (k : ℝ) + 1 ≤ Y₀ / 10) (hY100 : 100 ≤ Y₀)
    (hY : Real.log (720 * nearRadicalConst S Λ + 1) ≤ Y₀) :
    20 * S * (1 + 2 * Λ) ^ 2 *
        ((28 * (k : ℝ) * (16 * Real.exp 1) ^ k * Y₀ ^ 2 * Real.exp (-π * Y₀)) ^ 2 /
          (Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * k)))) ≤ Real.exp (-Y₀) := by
  set C := nearRadicalConst S Λ with hC
  have hC0 : 0 ≤ C := by rw [hC, nearRadicalConst]; positivity
  have hYpos : 0 < Y₀ := by linarith
  -- the algebraic form of the ratio
  have hform : (28 * (k : ℝ) * (16 * Real.exp 1) ^ k * Y₀ ^ 2 * Real.exp (-π * Y₀)) ^ 2 /
      (Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * k))) =
      137984 * (k : ℝ) ^ 2 * Y₀ ^ 4 * ((16 * Real.exp 1) * (8 * Real.exp 1)) ^ (2 * k) *
        Real.exp (-(3 * π / 2) * Y₀) := by
    have e1 : Real.exp (-π * Y₀) ^ 2 = Real.exp (-(3 * π / 2) * Y₀) * Real.exp (-π * Y₀ / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have hE := Real.exp_pos (-π * Y₀ / 2)
    have hA : (28 * (k : ℝ) * (16 * Real.exp 1) ^ k * Y₀ ^ 2 * Real.exp (-π * Y₀)) ^ 2 =
        784 * (k : ℝ) ^ 2 * ((16 * Real.exp 1) ^ k) ^ 2 * Y₀ ^ 4 *
          (Real.exp (-(3 * π / 2) * Y₀) * Real.exp (-π * Y₀ / 2)) := by
      rw [← e1]; ring
    have e2 : ((16 * Real.exp 1) * (8 * Real.exp 1)) ^ (2 * k) =
        ((16 * Real.exp 1) ^ k) ^ 2 * (8 * Real.exp 1) ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    rw [div_div_eq_mul_div, div_eq_iff hE.ne', hA, e2]
    ring
  rw [hform]
  have hpow : ((16 * Real.exp 1) * (8 * Real.exp 1)) ^ (2 * k) ≤ Real.exp (14 * k) := by
    rw [show 16 * Real.exp 1 * (8 * Real.exp 1) = 128 * Real.exp 1 ^ 2 by ring,
      show 14 * (k : ℝ) = ((2 * k : ℕ) : ℝ) * 7 by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) exp_one_mul_128_sq_le _
  have hk2 : (k : ℝ) ^ 2 ≤ Y₀ ^ 2 := by
    have : (k : ℝ) ≤ Y₀ := by linarith
    exact pow_le_pow_left₀ (Nat.cast_nonneg k) this 2
  have hexp : Real.exp (14 * k) * Real.exp (-(3 * π / 2) * Y₀) ≤ Real.exp (-(33 / 10) * Y₀) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have hpi := Real.pi_gt_d2
    have h1 : (k : ℝ) ≤ Y₀ / 10 := by linarith
    have h2 : (471 / 100) * Y₀ ≤ (3 * π / 2) * Y₀ :=
      mul_le_mul_of_nonneg_right (by linarith) hYpos.le
    linarith
  have h6 : Y₀ ^ 6 ≤ 720 * Real.exp Y₀ := by
    have := Real.pow_div_factorial_le_exp (x := Y₀) hYpos.le 6
    rw [div_le_iff₀ (by norm_num [Nat.factorial])] at this
    norm_num [Nat.factorial] at this
    linarith
  have hbig : 720 * C ≤ Real.exp ((13 / 10) * Y₀) := by
    have h1 : 720 * C + 1 ≤ Real.exp Y₀ := by
      calc 720 * C + 1 = Real.exp (Real.log (720 * C + 1)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp Y₀ := Real.exp_le_exp.mpr hY
    have h2 : Real.exp Y₀ ≤ Real.exp ((13 / 10) * Y₀) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsplit : Real.exp (-(33 / 10) * Y₀) =
      Real.exp (-((13 / 10) * Y₀)) * Real.exp (-Y₀) * Real.exp (-Y₀) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hE13 : Real.exp ((13 / 10) * Y₀) * Real.exp (-((13 / 10) * Y₀)) = 1 := by
    rw [← Real.exp_add]; simp
  have hEE : Real.exp Y₀ * Real.exp (-Y₀) = 1 := by rw [← Real.exp_add]; simp
  calc 20 * S * (1 + 2 * Λ) ^ 2 * (137984 * (k : ℝ) ^ 2 * Y₀ ^ 4 *
        ((16 * Real.exp 1) * (8 * Real.exp 1)) ^ (2 * k) * Real.exp (-(3 * π / 2) * Y₀))
      = C * ((k : ℝ) ^ 2 * Y₀ ^ 4 * (((16 * Real.exp 1) * (8 * Real.exp 1)) ^ (2 * k) *
          Real.exp (-(3 * π / 2) * Y₀))) := by rw [hC, nearRadicalConst]; ring
    _ ≤ C * (Y₀ ^ 2 * Y₀ ^ 4 * (Real.exp (14 * k) * Real.exp (-(3 * π / 2) * Y₀))) := by gcongr
    _ ≤ C * (Y₀ ^ 6 * Real.exp (-(33 / 10) * Y₀)) := by
        rw [show Y₀ ^ 2 * Y₀ ^ 4 = Y₀ ^ 6 by ring]; gcongr
    _ ≤ C * (720 * Real.exp Y₀ * Real.exp (-(33 / 10) * Y₀)) := by gcongr
    _ = (720 * C) * Real.exp (-((13 / 10) * Y₀)) * (Real.exp Y₀ * Real.exp (-Y₀)) *
          Real.exp (-Y₀) := by rw [hsplit]; ring
    _ ≤ Real.exp ((13 / 10) * Y₀) * Real.exp (-((13 / 10) * Y₀)) *
          (Real.exp Y₀ * Real.exp (-Y₀)) * Real.exp (-Y₀) := by gcongr
    _ = Real.exp (-Y₀) := by rw [hE13, hEE]; ring


/-! ## Linear structure, smoothness and support -/

theorem contDiff_riemannKernelDeriv (n : ℕ) (i : ℕ) : ContDiff ℝ n (riemannKernelDeriv i) := by
  induction n generalizing i with
  | zero => exact contDiff_zero.mpr (continuous_riemannKernelDeriv i)
  | succ n ih =>
    have hderiv : deriv (riemannKernelDeriv i) = riemannKernelDeriv (i + 1) :=
      funext fun u => (hasDerivAt_riemannKernelDeriv i u).deriv
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun u => (hasDerivAt_riemannKernelDeriv i u).differentiableAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · rw [hderiv]; exact ih (i + 1)

theorem contDiff_nearRadicalTest {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) :
    ContDiff ℝ 2 (nearRadicalTest L a) := by
  unfold nearRadicalTest kernelComb
  refine ContDiff.mul ?_ (Complex.ofRealCLM.contDiff.comp (contDiff_bulkCutoff L))
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_riemannKernelDeriv 2 i)

theorem tsupport_nearRadicalTest {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) :
    tsupport (nearRadicalTest L a) ⊆ Icc (-L) L := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra h
  have hL : L ≤ |u| := by
    by_contra h'; push Not at h'
    exact h ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  exact hu (by unfold nearRadicalTest; rw [bulkCutoff_eq_zero hL]; simp)

theorem kernelComb_single {K : ℕ} (i : Fin (K + 1)) (u : ℝ) :
    kernelComb (Pi.single i 1) u = riemannKernelDeriv i u := by
  unfold kernelComb
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
    (by simp)]
  simp

theorem nearRadicalTest_eq_sum {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (u : ℝ) :
    nearRadicalTest L a u = ∑ i, a i * nearRadicalTest L (Pi.single i 1) u := by
  simp only [nearRadicalTest, kernelComb_single]
  unfold kernelComb
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- The truncation map `a ↦ f_a`. -/
def nearRadicalTestMap {K : ℕ} (L : ℝ) : (Fin (K + 1) → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun a := nearRadicalTest L a
  map_add' a b := by
    funext u; unfold nearRadicalTest kernelComb
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext u; unfold nearRadicalTest kernelComb
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

theorem superExpDecay_nearRadicalTest {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) :
    SuperExpDecay (nearRadicalTest L a) := by
  have h := (superExpDecay_kernelComb a).mul_bounded (χ := fun u => ((bulkCutoff L u : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (contDiff_bulkCutoff L (n := 0)).continuous) (B := 1)
    (fun u => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bulkCutoff_nonneg L u)]
      exact bulkCutoff_le_one L u)
  refine (show (fun u => ((bulkCutoff L u : ℝ) : ℂ) * kernelComb a u) = nearRadicalTest L a from
    funext fun u => by unfold nearRadicalTest; ring) ▸ h

theorem paperFT_nearRadicalTest_eq_sum {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) (z : ℂ) :
    paperFT (nearRadicalTest L a) z = ∑ i, a i * paperFT (nearRadicalTest L (Pi.single i 1)) z := by
  unfold paperFT
  simp_rw [nearRadicalTest_eq_sum L a, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]; congr 1; funext u; ring
  · have := ((superExpDecay_nearRadicalTest L (Pi.single i 1)).integrable_mul_cexp z).const_mul (a i)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only; ring

/-- The two polar functionals `a ↦ (f̂_a(i/2), f̂_a(-i/2))`. -/
def nearRadicalPolarMap {K : ℕ} (L : ℝ) : (Fin (K + 1) → ℂ) →ₗ[ℂ] ℂ × ℂ where
  toFun a := (∑ i, a i * paperFT (nearRadicalTest L (Pi.single i 1)) (I / 2),
    ∑ i, a i * paperFT (nearRadicalTest L (Pi.single i 1)) (-(I / 2)))
  map_add' a b := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Prod.mk_add_mk]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk, Finset.mul_sum,
      mul_assoc]

theorem nearRadicalPolarMap_eq {K : ℕ} (L : ℝ) (a : Fin (K + 1) → ℂ) :
    nearRadicalPolarMap L a = (paperFT (nearRadicalTest L a) (I / 2),
      paperFT (nearRadicalTest L a) (-(I / 2))) := by
  rw [paperFT_nearRadicalTest_eq_sum, paperFT_nearRadicalTest_eq_sum]; rfl


/-- A bulk polynomial vanishing on `[Y₀/8, Y₀/4]` comes from zero coefficients. -/
theorem eq_zero_of_kernelPoly_bulk {K : ℕ} (x : Fin (K + 1) → ℝ) {Y₀ : ℝ} (hY₀ : 0 < Y₀)
    (h : ∀ t ∈ Icc (Y₀ / 8) (Y₀ / 4), |(kernelPoly x).eval t| ≤ 0) : x = 0 := by
  have hR : kernelPoly x = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (fun t ht => ?_) (Set.Icc_infinite (by linarith : Y₀ / 8 < Y₀ / 4))
    have := h t ht
    exact abs_nonpos_iff.mp this
  exact eq_zero_of_sum_riemannKernelPoly x hR

/-- **Injectivity of the truncation map** in the bulk regime. -/
theorem nearRadicalTestMap_injective {K : ℕ} (L : ℝ) (hY₀ : 40 ≤ Real.exp (2 * (L - 1)))
    (hkY : ((K + 2 : ℕ) : ℝ) + 1 ≤ Real.exp (2 * (L - 1)) / 10) :
    Function.Injective (nearRadicalTestMap (K := K) L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have ha' : nearRadicalTest L a = 0 := ha
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hYpos : 0 < Y₀ := Real.exp_pos _
  obtain ⟨z₁, hz₁, h₁⟩ := exists_bulk_max (kernelPoly fun i => (a i).re) hYpos
  obtain ⟨z₂, hz₂, h₂⟩ := exists_bulk_max (kernelPoly fun i => (a i).im) hYpos
  obtain ⟨z₃, hz₃, h₃⟩ := exists_bulk_max (kernelPoly (parityCoeff fun i => (a i).re)) hYpos
  obtain ⟨z₄, hz₄, h₄⟩ := exists_bulk_max (kernelPoly (parityCoeff fun i => (a i).im)) hYpos
  have hb := integral_norm_sq_nearRadicalTest_ge L a hY₀ hkY hz₁ hz₂ hz₃ hz₄ h₁ h₂ h₃ h₄
  rw [ha'] at hb
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integral_zero] at hb
  have hKb : 0 < Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2))) := by positivity
  have hsum : |(kernelPoly fun i => (a i).re).eval z₁| ^ 2 +
      |(kernelPoly fun i => (a i).im).eval z₂| ^ 2 +
      |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃| ^ 2 +
      |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄| ^ 2 ≤ 0 := by
    by_contra hc; push Not at hc
    have := mul_pos hKb hc
    linarith
  have e1 : |(kernelPoly fun i => (a i).re).eval z₁| = 0 := by
    have := sq_nonneg |(kernelPoly fun i => (a i).im).eval z₂|
    have := sq_nonneg |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃|
    have := sq_nonneg |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄|
    have h0 : |(kernelPoly fun i => (a i).re).eval z₁| ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h0 (sq_nonneg _))
  have e2 : |(kernelPoly fun i => (a i).im).eval z₂| = 0 := by
    have := sq_nonneg |(kernelPoly fun i => (a i).re).eval z₁|
    have := sq_nonneg |(kernelPoly (parityCoeff fun i => (a i).re)).eval z₃|
    have := sq_nonneg |(kernelPoly (parityCoeff fun i => (a i).im)).eval z₄|
    have h0 : |(kernelPoly fun i => (a i).im).eval z₂| ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h0 (sq_nonneg _))
  have hre := eq_zero_of_kernelPoly_bulk (fun i => (a i).re) hYpos (fun t ht => e1 ▸ h₁ t ht)
  have him := eq_zero_of_kernelPoly_bulk (fun i => (a i).im) hYpos (fun t ht => e2 ▸ h₂ t ht)
  funext i
  apply Complex.ext
  · exact congrFun hre i
  · exact congrFun him i

/-! ## The near radical has dimension `≍ e^{2a}` -/

/-- **Theorem (dimension of the near radical of the Weil form).**  For all large `a` there is a
subspace `V` of `C²` tests supported in `[-a, a]`, with `f̂(±i/2) = 0` (the Hodge class), of dimension
at least `e^{2a-2}/20`, on which the Weil form of `ζ` is super-exponentially small:
`‖W(f,f)‖ ≤ exp(-e^{2a-2}) ∫|f|²`.

Unconditional.  By min–max, the `⌈e^{2a-2}/20⌉` lowest eigenvalues of the level-`a` Weil and Hodge
forms lie below `exp(-e^{2a-2})`, and every certificate `W ≥ η‖f‖²` with
`η > exp(-e^{2a-2})` on a subspace forces that subspace to have codimension at least
`e^{2a-2}/20`.  `V` consists of truncations of `Q(∂)Φ`, with `Φ` Riemann's kernel and `deg Q` up to
`e^{2a-2}/10`. -/
theorem zeta_weil_near_radical_dimension :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧
      Real.exp (2 * L - 2) / 20 ≤ (Module.finrank ℂ V : ℝ) ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤ Real.exp (-Real.exp (2 * L - 2)) * ∫ u, ‖f u‖ ^ 2 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set S := zetaInvSqSum with hS
  have hS0 : 0 ≤ S := zetaInvSqSum_nonneg
  set C := nearRadicalConst S Λ with hC
  set Ystar := max 100 (Real.log (720 * C + 1)) with hYstar
  have hYstar100 : 100 ≤ Ystar := le_max_left _ _
  refine ⟨1 + Real.log Ystar / 2, fun L hL => ?_⟩
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hY₀ge : Ystar ≤ Y₀ := by
    have : Real.log Ystar ≤ 2 * (L - 1) := by linarith
    calc Ystar = Real.exp (Real.log Ystar) := (Real.exp_log (by linarith)).symm
      _ ≤ Y₀ := Real.exp_le_exp.mpr this
  have hY100 : 100 ≤ Y₀ := le_trans hYstar100 hY₀ge
  have hYlog : Real.log (720 * C + 1) ≤ Y₀ := le_trans (le_max_right _ _) hY₀ge
  have hYexp : Real.exp (2 * L - 2) = Y₀ := by rw [hY₀def]; ring_nf
  -- the number of derivatives
  set N := ⌊Y₀ / 10⌋₊ with hN
  have hN10 : 10 ≤ N := by
    rw [hN]; exact Nat.le_floor (by push_cast; linarith)
  have hNle : (N : ℝ) ≤ Y₀ / 10 := Nat.floor_le (by positivity)
  have hNgt : Y₀ / 10 < N + 1 := Nat.lt_floor_add_one _
  set K := N - 3 with hK
  have hK2 : K + 2 = N - 1 := by omega
  have hkY : ((K + 2 : ℕ) : ℝ) + 1 ≤ Y₀ / 10 := by
    rw [hK2]; push_cast [show 1 ≤ N by omega]; linarith
  have hY40 : 40 ≤ Y₀ := by linarith
  set T := nearRadicalTestMap (K := K) L with hT
  have hTinj := nearRadicalTestMap_injective (K := K) L hY40 hkY
  set ψ := nearRadicalPolarMap (K := K) L with hψ
  refine ⟨(LinearMap.ker ψ).map T, inferInstance, ?_, ?_, ?_⟩
  · -- dimension count
    have hequiv := Submodule.equivMapOfInjective T hTinj (LinearMap.ker ψ)
    rw [← hequiv.finrank_eq]
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    have hrange : Module.finrank ℂ (LinearMap.range ψ) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range ψ)
      simpa using this
    have hdim : Module.finrank ℂ (Fin (K + 1) → ℂ) = K + 1 := by simp
    rw [hdim] at hrn
    have hker : K - 1 ≤ Module.finrank ℂ (LinearMap.ker ψ) := by omega
    have hKreal : (N : ℝ) - 4 ≤ (Module.finrank ℂ (LinearMap.ker ψ) : ℝ) := by
      have h1 : ((K - 1 : ℕ) : ℝ) ≤ Module.finrank ℂ (LinearMap.ker ψ) := by exact_mod_cast hker
      have h2 : ((K - 1 : ℕ) : ℝ) = (N : ℝ) - 4 := by
        rw [hK, show N - 3 - 1 = N - 4 by omega]
        push_cast [show 4 ≤ N by omega]; ring
      linarith
    rw [hYexp]
    linarith
  · rintro f ⟨a, ha, rfl⟩
    have hψa : ψ a = 0 := ha
    rw [hψ, nearRadicalPolarMap_eq] at hψa
    exact ⟨contDiff_nearRadicalTest L a, tsupport_nearRadicalTest L a,
      (Prod.mk_eq_zero.mp hψa).1, (Prod.mk_eq_zero.mp hψa).2⟩
  · rintro f ⟨a, -, rfl⟩
    show ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖ ≤ _
    have hW := norm_W_nearRadicalTest_le_ratio L a hΛ hY40 hkY
    rw [← hY₀def, ← hS] at hW
    have hratio := nearRadical_ratio_le (k := K + 2) hS0 hΛ0 hkY hY100 hYlog
    rw [hYexp]
    have hI : 0 ≤ ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 := integral_nonneg fun _ => by positivity
    calc ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖
        ≤ 20 * S * (1 + 2 * Λ) ^ 2 *
            ((28 * ((K + 2 : ℕ) : ℝ) * (16 * Real.exp 1) ^ (K + 2) * Y₀ ^ 2 *
                Real.exp (-π * Y₀)) ^ 2 /
              (Real.exp (-π * Y₀ / 2) / (176 * (8 * Real.exp 1) ^ (2 * (K + 2))))) *
            ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 := hW
      _ ≤ Real.exp (-Y₀) * ∫ u : ℝ, ‖nearRadicalTest L a u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hratio hI

end

end RHTower
