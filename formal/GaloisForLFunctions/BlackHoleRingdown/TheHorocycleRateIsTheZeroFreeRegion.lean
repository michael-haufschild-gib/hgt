import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleReadsTheZeros
import GaloisForLFunctions.HTGeometry.MellinTestFunctionPerron
import GaloisForLFunctions.HTGeometry.MellinRegularStripLinear
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.RHTower.InvZetaRHSubpolynomial
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The horocycle rate is the zero-free region

Let `φ` be smooth with compact support in `(1, ∞)`, `F_φ` its pseudo-Eisenstein series and `A_φ(y)`
the mean of `F_φ` along the closed horocycle of height `y`. With `ψ = φ` as a complex function and
`ψ̃` its Mellin transform, `TheHorocycleReadsTheZeros.mellin_horocycleMean` gives for `Re w > 0`

  `∫_0^∞ A_φ(y) y^{w-1} dy = 2ψ̃(w) + 2 Q(w + 1) ψ̃(-w-1) / w`,   `Q(s) = s ξ(2s - 1)/ξ(2s)`.

Subtracting `c e^{-y}`, `c = 2Q(1)ψ̃(-1) = (6/π)∫ φ(y) y^{-2} dy`, removes the pole at `w = 0`:
the Mellin transform of `A_φ - c e^{-y}` is `Ψ(w) = 2ψ̃(w) + N(w + 1)/w` with
`N(s) = 2Q(s)ψ̃(-s) - cΓ(s)` and `N(1) = 0`. If `ξ` has no zeros right of `Re z = θ` and `1/ζ`
grows polynomially on every strip `Re z ≥ θ + δ`, then `Ψ` is holomorphic on `Re w > θ/2 - 1` and
decays faster than any power of `|Im w|` there: `ψ̃` decays rapidly by integration by parts,
`Q(s) = (s - 1)·(Γℝ(2s-1)/Γℝ(2s))·ζ(2s-1)/ζ(2s)` grows polynomially (Stirling on the Gamma ratio),
and `Γ` decays exponentially. Mellin inversion on `Re w = 1` and the shift to
`Re w = θ/2 - 1 + ε` give

  `|A_φ(y) - c| ≤ C y^{1 - θ/2 - ε}`   (`horocycle_rate_of_zeroFree`).

* `θ = 1` is unconditional: rate `y^{1/2 - ε}` (`horocycle_rate`), Sarnak's square-root rate up to
  `ε`.
* `θ = 1/2` is the Riemann hypothesis: rate `y^{3/4 - ε}` (`horocycle_rate_of_riemannHypothesis`).

With Zagier's converse (`re_le_of_horocycle_rate`: rate `y^α` forces `Re ρ ≤ 2 - 2α`) this is
**Zagier's theorem** for pseudo-Eisenstein test functions
(`riemannHypothesis_iff_horocycle_rate`): the Riemann hypothesis holds iff every horocycle mean
converges at rate `y^{3/4 - ε}` for every `ε > 0`.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology Complex
open scoped ContDiff

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.TestFunctionPerron

noncomputable section

/-! ## Rapid decay of the Mellin transform of a test function -/

/-- The `k`-th Euler derivative `(u d/du)^k f`. -/
def eulerIter : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | k + 1, f => fun u => (u : ℂ) * deriv (eulerIter k f) u

theorem isTest_eulerIter {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b) :
    ∀ k, IsTest (eulerIter k f) a b
  | 0 => hf
  | k + 1 => (isTest_eulerIter hf k).eulerDeriv

theorem mellin_eulerIter {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b) (s : ℂ) :
    ∀ k, mellin (eulerIter k f) s = (-s) ^ k * mellin f s
  | 0 => by simp [eulerIter]
  | k + 1 => by
      rw [eulerIter, (isTest_eulerIter hf k).mellin_eulerDeriv, mellin_eulerIter hf s k]
      ring

theorem one_add_im_sq_pow_le (s : ℂ) (K : ℕ) :
    (1 + s.im ^ 2) ^ K ≤ 2 ^ K * (1 + ‖s‖ ^ (2 * K)) := by
  have h1 : 1 + s.im ^ 2 ≤ 2 * max 1 (‖s‖ ^ 2) := by
    have h := Complex.abs_im_le_norm s
    have : s.im ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
    nlinarith [le_max_left 1 (‖s‖ ^ 2), le_max_right 1 (‖s‖ ^ 2)]
  have h2 : (max 1 (‖s‖ ^ 2)) ^ K ≤ 1 + ‖s‖ ^ (2 * K) := by
    rcases le_total 1 (‖s‖ ^ 2) with h | h
    · rw [max_eq_right h, ← pow_mul]
      linarith
    · rw [max_eq_left h, one_pow]
      linarith [pow_nonneg (norm_nonneg s) (2 * K)]
  calc (1 + s.im ^ 2) ^ K ≤ (2 * max 1 (‖s‖ ^ 2)) ^ K := pow_le_pow_left₀ (by positivity) h1 K
    _ = 2 ^ K * (max 1 (‖s‖ ^ 2)) ^ K := mul_pow _ _ _
    _ ≤ 2 ^ K * (1 + ‖s‖ ^ (2 * K)) := by gcongr

/-- **Rapid decay:** `|𝓜f(s)| ≤ C (1 + (Im s)²)^{-K}` on `|Re s - 1| ≤ R`, for every `K`. -/
theorem exists_norm_mellin_le_decay_pow {f : ℝ → ℂ} {a b : ℝ} (hf : IsTest f a b) (R : ℝ)
    (K : ℕ) : ∃ C, 0 ≤ C ∧ ∀ s : ℂ, |s.re - 1| ≤ R → ‖mellin f s‖ ≤ C / (1 + s.im ^ 2) ^ K := by
  have hg := isTest_eulerIter hf (2 * K)
  obtain ⟨B₀, hB₀0, hB₀⟩ := hf.exists_bound
  obtain ⟨B₂, hB₂0, hB₂⟩ := hg.exists_bound
  have hba : 0 ≤ b - a := by linarith [hf.le]
  set C₀ := (b - a) * Real.exp (R * IsTest.logScale a b) * B₀
  set C₂ := (b - a) * Real.exp (R * IsTest.logScale a b) * B₂
  refine ⟨2 ^ K * (C₀ + C₂), by positivity, fun s hs => ?_⟩
  have h0 := hf.norm_mellin_le hB₀ hs
  have h2 := hg.norm_mellin_le hB₂ hs
  rw [mellin_eulerIter hf, norm_mul, norm_pow, norm_neg] at h2
  rw [le_div_iff₀ (by positivity)]
  calc ‖mellin f s‖ * (1 + s.im ^ 2) ^ K ≤ ‖mellin f s‖ * (2 ^ K * (1 + ‖s‖ ^ (2 * K))) :=
        mul_le_mul_of_nonneg_left (one_add_im_sq_pow_le s K) (norm_nonneg _)
    _ = 2 ^ K * (‖mellin f s‖ + ‖s‖ ^ (2 * K) * ‖mellin f s‖) := by ring
    _ ≤ 2 ^ K * (C₀ + C₂) := by gcongr

/-- `u^n e^{-πu/2} ≤ (2/π)^n n!` for `u ≥ 0`. -/
theorem pow_mul_exp_neg_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ n * Real.exp (-(Real.pi * u / 2)) ≤ (2 / Real.pi) ^ n * n.factorial := by
  have hx : 0 ≤ Real.pi * u / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf] at h
  have hp : u ^ n = (2 / Real.pi) ^ n * (Real.pi * u / 2) ^ n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hp, Real.exp_neg, mul_assoc, ← div_eq_mul_inv]
  gcongr
  rw [div_le_iff₀ (Real.exp_pos _)]
  linarith [h]

/-- A polynomial times `e^{-π|t|/2}` is `O((1 + t²)^{-K})` for `|t| ≥ 1`. -/
theorem exists_pow_mul_exp_le (N K : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) ≤ C / (1 + t ^ 2) ^ K := by
  refine ⟨2 ^ K * ((2 / Real.pi) ^ (2 * K + N) * (2 * K + N).factorial), by positivity,
    fun t ht => ?_⟩
  have h0 : 0 ≤ |t| := abs_nonneg t
  rw [le_div_iff₀ (by positivity)]
  have h1 : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by rw [sq_abs]; nlinarith [sq_abs t]
  have h2 : (1 + t ^ 2) ^ K ≤ 2 ^ K * |t| ^ (2 * K) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 K
  have h3 := pow_mul_exp_neg_le (2 * K + N) h0
  rw [pow_add] at h3
  calc |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) * (1 + t ^ 2) ^ K
      ≤ |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) * (2 ^ K * |t| ^ (2 * K)) := by gcongr
    _ = 2 ^ K * (|t| ^ (2 * K) * |t| ^ N * Real.exp (-(Real.pi * |t| / 2))) := by ring
    _ ≤ _ := by gcongr

/-! ## The scattering ratio -/

/-- `Q(s) = s ξ(2s - 1)/ξ(2s) = (s - 1) Λ(2s - 1)/Λ(2s)`. -/
def scatterQ (s : ℂ) : ℂ := s * xi (2 * s - 1) / xi (2 * s)

theorem completedRiemannZeta_eq_gammaℝ_mul {z : ℂ} (h0 : z ≠ 0) (hΓ : Gammaℝ z ≠ 0) :
    completedRiemannZeta z = Gammaℝ z * riemannZeta z := by
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

theorem gammaℝ_ne_zero_of_im {z : ℂ} (h : z.im ≠ 0) : Gammaℝ z ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h0
  apply h
  rw [hn]
  simp

/-- `ξ(2s - 1)` and `ξ(2s)` through `Λ`: `s ξ(2s - 1) = s(2s - 1) ((s - 1) Λ(2s - 1))`,
`ξ(2s) = s(2s - 1) Λ(2s)`. -/
theorem xi_two_mul_sub_one_eq {s : ℂ} (h0 : 2 * s - 1 ≠ 0) (h1 : 2 * s - 1 ≠ 1) :
    s * xi (2 * s - 1) = s * (2 * s - 1) * ((s - 1) * completedRiemannZeta (2 * s - 1)) := by
  rw [xi_eq_half_mul h0 h1]
  ring

theorem xi_two_mul_eq {s : ℂ} (h0 : 2 * s ≠ 0) (h1 : 2 * s ≠ 1) :
    xi (2 * s) = s * (2 * s - 1) * completedRiemannZeta (2 * s) := by
  rw [xi_eq_half_mul h0 h1]
  ring

/-- `Q(s) = (s - 1) Λ(2s - 1)/Λ(2s)` when `2s, 2s - 1 ∉ {0, 1}`. -/
theorem scatterQ_eq_completed {s : ℂ} (hs0 : s ≠ 0) (h0 : 2 * s - 1 ≠ 0) (h1 : 2 * s - 1 ≠ 1)
    (h2 : 2 * s ≠ 1) :
    scatterQ s = (s - 1) * completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s) := by
  have hm : s * (2 * s - 1) ≠ 0 := mul_ne_zero hs0 h0
  rw [scatterQ, xi_two_mul_sub_one_eq h0 h1,
    xi_two_mul_eq (mul_ne_zero two_ne_zero hs0) h2, mul_div_mul_left _ _ hm]

theorem msB_div_msA_eq {s : ℂ} (hs : 1 < s.re) :
    msB (s - 1 / 2) / msA (s - 1 / 2) = scatterQ s / (s - 1) := by
  have h1re : 1 < (2 * s - 1).re := by simp; linarith
  have h2re : 1 < (2 * s).re := by simp; linarith
  have hne : ∀ z : ℂ, 1 < z.re → z ≠ 0 ∧ z ≠ 1 := fun z hz =>
    ⟨fun h => by rw [h] at hz; simp at hz; linarith, fun h => by rw [h] at hz; simp at hz⟩
  have hΓ1 := Gammaℝ_ne_zero_of_re_pos (by linarith : (0 : ℝ) < (2 * s - 1).re)
  have hΓ2 := Gammaℝ_ne_zero_of_re_pos (by linarith : (0 : ℝ) < (2 * s).re)
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  rw [scatterQ_eq_completed hs0 (hne _ h1re).1 (hne _ h1re).2 (hne _ h2re).2, msB, msA,
    reflectedCompletedLambda, reflectedCompletedLambda,
    show 1 + 2 * (s - 1 / 2) = 2 * s by ring, show 2 * (s - 1 / 2) = 2 * s - 1 by ring,
    ← completedRiemannZeta_eq_gammaℝ_mul (hne _ h1re).1 hΓ1,
    ← completedRiemannZeta_eq_gammaℝ_mul (hne _ h2re).1 hΓ2, mul_div_assoc,
    mul_div_cancel_left₀ _ hs1]

/-- Off the real axis, `Q(s) = (s - 1) (Γℝ(2s - 1)/Γℝ(2s)) ζ(2s - 1) ζ(2s)⁻¹`. -/
theorem scatterQ_eq {s : ℂ} (him : s.im ≠ 0) :
    scatterQ s = (s - 1) * (Gammaℝ (2 * s - 1) / Gammaℝ (2 * s)) * riemannZeta (2 * s - 1) *
      (riemannZeta (2 * s))⁻¹ := by
  have h2 : (2 * s).im ≠ 0 := by simp [him]
  have h1 : (2 * s - 1).im ≠ 0 := by simp [him]
  have hne : ∀ z : ℂ, z.im ≠ 0 → z ≠ 0 ∧ z ≠ 1 := fun z hz =>
    ⟨fun h => hz (by simp [h]), fun h => hz (by simp [h])⟩
  have hs0 : s ≠ 0 := fun h => him (by simp [h])
  rw [scatterQ_eq_completed hs0 (hne _ h1).1 (hne _ h1).2 (hne _ h2).2,
    completedRiemannZeta_eq_gammaℝ_mul (hne _ h1).1 (gammaℝ_ne_zero_of_im h1),
    completedRiemannZeta_eq_gammaℝ_mul (hne _ h2).1 (gammaℝ_ne_zero_of_im h2)]
  ring

theorem differentiableAt_scatterQ {s : ℂ} (h : xi (2 * s) ≠ 0) :
    DifferentiableAt ℂ scatterQ s := by
  have hx := xi_differentiable
  have h1 : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s - 1)) s :=
    (hx _).comp s ((differentiableAt_id.const_mul 2).sub_const 1)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
    (hx _).comp s (differentiableAt_id.const_mul 2)
  exact (differentiableAt_id.mul h1).div h2 h

/-- `|Γℝ(2s - 1)/Γℝ(2s)| = √π |Γ(s - ½)| |Γ(s)|⁻¹`. -/
theorem norm_gammaℝ_div (s : ℂ) :
    ‖Gammaℝ (2 * s - 1) / Gammaℝ (2 * s)‖ =
      Real.pi ^ (1 / 2 : ℝ) * (‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖) := by
  have e1 : Gammaℝ (2 * s - 1) = (Real.pi : ℂ) ^ (-(2 * s - 1) / 2) * Gamma (s - 1 / 2) := by
    rw [Gammaℝ_def]
    congr 2
    ring
  have e2 : Gammaℝ (2 * s) = (Real.pi : ℂ) ^ (-s) * Gamma s := by
    rw [Gammaℝ_def]
    congr 2 <;> ring
  rw [e1, e2, norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_inv]
  have hre1 : (-(2 * s - 1) / 2).re = 1 / 2 + (-s).re := by simp; ring
  rw [hre1, Real.rpow_add Real.pi_pos]
  have hp : 0 < Real.pi ^ (-s).re := Real.rpow_pos_of_pos Real.pi_pos _
  field_simp

/-- **Polynomial growth of `Q`** on `|Im s| ≥ 1`, given polynomial growth of `1/ζ(2s)`. -/
theorem exists_norm_scatterQ_le {σ₀ σ₁ K₀ : ℝ} {N₀ : ℕ} (hK₀ : 0 ≤ K₀)
    (hinv : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ K₀ * |s.im| ^ N₀) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| →
      ‖scatterQ s‖ ≤ C * |s.im| ^ N := by
  obtain ⟨C₁, N₁, hC₁, hΓ₁⟩ := exists_sharp_bound_norm_Gamma_strip (σ₀ - 1 / 2) (σ₁ - 1 / 2)
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ := exists_bound_norm_inv_Gamma_strip σ₀ σ₁
  obtain ⟨C₃, N₃, hC₃, hζ⟩ := exists_bound_norm_riemannZeta_strip (|2 * σ₀ - 1| + |2 * σ₁ - 1|)
  set L := |σ₀ - 1| + |σ₁ - 1| + 1
  refine ⟨L * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂)) * (C₃ * 2 ^ N₃) * K₀, 1 + (N₁ + N₂) + N₃ + N₀,
    by positivity, fun s h0 h1 ht => ?_⟩
  have hsim : s.im ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
  have hti : 0 < |s.im| := lt_of_lt_of_le one_pos ht
  rw [scatterQ_eq hsim, norm_mul, norm_mul, norm_mul, norm_gammaℝ_div]
  -- the four factors
  have hA : ‖s - 1‖ ≤ L * |s.im| := by
    have : ‖s - 1‖ ≤ |s.re - 1| + |s.im| := by
      have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
      simpa using h
    have hre : |s.re - 1| ≤ |σ₀ - 1| + |σ₁ - 1| := by
      rcases le_total 1 s.re with h | h
      · rw [abs_of_nonneg (by linarith)]
        linarith [le_abs_self (σ₁ - 1), abs_nonneg (σ₀ - 1)]
      · rw [abs_of_nonpos (by linarith)]
        linarith [neg_abs_le (σ₀ - 1), abs_nonneg (σ₁ - 1)]
    have hS : |σ₀ - 1| + |σ₁ - 1| ≤ (|σ₀ - 1| + |σ₁ - 1|) * |s.im| :=
      le_mul_of_one_le_right (by positivity) ht
    calc ‖s - 1‖ ≤ |s.re - 1| + |s.im| := this
      _ ≤ (|σ₀ - 1| + |σ₁ - 1|) * |s.im| + |s.im| := by linarith
      _ = L * |s.im| := by simp only [L]; ring
  have hB1 : ‖Gamma (s - 1 / 2)‖ ≤ C₁ * |s.im| ^ N₁ * Real.exp (-(Real.pi * |s.im| / 2)) := by
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    have him' : (s - 1 / 2).im = s.im := by simp
    have := hΓ₁ (s - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him']; exact ht)
    rwa [him'] at this
  have hB2 : ‖(Gamma s)⁻¹‖ ≤ C₂ * |s.im| ^ N₂ * Real.exp (Real.pi * |s.im| / 2) :=
    hΓ₂ s h0 h1 ht
  have hB : ‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖ ≤ C₁ * C₂ * |s.im| ^ (N₁ + N₂) := by
    calc ‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖
        ≤ (C₁ * |s.im| ^ N₁ * Real.exp (-(Real.pi * |s.im| / 2))) *
          (C₂ * |s.im| ^ N₂ * Real.exp (Real.pi * |s.im| / 2)) :=
          mul_le_mul hB1 hB2 (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * |s.im| ^ (N₁ + N₂) := by
          rw [pow_add]
          have : Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi * |s.im| / 2) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination (C₁ * C₂ * |s.im| ^ N₁ * |s.im| ^ N₂) * this
  have hC : ‖riemannZeta (2 * s - 1)‖ ≤ C₃ * 2 ^ N₃ * |s.im| ^ N₃ := by
    have hz : (2 : ℂ) * s - 1 = (((2 * s.re - 1 : ℝ)) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hσ : |2 * s.re - 1| ≤ |2 * σ₀ - 1| + |2 * σ₁ - 1| := by
      rcases le_total (2 * s.re - 1) 0 with h | h
      · rw [abs_of_nonpos h]
        linarith [neg_abs_le (2 * σ₀ - 1), abs_nonneg (2 * σ₁ - 1)]
      · rw [abs_of_nonneg h]
        linarith [le_abs_self (2 * σ₁ - 1), abs_nonneg (2 * σ₀ - 1)]
    have ht2 : 1 ≤ |2 * s.im| := by rw [abs_mul]; norm_num; linarith
    have := hζ _ _ hσ ht2
    rw [hz]
    calc _ ≤ C₃ * |2 * s.im| ^ N₃ := this
      _ = C₃ * 2 ^ N₃ * |s.im| ^ N₃ := by rw [abs_mul, mul_pow]; norm_num; ring
  have hD := hinv s h0 h1 ht
  have hti1 : (1 : ℝ) ≤ |s.im| ^ 1 := by simpa using ht
  calc ‖s - 1‖ * (Real.pi ^ (1 / 2 : ℝ) * (‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖)) *
        ‖riemannZeta (2 * s - 1)‖ * ‖(riemannZeta (2 * s))⁻¹‖
      ≤ (L * |s.im|) * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂ * |s.im| ^ (N₁ + N₂))) *
        (C₃ * 2 ^ N₃ * |s.im| ^ N₃) * (K₀ * |s.im| ^ N₀) := by
        gcongr
    _ = L * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂)) * (C₃ * 2 ^ N₃) * K₀ *
        |s.im| ^ (1 + (N₁ + N₂) + N₃ + N₀) := by
        ring

/-! ## Continuity of the horocycle mean -/

theorem continuousAt_ofComplex_mk {x y₀ : ℝ} (hy : 0 < y₀) :
    ContinuousAt (fun y : ℝ => ofComplex (⟨x, y⟩ : ℂ)) y₀ := by
  have hmk : Continuous (fun y : ℝ => (⟨x, y⟩ : ℂ)) := by
    have : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext y; apply Complex.ext <;> simp
    rw [this]
    fun_prop
  exact (ofComplex.continuousAt (by simp [ofComplex, hy])).comp hmk.continuousAt

theorem continuous_ofComplex_mk_re {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => ofComplex (⟨x, y⟩ : ℂ)) := by
  have hmk : Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
    have : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [this]
    fun_prop
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact (ofComplex.continuousAt (by simp [ofComplex, hy])).comp hmk.continuousAt

/-- The horocycle mean of a bounded continuous function is continuous in the height. -/
theorem continuousAt_horocycleMean {F : ℍ → ℂ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ z, ‖F z‖ ≤ B) {y₀ : ℝ} (hy₀ : 0 < y₀) : ContinuousAt (horocycleMean F) y₀ := by
  unfold horocycleMean
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ ?_ ?_
  · filter_upwards [Ioi_mem_nhds hy₀] with y hy
    exact (hF.comp (continuous_ofComplex_mk_re hy)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => ae_of_all _ fun x => hB _
  · exact integrableOn_const (by simp)
  · exact ae_of_all _ fun x => hF.continuousAt.comp (continuousAt_ofComplex_mk hy₀)

/-! ## The regular part of the Mellin transform -/

section Regular

variable (ψ : ℝ → ℂ)

/-- The residue constant `c = 2 Q(1) ψ̃(-1)`. -/
def residueConst : ℂ := 2 * scatterQ 1 * mellin ψ (-1)

/-- `N(s) = 2 Q(s) ψ̃(-s) - c Γ(s)`, which vanishes at `s = 1`. -/
def poleNumerator (s : ℂ) : ℂ := 2 * scatterQ s * mellin ψ (-s) - residueConst ψ * Gamma s

/-- The regular part `Ψ(w) = 2ψ̃(w) + N(w + 1)/w` of the Mellin transform of `A_φ - c e^{-y}`. -/
def regularPart (w : ℂ) : ℂ := 2 * mellin ψ w + dslope (poleNumerator ψ) 1 (w + 1)

theorem poleNumerator_one : poleNumerator ψ 1 = 0 := by
  simp [poleNumerator, residueConst, Complex.Gamma_one]

variable {ψ}

theorem regularPart_eq {w : ℂ} (hw : w ≠ 0) :
    regularPart ψ w = 2 * mellin ψ w + poleNumerator ψ (w + 1) / w := by
  rw [regularPart, dslope_of_ne _ (by simpa using hw), slope_def_field, poleNumerator_one,
    sub_zero, add_sub_cancel_right]

variable {a b θ : ℝ}

theorem differentiableOn_poleNumerator (hψ : IsTest ψ a b) (hθ : 0 ≤ θ)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0) :
    DifferentiableOn ℂ (poleNumerator ψ) {s : ℂ | θ / 2 < s.re} := by
  intro s hs
  have hs' : θ / 2 < s.re := hs
  have hx : xi (2 * s) ≠ 0 := hZ _ (by simp; linarith)
  have hΓ : DifferentiableAt ℂ Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m hm => ?_
    have := congrArg Complex.re hm
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold poleNumerator
  exact (((differentiableAt_scatterQ hx).const_mul 2).mul
    ((hψ.differentiableAt_mellin (-s)).comp s differentiableAt_id.neg)).sub (hΓ.const_mul _)

theorem differentiableAt_regularPart (hψ : IsTest ψ a b) (hθ0 : 0 ≤ θ) (hθ1 : θ < 2)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0) {w : ℂ} (hw : θ / 2 - 1 < w.re) :
    DifferentiableAt ℂ (regularPart ψ) w := by
  have hU : IsOpen {s : ℂ | θ / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : {s : ℂ | θ / 2 < s.re} ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by simp; linarith)
  have hd := (Complex.differentiableOn_dslope h1).2 (differentiableOn_poleNumerator hψ hθ0 hZ)
  have hw1 : w + 1 ∈ {s : ℂ | θ / 2 < s.re} := by simp; linarith
  have hdw := (hd _ hw1).differentiableAt (hU.mem_nhds hw1)
  exact ((hψ.differentiableAt_mellin w).const_mul 2).add
    (hdw.comp w (differentiableAt_id.add_const 1))

/-- **Regularity of `Ψ`** on `Re w > θ/2 - 1`: holomorphy and rapid decay on closed substrips. -/
theorem mellinRegularStrip_regularPart (hψ : IsTest ψ a b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0)
    (hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N) :
    MellinRegularStrip (regularPart ψ) (θ / 2 - 1) 2 := by
  refine ⟨fun w hw _ => differentiableAt_regularPart hψ hθ0 (by linarith) hZ hw,
    fun a' b' ha' hb' K => ?_⟩
  -- the box `|Im w| ≤ 1`
  have hbox : IsCompact (Icc a' b' ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn (f := regularPart ψ) (fun w hw => by
    have hw' : a' ≤ w.re := hw.1.1
    exact (differentiableAt_regularPart hψ hθ0 (by linarith) hZ (by linarith)).continuousAt
      |>.continuousWithinAt)
  -- `1/ζ(2s)` on the strip `a' + 1 ≤ Re s ≤ b' + 1`
  obtain ⟨K₀, N₀, hK₀, hinv⟩ := hP (2 * (a' + 1) - θ) (by linarith) (2 * (b' + 1))
  have hinv' : ∀ s : ℂ, a' + 1 ≤ s.re → s.re ≤ b' + 1 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (K₀ * 2 ^ N₀) * |s.im| ^ N₀ := by
    intro s h0 h1 ht
    have h2 : 2 ≤ |(2 * s).im| := by simp [abs_mul]; linarith
    have := hinv (2 * s) (by simp; linarith) (by simp; linarith) h2
    calc _ ≤ K₀ * |(2 * s).im| ^ N₀ := this
      _ = K₀ * 2 ^ N₀ * |s.im| ^ N₀ := by simp [abs_mul, mul_pow]; ring
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hinv'
  -- the Mellin transform of `ψ` at `w` and at `-w - 1`
  set R := |a' - 1| + |b' - 1| + |a' + 2| + |b' + 2|
  obtain ⟨C₁, hC₁, hm₁⟩ := exists_norm_mellin_le_decay_pow hψ R K
  obtain ⟨C₂, hC₂, hm₂⟩ := exists_norm_mellin_le_decay_pow hψ R (K + NQ)
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip (a' + 1) (b' + 1)
  obtain ⟨CE, hCE, hE⟩ := exists_pow_mul_exp_le NΓ K
  have hc := norm_nonneg (residueConst ψ)
  refine ⟨max B 0 * 2 ^ K + (2 * C₁ + 2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)),
    fun w hw1 hw2 => ?_⟩
  have hpos : 0 < (1 + w.im ^ 2) ^ K := by positivity
  have hB0 : 0 ≤ max B 0 * 2 ^ K := by positivity
  have hS0 : 0 ≤ 2 * C₁ + 2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE) := by positivity
  rcases le_or_gt |w.im| 1 with ht | ht
  · -- inside the box
    have hwb : w ∈ Icc a' b' ×ℂ Icc (-1 : ℝ) 1 := ⟨⟨hw1, hw2⟩, abs_le.1 ht⟩
    have h1 : (1 + w.im ^ 2) ^ K ≤ 2 ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_abs w.im, abs_nonneg w.im]
    rw [le_div_iff₀ hpos]
    calc ‖regularPart ψ w‖ * (1 + w.im ^ 2) ^ K ≤ max B 0 * 2 ^ K :=
          mul_le_mul ((hB w hwb).trans (le_max_left _ _)) h1 (by positivity) (le_max_right _ _)
      _ ≤ _ := by linarith
  · -- outside the box
    have ht1 : 1 ≤ |w.im| := ht.le
    have hw0 : w ≠ 0 := fun h => by rw [h] at ht; simp at ht; linarith
    have hnw : 1 ≤ ‖w‖ := ht1.trans (Complex.abs_im_le_norm w)
    rw [regularPart_eq hw0]
    set s := w + 1 with hsdef
    have hsre0 : a' + 1 ≤ s.re := by simp [hsdef]; linarith
    have hsre1 : s.re ≤ b' + 1 := by simp [hsdef]; linarith
    have hsim : s.im = w.im := by simp [hsdef]
    have hts : 1 ≤ |s.im| := by rw [hsim]; exact ht1
    -- the three pieces
    have hP1 : ‖mellin ψ w‖ ≤ C₁ / (1 + w.im ^ 2) ^ K := by
      refine hm₁ w ?_
      rw [abs_le]; constructor <;> linarith [abs_nonneg (a' - 1), le_abs_self (a' - 1),
        neg_abs_le (a' - 1), le_abs_self (b' - 1), abs_nonneg (a' + 2), abs_nonneg (b' + 2),
        abs_nonneg (b' - 1)]
    have hP2 : ‖mellin ψ (-s)‖ ≤ C₂ / (1 + w.im ^ 2) ^ (K + NQ) := by
      have h := hm₂ (-s) (by
        rw [abs_le]; simp [hsdef]; constructor <;>
          linarith [le_abs_self (a' + 2), neg_abs_le (b' + 2), abs_nonneg (a' - 1),
            abs_nonneg (b' - 1), neg_abs_le (a' + 2), le_abs_self (b' + 2)])
      simpa [hsdef] using h
    have hQs := hQ s hsre0 hsre1 hts
    have hΓs : ‖Gamma s‖ ≤ CΓ * (CE / (1 + w.im ^ 2) ^ K) := by
      have h := hΓ s hsre0 hsre1 hts
      rw [hsim] at h
      calc ‖Gamma s‖ ≤ CΓ * (|w.im| ^ NΓ * Real.exp (-(Real.pi * |w.im| / 2))) := by
            linarith [h]
        _ ≤ CΓ * (CE / (1 + w.im ^ 2) ^ K) := by gcongr; exact hE _ ht1
    have hpowle : |w.im| ^ NQ ≤ (1 + w.im ^ 2) ^ NQ := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      nlinarith [sq_abs w.im, abs_nonneg w.im]
    have hQψ : ‖scatterQ s‖ * ‖mellin ψ (-s)‖ ≤ CQ * C₂ / (1 + w.im ^ 2) ^ K := by
      rw [hsim] at hQs
      calc ‖scatterQ s‖ * ‖mellin ψ (-s)‖
          ≤ (CQ * |w.im| ^ NQ) * (C₂ / (1 + w.im ^ 2) ^ (K + NQ)) :=
            mul_le_mul hQs hP2 (norm_nonneg _) (by positivity)
        _ ≤ (CQ * (1 + w.im ^ 2) ^ NQ) * (C₂ / (1 + w.im ^ 2) ^ (K + NQ)) := by gcongr
        _ = CQ * C₂ / (1 + w.im ^ 2) ^ K := by
            rw [pow_add]
            field_simp
    have hN : ‖poleNumerator ψ s‖ ≤
        (2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by
      unfold poleNumerator
      calc ‖2 * scatterQ s * mellin ψ (-s) - residueConst ψ * Gamma s‖
          ≤ 2 * (‖scatterQ s‖ * ‖mellin ψ (-s)‖) + ‖residueConst ψ‖ * ‖Gamma s‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]
            norm_num
            linarith
        _ ≤ 2 * (CQ * C₂ / (1 + w.im ^ 2) ^ K) +
            ‖residueConst ψ‖ * (CΓ * (CE / (1 + w.im ^ 2) ^ K)) := by gcongr
        _ = _ := by ring
    calc ‖2 * mellin ψ w + poleNumerator ψ s / w‖
        ≤ 2 * ‖mellin ψ w‖ + ‖poleNumerator ψ s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_div]
          norm_num
          exact div_le_self (norm_nonneg _) hnw
      _ ≤ 2 * (C₁ / (1 + w.im ^ 2) ^ K) +
          (2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by gcongr
      _ = (2 * C₁ + 2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hpos.le

end Regular


/-! ## Mellin inversion and the contour shift -/

section Rate

theorem isTest_of_band {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφa : ∀ y, y < a → φ y = 0) (hφb : ∀ y, b < y → φ y = 0) :
    IsTest (fun t => (φ t : ℂ)) a b := by
  refine ⟨ha, hab, Complex.ofRealCLM.contDiff.comp hφ, fun y hy => ?_⟩
  by_contra hy'
  rcases not_and_or.1 hy' with h | h
  · exact hy (by simp [hφa y (not_le.1 h)])
  · exact hy (by simp [hφb y (not_le.1 h)])

theorem mellinConvergent_exp_neg {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ)) w := by
  refine (Complex.GammaIntegral_convergent hw).congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  ring

theorem mellin_exp_neg {w : ℂ} (hw : 0 < w.re) :
    mellin (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ)) w = Gamma w := by
  rw [Complex.Gamma_eq_integral hw, Complex.GammaIntegral, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp only [smul_eq_mul]
  push_cast
  ring

variable {ψ : ℝ → ℂ} {a b : ℝ}

/-- The Mellin transform of `A_ψ - c e^{-y}` is the regular part `Ψ` on `Re w > 0`. -/
theorem mellin_sub_exp_eq_regularPart (hψ : IsTest ψ a b) (ha : 1 < a) {w : ℂ} (hw : 0 < w.re) :
    mellin (fun y => horocycleMean (pseudoEisenstein ψ) y -
      residueConst ψ * ((Real.exp (-y) : ℝ) : ℂ)) w = regularPart ψ w := by
  have hψa : ∀ y, y < a → ψ y = 0 := fun y hy => hψ.eq_zero_of_le hy.le
  have hψb : ∀ y, b < y → ψ y = 0 := fun y hy => hψ.eq_zero_of_ge hy.le
  have hs1 : 1 < (w + 1).re := by simp; linarith
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hA := mellinConvergent_horocycleMean hψ.continuous ha hψa hψb hs1
  simp only [add_sub_cancel_right] at hA
  have hE := (mellinConvergent_exp_neg hw).const_smul (residueConst ψ)
  have hmA := mellin_horocycleMean hψ.continuous ha hψa hψb hs1
  simp only [add_sub_cancel_right] at hmA
  rw [msB_div_msA_eq hs1, add_sub_cancel_right] at hmA
  have hsplit : mellin (fun y => horocycleMean (pseudoEisenstein ψ) y -
      residueConst ψ * ((Real.exp (-y) : ℝ) : ℂ)) w =
      mellin (horocycleMean (pseudoEisenstein ψ)) w -
        residueConst ψ * mellin (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ)) w := by
    rw [mellin, mellin, mellin, ← integral_const_mul, ← integral_sub hA]
    · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [smul_eq_mul]
      ring
    · refine hE.congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      ring
  rw [hsplit, hmA, mellin_exp_neg hw, regularPart_eq hw0, poleNumerator,
    Complex.Gamma_add_one w hw0, show -(w + 1) = -(w + 1) by rfl]
  field_simp
  ring

/-- **The contour shift.** Under a zero-free half-plane `Re z > θ` with polynomial growth of `1/ζ`,
`|A_ψ(y) - c| ≤ C y^{1 - θ/2 - ε}` on `(0, 1]`. -/
theorem norm_horocycleMean_sub_le_of_zeroFree (hψ : IsTest ψ a b) (ha : 1 < a) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0)
    (hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein ψ) y - residueConst ψ‖ ≤ C * y ^ (1 - θ / 2 - ε) := by
  have hψa : ∀ y, y < a → ψ y = 0 := fun y hy => hψ.eq_zero_of_le hy.le
  have hψb : ∀ y, b < y → ψ y = 0 := fun y hy => hψ.eq_zero_of_ge hy.le
  have ha0 : 0 < a := by linarith
  set A := horocycleMean (pseudoEisenstein ψ) with hAdef
  set c := residueConst ψ with hcdef
  set g : ℝ → ℂ := fun y => A y - c * ((Real.exp (-y) : ℝ) : ℂ) with hg
  have hΨ := mellinRegularStrip_regularPart hψ hθ0 hθ1 hZ hP
  set c' : ℝ := θ / 2 - 1 + ε with hc'
  have hc'1 : θ / 2 - 1 < c' := by linarith
  have hc'2 : c' < 2 := by linarith
  have h11 : θ / 2 - 1 < 1 := by linarith
  set K := (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖regularPart ψ ((c' : ℂ) + t * Complex.I)‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨B, -, hB⟩ := exists_norm_pseudoEisenstein_le hψ.continuous ha hψa hψb
  have hFc := continuous_pseudoEisenstein hψ.continuous ha0 hψa
  refine ⟨K + ‖c‖, by positivity, fun y hy hy1 => ?_⟩
  -- Mellin inversion for `g` at `Re w = 1`
  have hconv : MellinConvergent g 1 := by
    have h1 := mellinConvergent_horocycleMean hψ.continuous ha hψa hψb (s := 2) (by norm_num)
    have h2 := (mellinConvergent_exp_neg (w := 1) (by norm_num)).const_smul c
    norm_num at h1
    refine (h1.sub h2).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hg, smul_eq_mul]
    ring
  have hline : ∀ t : ℝ, mellin g ((1 : ℝ) + t * Complex.I) = regularPart ψ ((1 : ℝ) + t * Complex.I) := by
    intro t
    exact mellin_sub_exp_eq_regularPart hψ ha (by simp)
  have hvert : VerticalIntegrable (mellin g) 1 := by
    refine (hΨ.integrable_line h11 (by norm_num)).congr (Eventually.of_forall fun t => ?_)
    exact (hline t).symm
  have hcont : ContinuousAt g y :=
    (continuousAt_horocycleMean hFc hB hy).sub (continuousAt_const.mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt)
  have hinv := mellinInv_mellin_eq 1 g hy hconv hvert hcont
  have hinv' : mellinInv 1 (mellin g) y = mellinInv 1 (regularPart ψ) y := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [hline t]
  have hshift := hΨ.mellinInv_eq h11 (by norm_num) hc'1 hc'2 hy
  have hbound := norm_mellinInv_le (Ψ := regularPart ψ) c' hy
  have hgy : ‖g y‖ ≤ K * y ^ (1 - θ / 2 - ε) := by
    rw [← hinv, hinv', hshift]
    refine hbound.trans (le_of_eq ?_)
    rw [hK, show -c' = 1 - θ / 2 - ε by rw [hc']; ring]
    ring
  -- the cutoff `c e^{-y}` differs from `c` by at most `‖c‖ y`
  have hexp : ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ ≤ y := by
    rw [show ((Real.exp (-y) : ℝ) : ℂ) - 1 = ((Real.exp (-y) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
        have := Real.exp_le_one_iff.2 (by linarith : -y ≤ 0); linarith)]
    linarith [Real.add_one_le_exp (-y)]
  have hyp : y ≤ y ^ (1 - θ / 2 - ε) := by
    have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (show 1 - θ / 2 - ε ≤ 1 by linarith)
    simpa using this
  have hsplit : A y - c = g y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1) := by
    simp only [hg]
    ring
  rw [hsplit]
  calc ‖g y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1)‖
      ≤ ‖g y‖ + ‖c‖ * ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ K * y ^ (1 - θ / 2 - ε) + ‖c‖ * y ^ (1 - θ / 2 - ε) := by
        gcongr
        exact hexp.trans hyp
    _ = (K + ‖c‖) * y ^ (1 - θ / 2 - ε) := by ring

/-- The limit of the horocycle means: `c = 2 Q(1) ψ̃(-1) = (6/π) ∫_0^∞ ψ(y) y^{-2} dy`, the mean of
`F_ψ` over `SL₂(ℤ)\ℍ` for the probability measure `(3/π) dx dy/y²`. -/
theorem residueConst_eq (ψ : ℝ → ℂ) :
    residueConst ψ = 6 / Real.pi * mellin ψ (-1) := by
  have hQ : scatterQ 1 = 3 / Real.pi := by
    rw [scatterQ, show (2 : ℂ) * 1 - 1 = 1 by norm_num, show (2 : ℂ) * 1 = 2 by norm_num, xi_one,
      xi_two, completedRiemannZeta_eq_gammaℝ_mul two_ne_zero
        (Gammaℝ_ne_zero_of_re_pos (by norm_num)), riemannZeta_two, Gammaℝ_def]
    rw [show -(2 : ℂ) / 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num, Complex.Gamma_one,
      Complex.cpow_neg_one]
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
    ring
  rw [residueConst, hQ]
  ring

end Rate

/-! ## The three rates -/

theorem xi_ne_zero_of_one_lt_re {z : ℂ} (hz : 1 < z.re) : xi z ≠ 0 := by
  rw [Ne, xi_eq_zero_iff (by linarith) (fun h => by rw [h] at hz; simp at hz)]
  exact riemannZeta_ne_zero_of_one_lt_re hz

/-- **Horocycle equidistribution at rate `y^{1/2 - ε}`, unconditionally.** The means of every
smooth pseudo-Eisenstein series supported above height `1` converge to `(6/π)∫ φ(y) y^{-2} dy`. -/
theorem horocycle_rate {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤ C * y ^ (1 / 2 - ε) := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
  have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
  have h := norm_horocycleMean_sub_le_of_zeroFree hψ ha (θ := 1) zero_le_one le_rfl
    (fun z hz => xi_ne_zero_of_one_lt_re hz)
    (fun δ hδ d => ⟨1 + 1 / δ, 0, by positivity, fun z hz _ _ => by
      simpa using norm_inv_riemannZeta_le_of_le_re (by linarith : 1 < 1 + δ) hz⟩) hε hε1
  rwa [residueConst_eq, show (1 : ℝ) - 1 / 2 - ε = 1 / 2 - ε by ring] at h

/-- **Under the Riemann hypothesis the rate is `y^{3/4 - ε}`.** -/
theorem horocycle_rate_of_riemannHypothesis (hRH : RiemannHypothesis) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤ C * y ^ (3 / 4 - ε) := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
  have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
  have hZ : ∀ z : ℂ, 1 / 2 < z.re → xi z ≠ 0 := fun z hz h0 => by
    have := (riemannHypothesis_iff_xi_zero_re_eq_half.1 hRH) z h0
    linarith
  have hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, 1 / 2 + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
    intro δ hδ d
    obtain ⟨Kb, hKb, -, hbd⟩ := exists_invZeta_shift_data_of_rh hRH (δ := min δ (1 / 2))
      (lt_min hδ (by norm_num)) (by linarith [min_le_right δ (1 / 2)]) one_pos d
    refine ⟨2 * Kb, 1, by positivity, fun z hz1 hz2 hzt => ?_⟩
    have hmem : z ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2 + min δ (1 / 2)) d :=
      ⟨by linarith [min_le_left δ (1 / 2)], hz2⟩
    have hz1' : z ≠ 1 := fun h => by rw [h] at hzt; simp at hzt; linarith
    have h := hbd z hmem
    rw [Sieve.invZeta_eq_inv hz1', Real.rpow_one] at h
    calc ‖(riemannZeta z)⁻¹‖ ≤ Kb * (2 + |z.im|) := h
      _ ≤ Kb * (2 * |z.im|) := by gcongr; linarith
      _ = 2 * Kb * |z.im| ^ 1 := by ring
  have h := norm_horocycleMean_sub_le_of_zeroFree hψ ha (θ := 1 / 2) (by norm_num) (by norm_num)
    hZ hP hε hε1
  rwa [residueConst_eq, show (1 : ℝ) - 1 / 2 / 2 - ε = 3 / 4 - ε by ring] at h

/-- **Zagier's theorem for pseudo-Eisenstein test functions.** The Riemann hypothesis holds iff the
horocycle means of every smooth pseudo-Eisenstein series supported above height `1` converge at
rate `y^{3/4 - ε}` for every `ε > 0`. -/
theorem riemannHypothesis_iff_horocycle_rate :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 1 → ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε) := by
  refine ⟨fun hRH ε hε φ hφ hc hs => ?_, riemannHypothesis_of_horocycle_rate⟩
  obtain ⟨C, hC, h⟩ := horocycle_rate_of_riemannHypothesis hRH hφ hc hs
    (ε := min ε (1 / 2)) (lt_min hε (by norm_num)) (by linarith [min_le_right ε (1 / 2)])
  refine ⟨_, C, fun y hy hy1 => (h y hy hy1).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith [min_le_left ε (1 / 2)])) hC

end

end GaloisForLFunctions.BlackHoleRingdown
