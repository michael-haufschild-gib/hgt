import GaloisForLFunctions.RHTower.WeilPolarConeExtremePoint
import GaloisForLFunctions.HTGeometry.HamburgerLogResidue

/-!
# `Λ` is an exposed point of the polar Weil cone

Let `P_c g = g − α_c (g(· − c) + g(· + c))` with `α_c = 1/(2 cosh(c/2))` be the polar second
difference (`polarShift`), and `K = Φ ⋆ Φ̃` the autocorrelation of Riemann's kernel. Put
`ℓ_c(v) = T_v(P_c P_c K) = Σ_{n ≥ 2} v(n) n^{−1/2} ((P_c P_c K)(log n) + (P_c P_c K)(−log n))`.

**Theorem** (`weilPolarCone_exposed_at_vonMangoldt`). For every polar Weil-positive `lam`, and every
`c ≥ 0`, `ℓ_c(lam − Λ) ≤ 0`. If `ℓ_{c_k}(lam − Λ) = 0` along a sequence `c_k → 0⁺`, then
`lam = Λ` on `n ≥ 2`. In particular, `ℓ̄ = Σ_k 2^{−k} ℓ_{1/(k+1)}` exposes `Λ`. No growth hypothesis
is needed.

* **Inequality.** `P_c(Φχ_L)` is polar and near-null for the zero side, and its autocorrelation is
  `P_c P_c (Φχ_L ⋆ Φχ_L~)`.
* **Equality.** The first variation along `P_c(Φχ_L) + εH` vanishes for both signs of `ε`. So
  `∫ H · P_c G_w = 0` for every polar `H`, which confines `G_w` to
  `ν y (e₊ − e₋) + A (e₊ + e₋)` (`exists_weightKernelTransform_form_of_polarShift`).
* **The two log-coefficients.** The theta primitive of `1 ⋆ w` then satisfies the odd theta relation
  with `log x` and `log² x` terms of coefficients `(A − ν)/2` and `ν/8`. Hamburger's residue at `0`
  with logarithms (`quadratic_log_coeffs_eq_zero_of_odd_coeffTheta_relation`) kills both. The
  density bound of the two-sided case is not needed.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23 GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The log-coefficients of the theta primitive -/

/-- **A theta primitive with log-power terms has none.** If the theta primitive of `1 ⋆ w'` has
the form `(ν/2) y² (e₊ + e₋) + (A − ν) y (e₊ − e₋) + C₊ e₊ + C₋ e₋`, then `ν = A = 0`. -/
theorem eq_zero_of_atomCuspSeries_form {w : ℕ → ℝ} (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    {ν A Cp Cm : ℝ}
    (hF : ∀ y, atomCuspSeries w 0 y + atomCuspSeries w 0 (-y) =
      ν / 2 * (y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2)))) +
        (A - ν) * (y * (Real.exp (y / 2) - Real.exp (-(y / 2)))) +
        Cp * Real.exp (y / 2) + Cm * Real.exp (-(y / 2))) :
    ν = 0 ∧ A = 0 := by
  set a := oneConvWeight (restrictAtoms w) with hadef
  set a' : ℕ → ℂ := fun k => (a k : ℂ) with ha'
  have hw2' : Summable fun n : ℕ => |restrictAtoms w (n + 1)| / ((n : ℝ) + 1) ^ (2 : ℝ) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
      (summable_rpow_two_of_div_sq hw2)
    unfold restrictAtoms
    split_ifs
    · exact le_rfl
    · rw [abs_zero, zero_div]; positivity
  have ha'sum : Summable fun n : ℕ => ‖a' (n + 1)‖ / ((n : ℝ) + 1) ^ (2 : ℝ) := by
    refine (summable_oneConvWeight_div_rpow_two hw2').congr fun n => ?_
    simp only [ha', Complex.norm_real, Real.norm_eq_abs, hadef]
  set T : ℝ → ℝ := fun x => ∑' k : ℕ, a (k + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * x) with hT
  have hθ : ∀ x : ℝ, coeffTheta a' x = (T x : ℂ) := by
    intro x
    rw [coeffTheta, hT, Complex.ofReal_tsum]
    refine tsum_congr fun k => ?_
    simp only [ha']; push_cast; ring_nf
  have hS : ∀ u, atomCuspSeries w 0 u = Real.exp (u / 2) * T (Real.exp (2 * u)) := fun u => by
    show weightedCuspSeries a 1 u = _
    rw [weightedCuspSeries_one_eq]
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a' x =
      -((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a' x⁻¹) +
        logQuadPoly Cp ((A - ν) / 2) (ν / 8) (Real.log x) +
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * logQuadPoly Cm (-((A - ν) / 2)) (ν / 8) (Real.log x) := by
    intro x hx
    set y := Real.log x / 2 with hy
    have hlogx : Real.log x = 2 * y := by rw [hy]; ring
    have hx2 : Real.exp (2 * y) = x := by rw [← hlogx, Real.exp_log hx]
    have hx2' : Real.exp (2 * (-y)) = x⁻¹ := by
      rw [show 2 * (-y) = -(2 * y) by ring, Real.exp_neg, hx2]
    have hrel := hF y
    rw [hS y, hS (-y), hx2, hx2', show -y / 2 = -(y / 2) by ring] at hrel
    have hpow : ((x : ℂ) ^ (-(1 / 2 : ℂ))) = ((Real.exp (-y) : ℝ) : ℂ) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hx.le, Real.rpow_def_of_pos hx, hlogx]
      congr 1; ring_nf
    have hE1 : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
    have hE2 : Real.exp (-(y / 2)) * Real.exp (-(y / 2)) = Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have hreal : T x = -(Real.exp (-y) * T x⁻¹) +
        (ν / 8 * (2 * y) ^ 2 + (A - ν) / 2 * (2 * y) + Cp) +
        Real.exp (-y) * (ν / 8 * (2 * y) ^ 2 - (A - ν) / 2 * (2 * y) + Cm) := by
      have h := congrArg (fun t => Real.exp (-(y / 2)) * t) hrel
      have e1 : Real.exp (-(y / 2)) * (Real.exp (y / 2) * T x + Real.exp (-(y / 2)) * T x⁻¹) =
          T x + Real.exp (-y) * T x⁻¹ := by
        rw [mul_add, ← mul_assoc, hE1, ← mul_assoc, hE2, one_mul]
      have e2 : Real.exp (-(y / 2)) *
          (ν / 2 * (y ^ 2 * (Real.exp (y / 2) + Real.exp (-(y / 2)))) +
            (A - ν) * (y * (Real.exp (y / 2) - Real.exp (-(y / 2)))) +
            Cp * Real.exp (y / 2) + Cm * Real.exp (-(y / 2))) =
          (ν / 8 * (2 * y) ^ 2 + (A - ν) / 2 * (2 * y) + Cp) +
            Real.exp (-y) * (ν / 8 * (2 * y) ^ 2 - (A - ν) / 2 * (2 * y) + Cm) := by
        linear_combination (ν / 2 * y ^ 2 + (A - ν) * y + Cp) * hE1 +
          (ν / 2 * y ^ 2 - (A - ν) * y + Cm) * hE2
      rw [e1, e2] at h
      linarith
    rw [hθ x, hθ x⁻¹, hpow, hreal, hlogx]
    unfold logQuadPoly
    push_cast
    ring
  obtain ⟨h2, h1⟩ := quadratic_log_coeffs_eq_zero_of_odd_coeffTheta_relation ha'sum htheta
  have hν : ν = 0 := by
    have : ((ν / 8 : ℝ) : ℂ) = 0 := by push_cast; exact h2
    have := Complex.ofReal_eq_zero.mp this
    linarith
  refine ⟨hν, ?_⟩
  have : (((A - ν) / 2 : ℝ) : ℂ) = 0 := by push_cast; exact h1
  have := Complex.ofReal_eq_zero.mp this
  linarith

/-! ## The autocorrelation of the polar near-null vector -/

theorem crossCorr_polarRiemannDifferenceReal_right (L c : ℝ) {U : ℝ → ℝ} (hU : Continuous U)
    (y : ℝ) :
    crossCorr U (polarRiemannDifferenceReal L c) y =
      polarShift c (crossCorr U (truncatedRiemannKernelReal L)) y := by
  set V := truncatedRiemannKernelReal L
  have hV := continuous_truncatedRiemannKernelReal L
  have hVc := hasCompactSupport_truncatedRiemannKernelReal L
  have i0 := integrable_mul_translate_right hU hV hVc y
  have i1 : Integrable fun t => polarWeight c * (U t * V (t - (y + c))) :=
    (integrable_mul_translate_right hU hV hVc (y + c)).const_mul _
  have i2 : Integrable fun t => polarWeight c * (U t * V (t - (y - c))) :=
    (integrable_mul_translate_right hU hV hVc (y - c)).const_mul _
  have hA : Integrable fun t => U t * V (t - y) - polarWeight c * (U t * V (t - (y + c))) :=
    i0.sub i1
  have e : crossCorr U (polarRiemannDifferenceReal L c) y =
      (∫ t, U t * V (t - y)) - (∫ t, polarWeight c * (U t * V (t - (y + c)))) -
        ∫ t, polarWeight c * (U t * V (t - (y - c))) := by
    rw [← integral_sub i0 i1, ← integral_sub hA i2]
    unfold crossCorr polarRiemannDifferenceReal
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [V]
    rw [show t - y - c = t - (y + c) by ring, show t - y - -c = t - (y - c) by ring]
    ring
  rw [e, integral_const_mul, integral_const_mul]
  unfold polarShift crossCorr
  ring

/-- `(P_c U_L) ⋆ (P_c U_L)~ = P_c P_c (U_L ⋆ U_L~)`. -/
theorem crossCorr_polarRiemannDifferenceReal_self (L c y : ℝ) :
    crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c) y =
      polarShift c (polarShift c (crossCorr (truncatedRiemannKernelReal L)
        (truncatedRiemannKernelReal L))) y := by
  rw [crossCorr_polarRiemannDifferenceReal L c (continuous_polarRiemannDifferenceReal L c)
    (hasCompactSupport_polarRiemannDifferenceReal L c) y]
  have e : crossCorr (truncatedRiemannKernelReal L) (polarRiemannDifferenceReal L c) =
      polarShift c (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) :=
    funext fun z => crossCorr_polarRiemannDifferenceReal_right L c
      (continuous_truncatedRiemannKernelReal L) z
  rw [e]

/-- The exposing kernel `P_c P_c K`, with `K = Φ ⋆ Φ̃`. -/
def polarExposingKernel (c : ℝ) : ℝ → ℝ := polarShift c (polarShift c riemannKernelAutocorr)

theorem abs_polarShift_polarShift_le {c K : ℝ} (hc : 0 ≤ c) {g : ℝ → ℝ}
    (hg : ∀ y, |g y| ≤ K * Real.exp (-(2 * |y|))) (y : ℝ) :
    |polarShift c (polarShift c g) y| ≤
      (K * (1 + 2 * polarWeight c * Real.exp (2 * c)) ^ 2) * Real.exp (-(2 * |y|)) := by
  have h2 := abs_polarShift_le_of_decay hc (abs_polarShift_le_of_decay hc hg) y
  calc _ ≤ _ := h2
    _ = _ := by ring

/-- `T_w(P_c U_L ⋆ (P_c U_L)~) → ℓ_c(w)` at rate `e^{−2L}`. -/
theorem exists_abs_atomPairing_polarAutocorr_sub_le {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {c : ℝ} (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |atomPairing w (crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)) -
        atomPairing w (polarExposingKernel c)| ≤ K * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hD, hK⟩ := exists_riemannKernelAutocorr_decay
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (1 + 2 * polarWeight c * Real.exp (2 * c)) ^ 2 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  obtain ⟨Sw, hSw⟩ : ∃ Sw : ℝ, Sw = ∑' n : ℕ, |w n| / (n : ℝ) ^ 2 := ⟨_, rfl⟩
  have hSw0 : 0 ≤ Sw := by rw [hSw]; exact tsum_nonneg fun _ => by positivity
  refine ⟨2 * (C₁ * m) * Sw, by positivity, fun L => ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-(2 * (L - 1))) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  set A := crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) with hAdef
  have hAeq : crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c) =
      polarShift c (polarShift c A) :=
    funext fun y => crossCorr_polarRiemannDifferenceReal_self L c y
  have hdiff : ∀ y, |A y - riemannKernelAutocorr y| ≤ (C₁ * E) * Real.exp (-(2 * |y|)) :=
    fun y => by rw [hE]; exact hD L y
  have hAbd : ∀ y, |A y| ≤ (C₂ + C₁ * E) * Real.exp (-(2 * |y|)) := fun y => by
    have h1 := hdiff y
    have h2 := hK y
    have h3 : |A y| ≤ |A y - riemannKernelAutocorr y| + |riemannKernelAutocorr y| := by
      have := abs_add_le (A y - riemannKernelAutocorr y) (riemannKernelAutocorr y)
      rwa [sub_add_cancel] at this
    nlinarith
  have hPA := abs_polarShift_polarShift_le hc hAbd
  have hPK := abs_polarShift_polarShift_le hc hK
  have hPD := abs_polarShift_polarShift_le hc hdiff
  obtain ⟨sA, -⟩ := summable_atomPairing_of_decay hw2 hPA
  obtain ⟨sK, -⟩ := summable_atomPairing_of_decay hw2 hPK
  obtain ⟨-, bD⟩ := summable_atomPairing_of_decay hw2 hPD
  have hsub : atomPairing w (polarShift c (polarShift c A)) - atomPairing w (polarExposingKernel c) =
      atomPairing w (polarShift c (polarShift c fun y => A y - riemannKernelAutocorr y)) := by
    unfold atomPairing polarExposingKernel
    rw [← sA.tsum_sub sK]
    refine tsum_congr fun n => ?_
    simp only [polarShift]
    ring
  rw [hAeq, hsub]
  rw [← hSw, ← hm] at bD
  calc _ ≤ 2 * (C₁ * E * m) * Sw := bD
    _ = 2 * (C₁ * m) * Sw * Real.exp (-(2 * (L - 1))) := by rw [← hE]; ring

/-! ## The exposing inequality -/

theorem weilPositive_add_sub_vonMangoldt {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
      (lam n - ArithmeticFunction.vonMangoldt n) := by
  have e : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
      (lam n - ArithmeticFunction.vonMangoldt n)) = lam := funext fun n => by ring
  rw [e]; exact hW

/-- **Supporting inequality.** Every polar Weil-positive `lam` satisfies `ℓ_c(lam − Λ) ≤ 0`
for every `c ≥ 0`. -/
theorem atomPairing_polarExposingKernel_nonpos {lam : ℕ → ℝ} (hW : WeilPositive lam) {c : ℝ}
    (hc : 0 ≤ c) :
    atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) (polarExposingKernel c) ≤ 0 := by
  have hp := weilPositive_add_sub_vonMangoldt hW
  have hw2 := summable_sub_vonMangoldt_div_sq_of_weilPositive hW
  obtain ⟨K, hK0, hK⟩ := exists_abs_atomPairing_polarAutocorr_sub_le hw2 hc
  have hT0 : ∀ L, atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)) ≤
        (5 / 4) * zetaInvSqSum * (3 * truncatedRiemannTailEnergy L) ^ 2 := by
    intro L
    have h := atomPairing_polarPerturbed_le hp L hc 0 (H := fun _ => 0) contDiff_const
      HasCompactSupport.zero (by simp [paperFT]) (by simp [paperFT])
    simp only [zero_mul, add_zero, abs_zero] at h
    exact h
  by_contra hpos'
  have hpos := lt_of_not_ge hpos'
  set ℓ := atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) (polarExposingKernel c)
  obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := ℓ / 36) (by positivity)
  obtain ⟨L₂, hL₂⟩ := exists_forall_mul_exp_le hK0 (δ := ℓ / 4) (by positivity)
  have h1 := hT0 (max L₁ L₂)
  have h2 := hK (max L₁ L₂)
  have h3 := hL₁ (max L₁ L₂) (le_max_left _ _)
  have h4 := hL₂ (max L₁ L₂) (le_max_right _ _)
  have e : (5 / 4) * zetaInvSqSum * (3 * truncatedRiemannTailEnergy (max L₁ L₂)) ^ 2 =
      9 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy (max L₁ L₂) ^ 2) := by ring
  have h2' := (abs_le.mp h2).1
  linarith

/-! ## Equality forces the first variation to vanish -/

/-- **Equality case.** If `ℓ_c(lam − Λ) = 0` for a polar Weil-positive `lam`, then the first
variation of `lam` at `P_c Φ` vanishes against every real polar test. -/
theorem atomPairing_polarShift_eq_zero_of_polarExposing {lam : ℕ → ℝ} (hW : WeilPositive lam)
    {c : ℝ} (hc : 0 ≤ c)
    (h0 : atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (polarExposingKernel c) = 0) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H)
    (hH1 : paperFT (fun u => (H u : ℂ)) (I / 2) = 0)
    (hH2 : paperFT (fun u => (H u : ℂ)) (-(I / 2)) = 0) :
    atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (polarShift c (crossCorr riemannKernelReal H)) = 0 := by
  set w : ℕ → ℝ := fun n => lam n - ArithmeticFunction.vonMangoldt n with hw
  have hp : WeilPositive fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n :=
    weilPositive_add_sub_vonMangoldt hW
  have hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2 :=
    summable_sub_vonMangoldt_div_sq_of_weilPositive hW
  obtain ⟨K, hK0, hK⟩ := exists_abs_atomPairing_polarShift_sub_le hw2 hc hH.continuous hHc
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_abs_atomPairing_polarAutocorr_sub_le hw2 hc
  set T := atomPairing w (polarShift c (crossCorr riemannKernelReal H)) with hT
  by_contra hT0
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = |T| := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; exact abs_pos.mpr hT0
  obtain ⟨EH, hEH⟩ : ∃ EH : ℝ, EH = testEnergy H := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (5 / 4) * zetaInvSqSum := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by have := zetaInvSqSum_nonneg; rw [hq]; positivity
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℝ, T2 = atomPairing w (crossCorr H H) := ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℝ, M₂ = q * (2 * EH ^ 2) + |T2| := ⟨_, rfl⟩
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = τ / (2 * M₂ + 2) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := ε * τ / 144) (by positivity)
  obtain ⟨L₂, hL₂⟩ := exists_forall_mul_exp_le hK0 (δ := τ / 8) (by positivity)
  obtain ⟨L₃, hL₃⟩ := exists_forall_mul_exp_le hK₀0 (δ := ε * τ / 8) (by positivity)
  set L := max (max L₁ L₂) L₃ with hL
  have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) (le_max_left _ _)
  have hL2 : L₂ ≤ L := le_trans (le_max_right _ _) (le_max_left _ _)
  have hL3 : L₃ ≤ L := le_max_right _ _
  obtain ⟨EL, hEL⟩ : ∃ EL : ℝ, EL = truncatedRiemannTailEnergy L := ⟨_, rfl⟩
  have hE0 : 0 ≤ EL := by rw [hEL]; exact truncatedRiemannTailEnergy_nonneg L
  have hELq : q * EL ^ 2 ≤ ε * τ / 144 := by rw [hq, hEL]; exact hL₁ L hL1
  have hdiff : |atomPairing w (crossCorr (polarRiemannDifferenceReal L c) H) - T| ≤ τ / 8 :=
    (hK L).trans (hL₂ L hL2)
  have hT0bd := (hK₀ L).trans (hL₃ L hL3)
  rw [h0, sub_zero] at hT0bd
  set D := polarRiemannDifferenceReal L c with hD
  have hDc := continuous_polarRiemannDifferenceReal L c
  have hDs := hasCompactSupport_polarRiemannDifferenceReal L c
  obtain ⟨T0, hT0⟩ : ∃ T0 : ℝ, T0 = atomPairing w (crossCorr D D) := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T1 : ℝ, T1 = atomPairing w (crossCorr D H) := ⟨_, rfl⟩
  have hT0lo : -(ε * τ / 8) ≤ T0 := by rw [hT0]; exact (abs_le.mp hT0bd).1
  have bp' := atomPairing_polarPerturbed_le hp L hc ε hH hHc hH1 hH2
  rw [atomPairing_add_smul_expand w hDc hDs hH.continuous hHc ε, abs_of_pos hεpos] at bp'
  have bm' := atomPairing_polarPerturbed_le hp L hc (-ε) hH hHc hH1 hH2
  rw [atomPairing_add_smul_expand w hDc hDs hH.continuous hHc (-ε), abs_neg,
    abs_of_pos hεpos] at bm'
  rw [← hT0, ← hT1, ← hT2, ← hq, ← hEL, ← hEH] at bp' bm'
  have hsq : (3 * EL + ε * EH) ^ 2 ≤ 2 * (9 * EL ^ 2) + 2 * (ε ^ 2 * EH ^ 2) := by
    nlinarith [sq_nonneg (3 * EL - ε * EH)]
  have hb : q * (3 * EL + ε * EH) ^ 2 ≤ 18 * (q * EL ^ 2) + ε ^ 2 * (q * (2 * EH ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hsq hq0
    have e : q * (2 * (9 * EL ^ 2) + 2 * (ε ^ 2 * EH ^ 2)) =
        18 * (q * EL ^ 2) + ε ^ 2 * (q * (2 * EH ^ 2)) := by ring
    linarith
  have hT2abs : -(ε ^ 2 * |T2|) ≤ ε ^ 2 * T2 := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le T2) (sq_nonneg ε)
    linarith
  have hnε : (-ε) ^ 2 = ε ^ 2 := by ring
  rw [hnε] at bm'
  have hT1b : 2 * ε * |T1| ≤ 18 * (q * EL ^ 2) + ε * τ / 8 + ε ^ 2 * M₂ := by
    have e : ε ^ 2 * M₂ = ε ^ 2 * (q * (2 * EH ^ 2)) + ε ^ 2 * |T2| := by rw [hM₂]; ring
    rw [e]
    rcases le_or_gt 0 T1 with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have hT1' : |T1| ≤ τ / 8 + ε * M₂ / 2 := by
    have h1 : 18 * (q * EL ^ 2) ≤ ε * τ / 8 := by linarith
    have : 2 * ε * |T1| ≤ 2 * ε * (τ / 8 + ε * M₂ / 2) := by
      have e : 2 * ε * (τ / 8 + ε * M₂ / 2) = ε * τ / 4 + ε ^ 2 * M₂ := by ring
      linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hεM : ε * M₂ ≤ τ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : τ / 2 * (2 * M₂ + 2) = τ * M₂ + τ := by ring
    linarith
  have htri : |T| - |T1| ≤ |T - T1| := abs_sub_abs_le_abs_sub T T1
  rw [← hT1] at hdiff
  rw [abs_sub_comm] at htri
  linarith

/-! ## `Λ` is exposed -/

/-- **Exposedness along a sequence.** If `ℓ_{c_k}(lam − Λ) = 0` for a polar Weil-positive `lam`
along shifts `c_k → 0⁺`, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositive_of_polarExposing_eq_zero {lam : ℕ → ℝ}
    (hW : WeilPositive lam) {c : ℕ → ℝ} (hc0 : ∀ k, 0 < c k) (hc : Tendsto c atTop (𝓝 0))
    (h0 : ∀ k, atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (polarExposingKernel (c k)) = 0) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hw2 := summable_sub_vonMangoldt_div_sq_of_weilPositive hW
  have hA : ∀ k (H : ℝ → ℝ), ContDiff ℝ 2 H → HasCompactSupport H →
      paperFT (fun u => (H u : ℂ)) (I / 2) = 0 → paperFT (fun u => (H u : ℂ)) (-(I / 2)) = 0 →
      ∫ s, H s * polarShift (c k)
        (weightKernelTransform fun n => lam n - ArithmeticFunction.vonMangoldt n) s = 0 := by
    intro k H hH hHc h1 h2
    rw [← atomPairing_polarShift_eq_integral hw2 (c k) hH.continuous hHc]
    exact atomPairing_polarShift_eq_zero_of_polarExposing hW (hc0 k).le (h0 k) hH hHc h1 h2
  obtain ⟨ν, A, Cp, Cm, hG, hF⟩ := exists_weightKernelTransform_form_of_polarShift hw2 hc0 hc hA
  obtain ⟨hν, hA0⟩ := eq_zero_of_atomCuspSeries_form hw2 hF
  have hGz : ∀ y, weightKernelTransform (fun n => lam n - ArithmeticFunction.vonMangoldt n) y = 0 :=
    fun y => by rw [hG y, hν, hA0]; ring
  intro n hn
  have h := eq_zero_of_weightKernelTransform_eq_zero hw2 hGz n hn
  linarith

theorem polarWeight_le_half (c : ℝ) : polarWeight c ≤ 1 / 2 := by
  unfold polarWeight
  have := Real.one_le_cosh (c / 2)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `ℓ̄(v) = Σ_k 2^{−k} ℓ_{1/(k+1)}(v)`. -/
def polarExposingFunctional (v : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (1 / 2 : ℝ) ^ k * atomPairing v (polarExposingKernel (1 / ((k : ℝ) + 1)))

theorem summable_polarExposingFunctional {v : ℕ → ℝ}
    (hv2 : Summable fun n : ℕ => |v n| / (n : ℝ) ^ 2) :
    Summable fun k : ℕ => (1 / 2 : ℝ) ^ k * atomPairing v (polarExposingKernel (1 / ((k : ℝ) + 1))) := by
  obtain ⟨-, C₂, -, hC₂, -, hK⟩ := exists_riemannKernelAutocorr_decay
  set Sv := ∑' n : ℕ, |v n| / (n : ℝ) ^ 2
  have hbd : ∀ k : ℕ, |atomPairing v (polarExposingKernel (1 / ((k : ℝ) + 1)))| ≤
      2 * (C₂ * (1 + Real.exp 2) ^ 2) * Sv := by
    intro k
    have hc : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    have hc1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hm : (1 + 2 * polarWeight (1 / ((k : ℝ) + 1)) * Real.exp (2 * (1 / ((k : ℝ) + 1)))) ^ 2 ≤
        (1 + Real.exp 2) ^ 2 := by
      have h1 := polarWeight_le_half (1 / ((k : ℝ) + 1))
      have h2 : Real.exp (2 * (1 / ((k : ℝ) + 1))) ≤ Real.exp 2 :=
        Real.exp_le_exp.mpr (by linarith)
      have h3 := polarWeight_pos (1 / ((k : ℝ) + 1))
      have h4 : 0 ≤ 2 * polarWeight (1 / ((k : ℝ) + 1)) * Real.exp (2 * (1 / ((k : ℝ) + 1))) := by
        positivity
      have h5 : 2 * polarWeight (1 / ((k : ℝ) + 1)) * Real.exp (2 * (1 / ((k : ℝ) + 1))) ≤
          Real.exp 2 := by nlinarith [Real.exp_pos (2 * (1 / ((k : ℝ) + 1)))]
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hdec : ∀ y, |polarExposingKernel (1 / ((k : ℝ) + 1)) y| ≤
        (C₂ * (1 + Real.exp 2) ^ 2) * Real.exp (-(2 * |y|)) := by
      intro y
      refine (abs_polarShift_polarShift_le hc hK y).trans ?_
      gcongr
    exact (summable_atomPairing_of_decay hv2 hdec).2
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).mul_right (2 * (C₂ * (1 + Real.exp 2) ^ 2) * Sv)) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hbd k) (by positivity)

/-- **`Λ` is an exposed point of the polar Weil cone.** Every polar Weil-positive `lam` has
`ℓ̄(lam − Λ) ≤ 0`, and equality forces `lam = Λ` on `n ≥ 2`. Unconditional, no growth hypothesis. -/
theorem weilPolarCone_exposed_at_vonMangoldt {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    polarExposingFunctional (fun n => lam n - ArithmeticFunction.vonMangoldt n) ≤ 0 ∧
      (polarExposingFunctional (fun n => lam n - ArithmeticFunction.vonMangoldt n) = 0 →
        ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) := by
  have hw2 := summable_sub_vonMangoldt_div_sq_of_weilPositive hW
  have hterm : ∀ k : ℕ, (1 / 2 : ℝ) ^ k * atomPairing
      (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (polarExposingKernel (1 / ((k : ℝ) + 1))) ≤ 0 := fun k =>
    mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (atomPairing_polarExposingKernel_nonpos hW (by positivity))
  refine ⟨tsum_nonpos hterm, fun h0 => ?_⟩
  have hs := summable_polarExposingFunctional hw2
  have hneg : HasSum (fun k : ℕ => -((1 / 2 : ℝ) ^ k * atomPairing
      (fun n => lam n - ArithmeticFunction.vonMangoldt n)
      (polarExposingKernel (1 / ((k : ℝ) + 1))))) 0 := by
    have := hs.hasSum.neg
    unfold polarExposingFunctional at h0
    rwa [h0, neg_zero] at this
  have hz := (hasSum_zero_iff_of_nonneg fun k => neg_nonneg.mpr (hterm k)).mp hneg
  refine eq_vonMangoldt_of_weilPositive_of_polarExposing_eq_zero hW
    (c := fun k => 1 / ((k : ℝ) + 1)) (fun k => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat fun k => ?_
  have hk := congrFun hz k
  simp only [Pi.zero_apply, neg_eq_zero] at hk
  rcases mul_eq_zero.mp hk with h | h
  · exact absurd h (by positivity)
  · exact h

/-- **RH as an extremal value on the polar cone.** RH holds iff some polar Weil-positive `lam`
has `ℓ̄(lam) ≥ ℓ̄(Λ)`. Such a `lam` equals `Λ`. -/
theorem riemannHypothesis_iff_exists_weilPositive_polarExposing_nonneg :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositive lam ∧
      0 ≤ polarExposingFunctional (fun n => lam n - ArithmeticFunction.vonMangoldt n) := by
  constructor
  · intro hRH
    refine ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      riemannHypothesis_iff_weilPositive_vonMangoldt.mp hRH, ?_⟩
    simp only [sub_self]
    unfold polarExposingFunctional atomPairing
    simp
  · rintro ⟨lam, hW, hge⟩
    obtain ⟨hle, heq⟩ := weilPolarCone_exposed_at_vonMangoldt hW
    have h := heq (le_antisymm hle hge)
    exact riemannHypothesis_iff_weilPositive_vonMangoldt.mpr
      (weilPositive_congr (fun n hn => h n hn) hW)

end

end RHTower
