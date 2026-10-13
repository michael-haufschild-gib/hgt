import GaloisForLFunctions.RHTower.CosDilationKernelMellinInversion
import GaloisForLFunctions.RHTower.ExactNullCertificateLogRoomGrowth
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import Mathlib.Analysis.Complex.RemovableSingularity
import GaloisForLFunctions.RHTower.GammaRealHalfPlane
import GaloisForLFunctions.HTGeometry.GammaReciprocalExpBound


/-!
# Blind Ξ²-divisible tests from smooth multipliers: the corpus kernel is `Cf ⋆ f`

Let `f` be smooth, supported in `[α, β]` with `0 < α ≤ β`, and `𝓜f(1) = ∫ f = 0`. Put

`R_f(s) = 4 𝓜f(s) 𝓜f(1−s) / (s²(s−1)² Γ_ℝ(s) Γ_ℝ(1−s))`
(`cosDilationCertMultiplier`, written with the removable singularity at `s = 1` resolved),

so that `archXi(s)² R_f(s) = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜f(s) 𝓜f(1−s)`
(`archXi_sq_mul_cosDilationCertMultiplier`) and, on the critical line,
`Ξ(t)² R_f(½+it) = |ζ(½+it)|² |𝓜f(½+it)|²`.

* `R_f` is holomorphic on `Re s > 0` (`differentiableAt_cosDilationCertMultiplier`).
* Strip bounds on `½ ≤ Re s ≤ 3`: `‖archXi² R_f‖, ‖ξ² R_f‖ ≤ C/(1 + (Im s)²)`
  (`exists_bound_archXi_sq_mul_cosDilationCertMultiplier`,
  `exists_bound_xi_sq_mul_cosDilationCertMultiplier`), from the polynomial growth of
  `Γ_ℝ(s)/Γ_ℝ(1−s)` (`exists_bound_norm_Gammaℝ_div_strip`, by Stirling-type bounds and the
  reflection formula), the polynomial growth of `ζ`, and the all-order Mellin decay of `f`
  (`IsTest.exists_norm_pow_mul_norm_mellin_le`).
* The corpus kernel `Ψ_{R_f} = 𝓜⁻¹[archXi² R_f]` is the cosine–dilation kernel `Cf ⋆ f`
  (`certKernel_cosDilationCertMultiplier`).
* **Blindness** (`logNode_blind_iff_cosDilationKernel_vanishes`): the positive test with
  `ĝ = Ξ² R_f` vanishes at every `log n`, `n ≥ 2`, iff `(Cf ⋆ f)(n) = 0` for every integer `n ≥ 2`,
  iff (by `tsum_dilationAutocorr_abs_eq`) the even dilation autocorrelation of `f` has
  `1`-periodization `Ψ_f(0) + 2Ψ_f(1) cos 2πx`.
-/

open MeasureTheory Set Real
open scoped ContDiff

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.TestFunctionPerron in
/-- **All-order Mellin decay of a test function on a vertical strip.** -/
theorem IsTest.exists_norm_pow_mul_norm_mellin_le (k : ℕ) :
    ∀ {g : ℝ → ℂ} {a b : ℝ}, IsTest g a b → ∀ R : ℝ,
      ∃ C : ℝ, ∀ s : ℂ, |s.re - 1| ≤ R → ‖s‖ ^ k * ‖mellin g s‖ ≤ C := by
  induction k with
  | zero =>
    intro g a b hg R
    obtain ⟨C, hC0, hC⟩ := hg.exists_norm_mellin_le_decay R
    refine ⟨C, fun s hs => ?_⟩
    rw [pow_zero, one_mul]
    refine (hC s hs).trans ?_
    exact div_le_self hC0 (by nlinarith [sq_nonneg s.im])
  | succ k ih =>
    intro g a b hg R
    obtain ⟨C, hC⟩ := ih hg.eulerDeriv R
    refine ⟨C, fun s hs => ?_⟩
    have h := hC s hs
    rw [hg.mellin_eulerDeriv, norm_mul, norm_neg] at h
    calc ‖s‖ ^ (k + 1) * ‖mellin g s‖ = ‖s‖ ^ k * (‖s‖ * ‖mellin g s‖) := by ring
      _ ≤ C := h

/-- Reflection for non-real arguments: `Γ(z)⁻¹ = Γ(1−z) sin(πz)/π`. -/
theorem inv_Gamma_eq_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (π * z) / π := by
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    have h2 := congrArg Complex.im hk
    simp [Real.pi_ne_zero] at h2
    exact hz h2
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have href := Complex.Gamma_mul_Gamma_one_sub z
  have hG : Complex.Gamma z ≠ 0 := by
    intro h; rw [h, zero_mul] at href
    exact (div_ne_zero hpi hsin) href.symm
  field_simp
  rw [mul_comm, href]
  field_simp

/-- **Polynomial growth of `Γ_ℝ(s)/Γ_ℝ(1−s)` on the strip `½ ≤ Re s ≤ 3`.** -/
theorem exists_bound_norm_Gammaℝ_div_strip :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → 2 ≤ |s.im| →
      ‖Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)‖ ≤ C * |s.im| ^ N := by
  obtain ⟨C₁, N₁, hC₁0, hC₁⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := 1 / 4) (by norm_num) (3 / 2)
  obtain ⟨C₂, N₂, hC₂0, hC₂⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := 3 / 4) (by norm_num) 2
  refine ⟨C₁ * C₂, N₁ + N₂, by positivity, fun s hσ1 hσ2 ht => ?_⟩
  set σ := s.re with hσ
  set t := s.im with htdef
  have hs : s = (σ : ℂ) + (t : ℂ) * Complex.I := (Complex.re_add_im s).symm
  have ht2 : 1 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
  have hA : ‖Complex.Gamma (s / 2)‖ ≤ C₁ * |t / 2| ^ N₁ * Real.exp (-(π * |t / 2| / 2)) := by
    have h := hC₁ (σ / 2) (t / 2) (by linarith) (by linarith) ht2
    have e : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [e]; exact h
  have hB : ‖Complex.Gamma (1 - (1 - s) / 2)‖ ≤
      C₂ * |t / 2| ^ N₂ * Real.exp (-(π * |t / 2| / 2)) := by
    have h := hC₂ ((1 + σ) / 2) (t / 2) (by linarith) (by linarith) ht2
    have e : 1 - (1 - s) / 2 = (((1 + σ) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [e]; exact h
  have himz : ((1 - s) / 2).im ≠ 0 := by
    have : ((1 - s) / 2).im = -(t / 2) := by rw [hs]; simp; ring_nf
    rw [this]; intro h0
    have : |t / 2| = 0 := by rw [show t / 2 = 0 by linarith]; simp
    linarith
  have hsin : ‖Complex.sin (π * ((1 - s) / 2))‖ ≤ Real.exp (π * |t / 2|) := by
    refine (GaloisForLFunctions.HTGeometry.norm_sin_le_exp_abs_im _).trans (le_of_eq ?_)
    congr 1
    have : (↑π * ((1 - s) / 2)).im = -(π * (t / 2)) := by rw [hs]; simp; ring_nf
    rw [this, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
  have hpi1 : ‖(π : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp; linarith
  have hpi2 : ‖(π : ℂ) ^ ((1 - s) / 2)‖ ≤ π := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    calc π ^ ((1 - s) / 2).re ≤ π ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) ?_
          simp; linarith
      _ = π := Real.rpow_one π
  have hdecomp : Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) =
      (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * ((π : ℂ) ^ ((1 - s) / 2) *
        (Complex.Gamma (1 - (1 - s) / 2) * Complex.sin (π * ((1 - s) / 2)) / π)) := by
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv, mul_inv,
      ← inv_Gamma_eq_of_im_ne_zero himz]
    congr 1
    rw [← Complex.cpow_neg]
    congr 1
    ring_nf
  rw [hdecomp, norm_mul, norm_mul, norm_mul, norm_div, norm_mul]
  have hpin : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
  rw [hpin]
  have hpos1 : 0 ≤ ‖Complex.Gamma (s / 2)‖ := norm_nonneg _
  have hpos2 : 0 ≤ ‖Complex.Gamma (1 - (1 - s) / 2)‖ := norm_nonneg _
  have hpos3 : 0 ≤ ‖Complex.sin (π * ((1 - s) / 2))‖ := norm_nonneg _
  have hexp : Real.exp (-(π * |t / 2| / 2)) * Real.exp (-(π * |t / 2| / 2)) *
      Real.exp (π * |t / 2|) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have htt : |t / 2| ^ (N₁ + N₂) ≤ |t| ^ (N₁ + N₂) := by
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  have key : ‖(π : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ * (‖(π : ℂ) ^ ((1 - s) / 2)‖ *
      (‖Complex.Gamma (1 - (1 - s) / 2)‖ * ‖Complex.sin (π * ((1 - s) / 2))‖ / π)) ≤
      1 * (C₁ * |t / 2| ^ N₁ * Real.exp (-(π * |t / 2| / 2))) * (π *
        (C₂ * |t / 2| ^ N₂ * Real.exp (-(π * |t / 2| / 2)) * Real.exp (π * |t / 2|) / π)) := by
    gcongr
  calc _ ≤ 1 * (C₁ * |t / 2| ^ N₁ * Real.exp (-(π * |t / 2| / 2))) * (π *
        (C₂ * |t / 2| ^ N₂ * Real.exp (-(π * |t / 2| / 2)) * Real.exp (π * |t / 2|) / π)) := key
    _ = C₁ * C₂ * |t / 2| ^ (N₁ + N₂) *
        (Real.exp (-(π * |t / 2| / 2)) * Real.exp (-(π * |t / 2| / 2)) *
          Real.exp (π * |t / 2|)) := by
        field_simp; ring_nf
    _ = C₁ * C₂ * |t / 2| ^ (N₁ + N₂) := by rw [hexp, mul_one]
    _ ≤ C₁ * C₂ * |t| ^ (N₁ + N₂) := by gcongr

open RHTower.ExactNullDivisorTransfer

variable {f : ℝ → ℝ}

/-- The multiplier `R_f(s) = 4 𝓜f(s) 𝓜f(1−s) / (s²(s−1)² Γ_ℝ(s) Γ_ℝ(1−s))`, written with its
removable singularity at `s = 1` resolved: `𝓜f(s)/(s−1)` is the divided slope and
`1/((s−1)Γ_ℝ(1−s)) = −½ π^{(1−s)/2}/Γ((3−s)/2)`. -/
def cosDilationCertMultiplier (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  -2 * (π : ℂ) ^ ((1 - s) / 2) * dslope (mellin fun y : ℝ => (f y : ℂ)) 1 s *
    mellin (fun y : ℝ => (f y : ℂ)) (1 - s) * (Complex.Gamma ((3 - s) / 2))⁻¹ /
      (s ^ 2 * Complex.Gammaℝ s)

/-- **The multiplier is holomorphic on `Re s > 0`.** -/
theorem differentiableAt_cosDilationCertMultiplier (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (cosDilationCertMultiplier f) s := by
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  have hm : Differentiable ℂ (mellin fun y : ℝ => (f y : ℂ)) := fun s =>
    htest.differentiableAt_mellin s
  have hds : DifferentiableAt ℂ (dslope (mellin fun y : ℝ => (f y : ℂ)) 1) s :=
    ((Complex.differentiableOn_dslope (s := Set.univ) (c := 1) Filter.univ_mem).mpr
      hm.differentiableOn).differentiableAt Filter.univ_mem
  have hP : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) ^ ((1 - s) / 2)) s :=
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id |>.div_const 2).const_cpow
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have hm1 : DifferentiableAt ℂ (fun s : ℂ => mellin (fun y : ℝ => (f y : ℂ)) (1 - s)) s :=
    (hm (1 - s)).comp s ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
  have hiG : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((3 - s) / 2))⁻¹) s := by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (3 - s) / 2) s :=
      ((differentiableAt_const (3 : ℂ)).sub differentiableAt_id).div_const 2
    exact DifferentiableAt.comp (g := fun z : ℂ => (Complex.Gamma z)⁻¹)
      (f := fun s : ℂ => (3 - s) / 2) s (Complex.differentiable_one_div_Gamma _) h1
  have hden : DifferentiableAt ℂ (fun s : ℂ => s ^ 2 * Complex.Gammaℝ s) s :=
    (differentiableAt_id.pow 2).mul (differentiableAt_Gammaℝ_of_re_pos hs)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hden0 : s ^ 2 * Complex.Gammaℝ s ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hs0) (Complex.Gammaℝ_ne_zero_of_re_pos hs)
  unfold cosDilationCertMultiplier
  exact (((((differentiableAt_const (-2 : ℂ)).mul hP).mul hds).mul hm1).mul hiG).div hden hden0

/-- **The resolved multiplier reproduces `(Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜f(s) 𝓜f(1−s)`.** -/
theorem archXi_sq_mul_cosDilationCertMultiplier {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hG : Complex.Gamma ((1 - s) / 2) ≠ 0) (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    archXi s ^ 2 * cosDilationCertMultiplier f s =
      Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) * mellin (fun y : ℝ => (f y : ℂ)) s *
        mellin (fun y : ℝ => (f y : ℂ)) (1 - s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hz : (1 - s) / 2 ≠ 0 := by
    intro h; apply hs1; linear_combination -(2 : ℂ) * h
  have hGR : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hds : dslope (mellin fun y : ℝ => (f y : ℂ)) 1 s =
      mellin (fun y : ℝ => (f y : ℂ)) s / (s - 1) := by
    rw [dslope_of_ne _ hs1, slope_def_field, h0, sub_zero]
  have hΓ3 : Complex.Gamma ((3 - s) / 2) = (1 - s) / 2 * Complex.Gamma ((1 - s) / 2) := by
    rw [show (3 - s) / 2 = (1 - s) / 2 + 1 by ring, Complex.Gamma_add_one _ hz]
  have hR1 : Complex.Gammaℝ (1 - s) = ((π : ℂ) ^ ((1 - s) / 2))⁻¹ * Complex.Gamma ((1 - s) / 2) := by
    rw [Complex.Gammaℝ_def, ← Complex.cpow_neg]
    congr 2; ring
  have hpw : (π : ℂ) ^ ((1 - s) / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hpi h.1
  unfold cosDilationCertMultiplier archXi
  rw [hds, hΓ3, hR1]
  field_simp
  ring

theorem xi_eq_archXi_mul_riemannZeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xi s = archXi s * riemannZeta s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0, archXi]
  field_simp

theorem Gamma_one_sub_div_two_ne_zero {s : ℂ} (ht : s.im ≠ 0) :
    Complex.Gamma ((1 - s) / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m hm => ht ?_
  have := congrArg Complex.im hm
  simp at this
  linarith

/-- **Decay of the Mellin product on the strip above height two.** -/
theorem exists_norm_gammaRatio_mellin_mul_le (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (P : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → 2 ≤ |s.im| →
      ‖Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) * mellin (fun y : ℝ => (f y : ℂ)) s *
        mellin (fun y : ℝ => (f y : ℂ)) (1 - s)‖ * |s.im| ^ P ≤ C / (1 + s.im ^ 2) := by
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  obtain ⟨CΓ, N, hCΓ0, hCΓ⟩ := exists_bound_norm_Gammaℝ_div_strip
  set k : ℕ := N + P + 2 with hk
  obtain ⟨Cm, hCm⟩ := IsTest.exists_norm_pow_mul_norm_mellin_le k htest 3
  have hCm0 : 0 ≤ Cm := by
    have := hCm 1 (by norm_num); exact le_trans (by positivity) this
  refine ⟨2 * (CΓ * Cm * Cm), by positivity, fun s hσ1 hσ2 ht => ?_⟩
  set X := |s.im| with hX
  have hX1 : 1 ≤ X := by linarith
  have hs1 : X ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hs2 : X ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s); simpa [hX] using this
  set m1 := ‖mellin (fun y : ℝ => (f y : ℂ)) s‖
  set m2 := ‖mellin (fun y : ℝ => (f y : ℂ)) (1 - s)‖
  have hm1 : X ^ k * m1 ≤ Cm := by
    refine le_trans ?_ (hCm s (by rw [abs_le]; constructor <;> linarith))
    gcongr
  have hm2 : m2 ≤ Cm := by
    have h := hCm (1 - s) (by simp; rw [abs_le]; constructor <;> linarith)
    have hk1 : 1 ≤ ‖1 - s‖ ^ k := one_le_pow₀ (hX1.trans hs2)
    calc m2 = 1 * m2 := (one_mul _).symm
      _ ≤ ‖1 - s‖ ^ k * m2 := by gcongr
      _ ≤ Cm := h
  have hΓ := hCΓ s hσ1 hσ2 ht
  rw [norm_mul, norm_mul]
  set g := ‖Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)‖
  have hA : g * m1 * m2 * X ^ P * X ^ 2 ≤ CΓ * Cm * Cm := by
    calc g * m1 * m2 * X ^ P * X ^ 2 ≤ (CΓ * X ^ N) * m1 * m2 * X ^ P * X ^ 2 := by gcongr
      _ = CΓ * (X ^ k * m1) * m2 := by rw [hk]; ring
      _ ≤ CΓ * Cm * Cm := by gcongr
  have hX2 : 0 < X ^ 2 := by positivity
  have hsq : 1 + s.im ^ 2 ≤ 2 * X ^ 2 := by
    have : s.im ^ 2 = X ^ 2 := (sq_abs s.im).symm
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have hB : g * m1 * m2 * X ^ P ≤ CΓ * Cm * Cm / X ^ 2 := by
    rw [le_div_iff₀ hX2]; exact hA
  have hpos : 0 ≤ g * m1 * m2 * X ^ P := by positivity
  calc g * m1 * m2 * X ^ P * (1 + s.im ^ 2) ≤ g * m1 * m2 * X ^ P * (2 * X ^ 2) := by gcongr
    _ = 2 * (g * m1 * m2 * X ^ P * X ^ 2) := by ring
    _ ≤ 2 * (CΓ * Cm * Cm) := by gcongr

/-- Functions holomorphic on `Re s > 0` are bounded on the rectangle `[½, 3] × [−2, 2]`. -/
theorem exists_bound_rect_of_differentiableAt {F : ℂ → ℂ}
    (hF : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → |s.im| ≤ 2 → ‖F s‖ ≤ M := by
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Icc (1 / 2 : ℝ) 3 ×ˢ Icc (-2 : ℝ) 2)
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn F K := by
    rintro _ ⟨p, hp, rfl⟩
    refine (hF _ ?_).continuousAt.continuousWithinAt
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    linarith [hp.1.1]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun s h1 h2 h3 => ?_⟩
  have hsK : s ∈ K := by
    refine ⟨(s.re, s.im), ⟨⟨h1, h2⟩, (abs_le.mp h3).1, (abs_le.mp h3).2⟩, ?_⟩
    simp only
    exact Complex.re_add_im s
  exact (hM s hsK).trans (le_max_left _ _)

/-- **The strip bound for `archXi² R_f`.** -/
theorem exists_bound_archXi_sq_mul_cosDilationCertMultiplier (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 →
      ‖archXi s ^ 2 * cosDilationCertMultiplier f s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_rect_of_differentiableAt (F := fun s =>
    archXi s ^ 2 * cosDilationCertMultiplier f s) fun s hs =>
      ((differentiableAt_archXi hs).pow 2).mul
        (differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp hs)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_gammaRatio_mellin_mul_le hf hα hαβ hsupp 0
  refine ⟨max (5 * M) C₁, fun s hσ1 hσ2 => ?_⟩
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  rcases le_or_gt |s.im| 2 with ht | ht
  · have hb := hM s hσ1 hσ2 ht
    rw [le_div_iff₀ hden]
    have hsq : s.im ^ 2 ≤ 4 := by
      have := sq_abs s.im; nlinarith [abs_nonneg s.im]
    calc ‖archXi s ^ 2 * cosDilationCertMultiplier f s‖ * (1 + s.im ^ 2) ≤ M * 5 := by
          gcongr; linarith
      _ ≤ max (5 * M) C₁ := by rw [mul_comm]; exact le_max_left _ _
  · have him : s.im ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h] at him; simp at him
    rw [archXi_sq_mul_cosDilationCertMultiplier (by linarith) hs1
      (Gamma_one_sub_div_two_ne_zero him) h0]
    have h := hC₁ s hσ1 hσ2 ht.le
    rw [pow_zero, mul_one] at h
    exact h.trans (div_le_div_of_nonneg_right (le_max_right _ _) hden.le)

/-- **The strip bound for `ξ² R_f`.** -/
theorem exists_bound_xi_sq_mul_cosDilationCertMultiplier (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 →
      ‖xi s ^ 2 * cosDilationCertMultiplier f s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_rect_of_differentiableAt (F := fun s =>
    xi s ^ 2 * cosDilationCertMultiplier f s) fun s hs =>
      ((xi_differentiable s).pow 2).mul
        (differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp hs)
  obtain ⟨Cζ, Nζ, hCζ0, hCζ⟩ := exists_bound_norm_riemannZeta_strip 3
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_gammaRatio_mellin_mul_le hf hα hαβ hsupp (2 * Nζ)
  refine ⟨max (5 * M) (Cζ ^ 2 * C₁), fun s hσ1 hσ2 => ?_⟩
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  rcases le_or_gt |s.im| 2 with ht | ht
  · have hb := hM s hσ1 hσ2 ht
    rw [le_div_iff₀ hden]
    have hsq : s.im ^ 2 ≤ 4 := by
      have := sq_abs s.im; nlinarith [abs_nonneg s.im]
    calc ‖xi s ^ 2 * cosDilationCertMultiplier f s‖ * (1 + s.im ^ 2) ≤ M * 5 := by
          gcongr; linarith
      _ ≤ max (5 * M) (Cζ ^ 2 * C₁) := by rw [mul_comm]; exact le_max_left _ _
  · have him : s.im ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h] at him; simp at him
    have hspos : 0 < s.re := by linarith
    rw [xi_eq_archXi_mul_riemannZeta hspos hs1, mul_pow, mul_assoc, mul_comm (riemannZeta s ^ 2),
      ← mul_assoc, archXi_sq_mul_cosDilationCertMultiplier hspos hs1
        (Gamma_one_sub_div_two_ne_zero him) h0, norm_mul, norm_pow]
    have hz : ‖riemannZeta s‖ ≤ Cζ * |s.im| ^ Nζ := by
      have h := hCζ s.re s.im (by rw [abs_le]; constructor <;> linarith) (by linarith)
      rwa [Complex.re_add_im] at h
    have h := hC₁ s hσ1 hσ2 ht.le
    set H := ‖Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) * mellin (fun y : ℝ => (f y : ℂ)) s *
        mellin (fun y : ℝ => (f y : ℂ)) (1 - s)‖
    have hH0 : 0 ≤ H := norm_nonneg _
    calc H * ‖riemannZeta s‖ ^ 2 ≤ H * (Cζ * |s.im| ^ Nζ) ^ 2 := by gcongr
      _ = Cζ ^ 2 * (H * |s.im| ^ (2 * Nζ)) := by ring
      _ ≤ Cζ ^ 2 * (C₁ / (1 + s.im ^ 2)) := by gcongr
      _ = Cζ ^ 2 * C₁ / (1 + s.im ^ 2) := by ring
      _ ≤ max (5 * M) (Cζ ^ 2 * C₁) / (1 + s.im ^ 2) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hden.le

/-- **The corpus kernel of `R_f` is `Cf ⋆ f`.** -/
theorem certKernel_cosDilationCertMultiplier (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) {x : ℝ} (hx : 0 < x) :
    certKernel (cosDilationCertMultiplier f) x = (cosDilationKernel f x : ℂ) := by
  have hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ (cosDilationCertMultiplier f) s :=
    fun s h1 _ => differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp (by linarith)
  obtain ⟨Ca, hCa⟩ := exists_bound_archXi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  rw [certKernel_eq_mellinInv_half _ hR hCa hx,
    ← mellinInv_gammaRatio_mellin_eq_cosDilationKernel hf hα hαβ hsupp hx]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hre : s.re = 1 / 2 := by simp [s]
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hG : Complex.Gamma ((1 - s) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp [s]; norm_num)
  rw [archXi_sq_mul_cosDilationCertMultiplier (by rw [hre]; norm_num) hs1 hG h0]

/-- **Blindness of the Ξ²-divisible test `Ξ² R_f` at `log n`, `n ≥ 2`, is the vanishing of the
cosine–dilation kernel `Cf ⋆ f` at every integer `n ≥ 2`.** -/
theorem logNode_blind_iff_cosDilationKernel_vanishes (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    (∀ n : ℕ, 2 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * Complex.I) ^ 2 * cosDilationCertMultiplier f (1 / 2 + t * Complex.I) *
        (n : ℂ) ^ (-((t : ℂ) * Complex.I)) = 0) ↔
    (∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) := by
  have hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 → DifferentiableAt ℂ (cosDilationCertMultiplier f) s :=
    fun s h1 _ => differentiableAt_cosDilationCertMultiplier hf hα hαβ hsupp (by linarith)
  obtain ⟨C, hC⟩ := exists_bound_xi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  obtain ⟨Ca, hCa⟩ := exists_bound_archXi_sq_mul_cosDilationCertMultiplier hf hα hαβ hsupp h0
  have hC' : ∀ t : ℝ, ‖archXi (3 + t * Complex.I) ^ 2 * cosDilationCertMultiplier f (3 + t * Complex.I)‖ ≤
      Ca / (1 + t ^ 2) := fun t => by
    have h := hCa (3 + t * Complex.I) (by simp; norm_num) (by simp)
    simpa using h
  rw [logNode_blind_iff_certKernel_vanishes _ hR hC hC']
  refine forall_congr' fun n => imp_congr_right fun hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [certKernel_cosDilationCertMultiplier hf hα hαβ hsupp h0 hn0, Complex.ofReal_eq_zero]

end

end RHTower
