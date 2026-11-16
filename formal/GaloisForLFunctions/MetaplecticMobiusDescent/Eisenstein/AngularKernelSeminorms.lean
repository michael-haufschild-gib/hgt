import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularKernelBounds
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.CompletedHeightTwists

/-!
# Source seminorm control for angular reflection kernels

Vertical Mellin decay is controlled by finitely many Schwartz seminorms of the source.
The shifted Gamma quotient has the same vertical degree at every angular weight. Contour
shifting transfers this control to every finite collection of weighted Euler derivatives.
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped ContDiff ComplexConjugate Classical Topology FourierTransform SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
open CompletedHeight SchwartzPlanePoisson
noncomputable section

theorem angularMellinData_strip_source_bound (ℓ : ℕ) (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        (1 + |t|) ^ j * ‖angularMellinData ℓ W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := angularCubicReflectionGamma_strip_bound ℓ A
  obtain ⟨s, CV, hCV, hVb⟩ := mellin_strip_source_bound a b ha (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨s, Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro W hsupp σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb W hsupp (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖angularCubicReflectionGamma ℓ ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [angularMellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        ‖angularCubicReflectionGamma ℓ ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ Cγ * (CV * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := mul_le_mul_of_nonneg_left hmb hCγ.le
    _ = _ := by ring

theorem angularMellinEulerData_strip_source_bound (ℓ : ℕ) (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        ‖angularMellinEulerData ℓ W j ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t ^ 2) := by
  obtain ⟨s, C, hC, hb⟩ := angularMellinData_strip_source_bound ℓ a b ha A (j + 2)
  refine ⟨s, ((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro W hsupp σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith only [hnorm, hσabs, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A),
      mul_nonneg (Nat.cast_nonneg A : (0 : ℝ) ≤ A) (abs_nonneg t)]
  rw [angularMellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖angularMellinData ℓ W ((σ : ℂ) + t * Complex.I)‖) := by gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖angularMellinData ℓ W ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ ((A : ℝ) + 2) ^ j * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (by positivity)
    _ = _ := by ring

theorem angularMellinInv_euler_line_source_bound (ℓ : ℕ) (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ y : ℝ, 0 < y →
        ‖mellinInv σ (angularMellinEulerData ℓ W j) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * y ^ (-σ) := by
  obtain ⟨s, C, hC, hb⟩ := angularMellinEulerData_strip_source_bound ℓ a b ha A j
  refine ⟨s, C / 2, by positivity, ?_⟩
  intro W hsupp σ hσ y hy
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        angularMellinEulerData ℓ W j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * (C * Q)) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * (C * Q)) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * (C * Q)) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by dsimp [Q]; field_simp

/-- One finite source seminorm bound controls small arguments and arbitrary decay at infinity. -/
theorem angularPaperKernel_euler_source_power_decay (ℓ : ℕ) (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ x : ℝ, 0 < x →
        (‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (1 / 4 : ℝ)) ∧
        (‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (-(A : ℝ))) := by
  obtain ⟨s, C, hC, hb⟩ := angularMellinInv_euler_line_source_bound ℓ a b ha A j
  let B := max (paperScale ^ (1 / 4 : ℝ)) (paperScale ^ (-(A : ℝ)))
  have hB : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos paperScale_pos _) (le_max_left _ _)
  refine ⟨s, C * B, mul_pos hC hB, ?_⟩
  intro W hsupp x hx
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hline (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      ‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) j x‖ ≤
        C * Q * (paperScale * x) ^ (-σ) := by
    have he : LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) j x =
        angularPaperKernelLogDerivative ℓ W j x := by
      simpa only [LocalLogFourier.eulerDeriv,Real.exp_zero,mul_one] using
        iteratedDeriv_angularPaperKernel_exp ℓ W a b ha hsupp (W.smooth ⊤) x hx j 0
    rw [he,angularPaperKernelLogDerivative]
    rw [angularMellinInv_euler_shift ℓ W a b ha hsupp (W.smooth ⊤) A j σ hσ _ (mul_pos paperScale_pos hx)]
    exact hb W hsupp σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  constructor
  · have hh := hline _ hleft
    rw [neg_neg, Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := hh
      _ = (C * paperScale ^ (1 / 4 : ℝ)) * Q * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ (C * B) * Q * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact le_max_left _ _
  · have hh := hline _ hright
    rw [Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (-(A : ℝ)) * x ^ (-(A : ℝ))) := hh
      _ = (C * paperScale ^ (-(A : ℝ))) * Q * x ^ (-(A : ℝ)) := by ring
      _ ≤ (C * B) * Q * x ^ (-(A : ℝ)) := by
        gcongr
        exact le_max_right _ _

theorem angularPaperKernel_euler_source_uniform_weighted_bound (ℓ : ℕ)
    (a b : ℝ) (ha : 0 < a) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ i ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) i x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose s c hc hb using fun i : Fin (K + 1) => angularPaperKernel_euler_source_power_decay ℓ a b ha A i.val
  let S : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤ ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤ D := by
    have hs : c i ≤ ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  refine ⟨S, 2 ^ A * (D + D), by positivity, ?_⟩
  intro W hsupp
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsource (i : Fin (K + 1)) : c i * (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ D * Q := by
    have hsub : s i ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hq : (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
      Seminorm.le_def.mp (Finset.sup_mono hsub) W
    exact mul_le_mul (hci i) hq (by positivity) hD.le
  have hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) i x‖ ≤ D * Q := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤ (c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (1 / 4 : ℝ) := (hb k W hsupp x hx).1
      _ ≤ c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg (hc k).le (by positivity))
      _ ≤ D * Q := hsource k
  have hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) i x‖ ≤ D * Q := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤ x ^ A * ((c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k W hsupp x hx).2 (pow_nonneg hx.le A)
      _ = c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤ D * Q := hsource k
  intro i hi x hx
  have hcoef : (2:ℝ)^A*(D*Q) ≤ (2^A*(D+D))*Q := by
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hD.le) (by positivity)) hQ
  change _ ≤ (2^A*(D+D))*Q
  by_cases hx1 : x≤1
  · calc
      _ ≤ 2^A*‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) i x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith : 1+x≤2) A) (norm_nonneg _)
      _ ≤ 2^A*(D*Q) := mul_le_mul_of_nonneg_left (hsmall i hi x hx hx1) (by positivity)
      _ ≤ _ := hcoef
  · calc
      _ ≤ (2*x)^A*‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) i x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith : 1+x≤2*x) A) (norm_nonneg _)
      _ = 2^A*(x^A*‖LocalLogFourier.eulerDeriv (angularPaperKernel ℓ W) i x‖) := by rw [mul_pow,mul_assoc]
      _ ≤ 2^A*(D*Q) := mul_le_mul_of_nonneg_left (hlarge i hi x (by linarith)) (by positivity)
      _ ≤ _ := hcoef

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
