import GaloisForLFunctions.RHTower.EvenSectorAbelLaplace

/-!
# Abel averaging of the far-bump inequality

Average the far-bump inequality for even tests (`realWeil_ge_of_weilPositiveEvenPolar`) over the far
bump position `a ≥ a₀ = R + 1` against the weight `ω_s(a) = s e^{−sa} (1 + e^{−a})²`.  Since
`ω_s c_a = (P/J) s (e^{−(1/2+s)a} + e^{−(3/2+s)a})` and `ω_s c_a² = (P/J)² s e^{−(1+s)a}`, every
term becomes a Laplace transform of a window sum, and the Laplace transforms factor through the
Dirichlet series `F(s) = Σ_{n ≥ 2} lam(n) n^{−1−s}`.

**Theorem** (`eventually_realWeil_ge`).  If moreover `s · X(s) → 0` as `s → 0⁺`, where
`X(s) = s F(s)`, then for every `ε > 0` and all small `s > 0`

`W(g) ≥ P² (2 − 4 X(s) + 2 X(s/2)) − ε`,

with `P = ∫ g(x) e^{−x/2} dx`.  The two window profiles (cross kernel `g ⋆ φ̃` and autocorrelation
`φ ⋆ φ̃`) enter only through their pole constants `PJ` and `J²`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-! ## The Abel weight -/

/-- `ω_s(a) = s e^{−sa} (1 + e^{−a})²`. -/
def farAbelWeight (s a : ℝ) : ℝ := s * Real.exp (-s * a) * (1 + Real.exp (-a)) ^ 2

theorem abelWeight_nonneg {s : ℝ} (hs : 0 ≤ s) (a : ℝ) : 0 ≤ farAbelWeight s a := by
  unfold farAbelWeight; positivity

theorem exp_neg_half_add (s a : ℝ) :
    Real.exp (-(1 / 2 + s) * a) = Real.exp (-s * a) * (Real.exp (a / 2))⁻¹ := by
  rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring

theorem exp_neg_three_half_add (s a : ℝ) :
    Real.exp (-(1 / 2 + (1 + s)) * a) = Real.exp (-s * a) * ((Real.exp (a / 2))⁻¹) ^ 3 := by
  rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

theorem exp_neg_one_add (s a : ℝ) :
    Real.exp (-(1 + s) * a) = Real.exp (-s * a) * ((Real.exp (a / 2))⁻¹) ^ 2 := by
  rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

theorem exp_neg_eq_inv_sq (a : ℝ) : Real.exp (-a) = ((Real.exp (a / 2))⁻¹) ^ 2 := by
  rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem exp_neg_half_eq_inv (a : ℝ) : Real.exp (-a / 2) = (Real.exp (a / 2))⁻¹ := by
  rw [← Real.exp_neg]; congr 1; ring

theorem abelWeight_mul_farCoeff (g : ℝ → ℝ) (s a : ℝ) :
    farAbelWeight s a * farCoeff g a = (∫ x, g x * Real.exp (-x / 2)) / farJ * s *
      (Real.exp (-(1 / 2 + s) * a) + Real.exp (-(1 / 2 + (1 + s)) * a)) := by
  have hJ := farJ_pos
  have ht := Real.exp_pos (a / 2)
  unfold farAbelWeight farCoeff
  rw [exp_neg_half_add, exp_neg_three_half_add, exp_neg_eq_inv_sq, exp_neg_half_eq_inv]
  field_simp
  ring

theorem abelWeight_mul_farCoeff_sq (g : ℝ → ℝ) (s a : ℝ) :
    farAbelWeight s a * farCoeff g a ^ 2 = ((∫ x, g x * Real.exp (-x / 2)) / farJ) ^ 2 * s *
      Real.exp (-(1 + s) * a) := by
  have hJ := farJ_pos
  have ht := Real.exp_pos (a / 2)
  unfold farAbelWeight farCoeff
  rw [exp_neg_one_add, exp_neg_eq_inv_sq, exp_neg_half_eq_inv]
  field_simp
  ring

theorem abelWeight_mul_abs_farCoeff (g : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) (a : ℝ) :
    farAbelWeight s a * |farCoeff g a| = |∫ x, g x * Real.exp (-x / 2)| / farJ * s *
      (Real.exp (-(1 / 2 + s) * a) + Real.exp (-(1 / 2 + (1 + s)) * a)) := by
  have hJ := farJ_pos
  have hw := abelWeight_nonneg hs a
  rw [← abs_of_nonneg hw, ← abs_mul, abelWeight_mul_farCoeff, abs_mul, abs_mul, abs_div,
    abs_of_pos hJ, abs_of_nonneg hs, abs_of_pos (by positivity :
      (0 : ℝ) < Real.exp (-(1 / 2 + s) * a) + Real.exp (-(1 / 2 + (1 + s)) * a))]

/-! ## Exponentials on a right half-line -/

theorem integrableOn_exp_neg_Ici {μ : ℝ} (hμ : 0 < μ) (a₀ : ℝ) :
    IntegrableOn (fun a => Real.exp (-μ * a)) (Ici a₀) :=
  (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi (by linarith) a₀)

theorem integral_exp_neg_Ici {μ : ℝ} (hμ : 0 < μ) (a₀ : ℝ) :
    ∫ a in Ici a₀, Real.exp (-μ * a) = Real.exp (-μ * a₀) / μ := by
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq]

theorem integral_exp_neg_Ici_le {μ : ℝ} (hμ : 1 / 2 ≤ μ) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) :
    ∫ a in Ici a₀, Real.exp (-μ * a) ≤ 2 := by
  rw [integral_exp_neg_Ici (by linarith)]
  have h1 : Real.exp (-μ * a₀) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem integrableOn_abelWeight {s : ℝ} (hs : 0 < s) (a₀ : ℝ) :
    IntegrableOn (farAbelWeight s) (Ici a₀) := by
  have e : farAbelWeight s = fun a => s * Real.exp (-s * a) + 2 * s * Real.exp (-(1 + s) * a) +
      s * Real.exp (-(2 + s) * a) := by
    funext a
    unfold farAbelWeight
    have h1 : Real.exp (-a) * Real.exp (-s * a) = Real.exp (-(1 + s) * a) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-a) ^ 2 * Real.exp (-s * a) = Real.exp (-(2 + s) * a) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    rw [← h1, ← h2]; ring
  rw [e]
  exact (((integrableOn_exp_neg_Ici hs a₀).const_mul s).add
    ((integrableOn_exp_neg_Ici (μ := 1 + s) (by linarith) a₀).const_mul (2 * s))).add
    ((integrableOn_exp_neg_Ici (μ := 2 + s) (by linarith) a₀).const_mul s)

/-- `|∫_{a ≥ a₀} ω_s − 1| ≤ s (a₀ + 3)` for `s > 0`, `a₀ ≥ 0`. -/
theorem abs_integral_abelWeight_sub_le {s : ℝ} (hs : 0 < s) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) :
    |(∫ a in Ici a₀, farAbelWeight s a) - 1| ≤ s * (a₀ + 3) := by
  have e : ∫ a in Ici a₀, farAbelWeight s a = Real.exp (-s * a₀) +
      2 * s * (Real.exp (-(1 + s) * a₀) / (1 + s)) + s * (Real.exp (-(2 + s) * a₀) / (2 + s)) := by
    have e1 : farAbelWeight s = fun a => s * Real.exp (-s * a) + 2 * s * Real.exp (-(1 + s) * a) +
        s * Real.exp (-(2 + s) * a) := by
      funext a
      unfold farAbelWeight
      have h1 : Real.exp (-a) * Real.exp (-s * a) = Real.exp (-(1 + s) * a) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : Real.exp (-a) ^ 2 * Real.exp (-s * a) = Real.exp (-(2 + s) * a) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      rw [← h1, ← h2]; ring
    have i1 : IntegrableOn (fun a => s * Real.exp (-s * a)) (Ici a₀) :=
      (integrableOn_exp_neg_Ici hs a₀).const_mul s
    have i2 : IntegrableOn (fun a => 2 * s * Real.exp (-(1 + s) * a)) (Ici a₀) :=
      (integrableOn_exp_neg_Ici (μ := 1 + s) (by linarith) a₀).const_mul (2 * s)
    have i3 : IntegrableOn (fun a => s * Real.exp (-(2 + s) * a)) (Ici a₀) :=
      (integrableOn_exp_neg_Ici (μ := 2 + s) (by linarith) a₀).const_mul s
    have i12 : IntegrableOn (fun a => s * Real.exp (-s * a) + 2 * s * Real.exp (-(1 + s) * a))
        (Ici a₀) := i1.add i2
    rw [e1]
    show ∫ a in Ici a₀, (s * Real.exp (-s * a) + 2 * s * Real.exp (-(1 + s) * a) +
      s * Real.exp (-(2 + s) * a)) = _
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_exp_neg_Ici hs, integral_exp_neg_Ici (μ := 1 + s) (by linarith),
      integral_exp_neg_Ici (μ := 2 + s) (by linarith)]
    field_simp
  rw [e]
  have h1 : 1 - s * a₀ ≤ Real.exp (-s * a₀) := by
    have := Real.add_one_le_exp (-s * a₀); linarith
  have h2 : Real.exp (-s * a₀) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 : Real.exp (-(1 + s) * a₀) / (1 + s) ≤ 1 := by
    rw [div_le_one (by linarith)]
    have := Real.exp_le_one_iff.mpr (show -(1 + s) * a₀ ≤ 0 by nlinarith); linarith
  have h4 : Real.exp (-(2 + s) * a₀) / (2 + s) ≤ 1 := by
    rw [div_le_one (by linarith)]
    have := Real.exp_le_one_iff.mpr (show -(2 + s) * a₀ ≤ 0 by nlinarith); linarith
  have h3' : 0 ≤ Real.exp (-(1 + s) * a₀) / (1 + s) := by positivity
  have h4' : 0 ≤ Real.exp (-(2 + s) * a₀) / (2 + s) := by positivity
  rw [abs_le]; constructor <;> nlinarith

/-! ## The averaged inequality -/

/-- **The Abel-averaged far-bump inequality.**  With `a₀ = R + 1`, for `0 < s ≤ 1/2`,
`0 ≤ (W − 2P²) I₀ + 4(P/J) s (A₁ + A₂) − 2(P/J)² s A₃ + M E` where `I₀ = ∫_{a ≥ a₀} ω_s`,
`A₁, A₂` are the Laplace integrals of `T` at `1/2 + s` and `3/2 + s`, `A₃` that of `S` at `1 + s`,
and `E = (|P|/J) s (e₁ + e₂) + (P/J)² s e₃` collects the exponential masses. -/
theorem abel_averaged_ineq {lam : ℕ → ℝ} (hpf : WeilPositiveEvenPolar lam)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgs : ∀ x, R < |x| → g x = 0)
    (hge : ∀ x, g (-x) = g x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s →
      0 ≤ ((weilFullFunctional lam
          (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re -
          2 * (∫ x, g x * Real.exp (-x / 2)) ^ 2) * (∫ a in Ici (R + 1), farAbelWeight s a) +
        4 * ((∫ x, g x * Real.exp (-x / 2)) / farJ) * s *
          ((∫ a in Ici (R + 1), farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a)) +
            ∫ a in Ici (R + 1), farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)) -
        2 * ((∫ x, g x * Real.exp (-x / 2)) / farJ) ^ 2 * s *
          (∫ a in Ici (R + 1), farSum lam a * Real.exp (-(1 + s) * a)) +
        M * (|∫ x, g x * Real.exp (-x / 2)| / farJ * s *
            ((∫ a in Ici (R + 1), Real.exp (-(1 / 2 + s) * a)) +
              ∫ a in Ici (R + 1), Real.exp (-(1 / 2 + (1 + s)) * a)) +
          ((∫ x, g x * Real.exp (-x / 2)) / farJ) ^ 2 * s *
            ∫ a in Ici (R + 1), Real.exp (-(1 + s) * a)) := by
  obtain ⟨M, hM0, hM⟩ := realWeil_ge_of_weilPositiveEvenPolar hpf hg hR hgs hge
  refine ⟨M, hM0, fun s hs => ?_⟩
  set W := (weilFullFunctional lam (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re
    with hW
  set P := ∫ x, g x * Real.exp (-x / 2) with hP
  set a₀ := R + 1 with ha₀
  have hgc := hasCompactSupport_of_abs_gt_eq_zero hgs
  have hT1 := (integral_kernelSum_mul_exp hsl (continuous_farCrossKernel hg hgc)
    (hasCompactSupport_farCrossKernel hgs) hs).1
  have hT2 := (integral_kernelSum_mul_exp hsl (continuous_farCrossKernel hg hgc)
    (hasCompactSupport_farCrossKernel hgs) (show 0 < 1 + s by linarith)).1
  have hS3 : Integrable fun a => farSum lam a * Real.exp (-(1 + s) * a) := by
    have := (integral_farSum_mul_exp hsl (show 0 < s / 2 by linarith)).1
    refine this.congr (Eventually.of_forall fun a => ?_)
    show farSum lam a * Real.exp (-(1 + 2 * (s / 2)) * a) = _
    rw [show 1 + 2 * (s / 2) = 1 + s by ring]
  rw [← farCrossSum_eq_kernelSum] at hT1 hT2
  have he1 := integrableOn_exp_neg_Ici (μ := 1 / 2 + s) (by linarith) a₀
  have he2 := integrableOn_exp_neg_Ici (μ := 1 / 2 + (1 + s)) (by linarith) a₀
  have he3 := integrableOn_exp_neg_Ici (μ := 1 + s) (by linarith) a₀
  have hw := integrableOn_abelWeight hs a₀
  set Φ : ℝ → ℝ := fun a => (W - 2 * P ^ 2) * farAbelWeight s a +
      4 * (P / farJ) * s * (farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a) +
        farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)) -
      2 * (P / farJ) ^ 2 * s * (farSum lam a * Real.exp (-(1 + s) * a)) +
      M * (|P| / farJ * s * (Real.exp (-(1 / 2 + s) * a) + Real.exp (-(1 / 2 + (1 + s)) * a)) +
        (P / farJ) ^ 2 * s * Real.exp (-(1 + s) * a)) with hΦ
  have hpt : ∀ a ∈ Ici a₀, 0 ≤ Φ a := by
    intro a ha
    have ha' : a₀ ≤ a := ha
    have hineq := hM a ha'
    have hω := abelWeight_nonneg hs.le a
    have k1 := abelWeight_mul_farCoeff g s a
    have k2 := abelWeight_mul_farCoeff_sq g s a
    have k3 := abelWeight_mul_abs_farCoeff g hs.le a
    rw [← hP] at k1 k2 k3
    have hmul := mul_le_mul_of_nonneg_left hineq hω
    simp only [hΦ]
    have e : farAbelWeight s a * (2 * P ^ 2 - 4 * farCoeff g a * farCrossSum lam g a +
        2 * farCoeff g a ^ 2 * farSum lam a - M * (|farCoeff g a| + farCoeff g a ^ 2)) =
        2 * P ^ 2 * farAbelWeight s a -
          4 * (farAbelWeight s a * farCoeff g a) * farCrossSum lam g a +
          2 * (farAbelWeight s a * farCoeff g a ^ 2) * farSum lam a -
          M * (farAbelWeight s a * |farCoeff g a| + farAbelWeight s a * farCoeff g a ^ 2) := by ring
    rw [e, k1, k2, k3] at hmul
    nlinarith
  have j1 : IntegrableOn (fun a => (W - 2 * P ^ 2) * farAbelWeight s a) (Ici a₀) :=
    hw.const_mul _
  have j2a : IntegrableOn (fun a => farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a)) (Ici a₀) :=
    hT1.integrableOn
  have j2b : IntegrableOn (fun a => farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a))
      (Ici a₀) := hT2.integrableOn
  have j2s : IntegrableOn (fun a => farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a) +
      farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)) (Ici a₀) := j2a.add j2b
  have j2 : IntegrableOn (fun a => 4 * (P / farJ) * s *
      (farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a) +
        farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a))) (Ici a₀) := j2s.const_mul _
  have j3a : IntegrableOn (fun a => farSum lam a * Real.exp (-(1 + s) * a)) (Ici a₀) :=
    hS3.integrableOn
  have j3 : IntegrableOn (fun a => 2 * (P / farJ) ^ 2 * s *
      (farSum lam a * Real.exp (-(1 + s) * a))) (Ici a₀) := j3a.const_mul _
  have j4a : IntegrableOn (fun a => Real.exp (-(1 / 2 + s) * a) +
      Real.exp (-(1 / 2 + (1 + s)) * a)) (Ici a₀) := he1.add he2
  have j4b : IntegrableOn (fun a => |P| / farJ * s * (Real.exp (-(1 / 2 + s) * a) +
      Real.exp (-(1 / 2 + (1 + s)) * a))) (Ici a₀) := j4a.const_mul _
  have j4c : IntegrableOn (fun a => (P / farJ) ^ 2 * s * Real.exp (-(1 + s) * a)) (Ici a₀) :=
    he3.const_mul _
  have j4d : IntegrableOn (fun a => |P| / farJ * s * (Real.exp (-(1 / 2 + s) * a) +
      Real.exp (-(1 / 2 + (1 + s)) * a)) + (P / farJ) ^ 2 * s * Real.exp (-(1 + s) * a))
      (Ici a₀) := j4b.add j4c
  have j4 : IntegrableOn (fun a => M * (|P| / farJ * s * (Real.exp (-(1 / 2 + s) * a) +
      Real.exp (-(1 / 2 + (1 + s)) * a)) + (P / farJ) ^ 2 * s * Real.exp (-(1 + s) * a)))
      (Ici a₀) := j4d.const_mul _
  have j12 : IntegrableOn (fun a => (W - 2 * P ^ 2) * farAbelWeight s a +
      4 * (P / farJ) * s * (farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a) +
        farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a))) (Ici a₀) := j1.add j2
  have j123 : IntegrableOn (fun a => (W - 2 * P ^ 2) * farAbelWeight s a +
      4 * (P / farJ) * s * (farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a) +
        farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)) -
      2 * (P / farJ) ^ 2 * s * (farSum lam a * Real.exp (-(1 + s) * a))) (Ici a₀) := j12.sub j3
  have hnonneg := setIntegral_nonneg (μ := volume) measurableSet_Ici hpt
  have hval : ∫ a in Ici a₀, Φ a =
      (W - 2 * P ^ 2) * (∫ a in Ici a₀, farAbelWeight s a) +
        4 * (P / farJ) * s *
          ((∫ a in Ici a₀, farCrossSum lam g a * Real.exp (-(1 / 2 + s) * a)) +
            ∫ a in Ici a₀, farCrossSum lam g a * Real.exp (-(1 / 2 + (1 + s)) * a)) -
        2 * (P / farJ) ^ 2 * s * (∫ a in Ici a₀, farSum lam a * Real.exp (-(1 + s) * a)) +
        M * (|P| / farJ * s * ((∫ a in Ici a₀, Real.exp (-(1 / 2 + s) * a)) +
            ∫ a in Ici a₀, Real.exp (-(1 / 2 + (1 + s)) * a)) +
          (P / farJ) ^ 2 * s * ∫ a in Ici a₀, Real.exp (-(1 + s) * a)) := by
    simp only [hΦ]
    rw [integral_add j123 j4, integral_sub j12 j3, integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_add j2a j2b,
      integral_add j4b j4c, integral_const_mul, integral_const_mul, integral_add he1 he2]
  rw [hval] at hnonneg
  exact hnonneg

end RHTower.EvenSector

end
