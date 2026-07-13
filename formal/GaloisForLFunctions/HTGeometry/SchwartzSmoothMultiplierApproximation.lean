import GaloisForLFunctions.HTGeometry.PolynomialSmoothApproximation
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Polynomial approximation of smooth multipliers on compact Schwartz packets

Finite-order smooth Weierstrass approximation is upgraded to convergence in the full Schwartz
topology after multiplication by one fixed compactly supported Schwartz map.  This is the
continuity bridge from polynomial momentum functional calculus to arbitrary smooth temperate
multipliers on compact packets.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial

noncomputable section

namespace SchwartzMap

def smoothMultiplierErrorEnvelope (f : SchwartzMap ℝ ℂ) (D : ℝ) (k : ℕ) : ℝ :=
  D * ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (k - i) f

theorem smoothMultiplierErrorEnvelope_nonneg
    (f : SchwartzMap ℝ ℂ) {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    0 ≤ smoothMultiplierErrorEnvelope f D k := by
  unfold smoothMultiplierErrorEnvelope
  positivity

theorem seminorm_zero_smulLeftCLM_ofReal_le_smoothMultiplierErrorEnvelope
    (m : ℝ → ℝ) (hm : Function.HasTemperateGrowth m)
    (f : SchwartzMap ℝ ℂ) {D : ℝ} (hD : 0 ≤ D) (k : ℕ)
    (hder : ∀ t ∈ tsupport f, ∀ j : ℕ, j ≤ k → ‖iteratedDeriv j m t‖ ≤ D) :
    SchwartzMap.seminorm ℂ 0 k
      (SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) f) ≤
      smoothMultiplierErrorEnvelope f D k := by
  apply SchwartzMap.seminorm_le_bound' (𝕜 := ℂ) 0 k
  · exact smoothMultiplierErrorEnvelope_nonneg f hD k
  · intro t
    simp only [pow_zero, one_mul]
    have hmTop : ContDiff ℝ (⊤ : ℕ∞) m := hm.1
    rw [show iteratedDeriv k
        (fun x => (SchwartzMap.smulLeftCLM ℂ (fun t => (m t : ℂ)) f) x) t =
        iteratedDeriv k (fun x => (m x : ℂ) ^ 1 * f x) t by
      congr 1
      funext x
      rw [SchwartzMap.smulLeftCLM_apply_apply]
      · simp
      · exact Complex.ofRealCLM.hasTemperateGrowth.comp hm]
    rw [iteratedDeriv_real_pow_mul_schwartz_eq_sum m hmTop f 1 k t]
    by_cases ht : t ∈ tsupport f
    · calc
        ‖∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℂ) * iteratedDeriv i (fun x => (m x ^ 1 : ℂ)) t *
              iteratedDeriv (k - i) f t‖ ≤
          ∑ i ∈ Finset.range (k + 1),
            ‖(k.choose i : ℂ) * iteratedDeriv i (fun x => (m x ^ 1 : ℂ)) t *
              iteratedDeriv (k - i) f t‖ := norm_sum_le _ _
        _ ≤ smoothMultiplierErrorEnvelope f D k := by
          unfold smoothMultiplierErrorEnvelope
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          have hcast : iteratedDeriv i (fun x => (m x ^ 1 : ℂ)) t =
              ((iteratedDeriv i m t : ℝ) : ℂ) := by
            simpa using iteratedDeriv_ofReal m hmTop i t
          rw [hcast, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real]
          have hmder := hder t ht i
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
          have hfderiv : ‖iteratedDeriv (k - i) f t‖ ≤
              SchwartzMap.seminorm ℂ 0 (k - i) f := by
            have hsem := SchwartzMap.le_seminorm ℂ 0 (k - i) f t
            rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hsem
            simpa only [pow_zero, one_mul] using hsem
          calc
            (k.choose i : ℝ) * ‖iteratedDeriv i m t‖ *
                ‖iteratedDeriv (k - i) f t‖ ≤
              (k.choose i : ℝ) * D *
                SchwartzMap.seminorm ℂ 0 (k - i) f := by
              gcongr
            _ = D * ((k.choose i : ℝ) *
                SchwartzMap.seminorm ℂ 0 (k - i) f) := by ring
    · have hzero : ∀ i ∈ Finset.range (k + 1),
          iteratedDeriv (k - i) f t = 0 := by
        intro i _hi
        exact iteratedDeriv_eq_zero_of_not_mem_tsupport f (k - i) ht
      have hsumzero : ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℂ) * iteratedDeriv i (fun x => (m x ^ 1 : ℂ)) t *
            iteratedDeriv (k - i) f t = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i hi, mul_zero]
      rw [hsumzero, norm_zero]
      exact smoothMultiplierErrorEnvelope_nonneg f hD k

theorem polynomial_eval_hasTemperateGrowth (P : ℝ[X]) :
    Function.HasTemperateGrowth (fun x : ℝ => P.eval x) := by
  have hx : Function.HasTemperateGrowth (fun x : ℝ => x) := by fun_prop
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa using hP.add hQ
  | monomial n a =>
      simpa [Polynomial.eval_monomial] using
        (Function.HasTemperateGrowth.const a).mul (hx.pow n)

/-- If real polynomials approximate a smooth temperate multiplier in all derivatives on the
support interval of `f`, then the multiplier errors times `f` converge in the full Schwartz
topology. -/
theorem tendsto_polynomial_multiplier_error_mul_schwartz_zero
    {a : ℝ → ℝ} (ha : Function.HasTemperateGrowth a)
    (P : ℕ → ℝ[X]) {T : ℝ} (hT : 0 ≤ T)
    (hP : ∀ k : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc (-T) T,
      |(Polynomial.derivative^[k] (P n)).eval x - iteratedDeriv k a x| < ε)
    (f : SchwartzMap ℝ ℂ) (hf : tsupport f ⊆ {x : ℝ | |x| ≤ T}) :
    Tendsto (fun n : ℕ => SchwartzMap.smulLeftCLM ℂ
      (fun x => ((P n).eval x - a x : ℂ)) f) atTop (nhds 0) := by
  let m : ℕ → ℝ → ℝ := fun n x => (P n).eval x - a x
  have hm (n : ℕ) : Function.HasTemperateGrowth (m n) :=
    (polynomial_eval_hasTemperateGrowth (P n)).sub ha
  apply tendsto_zero_of_uniform_tsupport_of_tendsto_zero_weight_seminorms hT
  · intro n
    have hs := tsupport_smulLeftCLM_pow_ofReal_subset (m n) 1 f
    simpa [m] using hs.trans hf
  · intro k
    rw [Metric.tendsto_nhds]
    intro ε hε
    let C : ℝ := ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 (k - i) f
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let δ : ℝ := ε / (1 + C)
    have hden : 0 < 1 + C := by positivity
    have hδ : 0 < δ := div_pos hε hden
    have hev : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1), ∀ x ∈ Icc (-T) T,
        |(Polynomial.derivative^[j] (P n)).eval x - iteratedDeriv j a x| < δ := by
      rw [Finset.eventually_all]
      intro j _hj
      exact hP j δ hδ
    filter_upwards [hev] with n hn
    rw [dist_zero_right]
    rw [Real.norm_of_nonneg (by positivity)]
    have hder : ∀ t ∈ tsupport f, ∀ j : ℕ, j ≤ k →
        ‖iteratedDeriv j (m n) t‖ ≤ δ := by
      intro t ht j hj
      have htI : t ∈ Icc (-T) T := by
        have habs := hf ht
        exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩
      have hnear := hn j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) t htI
      have hpoly : ContDiffAt ℝ j (fun x : ℝ => (P n).eval x) t :=
        ((P n).contDiff_aeval (j : WithTop ℕ∞)).contDiffAt
      have ha' : ContDiffAt ℝ j a t := ha.1.contDiffAt.of_le (by exact_mod_cast le_top)
      rw [show iteratedDeriv j (m n) t =
          iteratedDeriv j (fun x => (P n).eval x) t - iteratedDeriv j a t by
            exact iteratedDeriv_sub hpoly ha']
      rw [Polynomial.iteratedDeriv_eval_eq_eval_iterateDerivative]
      simpa [Real.norm_eq_abs] using hnear.le
    have hsemi := seminorm_zero_smulLeftCLM_ofReal_le_smoothMultiplierErrorEnvelope
      (m n) (hm n) f hδ.le k hder
    have henv : smoothMultiplierErrorEnvelope f δ k < ε := by
      dsimp [smoothMultiplierErrorEnvelope, δ, C]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    simpa [m] using hsemi.trans_lt henv

end SchwartzMap
