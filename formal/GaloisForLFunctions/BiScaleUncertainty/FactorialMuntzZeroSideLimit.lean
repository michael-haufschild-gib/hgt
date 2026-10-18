import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzZeroReadout
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-! Absolute convergence and the actual infinite zero-side smoothing limit.
The resulting corrected-source form is nonnegative without RH. -/

open MeasureTheory Complex Filter Set
open scoped Topology ComplexConjugate
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
noncomputable section
set_option autoImplicit false

def factorialMuntzZeroMajorant (n : ℕ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  (2*(factorialMuntzBoundaryCoefficient n)^2)*
    ((zetaZeroConfig.mult ρ : ℝ)/(1+Complex.normSq (gammaOf ρ)))

theorem summable_factorialMuntzZeroMajorant (n : ℕ) :
    Summable (factorialMuntzZeroMajorant n) := by
  have hs : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ)/(1+Complex.normSq (gammaOf ρ))) := by
    have h := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using h
  exact hs.mul_left (2*(factorialMuntzBoundaryCoefficient n)^2)

/-- A single summable majorant works for every normalized smoothing. -/
theorem factorialMuntzSmoothed_Wsummand_norm_uniform (n k : ℕ)
    (ρ : zetaZeroConfig.carrier) :
    ‖zetaZeroConfig.Wsummand (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ‖ ≤
      (Real.exp 1)^2*factorialMuntzZeroMajorant n ρ := by
  have hρ := zetaZeroConfig.strip _ ρ.2
  have hσ := zetaZeroConfig.strip _ (zetaZeroConfig.reflect_mem _ ρ.2)
  have h1 := factorialMuntzKernelReadout_bound k hρ.1 hρ.2
  have h2 := factorialMuntzKernelReadout_bound k hσ.1 hσ.2
  rw [factorialMuntzSmoothed_Wsummand_factor, norm_mul, norm_mul, RCLike.norm_conj]
  calc
    _ ≤ (Real.exp 1*Real.exp 1)*‖zetaZeroConfig.Wsummand
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ‖ := by
      gcongr
    _ ≤ (Real.exp 1*Real.exp 1)*factorialMuntzZeroMajorant n ρ :=
      mul_le_mul_of_nonneg_left (factorialMuntzBoundaryCorrected_Wsummand_norm_bound n ρ)
        (by positivity)
    _ = _ := by ring

theorem summable_norm_factorialMuntzBoundaryCorrected_Wsummand (n : ℕ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ‖) := by
  apply Summable.of_norm_bounded (summable_factorialMuntzZeroMajorant n)
  intro ρ
  simpa only [norm_norm, factorialMuntzZeroMajorant] using
    factorialMuntzBoundaryCorrected_Wsummand_norm_bound n ρ

theorem summable_norm_factorialMuntzSmoothed_Wsummand (n k : ℕ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (fun x => (factorialMuntzSmoothed n k x : ℂ))
        (fun x => (factorialMuntzSmoothed n k x : ℂ)) ρ‖) := by
  apply Summable.of_norm_bounded
    ((summable_factorialMuntzZeroMajorant n).mul_left ((Real.exp 1)^2))
  intro ρ
  simpa only [norm_norm] using factorialMuntzSmoothed_Wsummand_norm_uniform n k ρ

/-- The infinite zero sum really does commute with this smoothing limit. -/
theorem factorialMuntzSmoothed_W_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => zetaZeroConfig.W
      (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ))) atTop
      (𝓝 (zetaZeroConfig.W
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)))) := by
  unfold ZeroConfig.W
  exact tendsto_tsum_of_dominated_convergence
    ((summable_factorialMuntzZeroMajorant n).mul_left ((Real.exp 1)^2))
    (factorialMuntzSmoothed_Wsummand_tendsto n)
    (Eventually.of_forall fun k ρ => factorialMuntzSmoothed_Wsummand_norm_uniform n k ρ)

/-- An exact universal reciprocal-zero mass controls the whole corrected
family; the factorial dependence is precisely the squared correction. -/
theorem factorialMuntzBoundaryCorrected_W_eq_scaled (n : ℕ) :
    zetaZeroConfig.W
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) =
      (factorialMuntzBoundaryCoefficient n : ℂ)^2*
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℂ)/((ρ : ℂ)*(1-(ρ : ℂ))) := by
  unfold ZeroConfig.W
  calc
    _ = ∑' ρ : zetaZeroConfig.carrier, (factorialMuntzBoundaryCoefficient n : ℂ)^2*
        ((zetaZeroConfig.mult ρ : ℂ)/((ρ : ℂ)*(1-(ρ : ℂ)))) := by
      apply tsum_congr
      intro ρ
      rw [factorialMuntzBoundaryCorrected_Wsummand_eq]
      ring
    _ = _ := by rw [tsum_mul_left]

/-- The smoothing multiplier is independent of the factorial index. -/
theorem factorialMuntzSmoothed_W_eq_scaled (n k : ℕ) :
    zetaZeroConfig.W (fun x => (factorialMuntzSmoothed n k x : ℂ))
      (fun x => (factorialMuntzSmoothed n k x : ℂ)) =
      (factorialMuntzBoundaryCoefficient n : ℂ)^2*
        ∑' ρ : zetaZeroConfig.carrier,
          (factorialMuntzKernelReadout k ρ*conj (factorialMuntzKernelReadout k (reflect ρ)))*
            (zetaZeroConfig.mult ρ : ℂ)/((ρ : ℂ)*(1-(ρ : ℂ))) := by
  unfold ZeroConfig.W
  calc
    _ = ∑' ρ : zetaZeroConfig.carrier, (factorialMuntzBoundaryCoefficient n : ℂ)^2*
        ((factorialMuntzKernelReadout k ρ*conj (factorialMuntzKernelReadout k (reflect ρ)))*
          (zetaZeroConfig.mult ρ : ℂ)/((ρ : ℂ)*(1-(ρ : ℂ)))) := by
      apply tsum_congr
      intro ρ
      rw [factorialMuntzSmoothed_Wsummand_factor, factorialMuntzBoundaryCorrected_Wsummand_eq]
      ring
    _ = _ := by rw [tsum_mul_left]

theorem factorialMuntzSmoothed_W_cross_scale (n m k : ℕ) :
    (factorialMuntzBoundaryCoefficient m : ℂ)^2*
      zetaZeroConfig.W (fun x => (factorialMuntzSmoothed n k x : ℂ))
        (fun x => (factorialMuntzSmoothed n k x : ℂ)) =
    (factorialMuntzBoundaryCoefficient n : ℂ)^2*
      zetaZeroConfig.W (fun x => (factorialMuntzSmoothed m k x : ℂ))
        (fun x => (factorialMuntzSmoothed m k x : ℂ)) := by
  rw [factorialMuntzSmoothed_W_eq_scaled, factorialMuntzSmoothed_W_eq_scaled]
  ring

/-- The literal canonical correction has a nonnegative Weil zero-side form,
with absolute convergence already proved and no RH premise. -/
theorem factorialMuntzBoundaryCorrected_W_re_nonneg (n : ℕ) :
    0 ≤ (zetaZeroConfig.W
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))).re := by
  unfold ZeroConfig.W
  rw [Complex.re_tsum (summable_norm_factorialMuntzBoundaryCorrected_Wsummand n).of_norm]
  exact tsum_nonneg (factorialMuntzBoundaryCorrected_Wsummand_re_nonneg n)

theorem factorialMuntzBoundaryCorrected_Wsummand_re_pos (n : ℕ)
    (ρ : zetaZeroConfig.carrier) :
    0 < (zetaZeroConfig.Wsummand
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ)) ρ).re := by
  have hz : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hd : 0 < ((ρ : ℂ)*(1-(ρ : ℂ))).re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, zero_sub]
    nlinarith [mul_pos hz.2.1 (sub_pos.mpr hz.2.2), sq_nonneg (ρ : ℂ).im]
  have hd0 : (ρ : ℂ)*(1-(ρ : ℂ)) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hd
    exact (lt_irrefl 0) hd
  have hm : (0 : ℝ) < zetaZeroConfig.mult ρ := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (zetaZeroConfig.one_le_mult _ ρ.2)
  rw [factorialMuntzBoundaryCorrected_Wsummand_eq]
  have hc : (zetaZeroConfig.mult ρ : ℂ)*(factorialMuntzBoundaryCoefficient n : ℂ)^2 =
      (((zetaZeroConfig.mult ρ : ℝ)*(factorialMuntzBoundaryCoefficient n)^2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, div_eq_mul_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.inv_re]
  exact mul_pos (mul_pos hm (pow_pos (factorialMuntzBoundaryCoefficient_pos n) 2))
    (div_pos hd (Complex.normSq_pos.mpr hd0))

/-- Actual zero existence makes the corrected-source limit strictly positive. -/
theorem factorialMuntzBoundaryCorrected_W_re_pos (n : ℕ) :
    0 < (zetaZeroConfig.W
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
      (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))).re := by
  obtain ⟨ρ, h0, h1, hz⟩ := exists_riemannZeta_zero_mem_openStrip
  let q : zetaZeroConfig.carrier := ⟨ρ, hz, h0, h1⟩
  have hs := (summable_norm_factorialMuntzBoundaryCorrected_Wsummand n).of_norm
  unfold ZeroConfig.W
  rw [Complex.re_tsum hs]
  exact (Complex.hasSum_re hs.hasSum).summable.tsum_pos
    (factorialMuntzBoundaryCorrected_Wsummand_re_nonneg n) q
    (factorialMuntzBoundaryCorrected_Wsummand_re_pos n q)

/-- The complete smoothed physical difference has this same exact limit.
No separate passage to the limit in the prime or archimedean term is assumed. -/
theorem factorialMuntzSmoothed_weil_difference_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => archPoleEnergy (factorialMuntzSmoothed n k)-
      abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (factorialMuntzSmoothed n k)) atTop
      (𝓝 (zetaZeroConfig.W
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))
        (fun x => (factorialMuntzBoundaryCorrected n (factorialMuntzBoundaryCoefficient n) x : ℂ))).re) := by
  have h := (Complex.continuous_re.tendsto _).comp (factorialMuntzSmoothed_W_tendsto n)
  refine h.congr (fun k => ?_)
  dsimp only [Function.comp_def]
  rw [factorialMuntzSmoothed_weil_identity]
  ring

/-- Sufficiently narrow actual normalized smoothings have positive complete
Weil energy, including both polar branches and the Abel prime pairing. -/
theorem factorialMuntzSmoothed_weil_difference_eventually_pos (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, 0 < archPoleEnergy (factorialMuntzSmoothed n k)-
      abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (factorialMuntzSmoothed n k) :=
  (tendsto_order.1 (factorialMuntzSmoothed_weil_difference_tendsto n)).1 0
    (factorialMuntzBoundaryCorrected_W_re_pos n)

/-- One eventual smoothing range works for all factorial indices at once. -/
theorem factorialMuntzSmoothed_weil_difference_eventually_pos_uniform :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, 0 < archPoleEnergy (factorialMuntzSmoothed n k)-
      abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
        (factorialMuntzSmoothed n k) := by
  filter_upwards [factorialMuntzSmoothed_weil_difference_eventually_pos 0] with k hk
  intro n
  simp only [factorialMuntzSmoothed_weil_identity, add_sub_cancel_right] at hk ⊢
  have he := congrArg Complex.re (factorialMuntzSmoothed_W_cross_scale n 0 k)
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at he
  have hp := mul_pos (pow_pos (factorialMuntzBoundaryCoefficient_pos n) 2) hk
  rw [← he] at hp
  nlinarith [sq_nonneg (factorialMuntzBoundaryCoefficient 0)]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
