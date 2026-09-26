import GaloisForLFunctions.RHTower.Gamma0MaassHeckeOperator
import GaloisForLFunctions.RHTower.SelbergMaassRationalTraceFourierAggregation

/-!
# Fourier coefficients of `T_p` on `Γ₀(M)` Maass cusp forms

For a continuous function `F` on the upper half-plane that is `1`-periodic, write
`F̂(n; y) = ∫₀¹ F(x+iy) e(-nx) dx`. For every prime `p`,

  `(T_pF)^(n; y) = [p ∣ n] F̂(n/p; py) + p F̂(pn; y/p)`   (`coefficient_heckeT`).

* The term `F(pz)` is handled by dilation: its coefficient is the period-`p` coefficient
  of the slice at height `py`. Splitting `[0, p]` into unit intervals turns that into the
  geometric sum `Σ_{j<p} e(-nj/p) = p·[p ∣ n]` (`sum_kernel_nat`, `coeff_period_nat`).
* The translates `F((z+b)/p)`, `b mod p`, are handled by the substitution `x = pt − b`.
  It maps `[0, 1]` onto `[b/p, (b+1)/p]`, and these intervals tile `[0, 1]`
  (`coeff_sum_translates`).

For a Maass cusp form on `Γ₀(M)`, periodicity comes from `(1 1; 0 1) ∈ Γ₀(M)`
(`maass_coefficient_heckeT`).
-/

open MeasureTheory Complex
open _root_.RHTower

namespace GaloisForLFunctions.RHTower.Gamma0MaassHecke

noncomputable section

theorem kernel_add_nat (T : ℝ) (n : ℤ) (x : ℝ) (j : ℕ) :
    deningerFourierKernel T n (x + j) = deningerFourierKernel T n j * deningerFourierKernel T n x := by
  unfold deningerFourierKernel
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cexp_int_mul (k : ℤ) : Complex.exp (2 * Real.pi * Complex.I * k) = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * k = k * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- The finite geometric sum `Σ_{j<p} e(-nj/p)` is `p` if `p ∣ n` and `0` otherwise. -/
theorem sum_kernel_nat {p : ℕ} (hp : 0 < p) (n : ℤ) :
    ∑ j ∈ Finset.range p, deningerFourierKernel p n j = if (p : ℤ) ∣ n then (p : ℂ) else 0 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set ζ : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * n) / p)
  have hj : ∀ j : ℕ, deningerFourierKernel p n j = ζ ^ j := by
    intro j
    unfold deningerFourierKernel
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hj]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hζ : ζ = 1 := by
      simp only [ζ]
      rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((p * m : ℤ) : ℂ)) / p =
          ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [hζ]
  · have hζ1 : ζ ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
      apply hdvd
      refine ⟨-k, ?_⟩
      have : (n : ℂ) = (p : ℂ) * (-k : ℤ) := by
        field_simp at hk
        push_cast
        linear_combination -hk
      exact_mod_cast this
    rw [geom_sum_eq hζ1]
    have hζp : ζ ^ p = 1 := by
      simp only [ζ]
      rw [← Complex.exp_nat_mul]
      rw [show (p : ℂ) * (-(2 * Real.pi * Complex.I * n) / p) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [hζp, sub_self, zero_div]

theorem intervalIntegrable_kernel_mul (T : ℝ) (n : ℤ) {G : ℝ → ℂ} (hG : Continuous G) (a b : ℝ) :
    IntervalIntegrable (fun x => deningerFourierKernel T n x * G x) volume a b :=
  ((deningerFourierKernel_continuous T n).mul hG).intervalIntegrable a b

theorem periodic_add_nat {G : ℝ → ℂ} (hper : Function.Periodic G 1) (x : ℝ) (j : ℕ) :
    G (x + j) = G x := by
  have := (hper.nat_mul j) x
  simpa using this

/-- The coefficient over the period `p` of a `1`-periodic function: `ĝ_p(n) = [p ∣ n] ĝ_1(n/p)`. -/
theorem coeff_period_nat {p : ℕ} (hp : 0 < p) {G : ℝ → ℂ} (hG : Continuous G)
    (hper : Function.Periodic G 1) (n : ℤ) :
    deningerFourierCoeff p G n =
      if (p : ℤ) ∣ n then deningerFourierCoeff 1 G (n / p) else 0 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsplit : ∫ x in (0:ℝ)..p, deningerFourierKernel p n x * G x =
      ∑ j ∈ Finset.range p, ∫ x in ((j : ℕ) : ℝ)..((j + 1 : ℕ) : ℝ),
        deningerFourierKernel p n x * G x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ))]
    · simp
    · intro k _; exact intervalIntegrable_kernel_mul _ n hG _ _
  have hshift : ∀ j : ℕ, ∫ x in ((j : ℕ) : ℝ)..((j + 1 : ℕ) : ℝ),
      deningerFourierKernel p n x * G x =
      deningerFourierKernel p n j * ∫ x in (0:ℝ)..1, deningerFourierKernel p n x * G x := by
    intro j
    have h1 := intervalIntegral.integral_comp_add_right
      (fun x => deningerFourierKernel p n x * G x) (j : ℝ) (a := 0) (b := 1)
    rw [zero_add, add_comm (1 : ℝ)] at h1
    rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring, ← h1,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [kernel_add_nat, periodic_add_nat hper]
    ring
  unfold deningerFourierCoeff
  rw [hsplit]
  simp_rw [hshift]
  rw [← Finset.sum_mul, sum_kernel_nat hp n]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne')]
    have hk : ∀ x : ℝ, deningerFourierKernel p (p * m) x = deningerFourierKernel 1 m x := by
      intro x
      unfold deningerFourierKernel
      congr 1
      push_cast
      field_simp
    simp_rw [hk]
    push_cast
    field_simp
  · simp

/-- The sum over `j < p` of the coefficients of `x ↦ G((x + j)/p)` is `p ĝ(pn)`. -/
theorem coeff_sum_translates {p : ℕ} (hp : 0 < p) {G : ℝ → ℂ} (hG : Continuous G)
    (n : ℤ) :
    ∑ j ∈ Finset.range p, deningerFourierCoeff 1 (fun x => G ((x + j) / p)) n =
      p * deningerFourierCoeff 1 G (p * n) := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hj : ∀ j : ℕ, deningerFourierCoeff 1 (fun x => G ((x + j) / p)) n =
      p * ∫ t in (j : ℝ) / p..((j + 1 : ℕ) : ℝ) / p, deningerFourierKernel 1 (p * n) t * G t := by
    intro j
    unfold deningerFourierCoeff
    have h1 := intervalIntegral.integral_comp_mul_sub
      (fun x => deningerFourierKernel 1 n x * G ((x + j) / p)) hp' (j : ℝ)
      (a := (j : ℝ) / p) (b := ((j + 1 : ℕ) : ℝ) / p)
    rw [show (p : ℝ) * ((j : ℝ) / p) - j = 0 by field_simp; ring,
      show (p : ℝ) * (((j + 1 : ℕ) : ℝ) / p) - j = 1 by push_cast; field_simp; ring] at h1
    have h2 : ∫ x in (0:ℝ)..1, deningerFourierKernel 1 n x * G ((x + j) / p) =
        p * ∫ t in (j : ℝ) / p..((j + 1 : ℕ) : ℝ) / p,
          deningerFourierKernel 1 n (p * t - j) * G ((p * t - j + j) / p) := by
      rw [h1, Complex.real_smul, ← mul_assoc]
      push_cast
      rw [mul_inv_cancel₀ (by exact_mod_cast hp'), one_mul]
    simp only [Complex.ofReal_one, div_one, one_mul]
    rw [h2]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [show ((p : ℝ) * t - j + j) / p = t by field_simp; ring]
    congr 1
    unfold deningerFourierKernel
    rw [show -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (((p : ℝ) * t - j : ℝ) : ℂ)) / ((1 : ℝ) : ℂ) =
        -(2 * Real.pi * Complex.I * ((p * n : ℤ) : ℂ) * (t : ℂ)) / ((1 : ℝ) : ℂ) +
          ((n * j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hj]
  rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ) / p)]
  · unfold deningerFourierCoeff
    simp [hp']
  · intro k _; exact intervalIntegrable_kernel_mul _ _ hG _ _

section Hecke

open SelbergMaassMean UpperHalfPlane

/-- `ZMod p ≃ Fin p` through the canonical representative. -/
def zmodFin (p : ℕ) [NeZero p] : ZMod p ≃ Fin p where
  toFun b := ⟨b.val, ZMod.val_lt b⟩
  invFun j := ((j : ℕ) : ZMod p)
  left_inv b := ZMod.natCast_zmod_val b
  right_inv j := Fin.ext (ZMod.val_cast_of_lt j.2)

theorem point_mul_nat (p : ℕ) (x y : ℝ) : (p : ℂ) * point x y = point (p * x) (p * y) := by
  unfold point; push_cast; ring

theorem point_add_div_nat {p : ℕ} (hp : (p : ℂ) ≠ 0) (x y : ℝ) (b : ℕ) :
    (point x y + (b : ℂ)) / p = point ((x + b) / p) (y / p) := by
  unfold point; push_cast; field_simp; ring

/-- **Fourier coefficients of `T_p F`.** For a continuous `1`-periodic `F` on the upper
half-plane, the `n`-th coefficient of `T_pF` at height `y` is
`[p ∣ n] F̂(n/p; py) + p F̂(pn; y/p)`. -/
theorem coefficient_heckeT {p : ℕ} [hp : Fact p.Prime] {F : ℂ → ℂ}
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hper : ∀ z : ℂ, 0 < z.im → F (z + 1) = F z) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    SelbergMaassFourier.coefficient 1 n (heckeT p F) y =
      (if (p : ℤ) ∣ n then SelbergMaassFourier.coefficient 1 (n / p) F (p * y) else 0) +
        p * SelbergMaassFourier.coefficient 1 (p * n) F (y / p) := by
  have hp0 : 0 < p := hp.out.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  set G₁ : ℝ → ℂ := fun x => F (point x (p * y))
  set G₂ : ℝ → ℂ := fun x => F (point x (y / p))
  have hG₁ : Continuous G₁ := slice_continuous hF (by positivity)
  have hG₂ : Continuous G₂ := slice_continuous hF (by positivity)
  have hper₁ : Function.Periodic G₁ 1 := by
    intro x
    simp only [G₁]
    rw [show point (x + 1) (p * y) = point x (p * y) + 1 by unfold point; push_cast; ring]
    apply hper
    simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    positivity
  have hslice : (fun x => heckeT p F (point x y)) =
      (fun x => G₁ (p * x)) + fun x => ∑ j : Fin p, G₂ ((x + (j : ℕ)) / p) := by
    funext x
    simp only [heckeT, Fintype.sum_option, heckeAct, Pi.add_apply, G₁, G₂]
    congr 1
    · rw [point_mul_nat]
    · refine Fintype.sum_equiv (zmodFin p) _ _ fun b => ?_
      simp only [zmodFin, Equiv.coe_fn_mk]
      rw [point_add_div_nat hpC]
  have hc₁ : Continuous fun x => G₁ (p * x) := hG₁.comp (continuous_const.mul continuous_id)
  have hc₂ : Continuous fun x => ∑ j : Fin p, G₂ ((x + (j : ℕ)) / p) := by
    refine continuous_finsetSum _ fun j _ => hG₂.comp ?_
    exact (continuous_id.add continuous_const).div_const _
  unfold SelbergMaassFourier.coefficient
  rw [hslice, _root_.RHTower.deningerFourierCoeff_add _ _ n
    (intervalIntegrable_kernel_mul _ n hc₁ _ _) (intervalIntegrable_kernel_mul _ n hc₂ _ _)]
  congr 1
  · rw [deningerFourierCoeff_comp_mul one_ne_zero hpR.ne' n, mul_one,
      coeff_period_nat hp0 hG₁ hper₁ n]
  · have hcj : ∀ j : Fin p, Continuous (fun x : ℝ => G₂ ((x + (j : ℕ)) / p)) := fun j =>
      hG₂.comp ((continuous_id.add continuous_const).div_const _)
    rw [deningerFourierCoeff_fintype_sum 1 n (fun (j : Fin p) x => G₂ ((x + (j : ℕ)) / p)) hcj]
    rw [← Finset.sum_range (fun j => deningerFourierCoeff 1 (fun x => G₂ ((x + j) / p)) n),
      coeff_sum_translates hp0 hG₂ n]

/-- A `Γ₀(M)`-invariant function on `ℍ`, read on `ℂ`, is `1`-periodic on the upper half-plane. -/
theorem gamma0_periodic {M : ℕ} {f : ℍ → ℂ}
    (hf : f ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 M)))
    (z : ℂ) (hz : 0 < z.im) : (f ∘ UpperHalfPlane.ofComplex) (z + 1) = (f ∘ UpperHalfPlane.ofComplex) z := by
  have h := gamma0Inv_of_mem hf 1 1 0 1 (by norm_num) (dvd_zero _) z hz
  rwa [show mobC 1 1 0 1 z = z + 1 by simp [mobC]] at h

/-- **Hecke action on the Fourier coefficients of a `Γ₀(M)` Maass cusp form.** -/
theorem maass_coefficient_heckeT {p : ℕ} [Fact p.Prime] {M : ℕ} {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 M)) lam) (n : ℤ) {y : ℝ}
    (hy : 0 < y) :
    SelbergMaassFourier.coefficient 1 n (heckeT p (f.1.1 ∘ UpperHalfPlane.ofComplex)) y =
      (if (p : ℤ) ∣ n then
        SelbergMaassFourier.coefficient 1 (n / p) (f.1.1 ∘ UpperHalfPlane.ofComplex) (p * y)
      else 0) +
        p * SelbergMaassFourier.coefficient 1 (p * n) (f.1.1 ∘ UpperHalfPlane.ofComplex) (y / p) :=
  coefficient_heckeT (f.2.2.1.1.continuousOn) (gamma0_periodic f.1.2) n hy

end Hecke

end

end GaloisForLFunctions.RHTower.Gamma0MaassHecke
