import GaloisForLFunctions.RHTower.SelbergPoincareIntegrability
import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes

open MeasureTheory UpperHalfPlane Set
open scoped MatrixGroups

/-!
# The unfolded Poincaré pairing as a modal integral

In coordinates the strip integrand `y^s e(mz/N) g(z) y^{-2}` is dominated by `B y^{σ-2} e^{-2πmy/N}`, so Fubini
applies on `[0, N) × (0, ∞)`, and the horizontal integral is `N` times the Fourier coefficient of `g` of index
`-m` (`strip_integral_eq`). With the unfolding identity:
`∫_{cellP} P_m(z, s) g(z) dμ = N ∫_0^∞ y^{s-2} e^{-2πmy/N} a_{-m}(y) dy` (`poincare_pairing`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincarePairing

open GaloisForLFunctions.RHTower.SelbergPoincare GaloisForLFunctions.RHTower.SelbergPoincareUnfolding
open GaloisForLFunctions.RHTower.SelbergPoincareIntegrability
open GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergMaassFourier

theorem ofComplex_point (z : ℍ) : ofComplex (point z.re z.im) = z := by
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (by simpa [point] using z.im_pos)]
  apply Complex.ext <;> simp [point]

theorem stripN_eq (N : ℕ) : stripN N = {z : ℍ | (z.re, z.im) ∈ Ico (0 : ℝ) N ×ˢ Ioi 0} := by
  ext z; simp [stripN, z.im_pos]

/-- The strip integrand in coordinates. -/
noncomputable def coordF (N m : ℕ) (s : ℂ) (g : ℍ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.2 : ℂ)) ^ s * Complex.exp (2 * Real.pi * Complex.I * m * point p.1 p.2 / N) *
    g (ofComplex (point p.1 p.2))

theorem coordF_eq (N m : ℕ) (s : ℂ) (g : ℍ → ℂ) (z : ℍ) :
    coordF N m s g (z.re, z.im) = term N m s z 1 * g z := by
  rw [coordF, term_one, ofComplex_point]
  congr 3
  simp only [point]
  congr 2
  apply Complex.ext <;> simp

theorem coordF_div_eq (N m : ℕ) (s : ℂ) (g : ℍ → ℂ) {x y : ℝ} (hy : 0 < y) :
    coordF N m s g (x, y) / ((y : ℂ)) ^ 2 =
      ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
        (_root_.RHTower.deningerFourierKernel N (-(m : ℤ)) x * (g ∘ ofComplex) (point x y)) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [coordF, Complex.cpow_sub _ _ hy0, show ((y : ℂ)) ^ (2 : ℂ) = (y : ℂ) ^ (2 : ℕ) by
    rw [← Complex.cpow_natCast]; norm_num]
  simp only [_root_.RHTower.deningerFourierKernel, Function.comp_apply, point]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * m * ((x : ℂ) + y * Complex.I) / N) =
      Complex.exp ((-(2 * Real.pi * m * y / N) : ℝ)) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((-(m : ℤ) : ℤ) : ℂ) * x) / N) := by
    rw [← Complex.exp_add]; congr 1; push_cast
    by_cases hN : (N : ℂ) = 0
    · simp [hN]
    · field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [hexp]
  field_simp
  push_cast
  ring

theorem continuousOn_g_point {g : ℍ → ℂ} (hg : Continuous g) :
    ContinuousOn (fun p : ℝ × ℝ => g (ofComplex (point p.1 p.2))) (Ico (0 : ℝ) N ×ˢ Ioi 0) := by
  intro p hp
  have hp2 : 0 < p.2 := hp.2
  have h1 : ContinuousAt (fun p : ℝ × ℝ => point p.1 p.2) p := by unfold point; fun_prop
  have hpos : 0 < (point p.1 p.2).im := by simpa [point] using hp2
  have h2 : ContinuousAt ofComplex (point p.1 p.2) :=
    ofComplex.continuousAt (by exact ⟨⟨_, hpos⟩, Set.mem_univ _, rfl⟩)
  exact (hg.continuousAt.comp (ContinuousAt.comp (f := fun p : ℝ × ℝ => point p.1 p.2) h2 h1)).continuousWithinAt

theorem norm_coordF_div (N m : ℕ) [NeZero N] (s : ℂ) {g : ℍ → ℂ} {B : ℝ} (hgb : ∀ z, ‖g z‖ ≤ B)
    {x y : ℝ} (hy : 0 < y) :
    ‖coordF N m s g (x, y) / ((y : ℂ)) ^ 2‖ ≤ B * (y ^ (s.re - 2) * Real.exp (-(2 * Real.pi * m / N) * y)) := by
  rw [coordF_div_eq N m s g hy, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    ← Complex.ofReal_exp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hk : ‖_root_.RHTower.deningerFourierKernel N (-(m : ℤ)) x‖ = 1 := by
    simp only [_root_.RHTower.deningerFourierKernel, Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [hk, one_mul, Complex.sub_re, Complex.re_ofNat]
  have hB := hgb (ofComplex (point x y))
  have hpos : 0 ≤ y ^ (s.re - 2) * Real.exp (-(2 * Real.pi * m / N) * y) := by positivity
  have he : Real.exp (-(2 * Real.pi * m * y / N)) = Real.exp (-(2 * Real.pi * m / N) * y) := by
    congr 1; ring
  rw [he]
  simp only [Function.comp_apply]
  nlinarith [norm_nonneg (g (ofComplex (point x y)))]

/-- **The strip integral as a modal integral.** -/
theorem strip_integral_eq (N m : ℕ) [NeZero N] (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re) {g : ℍ → ℂ}
    (hgc : Continuous g) {B : ℝ} (hgb : ∀ z, ‖g z‖ ≤ B) :
    ∫ z in stripN N, term N m s z 1 * g z =
      N * ∫ y in Ioi (0 : ℝ), ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
        coefficient N (-(m : ℤ)) (g ∘ ofComplex) y := by
  have hA : MeasurableSet (Ico (0 : ℝ) N ×ˢ Ioi (0 : ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  have hpos : ∀ p ∈ Ico (0 : ℝ) N ×ˢ Ioi (0 : ℝ), 0 < p.2 := fun p hp => hp.2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hc : 0 < 2 * Real.pi * m / N := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  rw [stripN_eq]
  have h1 : ∫ z in {z : ℍ | (z.re, z.im) ∈ Ico (0 : ℝ) N ×ˢ Ioi 0}, term N m s z 1 * g z =
      ∫ z in {z : ℍ | (z.re, z.im) ∈ Ico (0 : ℝ) N ×ˢ Ioi 0}, coordF N m s g (z.re, z.im) := by
    congr 1; funext z; rw [coordF_eq]
  rw [h1, _root_.RHTower.setIntegral_coord_eq hA hpos]
  -- integrability on the product
  have hint : IntegrableOn (fun p : ℝ × ℝ => coordF N m s g p / ((p.2 : ℝ) : ℂ) ^ 2)
      (Ico (0 : ℝ) N ×ˢ Ioi 0) := by
    have h1 : IntegrableOn (fun y : ℝ => y ^ (s.re - 2) * Real.exp (-(2 * Real.pi * m / N) * y ^ (1 : ℝ)))
        (Ioi 0) := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl hc
    have h1' : Integrable (fun y : ℝ => B * (y ^ (s.re - 2) * Real.exp (-(2 * Real.pi * m / N) * y)))
        (volume.restrict (Ioi 0)) := by
      refine (h1.const_mul B).congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun y _ => ?_))
      simp [Real.rpow_one]
    have hprod := (integrable_const (1 : ℝ) (μ := volume.restrict (Ico (0 : ℝ) N))).mul_prod h1'
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    refine Integrable.mono' hprod ?_ ?_
    · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      apply ContinuousOn.aestronglyMeasurable _ hA
      intro p hp
      have hp2 : 0 < p.2 := hp.2
      have hc1 : ContinuousWithinAt (fun p : ℝ × ℝ => ((p.2 : ℂ)) ^ s) (Ico (0 : ℝ) N ×ˢ Ioi 0) p :=
        ((Complex.continuous_ofReal.comp continuous_snd).continuousAt.cpow continuousAt_const
          (Complex.ofReal_mem_slitPlane.mpr hp2)).continuousWithinAt
      have hc2 : ContinuousWithinAt (fun p : ℝ × ℝ =>
          Complex.exp (2 * Real.pi * Complex.I * m * point p.1 p.2 / N)) (Ico (0 : ℝ) N ×ˢ Ioi 0) p := by
        unfold point; fun_prop
      have hc3 := continuousOn_g_point (N := N) hgc p hp
      have hc4 : ContinuousWithinAt (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) ^ 2) (Ico (0 : ℝ) N ×ˢ Ioi 0) p := by
        fun_prop
      exact ((hc1.mul hc2).mul hc3).div hc4 (by exact_mod_cast (pow_pos hp2 2).ne')
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem hA (fun p hp => ?_)
      simp only [one_mul]
      have := norm_coordF_div N m s hgb (x := p.1) hp.2
      simpa using this
  rw [_root_.RHTower.setIntegral_prod_eq_iterated hint, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := hy
  simp only
  rw [setIntegral_congr_fun measurableSet_Ico (fun x _ => coordF_div_eq N m s g (x := x) hy0),
    integral_const_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN0.le]
  simp only [coefficient, _root_.RHTower.deningerFourierCoeff]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  push_cast
  field_simp

open GaloisForLFunctions.RHTower.SarnakXuePretrace CongruenceSubgroup in
/-- **Unfolded Poincaré pairing.** For `N ≥ 3`, `m ≥ 1`, `Re s > 1` and a continuous bounded
`Γ(N)`-invariant `g` with Fourier coefficients `a_n(y)` of period `N`,
`∫_{cellP} P_m(z, s) g(z) dμ = N ∫_0^∞ y^{s-2} e^{-2πmy/N} a_{-m}(y) dy`. -/
theorem poincare_pairing (N : ℕ) [NeZero N] (hN : 3 ≤ N) {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re)
    {g : ℍ → ℂ} (hgc : Continuous g) {B : ℝ} (hgb : ∀ z, ‖g z‖ ≤ B)
    (hg : ∀ (γ : Gamma N) z, g ((γ : SL(2, ℤ)) • z) = g z) :
    ∫ z in cellP N, poincare N m s z * g z =
      N * ∫ y in Ioi (0 : ℝ), ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
        coefficient N (-(m : ℤ)) (g ∘ ofComplex) y := by
  rw [poincare_unfold' N hN hm hs hgc hgb hg, strip_integral_eq N m hm hs hgc hgb]

end GaloisForLFunctions.RHTower.SelbergPoincarePairing
