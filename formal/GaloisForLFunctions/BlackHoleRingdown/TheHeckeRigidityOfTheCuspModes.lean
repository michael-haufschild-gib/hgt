import GaloisForLFunctions.BlackHoleRingdown.TheHeckeEigenformsOfTheCuspChannel
import GaloisForLFunctions.RHTower.Deninger.DeningerSmoothCoeffInjective

/-!
# The Hecke rigidity of the cusp modes

A Hecke eigenform of the cusp channel is determined by its eigenvalue data and its two first Fourier
modes. Write `a_n(y) = ∫₀¹ f(x+iy) e(-nx) dx`. If `T_p f = c_p f`, the coefficient formula of `T_p` gives
the recursion

  `c_p a_n(y) = [p ∣ n] a_{n/p}(py) + p a_{pn}(y/p)`.

Read at height `py` with `n = pm`, it expresses `a_{pm}` through `a_m` and `a_{m/p}`, indices of smaller size.
Since `a_0 = 0`, strong induction on `|n|` shows that `a_{±1} ≡ 0` forces every `a_n ≡ 0`, and the Fourier
expansion of each horocycle then forces `f = 0` (`eq_zero_of_firstCoeff_eq_zero`).

So a cusp mode is fixed by `(λ, (c_p)_p, a_1, a_{-1})` (`eq_of_heckeData`), and every nonzero Hecke eigenform
has a nonzero first mode (`exists_firstCoeff_ne_zero`): the arithmetic of the cusp channel is carried by its
first Fourier channel.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.Gamma0MaassHecke
  GaloisForLFunctions.RHTower.DeckPointPair
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)

namespace HeckeCusp

/-- The `n`-th Fourier coefficient of a function on `ℍ` along the horocycle at height `y`. -/
def fourierCoeff (g : UpperHalfPlane → ℂ) (n : ℤ) (y : ℝ) : ℂ :=
  SelbergMaassFourier.coefficient 1 n (g ∘ ofComplex) y

theorem point_im_pos {x y : ℝ} (hy : 0 < y) : 0 < (SelbergMaassMean.point x y).im := by
  simp [SelbergMaassMean.point, hy]

theorem coefficient_congr {F G : ℂ → ℂ} {y : ℝ} (hy : 0 < y) (h : ∀ w : ℂ, 0 < w.im → F w = G w)
    (n : ℤ) : SelbergMaassFourier.coefficient 1 n F y = SelbergMaassFourier.coefficient 1 n G y := by
  unfold SelbergMaassFourier.coefficient _root_.RHTower.deningerFourierCoeff
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only
  rw [h _ (point_im_pos hy)]

theorem coefficient_mul (c : ℂ) (F : ℂ → ℂ) (n : ℤ) (y : ℝ) :
    SelbergMaassFourier.coefficient 1 n (fun w => c * F w) y = c * SelbergMaassFourier.coefficient 1 n F y := by
  unfold SelbergMaassFourier.coefficient _root_.RHTower.deningerFourierCoeff
  rw [mul_left_comm c (1 / ((1 : ℝ) : ℂ)), ← intervalIntegral.integral_const_mul (μ := volume) c]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only
  ring

theorem coefficient_sub (F G : ℂ → ℂ) (n : ℤ) {y : ℝ}
    (hF : Continuous fun x : ℝ => F (SelbergMaassMean.point x y))
    (hG : Continuous fun x : ℝ => G (SelbergMaassMean.point x y)) :
    SelbergMaassFourier.coefficient 1 n (fun w => F w - G w) y =
      SelbergMaassFourier.coefficient 1 n F y - SelbergMaassFourier.coefficient 1 n G y := by
  unfold SelbergMaassFourier.coefficient _root_.RHTower.deningerFourierCoeff
  rw [← mul_sub, ← intervalIntegral.integral_sub]
  · congr 2
    funext x
    ring
  · have hk : Continuous (_root_.RHTower.deningerFourierKernel 1 n) := by
      unfold _root_.RHTower.deningerFourierKernel
      fun_prop
    exact (hk.mul hF).intervalIntegrable _ _
  · have hk : Continuous (_root_.RHTower.deningerFourierKernel 1 n) := by
      unfold _root_.RHTower.deningerFourierKernel
      fun_prop
    exact (hk.mul hG).intervalIntegrable _ _

variable {lam : ℝ} {g : UpperHalfPlane → ℂ}

theorem fourierCoeff_zero (hg : g ∈ cuspSpace lam) {y : ℝ} (hy : 0 < y) : fourierCoeff g 0 y = 0 := by
  rw [fourierCoeff, coefficient_zero]
  exact hg.2.2.2 y hy

/-- **The Hecke recursion of the Fourier modes.** -/
theorem hecke_recursion (hg : g ∈ cuspSpace lam) (p : ℕ) [hp : Fact p.Prime] {c : ℂ}
    (hc : heckeH p g = c • g) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    c * fourierCoeff g n y =
      (if (p : ℤ) ∣ n then fourierCoeff g (n / p) (p * y) else 0) + p * fourierCoeff g (p * n) (y / p) := by
  have hF : ContinuousOn (g ∘ ofComplex) {z : ℂ | 0 < z.im} := hg.2.1.1.continuousOn
  have h1 := coefficient_heckeT (p := p) hF (periodic_comp hg) n hy
  have h2 : SelbergMaassFourier.coefficient 1 n (heckeT p (g ∘ ofComplex)) y =
      SelbergMaassFourier.coefficient 1 n (fun w => c * (g ∘ ofComplex) w) y := by
    refine coefficient_congr hy (fun w hw => ?_) n
    rw [← heckeH_comp_ofComplex p g hw, hc]
    rfl
  rw [h2, coefficient_mul] at h1
  exact h1

/-- **Vanishing first modes force a Hecke eigenform to vanish.** -/
theorem eq_zero_of_firstCoeff_eq_zero (hg : g ∈ cuspSpace lam)
    (hH : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g)
    (h1 : ∀ y : ℝ, 0 < y → fourierCoeff g 1 y = 0) (hm1 : ∀ y : ℝ, 0 < y → fourierCoeff g (-1) y = 0) :
    g = 0 := by
  have hall : ∀ n : ℤ, ∀ y : ℝ, 0 < y → fourierCoeff g n y = 0 := by
    intro n
    induction hk : n.natAbs using Nat.strong_induction_on generalizing n with
    | _ k ih =>
      intro y hy
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · rw [Int.natAbs_eq_zero.mp hk]
          exact fourierCoeff_zero hg hy
        · rcases Int.natAbs_eq_iff.mp hk with h | h
          · rw [h]
            exact h1 y hy
          · rw [h]
            exact hm1 y hy
      · obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
        haveI := Fact.mk hp
        obtain ⟨c, hc⟩ := hH p
        have hpn : (p : ℤ) ∣ n := by
          rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, hk]
          exact hpk
        obtain ⟨m, rfl⟩ := hpn
        have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        have hk' : k = p * m.natAbs := by rw [← hk, Int.natAbs_mul, Int.natAbs_natCast]
        have hm : m.natAbs < k := by
          rw [hk']
          have : 0 < m.natAbs := by
            rcases Nat.eq_zero_or_pos m.natAbs with h0 | h0
            · rw [h0, mul_zero] at hk'
              omega
            · exact h0
          nlinarith [hp.two_le]
        have hrec := hecke_recursion hg p hc m (show 0 < (p : ℝ) * y by have := hp.pos; positivity)
        rw [ih _ hm m rfl _ (by have := hp.pos; positivity)] at hrec
        have hdiv : (if (p : ℤ) ∣ m then fourierCoeff g (m / p) (p * (p * y)) else 0) = 0 := by
          split_ifs with hpm
          · obtain ⟨m', hm'⟩ := hpm
            rw [hm', Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)]
            refine ih _ ?_ _ rfl _ (by have := hp.pos; positivity)
            have : m'.natAbs ≤ m.natAbs := by
              rw [hm', Int.natAbs_mul, Int.natAbs_natCast]
              exact Nat.le_mul_of_pos_left _ hp.pos
            omega
          · rfl
        rw [hdiv, zero_add, mul_zero] at hrec
        have hyp : (p : ℝ) * y / p = y := by
          have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
          field_simp
        rw [hyp] at hrec
        have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
        exact (mul_eq_zero.mp hrec.symm).resolve_left hpC
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  funext z
  have hy := z.im_pos
  have hper : Function.Periodic (fun x : ℝ => g (ofComplex (SelbergMaassMean.point x z.im))) 1 := by
    intro x
    have h := periodic_comp hg (SelbergMaassMean.point x z.im) (point_im_pos hy)
    simp only [Function.comp] at h
    have e : SelbergMaassMean.point (x + 1) z.im = SelbergMaassMean.point x z.im + 1 := by
      simp [SelbergMaassMean.point]
      ring
    simp only
    rw [e, h]
  have hslice := _root_.RHTower.deningerSmoothPeriodic_eq_zero_of_coeff (T := 1)
    (continuous_slice hg.2.1 hy) hper fun n => hall n z.im hy
  have hz : ofComplex (SelbergMaassMean.point z.re z.im) = z := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (point_im_pos hy)]
    simp [SelbergMaassMean.point]
    exact Complex.re_add_im (z : ℂ)
  have := congrFun hslice z.re
  simp only [hz, Pi.zero_apply] at this
  exact this

/-- **Multiplicity one in the Hecke sense.** Two Hecke eigenforms of the same eigenvalue, with the same Hecke
eigenvalues and the same first modes, coincide. -/
theorem eq_of_heckeData {g' : UpperHalfPlane → ℂ} (hg : g ∈ cuspSpace lam) (hg' : g' ∈ cuspSpace lam)
    (c : ℕ → ℂ) (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g)
    (hc' : ∀ (p : ℕ) [Fact p.Prime], heckeH p g' = c p • g')
    (h1 : ∀ y : ℝ, 0 < y → fourierCoeff g 1 y = fourierCoeff g' 1 y)
    (hm1 : ∀ y : ℝ, 0 < y → fourierCoeff g (-1) y = fourierCoeff g' (-1) y) : g = g' := by
  have hd : g - g' ∈ cuspSpace lam := Submodule.sub_mem _ hg hg'
  have hsub : ∀ n y, 0 < y → fourierCoeff (g - g') n y = fourierCoeff g n y - fourierCoeff g' n y := by
    intro n y hy
    exact coefficient_sub _ _ n (continuous_slice hg.2.1 hy) (continuous_slice hg'.2.1 hy)
  have hH : ∀ (p : ℕ) [Fact p.Prime], ∃ e : ℂ, heckeH p (g - g') = e • (g - g') := by
    intro p _
    refine ⟨c p, ?_⟩
    have hlin : heckeH p (g - g') = heckeH p g - heckeH p g' := by
      funext z
      simp [heckeH, Finset.sum_sub_distrib]
    rw [hlin, hc p, hc' p, smul_sub]
  have h0 := eq_zero_of_firstCoeff_eq_zero hd hH (fun y hy => by rw [hsub 1 y hy, h1 y hy, sub_self])
    (fun y hy => by rw [hsub (-1) y hy, hm1 y hy, sub_self])
  exact sub_eq_zero.mp h0

/-- **Every nonzero Hecke eigenform has a nonzero first mode.** -/
theorem exists_firstCoeff_ne_zero (hg : g ∈ cuspSpace lam) (hg0 : g ≠ 0)
    (hH : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g) :
    ∃ y : ℝ, 0 < y ∧ (fourierCoeff g 1 y ≠ 0 ∨ fourierCoeff g (-1) y ≠ 0) := by
  by_contra hcon
  push Not at hcon
  exact hg0 (eq_zero_of_firstCoeff_eq_zero hg hH (fun y hy => (hcon y hy).1) fun y hy => (hcon y hy).2)

/-- **Every eigenvalue of the cusp spectrum carries a Hecke eigenform with a nonzero first mode.** -/
theorem exists_heckeMaassForm_firstCoeff (i : CuspEigenIndex 0) :
    ∃ g ∈ cuspSpace i.1, (∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeH p g = c • g) ∧
      ∃ y : ℝ, 0 < y ∧ (fourierCoeff g 1 y ≠ 0 ∨ fourierCoeff g (-1) y ≠ 0) := by
  obtain ⟨g, hg, hg0, hH⟩ := exists_heckeEigenform (cuspSpace_ne_bot i)
  exact ⟨g, hg, hH, exists_firstCoeff_ne_zero hg hg0 hH⟩

end HeckeCusp

end GaloisForLFunctions.BlackHoleRingdown
