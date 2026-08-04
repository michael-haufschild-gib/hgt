import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The characteristic clock equation is ill posed for non-analytic transverse data

The clock construction solves

`∂ξ∂η u = (∑ᵢ ∂ᵢ²u + V u)/4`

by the Ovsyannikov scheme, which asks the transverse dependence to be *analytic*. That hypothesis is
not an artifact of the method. In the transverse directions the equation is elliptic — a second
derivative appears there while the null directions carry one derivative each — so the characteristic
problem inherits Hadamard's phenomenon: arbitrarily small characteristic data can produce arbitrarily
large solutions.

This file proves that, in the sharpest elementary form. The exact solutions

`u_{k,n}(ξ, η, z) = e^{-n/2} n^{-k} · exp(n ξ/2 + n η/2 + n z)`

solve the equation with `V = 0`, are bounded by `n^{-k}` on the two characteristic faces of the unit
box together with all their transverse derivatives of order below `k`, and take the value
`e^{n/2} n^{-k}` at the far corner. So no estimate bounding the solution at an interior point by any
function of finitely many transverse derivatives of the characteristic data can hold: the smooth
category is out of reach for this route, and reaching it requires the Cauchy problem on a spacelike
hypersurface rather than the characteristic one.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-! ## Derivatives of an affine exponential -/

theorem hasDerivAt_expAffine (a b x : ℝ) :
    HasDerivAt (fun w : ℝ => Real.exp (a * w + b)) (a * Real.exp (a * x + b)) x := by
  have hinner : HasDerivAt (fun w : ℝ => a * w + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h := (Real.hasDerivAt_exp (a * x + b)).comp x hinner
  rw [show a * Real.exp (a * x + b) = Real.exp (a * x + b) * a from by ring]
  exact h

theorem deriv_expAffine (a b : ℝ) :
    deriv (fun w : ℝ => Real.exp (a * w + b)) = fun x => a * Real.exp (a * x + b) := by
  funext x
  exact (hasDerivAt_expAffine a b x).deriv

theorem iteratedDeriv_scaledExpAffine (j : ℕ) (c a b : ℝ) :
    iteratedDeriv j (fun w : ℝ => c * Real.exp (a * w + b))
      = fun x => c * a ^ j * Real.exp (a * x + b) := by
  induction j with
  | zero =>
    funext x
    simp [iteratedDeriv_zero]
  | succ j ih =>
    funext x
    have hd : HasDerivAt (fun w : ℝ => c * a ^ j * Real.exp (a * w + b))
        (c * a ^ (j + 1) * Real.exp (a * x + b)) x := by
      have h := (hasDerivAt_expAffine a b x).const_mul (c * a ^ j)
      rw [show c * a ^ (j + 1) * Real.exp (a * x + b)
        = c * a ^ j * (a * Real.exp (a * x + b)) from by ring]
      exact h
    rw [iteratedDeriv_succ, ih]
    exact hd.deriv

/-! ## The Hadamard family for the characteristic equation -/

/-- The normalising factor: the family is scaled so that its characteristic data is at most
`n^{-k}`. -/
noncomputable def hadamardScale (k n : ℕ) : ℝ := Real.exp (-(n : ℝ) / 2) / (n : ℝ) ^ k

/-- An exact solution of `∂ξ∂η u = ∂_z²u/4` with characteristic data of size `n^{-k}`. -/
noncomputable def hadamardWave (k n : ℕ) (ξ η z : ℝ) : ℝ :=
  hadamardScale k n * Real.exp ((n : ℝ) / 2 * ξ + (n : ℝ) / 2 * η + (n : ℝ) * z)

theorem hadamardScale_nonneg (k n : ℕ) : 0 ≤ hadamardScale k n := by
  rw [hadamardScale]
  positivity

theorem hadamardWave_pos (k n : ℕ) (hn : 0 < n) (ξ η z : ℝ) : 0 < hadamardWave k n ξ η z := by
  have hs : 0 < hadamardScale k n := by
    rw [hadamardScale]
    have : (0 : ℝ) < (n : ℝ) ^ k := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      positivity
    positivity
  rw [hadamardWave]
  positivity

/-- The derivative along the first null coordinate. -/
theorem hasDerivAt_hadamardWave_fst (k n : ℕ) (ξ η z : ℝ) :
    HasDerivAt (fun x : ℝ => hadamardWave k n x η z)
      ((n : ℝ) / 2 * hadamardWave k n ξ η z) ξ := by
  have hEq : (fun x : ℝ => hadamardWave k n x η z)
      = fun x : ℝ => hadamardScale k n
        * Real.exp ((n : ℝ) / 2 * x + ((n : ℝ) / 2 * η + (n : ℝ) * z)) := by
    funext x
    rw [hadamardWave]
    ring_nf
  rw [hEq]
  have hbase := (hasDerivAt_expAffine ((n : ℝ) / 2) ((n : ℝ) / 2 * η + (n : ℝ) * z) ξ).const_mul
    (hadamardScale k n)
  refine hbase.congr_deriv ?_
  rw [hadamardWave]
  ring_nf

/-- The derivative along the second null coordinate. -/
theorem hasDerivAt_hadamardWave_snd (k n : ℕ) (ξ η z : ℝ) :
    HasDerivAt (fun y : ℝ => hadamardWave k n ξ y z)
      ((n : ℝ) / 2 * hadamardWave k n ξ η z) η := by
  have hEq : (fun y : ℝ => hadamardWave k n ξ y z)
      = fun y : ℝ => hadamardScale k n
        * Real.exp ((n : ℝ) / 2 * y + ((n : ℝ) / 2 * ξ + (n : ℝ) * z)) := by
    funext y
    rw [hadamardWave]
    ring_nf
  rw [hEq]
  have hbase := (hasDerivAt_expAffine ((n : ℝ) / 2) ((n : ℝ) / 2 * ξ + (n : ℝ) * z) η).const_mul
    (hadamardScale k n)
  refine hbase.congr_deriv ?_
  rw [hadamardWave]
  ring_nf

/-- Every transverse derivative of the family, in closed form. -/
theorem iteratedDeriv_hadamardWave_trans (k n j : ℕ) (ξ η : ℝ) :
    iteratedDeriv j (fun w : ℝ => hadamardWave k n ξ η w)
      = fun z => (n : ℝ) ^ j * hadamardWave k n ξ η z := by
  have hEq : (fun w : ℝ => hadamardWave k n ξ η w)
      = fun w : ℝ => hadamardScale k n
        * Real.exp ((n : ℝ) * w + ((n : ℝ) / 2 * ξ + (n : ℝ) / 2 * η)) := by
    funext w
    rw [hadamardWave]
    ring_nf
  rw [hEq, iteratedDeriv_scaledExpAffine]
  funext z
  rw [hadamardWave]
  ring_nf

/-- **The family solves the characteristic equation with vanishing potential.** -/
theorem hadamardWave_characteristic (k n : ℕ) (ξ η z : ℝ) :
    HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => hadamardWave k n x y z) ξ)
      (iteratedDeriv 2 (fun w : ℝ => hadamardWave k n ξ η w) z / 4) η := by
  have hderiv : (fun y : ℝ => deriv (fun x : ℝ => hadamardWave k n x y z) ξ)
      = fun y : ℝ => (n : ℝ) / 2 * hadamardWave k n ξ y z := by
    funext y
    exact (hasDerivAt_hadamardWave_fst k n ξ y z).deriv
  rw [hderiv, iteratedDeriv_hadamardWave_trans]
  have hbase := (hasDerivAt_hadamardWave_snd k n ξ η z).const_mul ((n : ℝ) / 2)
  refine hbase.congr_deriv ?_
  ring

/-! ## Small characteristic data, large interior values -/

/-- **The characteristic data is bounded by `n^{j-k}` in every transverse derivative**, on the two
characteristic faces of the unit box. -/
theorem abs_iteratedDeriv_hadamardWave_le (k n j : ℕ) (hn : 0 < n) {ξ η z : ℝ}
    (_hξ : 0 ≤ ξ) (_hη : 0 ≤ η) (hsum : ξ + η ≤ 1) (hz : z ≤ 0) :
    |iteratedDeriv j (fun w : ℝ => hadamardWave k n ξ η w) z| ≤ (n : ℝ) ^ j / (n : ℝ) ^ k := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  rw [iteratedDeriv_hadamardWave_trans]
  have hexp : Real.exp ((n : ℝ) / 2 * ξ + (n : ℝ) / 2 * η + (n : ℝ) * z)
      ≤ Real.exp ((n : ℝ) / 2) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : (n : ℝ) / 2 * ξ + (n : ℝ) / 2 * η = (n : ℝ) / 2 * (ξ + η) := by ring
    have h2 : (n : ℝ) / 2 * (ξ + η) ≤ (n : ℝ) / 2 := by
      have hhalf : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      nlinarith [hhalf, hsum]
    have h3 : (n : ℝ) * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnR.le hz
    linarith [h1 ▸ h2]
  have hw0 : 0 ≤ hadamardWave k n ξ η z := (hadamardWave_pos k n hn ξ η z).le
  have hval : |(n : ℝ) ^ j * hadamardWave k n ξ η z|
      = (n : ℝ) ^ j * hadamardWave k n ξ η z :=
    abs_of_nonneg (mul_nonneg (pow_nonneg hnR.le j) hw0)
  have hkey : Real.exp (-(n : ℝ) / 2)
      * Real.exp ((n : ℝ) / 2 * ξ + (n : ℝ) / 2 * η + (n : ℝ) * z) ≤ 1 := by
    rw [← Real.exp_add]
    refine Real.exp_le_one_iff.mpr ?_
    have := Real.exp_le_exp.mp hexp
    linarith
  have hfac : (0 : ℝ) ≤ (n : ℝ) ^ j / (n : ℝ) ^ k := by positivity
  calc |(n : ℝ) ^ j * hadamardWave k n ξ η z|
      = (n : ℝ) ^ j * hadamardWave k n ξ η z := hval
    _ = (n : ℝ) ^ j / (n : ℝ) ^ k
        * (Real.exp (-(n : ℝ) / 2)
          * Real.exp ((n : ℝ) / 2 * ξ + (n : ℝ) / 2 * η + (n : ℝ) * z)) := by
        rw [hadamardWave, hadamardScale]
        ring
    _ ≤ (n : ℝ) ^ j / (n : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left hkey hfac
    _ = (n : ℝ) ^ j / (n : ℝ) ^ k := mul_one _

/-- The value at the far corner of the box. -/
theorem hadamardWave_corner (k n : ℕ) :
    hadamardWave k n 1 1 0 = Real.exp ((n : ℝ) / 2) / (n : ℝ) ^ k := by
  have harg : -(n : ℝ) / 2 + ((n : ℝ) / 2 * 1 + (n : ℝ) / 2 * 1 + (n : ℝ) * 0) = (n : ℝ) / 2 := by
    ring
  rw [hadamardWave, hadamardScale, div_mul_eq_mul_div, ← Real.exp_add, harg]

/-- **The corner value grows without bound.** -/
theorem tendsto_hadamardWave_corner (k : ℕ) :
    Tendsto (fun n : ℕ => hadamardWave k n 1 1 0) atTop atTop := by
  have hbase : Tendsto (fun x : ℝ => Real.exp x / x ^ k) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop k
  have hhalf : Tendsto (fun n : ℕ => (n : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hcomp : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) / 2) / ((n : ℝ) / 2) ^ k) atTop atTop :=
    hbase.comp hhalf
  have hdiv : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) / 2) / ((n : ℝ) / 2) ^ k / (2 : ℝ) ^ k) atTop atTop :=
    hcomp.atTop_div_const (by positivity)
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [hadamardWave_corner]
  rw [div_div, ← mul_pow]
  congr 2
  ring

/-! ## The ill-posedness statement -/

/-- **The characteristic problem is ill posed in every finite order of transverse smoothness.**

For every order `m`, every tolerance `ε > 0` and every target `C`, there is an exact solution of the
characteristic equation with vanishing potential whose characteristic data on the two faces of the
unit box is bounded by `ε` together with all transverse derivatives of order at most `m`, and whose
value at the far corner exceeds `C`.

So no estimate bounding the solution by finitely many transverse derivatives of its characteristic
data can hold: analyticity in the transverse directions is necessary for this route, not merely
convenient. -/
theorem exists_characteristic_illPosed (m : ℕ) (ε C : ℝ) (hε : 0 < ε) :
    ∃ u : ℝ → ℝ → ℝ → ℝ,
      (∀ ξ η z : ℝ, HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => u x y z) ξ)
          (iteratedDeriv 2 (fun w : ℝ => u ξ η w) z / 4) η) ∧
        (∀ j ≤ m, ∀ η z : ℝ, 0 ≤ η → η ≤ 1 → z ≤ 0 →
          |iteratedDeriv j (fun w : ℝ => u 0 η w) z| ≤ ε) ∧
        (∀ j ≤ m, ∀ ξ z : ℝ, 0 ≤ ξ → ξ ≤ 1 → z ≤ 0 →
          |iteratedDeriv j (fun w : ℝ => u ξ 0 w) z| ≤ ε) ∧
        C ≤ u 1 1 0 := by
  classical
  set k : ℕ := m + 1 with hk
  -- the data bound holds for all large `n`
  have hdata : Tendsto (fun n : ℕ => ((n : ℝ) ^ m / (n : ℝ) ^ k)) atTop (nhds 0) := by
    have hEq : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ m / (n : ℝ) ^ k = 1 / (n : ℝ) := by
      intro n hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [hk, pow_succ]
      field_simp
    refine Tendsto.congr' ?_ (tendsto_one_div_atTop_nhds_zero_nat)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hEq n hn).symm
  have hsmall := (hdata.eventually (gt_mem_nhds hε))
  have hbig := (tendsto_hadamardWave_corner k).eventually_ge_atTop C
  obtain ⟨n, hn1, hnsmall, hnbig⟩ := ((eventually_ge_atTop 1).and (hsmall.and hbig)).exists
  have hnpos : 0 < n := hn1
  refine ⟨hadamardWave k n, fun ξ η z => hadamardWave_characteristic k n ξ η z, ?_, ?_, hnbig⟩
  · intro j hj η z hη0 hη1 hz
    refine le_trans (abs_iteratedDeriv_hadamardWave_le k n j hnpos le_rfl hη0 (by linarith) hz) ?_
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hmono : (n : ℝ) ^ j ≤ (n : ℝ) ^ m := pow_le_pow_right₀ hnR hj
    have hpos : (0 : ℝ) < (n : ℝ) ^ k := by
      have : (0 : ℝ) < (n : ℝ) := by linarith
      positivity
    exact le_trans (by gcongr) hnsmall.le
  · intro j hj ξ z hξ0 hξ1 hz
    refine le_trans (abs_iteratedDeriv_hadamardWave_le k n j hnpos hξ0 le_rfl (by linarith) hz) ?_
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hmono : (n : ℝ) ^ j ≤ (n : ℝ) ^ m := pow_le_pow_right₀ hnR hj
    have hpos : (0 : ℝ) < (n : ℝ) ^ k := by
      have : (0 : ℝ) < (n : ℝ) := by linarith
      positivity
    exact le_trans (by gcongr) hnsmall.le

end GaloisForLFunctions.HTGeometry
