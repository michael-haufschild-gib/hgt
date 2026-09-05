import GaloisForLFunctions.RHTower.MassBesselDyadicAperture
import GaloisForLFunctions.RHTower.DyadicVonMangoldtLogWeighted
import GaloisForLFunctions.HTGeometry.MassCarrierPartialSum

/-!
# The dyadic radiation remainder at every finite order

Subtracting the first `m` deep-time radiation terms from a dyadic prime aperture leaves the aperture
of the order-`m` carrier defect.  Because the defect is controlled uniformly over the shell, the
remainder is the prime mass of the `m`-th Poincaré coefficient times the corresponding power of the
spectral parameter, plus a smaller error.
-/

open Filter ArithmeticFunction HTGeometry
open scoped Topology BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry in
/-- The dyadic prime mass weighted by a Poincaré coefficient polynomial. -/
def dyadicPoincareMass (a : ℝ) (n' M j : ℕ) (X : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    (((vonMangoldt k : ℝ) / Real.sqrt k : ℝ) : ℂ)
      * (poincareCoeffPoly a n' M j).eval (((Real.log k : ℝ) : ℂ) ^ 2)

/-- The first `m` deep-time radiation terms of a dyadic prime aperture. -/
def dyadicPoincareSum (a σ X : ℝ) (n' M m : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range m, dyadicPoincareMass a n' M j X * ((apertureSpectralPoint σ u)⁻¹) ^ j

/-- The order-`m` radiation remainder of a dyadic prime aperture. -/
def massBesselDyadicRadiationRemainder (a σ X : ℝ) (n' M m : ℕ) (u : ℝ) : ℂ :=
  massBesselDyadicAperture a σ X u
    - massBesselLeading a (apertureSpectralPoint σ u) * dyadicPoincareSum a σ X n' M m u

/-- Removing one more radiation term. -/
theorem massBesselDyadicRadiationRemainder_succ (a σ X : ℝ) (n' M m : ℕ) (u : ℝ) :
    massBesselDyadicRadiationRemainder a σ X n' M m u
      = massBesselLeading a (apertureSpectralPoint σ u)
          * (dyadicPoincareMass a n' M m X * ((apertureSpectralPoint σ u)⁻¹) ^ m)
        + massBesselDyadicRadiationRemainder a σ X n' M (m + 1) u := by
  rw [massBesselDyadicRadiationRemainder, massBesselDyadicRadiationRemainder, dyadicPoincareSum,
    dyadicPoincareSum, Finset.sum_range_succ]
  ring

open GaloisForLFunctions.HTGeometry in
theorem eval_truncBelow_carrierProductPoly (a x : ℝ) (n' m : ℕ) (w : ℂ) :
    (truncBelow m (carrierProductPoly a x n' m)).eval w
      = ∑ j ∈ Finset.range m,
          (poincareCoeffPoly a n' m j).eval (((x : ℝ) : ℂ) ^ 2) * w ^ j := by
  rw [eval_truncBelow]
  exact Finset.sum_congr rfl fun j _ => by rw [coeff_carrierProductPoly]

open GaloisForLFunctions.HTGeometry in
/-- **The radiation remainder is the aperture of the order-`m` carrier defect.** -/
theorem massBesselDyadicRadiationRemainder_eq (a σ X : ℝ) (n' m : ℕ) (u : ℝ) :
    massBesselDyadicRadiationRemainder a σ X n' m m u
      = ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          (((vonMangoldt k : ℝ) / Real.sqrt k : ℝ) : ℂ)
            * (massBesselCarrier a (apertureSpectralPoint σ u) (Real.log k)
              - massBesselLeading a (apertureSpectralPoint σ u)
                * (truncBelow m (carrierProductPoly a (Real.log k) n' m)).eval
                    (apertureSpectralPoint σ u)⁻¹) := by
  classical
  set t : ℂ := apertureSpectralPoint σ u with htdef
  set L : ℂ := massBesselLeading a t with hLdef
  have hswap : L * ∑ j ∈ Finset.range m, dyadicPoincareMass a n' m j X * (t⁻¹) ^ j
      = ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          (((vonMangoldt k : ℝ) / Real.sqrt k : ℝ) : ℂ)
            * (L * (truncBelow m (carrierProductPoly a (Real.log k) n' m)).eval t⁻¹) := by
    rw [Finset.mul_sum]
    have hexpand : ∀ j ∈ Finset.range m,
        L * (dyadicPoincareMass a n' m j X * (t⁻¹) ^ j)
        = ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
            (((vonMangoldt k : ℝ) / Real.sqrt k : ℝ) : ℂ)
              * (L * ((poincareCoeffPoly a n' m j).eval (((Real.log k : ℝ) : ℂ) ^ 2)
                * (t⁻¹) ^ j)) := by
      intro j _
      rw [dyadicPoincareMass, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_truncBelow_carrierProductPoly, Finset.mul_sum, Finset.mul_sum]
  rw [massBesselDyadicRadiationRemainder, dyadicPoincareSum, ← htdef, ← hLdef, hswap,
    massBesselDyadicAperture, ← htdef, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

open GaloisForLFunctions.HTGeometry in
/-- The uniform shell bound for the order-`m` carrier defect. -/
def radiationShellBound (a σ c : ℝ) (n' m : ℕ) (u M : ℝ) : ℝ :=
  ‖massBesselLeading a (apertureSpectralPoint σ u)‖
      * (carrierTruncConst a c (n' + 1) m * max 1 (M ^ 2) ^ m * (u⁻¹) ^ m)
    + 8 * a * (((a * u) ^ ((1 : ℝ) / 2))⁻¹ * (rayRemConst (n' + 1) / (a * u) ^ (n' + 1)))

open GaloisForLFunctions.HTGeometry in
/-- **The order-`m` radiation remainder is bounded by the prime mass times a shell-uniform
constant.** -/
theorem norm_massBesselDyadicRadiationRemainder_le {a σ X u M c : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (hu : 1 ≤ u) (hσu : σ ≤ u)
    (hlog : ∀ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, Real.log k ^ 2 ≤ M ^ 2)
    (h1 : 2 * M ^ 2 ≤ u) (h2 : Real.sqrt 2 * M ^ 2 < σ * u)
    (hc : M ^ 2 / u ≤ c) (hdefu : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (M ^ 2 / u) ≤ 1 / 2)
    (n' m : ℕ) :
    ‖massBesselDyadicRadiationRemainder a σ X (n' + 1) m m u‖
      ≤ dyadicSqrtVonMangoldtMass X * radiationShellBound a σ c n' m u M := by
  classical
  set t : ℂ := apertureSpectralPoint σ u with htdef
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have htre : 0 < t.re := by rw [htdef, spectralPoint_re]; exact hσ
  have htim : 0 < t.im := by rw [htdef, spectralPoint_im]; exact hu0
  have hnormt : u ≤ ‖t‖ := by rw [htdef]; exact le_norm_spectralPoint σ u
  have hnormt2 : ‖t‖ ≤ 2 * u := by rw [htdef]; exact norm_spectralPoint_le hσ hσu
  have htne : t ≠ 0 := by
    intro h
    rw [h] at htre
    simp at htre
  have hinv : ‖t⁻¹‖ ≤ u⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hu0 hnormt
  have hr1 : u⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hu
  have hr0 : (0 : ℝ) ≤ u⁻¹ := le_of_lt (by positivity)
  have hterm : ∀ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      ‖massBesselCarrier a t (Real.log k)
        - massBesselLeading a t
          * (truncBelow m (carrierProductPoly a (Real.log k) (n' + 1) m)).eval t⁻¹‖
      ≤ radiationShellBound a σ c n' m u M := by
    intro k hk
    set x : ℝ := Real.log k with hxdef
    have hx := hlog k hk
    have hxr : x ^ 2 * (u⁻¹) ^ 2 ≤ 1 / 2 := by
      have hus : (1 : ℝ) ≤ u ^ 2 := by nlinarith
      have : x ^ 2 ≤ M ^ 2 := hx
      have hinv2 : (u⁻¹) ^ 2 = (u ^ 2)⁻¹ := by rw [inv_pow]
      rw [hinv2]
      rw [mul_inv_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg x]
    have hxc : x ^ 2 * u⁻¹ ≤ c := by
      have : x ^ 2 * u⁻¹ ≤ M ^ 2 * u⁻¹ := by
        exact mul_le_mul_of_nonneg_right hx hr0
      calc x ^ 2 * u⁻¹ ≤ M ^ 2 * u⁻¹ := this
        _ = M ^ 2 / u := by rw [div_eq_mul_inv]
        _ ≤ c := hc
    have hdef : a * shellDefectRate x * u⁻¹ ≤ 1 / 2 := by
      have hcb : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 := cbinomAbsCoeff_nonneg _ _
      have hrate : shellDefectRate x = cbinomAbsCoeff ((1 : ℝ) / 2) 1 * x ^ 2 := by
        rw [shellDefectRate, sq_abs]
      rw [hrate]
      have hstep : a * (cbinomAbsCoeff ((1 : ℝ) / 2) 1 * x ^ 2) * u⁻¹
          ≤ a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (M ^ 2 / u) := by
        rw [show M ^ 2 / u = M ^ 2 * u⁻¹ from div_eq_mul_inv _ _]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha.le hcb) hr0) (sub_nonneg.mpr hx)]
      linarith
    have hsmall : Real.sqrt 2 * x ^ 2 < t.re * ‖t‖ := by
      have hre : t.re = σ := by rw [htdef, spectralPoint_re]
      rw [hre]
      have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      nlinarith [hx, hnormt, hσ.le, hs2.le]
    have hmain := norm_massBesselCarrier_sub_partialSum_le (a := a) (x := x) (r := u⁻¹) (c := c)
      ha hr0 hr1 hxr hxc hdef m n' htre htim hsmall hinv
    refine le_trans hmain ?_
    rw [radiationShellBound]
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hmx : max 1 (x ^ 2) ^ m ≤ max 1 (M ^ 2) ^ m := by
        refine pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) ?_ m
        exact max_le_max (le_refl 1) hx
      have hwm : ‖t⁻¹‖ ^ m ≤ (u⁻¹) ^ m := pow_le_pow_left₀ (norm_nonneg _) hinv m
      have hC : (0 : ℝ) ≤ carrierTruncConst a c (n' + 1) m := by
        have h1' := one_le_carrierShellConst (a := a) (le_trans (by positivity) hc) (n' + 1) m
        have h2' : (0 : ℝ) ≤ (carrierDegBound a (n' + 1) m : ℝ)
            * (poincareMassSum a (n' + 1) m * max 1 c ^ carrierDegBound a (n' + 1) m) :=
          mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (poincareMassSum_nonneg _ _ _)
              (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
        have h3' : (0 : ℝ) ≤ 1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m := by
          have := pow_nonneg (mul_nonneg ha.le (cbinomAbsCoeff_nonneg ((1 : ℝ) / 2) 1)) m
          linarith
        rw [carrierTruncConst]
        nlinarith
      have hmax0 : (0 : ℝ) ≤ max 1 (x ^ 2) ^ m :=
        pow_nonneg (le_trans zero_le_one (le_max_left _ _)) m
      have hmax0' : (0 : ℝ) ≤ max 1 (M ^ 2) ^ m :=
        pow_nonneg (le_trans zero_le_one (le_max_left _ _)) m
      have hwm0 : (0 : ℝ) ≤ ‖t⁻¹‖ ^ m := pow_nonneg (norm_nonneg _) m
      calc carrierTruncConst a c (n' + 1) m * max 1 (x ^ 2) ^ m * ‖t⁻¹‖ ^ m
          ≤ carrierTruncConst a c (n' + 1) m * max 1 (M ^ 2) ^ m * ‖t⁻¹‖ ^ m := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmx hC) hwm0
        _ ≤ carrierTruncConst a c (n' + 1) m * max 1 (M ^ 2) ^ m * (u⁻¹) ^ m := by
            exact mul_le_mul_of_nonneg_left hwm (by positivity)
    · have hzrep : 0 < (massBesselRoot t x).re := massBesselRoot_re_pos htre htim x
      set z : ℂ := massBesselRoot t x with hzdef
      have hzsq : u ^ 2 / 2 ≤ ‖z‖ ^ 2 := by
        have h := norm_massBesselRoot_sq_ge htre htim x
        rw [← hzdef] at h
        have htsq : u ^ 2 ≤ ‖t‖ ^ 2 := by nlinarith [hnormt, hu0]
        have hxu : x ^ 2 ≤ u ^ 2 / 2 := by
          nlinarith [hx, h1, mul_nonneg hu0.le (by linarith : (0 : ℝ) ≤ u - 1)]
        linarith
      have hznorm : u / 2 ≤ ‖z‖ := by
        have hsq : (u / 2) ^ 2 ≤ ‖z‖ ^ 2 := by
          have hid : (u / 2) ^ 2 = u ^ 2 / 4 := by ring
          rw [hid]
          linarith [hzsq, sq_nonneg u]
        have hle := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg z)] at hle
      have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by positivity) hznorm
      have hau : (0 : ℝ) < a * u := by positivity
      have hbig : a * u ≤ 2 * (a * ‖z‖) := by
        have h := mul_le_mul_of_nonneg_left hznorm ha.le
        calc a * u = 2 * (a * (u / 2)) := by ring
          _ ≤ 2 * (a * ‖z‖) := by linarith
      have hexp1 : Real.exp (-(a * z.re)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ a * z.re := mul_nonneg ha.le hzrep.le
        linarith
      have hratio : 2 * a * ‖t‖ / ‖z‖ ≤ 8 * a := by
        rw [div_le_iff₀ hzpos]
        have h1' : 2 * a * ‖t‖ ≤ 2 * a * (2 * u) :=
          mul_le_mul_of_nonneg_left hnormt2 (by linarith)
        have h2' : 8 * a * (u / 2) ≤ 8 * a * ‖z‖ :=
          mul_le_mul_of_nonneg_left hznorm (by linarith)
        linarith
      have hp1 : (0 : ℝ) < ((a * u) ^ ((1 : ℝ) / 2)) := Real.rpow_pos_of_pos hau _
      have hpow1 : ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹ ≤ ((a * u) ^ ((1 : ℝ) / 2))⁻¹ :=
        inv_anti₀ hp1 (Real.rpow_le_rpow hau.le hbig (by norm_num))
      have hpow2 : rayRemConst (n' + 1) / (2 * (a * ‖z‖)) ^ (n' + 1)
          ≤ rayRemConst (n' + 1) / (a * u) ^ (n' + 1) :=
        div_le_div_of_nonneg_left (rayRemConst_nonneg _) (by positivity)
          (pow_le_pow_left₀ hau.le hbig (n' + 1))
      have hp1inv : (0 : ℝ) ≤ ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹ := by positivity
      have hp2nn : (0 : ℝ) ≤ rayRemConst (n' + 1) / (2 * (a * ‖z‖)) ^ (n' + 1) :=
        div_nonneg (rayRemConst_nonneg _) (by positivity)
      have hp1'nn : (0 : ℝ) ≤ ((a * u) ^ ((1 : ℝ) / 2))⁻¹ := by positivity
      have hstepB : Real.exp (-(a * z.re)) * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹
            * (rayRemConst (n' + 1) / (2 * (a * ‖z‖)) ^ (n' + 1))
          ≤ ((a * u) ^ ((1 : ℝ) / 2))⁻¹ * (rayRemConst (n' + 1) / (a * u) ^ (n' + 1)) := by
        have hfirst : Real.exp (-(a * z.re)) * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹
            ≤ ((a * u) ^ ((1 : ℝ) / 2))⁻¹ := by
          calc Real.exp (-(a * z.re)) * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹
              ≤ 1 * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹ :=
                mul_le_mul_of_nonneg_right hexp1 hp1inv
            _ = ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹ := one_mul _
            _ ≤ ((a * u) ^ ((1 : ℝ) / 2))⁻¹ := hpow1
        exact mul_le_mul hfirst hpow2 hp2nn hp1'nn
      have hBnn : (0 : ℝ) ≤ Real.exp (-(a * z.re)) * ((2 * (a * ‖z‖)) ^ ((1 : ℝ) / 2))⁻¹
          * (rayRemConst (n' + 1) / (2 * (a * ‖z‖)) ^ (n' + 1)) :=
        mul_nonneg (mul_nonneg (Real.exp_pos _).le hp1inv) hp2nn
      exact mul_le_mul hratio hstepB hBnn (by positivity)
  rw [massBesselDyadicRadiationRemainder_eq]
  refine le_trans (norm_sum_le _ _) ?_
  rw [dyadicSqrtVonMangoldtMass, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hterm k hk) (by positivity)

end

end RHTower
