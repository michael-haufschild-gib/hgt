import GaloisForLFunctions.HTGeometry.PolyaCompositionMaximum
import GaloisForLFunctions.HTGeometry.IteratedExponentialGrowthHeight
import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# Polynomial inner factors forced by positive lower order

Pólya's composition maximum inequality transfers a finite-order envelope of F ∘ g to a global
polynomial norm bound on g whenever F has positive lower order. Polynomial-growth Liouville then
identifies g with a polynomial. No growth assumption is imposed on g itself.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- Finite order of a composite with a positive-lower-order outer function forces a polynomial
inner function. No lower growth assumption is imposed on the inner function. -/
theorem exists_polynomial_inner_of_positiveLowerOrder_comp
    {F g : ℂ → ℂ} (hF : Differentiable ℂ F) (hg : Differentiable ℂ g)
    (hpos : PositiveLowerOrder F) (hcomp : FiniteOrderEnvelope (fun z => F (g z))) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, g z = P.eval z := by
  obtain ⟨δ, hδ, hlow⟩ := hpos
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hlow
  obtain ⟨C, d, hC, hbound⟩ := hcomp
  obtain ⟨c, hc, hpolya⟩ := exists_polya_constant
  obtain ⟨N, hN⟩ := exists_nat_ge ((d : ℝ) / δ)
  have hNδ : (d : ℝ) ≤ (N : ℝ) * δ := (div_le_iff₀ hδ).1 hN
  let A : ℝ := C * 3 ^ d + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let K : ℝ := max 1 (max R₀ (A ^ (1 / δ)))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hKR : R₀ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKA : A ^ (1 / δ) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hKδ : A ≤ K ^ δ := by
    have heq : (A ^ (1 / δ)) ^ δ = A := by
      rw [← Real.rpow_mul hA.le]
      have hcancel : (1 / δ) * δ = 1 := by field_simp
      rw [hcancel, Real.rpow_one]
    rw [← heq]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hKA hδ.le
  let b : ℝ := ‖g 0‖
  have hb : 0 ≤ b := norm_nonneg _
  let M : ℝ := (K + (c + 1) * b) / c
  apply exists_polynomial_of_polynomial_growth hg (M := M) (d := N)
  intro z
  by_contra hz
  have hzbig : M * (1 + ‖z‖) ^ N < ‖g z‖ := not_le.1 hz
  let v : ℝ := 1 + ‖z‖
  have hv1 : 1 ≤ v := by dsimp [v]; linarith [norm_nonneg z]
  have hv : 0 < v := lt_of_lt_of_le zero_lt_one hv1
  have hvN : 1 ≤ v ^ N := one_le_pow₀ hv1
  let R : ℝ := K * v ^ N
  have hR : 0 < R := mul_pos hK0 (pow_pos hv _)
  have hRK : K ≤ R := by
    change K ≤ K * v ^ N
    nlinarith
  let H : ℝ := ‖g z‖ - b
  have hscale : R + b < c * H := by
    have hterm : (c + 1) * b ≤ (c + 1) * b * v ^ N := by
      nlinarith [mul_nonneg (show 0 ≤ c + 1 by linarith) hb]
    have hMc : c * M = K + (c + 1) * b := by dsimp [M]; field_simp
    have hmul := mul_lt_mul_of_pos_left hzbig hc
    change c * (M * v ^ N) < c * ‖g z‖ at hmul
    rw [← mul_assoc, hMc] at hmul
    dsimp [R, H]
    nlinarith [hmul]
  have hH : 0 < H := by nlinarith [hscale]
  have hinner : Differentiable ℂ (fun w => g w - g 0) := hg.sub_const _
  have houter : Differentiable ℂ (fun w => F (w + g 0)) :=
    hF.comp (differentiable_id.add_const _)
  have hreach : ∃ w : ℂ, ‖w‖ ≤ (2 * v) / 2 ∧ H ≤ ‖g w - g 0‖ := by
    refine ⟨z, ?_, norm_sub_norm_le _ _⟩
    dsimp [v]
    linarith [norm_nonneg z]
  obtain ⟨w, hw, hmax⟩ := hpolya (fun u => F (u + g 0)) (fun u => g u - g 0)
    houter hinner (by simp) (2 * v) H (by positivity) hH hreach
  obtain ⟨u, hu, hFu⟩ := hR₀ R (hKR.trans hRK)
  have huarg : ‖u - g 0‖ ≤ c * H := by
    calc
      ‖u - g 0‖ ≤ ‖u‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ R + b := by simpa [b, add_comm] using add_le_add_right hu ‖g 0‖
      _ ≤ c * H := hscale.le
  have hlower : Real.exp (R ^ δ) ≤ ‖F (g w)‖ := by
    have hm := hmax (u - g 0) huarg
    simp only [sub_add_cancel] at hm
    simpa only [iterExp_succ, iterExp_zero] using hFu.trans hm
  have hwbound : 1 + ‖w‖ ≤ 3 * v := by linarith [hw, hv1]
  have hupper : ‖F (g w)‖ ≤ Real.exp (C * 3 ^ d * v ^ d) := by
    apply (hbound w).trans
    apply Real.exp_le_exp.2
    calc
      C * (1 + ‖w‖) ^ d ≤ C * (3 * v) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hwbound d) hC
      _ = C * 3 ^ d * v ^ d := by rw [mul_pow]; ring
  have hvpow : v ^ d ≤ (v ^ N) ^ δ := by
    calc
      v ^ d = v ^ (d : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ v ^ ((N : ℝ) * δ) := Real.rpow_le_rpow_of_exponent_le hv1 hNδ
      _ = (v ^ N) ^ δ := by rw [Real.rpow_mul hv.le, Real.rpow_natCast]
  have hRpow : A * v ^ d ≤ R ^ δ := by
    dsimp [R]
    rw [Real.mul_rpow hK0.le (pow_nonneg hv.le N)]
    exact mul_le_mul hKδ hvpow (pow_nonneg hv.le d) (Real.rpow_nonneg hK0.le _)
  have hstrict : C * 3 ^ d * v ^ d < R ^ δ := by
    have hpowpos := pow_pos hv d
    dsimp [A] at hRpow
    nlinarith
  exact (not_lt_of_ge (Real.exp_le_exp.1 (hlower.trans hupper))) hstrict

end GaloisForLFunctions.HTGeometry
