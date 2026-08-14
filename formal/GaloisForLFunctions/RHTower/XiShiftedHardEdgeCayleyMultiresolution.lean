import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Dyadic Cayley multiresolution at the Route-U hard edge

Dyadic hard-edge refinement splits every finite Chebyshev packet into an even transported packet
and a fresh odd packet.  Normalized arcsine energy makes those sectors exactly orthogonal, giving
an unconditional Pythagorean refinement and its sharp one-quarter lower bound.

The same refinement does not compare Route-U divisor packets at fixed spectral nodes.  Applying
`T₂` to a Cayley node at mass `2a` produces a nonlinear transported node, formalized below as an
explicit rational function.  Thus flat arcsine Pythagoras cannot be promoted to a completed
prime--Gamma source inequality without a separate arithmetic node-transport estimate.

No zero-location hypothesis or numerical computation occurs in this module.
-/

open scoped BigOperators
open Polynomial

noncomputable section

namespace RHTower.RouteUDyadicCayley

/-- Abstract Cayley hard-edge node. -/
def cayleyNode (a z : ℂ) : ℂ :=
  (a ^ 2 - z ^ 2) / (a ^ 2 + z ^ 2)

/-- Exact node obtained by applying `T₂` after doubling hard-edge mass. -/
def dyadicTransportedNode (a z : ℂ) : ℂ :=
  (16 * a ^ 4 - 24 * a ^ 2 * z ^ 2 + z ^ 4) /
    (4 * a ^ 2 + z ^ 2) ^ 2

/-- Dyadic Chebyshev parity lives at a nonlinear transported spectral node, not at the original
mass-`a` Cayley node. -/
theorem cayleyNode_doubling_eq_dyadicTransportedNode
    {a z : ℂ} (hplus : 4 * a ^ 2 + z ^ 2 ≠ 0) :
    (Polynomial.Chebyshev.T ℂ 2).eval (cayleyNode (2 * a) z) =
      dyadicTransportedNode a z := by
  have hx : cayleyNode (2 * a) z =
      (4 * a ^ 2 - z ^ 2) / (4 * a ^ 2 + z ^ 2) := by
    rw [cayleyNode]
    congr 1 <;> ring
  rw [Polynomial.Chebyshev.T_two, hx]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    dyadicTransportedNode]
  field_simp [hplus]
  ring

/-- Exact drift from the original mass-`a` node.  Its numerator begins at spectral order four;
the quadratic drift cancels identically under tangent doubling. -/
theorem dyadicTransportedNode_sub_cayleyNode
    {a z : ℂ} (hplus : 4 * a ^ 2 + z ^ 2 ≠ 0)
    (hcoarse : a ^ 2 + z ^ 2 ≠ 0) :
    dyadicTransportedNode a z - cayleyNode a z =
      2 * z ^ 4 * (z ^ 2 - 8 * a ^ 2) /
        ((4 * a ^ 2 + z ^ 2) ^ 2 * (a ^ 2 + z ^ 2)) := by
  rw [dyadicTransportedNode, cayleyNode]
  have hden : (4 * a ^ 2 + z ^ 2) ^ 2 * (a ^ 2 + z ^ 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hplus) hcoarse
  have hplus' : a ^ 2 * 4 + z ^ 2 ≠ 0 := by
    rw [show a ^ 2 * 4 + z ^ 2 = 4 * a ^ 2 + z ^ 2 by ring]
    exact hplus
  apply (eq_div_iff hden).2
  field_simp [hplus, hplus', hcoarse]
  ring

/-- Finite even Chebyshev sector. -/
def evenPacket (N : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range N,
    Polynomial.C (c i) * Polynomial.Chebyshev.T ℝ ((2 * i : ℕ) : ℤ)

/-- Finite odd Chebyshev sector newly admitted by dyadic mesh refinement. -/
def oddPacket (N : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range N,
    Polynomial.C (c i) * Polynomial.Chebyshev.T ℝ ((2 * i + 1 : ℕ) : ℤ)

/-- Probability-normalized arcsine functional.  Mathlib's `measureT` has total mass `π`. -/
def arcsineL (P : Polynomial ℝ) : ℝ :=
  (∫ x, P.eval x ∂Polynomial.Chebyshev.measureT) / Real.pi

theorem arcsineL_add (P Q : Polynomial ℝ) :
    arcsineL (P + Q) = arcsineL P + arcsineL Q := by
  have heval : (fun x : ℝ => (P + Q).eval x) =
      fun x : ℝ => P.eval x + Q.eval x := by
    funext x
    simp
  rw [arcsineL, arcsineL, arcsineL, heval,
    MeasureTheory.integral_add
      (Polynomial.Chebyshev.integrable_measureT (by fun_prop))
      (Polynomial.Chebyshev.integrable_measureT (by fun_prop))]
  ring

theorem arcsineL_smul (a : ℝ) (P : Polynomial ℝ) :
    arcsineL (a • P) = a * arcsineL P := by
  rw [arcsineL, arcsineL]
  simp only [Polynomial.eval_smul, smul_eq_mul,
    MeasureTheory.integral_const_mul]
  ring

theorem arcsineL_C_mul (a : ℝ) (P : Polynomial ℝ) :
    arcsineL (Polynomial.C a * P) = a * arcsineL P := by
  simpa [Polynomial.smul_eq_C_mul] using arcsineL_smul a P

/-- Every finite detail sector has nonnegative arcsine energy. -/
theorem arcsineL_sq_nonneg (P : Polynomial ℝ) :
    0 ≤ arcsineL (P ^ 2) := by
  rw [arcsineL]
  apply div_nonneg
  · apply MeasureTheory.integral_nonneg
    intro x
    simp only [Polynomial.eval_pow]
    positivity
  · exact Real.pi_pos.le

theorem arcsineL_T_mul_T_of_ne {n m : ℕ} (h : n ≠ m) :
    arcsineL (Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.T ℝ m) = 0 := by
  rw [arcsineL]
  simp only [Polynomial.eval_mul]
  rw [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne h]
  simp

theorem arcsineL_finset_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) :
    arcsineL (∑ i ∈ s, P i) = ∑ i ∈ s, arcsineL (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [arcsineL]
  | @insert a s ha ih => simp [ha, arcsineL_add, ih]

/-- Even and odd finite Chebyshev sectors are exactly arcsine-orthogonal. -/
theorem arcsineL_evenPacket_mul_oddPacket
    (M N : ℕ) (c d : ℕ → ℝ) :
    arcsineL (evenPacket M c * oddPacket N d) = 0 := by
  rw [evenPacket, oddPacket, Finset.sum_mul, arcsineL_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mul_sum, arcsineL_finset_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : 2 * i ≠ 2 * j + 1 := by omega
  rw [show
      (Polynomial.C (c i) * Polynomial.Chebyshev.T ℝ ((2 * i : ℕ) : ℤ)) *
          (Polynomial.C (d j) * Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) =
        Polynomial.C (c i * d j) *
          (Polynomial.Chebyshev.T ℝ ((2 * i : ℕ) : ℤ) *
            Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)) by
      rw [Polynomial.C_mul]
      ring]
  rw [arcsineL_C_mul, arcsineL_T_mul_T_of_ne hne, mul_zero]

/-- Exact flat even/odd Pythagorean law. -/
theorem flatPythagorean
    (M N : ℕ) (c d : ℕ → ℝ) :
    arcsineL ((evenPacket M c + oddPacket N d) ^ 2) =
      arcsineL ((evenPacket M c) ^ 2) +
        arcsineL ((oddPacket N d) ^ 2) := by
  have hcross := arcsineL_evenPacket_mul_oddPacket M N c d
  rw [show (evenPacket M c + oddPacket N d) ^ 2 =
      (evenPacket M c) ^ 2 +
        (evenPacket M c * oddPacket N d +
          evenPacket M c * oddPacket N d) +
        (oddPacket N d) ^ 2 by ring]
  rw [arcsineL_add, arcsineL_add, arcsineL_add, hcross]
  ring

/-- Exact dyadic refinement: one half of the transported coarse packet plus fresh odd detail. -/
theorem flatHalfPythagorean
    (M N : ℕ) (c d : ℕ → ℝ) :
    arcsineL (((1 / 2 : ℝ) • evenPacket M c + oddPacket N d) ^ 2) =
      (1 / 4 : ℝ) * arcsineL ((evenPacket M c) ^ 2) +
        arcsineL ((oddPacket N d) ^ 2) := by
  have hcross := arcsineL_evenPacket_mul_oddPacket M N c d
  have hhalfMul :
      Polynomial.C (1 / 2 : ℝ) * (2 : Polynomial ℝ) = 1 := by
    change Polynomial.C (1 / 2 : ℝ) * Polynomial.C 2 = Polynomial.C 1
    rw [← Polynomial.C_mul]
    norm_num
  have hhalfSq :
      Polynomial.C (1 / 2 : ℝ) ^ 2 = Polynomial.C (1 / 4 : ℝ) := by
    rw [← Polynomial.C_pow]
    norm_num
  have hcrossPoly :
      Polynomial.C (1 / 2 : ℝ) * evenPacket M c * oddPacket N d * 2 =
        evenPacket M c * oddPacket N d := by
    calc
      Polynomial.C (1 / 2 : ℝ) * evenPacket M c * oddPacket N d * 2 =
          (Polynomial.C (1 / 2 : ℝ) * 2) *
            (evenPacket M c * oddPacket N d) := by ring
      _ = evenPacket M c * oddPacket N d := by rw [hhalfMul, one_mul]
  have hcrossPoly' :
      2 * (Polynomial.C (1 / 2 : ℝ) * evenPacket M c) * oddPacket N d =
        evenPacket M c * oddPacket N d := by
    calc
      2 * (Polynomial.C (1 / 2 : ℝ) * evenPacket M c) * oddPacket N d =
          Polynomial.C (1 / 2 : ℝ) * evenPacket M c * oddPacket N d * 2 := by
            ring
      _ = evenPacket M c * oddPacket N d := hcrossPoly
  rw [show (((1 / 2 : ℝ) • evenPacket M c + oddPacket N d) ^ 2) =
      (1 / 4 : ℝ) • (evenPacket M c) ^ 2 +
        Polynomial.C (1 : ℝ) * (evenPacket M c * oddPacket N d) +
        (oddPacket N d) ^ 2 by
      simp only [smul_eq_C_mul]
      rw [add_sq, mul_pow, hhalfSq, hcrossPoly']
      simp]
  rw [arcsineL_add, arcsineL_add, arcsineL_smul, arcsineL_C_mul, hcross]
  ring

/-- Sharp flat half-submartingale inequality.  The gap is exactly the fresh odd detail energy. -/
theorem flatHalfSubmartingale
    (M N : ℕ) (c d : ℕ → ℝ) :
    (1 / 4 : ℝ) * arcsineL ((evenPacket M c) ^ 2) ≤
      arcsineL (((1 / 2 : ℝ) • evenPacket M c + oddPacket N d) ^ 2) := by
  rw [flatHalfPythagorean]
  exact le_add_of_nonneg_right (arcsineL_sq_nonneg (oddPacket N d))

end RHTower.RouteUDyadicCayley
