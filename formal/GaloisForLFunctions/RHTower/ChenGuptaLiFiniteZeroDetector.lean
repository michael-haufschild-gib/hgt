/-
# Chen--Gupta--Li finite zero-detector product

Chen--Gupta--Li, Section 12, starts its zero-detection argument by multiplying
the truncated Möbius inverse

`M_X(s, χ) = Σ_{d ≤ X} μ(d) χ(d) d^{-s}`

by a Dirichlet `L`-series.  This module proves the exact finite algebraic
counterpart: multiply two literal finite truncations and regroup the product
by its natural-number index.  It does not assert any continuation, contour
formula, zero alternative, or density estimate.
-/

import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenZeroDetection

open ArithmeticFunction

noncomputable section

namespace RHTower

/-- Finite Möbius inverse used in the zero detector, with an inclusive finite
cutoff encoded by `X + 1`. -/
def zeroDetectionMobiusPolynomial (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (X + 1), (moebius d : ℂ) * χ d * (d : ℂ) ^ (-s)

/-- A finite Dirichlet-series truncation at the same character and complex
argument as the Möbius inverse. -/
def zeroDetectionLTruncation (Y q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (Y + 1), χ m * (m : ℂ) ^ (-s)

/-- The literal contribution at index `n` in the product of the two finite
truncations.  Keeping the pair phase inside the coefficient avoids importing
any analytic or infinite-series fact into the regrouping step. -/
def zeroDetectionFiniteProductCoefficient (X Y q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ dm ∈ Finset.Icc 1 (X + 1) ×ˢ Finset.Icc 1 (Y + 1) with dm.1 * dm.2 = n,
    (moebius dm.1 : ℂ) * χ (dm.1 * dm.2) *
      ((dm.1 : ℂ) ^ (-s) * (dm.2 : ℂ) ^ (-s))

/-- The unphased finite Möbius convolution coefficient.  Once the index is
fixed, the character and Dirichlet phase factor out of this literal finite sum. -/
def zeroDetectionTruncatedConvolutionCoefficient (X Y n : ℕ) : ℂ :=
  ∑ dm ∈ Finset.Icc 1 (X + 1) ×ˢ Finset.Icc 1 (Y + 1) with dm.1 * dm.2 = n,
    (moebius dm.1 : ℂ)

/-- Complex powers at positive natural bases respect multiplication.  This is
the exact phase identity needed to turn a double Dirichlet-polynomial term
into an index-`n` term. -/
theorem natural_cpow_mul_neg (d m : ℕ) (s : ℂ) :
    (d : ℂ) ^ (-s) * (m : ℂ) ^ (-s) = (d * m : ℂ) ^ (-s) := by
  rw [show (d * m : ℂ) = (d : ℂ) * (m : ℂ) by norm_cast]
  exact (Complex.mul_cpow_ofReal_nonneg d.cast_nonneg m.cast_nonneg (-s)).symm

/-- Exact multiplication of the two finite detector factors. -/
theorem zeroDetectionMobiusPolynomial_mul_truncation (X Y q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    zeroDetectionMobiusPolynomial X q χ s * zeroDetectionLTruncation Y q χ s =
      ∑ d ∈ Finset.Icc 1 (X + 1), ∑ m ∈ Finset.Icc 1 (Y + 1),
        (moebius d : ℂ) * χ (d * m) * ((d : ℂ) ^ (-s) * (m : ℂ) ^ (-s)) := by
  unfold zeroDetectionMobiusPolynomial zeroDetectionLTruncation
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul]
  ring

/-- Regroup the finite product by the index `n = d m`.  The product range is
closed internally, so no index-range premise is exposed to callers. -/
theorem zeroDetectionFiniteProductCoefficient_expand (X Y q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    zeroDetectionMobiusPolynomial X q χ s * zeroDetectionLTruncation Y q χ s =
      ∑ n ∈ Finset.Icc 1 ((X + 1) * (Y + 1)),
        zeroDetectionFiniteProductCoefficient X Y q χ s n := by
  rw [zeroDetectionMobiusPolynomial_mul_truncation]
  symm
  unfold zeroDetectionFiniteProductCoefficient
  rw [← Finset.sum_product (Finset.Icc 1 (X + 1)) (Finset.Icc 1 (Y + 1))
    (fun dm : ℕ × ℕ =>
      (moebius dm.1 : ℂ) * χ (dm.1 * dm.2) *
        ((dm.1 : ℂ) ^ (-s) * (dm.2 : ℂ) ^ (-s)))]
  exact Finset.sum_fiberwise_of_maps_to
    (s := Finset.Icc 1 (X + 1) ×ˢ Finset.Icc 1 (Y + 1))
    (t := Finset.Icc 1 ((X + 1) * (Y + 1)))
    (g := fun dm : ℕ × ℕ => dm.1 * dm.2)
    (by
      intro dm hdm
      rw [Finset.mem_product] at hdm
      rcases hdm with ⟨hd, hm⟩
      rw [Finset.mem_Icc] at hd hm ⊢
      constructor
      · exact Nat.mul_pos hd.1 hm.1
      · exact Nat.mul_le_mul hd.2 hm.2)
    (fun dm =>
      (moebius dm.1 : ℂ) * χ (dm.1 * dm.2) *
        ((dm.1 : ℂ) ^ (-s) * (dm.2 : ℂ) ^ (-s)))

/-- At a fixed product index, the finite detector coefficient factors as the
truncated Möbius convolution coefficient times `χ(n)n^{-s}`. -/
theorem zeroDetectionFiniteProductCoefficient_factor (X Y q n : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    zeroDetectionFiniteProductCoefficient X Y q χ s n =
      zeroDetectionTruncatedConvolutionCoefficient X Y n * χ n * (n : ℂ) ^ (-s) := by
  unfold zeroDetectionFiniteProductCoefficient zeroDetectionTruncatedConvolutionCoefficient
  calc
    _ = ∑ dm ∈ Finset.Icc 1 (X + 1) ×ˢ Finset.Icc 1 (Y + 1) with dm.1 * dm.2 = n,
        (moebius dm.1 : ℂ) * χ n * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro dm hdm
      rw [Finset.mem_filter] at hdm
      have hχ : χ ((dm.1 : ZMod q) * (dm.2 : ZMod q)) = χ (n : ZMod q) := by
        rw [← Nat.cast_mul, hdm.2]
      have hpow : (dm.1 : ℂ) ^ (-s) * (dm.2 : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := by
        calc
          (dm.1 : ℂ) ^ (-s) * (dm.2 : ℂ) ^ (-s) =
              (dm.1 * dm.2 : ℂ) ^ (-s) := natural_cpow_mul_neg dm.1 dm.2 s
          _ = (n : ℂ) ^ (-s) := by
            rw [← Nat.cast_mul]
            exact congrArg (fun k : ℕ => (k : ℂ) ^ (-s)) hdm.2
      rw [hχ, hpow]
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]

end RHTower
