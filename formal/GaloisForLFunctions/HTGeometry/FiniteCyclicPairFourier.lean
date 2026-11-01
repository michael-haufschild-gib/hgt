import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval

/-!
# Fourier analysis on a product of two cyclic groups

The transform is the composite of the standard cyclic transforms. Cyclic Parseval
supplies its norm identity; polarization gives the real cross-inner-product law.
Affine shears act by dual shears with the exact translation phase.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Finset

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ} [NeZero n]

/-- The two-coordinate Fourier transform is the composite of the standard cyclic transforms. -/
def cyclicPairFourier (f : ZMod n × ZMod n → ℂ) (a : ZMod n × ZMod n) : ℂ :=
  ZMod.dft (fun x => ZMod.dft (fun y => f (x, y)) a.2) a.1

theorem cyclicPairFourier_apply (f : ZMod n × ZMod n → ℂ) (a b : ZMod n) :
    cyclicPairFourier f (a, b) =
      ∑ x, ∑ y, ZMod.stdAddChar (-(x * a + y * b)) * f (x, y) := by
  simp only [cyclicPairFourier, ZMod.dft_apply, smul_eq_mul, Finset.mul_sum,
    neg_add, AddChar.map_add_eq_mul, mul_assoc]

theorem cyclicPairFourier_zero (f : ZMod n × ZMod n → ℂ) :
    cyclicPairFourier f (0, 0) = ∑ p, f p := by
  simp only [cyclicPairFourier, ZMod.dft_apply_zero, Fintype.sum_prod_type]

/-- Parseval on the residue torus follows by applying cyclic Parseval in each coordinate. -/
theorem cyclicPairFourier_parseval (f : ZMod n × ZMod n → ℂ) :
    ∑ a, Complex.normSq (cyclicPairFourier f a) =
      (n : ℝ) ^ 2 * ∑ p, Complex.normSq (f p) := by
  simp only [Fintype.sum_prod_type, cyclicPairFourier]
  rw [Finset.sum_comm]
  simp_rw [GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval]
  rw [← Finset.mul_sum, ← mul_assoc, ← pow_two]

/-- Pullback by a horizontal affine shear gives the dual shear and its translation phase. -/
theorem cyclicPairFourier_shearX (f : ZMod n × ZMod n → ℂ)
    (s b a t : ZMod n) :
    cyclicPairFourier (fun p => f (p.1 + s * p.2 + b, p.2)) (a, t) =
      ZMod.stdAddChar (b * a) * cyclicPairFourier f (a, t - s * a) := by
  rw [cyclicPairFourier_apply, cyclicPairFourier_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Fintype.sum_equiv (Equiv.addRight (s * y + b))
    (fun x => ZMod.stdAddChar (-(x * a + y * t)) * f (x + s * y + b, y))
    (fun x => ZMod.stdAddChar (b * a) *
      (ZMod.stdAddChar (-(x * a + y * (t - s * a))) * f (x, y)))
  intro x
  change ZMod.stdAddChar (-(x * a + y * t)) * f (x + s * y + b, y) =
    ZMod.stdAddChar (b * a) *
      (ZMod.stdAddChar (-((x + (s * y + b)) * a + y * (t - s * a))) *
        f (x + (s * y + b), y))
  simp only [add_assoc]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Pullback by a vertical affine shear gives the other dual shear. -/
theorem cyclicPairFourier_shearY (f : ZMod n × ZMod n → ℂ)
    (s b a t : ZMod n) :
    cyclicPairFourier (fun p => f (p.1, p.2 + s * p.1 + b)) (a, t) =
      ZMod.stdAddChar (b * t) * cyclicPairFourier f (a - s * t, t) := by
  rw [cyclicPairFourier_apply, cyclicPairFourier_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Fintype.sum_equiv (Equiv.addRight (s * x + b))
    (fun y => ZMod.stdAddChar (-(x * a + y * t)) * f (x, y + s * x + b))
    (fun y => ZMod.stdAddChar (b * t) *
      (ZMod.stdAddChar (-(x * (a - s * t) + y * t)) * f (x, y)))
  intro y
  change ZMod.stdAddChar (-(x * a + y * t)) * f (x, y + s * x + b) =
    ZMod.stdAddChar (b * t) *
      (ZMod.stdAddChar (-(x * (a - s * t) + (y + (s * x + b)) * t)) *
        f (x, y + (s * x + b)))
  simp only [add_assoc]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem cyclicPairFourier_add (f g : ZMod n × ZMod n → ℂ)
    (a : ZMod n × ZMod n) :
    cyclicPairFourier (f + g) a = cyclicPairFourier f a + cyclicPairFourier g a := by
  rcases a with ⟨a, b⟩
  simp only [cyclicPairFourier_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Polarizing Parseval gives the real part of the cross-inner-product identity. -/
theorem cyclicPairFourier_re_inner (f g : ZMod n × ZMod n → ℂ) :
    ∑ a, (conj (cyclicPairFourier f a) * cyclicPairFourier g a).re =
      (n : ℝ) ^ 2 * ∑ p, (conj (f p) * g p).re := by
  have hquad (z w : ℂ) : Complex.normSq (z + w) =
      Complex.normSq z + Complex.normSq w + 2 * (conj z * w).re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have h := cyclicPairFourier_parseval (f + g)
  simp_rw [cyclicPairFourier_add, Pi.add_apply, hquad] at h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [cyclicPairFourier_parseval f, cyclicPairFourier_parseval g] at h
  nlinarith only [h]

end GaloisForLFunctions.HTGeometry
