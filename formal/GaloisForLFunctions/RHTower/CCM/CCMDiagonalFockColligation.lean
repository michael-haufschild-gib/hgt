import GaloisForLFunctions.RHTower.CCM.CCMHalfUnitCauchySeam

/-!
# The diagonal Fock coordinate as a polar–prime Mellin colligation

Four exact mechanisms of the card are formalized.

*The two Laplace channels.*  `C(x,y) = ∫_0^∞ e^{-xh}e^{-yh}dh = 1/(x+y)` and
`B(x,y) = ∫_0^∞ e^{-(x+1/2)h}e^{-(y+1/2)h}dh = 1/(x+y+1)` — equations `(9)` and `(11)`.  Both come
from the corpus ray integral `integral_exp_ray`.

*The prime feature.*  `(√(Λ(n)/n) n^{-x})(√(Λ(n)/n) n^{-y}) = (Λ(n)/n) n^{-(x+y)}`, which is the
termwise content of `(10)`: the von Mangoldt channel is an explicit positive Gram.

*The incidence rearrangement.*  `M = C + B − E` is exactly `C = E − B + M`, which is `(8)` ⟹ `(6)`.

*The four-channel passivity criterion.*  The kernel identity passes to every finite quadratic form,
and the contraction criterion is then the stated inequality — equations `(18)`–`(19)`.

The Laplace–Stieltjes identity `(7)`, the Krein Gram representation `(12)`, the RKHS `H_A` and the
diagonal Fock theorem are cited parents and stay outside the Lean statement.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The two Laplace channels -/

/-- **Equation (9).**  The universal Cauchy coordinate is the ray Laplace Gram. -/
theorem cauchy_channel_eq {x y : ℝ} (h : 0 < x + y) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * Real.exp (-(y * t))) = 1 / (x + y) :=
  integral_exp_ray h

/-- **Equation (11).**  The shifted polar channel is the shifted ray Laplace Gram. -/
theorem polar_channel_eq {x y : ℝ} (h : 0 < x + y + 1) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-((x + 1 / 2) * t)) * Real.exp (-((y + 1 / 2) * t)))
      = 1 / (x + y + 1) := by
  have hsum : 0 < (x + 1 / 2) + (y + 1 / 2) := by linarith
  have hval := integral_exp_ray hsum
  rw [hval]
  congr 1
  ring

/-! ## The prime feature -/

/-- **Equation (10), termwise.**  The von Mangoldt channel is an explicit positive Gram. -/
theorem prime_feature_mul {Lam nn x y : ℝ} (hn : 0 < nn) (hL : 0 ≤ Lam) :
    (Real.sqrt (Lam / nn) * nn ^ (-x)) * (Real.sqrt (Lam / nn) * nn ^ (-y))
      = (Lam / nn) * nn ^ (-(x + y)) := by
  have hdiv : 0 ≤ Lam / nn := div_nonneg hL (le_of_lt hn)
  have hsq : Real.sqrt (Lam / nn) * Real.sqrt (Lam / nn) = Lam / nn :=
    Real.mul_self_sqrt hdiv
  have hpow : nn ^ (-x) * nn ^ (-y) = nn ^ (-(x + y)) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc (Real.sqrt (Lam / nn) * nn ^ (-x)) * (Real.sqrt (Lam / nn) * nn ^ (-y))
      = (Real.sqrt (Lam / nn) * Real.sqrt (Lam / nn)) * (nn ^ (-x) * nn ^ (-y)) := by ring
    _ = (Lam / nn) * nn ^ (-(x + y)) := by rw [hsq, hpow]

/-! ## The incidence rearrangement -/

/-- **Equations (8) → (6).**  The colligation identity. -/
theorem colligation_rearrange {C E B M : ℝ} (h : M = C + B - E) : C = E - B + M := by
  linarith

/-- **Equation (6), reverse.** -/
theorem colligation_rearrange' {C E B M : ℝ} (h : C = E - B + M) : M = C + B - E := by
  linarith

/-! ## The four-channel passivity criterion -/

/-- **Equation (18).**  The kernel colligation passes to every finite quadratic form. -/
theorem quadratic_colligation {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (K0 KE KB KR : ι → ι → ℝ) (h : ∀ i j, K0 i j = KE i j - KB i j + KR i j) :
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * K0 i j)
      = (∑ i ∈ s, ∑ j ∈ s, c i * c j * KE i j)
        - (∑ i ∈ s, ∑ j ∈ s, c i * c j * KB i j)
        + (∑ i ∈ s, ∑ j ∈ s, c i * c j * KR i j) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h i j]
  ring

/-- **Equation (19).**  Under the colligation, the contraction criterion is exactly the
four-channel passivity inequality. -/
theorem passivity_iff {A Q0 QE QB QR : ℝ} (h : Q0 = QE - QB + QR) :
    0 ≤ A - Q0 ↔ QE + QR ≤ A + QB := by
  constructor <;> intro hh <;> linarith

end GaloisForLFunctions.RHTower

end
