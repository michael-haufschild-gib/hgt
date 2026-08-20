/-
# Chen--Gupta--Li analytic detector anchor

The zero detector is ultimately evaluated away from the absolute-convergence
half-plane, but its initial identity is anchored there.  This module packages
points with `Re(s) > 1` as data and records two unconditional facts supplied
by the analytic continuation and L-series libraries: the Dirichlet L-function
agrees with its series, and the full character-twisted Möbius inverse
multiplies that series to one.

It intentionally does not extend either identity to a zero in the critical
strip; that continuation/contour step remains to be formalized.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteZeroDetector
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

/-- A complex point in the half-plane where a Dirichlet character L-series is
absolutely convergent.  Its defining inequality is certified data, not a
premise of the theorems below. -/
def CGLAbsoluteConvergencePoint := {s : ℂ // 1 < s.re}

/-- Finite coefficient function of the source truncated Möbius inverse. -/
def cglTruncatedMobiusTwist (X q : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 (X + 1) then (ArithmeticFunction.moebius n : ℂ) * χ n else 0

/-- The literal finite Möbius detector polynomial is exactly the L-series of
its finite-support coefficient function, at every complex point. -/
theorem lseries_cglTruncatedMobiusTwist_eq_zeroDetectionMobiusPolynomial
    (X q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    LSeries (cglTruncatedMobiusTwist X q χ) s = zeroDetectionMobiusPolynomial X q χ s := by
  unfold LSeries
  rw [tsum_eq_sum (s := Finset.Icc 1 (X + 1))]
  · unfold zeroDetectionMobiusPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      rw [Finset.mem_Icc] at hn
      omega
    rw [LSeries.term_of_ne_zero hn0]
    simp only [cglTruncatedMobiusTwist, if_pos hn]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
  · intro n hn
    rw [LSeries.term]
    split_ifs with hn0
    · rfl
    · simp [cglTruncatedMobiusTwist, hn]

/-- The L-series of the finite Möbius coefficient function is summable at every
complex point because its support is literally finite. -/
theorem lseriesSummable_cglTruncatedMobiusTwist (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    LSeriesSummable (cglTruncatedMobiusTwist X q χ) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc 1 (X + 1)))
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hmem
  rw [LSeries.term] at hn
  by_cases hn0 : n = 0
  · simp [hn0] at hn
  · simp [hn0, cglTruncatedMobiusTwist] at hn
    exact hmem (Finset.mem_Icc.mpr ⟨hn.1, hn.2.1⟩)

/-- On the certified absolute-convergence half-plane, the analytically
continued Dirichlet L-function agrees with its defining L-series. -/
theorem cgl_lfunction_eq_lseries (q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLAbsoluteConvergencePoint) :
    DirichletCharacter.LFunction χ s.1 = LSeries (fun n : ℕ => χ n) s.1 := by
  exact DirichletCharacter.LFunction_eq_LSeries χ s.2

/-- The full character-twisted Möbius inverse is an exact multiplicative
inverse of the Dirichlet L-series at every certified convergence point. -/
theorem cgl_lseries_mul_full_mobius_eq_one (q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLAbsoluteConvergencePoint) :
    LSeries (fun n : ℕ => χ n) s.1 *
      LSeries ((fun n : ℕ => χ n) * fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s.1 = 1 := by
  exact DirichletCharacter.LSeries.mul_mu_eq_one χ s.2

/-- On the certified absolute-convergence half-plane, the source finite
product `M_X(s,χ)L(s,χ)` is exactly the L-series of its Dirichlet convolution
coefficient function. -/
theorem zeroDetectionMobiusPolynomial_mul_lfunction_eq_convolutionLSeries
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLAbsoluteConvergencePoint) :
    zeroDetectionMobiusPolynomial X (q + 1) χ s.1 * DirichletCharacter.LFunction χ s.1 =
      LSeries (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
        (fun n : ℕ => χ n)) s.1 := by
  calc
    zeroDetectionMobiusPolynomial X (q + 1) χ s.1 * DirichletCharacter.LFunction χ s.1 =
        LSeries (cglTruncatedMobiusTwist X (q + 1) χ) s.1 *
          LSeries (fun n : ℕ => χ n) s.1 := by
      rw [lseries_cglTruncatedMobiusTwist_eq_zeroDetectionMobiusPolynomial,
        cgl_lfunction_eq_lseries]
    _ = LSeries (LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
        (fun n : ℕ => χ n)) s.1 := by
      exact (LSeries_convolution'
        (lseriesSummable_cglTruncatedMobiusTwist X (q + 1) χ s.1)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re χ s.2)).symm

/-- A certified zero of a Dirichlet L-function at the positive modulus `q+1`.
The vanishing proof belongs to the zero datum, so zero-side identities expose
no premise. -/
structure CGLDirichletLZero (q : ℕ) where
  character : DirichletCharacter ℂ (q + 1)
  point : ℂ
  vanishes : DirichletCharacter.LFunction character point = 0

/-- The exact finite remainder used at a certified L-function zero. -/
def cglFiniteDetectorRemainder (X q : ℕ) (z : CGLDirichletLZero q) : ℂ :=
  1 - zeroDetectionMobiusPolynomial X (q + 1) z.character z.point *
    DirichletCharacter.LFunction z.character z.point

/-- At every certified zero, the finite detector remainder is exactly one. -/
theorem cglFiniteDetectorRemainder_at_zero (X q : ℕ) (z : CGLDirichletLZero q) :
    cglFiniteDetectorRemainder X q z = 1 := by
  unfold cglFiniteDetectorRemainder
  rw [z.vanishes, mul_zero, sub_zero]

/-- The finite detector remainder has norm one at every certified zero. -/
theorem norm_cglFiniteDetectorRemainder_at_zero (X q : ℕ) (z : CGLDirichletLZero q) :
    ‖cglFiniteDetectorRemainder X q z‖ = 1 := by
  rw [cglFiniteDetectorRemainder_at_zero]
  norm_num

/-- Through the finite cutoff, the coefficients of the full product
`M_X(s, χ)L(s, χ)` are exactly the truncated Möbius divisor coefficients times
the character.  This is a coefficient identity, so no convergence or zero
assumption is involved. -/
theorem cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (n : Fin (X + 1)) :
    LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) (n.1 + 1) =
      (zeroDetectionMobiusCoefficient X (n.1 + 1) : ℂ) * χ (n.1 + 1) := by
  let k : ℕ := n.1 + 1
  have hkpos : k ≠ 0 := by
    dsimp [k]
    omega
  have hkbound : k ≤ X + 1 := by
    dsimp [k]
    omega
  have hfilter : k.divisors.filter (fun d => d ≤ X + 1) = k.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    have hdk : d ∣ k := (Nat.mem_divisors.mp hd).1
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hkpos) hdk).trans hkbound
  have hmain : LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
      (fun m : ℕ => χ m) k = (zeroDetectionMobiusCoefficient X k : ℂ) * χ k := by
    rw [LSeries.convolution_def]
    calc
      (∑ p ∈ k.divisorsAntidiagonal,
          cglTruncatedMobiusTwist X (q + 1) χ p.1 * χ p.2) =
          ∑ p ∈ k.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℂ) * χ k := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
        have hp1pos : 0 < p.1 :=
          Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hp).1
        have hp1le : p.1 ≤ k := by
          exact Nat.le_of_dvd (Nat.pos_of_ne_zero hkpos) ⟨p.2, hpdata.1.symm⟩
        have hp1mem : p.1 ∈ Finset.Icc 1 (X + 1) :=
          Finset.mem_Icc.mpr ⟨hp1pos, hp1le.trans hkbound⟩
        rw [cglTruncatedMobiusTwist, if_pos hp1mem]
        have hχ : χ ((p.1 : ZMod (q + 1)) * (p.2 : ZMod (q + 1))) = χ (k : ZMod (q + 1)) := by
          rw [← Nat.cast_mul, hpdata.1]
        calc
          (ArithmeticFunction.moebius p.1 : ℂ) * χ p.1 * χ p.2 =
              (ArithmeticFunction.moebius p.1 : ℂ) * (χ p.1 * χ p.2) := by ring
          _ = (ArithmeticFunction.moebius p.1 : ℂ) * χ (p.1 * p.2) := by rw [← map_mul]
          _ = _ := by rw [hχ]
      _ = (∑ p ∈ k.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℂ)) * χ k := by
        rw [← Finset.sum_mul]
      _ = (zeroDetectionMobiusCoefficient X k : ℂ) * χ k := by
        unfold zeroDetectionMobiusCoefficient
        rw [hfilter]
        have hsum : (∑ p ∈ k.divisorsAntidiagonal, (ArithmeticFunction.moebius p.1 : ℂ)) =
            ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℂ) :=
          Nat.sum_divisorsAntidiagonal (fun d _ => (ArithmeticFunction.moebius d : ℂ))
        rw [hsum]
        simp
  simpa [k] using hmain

/-- The unit coefficient of the full finite detector product is one. -/
theorem cglTruncatedMobiusTwist_convolution_character_one
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) :
    LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ) (fun m : ℕ => χ m) 1 = 1 := by
  simpa [zeroDetectionMobiusCoefficient_one] using
    cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient X q χ (0 : Fin (X + 1))

/-- Every non-unit coefficient through the finite cutoff in the full detector
product vanishes.  `n : Fin X` represents the complete interval from `2` to
`X + 1`, without a caller-supplied range premise. -/
theorem cglTruncatedMobiusTwist_convolution_character_vanishes_below_cutoff
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (n : Fin X) :
    LSeries.convolution (cglTruncatedMobiusTwist X (q + 1) χ)
      (fun m : ℕ => χ m) (n.1 + 2) = 0 := by
  let k : Fin (X + 1) := ⟨n.1 + 1, by omega⟩
  have hk : k.1 + 1 = n.1 + 2 := by
    dsimp [k]
  rw [← hk, cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient]
  have hc : (zeroDetectionMobiusCoefficient X (n.1 + 2) : ℂ) = 0 := by
    exact_mod_cast zeroDetectionMobiusCoefficient_vanishes_below_cutoff X n
  rw [hk, hc, zero_mul]

end RHTower
