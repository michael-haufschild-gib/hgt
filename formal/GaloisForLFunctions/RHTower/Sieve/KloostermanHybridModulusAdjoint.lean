import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridModulusLinear

/-!
# Adjoint laws for signed Kloosterman modulus averages

Spectral cancellation requires the coefficient sequences to be shared across moduli and the
signed modulus amplitude to carry an exact adjoint.  This file proves the finite conjugation laws
from additive-character orthogonality and Kloosterman conjugation, then specializes the hybrid
form to shared arithmetic coefficients.  No spectral estimate is assumed.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Conjugating an additive hybrid logarithmic polynomial negates frequency and height. -/
theorem star_additiveHybridLogPoly
    (q N : ℕ) (a : ℕ → ℂ) (d : ZMod (q + 1)) (w : ℝ) :
    star (additiveHybridLogPoly q N a d w) =
      additiveHybridLogPoly q N (fun n => star (a n)) (-d) (-w) := by
  unfold additiveHybridLogPoly
  change (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 N,
    a n * Complex.exp
      (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) *
      ZMod.stdAddChar (d * (Nat.cast n : ZMod (q + 1)))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_mul, map_mul, ← Complex.exp_conj, ← AddChar.map_neg_eq_conj]
  congr 2
  · rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  · ring

/-- Physical-height form of additive hybrid conjugation. -/
theorem star_additiveHybridDirichletPoly
    (q N : ℕ) (a : ℕ → ℂ) (d : ZMod (q + 1)) (t : ℝ) :
    star (additiveHybridDirichletPoly q N a d t) =
      additiveHybridDirichletPoly q N (fun n => star (a n)) (-d) (-t) := by
  unfold additiveHybridDirichletPoly
  rw [star_additiveHybridLogPoly]
  congr 1
  ring

/-- The complete Kloosterman bilinear form is symmetric. -/
theorem kloostermanBilinear_comm
    (q : ℕ) [NeZero q] (a b : ZMod q → ℂ) :
    kloostermanBilinear q a b = kloostermanBilinear q b a := by
  rw [kloostermanBilinear_eq, kloostermanBilinear_eq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  rw [kloostermanSum_comm]
  ring

/-- Adjoint of one complete Kloosterman bilinear form. -/
theorem star_kloostermanBilinear
    (q : ℕ) [NeZero q] (a b : ZMod q → ℂ) :
    star (kloostermanBilinear q a b) =
      kloostermanBilinear q
        (fun m => star (a (-m))) (fun n => star (b (-n))) := by
  rw [kloostermanBilinear_eq, kloostermanBilinear_eq]
  change (starRingEnd ℂ)
      (∑ m : ZMod q, a m * ∑ n : ZMod q, b n * kloostermanSum q m n) = _
  rw [map_sum]
  simp only [map_mul, map_sum]
  change (∑ m : ZMod q,
      star (a m) * ∑ n : ZMod q, star (b n) * star (kloostermanSum q m n)) = _
  simp_rw [star_kloostermanSum]
  let e : ZMod q ≃ ZMod q := Equiv.neg (ZMod q)
  have hinner (m : ZMod q) :
      (∑ n : ZMod q, star (b n) * kloostermanSum q (-m) (-n)) =
        ∑ n : ZMod q, star (b (-n)) * kloostermanSum q (-m) n := by
    simpa only [e, Equiv.neg_apply, neg_neg] using
      (e.sum_comp (fun n : ZMod q =>
        star (b n) * kloostermanSum q (-m) (-n))).symm
  calc
    (∑ m : ZMod q,
        star (a m) * ∑ n : ZMod q, star (b n) * kloostermanSum q (-m) (-n)) =
        ∑ m : ZMod q, star (a m) * ∑ n : ZMod q,
          star (b (-n)) * kloostermanSum q (-m) n := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [hinner]
    _ = ∑ m : ZMod q,
          (star (a (-m)) * ∑ n : ZMod q,
            star (b (-n)) * kloostermanSum q m n) := by
      simpa only [e, Equiv.neg_apply, neg_neg] using
        (e.sum_comp (fun m : ZMod q =>
          star (a m) * ∑ n : ZMod q,
            star (b (-n)) * kloostermanSum q (-m) n)).symm
    _ = _ := rfl

/-- Symmetry survives the signed sum across moduli. -/
theorem kloostermanModulusBilinear_comm
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (a b : (q : ℕ) → ZMod (q + 1) → ℂ) :
    kloostermanModulusBilinear Q w a b =
      kloostermanModulusBilinear Q w b a := by
  unfold kloostermanModulusBilinear
  apply Finset.sum_congr rfl
  intro q _hq
  rw [kloostermanBilinear_comm]

/-- Exact adjoint of the signed modulus-average bilinear form. -/
theorem star_kloostermanModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (a b : (q : ℕ) → ZMod (q + 1) → ℂ) :
    star (kloostermanModulusBilinear Q w a b) =
      kloostermanModulusBilinear Q (fun q => star (w q))
        (fun q m => star (a q (-m))) (fun q n => star (b q (-n))) := by
  unfold kloostermanModulusBilinear
  change (starRingEnd ℂ)
      (∑ q ∈ Q, w q * kloostermanBilinear (q + 1) (a q) (b q)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [map_mul]
  change star (w q) * star (kloostermanBilinear (q + 1) (a q) (b q)) = _
  rw [star_kloostermanBilinear]

/-- Signed hybrid Kloosterman amplitude with the same two arithmetic coefficient sequences at
every modulus. -/
def kloostermanSharedHybridModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  kloostermanHybridModulusBilinear Q w N M (fun _ => a) (fun _ => b) t

/-- Shared-coefficient carrier is symmetric in its two length/coefficient legs. -/
theorem kloostermanSharedHybridModulusBilinear_comm
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    kloostermanSharedHybridModulusBilinear Q w N M a b t =
      kloostermanSharedHybridModulusBilinear Q w M N b a t := by
  unfold kloostermanSharedHybridModulusBilinear
  rw [kloostermanHybridModulusBilinear_eq,
    kloostermanHybridModulusBilinear_eq]
  exact kloostermanModulusBilinear_comm Q w _ _

/-- Exact time-reflection adjoint of the shared signed hybrid carrier. -/
theorem star_kloostermanSharedHybridModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    star (kloostermanSharedHybridModulusBilinear Q w N M a b t) =
      kloostermanSharedHybridModulusBilinear Q (fun q => star (w q)) N M
        (fun n => star (a n)) (fun n => star (b n)) (-t) := by
  unfold kloostermanSharedHybridModulusBilinear
  rw [kloostermanHybridModulusBilinear_eq,
    star_kloostermanModulusBilinear,
    kloostermanHybridModulusBilinear_eq]
  congr 1
  · funext q d
    rw [star_additiveHybridDirichletPoly]
    simp
  · funext q n
    rw [star_additiveHybridDirichletPoly]
    simp

end

end RHTower.Sieve
