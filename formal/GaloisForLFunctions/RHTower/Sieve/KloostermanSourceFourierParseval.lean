import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalSourceFourier
import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveLargeSieve

/-!
# Parseval control of Kloosterman source transforms

Arbitrary finite natural-number sources may collide after reduction modulo a Kloosterman modulus.
This module first compresses coefficients exactly by residue class. Existing finite additive
Parseval then gives the exact full-frequency energy and, by restricting to inverse unit
frequencies, an unconditional energy bound for `kloostermanSourceFourier`.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Total source coefficient in one residue class. -/
def kloostermanSourceResidue
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) (z : ZMod q) : ℂ :=
  (B.filter (fun n : ℕ => (n : ZMod q) = z)).sum b

/-- Full additive source transform at an arbitrary residue frequency. -/
def kloostermanSourceFourierFull
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) (t : ZMod q) : ℂ :=
  ∑ n ∈ B, b n * ZMod.stdAddChar (t * (n : ZMod q))

/-- The source transform in the terminal factorization is the full transform at the inverse unit
frequency. -/
theorem kloostermanSourceFourier_eq_full_inverse
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ)
    (x : (ZMod q)ˣ) :
    kloostermanSourceFourier q B b x =
      kloostermanSourceFourierFull q B b ((x⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  unfold kloostermanSourceFourier kloostermanSourceFourierFull
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  ring

/-- Full source Fourier transform after exact compression of colliding natural indices by their
residue class. -/
theorem kloostermanSourceFourierFull_eq_residueFourier
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ)
    (t : ZMod q) :
    kloostermanSourceFourierFull q B b t =
      ∑ z : ZMod q, kloostermanSourceResidue q B b z *
        ZMod.stdAddChar (t * z) := by
  classical
  unfold kloostermanSourceFourierFull kloostermanSourceResidue
  symm
  calc
    (∑ z : ZMod q,
        (B.filter (fun n : ℕ => (n : ZMod q) = z)).sum b *
          ZMod.stdAddChar (t * z)) =
        ∑ z : ZMod q,
          (B.filter (fun n : ℕ => (n : ZMod q) = z)).sum
            (fun n => b n * ZMod.stdAddChar (t * z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
    _ = ∑ z : ZMod q,
          (B.filter (fun n : ℕ => (n : ZMod q) = z)).sum
            (fun n => b n * ZMod.stdAddChar (t * (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]
    _ = ∑ n ∈ B, b n * ZMod.stdAddChar (t * (n : ZMod q)) := by
      exact Finset.sum_fiberwise B (fun n => (n : ZMod q))
        (fun n => b n * ZMod.stdAddChar (t * (n : ZMod q)))

/-- Exact full-frequency Parseval identity, with source collisions retained in the residue energy. -/
theorem sum_normSq_kloostermanSourceFourierFull_eq_residueEnergy
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) :
    ∑ t : ZMod q, Complex.normSq (kloostermanSourceFourierFull q B b t) =
      (q : ℝ) * ∑ z : ZMod q, Complex.normSq (kloostermanSourceResidue q B b z) := by
  simp_rw [kloostermanSourceFourierFull_eq_residueFourier]
  exact sum_normSq_weighted_stdAddChar_mul_of_injective
    q (fun z : ZMod q => z) Function.injective_id (kloostermanSourceResidue q B b)

/-- Unit-frequency source energy is bounded by the exact full residue-collision energy. -/
theorem sum_normSq_kloostermanSourceFourier_le_residueEnergy
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) :
    ∑ x : (ZMod q)ˣ, Complex.normSq (kloostermanSourceFourier q B b x) ≤
      (q : ℝ) * ∑ z : ZMod q, Complex.normSq (kloostermanSourceResidue q B b z) := by
  simp_rw [kloostermanSourceFourier_eq_full_inverse]
  let f : (ZMod q)ˣ → ZMod q := fun x => ((x⁻¹ : (ZMod q)ˣ) : ZMod q)
  have hf : Function.Injective f := by
    intro x y hxy
    have hinv : x⁻¹ = y⁻¹ := Units.ext hxy
    exact inv_injective hinv
  calc
    (∑ x : (ZMod q)ˣ,
        Complex.normSq (kloostermanSourceFourierFull q B b (f x))) =
        ∑ t ∈ Finset.univ.image f,
          Complex.normSq (kloostermanSourceFourierFull q B b t) := by
      symm
      exact Finset.sum_image hf.injOn
    _ ≤ ∑ t : ZMod q,
          Complex.normSq (kloostermanSourceFourierFull q B b t) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr (fun x hx => Finset.mem_univ (f x)))
        (fun t ht hnot => Complex.normSq_nonneg _)
    _ = (q : ℝ) * ∑ z : ZMod q,
          Complex.normSq (kloostermanSourceResidue q B b z) := by
      rw [sum_normSq_kloostermanSourceFourierFull_eq_residueEnergy]

end

end RHTower.Sieve
