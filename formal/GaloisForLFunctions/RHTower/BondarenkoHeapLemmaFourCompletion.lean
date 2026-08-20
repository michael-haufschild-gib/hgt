/-
# Bondarenko--Heap Lemma 4: exact finite Fourier completion

This module supplies the discrete completion identity behind Lemma 4 of
Bondarenko--Heap, `Siegel Zeros and small gaps between zeros of the Riemann
zeta function` (arXiv:2608.07399).  It treats arbitrary finite weights, so no
smoothness, support, or bounded-variation premise enters the algebraic layer.
-/
import GaloisForLFunctions.RHTower.QuadraticJacobiSum

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Negative-phase finite additive Fourier transform on a certified odd prime field. -/
def oddPrimeAdditiveFourier (p : OddPrime) (f : ZMod p.1 → ℂ) (b : ZMod p.1) : ℂ :=
  ∑ a : ZMod p.1, f a * ZMod.stdAddChar (-(b * a))

/-- Exact finite Fourier inversion for the standard additive character. -/
theorem oddPrimeAdditiveFourier_inversion (p : OddPrime) (f : ZMod p.1 → ℂ)
    (x : ZMod p.1) :
    f x = (p.1 : ℂ)⁻¹ * ∑ b : ZMod p.1,
      oddPrimeAdditiveFourier p f b * ZMod.stdAddChar (b * x) := by
  have hcard : (p.1 : ℂ) ≠ 0 := by exact_mod_cast p.2.1.ne_zero
  have hsum (t : ZMod p.1) :
      ∑ b : ZMod p.1, ZMod.stdAddChar (b * t) =
        if t = 0 then (p.1 : ℂ) else 0 := by
    simpa using AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p.1)) t
      (ZMod.isPrimitive_stdAddChar p.1)
  have hinner : ∑ b : ZMod p.1,
      oddPrimeAdditiveFourier p f b * ZMod.stdAddChar (b * x) =
      ∑ a : ZMod p.1, f a * ∑ b : ZMod p.1,
        ZMod.stdAddChar (b * (x - a)) := by
    unfold oddPrimeAdditiveFourier
    calc
      _ = ∑ b : ZMod p.1, ∑ a : ZMod p.1,
          (f a * ZMod.stdAddChar (-(b * a))) * ZMod.stdAddChar (b * x) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.sum_mul]
      _ = ∑ a : ZMod p.1, ∑ b : ZMod p.1,
          (f a * ZMod.stdAddChar (-(b * a))) * ZMod.stdAddChar (b * x) :=
            Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        calc
          f a * ZMod.stdAddChar (-(b * a)) * ZMod.stdAddChar (b * x) =
              f a * (ZMod.stdAddChar (-(b * a)) * ZMod.stdAddChar (b * x)) := by ring
          _ = _ := by
            rw [← ZMod.stdAddChar.map_add_eq_mul]
            congr 1
            ring_nf
  rw [hinner]
  simp_rw [hsum, sub_eq_zero]
  simp only [apply_ite, mul_zero]
  have hsumx : ∑ a : ZMod p.1, (if x = a then f a * (p.1 : ℂ) else 0) =
      f x * (p.1 : ℂ) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hbx
      simp [Ne.symm hbx]
    · simp
  rw [hsumx]
  field_simp

/-- A finite weighted incomplete quadratic correlation in the prime-field source case. -/
def oddPrimeQuadraticWeightedCorrelation (p : OddPrime) (k r : ZMod p.1)
    (s : Finset ℤ) (w : ℤ → ℂ) : ℂ :=
  ∑ m ∈ s, w m * oddPrimeQuadraticCharacter p (m : ZMod p.1) *
    oddPrimeQuadraticCharacter p (k * (m : ZMod p.1) + r)

/-- Positive-phase Fourier transform of an arbitrary finite source weight. -/
def oddPrimeWeightFourier (p : OddPrime) (s : Finset ℤ) (w : ℤ → ℂ)
    (b : ZMod p.1) : ℂ :=
  ∑ m ∈ s, w m * ZMod.stdAddChar (b * (m : ZMod p.1))

/-- Exact Fourier completion of the source's weighted quadratic correlation at an odd prime.
The nonzero-frequency factor is the established `oddPrimeQuadraticAdditiveCorrelation`; no
character-sum estimate, weight regularity, or analytic hypothesis is used. -/
theorem oddPrime_quadratic_weightedCorrelation_fourierCompletion
    (p : OddPrime) (k r : ZMod p.1) (s : Finset ℤ) (w : ℤ → ℂ) :
    oddPrimeQuadraticWeightedCorrelation p k r s w =
      (p.1 : ℂ)⁻¹ * ∑ b : ZMod p.1,
        oddPrimeQuadraticAdditiveCorrelation p k r b * oddPrimeWeightFourier p s w b := by
  let F : ZMod p.1 → ℂ := fun a =>
    oddPrimeQuadraticCharacter p a * oddPrimeQuadraticCharacter p (k * a + r)
  have hfourier (x : ZMod p.1) :
      F x = (p.1 : ℂ)⁻¹ * ∑ b : ZMod p.1,
        oddPrimeQuadraticAdditiveCorrelation p k r b * ZMod.stdAddChar (b * x) := by
    simpa [oddPrimeAdditiveFourier, oddPrimeQuadraticAdditiveCorrelation, F] using
      oddPrimeAdditiveFourier_inversion p F x
  unfold oddPrimeQuadraticWeightedCorrelation oddPrimeWeightFourier
  calc
    _ = ∑ m ∈ s, w m * F (m : ZMod p.1) := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [F]
      ring
    _ = ∑ m ∈ s, w m * ((p.1 : ℂ)⁻¹ * ∑ b : ZMod p.1,
        oddPrimeQuadraticAdditiveCorrelation p k r b *
          ZMod.stdAddChar (b * (m : ZMod p.1))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hfourier]
    _ = (p.1 : ℂ)⁻¹ * ∑ b : ZMod p.1,
        oddPrimeQuadraticAdditiveCorrelation p k r b *
          ∑ m ∈ s, w m * ZMod.stdAddChar (b * (m : ZMod p.1)) := by
      calc
        _ = ∑ m ∈ s, (p.1 : ℂ)⁻¹ *
            (w m * ∑ b : ZMod p.1,
              oddPrimeQuadraticAdditiveCorrelation p k r b *
                ZMod.stdAddChar (b * (m : ZMod p.1))) := by
              apply Finset.sum_congr rfl
              intro m hm
              ring
        _ = (p.1 : ℂ)⁻¹ * ∑ m ∈ s, w m * ∑ b : ZMod p.1,
            oddPrimeQuadraticAdditiveCorrelation p k r b *
              ZMod.stdAddChar (b * (m : ZMod p.1)) := by
              rw [Finset.mul_sum]
        _ = (p.1 : ℂ)⁻¹ * ∑ b : ZMod p.1, ∑ m ∈ s,
            (w m * oddPrimeQuadraticAdditiveCorrelation p k r b) *
              ZMod.stdAddChar (b * (m : ZMod p.1)) := by
              apply congrArg (fun z : ℂ => (p.1 : ℂ)⁻¹ * z)
              calc
                _ = ∑ m ∈ s, ∑ b : ZMod p.1,
                    (w m * oddPrimeQuadraticAdditiveCorrelation p k r b) *
                      ZMod.stdAddChar (b * (m : ZMod p.1)) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro b hb
                    ring
                _ = _ := Finset.sum_comm
        _ = _ := by
          apply congrArg (fun z : ℂ => (p.1 : ℂ)⁻¹ * z)
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring

end RHTower
