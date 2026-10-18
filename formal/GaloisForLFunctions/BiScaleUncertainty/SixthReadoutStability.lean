import GaloisForLFunctions.BiScaleUncertainty.PrimeFamilyPhaseRecovery

/-!
# Stability of normalized sixth translated-moment readouts

Cubing the coefficients turns the sixth readout matrix into a rank-one Gram
matrix. Choosing one global sign gives polynomial error bounds valid even at
zero coordinates, together with stronger weighted estimates off the zero set.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CubedGram
set_option autoImplicit false

variable {ι : Type*} [Fintype ι]

/-- Sixth power of coefficient error in a fixed orientation. -/
def error6 (a b : ι → ℝ) : ℝ := ∑ i, (a i - b i)^6

/-- Squared coefficient error weighted by its local nondegeneracy. -/
def weightedError (a b : ι → ℝ) : ℝ :=
  ∑ i, (a i-b i)^2 * (a i^2+b i^2)^2

/-- Combined sixth-power mass of two coefficient vectors. -/
def mass6 (a b : ι → ℝ) : ℝ := ∑ i, (a i^6+b i^6)

/-- Squared Frobenius discrepancy of the normalized sixth readout matrices. -/
def readoutError (a b : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ((a i*a j)^3-(b i*b j)^3)^2

private theorem gram_expansion (x y : ι → ℝ) :
    (∑ i, ∑ j, (x i*x j-y i*y j)^2) =
      (∑ i, x i^2)^2+(∑ i, y i^2)^2-2*(∑ i, x i*y i)^2 := by
  calc
    _ = ∑ i, ∑ j, (x i^2*x j^2+y i^2*y j^2-2*(x i*y i)*(x j*y j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring_nf
      rw [← Finset.sum_mul]
      ring

private theorem difference_expansion (x y : ι → ℝ) :
    (∑ i, (x i-y i)^2) = (∑ i, x i^2)+(∑ i, y i^2)-2*(∑ i, x i*y i) := by
  calc
    _ = ∑ i, (x i^2+y i^2-2*(x i*y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem gram_bounds (x y : ι → ℝ) (hz : 0 ≤ ∑ i, x i*y i) :
    (∑ i, (x i-y i)^2)^2 ≤ 2*∑ i, ∑ j, (x i*x j-y i*y j)^2 ∧
    ((∑ i, x i^2)+(∑ i, y i^2))*(∑ i, (x i-y i)^2) ≤
      2*∑ i, ∑ j, (x i*x j-y i*y j)^2 := by
  have hd : 0 ≤ (∑ i, x i^2)+(∑ i, y i^2)-2*(∑ i, x i*y i) := by
    rw [← difference_expansion]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp := mul_nonneg hz hd
  have hs := sq_nonneg ((∑ i, x i^2)-(∑ i, y i^2))
  rw [gram_expansion, difference_expansion]
  constructor <;> nlinarith only [hp, hs]

private theorem scalar_sixth (u v : ℝ) : (u-v)^6 ≤ 16*(u^3-v^3)^2 := by
  have h : 0 ≤ 3*(u-v)^2*(u+v)^2*(3*(u+v)^2+2*(u-v)^2) := by positivity
  nlinarith only [h]

private theorem scalar_weighted (u v : ℝ) :
    (u-v)^2*(u^2+v^2)^2 ≤ 4*(u^3-v^3)^2 := by
  have h : 0 ≤ (u-v)^2*(u+v)^2*(2*(u^2+v^2)+(u+v)^2) := by positivity
  nlinarith only [h]

private theorem oriented_bounds (a b : ι → ℝ) (hz : 0 ≤ ∑ i, a i^3*b i^3) :
    (error6 a b)^2 ≤ 512*readoutError a b ∧
    mass6 a b*error6 a b ≤ 32*readoutError a b ∧
    mass6 a b*weightedError a b ≤ 8*readoutError a b := by
  let D := ∑ i, (a i^3-b i^3)^2
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hM : 0 ≤ mass6 a b := by unfold mass6; positivity
  have hT : 0 ≤ error6 a b := by unfold error6; positivity
  have h6 : error6 a b ≤ 16*D := by
    calc
      _ ≤ ∑ i, 16*(a i^3-b i^3)^2 :=
        Finset.sum_le_sum (fun i _ => scalar_sixth (a i) (b i))
      _ = _ := by rw [← Finset.mul_sum]
  have hw : weightedError a b ≤ 4*D := by
    calc
      _ ≤ ∑ i, 4*(a i^3-b i^3)^2 :=
        Finset.sum_le_sum (fun i _ => scalar_weighted (a i) (b i))
      _ = _ := by rw [← Finset.mul_sum]
  have hg := gram_bounds (fun i => a i^3) (fun i => b i^3) hz
  have hmass : (∑ i, (a i^3)^2)+(∑ i, (b i^3)^2) = mass6 a b := by
    simp only [mass6, Finset.sum_add_distrib, ← pow_mul]
  have herror : (∑ i, ∑ j, (a i^3*a j^3-b i^3*b j^3)^2) = readoutError a b := by
    simp only [readoutError, mul_pow]
  rw [hmass, herror] at hg
  change D^2 ≤ 2*readoutError a b ∧ mass6 a b*D ≤ 2*readoutError a b at hg
  have hsq := mul_nonneg (sub_nonneg.mpr h6) (show 0 ≤ 16*D+error6 a b by positivity)
  have hmul6 := mul_le_mul_of_nonneg_left h6 hM
  have hmulw := mul_le_mul_of_nonneg_left hw hM
  constructor
  · nlinarith only [hsq, hg.1]
  constructor
  · nlinarith only [hmul6, hg.2]
  · nlinarith only [hmulw, hg.2]

/-- A single common sign satisfies the global sixth-root bound, the nonzero-mass
cube-root bound, and the weighted Lipschitz bound, with no support assumptions. -/
theorem stability (a b : ι → ℝ) :
    ((error6 a b)^2 ≤ 512*readoutError a b ∧
      mass6 a b*error6 a b ≤ 32*readoutError a b ∧
      mass6 a b*weightedError a b ≤ 8*readoutError a b) ∨
    ((error6 a (fun i => -b i))^2 ≤ 512*readoutError a b ∧
      mass6 a b*error6 a (fun i => -b i) ≤ 32*readoutError a b ∧
      mass6 a b*weightedError a (fun i => -b i) ≤ 8*readoutError a b) := by
  by_cases hz : 0 ≤ ∑ i, a i^3*b i^3
  · exact Or.inl (oriented_bounds a b hz)
  · right
    have hn : 0 ≤ ∑ i, a i^3*(-b i)^3 := by
      have he : (∑ i, a i^3*(-b i)^3) = -(∑ i, a i^3*b i^3) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he]
      linarith
    have h := oriented_bounds a (fun i => -b i) hn
    have hm : mass6 a (fun i => -b i) = mass6 a b := by
      unfold mass6
      apply Finset.sum_congr rfl
      intro i _
      ring
    have he : readoutError a (fun i => -b i) = readoutError a b := by
      simp only [readoutError, neg_mul_neg]
    rw [hm, he] at h
    exact h

/-- Along one mode, coefficient distance has degree one and the observation
has degree six; this is the degeneration behind the global sixth-root exponent. -/
theorem one_mode_scaling (t : ℝ) :
    error6 (fun _ : Fin 1 => t) (fun _ => 0) = t^6 ∧
    readoutError (fun _ : Fin 1 => t) (fun _ => 0) = t^12 := by
  constructor
  · simp [error6]
  · simp [readoutError]
    ring

/-- A vanishing second coordinate leaves positive total mass while its sign
changes the observations only cubically. Both common-sign distances are explicit. -/
theorem two_mode_vanishing (t : ℝ) :
    error6 ![1,t] ![1,-t] = 64*t^6 ∧
    error6 ![1,t] (fun i => -(![1,-t] i)) = 64 ∧
    readoutError ![1,t] ![1,-t] = 8*t^6 ∧
    mass6 ![1,t] ![1,-t] = 2+2*t^6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [error6, readoutError, mass6, Fin.sum_univ_two] <;> ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CubedGram

namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Remove the factorial Fourier normalization from each actual prime-family readout. -/
def normalizedPrimeSixthReadout (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) : ℝ :=
  sixthPairReadout N (primeFamilyWeight N a) 1 p q / (N.factorial : ℝ)^6

theorem normalizedPrimeSixthReadout_eq (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) :
    normalizedPrimeSixthReadout N a p q = (a p*a q)^3 := by
  unfold normalizedPrimeSixthReadout
  rw [primeFamily_sixth_readout]
  exact mul_div_cancel_left₀ _ (by positivity)

/-- Squared noise in the normalized actual observation matrix. -/
def primeSixthNoise (N : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ p : oddPrimeModes N, ∑ q : oddPrimeModes N,
    (normalizedPrimeSixthReadout N a p q-normalizedPrimeSixthReadout N b p q)^2

/-- Unconditional noisy recovery for actual divisor-sieve signals, including
empty and unknown zero support. The same orientation satisfies all three bounds. -/
theorem primeFamily_sixth_stability (N : ℕ) (a b : ℕ → ℝ) :
    let a' := fun p : oddPrimeModes N => a p
    let b' := fun p : oddPrimeModes N => b p
    ((CubedGram.error6 a' b')^2 ≤ 512*primeSixthNoise N a b ∧
      CubedGram.mass6 a' b'*CubedGram.error6 a' b' ≤ 32*primeSixthNoise N a b ∧
      CubedGram.mass6 a' b'*CubedGram.weightedError a' b' ≤ 8*primeSixthNoise N a b) ∨
    ((CubedGram.error6 a' (fun p => -b' p))^2 ≤ 512*primeSixthNoise N a b ∧
      CubedGram.mass6 a' b'*CubedGram.error6 a' (fun p => -b' p) ≤ 32*primeSixthNoise N a b ∧
      CubedGram.mass6 a' b'*CubedGram.weightedError a' (fun p => -b' p) ≤ 8*primeSixthNoise N a b) := by
  simpa only [primeSixthNoise, normalizedPrimeSixthReadout_eq, CubedGram.readoutError]
    using CubedGram.stability (fun p : oddPrimeModes N => a p) (fun p : oddPrimeModes N => b p)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
