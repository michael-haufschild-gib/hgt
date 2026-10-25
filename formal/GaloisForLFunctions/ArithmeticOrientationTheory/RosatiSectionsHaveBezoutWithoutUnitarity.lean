import GaloisForLFunctions.ArithmeticOrientationTheory.SourceSectionBoundaryRigidity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LambdaRingEffectivityAndHeckeLefschetzRigidity

/-!
# Rosati source Bézout needs no unitarity

The mixed Frobenius defect is the pairing of an evaluation vector with a permutation of the
second vector. Finite Cauchy–Schwarz therefore proves Bézout and ampleness for every Rosati
source cone, including fake curve data. Riemann–Roch is the additional condition that the
reflection defect vanish. This separates the positive mass construction from purity.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The mixed Toeplitz form is a reflected Frobenius evaluation pairing on every curve datum. -/
theorem mixedToeplitz_eq_reflectedFrobenius (S : Finset ℕ) (e d : ℕ → ℝ) :
    (∑ k ∈ S, ∑ l ∈ S, e k * d l * D.trace (Nat.dist k l)) =
      ∑ i : ι, (conj (GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S e (D.β i)) *
        GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S d (D.β (D.reflPerm i))).re := by
  have hconj (i : ι) : D.β (D.conjPerm.symm i) = conj (D.β i) := by
    have h := D.β_conjPerm (D.conjPerm.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Complex.conj_conj]
  have hdist (k l : ℕ) : D.trace (Nat.dist k l) =
      ∑ i : ι, (conj (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re := by
    rw [trace, powerSum_dist,
      ← Equiv.sum_comp D.conjPerm.symm (fun i => D.β i ^ k * D.β (D.fePerm i) ^ l),
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hconj]
    rfl
  simp only [hdist, GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly, map_sum, map_mul, map_pow, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  calc
    (∑ k ∈ S, ∑ l ∈ S, ∑ i : ι,
        e k * d l * (conj (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re)
        = ∑ l ∈ S, ∑ k ∈ S, ∑ i : ι,
          e k * d l * (conj (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re := Finset.sum_comm
    _ = ∑ l ∈ S, ∑ i : ι, ∑ k ∈ S,
        e k * d l * (conj (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i : ι, ∑ l ∈ S, ∑ k ∈ S,
        e k * d l * (conj (D.β i) ^ k * D.β (D.reflPerm i) ^ l).re := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun k _ => ?_
      have he : (e k : ℂ) * conj (D.β i) ^ k * ((d l : ℂ) * D.β (D.reflPerm i) ^ l) =
          ((e k * d l : ℝ) : ℂ) * (conj (D.β i) ^ k * D.β (D.reflPerm i) ^ l) := by
        push_cast
        ring
      rw [he, Complex.re_ofReal_mul]

/-- The entire mixed surface defect has the same reflected finite evaluation formula. -/
theorem windowSurface_defect_eq_reflectedFrobenius (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface S).defect x y =
      ∑ i : ι, (conj (GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S (fun k => x.2.2 k * D.sqrtq ^ k) (D.β i)) *
        GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S (fun k => y.2.2 k * D.sqrtq ^ k) (D.β (D.reflPerm i))).re := by
  rw [← D.mixedToeplitz_eq_reflectedFrobenius S
    (fun k => x.2.2 k * D.sqrtq ^ k) (fun k => y.2.2 k * D.sqrtq ^ k)]
  have hδ : (D.windowSurface S).defect x y =
      D.windowA S x.2.2 * windowB S y.2.2 + windowB S x.2.2 * D.windowA S y.2.2 -
        D.windowGraph S x.2.2 y.2.2 := by
    rw [PolarSurface.defect, PolarSurface.polar,
      D.windowSurface_pair_H, D.windowSurface_pair_V,
      D.windowSurface_pair_H, D.windowSurface_pair_V]
    change _ - D.windowPairFun S x y = _
    unfold windowPairFun
    ring
  have hpol : D.windowA S x.2.2 * windowB S y.2.2 +
      windowB S x.2.2 * D.windowA S y.2.2 =
      ∑ k ∈ S, ∑ l ∈ S, x.2.2 k * y.2.2 l * (D.q ^ k + D.q ^ l) := by
    simp only [windowA, windowB, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hδ, hpol, windowGraph, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_sub, D.graphPair_entry]
  ring

private theorem finite_complex_cauchy (v w : ι → ℂ) :
    (∑ i, (conj (v i) * w i).re) ^ 2 ≤
      (∑ i, ‖v i‖ ^ 2) * ∑ i, ‖w i‖ ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => sq_nonneg ‖v i‖) (fun i _ => sq_nonneg ‖w i‖)
  intro i _
  have h := Complex.abs_re_le_norm (conj (v i) * w i)
  rw [norm_mul, Complex.norm_conj] at h
  have hn := mul_nonneg (norm_nonneg (v i)) (norm_nonneg (w i))
  have hh := mul_nonneg (sub_nonneg.mpr h)
    (add_nonneg hn (abs_nonneg (conj (v i) * w i).re))
  have hs : (conj (v i) * w i).re ^ 2 ≤ (‖v i‖ * ‖w i‖) ^ 2 := by
    nlinarith only [hh, sq_abs (conj (v i) * w i).re]
  simpa only [mul_pow] using hs

/-- Rosati masses bound the mixed defect without a purity or Hodge-index premise. -/
theorem windowSurface_defect_sq_le_rosatiSourceEnergy (S : Finset ℕ) (x y : SpanCycle) :
    (D.windowSurface S).defect x y ^ 2 ≤ D.rosatiSourceEnergy S x * D.rosatiSourceEnergy S y := by
  rw [D.windowSurface_defect_eq_reflectedFrobenius]
  have h := finite_complex_cauchy
    (fun i => GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S (fun k => x.2.2 k * D.sqrtq ^ k) (D.β i))
    (fun i => GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S (fun k => y.2.2 k * D.sqrtq ^ k) (D.β (D.reflPerm i)))
  rw [Equiv.sum_comp D.reflPerm
    (fun i => ‖GaloisForLFunctions.ArithmeticCastelnuovoSeveri.frobPoly S (fun k => y.2.2 k * D.sqrtq ^ k) (D.β i)‖ ^ 2)] at h
  exact h

private theorem rosatiSourceEnergy_fibre_invariant (S : Finset ℕ) (x : SpanCycle) (a b : ℝ) :
    D.rosatiSourceEnergy S (x + a • (D.windowSurface S).H + b • (D.windowSurface S).V) =
      D.rosatiSourceEnergy S x := by
  have hf : (x + a • (D.windowSurface S).H + b • (D.windowSurface S).V).2.2 = x.2.2 := by
    funext k
    change x.2.2 k + a * 0 + b * 0 = x.2.2 k
    ring
  simp only [rosatiSourceEnergy, hf]

/-- Every Rosati source cone has Bézout, including nonunitary curve data. -/
theorem rosatiSourceCone_bezout (S : Finset ℕ) :
    (D.windowSurface S).BezoutAxiom (D.rosatiSourceCone S) := by
  exact ((D.windowSurface S).sourceCone_bezout_iff_defect_sq_le
    (D.rosatiSourceEnergy_nonneg S) (D.rosatiSourceEnergy_neg S)
    (rosatiSourceEnergy_fibre_invariant D S)).mpr
      (D.windowSurface_defect_sq_le_rosatiSourceEnergy S)

/-- Zero Rosati mass annihilates every mixed defect, so ampleness also holds without unitarity. -/
theorem rosatiSourceCone_ample (S : Finset ℕ) :
    (D.windowSurface S).AmpleAxiom (D.rosatiSourceCone S) := by
  apply ((D.windowSurface S).sourceCone_ample_iff_defect_radical
    (rosatiSourceEnergy_fibre_invariant D S)).mpr
  intro x hx y
  have hzero := le_antisymm hx (D.rosatiSourceEnergy_nonneg S x)
  have hb := D.windowSurface_defect_sq_le_rosatiSourceEnergy S x y
  rw [hzero, zero_mul] at hb
  nlinarith only [hb, sq_nonneg ((D.windowSurface S).defect x y)]

/-- At each window, RR is exactly the vanishing of the remaining reflection defect. -/
theorem rosatiSourceCone_riemannRoch_iff_reflection_zero (S : Finset ℕ) :
    (D.windowSurface S).RiemannRochAxiom (D.rosatiSourceCone S) ↔
      ∀ x : SpanCycle, D.frobReflectionDefect S (fun k => x.2.2 k * D.sqrtq ^ k) = 0 := by
  rw [rosatiSourceCone, (D.windowSurface S).sourceCone_riemannRoch_iff_le_defect_without_symmetry
    (D.rosatiSourceEnergy_nonneg S) (rosatiSourceEnergy_fibre_invariant D S)]
  apply forall_congr'
  intro x
  rw [D.windowSurface_defect_eq_frobSquareMass_sub_frobReflectionDefect, rosatiSourceEnergy]
  have hn := D.frobReflectionDefect_nonneg S (fun k => x.2.2 k * D.sqrtq ^ k)
  constructor <;> intro h <;> linarith only [h, hn]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum

namespace GaloisForLFunctions.ArithmeticOrientationTheory

variable {ι : Type*} [Fintype ι]

/-- The matrix-section reading is the same unconditional Rosati source cone. -/
theorem frobMassSectionCone_eq_rosatiSourceCone (D : CurveDatum ι) (S : Finset ℕ) :
    frobMassSectionCone D S = D.rosatiSourceCone S := by
  rw [frobMassSectionCone, sourceSectionCone_eq_sourceCone, CurveDatum.rosatiSourceCone]
  congr 1
  funext x
  exact frobeniusMass_frobEvalMatrix_eq_frobSquareMass D S x

/-- Frobenius evaluation sections have Bézout and ampleness for every curve datum. -/
theorem frobMassSectionCone_bezout_and_ample (D : CurveDatum ι) (S : Finset ℕ) :
    (D.windowSurface S).BezoutAxiom (frobMassSectionCone D S) ∧
      (D.windowSurface S).AmpleAxiom (frobMassSectionCone D S) := by
  rw [frobMassSectionCone_eq_rosatiSourceCone]
  exact ⟨D.rosatiSourceCone_bezout S, D.rosatiSourceCone_ample S⟩

/-- The golden calibration satisfies both positivity axioms while failing RR. -/
theorem goldenDatum_frobMass_bezout_ample_not_riemannRoch :
    (goldenDatum.windowSurface {1}).BezoutAxiom (frobMassSectionCone goldenDatum {1}) ∧
      (goldenDatum.windowSurface {1}).AmpleAxiom (frobMassSectionCone goldenDatum {1}) ∧
      ¬ (goldenDatum.windowSurface {1}).RiemannRochAxiom (frobMassSectionCone goldenDatum {1}) := by
  rw [frobMassSectionCone_eq_rosatiSourceCone]
  exact ⟨goldenDatum.rosatiSourceCone_bezout _, goldenDatum.rosatiSourceCone_ample _,
    goldenDatum_not_rosatiSourceCone_riemannRoch⟩

end GaloisForLFunctions.ArithmeticOrientationTheory
