import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FourDivisibleEuclidean
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.CoordinateBoxLines

/-!
# Affine-line divisibility detects mixed moments

The Euclidean divisibility criterion turns affine-line counts into a bilinear
moment identity. If every nondegenerate affine line contains a multiple of
four indexed points, the two coordinate words are orthogonal. Repeated points
are allowed, so the result also covers nonnegative integer multiplicities.
For a nonidentity field twist, divisibility by the characteristic already
suffices to annihilate the corresponding twisted moment.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Codes

variable {K ι : Type*} [Field K] [Fintype ι]

/-- Affine linear combinations of two coordinate words. -/
def affineCoordinateCode (x y : ι → K) : Submodule K (ι → K) where
  carrier := {c | ∃ A B C : K, ∀ i, c i = A * x i + B * y i + C}
  zero_mem' := ⟨0, 0, 0, fun _ => by simp only [zero_mul, zero_add, Pi.zero_apply]⟩
  add_mem' := by
    rintro c d ⟨A, B, C, hc⟩ ⟨D, E, F, hd⟩
    refine ⟨A + D, B + E, C + F, fun i => ?_⟩
    change c i + d i = _
    rw [hc, hd]
    ring
  smul_mem' := by
    rintro a c ⟨A, B, C, hc⟩
    refine ⟨a * A, a * B, a * C, fun i => ?_⟩
    change a * c i = _
    rw [hc]
    ring

/-- Any common divisor of nondegenerate line-fiber counts divides the total point count. -/
theorem card_dvd_of_affineLine_counts [Fintype K] (Δ : ℕ) (x y : ι → K)
    (hline : ∀ A B C : K, A ≠ 0 ∨ B ≠ 0 →
      Δ ∣ (Finset.univ.filter (fun i => A * x i + B * y i = C)).card) :
    Δ ∣ Fintype.card ι := by
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset K))
    (f := x) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at hpart
  rw [hpart]
  apply Finset.dvd_sum
  intro a _
  simpa only [one_mul, zero_mul, add_zero] using hline 1 0 a (Or.inl one_ne_zero)

/-- The affine evaluation code inherits every common divisor of line-fiber counts. -/
theorem affineCoordinateCode_divisible [Fintype K] (Δ : ℕ) (x y : ι → K)
    (hline : ∀ A B C : K, A ≠ 0 ∨ B ≠ 0 →
      Δ ∣ (Finset.univ.filter (fun i => A * x i + B * y i = C)).card) :
    Divisible Δ (affineCoordinateCode x y) := by
  have hn := card_dvd_of_affineLine_counts Δ x y hline
  intro c hc
  obtain ⟨A, B, C, hc⟩ := hc
  by_cases hAB : A ≠ 0 ∨ B ≠ 0
  · have hz : Δ ∣ symbolCount c 0 := by
      have heq : symbolCount c 0 =
          (Finset.univ.filter (fun i => A * x i + B * y i = -C)).card := by
        unfold symbolCount
        congr 1
        apply Finset.filter_congr
        intro i _
        rw [hc, add_eq_zero_iff_eq_neg]
      rw [heq]
      exact hline A B (-C) hAB
    have hp := symbolCount_add_weight_sub c 0
    simp only [sub_zero] at hp
    exact (Nat.dvd_add_iff_right hz).mpr (by rwa [hp])
  · have hA : A = 0 := not_ne_iff.mp (not_or.mp hAB).1
    have hB : B = 0 := not_ne_iff.mp (not_or.mp hAB).2
    have hword : c = fun _ => C := by
      funext i
      simpa only [hA, hB, zero_mul, zero_add] using hc i
    rw [hword]
    by_cases hC : C = 0
    · simp only [hC, weight, ne_eq, not_true_eq_false, Finset.filter_false,
        Finset.card_empty, dvd_zero]
    · simpa only [weight, hC, ne_eq, not_false_eq_true, Finset.filter_true,
        Finset.card_univ] using hn

/-- Four-divisible affine-line counts annihilate the mixed coordinate moment in characteristic two. -/
theorem mixedMoment_eq_zero_of_affineLine_counts [Fintype K] [CharP K 2] (x y : ι → K)
    (hline : ∀ A B C : K, A ≠ 0 ∨ B ≠ 0 →
      4 ∣ (Finset.univ.filter (fun i => A * x i + B * y i = C)).card) :
    ∑ i, x i * y i = 0 := by
  have horth := fourDivisible_selfOrthogonal (affineCoordinateCode x y)
    (show (fun _ => (1 : K)) ∈ affineCoordinateCode x y from
      ⟨0, 0, 1, fun _ => by simp only [zero_mul, zero_add]⟩)
    (affineCoordinateCode_divisible 4 x y hline)
  exact horth x ⟨1, 0, 0, fun _ => by simp only [one_mul, zero_mul, add_zero]⟩
    y ⟨0, 1, 0, fun _ => by simp only [zero_mul, one_mul, zero_add, add_zero]⟩

/-- For a nonidentity twist, characteristic-divisible line counts annihilate the twisted moment. -/
theorem twistedMoment_eq_zero_of_affineLine_counts [Fintype K]
    (p : ℕ) [CharP K p] (σ : K →+* K) (hσ : σ ≠ RingHom.id K) (x y : ι → K)
    (hline : ∀ A B C : K, A ≠ 0 ∨ B ≠ 0 →
      p ∣ (Finset.univ.filter (fun i => A * x i + B * y i = C)).card) :
    ∑ i, x i * σ (y i) = 0 := by
  have horth := divisible_selfOrthogonal p σ hσ (affineCoordinateCode x y)
    (show (fun _ => (1 : K)) ∈ affineCoordinateCode x y from
      ⟨0, 0, 1, fun _ => by simp only [zero_mul, zero_add]⟩)
    (affineCoordinateCode_divisible p x y hline)
  exact horth x ⟨1, 0, 0, fun _ => by simp only [one_mul, zero_mul, add_zero]⟩
    y ⟨0, 1, 0, fun _ => by simp only [zero_mul, one_mul, zero_add, add_zero]⟩

/-- A nonzero twisted moment detects a line whose occupancy survives modulo the characteristic. -/
theorem exists_affineLine_count_not_dvd_of_twistedMoment [Fintype K]
    (p : ℕ) [CharP K p] (σ : K →+* K) (hσ : σ ≠ RingHom.id K) (x y : ι → K)
    (h : ∑ i, x i * σ (y i) ≠ 0) :
    ∃ A B C : K, (A ≠ 0 ∨ B ≠ 0) ∧
      ¬p ∣ (Finset.univ.filter (fun i => A * x i + B * y i = C)).card := by
  by_contra! hline
  exact h (twistedMoment_eq_zero_of_affineLine_counts p σ hσ x y hline)

/-- A nonzero mixed moment forces a nondegenerate affine line with count nonzero modulo four. -/
theorem exists_affineLine_count_not_dvd_four [Fintype K] [CharP K 2] (x y : ι → K)
    (h : ∑ i, x i * y i ≠ 0) :
    ∃ A B C : K, (A ≠ 0 ∨ B ≠ 0) ∧
      ¬4 ∣ (Finset.univ.filter (fun i => A * x i + B * y i = C)).card := by
  by_contra! hline
  exact h (mixedMoment_eq_zero_of_affineLine_counts x y hline)

/-- A finite point set with nonzero mixed moment has a line occupancy nonzero modulo four. -/
theorem exists_affineLine_set_count_not_dvd_four [Fintype K] [CharP K 2]
    (S : Finset (K × K)) (h : ∑ z ∈ S, z.1 * z.2 ≠ 0) :
    ∃ A B C : K, (A ≠ 0 ∨ B ≠ 0) ∧
      ¬4 ∣ (S.filter (fun z => A * z.1 + B * z.2 = C)).card := by
  have hsum : ∑ z : S, z.val.1 * z.val.2 ≠ 0 := by
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun z => z.1 * z.2)]
    exact h
  obtain ⟨A, B, C, hAB, hc⟩ := exists_affineLine_count_not_dvd_four
    (fun z : S => z.val.1) (fun z : S => z.val.2) hsum
  refine ⟨A, B, C, hAB, ?_⟩
  have hcard : (Finset.univ.filter (fun z : S => A * z.val.1 + B * z.val.2 = C)).card =
      (S.filter (fun z => A * z.1 + B * z.2 = C)).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact (Finset.sum_subtype S (fun _ => Iff.rfl)
      (fun z => if A * z.1 + B * z.2 = C then (1 : ℕ) else 0)).symm
  rwa [hcard] at hc

/-- A coordinate box whose coordinate sums have nonzero product cannot have every line
occupancy divisible by four. -/
theorem coordinateBoxLine_exists_count_not_dvd_four [Fintype K] [CharP K 2]
    (I J : Finset K) (h : (∑ x ∈ I, x) * (∑ y ∈ J, y) ≠ 0) :
    ∃ A B C : K, (A ≠ 0 ∨ B ≠ 0) ∧ ¬4 ∣ (coordinateBoxLine I J A B C).card := by
  apply exists_affineLine_set_count_not_dvd_four (I ×ˢ J)
  rw [Finset.sum_product, ← Finset.sum_mul_sum]
  exact h

#print axioms mixedMoment_eq_zero_of_affineLine_counts
#print axioms exists_affineLine_count_not_dvd_four
#print axioms coordinateBoxLine_exists_count_not_dvd_four
#print axioms twistedMoment_eq_zero_of_affineLine_counts
#print axioms exists_affineLine_count_not_dvd_of_twistedMoment

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
