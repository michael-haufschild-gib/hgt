import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPoleEvaluation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOnePointRiemannRoch
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rational zeros are bounded by the infinity pole order

Interpolate at the zeros inside a large one-point pole space. Multiples
of the vanishing function form an injective image of a smaller pole
space inside the evaluation kernel. The one-point Riemann–Roch formula
and rank-nullity bound the number of zeros by the allowed pole order.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) R
local notation "A" => SquareKummerNormalization p s c (p ^ (d + 1) - 2) R
local notation "P" => squareKummerPoleSpace p s c d r
local notation "g" => Module.finrank K (globalRegularDifferentials K L)
variable {ι : Type*} [Fintype ι]

/-- A nonzero function with sole pole of order at most `m` vanishes at at most `m` distinct rational affine points. -/
theorem squareKummer_rational_zeros_le_pole_bound
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ)
    (m : ℕ) (f : P m) (hf : f.val ≠ 0)
    (hzero : ∀ i, φ i (squareKummerPoleNormalizationMap p s c d r m f) = 0) :
    Fintype.card ι ≤ m := by
  obtain ⟨M, hM⟩ := squareKummerPoleEvaluation_eventually_surjective p s c d r φ hφ
  let n := 2 * g + M
  let E := squareKummerPoleEvaluation p s c d r (m + n) φ
  have hsurj : Function.Surjective E := hM (m + n) (by dsimp only [n]; omega)
  let F := squareKummerPoleMultiplication p s c d r m n f
  let H : P n →ₗ[K] LinearMap.ker E := F.codRestrict _ (fun x => by
    change E (F x) = 0
    exact squareKummerPoleMultiplication_evaluation_zero p s c d r m n f φ hzero x)
  have hH : Function.Injective H := by
    intro x y h
    exact squareKummerPoleMultiplication_injective p s c d r m n f hf
      (congrArg Subtype.val h)
  have hle := LinearMap.finrank_le_finrank_of_injective hH
  have hnull := LinearMap.finrank_range_add_finrank_ker E
  have hcod : Module.finrank K (LinearMap.range E) = Fintype.card ι := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi]
  have hsmall : Module.finrank K (P n) = g + M + 1 :=
    squareKummer_poleSpace_twice_genus_add_finrank p s c d r M
  have hlarge : Module.finrank K (P (m + n)) = g + (M + m) + 1 := by
    rw [show m + n = 2 * g + (M + m) by dsimp only [n]; omega]
    exact squareKummer_poleSpace_twice_genus_add_finrank p s c d r (M + m)
  rw [hcod, hlarge] at hnull
  rw [hsmall] at hle
  omega

/-- Evaluating at more distinct rational points than the allowed pole order loses no function. -/
theorem squareKummerPoleEvaluation_injective
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) (m : ℕ)
    (hm : m < Fintype.card ι) :
    Function.Injective (squareKummerPoleEvaluation p s c d r m φ) := by
  intro x y hE
  by_contra hne
  have hxy : (x - y : P m).val ≠ 0 := by
    intro h
    have heq : x - y = (0 : P m) := Subtype.ext h
    exact hne (sub_eq_zero.mp heq)
  have hz : squareKummerPoleEvaluation p s c d r m φ (x - y) = 0 := by
    rw [map_sub, hE, sub_self]
  have hbound := squareKummer_rational_zeros_le_pole_bound p s c d r φ hφ m (x - y) hxy
    (fun i => congrFun hz i)
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
