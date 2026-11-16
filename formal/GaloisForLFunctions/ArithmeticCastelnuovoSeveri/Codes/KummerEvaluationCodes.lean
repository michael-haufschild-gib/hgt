import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalZeroBound
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.DivisibleSymbolOrthogonality

/-!
# One-point evaluation codes on Kummer normalizations

Evaluating actual bounded-pole functions at distinct rational affine
points gives linear codes. The rational zero bound proves the designed
distance and injectivity below the code length. The explicit one-point
Riemann–Roch formula then supplies their dimensions.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) R
local notation "A" => SquareKummerNormalization p s c (p ^ (d + 1) - 2) R
local notation "g" => Module.finrank K (globalRegularDifferentials K L)
variable {ι : Type*} [Fintype ι]

/-- The linear code obtained by evaluating the actual one-point pole space. -/
def squareKummerEvaluationCode (m : ℕ) (φ : ι → A →ₐ[K] K) : Submodule K (ι → K) :=
  (squareKummerPoleEvaluation p s c d r m φ).range

/-- Below the evaluation length, the code retains the entire bounded-pole dimension. -/
theorem squareKummerEvaluationCode_finrank (m : ℕ)
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) (hm : m < Fintype.card ι) :
    Module.finrank K (squareKummerEvaluationCode p s c d r m φ) =
      Module.finrank K (squareKummerPoleSpace p s c d r m) :=
  LinearMap.finrank_range_of_inj (squareKummerPoleEvaluation_injective p s c d r φ hφ m hm)

/-- The character cutoffs give the exact code dimension, including the range before Riemann–Roch becomes linear. -/
theorem squareKummerEvaluationCode_finrank_cutoffs (m : ℕ)
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) (hm : m < Fintype.card ι) :
    Module.finrank K (squareKummerEvaluationCode p s c d r m φ) =
      ∑ i : Fin (p ^ (s + 1) + 1), kummerPoleCutoff p s d r m i.val := by
  rw [squareKummerEvaluationCode_finrank p s c d r m φ hφ hm,
    squareKummer_poleSpace_finrank]

/-- From pole allowance `2g-1` onward, the code dimension satisfies Riemann–Roch. -/
theorem squareKummerEvaluationCode_riemannRoch (m : ℕ)
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ)
    (hm : m < Fintype.card ι) (hg : 2 * g ≤ m + 1) :
    Module.finrank K (squareKummerEvaluationCode p s c d r m φ) + g = m + 1 := by
  rw [squareKummerEvaluationCode_finrank p s c d r m φ hφ hm]
  exact squareKummer_poleSpace_riemannRoch p s c d r m hg

/-- The code family with pole allowance `2g+a` has explicit dimension `g+a+1` throughout its injective range. -/
theorem squareKummerEvaluationCode_finrank_tail
    (a : Fin (Fintype.card ι - 2 * g)) (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) :
    Module.finrank K (squareKummerEvaluationCode p s c d r (2 * g + a.val) φ) = g + a.val + 1 := by
  have hm : 2 * g + a.val < Fintype.card ι := by
    have ha := a.isLt
    omega
  rw [squareKummerEvaluationCode_finrank p s c d r _ φ hφ hm]
  exact squareKummer_poleSpace_twice_genus_add_finrank p s c d r a.val

/-- Every nonzero evaluation word has Hamming weight at least the length minus the allowed pole order. -/
theorem squareKummerEvaluationCode_weight_bound (m : ℕ)
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) :
    ∀ w ∈ squareKummerEvaluationCode p s c d r m φ,
      w ≠ 0 → Fintype.card ι - m ≤ Codes.weight w := by
  classical
  rintro w ⟨f, rfl⟩ hw
  have hf : f.val ≠ 0 := by
    intro hz
    have hfzero : f = 0 := Subtype.ext hz
    apply hw
    rw [hfzero, map_zero]
  let Z := {i : ι // squareKummerPoleEvaluation p s c d r m φ f i = 0}
  let ψ : Z → A →ₐ[K] K := fun i => φ i.val
  have hψ : Function.Injective ψ := fun x y h => Subtype.ext (hφ h)
  have hzeros := squareKummer_rational_zeros_le_pole_bound p s c d r ψ hψ m f hf
    (fun i => i.property)
  have hcount : Codes.symbolCount (squareKummerPoleEvaluation p s c d r m φ f) 0 ≤ m := by
    simpa only [Z, Fintype.card_subtype, Codes.symbolCount] using hzeros
  have hpartition := Codes.symbolCount_add_weight_sub
    (squareKummerPoleEvaluation p s c d r m φ f) 0
  simp only [sub_zero] at hpartition
  change Codes.symbolCount (squareKummerPoleEvaluation p s c d r m φ f) 0 +
    Codes.weight (squareKummerPoleEvaluation p s c d r m φ f) = Fintype.card ι at hpartition
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
