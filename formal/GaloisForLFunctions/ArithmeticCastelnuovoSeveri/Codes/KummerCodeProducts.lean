import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Codes.NormalizedKummerEvaluationCodes

/-!
# Multiplicative filtration of Kummer evaluation codes

Increasing a pole allowance enlarges the code. Coordinatewise products
add pole allowances, since evaluation respects multiplication in the
normalization. Interpolation makes the filtration eventually equal to
the full coordinate space.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "A" => SquareKummerNormalization p s c (p ^ (d + 1) - 2)
  (kummerExponent (p ^ (d + 1)) r)
variable {ι : Type*}

/-- The code spaces form an increasing filtration by allowed pole order. -/
theorem squareKummerEvaluationCode_mono (φ : ι → A →ₐ[K] K) :
    Monotone (fun m => squareKummerEvaluationCode p s c d r m φ) := by
  intro m n hmn w hw
  rcases hw with ⟨f, rfl⟩
  exact ⟨⟨f.val, squareKummerPoleSpace_mono p s c d r hmn f.property⟩, rfl⟩

/-- A coordinatewise product belongs to the code with the sum of the pole allowances. -/
theorem squareKummerEvaluationCode_mul_mem (φ : ι → A →ₐ[K] K) (m n : ℕ)
    {u w : ι → K} (hu : u ∈ squareKummerEvaluationCode p s c d r m φ)
    (hw : w ∈ squareKummerEvaluationCode p s c d r n φ) :
    u * w ∈ squareKummerEvaluationCode p s c d r (m + n) φ := by
  rcases hu with ⟨f, rfl⟩
  rcases hw with ⟨h, rfl⟩
  refine ⟨squareKummerPoleMultiplication p s c d r m n f h, ?_⟩
  ext i
  change φ i ((squareKummerPoleNormalizationMap p s c d r m f) *
    (squareKummerPoleNormalizationMap p s c d r n h)) =
      φ i (squareKummerPoleNormalizationMap p s c d r m f) *
        φ i (squareKummerPoleNormalizationMap p s c d r n h)
  exact map_mul _ _ _

/-- Distinct finite evaluation coordinates are eventually interpolated without restriction. -/
theorem squareKummerEvaluationCode_eventually_top [Fintype ι]
    (φ : ι → A →ₐ[K] K) (hφ : Function.Injective φ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → squareKummerEvaluationCode p s c d r m φ = ⊤ := by
  obtain ⟨M, hM⟩ := squareKummerPoleEvaluation_eventually_surjective p s c d r φ hφ
  exact ⟨M, fun m hm => LinearMap.range_eq_top.mpr (hM m hm)⟩

variable (n : ℕ)

/-- The maximal Kummer code family is an increasing filtration. -/
theorem normalizedKummerEvaluationCode_mono :
    Monotone (normalizedKummerEvaluationCode p d n r) :=
  squareKummerEvaluationCode_mono p (kummerSquareIndex d n) _ d (r + 1) id

/-- Products of words in the maximal Kummer family add their pole allowances. -/
theorem normalizedKummerEvaluationCode_mul_mem (a b : ℕ)
    {u w : NormalizedKummerAlgebraPoints p d n r → SquareConstantField p (kummerSquareIndex d n)}
    (hu : u ∈ normalizedKummerEvaluationCode p d n r a)
    (hw : w ∈ normalizedKummerEvaluationCode p d n r b) :
    u * w ∈ normalizedKummerEvaluationCode p d n r (a + b) :=
  squareKummerEvaluationCode_mul_mem p (kummerSquareIndex d n) _ d (r + 1) id a b hu hw

/-- Every maximal Kummer code family eventually fills its full finite coordinate space. -/
theorem normalizedKummerEvaluationCode_eventually_top :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → normalizedKummerEvaluationCode p d n r m = ⊤ := by
  letI : Fintype (NormalizedKummerAlgebraPoints p d n r) := Fintype.ofFinite _
  exact squareKummerEvaluationCode_eventually_top p (kummerSquareIndex d n) _ d (r + 1)
    id Function.injective_id

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
