import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros
import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfDegreeKappaHasAtMostKappaExceptionalPoints
import GaloisForLFunctions.InfiniteRankPurityTheory.TheExceptionalParameterIsBornAtFourPiExpMinusGamma

/-!
# The index of the pairing is at most the defect of a splitting

The pairing of a zero configuration is `2 d₁ d₂ − Z(f)`, with `Z` Weil's form on the zeros. Its
index is one plus the number of negative squares of `Z`, and these are the zeros right of the
line. The index law bounds the zeros right of the line of a Hermite–Biehler sum by the degree of
its defect. This file joins the two.

* **The index by a set of exceptional points** (`hermNegIndex_zeroGram_le_of_rightZeros_subset`):
  if the zeros right of the line of a tempered configuration lie in a set of at most `κ` points,
  Weil's form has at most `κ` negative squares on every finite family of packets.
* **The defect of a splitting bounds the index** (`hermNegIndex_zeroGram_le_of_hermiteBiehler`,
  `hermNegIndex_zeroGram_zeta_le_of_hermiteBiehler`): if these zeros are zeros of a sum
  `P_W E − c P_{W♯} E'` with `|E'| ≤ |E|` right of the line and a defect `W` of `κ` points, the
  number of negative squares is at most `κ`. For the zeros of `ζ`: a splitting of `ξ` with a
  defect of degree `κ` bounds the index of the pairing of the degree points by `1 + κ`.
* **The line law of Lagarias and Suzuki is an index-one statement**
  (`hermNegIndex_zeroGram_le_one_of_constantTerm`,
  `hermNegIndex_zeroGram_eq_zero_of_constantTerm`): a tempered configuration carried by the zeros
  of the constant term `Λ(2s)Y^s + Λ(2s − 1)Y^{1−s}`, cleared of its poles, has at most one
  negative square for `Y ≥ 1`, and none for `1 ≤ Y ≤ 4π e^{−γ}`. Above the threshold the pairing
  has one positive square besides the pole plane: the real exceptional pair is a second pole
  plane.
-/

open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open ArithmeticCastelnuovoSeveri InfiniteRankPurityTheory

variable {ι : Type*} [Fintype ι]

/-- **The index by a set of exceptional points.** If the zeros right of the line of a tempered
configuration lie in a set of at most `κ` points, Weil's form has at most `κ` negative squares on
every finite family of packets. -/
theorem hermNegIndex_zeroGram_le_of_rightZeros_subset (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {A : Set ℂ} (hA : rightZeros Z ⊆ A) {κ : ℕ} (hκ : A.encard ≤ κ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (zeroGram Z f) ≤ κ := by
  have h := negIndex_zeroGram_le_of_tempered Z hZ f hf hfc
  exact_mod_cast h.trans ((Set.encard_le_encard hA).trans hκ)

/-- **The defect of a splitting bounds the index.** Let the zeros right of the line of a tempered
configuration be zeros of `P_W E − c P_{W♯} E'`, with `E`, `E'` holomorphic right of the line,
`E ≠ 0`, `|E'| ≤ |E|`, `|c| = 1` and `W` a divisor of `κ` points right of the line. Then Weil's
form has at most `κ` negative squares on every finite family of packets. -/
theorem hermNegIndex_zeroGram_le_of_hermiteBiehler (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {E E' : ℂ → ℂ} {c : ℂ} (hE : DifferentiableOn ℂ E rightHalf)
    (hE' : DifferentiableOn ℂ E' rightHalf) (hne : ∀ s ∈ rightHalf, E s ≠ 0)
    (hle : ∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) (hc : ‖c‖ = 1) (W : Multiset ℂ)
    (hW : ∀ w ∈ W, w ∈ rightHalf)
    (hdiff : ∃ z ∈ rightHalf,
      divisorPoly W z * E z - c * divisorPoly (reflectDivisor W) z * E' z ≠ 0)
    (hcar : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re →
      divisorPoly W ρ * E ρ - c * divisorPoly (reflectDivisor W) ρ * E' ρ = 0)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (zeroGram Z f) ≤ Multiset.card W :=
  hermNegIndex_zeroGram_le_of_rightZeros_subset Z hZ
    (A := {s | s ∈ rightHalf ∧
      divisorPoly W s * E s - c * divisorPoly (reflectDivisor W) s * E' s = 0})
    (fun ρ hρ => ⟨hρ.2, hcar ρ hρ.1 hρ.2⟩)
    (hermiteBiehler_index hE hE' hne hle hc W hW hdiff) f hf hfc

/-- **A splitting of `ξ` with a defect of degree `κ` bounds the index of the pairing of the
degree points.** If every zero of `ζ` right of the line is a zero of `P_W E − c P_{W♯} E'` as
above, Weil's form of the zeros of `ζ` has at most `κ` negative squares on every finite family
of packets. -/
theorem hermNegIndex_zeroGram_zeta_le_of_hermiteBiehler {E E' : ℂ → ℂ} {c : ℂ}
    (hE : DifferentiableOn ℂ E rightHalf) (hE' : DifferentiableOn ℂ E' rightHalf)
    (hne : ∀ s ∈ rightHalf, E s ≠ 0) (hle : ∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖) (hc : ‖c‖ = 1)
    (W : Multiset ℂ) (hW : ∀ w ∈ W, w ∈ rightHalf)
    (hdiff : ∃ z ∈ rightHalf,
      divisorPoly W z * E z - c * divisorPoly (reflectDivisor W) z * E' z ≠ 0)
    (hcar : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re →
      divisorPoly W ρ * E ρ - c * divisorPoly (reflectDivisor W) ρ * E' ρ = 0)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (zeroGram zetaZeroConfig f) ≤ Multiset.card W :=
  hermNegIndex_zeroGram_le_of_hermiteBiehler zetaZeroConfig temperedConfig_zetaZeroConfig hE hE'
    hne hle hc W hW hdiff hcar f hf hfc

/-- **The line law is an index-one statement.** For `Y ≥ 1`, a tempered configuration carried by
the zeros of the cleared constant term has at most one negative square of Weil's form. -/
theorem hermNegIndex_zeroGram_le_one_of_constantTerm {Y : ℝ} (hY : 1 ≤ Y) (Z : ZeroConfig)
    (hZ : TemperedConfig Z) (hcar : ∀ ρ ∈ Z.carrier, constantTerm Y ρ = 0) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (zeroGram Z f) ≤ 1 :=
  hermNegIndex_zeroGram_le_of_rightZeros_subset Z hZ
    (A := {s | s ∈ rightHalf ∧ constantTerm Y s = 0})
    (fun ρ hρ => ⟨hρ.2, hcar ρ hρ.1⟩)
    (by
      rw [Nat.cast_one]
      exact Set.encard_le_one_iff_subsingleton.mpr (constantTerm_zero_subsingleton hY))
    f hf hfc

/-- **Up to the threshold the index is zero.** For `1 ≤ Y ≤ 4π e^{−γ}`, a tempered configuration
carried by the zeros of the cleared constant term has no negative square of Weil's form. -/
theorem hermNegIndex_zeroGram_eq_zero_of_constantTerm {Y : ℝ} (hY1 : 1 ≤ Y)
    (hY : Y ≤ 4 * Real.pi * Real.exp (-Real.eulerMascheroniConstant)) (Z : ZeroConfig)
    (hZ : TemperedConfig Z) (hcar : ∀ ρ ∈ Z.carrier, constantTerm Y ρ = 0) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    hermNegIndex (zeroGram Z f) = 0 := by
  have hempty : rightZeros Z ⊆ (∅ : Set ℂ) := fun ρ hρ =>
    absurd ((exists_exceptionalParameter_iff hY1).mp ⟨ρ, hρ.2, hcar ρ hρ.1⟩) (not_lt.mpr hY)
  exact Nat.le_zero.mp (hermNegIndex_zeroGram_le_of_rightZeros_subset Z hZ hempty
    (by simp) f hf hfc)

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
