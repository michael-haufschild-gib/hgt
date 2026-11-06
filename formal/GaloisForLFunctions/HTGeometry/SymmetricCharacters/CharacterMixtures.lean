import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CyclicTrace
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.MixtureRigidity

/-!
# Positive character mixtures and exact disjoint-cycle rigidity

A finite positive mixture of independent-color characters remains positive definite and
restriction compatible. Multiplicativity on two equal disjoint cycles is more rigid: it holds
at every cycle length exactly when the probability alphabets agree throughout positive support.
-/

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace GaloisForLFunctions.SymmetricCharacters

variable {I A X J : Type*} [Fintype I] [Fintype A] [Fintype X]

/-- A finite mixture with fixed latent weights, used unchanged at every rank. -/
def mixedCharacter (ν : I → NNReal) (w : I → A → NNReal) (σ : Equiv.Perm X) : ℝ :=
  ∑ i, (ν i : ℝ) * probabilityCharacter (w i) σ

theorem mixedCharacter_one (ν : I → NNReal) (w : I → A → NNReal) :
    mixedCharacter (X := X) ν w 1 = ∑ i, (ν i : ℝ) := by
  simp only [mixedCharacter, probabilityCharacter_one, mul_one]

theorem mixedCharacter_restrict (ν : I → NNReal) (w : I → A → NNReal)
    (σ : Equiv.Perm X) :
    mixedCharacter ν w (Equiv.optionCongr σ) = mixedCharacter ν w σ := by
  simp only [mixedCharacter, probabilityCharacter_restrict]

theorem mixedCharacter_posSemidef (ν : I → NNReal) (w : I → A → NNReal)
    (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun j k => (mixedCharacter ν w ((g j)⁻¹ * g k) : ℂ)) := by
  have h := Matrix.posSemidef_sum Finset.univ (fun i _ =>
    (probabilityCharacter_posSemidef (w i) g).smul (Complex.zero_le_real.mpr (ν i).coe_nonneg))
  convert h using 1
  ext j k
  simp [mixedCharacter, Matrix.sum_apply, Matrix.smul_apply]

/-- Exact covariance formula for a pair of equal disjoint cycles. -/
theorem mixedCharacter_doubleCycle_defect (ν : I → NNReal) (w : I → A → NNReal) (n : ℕ) :
    (∑ i, (ν i : ℝ)) *
        mixedCharacter ν w (Equiv.sumCongr (finRotate (n + 1)) (finRotate (n + 1))) -
      mixedCharacter ν w (finRotate (n + 1)) ^ 2 =
      mixtureDefect ν (fun i => ∑ a, (probabilityWeights (w i) a : ℝ) ^ (n + 1)) := by
  simp only [mixedCharacter, probabilityCharacter, coloringCharacter_sumCongr,
    coloringCharacter_finRotate, mixtureDefect, pow_two]

/-- The finite probability alphabet, retaining zero-weight letters. -/
def probabilityAlphabet (w : A → NNReal) : Multiset ℝ :=
  Finset.univ.val.map (fun a => (probabilityWeights w a : ℝ))

private theorem probabilityAlphabet_powerSum (w : A → NNReal) (k : ℕ) :
    ((probabilityAlphabet w).map (fun x => x ^ k)).sum =
      ∑ a, (probabilityWeights w a : ℝ) ^ k := by
  rw [probabilityAlphabet, Multiset.map_map]
  rfl

private theorem mixtureDefect_const (ν : I → NNReal) (c : ℝ) :
    mixtureDefect ν (fun _ => c) = 0 := by
  simp only [mixtureDefect, ← Finset.sum_mul]
  ring

/-- Exact classification of finite latent mixtures that remain multiplicative on disjoint
cycles. Moment zero is fixed by the alphabet size; the positive cycle lengths determine it. -/
theorem mixedCharacter_factorization_iff (ν : I → NNReal) (w : I → A → NNReal) :
    (∀ n : ℕ, (∑ i, (ν i : ℝ)) *
        mixedCharacter ν w (Equiv.sumCongr (finRotate (n + 1)) (finRotate (n + 1))) =
      mixedCharacter ν w (finRotate (n + 1)) ^ 2) ↔
      ∀ i j, ν i = 0 ∨ ν j = 0 ∨ probabilityAlphabet (w i) = probabilityAlphabet (w j) := by
  rw [← all_mixtureDefects_zero_iff]
  simp only [probabilityAlphabet_powerSum]
  constructor
  · intro h k
    cases k with
    | zero =>
      simp only [pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact mixtureDefect_const ν _
    | succ n =>
      have hd := mixedCharacter_doubleCycle_defect ν w n
      rw [h n, sub_self] at hd
      exact hd.symm
  · intro h n
    have hd := mixedCharacter_doubleCycle_defect ν w n
    rw [h (n + 1)] at hd
    exact sub_eq_zero.mp hd

end GaloisForLFunctions.SymmetricCharacters
