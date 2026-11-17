import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.MobiusProbeKernel
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelCountsTheZerosRightOfTheLine

/-!
# Half-plane normalization preserves the exact arithmetic index

The positive exponential factor in the Möbius kernel is absorbed into
an invertible diagonal matrix. Sylvester congruence therefore preserves
all three inertia indices. Integer nodes beyond five remain a uniqueness
set, so the normalized kernels retain the exact count of right-hand zeros.
-/

open Matrix
open scoped ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
open HTGeometry ArithmeticCastelnuovoSeveri
noncomputable section

def mobiusGram {n : ℕ} (r τ υ : ℝ) (p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => mobiusProbeKernel r τ υ (p i) (p j)

def mobiusNormalizingMatrix {n : ℕ} (r τ : ℝ) (p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (Real.exp (-r / 2) : ℂ) * conj (mobiusDenominator τ (p i)))

theorem mobiusNormalizingMatrix_isUnit {n : ℕ} (r τ : ℝ) (p : Fin n → ℝ) :
    IsUnit (mobiusNormalizingMatrix r τ p) := by
  apply Matrix.isUnit_diagonal.mpr
  apply Pi.isUnit_iff.mpr
  intro i
  apply isUnit_iff_ne_zero.mpr
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    ((map_ne_zero _).mpr (mobiusDenominator_ne_zero τ (p i)))

/-- One invertible diagonal congruence removes the entire Möbius normalization. -/
theorem mobiusGram_normalized_congruence {n : ℕ} (r τ υ : ℝ) (p : Fin n → ℝ) :
    (mobiusNormalizingMatrix r τ p)ᴴ * mobiusGram r τ υ p * mobiusNormalizingMatrix r τ p =
      probeGram (fun i => node (p i)) := by
  have hr : Real.exp (-r / 2) ^ 2 * Real.exp r = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hc : (Real.exp (-r / 2) : ℂ) ^ 2 * (Real.exp r : ℂ) = 1 := by exact_mod_cast hr
  have hs : (mobiusNormalizingMatrix r τ p)ᴴ =
      Matrix.diagonal (fun i => (Real.exp (-r / 2) : ℂ) * mobiusDenominator τ (p i)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp only [mobiusNormalizingMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        if_pos rfl, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    · simp only [mobiusNormalizingMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        if_neg h, if_neg (Ne.symm h), star_zero]
  rw [hs]
  ext i j
  simp only [mobiusNormalizingMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, mobiusGram, probeGram]
  calc
    _ = (Real.exp (-r / 2) : ℂ) ^ 2 *
        (mobiusDenominator τ (p i) * conj (mobiusDenominator τ (p j)) *
          mobiusProbeKernel r τ υ (p i) (p j)) := by ring
    _ = ((Real.exp (-r / 2) : ℂ) ^ 2 * (Real.exp r : ℂ)) *
        (bareMixedEnergy (probe (node (p i))) (probe (node (p j))) : ℂ) := by
      rw [mobiusProbeKernel_congruence]
      ring
    _ = _ := by rw [hc, one_mul]

/-- Möbius normalization preserves the full inertia triple, including its nullspace dimension. -/
theorem mobiusGram_inertia {n : ℕ} (r τ υ : ℝ) (p : Fin n → ℝ) :
    hermPosIndex (mobiusGram r τ υ p) = hermPosIndex (probeGram (fun i => node (p i))) ∧
    hermNegIndex (mobiusGram r τ υ p) = hermNegIndex (probeGram (fun i => node (p i))) ∧
    hermNullIndex (mobiusGram r τ υ p) = hermNullIndex (probeGram (fun i => node (p i))) := by
  have hu := mobiusNormalizingMatrix_isUnit r τ p
  have hp := posIndex_conjugate (mobiusGram r τ υ p) hu
  have hn := negIndex_conjugate (mobiusGram r τ υ p) hu
  have hz := nullIndex_conjugate (mobiusGram r τ υ p) hu
  rw [mobiusGram_normalized_congruence] at hp hn hz
  exact ⟨hp.symm, hn.symm, hz.symm⟩

/-- Every normalized kernel family counts exactly the distinct zeta zeros right of the line. -/
theorem mobius_probeIndex_law (r τ υ : ℝ) (k : ℕ) :
    (∃ (n : ℕ) (p : Fin n → ℝ), k ≤ hermNegIndex (mobiusGram r τ υ p)) ↔
      (k : ℕ∞) ≤ (rightZeros Zeta23.zetaZeroConfig).encard := by
  constructor
  · rintro ⟨n, p, hp⟩
    rw [(mobiusGram_inertia r τ υ p).2.1] at hp
    have hn (i : Fin n) : 1 ≤ node (p i) := by
      unfold node
      linarith only [abs_nonneg (p i)]
    exact (ENat.coe_le_coe.mpr hp).trans (hermNegIndex_probeGram_le hn)
  · intro hk
    have hs : ∀ t ∈ {t : ℝ | ∃ m : ℕ, 5 ≤ m ∧ t = m}, 1 ≤ t := by
      rintro t ⟨m, hm, rfl⟩
      exact_mod_cast (show 1 ≤ m by omega)
    obtain ⟨n, p, hp, hi⟩ :=
      (probeIndex_law hs (isRightProbeUniquenessSet_natFrom (by norm_num : 2 ≤ 5)) k).mpr hk
    have he : (fun i => node (p i - 5)) = p := by
      funext i
      have hpi : 5 ≤ p i := by
        obtain ⟨m, hm, hpm⟩ := hp i
        rw [hpm]
        exact_mod_cast hm
      unfold node
      rw [abs_of_nonneg (sub_nonneg.mpr hpi)]
      ring
    refine ⟨n, fun i => p i - 5, ?_⟩
    rw [(mobiusGram_inertia r τ υ (fun i => p i - 5)).2.1, he]
    exact hi

#print axioms mobiusGram_normalized_congruence
#print axioms mobiusGram_inertia
#print axioms mobius_probeIndex_law
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
