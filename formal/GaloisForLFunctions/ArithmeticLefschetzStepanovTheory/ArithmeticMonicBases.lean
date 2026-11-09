import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TorsionNewtonPolynomials
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Integral bases with prescribed arithmetic leading monomials

A family having leading monomial `X^a` with coefficient one at every index
is an integral basis. Subtracting its leading term strictly lowers
arithmetic length; the inverse change of coordinates preserves length.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- Finite integral synthesis in a family indexed by prime exponent vectors. -/
def arithmeticMonicSynthesis (B : (P →₀ ℕ) → MvPolynomial P ℤ) :
    ((P →₀ ℕ) →₀ ℤ) →ₗ[ℤ] MvPolynomial P ℤ := Finsupp.linearCombination ℤ B

theorem arithmeticMonicSynthesis_apply (B : (P →₀ ℕ) → MvPolynomial P ℤ)
    (c : (P →₀ ℕ) →₀ ℤ) : arithmeticMonicSynthesis B c = ∑ a ∈ c.support, c a • B a := rfl

theorem arithmeticMonicSynthesis_single (B : (P →₀ ℕ) → MvPolynomial P ℤ)
    (a : P →₀ ℕ) (c : ℤ) : arithmeticMonicSynthesis B (Finsupp.single a c) = c • B a :=
  Finsupp.linearCombination_single _ _ _

variable {B : (P →₀ ℕ) → MvPolynomial P ℤ}

theorem coeff_arithmeticMonicFamily_eq_zero_of_weight_lt (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (a b : P →₀ ℕ) (hab : weight a < weight b) : (B a).coeff b = 0 := by
  apply MvPolynomial.notMem_support_iff.mp
  exact fun hb => (not_le_of_gt hab) ((hB a).2 b hb)

/-- The greatest nonzero coordinate survives synthesis unchanged. -/
theorem coeff_arithmeticMonicSynthesis_top (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (c : (P →₀ ℕ) →₀ ℤ) (a : P →₀ ℕ) (ha : a ∈ c.support)
    (hmax : ∀ b ∈ c.support, weight b ≤ weight a) :
    (arithmeticMonicSynthesis B c).coeff a = c a := by
  classical
  rw [arithmeticMonicSynthesis_apply, MvPolynomial.coeff_sum, sum_eq_single a]
  · rw [MvPolynomial.coeff_smul, (hB a).1]
    simp only [smul_eq_mul, mul_one]
  · intro b hb hba
    have hlt : weight b < weight a := lt_of_le_of_ne (hmax b hb)
      (fun h => hba (weight_injective h))
    rw [MvPolynomial.coeff_smul, coeff_arithmeticMonicFamily_eq_zero_of_weight_lt hB b a hlt,
      smul_zero]
  · exact fun h => (h ha).elim

theorem arithmeticMonicSynthesis_injective (hB : ∀ a, ArithmeticMonicAt (B a) a) :
    Function.Injective (arithmeticMonicSynthesis B) := by
  intro c d heq
  have hz : arithmeticMonicSynthesis B (c - d) = 0 := by rw [map_sub, heq, sub_self]
  suffices c - d = 0 from sub_eq_zero.mp this
  by_contra hne
  obtain ⟨a, ha, hmax⟩ := exists_max_image (c - d).support weight
    (Finsupp.support_nonempty_iff.mpr hne)
  have hc := congrArg (MvPolynomial.coeff a) hz
  rw [coeff_arithmeticMonicSynthesis_top hB (c - d) a ha hmax, MvPolynomial.coeff_zero] at hc
  exact (Finsupp.mem_support_iff.mp ha) hc

theorem length_arithmeticMonicSynthesis_le (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (c : (P →₀ ℕ) →₀ ℤ) (N : ℕ) (hc : ∀ a ∈ c.support, weight a ≤ N) :
    length (arithmeticMonicSynthesis B c) ≤ N := by
  classical
  apply Finset.sup_le
  intro b hb
  rw [arithmeticMonicSynthesis_apply] at hb
  obtain ⟨a, ha, hba⟩ := mem_biUnion.mp (MvPolynomial.support_sum hb)
  have hba' : b ∈ (B a).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul] at hba
    exact MvPolynomial.mem_support_iff.mpr ((mul_ne_zero_iff.mp hba).2)
  exact ((hB a).2 b hba').trans (hc a ha)

/-- Arithmetic length is preserved exactly by every integral monic triangular family. -/
theorem length_arithmeticMonicSynthesis (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (c : (P →₀ ℕ) →₀ ℤ) : length (arithmeticMonicSynthesis B c) = c.support.sup weight := by
  classical
  apply le_antisymm (length_arithmeticMonicSynthesis_le hB c _ (fun a ha => le_sup ha))
  by_cases hc : c = 0
  · subst c; exact bot_le
  obtain ⟨a, ha, hmax⟩ := exists_max_image c.support weight (Finsupp.support_nonempty_iff.mpr hc)
  have htop : c.support.sup weight = weight a :=
    le_antisymm (Finset.sup_le hmax) (le_sup (f := weight) ha)
  rw [htop]
  apply le_sup (f := weight)
  rw [MvPolynomial.mem_support_iff, coeff_arithmeticMonicSynthesis_top hB c a ha hmax]
  exact Finsupp.mem_support_iff.mp ha

theorem length_sub_top_arithmeticMonicFamily_lt (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (F : MvPolynomial P ℤ) (a : P →₀ ℕ) (ha : a ∈ F.support)
    (hmax : ∀ b ∈ F.support, weight b ≤ weight a) :
    length (F - F.coeff a • B a) < length F := by
  classical
  have htop : length F = weight a :=
    le_antisymm (Finset.sup_le hmax) (le_sup (f := weight) ha)
  rw [htop]
  apply (Finset.sup_lt_iff (weight_pos a)).mpr
  intro b hb
  have hbne := MvPolynomial.mem_support_iff.mp hb
  have hbU := MvPolynomial.support_sub P F (F.coeff a • B a) hb
  have hble : weight b ≤ weight a := by
    rcases mem_union.mp hbU with hbF | hbB
    · exact hmax b hbF
    · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul] at hbB
      exact (hB a).2 b (MvPolynomial.mem_support_iff.mpr ((mul_ne_zero_iff.mp hbB).2))
  apply lt_of_le_of_ne hble
  intro he
  have hba : b = a := weight_injective he
  apply hbne
  rw [hba, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, (hB a).1,
    smul_eq_mul, mul_one, sub_self]

/-- Integral leading-coefficient subtraction constructs coordinates at the original length. -/
theorem exists_filtered_arithmeticMonic_expansion (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (F : MvPolynomial P ℤ) (N : ℕ) (hlen : length F ≤ N) :
    ∃ c : (P →₀ ℕ) →₀ ℤ, (∀ a ∈ c.support, weight a ≤ N) ∧ arithmeticMonicSynthesis B c = F := by
  classical
  induction N using Nat.strong_induction_on generalizing F with
  | h N ih =>
    by_cases hF : F = 0
    · subst F
      exact ⟨0, by simp only [Finsupp.support_zero, notMem_empty, false_implies, implies_true], map_zero _⟩
    obtain ⟨a, ha, hmax⟩ := exists_max_image F.support weight (MvPolynomial.support_nonempty.mpr hF)
    have haN : weight a ≤ N := (le_sup (f := weight) ha).trans hlen
    let G := F - F.coeff a • B a
    have hGlt : length G < length F := length_sub_top_arithmeticMonicFamily_lt hB F a ha hmax
    obtain ⟨c, hc, hcs⟩ := ih (length G) (hGlt.trans_le hlen) G le_rfl
    refine ⟨c + Finsupp.single a (F.coeff a), ?_, ?_⟩
    · intro b hb
      rcases mem_union.mp (Finsupp.support_add hb) with hbC | hbA
      · exact (hc b hbC).trans (hGlt.le.trans hlen)
      · have hba : b = a := mem_singleton.mp (Finsupp.support_single_subset hbA)
        exact hba ▸ haN
    · rw [map_add, arithmeticMonicSynthesis_single, hcs]
      exact sub_add_cancel F (F.coeff a • B a)

theorem arithmeticMonicSynthesis_surjective (hB : ∀ a, ArithmeticMonicAt (B a) a) :
    Function.Surjective (arithmeticMonicSynthesis B) := by
  intro F
  obtain ⟨c, _, hc⟩ := exists_filtered_arithmeticMonic_expansion hB F (length F) le_rfl
  exact ⟨c, hc⟩

/-- The integral change of coordinates supplied by arithmetic triangularity. -/
def arithmeticMonicEquiv (B : (P →₀ ℕ) → MvPolynomial P ℤ)
    (hB : ∀ a, ArithmeticMonicAt (B a) a) : ((P →₀ ℕ) →₀ ℤ) ≃ₗ[ℤ] MvPolynomial P ℤ :=
  LinearEquiv.ofBijective (arithmeticMonicSynthesis B)
    ⟨arithmeticMonicSynthesis_injective hB, arithmeticMonicSynthesis_surjective hB⟩

def arithmeticMonicBasis (B : (P →₀ ℕ) → MvPolynomial P ℤ)
    (hB : ∀ a, ArithmeticMonicAt (B a) a) : Module.Basis (P →₀ ℕ) ℤ (MvPolynomial P ℤ) :=
  Module.Basis.ofRepr (arithmeticMonicEquiv B hB).symm

theorem arithmeticMonicBasis_apply (hB : ∀ a, ArithmeticMonicAt (B a) a) (a : P →₀ ℕ) :
    arithmeticMonicBasis B hB a = B a := by
  change arithmeticMonicSynthesis B (Finsupp.single a 1) = _
  rw [arithmeticMonicSynthesis_single, one_smul]

theorem arithmeticMonicSynthesis_repr (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (F : MvPolynomial P ℤ) :
    arithmeticMonicSynthesis B ((arithmeticMonicBasis B hB).repr F) = F :=
  (arithmeticMonicEquiv B hB).apply_symm_apply F

theorem arithmeticMonicBasis_repr_length (hB : ∀ a, ArithmeticMonicAt (B a) a)
    (F : MvPolynomial P ℤ) : ((arithmeticMonicBasis B hB).repr F).support.sup weight = length F := by
  rw [← length_arithmeticMonicSynthesis hB, arithmeticMonicSynthesis_repr]

#print axioms arithmeticMonicBasis
#print axioms arithmeticMonicBasis_repr_length

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
