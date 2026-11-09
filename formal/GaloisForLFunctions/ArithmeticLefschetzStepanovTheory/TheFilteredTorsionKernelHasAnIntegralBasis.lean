import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TorsionNewtonPolynomials
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionMultiplicityLeadingExponents
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# An integral basis for every filtered torsion kernel

Full torsion multiplicity is diagonal in the Newton polynomials
`∏ p, u_p^(a_p mod q) (u_p^q - 1)^(a_p div q)`: retain precisely the
indices with quotient order at least `r`. The change of basis preserves
arithmetic length, so imposing length at most `N` retains precisely the
indices of integer weight at most `N`. Leading-coefficient subtraction
proves existence over the integers; triangularity proves uniqueness.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- Exact full multiplicity on the complete prime torsion grid. -/
def FullTorsionMultiplicity (q r : ℕ) (F : MvPolynomial P ℤ) : Prop :=
  ∀ t : P → ZMod q, MvPolynomial.map (Int.castRingHom ℂ) F ∈
    vanishingIdeal ℂ {fun p => ZMod.stdAddChar (t p)} ^ r

/-- Synthesis from the integral torsion Newton polynomials. -/
def torsionNewtonSynthesis (q : ℕ) : ((P →₀ ℕ) →₀ ℤ) →ₗ[ℤ] MvPolynomial P ℤ :=
  Finsupp.linearCombination ℤ (torsionNewtonPolynomial q)

theorem torsionNewtonSynthesis_apply (q : ℕ) (c : (P →₀ ℕ) →₀ ℤ) :
    torsionNewtonSynthesis q c = ∑ a ∈ c.support, c a • torsionNewtonPolynomial q a := rfl

theorem torsionNewtonSynthesis_single (q : ℕ) (a : P →₀ ℕ) (c : ℤ) :
    torsionNewtonSynthesis q (Finsupp.single a c) = c • torsionNewtonPolynomial q a :=
  Finsupp.linearCombination_single _ _ _

/-- Coordinatewise divisibility is monotone for the arithmetic weight. -/
theorem weight_mono {a b : P →₀ ℕ} (h : a ≤ b) : weight a ≤ weight b :=
  prod_le_prod' fun p _ => Nat.pow_le_pow_right (p : Nat.Primes).2.pos (h p)

/-- The greatest arithmetic support integer must carry the required quotient order. -/
theorem le_torsionQuotientOrder_of_weight_top (q r : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) (a : P →₀ ℕ) (ha : a ∈ F.support)
    (hmax : ∀ d ∈ F.support, weight d ≤ weight a)
    (hmult : FullTorsionMultiplicity q r F) : r ≤ torsionQuotientOrder q a := by
  apply le_torsionQuotientOrder_of_maximal q r (MvPolynomial.map (Int.castRingHom ℂ) F) a
  · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
    exact_mod_cast MvPolynomial.mem_support_iff.mp ha
  · intro d hd had
    have hdF : d ∈ F.support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hd
      exact MvPolynomial.mem_support_iff.mpr fun h => hd (by rw [h, map_zero])
    exact weight_injective (le_antisymm (hmax d hdF) (weight_mono had))
  · exact hmult

/-- Quotient order is the exact full torsion multiplicity of a Newton polynomial. -/
theorem torsionNewtonPolynomial_multiplicity_iff (q r : ℕ) [NeZero q] (a : P →₀ ℕ) :
    FullTorsionMultiplicity q r (torsionNewtonPolynomial q a) ↔
      r ≤ torsionQuotientOrder q a := by
  constructor
  · intro hmult
    have hm := torsionNewtonPolynomial_monic q a
    exact le_torsionQuotientOrder_of_weight_top q r _ a
      (MvPolynomial.mem_support_iff.mpr (by rw [hm.1]; exact one_ne_zero)) hm.2 hmult
  · intro hr t
    exact torsionNewtonPolynomial_mem_pointIdeal_pow q r a hr t

/-- The highest nonzero Newton coefficient is unchanged by synthesis. -/
theorem coeff_torsionNewtonSynthesis_top (q : ℕ) [NeZero q]
    (c : (P →₀ ℕ) →₀ ℤ) (a : P →₀ ℕ) (ha : a ∈ c.support)
    (hmax : ∀ b ∈ c.support, weight b ≤ weight a) :
    (torsionNewtonSynthesis q c).coeff a = c a := by
  classical
  rw [torsionNewtonSynthesis_apply, MvPolynomial.coeff_sum, sum_eq_single a]
  · rw [MvPolynomial.coeff_smul, (torsionNewtonPolynomial_monic q a).1]
    simp only [smul_eq_mul, mul_one]
  · intro b hb hba
    have hlt : weight b < weight a := lt_of_le_of_ne (hmax b hb)
      (fun h => hba (weight_injective h))
    rw [MvPolynomial.coeff_smul, coeff_torsionNewtonPolynomial_eq_zero_of_weight_lt q b a hlt,
      smul_zero]
  · intro h
    exact (h ha).elim

/-- Integral Newton coordinates are unique at all arithmetic lengths. -/
theorem torsionNewtonSynthesis_injective (q : ℕ) [NeZero q] :
    Function.Injective (torsionNewtonSynthesis (P := P) q) := by
  intro c d heq
  have hz : torsionNewtonSynthesis q (c - d) = 0 := by rw [map_sub, heq, sub_self]
  suffices c - d = 0 from sub_eq_zero.mp this
  by_contra hne
  obtain ⟨a, ha, hmax⟩ := exists_max_image (c - d).support weight
    (Finsupp.support_nonempty_iff.mpr hne)
  have hc := congrArg (MvPolynomial.coeff a) hz
  rw [coeff_torsionNewtonSynthesis_top q (c - d) a ha hmax, MvPolynomial.coeff_zero] at hc
  exact (Finsupp.mem_support_iff.mp ha) hc

/-- Every admissible coefficient vector synthesizes to the prescribed multiplicity. -/
theorem torsionNewtonSynthesis_multiplicity (q r : ℕ) [NeZero q]
    (c : (P →₀ ℕ) →₀ ℤ) (hc : ∀ a ∈ c.support, r ≤ torsionQuotientOrder q a) :
    FullTorsionMultiplicity q r (torsionNewtonSynthesis q c) := by
  intro t
  rw [torsionNewtonSynthesis_apply, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (torsionNewtonPolynomial_mem_pointIdeal_pow q r a (hc a ha) t)

/-- Newton synthesis respects every arithmetic length cutoff. -/
theorem length_torsionNewtonSynthesis_le (q : ℕ) [NeZero q]
    (c : (P →₀ ℕ) →₀ ℤ) (N : ℕ) (hc : ∀ a ∈ c.support, weight a ≤ N) :
    length (torsionNewtonSynthesis q c) ≤ N := by
  classical
  apply Finset.sup_le
  intro b hb
  rw [torsionNewtonSynthesis_apply] at hb
  obtain ⟨a, ha, hba⟩ := mem_biUnion.mp (MvPolynomial.support_sum hb)
  have hba' : b ∈ (torsionNewtonPolynomial q a).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul] at hba
    exact MvPolynomial.mem_support_iff.mpr ((mul_ne_zero_iff.mp hba).2)
  exact ((torsionNewtonPolynomial_monic q a).2 b hba').trans (hc a ha)

/-- Newton coordinates preserve arithmetic length exactly, including cancellation in the input. -/
theorem length_torsionNewtonSynthesis (q : ℕ) [NeZero q] (c : (P →₀ ℕ) →₀ ℤ) :
    length (torsionNewtonSynthesis q c) = c.support.sup weight := by
  classical
  apply le_antisymm (length_torsionNewtonSynthesis_le q c _ (fun a ha => le_sup ha))
  by_cases hc : c = 0
  · subst c
    simp only [Finsupp.support_zero, Finset.sup_empty, Nat.zero_le]
  obtain ⟨a, ha, hmax⟩ := exists_max_image c.support weight
    (Finsupp.support_nonempty_iff.mpr hc)
  have htop : c.support.sup weight = weight a :=
    le_antisymm (Finset.sup_le hmax) (le_sup (f := weight) ha)
  rw [htop]
  apply le_sup (f := weight)
  rw [MvPolynomial.mem_support_iff, coeff_torsionNewtonSynthesis_top q c a ha hmax]
  exact Finsupp.mem_support_iff.mp ha

/-- Removing the leading Newton polynomial strictly lowers arithmetic length. -/
theorem length_sub_top_torsionNewtonPolynomial_lt (q : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) (a : P →₀ ℕ) (ha : a ∈ F.support)
    (hmax : ∀ b ∈ F.support, weight b ≤ weight a) :
    length (F - F.coeff a • torsionNewtonPolynomial q a) < length F := by
  classical
  have htop : length F = weight a :=
    le_antisymm (Finset.sup_le hmax) (le_sup (f := weight) ha)
  rw [htop]
  apply (Finset.sup_lt_iff (weight_pos a)).mpr
  intro b hb
  have hbne := MvPolynomial.mem_support_iff.mp hb
  have hbU := MvPolynomial.support_sub P F (F.coeff a • torsionNewtonPolynomial q a) hb
  have hble : weight b ≤ weight a := by
    rcases mem_union.mp hbU with hbF | hbB
    · exact hmax b hbF
    · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, smul_eq_mul] at hbB
      exact (torsionNewtonPolynomial_monic q a).2 b
        (MvPolynomial.mem_support_iff.mpr ((mul_ne_zero_iff.mp hbB).2))
  apply lt_of_le_of_ne hble
  intro he
  have hba : b = a := weight_injective he
  apply hbne
  rw [hba, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    (torsionNewtonPolynomial_monic q a).1, smul_eq_mul, mul_one, sub_self]

theorem FullTorsionMultiplicity.sub {q r : ℕ} {F G : MvPolynomial P ℤ}
    (hF : FullTorsionMultiplicity q r F) (hG : FullTorsionMultiplicity q r G) :
    FullTorsionMultiplicity q r (F - G) := by
  intro t
  rw [map_sub]
  exact Ideal.sub_mem _ (hF t) (hG t)

theorem FullTorsionMultiplicity.smul {q r : ℕ} {F : MvPolynomial P ℤ}
    (hF : FullTorsionMultiplicity q r F) (c : ℤ) :
    FullTorsionMultiplicity q r (c • F) := by
  intro t
  rw [MvPolynomial.smul_eq_C_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (hF t)

/-- Every integer auxiliary has an admissible Newton expansion at its original length. -/
theorem exists_filtered_torsionNewton_expansion (q r : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) (N : ℕ) (hlen : length F ≤ N)
    (hmult : FullTorsionMultiplicity q r F) :
    ∃ c : (P →₀ ℕ) →₀ ℤ,
      (∀ a ∈ c.support, weight a ≤ N ∧ r ≤ torsionQuotientOrder q a) ∧
      torsionNewtonSynthesis q c = F := by
  classical
  induction N using Nat.strong_induction_on generalizing F with
  | h N ih =>
    by_cases hF : F = 0
    · subst F
      exact ⟨0, by simp only [Finsupp.support_zero, notMem_empty, false_implies, implies_true],
        map_zero _⟩
    obtain ⟨a, ha, hmax⟩ := exists_max_image F.support weight
      (MvPolynomial.support_nonempty.mpr hF)
    have har : r ≤ torsionQuotientOrder q a :=
      le_torsionQuotientOrder_of_weight_top q r F a ha hmax hmult
    have haN : weight a ≤ N := (le_sup (f := weight) ha).trans hlen
    let G := F - F.coeff a • torsionNewtonPolynomial q a
    have hGlt : length G < length F := length_sub_top_torsionNewtonPolynomial_lt q F a ha hmax
    have hB : FullTorsionMultiplicity q r (torsionNewtonPolynomial q a) :=
      fun t => torsionNewtonPolynomial_mem_pointIdeal_pow q r a har t
    have hGmult : FullTorsionMultiplicity q r G :=
      hmult.sub (hB.smul (F.coeff a))
    obtain ⟨c, hc, hcs⟩ := ih (length G) (hGlt.trans_le hlen) G le_rfl hGmult
    refine ⟨c + Finsupp.single a (F.coeff a), ?_, ?_⟩
    · intro b hb
      rcases mem_union.mp (Finsupp.support_add hb) with hbC | hbA
      · exact ⟨(hc b hbC).1.trans (hGlt.le.trans hlen), (hc b hbC).2⟩
      · have hba : b = a := mem_singleton.mp (Finsupp.support_single_subset hbA)
        exact hba ▸ ⟨haN, har⟩
    · rw [map_add, torsionNewtonSynthesis_single, hcs]
      exact sub_add_cancel F (F.coeff a • torsionNewtonPolynomial q a)

/-- Exact integral coordinates for the torsion kernel at every arithmetic cutoff. -/
theorem filtered_torsion_kernel_iff_unique_expansion (q r N : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) :
    (length F ≤ N ∧ FullTorsionMultiplicity q r F) ↔
      ∃! c : (P →₀ ℕ) →₀ ℤ,
        (∀ a ∈ c.support, weight a ≤ N ∧ r ≤ torsionQuotientOrder q a) ∧
        torsionNewtonSynthesis q c = F := by
  constructor
  · rintro ⟨hlen, hmult⟩
    obtain ⟨c, hc, hcs⟩ := exists_filtered_torsionNewton_expansion q r F N hlen hmult
    refine ⟨c, ⟨hc, hcs⟩, ?_⟩
    intro d hd
    exact torsionNewtonSynthesis_injective q (hd.2.trans hcs.symm)
  · rintro ⟨c, ⟨hc, hcs⟩, _⟩
    rw [← hcs]
    exact ⟨length_torsionNewtonSynthesis_le q c N (fun a ha => (hc a ha).1),
      torsionNewtonSynthesis_multiplicity q r c (fun a ha => (hc a ha).2)⟩

#print axioms filtered_torsion_kernel_iff_unique_expansion

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
