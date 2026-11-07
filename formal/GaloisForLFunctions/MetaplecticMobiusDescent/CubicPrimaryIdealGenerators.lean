/-
Primary ideal generators adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicIdealMobiusInversion

/-!
# Multiplicative primary generators for Eisenstein ideals

Multiply the locally constructed Jacobi-sum prime generators with their
ideal multiplicities. This gives a multiplicative generator away from
the ramified prime and zero otherwise. The primary congruence removes
the unit ambiguity; the squared complex norm equals the ideal norm.
-/
noncomputable section
open MeasureTheory Set Filter UniqueFactorizationMonoid
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified

private instance cubicPrimaryIdealCyclotomic : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance cubicPrimaryIdealPID : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def primaryIdealPrime (P : Ideal O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    Eisenstein.primaryGenerator P h.2
  else 0

theorem primaryIdealPrime_spec (P : Ideal O) (h : primaryIdealPrime P ≠ 0) :
    P.IsMaximal ∧ lambda ∉ P ∧
      Ideal.span {primaryIdealPrime P} = P ∧ lambda ^ 2 ∣ primaryIdealPrime P - 1 := by
  classical
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    have hs := Eisenstein.primaryGenerator_spec P hg.2
    simpa only [primaryIdealPrime, dif_pos hg] using ⟨hg.1, hg.2, hs.1.symm, hs.2⟩
  · simp only [primaryIdealPrime, dif_neg hg, ne_eq, not_true_eq_false] at h

theorem primaryIdealPrime_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) :
    primaryIdealPrime P ≠ 0 := by
  classical
  have hs := Eisenstein.primaryGenerator_spec P hg
  have htest : P.IsMaximal ∧ lambda ∉ P := ⟨inferInstance, hg⟩
  intro hz
  have hp0 : Eisenstein.primaryGenerator P hg = 0 := by
    simpa only [primaryIdealPrime, dif_pos htest] using hz
  rw [hp0] at hs
  exact (NeZero.ne P) (by simpa using hs.1)

def primaryIdealGenerator (I : Ideal O) : O :=
  if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map primaryIdealPrime).prod

@[simp] theorem primaryIdealGenerator_zero : primaryIdealGenerator 0 = 0 := by rw [primaryIdealGenerator, if_pos rfl]

@[simp] theorem primaryIdealGenerator_bot : primaryIdealGenerator ⊥ = 0 := primaryIdealGenerator_zero

@[simp] theorem primaryIdealGenerator_one : primaryIdealGenerator 1 = 1 := by
  rw [primaryIdealGenerator, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl

theorem primaryIdealGenerator_mul (I J : Ideal O) :
    primaryIdealGenerator (I * J) = primaryIdealGenerator I * primaryIdealGenerator J := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [primaryIdealGenerator, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

def primaryIdealGeneratorHom : Ideal O →*₀ O where
  toFun := primaryIdealGenerator
  map_zero' := primaryIdealGenerator_zero
  map_one' := primaryIdealGenerator_one
  map_mul' := primaryIdealGenerator_mul

theorem primaryIdealGenerator_ne_zero_ideal (I : Ideal O) (h : primaryIdealGenerator I ≠ 0) : I ≠ 0 := by
  intro hI
  exact h (by simp [hI])

theorem primaryIdealPrime_factor_ne_zero (I P : Ideal O) (hI : primaryIdealGenerator I ≠ 0)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : primaryIdealPrime P ≠ 0 := by
  have hI0 := primaryIdealGenerator_ne_zero_ideal I hI
  have hprod : ((UniqueFactorizationMonoid.normalizedFactors I).map primaryIdealPrime).prod ≠ 0 := by
    simpa only [primaryIdealGenerator, if_neg hI0] using hI
  intro hz
  exact hprod (Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨P, hP, hz⟩))

theorem span_multiset_prod (s : Multiset O) :
    Ideal.span {s.prod} = (s.map (fun x => Ideal.span {x})).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem primaryIdealGenerator_spec (I : Ideal O) (h : primaryIdealGenerator I ≠ 0) :
    Ideal.span {primaryIdealGenerator I} = I ∧ lambda ^ 2 ∣ primaryIdealGenerator I - 1 := by
  classical
  have hI0 := primaryIdealGenerator_ne_zero_ideal I h
  have hprime : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Ideal.span {primaryIdealPrime P} = P ∧ lambda ^ 2 ∣ primaryIdealPrime P - 1 := by
    intro P hP
    exact (primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P h hP)).2.2
  rw [primaryIdealGenerator, if_neg hI0]
  constructor
  · rw [span_multiset_prod, Multiset.map_map]
    have hm : (UniqueFactorizationMonoid.normalizedFactors I).map
        ((fun x => Ideal.span {x}) ∘ primaryIdealPrime) =
        UniqueFactorizationMonoid.normalizedFactors I := by
      calc
        _ = (UniqueFactorizationMonoid.normalizedFactors I).map id :=
          Multiset.map_congr rfl (fun P hP => (hprime P hP).1)
        _ = _ := Multiset.map_id' _
    rw [hm]
    exact Ideal.prod_normalizedFactors_eq_self hI0
  · apply primary_multiset_prod
    intro r hr
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hr
    exact (hprime P hP).2

theorem primaryIdealGenerator_span (n : O) (hn : n ≠ 0)
    (hprimary : lambda ^ 2 ∣ n - 1) : primaryIdealGenerator (Ideal.span {n}) = n := by
  classical
  have hI0 : (Ideal.span {n} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  have hgen : primaryIdealGenerator (Ideal.span {n}) ≠ 0 := by
    rw [primaryIdealGenerator, if_neg hI0]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨P, hP, hz⟩ := Multiset.mem_map.mp hzero
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
    have hnP : n ∈ P := hle (Ideal.subset_span (by simp))
    exact primaryIdealPrime_ne_zero P (primary_maximal_divisor_good n hprimary P hnP) hz
  have hspec := primaryIdealGenerator_spec (Ideal.span {n}) hgen
  exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1)
    hspec.2 hprimary

theorem primaryIdealGenerator_norm_sq (I : Ideal O) (h : primaryIdealGenerator I ≠ 0) :
    ‖ringComplex (primaryIdealGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [ringComplex_norm_sq_eq_absNorm_span, (primaryIdealGenerator_spec I h).1]


abbrev GoodIdeal := {I : Ideal O // primaryIdealGenerator I ≠ 0}

theorem primaryIdealGenerator_ne_zero_of_good_factors (I : Ideal O) (hI : I ≠ 0)
    (hg : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, lambda ∉ P) :
    primaryIdealGenerator I ≠ 0 := by
  rw [primaryIdealGenerator, if_neg hI]
  apply Multiset.prod_ne_zero
  intro hz
  obtain ⟨P, hP, hzero⟩ := Multiset.mem_map.mp hz
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  exact primaryIdealPrime_ne_zero P (hg P hP) hzero

theorem primaryIdealGenerator_span_ne_zero_iff (z : O) :
    primaryIdealGenerator (Ideal.span {z}) ≠ 0 ↔ ¬ lambda ∣ z := by
  constructor
  · intro hg hdiv
    have hs := primaryIdealGenerator_spec (Ideal.span {z}) hg
    have hzgen : z ∣ primaryIdealGenerator (Ideal.span {z}) := by
      apply Ideal.mem_span_singleton.mp
      exact hs.1.le (Ideal.subset_span (by simp))
    have hgen := hdiv.trans hzgen
    have hminus : lambda ∣ primaryIdealGenerator (Ideal.span {z}) - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hs.2
    have hone : lambda ∣ (1 : O) := by
      convert dvd_sub hgen hminus using 1 ; ring
    exact residue_lambda_prime.2.1 (isUnit_of_dvd_one hone)
  · intro hdiv
    have hz : z ≠ 0 := by intro h; subst z; exact hdiv (dvd_zero _)
    have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
    apply primaryIdealGenerator_ne_zero_of_good_factors _ hI
    intro P hP hlam
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzin : z ∈ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
      (Ideal.subset_span (by simp))
    have hcop : IsCoprime lambda z := residue_lambda_prime.irreducible.coprime_iff_not_dvd.mpr hdiv
    obtain ⟨a, b, hab⟩ := hcop
    have hone : (1 : O) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left a hlam) (P.mul_mem_left b hzin)
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).mpr hone)


#print axioms primaryIdealGenerator_mul
#print axioms primaryIdealGenerator_spec
#print axioms primaryIdealGenerator_span
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
