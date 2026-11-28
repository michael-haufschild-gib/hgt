import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.SquarefreePolynomialCount

/-! The product of reciprocal torus orders for a squarefree
polynomial of degree \(N\) is at least the reciprocal of the field
cardinality to the power \(N\). A squarefree count bounds its mass
over all monic labels with nonzero constant term. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

open Classical in
def degreeType {K : Type} [Field K] (f : K[X]) : Multiset ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree

open UniqueFactorizationMonoid in
theorem sum_degreeType {K : Type} [Field K] (f : K[X]) (hf : f ≠ 0) :
    (degreeType f).sum = f.natDegree := by
  classical
  unfold degreeType
  have h0 : (0 : K[X]) ∉ UniqueFactorizationMonoid.normalizedFactors f := fun h =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor 0 h).ne_zero rfl
  rw [← Polynomial.natDegree_multiset_prod _ h0]
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

theorem one_le_of_mem_degreeType {K : Type} [Field K] (f : K[X]) (d : ℕ) (hd : d ∈ degreeType f) :
    1 ≤ d := by
  classical
  unfold degreeType at hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hd
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)

theorem inv_pow_sum_le (q : ℝ) (hq : 1 < q) (s : Multiset ℕ) (hs : ∀ d ∈ s, 1 ≤ d) :
    (q ^ s.sum)⁻¹ ≤ (s.map (fun d => (q ^ d - 1)⁻¹)).prod := by
  have hq0 : 0 < q := by linarith
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun d hd => hs d (Multiset.mem_cons_of_mem hd))
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, pow_add, mul_inv]
    have hqa : 1 < q ^ a := one_lt_pow₀ hq (by omega)
    have h1 : (q ^ a)⁻¹ ≤ (q ^ a - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (q ^ s.sum)⁻¹ := (inv_pos.mpr (pow_pos hq0 _)).le
    have h3 : 0 ≤ (q ^ a - 1)⁻¹ := (inv_pos.mpr (by linarith)).le
    exact mul_le_mul h1 ih' h2 h3

variable (g : ℕ) [Fact g.Prime]

open Classical in
def squarefreeCoefficients (N : ℕ) : Finset (Fin N → ZMod g) :=
  univ.filter fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0

def squarefreeWeight (f : (ZMod g)[X]) : ℝ :=
  ((degreeType f).map (fun d => ((g : ℝ) ^ d - 1)⁻¹)).prod

theorem square_mass_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    1 - 2 / (g : ℝ) ≤ ∑ c ∈ squarefreeCoefficients g N, squarefreeWeight g (monicOf c) := by
  have hg : (1 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).one_lt
  have hg0 : (0 : ℝ) < g := zero_lt_one.trans hg
  have hw (c : Fin N → ZMod g) : ((g : ℝ) ^ N)⁻¹ ≤ squarefreeWeight g (monicOf c) := by
    rw [squarefreeWeight]
    have h := inv_pow_sum_le _ hg (degreeType (monicOf c)) (one_le_of_mem_degreeType _)
    rwa [sum_degreeType _ (monic_monicOf c).ne_zero, natDegree_monicOf] at h
  classical
  have hc := squarefree_count (ZMod g) N hN
  rw [ZMod.card] at hc
  have hcNat : g ^ N ≤ (squarefreeCoefficients g N).card + 2 * g ^ (N - 1) := by
    convert hc using 2
    apply congrArg Finset.card
    ext c
    simp [squarefreeCoefficients]
  have hc' : (g : ℝ) ^ N ≤ ((squarefreeCoefficients g N).card : ℝ) + 2 * (g : ℝ) ^ (N - 1) := by
    exact_mod_cast hcNat
  have hp : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 _
  have hpow : (g : ℝ) ^ N = (g : ℝ) ^ (N - 1) * (g : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have he : (2 / (g : ℝ)) * (g : ℝ) ^ N = 2 * (g : ℝ) ^ (N - 1) := by
    rw [hpow]
    field_simp
  calc
    1 - 2 / (g : ℝ) ≤ ((squarefreeCoefficients g N).card : ℝ) * ((g : ℝ) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp, sub_mul, one_mul, he]
      exact sub_le_iff_le_add.mpr hc'
    _ ≤ ∑ c ∈ squarefreeCoefficients g N, squarefreeWeight g (monicOf c) := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ fun c _ => hw c

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.square_mass_lower_bound
