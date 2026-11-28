import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.FiniteFieldRootTorsion
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.PrimeToPartPower
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.IrreduciblePolynomialCount

/-! A collision with a fixed character value places the ratio
in a primary subgroup. The minimal polynomial then divides a
binomial of degree at most the size of that subgroup. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

private theorem exists_primary_pow_eq_one {M : Type} [Monoid M] {n l a : ℕ}
    (hn : 2 ≤ n) (hl : l.Prime) (u : M) (hu : u ^ n = 1) (hp : u ^ (l ^ a) = 1) :
    ∃ p ∈ n.primeFactors, u ^ (p ^ padicValNat p n) = 1 := by
  have hd := orderOf_dvd_of_pow_eq_one hu
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hp)
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩, by rw [hk, one_pow]⟩
  · have hln : l ^ k ∣ n := hk ▸ hd
    have hl_n : l ∣ n := (dvd_pow_self l hpos.ne').trans hln
    letI : Fact l.Prime := ⟨hl⟩
    refine ⟨l, Nat.mem_primeFactors.mpr ⟨hl, hl_n, by omega⟩, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact pow_dvd_pow _ ((padicValNat_dvd_iff_le (by omega)).mp hln)

variable (g : ℕ) [Fact g.Prime]

private def primaryBinomial (δ l : ℕ) (c₀ : (ZMod g)ˣ) : (ZMod g)[X] :=
  let k := l ^ padicValNat l (g ^ δ - 1)
  X ^ k - C ((c₀ : ZMod g) ^ k)

open Classical in
private def binomialFactors (δ l : ℕ) (c₀ : (ZMod g)ˣ) : Finset (Fin δ → ZMod g) :=
  univ.filter (fun c => Irreducible (monicOf c) ∧ monicOf c ∣ primaryBinomial g δ l c₀)

private theorem mem_binomialFactors {δ l : ℕ} {c₀ : (ZMod g)ˣ} {c : Fin δ → ZMod g} :
    c ∈ binomialFactors g δ l c₀ ↔ Irreducible (monicOf c) ∧ monicOf c ∣ primaryBinomial g δ l c₀ := by
  simp only [binomialFactors, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
def characterFactorCandidates (δ : ℕ) (c₀ : (ZMod g)ˣ) : Finset (Fin δ → ZMod g) :=
  (g ^ δ - 1).primeFactors.biUnion (fun l => binomialFactors g δ l c₀)

theorem irreducible_of_mem_characterFactorCandidates {δ : ℕ} {c₀ : (ZMod g)ˣ}
    {c : Fin δ → ZMod g} (hc : c ∈ characterFactorCandidates g δ c₀) : Irreducible (monicOf c) := by
  classical
  obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_binomialFactors g).mp hl).1

theorem characterFactorCandidates_count (δ : ℕ) (c₀ : (ZMod g)ˣ) :
    δ * (characterFactorCandidates g δ c₀).card ≤
      ∑ l ∈ (g ^ δ - 1).primeFactors, l ^ padicValNat l (g ^ δ - 1) := by
  classical
  unfold characterFactorCandidates
  refine (Nat.mul_le_mul_left δ (Finset.card_biUnion_le)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l hl => ?_
  have hpos : 0 < l ^ padicValNat l (g ^ δ - 1) := pow_pos (Nat.prime_of_mem_primeFactors hl).pos _
  have hc := card_mul_le_degree_of_irreducibles_dvd (binomialFactors g δ l c₀)
    (fun c hc => ((mem_binomialFactors g).mp hc).1) (primaryBinomial g δ l c₀)
    (X_pow_sub_C_ne_zero hpos _) (fun c hc => ((mem_binomialFactors g).mp hc).2)
  simpa only [primaryBinomial, natDegree_X_pow_sub_C] using hc

theorem minpoly_mem_characterFactorCandidates (x : Fbar g) (hx : IsIntegral (ZMod g) x)
    (hx0 : x ≠ 0) (c₀ : (ZMod g)ˣ) {l : ℕ} (hl : l.Prime)
    (he : primeToPart l x = primeToPart l (algebraMap (ZMod g) (Fbar g) (c₀ : ZMod g))) (hg : 3 ≤ g) :
    (fun i : Fin (minpoly (ZMod g) x).natDegree => (minpoly (ZMod g) x).coeff i) ∈
      characterFactorCandidates g (minpoly (ZMod g) x).natDegree c₀ := by
  classical
  let P := minpoly (ZMod g) x
  let δ := P.natDegree
  let n := g ^ δ - 1
  let y : Fbar g := algebraMap (ZMod g) (Fbar g) (c₀ : ZMod g)
  have hP : Irreducible P := minpoly.irreducible hx
  have hmon : P.Monic := minpoly.monic hx
  have hδ : 1 ≤ δ := hP.natDegree_pos
  have hn : 2 ≤ n := by
    have h := hg.trans (Nat.le_self_pow (by omega : δ ≠ 0) g)
    dsimp only [n]
    omega
  have hxn : x ^ n = 1 := by
    have h := pow_card_pow_sub_one_of_aeval_eq_zero P hP hmon x (minpoly.aeval _ _) hx0
    rwa [ZMod.card] at h
  have hy0 : y ≠ 0 := (_root_.map_ne_zero _).mpr c₀.ne_zero
  have hyn : y ^ n = 1 := by
    have h : g - 1 ∣ n := by simpa [n] using Nat.sub_dvd_pow_sub_pow g 1 δ
    obtain ⟨k, hk⟩ := h
    have hbase := FiniteField.pow_card_sub_one_eq_one (c₀ : ZMod g) c₀.ne_zero
    rw [ZMod.card] at hbase
    change (algebraMap (ZMod g) (Fbar g) (c₀ : ZMod g)) ^ n = 1
    rw [hk, ← map_pow, pow_mul, hbase, one_pow, map_one]
  have hp := div_pow_ordProj_max_eq_one hl (by omega : n ≠ 0) (by omega : n ≠ 0)
    hxn hyn hy0 he
  have huv : (x / y) ^ n = 1 := by rw [div_pow, hxn, hyn, div_one]
  obtain ⟨j, hj, hjpow⟩ := exists_primary_pow_eq_one hn hl (x / y) huv hp
  have hdiv : P ∣ primaryBinomial g δ j c₀ := by
    apply minpoly.dvd (ZMod g) x
    unfold primaryBinomial
    rw [map_sub, map_pow, aeval_X, aeval_C, map_pow, sub_eq_zero]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hy0)] at hjpow
    exact hjpow
  have hcoeff : monicOf (fun i : Fin δ => P.coeff i) = P := monicOf_coeffs P hmon rfl
  exact Finset.mem_biUnion.mpr ⟨j, hj, (mem_binomialFactors g).mpr
    ⟨by rwa [hcoeff], by rwa [hcoeff]⟩⟩

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.minpoly_mem_characterFactorCandidates
