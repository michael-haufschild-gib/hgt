import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.FiniteFieldRootConjugacy
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.FiniteFieldRootTorsion
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.PrimeToPartPower
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.IrreduciblePolynomialCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.GCD.Basic

/-! A collision within an irreducible factor forces a root into
a primary enlargement of a proper subfield. Across two factors,
each root of the second bounds one fiber of the prime-to-part map. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

theorem primary_le_rpow_quarter {l v g d : ℕ} (h : l ^ (4 * v) ≤ g ^ d) :
    ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by
  have h' : ((l ^ v : ℕ) : ℝ) ^ 4 ≤ ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg g)]
    have he : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = d := by push_cast; ring
    rw [he, Real.rpow_natCast]
    have hn : (l ^ v) ^ 4 ≤ g ^ d := by simpa only [← pow_mul, mul_comm v 4] using h
    exact_mod_cast hn
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h'

theorem root_ne_zero_of_coeff_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    {P : K[X]} (h0 : P.coeff 0 ≠ 0) {x : L} (hx : aeval x P = 0) : x ≠ 0 := by
  rintro rfl
  rw [← coeff_zero_eq_aeval_zero'] at hx
  exact h0 (map_eq_zero_iff _ (algebraMap K L).injective |>.mp hx)

variable (g : ℕ) [Fact g.Prime]

theorem prime_field_exp_pos {δ : ℕ} (hδ : 1 ≤ δ) : 0 < g ^ δ - 1 :=
  Nat.sub_pos_of_lt (one_lt_pow₀ (Fact.out : g.Prime).one_lt (by omega))

theorem root_pow_monicOf {δ : ℕ} {c : Fin δ → ZMod g}
    (hi : Irreducible (monicOf c)) (h0 : (monicOf c).coeff 0 ≠ 0)
    {x : Fbar g} (hx : aeval x (monicOf c) = 0) : x ^ (g ^ δ - 1) = 1 := by
  have h := pow_card_pow_sub_one_of_aeval_eq_zero _ hi (monic_monicOf c) x hx
    (root_ne_zero_of_coeff_zero h0 hx)
  rwa [ZMod.card, natDegree_monicOf] at h

open Classical in
def sameFactorCandidates (δ l : ℕ) : Finset (Fin δ → ZMod g) :=
  (nonzeroIrreducibleCoefficients (ZMod g) δ).filter (fun c =>
    ∃ x y : Fbar g, aeval x (monicOf c) = 0 ∧ aeval y (monicOf c) = 0 ∧
      primeToPart l x = primeToPart l y ∧ x ≠ y)

theorem mem_sameFactorCandidates {δ l : ℕ} {c : Fin δ → ZMod g} :
    c ∈ sameFactorCandidates g δ l ↔
      c ∈ nonzeroIrreducibleCoefficients (ZMod g) δ ∧
      ∃ x y : Fbar g, aeval x (monicOf c) = 0 ∧ aeval y (monicOf c) = 0 ∧
        primeToPart l x = primeToPart l y ∧ x ≠ y := by
  simp only [sameFactorCandidates, Finset.mem_filter]

private theorem same_factor_dvd_binomial {δ l : ℕ} (hl : l.Prime) (hδ : 1 ≤ δ)
    {c : Fin δ → ZMod g} (hc : c ∈ sameFactorCandidates g δ l) :
    ∃ e ∈ (Finset.range δ).filter (fun e => e ∣ δ),
      monicOf c ∣ X ^ ((g ^ e - 1) * l ^ padicValNat l (g ^ δ - 1)) - 1 := by
  obtain ⟨hci, x, y, hx, hy, hxy, hne⟩ := (mem_sameFactorCandidates g).mp hc
  obtain ⟨hirr, hc₀⟩ := mem_nonzeroIrreducibleCoefficients.mp hci
  obtain ⟨j, hj⟩ := exists_frobenius_pow_eq_of_roots (monic_monicOf c) hirr hx hy
  rw [ZMod.card] at hj
  let n := g ^ δ - 1
  let m := l ^ padicValNat l n
  have hn : 0 < n := prime_field_exp_pos g hδ
  have hxn : x ^ n = 1 := root_pow_monicOf g hirr hc₀ hx
  have hyn : y ^ n = 1 := root_pow_monicOf g hirr hc₀ hy
  have hxm (z : Fbar g) (hz : z ^ n = 1) : (primeToPart l z) ^ m = z ^ m := by
    have h := primeToPart_pow_ordProj hl hn.ne' z hz
    simpa only [m, Nat.factorization_def _ hl] using h
  have heq : x ^ m = y ^ m := (hxm x hxn).symm.trans ((congrArg (fun z => z ^ m) hxy).trans (hxm y hyn))
  rw [hj, pow_right_comm] at heq
  have hx0 := root_ne_zero_of_coeff_zero hc₀ hx
  have hjpos : 0 < g ^ j := pow_pos (Fact.out : g.Prime).pos _
  have hfix : (x ^ m) ^ (g ^ j - 1) = 1 := by
    apply mul_right_cancel₀ (pow_ne_zero _ hx0)
    rw [← pow_succ, Nat.sub_add_cancel hjpos, ← heq, one_mul]
  have hz : (x ^ m) ^ n = 1 := by rw [pow_right_comm, hxn, one_pow]
  let e := Nat.gcd j δ
  have hdv : e ∣ δ := Nat.gcd_dvd_right _ _
  have hlt : e < δ := by
    refine lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdv) ?_
    intro he
    obtain ⟨k, hk⟩ : δ ∣ j := he ▸ Nat.gcd_dvd_left j δ
    have hxd : x ^ g ^ δ = x := by
      have hp : 0 < g ^ δ := pow_pos (Fact.out : g.Prime).pos _
      rw [← Nat.sub_add_cancel hp, pow_succ, show g ^ δ - 1 = n from rfl, hxn, one_mul]
    have hf (k : ℕ) : x ^ g ^ (δ * k) = x := by
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hxd]
    exact hne (by rw [hj, hk, hf])
  have hroot : (x ^ m) ^ (g ^ e - 1) = 1 := by
    rw [show e = j.gcd δ from rfl, ← Nat.pow_sub_one_gcd_pow_sub_one]
    exact pow_gcd_eq_one.mpr ⟨hfix, hz⟩
  refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hdv⟩, ?_⟩
  rw [minpoly.eq_of_irreducible_of_monic hirr hx (monic_monicOf c)]
  apply minpoly.dvd (ZMod g) x
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero, Nat.mul_comm, pow_mul]
  exact hroot

theorem same_factor_count (δ l : ℕ) (hl : l.Prime) (hδ : 2 ≤ δ)
    (hgood : l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ) :
    ((sameFactorCandidates g δ l).card : ℝ) ≤ (g : ℝ) ^ (3 * (δ : ℝ) / 4) := by
  classical
  let I := (Finset.range δ).filter (fun e => e ∣ δ)
  let m := l ^ padicValNat l (g ^ δ - 1)
  let T (e : ℕ) : (ZMod g)[X] := X ^ ((g ^ e - 1) * m) - 1
  let V (e : ℕ) := (sameFactorCandidates g δ l).filter (fun c => monicOf c ∣ T e)
  have hV : sameFactorCandidates g δ l ⊆ I.biUnion V := by
    intro c hc
    obtain ⟨e, he, hdiv⟩ := same_factor_dvd_binomial g hl (by omega : 1 ≤ δ) hc
    exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_filter.mpr ⟨hc, hdiv⟩⟩
  let B : ℝ := (g : ℝ) ^ ((δ : ℝ) / 2) * (g : ℝ) ^ ((δ : ℝ) / 4)
  have hVle (e : ℕ) (he : e ∈ I) : (δ : ℝ) * ((V e).card : ℝ) ≤ B := by
    have ⟨hel, hed⟩ := Finset.mem_filter.mp he
    have hel' := Finset.mem_range.mp hel
    have he1 : 1 ≤ e := by
      by_contra! h
      have he0 : e = 0 := by omega
      rw [he0, zero_dvd_iff] at hed
      omega
    have he2 : e * 2 ≤ δ := by
      obtain ⟨k, hk⟩ := hed
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> simp_all
        · exact h
      exact (Nat.mul_le_mul_left e hk2).trans_eq hk.symm
    have hp : 0 < (g ^ e - 1) * m := Nat.mul_pos (prime_field_exp_pos g he1) (pow_pos hl.pos _)
    have hT : T e ≠ 0 := by
      change (X ^ ((g ^ e - 1) * m) - C 1 : (ZMod g)[X]) ≠ 0
      exact X_pow_sub_C_ne_zero hp _
    have hc := card_mul_le_degree_of_irreducibles_dvd (V e)
      (fun c hc => (mem_nonzeroIrreducibleCoefficients.mp
        ((mem_sameFactorCandidates g).mp (Finset.mem_filter.mp hc).1).1).1)
      (T e) hT (fun c hc => (Finset.mem_filter.mp hc).2)
    have hdeg : (T e).natDegree = (g ^ e - 1) * m := by
      change (X ^ ((g ^ e - 1) * m) - C 1 : (ZMod g)[X]).natDegree = _
      exact natDegree_X_pow_sub_C
    have hQ : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
    have heR : (e : ℝ) ≤ (δ : ℝ) / 2 := by
      have h : (e : ℝ) * 2 ≤ δ := by exact_mod_cast he2
      linarith only [h]
    have hpow : ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ ((δ : ℝ) / 2) := by
      calc ((g ^ e - 1 : ℕ) : ℝ) ≤ (g : ℝ) ^ e := by exact_mod_cast Nat.sub_le _ _
        _ ≤ _ := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hQ heR
    rw [hdeg] at hc
    exact (show (δ : ℝ) * ((V e).card : ℝ) ≤ ((g ^ e - 1 : ℕ) : ℝ) * m by exact_mod_cast hc).trans
      (mul_le_mul hpow (primary_le_rpow_quarter hgood) (Nat.cast_nonneg _) (by positivity))
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast (show 0 < δ by omega)
  have hI : I.card ≤ δ := (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hcom : (δ : ℝ) * ((sameFactorCandidates g δ l).card : ℝ) ≤ δ * B := by
    calc (δ : ℝ) * ((sameFactorCandidates g δ l).card : ℝ) ≤
          (δ : ℝ) * ∑ e ∈ I, ((V e).card : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hδR.le
          exact_mod_cast (Finset.card_le_card hV).trans Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ I, B := by rw [Finset.mul_sum]; exact Finset.sum_le_sum hVle
      _ ≤ δ * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by positivity : 0 ≤ B)
  have hB : B = (g : ℝ) ^ (3 * (δ : ℝ) / 4) := by
    change (g : ℝ) ^ ((δ : ℝ) / 2) * (g : ℝ) ^ ((δ : ℝ) / 4) = _
    rw [← Real.rpow_add (Nat.cast_pos.mpr (Fact.out : g.Prime).pos)]
    congr 1
    ring
  exact (le_of_mul_le_mul_left hcom hδR).trans_eq hB

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.same_factor_count
