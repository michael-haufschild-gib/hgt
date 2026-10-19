import GaloisForLFunctions.TransHorizonIncidenceMechanics.FourthBandEnvelopeAndSharpFiveHorizonBoundary
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonRadicalStateAndDefectNormalForm

/-!
# Exact cofinal Möbius source alphabet

On the literal horizon `(B+2)N`, all source values are determined by the
Möbius responses of divisors of the primorials through `B+1`. Every value in
that finite alphabet occurs at arbitrarily large cutoffs in the same horizon.

The proof reuses THIM's visible radical state and complementary-band formula.
Large prime extensions give exact attainment using unbounded primes.
The truncated divisor observable and its prime-deletion recursion are classical:
Helfgott–Thompson, Proposition 3.2, https://doi.org/10.1007/s40993-022-00408-8.
This leaf supports the complete cofinal source-law candidate.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

private theorem quotient_moebius {R d : ℕ} (hR : Squarefree R) (hd : d ∣ R) :
    moebiusReal (R / d) = moebiusReal R * moebiusReal d := by
  have hsf : Squarefree d := hR.squarefree_of_dvd hd
  have hcop : Nat.Coprime d (R / d) := Nat.coprime_of_squarefree_mul
    (by simpa only [Nat.mul_div_cancel' hd] using hR)
  have heq := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [Nat.mul_div_cancel' hd] at heq
  have heq' : moebiusReal R = moebiusReal d * moebiusReal (R / d) := by
    unfold moebiusReal
    exact_mod_cast heq
  have hs : moebiusReal d ^ 2 = 1 := by
    unfold moebiusReal
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  calc
    moebiusReal (R / d) = moebiusReal (R / d) * 1 := by ring
    _ = moebiusReal (R / d) * moebiusReal d ^ 2 := by rw [hs]
    _ = (moebiusReal d * moebiusReal (R / d)) * moebiusReal d := by ring
    _ = moebiusReal R * moebiusReal d := by rw [← heq']

-- Complementary squarefree divisors exchange the cutoff and quotient horizon.
private theorem source_reflection {N l R : ℕ} (hN : 1 ≤ N) (hl : 1 ≤ l)
    (hR : Squarefree R) (hlo : l * N < R) (hhi : R ≤ (l + 1) * N) :
    sieveSeq N moebiusReal R = -moebiusReal R * sieveSeq l moebiusReal R := by
  have hR2 : 2 ≤ R := by nlinarith
  rw [sieveSeq_band_eq_sum_divisors_sub_quotients hlo hhi,
    sum_divisors_moebiusReal_eq_zero hR2, zero_sub, sieveSeq,
    Finset.sum_filter, neg_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ R
  · simp only [if_pos h, quotient_moebius hR h]
  · simp only [if_neg h, mul_zero]

noncomputable section

/-- Signed responses at the finite quotient states, together with zero. -/
def moebiusLinearHorizonAlphabet (B : ℕ) : Finset ℝ := by
  classical
  exact {0} ∪ (Icc 1 B).biUnion (fun l => (primorial l).divisors.biUnion
    (fun d => {sieveSeq l moebiusReal d, -sieveSeq l moebiusReal d}))

private theorem mem_sourceAlphabet (B : ℕ) (a : ℝ) :
    a ∈ moebiusLinearHorizonAlphabet B ↔ a = 0 ∨ ∃ l ∈ Icc 1 B,
      ∃ d ∈ (primorial l).divisors,
        a = sieveSeq l moebiusReal d ∨ a = -sieveSeq l moebiusReal d := by
  classical
  simp [moebiusLinearHorizonAlphabet]

private theorem one_mem_sourceAlphabet {B : ℕ} (hB : 1 ≤ B) :
    (1 : ℝ) ∈ moebiusLinearHorizonAlphabet B := by
  apply (mem_sourceAlphabet B 1).mpr
  right
  refine ⟨1, mem_Icc.mpr ⟨le_rfl, hB⟩, 1, ?_, Or.inl ?_⟩
  · exact Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt (primorial_pos _)⟩
  · symm
    simpa using sieveSeq_moebiusReal_eq_ite_of_le (N := 1) (m := 1) le_rfl le_rfl

-- The visible radical reduces every sample to a signed small-horizon response.
private theorem source_in_alphabet {B N k : ℕ} (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hk : 1 ≤ k) (hhi : k ≤ (B + 1) * N) :
    sieveSeq N moebiusReal k ∈ moebiusLinearHorizonAlphabet B := by
  let R := horizonRadicalState N k
  have hR : 0 < R := horizonRadicalState_pos N k
  have hRk : R ≤ k := Nat.le_of_dvd (by omega) (horizonRadicalState_dvd N k)
  have hsf : Squarefree R := horizonRadicalState_squarefree N k
  have heq : sieveSeq N moebiusReal R = sieveSeq N moebiusReal k :=
    sieveSeq_horizonRadicalState N k moebiusReal_eq_zero_of_not_squarefree
  rw [← heq]
  by_cases hsub : R ≤ N
  · rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hsub]
    split_ifs
    · exact one_mem_sourceAlphabet hB
    · exact (mem_sourceAlphabet B 0).mpr (Or.inl rfl)
  · let l := (R - 1) / N
    have hl : 1 ≤ l := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hlo : l * N < R := by
      have := Nat.div_mul_le_self (R - 1) N
      dsimp [l]
      omega
    have hupper : R ≤ (l + 1) * N := by
      have hmod := Nat.mod_lt (R - 1) (by omega : 0 < N)
      have hdiv := Nat.div_add_mod (R - 1) N
      dsimp [l]
      nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ R)]
    have hlB : l ≤ B := by nlinarith
    have hd : horizonRadicalState l R ∈ (primorial l).divisors :=
      Nat.mem_divisors.mpr ⟨horizonRadicalState_dvd_primorial l R,
        ne_of_gt (primorial_pos _)⟩
    have href := source_reflection hN hl hsf hlo hupper
    have hsmall := sieveSeq_horizonRadicalState l R moebiusReal_eq_zero_of_not_squarefree
    apply (mem_sourceAlphabet B _).mpr
    right
    refine ⟨l, mem_Icc.mpr ⟨hl, hlB⟩, horizonRadicalState l R, hd, ?_⟩
    rw [hsmall, href]
    have hne := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
    rcases ArithmeticFunction.moebius_eq_or R with hm | hm | hm
    · exact (hne hm).elim
    · right
      have hm' : moebiusReal R = 1 := by simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hm
      rw [hm']
      ring
    · left
      have hm' : moebiusReal R = -1 := by simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hm
      rw [hm']
      ring

private theorem source_prime_extension {l p : ℕ} (hp : p.Prime) (hlp : l < p)
    (d : ℕ) : sieveSeq l moebiusReal (d * p) = sieveSeq l moebiusReal d := by
  refine sieveSeq_mul_right_of_rough (N := l) (r := p) ?_ moebiusReal d
  intro q hq hql
  rcases (Nat.dvd_prime hp).mp hq with h | h
  · exact h
  · omega

-- A new large prime preserves the small-horizon response and flips its Möbius sign.
private theorem exists_source_prime_extension (l T d : ℕ) (hd : 1 ≤ d)
    (hsf : Squarefree d) : ∃ R : ℕ, T ≤ R ∧ Squarefree R ∧
      sieveSeq l moebiusReal R = sieveSeq l moebiusReal d ∧
      moebiusReal R = -moebiusReal d := by
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (l + T + d + 1)
  have hcop : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr (by
    intro h
    have := Nat.le_of_dvd (by omega : 0 < d) h
    omega)).symm
  refine ⟨d * p, by nlinarith, (Nat.squarefree_mul hcop).mpr ⟨hsf, hp.squarefree⟩,
    source_prime_extension hp (by omega) d, ?_⟩
  unfold moebiusReal
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

private theorem exists_source_band (l T R : ℕ) (hl : 1 ≤ l)
    (hR : l * (T + l + 1) + 1 ≤ R) :
    ∃ N : ℕ, T ≤ N ∧ 1 ≤ N ∧ l * N < R ∧ R ≤ (l + 1) * N := by
  let N := (R - 1) / l
  have hlN : T + l + 1 ≤ N :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by
      have hsub : l * (T + l + 1) ≤ R - 1 := by omega
      simpa only [Nat.mul_comm] using hsub)
  refine ⟨N, by omega, by omega, ?_, ?_⟩
  · have := Nat.div_mul_le_self (R - 1) l
    dsimp [N]
    nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ R)]
  · have hmod := Nat.mod_lt (R - 1) (by omega : 0 < l)
    have hdiv := Nat.div_add_mod (R - 1) l
    change R ≤ (l + 1) * ((R - 1) / l)
    dsimp [N] at hlN
    nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ R)]

-- One or two prime extensions realize both signs beyond any prescribed cutoff.
private theorem source_state_attainment {l d : ℕ} (hl : 1 ≤ l)
    (hd : d ∈ (primorial l).divisors) (T : ℕ) :
    (∃ N k : ℕ, T ≤ N ∧ 1 ≤ N ∧ 1 ≤ k ∧ k ≤ (l + 1) * N ∧
      sieveSeq N moebiusReal k = sieveSeq l moebiusReal d) ∧
    (∃ N k : ℕ, T ≤ N ∧ 1 ≤ N ∧ 1 ≤ k ∧ k ≤ (l + 1) * N ∧
      sieveSeq N moebiusReal k = -sieveSeq l moebiusReal d) := by
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (primorial_pos l)
  have hdsf : Squarefree d := (squarefree_primorial l).squarefree_of_dvd hdvd
  let K := l * (T + l + 1) + 1
  obtain ⟨R, hKR, hRsf, hsmallR, hmuR⟩ := exists_source_prime_extension l K d hd1 hdsf
  have hR1 : 1 ≤ R := by dsimp [K] at hKR; omega
  obtain ⟨S, hKS, hSsf, hsmallS, hmuS⟩ := exists_source_prime_extension l K R hR1 hRsf
  have hS1 : 1 ≤ S := by dsimp [K] at hKS; omega
  obtain ⟨N, hTN, hN1, hloR, hhiR⟩ := exists_source_band l T R hl hKR
  obtain ⟨M, hTM, hM1, hloS, hhiS⟩ := exists_source_band l T S hl hKS
  have hRval : sieveSeq N moebiusReal R = moebiusReal d * sieveSeq l moebiusReal d := by
    rw [source_reflection hN1 hl hRsf hloR hhiR, hmuR, hsmallR, neg_neg]
  have hSval : sieveSeq M moebiusReal S = -moebiusReal d * sieveSeq l moebiusReal d := by
    rw [source_reflection hM1 hl hSsf hloS hhiS, hmuS, hmuR, hsmallS, hsmallR]
    ring
  have hne := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hdsf
  rcases ArithmeticFunction.moebius_eq_or d with hm | hm | hm
  · exact (hne hm).elim
  · have hm' : moebiusReal d = 1 := by
      simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hm
    refine ⟨⟨N, R, hTN, hN1, hR1, hhiR, ?_⟩,
      ⟨M, S, hTM, hM1, hS1, hhiS, ?_⟩⟩
    · simpa [hm'] using hRval
    · simpa [hm'] using hSval
  · have hm' : moebiusReal d = -1 := by
      simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hm
    refine ⟨⟨M, S, hTM, hM1, hS1, hhiS, ?_⟩,
      ⟨N, R, hTN, hN1, hR1, hhiR, ?_⟩⟩
    · simpa [hm'] using hSval
    · simpa [hm'] using hRval

/-- Every sample in the fixed linear horizon belongs to the finite arithmetic alphabet. -/
theorem moebius_source_mem_linear_horizon_alphabet (B : ℕ) (N : ℕ+)
    (k : Fin ((B + 2) * (N : ℕ))) :
    sieveSeq N moebiusReal (k.val + 1) ∈ moebiusLinearHorizonAlphabet (B + 1) := by
  exact source_in_alphabet (by omega) N.property (by omega)
    (Nat.succ_le_of_lt k.isLt)

/-- Every alphabet value occurs at arbitrarily large cutoffs, and these are all possible values. -/
theorem moebius_linear_horizon_alphabet_iff_cofinal_source_value (B : ℕ) (a : ℝ) :
    a ∈ moebiusLinearHorizonAlphabet (B + 1) ↔ ∀ T : ℕ, ∃ N : ℕ+, T ≤ (N : ℕ) ∧
      ∃ k : Fin ((B + 2) * (N : ℕ)), sieveSeq N moebiusReal (k.val + 1) = a := by
  constructor
  · intro ha T
    rcases (mem_sourceAlphabet (B + 1) a).mp ha with hzero | ⟨l, hl, d, hd, ha⟩
    · subst a
      refine ⟨⟨T + 2, by omega⟩, by dsimp; omega, ⟨1, by dsimp; nlinarith⟩, ?_⟩
      change sieveSeq (T + 2) moebiusReal 2 = 0
      simpa using sieveSeq_moebiusReal_eq_ite_of_le (N := T + 2) (m := 2)
        (by omega) (by omega)
    · have hex : ∃ N k : ℕ, T ≤ N ∧ 1 ≤ N ∧ 1 ≤ k ∧ k ≤ (l + 1) * N ∧
          sieveSeq N moebiusReal k = a := by
        rcases ha with rfl | rfl
        · exact (source_state_attainment (mem_Icc.mp hl).1 hd T).1
        · exact (source_state_attainment (mem_Icc.mp hl).1 hd T).2
      obtain ⟨N, k, hTN, hN, hk, hbound, heq⟩ := hex
      have hhi : k ≤ (B + 2) * N := by nlinarith [(mem_Icc.mp hl).2]
      refine ⟨⟨N, by omega⟩, hTN, ⟨k - 1, by dsimp; omega⟩, ?_⟩
      change sieveSeq N moebiusReal (k - 1 + 1) = a
      simpa only [Nat.sub_add_cancel hk] using heq
  · intro h
    obtain ⟨N, _, k, hk⟩ := h 0
    rw [← hk]
    exact moebius_source_mem_linear_horizon_alphabet B N k

end
end GaloisForLFunctions.BezoutValuationIncidence
