import GaloisForLFunctions.RHTower.DivisorUnsignedGlobalEnvelope
import GaloisForLFunctions.RHTower.MobiusDivisorQuotientWindowOrder
import GaloisForLFunctions.RHTower.DivisorSmoothSquareMaximum
import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeReserve

/-!
# Cofinal primes compatible with every prescribed initial prime

Actual primes are produced independently of the prescribed partner. Every
subset of each pair stays below the original complete source diagonal at
every integer cutoff. The proof retains every cofactor and clipped channel.
It does not assert extension from a nonempty processed core or exhaustion.
-/

noncomputable section
open Finset
namespace RHTower

private lemma near_parent_block {a b c e s : ℝ} (hs : 0 ≤ s)
    (ha : s/16 ≤ a) (hb : s/16 ≤ b) (hab : |a-b| ≤ s/500)
    (hc0 : 0 ≤ c) (he0 : 0 ≤ e) (hc : c ≤ (3/5)*s) (he : e ≤ (3/5)*s) :
    (a-b-c+e)^(2 : ℕ) ≤ a^(2 : ℕ)+b^(2 : ℕ)+c^(2 : ℕ)+e^(2 : ℕ) := by
  have hce : |c-e| ≤ (3/5)*s := abs_le.mpr ⟨by linarith,by linarith⟩
  have hprod := mul_le_mul hab hce (abs_nonneg _) (by positivity : 0 ≤ s/500)
  rw [← abs_mul] at hprod
  have hcross := (abs_le.mp hprod).1
  have hab0 := mul_le_mul ha hb (by positivity : 0 ≤ s/16) (by linarith : 0 ≤ a)
  have hce0 := mul_nonneg hc0 he0
  nlinarith only [hcross,hab0,hce0,sq_nonneg s]

private lemma separated_blocks :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M p q d : ℕ, 0 < p → 0 < d → T*p ≤ q →
      (divisorUnsignedDilationChannel M d-
        divisorUnsignedDilationChannel M (p*d)-
        divisorUnsignedDilationChannel M (q*d)+
        divisorUnsignedDilationChannel M (p*(q*d)))^(2 : ℕ) ≤
      (divisorUnsignedDilationChannel M d)^(2 : ℕ)+
        (divisorUnsignedDilationChannel M (p*d))^(2 : ℕ)+
        (divisorUnsignedDilationChannel M (q*d))^(2 : ℕ)+
        (divisorUnsignedDilationChannel M (p*(q*d)))^(2 : ℕ) := by
  obtain ⟨T,hT,hmean⟩ := exists_divisorUnsignedDilationChannel_uniform_mean_error
    (1/1000) (by norm_num)
  refine ⟨T,hT,fun M p q d hp hd hq => ?_⟩
  let c₀ := Real.log (2*Real.pi)/2-Real.eulerMascheroniConstant-1/4
  have hc₀ : (1/12:ℝ) < c₀ := by
    have h := divisorHyperbolaSmoothMean_gt_one_sixth
    dsimp [c₀,divisorHyperbolaSmoothMean] at *
    linarith
  have hs := Real.sqrt_nonneg (M:ℝ)
  have hpd : 0 < p*d := Nat.mul_pos hp hd
  by_cases hlarge : T ≤ M/(p*d)
  · have hmul : T*(p*d) ≤ M := (Nat.le_div_iff_mul_le hpd).mp hlarge
    have hTd : T*d ≤ M := by
      have hp1 : 1 ≤ p := hp
      have hdp : d ≤ p*d := by simpa using Nat.mul_le_mul_right d hp1
      exact (Nat.mul_le_mul_left T hdp).trans hmul
    have hA := hmean M d hd ((Nat.le_div_iff_mul_le hd).mpr hTd)
    have hB := hmean M (p*d) hpd hlarge
    change |divisorUnsignedDilationChannel M d-c₀*Real.sqrt M| ≤ _ at hA
    change |divisorUnsignedDilationChannel M (p*d)-c₀*Real.sqrt M| ≤ _ at hB
    obtain ⟨hAl,hAu⟩ := abs_le.mp hA
    obtain ⟨hBl,hBu⟩ := abs_le.mp hB
    have hc := mul_le_mul_of_nonneg_right hc₀.le hs
    apply near_parent_block hs
    · linarith
    · linarith
    · exact abs_le.mpr ⟨by linarith,by linarith⟩
    · exact divisorUnsignedDilationChannel_nonneg M (q*d)
    · exact divisorUnsignedDilationChannel_nonneg M (p*(q*d))
    · exact divisorUnsignedDilationChannel_le_three_fifths_sqrt M (q*d)
    · exact divisorUnsignedDilationChannel_le_three_fifths_sqrt M (p*(q*d))
  · have hM : M < T*(p*d) := (Nat.div_lt_iff_lt_mul hpd).mp (by omega)
    have hqd : T*(p*d) ≤ q*d := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right d hq
    have hqp : q*d ≤ p*(q*d) := by simpa using Nat.mul_le_mul_right (q*d) hp
    have hz (r : ℕ) (hr : M < r) : divisorUnsignedDilationChannel M r = 0 := by
      simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1 < r)]
    rw [hz _ (hM.trans_le hqd),hz _ ((hM.trans_le hqd).trans_le hqp)]
    simp only [sub_zero,add_zero,zero_pow (by omega : (2:ℕ) ≠ 0)]
    nlinarith only [mul_nonneg (divisorUnsignedDilationChannel_nonneg M d)
      (divisorUnsignedDilationChannel_nonneg M (p*d))]

private lemma singleton_le (M p : ℕ) (hp : p.Prime) :
    mobiusDivisorSelectionEnergy M {p} ≤ mobiusDivisorSelectionEnergy M ∅ := by
  have h := sum_mobiusDivisorPrimePair_sq_le hp M
  rwa [← mobiusDivisorSelectionEnergy_singleton_eq_primePair M hp,
    ← mobiusDivisorSelectionEnergy_empty] at h

private lemma inactive_insert (M p : ℕ) (P : Finset ℕ) (hp : M ≤ p) :
    mobiusDivisorSelectionEnergy M (insert p P) = mobiusDivisorSelectionEnergy M P := by
  unfold mobiusDivisorSelectionEnergy subsetLabelEnergy
  apply sum_congr rfl
  intro R _
  change (mobiusDivisorSelectionFibre M (insert p P) R)^(2 : ℕ) =
    (mobiusDivisorSelectionFibre M P R)^(2 : ℕ)
  have h := mobiusDivisorSelectionFibre_union_inactive M P {p} R (by simpa using hp)
  simpa only [union_singleton] using congrArg (fun x : ℝ => x^(2 : ℕ)) h

private lemma separated_pair :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ M p q : ℕ, p.Prime → q.Prime → p ≠ q → T*p ≤ q →
      mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ := by
  obtain ⟨T,hT,hblocks⟩ := separated_blocks
  refine ⟨T,hT,fun M p q hp hq hpq hsep => ?_⟩
  by_cases hpM : p < M
  · by_cases hqM : q < M
    · rw [mobiusDivisorSelectionEnergy_two_primes_eq_blocks M p q hpq,
        mobiusDivisorSelectionEnergy_empty_eq_two_prime_blocks M hp hq hpM hqM hpq]
      apply sum_le_sum
      intro R hR
      have hqR : q ∉ R := by
        intro h
        exact (mem_erase.mp (mem_powerset.mp hR h)).1 rfl
      have hpR : p ∉ R := by
        intro h
        exact (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR h)).2).1 rfl
      have hpr : ∀ r ∈ R,r.Prime := by
        intro r hr
        exact (mem_filter.mp (mem_erase.mp (mem_erase.mp (mem_powerset.mp hR hr)).2).2).2
      have hpi : ∀ r ∈ insert p R,r.Prime := by simpa using And.intro hp hpr
      have hqi : ∀ r ∈ insert q R,r.Prime := by simpa using And.intro hq hpr
      have hpqi : ∀ r ∈ insert p (insert q R),r.Prime := by simpa using And.intro hp hqi
      rw [mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hpr,
        mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert p R) hpi,
        mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert q R) hqi,
        mobiusDivisorOrientedFibre_empty_eq_unsigned_product (insert p (insert q R)) hpqi]
      simp only [prod_insert hpR,prod_insert hqR,
        prod_insert (show p ∉ insert q R by simp [hpq,hpR])]
      exact hblocks M p q (∏ r ∈ R,r) hp.pos (prod_pos (fun r hr => (hpr r hr).pos)) hsep
    · rw [inactive_insert M q {p} (by omega)]
      exact singleton_le M p hp
  · rw [show (insert q {p} : Finset ℕ) = insert p {q} by ext r; simp [or_comm],
      inactive_insert M p {q} (by omega)]
    exact singleton_le M q hq

private lemma universal_partner_threshold :
    ∃ B : ℕ, ∀ M p q : ℕ, p.Prime → q.Prime → p ≠ q → B ≤ q →
      mobiusDivisorSelectionEnergy M (insert q {p}) ≤ mobiusDivisorSelectionEnergy M ∅ := by
  obtain ⟨T,hT,hsep⟩ := separated_pair
  obtain ⟨P₀,hlarge⟩ := exists_mobiusDivisorSelectionEnergy_two_large_primes_le_empty
  refine ⟨T*(P₀+1),fun M p q hp hq hpq hB => ?_⟩
  by_cases hp₀ : P₀ ≤ p
  · have hq₀ : P₀ ≤ q := by
      have h := Nat.mul_le_mul_right (P₀+1) hT
      omega
    by_cases hpM : p < M
    · by_cases hqM : q < M
      · exact hlarge M p q hp hq hp₀ hq₀ hpM hqM hpq
      · rw [inactive_insert M q {p} (by omega)]
        exact singleton_le M p hp
    · rw [show (insert q {p} : Finset ℕ) = insert p {q} by ext r; simp [or_comm],
        inactive_insert M p {q} (by omega)]
      exact singleton_le M q hq
  · exact hsep M p q hp hq hpq ((Nat.mul_le_mul_left T (by omega : p ≤ P₀+1)).trans hB)

/-- Actual cofinal prime partners, each compatible with every prescribed initial
prime. Both orders and every intermediate subset obey the original complete
energy ceiling at every integer cutoff, without a supplied channel comparison. -/
theorem exists_mobiusDivisorUniversalInitialPrimePartners :
    ∃ q : ℕ → ℕ, ∀ n : ℕ, n < q n ∧ (q n).Prime ∧
      ∀ p : ℕ, p.Prime → ∀ M : ℕ, ∀ P : Finset ℕ, P ⊆ {p,q n} →
        mobiusDivisorSelectionEnergy M P ≤ mobiusDivisorSelectionEnergy M ∅ := by
  classical
  obtain ⟨B,hB⟩ := universal_partner_threshold
  have hex (n : ℕ) : ∃ q : ℕ, max B (n+1) ≤ q ∧ q.Prime :=
    Nat.exists_infinite_primes (max B (n+1))
  choose q hq hprime using hex
  refine ⟨q,fun n => ⟨by have := (le_max_right B (n+1)).trans (hq n); omega,hprime n,?_⟩⟩
  intro p hp M P hP
  by_cases hpp : p ∈ P
  · by_cases hqp : q n ∈ P
    · have he : P = insert (q n) {p} := by
        ext r
        constructor
        · intro hr
          simpa only [mem_insert,mem_singleton,or_comm] using hP hr
        · intro hr
          rcases mem_insert.mp hr with hr|hr
          · simpa only [hr] using hqp
          · simpa only [mem_singleton.mp hr] using hpp
      rw [he]
      by_cases hpq : p = q n
      · subst p
        simpa using singleton_le M (q n) (hprime n)
      · exact hB M p (q n) hp (hprime n) hpq ((le_max_left _ _).trans (hq n))
    · have he : P = {p} := by
        ext r
        constructor
        · intro hr
          have h := hP hr
          simp only [mem_insert,mem_singleton] at h
          rcases h with h|h
          · exact mem_singleton.mpr h
          · exact False.elim (hqp (h ▸ hr))
        · intro hr
          simpa only [mem_singleton.mp hr] using hpp
      rw [he]
      exact singleton_le M p hp
  · by_cases hqp : q n ∈ P
    · have he : P = {q n} := by
        ext r
        constructor
        · intro hr
          have h := hP hr
          simp only [mem_insert,mem_singleton] at h
          rcases h with h|h
          · exact False.elim (hpp (h ▸ hr))
          · exact mem_singleton.mpr h
        · intro hr
          simpa only [mem_singleton.mp hr] using hqp
      rw [he]
      exact singleton_le M (q n) (hprime n)
    · have he : P = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro r hr
        have h := hP hr
        simp only [mem_insert,mem_singleton] at h
        exact h.elim (fun h => hpp (h ▸ hr)) (fun h => hqp (h ▸ hr))
      rw [he]

end RHTower
