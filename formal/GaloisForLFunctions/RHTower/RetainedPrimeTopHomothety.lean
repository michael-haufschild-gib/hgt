import GaloisForLFunctions.RHTower.RetainedPrimeSupportThreshold
import GaloisForLFunctions.RHTower.DivisorUnsignedChannelPositivity

/-!
# Full retained-label homothety and its initial sign chamber

The full retained coordinate is exactly the divisor source on multiples of
its prime product. General masked homothety preserves every clipped endpoint
and identifies this coordinate with a coprime arithmetic head. A coprime gap
gives an exact initial one-channel chamber and its Möbius orientation.
Complete directional witnesses and their synchronized prime-quotient parent
must extend beyond that chamber. These are aperture costs, not energy floors.
-/

noncomputable section
open Finset
namespace RHTower

private lemma image_prime (Q : Finset Nat.Primes) :
    ∀ p ∈ Q.image (fun q : Nat.Primes => (q : ℕ)), p.Prime := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
  exact q.property

/-- The full retained-label coordinate is exactly the source supported on multiples of its product. -/
theorem retainedPrimeFieldProfile_top_eq_multiples (Q : Finset Nat.Primes) (M : ℕ) :
    retainedPrimeFieldProfile Q M
      ⟨Q.image (fun p : Nat.Primes => (p : ℕ)), mem_powerset.mpr Subset.rfl⟩ =
      ∑ d ∈ (Icc 1 M).filter (fun d => (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) ∣ d),
        mobiusDivisorDilationChannel M d := by
  rw [retainedPrimeFieldProfile, sum_filter]
  apply sum_congr rfl
  intro d hd
  congr 1
  apply propext
  constructor
  · intro he
    have hval := congrArg Subtype.val he
    change d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)) =
      Q.image (fun p : Nat.Primes => (p : ℕ)) at hval
    have hsub : Q.image (fun p : Nat.Primes => (p : ℕ)) ⊆ d.primeFactors :=
      hval ▸ inter_subset_left
    exact (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd d)
  · intro hdiv
    have hfac := Nat.primeFactors_mono hdiv (by have := mem_Icc.mp hd; omega : d ≠ 0)
    rw [Nat.primeFactors_prod (image_prime Q)] at hfac
    apply Subtype.ext
    exact inter_eq_right.mpr hfac

/-- General clipped signed homothety keeps the complete shared-prime mask. -/
theorem mobiusDivisorDilationChannel_interpolation_masked (r M d : ℕ) (hr : 0 < r) :
    mobiusDivisorDilationChannel M (r*d) =
      Real.sqrt r * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        (if r.Coprime d then
          (1-divisorPrimeClipWeight M r)*mobiusDivisorDilationChannel (M/r) d +
            divisorPrimeClipWeight M r*mobiusDivisorDilationChannel (M/r+1) d
        else 0) := by
  by_cases hc : r.Coprime d
  · rw [if_pos hc, mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
      divisorUnsignedDilationChannel_prime_interpolation M r d hr,
      mobiusDivisorDilationChannel_eq_moebius_unsigned,
      mobiusDivisorDilationChannel_eq_moebius_unsigned]
    push_cast
    ring
  · have hm : ArithmeticFunction.moebius (r*d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hs => hc (Nat.coprime_of_squarefree_mul hs))
    simp [hc, mobiusDivisorDilationChannel_eq_moebius_unsigned, hm]

/-- The complete divisor-source head on cofactors coprime to the retained product. -/
def mobiusDivisorCoprimeHead (r N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, if r.Coprime d then mobiusDivisorDilationChannel N d else 0

/-- Extending the cofactor head by one index adds a zero terminal channel. -/
lemma mobiusDivisorCoprimeHead_succ_eq_sum (r N : ℕ) : mobiusDivisorCoprimeHead r (N+1) =
    ∑ d ∈ Icc 1 N, if r.Coprime d then mobiusDivisorDilationChannel (N+1) d else 0 := by
  rw [mobiusDivisorCoprimeHead, sum_Icc_succ_top (by omega : 1 ≤ N+1)]
  have hz : mobiusDivisorDilationChannel (N+1) (N+1) = 0 := by simp [mobiusDivisorDilationChannel]
  simp [hz]

/-- Exact full-label homothety, including the last clipped block and the coprime arithmetic head. -/
theorem retainedPrimeFieldProfile_top_interpolation (Q : Finset Nat.Primes) (M : ℕ) :
    let r := ∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p
    retainedPrimeFieldProfile Q M
      ⟨Q.image (fun p : Nat.Primes => (p : ℕ)), mem_powerset.mpr Subset.rfl⟩ =
      Real.sqrt r * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        ((1-divisorPrimeClipWeight M r)*mobiusDivisorCoprimeHead r (M/r) +
          divisorPrimeClipWeight M r*mobiusDivisorCoprimeHead r (M/r+1)) := by
  intro r
  have hr : 0 < r := prod_pos (fun p hp => (image_prime Q p hp).pos)
  rw [retainedPrimeFieldProfile_top_eq_multiples, sum_Icc_filter_dvd_reindex r M hr]
  rw [mobiusDivisorCoprimeHead_succ_eq_sum]
  unfold mobiusDivisorCoprimeHead
  simp only [mul_add, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [mobiusDivisorDilationChannel_interpolation_masked r M d hr]
  split_ifs <;> ring

/-- Before the next admissible coprime cofactor, the full retained coordinate
is exactly its first arithmetic channel, including the terminal endpoint. -/
theorem retainedPrimeFieldProfile_top_eq_channel_of_coprime_gap
    (Q : Finset Nat.Primes) (M q : ℕ)
    (hlo : (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) ≤ M)
    (hhi : M ≤ (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p)*q)
    (hgap : ∀ d : ℕ, 1 < d → d < q →
      ¬(∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p).Coprime d) :
    retainedPrimeFieldProfile Q M
      ⟨Q.image (fun p : Nat.Primes => (p : ℕ)), mem_powerset.mpr Subset.rfl⟩ =
      mobiusDivisorDilationChannel M (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) := by
  let r := ∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p
  have hr : 0 < r := prod_pos (fun p hp => (image_prime Q p hp).pos)
  rw [retainedPrimeFieldProfile_top_eq_multiples, sum_Icc_filter_dvd_reindex r M hr]
  have h1 : 1 ∈ Icc 1 (M/r) := mem_Icc.mpr ⟨le_rfl,
    (Nat.le_div_iff_mul_le hr).mpr (by simpa using hlo)⟩
  rw [sum_eq_single 1]
  · simp [r]
  · intro d hd hd1
    have hd' := mem_Icc.mp hd
    have hrd : r*d ≤ M := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hr).mp hd'.2
    by_cases hdq : d < q
    · have hc := hgap d (by omega) hdq
      have hm : ArithmeticFunction.moebius (r*d) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          (fun hs => hc (Nat.coprime_of_squarefree_mul hs))
      simp [mobiusDivisorDilationChannel_eq_moebius_unsigned, hm]
    · have hhi' : M ≤ r*q := hhi
      have he : r*d = M := by nlinarith
      rw [he]
      have hM0 : 0 < M := hr.trans_le hlo
      simp [mobiusDivisorDilationChannel, Icc_eq_empty_of_lt (show M-1<M by omega)]
  · exact fun hn => False.elim (hn h1)

/-- The full retained source keeps its initial Möbius orientation throughout
the entire coprime-gap chamber. -/
theorem retainedPrimeFieldProfile_top_initial_sign (Q : Finset Nat.Primes) (M q : ℕ)
    (hhi : M ≤ (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p)*q)
    (hgap : ∀ d : ℕ, 1 < d → d < q →
      ¬(∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p).Coprime d) :
    0 ≤ ((ArithmeticFunction.moebius (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) : ℤ) : ℝ) *
      retainedPrimeFieldProfile Q M
        ⟨Q.image (fun p : Nat.Primes => (p : ℕ)), mem_powerset.mpr Subset.rfl⟩ := by
  by_cases hM : M ≤ ∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p
  · rw [retainedPrimeFieldProfile_eq_zero_of_le_product Q M _ hM, mul_zero]
  · rw [retainedPrimeFieldProfile_top_eq_channel_of_coprime_gap Q M q (by omega) hhi hgap,
      mobiusDivisorDilationChannel_eq_moebius_unsigned]
    have hp := mul_nonneg (sq_nonneg
      (((ArithmeticFunction.moebius (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) : ℤ) : ℝ)))
      (divisorUnsignedDilationChannel_nonneg M (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p))
    nlinarith only [hp]

/-- Retaining every prime below q excludes every nontrivial coprime cofactor below q. -/
theorem retainedPrimeProduct_coprime_gap (Q : Finset Nat.Primes) (q : ℕ)
    (hQ : mobiusDivisorSelectionPrimes q ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)))
    (d : ℕ) (hd : 1 < d) (hdq : d < q) :
    ¬(∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p).Coprime d := by
  intro hc
  have hp := Nat.minFac_prime (by omega : d ≠ 1)
  have hpd := Nat.minFac_le (by omega : 0 < d)
  have hpS := hQ (mem_filter.mpr ⟨mem_range.mpr (hpd.trans_lt hdq), hp⟩)
  have hpr : d.minFac ∣ ∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p :=
    dvd_prod_of_mem id hpS
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hpr (Nat.minFac_dvd d))

/-- Complete directional control must leave the full retained coordinate's
initial sign chamber, not merely reach its first nonzero source index. -/
theorem retainedPrimeField_witness_reaches_coprime_gap
    (Q : Finset Nat.Primes) (K : Finset ℕ) (q : ℕ)
    (hK : ∀ z : retainedPrimeFieldCoordinates Q, z ≠ 0 →
      ∃ M ∈ K, 0 < retainedPrimeFieldPairing Q z M)
    (hgap : ∀ d : ℕ, 1 < d → d < q →
      ¬(∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p).Coprime d) :
    ∃ M ∈ K, (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p)*q < M := by
  let R : retainedPrimeFieldIndex Q :=
    ⟨Q.image (fun p : Nat.Primes => (p : ℕ)), mem_powerset.mpr Subset.rfl⟩
  let a : ℝ := ((ArithmeticFunction.moebius (∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p) : ℤ) : ℝ)
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact_mod_cast (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      (GibbsGas.squarefree_prod_primes (image_prime Q)))
  let z : retainedPrimeFieldCoordinates Q := Pi.single R (-a)
  have hz : z ≠ 0 := by
    intro he
    have h := congrFun he R
    simp [z, ha] at h
  obtain ⟨M, hM, hm⟩ := hK z hz
  rw [retainedPrimeFieldPairing_eq_sum_profile] at hm
  have hm' : 0 < (-a) * retainedPrimeFieldProfile Q M R := by
    simpa [z, Pi.single_apply] using hm
  refine ⟨M, hM, ?_⟩
  by_contra hn
  have hs := retainedPrimeFieldProfile_top_initial_sign Q M q (by omega) hgap
  change 0 ≤ a * retainedPrimeFieldProfile Q M R at hs
  nlinarith

/-- Synchronizing complete retained-field witnesses as prime quotients forces
an explicit parent aperture beyond twice the entire initial sign chamber. -/
theorem retainedPrimeField_parent_aperture_gt (Q : Finset Nat.Primes)
    (K : Finset ℕ) (q M : ℕ) (prime : ℕ → ℕ)
    (hK : ∀ z : retainedPrimeFieldCoordinates Q, z ≠ 0 →
      ∃ k ∈ K, 0 < retainedPrimeFieldPairing Q z k)
    (hQ : mobiusDivisorSelectionPrimes q ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)))
    (hcopy : ∀ k ∈ K, (prime k).Prime ∧ M / prime k = k) :
    2 * ((∏ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), p)*q) < M := by
  obtain ⟨k, hk, hlt⟩ := retainedPrimeField_witness_reaches_coprime_gap Q K q hK
    (retainedPrimeProduct_coprime_gap Q q hQ)
  obtain ⟨hp, hquot⟩ := hcopy k hk
  have hdiv := Nat.div_mul_le_self M (prime k)
  rw [hquot] at hdiv
  have h2 := hp.two_le
  nlinarith

end RHTower
