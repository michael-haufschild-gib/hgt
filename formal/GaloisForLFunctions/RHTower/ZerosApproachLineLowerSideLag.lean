import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.WeilLagSingleBaseLowerSide

/-!
# Lower single-base lag bounds along infinitely many prime bases, given zeros approaching the line

At an attained top `β₀ > ½` of the real parts of the zeros, the lag values `Φ(m log b)` are
unbounded below unless some top ordinate `γ` is resonant for `b`, that is `γ log b ∈ 2πℤ`
(`exists_pow_integerLag_lt_of_attainedTop_nonresonant`).

* **One ordinate resonates with at most one prime** (`not_resonant_two_primes`).  If
  `γ log p = 2πk` and `γ log p' = 2πk'` with `γ ≠ 0`, then `|k'| log p = |k| log p'`, so
  `p^{|k'|} = p'^{|k|}` and `p = p'` by unique factorization.
* **Zeros approaching the line make the top level finite** (`finite_topLevel_of_zerosApproachLine`),
  so among infinitely many primes some prime is nonresonant for every top ordinate.

**Theorem** (`riemannHypothesis_iff_zerosApproachLine_and_primePow_integerLag_bddBelow`).  For every
infinite set `P` of primes, RH holds iff the zeros approach the line and, for every `p ∈ P`, the
lag values `Φ(m log p)`, `m ≥ 1`, are bounded below.

Together with the upper-side split
(`riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove`), both one-sided single-base
receivers are complete modulo the large-height rung: the upper side needs one base, the lower side
needs an infinite family of bases to escape resonance.
-/

open Complex Set

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-- **One nonzero ordinate resonates with at most one prime.** -/
theorem not_resonant_two_primes {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p')
    {γ : ℝ} (hγ : γ ≠ 0) {k k' : ℤ} (hk : γ * Real.log p = 2 * Real.pi * k)
    (hk' : γ * Real.log p' = 2 * Real.pi * k') : False := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlp' : 0 < Real.log p' := Real.log_pos (by exact_mod_cast hp'.one_lt)
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero] at hk
    exact (mul_ne_zero hγ hlp.ne') hk
  have hk'0 : k' ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_zero] at hk'
    exact (mul_ne_zero hγ hlp'.ne') hk'
  -- `k' log p = k log p'`
  have hcross : (k' : ℝ) * Real.log p = (k : ℝ) * Real.log p' := by
    have h1 : γ * ((k' : ℝ) * Real.log p) = γ * ((k : ℝ) * Real.log p') := by
      have : γ * Real.log p * k' = γ * Real.log p' * k := by
        rw [hk, hk']; ring
      linarith
    exact mul_left_cancel₀ hγ h1
  -- pass to absolute values
  have habs : (k'.natAbs : ℝ) * Real.log p = (k.natAbs : ℝ) * Real.log p' := by
    have h1 := congrArg abs hcross
    rw [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlp'] at h1
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    simpa only [Int.cast_abs] using h1
  have hpow : ((p ^ k'.natAbs : ℕ) : ℝ) = ((p' ^ k.natAbs : ℕ) : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp'0 : (0 : ℝ) < p' := by exact_mod_cast hp'.pos
    push_cast
    have h1 : Real.log ((p : ℝ) ^ k'.natAbs) = Real.log ((p' : ℝ) ^ k.natAbs) := by
      rw [Real.log_pow, Real.log_pow]; exact habs
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp0 _)) (Set.mem_Ioi.mpr (pow_pos hp'0 _)) h1
  have hnat : p ^ k'.natAbs = p' ^ k.natAbs := by exact_mod_cast hpow
  have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
  have hdvd : p' ∣ p ^ k'.natAbs := by
    rw [hnat]; exact dvd_pow_self p' hpos.ne'
  have := (Nat.prime_dvd_prime_iff_eq hp' hp).mp (hp'.dvd_of_dvd_pow hdvd)
  exact hne this.symm

/-- Zeros approaching the line leave only finitely many zeros right of `½ + h`, `h > 0`. -/
theorem finite_re_gt_of_zerosApproachLine (hZ : ZerosApproachLine) {h : ℝ} (hh : 0 < h) :
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite := by
  refine (finite_abs_im_gt_of_zerosApproachLine hZ hh).subset fun q hq => ?_
  simp only [mem_setOf_eq] at hq ⊢
  rw [spectral_im_eq, abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- **Zeros approaching the line make every level above the line finite.** -/
theorem finite_topLevel_of_zerosApproachLine (hZ : ZerosApproachLine) {β₀ : ℝ}
    (hβ : 1 / 2 < β₀) : (topLevel β₀).Finite := by
  refine (finite_re_gt_of_zerosApproachLine hZ (h := (β₀ - 1 / 2) / 2) (by linarith)).subset
    fun q hq => ?_
  have hq' : (q.1 : ℂ).re = β₀ := hq
  simp only [mem_setOf_eq]
  linarith

/-- **Among infinitely many primes one is nonresonant for a finite top level.** -/
theorem exists_mem_nonresonantTop {β₀ : ℝ} (hfin : (topLevel β₀).Finite) {P : Set ℕ}
    (hP : P.Infinite) (hPp : ∀ p ∈ P, p.Prime) : ∃ p ∈ P, NonresonantTop β₀ p := by
  classical
  -- the primes resonant with a given top copy form a subsingleton
  set R : XiZeroCopy → Set ℕ := fun q => {p | p.Prime ∧ ∃ k : ℤ,
    zeroOrdinate q * Real.log p = 2 * Real.pi * k} with hR
  have hsub : ∀ q, (R q).Subsingleton := by
    rintro q p ⟨hp, k, hk⟩ p' ⟨hp', k', hk'⟩
    by_contra hne
    exact not_resonant_two_primes hp hp' hne (zeroOrdinate_ne_zero' q) hk hk'
  have hbad : (⋃ q ∈ topLevel β₀, R q).Finite :=
    hfin.biUnion fun q _ => (hsub q).finite
  obtain ⟨p, hpP, hpbad⟩ := (hP.sdiff hbad).nonempty
  refine ⟨p, hpP, fun q hq k hk => hpbad ?_⟩
  exact Set.mem_biUnion hq ⟨hPp p hpP, k, hk⟩

/-- **RH splits into zeros approaching the line and lower lag bounds along infinitely many prime
bases.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_primePow_integerLag_bddBelow {P : Set ℕ}
    (hP : P.Infinite) (hPp : ∀ p ∈ P, p.Prime) :
    RiemannHypothesis ↔ ZerosApproachLine ∧
      ∀ p ∈ P, ∃ M : ℝ, ∀ m : ℕ, 1 ≤ m → M ≤ integerLag (p ^ m) := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_weilLagFunctionReal_bddBelow.mp hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH, fun p _ => ⟨-M, fun m _ => hM _⟩⟩
  · rintro ⟨hZ, hlow⟩
    by_contra hRH
    obtain ⟨β₀, hβ, htop⟩ := exists_attainedTop_of_zerosApproachLine hZ hRH
    obtain ⟨p, hpP, hres⟩ :=
      exists_mem_nonresonantTop (finite_topLevel_of_zerosApproachLine hZ hβ) hP hPp
    obtain ⟨M, hM⟩ := hlow p hpP
    exact not_attainedTop_nonresonant_of_forall_ge (hPp p hpP).two_le hM hβ hres htop

end

end RHTower
