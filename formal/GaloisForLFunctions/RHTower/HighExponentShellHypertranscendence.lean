import GaloisForLFunctions.RHTower.HighExponentShellZeroFree
import GaloisForLFunctions.RHTower.MFreeTower
import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon
import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionMatroid
import GaloisForLFunctions.HTGeometry.PrimeClockAnalyticEulerCompletion
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances
import GaloisForLFunctions.HTGeometry.ZetaUpperEndHypertranscendence
import GaloisForLFunctions.HTGeometry.AffineBaseJetGauge
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Hypertranscendence and exact fusion of the high-exponent shell family

The largest-prime-exponent shells give a positive, pairwise disjoint coefficient partition of
the Riemann-zeta Dirichlet series.  This module proves a complementary finite/infinite law:

* all positive shells fuse coefficientwise to the zeta stream minus its constant term;
* every finite jet rectangle of distinct shell levels is algebraically independent;
* zeta itself and all shells of exponent at least two are jointly differentially independent
  over the actual rational-coordinate field `ℂ(s)`;
* after adjoining zeta and all its derivatives, the adjacent reciprocal-dilation multipliers
  remain jointly differentially independent for every exponent at least two.

The proof uses the total prime-factor count `Ω` as an associated grading.  A level-`m` shell has
no coefficient below grade `m`; after one selected-prime derivative, its lowest grade is `m-1`
and is supported at one pure prime power.  The resulting lowest-layer Jacobian is a prime-log
Vandermonde block.  All mixed-prime tail terms occur in higher grade and cannot cancel it.
-/

open scoped BigOperators ArithmeticFunction.Omega Differential
  UpperEndDifferentialInstances UpperEndComplexTowerInstances

namespace RHTower

open ArithmeticFunction Matrix
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A nonzero shell coefficient has at least `m` prime factors, counted with multiplicity. -/
theorem shellIndicator_cardFactors_lower {m n : ℕ}
    (h : shellIndicator m n ≠ 0) : m ≤ Ω n := by
  have h1 : shellIndicator m n = 1 :=
    (shellIndicator_eq_zero_or_one m n).resolve_left h
  obtain ⟨hfree, hnot⟩ := (shellIndicator_eq_one_iff m n).mp h1
  rw [MFree] at hnot
  push Not at hnot
  obtain ⟨p, hp, hpdvd⟩ := hnot
  obtain ⟨k, hk⟩ := hpdvd
  have hn0 : n ≠ 0 := by
    intro hn
    apply not_mFree_zero (m + 1)
    simpa [hn] using hfree
  have hp0 : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    simp at hk
    exact hn0 hk
  have hΩ := cardFactors_mul hp0 hk0
  rw [← hk, cardFactors_apply_prime_pow hp] at hΩ
  omega

/-- Equality in the shell grade bound characterizes a pure prime power. -/
theorem shellIndicator_eq_prime_pow_of_cardFactors_eq {m n : ℕ}
    (h : shellIndicator m n ≠ 0) (hΩ : Ω n = m) :
    ∃ p : Nat.Primes, n = (p : ℕ) ^ m := by
  have h1 : shellIndicator m n = 1 :=
    (shellIndicator_eq_zero_or_one m n).resolve_left h
  obtain ⟨hfree, hnot⟩ := (shellIndicator_eq_one_iff m n).mp h1
  rw [MFree] at hnot
  push Not at hnot
  obtain ⟨p, hp, hpdvd⟩ := hnot
  obtain ⟨k, hk⟩ := hpdvd
  have hn0 : n ≠ 0 := by
    intro hn
    apply not_mFree_zero (m + 1)
    simpa [hn] using hfree
  have hp0 : p ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    simp at hk
    exact hn0 hk
  have hmul := cardFactors_mul hp0 hk0
  rw [← hk, hΩ, cardFactors_apply_prime_pow hp] at hmul
  have hΩk : Ω k = 0 := by omega
  have hk1 : k = 1 := by
    rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp hΩk with hkz | hko
    · exact False.elim (hk0 hkz)
    · exact hko
  refine ⟨⟨p, hp⟩, ?_⟩
  simpa [hk1] using hk

/-- The shell indicators telescope through every finite range of exponent levels. -/
theorem sum_range_shellIndicator (M n : ℕ) :
    ∑ m ∈ Finset.range M, shellIndicator (m + 1) n =
      mFreeIndicator (M + 1) n - mFreeIndicator 1 n := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, shellIndicator_apply]
      ring

/-- Every positive integer is free of prime powers one degree above its total prime-factor
count. -/
theorem mFree_cardFactors_succ {n : ℕ} (hn : n ≠ 0) :
    MFree (Ω n + 1) n := by
  intro p hp hpdvd
  obtain ⟨k, hk⟩ := hpdvd
  have hp0 : p ^ (Ω n + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    simp at hk
    exact hn hk
  have hΩ := cardFactors_mul hp0 hk0
  rw [← hk, cardFactors_apply_prime_pow hp] at hΩ
  omega

/-- Complex arithmetic-function realization of one high-exponent shell. -/
def complexShellIndicator (m : ℕ) : ArithmeticFunction ℂ :=
  (shellIndicator m : ArithmeticFunction ℂ)

@[simp] theorem complexShellIndicator_apply (m n : ℕ) :
    complexShellIndicator m n = (shellIndicator m n : ℂ) := rfl

/-- **Exact infinite shell fusion.** Pointwise in the coefficient index, all positive
largest-exponent shells sum to the zeta stream with its constant term removed. -/
theorem tsum_complexShellIndicator (n : ℕ) :
    (∑' m : ℕ, complexShellIndicator (m + 1) n) =
      zetaArith n - (1 : ArithmeticFunction ℂ) n := by
  rw [tsum_eq_sum (s := Finset.range (Ω n))]
  · change (∑ m ∈ Finset.range (Ω n), (shellIndicator (m + 1) n : ℂ)) =
      zetaArith n - (1 : ArithmeticFunction ℂ) n
    rw [← Int.cast_sum, sum_range_shellIndicator]
    by_cases hn : n = 0
    · subst n
      simp
    · rw [mFreeIndicator_apply, if_pos (mFree_cardFactors_succ hn),
        mFreeIndicator_one]
      simp [zetaArith_apply, hn, ArithmeticFunction.one_apply]
  · intro m hm
    by_contra hnonzero
    have hshell : shellIndicator (m + 1) n ≠ 0 := by
      intro hzero
      apply hnonzero
      simp [complexShellIndicator_apply, hzero]
    have hlower := shellIndicator_cardFactors_lower hshell
    have hmge : Ω n ≤ m := by simpa using hm
    omega

/-- The unified zeta/shell source: level one is the all-ones zeta stream, while every other
positive level is the corresponding largest-prime-exponent shell. -/
def zetaShellArithmetic (m : ℕ) : ArithmeticFunction ℂ :=
  if m = 1 then zetaArith else complexShellIndicator m

@[simp]
theorem zetaShellArithmetic_one :
    zetaShellArithmetic 1 = zetaArith := by
  simp [zetaShellArithmetic]

theorem zetaShellArithmetic_eq_shell {m : ℕ} (hm : m ≠ 1) :
    zetaShellArithmetic m = complexShellIndicator m := by
  simp [zetaShellArithmetic, hm]

/-- On grade zero, a selected prime derivative of a zeta jet is the point mass at one. -/
theorem primeDeriv_rotatedZetaJet_eq_pointMass_of_cardFactors_eq_zero
    (q : Nat.Primes) (k n : ℕ) (hΩ : Ω n = 0) :
    primeDeriv q.1 (rotatedLogArithmeticJet k zetaArith) n =
      arithmeticPointMass 1 (rotatedPrimeLogClock q ^ k) n := by
  rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp hΩ with hn | hn
  · subst n
    simp
  · subst n
    rw [primeDeriv_apply, rotatedLogArithmeticJet_apply, zetaArith_apply,
      arithmeticPointMass_apply_self one_ne_zero]
    simp only [one_mul, if_neg q.2.ne_zero, Nat.Prime.factorization_self q.2]
    simp [rotatedPrimeLogClock, primeLogClock]

/-- The selected prime derivative of a shell jet has no coefficient below grade `m-1`. -/
theorem primeDeriv_rotatedShellJet_eq_zero_of_cardFactors_lt
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n < m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (complexShellIndicator m)) n = 0 := by
  rw [primeDeriv_apply]
  by_cases hn : n = 0
  · subst n
    simp
  have hnq0 : n * q.1 ≠ 0 := mul_ne_zero hn q.2.ne_zero
  by_cases hshell : shellIndicator m (n * q.1) = 0
  · simp [rotatedLogArithmeticJet_apply, complexShellIndicator_apply, hshell]
  have hlower := shellIndicator_cardFactors_lower hshell
  have hmul := cardFactors_mul hn q.2.ne_zero
  rw [cardFactors_apply_prime q.2] at hmul
  rw [hmul] at hlower
  have : m - 1 ≤ Ω n := by omega
  exact False.elim (by omega)

/-- On its lowest grade, the selected prime derivative of a shell jet is one point mass. -/
theorem primeDeriv_rotatedShellJet_eq_pointMass_of_cardFactors_eq
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n = m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (complexShellIndicator m)) n =
      arithmeticPointMass (q.1 ^ (m - 1))
        ((m : ℂ) * (((m : ℂ) * rotatedPrimeLogClock q) ^ k)) n := by
  by_cases htarget : n = q.1 ^ (m - 1)
  · subst n
    rw [primeDeriv_apply]
    have hpow : q.1 ^ (m - 1) * q.1 = q.1 ^ m := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow, rotatedLogArithmeticJet_apply, complexShellIndicator_apply]
    have hshell : shellIndicator m (q.1 ^ m) = 1 := by
      rw [shellIndicator_apply, mFreeIndicator_apply_prime_pow (Nat.succ_ne_zero m) q.2,
        mFreeIndicator_apply_prime_pow hm.ne' q.2]
      simp
    rw [hshell, Nat.Prime.factorization_pow q.2,
      arithmeticPointMass_apply_self (pow_ne_zero _ q.2.ne_zero)]
    simp only [Finsupp.single_eq_same, Int.cast_one, mul_one]
    have hlog : (Real.log ((q.1 ^ m : ℕ) : ℝ) : ℂ) =
        (m : ℂ) * (Real.log q.1 : ℂ) := by
      rw [show ((q.1 ^ m : ℕ) : ℝ) = (q.1 : ℝ) ^ m by norm_num, Real.log_pow]
      exact_mod_cast rfl
    rw [hlog]
    simp only [rotatedPrimeLogClock, primeLogClock]
    ring
  · rw [arithmeticPointMass_apply_of_ne (pow_ne_zero _ q.2.ne_zero) htarget]
    rw [primeDeriv_apply]
    by_cases hn : n = 0
    · subst n
      simp
    by_cases hshell : shellIndicator m (n * q.1) = 0
    · simp [rotatedLogArithmeticJet_apply, complexShellIndicator_apply, hshell]
    exfalso
    have hmulΩ := cardFactors_mul hn q.2.ne_zero
    rw [cardFactors_apply_prime q.2, hΩ] at hmulΩ
    have hΩshell : Ω (n * q.1) = m := by omega
    obtain ⟨p, hpure⟩ :=
      shellIndicator_eq_prime_pow_of_cardFactors_eq hshell hΩshell
    have hqdvd : q.1 ∣ p.1 ^ m := by
      rw [← hpure]
      exact ⟨n, by ring⟩
    have hpq : q = p := by
      apply Subtype.ext
      exact Nat.prime_eq_prime_of_dvd_pow q.2 p.2 hqdvd
    subst p
    apply htarget
    apply Nat.eq_of_mul_eq_mul_right q.2.pos
    calc
      n * q.1 = q.1 ^ m := hpure
      _ = q.1 ^ (m - 1) * q.1 := by
        rw [← pow_succ]
        congr 1
        omega

/-- Every unified zeta/shell jet has no selected-prime coefficient below its level minus one. -/
theorem primeDeriv_rotatedZetaShellJet_eq_zero_of_cardFactors_lt
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n < m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (zetaShellArithmetic m)) n = 0 := by
  by_cases hm1 : m = 1
  · omega
  · rw [zetaShellArithmetic_eq_shell hm1]
    exact primeDeriv_rotatedShellJet_eq_zero_of_cardFactors_lt hm q k n hΩ

/-- On its lowest grade, every unified zeta/shell jet is the same prime-ray point-mass model. -/
theorem primeDeriv_rotatedZetaShellJet_eq_pointMass_of_cardFactors_eq
    {m : ℕ} (hm : 0 < m) (q : Nat.Primes) (k n : ℕ)
    (hΩ : Ω n = m - 1) :
    primeDeriv q.1 (rotatedLogArithmeticJet k (zetaShellArithmetic m)) n =
      arithmeticPointMass (q.1 ^ (m - 1))
        ((m : ℂ) * (((m : ℂ) * rotatedPrimeLogClock q) ^ k)) n := by
  by_cases hm1 : m = 1
  · subst m
    simp only [zetaShellArithmetic_one, Nat.reduceSubDiff, pow_zero,
      Nat.cast_one, one_mul]
    exact primeDeriv_rotatedZetaJet_eq_pointMass_of_cardFactors_eq_zero q k n
      (by simpa using hΩ)
  · rw [zetaShellArithmetic_eq_shell hm1]
    exact primeDeriv_rotatedShellJet_eq_pointMass_of_cardFactors_eq hm q k n hΩ

/-- `Ω` is additive on a finite product of positive integers. -/
theorem cardFactors_finset_prod
    {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    Ω (∏ i ∈ s, a i) = ∑ i ∈ s, Ω (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        cardFactors_mul (ha i (Finset.mem_insert_self i s))]
      · rw [ih]
        intro j hj
        exact ha j (Finset.mem_insert_of_mem hj)
      · exact Finset.prod_ne_zero_iff.mpr fun j hj =>
          ha j (Finset.mem_insert_of_mem hj)

/-- Equality of the lowest `Ω`-graded layers forces equality of the determinant coefficient at
the matching total grade. -/
theorem arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer
    (q N : ℕ) (e : Fin q → ℕ)
    (M P : Matrix (Fin q) (Fin q) (ArithmeticFunction ℂ))
    (hN0 : N ≠ 0) (hΩN : Ω N = ∑ j, e j)
    (hMzero : ∀ i j n, Ω n < e j → M i j n = 0)
    (hPzero : ∀ i j n, Ω n < e j → P i j n = 0)
    (hlayer : ∀ i j n, Ω n = e j → M i j n = P i j n) :
    M.det N = P.det N := by
  rw [GaloisForLFunctions.arithmeticFunction_det_apply,
    GaloisForLFunctions.arithmeticFunction_det_apply]
  apply Fintype.sum_congr
  intro d
  have hfactor0 : ∀ j, d.factors j ≠ 0 := by
    intro j
    exact (d.factor_pos (Nat.pos_of_ne_zero hN0) j).ne'
  have hΩsum : (∑ j, Ω (d.factors j)) = ∑ j, e j := by
    calc
      (∑ j, Ω (d.factors j)) =
          Ω (∏ j, d.factors j) := by
            symm
            simpa using cardFactors_finset_prod Finset.univ d.factors
              (fun j _ => hfactor0 j)
      _ = Ω N := by rw [d.prod_factors]
      _ = ∑ j, e j := hΩN
  by_cases hall : ∀ j, Ω (d.factors j) = e j
  · congr 1
    funext i j
    exact hlayer i j (d.factors j) (hall j)
  · have hexlt : ∃ j, Ω (d.factors j) < e j := by
      by_contra hnone
      simp only [not_exists, not_lt] at hnone
      obtain ⟨j, hj⟩ := not_forall.mp hall
      have hjlt : e j < Ω (d.factors j) := lt_of_le_of_ne
        (hnone j) (Ne.symm hj)
      have hsumlt :
          (∑ j, e j) < ∑ j, Ω (d.factors j) := by
        apply Finset.sum_lt_sum
        · intro i hi
          exact hnone i
        · exact ⟨j, Finset.mem_univ j, hjlt⟩
      rw [hΩsum] at hsumlt
      exact (Nat.lt_irrefl _) hsumlt
    obtain ⟨j, hj⟩ := hexlt
    rw [Matrix.det_eq_zero_of_column_eq_zero j
      (fun i => hMzero i j (d.factors j) hj)]
    rw [Matrix.det_eq_zero_of_column_eq_zero j
      (fun i => hPzero i j (d.factors j) hj)]

/-- Arbitrary finite-index form of the lowest-layer determinant coefficient law. -/
theorem arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (e : ι → ℕ)
    (M P : Matrix ι ι (ArithmeticFunction ℂ))
    (hN0 : N ≠ 0) (hΩN : Ω N = ∑ j, e j)
    (hMzero : ∀ i j n, Ω n < e j → M i j n = 0)
    (hPzero : ∀ i j n, Ω n < e j → P i j n = 0)
    (hlayer : ∀ i j n, Ω n = e j → M i j n = P i j n) :
    M.det N = P.det N := by
  classical
  let E : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eF : Fin (Fintype.card ι) → ℕ := fun i => e (E.symm i)
  let MF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι))
      (ArithmeticFunction ℂ) := M.reindex E E
  let PF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι))
      (ArithmeticFunction ℂ) := P.reindex E E
  have hΩNF : Ω N = ∑ j, eF j := by
    rw [show (∑ j, eF j) = ∑ j, e j by
      exact E.symm.sum_comp e]
    exact hΩN
  have hfin := arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer
    (Fintype.card ι) N eF MF PF hN0 hΩNF
    (fun i j n hn => hMzero (E.symm i) (E.symm j) n (by simpa [eF] using hn))
    (fun i j n hn => hPzero (E.symm i) (E.symm j) n (by simpa [eF] using hn))
    (fun i j n hn => hlayer (E.symm i) (E.symm j) n (by simpa [eF] using hn))
  simpa only [MF, PF, Matrix.det_reindex_self] using hfin

/-- **Ω-leading-echelon law.** Distinct positive grading levels with the canonical prime-ray
lowest layer force every finite rectangle of logarithmic jets to be algebraically independent. -/
theorem omegaLeadingJets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (g : Fin d → ArithmeticFunction ℂ)
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level)
    (hbelow : ∀ r (q : Nat.Primes) (k n : ℕ), Ω n < level r - 1 →
      primeDeriv q.1 (rotatedLogArithmeticJet k (g r)) n = 0)
    (hleading : ∀ r (q : Nat.Primes) (k n : ℕ), Ω n = level r - 1 →
      primeDeriv q.1 (rotatedLogArithmeticJet k (g r)) n =
        arithmeticPointMass (q.1 ^ (level r - 1))
          ((level r : ℂ) *
            (((level r : ℂ) * rotatedPrimeLogClock q) ^ k)) n)
    (jet : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (jet + 1) =>
        rotatedLogArithmeticJet x.2 (g x.1)) := by
  classical
  let A : Fin d → Type := fun _ => Fin (jet + 1)
  letI (r : Fin d) : Fintype (A r) := inferInstance
  letI (r : Fin d) : DecidableEq (A r) := inferInstance
  let exponent : Fin d → ℕ := fun r => level r - 1
  have hexponent : Function.Injective exponent := by
    intro r s hrs
    apply hinj
    dsimp only [exponent] at hrs
    have hr := hpos r
    have hs := hpos s
    omega
  let a : ∀ r, A r → Nat.Primes → ℂ := fun r k p =>
    (((level r : ℕ) : ℂ) * rotatedPrimeLogClock p) ^ (k : ℕ)
  have htail : ∀ r, TailCoefficientIndependent (a r) := by
    intro r
    let base : Unit → Nat.Primes → ℂ := fun _ _ => 1
    have hbase : TailCoefficientIndependent base := by
      rw [tailCoefficientIndependent_unit_iff]
      unfold PrimeCoefficientTailZero
      simpa [base] using (Set.infinite_univ : (Set.univ : Set Nat.Primes).Infinite)
    have hrange : (Set.range (coefficientPattern base)).Finite := by
      apply (Set.finite_singleton (fun _ : Unit => (1 : ℂ))).subset
      intro y hy
      obtain ⟨p, rfl⟩ := hy
      funext u
      cases u
      rfl
    have hraw := (primePowerCoefficientShiftedRotatedJet_tailIndependent_iff
      (exponent r) base (fun _ : Unit => 0)
      (fun _ _ _ => Subsingleton.elim _ _) hrange jet).mpr hbase
    have hlevel : exponent r + 1 = level r := by
      dsimp only [exponent]
      have hr := hpos r
      omega
    intro c hc
    let c' : Unit × (Unit × Fin (jet + 1)) → ℂ :=
      fun x => c x.2.2
    let E : Unit × (Unit × Fin (jet + 1)) ≃ A r :=
      (Equiv.uniqueProd (Unit × Fin (jet + 1)) Unit).trans
        (Equiv.uniqueProd (Fin (jet + 1)) Unit)
    have hsum (p : Nat.Primes) :
        (∑ x : Unit × (Unit × Fin (jet + 1)),
            c' x * (1 * primeShiftFactor 0 p *
              ((((exponent r + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
                (x.2.2 : ℕ)))) =
          ∑ k : A r, c k * a r k p := by
      simp only [c', a, A, primeShiftFactor, neg_zero, zero_mul,
        Complex.exp_zero, one_mul, hlevel]
      simpa only [E, Equiv.coe_fn_mk] using
        E.sum_comp (fun k : A r =>
          c k * ((level r : ℂ) * rotatedPrimeLogClock p) ^ (k : ℕ))
    have hc'finite :
        {p | ∑ x : Unit × (Unit × Fin (jet + 1)),
            c' x * (1 * primeShiftFactor 0 p *
              ((((exponent r + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
                (x.2.2 : ℕ))) ≠ 0}.Finite := by
      simpa only [hsum] using hc
    have hc' := hraw c' hc'finite
    funext k
    simpa only [c', Pi.zero_apply] using
      congrFun hc' ((), ((), k))
  obtain ⟨q, hq, _havoid, hblock⟩ :=
    cofinitePrimePowerPacket_of_injective_layerExponents
      d A exponent hexponent a htail ∅ Set.finite_empty
  let I := Σ r, A r
  let eI : I → ℕ := fun x => exponent x.1
  let aI : I → Nat.Primes → ℂ := primePowerSigmaCoefficient a
  let B : Matrix I I ℂ := primePowerPacketCoefficientMatrix eI aI q
  let P : Matrix I I (ArithmeticFunction ℂ) :=
    primePowerPointMassMatrix q eI B
  let sourceJet : I → ArithmeticFunction ℂ := fun x =>
    rotatedLogArithmeticJet x.2 (g x.1)
  let M : Matrix I I (ArithmeticFunction ℂ) := fun i j =>
    primeDeriv (q i).1 (sourceJet j)
  let N : ℕ := ∏ i, (q i : ℕ) ^ eI i
  have hN0 : N ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (q i).2.ne_zero
  have hΩN : Ω N = ∑ i, eI i := by
    calc
      Ω N = ∑ i, Ω ((q i : ℕ) ^ eI i) := by
        exact cardFactors_finset_prod Finset.univ
          (fun i => (q i : ℕ) ^ eI i)
          (fun i _ => pow_ne_zero _ (q i).2.ne_zero)
      _ = ∑ i, eI i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact cardFactors_apply_prime_pow (q i).2
  have hMzero : ∀ i j n, Ω n < eI j → M i j n = 0 := by
    intro i j n hn
    exact hbelow j.1 (q i) j.2 n
      (by simpa [eI, exponent] using hn)
  have hPzero : ∀ i j n, Ω n < eI j → P i j n = 0 := by
    intro i j n hn
    dsimp only [P, primePowerPointMassMatrix]
    by_cases hloc : n = (q i : ℕ) ^ eI j
    · subst n
      rw [cardFactors_apply_prime_pow (q i).2] at hn
      exact False.elim (Nat.lt_irrefl _ hn)
    · exact arithmeticPointMass_apply_of_ne
        (pow_ne_zero _ (q i).2.ne_zero) hloc _
  have hlayer : ∀ i j n, Ω n = eI j → M i j n = P i j n := by
    intro i j n hn
    have hlevel : exponent j.1 + 1 = level j.1 := by
      dsimp only [exponent]
      have hjpos := hpos j.1
      omega
    have hsource :=
      hleading j.1 (q i) j.2 n
        (by simpa [eI, exponent] using hn)
    simpa only [M, sourceJet, P, primePowerPointMassMatrix, B,
      primePowerPacketCoefficientMatrix, eI, aI, primePowerSigmaCoefficient,
      a, hlevel] using hsource
  have hcoefficient : M.det N = P.det N :=
    arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer_fintype
      N eI M P hN0 hΩN hMzero hPzero hlayer
  have hPcoefficient :
      P.det N = (primePowerBlockMatrix eI B).det := by
    exact primePowerPointMassMatrix_det_apply q hq eI B
  have hMdet : M.det ≠ 0 := by
    intro hzero
    have hz : M.det N = 0 := by rw [hzero]; rfl
    rw [hcoefficient, hPcoefficient] at hz
    exact hblock hz
  have hAI : AlgebraicIndependent ℂ sourceJet := by
    refine algebraicIndependent_of_domain_jacobian
      (K := ℂ) (R := ArithmeticFunction ℂ)
      sourceJet (fun i => primeDeriv (q i).1)
      (fun i => primeDeriv_add (q i).1)
      (fun i => primeDeriv_mul (q i).1 (q i).2)
      (fun i => primeDeriv_algebraMap (q i).1 (q i).2)
      M hMdet ?_
    intro i j
    rfl
  let embed : (Fin d × Fin (jet + 1)) → I := fun x => ⟨x.1, x.2⟩
  have hembed : Function.Injective embed := by
    rintro ⟨r, k⟩ ⟨s, l⟩ h
    cases h
    rfl
  have hsub := hAI.comp embed hembed
  simpa only [Function.comp_apply, embed, sourceJet] using hsub

/-- Every finite rectangle of jets of distinct positive shell levels is algebraically
independent in the native Dirichlet-convolution algebra. -/
theorem highExponentShellJets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) (jet : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (jet + 1) =>
        rotatedLogArithmeticJet x.2 (complexShellIndicator (level x.1))) := by
  apply omegaLeadingJets_algebraicIndependent
    (fun r => complexShellIndicator (level r)) level hpos hinj
  · intro r q k n hn
    exact primeDeriv_rotatedShellJet_eq_zero_of_cardFactors_lt
      (hpos r) q k n hn
  · intro r q k n hn
    exact primeDeriv_rotatedShellJet_eq_pointMass_of_cardFactors_eq
      (hpos r) q k n hn

/-- Every finite rectangle of jets of distinct positive levels in the unified family consisting
of zeta at level one and the exponent shells at all other levels is algebraically independent. -/
theorem zetaShellJets_algebraicIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) (jet : ℕ) :
    AlgebraicIndependent ℂ
      (fun x : Fin d × Fin (jet + 1) =>
        rotatedLogArithmeticJet x.2 (zetaShellArithmetic (level x.1))) := by
  apply omegaLeadingJets_algebraicIndependent
    (fun r => zetaShellArithmetic (level r)) level hpos hinj
  · intro r q k n hn
    exact primeDeriv_rotatedZetaShellJet_eq_zero_of_cardFactors_lt
      (hpos r) q k n hn
  · intro r q k n hn
    exact primeDeriv_rotatedZetaShellJet_eq_pointMass_of_cardFactors_eq
      (hpos r) q k n hn

/-- Distinct positive shell coefficient streams are differentially independent after passage
to the Dirichlet-convolution fraction field. -/
theorem highExponentShellArithmetic_differentialIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (complexShellIndicator (level r))) := by
  unfold DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin d → ℕ → arithmeticFunctionFractionField := fun r k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k (complexShellIndicator (level r)))
  apply algebraicIndependent_prod_nat_of_fin x
  intro jet
  have hraw :=
    highExponentShellJets_algebraicIndependent level hpos hinj jet
  have hmap := hraw.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using hmap

/-- Zeta together with any distinct positive shell levels is differentially independent in the
Dirichlet-convolution fraction field. -/
theorem zetaShellArithmetic_differentialIndependent
    {d : ℕ} [Nonempty (Fin d)]
    (level : Fin d → ℕ) (hpos : ∀ r, 0 < level r)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun r => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (zetaShellArithmetic (level r))) := by
  unfold DifferentialIndependent
  simp_rw [differentialJet_algebraMap_rotatedLogArithmeticJet]
  let x : Fin d → ℕ → arithmeticFunctionFractionField := fun r k =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (rotatedLogArithmeticJet k (zetaShellArithmetic (level r)))
  apply algebraicIndependent_prod_nat_of_fin x
  intro jet
  have hraw := zetaShellJets_algebraicIndependent level hpos hinj jet
  have hmap := hraw.map'
    (f := IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
    (IsFractionRing.injective (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField)
  simpa only [Function.comp_apply, x] using hmap

/-- Arbitrary finite-index form of zeta/shell differential independence. -/
theorem zetaShellArithmetic_differentialIndependent_fintype
    {I : Type*} [Fintype I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (zetaShellArithmetic (level i))) := by
  classical
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hfin :=
    zetaShellArithmetic_differentialIndependent
      (fun r => level (E.symm r))
      (fun r => hpos (E.symm r))
      (hinj.comp E.symm.injective)
  have hcomp := hfin.comp E E.injective
  convert hcomp using 1
  funext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- Arbitrary finite-index form of shell differential independence. -/
theorem highExponentShellArithmetic_differentialIndependent_fintype
    {I : Type*} [Fintype I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent ℂ
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (complexShellIndicator (level i))) := by
  classical
  let E : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  have hfin :=
    highExponentShellArithmetic_differentialIndependent
      (fun r => level (E.symm r))
      (fun r => hpos (E.symm r))
      (hinj.comp E.symm.injective)
  have hcomp := hfin.comp E E.injective
  convert hcomp using 1
  funext i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

/-- A shell coefficient stream is uniformly bounded and hence has finite abscissa. -/
def highExponentShellFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨complexShellIndicator m, 1, ?_⟩
  intro y hy
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    rcases shellIndicator_eq_zero_or_one m n with hzero | hone
    · simp [complexShellIndicator_apply, hzero]
    · simp [complexShellIndicator_apply, hone]
  · simpa using hy

@[simp]
theorem highExponentShellFiniteAbscissaSource_val (m : ℕ) :
    (highExponentShellFiniteAbscissaSource m).1 =
      complexShellIndicator m :=
  rfl

/-- Finite-abscissa source for the unified zeta/shell family. -/
def zetaShellFiniteAbscissaSource (m : ℕ) :
    finiteAbscissaArithmeticSubalgebra :=
  if m = 1 then zetaSource else highExponentShellFiniteAbscissaSource m

@[simp]
theorem zetaShellFiniteAbscissaSource_val (m : ℕ) :
    (zetaShellFiniteAbscissaSource m).1 = zetaShellArithmetic m := by
  by_cases hm : m = 1
  · subst m
    simp [zetaShellFiniteAbscissaSource]
  · simp [zetaShellFiniteAbscissaSource, zetaShellArithmetic, hm]

/-- Actual upper-end meromorphic carrier of the shell Dirichlet series. -/
def highExponentShellUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (highExponentShellFiniteAbscissaSource m)

/-- Actual upper-end meromorphic carrier of the unified zeta/shell source. -/
def zetaShellUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (zetaShellFiniteAbscissaSource m)

@[simp]
theorem zetaShellUpperEndCarrier_one :
    zetaShellUpperEndCarrier 1 = zetaUpperEndMero := by
  rfl

theorem zetaShellUpperEndCarrier_eq_shell {m : ℕ} (hm : m ≠ 1) :
    zetaShellUpperEndCarrier m = highExponentShellUpperEndCarrier m := by
  simp [zetaShellUpperEndCarrier, zetaShellFiniteAbscissaSource, hm,
    highExponentShellUpperEndCarrier]

/-- Zeta together with every finite packet of distinct positive shell levels is jointly
differentially independent over the actual rational-coordinate field. -/
theorem zetaShellUpperEndCarrier_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => zetaShellUpperEndCarrier (level i)) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  simpa [zetaShellUpperEndCarrier] using
    zetaShellArithmetic_differentialIndependent_fintype level hpos hinj

/-- Arbitrarily many distinct positive members of the unified zeta/shell family remain jointly
differentially independent over the rational coordinate. -/
theorem zetaShellUpperEndCarrier_differentialIndependent_of_injective
    {I : Type*} (level : I → ℕ)
    (hpos : ∀ i, 0 < level i) (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => zetaShellUpperEndCarrier (level i)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro J hJfinite
  by_cases hJempty : J = ∅
  · subst J
    exact algebraicIndependent_empty_type
  letI : Fintype J := hJfinite.fintype
  letI : Nonempty J :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hJempty)
  apply zetaShellUpperEndCarrier_differentialIndependent
    (fun j : J => level j)
  · intro j
    exact hpos j
  · intro i j hij
    exact Subtype.ext (hinj hij)

/-- **Optimal zeta-plus-shell differential freeness.** Zeta itself and every exponent shell from
level two onward form one countably infinite jointly differentially independent family over
`ℂ(s)`.  Level two is optimal for this exact parametrization because level one is already used
by the zeta source in the common leading-echelon model. -/
theorem zetaPositiveShellUpperEnd_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun m : {m : ℕ // 2 ≤ m} =>
          highExponentShellUpperEndCarrier m.1)) := by
  let level : Unit ⊕ {m : ℕ // 2 ≤ m} → ℕ :=
    Sum.elim (fun _ : Unit => 1) (fun m => m.1)
  have hpos : ∀ i, 0 < level i := by
    rintro (u | m)
    · simp [level]
    · dsimp only [level, Sum.elim_inr]
      omega
  have hinj : Function.Injective level := by
    rintro (u | m) (v | n) h
    · exact congrArg Sum.inl (Subsingleton.elim u v)
    · dsimp only [level, Sum.elim_inl, Sum.elim_inr] at h
      omega
    · dsimp only [level, Sum.elim_inl, Sum.elim_inr] at h
      omega
    · congr 1
      exact Subtype.ext h
  have h :=
    zetaShellUpperEndCarrier_differentialIndependent_of_injective
      level hpos hinj
  convert h using 1
  funext i
  rcases i with u | m
  · simp [level]
  · have hm1 : m.1 ≠ 1 := by omega
    simpa [level] using (zetaShellUpperEndCarrier_eq_shell hm1).symm

/-! The zero-free divisor application starts at level twelve.  It is the restriction of the
stronger algebraic theorem above, whose natural range starts at level two. -/

/-- Zeta and the zero-free high-exponent subfamily are jointly differentially independent. -/
theorem zetaHighExponentShellUpperEnd_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField
      (Sum.elim (fun _ : Unit => zetaUpperEndMero)
        (fun m : {m : ℕ // 12 ≤ m} =>
          highExponentShellUpperEndCarrier m.1)) := by
  let embed :
      Unit ⊕ {m : ℕ // 12 ≤ m} → Unit ⊕ {m : ℕ // 2 ≤ m}
    | Sum.inl u => Sum.inl u
    | Sum.inr m => Sum.inr ⟨m.1, by omega⟩
  have hinj : Function.Injective embed := by
    rintro (u | m) (v | n) h
    · exact congrArg Sum.inl (Subsingleton.elim u v)
    · simp [embed] at h
    · simp [embed] at h
    · simp only [embed, Sum.inr.injEq] at h
      apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun x : {m : ℕ // 2 ≤ m} => x.1) h
  have h :=
    zetaPositiveShellUpperEnd_differentialIndependent.comp embed hinj
  convert h using 1
  funext i
  rcases i with u | m
  · rfl
  · rfl

/-! ## Relative hypertranscendence of the zero-free shell multipliers -/

/-- Differential field generated by the rational coordinate and the Riemann zeta germ. -/
abbrev zetaUpperEndDifferentialField : Type :=
  differentialAdjoin upperEndRationalCoordinateField
    (Set.range (fun _ : Unit => zetaUpperEndMero))

/-- Upper-end germ of the multiplier obtained by dividing one shell Dirichlet series by zeta.
On the half-plane of absolute convergence this is
`ζ((m+1)s)⁻¹ - ζ(ms)⁻¹`. -/
def relativeShellMultiplierUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  zetaUpperEndMero⁻¹ * highExponentShellUpperEndCarrier m

/-- Every shell from level two onward remains jointly differentially independent after the
coefficient field is enlarged by zeta and all of its derivatives. -/
theorem positiveShellUpperEndCarrier_relativeDifferentialIndependent :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun m : {m : ℕ // 2 ≤ m} =>
        highExponentShellUpperEndCarrier m.1) := by
  exact
    (GaloisForLFunctions.differentialIndependent_sumElim_iff
      (fun _ : Unit => zetaUpperEndMero)
      (fun m : {m : ℕ // 2 ≤ m} =>
        highExponentShellUpperEndCarrier m.1)).mp
      zetaPositiveShellUpperEnd_differentialIndependent |>.2

/-- **Optimal relative multiplier hypertranscendence.** The adjacent reciprocal-dilation
differences

`H_m(s) = ζ((m+1)s)⁻¹ - ζ(ms)⁻¹`, `m ≥ 2`,

form a countably infinite jointly differentially independent family even over the differential
field generated by `ℂ(s)` and `ζ(s)`. -/
theorem relativeShellMultiplierUpperEndCarrier_differentialIndependent_two :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun m : {m : ℕ // 2 ≤ m} =>
        relativeShellMultiplierUpperEndCarrier m.1) := by
  letI : Differential zetaUpperEndDifferentialField :=
    derivationClosedDifferential
      (differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero)))
      (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero)))
  letI : DifferentialAlgebra zetaUpperEndDifferentialField upperEndMeroField :=
    ⟨fun z => derivationClosedDifferential_apply
      (differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero)))
      (derivationClosed_differentialAdjoin upperEndRationalCoordinateField
        (Set.range (fun _ : Unit => zetaUpperEndMero))) z⟩
  let zetaBase : zetaUpperEndDifferentialField :=
    ⟨zetaUpperEndMero,
      subset_differentialAdjoin upperEndRationalCoordinateField _
        (Set.mem_range_self ())⟩
  have hzetaBase : zetaBase ≠ 0 := by
    intro hzero
    apply zetaUpperEndMero_ne_zero
    exact congrArg Subtype.val hzero
  let a : {m : ℕ // 2 ≤ m} → zetaUpperEndDifferentialField :=
    fun _ => zetaBase⁻¹
  have ha : ∀ m, a m ≠ 0 := fun _ => inv_ne_zero hzetaBase
  have hscaled :=
    positiveShellUpperEndCarrier_relativeDifferentialIndependent.mulBase a ha
  simpa only [a, zetaBase, relativeShellMultiplierUpperEndCarrier,
    IntermediateField.algebraMap_apply, map_inv₀] using hscaled

/-- The zero-free high-exponent shell family remains jointly differentially independent after
the coefficient field is enlarged by zeta and all of its derivatives. -/
theorem highExponentShellUpperEndCarrier_relativeDifferentialIndependent :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun m : {m : ℕ // 12 ≤ m} =>
        highExponentShellUpperEndCarrier m.1) := by
  let embed : {m : ℕ // 12 ≤ m} → {m : ℕ // 2 ≤ m} :=
    fun m => ⟨m.1, by omega⟩
  exact positiveShellUpperEndCarrier_relativeDifferentialIndependent.comp embed
    (fun _ _ h => Subtype.ext
      (congrArg (fun x : {m : ℕ // 2 ≤ m} => x.1) h))

/-- The zero-free multiplier subfamily inherits the optimal relative independence theorem. -/
theorem relativeShellMultiplierUpperEndCarrier_differentialIndependent :
    DifferentialIndependent zetaUpperEndDifferentialField
      (fun m : {m : ℕ // 12 ≤ m} =>
        relativeShellMultiplierUpperEndCarrier m.1) := by
  let embed : {m : ℕ // 12 ≤ m} → {m : ℕ // 2 ≤ m} :=
    fun m => ⟨m.1, by omega⟩
  exact relativeShellMultiplierUpperEndCarrier_differentialIndependent_two.comp embed
    (fun _ _ h => Subtype.ext
      (congrArg (fun x : {m : ℕ // 2 ≤ m} => x.1) h))

/-- Every shell is zeta times its relative multiplier in the upper-end meromorphic field. -/
theorem zeta_mul_relativeShellMultiplierUpperEndCarrier (m : ℕ) :
    zetaUpperEndMero * relativeShellMultiplierUpperEndCarrier m =
      highExponentShellUpperEndCarrier m := by
  simp [relativeShellMultiplierUpperEndCarrier, zetaUpperEndMero_ne_zero]

/-- Every finite family of distinct positive shell Dirichlet series is jointly differentially
independent over the actual rational-coordinate field. -/
theorem highExponentShellUpperEndCarrier_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (level : I → ℕ) (hpos : ∀ i, 0 < level i)
    (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => highExponentShellUpperEndCarrier (level i)) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  simpa [highExponentShellFiniteAbscissaSource,
    highExponentShellUpperEndCarrier] using
      highExponentShellArithmetic_differentialIndependent_fintype
        level hpos hinj

/-- The full arbitrarily indexed family of distinct positive shell Dirichlet series is jointly
differentially independent over the actual rational-coordinate field. -/
theorem highExponentShellUpperEndCarrier_differentialIndependent_of_injective
    {I : Type*} (level : I → ℕ)
    (hpos : ∀ i, 0 < level i) (hinj : Function.Injective level) :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun i => highExponentShellUpperEndCarrier (level i)) := by
  classical
  apply differentialIndependent_of_forall_finite_subfamily
  intro J hJfinite
  by_cases hJempty : J = ∅
  · subst J
    exact algebraicIndependent_empty_type
  letI : Fintype J := hJfinite.fintype
  letI : Nonempty J :=
    Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hJempty)
  apply highExponentShellUpperEndCarrier_differentialIndependent
    (fun j : J => level j)
  · intro j
    exact hpos j
  · intro i j hij
    exact Subtype.ext (hinj hij)

/-- **High-exponent shell hypertranscendence law.** Every shell at level at least twelve is one
member of a countably infinite jointly differentially independent family over `ℂ(s)`. -/
theorem highExponentShellUpperEndCarrier_differentialIndependent_twelve :
    DifferentialIndependent upperEndRationalCoordinateField
      (fun m : {m : ℕ // 12 ≤ m} =>
        highExponentShellUpperEndCarrier m.1) := by
  apply highExponentShellUpperEndCarrier_differentialIndependent_of_injective
    (fun m : {m : ℕ // 12 ≤ m} => m.1)
  · intro m
    omega
  · exact Subtype.val_injective

end

end RHTower
