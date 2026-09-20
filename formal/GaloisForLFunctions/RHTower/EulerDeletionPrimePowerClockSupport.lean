import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale

/-!
# Prime-power support of Euler-deletion clock jumps

The chronological clock changes only at prime-power moduli.  This preserves
the literal EDQ source: it only identifies steps at which no new residue
information can enter a later history layer.
-/

noncomputable section
set_option autoImplicit false

namespace RHTower.DeletionResidueMartingale

open Finset
open scoped BigOperators

/-- A non-prime-power next modulus is already resolved by the preceding
chronological clock. -/
theorem successor_dvd_clock_of_not_isPrimePow (n : ℕ) (hn : ¬ IsPrimePow (n + 1)) :
    n + 1 ∣ clock n := by
  apply (Nat.factorization_le_iff_dvd (Nat.succ_ne_zero n) (clock_pos n).ne').mp
  intro p
  by_cases hp0 : (n + 1).factorization p = 0
  · simp [hp0]
  · have hp : p.Prime := by
      by_contra hnot
      exact hp0 ((Nat.factorization_eq_zero_iff (n + 1) p).mpr (Or.inl hnot))
    have he : 0 < (n + 1).factorization p := Nat.pos_of_ne_zero hp0
    have hpdiv : p ^ (n + 1).factorization p ∣ n + 1 :=
      (hp.pow_dvd_iff_le_factorization (Nat.succ_ne_zero n)).mpr le_rfl
    have hlt : p ^ (n + 1).factorization p < n + 1 := by
      apply lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos n) hpdiv)
      intro hEq
      exact hn ((isPrimePow_nat_iff (n + 1)).mpr
        ⟨p, (n + 1).factorization p, hp, he, hEq⟩)
    have hclock : p ^ (n + 1).factorization p ∣ clock n :=
      dvd_clock (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))
        (Nat.le_of_lt_succ hlt)
    exact (hp.pow_dvd_iff_le_factorization (clock_pos n).ne').mp hclock

/-- Any positive modulus absent from a chronological clock has a prime-power divisor that is
strictly newer than that clock.  This is an exact factorization statement: it introduces no
size estimate and identifies the chronological prime-power coordinate that remains unresolved. -/
theorem exists_primePow_dvd_of_not_dvd_clock
    {L n : ℕ} (hn : n ≠ 0) (hnd : ¬ n ∣ clock L) :
    ∃ q : ℕ, IsPrimePow q ∧ q ∣ n ∧ L < q := by
  have hfac : ¬ n.factorization ≤ (clock L).factorization := by
    intro h
    exact hnd ((Nat.factorization_le_iff_dvd hn (clock_pos L).ne').mp h)
  rw [Finsupp.le_def] at hfac
  push Not at hfac
  obtain ⟨p, hp⟩ := hfac
  have he : 0 < n.factorization p :=
    lt_of_le_of_lt (Nat.zero_le _) hp
  have hprime : p.Prime := by
    by_contra hnot
    have hzero := Nat.factorization_eq_zero_of_not_prime n hnot
    omega
  have hdiv : p ^ n.factorization p ∣ n :=
    (hprime.pow_dvd_iff_le_factorization hn).mpr le_rfl
  have hgt : L < p ^ n.factorization p := by
    by_contra hle
    have hclock : p ^ n.factorization p ∣ clock L :=
      dvd_clock (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hprime.ne_zero))
        (Nat.le_of_not_gt hle)
    have hlefac := (hprime.pow_dvd_iff_le_factorization (clock_pos L).ne').mp hclock
    omega
  exact ⟨p ^ n.factorization p,
    (isPrimePow_nat_iff _).mpr ⟨p, n.factorization p, hprime, he, rfl⟩,
    hdiv, hgt⟩

/-- Peeling a chosen prime from a squarefree non-clock modulus either leaves a divisor already
resolved by the clock, or exposes a second, distinct prime beyond that clock.  This is the
recursive alternative needed for the multifuture part of a literal EDQ lcm fibre. -/
theorem exists_distinct_prime_dvd_of_squarefree_div_not_dvd_clock
    {L d p : ℕ} (hp : p.Prime) (hpd : p ∣ d) (hsq : Squarefree d)
    (hnot : ¬ d / p ∣ clock L) :
    ∃ q : ℕ, q.Prime ∧ q ∣ d ∧ q ≠ p ∧ L < q := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hdp : p * (d / p) = d := Nat.mul_div_cancel' hpd
  have hrpos : 0 < d / p := Nat.div_pos (Nat.le_of_dvd hdpos hpd) hp.pos
  have hrdiv : d / p ∣ d := by
    exact ⟨p, hdp.symm.trans (Nat.mul_comm _ _)⟩
  have hrsq : Squarefree (d / p) := hsq.squarefree_of_dvd hrdiv
  obtain ⟨q, hqpow, hqdiv, hqgt⟩ :=
    exists_primePow_dvd_of_not_dvd_clock hrpos.ne' hnot
  have hqprime : q.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hrsq.squarefree_of_dvd hqdiv, hqpow⟩
  have hpnot : ¬ p ∣ d / p := by
    intro hpdiv
    have hpp : p * p ∣ d := by
      have : p * p ∣ p * (d / p) := Nat.mul_dvd_mul_left p hpdiv
      simpa [hdp] using this
    have hppsq : Squarefree (p * p) := hsq.squarefree_of_dvd hpp
    have hcop := Nat.coprime_of_squarefree_mul hppsq
    exact hp.ne_one (by simpa [Nat.coprime_self] using hcop)
  refine ⟨q, hqprime, hqdiv.trans hrdiv, ?_, hqgt⟩
  intro hqp
  subst q
  exact hpnot hqdiv

/-- A squarefree modulus splits exactly into the factor already represented by the chronological
clock and a residual factor whose every prime is strictly future to that clock.  This extracts all
old prime coordinates at once, rather than peeling them one at a time. -/
theorem squarefree_clock_gcd_split
    {L d : ℕ} (hsq : Squarefree d) :
    d = (d / gcd d (clock L)) * gcd d (clock L) ∧
      0 < d / gcd d (clock L) ∧
      0 < gcd d (clock L) ∧
      gcd d (clock L) ∣ clock L ∧
      ∀ p : ℕ, p.Prime → p ∣ d / gcd d (clock L) → L < p := by
  have hg : gcd d (clock L) ∣ d := Nat.gcd_dvd_left _ _
  have hprod : d / gcd d (clock L) * gcd d (clock L) = d :=
    Nat.div_mul_cancel hg
  have hres : 0 < d / gcd d (clock L) := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, zero_mul] at hprod
    exact hsq.ne_zero hprod.symm
  have hold : 0 < gcd d (clock L) :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hsq.ne_zero)
  refine ⟨hprod.symm, hres, hold, Nat.gcd_dvd_right _ _, ?_⟩
  intro p hp hpres
  by_contra hnot
  have hple : p ≤ L := Nat.le_of_not_gt hnot
  have hpold : p ∣ clock L :=
    dvd_clock (Nat.one_le_iff_ne_zero.mpr hp.ne_zero) hple
  have hpd : p ∣ d := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hpres _
  have hpg : p ∣ gcd d (clock L) := Nat.dvd_gcd hpd hpold
  have hpsq_d : p * p ∣ d := by
    rw [← hprod]
    exact Nat.mul_dvd_mul hpres hpg
  have hpsq : Squarefree (p * p) := hsq.squarefree_of_dvd hpsq_d
  have hcop := Nat.coprime_of_squarefree_mul hpsq
  exact hp.ne_one (by simpa [Nat.coprime_self] using hcop)

/-- The old chronological gcd and future residual in the squarefree clock split are coprime. -/
theorem squarefree_clock_gcd_split_coprime
    {L d : ℕ} (hsq : Squarefree d) :
    Nat.Coprime (d / gcd d (clock L)) (gcd d (clock L)) := by
  obtain ⟨hdeq, _, _, _, _⟩ := squarefree_clock_gcd_split (L := L) hsq
  have hsqprod : Squarefree ((d / gcd d (clock L)) * gcd d (clock L)) := by
    rw [← hdeq]
    exact hsq
  exact Nat.coprime_of_squarefree_mul hsqprod

/-- The Möbius sign factors exactly over the coprime old/future clock decomposition. -/
theorem moebius_squarefree_clock_gcd_split
    {L d : ℕ} (hsq : Squarefree d) :
    ArithmeticFunction.moebius d =
      ArithmeticFunction.moebius (d / gcd d (clock L)) *
        ArithmeticFunction.moebius (gcd d (clock L)) := by
  obtain ⟨hdeq, _, _, _, _⟩ := squarefree_clock_gcd_split (L := L) hsq
  calc
    ArithmeticFunction.moebius d =
        ArithmeticFunction.moebius (d / gcd d (clock L) * gcd d (clock L)) :=
      congrArg ArithmeticFunction.moebius hdeq
    _ = ArithmeticFunction.moebius (d / gcd d (clock L)) *
        ArithmeticFunction.moebius (gcd d (clock L)) :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (squarefree_clock_gcd_split_coprime hsq)

/-- The chronological clock divides the factorial of its index.  This gives an exact finite
certificate that every prime represented by the clock is no later than that index. -/
theorem clock_dvd_factorial (L : ℕ) : clock L ∣ L.factorial := by
  unfold clock
  apply Finset.lcm_dvd
  intro i hi
  apply Nat.dvd_factorial
  · omega
  · have hi' := Finset.mem_range.mp hi
    omega

/-- A prime divisor of a chronological clock is no later than that clock's index. -/
theorem prime_dvd_clock_le {p L : ℕ} (hp : p.Prime) (hpc : p ∣ clock L) : p ≤ L :=
  hp.dvd_factorial.mp (hpc.trans (clock_dvd_factorial L))

/-- The future residual in a squarefree clock split is coprime to the entire chronological clock,
not only to its extracted gcd. -/
theorem squarefree_clock_residual_coprime_clock
    {L d : ℕ} (hsq : Squarefree d) :
    Nat.Coprime (d / gcd d (clock L)) (clock L) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hnot
  obtain ⟨_, _, _, _, hfuture⟩ := squarefree_clock_gcd_split (L := L) hsq
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hnot
  have hpres : p ∣ d / gcd d (clock L) :=
    hpg.trans (Nat.gcd_dvd_left _ _)
  have hpclock : p ∣ clock L :=
    hpg.trans (Nat.gcd_dvd_right _ _)
  exact (Nat.not_lt_of_ge (prime_dvd_clock_le hp hpclock)) (hfuture p hp hpres)

/-- The lcm label separates into future and old factors whenever the former are coprime to the
chronological clock and the latter divide it. -/
theorem lcm_mul_of_future_coprime_clock
    {L m n r s : ℕ}
    (hm : Nat.Coprime m (clock L)) (hn : Nat.Coprime n (clock L))
    (hr : r ∣ clock L) (hs : s ∣ clock L) :
    Nat.lcm (m * r) (n * s) = Nat.lcm m n * Nat.lcm r s := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact Nat.mul_dvd_mul
        ((show m ∣ Nat.lcm m n from Nat.dvd_lcm_left _ _))
        ((show r ∣ Nat.lcm r s from Nat.dvd_lcm_left _ _))
    · exact Nat.mul_dvd_mul
        ((show n ∣ Nat.lcm m n from Nat.dvd_lcm_right _ _))
        ((show s ∣ Nat.lcm r s from Nat.dvd_lcm_right _ _))
  · have hfutureClock : Nat.Coprime (Nat.lcm m n) (clock L) := by
      apply Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul m n)
      exact hm.mul_left hn
    have holdClock : Nat.lcm r s ∣ clock L := Nat.lcm_dvd hr hs
    have hcross : Nat.Coprime (Nat.lcm m n) (Nat.lcm r s) :=
      hfutureClock.coprime_dvd_right holdClock
    apply hcross.mul_dvd_of_dvd_of_dvd
    · apply Nat.lcm_dvd
      · exact (show m ∣ m * r from ⟨r, rfl⟩).trans (Nat.dvd_lcm_left _ _)
      · exact (show n ∣ n * s from ⟨s, rfl⟩).trans (Nat.dvd_lcm_right _ _)
    · apply Nat.lcm_dvd
      · exact (show r ∣ m * r from ⟨m, Nat.mul_comm _ _⟩).trans (Nat.dvd_lcm_left _ _)
      · exact (show s ∣ n * s from ⟨n, Nat.mul_comm _ _⟩).trans (Nat.dvd_lcm_right _ _)

/-- Once old factors divide the clock and future residuals are coprime to it, the factored lcm
is a clock divisor exactly when its future lcm is trivial.  This removes every old coordinate
from the EDQ non-clock lcm restriction while retaining the literal pair label. -/
theorem lcm_mul_clock_dvd_iff_residual_lcm_eq_one
    {L m n r s : ℕ}
    (hm : Nat.Coprime m (clock L)) (hn : Nat.Coprime n (clock L))
    (hr : r ∣ clock L) (hs : s ∣ clock L) :
    Nat.lcm m n * Nat.lcm r s ∣ clock L ↔ Nat.lcm m n = 1 := by
  have hfutureClock : Nat.Coprime (Nat.lcm m n) (clock L) := by
    apply Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul m n)
    exact hm.mul_left hn
  constructor
  · intro hlabel
    have hfutureDvd : Nat.lcm m n ∣ clock L :=
      (dvd_mul_right (Nat.lcm m n) (Nat.lcm r s)).trans hlabel
    calc
      Nat.lcm m n = Nat.gcd (Nat.lcm m n) (clock L) := (Nat.gcd_eq_left hfutureDvd).symm
      _ = 1 := hfutureClock.gcd_eq_one
  · intro hfuture
    rw [hfuture]
    simpa using (Nat.lcm_dvd hr hs)

/-- Exact non-clock form of the split lcm restriction.  The remaining condition is entirely on
the two future residual coordinates. -/
theorem lcm_mul_clock_not_dvd_iff_residual_lcm_ne_one
    {L m n r s : ℕ}
    (hm : Nat.Coprime m (clock L)) (hn : Nat.Coprime n (clock L))
    (hr : r ∣ clock L) (hs : s ∣ clock L) :
    (¬ Nat.lcm m n * Nat.lcm r s ∣ clock L) ↔ Nat.lcm m n ≠ 1 := by
  rw [lcm_mul_clock_dvd_iff_residual_lcm_eq_one hm hn hr hs]

/-- Re-extracting the future residual from two residual/cofactor products returns the two
original residuals.  Consequently their literal residual lcm is exactly `lcm m n`. -/
theorem residual_lcm_mul_old_eq
    {m n r s C : ℕ} (hC : 0 < C)
    (hm : Nat.Coprime m C) (hn : Nat.Coprime n C)
    (hr : r ∣ C) (hs : s ∣ C) :
    Nat.lcm ((m * r) / Nat.gcd (m * r) C) ((n * s) / Nat.gcd (n * s) C) = Nat.lcm m n := by
  have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hr hC
  have hspos : 0 < s := Nat.pos_of_dvd_of_pos hs hC
  rw [Nat.gcd_mul_of_coprime_of_dvd hm hr, Nat.gcd_mul_of_coprime_of_dvd hn hs,
    Nat.mul_div_left m hrpos, Nat.mul_div_left n hspos]

/-- The literal lcm label of two squarefree divisors splits exactly into its all-future residual
label and its chronological old-factor label. -/
theorem squarefree_clock_gcd_split_lcm
    {L d e : ℕ} (hsd : Squarefree d) (hse : Squarefree e) :
    Nat.lcm d e =
      Nat.lcm (d / gcd d (clock L)) (e / gcd e (clock L)) *
        Nat.lcm (gcd d (clock L)) (gcd e (clock L)) := by
  obtain ⟨hdeq, _, _, hdC, _⟩ := squarefree_clock_gcd_split (L := L) hsd
  obtain ⟨heeq, _, _, heC, _⟩ := squarefree_clock_gcd_split (L := L) hse
  calc
    Nat.lcm d e = Nat.lcm
        ((d / gcd d (clock L)) * gcd d (clock L))
        ((e / gcd e (clock L)) * gcd e (clock L)) :=
      congrArg₂ Nat.lcm hdeq heeq
    _ = Nat.lcm (d / gcd d (clock L)) (e / gcd e (clock L)) *
        Nat.lcm (gcd d (clock L)) (gcd e (clock L)) :=
      lcm_mul_of_future_coprime_clock
        (squarefree_clock_residual_coprime_clock hsd)
        (squarefree_clock_residual_coprime_clock hse) hdC heC

/-- Exact truncated-carrier reindexing by the future residual and chronological cofactor.
For every squarefree physical divisor `d ≤ N`, the inverse coordinates are literally
`(d / gcd d C, gcd d C)`.  Thus the only residual old-factor truncation is the explicit
condition `m * r ≤ N`; no cofactor is discarded or completed implicitly. -/
theorem squarefree_interval_sum_reindex_gcd
    {R : Type*} [AddCommMonoid R] (N C : ℕ) (hC : 0 < C) (f : ℕ → R) :
    ∑ d ∈ Finset.filter Squarefree (Icc 1 N), f d =
      ∑ m ∈ Finset.filter (fun m => Nat.Coprime m C) (Icc 1 N),
        ∑ r ∈ Finset.filter (fun r => m * r ≤ N ∧ Squarefree (m * r)) C.divisors,
          f (m * r) := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (i := fun d => ⟨d / Nat.gcd d C, Nat.gcd d C⟩)
    (j := fun mr => mr.1 * mr.2) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, hsq⟩ := hd
    have hdpos : 0 < d := hd1
    have hgpos : 0 < Nat.gcd d C := Nat.gcd_pos_of_pos_left C hdpos
    have hprod : d / Nat.gcd d C * Nat.gcd d C = d :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left d C)
    have hmpos : 0 < d / Nat.gcd d C := by
      apply Nat.pos_of_ne_zero
      intro hmzero
      apply hdpos.ne
      rw [← hprod, hmzero, zero_mul]
    have hmN : d / Nat.gcd d C ≤ N := by
      calc
        d / Nat.gcd d C ≤ d / Nat.gcd d C * Nat.gcd d C :=
          Nat.le_mul_of_pos_right _ hgpos
        _ = d := hprod
        _ ≤ N := hdN
    have hcop : Nat.Coprime (d / Nat.gcd d C) C :=
      Nat.coprime_div_gcd_of_squarefree hsq hC.ne'
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmpos, hmN⟩, hcop⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d C, hC.ne'⟩, ?_⟩
    change d / Nat.gcd d C * Nat.gcd d C ≤ N ∧
      Squarefree (d / Nat.gcd d C * Nat.gcd d C)
    rw [hprod]
    exact ⟨hdN, hsq⟩
  · rintro ⟨m, r⟩ hmr
    rw [Finset.mem_sigma] at hmr
    obtain ⟨hm, hr⟩ := hmr
    rw [Finset.mem_filter] at hm hr
    obtain ⟨hmIcc, hmc⟩ := hm
    obtain ⟨hrdiv, hbound⟩ := hr
    rw [Finset.mem_Icc] at hmIcc
    rw [Nat.mem_divisors] at hrdiv
    obtain ⟨hrc, _⟩ := hrdiv
    obtain ⟨hmulN, hsq⟩ := hbound
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hrc hC
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hmIcc.1 hrpos, hmulN⟩, hsq⟩
  · intro d hd
    dsimp
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left d C)
  · rintro ⟨m, r⟩ hmr
    rw [Finset.mem_sigma] at hmr
    obtain ⟨hm, hr⟩ := hmr
    rw [Finset.mem_filter] at hm hr
    obtain ⟨_, hmc⟩ := hm
    obtain ⟨hrdiv, _⟩ := hr
    rw [Nat.mem_divisors] at hrdiv
    obtain ⟨hrc, _⟩ := hrdiv
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hrc hC
    have hg : Nat.gcd (m * r) C = r := Nat.gcd_mul_of_coprime_of_dvd hmc hrc
    simp only
    rw [hg, Nat.mul_div_left m hrpos]
  · intro d hd
    dsimp
    congr 1
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left d C)).symm

/-- The squarefree physical pair carrier is exactly the product of two residual/cofactor
carriers.  Both truncations remain literal: `m * r ≤ N` and `n * s ≤ N`.  The pair weight is
arbitrary, so this theorem transports the actual EDQ lcm and beta kernel without changing it. -/
theorem squarefree_interval_pair_sum_reindex_gcd
    {R : Type*} [AddCommMonoid R] (N C : ℕ) (hC : 0 < C) (f : ℕ → ℕ → R) :
    ∑ d ∈ Finset.filter Squarefree (Icc 1 N),
      ∑ e ∈ Finset.filter Squarefree (Icc 1 N), f d e =
    ∑ m ∈ Finset.filter (fun m => Nat.Coprime m C) (Icc 1 N),
      ∑ r ∈ Finset.filter (fun r => m * r ≤ N ∧ Squarefree (m * r)) C.divisors,
        ∑ n ∈ Finset.filter (fun n => Nat.Coprime n C) (Icc 1 N),
          ∑ s ∈ Finset.filter (fun s => n * s ≤ N ∧ Squarefree (n * s)) C.divisors,
            f (m * r) (n * s) := by
  classical
  calc
    ∑ d ∈ Finset.filter Squarefree (Icc 1 N),
        ∑ e ∈ Finset.filter Squarefree (Icc 1 N), f d e =
      ∑ m ∈ Finset.filter (fun m => Nat.Coprime m C) (Icc 1 N),
        ∑ r ∈ Finset.filter (fun r => m * r ≤ N ∧ Squarefree (m * r)) C.divisors,
          ∑ e ∈ Finset.filter Squarefree (Icc 1 N), f (m * r) e :=
      squarefree_interval_sum_reindex_gcd N C hC
        (fun d => ∑ e ∈ Finset.filter Squarefree (Icc 1 N), f d e)
    _ = _ := by
      refine Finset.sum_congr rfl fun m hm => ?_
      refine Finset.sum_congr rfl fun r hr => ?_
      exact squarefree_interval_sum_reindex_gcd N C hC (fun e => f (m * r) e)

end RHTower.DeletionResidueMartingale
