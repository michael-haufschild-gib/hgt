import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheFunctionFieldCalibration
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# The function-field calibration is derived

Over a finite field `F` with `q` elements, the Möbius function of `F[T]` on monic polynomials is
`μ(f) = (−1)^{#irreducible factors}` on squarefree `f` and `0` otherwise (`polyMoebius`). This file
derives its degree sums from unique factorization, where the corpus calibration
(`ArithmeticContinuationAndCriticalEnergy.fqMobiusDegreeSum`) posits them.

* **Divisor sums vanish** (`sum_monicDivisors_polyMoebius`). For monic `f` of positive degree,
  `Σ_{d ∣ f monic} μ(d) = 0`: pair the divisors prime to an irreducible factor `P` with their multiples
  by `P` (`polyMoebius_mul_irreducible`); divisors by `P²` contribute nothing.
* **Divisor counting** (`card_filter_dvd_monicOfDeg`). A monic `d` of degree `k ≤ n` divides exactly
  `q^{n−k}` monic polynomials of degree `n`.
* **The degree sums** (`sum_monicOfDeg_polyMoebius`). Double counting gives
  `Σ_{k ≤ n} M(k) q^{n−k} = [n = 0]` for `M(k) = Σ_{deg d = k} μ(d)`, hence `M = 1, −q, 0, 0, …`.
  This is the model of the corpus calibration (`fqMobiusDegreeSum_eq`).
* **The trivial point is better than typical** (`sum_range_sum_monicOfDeg_polyMoebius`). The Möbius
  sums of `F[T]` up to degree `N ≥ 1` equal `1 − q`: bounded, gauge exponent `0` against the size
  `q^N`. Over `ℤ` the trivial point is never better than typical (`Θ ≥ 1/2`), because `ζ` has zeros;
  the zeta function of `F[T]` has none, and its trivial point lies below the half-power floor.
* **The Liouville twin carries the pole** (`sum_monicDivisors_sq_dvd_polyMoebius`,
  `sum_monicOfDeg_polyMoebius_sq`). `Σ_{d² ∣ f} μ(d) = μ(f)²`, and the same double counting gives
  `q^n − q^{n−1}` squarefree monic polynomials of degree `n ≥ 2`: at the twin `μλ = μ²` the sums grow
  like the size. Over `F[T]` the twin duality of the special locus is exact at the trivial point:
  exponent `0` at `0`, exponent `1` at its Liouville twin.
-/

open Polynomial Finset UniqueFactorizationMonoid

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The monic polynomials of degree `n`, as `X^n + p` with `deg p < n`. -/
def monicOfDeg (n : ℕ) : Finset F[X] :=
  (univ : Finset (Fin n → F)).image fun c => X ^ n + ((degreeLTEquiv F n).symm c : F[X])

variable {F}

theorem mem_monicOfDeg {n : ℕ} {f : F[X]} : f ∈ monicOfDeg F n ↔ f.Monic ∧ f.natDegree = n := by
  constructor
  · intro hf
    obtain ⟨c, -, rfl⟩ := mem_image.mp hf
    have hp : ((degreeLTEquiv F n).symm c : F[X]).degree < n :=
      mem_degreeLT.mp ((degreeLTEquiv F n).symm c).2
    refine ⟨monic_X_pow_add hp, ?_⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rintro ⟨hm, hdeg⟩
    have hlt : (f - X ^ n).degree < (n : WithBot ℕ) := by
      have h := degree_sub_lt (p := f) (q := X ^ n)
        (by rw [degree_X_pow, degree_eq_natDegree hm.ne_zero, hdeg]) hm.ne_zero
        (by rw [hm.leadingCoeff, leadingCoeff_X_pow])
      rwa [degree_eq_natDegree hm.ne_zero, hdeg] at h
    refine mem_image.mpr ⟨degreeLTEquiv F n ⟨f - X ^ n, mem_degreeLT.mpr hlt⟩, mem_univ _, ?_⟩
    simp

/-- There are `q^n` monic polynomials of degree `n`. -/
theorem card_monicOfDeg (n : ℕ) : #(monicOfDeg F n) = Fintype.card F ^ n := by
  rw [monicOfDeg, card_image_of_injective _ fun c c' h => (degreeLTEquiv F n).symm.injective
    (Subtype.ext (add_left_cancel h)), card_univ, Fintype.card_fun, Fintype.card_fin]

theorem monicOfDeg_zero : monicOfDeg F 0 = {1} := by
  ext f
  rw [mem_monicOfDeg, mem_singleton]
  exact ⟨fun h => eq_one_of_monic_natDegree_zero h.1 h.2, fun h => h ▸ ⟨monic_one, natDegree_one⟩⟩

/-! ### The Möbius function of `F[T]` -/

open Classical in
/-- The Möbius function of `F[T]`: `(−1)^{#normalized factors}` on squarefree polynomials. -/
def polyMoebius (f : F[X]) : ℤ :=
  if Squarefree f then (-1) ^ Multiset.card (normalizedFactors f) else 0

omit [Fintype F] in
theorem polyMoebius_one : polyMoebius (1 : F[X]) = 1 := by
  simp [polyMoebius, normalizedFactors_one]

omit [Fintype F] in
/-- `μ(dP) = −μ(d)` for an irreducible `P` not dividing `d`. -/
theorem polyMoebius_mul_irreducible {d P : F[X]} (hd : d ≠ 0) (hP : Irreducible P)
    (hPd : ¬ P ∣ d) : polyMoebius (d * P) = -polyMoebius d := by
  have hrel : IsRelPrime d P :=
    ((Irreducible.coprime_iff_not_dvd hP).mpr hPd).isRelPrime.symm
  have hsq : Squarefree (d * P) ↔ Squarefree d := by
    rw [squarefree_mul_iff]
    exact ⟨fun h => h.2.1, fun h => ⟨hrel, h, hP.squarefree⟩⟩
  have hcard : Multiset.card (normalizedFactors (d * P)) =
      Multiset.card (normalizedFactors d) + 1 := by
    rw [normalizedFactors_mul hd hP.ne_zero, normalizedFactors_irreducible hP, Multiset.card_add,
      Multiset.card_singleton]
  unfold polyMoebius
  by_cases h : Squarefree d
  · rw [if_pos (hsq.mpr h), if_pos h, hcard, pow_succ]
    ring
  · rw [if_neg (fun h' => h (hsq.mp h')), if_neg h, neg_zero]

omit [Fintype F] in
/-- `μ` vanishes on multiples of the square of a non-unit. -/
theorem polyMoebius_eq_zero_of_sq_dvd {d P : F[X]} (hP : ¬ IsUnit P) (h : P * P ∣ d) :
    polyMoebius d = 0 := by
  unfold polyMoebius
  rw [if_neg fun hsq => hP (hsq P h)]

/-! ### Monic divisors -/

variable (F) in
/-- The monic polynomials of degree at most `n`. -/
def monicUpTo (n : ℕ) : Finset F[X] := (range (n + 1)).biUnion (monicOfDeg F)

theorem mem_monicUpTo {n : ℕ} {f : F[X]} : f ∈ monicUpTo F n ↔ f.Monic ∧ f.natDegree ≤ n := by
  simp only [monicUpTo, mem_biUnion, mem_range, mem_monicOfDeg]
  constructor
  · rintro ⟨k, hk, hm, rfl⟩
    exact ⟨hm, by omega⟩
  · rintro ⟨hm, hle⟩
    exact ⟨f.natDegree, by omega, hm, rfl⟩

open Classical in
/-- The monic divisors of `f`. -/
def monicDivisors (f : F[X]) : Finset F[X] := (monicUpTo F f.natDegree).filter (· ∣ f)

open Classical in
theorem mem_monicDivisors {f d : F[X]} (hf : f ≠ 0) : d ∈ monicDivisors f ↔ d.Monic ∧ d ∣ f := by
  rw [monicDivisors, mem_filter, mem_monicUpTo]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, natDegree_le_of_dvd h.2 hf⟩, h.2⟩⟩

/-- **Divisor sums of `μ` vanish** on monic polynomials of positive degree. -/
theorem sum_monicDivisors_polyMoebius {f : F[X]} (hf : f.Monic) (hdeg : f.natDegree ≠ 0) :
    ∑ d ∈ monicDivisors f, polyMoebius d = 0 := by
  classical
  have hf0 := hf.ne_zero
  -- A monic irreducible factor `P`.
  obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor
    (fun hu => hdeg (by rw [hf.eq_one_of_isUnit hu, natDegree_one])) hf0
  set P := normalize p with hPdef
  have hPirr : Irreducible P := (normalize_associated p).symm.irreducible hp
  have hPm : P.Monic := monic_normalize hp.ne_zero
  have hPf : P ∣ f := normalize_dvd_iff.mpr hpf
  set D := monicDivisors f
  have hmem := fun d => mem_monicDivisors (d := d) hf0
  -- Multiplying by `P` maps the divisors prime to `P` onto the divisors exactly divisible by `P`.
  have himage : ∑ d ∈ D.filter (P ∣ ·), polyMoebius d =
      ∑ d ∈ D.filter (¬ P ∣ ·), polyMoebius (d * P) := by
    rw [← sum_image (s := D.filter (¬ P ∣ ·)) (g := (· * P)) fun a _ b _ h =>
      mul_right_cancel₀ hPirr.ne_zero h]
    refine (sum_subset (fun e he => ?_) fun e he hne => ?_).symm
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp he
      obtain ⟨hdD, hPd⟩ := mem_filter.mp hd
      obtain ⟨hdm, hdf⟩ := (hmem d).mp hdD
      have hcop : IsCoprime d P := ((Irreducible.coprime_iff_not_dvd hPirr).mpr hPd).symm
      exact mem_filter.mpr ⟨(hmem _).mpr ⟨hdm.mul hPm, hcop.mul_dvd hdf hPf⟩, dvd_mul_left P d⟩
    · obtain ⟨heD, hPe⟩ := mem_filter.mp he
      obtain ⟨hem, hef⟩ := (hmem e).mp heD
      obtain ⟨e', rfl⟩ := hPe
      have he'm : e'.Monic := hPm.of_mul_monic_left hem
      by_cases hPe' : P ∣ e'
      · exact polyMoebius_eq_zero_of_sq_dvd hPirr.not_isUnit (mul_dvd_mul_left P hPe')
      · exfalso
        refine hne (mem_image.mpr ⟨e', mem_filter.mpr ⟨(hmem e').mpr ⟨he'm,
          (dvd_mul_left e' P).trans hef⟩, hPe'⟩, mul_comm e' P⟩)
  rw [← sum_filter_add_sum_filter_not D (P ∣ ·), himage, ← sum_add_distrib]
  refine sum_eq_zero fun d hd => ?_
  obtain ⟨hdD, hPd⟩ := mem_filter.mp hd
  rw [polyMoebius_mul_irreducible ((hmem d).mp hdD).1.ne_zero hPirr hPd, neg_add_cancel]

/-! ### Counting and the degree sums -/

open Classical in
/-- A monic `d` of degree `k ≤ n` divides `q^{n−k}` monic polynomials of degree `n`. -/
theorem card_filter_dvd_monicOfDeg {d : F[X]} {k n : ℕ} (hd : d ∈ monicOfDeg F k) (hkn : k ≤ n) :
    #((monicOfDeg F n).filter (d ∣ ·)) = Fintype.card F ^ (n - k) := by
  classical
  obtain ⟨hdm, hdk⟩ := mem_monicOfDeg.mp hd
  have himg : (monicOfDeg F n).filter (d ∣ ·) = (monicOfDeg F (n - k)).image (d * ·) := by
    ext f
    simp only [mem_filter, mem_image, mem_monicOfDeg]
    constructor
    · rintro ⟨⟨hfm, hfn⟩, e, rfl⟩
      have hem : e.Monic := hdm.of_mul_monic_left hfm
      refine ⟨e, ⟨hem, ?_⟩, rfl⟩
      rw [hdm.natDegree_mul hem, hdk] at hfn
      omega
    · rintro ⟨e, ⟨hem, hen⟩, rfl⟩
      refine ⟨⟨hdm.mul hem, ?_⟩, dvd_mul_right d e⟩
      rw [hdm.natDegree_mul hem, hdk, hen]
      omega
  rw [himg, card_image_of_injective _ fun a b h => mul_left_cancel₀ hdm.ne_zero h,
    card_monicOfDeg]

/-- The degree-`k` Möbius sum `M(k) = Σ_{deg d = k} μ(d)`. -/
def moebiusDegreeSum (F : Type*) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) : ℤ :=
  ∑ d ∈ monicOfDeg F k, polyMoebius d

/-- **Double counting.** `Σ_{k ≤ n} M(k) q^{n−k} = [n = 0]`. -/
theorem sum_moebiusDegreeSum_mul_pow (n : ℕ) :
    ∑ k ∈ range (n + 1), moebiusDegreeSum F k * (Fintype.card F : ℤ) ^ (n - k) =
      if n = 0 then 1 else 0 := by
  classical
  -- Both sides count `Σ_{deg f = n} Σ_{d ∣ f} μ(d)`.
  have hdisj : (↑(range (n + 1)) : Set ℕ).PairwiseDisjoint (monicOfDeg F) := by
    intro k _ k' _ hkk
    refine disjoint_left.mpr fun f hf hf' => hkk ?_
    rw [← (mem_monicOfDeg.mp hf).2, (mem_monicOfDeg.mp hf').2]
  have hcount : ∑ f ∈ monicOfDeg F n, ∑ d ∈ monicDivisors f, polyMoebius d =
      ∑ k ∈ range (n + 1), moebiusDegreeSum F k * (Fintype.card F : ℤ) ^ (n - k) := by
    have hdiv : ∀ f ∈ monicOfDeg F n, monicDivisors f = (monicUpTo F n).filter (· ∣ f) := by
      intro f hf
      rw [monicDivisors, (mem_monicOfDeg.mp hf).2]
    rw [sum_congr rfl fun f hf => by rw [hdiv f hf, sum_filter], sum_comm, monicUpTo,
      sum_biUnion hdisj]
    refine sum_congr rfl fun k hk => ?_
    rw [moebiusDegreeSum, sum_mul]
    refine sum_congr rfl fun d hd => ?_
    rw [← sum_filter, sum_const,
      card_filter_dvd_monicOfDeg (k := k) hd (by have := mem_range.mp hk; omega),
      nsmul_eq_mul, mul_comm]
    push_cast
    ring
  rw [← hcount]
  split_ifs with hn
  · subst hn
    rw [monicOfDeg_zero, sum_singleton]
    have : monicDivisors (1 : F[X]) = {1} := by
      ext d
      rw [mem_monicDivisors one_ne_zero, mem_singleton]
      exact ⟨fun h => h.1.eq_one_of_isUnit (isUnit_of_dvd_one h.2), fun h => by
        subst h
        exact ⟨monic_one, dvd_rfl⟩⟩
    rw [this, sum_singleton, polyMoebius_one]
  · exact sum_eq_zero fun f hf => sum_monicDivisors_polyMoebius (mem_monicOfDeg.mp hf).1
      (by rw [(mem_monicOfDeg.mp hf).2]; exact hn)

/-- **The degree sums of `μ` over `F[T]`**: `1`, `−q`, then `0`. -/
theorem sum_monicOfDeg_polyMoebius (n : ℕ) :
    moebiusDegreeSum F n =
      if n = 0 then 1 else if n = 1 then -(Fintype.card F : ℤ) else 0 := by
  rcases n with _ | m
  · have h := sum_moebiusDegreeSum_mul_pow (F := F) 0
    simpa using h
  · have h := sum_moebiusDegreeSum_mul_pow (F := F) (m + 1)
    have hprev := sum_moebiusDegreeSum_mul_pow (F := F) m
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one] at h
    have hshift : ∑ k ∈ range (m + 1), moebiusDegreeSum F k * (Fintype.card F : ℤ) ^ (m + 1 - k) =
        (Fintype.card F : ℤ) *
          ∑ k ∈ range (m + 1), moebiusDegreeSum F k * (Fintype.card F : ℤ) ^ (m - k) := by
      rw [mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [show m + 1 - k = m - k + 1 by have := mem_range.mp hk; omega, pow_succ]
      ring
    rw [hshift, hprev] at h
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_eq_right] at h ⊢
    split_ifs at h ⊢ <;> linarith

/-- **The corpus model is derived**: `fqMobiusDegreeSum q k` is the degree-`k` Möbius sum of `F[T]`. -/
theorem fqMobiusDegreeSum_eq (k : ℕ) :
    ArithmeticContinuationAndCriticalEnergy.fqMobiusDegreeSum (Fintype.card F) k =
      (moebiusDegreeSum F k : ℝ) := by
  rw [sum_monicOfDeg_polyMoebius, ArithmeticContinuationAndCriticalEnergy.fqMobiusDegreeSum]
  split_ifs <;> simp

/-- **The trivial point of `F[T]` is better than typical.** The Möbius sums up to degree `N ≥ 1`
equal `1 − q`. -/
theorem sum_range_sum_monicOfDeg_polyMoebius {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range (N + 1), moebiusDegreeSum F k = 1 - Fintype.card F := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  rw [sum_eq_zero fun k _ => by
    rw [sum_monicOfDeg_polyMoebius]
    simp only [Nat.add_one_ne_zero, if_false, show k + 1 + 1 ≠ 1 by omega]]
  simp only [sum_monicOfDeg_polyMoebius]
  simp only [zero_add, Nat.add_one_ne_zero, if_false, if_true]
  ring

/-! ### The Liouville twin of `F[T]` -/

open Classical in
/-- **The squarefree indicator.** `Σ_{d monic, d² ∣ f} μ(d) = μ(f)²` for monic `f`. -/
theorem sum_monicDivisors_sq_dvd_polyMoebius {f : F[X]} (hf : f.Monic) :
    ∑ d ∈ (monicDivisors f).filter (fun d => d * d ∣ f), polyMoebius d = polyMoebius f ^ 2 := by
  have hf0 := hf.ne_zero
  have hmem := fun d => mem_monicDivisors (d := d) hf0
  by_cases hsq : Squarefree f
  · have hset : (monicDivisors f).filter (fun d => d * d ∣ f) = {1} := by
      ext d
      rw [mem_filter, hmem, mem_singleton]
      constructor
      · rintro ⟨⟨hdm, -⟩, hdd⟩
        exact hdm.eq_one_of_isUnit (hsq d hdd)
      · rintro rfl
        exact ⟨⟨monic_one, one_dvd f⟩, by rw [one_mul]; exact one_dvd f⟩
    rw [hset, sum_singleton, polyMoebius_one, polyMoebius, if_pos hsq, ← pow_mul, mul_comm,
      pow_mul, neg_one_sq, one_pow]
  · rw [show polyMoebius f = 0 by rw [polyMoebius, if_neg hsq], zero_pow two_ne_zero]
    -- A monic irreducible `P` with `P² ∣ f`.
    obtain ⟨x, hxx, hxu⟩ : ∃ x, x * x ∣ f ∧ ¬ IsUnit x := by
      by_contra h
      push Not at h
      exact hsq h
    obtain ⟨p, hp, hpx⟩ := WfDvdMonoid.exists_irreducible_factor hxu
      (fun hx0 => hf0 (by rw [hx0, zero_mul] at hxx; exact zero_dvd_iff.mp hxx))
    set P := normalize p
    have hPirr : Irreducible P := (normalize_associated p).symm.irreducible hp
    have hPm : P.Monic := monic_normalize hp.ne_zero
    have hPP : P * P ∣ f := (mul_dvd_mul (normalize_dvd_iff.mpr hpx) (normalize_dvd_iff.mpr hpx)).trans hxx
    set D := (monicDivisors f).filter (fun d => d * d ∣ f)
    have himage : ∑ d ∈ D.filter (P ∣ ·), polyMoebius d =
        ∑ d ∈ D.filter (¬ P ∣ ·), polyMoebius (d * P) := by
      rw [← sum_image (s := D.filter (¬ P ∣ ·)) (g := (· * P)) fun a _ b _ h =>
        mul_right_cancel₀ hPirr.ne_zero h]
      refine (sum_subset (fun e he => ?_) fun e he hne => ?_).symm
      · obtain ⟨d, hd, rfl⟩ := mem_image.mp he
        obtain ⟨hdD, hPd⟩ := mem_filter.mp hd
        obtain ⟨hdD', hdd⟩ := mem_filter.mp hdD
        obtain ⟨hdm, hdf⟩ := (hmem d).mp hdD'
        have hcop : IsCoprime d P := ((Irreducible.coprime_iff_not_dvd hPirr).mpr hPd).symm
        have hsqdvd : d * P * (d * P) ∣ f := by
          rw [show d * P * (d * P) = d * d * (P * P) by ring]
          exact (hcop.mul_left hcop).mul_right (hcop.mul_left hcop) |>.mul_dvd hdd hPP
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨(hmem _).mpr ⟨hdm.mul hPm,
          (dvd_mul_right (d * P) (d * P)).trans hsqdvd⟩, hsqdvd⟩, dvd_mul_left P d⟩
      · obtain ⟨heD, hPe⟩ := mem_filter.mp he
        obtain ⟨heD', hee⟩ := mem_filter.mp heD
        obtain ⟨hem, hef⟩ := (hmem e).mp heD'
        obtain ⟨e', rfl⟩ := hPe
        have he'm : e'.Monic := hPm.of_mul_monic_left hem
        by_cases hPe' : P ∣ e'
        · exact polyMoebius_eq_zero_of_sq_dvd hPirr.not_isUnit (mul_dvd_mul_left P hPe')
        · exfalso
          have he'e' : e' * e' ∣ f :=
            (mul_dvd_mul (dvd_mul_left e' P) (dvd_mul_left e' P)).trans hee
          refine hne (mem_image.mpr ⟨e', mem_filter.mpr ⟨mem_filter.mpr ⟨(hmem e').mpr ⟨he'm,
            (dvd_mul_left e' P).trans hef⟩, he'e'⟩, hPe'⟩, mul_comm e' P⟩)
    rw [← sum_filter_add_sum_filter_not D (P ∣ ·), himage, ← sum_add_distrib]
    refine sum_eq_zero fun d hd => ?_
    obtain ⟨hdD, hPd⟩ := mem_filter.mp hd
    rw [polyMoebius_mul_irreducible
      ((hmem d).mp (mem_filter.mp hdD).1).1.ne_zero hPirr hPd, neg_add_cancel]

/-- **The Liouville twin of `F[T]` carries the pole.** There are `q^n − q^{n−1}` squarefree monic
polynomials of degree `n ≥ 2`: `Σ_{deg f = n} μ(f)² = q^n − q^{n−1}`. Over `F[T]` the Möbius sums of the
trivial point are bounded while those of its Liouville twin `μ λ = μ²` grow like the size. -/
theorem sum_monicOfDeg_polyMoebius_sq {n : ℕ} (hn : 2 ≤ n) :
    ∑ f ∈ monicOfDeg F n, polyMoebius f ^ 2 =
      (Fintype.card F : ℤ) ^ n - (Fintype.card F : ℤ) ^ (n - 1) := by
  classical
  set q : ℤ := (Fintype.card F : ℤ) with hq
  have hdisj : (↑(range (n + 1)) : Set ℕ).PairwiseDisjoint (monicOfDeg F) := by
    intro k _ k' _ hkk
    refine disjoint_left.mpr fun f hf hf' => hkk ?_
    rw [← (mem_monicOfDeg.mp hf).2, (mem_monicOfDeg.mp hf').2]
  -- The number of `f` of degree `n` divisible by `d²`, for `d` of degree `k`.
  have hcount : ∀ k ≤ n, ∀ d ∈ monicOfDeg F k,
      (#((monicOfDeg F n).filter (fun f => d * d ∣ f)) : ℤ) =
        if 2 * k ≤ n then q ^ (n - 2 * k) else 0 := by
    intro k _ d hd
    obtain ⟨hdm, hdk⟩ := mem_monicOfDeg.mp hd
    have hdd : d * d ∈ monicOfDeg F (2 * k) :=
      mem_monicOfDeg.mpr ⟨hdm.mul hdm, by rw [hdm.natDegree_mul hdm, hdk]; ring⟩
    split_ifs with h2k
    · rw [card_filter_dvd_monicOfDeg hdd h2k]
      push_cast
      rfl
    · rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
      intro f hf hdf
      obtain ⟨hfm, hfn⟩ := mem_monicOfDeg.mp hf
      have := natDegree_le_of_dvd hdf hfm.ne_zero
      rw [hdm.natDegree_mul hdm, hdk, hfn] at this
      omega
  calc ∑ f ∈ monicOfDeg F n, polyMoebius f ^ 2
      = ∑ f ∈ monicOfDeg F n, ∑ d ∈ monicUpTo F n, if d * d ∣ f then polyMoebius d else 0 := by
        refine sum_congr rfl fun f hf => ?_
        obtain ⟨hfm, hfn⟩ := mem_monicOfDeg.mp hf
        rw [← sum_monicDivisors_sq_dvd_polyMoebius hfm, monicDivisors, hfn, filter_filter,
          sum_filter]
        refine sum_congr rfl fun d _ => ?_
        by_cases hdd : d * d ∣ f
        · rw [if_pos hdd, if_pos ⟨(dvd_mul_right d d).trans hdd, hdd⟩]
        · rw [if_neg hdd, if_neg fun h => hdd h.2]
    _ = ∑ k ∈ range (n + 1), moebiusDegreeSum F k * (if 2 * k ≤ n then q ^ (n - 2 * k) else 0) := by
        rw [sum_comm, monicUpTo, sum_biUnion hdisj]
        refine sum_congr rfl fun k hk => ?_
        rw [moebiusDegreeSum, sum_mul]
        refine sum_congr rfl fun d hd => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm,
          hcount k (by have := mem_range.mp hk; omega) d hd]
    _ = q ^ n - q ^ (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        rw [sum_eq_zero fun k _ => by
          rw [sum_monicOfDeg_polyMoebius]
          simp only [Nat.add_one_ne_zero, if_false, show k + 1 + 1 ≠ 1 by omega, zero_mul]]
        simp only [sum_monicOfDeg_polyMoebius, Nat.add_one_ne_zero, if_false, if_true, zero_add,
          show 2 * (0 + 1) ≤ m + 2 by omega, show 2 * 0 ≤ m + 2 by omega]
        rw [show m + 2 - 2 * (0 + 1) = m by omega, show m + 2 - 2 * 0 = m + 2 by omega,
          show m + 2 - 1 = m + 1 by omega]
        ring

end GaloisForLFunctions.ArithmeticGaugeTheory
