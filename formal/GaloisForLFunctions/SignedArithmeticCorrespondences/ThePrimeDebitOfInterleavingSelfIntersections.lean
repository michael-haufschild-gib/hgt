import GaloisForLFunctions.SignedArithmeticCorrespondences.TheFullWeilFormOnInterleavingDivisors
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts
import GaloisForLFunctions.HTGeometry.FiniteReversedAbelBounds

/-!
# The prime debit of interleaving self-intersections

Split the Weil self-pairing on any finite support into its diagonal-plus-real-place
budget and its mixed prime-and-boundary debit. On signed integer endpoint jumps,
these two pieces match the counterterm-and-jet expression and the Chebyshev-and-boundary
expression of `interleaved_finite_part`.

On unshifted prefixes `[1, N]`, divisor incidence cannot pay this prime debit:
already at `N = 2` the integer centered multiple mask of `2` has negative Weil
form, and for every prime `p` the Weil form of `1_{p ∣ n} - 1/p` on `[1, N]`
diverges to `-∞` at rate `-(1/p)(1 - 1/p) N log N`. Even on late combs, the
prime-and-boundary contribution of a centered prime divisibility mask is strictly
negative before spending the diagonal and real-place budget.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Finset MeasureTheory Filter Topology
open AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt

/-! ### Budget–debit decomposition of the Weil form -/

/-- Diagonal counterterm minus the off-diagonal archimedean jet pairing. -/
def diagRealBudget (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ n ∈ S, c n ^ 2 * counterterm n) -
    ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * jetKernel m n

/-- Off-diagonal `w`-weighted prime contacts minus twice the product of the two pole degrees. -/
def mixedPrimeDebitW (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW w m n) -
    2 * (degOne S c * degTwo S c)

/-- Mixed prime-and-boundary debit for the ordinary von Mangoldt contact weights. -/
def mixedPrimeDebit (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  mixedPrimeDebitW (fun k => (Λ k : ℝ)) S c

theorem combFormW_eq_diagRealBudget_sub_mixedPrimeDebitW
    (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :
    combFormW w S c = diagRealBudget S c - mixedPrimeDebitW w S c := by
  have hsplit : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (jetKernel m n + contactW w m n) =
      (∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * jetKernel m n) +
        ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW w m n := by
    simp only [mul_add, sum_add_distrib]
  rw [combFormW, combPairingW, diagRealBudget, mixedPrimeDebitW, hsplit]
  ring

theorem combForm_eq_diagRealBudget_sub_mixedPrimeDebit (S : Finset ℕ) (c : ℕ → ℝ) :
    combForm S c = diagRealBudget S c - mixedPrimeDebit S c := by
  simpa only [combFormW_vonMangoldt, mixedPrimeDebit] using
    combFormW_eq_diagRealBudget_sub_mixedPrimeDebitW (fun k => (Λ k : ℝ)) S c

theorem mixedPrimeDebitW_le_diagRealBudget_iff
    (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :
    mixedPrimeDebitW w S c ≤ diagRealBudget S c ↔ 0 ≤ combFormW w S c := by
  rw [combFormW_eq_diagRealBudget_sub_mixedPrimeDebitW]
  constructor <;> intro h <;> linarith only [h]

theorem mixedPrimeDebit_le_diagRealBudget_iff (S : Finset ℕ) (c : ℕ → ℝ) :
    mixedPrimeDebit S c ≤ diagRealBudget S c ↔ 0 ≤ combForm S c := by
  simpa only [combFormW_vonMangoldt, mixedPrimeDebit] using
    mixedPrimeDebitW_le_diagRealBudget_iff (fun k => (Λ k : ℝ)) S c

private theorem jetMonomial_integral_self {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : m ≠ n) :
    (∫ x in (0 : ℝ)..1, (x ^ (max m n - min m n - 1) + x ^ (m + n - 1))) = 2 * jetKernel m n := by
  let k := max m n - min m n
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hcast (j : ℕ) (hj : 1 ≤ j) : (((j - 1 : ℕ) : ℝ) + 1) = j := by
    rw [Nat.cast_sub hj, Nat.cast_one]; ring
  have he : (k : ℝ) = |(m : ℝ) - n| := by
    rcases le_total m n with h | h
    · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
      simp only [k, max_eq_right h, min_eq_left h, Nat.cast_sub h,
        abs_of_nonpos (sub_nonpos.mpr h')]
      ring
    · have h' : (n : ℝ) ≤ m := by exact_mod_cast h
      simp only [k, max_eq_left h, min_eq_right h, Nat.cast_sub h,
        abs_of_nonneg (sub_nonneg.mpr h')]
  change (∫ x in (0 : ℝ)..1, x ^ (k - 1) + x ^ (m + n - 1)) = _
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ (k - 1))
      (g := fun x : ℝ => x ^ (m + n - 1))
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    _root_.RHTower.hilbertMoment_eq_integral_pow,
    _root_.RHTower.hilbertMoment_eq_integral_pow,
    hcast k hk, hcast (m + n) (by omega), he, Nat.cast_add, jetKernel]
  ring

/-- On an integral upper-jump divisor, `diagRealBudget` is the diagonal counterterm
minus half the `mixedJetSection` integral, and `mixedPrimeDebit` is the signed
Chebyshev remainder minus twice the fractional boundary. -/
theorem interleaved_self_budget_and_debit (N : ℕ) (a : ℕ → ℤ) :
    let u := upperDivisor N a
    diagRealBudget (Icc 1 N) (fun n => (u n : ℝ)) =
      (∑ n ∈ Icc 1 N, (u n : ℝ) ^ 2 * counterterm n) -
        (∫ x in (0 : ℝ)..1, mixedJetSection N a a x) / 2 ∧
    mixedPrimeDebit (Icc 1 N) (fun n => (u n : ℝ)) =
      (∑ k ∈ range (N + 1), twoSidedCoefficient N a a k * _root_.RHTower.psiRemainder k) -
        2 * fractionalBoundary N N u a := by
  intro u
  have hj : (∫ x in (0 : ℝ)..1, mixedJetSection N a a x) =
      2 * ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (u m : ℝ) * u n * jetKernel m n := by
    unfold mixedJetSection
    simp only [mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun n _ =>
      Continuous.intervalIntegrable (by
        change Continuous fun x : ℝ => ∑ m ∈ (Icc 1 N).erase n,
          (u m : ℝ) * u n * (x ^ (max m n - min m n - 1) + x ^ (m + n - 1))
        fun_prop) _ _)]
    refine sum_congr rfl fun n hn => ?_
    rw [intervalIntegral.integral_finsetSum (fun m _ =>
      Continuous.intervalIntegrable (by
        change Continuous fun x : ℝ =>
          (u m : ℝ) * u n * (x ^ (max m n - min m n - 1) + x ^ (m + n - 1))
        fun_prop) _ _)]
    refine sum_congr rfl fun m hm => ?_
    rw [intervalIntegral.integral_const_mul,
      jetMonomial_integral_self (mem_Icc.mp (mem_erase.mp hm).2).1
        (mem_Icc.mp hn).1 (mem_erase.mp hm).1]
    ring
  have hbud : diagRealBudget (Icc 1 N) (fun n => (u n : ℝ)) =
      (∑ n ∈ Icc 1 N, (u n : ℝ) ^ 2 * counterterm n) -
        (∫ x in (0 : ℝ)..1, mixedJetSection N a a x) / 2 := by
    rw [diagRealBudget, hj]
    ring
  refine ⟨hbud, ?_⟩
  have hfin := interleaved_finite_part N a a
  have hself := formBilin_self (Icc 1 N) (fun n => (u n : ℝ))
  have hsq : (∑ n ∈ Icc 1 N, (u n : ℝ) * u n * counterterm n) =
      ∑ n ∈ Icc 1 N, (u n : ℝ) ^ 2 * counterterm n :=
    sum_congr rfl fun n _ => by ring
  unfold interleavedFinitePart at hfin
  dsimp only at hfin
  rw [hself, combForm_eq_diagRealBudget_sub_mixedPrimeDebit, hsq, hbud] at hfin
  linarith only [hfin]

/-! ### Centered residue and divisibility indicators -/

/-- Centered indicator of the congruence class `n ≡ r (mod d)`. -/
def centeredResidue (d r n : ℕ) : ℝ :=
  (if d = 0 then 0 else if n % d = r % d then (1 : ℝ) else 0) - 1 / (d : ℝ)

/-- Centered indicator of multiples of `d`. -/
def centeredMultiple (d n : ℕ) : ℝ :=
  (if d ∣ n then (1 : ℝ) else 0) - 1 / (d : ℝ)

theorem centeredMultiple_eq_centeredResidue {d : ℕ} (hd : 0 < d) (n : ℕ) :
    centeredMultiple d n = centeredResidue d 0 n := by
  simp only [centeredMultiple, centeredResidue, hd.ne', if_false, Nat.zero_mod,
    Nat.dvd_iff_mod_eq_zero]

theorem card_Ioc_mod_eq {d : ℕ} (hd : 0 < d) (r a q : ℕ) :
    ((Ioc a (a + d * q)).filter (fun n => n % d = r % d)).card = q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Ioc a (a + d * (q + 1)) = Ioc a (a + d * q) ∪ Ioc (a + d * q) (a + d * q + d) := by
      rw [show a + d * (q + 1) = a + d * q + d by ring]
      exact (Ioc_union_Ioc_eq_Ioc (Nat.le_add_right a _) (Nat.le_add_right _ d)).symm
    have hdisj : Disjoint (Ioc a (a + d * q)) (Ioc (a + d * q) (a + d * q + d)) :=
      Ioc_disjoint_Ioc_of_le le_rfl
    rw [hsplit, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj), ih]
    suffices h1 : ((Ioc (a + d * q) (a + d * q + d)).filter (fun n => n % d = r % d)).card = 1 by
      omega
    set A := a + d * q
    let t := (r + d - (A + 1) % d) % d
    have ht : t < d := Nat.mod_lt _ hd
    have hmem : A + 1 + t ∈ (Ioc A (A + d)).filter (fun n => n % d = r % d) := by
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
      have hmod : (A + 1 + t) % d = ((A + 1) % d + t) % d := by
        rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl d)]
      have hle : (A + 1) % d ≤ r + d := by
        have := Nat.mod_lt (A + 1) hd
        omega
      have heq : ((A + 1) % d + (r + d - (A + 1) % d)) % d = r % d := by
        rw [Nat.add_sub_of_le hle, Nat.add_mod_right]
      dsimp [t] at hmod ⊢
      rw [hmod, Nat.mod_add_mod, Nat.add_comm ((A + 1) % d), Nat.sub_add_cancel hle,
        Nat.add_mod_right]
    refine card_eq_one.mpr ⟨A + 1 + t, eq_singleton_iff_unique_mem.mpr ⟨hmem, fun n hn => ?_⟩⟩
    obtain ⟨hnI, hnmod⟩ := mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hnI
    have hm1 := (mem_filter.mp hmem).2
    have hdiv : d ∣ Nat.dist n (A + 1 + t) := by
      rcases le_total n (A + 1 + t) with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]
        exact (Nat.modEq_iff_dvd' hle).mp (hnmod.trans hm1.symm)
      · rw [Nat.dist_eq_sub_of_le_right hle]
        exact (Nat.modEq_iff_dvd' hle).mp (hm1.trans hnmod.symm)
    by_contra hne
    have hpos : 0 < Nat.dist n (A + 1 + t) := Nat.dist_pos_of_ne hne
    have hge := Nat.le_of_dvd hpos hdiv
    rw [Nat.dist] at hge
    omega

theorem card_Ioc_short_mod_le_one {d : ℕ} (hd : 0 < d) (r A m : ℕ) (hm : m < d) :
    ((Ioc A (A + m)).filter (fun n => n % d = r % d)).card ≤ 1 := by
  refine card_le_one.mpr fun x hx y hy => ?_
  obtain ⟨hxI, hxm⟩ := mem_filter.mp hx
  obtain ⟨hyI, hym⟩ := mem_filter.mp hy
  obtain ⟨hx1, hx2⟩ := mem_Ioc.mp hxI
  obtain ⟨hy1, hy2⟩ := mem_Ioc.mp hyI
  have hdiv : d ∣ Nat.dist x y := by
    rcases le_total x y with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      exact (Nat.modEq_iff_dvd' hle).mp (hxm.trans hym.symm)
    · rw [Nat.dist_eq_sub_of_le_right hle]
      exact (Nat.modEq_iff_dvd' hle).mp (hym.trans hxm.symm)
  by_contra hne
  have hge := Nat.le_of_dvd (Nat.dist_pos_of_ne hne) hdiv
  rw [Nat.dist] at hge
  omega

/-- Every centered congruence-class indicator has interval sum at most `1` in magnitude,
uniformly in the modulus `d`, the residue `r`, and the interval endpoints. -/
theorem abs_sum_centeredResidue_Ioc_le_one {d : ℕ} (hd : 0 < d) (r a b : ℕ) :
    |∑ n ∈ Ioc a b, centeredResidue d r n| ≤ 1 := by
  rcases lt_or_ge b a with hlt | hab
  · simp [Ioc_eq_empty (not_lt.mpr hlt.le)]
  set L := b - a
  have hb : b = a + L := (Nat.add_sub_of_le hab).symm
  rw [hb]
  set q := L / d
  set m := L % d
  have hL : d * q + m = L := Nat.div_add_mod L d
  have hm : m < d := Nat.mod_lt L hd
  have hsplit : Ioc a (a + L) = Ioc a (a + d * q) ∪ Ioc (a + d * q) (a + d * q + m) := by
    rw [← hL, Nat.add_assoc]
    exact (Ioc_union_Ioc_eq_Ioc (Nat.le_add_right a _) (Nat.le_add_right _ m)).symm
  have hdisj : Disjoint (Ioc a (a + d * q)) (Ioc (a + d * q) (a + d * q + m)) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  have hcount : ∑ n ∈ Ioc a (a + L), (if n % d = r % d then (1 : ℝ) else 0) =
      (q : ℝ) + (((Ioc (a + d * q) (a + d * q + m)).filter (fun n => n % d = r % d)).card : ℝ) := by
    rw [← sum_filter, hsplit, filter_union,
      sum_union (disjoint_filter_filter hdisj), sum_const, sum_const,
      card_Ioc_mod_eq hd r a q, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
  set e := ((Ioc (a + d * q) (a + d * q + m)).filter (fun n => n % d = r % d)).card
  have he1 : e ≤ 1 := card_Ioc_short_mod_le_one hd r (a + d * q) m hm
  have he0 : m = 0 → e = 0 := fun hm0 => by simp [e, hm0]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : ∑ n ∈ Ioc a (a + L), centeredResidue d r n =
      (q : ℝ) + (e : ℝ) - ((d * q + m : ℕ) : ℝ) / d := by
    simp only [centeredResidue, hd.ne', if_false, sum_sub_distrib, hcount,
      sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul, hL]
    ring
  rw [hsum]
  push_cast
  rw [add_div, mul_div_cancel_left₀ (q : ℝ) hdR.ne']
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · simp [he0 hm0, hm0]
  · have hmd : (m : ℝ) / d ≤ 1 := (div_le_one hdR).mpr (by exact_mod_cast hm.le)
    have hmd0 : 0 ≤ (m : ℝ) / d := by positivity
    have heR0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have heR1 : (e : ℝ) ≤ 1 := by exact_mod_cast he1
    rw [abs_le]
    constructor <;> linarith

theorem abs_sum_centeredMultiple_Ioc_le_one {d : ℕ} (hd : 0 < d) (a b : ℕ) :
    |∑ n ∈ Ioc a b, centeredMultiple d n| ≤ 1 := by
  simpa only [← centeredMultiple_eq_centeredResidue hd] using
    abs_sum_centeredResidue_Ioc_le_one hd 0 a b

/-- Harmonic incidence discrepancy on `(a, b]` costs at most `1 / (a + 1)`. -/
theorem abs_sum_centeredResidue_harmonic_Ioc_le {d : ℕ} (hd : 0 < d) (r a b : ℕ) :
    |∑ n ∈ Ioc a b, centeredResidue d r n / (n : ℝ)| ≤ 1 / ((a : ℝ) + 1) := by
  rcases lt_or_ge b a with hlt | hab
  · simp only [Ioc_eq_empty (not_lt.mpr hlt.le), sum_empty, abs_zero]
    positivity
  set L := b - a
  have hb : b = a + L := (Nat.add_sub_of_le hab).symm
  rw [hb, ← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
    show a + L + 1 - (a + 1) = L by omega]
  have hpart (k : ℕ) (_ : k ≤ L) :
      |∑ j ∈ range k, centeredResidue d r (a + 1 + j)| ≤ 1 := by
    have h := abs_sum_centeredResidue_Ioc_le_one hd r a (a + k)
    rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
      show a + k + 1 - (a + 1) = k by omega] at h
    exact h
  have h := HTGeometry.abs_sum_mul_le_of_finite_partial
    (g := fun i => centeredResidue d r (a + 1 + i))
    (w := fun i => 1 / ((a + 1 + i : ℕ) : ℝ)) L hpart
    (fun _ => by positivity)
    (fun i => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
  simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one, one_mul, div_eq_mul_inv, mul_comm] using h

/-! ### Row-by-row Abel control of the real-place jets on centered residues -/

/-- At any degree point `n`, the entire off-diagonal jet row against a centered
congruence indicator is bounded by `2` in absolute value, uniformly in the window. -/
theorem abs_sum_jetKernel_centeredResidue_erase_le {d : ℕ} (hd : 0 < d)
    (r A B n : ℕ) (hn : n ∈ Ioc A B) :
    |∑ m ∈ (Ioc A B).erase n, centeredResidue d r m * jetKernel m n| ≤ 2 := by
  obtain ⟨hnA, hnB⟩ := mem_Ioc.mp hn
  have hsplit : (Ioc A B).erase n = Ioc A (n - 1) ∪ Ioc n B := by
    ext m
    simp only [mem_erase, mem_Ioc, mem_union]
    omega
  have hdisj : Disjoint (Ioc A (n - 1)) (Ioc n B) :=
    Ioc_disjoint_Ioc_of_le (Nat.sub_le n 1)
  rw [hsplit, sum_union hdisj]
  -- Upper half `m ∈ Ioc n B`: write `m = n + 1 + i`
  have hup_sing : |∑ m ∈ Ioc n B, centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|))| ≤ 1 / 2 := by
    rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
      show B + 1 - (n + 1) = B - n by omega]
    have hrew : (∑ i ∈ range (B - n),
          centeredResidue d r (n + 1 + i) * (1 / (2 * |((n + 1 + i : ℕ) : ℝ) - n|))) =
        ∑ i ∈ range (B - n), (1 / (2 * ((i : ℝ) + 1))) * centeredResidue d r (n + 1 + i) := by
      refine sum_congr rfl fun i _ => ?_
      have hi : ((n + 1 + i : ℕ) : ℝ) - n = (i : ℝ) + 1 := by push_cast; ring
      rw [hi, abs_of_pos (by positivity), mul_comm]
    rw [hrew]
    have h := HTGeometry.abs_sum_mul_le_of_finite_partial
      (g := fun i => centeredResidue d r (n + 1 + i))
      (w := fun i => 1 / (2 * ((i : ℝ) + 1))) (B - n)
      (fun k _ => by
        have hk := abs_sum_centeredResidue_Ioc_le_one hd r n (n + k)
        rwa [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
          show n + k + 1 - (n + 1) = k by omega] at hk)
      (fun _ => by positivity)
      (fun i => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
    simpa using h
  have hup_reg : |∑ m ∈ Ioc n B, centeredResidue d r m * (1 / (2 * ((m : ℝ) + n)))| ≤ 1 / 2 := by
    rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
      show B + 1 - (n + 1) = B - n by omega]
    have hrew : (∑ i ∈ range (B - n),
          centeredResidue d r (n + 1 + i) * (1 / (2 * (((n + 1 + i : ℕ) : ℝ) + n)))) =
        ∑ i ∈ range (B - n),
          (1 / (2 * (((n + 1 + i : ℕ) : ℝ) + n))) * centeredResidue d r (n + 1 + i) :=
      sum_congr rfl fun i _ => mul_comm _ _
    rw [hrew]
    have h := HTGeometry.abs_sum_mul_le_of_finite_partial
      (g := fun i => centeredResidue d r (n + 1 + i))
      (w := fun i => 1 / (2 * (((n + 1 + i : ℕ) : ℝ) + n))) (B - n)
      (fun k _ => by
        have hk := abs_sum_centeredResidue_Ioc_le_one hd r n (n + k)
        rwa [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
          show n + k + 1 - (n + 1) = k by omega] at hk)
      (fun _ => by positivity)
      (fun i => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
    have hw0 : 1 * (1 / (2 * (((n + 1 + 0 : ℕ) : ℝ) + n))) ≤ 1 / 2 := by
      rw [one_mul]
      exact one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
    exact h.trans hw0
  -- Lower half `m ∈ Ioc A (n - 1)`
  have hlow_sing :
      |∑ m ∈ Ioc A (n - 1), centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|))| ≤ 1 / 2 := by
    rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range]
    set L := n - 1 + 1 - (A + 1)
    have hrew : (∑ i ∈ range L,
          centeredResidue d r (A + 1 + i) * (1 / (2 * |((A + 1 + i : ℕ) : ℝ) - n|))) =
        ∑ j ∈ range L, (1 / (2 * ((j : ℝ) + 1))) * centeredResidue d r (A + 1 + (L - 1 - j)) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun j hj => ?_
      have hjL := mem_range.mp hj
      have hsub : ((A + 1 + (L - 1 - j) : ℕ) : ℝ) - n = -((j : ℝ) + 1) := by
        have hnat : A + 1 + (L - 1 - j) + (j + 1) = n := by omega
        have hR : (((A + 1 + (L - 1 - j) + (j + 1) : ℕ)) : ℝ) = n := by exact_mod_cast hnat
        push_cast at hR
        linarith
      rw [hsub, abs_neg, abs_of_pos (by positivity), mul_comm]
    rw [hrew]
    have h := HTGeometry.abs_sum_reversed_mul_le
      (g := fun i => centeredResidue d r (A + 1 + i))
      (w := fun j => 1 / (2 * ((j : ℝ) + 1))) L
      (fun u v huv => by
        rw [sum_Ico_eq_sum_range]
        have hk := abs_sum_centeredResidue_Ioc_le_one hd r (A + u) (A + v)
        rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
          show A + v + 1 - (A + u + 1) = v - u by omega] at hk
        refine (le_of_eq (congrArg abs (sum_congr rfl fun x _ => ?_))).trans hk
        rw [show A + 1 + (u + x) = A + u + 1 + x by omega])
      (fun _ => by positivity)
      (fun j => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
    simpa using h
  have hlow_reg :
      |∑ m ∈ Ioc A (n - 1), centeredResidue d r m * (1 / (2 * ((m : ℝ) + n)))| ≤ 1 / 2 := by
    rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range]
    set L := n - 1 + 1 - (A + 1)
    have hrew : (∑ i ∈ range L,
          centeredResidue d r (A + 1 + i) * (1 / (2 * (((A + 1 + i : ℕ) : ℝ) + n)))) =
        ∑ i ∈ range L,
          (1 / (2 * (((A + 1 + i : ℕ) : ℝ) + n))) * centeredResidue d r (A + 1 + i) :=
      sum_congr rfl fun i _ => mul_comm _ _
    rw [hrew]
    have h := HTGeometry.abs_sum_mul_le_of_finite_partial
      (g := fun i => centeredResidue d r (A + 1 + i))
      (w := fun i => 1 / (2 * (((A + 1 + i : ℕ) : ℝ) + n))) L
      (fun k _ => by
        have hk := abs_sum_centeredResidue_Ioc_le_one hd r A (A + k)
        rwa [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
          show A + k + 1 - (A + 1) = k by omega] at hk)
      (fun _ => by positivity)
      (fun i => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
    have hw0 : 1 * (1 / (2 * (((A + 1 + 0 : ℕ) : ℝ) + n))) ≤ 1 / 2 := by
      rw [one_mul]
      exact one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith)
    exact h.trans hw0
  have hexp (T : Finset ℕ) :
      ∑ m ∈ T, centeredResidue d r m * jetKernel m n =
        ∑ m ∈ T, centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|)) +
          ∑ m ∈ T, centeredResidue d r m * (1 / (2 * ((m : ℝ) + n))) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [jetKernel]
    ring
  rw [hexp (Ioc A (n - 1)), hexp (Ioc n B)]
  have h1 := abs_add_le
    (∑ m ∈ Ioc A (n - 1), centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|)) +
      ∑ m ∈ Ioc A (n - 1), centeredResidue d r m * (1 / (2 * ((m : ℝ) + n))))
    (∑ m ∈ Ioc n B, centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|)) +
      ∑ m ∈ Ioc n B, centeredResidue d r m * (1 / (2 * ((m : ℝ) + n))))
  have h2 := abs_add_le
    (∑ m ∈ Ioc A (n - 1), centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|)))
    (∑ m ∈ Ioc A (n - 1), centeredResidue d r m * (1 / (2 * ((m : ℝ) + n))))
  have h3 := abs_add_le
    (∑ m ∈ Ioc n B, centeredResidue d r m * (1 / (2 * |(m : ℝ) - n|)))
    (∑ m ∈ Ioc n B, centeredResidue d r m * (1 / (2 * ((m : ℝ) + n))))
  linarith

/-! ### Unconditional failure on unshifted interleaved prefixes -/

/-- At `N = 2`, the integral centered divisibility divisor `u(n) = 2 · 1_{2 ∣ n} - 1`
(realized by upper jumps `a(1) = -2, a(2) = 1`) already has `diagRealBudget < mixedPrimeDebit`. -/
theorem unshifted_prefix_two_debit_gt_budget :
    let a : ℕ → ℤ := fun j => if j = 1 then -2 else if j = 2 then 1 else 0
    let u := fun n => (upperDivisor 2 a n : ℝ)
    (∀ n ∈ Icc 1 2, u n = 2 * centeredMultiple 2 n) ∧
      diagRealBudget (Icc 1 2) u < mixedPrimeDebit (Icc 1 2) u := by
  intro a u
  have hIcc : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hu1 : u 1 = -1 := by
    simp [u, a, upperDivisor, hIcc]
  have hu2 : u 2 = 1 := by
    simp [u, a, upperDivisor, hIcc]
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [hIcc, mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl
    · rw [hu1]; norm_num [centeredMultiple]
    · rw [hu2]; norm_num [centeredMultiple]
  · rw [← not_le, mixedPrimeDebit_le_diagRealBudget_iff]
    push_neg
    have hd1 : degOne (Icc 1 2) u = -1 / 2 := by
      rw [degOne, hIcc, sum_pair (by norm_num), hu1, hu2]; norm_num
    have hd2 : degTwo (Icc 1 2) u = 0 := by
      rw [degTwo, hIcc, sum_pair (by norm_num), hu1, hu2]; ring
    have he1 : (Icc 1 2).erase 1 = {2} := by decide
    have he2 : (Icc 1 2).erase 2 = {1} := by decide
    have hj12 : jetKernel 2 1 = 2 / 3 := by rw [jetKernel]; norm_num
    have hj21 : jetKernel 1 2 = 2 / 3 := by rw [jetKernel]; norm_num
    have hc12 : contact 2 1 = Real.log 2 := by
      rw [contact, if_neg (by norm_num), if_pos (by norm_num), zero_add]
      simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hc21 : contact 1 2 = Real.log 2 := by
      rw [contact_comm, hc12]
    have hpair : combPairing (Icc 1 2) u =
        -(4 / 3 + 2 * Real.log 2 + counterterm 1 + counterterm 2) := by
      rw [combPairing, hIcc, sum_pair (by norm_num), sum_pair (by norm_num),
         ← hIcc, he1, he2, sum_singleton, sum_singleton,
        pairKernel, pairKernel, hj12, hj21, hc12, hc21, hu1, hu2]
      ring
    have hct1 : counterterm 1 = -Real.log (2 * Real.pi) := by
      rw [counterterm, show (1 : ℝ) / (2 * Real.pi) = (2 * Real.pi)⁻¹ by ring, Real.log_inv]
    have hct2 : counterterm 2 = -Real.log Real.pi := by
      rw [counterterm, show (2 : ℝ) / (2 * Real.pi) = Real.pi⁻¹ by field_simp, Real.log_inv]
    have hform : combForm (Icc 1 2) u = 4 / 3 + Real.log 2 - 2 * Real.log Real.pi := by
      rw [combForm, hd1, hd2, hpair, hct1, hct2,
        Real.log_mul (by norm_num) Real.pi_pos.ne']
      ring
    have hlog2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hlogpi : (7 / 6 : ℝ) < Real.log Real.pi := by
      rw [Real.lt_log_iff_exp_lt Real.pi_pos]
      have h6 : Real.exp (7 / 6 : ℝ) ^ 6 = Real.exp 1 ^ 7 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
      have he1' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hpi' : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
      have hpow : Real.exp 1 ^ 7 < (3.141592 : ℝ) ^ 6 := by
        have := Real.exp_pos 1
        nlinarith [pow_le_pow_left₀ this.le he1'.le 6]
      have hlt6 : Real.exp (7 / 6 : ℝ) ^ 6 < Real.pi ^ 6 := by
        rw [h6]
        exact hpow.trans (pow_lt_pow_left₀ hpi' (by norm_num) (by norm_num))
      by_contra hge
      exact hlt6.not_ge (pow_le_pow_left₀ Real.pi_pos.le (not_lt.mp hge) 6)
    rw [hform]
    linarith

theorem abs_centeredMultiple_le_one {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |centeredMultiple d n| ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : 0 ≤ 1 / (d : ℝ) ∧ 1 / (d : ℝ) ≤ 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hd1⟩
  unfold centeredMultiple
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem sum_centeredMultiple_sq_period {d : ℕ} (hd : 0 < d) (j : ℕ) :
    ∑ n ∈ Ioc (d * j) (d * (j + 1)), centeredMultiple d n ^ 2 = 1 - 1 / (d : ℝ) := by
  have hmem : d * (j + 1) ∈ Ioc (d * j) (d * (j + 1)) :=
    mem_Ioc.mpr ⟨by nlinarith, le_rfl⟩
  have honly : ∀ n ∈ (Ioc (d * j) (d * (j + 1))).erase (d * (j + 1)), ¬ d ∣ n := by
    rintro n hn ⟨k, rfl⟩
    obtain ⟨hne, hnI⟩ := mem_erase.mp hn
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hnI
    have hk1 : j < k := (Nat.mul_lt_mul_left hd).mp h1
    have hk2 : k ≤ j + 1 := (Nat.mul_le_mul_left hd).mp h2
    exact hne (by rw [show k = j + 1 by omega])
  rw [← add_sum_erase _ _ hmem]
  have h1 : centeredMultiple d (d * (j + 1)) ^ 2 = (1 - 1 / (d : ℝ)) ^ 2 := by
    rw [centeredMultiple, if_pos (dvd_mul_right d (j + 1))]
  have h2 : ∀ n ∈ (Ioc (d * j) (d * (j + 1))).erase (d * (j + 1)),
      centeredMultiple d n ^ 2 = (1 / (d : ℝ)) ^ 2 := fun n hn => by
    rw [centeredMultiple, if_neg (honly n hn), zero_sub, neg_sq]
  rw [h1, sum_congr rfl h2, sum_const, card_erase_of_mem hmem, Nat.card_Ioc]
  have hlen : d * (j + 1) - d * j = d := by ring
  rw [hlen, Nat.cast_sub hd, Nat.cast_one, nsmul_eq_mul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

private theorem sum_prime_dvd_vonMangoldt_div_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ k ∈ (Icc 2 N).filter (p ∣ ·), (Λ k : ℝ) * ((N / k : ℕ) : ℝ) ≤
      Real.log p * (N : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by positivity
  -- Nonzero terms are positive powers `p ^ (e + 1)` with `e < N`
  have hsub : ∑ k ∈ (Icc 2 N).filter (p ∣ ·), (Λ k : ℝ) * ((N / k : ℕ) : ℝ) ≤
      ∑ e ∈ range N, Real.log p * ((N : ℝ) / (p : ℝ) ^ (e + 1)) := by
    rw [← sum_filter_ne_zero]
    have hmap : ∀ k ∈ ((Icc 2 N).filter (p ∣ ·)).filter
          (fun k => (Λ k : ℝ) * ((N / k : ℕ) : ℝ) ≠ 0),
        ∃ e ∈ range N, k = p ^ (e + 1) := by
      intro k hk
      obtain ⟨hk1, hne⟩ := mem_filter.mp hk
      obtain ⟨hkI, hpk⟩ := mem_filter.mp hk1
      have hΛ0 : Λ k ≠ 0 := fun h0 => hne (by simp [h0])
      rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hΛ0
      obtain ⟨q, e, hq, he, rfl⟩ := hΛ0
      have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.nat_prime).mp (hp.dvd_of_dvd_pow hpk)
      subst hqp
      have hkN := (mem_Icc.mp hkI).2
      have hlt : e < N + 1 := by
        have h2e : e < 2 ^ e := Nat.lt_two_pow_self
        have hpe : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
        omega
      exact ⟨e - 1, mem_range.mpr (by omega), by rw [Nat.sub_add_cancel he]⟩
    let g : ℕ → ℕ := fun k => Nat.log p k - 1
    have hg : ∀ k ∈ ((Icc 2 N).filter (p ∣ ·)).filter
          (fun k => (Λ k : ℝ) * ((N / k : ℕ) : ℝ) ≠ 0),
        g k ∈ range N ∧ p ^ (g k + 1) = k := by
      intro k hk
      obtain ⟨e, he, rfl⟩ := hmap k hk
      dsimp [g]
      rw [Nat.log_pow hp.one_lt, Nat.add_sub_cancel]
      exact ⟨he, rfl⟩
    calc _ ≤ ∑ k ∈ ((Icc 2 N).filter (p ∣ ·)).filter
            (fun k => (Λ k : ℝ) * ((N / k : ℕ) : ℝ) ≠ 0),
          Real.log p * ((N : ℝ) / (p ^ (g k + 1) : ℕ)) := by
          refine sum_le_sum fun k hk => ?_
          rw [(hg k hk).2]
          have hk0 : (0 : ℝ) < k := by
            have := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hk).1).1).1
            exact_mod_cast (by omega : 0 < k)
          have hΛ : (Λ k : ℝ) = Real.log p := by
            rw [← (hg k hk).2, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
              ArithmeticFunction.vonMangoldt_apply_prime hp]
          rw [hΛ]
          refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by linarith))
          rw [le_div_iff₀ hk0]
          exact_mod_cast Nat.div_mul_le_self N k
      _ = ∑ e ∈ (((Icc 2 N).filter (p ∣ ·)).filter
            (fun k => (Λ k : ℝ) * ((N / k : ℕ) : ℝ) ≠ 0)).image g,
          Real.log p * ((N : ℝ) / (p : ℝ) ^ (e + 1)) := by
          rw [sum_image]
          · refine sum_congr rfl fun k _ => by push_cast; rfl
          · intro x hx y hy hxy
            rw [← (hg x hx).2, ← (hg y hy).2, hxy]
      _ ≤ ∑ e ∈ range N, Real.log p * ((N : ℝ) / (p : ℝ) ^ (e + 1)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun e he => ?_) (fun _ _ _ => by positivity)
          obtain ⟨k, hk, rfl⟩ := mem_image.mp he
          exact (hg k hk).1
  refine hsub.trans ?_
  have hgeo : ∑ e ∈ range N, (1 / (p : ℝ)) ^ (e + 1) ≤ 1 := by
    calc ∑ e ∈ range N, (1 / (p : ℝ)) ^ (e + 1)
        ≤ ∑ e ∈ range N, ((1 / 2 : ℝ)) ^ (e + 1) :=
          sum_le_sum fun e _ => pow_le_pow_left₀ (by positivity)
            (one_div_le_one_div_of_le (by norm_num) hp2) _
      _ = (1 - (1 / 2 : ℝ) ^ N) := by
          induction N with
          | zero => simp
          | succ n ih =>
            rw [sum_range_succ, ih]
            ring
      _ ≤ 1 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]
  calc ∑ e ∈ range N, Real.log p * ((N : ℝ) / (p : ℝ) ^ (e + 1))
      = Real.log p * (N : ℝ) * ∑ e ∈ range N, (1 / (p : ℝ)) ^ (e + 1) := by
        rw [mul_sum]
        refine sum_congr rfl fun e _ => ?_
        rw [one_div_pow]
        ring
    _ ≤ Real.log p * (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hgeo (mul_nonneg (Real.log_nonneg (by linarith)) (Nat.cast_nonneg N))
    _ = Real.log p * (N : ℝ) := mul_one _

/-- On unshifted prefixes `[1, N]`, the Weil form of `1_{p ∣ n} - 1/p` diverges to `-∞`
for every prime `p`. In particular, divisor incidence fails to pay the mixed prime
debit on `[1, N]` for all sufficiently large `N`. -/
theorem tendsto_combForm_Icc_centeredMultiple_atBot {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N : ℕ => combForm (Icc 1 N) (centeredMultiple p)) atTop atBot ∧
      ∀ᶠ N : ℕ in atTop,
        diagRealBudget (Icc 1 N) (centeredMultiple p) <
          mixedPrimeDebit (Icc 1 N) (centeredMultiple p) := by
  set v := centeredMultiple p
  have hp0 : 0 < p := hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hfac : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hub : ∀ N : ℕ, p ≤ N →
      combForm (Icc 1 N) v ≤
        2 + (1 - 1 / (p : ℝ)) * (((N / p : ℕ) : ℝ) * Real.log p) +
          (p : ℝ) * Real.log N + 2 * (N : ℝ) + 2 * Real.log p * (N : ℝ) -
          (1 - 1 / (p : ℝ)) * Real.log ((N / p).factorial : ℝ) := by
    intro N hpN
    have _hN1 : 1 ≤ N := hp0.trans_le hpN
    have hIoc : Icc 1 N = Ioc 0 N := Icc_one_eq_Ioc_zero N
    -- 1. Pole bound
    have hd1 : |degOne (Icc 1 N) v| ≤ 1 := by
      rw [degOne, hIoc]
      have hrew : (∑ n ∈ Ioc 0 N, v n / (n : ℝ)) =
          ∑ n ∈ Ioc 0 N, centeredResidue p 0 n / (n : ℝ) :=
        sum_congr rfl fun n _ => by rw [centeredMultiple_eq_centeredResidue hp0]
      rw [hrew]
      simpa using abs_sum_centeredResidue_harmonic_Ioc_le hp0 0 0 N
    have hd2 : |degTwo (Icc 1 N) v| ≤ 1 := by
      rw [degTwo, hIoc]
      exact abs_sum_centeredMultiple_Ioc_le_one hp0 0 N
    have hpole : 2 * (degOne (Icc 1 N) v * degTwo (Icc 1 N) v) ≤ 2 := by
      have habs : |degOne (Icc 1 N) v * degTwo (Icc 1 N) v| ≤ 1 * 1 := by
        rw [abs_mul]
        exact mul_le_mul hd1 hd2 (abs_nonneg _) zero_le_one
      linarith [(abs_le.mp habs).2]
    -- 2. Jet bound
    have hjet : -(∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n) ≤ 2 * N := by
      have habs : |∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n| ≤ 2 * N := by
        calc |∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n|
            ≤ ∑ n ∈ Icc 1 N, |∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ _n ∈ Icc 1 N, (2 : ℝ) := by
              refine sum_le_sum fun n hn => ?_
              have hfactor : (∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n) =
                  v n * ∑ m ∈ (Ioc 0 N).erase n, centeredResidue p 0 m * jetKernel m n := by
                rw [hIoc, mul_sum]
                refine sum_congr rfl fun m _ => ?_
                rw [← centeredMultiple_eq_centeredResidue hp0]
                ring
              rw [hfactor, abs_mul]
              have hv := abs_centeredMultiple_le_one hp0 n
              have hr := abs_sum_jetKernel_centeredResidue_erase_le hp0 0 0 N n (hIoc ▸ hn)
              nlinarith [abs_nonneg (v n)]
          _ = 2 * N := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      linarith [(abs_le.mp habs).1]
    -- 3. Diagonal bound
    set M := N / p
    have hpM : p * M ≤ N := Nat.mul_div_le N p
    have hpart : Ioc 0 (p * M) = (range M).biUnion (fun j => Ioc (p * j) (p * (j + 1))) := by
      induction M with
      | zero => simp
      | succ m ih =>
        rw [range_succ, biUnion_insert, union_comm, ← ih]
        exact (Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by nlinarith)).symm
    have hpdisj : Set.PairwiseDisjoint (range M : Set ℕ) (fun j => Ioc (p * j) (p * (j + 1))) := by
      intro i _ j _ hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact Ioc_disjoint_Ioc_of_le (by nlinarith)
      · exact (Ioc_disjoint_Ioc_of_le (by nlinarith)).symm
    have hdiag : ∑ n ∈ Icc 1 N, v n ^ 2 * counterterm n ≤
        (1 - 1 / (p : ℝ)) * ((M : ℝ) * Real.log p + Real.log (M.factorial : ℝ)) +
          (p : ℝ) * Real.log N := by
      have hsplit : Icc 1 N = Ioc 0 (p * M) ∪ Ioc (p * M) N := by
        rw [hIoc]
        exact (Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hpM).symm
      rw [hsplit, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
      have hct_le : ∀ n : ℕ, 1 ≤ n → counterterm n ≤ Real.log n := fun n hn => by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        rw [counterterm]
        exact Real.log_le_log (by positivity) (div_le_self hn0.le h2pi)
      have hmain : ∑ n ∈ Ioc 0 (p * M), v n ^ 2 * counterterm n ≤
          (1 - 1 / (p : ℝ)) * ((M : ℝ) * Real.log p + Real.log (M.factorial : ℝ)) := by
        rw [hpart, sum_biUnion hpdisj]
        calc ∑ j ∈ range M, ∑ n ∈ Ioc (p * j) (p * (j + 1)), v n ^ 2 * counterterm n
            ≤ ∑ j ∈ range M,
                (1 - 1 / (p : ℝ)) * (Real.log p + Real.log ((j + 1 : ℕ) : ℝ)) := by
              refine sum_le_sum fun j _ => ?_
              have hup : ∀ n ∈ Ioc (p * j) (p * (j + 1)),
                  counterterm n ≤ Real.log p + Real.log ((j + 1 : ℕ) : ℝ) := fun n hn => by
                obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
                refine (hct_le n (by omega)).trans ?_
                rw [← Real.log_mul (by positivity) (by positivity)]
                exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn2)
              calc ∑ n ∈ Ioc (p * j) (p * (j + 1)), v n ^ 2 * counterterm n
                  ≤ ∑ n ∈ Ioc (p * j) (p * (j + 1)),
                      v n ^ 2 * (Real.log p + Real.log ((j + 1 : ℕ) : ℝ)) :=
                    sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hup n hn) (sq_nonneg _)
                _ = (1 - 1 / (p : ℝ)) * (Real.log p + Real.log ((j + 1 : ℕ) : ℝ)) := by
                    rw [← sum_mul, sum_centeredMultiple_sq_period hp0]
          _ = (1 - 1 / (p : ℝ)) * ((M : ℝ) * Real.log p + Real.log (M.factorial : ℝ)) := by
              rw [← mul_sum, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
              have hlogM := sum_log_Icc M
              rw [AbsoluteGeometryOfSpecZ.sum_Icc_one_eq_sum_range] at hlogM
              have hcomm : ∑ k ∈ range M, Real.log ((1 + k : ℕ) : ℝ) =
                  ∑ j ∈ range M, Real.log ((j + 1 : ℕ) : ℝ) :=
                sum_congr rfl fun j _ => by rw [Nat.add_comm]
              rw [← hcomm, hlogM]
      have htail : ∑ n ∈ Ioc (p * M) N, v n ^ 2 * counterterm n ≤ (p : ℝ) * Real.log N := by
        calc ∑ n ∈ Ioc (p * M) N, v n ^ 2 * counterterm n
            ≤ ∑ _n ∈ Ioc (p * M) N, Real.log N := by
              refine sum_le_sum fun n hn => ?_
              obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
              have hctN : counterterm n ≤ Real.log N :=
                (hct_le n (by omega)).trans
                  (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn2))
              have hv1 : v n ^ 2 ≤ 1 := by
                have := abs_centeredMultiple_le_one hp0 n
                nlinarith [sq_abs (v n)]
              nlinarith [Real.log_natCast_nonneg N, sq_nonneg (v n)]
          _ ≤ (p : ℝ) * Real.log N := by
              rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
              have hrem : N - p * M < p := by
                have := Nat.div_add_mod N p
                have := Nat.mod_lt N hp0
                omega
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrem.le) (Real.log_natCast_nonneg N)
      linarith
    -- 4. Contact lower bound
    have hcont : 2 * (1 - 1 / (p : ℝ)) * Real.log (M.factorial : ℝ) - 2 * Real.log p * N ≤
        ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * contact m n := by
      have hsym : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * contact m n =
          2 * ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m), v m * v (m * k) * (Λ k : ℝ) := by
        have hsplit_c : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * contact m n =
            (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * (if m ∣ n then (Λ (n / m) : ℝ) else 0)) +
              ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * (if n ∣ m then (Λ (m / n) : ℝ) else 0) := by
          simp only [contact, mul_add, sum_add_distrib]
        have hswap1 : (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
              v m * v n * (if m ∣ n then (Λ (n / m) : ℝ) else 0)) =
            ∑ m ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).erase m,
              v m * v n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) :=
          Finset.sum_comm' (s' := fun m => (Icc 1 N).erase m) (t' := Icc 1 N) fun n m => by
            simp only [mem_erase]; tauto
        have hswap2 : (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
              v m * v n * (if n ∣ m then (Λ (m / n) : ℝ) else 0)) =
            ∑ m ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).erase m,
              v m * v n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) :=
          sum_congr rfl fun n _ => sum_congr rfl fun m _ => by ring
        rw [hsplit_c, hswap1, hswap2, ← two_mul]
        congr 1
        refine sum_congr rfl fun m hm => ?_
        have hm0 : 0 < m := (mem_Icc.mp hm).1
        have hfilt : ∑ n ∈ (Icc 1 N).erase m, v m * v n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) =
            ∑ n ∈ ((Icc 1 N).erase m).filter (m ∣ ·), v m * v n * (Λ (n / m) : ℝ) := by
          rw [sum_filter]
          exact sum_congr rfl fun n _ => by split_ifs <;> ring
        rw [hfilt]
        refine sum_nbij' (fun n => n / m) (fun k => m * k) ?_ ?_ ?_ ?_ ?_
        · intro n hn
          obtain ⟨hn1, k, rfl⟩ := mem_filter.mp hn
          obtain ⟨hne, hnI⟩ := mem_erase.mp hn1
          rw [Nat.mul_div_cancel_left k hm0]
          have hk0 : k ≠ 0 := by rintro rfl; simp at hnI
          have hk1 : k ≠ 1 := by rintro rfl; exact hne (mul_one m)
          exact mem_Icc.mpr ⟨by omega, (Nat.le_div_iff_mul_le hm0).mpr
            (by simpa only [mul_comm] using (mem_Icc.mp hnI).2)⟩
        · intro k hk
          obtain ⟨hk2, hktop⟩ := mem_Icc.mp hk
          refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_Icc.mpr ⟨by nlinarith, ?_⟩⟩, dvd_mul_right m k⟩
          · intro h
            have := Nat.eq_of_mul_eq_mul_left hm0 (h.trans (mul_one m).symm)
            omega
          · exact (Nat.mul_le_mul_left m hktop).trans (Nat.mul_div_le N m)
        · intro n hn; exact Nat.mul_div_cancel' (mem_filter.mp hn).2
        · intro k _; exact Nat.mul_div_cancel_left k hm0
        · intro n hn
          rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]
      rw [hsym]
      have hpt : ∀ m k : ℕ,
          v m ^ 2 * (Λ k : ℝ) - (if p ∣ k then (Λ k : ℝ) else 0) ≤ v m * v (m * k) * (Λ k : ℝ) := by
        intro m k
        have hΛ0 : (0 : ℝ) ≤ Λ k := ArithmeticFunction.vonMangoldt_nonneg
        by_cases hpm : p ∣ m
        · have hpmk : p ∣ m * k := dvd_mul_of_dvd_left hpm k
          have heq : v (m * k) = v m := by simp [v, centeredMultiple, hpm, hpmk]
          rw [heq]
          have : (0 : ℝ) ≤ if p ∣ k then (Λ k : ℝ) else 0 := by split_ifs <;> positivity
          linarith [sq_eq_mul_self (v m) ▸ le_rfl]
        · by_cases hpk : p ∣ k
          · have hpmk : p ∣ m * k := dvd_mul_of_dvd_right hpk m
            have hd : v m * v (m * k) - v m ^ 2 = -1 / (p : ℝ) := by
              simp only [v, centeredMultiple, if_neg hpm, if_pos hpmk]
              ring
            rw [if_pos hpk]
            have h1p : -1 ≤ -(1 / (p : ℝ)) := by
              have : (1 : ℝ) / p ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
              linarith
            nlinarith
          · have hpmk : ¬ p ∣ m * k := fun h =>
              (hp.dvd_mul.mp h).elim hpm hpk
            have heq : v (m * k) = v m := by simp [v, centeredMultiple, hpm, hpmk]
            rw [heq, if_neg hpk]
            linarith [sq_eq_mul_self (v m) ▸ le_rfl]
      have hsum_ge : ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m),
            (v m ^ 2 * (Λ k : ℝ) - (if p ∣ k then (Λ k : ℝ) else 0)) ≤
          ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m), v m * v (m * k) * (Λ k : ℝ) :=
        sum_le_sum fun m _ => sum_le_sum fun k _ => hpt m k
      have hcheb : ∀ K : ℕ, ∑ k ∈ Icc 2 K, (Λ k : ℝ) = chebyshev K := fun K => by
        rcases lt_or_ge K 1 with hK | hK
        · have h1 : Icc 2 K = ∅ := Icc_eq_empty_of_lt (by omega)
          have h2 : Icc 1 K = ∅ := Icc_eq_empty_of_lt (by omega)
          rw [chebyshev, h1, h2]
        · have hsplitK : Icc 1 K = insert 1 (Icc 2 K) := by
            ext k; simp only [mem_Icc, mem_insert]; omega
          rw [chebyshev, hsplitK, sum_insert (by simp),
            ArithmeticFunction.vonMangoldt_apply_one, zero_add]
      have hgood : (1 - 1 / (p : ℝ)) * Real.log (M.factorial : ℝ) ≤
          ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m), v m ^ 2 * (Λ k : ℝ) := by
        have h1 : ∀ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m), v m ^ 2 * (Λ k : ℝ) =
            v m ^ 2 * chebyshev (N / m) := fun m _ => by rw [← mul_sum, hcheb]
        rw [sum_congr rfl h1]
        have hsub : Ioc 0 (p * M) ⊆ Icc 1 N := by
          rw [hIoc]; exact Ioc_subset_Ioc_right hpM
        refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))
        rw [hpart, sum_biUnion hpdisj]
        have hmono : Monotone chebyshev := fun a b hab =>
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hab)
            fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
        calc (1 - 1 / (p : ℝ)) * Real.log (M.factorial : ℝ)
            = (1 - 1 / (p : ℝ)) * ∑ j ∈ range M, chebyshev (M / (j + 1)) := by
              rw [← sum_chebyshev_div M, AbsoluteGeometryOfSpecZ.sum_Icc_one_eq_sum_range]
              congr 1
              exact sum_congr rfl fun j _ => by rw [Nat.add_comm]
          _ = ∑ j ∈ range M, (1 - 1 / (p : ℝ)) * chebyshev (M / (j + 1)) := mul_sum _ _ _
          _ ≤ ∑ j ∈ range M, ∑ m ∈ Ioc (p * j) (p * (j + 1)), v m ^ 2 * chebyshev (N / m) := by
              refine sum_le_sum fun j _ => ?_
              rw [← sum_centeredMultiple_sq_period hp0 j, sum_mul]
              refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hmono ?_) (sq_nonneg _)
              obtain ⟨_, hm2⟩ := mem_Ioc.mp hm
              have hdiv1 : M / (j + 1) = N / (p * (j + 1)) := by
                rw [Nat.div_div_eq_div_mul, mul_comm]
              rw [hdiv1]
              exact Nat.div_le_div_left hm2 (by omega)
      have herr : ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m), (if p ∣ k then (Λ k : ℝ) else 0) ≤
          Real.log p * N := by
        have hex : ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 (N / m), (if p ∣ k then (Λ k : ℝ) else 0) =
            ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 2 N,
              if k ≤ N / m then (if p ∣ k then (Λ k : ℝ) else 0) else 0 := by
          refine sum_congr rfl fun m _ => ?_
          rw [← sum_filter]
          have hf : (Icc 2 N).filter (fun k => k ≤ N / m) = Icc 2 (N / m) := by
            ext k; simp only [mem_filter, mem_Icc]
            have := Nat.div_le_self N m
            omega
          rw [hf]
        rw [hex, sum_comm]
        calc ∑ k ∈ Icc 2 N, ∑ m ∈ Icc 1 N,
              (if k ≤ N / m then (if p ∣ k then (Λ k : ℝ) else 0) else 0)
            = ∑ k ∈ (Icc 2 N).filter (p ∣ ·), (Λ k : ℝ) * ((N / k : ℕ) : ℝ) := by
              rw [sum_filter]
              refine sum_congr rfl fun k hk => ?_
              have hk0 : 0 < k := by have := (mem_Icc.mp hk).1; omega
              by_cases hpk : p ∣ k
              · simp only [if_pos hpk, ← sum_filter]
                have hf2 : (Icc 1 N).filter (fun m => k ≤ N / m) = Icc 1 (N / k) := by
                  ext m; simp only [mem_filter, mem_Icc]
                  constructor
                  · rintro ⟨⟨hm1, _⟩, hkm⟩
                    exact ⟨hm1, (Nat.le_div_iff_mul_le hk0).mpr
                      (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hm1).mp hkm)⟩
                  · rintro ⟨hm1, hmk⟩
                    exact ⟨⟨hm1, hmk.trans (Nat.div_le_self N k)⟩,
                      (Nat.le_div_iff_mul_le hm1).mpr
                        (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hk0).mp hmk)⟩
                rw [hf2, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]
              · simp [hpk]
          _ ≤ Real.log p * N := sum_prime_dvd_vonMangoldt_div_le hp N
      have hsub_dist : ∀ m ∈ Icc 1 N,
          ∑ k ∈ Icc 2 (N / m), (v m ^ 2 * (Λ k : ℝ) - (if p ∣ k then (Λ k : ℝ) else 0)) =
            (∑ k ∈ Icc 2 (N / m), v m ^ 2 * (Λ k : ℝ)) -
              ∑ k ∈ Icc 2 (N / m), (if p ∣ k then (Λ k : ℝ) else 0) :=
        fun _ _ => sum_sub_distrib _ _
      rw [sum_congr rfl hsub_dist, sum_sub_distrib] at hsum_ge
      linarith
    -- Assemble all four bounds
    have hform : combForm (Icc 1 N) v =
        2 * (degOne (Icc 1 N) v * degTwo (Icc 1 N) v) +
          (∑ n ∈ Icc 1 N, v n ^ 2 * counterterm n) -
          (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n) -
          (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * contact m n) := by
      rw [combForm, combPairing]
      have hpk : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * pairKernel m n =
          (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * jetKernel m n) +
            ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, v m * v n * contact m n := by
        simp only [pairKernel, mul_add, sum_add_distrib]
      rw [hpk]
      ring
    rw [hform]
    rw [mul_add] at hdiag
    linarith
  have htend : Tendsto (fun N : ℕ => combForm (Icc 1 N) v) atTop atBot := by
    rw [tendsto_atBot]
    intro B
    set C₂ : ℝ := 3 + 3 * Real.log p + p
    set L₁ : ℝ := (4 * (p : ℝ) * C₂ + 8) / (1 - 1 / (p : ℝ))
    set K₁ : ℕ := ⌈Real.exp L₁⌉₊ + 2
    set N₀ : ℕ := p * (2 * K₁ + ⌈|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10⌉₊ + 4)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hpN : p ≤ N := le_trans (Nat.le_mul_of_pos_right p (by positivity)) hN
    have hmain := hub N hpN
    set M := N / p
    have hMK : 2 * K₁ ≤ M := by
      have : 2 * K₁ + ⌈|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10⌉₊ + 4 ≤ M :=
        (Nat.le_div_iff_mul_le hp0).mpr (by rw [mul_comm]; exact hN)
      omega
    have hMB : ⌈|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10⌉₊ + 2 * K₁ + 4 ≤ M := by
      have : 2 * K₁ + ⌈|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10⌉₊ + 4 ≤ M :=
        (Nat.le_div_iff_mul_le hp0).mpr (by rw [mul_comm]; exact hN)
      omega
    have hlogM : ((M - K₁ : ℕ) : ℝ) * L₁ ≤ Real.log (M.factorial : ℝ) := by
      rw [← sum_log_Icc M]
      have hsub : Ioc K₁ M ⊆ Icc 1 M := fun k hk =>
        mem_Icc.mpr ⟨by have := (mem_Ioc.mp hk).1; omega, (mem_Ioc.mp hk).2⟩
      calc ((M - K₁ : ℕ) : ℝ) * L₁
          = ∑ _k ∈ Ioc K₁ M, L₁ := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Ioc K₁ M, Real.log k := by
            refine sum_le_sum fun k hk => ?_
            have hkK := (mem_Ioc.mp hk).1
            have hexp : Real.exp L₁ ≤ k :=
              (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp L₁⌉₊ ≤ k by omega))
            exact (Real.le_log_iff_exp_le (by exact_mod_cast (by omega : 0 < k))).mpr hexp
        _ ≤ ∑ k ∈ Icc 1 M, Real.log k :=
            sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
              Real.log_natCast_nonneg k
    have hlogN : Real.log N ≤ N := by
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (hp0.trans_le hpN)
      linarith [Real.log_le_sub_one_of_pos hN0]
    have hNM : (N : ℝ) ≤ (p : ℝ) * ((M : ℝ) + 1) := by
      exact_mod_cast (Nat.lt_mul_div_succ N hp0).le
    have hM2 : (M : ℝ) / 2 ≤ ((M - K₁ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (2 : ℝ) * K₁ ≤ M := by exact_mod_cast hMK
      linarith
    have hL₁_nonneg : 0 ≤ L₁ := by
      have hC₂ : 0 ≤ C₂ := by
        dsimp [C₂]
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ p)
        positivity
      exact div_nonneg (by positivity) hfac.le
    have hprod : (1 - 1 / (p : ℝ)) * (((M : ℝ) / 2) * L₁) =
        2 * (p : ℝ) * C₂ * M + 4 * M := by
      dsimp [L₁]
      field_simp [hfac.ne']
      ring
    have hhalf : 2 * (p : ℝ) * C₂ * M + 4 * M ≤
        (1 - 1 / (p : ℝ)) * Real.log (M.factorial : ℝ) := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right hM2 hL₁_nonneg).trans hlogM) hfac.le
    have hlin : 2 + (1 - 1 / (p : ℝ)) * ((M : ℝ) * Real.log p) + (p : ℝ) * Real.log N +
          2 * (N : ℝ) + 2 * Real.log p * (N : ℝ) ≤
        2 + 2 * (p : ℝ) * C₂ * M := by
      have hlp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
      have hNle : (N : ℝ) ≤ 2 * (p : ℝ) * M := by nlinarith
      have h1 : (1 - 1 / (p : ℝ)) * ((M : ℝ) * Real.log p) ≤ (p : ℝ) * Real.log p * M := by
        have h1p : 1 - 1 / (p : ℝ) ≤ p := by linarith [show (0 : ℝ) ≤ 1 / p by positivity]
        have hMlp : 0 ≤ (M : ℝ) * Real.log p := mul_nonneg (by positivity) hlp
        calc (1 - 1 / (p : ℝ)) * ((M : ℝ) * Real.log p)
            ≤ (p : ℝ) * ((M : ℝ) * Real.log p) := mul_le_mul_of_nonneg_right h1p hMlp
          _ = (p : ℝ) * Real.log p * M := by ring
      have h2 : (p : ℝ) * Real.log N ≤ 2 * (p : ℝ) ^ 2 * M := by
        calc (p : ℝ) * Real.log N ≤ (p : ℝ) * N := mul_le_mul_of_nonneg_left hlogN (by positivity)
          _ ≤ (p : ℝ) * (2 * (p : ℝ) * M) := mul_le_mul_of_nonneg_left hNle (by positivity)
          _ = 2 * (p : ℝ) ^ 2 * M := by ring
      have h3 : 2 * Real.log p * (N : ℝ) ≤ 4 * (p : ℝ) * Real.log p * M := by
        calc 2 * Real.log p * (N : ℝ)
            ≤ 2 * Real.log p * (2 * (p : ℝ) * M) :=
              mul_le_mul_of_nonneg_left hNle (mul_nonneg (by norm_num) hlp)
          _ = 4 * (p : ℝ) * Real.log p * M := by ring
      have hexpC : 2 * (p : ℝ) * C₂ * M =
          6 * (p : ℝ) * M + 6 * (p : ℝ) * Real.log p * M + 2 * (p : ℝ) ^ 2 * M := by
        dsimp [C₂]; ring
      have hpM_nonneg : 0 ≤ (p : ℝ) * M := by positivity
      have hpMlp_nonneg : 0 ≤ (p : ℝ) * Real.log p * M := by positivity
      rw [hexpC]
      linarith
    have hBceil : |B| + 10 ≤ (M : ℝ) := by
      have hceil := Nat.le_ceil (|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10)
      have hMge : (⌈|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10⌉₊ : ℝ) ≤ M := by
        exact_mod_cast (show ⌈|B| + (1 - 1 / (p : ℝ)) * K₁ * L₁ + 10⌉₊ ≤ M by omega)
      have : 0 ≤ (1 - 1 / (p : ℝ)) * K₁ * L₁ := by positivity
      linarith
    have hBabs : -B ≤ |B| := neg_le_abs B
    linarith
  refine ⟨htend, ?_⟩
  filter_upwards [htend.eventually (gt_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with N hN
  rw [combForm_eq_diagRealBudget_sub_mixedPrimeDebit] at hN
  linarith

/-- Even on a late comb `(N, N + 3KN]`, the mixed prime debit of `1_{p ∣ n} - 1/p`
is strictly positive for every prime `3K < p ≤ KN` once `N ≥ 4`: the prime-and-boundary
term is strictly negative before spending the diagonal and real-place budget. -/
theorem lateComb_mixedPrimeDebit_pos {K N p : ℕ} (hK : 1 ≤ K) (hN : 4 ≤ N)
    (hp : p.Prime) (hpK : 3 * K < p) (hptop : p ≤ K * N) :
    0 < mixedPrimeDebit (Ioc N (N + 3 * K * N)) (centeredMultiple p) := by
  set S := Ioc N (N + 3 * K * N)
  set v := centeredMultiple p
  have hp0 : 0 < p := hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  -- Bound the pole product by `2 / (N + 1)`
  have hd1 : |degOne S v| ≤ 1 / ((N : ℝ) + 1) := by
    rw [degOne]
    have h := abs_sum_centeredResidue_harmonic_Ioc_le hp0 0 N (N + 3 * K * N)
    rwa [sum_congr rfl fun n _ => by rw [← centeredMultiple_eq_centeredResidue hp0]] at h
  have hd2 : |degTwo S v| ≤ 1 := by
    rw [degTwo]; exact abs_sum_centeredMultiple_Ioc_le_one hp0 N (N + 3 * K * N)
  have hpole : 2 * (degOne S v * degTwo S v) ≤ 2 / ((N : ℝ) + 1) := by
    have habs : |degOne S v * degTwo S v| ≤ (1 / ((N : ℝ) + 1)) * 1 := by
      rw [abs_mul]; exact mul_le_mul hd1 hd2 (abs_nonneg _) (by positivity)
    linarith [(abs_le.mp habs).2]
  -- Every contact pair in `S` has ratio `2 ≤ r ≤ 3K < p`, where `v (r * m) = v m`, so `v m * v n ≥ 0`
  have hnonneg : ∀ n ∈ S, ∀ m ∈ S.erase n, 0 ≤ v m * v n * contact m n := by
    intro n hn m hm
    obtain ⟨hmne, hmS⟩ := mem_erase.mp hm
    have hside : ∀ a b : ℕ, a ∈ S → b ∈ S → a ≠ b →
        0 ≤ v a * v b * (if a ∣ b then (Λ (b / a) : ℝ) else 0) := by
      intro a b ha hb hab
      by_cases hd : a ∣ b
      · obtain ⟨r, rfl⟩ := hd
        obtain ⟨ha1, -⟩ := mem_Ioc.mp ha
        obtain ⟨-, hb2⟩ := mem_Ioc.mp hb
        have hr0 : r ≠ 0 := by rintro rfl; omega
        have hr1 : r ≠ 1 := by rintro rfl; exact hab (mul_one a)
        have hr3K : r ≤ 3 * K := by
          by_contra hgt
          have : (N + 1) * (3 * K + 1) ≤ a * r := Nat.mul_le_mul ha1 (by omega)
          nlinarith
        have hpr : ¬ p ∣ r := fun hdiv => absurd (Nat.le_of_dvd (by omega) hdiv) (by omega)
        have hv : v (a * r) = v a := by
          simp only [v, centeredMultiple]
          congr 1
          by_cases hpa : p ∣ a
          · simp [hpa, dvd_mul_of_dvd_left hpa r]
          · have hpar : ¬ p ∣ a * r := fun h => (hp.dvd_mul.mp h).elim hpa hpr
            simp [hpa, hpar]
        rw [hv, if_pos (dvd_mul_right a r)]
        exact mul_nonneg (mul_self_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
      · simp [hd]
    have hexp : v m * v n * contact m n =
        v m * v n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) +
          v n * v m * (if n ∣ m then (Λ (m / n) : ℝ) else 0) := by
      rw [contact]; ring
    rw [hexp]
    exact add_nonneg (hside m n hmS hn hmne) (hside n m hn hmS hmne.symm)
  -- Exhibit one multiple `m₀ = p * (N / p + 1) ∈ (N, 2N]` with `2 * m₀ ∈ S`
  set m₀ := p * (N / p + 1)
  have hm₀_gt : N < m₀ := by
    dsimp [m₀]; rw [mul_comm]; exact Nat.lt_mul_div_succ N hp0
  have hm₀_le : m₀ ≤ 2 * K * N := by
    have h1 : p * (N / p) ≤ N := Nat.mul_div_le N p
    have h2 : N ≤ K * N := Nat.le_mul_of_pos_left N hK
    dsimp [m₀]
    linarith
  have hm₀S : m₀ ∈ S := mem_Ioc.mpr ⟨hm₀_gt, by omega⟩
  have h2m₀S : 2 * m₀ ∈ S := mem_Ioc.mpr ⟨by omega, by omega⟩
  have hne : m₀ ≠ 2 * m₀ := by omega
  have hsingle : (1 / 2 : ℝ) * Real.log 2 ≤
      ∑ n ∈ S, ∑ m ∈ S.erase n, v m * v n * contact m n := by
    calc (1 / 2 : ℝ) * Real.log 2
        ≤ v m₀ * v (2 * m₀) * contact m₀ (2 * m₀) := by
          have hvm₀ : v m₀ = 1 - 1 / (p : ℝ) := by
            simp [v, centeredMultiple, m₀, dvd_mul_right]
          have hv2m₀ : v (2 * m₀) = 1 - 1 / (p : ℝ) := by
            have : p ∣ 2 * m₀ := dvd_mul_of_dvd_right (dvd_mul_right p _) 2
            simp [v, centeredMultiple, this]
          have hc : contact m₀ (2 * m₀) = Real.log 2 := by
            rw [contact_of_dvd_of_lt ⟨2, by ring⟩ (by omega),
              show 2 * m₀ / m₀ = 2 by rw [mul_comm, Nat.mul_div_cancel_left 2 (by omega)],
              ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
          rw [hvm₀, hv2m₀, hc]
          have hhalf : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
            have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
            linarith
          have hsq : (1 / 4 : ℝ) ≤ (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by nlinarith
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          nlinarith
      _ ≤ ∑ m ∈ S.erase (2 * m₀), v m * v (2 * m₀) * contact m (2 * m₀) :=
          single_le_sum (fun m hm => hnonneg _ h2m₀S m hm) (mem_erase.mpr ⟨hne, hm₀S⟩)
      _ ≤ ∑ n ∈ S, ∑ m ∈ S.erase n, v m * v n * contact m n :=
          single_le_sum (fun n hn => sum_nonneg fun m hm => hnonneg n hn m hm) h2m₀S
  rw [mixedPrimeDebit, mixedPrimeDebitW]
  have hcont_eq : ∀ m n, contactW (fun k => (Λ k : ℝ)) m n = contact m n := fun _ _ => rfl
  simp only [hcont_eq]
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hN4 : 2 / ((N : ℝ) + 1) ≤ 2 / 5 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  linarith

#print axioms combForm_eq_diagRealBudget_sub_mixedPrimeDebit
#print axioms interleaved_self_budget_and_debit
#print axioms abs_sum_centeredResidue_Ioc_le_one
#print axioms abs_sum_jetKernel_centeredResidue_erase_le
#print axioms unshifted_prefix_two_debit_gt_budget
#print axioms tendsto_combForm_Icc_centeredMultiple_atBot
#print axioms lateComb_mixedPrimeDebit_pos

end GaloisForLFunctions.SignedArithmeticCorrespondences
