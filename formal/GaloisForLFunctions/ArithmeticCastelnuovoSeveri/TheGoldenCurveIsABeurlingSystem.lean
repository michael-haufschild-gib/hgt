import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The golden fake curve is a rank-one Beurling system

A **rank-one Beurling system** has generalized primes of norms `q^d` with multiplicities
`π_d ∈ ℕ`; its point counts are the ghost components `N_k = Σ_{d ∣ k} d π_d`. The golden datum
over `𝔽₅` (`N_k = 1 + 5^k − L_k`, `goldenDatum_pointCount_eq`) is one (`goldenDatum_beurling`):

    N_k = 1 + 5^k − tr(B^k),      B = [[3, 1], [1, 2]],

and the edge shift of `B` is a subshift of the full shift on five letters (`goldenRel`), so
`5^k − tr(B^k)` counts the periodic points of the full shift that leave the subshift. Grouped by
minimal period they are free orbits, and `π_d` is `1` (at `d = 1`) plus the number of primitive
orbits of length `d` outside the subshift (`exists_primeCounts`).

* **Orbit counting** (`card_perSeqs_eq_sum`, `dvd_card_of_shift_invariant`). The admissible
  `k`-periodic sequences split by minimal period `d ∣ k`; the shift acts on those of minimal
  period `d` with all orbits of size `d`.
* **Transfer matrix** (`card_cycWords_eq_trace`). Cyclic words of length `k` admissible for a
  relation `R` are counted by `tr(M^k)`, `M` the incidence matrix of `R`.

With `witt_integral_not_pure`: the golden datum is a Beurling system of Kronecker rank one with
nonnegative integral prime counts, an integral rational zeta function with the pole plane split
off, and the functional equation, and it violates purity and the Hodge index. Positivity of the
Euler product does not supply the Hodge index; the selectivity against Beurling systems must come
from the Bézout structure of the surface.
-/

open Function Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Periodic sequences and the shift -/

section Shift

variable {α : Type*}

/-- The shift `x ↦ (n ↦ x (n + 1))` of sequences. -/
def seqShift (x : ℕ → α) : ℕ → α := fun n => x (n + 1)

theorem seqShift_iterate (m : ℕ) (x : ℕ → α) (n : ℕ) : seqShift^[m] x n = x (n + m) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply, ih]
    simp only [seqShift]
    rw [Nat.add_assoc]

theorem isPeriodicPt_seqShift_iff {k : ℕ} {x : ℕ → α} :
    IsPeriodicPt seqShift k x ↔ ∀ n, x (n + k) = x n := by
  unfold IsPeriodicPt IsFixedPt
  constructor
  · intro h n
    have := congrFun h n
    rwa [seqShift_iterate] at this
  · intro h
    funext n
    rw [seqShift_iterate]
    exact h n

/-- A sequence is admissible for `R` when consecutive letters are related. -/
def Admissible (R : α → α → Prop) (x : ℕ → α) : Prop := ∀ n, R (x n) (x (n + 1))

theorem Admissible.seqShift {R : α → α → Prop} {x : ℕ → α} (h : Admissible R x) :
    Admissible R (seqShift x) := fun n => h (n + 1)

theorem admissible_of_seqShift {R : α → α → Prop} {x : ℕ → α} {k : ℕ} (hk : 0 < k)
    (hper : IsPeriodicPt seqShift k x) (h : Admissible R (seqShift x)) : Admissible R x := by
  intro n
  rcases n with _ | n
  · have hp := isPeriodicPt_seqShift_iff.mp hper
    have h1 := hp 0
    have h2 := hp 1
    have h3 := h (k - 1)
    simp only [seqShift, show k - 1 + 1 = k by omega] at h3
    rw [zero_add] at h1
    rw [show k + 1 = 1 + k by ring, h2, h1] at h3
    exact h3
  · exact h n

/-- The `k`-periodic sequence of a word. -/
def periodize {k : ℕ} (hk : 0 < k) (w : Fin k → α) : ℕ → α := fun n => w ⟨n % k, Nat.mod_lt n hk⟩

theorem periodize_injective {k : ℕ} (hk : 0 < k) :
    Injective (periodize hk : (Fin k → α) → ℕ → α) := by
  intro w w' h
  funext t
  have := congrFun h t
  simpa [periodize, Nat.mod_eq_of_lt t.2] using this

theorem isPeriodicPt_periodize {k : ℕ} (hk : 0 < k) (w : Fin k → α) :
    IsPeriodicPt seqShift k (periodize hk w) :=
  isPeriodicPt_seqShift_iff.mpr fun n => by simp [periodize, Nat.add_mod_right]

theorem eq_periodize_of_periodic {k : ℕ} (hk : 0 < k) {x : ℕ → α}
    (hx : IsPeriodicPt seqShift k x) : periodize hk (fun t : Fin k => x t) = x := by
  funext n
  simp only [periodize]
  have hp := isPeriodicPt_seqShift_iff.mp hx
  conv_rhs => rw [← Nat.mod_add_div n k]
  generalize n / k = q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hp, ih]

end Shift

/-! ### Counting periodic sequences by minimal period -/

section Count

open scoped Classical

variable {α : Type*} [Fintype α]

/-- The admissible `k`-periodic sequences. -/
def perSeqs (R : α → α → Prop) (k : ℕ) : Finset (ℕ → α) :=
  if hk : 0 < k then
    (Finset.univ.filter fun w : Fin k → α => Admissible R (periodize hk w)).image (periodize hk)
  else ∅

theorem mem_perSeqs {R : α → α → Prop} {k : ℕ} (hk : 0 < k) {x : ℕ → α} :
    x ∈ perSeqs R k ↔ Admissible R x ∧ IsPeriodicPt seqShift k x := by
  rw [perSeqs, dif_pos hk, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(Finset.mem_filter.mp hw).2, isPeriodicPt_periodize hk w⟩
  · rintro ⟨hadm, hper⟩
    refine ⟨fun t => x t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      eq_periodize_of_periodic hk hper⟩
    rw [eq_periodize_of_periodic hk hper]
    exact hadm

theorem card_perSeqs {R : α → α → Prop} {k : ℕ} (hk : 0 < k) :
    (perSeqs R k).card =
      (Finset.univ.filter fun w : Fin k → α => Admissible R (periodize hk w)).card := by
  rw [perSeqs, dif_pos hk, Finset.card_image_of_injective _ (periodize_injective hk)]

/-- The admissible sequences of minimal period exactly `d`. -/
def primSeqs (R : α → α → Prop) (d : ℕ) : Finset (ℕ → α) :=
  (perSeqs R d).filter fun x => minimalPeriod seqShift x = d

theorem mem_primSeqs {R : α → α → Prop} {d : ℕ} (hd : 0 < d) {x : ℕ → α} :
    x ∈ primSeqs R d ↔ Admissible R x ∧ minimalPeriod seqShift x = d := by
  rw [primSeqs, Finset.mem_filter, mem_perSeqs hd]
  constructor
  · rintro ⟨⟨hadm, _⟩, hmin⟩
    exact ⟨hadm, hmin⟩
  · rintro ⟨hadm, hmin⟩
    have := isPeriodicPt_minimalPeriod seqShift x
    rw [hmin] at this
    exact ⟨⟨hadm, this⟩, hmin⟩

/-- **The periodic sequences split by minimal period.** -/
theorem card_perSeqs_eq_sum {R : α → α → Prop} {k : ℕ} (hk : 0 < k) :
    (perSeqs R k).card = ∑ d ∈ k.divisors, (primSeqs R d).card := by
  classical
  have hset : perSeqs R k = k.divisors.biUnion (primSeqs R) := by
    ext x
    rw [mem_perSeqs hk, Finset.mem_biUnion]
    constructor
    · rintro ⟨hadm, hper⟩
      have hpos := hper.minimalPeriod_pos hk
      exact ⟨minimalPeriod seqShift x, Nat.mem_divisors.mpr ⟨hper.minimalPeriod_dvd, hk.ne'⟩,
        (mem_primSeqs hpos).mpr ⟨hadm, rfl⟩⟩
    · rintro ⟨d, hd, hx⟩
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      obtain ⟨hadm, hmin⟩ := (mem_primSeqs hd0).mp hx
      refine ⟨hadm, ?_⟩
      have := isPeriodicPt_minimalPeriod seqShift x
      rw [hmin] at this
      exact this.trans_dvd (Nat.dvd_of_mem_divisors hd)
  rw [hset, Finset.card_biUnion]
  intro d₁ hd₁ d₂ hd₂ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x h1 h2
  have e1 := ((mem_primSeqs (Nat.pos_of_mem_divisors hd₁)).mp h1).2
  have e2 := ((mem_primSeqs (Nat.pos_of_mem_divisors hd₂)).mp h2).2
  exact hne (e1.symm.trans e2)

omit [Fintype α] in
/-- **Free orbits.** A finite set of sequences of minimal period `d`, closed under the shift,
has cardinality divisible by `d`. -/
theorem dvd_card_of_shift_invariant {d : ℕ} (hd : 0 < d) (S : Finset (ℕ → α))
    (hS : ∀ x ∈ S, seqShift x ∈ S) (hper : ∀ x ∈ S, minimalPeriod seqShift x = d) :
    d ∣ S.card := by
  classical
  induction h : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rw [Finset.card_empty] at h
      rw [← h]
      exact dvd_zero _
    · set O := (Finset.range d).image fun i => seqShift^[i] x with hO
      have hiter : ∀ i, seqShift^[i] x ∈ S := by
        intro i
        induction i with
        | zero => exact hx
        | succ i ih' => rw [iterate_succ_apply']; exact hS _ ih'
      have hOS : O ⊆ S := fun y hy => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        exact hiter i
      have hxd := hper x hx
      have hOcard : O.card = d := by
        rw [hO, Finset.card_image_of_injOn, Finset.card_range]
        intro i hi j hj hij
        refine iterate_injOn_Iio_minimalPeriod ?_ ?_ hij
        · rw [hxd]; exact Finset.mem_range.mp hi
        · rw [hxd]; exact Finset.mem_range.mp hj
      have hrest : ∀ y ∈ S \ O, seqShift y ∈ S \ O := by
        intro y hy
        obtain ⟨hyS, hyO⟩ := Finset.mem_sdiff.mp hy
        refine Finset.mem_sdiff.mpr ⟨hS y hyS, fun hsy => hyO ?_⟩
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hsy
        have hyd := hper y hyS
        have hyper : seqShift^[d] y = y := by
          have := isPeriodicPt_minimalPeriod seqShift y
          rw [hyd] at this
          exact this
        have hy' : y = seqShift^[d - 1 + i] x := by
          rw [iterate_add_apply, hi, ← iterate_succ_apply, show (d - 1).succ = d by omega,
            hyper]
        rw [hy', ← iterate_mod_minimalPeriod_eq, hxd]
        exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.mod_lt _ hd), rfl⟩
      have hdn : d ≤ n := by
        rw [← h, ← hOcard]
        exact Finset.card_le_card hOS
      have hcard : (S \ O).card = n - d := by
        rw [Finset.card_sdiff_of_subset hOS, hOcard, h]
      have := ih (n - d) (by omega) (S \ O) hrest (fun y hy => hper y (Finset.mem_sdiff.mp hy).1)
        hcard
      rw [show n = n - d + d by omega]
      exact dvd_add this dvd_rfl

theorem seqShift_mem_primSeqs {R : α → α → Prop} {d : ℕ} (hd : 0 < d) {x : ℕ → α}
    (hx : x ∈ primSeqs R d) : seqShift x ∈ primSeqs R d := by
  obtain ⟨hadm, hmin⟩ := (mem_primSeqs hd).mp hx
  have hp : x ∈ periodicPts seqShift := ⟨d, hd, by
    have := isPeriodicPt_minimalPeriod seqShift x
    rwa [hmin] at this⟩
  exact (mem_primSeqs hd).mpr ⟨hadm.seqShift, by rw [minimalPeriod_apply hp, hmin]⟩

theorem primSeqs_mono {R R' : α → α → Prop} (hRR : ∀ a b, R a b → R' a b) (d : ℕ) :
    primSeqs R d ⊆ primSeqs R' d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro x hx
    simp [primSeqs, perSeqs] at hx
  · intro x hx
    obtain ⟨hadm, hmin⟩ := (mem_primSeqs hd).mp hx
    exact (mem_primSeqs hd).mpr ⟨fun n => hRR _ _ (hadm n), hmin⟩

/-- The primitive sequences of `R'` that are not `R`-admissible form free orbits. -/
theorem dvd_card_primSeqs_sdiff {R R' : α → α → Prop} {d : ℕ} (hd : 0 < d) :
    d ∣ (primSeqs R' d \ primSeqs R d).card := by
  classical
  refine dvd_card_of_shift_invariant hd _ (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨seqShift_mem_primSeqs hd h1, fun h3 => h2 ?_⟩
    obtain ⟨hadm, hmin⟩ := (mem_primSeqs hd).mp h3
    obtain ⟨_, hminx⟩ := (mem_primSeqs hd).mp h1
    have hper : IsPeriodicPt seqShift d x := by
      have := isPeriodicPt_minimalPeriod seqShift x
      rwa [hminx] at this
    exact (mem_primSeqs hd).mpr ⟨admissible_of_seqShift hd hper hadm, hminx⟩
  · exact ((mem_primSeqs hd).mp (Finset.mem_sdiff.mp hx).1).2

/-- **Realizability of a difference of periodic counts.** If `R ⊆ R'`, then
`1 + #per_{R'}(k) − #per_R(k) = Σ_{d ∣ k} d π_d` with `π_d ∈ ℕ`: `π_1` counts one extra point,
and `π_d` the primitive `R'`-orbits of length `d` that are not `R`-admissible. -/
theorem exists_primeCounts {R R' : α → α → Prop} (hRR : ∀ a b, R a b → R' a b) :
    ∃ π : ℕ → ℕ, ∀ k, 0 < k →
      ((perSeqs R' k).card : ℤ) - (perSeqs R k).card + 1 = ∑ d ∈ k.divisors, (d : ℤ) * π d := by
  classical
  refine ⟨fun d => (if d = 1 then 1 else 0) + (primSeqs R' d \ primSeqs R d).card / d,
    fun k hk => ?_⟩
  have hterm : ∀ d ∈ k.divisors, (d : ℤ) * (((if d = 1 then 1 else 0) +
      (primSeqs R' d \ primSeqs R d).card / d : ℕ) : ℤ) =
      (if d = 1 then 1 else 0) + ((primSeqs R' d).card - (primSeqs R d).card : ℤ) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    obtain ⟨c, hc⟩ := dvd_card_primSeqs_sdiff (R := R) (R' := R') hd0
    have hsub := primSeqs_mono hRR d
    have hcard : ((primSeqs R' d \ primSeqs R d).card : ℤ) =
        (primSeqs R' d).card - (primSeqs R d).card := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [← hcard, hc, Nat.mul_div_cancel_left _ hd0]
    split_ifs with h1
    · subst h1; push_cast; ring
    · push_cast; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' k.divisors 1,
    if_pos (Nat.mem_divisors.mpr ⟨one_dvd k, hk.ne'⟩), Finset.sum_sub_distrib,
    card_perSeqs_eq_sum hk, card_perSeqs_eq_sum hk]
  push_cast
  ring

end Count

/-! ### The transfer matrix -/

section Transfer

open scoped Classical

variable {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop)

/-- The incidence matrix of a relation. -/
def incMatrix : Matrix α α ℕ := Matrix.of fun a b => if R a b then 1 else 0

/-- Admissible linear words of length `m + 1` from `a` to `b`. -/
def pathWords (m : ℕ) (a b : α) : Finset (Fin (m + 1) → α) :=
  Finset.univ.filter fun w => w 0 = a ∧ w (Fin.last m) = b ∧
    ∀ t : Fin m, R (w t.castSucc) (w t.succ)

theorem mem_pathWords {m : ℕ} {a b : α} {w : Fin (m + 1) → α} :
    w ∈ pathWords R m a b ↔ w 0 = a ∧ w (Fin.last m) = b ∧ ∀ t : Fin m, R (w t.castSucc) (w t.succ) := by
  simp [pathWords]

/-- **Path counting**: linear admissible words are counted by the powers of the incidence matrix. -/
theorem card_pathWords (m : ℕ) (a b : α) : (pathWords R m a b).card = (incMatrix R ^ m) a b := by
  induction m generalizing a with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs with hab
    · subst hab
      rw [Finset.card_eq_one]
      refine ⟨fun _ => a, ?_⟩
      ext w
      rw [mem_pathWords, Finset.mem_singleton]
      constructor
      · rintro ⟨h0, -⟩
        funext t
        rw [Fin.fin_one_eq_zero t, h0]
      · rintro rfl
        exact ⟨rfl, rfl, fun t => t.elim0⟩
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      obtain ⟨h0, h1, -⟩ := (mem_pathWords R).mp hw
      exact hab (h0.symm.trans h1)
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply,
      Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (m + 2) → α => w 1)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← ih c]
    simp only [incMatrix, Matrix.of_apply]
    split_ifs with hac
    · rw [one_mul]
      refine Finset.card_nbij' (fun w => Fin.tail w) (fun v => (Fin.cons a v : Fin (m + 2) → α))
        ?_ ?_ ?_ ?_
      · intro w hw
        obtain ⟨hw1, hc⟩ := Finset.mem_filter.mp hw
        obtain ⟨_, hb, hp⟩ := (mem_pathWords R).mp hw1
        refine (mem_pathWords R).mpr ⟨hc, ?_, fun t => ?_⟩
        · show w (Fin.last m).succ = b
          rw [Fin.succ_last]
          exact hb
        · have := hp t.succ
          show R (w (Fin.succ (Fin.castSucc t))) (w (Fin.succ (Fin.succ t)))
          rw [Fin.succ_castSucc]
          exact this
      · intro v hv
        obtain ⟨hv0, hvb, hvp⟩ := (mem_pathWords R).mp hv
        refine Finset.mem_filter.mpr ⟨(mem_pathWords R).mpr ⟨by simp, ?_, fun t => ?_⟩, ?_⟩
        · show (Fin.cons a v : Fin (m + 2) → α) (Fin.last (m + 1)) = b
          rw [← Fin.succ_last, Fin.cons_succ]
          exact hvb
        · refine Fin.cases ?_ (fun s => ?_) t
          · simpa [hv0] using hac
          · show R ((Fin.cons a v : Fin (m + 2) → α) (Fin.castSucc (Fin.succ s)))
              ((Fin.cons a v : Fin (m + 2) → α) (Fin.succ (Fin.succ s)))
            rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
            exact hvp s
        · show (Fin.cons a v : Fin (m + 2) → α) (Fin.succ 0) = c
          rw [Fin.cons_succ]
          exact hv0
      · intro w hw
        have ha := ((mem_pathWords R).mp (Finset.mem_filter.mp hw).1).1
        rw [← ha]
        exact Fin.cons_self_tail w
      · intro v _
        funext i
        simp [Fin.tail]
    · rw [zero_mul, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      obtain ⟨hw1, hc⟩ := Finset.mem_filter.mp hw
      obtain ⟨ha, _, hp⟩ := (mem_pathWords R).mp hw1
      apply hac
      have := hp 0
      rw [show (Fin.castSucc (0 : Fin (m + 1))) = 0 from rfl, ha,
        show ((0 : Fin (m + 1)).succ) = 1 from rfl, hc] at this
      exact this

omit [Fintype α] [DecidableEq α] in
/-- Admissibility of a periodized word is the cyclic condition. -/
theorem admissible_periodize_iff (m : ℕ) (w : Fin (m + 1) → α) :
    Admissible R (periodize (Nat.succ_pos m) w) ↔
      (∀ t : Fin m, R (w t.castSucc) (w t.succ)) ∧ R (w (Fin.last m)) (w 0) := by
  constructor
  · intro h
    refine ⟨fun t => ?_, ?_⟩
    · have e1 : periodize (Nat.succ_pos m) w t = w t.castSucc :=
        congrArg w (Fin.ext (by simp [Nat.mod_eq_of_lt (show (t : ℕ) < m + 1 by omega)]))
      have e2 : periodize (Nat.succ_pos m) w (t + 1) = w t.succ :=
        congrArg w (Fin.ext (by simp [Nat.mod_eq_of_lt (show (t : ℕ) + 1 < m + 1 by omega)]))
      have := h t
      rwa [e1, e2] at this
    · have e1 : periodize (Nat.succ_pos m) w m = w (Fin.last m) :=
        congrArg w (Fin.ext (by simp [Nat.mod_eq_of_lt (show m < m + 1 by omega)]))
      have e2 : periodize (Nat.succ_pos m) w (m + 1) = w 0 :=
        congrArg w (Fin.ext (by simp))
      have := h m
      rwa [e1, e2] at this
  · rintro ⟨hp, hl⟩ n
    have hn : n = n % (m + 1) + (m + 1) * (n / (m + 1)) := (Nat.mod_add_div n (m + 1)).symm
    have hlt : n % (m + 1) < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)
    rcases Nat.lt_or_ge (n % (m + 1)) m with hr | hr
    · have hv : (n + 1) % (m + 1) = n % (m + 1) + 1 := by
        conv_lhs => rw [hn]
        rw [show n % (m + 1) + (m + 1) * (n / (m + 1)) + 1 =
            (n % (m + 1) + 1) + (m + 1) * (n / (m + 1)) by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega)]
      have e1 : periodize (Nat.succ_pos m) w n = w (⟨n % (m + 1), hr⟩ : Fin m).castSucc :=
        congrArg w (Fin.ext rfl)
      have e2 : periodize (Nat.succ_pos m) w (n + 1) = w (⟨n % (m + 1), hr⟩ : Fin m).succ :=
        congrArg w (Fin.ext (by simp [hv]))
      show R (periodize _ w n) (periodize _ w (n + 1))
      rw [e1, e2]
      exact hp _
    · have hm : n % (m + 1) = m := by omega
      have hv : (n + 1) % (m + 1) = 0 := by
        conv_lhs => rw [hn, hm]
        rw [show m + (m + 1) * (n / (m + 1)) + 1 = (m + 1) * (n / (m + 1) + 1) by ring,
          Nat.mul_mod_right]
      have e1 : periodize (Nat.succ_pos m) w n = w (Fin.last m) :=
        congrArg w (Fin.ext (by simp [hm]))
      have e2 : periodize (Nat.succ_pos m) w (n + 1) = w 0 :=
        congrArg w (Fin.ext (by simp [hv]))
      show R (periodize _ w n) (periodize _ w (n + 1))
      rw [e1, e2]
      exact hl

/-- **Transfer matrix**: admissible cyclic words of length `m + 1` are counted by
`tr(M^{m+1})`. -/
theorem card_perSeqs_eq_trace (m : ℕ) :
    (perSeqs R (m + 1)).card = Matrix.trace (incMatrix R ^ (m + 1)) := by
  rw [card_perSeqs (Nat.succ_pos m)]
  simp_rw [admissible_periodize_iff]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (m + 1) → α => w 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _), Matrix.trace, pow_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Finset.filter_filter,
    Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (m + 1) → α => w (Fin.last m))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← card_pathWords, Finset.filter_filter]
  simp only [incMatrix, Matrix.of_apply]
  split_ifs with hba
  · rw [mul_one]
    congr 1
    ext w
    rw [Finset.mem_filter, mem_pathWords]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨hp, _⟩, h0⟩, hl⟩
      exact ⟨h0, hl, hp⟩
    · rintro ⟨h0, hl, hp⟩
      refine ⟨⟨⟨hp, ?_⟩, h0⟩, hl⟩
      rw [hl, h0]
      exact hba
  · rw [mul_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    obtain ⟨⟨⟨_, hl⟩, h0⟩, hb⟩ := hw
    rw [hb, h0] at hl
    exact hba hl

end Transfer

/-! ### The golden subshift -/

/-- The vertex entered by a letter: `0, 1, 2 ↦ 0`, `3, 4 ↦ 1`. -/
def goldenTarget (a : Fin 5) : Fin 2 := if (a : ℕ) < 3 then 0 else 1

/-- The letters leaving a vertex: `0, 1, 2, 3` from `0`, and `0, 3, 4` from `1`. -/
def goldenOut (v : Fin 2) (b : Fin 5) : Prop := if v = 0 then (b : ℕ) ≠ 4 else b = 0 ∨ 3 ≤ (b : ℕ)

/-- The golden subshift of the full shift on five letters: the edge shift of `[[3, 1], [1, 2]]`. -/
def goldenRel (a b : Fin 5) : Prop := goldenOut (goldenTarget a) b

/-- The vertex matrix `B = [[3, 1], [1, 2]]` of the golden subshift. -/
def goldenB : Matrix (Fin 2) (Fin 2) ℕ := !![3, 1; 1, 2]

open scoped Classical in
/-- Letters to vertices. -/
def goldenS : Matrix (Fin 5) (Fin 2) ℕ := Matrix.of fun a v => if goldenTarget a = v then 1 else 0

open scoped Classical in
/-- Vertices to the letters leaving them. -/
def goldenT : Matrix (Fin 2) (Fin 5) ℕ := Matrix.of fun v b => if goldenOut v b then 1 else 0

open scoped Classical in
theorem incMatrix_goldenRel : incMatrix goldenRel = goldenS * goldenT := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [incMatrix, goldenRel, goldenS, goldenT, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr

theorem goldenT_mul_goldenS : goldenT * goldenS = goldenB := by
  ext v w
  fin_cases v <;> fin_cases w <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, goldenOut, goldenTarget, goldenB, goldenS, goldenT]

theorem goldenB_sq : goldenB * goldenB + 5 • (1 : Matrix (Fin 2) (Fin 2) ℕ) = 5 • goldenB := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, goldenB]

/-- `tr(B^k) = L_k`. -/
theorem trace_goldenB_pow (k : ℕ) : ((Matrix.trace (goldenB ^ k) : ℕ) : ℤ) = goldenLucas k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [Matrix.trace, goldenLucas]
    | 1, _ => simp [Matrix.trace, Fin.sum_univ_two, goldenB, goldenLucas]
    | (k + 2), ih =>
      have hrec : goldenB ^ (k + 2) + 5 • goldenB ^ k = 5 • goldenB ^ (k + 1) := by
        have h := congrArg (fun X => goldenB ^ k * X) goldenB_sq
        simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
        rwa [← Matrix.mul_assoc, ← pow_succ, ← pow_succ] at h
      have ht := congrArg Matrix.trace hrec
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at ht
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have ht' : ((Matrix.trace (goldenB ^ (k + 2)) : ℕ) : ℤ) =
          5 * ((Matrix.trace (goldenB ^ (k + 1)) : ℕ) : ℤ) -
            5 * ((Matrix.trace (goldenB ^ k) : ℕ) : ℤ) := by
        have := congrArg (fun n : ℕ => (n : ℤ)) ht
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at this
        linarith
      rw [ht', h1, h0, goldenLucas]

/-- `tr((ST)^{k+1}) = tr((TS)^{k+1})`. -/
theorem trace_mul_pow_comm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (S : Matrix m n ℕ) (T : Matrix n m ℕ) (k : ℕ) :
    Matrix.trace ((S * T) ^ (k + 1)) = Matrix.trace ((T * S) ^ (k + 1)) := by
  have hpow : ∀ j : ℕ, (S * T) ^ (j + 1) = S * (T * S) ^ j * T := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
      rw [pow_succ, ihj, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [hpow, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- The golden subshift has `L_k` periodic points of period `k`. -/
theorem card_perSeqs_golden {k : ℕ} (hk : 0 < k) :
    ((perSeqs goldenRel k).card : ℤ) = goldenLucas k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [card_perSeqs_eq_trace, incMatrix_goldenRel, trace_mul_pow_comm, goldenT_mul_goldenS,
    trace_goldenB_pow]

/-- The full shift on five letters has `5^k` periodic points of period `k`. -/
theorem card_perSeqs_full {k : ℕ} (hk : 0 < k) :
    (perSeqs (fun _ _ : Fin 5 => True) k).card = 5 ^ k := by
  classical
  have hall : ∀ w ∈ (Finset.univ : Finset (Fin k → Fin 5)),
      Admissible (fun _ _ : Fin 5 => True) (periodize hk w) := fun _ _ _ => trivial
  rw [card_perSeqs hk, Finset.filter_true_of_mem hall, Finset.card_univ, Fintype.card_eq_nat_card,
    Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_fin]

/-- **The golden fake curve is a rank-one Beurling system.** Its point counts are the ghost
components of nonnegative integral prime counts: `N_k = Σ_{d ∣ k} d π_d`, `π_d ∈ ℕ`. -/
theorem goldenDatum_beurling : ∃ π : ℕ → ℕ, ∀ k, 1 ≤ k →
    goldenDatum.pointCount k = ∑ d ∈ k.divisors, (d : ℝ) * π d := by
  obtain ⟨π, hπ⟩ := exists_primeCounts (R := goldenRel) (R' := fun _ _ : Fin 5 => True)
    (fun _ _ _ => trivial)
  refine ⟨π, fun k hk => ?_⟩
  have h := hπ k hk
  rw [card_perSeqs_full hk, card_perSeqs_golden hk] at h
  rw [goldenDatum_pointCount_eq]
  have h' : ((5 ^ k + 1 - goldenLucas k : ℤ) : ℝ) =
      ((∑ d ∈ k.divisors, (d : ℤ) * π d : ℤ) : ℝ) := by
    rw [← h]
    push_cast
    ring
  rw [h']
  push_cast
  rfl

/-- **A rank-one Beurling system with integral zeta function and the functional equation that
violates purity.** -/
theorem goldenDatum_beurling_not_pure :
    (∃ π : ℕ → ℕ, ∀ k, 1 ≤ k → goldenDatum.pointCount k = ∑ d ∈ k.divisors, (d : ℝ) * π d) ∧
    (∃ Zℤ : PowerSeries ℤ, PowerSeries.constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries) ∧
    (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
    ¬ ∀ i, ‖goldenDatum.β i‖ = 1 :=
  ⟨goldenDatum_beurling, witt_integral_not_pure.1, witt_integral_not_pure.2.2.1,
    witt_integral_not_pure.2.2.2⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
