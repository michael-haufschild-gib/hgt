import GaloisForLFunctions.HTGeometry.RamifiedMultiGradedNewtonModelBase

/-!
# Observability for the exact signed Wiman velocity flag

After clearing rational Puiseux exponents, a first-order Wiman branch is linear in its output
coordinate and has one signed exponent in the adjacent input coordinate.  Its multigraded leading
degree is therefore bidiagonal, not a pure coordinate unit.  This module proves the full Hahn
leading-term calculation for that exact shape.  Positivity of every Wiman charge `p + 1` becomes
the integral inequality saying the adjacent tail exponent is smaller than the next ramification
index.  That inequality separates successive logarithmic states, makes their gradient triangular
with nonzero diagonal, and forces algebraic independence of the raw output jets.

All higher Hahn terms remain unrestricted.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

theorem ofLex_finset_sum_apply {N : ℕ} {I : Type*} [DecidableEq I]
    (s : Finset I) (d : I → mgDeg N) (l : Fin N) :
    ofLex (∑ i ∈ s, d i) l = ∑ i ∈ s, ofLex (d i) l := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change ofLex (d a) l + ofLex (∑ i ∈ s, d i) l = _
      rw [ih]

def mgRamWimanVelocityDegree {N : ℕ} (r : Fin N → ℕ)
    (tail : Fin N → ℤ) (j : Fin N) : mgDeg N :=
  toLex fun l =>
    if l = j then -(r j : ℤ)
    else if h : (j : ℕ) + 1 < N then
      if l = (⟨(j : ℕ) + 1, h⟩ : Fin N) then tail j else 0
    else 0

@[simp] theorem ofLex_mgRamWimanVelocityDegree {N : ℕ} (r : Fin N → ℕ)
    (tail : Fin N → ℤ) (j l : Fin N) :
    ofLex (mgRamWimanVelocityDegree r tail j) l =
      if l = j then -(r j : ℤ)
      else if h : (j : ℕ) + 1 < N then
        if l = (⟨(j : ℕ) + 1, h⟩ : Fin N) then tail j else 0
      else 0 := rfl

def mgRamWimanSuffixDegree {N : ℕ} (r : Fin N → ℕ)
    (tail : Fin N → ℤ) (k : ℕ) : mgDeg N :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)),
    mgRamWimanVelocityDegree r tail j

def mgRamWimanNextDegree {n : ℕ} (r : Fin (n + 1) → ℕ)
    (tail : Fin (n + 1) → ℤ) (j : Fin (n + 1)) : mgDeg (n + 1) :=
  mgRamWimanSuffixDegree r tail (j : ℕ) + mgRamStep r j

theorem ofLex_mgRamWimanSuffixDegree_of_lt {N : ℕ}
    (r : Fin N → ℕ) (tail : Fin N → ℤ) {k : ℕ} {l : Fin N}
    (hlk : (l : ℕ) < k) :
    ofLex (mgRamWimanSuffixDegree r tail k) l = 0 := by
  rw [mgRamWimanSuffixDegree]
  rw [ofLex_finset_sum_apply]
  change (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)),
    ofLex (mgRamWimanVelocityDegree r tail j) l) = 0
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_filter] at hj
  rw [ofLex_mgRamWimanVelocityDegree]
  have hlj : l ≠ j := by
    intro h
    subst j
    omega
  rw [if_neg hlj]
  split_ifs with hjN hlsucc
  · have : (l : ℕ) = (j : ℕ) + 1 := congrArg Fin.val hlsucc
    omega
  · simp
  · simp

theorem ofLex_mgRamWimanSuffixDegree_self {N : ℕ}
    (r : Fin N → ℕ) (tail : Fin N → ℤ) (j : Fin N) :
    ofLex (mgRamWimanSuffixDegree r tail (j : ℕ)) j = -(r j : ℤ) := by
  rw [mgRamWimanSuffixDegree]
  rw [ofLex_finset_sum_apply]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin N => (j : ℕ) ≤ (q : ℕ)),
    ofLex (mgRamWimanVelocityDegree r tail q) j) = -(r j : ℤ)
  rw [Finset.sum_eq_single j]
  · rw [ofLex_mgRamWimanVelocityDegree, if_pos rfl]
  · intro q hq hqj
    rw [Finset.mem_filter] at hq
    rw [ofLex_mgRamWimanVelocityDegree, if_neg (Ne.symm hqj)]
    split_ifs with hqN hjsucc
    · have : (j : ℕ) = (q : ℕ) + 1 := congrArg Fin.val hjsucc
      have hle : (j : ℕ) ≤ (q : ℕ) := hq.2
      omega
    · simp
    · simp
  · intro hj
    exact (hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩)).elim

theorem ofLex_mgRamWimanNextDegree_le {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (j l : Fin (n + 1)) (hlj : l ≤ j) :
    ofLex (mgRamWimanNextDegree r tail j) l = 0 := by
  by_cases hEq : l = j
  · subst l
    rw [mgRamWimanNextDegree]
    change ofLex (mgRamWimanSuffixDegree r tail (j : ℕ)) j +
      ofLex (mgRamStep r j) j = 0
    rw [ofLex_mgRamWimanSuffixDegree_self, ofLex_mgRamStep, if_pos rfl]
    omega
  · have hlt : l < j := lt_of_le_of_ne hlj hEq
    rw [mgRamWimanNextDegree]
    change ofLex (mgRamWimanSuffixDegree r tail (j : ℕ)) l +
      ofLex (mgRamStep r j) l = 0
    rw [ofLex_mgRamWimanSuffixDegree_of_lt r tail (Fin.mk_lt_mk.mp hlt),
      ofLex_mgRamStep, if_neg (ne_of_lt hlt)]
    omega

theorem ofLex_mgRamWimanNextDegree_succ {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (j : Fin (n + 1)) (h : (j : ℕ) + 1 < n + 1) :
    ofLex (mgRamWimanNextDegree r tail j) ⟨(j : ℕ) + 1, h⟩ =
      tail j - (r ⟨(j : ℕ) + 1, h⟩ : ℤ) := by
  rw [mgRamWimanNextDegree]
  change ofLex (mgRamWimanSuffixDegree r tail (j : ℕ)) ⟨(j : ℕ) + 1, h⟩ +
    ofLex (mgRamStep r j) ⟨(j : ℕ) + 1, h⟩ = _
  rw [ofLex_mgRamStep, if_neg (by
    intro hEq
    have hv := congrArg Fin.val hEq
    simp at hv)]
  rw [mgRamWimanSuffixDegree]
  rw [ofLex_finset_sum_apply]
  change (∑ q ∈ Finset.univ.filter (fun q : Fin (n + 1) => (j : ℕ) ≤ (q : ℕ)),
    ofLex (mgRamWimanVelocityDegree r tail q) ⟨(j : ℕ) + 1, h⟩) + 0 = _
  have hjmem : j ∈ Finset.univ.filter
      (fun q : Fin (n + 1) => (j : ℕ) ≤ (q : ℕ)) := by simp
  rw [← Finset.add_sum_erase _ _ hjmem]
  rw [ofLex_mgRamWimanVelocityDegree, if_neg (by
    intro hEq
    have hv := congrArg Fin.val hEq
    simp at hv)]
  rw [dif_pos h, if_pos (Fin.ext rfl)]
  have hsuccmem : (⟨(j : ℕ) + 1, h⟩ : Fin (n + 1)) ∈
      (Finset.univ.filter (fun q : Fin (n + 1) => (j : ℕ) ≤ (q : ℕ))).erase j := by
    rw [Finset.mem_erase, Finset.mem_filter]
    exact ⟨by
      intro hEq
      have hv := congrArg Fin.val hEq
      simp at hv, Finset.mem_univ _, Nat.le_succ _⟩
  rw [← Finset.add_sum_erase _ _ hsuccmem]
  rw [ofLex_mgRamWimanVelocityDegree, if_pos rfl]
  have hrest : ∑ q ∈
      ((Finset.univ.filter (fun q : Fin (n + 1) => (j : ℕ) ≤ (q : ℕ))).erase j).erase
        ⟨(j : ℕ) + 1, h⟩,
      ofLex (mgRamWimanVelocityDegree r tail q) ⟨j.val + 1, h⟩ = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_filter] at hq
    rw [ofLex_mgRamWimanVelocityDegree, if_neg (Ne.symm hq.1)]
    split_ifs with hqN hqsucc
    · have hval : (j : ℕ) + 1 = (q : ℕ) + 1 := congrArg Fin.val hqsucc
      have hqe : q = j := Fin.ext (by omega)
      exact (hq.2.1 hqe).elim
    · simp
    · simp
  rw [hrest]
  ring

/-- Cleared adjacent exponent form of positivity of the Wiman charge `p + 1`. -/
def RamifiedWimanChargesPositive {n : ℕ} (r : Fin (n + 1) → ℕ)
    (tail : Fin (n + 1) → ℤ) : Prop :=
  ∀ (j : Fin (n + 1)) (h : (j : ℕ) + 1 < n + 1),
    tail j < (r ⟨(j : ℕ) + 1, h⟩ : ℤ)

def mgRamWimanObservableDegree {n : ℕ} (r : Fin (n + 1) → ℕ)
    (tail : Fin (n + 1) → ℤ) (m : Fin (n + 1)) : mgDeg (n + 1) :=
  if hm : m = 0 then mgRamUnit r 0
  else mgRamWimanNextDegree r tail ⟨(m : ℕ) - 1, by omega⟩

theorem mgRamWimanObservableDegree_succ {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (m : Fin (n + 1)) (hm : (m : ℕ) + 1 < n + 1) :
    mgRamWimanObservableDegree r tail ⟨(m : ℕ) + 1, hm⟩ =
      mgRamWimanNextDegree r tail m := by
  rw [mgRamWimanObservableDegree, dif_neg]
  · congr 1
  · intro hzero
    have hv := congrArg Fin.val hzero
    simp at hv

theorem ofLex_mgRamWimanObservableDegree_eq_zero_of_lt {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    {j m : Fin (n + 1)} (hjm : j < m) :
    ofLex (mgRamWimanObservableDegree r tail m) j = 0 := by
  rw [mgRamWimanObservableDegree, dif_neg]
  · apply ofLex_mgRamWimanNextDegree_le
    change (j : ℕ) ≤ (m : ℕ) - 1
    omega
  · intro hm
    subst m
    exact Fin.not_lt_zero j hjm

theorem ofLex_mgRamWimanObservableDegree_self_neg {n : ℕ}
    {r : Fin (n + 1) → ℕ} (hr : ∀ j, 0 < r j)
    {tail : Fin (n + 1) → ℤ} (hcharge : RamifiedWimanChargesPositive r tail)
    (m : Fin (n + 1)) :
    ofLex (mgRamWimanObservableDegree r tail m) m < 0 := by
  by_cases hm : m = 0
  · rw [mgRamWimanObservableDegree, dif_pos hm]
    subst m
    rw [ofLex_mgRamUnit, if_pos rfl]
    exact neg_neg_of_pos (by exact_mod_cast hr 0)
  · rw [mgRamWimanObservableDegree, dif_neg hm]
    let j : Fin (n + 1) := ⟨(m : ℕ) - 1, by omega⟩
    have hmpos : 0 < (m : ℕ) := by
      apply Nat.pos_of_ne_zero
      intro hmzero
      apply hm
      exact Fin.ext hmzero
    have hj : (j : ℕ) + 1 = (m : ℕ) := by
      dsimp [j]
      omega
    have hjN : (j : ℕ) + 1 < n + 1 := by rw [hj]; exact m.isLt
    have hmj : m = (⟨(j : ℕ) + 1, hjN⟩ : Fin (n + 1)) := by
      apply Fin.ext
      exact hj.symm
    change ofLex (mgRamWimanNextDegree r tail j) m < 0
    rw [hmj, ofLex_mgRamWimanNextDegree_succ]
    exact sub_neg.mpr (hcharge j hjN)

theorem mgRamWimanNextDegree_lt {n : ℕ}
    {r : Fin (n + 1) → ℕ} {tail : Fin (n + 1) → ℤ}
    (hcharge : RamifiedWimanChargesPositive r tail)
    {j k : Fin (n + 1)} (hjk : j < k) :
    mgRamWimanNextDegree r tail j < mgRamWimanNextDegree r tail k := by
  have hjN : (j : ℕ) + 1 < n + 1 := by
    exact lt_of_le_of_lt (Nat.succ_le_iff.mpr (Fin.mk_lt_mk.mp hjk)) k.isLt
  let p : Fin (n + 1) := ⟨j.val + 1, hjN⟩
  change ∃ p : Fin (n + 1),
    (∀ l, l < p → ofLex (mgRamWimanNextDegree r tail j) l =
      ofLex (mgRamWimanNextDegree r tail k) l) ∧
    ofLex (mgRamWimanNextDegree r tail j) p <
      ofLex (mgRamWimanNextDegree r tail k) p
  refine ⟨p, ?_, ?_⟩
  · intro l hlp
    have hlj : l ≤ j := by
      change (l : ℕ) ≤ (j : ℕ)
      change (l : ℕ) < (j : ℕ) + 1 at hlp
      omega
    have hlk : l ≤ k := le_trans hlj (le_of_lt hjk)
    rw [ofLex_mgRamWimanNextDegree_le r tail j l hlj,
      ofLex_mgRamWimanNextDegree_le r tail k l hlk]
  · have hpk : p ≤ k := by
      change (j : ℕ) + 1 ≤ (k : ℕ)
      exact Nat.succ_le_iff.mpr (Fin.mk_lt_mk.mp hjk)
    rw [show p = (⟨(j : ℕ) + 1, hjN⟩ : Fin (n + 1)) by rfl,
      ofLex_mgRamWimanNextDegree_succ r tail j hjN,
      ofLex_mgRamWimanNextDegree_le r tail k p hpk]
    exact sub_neg.mpr (hcharge j hjN)

theorem mgRamWiman_main_degree {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (m : Fin (n + 1)) :
    mgRamWimanSuffixDegree r tail (m : ℕ) +
        (mgRamWimanObservableDegree r tail m + mgRamStep r m) =
      mgRamWimanObservableDegree r tail m + mgRamWimanNextDegree r tail m := by
  rw [mgRamWimanNextDegree]
  abel

theorem mgRamWiman_higher_term_degree {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (m j : Fin (n + 1)) :
    mgRamWimanSuffixDegree r tail (j : ℕ) +
        (mgRamWimanObservableDegree r tail m + mgRamStep r j) =
      mgRamWimanObservableDegree r tail m + mgRamWimanNextDegree r tail j := by
  rw [mgRamWimanNextDegree]
  abel

theorem mgRamWiman_lower_derivative_target_prefix {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    {j m : Fin (n + 1)} (hjm : j < m) :
    let t := mgRamWimanObservableDegree r tail m + mgRamWimanNextDegree r tail m -
      mgRamWimanSuffixDegree r tail (j : ℕ)
    (∀ l, l < j → ofLex t l = 0) ∧ ofLex t j = (r j : ℤ) := by
  dsimp only
  constructor
  · intro l hlj
    change ofLex (mgRamWimanObservableDegree r tail m) l +
      ofLex (mgRamWimanNextDegree r tail m) l -
      ofLex (mgRamWimanSuffixDegree r tail (j : ℕ)) l = 0
    rw [ofLex_mgRamWimanObservableDegree_eq_zero_of_lt r tail (lt_trans hlj hjm),
      ofLex_mgRamWimanNextDegree_le r tail m l
        (le_trans (le_of_lt hlj) (le_of_lt hjm)),
      ofLex_mgRamWimanSuffixDegree_of_lt r tail (Fin.mk_lt_mk.mp hlj)]
    ring
  · change ofLex (mgRamWimanObservableDegree r tail m) j +
      ofLex (mgRamWimanNextDegree r tail m) j -
      ofLex (mgRamWimanSuffixDegree r tail (j : ℕ)) j = (r j : ℤ)
    rw [ofLex_mgRamWimanObservableDegree_eq_zero_of_lt r tail hjm,
      ofLex_mgRamWimanNextDegree_le r tail m j (le_of_lt hjm),
      ofLex_mgRamWimanSuffixDegree_self]
    ring

theorem hahnFractionRamSuffixProductBase_hasLeadAt_wiman
    {K : Type*} [Field K] {N : ℕ} {r : Fin N → ℕ} {tail : Fin N → ℤ}
    (A : Fin N → HahnFraction (mgDeg N) K) (lambda : Fin N → K)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j))
    (k : ℕ) :
    FracHasLeadAt (hahnFractionRamSuffixProductBase A k)
      (mgRamWimanSuffixDegree r tail k)
      (hahnFractionRamSuffixCoefficientBase lambda k) := by
  rw [hahnFractionRamSuffixCoefficientBase, mgRamWimanSuffixDegree]
  exact FracHasLeadAt.prod A (mgRamWimanVelocityDegree r tail) lambda
    (Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)))
    (fun j _ => hA j)

/-- One exact logarithmic step for a cleared Wiman bidiagonal velocity flag. -/
theorem hahnFractionRamCascade_logarithmicStep_hasLeadAtBase_wiman
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (_hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j))
    (m : Fin (n + 1)) (y : HahnFraction (mgDeg (n + 1)) K) (c : K)
    (hc : c ≠ 0)
    (hy : FracHasLeadAt y (mgRamWimanObservableDegree r tail m) c) :
    FracHasLeadAt (hahnFractionRamCascadeDerivationBase K r A y / y)
      (mgRamWimanNextDegree r tail m)
      (-hahnFractionRamSuffixCoefficientBase lambda (m : ℕ) *
        (((ofLex (mgRamWimanObservableDegree r tail m) m : ℤ) : K) / (r m : K))) := by
  classical
  let E := mgRamWimanObservableDegree r tail m
  let U := fun k : ℕ => mgRamWimanSuffixDegree r tail k
  let V := fun j : Fin (n + 1) => mgRamWimanNextDegree r tail j
  let Q := fun j : Fin (n + 1) => hahnFractionRamSuffixProductBase A (j : ℕ)
  let q := fun j : Fin (n + 1) => hahnFractionRamSuffixCoefficientBase lambda (j : ℕ)
  let a := -q m * ((((ofLex E m : ℤ) : K) / (r m : K)))
  let T := E + V m
  have hQ : ∀ j, FracHasLeadAt (Q j) (U (j : ℕ)) (q j) := by
    intro j
    exact hahnFractionRamSuffixProductBase_hasLeadAt_wiman A lambda hA (j : ℕ)
  have hterm : ∀ j : Fin (n + 1),
      FracHasLeadAt ((-Q j) * hahnFractionRamPartialBase K r j y) T
        (if j = m then a * c else 0) := by
    intro j
    by_cases hjm : j = m
    · subst j
      have hdy := hy.hahnFractionRamPartialBase (K := K) (r := r) (j := m)
      have hmain := (hQ m).neg.mul hdy
      rw [if_pos rfl]
      convert hmain using 1
      · dsimp [T, E, U, V]
        exact (mgRamWiman_main_degree r tail m).symm
      · dsimp [a, q, E]
        ring
    · rcases lt_or_gt_of_ne hjm with hjm' | hmj
      · have hd : ∀ l, l ≤ j → ofLex E l = 0 := by
          intro l hlj
          exact ofLex_mgRamWimanObservableDegree_eq_zero_of_lt r tail
            (lt_of_le_of_lt hlj hjm')
        let t := E + V m - U (j : ℕ)
        have htdata := mgRamWiman_lower_derivative_target_prefix r tail hjm'
        change (∀ l, l < j → ofLex t l = 0) ∧ ofLex t j = (r j : ℤ) at htdata
        have hdy : FracHasLeadAt (hahnFractionRamPartialBase K r j y) t 0 :=
          hy.hahnFractionRamPartialBase_of_prefix_zero hd htdata.1 htdata.2
        have hzero := (hQ j).neg.mul hdy
        rw [if_neg hjm]
        convert hzero using 1
        · dsimp [t, T]
          abel
        · ring
      · have hdy := hy.hahnFractionRamPartialBase (K := K) (r := r) (j := j)
        have hhigh := (hQ j).neg.mul hdy
        have hdegree : T < E + V j := by
          dsimp [T]
          simpa [add_comm] using add_lt_add_left (mgRamWimanNextDegree_lt hcharge hmj) E
        have hhigh' : FracHasLeadAt ((-Q j) * hahnFractionRamPartialBase K r j y)
            (E + V j)
            ((-q j) * (((((ofLex E j : ℤ) : K) / (r j : K))) * c)) := by
          convert hhigh using 1
          dsimp [E, U, V]
          exact (mgRamWiman_higher_term_degree r tail m j).symm
        rw [if_neg hjm]
        exact hhigh'.mono hdegree
  have hsum : FracHasLeadAt
      (∑ j : Fin (n + 1), (-Q j) * hahnFractionRamPartialBase K r j y)
      T (a * c) := by
    have h := FracHasLeadAt.sum
      (fun j : Fin (n + 1) => (-Q j) * hahnFractionRamPartialBase K r j y)
      T (fun j => if j = m then a * c else 0) Finset.univ
      (fun j _ => hterm j)
    simpa using h
  have hdelta : FracHasLeadAt (hahnFractionRamCascadeDerivationBase K r A y)
      T (a * c) := by
    rw [hahnFractionRamCascadeDerivationBase_apply]
    exact hsum
  have hquot := hdelta.div hy hc
  convert hquot using 1
  · dsimp [T, E, V]
    abel
  · dsimp [a, q, E]
    field_simp

/-- Every recursive logarithmic state has its exact Wiman-flag boundary. -/
theorem hahnFractionRamLogStateBase_exists_lead_wiman
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j))
    (m : Fin (n + 1)) :
    ∃ c : K, c ≠ 0 ∧
      FracHasLeadAt (hahnFractionRamLogStateBase K r A (m : ℕ))
        (mgRamWimanObservableDegree r tail m) c := by
  have hnat : ∀ k : ℕ, (hk : k < n + 1) →
      ∃ c : K, c ≠ 0 ∧
        FracHasLeadAt (hahnFractionRamLogStateBase K r A k)
          (mgRamWimanObservableDegree r tail ⟨k, hk⟩) c := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨1, one_ne_zero, ?_⟩
        have hfin : (⟨0, hk⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
        rw [hfin, mgRamWimanObservableDegree, dif_pos rfl]
        exact hahnFractionRamCoordinateBase_hasLeadAt K r 0
    | succ k ih =>
        intro hk
        have hk' : k < n + 1 := by omega
        obtain ⟨c, hc, hstate⟩ := ih hk'
        let km : Fin (n + 1) := ⟨k, hk'⟩
        have hnext := hahnFractionRamCascade_logarithmicStep_hasLeadAtBase_wiman
          r hr tail hcharge A lambda hA km (hahnFractionRamLogStateBase K r A k) c hc hstate
        let a : K :=
          -hahnFractionRamSuffixCoefficientBase lambda k *
            (((ofLex (mgRamWimanObservableDegree r tail km) km : ℤ) : K) / (r km : K))
        have hsuffix : hahnFractionRamSuffixCoefficientBase lambda k ≠ 0 :=
          hahnFractionRamSuffixCoefficientBase_ne_zero hlambda k
        have hselfZ : ofLex (mgRamWimanObservableDegree r tail km) km ≠ 0 :=
          ne_of_lt (ofLex_mgRamWimanObservableDegree_self_neg hr hcharge km)
        have hselfK : ((ofLex (mgRamWimanObservableDegree r tail km) km : ℤ) : K) ≠ 0 := by
          exact_mod_cast hselfZ
        have hrK : (r km : K) ≠ 0 := by
          exact_mod_cast (ne_of_gt (hr km))
        have ha : a ≠ 0 := by
          dsimp [a]
          exact mul_ne_zero (neg_ne_zero.mpr hsuffix) (div_ne_zero hselfK hrK)
        refine ⟨a, ha, ?_⟩
        rw [hahnFractionRamLogStateBase_succ]
        rw [mgRamWimanObservableDegree_succ r tail km (by simpa [km] using hk)]
        exact hnext
  exact hnat (m : ℕ) m.isLt

/-- Leading coefficient matrix of the Wiman logarithmic-state gradient. -/
def hahnFractionWimanCascadeLeadMatrixBase
    (K : Type*) [Field K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (c : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j =>
    (((ofLex (mgRamWimanObservableDegree r tail i) j : ℤ) : K) / (r j : K)) * c i

theorem hahnFractionWimanCascadeLeadMatrixBase_upper
    (K : Type*) [Field K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (tail : Fin (n + 1) → ℤ)
    (c : Fin (n + 1) → K) (i j : Fin (n + 1)) (hji : j < i) :
    hahnFractionWimanCascadeLeadMatrixBase K r tail c i j = 0 := by
  rw [hahnFractionWimanCascadeLeadMatrixBase,
    ofLex_mgRamWimanObservableDegree_eq_zero_of_lt r tail hji]
  norm_num

theorem hahnFractionWimanCascadeLeadMatrixBase_diag_ne_zero
    (K : Type*) [Field K] [CharZero K] {n : ℕ}
    {r : Fin (n + 1) → ℕ} (hr : ∀ j, 0 < r j)
    {tail : Fin (n + 1) → ℤ} (hcharge : RamifiedWimanChargesPositive r tail)
    (c : Fin (n + 1) → K) (hc : ∀ i, c i ≠ 0) (i : Fin (n + 1)) :
    hahnFractionWimanCascadeLeadMatrixBase K r tail c i i ≠ 0 := by
  rw [hahnFractionWimanCascadeLeadMatrixBase]
  have hselfZ : ofLex (mgRamWimanObservableDegree r tail i) i ≠ 0 :=
    ne_of_lt (ofLex_mgRamWimanObservableDegree_self_neg hr hcharge i)
  have hselfK : ((ofLex (mgRamWimanObservableDegree r tail i) i : ℤ) : K) ≠ 0 := by
    exact_mod_cast hselfZ
  have hrK : (r i : K) ≠ 0 := by exact_mod_cast (ne_of_gt (hr i))
  exact mul_ne_zero (div_ne_zero hselfK hrK) (hc i)

theorem hahnFractionWimanCascadeLeadMatrixBase_det_ne_zero
    (K : Type*) [Field K] [CharZero K] {n : ℕ}
    {r : Fin (n + 1) → ℕ} (hr : ∀ j, 0 < r j)
    {tail : Fin (n + 1) → ℤ} (hcharge : RamifiedWimanChargesPositive r tail)
    (c : Fin (n + 1) → K) (hc : ∀ i, c i ≠ 0) :
    (hahnFractionWimanCascadeLeadMatrixBase K r tail c).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular
    (hahnFractionWimanCascadeLeadMatrixBase_upper K r tail c)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    hahnFractionWimanCascadeLeadMatrixBase_diag_ne_zero K hr hcharge c hc i

theorem hahnFractionRamGradientMatrixBase_det_ne_zero_of_wiman_leads
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (f : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (c : Fin (n + 1) → K) (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, FracHasLeadAt (f i) (mgRamWimanObservableDegree r tail i) (c i)) :
    (hahnFractionRamGradientMatrixBase K r f).det ≠ 0 := by
  refine fracDet_ne_zero_of_hasLeadAt (hahnFractionRamGradientMatrixBase K r f)
    (mgRamWimanObservableDegree r tail) (mgRamStep r)
    (hahnFractionWimanCascadeLeadMatrixBase K r tail c) ?_
    (hahnFractionWimanCascadeLeadMatrixBase_det_ne_zero K hr hcharge c hc)
  intro i j
  exact (hf i).hahnFractionRamPartialBase (K := K) (r := r) (j := j)

/-- Cleared signed Wiman leads force independence of all logarithmic states. -/
theorem algebraicIndependent_hahnFractionRamLogStateBase_wiman
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j)) :
    AlgebraicIndependent K
      (fun i : Fin (n + 1) => hahnFractionRamLogStateBase K r A (i : ℕ)) := by
  choose c hc hf using fun i =>
    hahnFractionRamLogStateBase_exists_lead_wiman r hr tail hcharge A lambda hlambda hA i
  apply algebraicIndependent_of_hahnFractionRamGradientMatrixBase_det_ne_zero r
  exact hahnFractionRamGradientMatrixBase_det_ne_zero_of_wiman_leads
    r hr tail hcharge _ c hc hf

/-- **Exact Wiman-shape output-jet observability.**  The first full raw jet block is independent
over the coefficient field for arbitrary nonzero bidiagonal branch leads with positive cleared
Wiman charges and unrestricted higher Hahn terms. -/
theorem algebraicIndependent_hahnFractionRamCascadeOutputJetsBase_wiman
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j)) :
    AlgebraicIndependent K
      (fun j : Fin (n + 1) =>
        ((hahnFractionRamCascadeDerivationBase K r A :
            HahnFraction (mgDeg (n + 1)) K → HahnFraction (mgDeg (n + 1)) K)^[(j : ℕ)])
          (hahnFractionRamCoordinateBase K r 0)) := by
  apply algebraicIndependent_of_independent_family_mem_adjoin
    (fun j : Fin (n + 1) =>
      ((hahnFractionRamCascadeDerivationBase K r A :
          HahnFraction (mgDeg (n + 1)) K → HahnFraction (mgDeg (n + 1)) K)^[(j : ℕ)])
        (hahnFractionRamCoordinateBase K r 0))
    (fun i : Fin (n + 1) => hahnFractionRamLogStateBase K r A (i : ℕ))
    (algebraicIndependent_hahnFractionRamLogStateBase_wiman
      r hr tail hcharge A lambda hlambda hA)
    (hahnFractionRamLogStateBase_mem_outputJetAdjoin K r A)
    rfl

/-! ## Differential coefficient field -/

/-- Coefficient differentiation is degree zero, while a positive internal Wiman charge makes the
state-cascade contribution strictly earlier. -/
theorem hahnFractionRamCascadeDifferential_logarithmicStep_hasLeadAtBase_wiman
    {C K : Type*} [Field C] [Field K] [Algebra C K] [CharZero K] {n : ℕ}
    (dK : Derivation C K K)
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j))
    (m : Fin (n + 1)) (hm : (m : ℕ) + 1 < n + 1)
    (y : HahnFraction (mgDeg (n + 1)) K) (c : K) (hc : c ≠ 0)
    (hy : FracHasLeadAt y (mgRamWimanObservableDegree r tail m) c) :
    FracHasLeadAt
      (hahnFractionRamCascadeDifferentialDerivation C K dK r A y / y)
      (mgRamWimanNextDegree r tail m)
      (-hahnFractionRamSuffixCoefficientBase lambda (m : ℕ) *
        (((ofLex (mgRamWimanObservableDegree r tail m) m : ℤ) : K) / (r m : K))) := by
  let last : Fin (n + 1) := ⟨n, by omega⟩
  have hmlast : m < last := by
    change (m : ℕ) < n
    omega
  have hnextZero : mgRamWimanNextDegree r tail last = 0 := by
    apply ofLex.injective
    funext l
    change ofLex (mgRamWimanNextDegree r tail last) l = 0
    rw [ofLex_mgRamWimanNextDegree_le r tail last l]
    exact Fin.le_last l
  have hnextNeg : mgRamWimanNextDegree r tail m < 0 := by
    rw [← hnextZero]
    exact mgRamWimanNextDegree_lt hcharge hmlast
  have hcoeff := (hy.hahnFractionCoefficientDerivation dK).div hy hc
  have hcoeffZero :
      FracHasLeadAt (hahnFractionCoefficientDerivation dK y / y) 0 (dK c / c) := by
    convert hcoeff using 1
    abel
  have hcoeffLower :
      FracHasLeadAt (hahnFractionCoefficientDerivation dK y / y)
        (mgRamWimanNextDegree r tail m) 0 :=
    hcoeffZero.mono hnextNeg
  have hcascade := hahnFractionRamCascade_logarithmicStep_hasLeadAtBase_wiman
    r hr tail hcharge A lambda hA m y c hc hy
  rw [hahnFractionRamCascadeDifferentialDerivation_apply, add_div]
  simpa using hcoeffLower.add hcascade

/-- Every nonautonomous logarithmic state has the exact signed Wiman boundary. -/
theorem hahnFractionRamDifferentialLogStateBase_exists_lead_wiman
    {C K : Type*} [Field C] [Field K] [Algebra C K] [CharZero K] {n : ℕ}
    (dK : Derivation C K K)
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j))
    (m : Fin (n + 1)) :
    ∃ c : K, c ≠ 0 ∧
      FracHasLeadAt (hahnFractionRamDifferentialLogStateBase C K dK r A (m : ℕ))
        (mgRamWimanObservableDegree r tail m) c := by
  have hnat : ∀ k : ℕ, (hk : k < n + 1) →
      ∃ c : K, c ≠ 0 ∧
        FracHasLeadAt (hahnFractionRamDifferentialLogStateBase C K dK r A k)
          (mgRamWimanObservableDegree r tail ⟨k, hk⟩) c := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨1, one_ne_zero, ?_⟩
        have hfin : (⟨0, hk⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
        rw [hfin, mgRamWimanObservableDegree, dif_pos rfl]
        exact hahnFractionRamCoordinateBase_hasLeadAt K r 0
    | succ k ih =>
        intro hk
        have hk' : k < n + 1 := by omega
        obtain ⟨c, hc, hstate⟩ := ih hk'
        let km : Fin (n + 1) := ⟨k, hk'⟩
        have hnext := hahnFractionRamCascadeDifferential_logarithmicStep_hasLeadAtBase_wiman
          dK r hr tail hcharge A lambda hA km (by simpa [km] using hk)
          (hahnFractionRamDifferentialLogStateBase C K dK r A k) c hc hstate
        let a : K :=
          -hahnFractionRamSuffixCoefficientBase lambda k *
            (((ofLex (mgRamWimanObservableDegree r tail km) km : ℤ) : K) / (r km : K))
        have hsuffix : hahnFractionRamSuffixCoefficientBase lambda k ≠ 0 :=
          hahnFractionRamSuffixCoefficientBase_ne_zero hlambda k
        have hselfZ : ofLex (mgRamWimanObservableDegree r tail km) km ≠ 0 :=
          ne_of_lt (ofLex_mgRamWimanObservableDegree_self_neg hr hcharge km)
        have hselfK : ((ofLex (mgRamWimanObservableDegree r tail km) km : ℤ) : K) ≠ 0 := by
          exact_mod_cast hselfZ
        have hrK : (r km : K) ≠ 0 := by exact_mod_cast (ne_of_gt (hr km))
        have ha : a ≠ 0 := by
          dsimp [a]
          exact mul_ne_zero (neg_ne_zero.mpr hsuffix) (div_ne_zero hselfK hrK)
        refine ⟨a, ha, ?_⟩
        rw [hahnFractionRamDifferentialLogStateBase_succ]
        rw [mgRamWimanObservableDegree_succ r tail km (by simpa [km] using hk)]
        exact hnext
  exact hnat (m : ℕ) m.isLt

/-- Differential-coefficient Wiman logarithmic states are algebraically independent. -/
theorem algebraicIndependent_hahnFractionRamDifferentialLogStateBase_wiman
    {C K : Type*} [Field C] [Field K] [Algebra C K] [CharZero K] {n : ℕ}
    (dK : Derivation C K K)
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j)) :
    AlgebraicIndependent K
      (fun i : Fin (n + 1) =>
        hahnFractionRamDifferentialLogStateBase C K dK r A (i : ℕ)) := by
  choose c hc hf using fun i =>
    hahnFractionRamDifferentialLogStateBase_exists_lead_wiman
      dK r hr tail hcharge A lambda hlambda hA i
  apply algebraicIndependent_of_hahnFractionRamGradientMatrixBase_det_ne_zero r
  exact hahnFractionRamGradientMatrixBase_det_ne_zero_of_wiman_leads
    r hr tail hcharge _ c hc hf

/-- **Exact nonautonomous Wiman-shape observability.**  Clock differentiation and arbitrary clock
coefficients do not change the first full independent output-jet block. -/
theorem algebraicIndependent_hahnFractionRamDifferentialCascadeOutputJetsBase_wiman
    {C K : Type*} [Field C] [Field K] [Algebra C K] [CharZero K] {n : ℕ}
    (dK : Derivation C K K)
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (tail : Fin (n + 1) → ℤ) (hcharge : RamifiedWimanChargesPositive r tail)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) K)
    (lambda : Fin (n + 1) → K) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamWimanVelocityDegree r tail j) (lambda j)) :
    AlgebraicIndependent K
      (fun j : Fin (n + 1) =>
        ((hahnFractionRamCascadeDifferentialDerivation C K dK r A :
            HahnFraction (mgDeg (n + 1)) K → HahnFraction (mgDeg (n + 1)) K)^[(j : ℕ)])
          (hahnFractionRamCoordinateBase K r 0)) := by
  apply algebraicIndependent_of_independent_family_mem_adjoin
    (fun j : Fin (n + 1) =>
      ((hahnFractionRamCascadeDifferentialDerivation C K dK r A :
          HahnFraction (mgDeg (n + 1)) K → HahnFraction (mgDeg (n + 1)) K)^[(j : ℕ)])
        (hahnFractionRamCoordinateBase K r 0))
    (fun i : Fin (n + 1) =>
      hahnFractionRamDifferentialLogStateBase C K dK r A (i : ℕ))
    (algebraicIndependent_hahnFractionRamDifferentialLogStateBase_wiman
      dK r hr tail hcharge A lambda hlambda hA)
    (hahnFractionRamDifferentialLogStateBase_mem_outputJetAdjoin C K dK r A)
    rfl

end GaloisForLFunctions.HTGeometry
