/-
# The half-plane (quadrant-local) deck charge — the ℤ/4 refinement that survives reality

Reality forces a conjugation-symmetric zero configuration of `xiDescent` to have total order
`Σ_S ord = 2·(Σ_{upper} ord)` (`seam_order_two_mul`): the aggregate index sits wholly inside the
mod-`2` **discard** (`parity_blind_to_pairs` : `deckRed 2 (k+2q)=deckRed 2 k`, the pair count `q` is
invisible).  So the mod-`2` aggregate charge is *automatically* trivial — blind to a single odd upper
defect.

The fix is to keep the discarded quotient: the **half-plane charge**

  `halfCharge n S ord = wCharge n (Σ_{w∈S, Im w>0} ord w) ∈ ℤ/n`

is the one-sided (upper) order sum — a quadrant-local invariant, not a closed-loop charge.  Its
vanishing is **not** automatic from reality.  The exact relation to the aggregate is the tower
identity

  `wCharge (2^{k+1}) (Σ_S ord) = 0  ↔  halfCharge (2^k) S ord = 0`

(`aggregate_charge_succ_eq_zero_iff_halfCharge`): the aggregate at level `k+1` recovers the half
charge at level `k`.  In particular the **mod-4 aggregate** `wCharge 4 (Σ_S ord)` recovers the upper
parity bit that the mod-2 aggregate discards, and the witness `S = {i, −i}` (orders `1,1`) has
mod-2 aggregate `0`, half charge `1`, and mod-4 aggregate `2 ≠ 0`
(`exists_conjSym_halfCharge_ne_zero`).

Under RH the half charge is forced trivial (`rhLadder_imp_xiDescentHalfCharge_zero`), so it is the
finer detector on which the quadrant-seam conservation programme is posed: a nonzero half charge is a
genuine off-line odd defect that the aggregate cannot see.
-/
import GaloisForLFunctions.RHTower.UPlaneTorsor

namespace RHTower

open Complex

/-! ### §1 The invariant -/

/-- The upper-half order sum of a configuration: `Σ_{w∈S, Im w>0} ord w`. -/
noncomputable def upperOrder (S : Finset ℂ) (ord : ℂ → ℕ) : ℕ :=
  ∑ w ∈ S.filter (fun w => 0 < w.im), ord w

/-- The **half-plane (quadrant-local) deck charge** at modulus `n`: the reduction of the upper-half
order sum.  Finer than the mod-`n` charge of the full (conjugation-symmetric) aggregate, which reads
only twice this. -/
noncomputable def halfCharge (n : ℕ) (S : Finset ℂ) (ord : ℂ → ℕ) : ZMod n :=
  wCharge n ((upperOrder S ord : ℕ) : ℤ)

/-! ### §2 Reality: the aggregate is twice the half charge, hence mod-2 blind -/

/-- **Reality relation.**  For a conjugation-symmetric, fixed-point-free, conjugation-invariant
configuration, the total order is twice the upper-half order sum. -/
theorem aggregate_eq_two_upperOrder {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    ∑ w ∈ S, ord w = 2 * upperOrder S ord := by
  rw [upperOrder]; exact seam_order_two_mul ord hSconj hnofix hord

/-- **Mod-2 aggregate blindness.**  The rung-`1` charge of the full aggregate is always `0`: the pair
count is the discarded quotient. -/
theorem aggregate_wCharge_two_eq_zero {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    wCharge 2 ((∑ w ∈ S, ord w : ℕ) : ℤ) = 0 :=
  seam_charge_two_eq_zero ord hSconj hnofix hord

/-! ### §3 The half charge is a genuine mod-2 invariant -/

/-- The half charge vanishes at rung `1` exactly when the upper-half order sum is even. -/
theorem halfCharge_two_eq_zero_iff_even (S : Finset ℂ) (ord : ℂ → ℕ) :
    halfCharge 2 S ord = 0 ↔ Even (upperOrder S ord) := by
  rw [halfCharge, wCharge_eq_zero_iff, Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by omega⟩
  · rintro ⟨c, hc⟩; exact ⟨c, by omega⟩

/-- **Detection of a single odd upper defect.**  If the upper-half order sum is odd — exactly what a
lone off-line odd-order defect produces — the half charge is nonzero, while the aggregate reads `0`. -/
theorem halfCharge_two_ne_zero_of_odd_upperOrder {S : Finset ℂ} {ord : ℂ → ℕ}
    (hodd : ¬ Even (upperOrder S ord)) : halfCharge 2 S ord ≠ 0 :=
  fun h => hodd ((halfCharge_two_eq_zero_iff_even S ord).mp h)

/-! ### §4 The refinement: the aggregate at level `k+1` recovers the half charge at level `k` -/

/-- **The tower refinement.**  For a conjugation-symmetric configuration, the rung-`(k+1)` aggregate
charge vanishes exactly when the rung-`k` half charge vanishes.  The aggregate always reads twice the
half charge, so each aggregate rung recovers one lower half-charge rung; the mod-2 aggregate
(`k = 0`) recovers only the trivial rung — the blindness — while the mod-4 aggregate (`k = 1`)
recovers the upper parity. -/
theorem aggregate_charge_succ_eq_zero_iff_halfCharge {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) (k : ℕ) :
    wCharge (2 ^ (k + 1)) ((∑ w ∈ S, ord w : ℕ) : ℤ) = 0 ↔ halfCharge (2 ^ k) S ord = 0 := by
  haveI : NeZero (2 ^ (k + 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [wCharge_eq_zero_iff, Int.natCast_dvd_natCast,
    aggregate_eq_two_upperOrder ord hSconj hnofix hord, pow_succ',
    mul_dvd_mul_iff_left (two_ne_zero), halfCharge, wCharge_eq_zero_iff, Int.natCast_dvd_natCast]

/-- **The ℤ/4 refinement, explicit.**  For a conjugation-symmetric configuration the mod-4 aggregate
vanishes exactly when the upper-half order sum is even — the parity bit the mod-2 aggregate cannot
see. -/
theorem mod4_aggregate_eq_zero_iff_upper_even {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hnofix : ∀ w ∈ S, (starRingEnd ℂ) w ≠ w)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    wCharge 4 ((∑ w ∈ S, ord w : ℕ) : ℤ) = 0 ↔ Even (upperOrder S ord) := by
  have h := aggregate_charge_succ_eq_zero_iff_halfCharge ord hSconj hnofix hord 1
  rw [show (2 : ℕ) ^ (1 + 1) = 4 from by norm_num] at h
  rw [h, show (2 : ℕ) ^ 1 = 2 from by norm_num, halfCharge_two_eq_zero_iff_even]

/-! ### §5 Non-automaticity: reality does not kill the half charge -/

/-- **The half charge survives the conjugate-pair collapse.**  There is a conjugation-symmetric,
fixed-point-free, conjugation-invariant configuration (`{i, −i}`, orders `1,1`) whose mod-2 aggregate
charge is `0` but whose half charge is nonzero — and whose mod-4 aggregate is nonzero.  Reality forces
the aggregate even, but leaves the upper parity free: the quadrant-local invariant is not vacuous. -/
theorem exists_conjSym_halfCharge_ne_zero :
    ∃ (S : Finset ℂ) (ord : ℂ → ℕ),
      (∀ w ∈ S, (starRingEnd ℂ) w ∈ S) ∧ (∀ w ∈ S, (starRingEnd ℂ) w ≠ w) ∧
      (∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) ∧
      wCharge 2 ((∑ w ∈ S, ord w : ℕ) : ℤ) = 0 ∧
      halfCharge 2 S ord ≠ 0 ∧
      wCharge 4 ((∑ w ∈ S, ord w : ℕ) : ℤ) ≠ 0 := by
  have hIne : (I : ℂ) ≠ -I := by
    intro h; have := congrArg Complex.im h
    simp only [Complex.I_im, Complex.neg_im] at this; norm_num at this
  have hnIne : (-I : ℂ) ≠ I := hIne.symm
  have hfilter : (({I, -I} : Finset ℂ).filter (fun w => 0 < w.im)) = {I} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hz⟩
      · rfl
      · exact absurd hz (by simp [Complex.neg_im, Complex.I_im])
    · rintro rfl; exact ⟨Or.inl rfl, by simp [Complex.I_im]⟩
  have hupper : upperOrder ({I, -I} : Finset ℂ) (fun _ => 1) = 1 := by
    rw [upperOrder, hfilter, Finset.sum_singleton]
  have hsum : (∑ w ∈ ({I, -I} : Finset ℂ), (fun _ : ℂ => 1) w) = 2 := by
    rw [Finset.sum_pair hIne]
  refine ⟨{I, -I}, fun _ => 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inr Complex.conj_I
    · left; rw [map_neg, Complex.conj_I, neg_neg]
  · intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · rw [Complex.conj_I]; exact hnIne
    · rw [map_neg, Complex.conj_I, neg_neg]; exact hIne
  · intro _ _; rfl
  · rw [hsum]; decide
  · rw [halfCharge, hupper]; decide
  · rw [hsum]; decide

/-! ### §6 The descended function: the half charge, and RH forces it trivial -/

/-- The half-plane charge of the descended completed zeta on a configuration of `u`-plane points. -/
noncomputable def xiDescentHalfCharge (k : ℕ) (S : Finset ℂ) : ZMod (2 ^ k) :=
  halfCharge (2 ^ k) S (fun w => (analyticOrderAt xiDescent w).toNat)

/-- **RH forces the half charge trivial.**  If `RHLadder k` holds, then for any configuration of
slit-plane points the descended half charge vanishes: every upper zero has order divisible by `2^k`,
so the upper-half order sum is too.  A nonzero half charge is therefore a genuine off-line odd defect
— the finer detector past the aggregate's blindness. -/
theorem rhLadder_imp_xiDescentHalfCharge_zero {k : ℕ} {S : Finset ℂ}
    (hS : ∀ w ∈ S, w ∈ slitPlane) (hlad : RHLadder k) :
    xiDescentHalfCharge k S = 0 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [xiDescentHalfCharge, halfCharge, wCharge_eq_zero_iff, Int.natCast_dvd_natCast, upperOrder]
  have hlad' := (rhLadder_iff_xiDescent_upperHalf k).mp hlad
  refine Finset.dvd_sum ?_
  intro w hw
  rw [Finset.mem_filter] at hw
  obtain ⟨hwS, hwim⟩ := hw
  by_cases hz : xiDescent w = 0
  · have hdvd := hlad' w (hS w hwS) (le_of_lt hwim) hz
    have hcoe : analyticOrderAt xiDescent w = ((analyticOrderAt xiDescent w).toNat : ℕ∞) :=
      (ENat.coe_toNat (xiDescent_orderAt_ne_top w)).symm
    rw [hcoe] at hdvd
    exact_mod_cast hdvd
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]; simp

end RHTower
