import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexUnderRotationDampingAndCoalescence
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.UpperLefschetzBoundsAreBlindOnlyToRealZeros

/-!
# The twist tower completes the upper count

Over `𝔽_q` the index of a curve's trace kernel is first bounded by the genus and then brought to
zero by a count. Auxiliary-polynomial constructions (Stepanov) produce **upper** counts
`N ≤ q + 1 + C√q`; the global law needs the **lower** count. This module isolates how the lower count
is obtained, in the language of curve data.

**Riemann–Roch ceiling** (`two_mul_negIndex_traceKernel_le`, `golden_attains_ceiling`). The index
of the trace kernel is at most the genus: reflection maps the outer eigenvalues injectively to the
inner ones. The golden datum attains the ceiling with positive point counts.

**The parity twin over `𝔽_q` is index-preserving** (`quadTwist`, `negIndex_traceKernel_quadTwist`).
The quadratic twist `β ↦ −β` twists the trace kernel by the unitary character `(−1)^n`, so it has
the same index, while the counts pair off: `N_k + N_k' = 2(q^k + 1)` for odd `k`
(`pointCount_add_quadTwist_of_odd`), `N_k' = N_k` for even `k`.

**One twist does not complete** (`splitDatum`, `one_twist_does_not_complete`). The datum with
eigenvalues `±2, ±½` satisfies the upper count for itself and for its twist with constant `0`, and
is not unitary: even degrees carry no parity information.

**The twist tower completes** (`unitary_iff_twistTower_upper`). Upper counts, with one constant,
for the quadratic twists of all `2`-power base changes (`twistCount D (2^j) m`, the count over
`𝔽_{q^{2^j m}}` of the twist of the base change to `𝔽_{q^{2^j}}`) are equivalent to RH: writing
`k = 2^j m` with `m` odd, the twist count at `(2^j, m)` is the curve's lower count at `k`.

**Twisted base changes** (`baseChange`, `twistCount_eq_pointCount`,
`unitary_iff_twistedBaseChanges_upper`). The twist count is the point count of an actual datum, the
quadratic twist of the base change to `𝔽_{q^{2^j}}`; on zeta functions the twist is the vertical shift
`s ↦ s + iπ/log q^{2^j}`. Over `𝔽_q` these shifts are geometric, so an upper-count producer applies to
each of them.

So a producer of upper counts reaches the global law only together with a parity symmetry acting on
every base change. Over `ℤ` the parity twin (the Liouville twist) acts on the prime constituents
tower by tower but not on the archimedean factor, and the complementary parity class of the primes
carries no upper-count producer.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HeckeKreinToeplitz.CurveDatumKernel

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-! ### The Riemann–Roch ceiling -/

/-- **The Riemann–Roch ceiling.** Twice the index of the trace kernel is at most the number of
Frobenius eigenvalues: `κ ≤ g`. -/
theorem two_mul_negIndex_traceKernel_le :
    2 * negIndex (traceKernel D) ≤ Fintype.card ι := by
  classical
  rw [negIndex_traceKernel]
  set inner : Finset ι := univ.filter fun i => ‖D.β i‖ < 1
  have hin : (outer D).card ≤ inner.card := by
    refine card_le_card_of_injOn (reflectPerm D) (fun i hi => ?_) (reflectPerm D).injective.injOn
    have h1 : 1 < ‖D.β i‖ := (mem_filter.mp hi).2
    simp only [inner, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, norm_β_reflectPerm]
    exact inv_lt_one_of_one_lt₀ h1
  have hdisj : Disjoint (outer D) inner := disjoint_filter.mpr fun i _ h1 h2 =>
    lt_asymm h1 h2
  have hsum := card_union_of_disjoint hdisj ▸ card_le_univ (outer D ∪ inner)
  have himg := card_image_le (s := outer D) (f := D.β)
  have : 2 * ((outer D).image D.β).card ≤ Fintype.card ι := by omega
  exact_mod_cast this

/-- The golden datum attains the ceiling: genus one, index one. -/
theorem golden_attains_ceiling :
    2 * negIndex (traceKernel goldenDatum) = Fintype.card (Fin 2) := by
  rw [negIndex_golden_traceKernel]; simp

/-! ### The quadratic twist -/

/-- The **quadratic twist** `β ↦ −β`: the zeta function at `−T`. -/
def quadTwist : CurveDatum ι where
  q := D.q
  one_lt_q := D.one_lt_q
  β := fun i => -D.β i
  conjPerm := D.conjPerm
  β_conjPerm := fun i => by rw [D.β_conjPerm, map_neg]
  fePerm := D.fePerm
  β_fePerm := fun i => by
    rw [show -D.β (D.fePerm i) * -D.β i = D.β (D.fePerm i) * D.β i by ring, D.β_fePerm]

theorem trace_quadTwist (k : ℕ) : (quadTwist D).trace k = (-1) ^ k * D.trace k := by
  have h : (quadTwist D).powerSum k = (-1) ^ k * D.powerSum k := by
    simp only [CurveDatum.powerSum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    show (-D.β i) ^ k = (-1) ^ k * D.β i ^ k
    rw [neg_eq_neg_one_mul, mul_pow]
  rw [CurveDatum.trace, h, show ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) by push_cast; ring,
    re_ofReal_mul]
  rfl

theorem pointCount_quadTwist (k : ℕ) :
    (quadTwist D).pointCount k = D.q ^ k + 1 - (-1) ^ k * D.sqrtq ^ k * D.trace k := by
  simp only [CurveDatum.pointCount, trace_quadTwist]
  rw [show (quadTwist D).sqrtq = D.sqrtq from rfl, show (quadTwist D).q = D.q from rfl]
  ring

/-- **The twin counts pair off in odd degree**: `N_k + N_k' = 2(q^k + 1)`. -/
theorem pointCount_add_quadTwist_of_odd {k : ℕ} (hk : Odd k) :
    D.pointCount k + (quadTwist D).pointCount k = 2 * (D.q ^ k + 1) := by
  rw [pointCount_quadTwist, CurveDatum.pointCount, hk.neg_one_pow]; ring

/-- In even degree the twin has the curve's counts. -/
theorem pointCount_quadTwist_of_even {k : ℕ} (hk : Even k) :
    (quadTwist D).pointCount k = D.pointCount k := by
  rw [pointCount_quadTwist, CurveDatum.pointCount, hk.neg_one_pow]; ring

/-- **The parity twin is index-preserving**: its trace kernel is the twist of the curve's by the
unitary character `(−1)^n`. -/
theorem negIndex_traceKernel_quadTwist :
    negIndex (traceKernel (quadTwist D)) = negIndex (traceKernel D) := by
  have hβ : ∀ i, D.β i ≠ 0 := β_ne_zero D
  have hk : traceKernel (quadTwist D) = fun n => valChar (-1) n * traceKernel D n := by
    funext n
    simp only [traceKernel, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [valChar, quadTwist, neg_eq_zero, hβ i, if_false, one_ne_zero, MonoidHom.coe_mk,
      OneHom.coe_mk]
    rw [show -D.β i = (-1) * D.β i by ring, mul_zpow]
  rw [hk]
  exact negIndex_twist (fun n => by
    simp only [valChar, neg_eq_zero, one_ne_zero, if_false, MonoidHom.coe_mk, OneHom.coe_mk,
      norm_zpow, norm_neg, norm_one, one_zpow]) _

/-! ### One twist does not complete -/

/-- The datum with eigenvalues `2, −2, ½, −½` over `q = 5`. -/
def splitDatum : CurveDatum (Fin 4) where
  q := 5
  one_lt_q := by norm_num
  β := ![2, -2, 1 / 2, -(1 / 2)]
  conjPerm := Equiv.refl _
  β_conjPerm := fun i => by fin_cases i <;> simp [Complex.conj_ofNat]
  fePerm := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩
  β_fePerm := fun i => by fin_cases i <;> simp

theorem splitDatum_trace (k : ℕ) :
    splitDatum.trace k = 2 ^ k * (1 + (-1) ^ k) + (1 / 2) ^ k * (1 + (-1) ^ k) := by
  have h : splitDatum.powerSum k =
      (((2 ^ k * (1 + (-1) ^ k) + (1 / 2) ^ k * (1 + (-1) ^ k) : ℝ)) : ℂ) := by
    simp only [CurveDatum.powerSum, splitDatum, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    rw [neg_eq_neg_one_mul (2 : ℂ), neg_eq_neg_one_mul ((1 : ℂ) / 2), mul_pow, mul_pow]
    push_cast
    ring
  rw [CurveDatum.trace, h, ofReal_re]

theorem splitDatum_trace_nonneg (k : ℕ) : 0 ≤ splitDatum.trace k := by
  rw [splitDatum_trace]
  have h : 0 ≤ 1 + (-1 : ℝ) ^ k := by
    rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num
  positivity

/-- **One twist does not complete the upper count.** The split datum satisfies the upper count
`N_k ≤ q^k + 1` for itself and for its quadratic twist, yet it is not unitary. -/
theorem one_twist_does_not_complete :
    (∀ k, splitDatum.pointCount k ≤ splitDatum.q ^ k + 1 + 0 * splitDatum.sqrtq ^ k) ∧
      (∀ k, (quadTwist splitDatum).pointCount k ≤
        (quadTwist splitDatum).q ^ k + 1 + 0 * (quadTwist splitDatum).sqrtq ^ k) ∧
      ¬ ∀ i, ‖splitDatum.β i‖ = 1 := by
  refine ⟨fun k => (splitDatum.neg_le_trace_iff_pointCount_le k 0).mp (by
      rw [neg_zero]; exact splitDatum_trace_nonneg k),
    fun k => ((quadTwist splitDatum).neg_le_trace_iff_pointCount_le k 0).mp (by
      rw [neg_zero, trace_quadTwist, splitDatum_trace]
      rcases Nat.even_or_odd k with h | h
      · rw [h.neg_one_pow]; positivity
      · rw [h.neg_one_pow]; norm_num), fun h => ?_⟩
  have := h 0
  simp [splitDatum] at this

/-! ### The twist tower -/

/-- The count over `𝔽_{q^{nm}}` of the quadratic twist of the base change to `𝔽_{q^n}`:
`q^{nm} + 1 − (−1)^m q^{nm/2} Σ_i β_i^{nm}`. -/
def twistCount (n m : ℕ) : ℝ :=
  D.q ^ (n * m) + 1 - (-1) ^ m * D.sqrtq ^ (n * m) * D.trace (n * m)

theorem twistCount_le_iff (n m : ℕ) (C : ℝ) :
    twistCount D n m ≤ D.q ^ (n * m) + 1 + C * D.sqrtq ^ (n * m) ↔
      -C ≤ (-1) ^ m * D.trace (n * m) := by
  have hs : 0 < D.sqrtq ^ (n * m) := pow_pos D.sqrtq_pos _
  unfold twistCount
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The twist tower completes the upper count.** A curve datum is unitary iff, for one constant
`C`, the quadratic twists of all its `2`-power base changes satisfy the upper count
`N ≤ q^{2^j m} + 1 + C q^{2^j m/2}`. -/
theorem unitary_iff_twistTower_upper :
    (∀ i, ‖D.β i‖ = 1) ↔
      ∃ C : ℝ, ∀ j m : ℕ, twistCount D (2 ^ j) m ≤ D.q ^ (2 ^ j * m) + 1 + C * D.sqrtq ^ (2 ^ j * m) := by
  constructor
  · intro hU
    refine ⟨Fintype.card ι, fun j m => (twistCount_le_iff D _ _ _).mpr ?_⟩
    have := D.abs_trace_le_card_of_unitary hU (2 ^ j * m)
    rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [h] <;> linarith [abs_le.mp this]
  · rintro ⟨C, hC⟩
    refine D.unitary_of_trace_le (C := max C (Fintype.card ι)) fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [CurveDatum.trace_zero]; exact le_max_right _ _
    · obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk.ne'
      have := (twistCount_le_iff D _ _ _).mp (hC j m)
      rw [hm.neg_one_pow] at this
      linarith [le_max_left C (Fintype.card ι)]

/-! ### The twist tower as twisted base changes -/

/-- The **base change** to `𝔽_{q^n}`: eigenvalues `β^n` over `q^n`. -/
def baseChange (n : ℕ) (hn : 0 < n) : CurveDatum ι where
  q := D.q ^ n
  one_lt_q := one_lt_pow₀ D.one_lt_q hn.ne'
  β := fun i => D.β i ^ n
  conjPerm := D.conjPerm
  β_conjPerm := fun i => by rw [D.β_conjPerm, map_pow]
  fePerm := D.fePerm
  β_fePerm := fun i => by rw [← mul_pow, D.β_fePerm, one_pow]

theorem trace_baseChange (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (baseChange D n hn).trace k = D.trace (n * k) := by
  simp only [CurveDatum.trace, CurveDatum.powerSum, baseChange, ← pow_mul]

theorem sqrtq_baseChange (n : ℕ) (hn : 0 < n) : (baseChange D n hn).sqrtq = D.sqrtq ^ n := by
  have hq : D.q ^ n = (D.sqrtq ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, D.sqrtq_sq]
  show Real.sqrt (D.q ^ n) = D.sqrtq ^ n
  rw [hq, Real.sqrt_sq (pow_nonneg D.sqrtq_pos.le n)]

/-- **The twist count is the count of a twisted base change**: the point count of the quadratic
twist of the base change to `𝔽_{q^n}`, over `𝔽_{q^{nm}}`. -/
theorem twistCount_eq_pointCount (n : ℕ) (hn : 0 < n) (m : ℕ) :
    twistCount D n m = (quadTwist (baseChange D n hn)).pointCount m := by
  rw [pointCount_quadTwist, trace_baseChange, sqrtq_baseChange, twistCount,
    show (baseChange D n hn).q = D.q ^ n from rfl, ← pow_mul, ← pow_mul]

/-- **RH for curve data is the upper count for the twisted `2`-power base changes.** -/
theorem unitary_iff_twistedBaseChanges_upper :
    (∀ i, ‖D.β i‖ = 1) ↔ ∃ C : ℝ, ∀ j m : ℕ,
      (quadTwist (baseChange D (2 ^ j) (pow_pos two_pos j))).pointCount m ≤
        (quadTwist (baseChange D (2 ^ j) (pow_pos two_pos j))).q ^ m + 1 +
          C * (quadTwist (baseChange D (2 ^ j) (pow_pos two_pos j))).sqrtq ^ m := by
  rw [unitary_iff_twistTower_upper]
  refine exists_congr fun C => forall₂_congr fun j m => ?_
  rw [← twistCount_eq_pointCount, show (quadTwist (baseChange D (2 ^ j) (pow_pos two_pos j))).q =
    D.q ^ 2 ^ j from rfl, show (quadTwist (baseChange D (2 ^ j) (pow_pos two_pos j))).sqrtq =
    (baseChange D (2 ^ j) (pow_pos two_pos j)).sqrtq from rfl, sqrtq_baseChange, ← pow_mul,
    ← pow_mul]

end GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.ArithmeticKreinLangerTheory in
#print axioms unitary_iff_twistedBaseChanges_upper
