/-
Schatten classes via approximation numbers, and the Sonin trace-ideal obstruction.

The `n`-th approximation number of a bounded operator on a complex Hilbert space is its
distance from the operators of rank at most `n`; on a Hilbert space these coincide with the
singular values, so `p`-summability of the approximation numbers defines the Schatten
`p`-class. Every member of every class is compact: summability drives the approximation
numbers to zero and the finite-rank approximants converge in operator norm. The classes are
increasing in the exponent, and finite-rank operators belong to every class.

Consequently a noncompact operator lies in no Schatten class for any positive exponent. The
Sonin dilation corners, the positive Euler corners, the archimedean Hardy--Titchmarsh source
corners, their quadratic Gram entries, and the Euler semicommutator are all excluded from
every trace ideal at once.
-/
import GaloisForLFunctions.RHTower.SoninEssentialNormExtensions

noncomputable section

namespace RHTower

open ContinuousLinearMap Metric Filter
open scoped InnerProduct

section ApproximationNumbers

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator has rank at most `n` when its range lies in a subspace of dimension at
most `n`. -/
def HasRankLE (F : H →L[ℂ] H) (n : ℕ) : Prop :=
  ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ n ∧ ∀ x, F x ∈ V

theorem hasRankLE_zero (n : ℕ) : HasRankLE (0 : H →L[ℂ] H) n :=
  ⟨⊥, inferInstance, by simp, fun x => by simp⟩

theorem HasRankLE.mono {F : H →L[ℂ] H} {m n : ℕ} (h : HasRankLE F m) (hmn : m ≤ n) :
    HasRankLE F n := by
  obtain ⟨V, hfd, hle, hmem⟩ := h
  exact ⟨V, hfd, hle.trans hmn, hmem⟩

/-- Operators of finite rank are compact: the image of the unit ball is a bounded subset of a
finite-dimensional subspace. -/
theorem isCompactOperator_of_hasRankLE {F : H →L[ℂ] H} {n : ℕ} (h : HasRankLE F n) :
    IsCompactOperator F := by
  obtain ⟨V, hfd, -, hmem⟩ := h
  refine ⟨Subtype.val '' closedBall (0 : V) (‖F‖ + 1),
    (isCompact_closedBall 0 _).image continuous_subtype_val, ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_
  intro x hx
  refine ⟨⟨F x, hmem x⟩, ?_, rfl⟩
  rw [mem_closedBall_zero_iff]
  calc ‖(⟨F x, hmem x⟩ : V)‖ = ‖F x‖ := rfl
    _ ≤ ‖F‖ * ‖x‖ := F.le_opNorm x
    _ ≤ ‖F‖ * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_zero_iff.mp hx)) (norm_nonneg F)
    _ ≤ ‖F‖ + 1 := by rw [mul_one]; linarith [norm_nonneg F]

/-- The `n`-th approximation number: the distance from the operators of rank at most `n`. -/
def approxNumber (T : H →L[ℂ] H) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ F : H →L[ℂ] H, HasRankLE F n ∧ ‖T - F‖ = r}

theorem approxNumber_set_nonempty (T : H →L[ℂ] H) (n : ℕ) :
    {r : ℝ | ∃ F : H →L[ℂ] H, HasRankLE F n ∧ ‖T - F‖ = r}.Nonempty :=
  ⟨‖T‖, 0, hasRankLE_zero n, by rw [sub_zero]⟩

theorem approxNumber_set_bddBelow (T : H →L[ℂ] H) (n : ℕ) :
    BddBelow {r : ℝ | ∃ F : H →L[ℂ] H, HasRankLE F n ∧ ‖T - F‖ = r} := by
  refine ⟨0, ?_⟩
  rintro r ⟨F, -, rfl⟩
  positivity

theorem approxNumber_le (T : H →L[ℂ] H) (n : ℕ) (F : H →L[ℂ] H) (hF : HasRankLE F n) :
    approxNumber T n ≤ ‖T - F‖ :=
  csInf_le (approxNumber_set_bddBelow T n) ⟨F, hF, rfl⟩

theorem approxNumber_nonneg (T : H →L[ℂ] H) (n : ℕ) : 0 ≤ approxNumber T n := by
  refine le_csInf (approxNumber_set_nonempty T n) ?_
  rintro r ⟨F, -, rfl⟩
  positivity

theorem approxNumber_le_norm (T : H →L[ℂ] H) (n : ℕ) : approxNumber T n ≤ ‖T‖ := by
  simpa using approxNumber_le T n 0 (hasRankLE_zero n)

theorem approxNumber_antitone (T : H →L[ℂ] H) : Antitone (approxNumber T) := by
  intro m n hmn
  refine csInf_le_csInf (approxNumber_set_bddBelow T n) (approxNumber_set_nonempty T m) ?_
  rintro r ⟨F, hF, rfl⟩
  exact ⟨F, hF.mono hmn, rfl⟩

theorem exists_hasRankLE_norm_sub_lt (T : H →L[ℂ] H) (n : ℕ) {ε : ℝ}
    (h : approxNumber T n < ε) :
    ∃ F : H →L[ℂ] H, HasRankLE F n ∧ ‖T - F‖ < ε := by
  obtain ⟨r, hrmem, hr⟩ := (csInf_lt_iff (approxNumber_set_bddBelow T n)
    (approxNumber_set_nonempty T n)).mp h
  obtain ⟨F, hF, rfl⟩ := hrmem
  exact ⟨F, hF, hr⟩

/-- Membership in the Schatten `p`-class: `p`-summability of the approximation numbers. -/
def MemSchattenClass (p : ℝ) (T : H →L[ℂ] H) : Prop :=
  Summable fun n => approxNumber T n ^ p

theorem MemSchattenClass.tendsto_approxNumber {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) :
    Tendsto (approxNumber T) atTop (nhds 0) := by
  have h1 : Tendsto (fun n => approxNumber T n ^ p) atTop (nhds 0) :=
    hT.tendsto_atTop_zero
  have h2 : Tendsto (fun y : ℝ => y ^ p⁻¹) (nhds 0) (nhds 0) := by
    have h := (Real.continuousAt_rpow_const 0 p⁻¹ (Or.inr (by positivity))).tendsto
    rwa [Real.zero_rpow (inv_ne_zero hp.ne')] at h
  have h3 : Tendsto (fun n => (approxNumber T n ^ p) ^ p⁻¹) atTop (nhds 0) := h2.comp h1
  refine h3.congr fun n => ?_
  rw [← Real.rpow_mul (approxNumber_nonneg T n), mul_inv_cancel₀ hp.ne', Real.rpow_one]

/-- **Schatten operators are compact.** Summability of the approximation numbers makes the
operator a norm-limit of finite-rank operators. -/
theorem MemSchattenClass.isCompactOperator [CompleteSpace H] {p : ℝ} (hp : 0 < p)
    {T : H →L[ℂ] H} (hT : MemSchattenClass p T) : IsCompactOperator T := by
  have hmem : T ∈ closure {W : H →L[ℂ] H | IsCompactOperator W} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨n, hn⟩ := ((hT.tendsto_approxNumber hp).eventually_lt_const hδ).exists
    obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt T n hn
    refine ⟨F, isCompactOperator_of_hasRankLE hF, ?_⟩
    rw [dist_eq_norm]
    exact hFlt
  exact isClosed_setOf_isCompactOperator.closure_subset hmem

/-- Finite-rank operators lie in every Schatten class. -/
theorem memSchattenClass_of_hasRankLE {p : ℝ} (hp : 0 < p) {F : H →L[ℂ] H} {n : ℕ}
    (hF : HasRankLE F n) : MemSchattenClass p F := by
  have hzero : ∀ m, n ≤ m → approxNumber F m = 0 := fun m hm =>
    le_antisymm (by simpa using approxNumber_le F m F (hF.mono hm))
      (approxNumber_nonneg F m)
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro m hm
  rw [hzero m (by simpa using Finset.mem_range.not.mp hm), Real.zero_rpow hp.ne']

/-- The Schatten classes increase with the exponent. -/
theorem MemSchattenClass.mono {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) : MemSchattenClass q T := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hT.tendsto_approxNumber hp).eventually_lt_const one_pos)
  have htail : Summable fun n => approxNumber T (n + N) ^ p :=
    (summable_nat_add_iff N).mpr hT
  have htailq : Summable fun n => approxNumber T (n + N) ^ q := by
    refine htail.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact Real.rpow_nonneg (approxNumber_nonneg T _) q
    · rcases eq_or_lt_of_le (approxNumber_nonneg T (n + N)) with hzero | hpos
      · rw [← hzero, Real.zero_rpow (hp.trans_le hpq).ne', Real.zero_rpow hp.ne']
      · exact Real.rpow_le_rpow_of_exponent_ge hpos
          (le_of_lt (hN (n + N) (Nat.le_add_left N n))) hpq
  exact (summable_nat_add_iff N).mp htailq

/-- A noncompact operator lies in no Schatten class. -/
theorem not_memSchattenClass_of_not_isCompactOperator [CompleteSpace H] {p : ℝ}
    (hp : 0 < p) {T : H →L[ℂ] H} (h : ¬ IsCompactOperator T) :
    ¬ MemSchattenClass p T :=
  fun hT => h (hT.isCompactOperator hp)

end ApproximationNumbers

/-! ### The Sonin trace-ideal obstruction -/

/-- The one-scale even Sonin dilation corner lies in no Schatten class. -/
theorem not_memSchattenClass_evenCentralSoninDilationCorner
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    ¬ MemSchattenClass s (evenCentralSoninDilationCorner a p hp) :=
  not_memSchattenClass_of_not_isCompactOperator hs
    (evenCentralSoninDilationCorner_not_isCompactOperator a p ha hp)

/-- The positive Euler corner lies in no Schatten class. -/
theorem not_memSchattenClass_evenCentralPositiveEulerCorner
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    ¬ MemSchattenClass s (evenCentralPositiveEulerCorner a p hp) :=
  not_memSchattenClass_of_not_isCompactOperator hs
    (evenCentralPositiveEulerCorner_not_isCompactOperator a p ha hp)

/-- The literal archimedean Hardy--Titchmarsh Euler corner lies in no Schatten class: no
trace-ideal or Fredholm-determinant regularization applies to the unsmoothed source metric. -/
theorem not_memSchattenClass_archimedeanPrimeEulerCorner
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    ¬ MemSchattenClass s (archimedeanPrimeEulerCorner a p) :=
  not_memSchattenClass_of_not_isCompactOperator hs
    (archimedeanPrimeEulerCorner_not_isCompactOperator a p ha hp)

/-- The ordered two-scale archimedean Euler Gram entry lies in no Schatten class. -/
theorem not_memSchattenClass_archimedeanPrimeEulerQuadraticCorner
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) {s : ℝ} (hs : 0 < s) :
    ¬ MemSchattenClass s (archimedeanPrimeEulerQuadraticCorner a p q) :=
  not_memSchattenClass_of_not_isCompactOperator hs
    (archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator a p q ha hp hq)

/-- The Euler metric semicommutator lies in no Schatten class. -/
theorem not_memSchattenClass_archimedeanPrimeEulerSemicommutator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) {s : ℝ} (hs : 0 < s) :
    ¬ MemSchattenClass s (archimedeanPrimeEulerSemicommutator a p) :=
  not_memSchattenClass_of_not_isCompactOperator hs
    (archimedeanPrimeEulerSemicommutator_not_isCompactOperator a p ha hp)

/-- The prime specialization of the trace-ideal obstruction on the literal source carrier. -/
theorem not_memSchattenClass_archimedeanPrimeEulerCorner_natPrime
    (a : ℝ) (p : ℕ) (ha : 0 < a) (hp : p.Prime) {s : ℝ} (hs : 0 < s) :
    ¬ MemSchattenClass s (archimedeanPrimeEulerCorner a (p : ℝ)) :=
  not_memSchattenClass_archimedeanPrimeEulerCorner a (p : ℝ) ha
    (by exact_mod_cast hp.one_lt) hs

end RHTower
