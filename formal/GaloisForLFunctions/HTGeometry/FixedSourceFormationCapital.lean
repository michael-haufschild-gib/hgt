import GaloisForLFunctions.HTGeometry.CofinalCapitalDensitySelection

/-!
# Fixed-source formation capital

Sections 2, 3 and 4 of the formation-resource card `ULF-FRM-2`.

* `(FCAP.5)`–`(FCAP.8)`, `(FCAP.10)`, `(FCAP.13b)`  the Hellinger and Rényi fixed-source capital
  theorems, from the Rényi data-processing and tensor laws of
  `HTGeometry/CofinalCapitalDensitySelection`;
* `(FCAP.14)`, `(FCAP.15)`  **Theorem 3.1**, the arbitrary-depth classification: a fixed source
  finances unbounded independent target depth exactly when the target is neutral or the source
  marks are mutually singular, with both formation kernels constructed explicitly;
* `(FCAP.16)`, `(FCAP.17)`  **Theorem 3.2**, approximate fixed-source properness, from the
  Hellinger triangle inequality realized as the `ℓ²` norm of the square-root chart;
* `(FCAP.20)`–`(FCAP.22)`  §4, the explicit likelihood-ratio counterexample showing that one
  scalar is not a complete conversion criterion.

Everything is unconditional and finite.
-/

open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {S X : Type*} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X]

/-- `(FCAP.5)`  Hellinger affinity of two finite packets. -/
def finitePacketAffinity (u v : X → ℝ) : ℝ := renyiOverlap (1 / 2) u v

theorem finitePacketAffinity_eq_sum (u v : X → ℝ) :
    finitePacketAffinity u v = ∑ x, u x ^ (1/2 : ℝ) * v x ^ (1/2 : ℝ) := by
  rw [finitePacketAffinity, renyiOverlap]
  norm_num

/-- **Theorem 2.1, `(FCAP.7)`.**  A fixed source can only form independent depth by paying
multiplicative affinity. -/
theorem ExactFormation.finitePacketAffinity_le {E : FiniteExperiment S} {F : FiniteExperiment X}
    {d : ℕ} (A : ExactFormation E F d) :
    finitePacketAffinity E.law₀ E.law₁ ≤ finitePacketAffinity F.law₀ F.law₁ ^ d := by
  have hdp := renyiOverlap_markovDataProcessing (α := (1/2 : ℝ)) (by norm_num) (by norm_num)
    A.kernel E.nonneg₀ E.nonneg₁
  rw [A.forms_zero, A.forms_one] at hdp
  have hpow : renyiOverlap (1/2 : ℝ) (F.tensorPow d).law₀ (F.tensorPow d).law₁
      = renyiOverlap (1/2 : ℝ) F.law₀ F.law₁ ^ d :=
    renyiOverlap_tensorPower _ d F.nonneg₀ F.nonneg₁
  rw [hpow] at hdp
  exact hdp

/-- **Theorem 2.3, `(FCAP.13b)`.**  The whole Rényi capital spectrum obeys the same law. -/
theorem ExactFormation.renyiOverlap_le {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {E : FiniteExperiment S} {F : FiniteExperiment X} {d : ℕ} (A : ExactFormation E F d) :
    renyiOverlap α E.law₀ E.law₁ ≤ renyiOverlap α F.law₀ F.law₁ ^ d := by
  have hdp := renyiOverlap_markovDataProcessing h0 h1 A.kernel E.nonneg₀ E.nonneg₁
  rw [A.forms_zero, A.forms_one] at hdp
  have hpow : renyiOverlap α (F.tensorPow d).law₀ (F.tensorPow d).law₁
      = renyiOverlap α F.law₀ F.law₁ ^ d :=
    renyiOverlap_tensorPower _ d F.nonneg₀ F.nonneg₁
  rw [hpow] at hdp
  exact hdp

/-- **`(FCAP.8)`.**  The exact depth bound. -/
theorem ExactFormation.depth_le {E : FiniteExperiment S} {F : FiniteExperiment X} {d : ℕ}
    (A : ExactFormation E F d)
    (ha0 : 0 < finitePacketAffinity F.law₀ F.law₁) (ha1 : finitePacketAffinity F.law₀ F.law₁ < 1)
    (hc0 : 0 < finitePacketAffinity E.law₀ E.law₁) :
    (d : ℝ) ≤ Real.log (finitePacketAffinity E.law₀ E.law₁)
      / Real.log (finitePacketAffinity F.law₀ F.law₁) := by
  have hle := A.finitePacketAffinity_le
  have hloga : Real.log (finitePacketAffinity F.law₀ F.law₁) < 0 := Real.log_neg ha0 ha1
  have hlog : Real.log (finitePacketAffinity E.law₀ E.law₁)
      ≤ (d : ℝ) * Real.log (finitePacketAffinity F.law₀ F.law₁) := by
    calc Real.log (finitePacketAffinity E.law₀ E.law₁)
        ≤ Real.log (finitePacketAffinity F.law₀ F.law₁ ^ d) := Real.log_le_log hc0 hle
      _ = (d : ℝ) * Real.log (finitePacketAffinity F.law₀ F.law₁) := by
          rw [Real.log_pow]
  rw [le_div_iff_of_neg hloga]
  exact hlog

theorem finitePacketAffinity_eq_sum_sqrt {u v : X → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    finitePacketAffinity u v = ∑ x, Real.sqrt (u x) * Real.sqrt (v x) := by
  rw [finitePacketAffinity_eq_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

/-! ## Arbitrary-depth classification -/

/-- The constant formation kernel: ignore the source and prepare a fixed packet. -/
def constantKernel (Y : Type*) [Fintype Y] (q : Y → ℝ) (hq : ∀ y, 0 ≤ q y)
    (hq1 : ∑ y, q y = 1) : FiniteMarkovKernel S Y where
  weight y _ := q y
  nonneg y _ := hq y
  column_sum _ := hq1

theorem constantKernel_applyReal {Y : Type*} [Fintype Y] {q : Y → ℝ} (hq : ∀ y, 0 ≤ q y)
    (hq1 : ∑ y, q y = 1) {r : S → ℝ} (hr : ∑ x, r x = 1) :
    (constantKernel (S := S) Y q hq hq1).toFinitePositiveKernel.applyReal r = q := by
  funext y
  rw [FinitePositiveKernel.applyReal]
  change ∑ x, q y * r x = q y
  rw [← Finset.mul_sum, hr, mul_one]

/-- **Theorem 3.1, `(FCAP.14)` direction.**  A neutral target is formable at every depth. -/
def neutralFormation (E : FiniteExperiment S) (F : FiniteExperiment X) (d : ℕ)
    (h : F.law₀ = F.law₁) : ExactFormation E F d where
  kernel := constantKernel _ (tensorPower d F.law₀) (tensorPower_nonneg d F.nonneg₀)
    (by rw [sum_tensorPower, F.sum₀, one_pow])
  forms_zero :=
    constantKernel_applyReal _ _ E.sum₀
  forms_one := by
    have := constantKernel_applyReal (S := S) (tensorPower_nonneg d F.nonneg₀)
      (by rw [sum_tensorPower, F.sum₀, one_pow] : ∑ y, tensorPower d F.law₀ y = 1) E.sum₁
    rw [this]
    show tensorPower d F.law₀ = tensorPower d F.law₁
    rw [h]

/-- The separating formation kernel used when the source marks have disjoint supports. -/
def separatingKernel (Y : Type*) [Fintype Y] (r₁ : S → ℝ) (q₀ q₁ : Y → ℝ)
    (hq₀ : ∀ y, 0 ≤ q₀ y) (hq₁ : ∀ y, 0 ≤ q₁ y)
    (hq₀1 : ∑ y, q₀ y = 1) (hq₁1 : ∑ y, q₁ y = 1) : FiniteMarkovKernel S Y where
  weight y x := if r₁ x = 0 then q₀ y else q₁ y
  nonneg y x := by
    by_cases h : r₁ x = 0
    · rw [if_pos h]; exact hq₀ y
    · rw [if_neg h]; exact hq₁ y
  column_sum x := by
    by_cases h : r₁ x = 0
    · simp only [if_pos h]; exact hq₀1
    · simp only [if_neg h]; exact hq₁1

/-- **Theorem 3.1, `(FCAP.15)` direction.**  A singular source forms every depth. -/
def singularFormation (E : FiniteExperiment S) (F : FiniteExperiment X) (d : ℕ)
    (h : ∀ x, E.law₀ x = 0 ∨ E.law₁ x = 0) : ExactFormation E F d where
  kernel := separatingKernel _ E.law₁ (tensorPower d F.law₀) (tensorPower d F.law₁)
    (tensorPower_nonneg d F.nonneg₀) (tensorPower_nonneg d F.nonneg₁)
    (by rw [sum_tensorPower, F.sum₀, one_pow]) (by rw [sum_tensorPower, F.sum₁, one_pow])
  forms_zero := by
    funext y
    rw [FinitePositiveKernel.applyReal]
    have hterm : ∀ x : S,
        (if E.law₁ x = 0 then tensorPower d F.law₀ y else tensorPower d F.law₁ y) * E.law₀ x
          = tensorPower d F.law₀ y * E.law₀ x := by
      intro x
      by_cases hx : E.law₀ x = 0
      · rw [hx, mul_zero, mul_zero]
      · rcases h x with h0 | h1
        · exact absurd h0 hx
        · rw [if_pos h1]
    change ∑ x, (if E.law₁ x = 0 then tensorPower d F.law₀ y else tensorPower d F.law₁ y)
      * E.law₀ x = _
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum, E.sum₀, mul_one]
    rfl
  forms_one := by
    funext y
    rw [FinitePositiveKernel.applyReal]
    have hterm : ∀ x : S,
        (if E.law₁ x = 0 then tensorPower d F.law₀ y else tensorPower d F.law₁ y) * E.law₁ x
          = tensorPower d F.law₁ y * E.law₁ x := by
      intro x
      by_cases hx : E.law₁ x = 0
      · rw [hx, mul_zero, mul_zero]
      · rw [if_neg hx]
    change ∑ x, (if E.law₁ x = 0 then tensorPower d F.law₀ y else tensorPower d F.law₁ y)
      * E.law₁ x = _
    rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum, E.sum₁, mul_one]
    rfl

/-- **Theorem 3.1.**  A fixed source finances unbounded independent target depth exactly when the
target is neutral or the source marks are mutually singular. -/
theorem forall_depth_formation_iff (E : FiniteExperiment S) (F : FiniteExperiment X) :
    (∀ d : ℕ, Nonempty (ExactFormation E F d))
      ↔ (F.law₀ = F.law₁ ∨ ∀ x, E.law₀ x = 0 ∨ E.law₁ x = 0) := by
  constructor
  · intro h
    by_cases hneutral : finitePacketAffinity F.law₀ F.law₁ = 1
    · left
      exact (renyiOverlap_eq_one_iff (by norm_num) (by norm_num) F.nonneg₀ F.nonneg₁
        F.sum₀ F.sum₁).mp hneutral
    · right
      have ha1 : finitePacketAffinity F.law₀ F.law₁ < 1 :=
        lt_of_le_of_ne (renyiOverlap_le_one (by norm_num) (by norm_num) F.nonneg₀ F.nonneg₁
          F.sum₀ F.sum₁) hneutral
      have ha0 : 0 ≤ finitePacketAffinity F.law₀ F.law₁ := renyiOverlap_nonneg F.nonneg₀ F.nonneg₁
      have hc0 : 0 ≤ finitePacketAffinity E.law₀ E.law₁ := renyiOverlap_nonneg E.nonneg₀ E.nonneg₁
      have hlim : Filter.Tendsto (fun d : ℕ => finitePacketAffinity F.law₀ F.law₁ ^ d)
          Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
      have hle : ∀ d : ℕ, finitePacketAffinity E.law₀ E.law₁
          ≤ finitePacketAffinity F.law₀ F.law₁ ^ d := fun d => (h d).some.finitePacketAffinity_le
      have hczero : finitePacketAffinity E.law₀ E.law₁ = 0 :=
        le_antisymm (ge_of_tendsto' hlim hle) hc0
      rw [finitePacketAffinity_eq_sum_sqrt E.nonneg₀ E.nonneg₁] at hczero
      intro x
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hczero x
        (Finset.mem_univ x)
      rcases mul_eq_zero.mp hterm with h0 | h1
      · left
        exact (Real.sqrt_eq_zero (E.nonneg₀ x)).mp h0
      · right
        exact (Real.sqrt_eq_zero (E.nonneg₁ x)).mp h1
  · rintro (h | h) d
    · exact ⟨neutralFormation E F d h⟩
    · exact ⟨singularFormation E F d h⟩

/-! ## Approximate fixed-source properness -/

/-- `(FCAP.5)`  Hellinger distance of two finite packets. -/
def finitePacketHellinger (u v : X → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 fun x => Real.sqrt (u x) : EuclideanSpace ℝ X)
    - (WithLp.toLp 2 fun x => Real.sqrt (v x))‖

theorem finitePacketHellinger_nonneg (u v : X → ℝ) : 0 ≤ finitePacketHellinger u v := norm_nonneg _

theorem finitePacketHellinger_symm (u v : X → ℝ) : finitePacketHellinger u v = finitePacketHellinger v u :=
  norm_sub_rev _ _

theorem finitePacketHellinger_triangle (u v w : X → ℝ) :
    finitePacketHellinger u w ≤ finitePacketHellinger u v + finitePacketHellinger v w := by
  have h : (WithLp.toLp 2 fun x => Real.sqrt (u x) : EuclideanSpace ℝ X)
      - (WithLp.toLp 2 fun x => Real.sqrt (w x))
      = ((WithLp.toLp 2 fun x => Real.sqrt (u x) : EuclideanSpace ℝ X)
          - (WithLp.toLp 2 fun x => Real.sqrt (v x)))
        + ((WithLp.toLp 2 fun x => Real.sqrt (v x) : EuclideanSpace ℝ X)
          - (WithLp.toLp 2 fun x => Real.sqrt (w x))) := by abel
  rw [finitePacketHellinger, h]
  exact norm_add_le _ _

theorem finitePacketHellinger_sq {u v : X → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hu1 : ∑ x, u x = 1) (hv1 : ∑ x, v x = 1) :
    finitePacketHellinger u v ^ 2 = 2 - 2 * finitePacketAffinity u v := by
  rw [finitePacketHellinger, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hterm : ∀ x : X,
      ‖((WithLp.toLp 2 fun y => Real.sqrt (u y) : EuclideanSpace ℝ X)
        - (WithLp.toLp 2 fun y => Real.sqrt (v y))).ofLp x‖ ^ 2
        = u x - 2 * (Real.sqrt (u x) * Real.sqrt (v x)) + v x := by
    intro x
    have hcoord : ((WithLp.toLp 2 fun y => Real.sqrt (u y) : EuclideanSpace ℝ X)
        - (WithLp.toLp 2 fun y => Real.sqrt (v y))).ofLp x
        = Real.sqrt (u x) - Real.sqrt (v x) := rfl
    rw [hcoord, Real.norm_eq_abs, sq_abs, sub_sq, Real.sq_sqrt (hu x), Real.sq_sqrt (hv x)]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [finitePacketAffinity_eq_sum_sqrt hu hv]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hu1, hv1, ← Finset.mul_sum]
  ring

theorem finitePacketHellinger_eq_sqrt {u v : X → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hu1 : ∑ x, u x = 1) (hv1 : ∑ x, v x = 1) :
    finitePacketHellinger u v = Real.sqrt (2 - 2 * finitePacketAffinity u v) := by
  rw [← finitePacketHellinger_sq hu hv hu1 hv1, Real.sqrt_sq (finitePacketHellinger_nonneg u v)]

/-- Hellinger distance is monotone under a Markov kernel. -/
theorem finitePacketHellinger_markovDataProcessing (K : FiniteMarkovKernel S X)
    {u v : S → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hu1 : ∑ x, u x = 1) (hv1 : ∑ x, v x = 1) :
    finitePacketHellinger (K.toFinitePositiveKernel.applyReal u)
        (K.toFinitePositiveKernel.applyReal v) ≤ finitePacketHellinger u v := by
  have hU : ∀ y, 0 ≤ K.toFinitePositiveKernel.applyReal u y := fun y =>
    FinitePositiveKernel.applyReal_nonneg _ hu y
  have hV : ∀ y, 0 ≤ K.toFinitePositiveKernel.applyReal v y := fun y =>
    FinitePositiveKernel.applyReal_nonneg _ hv y
  have hU1 : ∑ y, K.toFinitePositiveKernel.applyReal u y = 1 := by
    rw [FiniteMarkovKernel.sum_applyReal K]; exact hu1
  have hV1 : ∑ y, K.toFinitePositiveKernel.applyReal v y = 1 := by
    rw [FiniteMarkovKernel.sum_applyReal K]; exact hv1
  rw [finitePacketHellinger_eq_sqrt hU hV hU1 hV1, finitePacketHellinger_eq_sqrt hu hv hu1 hv1]
  refine Real.sqrt_le_sqrt ?_
  have := renyiOverlap_markovDataProcessing (α := (1/2 : ℝ)) (by norm_num) (by norm_num) K hu hv
  unfold finitePacketAffinity
  linarith

/-- **Theorem 3.2, `(FCAP.17)`.**  No fixed overlapping source admits asymptotically exact
nonneutral target formation at unbounded depth. -/
theorem approximate_properness (E : FiniteExperiment S) (F : FiniteExperiment X) (d : ℕ)
    (K : FiniteMarkovKernel S (Fin d → X)) :
    Real.sqrt (2 - 2 * finitePacketAffinity F.law₀ F.law₁ ^ d)
        - Real.sqrt (2 - 2 * finitePacketAffinity E.law₀ E.law₁)
      ≤ finitePacketHellinger (K.toFinitePositiveKernel.applyReal E.law₀) (F.tensorPow d).law₀
        + finitePacketHellinger (K.toFinitePositiveKernel.applyReal E.law₁) (F.tensorPow d).law₁ := by
  set R₀ := K.toFinitePositiveKernel.applyReal E.law₀ with hR₀
  set R₁ := K.toFinitePositiveKernel.applyReal E.law₁ with hR₁
  have htarget : finitePacketHellinger (F.tensorPow d).law₀ (F.tensorPow d).law₁
      = Real.sqrt (2 - 2 * finitePacketAffinity F.law₀ F.law₁ ^ d) := by
    have hpow : finitePacketAffinity (F.tensorPow d).law₀ (F.tensorPow d).law₁
        = finitePacketAffinity F.law₀ F.law₁ ^ d :=
      renyiOverlap_tensorPower _ d F.nonneg₀ F.nonneg₁
    rw [finitePacketHellinger_eq_sqrt (F.tensorPow d).nonneg₀ (F.tensorPow d).nonneg₁
      (F.tensorPow d).sum₀ (F.tensorPow d).sum₁, hpow]
  have hsource : finitePacketHellinger E.law₀ E.law₁
      = Real.sqrt (2 - 2 * finitePacketAffinity E.law₀ E.law₁) :=
    finitePacketHellinger_eq_sqrt E.nonneg₀ E.nonneg₁ E.sum₀ E.sum₁
  have hdp : finitePacketHellinger R₀ R₁ ≤ finitePacketHellinger E.law₀ E.law₁ :=
    finitePacketHellinger_markovDataProcessing K E.nonneg₀ E.nonneg₁ E.sum₀ E.sum₁
  have htri : finitePacketHellinger (F.tensorPow d).law₀ (F.tensorPow d).law₁
      ≤ finitePacketHellinger (F.tensorPow d).law₀ R₀ + finitePacketHellinger R₀ R₁
        + finitePacketHellinger R₁ (F.tensorPow d).law₁ := by
    calc finitePacketHellinger (F.tensorPow d).law₀ (F.tensorPow d).law₁
        ≤ finitePacketHellinger (F.tensorPow d).law₀ R₁ + finitePacketHellinger R₁ (F.tensorPow d).law₁ :=
          finitePacketHellinger_triangle _ _ _
      _ ≤ (finitePacketHellinger (F.tensorPow d).law₀ R₀ + finitePacketHellinger R₀ R₁)
            + finitePacketHellinger R₁ (F.tensorPow d).law₁ :=
          add_le_add (finitePacketHellinger_triangle _ _ _) le_rfl
  rw [finitePacketHellinger_symm R₁ (F.tensorPow d).law₁] at htri
  rw [← htarget, ← hsource]
  rw [finitePacketHellinger_symm R₀ (F.tensorPow d).law₀, finitePacketHellinger_symm R₁ (F.tensorPow d).law₁]
  linarith

/-! ## §4  One scalar is not a complete formation coordinate -/

namespace LikelihoodCounterexample

/-- `(FCAP.20)` first source mark. -/
def srcZero : Fin 2 → ℝ := ![9/10, 1/10]
/-- `(FCAP.20)` second source mark. -/
def srcOne : Fin 2 → ℝ := ![1/10, 9/10]
/-- `(FCAP.21)` first target mark. -/
def tgtZero : Fin 2 → ℝ := ![1/100, 99/100]
/-- `(FCAP.21)` second target mark. -/
def tgtOne : Fin 2 → ℝ := ![1/1000, 999/1000]

/-- **`(FCAP.20)`–`(FCAP.21)`.**  No common Markov kernel converts the source pair into the
target pair, even at depth one. -/
theorem no_common_kernel (K : FiniteMarkovKernel (Fin 2) (Fin 2))
    (h₀ : K.toFinitePositiveKernel.applyReal srcZero = tgtZero)
    (h₁ : K.toFinitePositiveKernel.applyReal srcOne = tgtOne) : False := by
  have e₀ := congrFun h₀ 0
  have e₁ := congrFun h₁ 0
  rw [FinitePositiveKernel.applyReal] at e₀ e₁
  simp only [Fin.sum_univ_two, srcZero, srcOne, tgtZero, tgtOne,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e₀ e₁
  have hw₁ := K.nonneg 0 1
  linarith

/-- **`(FCAP.22)`.**  Yet the Hellinger capital allows the conversion. -/
theorem affinity_lt : finitePacketAffinity srcZero srcOne < finitePacketAffinity tgtZero tgtOne := by
  have hs : ∀ x, (0:ℝ) ≤ srcZero x := fun x => by fin_cases x <;> norm_num [srcZero]
  have hs' : ∀ x, (0:ℝ) ≤ srcOne x := fun x => by fin_cases x <;> norm_num [srcOne]
  have ht : ∀ x, (0:ℝ) ≤ tgtZero x := fun x => by fin_cases x <;> norm_num [tgtZero]
  have ht' : ∀ x, (0:ℝ) ≤ tgtOne x := fun x => by fin_cases x <;> norm_num [tgtOne]
  rw [finitePacketAffinity_eq_sum_sqrt hs hs', finitePacketAffinity_eq_sum_sqrt ht ht']
  simp only [Fin.sum_univ_two, srcZero, srcOne, tgtZero, tgtOne,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hL : Real.sqrt (9/10) * Real.sqrt (1/10) + Real.sqrt (1/10) * Real.sqrt (9/10)
      = 3/5 := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)]
    rw [show (9:ℝ)/10 * (1/10) = (3/10)^2 by norm_num,
      show (1:ℝ)/10 * (9/10) = (3/10)^2 by norm_num]
    rw [Real.sqrt_sq (by norm_num)]
    norm_num
  rw [hL]
  have hR : (3:ℝ)/5 < Real.sqrt (99/100) * Real.sqrt (999/1000) := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [show (3:ℝ)/5 = Real.sqrt ((3/5)^2) from (Real.sqrt_sq (by norm_num)).symm]
    refine Real.sqrt_lt_sqrt (by norm_num) ?_
    norm_num
  have hpos : (0:ℝ) ≤ Real.sqrt (1/100) * Real.sqrt (1/1000) := by positivity
  linarith

end LikelihoodCounterexample

/-! ## §10  Selection corollary -/

/-- **`(FCAP.47)`, `(FCAP.48)`.**  A fixed *overlapping* source that finances unbounded independent
depth of an identifiable reflected family forces neutral displacement. -/
theorem selection_of_cofinal {I : Type*} [Zero I] (P : I → FiniteExperiment X)
    (hident : ∀ a : I, (P a).law₀ = (P a).law₁ → a = 0)
    (E : FiniteExperiment S) (hoverlap : ∃ x, E.law₀ x ≠ 0 ∧ E.law₁ x ≠ 0)
    (a : I) (h : ∀ d : ℕ, Nonempty (ExactFormation E (P a) d)) : a = 0 := by
  rcases (forall_depth_formation_iff E (P a)).mp h with hneutral | hsingular
  · exact hident a hneutral
  · obtain ⟨x, hx₀, hx₁⟩ := hoverlap
    rcases hsingular x with h0 | h1
    · exact absurd h0 hx₀
    · exact absurd h1 hx₁

end

end GaloisForLFunctions.HTGeometry
