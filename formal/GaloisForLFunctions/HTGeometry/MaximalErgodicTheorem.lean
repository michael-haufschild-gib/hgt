import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The maximal ergodic theorem

For a measure-preserving map `T` and an integrable `f`, the running maximum

`M_N = max (S_0 f, …, S_N f)`

of the Birkhoff sums has nonnegative integral of `f` over the set where it is positive.  The proof
is Garsia's: on that set the maximum is attained at a positive index, so `M_N ≤ f + M_N ∘ T` there,
while `M_N` vanishes off the set and `∫ M_N ∘ T = ∫ M_N`.

Applying this to `f - a` bounds the measure of the set where some Birkhoff average exceeds `a`.
-/

open MeasureTheory Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} {T : α → α} {f : α → ℝ}

/-- The running maximum `max (S_0 f, …, S_N f)` of the Birkhoff sums. -/
noncomputable def maxBirkhoff (T : α → α) (f : α → ℝ) : ℕ → α → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (maxBirkhoff T f n x) (birkhoffSum T f (n + 1) x)

@[simp]
theorem maxBirkhoff_zero (T : α → α) (f : α → ℝ) (x : α) : maxBirkhoff T f 0 x = 0 := rfl

theorem maxBirkhoff_succ (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    maxBirkhoff T f (n + 1) x =
      max (maxBirkhoff T f n x) (birkhoffSum T f (n + 1) x) := rfl

theorem maxBirkhoff_nonneg (T : α → α) (f : α → ℝ) (N : ℕ) (x : α) :
    0 ≤ maxBirkhoff T f N x := by
  induction N with
  | zero => simp
  | succ N ih => exact le_trans ih (le_max_left _ _)

theorem birkhoffSum_le_maxBirkhoff (T : α → α) (f : α → ℝ) {n N : ℕ} (h : n ≤ N) (x : α) :
    birkhoffSum T f n x ≤ maxBirkhoff T f N x := by
  induction N with
  | zero =>
    have : n = 0 := Nat.le_zero.mp h
    subst this
    simp
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · rw [maxBirkhoff_succ]
      exact le_trans (ih (by omega)) (le_max_left _ _)
    · subst h'
      rw [maxBirkhoff_succ]
      exact le_max_right _ _

theorem exists_eq_maxBirkhoff (T : α → α) (f : α → ℝ) (N : ℕ) (x : α) :
    ∃ n ≤ N, maxBirkhoff T f N x = birkhoffSum T f n x := by
  induction N with
  | zero => exact ⟨0, le_refl _, by simp⟩
  | succ N ih =>
    obtain ⟨n, hn, hEq⟩ := ih
    rcases le_total (birkhoffSum T f (N + 1) x) (maxBirkhoff T f N x) with h | h
    · exact ⟨n, hn.trans (Nat.le_succ N), by rw [maxBirkhoff_succ, max_eq_left h, hEq]⟩
    · exact ⟨N + 1, le_refl _, by rw [maxBirkhoff_succ, max_eq_right h]⟩

/-- **Where the running maximum is positive it is attained at a positive index**, hence dominated
by `f` plus the running maximum one step along the orbit. -/
theorem maxBirkhoff_le_of_pos (T : α → α) (f : α → ℝ) (N : ℕ) (x : α)
    (hx : 0 < maxBirkhoff T f N x) :
    maxBirkhoff T f N x ≤ f x + maxBirkhoff T f N (T x) := by
  obtain ⟨n, hn, hEq⟩ := exists_eq_maxBirkhoff T f N x
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hEq, birkhoffSum_zero] at hx
    exact lt_irrefl 0 hx
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hEq, birkhoffSum_succ']
  have hle := birkhoffSum_le_maxBirkhoff T f (by omega : m ≤ N) (T x)
  linarith

variable [MeasurableSpace α] {μ : Measure α}

/-! ### Measurability and integrability -/

theorem measurable_birkhoffSum (hTm : Measurable T) (hfm : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  have : birkhoffSum T f n = fun x => ∑ k ∈ Finset.range n, f (T^[k] x) := rfl
  rw [this]
  exact Finset.measurable_sum _ fun k _ => hfm.comp (hTm.iterate k)

theorem measurable_maxBirkhoff (hTm : Measurable T) (hfm : Measurable f) (N : ℕ) :
    Measurable (maxBirkhoff T f N) := by
  induction N with
  | zero =>
    have : maxBirkhoff T f 0 = fun _ : α => (0 : ℝ) := rfl
    rw [this]
    exact measurable_const
  | succ N ih =>
    have : maxBirkhoff T f (N + 1) =
        fun x => max (maxBirkhoff T f N x) (birkhoffSum T f (N + 1) x) := rfl
    rw [this]
    exact ih.max (measurable_birkhoffSum hTm hfm (N + 1))

theorem integrable_birkhoffSum (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffSum T f n) μ := by
  have hsum : birkhoffSum T f n = fun x => ∑ k ∈ Finset.range n, f (T^[k] x) := rfl
  rw [hsum]
  refine integrable_finsetSum _ fun k _ => ?_
  exact ((hT.iterate k).integrable_comp hf.aestronglyMeasurable).mpr hf

theorem integrable_maxBirkhoff (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (N : ℕ) :
    Integrable (maxBirkhoff T f N) μ := by
  induction N with
  | zero =>
    have : maxBirkhoff T f 0 = fun _ : α => (0 : ℝ) := rfl
    rw [this]
    exact integrable_zero α ℝ μ
  | succ N ih =>
    have heq : (maxBirkhoff T f N ⊔ birkhoffSum T f (N + 1) : α → ℝ)
        = maxBirkhoff T f (N + 1) := by
      funext x
      simp [maxBirkhoff_succ, Pi.sup_apply]
    rw [← heq]
    exact ih.sup (integrable_birkhoffSum hT hf (N + 1))

/-- Integrals are unchanged along a measure-preserving map. -/
theorem integral_comp_measurePreserving (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : AEStronglyMeasurable g μ) : ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
  have hmap : Measure.map T μ = μ := hT.map_eq
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hmap]
  have := integral_map (φ := T) hT.measurable.aemeasurable hg'
  rw [hmap] at this
  exact this.symm

/-! ### The maximal ergodic theorem -/

/-- **Garsia's maximal ergodic theorem.**  The integral of `f` over the set where some Birkhoff
sum of index at most `N` is positive is nonnegative. -/
theorem setIntegral_nonneg_of_maxBirkhoff_pos
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    (hf : Integrable f μ) (hfm : Measurable f) (N : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxBirkhoff T f N x}, f x ∂μ := by
  classical
  set M : α → ℝ := maxBirkhoff T f N with hMdef
  set A : Set α := {x | 0 < M x} with hAdef
  have hMmeas : Measurable M := measurable_maxBirkhoff hTm hfm N
  have hAmeas : MeasurableSet A := measurableSet_lt measurable_const hMmeas
  have hMint : Integrable M μ := integrable_maxBirkhoff hT hf N
  have hMTint : Integrable (fun x => M (T x)) μ :=
    (hT.integrable_comp hMint.aestronglyMeasurable).mpr hMint
  have hstep : ∀ x ∈ A, M x - M (T x) ≤ f x := by
    intro x hx
    have hpos : 0 < M x := hx
    have := maxBirkhoff_le_of_pos T f N x hpos
    simp only [hMdef] at this ⊢
    linarith
  have h1 : ∫ x in A, (M x - M (T x)) ∂μ ≤ ∫ x in A, f x ∂μ :=
    setIntegral_mono_on (hMint.sub hMTint).integrableOn hf.integrableOn hAmeas hstep
  have h2 : ∫ x in A, (M x - M (T x)) ∂μ
      = (∫ x in A, M x ∂μ) - ∫ x in A, M (T x) ∂μ :=
    integral_sub hMint.integrableOn hMTint.integrableOn
  have h3 : ∫ x in A, M x ∂μ = ∫ x, M x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    have hnpos : ¬ (0 < M x) := hx
    have h0 : 0 ≤ M x := maxBirkhoff_nonneg T f N x
    linarith
  have h4 : ∫ x in A, M (T x) ∂μ ≤ ∫ x, M (T x) ∂μ :=
    setIntegral_le_integral hMTint
      (Filter.Eventually.of_forall fun x => maxBirkhoff_nonneg T f N (T x))
  have h5 : ∫ x, M (T x) ∂μ = ∫ x, M x ∂μ :=
    integral_comp_measurePreserving hT hMint.aestronglyMeasurable
  linarith

end GaloisForLFunctions.HTGeometry
