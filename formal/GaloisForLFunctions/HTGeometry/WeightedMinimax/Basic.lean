import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Weighted minimax norms of real polynomials on a compact interval

For a continuous nonnegative weight `v` on `Icc a b` whose positivity set is infinite, the
weighted supremum `wsup v a b R = sup_{x ∈ [a,b]} v x * |R x|` is attained, is a genuine norm on
each space of polynomials of bounded degree, and therefore admits a minimizer over the monic
polynomials of a fixed degree. Nothing here is assumed: the weight data is a hypothesis of each
statement and is discharged for concrete weights by the consumers of this file.
-/

namespace GaloisForLFunctions.HTGeometry.WeightedMinimax

noncomputable section
open Set Polynomial

/-- Admissible weight data for the weighted minimax problem on `Icc a b`: a continuous weight,
nonnegative on the interval, whose positivity set inside the interval is infinite. -/
structure IsWeight (v : ℝ → ℝ) (a b : ℝ) : Prop where
  le : a ≤ b
  cont : Continuous v
  nonneg : ∀ x ∈ Icc a b, 0 ≤ v x
  infinite : {x ∈ Icc a b | v x ≠ 0}.Infinite

/-- The weighted supremum of `|R|` on `Icc a b`. -/
def wsup (v : ℝ → ℝ) (a b : ℝ) (R : Polynomial ℝ) : ℝ :=
  sSup ((fun x => v x * |R.eval x|) '' Icc a b)

variable {v : ℝ → ℝ} {a b : ℝ}

theorem continuousOn_weighted (hv : Continuous v) (R : Polynomial ℝ) :
    ContinuousOn (fun x => v x * |R.eval x|) (Icc a b) :=
  (hv.mul (Polynomial.continuous R).abs).continuousOn

theorem exists_isGreatest_weighted (hw : IsWeight v a b) (R : Polynomial ℝ) :
    ∃ x ∈ Icc a b, IsGreatest ((fun y => v y * |R.eval y|) '' Icc a b) (v x * |R.eval x|) := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hw.le)
    (continuousOn_weighted hw.cont R)
  refine ⟨x, hx, ⟨⟨x, hx, rfl⟩, ?_⟩⟩
  rintro y ⟨z, hz, rfl⟩
  exact hmax hz

/-- The weighted supremum is attained, and dominates every weighted value on the interval. -/
theorem wsup_spec (hw : IsWeight v a b) (R : Polynomial ℝ) :
    ∃ x ∈ Icc a b, wsup v a b R = v x * |R.eval x| ∧
      ∀ y ∈ Icc a b, v y * |R.eval y| ≤ wsup v a b R := by
  obtain ⟨x, hx, hg⟩ := exists_isGreatest_weighted hw R
  have h : wsup v a b R = v x * |R.eval x| := hg.csSup_eq
  refine ⟨x, hx, h, fun y hy => ?_⟩
  rw [h]
  exact hg.2 ⟨y, hy, rfl⟩

theorem le_wsup (hw : IsWeight v a b) (R : Polynomial ℝ) {x : ℝ} (hx : x ∈ Icc a b) :
    v x * |R.eval x| ≤ wsup v a b R := by
  obtain ⟨_, _, _, hle⟩ := wsup_spec hw R
  exact hle x hx

theorem wsup_attained (hw : IsWeight v a b) (R : Polynomial ℝ) :
    ∃ x ∈ Icc a b, wsup v a b R = v x * |R.eval x| := by
  obtain ⟨x, hx, he, _⟩ := wsup_spec hw R
  exact ⟨x, hx, he⟩

theorem wsup_nonneg (hw : IsWeight v a b) (R : Polynomial ℝ) : 0 ≤ wsup v a b R := by
  obtain ⟨x, hx, he⟩ := wsup_attained hw R
  rw [he]
  exact mul_nonneg (hw.nonneg x hx) (abs_nonneg _)

theorem wsup_zero (hw : IsWeight v a b) : wsup v a b 0 = 0 := by
  obtain ⟨x, _, he⟩ := wsup_attained hw 0
  rw [he]
  simp

theorem wsup_neg (R : Polynomial ℝ) :
    wsup v a b (-R) = wsup v a b R := by
  unfold wsup
  congr 1
  apply Set.image_congr
  intro x _
  simp

theorem wsup_add_le (hw : IsWeight v a b) (R S : Polynomial ℝ) :
    wsup v a b (R + S) ≤ wsup v a b R + wsup v a b S := by
  obtain ⟨x, hx, he⟩ := wsup_attained hw (R + S)
  rw [he]
  have h1 : v x * |(R + S).eval x| ≤ v x * |R.eval x| + v x * |S.eval x| := by
    rw [Polynomial.eval_add]
    have := abs_add_le (R.eval x) (S.eval x)
    nlinarith [hw.nonneg x hx, abs_nonneg (R.eval x), abs_nonneg (S.eval x)]
  exact h1.trans (add_le_add (le_wsup hw R hx) (le_wsup hw S hx))

theorem wsup_const_mul (hw : IsWeight v a b) (c : ℝ) (R : Polynomial ℝ) :
    wsup v a b (Polynomial.C c * R) = |c| * wsup v a b R := by
  obtain ⟨x, hx, he, hle⟩ := wsup_spec hw R
  have hg : IsGreatest ((fun y => v y * |(Polynomial.C c * R).eval y|) '' Icc a b)
      (|c| * (v x * |R.eval x|)) := by
    constructor
    · refine ⟨x, hx, ?_⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
      ring
    · rintro y ⟨z, hz, rfl⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
      have : v z * |R.eval z| ≤ v x * |R.eval x| := by rw [← he]; exact hle z hz
      nlinarith [abs_nonneg c]
  rw [show wsup v a b (Polynomial.C c * R) = |c| * (v x * |R.eval x|) from hg.csSup_eq, he]

theorem eq_zero_of_wsup_eq_zero (hw : IsWeight v a b) {R : Polynomial ℝ}
    (h : wsup v a b R = 0) : R = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine hw.infinite.mono ?_
  rintro x ⟨hx, hvx⟩
  have h1 : v x * |R.eval x| ≤ 0 := by rw [← h]; exact le_wsup hw R hx
  have h2 : (0:ℝ) ≤ v x * |R.eval x| := mul_nonneg (hw.nonneg x hx) (abs_nonneg _)
  have h3 : v x * |R.eval x| = 0 := le_antisymm h1 h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 hvx
  · exact abs_eq_zero.mp h4

theorem wsup_pos (hw : IsWeight v a b) {R : Polynomial ℝ} (hR : R ≠ 0) : 0 < wsup v a b R :=
  lt_of_le_of_ne (wsup_nonneg hw R) (fun h => hR (eq_zero_of_wsup_eq_zero hw h.symm))

/-! ### Monic polynomials of a fixed degree -/

/-- Polynomials of degree at most `n` whose `j`-th coefficient is one. -/
def coeffSet (n j : ℕ) : Set (Polynomial ℝ) := {p | p.natDegree ≤ n ∧ p.coeff j = 1}

/-- Monic polynomials of degree exactly `n`, described by a degree bound and one coefficient. -/
def monicDeg (n : ℕ) : Set (Polynomial ℝ) := coeffSet n n

theorem mem_monicDeg_iff {n : ℕ} {p : Polynomial ℝ} :
    p ∈ monicDeg n ↔ p.natDegree ≤ n ∧ p.coeff n = 1 := Iff.rfl

theorem mem_coeffSet_iff {n j : ℕ} {p : Polynomial ℝ} :
    p ∈ coeffSet n j ↔ p.natDegree ≤ n ∧ p.coeff j = 1 := Iff.rfl

theorem mem_degreeLT_of_natDegree_le {p : Polynomial ℝ} {n : ℕ} (h : p.natDegree ≤ n) :
    p ∈ Polynomial.degreeLT ℝ (n + 1) := by
  rw [Polynomial.mem_degreeLT]
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  exact_mod_cast Nat.lt_succ_of_le h

theorem natDegree_le_of_mem_degreeLT {p : Polynomial ℝ} {n : ℕ}
    (h : p ∈ Polynomial.degreeLT ℝ (n + 1)) : p.natDegree ≤ n := by
  rw [Polynomial.mem_degreeLT] at h
  rw [Polynomial.natDegree_le_iff_degree_le]
  by_cases hp : p = 0
  · simp [hp]
  · have := Polynomial.degree_eq_natDegree hp
    rw [this] at h ⊢
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h)

theorem degreeLT_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (Polynomial.degreeLT ℝ n) :=
  FiniteDimensional.of_injective (Polynomial.degreeLTEquiv ℝ n).toLinearMap
    (Polynomial.degreeLTEquiv ℝ n).injective

/-- The weighted supremum as an additive group seminorm on polynomials of degree `≤ n`. -/
def wsupSeminorm (hw : IsWeight v a b) (n : ℕ) :
    AddGroupSeminorm (Polynomial.degreeLT ℝ (n + 1)) where
  toFun p := wsup v a b p.val
  map_zero' := by simpa using wsup_zero hw
  add_le' p q := by simpa using wsup_add_le hw p.val q.val
  neg' p := by simpa using wsup_neg (v := v) (a := a) (b := b) p.val

/-- The weighted supremum is a genuine norm on polynomials of degree `≤ n`. -/
def wsupGroupNorm (hw : IsWeight v a b) (n : ℕ) :
    AddGroupNorm (Polynomial.degreeLT ℝ (n + 1)) where
  toAddGroupSeminorm := wsupSeminorm hw n
  eq_zero_of_map_eq_zero' p h := by
    have h1 : p.val = 0 := eq_zero_of_wsup_eq_zero hw h
    exact Submodule.coe_eq_zero.mp h1

@[implicit_reducible]
def wsupNormedGroup (hw : IsWeight v a b) (n : ℕ) :
    NormedAddCommGroup (Polynomial.degreeLT ℝ (n + 1)) :=
  (wsupGroupNorm hw n).toNormedAddCommGroup

@[implicit_reducible]
def wsupNormedSpace (hw : IsWeight v a b) (n : ℕ) :
    letI := wsupNormedGroup hw n
    NormedSpace ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
  letI := wsupNormedGroup hw n
  exact { (inferInstance : Module ℝ (Polynomial.degreeLT ℝ (n + 1))) with
    norm_smul_le := fun r p => by
      change wsup v a b ((r • p : Polynomial.degreeLT ℝ (n + 1)) : Polynomial ℝ) ≤
        ‖r‖ * wsup v a b (p : Polynomial ℝ)
      have hc : ((r • p : Polynomial.degreeLT ℝ (n + 1)) : Polynomial ℝ)
          = Polynomial.C r * (p : Polynomial ℝ) := by
        simp [Polynomial.smul_eq_C_mul]
      rw [hc, wsup_const_mul hw r]
      exact le_of_eq (by simp [Real.norm_eq_abs]) }

theorem wsup_proper (hw : IsWeight v a b) (n : ℕ) :
    letI := wsupNormedGroup hw n
    ProperSpace (Polynomial.degreeLT ℝ (n + 1)) := by
  letI := wsupNormedGroup hw n
  letI := wsupNormedSpace hw n
  letI := degreeLT_finiteDimensional (n + 1)
  exact FiniteDimensional.proper ℝ (Polynomial.degreeLT ℝ (n + 1))

/-- The `j`-th coefficient, as a linear functional on polynomials of degree `≤ n`. -/
def coeffFunctional (n j : ℕ) : Polynomial.degreeLT ℝ (n + 1) →ₗ[ℝ] ℝ where
  toFun p := (p : Polynomial ℝ).coeff j
  map_add' p q := by simp
  map_smul' r p := by simp

theorem coeffFunctional_continuous (hw : IsWeight v a b) (n j : ℕ) :
    letI := wsupNormedGroup hw n
    Continuous (coeffFunctional n j) := by
  letI := wsupNormedGroup hw n
  letI := wsupNormedSpace hw n
  letI := degreeLT_finiteDimensional (n + 1)
  exact (coeffFunctional n j).continuous_of_finiteDimensional

/-- A minimizer of the weighted supremum with a prescribed coefficient equal to one exists at
every degree, and its weighted supremum is strictly positive. -/
theorem exists_coeffSet_minimizer (hw : IsWeight v a b) (n j : ℕ) (hj : j ≤ n) :
    ∃ T ∈ coeffSet n j, 0 < wsup v a b T ∧
      ∀ p ∈ coeffSet n j, wsup v a b T ≤ wsup v a b p := by
  letI := wsupNormedGroup hw n
  letI := wsupNormedSpace hw n
  letI := wsup_proper hw n
  set M : Set (Polynomial.degreeLT ℝ (n + 1)) :=
    {p | (p : Polynomial ℝ).coeff j = 1} with hM
  have hMne : M.Nonempty := by
    refine ⟨⟨Polynomial.X ^ j, mem_degreeLT_of_natDegree_le (by simpa using hj)⟩, ?_⟩
    simp [hM]
  have hMcl : IsClosed M :=
    isClosed_eq (coeffFunctional_continuous hw n j) continuous_const
  obtain ⟨R, hR, hmin⟩ := hMcl.exists_infDist_eq_dist hMne 0
  have hRc : (R : Polynomial ℝ).coeff j = 1 := hR
  have hRne : (R : Polynomial ℝ) ≠ 0 := by
    intro h
    rw [h] at hRc
    simp at hRc
  refine ⟨(R : Polynomial ℝ), ⟨natDegree_le_of_mem_degreeLT R.2, hRc⟩,
    wsup_pos hw hRne, ?_⟩
  rintro p ⟨hp1, hp2⟩
  have hpM : (⟨p, mem_degreeLT_of_natDegree_le hp1⟩ : Polynomial.degreeLT ℝ (n + 1)) ∈ M := hp2
  have hb := Metric.infDist_le_dist_of_mem
    (x := (0 : Polynomial.degreeLT ℝ (n + 1))) hpM
  rw [hmin, dist_zero_left, dist_zero_left] at hb
  exact hb

/-- A monic minimizer of the weighted supremum exists at every degree, and its weighted
supremum is strictly positive. -/
theorem exists_monicDeg_minimizer (hw : IsWeight v a b) (n : ℕ) :
    ∃ T ∈ monicDeg n, 0 < wsup v a b T ∧
      ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p :=
  exists_coeffSet_minimizer hw n n le_rfl

end
end GaloisForLFunctions.HTGeometry.WeightedMinimax
