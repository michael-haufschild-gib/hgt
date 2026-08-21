import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Good
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Order.Preorder.Chain

/-!
# Marked points for a poset of good functions (Kleinbock–Margulis, §4)

Let `S` be a partially ordered set of continuous functions `ψ_s` on a ball `B̃ = B(x₀, 3^k r₀)`,
each `(C, α)`-good on `B̃`, each with supremum norm at least `ρ` on `B = B(x₀, r₀)`, and such that
at each point only finitely many of them are smaller than `ρ`.  A point `z ∈ B` is
*`(ε, S, ψ)`-marked* if there is a chain `T ⊆ S` with

* `ε ≤ |ψ_s z| ≤ ρ` for `s ∈ T`, and
* `ρ ≤ |ψ_s z|` for every `s ∈ S(T)`,

where `S(T)` consists of the elements of `S \ T` comparable with every element of `T`.

The main result (`measure_not_marked_le`, Theorem 4.1) bounds the measure of the unmarked points
of `B` by `k C (3^d N_d)^k (ε/ρ)^α |B|`, where `N_d` is a Besicovitch covering constant.

The proof is an induction on the length `k` of `S`.  Around each point `x` of the "bad" set `E`
where some `|ψ_s x| < ρ` one produces a ball `B_x = B(x, r_x)` of radius at most `2r₀` on which one
distinguished `ψ_{s_x}` stays below `ρ` while *every* `ψ_s` still has supremum norm at least `ρ`
(`exists_marking_radius`).  Points of `B_x` that are marked for the shorter poset `S({s_x})` and at
which `|ψ_{s_x}|` is at least `ε` are marked for `S`; the induction hypothesis and the goodness of
`ψ_{s_x}` therefore bound the unmarked points inside `B_x`, and Besicovitch's covering theorem
assembles these local estimates.

## Main results

* `subPoset`, `LengthLE`, `IsMarked` — the combinatorial set-up of §4.
* `exists_marking_radius` — Lemmas 4.3 and 4.4.
* `IsMarked.of_subPoset` — Lemma 4.6.
* `measure_not_marked_le` — Theorem 4.1.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d : ℕ} {ι : Type*} [PartialOrder ι]

/-! ### The poset set-up -/

/-- `S(T)`: the elements of `S \ T` that are comparable with every element of `T`. -/
def subPoset (S T : Set ι) : Set ι := {s | s ∈ S ∧ s ∉ T ∧ ∀ t ∈ T, s ≤ t ∨ t ≤ s}

theorem subPoset_subset (S T : Set ι) : subPoset S T ⊆ S := fun _ hs => hs.1

@[simp] theorem subPoset_empty (S : Set ι) : subPoset S (∅ : Set ι) = S := by
  ext s; simp [subPoset]

/-- Adjoining `s₁` to a chain `T ⊆ S({s₁})` does not change the derived poset. -/
theorem subPoset_insert {S T : Set ι} {s₁ : ι} (hT : T ⊆ subPoset S {s₁}) :
    subPoset S (insert s₁ T) = subPoset (subPoset S {s₁}) T := by
  ext s
  constructor
  · rintro ⟨hsS, hsn, hcomp⟩
    refine ⟨⟨hsS, fun h => hsn (Or.inl h), fun t ht => ?_⟩, fun h => hsn (mem_insert_of_mem _ h),
      fun t ht => hcomp t (mem_insert_of_mem _ ht)⟩
    rw [mem_singleton_iff] at ht
    subst ht
    exact hcomp t (mem_insert _ _)
  · rintro ⟨⟨hsS, hs1, hcomp1⟩, hsn, hcomp⟩
    refine ⟨hsS, ?_, ?_⟩
    · rintro (rfl | h)
      · exact hs1 rfl
      · exact hsn h
    · rintro t ht
      rcases ht with rfl | ht
      · exact hcomp1 t rfl
      · exact hcomp t ht

/-- `l(S) ≤ k`: every finite chain contained in `S` has at most `k` elements. -/
def LengthLE (S : Set ι) (k : ℕ) : Prop :=
  ∀ c : Finset ι, ↑c ⊆ S → IsChain (· ≤ ·) (↑c : Set ι) → c.card ≤ k

theorem LengthLE.mono {S S' : Set ι} {k : ℕ} (h : LengthLE S k) (hS : S' ⊆ S) : LengthLE S' k :=
  fun c hc hchain => h c (hc.trans hS) hchain

/-- A poset of length `0` is empty. -/
theorem LengthLE.eq_empty {S : Set ι} (h : LengthLE S 0) : S = ∅ := by
  ext s
  simp only [mem_empty_iff_false, iff_false]
  intro hs
  have := h {s} (by simpa using hs) (by simp [IsChain])
  simp at this

/-- Inequality (4.1) for a one-element subset: removing a comparable element shortens the poset. -/
theorem LengthLE.subPoset_singleton {S : Set ι} {k : ℕ} (h : LengthLE S (k + 1)) {s₁ : ι}
    (hs₁ : s₁ ∈ S) : LengthLE (subPoset S {s₁}) k := by
  classical
  intro c hc hchain
  have hs₁c : s₁ ∉ c := by
    intro hmem
    exact (hc hmem).2.1 rfl
  have hsub : ↑(insert s₁ c) ⊆ S := by
    intro t ht
    rcases Finset.mem_insert.mp (by exact_mod_cast ht) with rfl | ht'
    · exact hs₁
    · exact (hc ht').1
  have hchain' : IsChain (· ≤ ·) (↑(insert s₁ c) : Set ι) := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact ((hc hb).2.2 a rfl).imp id id |>.symm.imp id id
    · exact (hc ha).2.2 b rfl
    · exact hchain ha hb hab
  have := h (insert s₁ c) hsub hchain'
  rw [Finset.card_insert_of_notMem hs₁c] at this
  omega

/-! ### Supremum norms and marked points -/

/-- `ρ ≤ sup_{z ∈ B} |f z|`, stated without a supremum. -/
def SupGe (f : (Fin d → ℝ) → ℝ) (B : Set (Fin d → ℝ)) (ρ : ℝ) : Prop :=
  ∀ c, c < ρ → ∃ z ∈ B, c < |f z|

theorem SupGe.mono {f : (Fin d → ℝ) → ℝ} {B B' : Set (Fin d → ℝ)} {ρ : ℝ} (h : SupGe f B ρ)
    (hBB : B ⊆ B') : SupGe f B' ρ := fun c hc => by
  obtain ⟨z, hz, hzc⟩ := h c hc
  exact ⟨z, hBB hz, hzc⟩

theorem supGe_of_mem {f : (Fin d → ℝ) → ℝ} {B : Set (Fin d → ℝ)} {ρ : ℝ} {z : Fin d → ℝ}
    (hz : z ∈ B) (hfz : ρ ≤ |f z|) : SupGe f B ρ := fun c hc => ⟨z, hz, lt_of_lt_of_le hc hfz⟩

/-- **`(ε, S, ψ)`-marked points.** -/
def IsMarked (ε ρ : ℝ) (S : Set ι) (ψ : ι → (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) : Prop :=
  ∃ T : Set ι, T ⊆ S ∧ IsChain (· ≤ ·) T ∧ (∀ s ∈ T, ε ≤ |ψ s z| ∧ |ψ s z| ≤ ρ) ∧
    ∀ s ∈ subPoset S T, ρ ≤ |ψ s z|

/-- **Lemma 4.2.**  A point at which every `|ψ_s|` is at least `ρ` is marked. -/
theorem isMarked_of_forall_le {ε ρ : ℝ} {S : Set ι} {ψ : ι → (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (h : ∀ s ∈ S, ρ ≤ |ψ s z|) : IsMarked ε ρ S ψ z :=
  ⟨∅, empty_subset _, Set.pairwise_empty _, by simp, by simpa using h⟩

/-- **Lemma 4.6.**  A point of `B_x` marked for the shortened poset `S({s₁})`, at which
`|ψ_{s₁}|` lies between `ε` and `ρ`, is marked for `S`. -/
theorem IsMarked.of_subPoset {ε ρ : ℝ} {S : Set ι} {ψ : ι → (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    {s₁ : ι} (hs₁ : s₁ ∈ S) (hlow : ε ≤ |ψ s₁ z|) (hhigh : |ψ s₁ z| ≤ ρ)
    (h : IsMarked ε ρ (subPoset S {s₁}) ψ z) : IsMarked ε ρ S ψ z := by
  obtain ⟨T, hTS, hchain, hM1, hM2⟩ := h
  refine ⟨insert s₁ T, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases hs with rfl | hs
    · exact hs₁
    · exact (hTS hs).1
  · intro a ha b hb hab
    simp only [mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact ((hTS hb).2.2 a rfl).symm
    · exact (hTS ha).2.2 b rfl
    · exact hchain ha hb hab
  · intro s hs
    rcases hs with rfl | hs
    · exact ⟨hlow, hhigh⟩
    · exact hM1 s hs
  · rw [subPoset_insert hTS]
    exact hM2

/-! ### The marking radius -/

/-- The radii `r ≤ 2r₀` for which `|ψ|` stays below `ρ` on `B(x, r)`.  Its supremum is the radius
`r_{s,x}` of §4. -/
def goodRadii (ψ : (Fin d → ℝ) → ℝ) (ρ r₀ : ℝ) (x : Fin d → ℝ) : Set ℝ :=
  {r | 0 < r ∧ r ≤ 2 * r₀ ∧ ∀ y ∈ ball x r, |ψ y| ≤ ρ}

theorem bddAbove_goodRadii (ψ : (Fin d → ℝ) → ℝ) (ρ r₀ : ℝ) (x : Fin d → ℝ) :
    BddAbove (goodRadii ψ ρ r₀ x) := ⟨2 * r₀, fun _ hr => hr.2.1⟩

/-- If `|ψ x| < ρ` and `ψ` is continuous near `x`, some radius is admissible. -/
theorem goodRadii_nonempty {ψ : (Fin d → ℝ) → ℝ} {ρ r₀ : ℝ} {x₀ x : Fin d → ℝ} (hr₀ : 0 < r₀)
    (hx : x ∈ ball x₀ (3 * r₀)) (hcont : ContinuousOn ψ (ball x₀ (3 * r₀))) (hψx : |ψ x| < ρ) :
    (goodRadii ψ ρ r₀ x).Nonempty := by
  have hW : ball x₀ (3 * r₀) ∈ 𝓝 x := isOpen_ball.mem_nhds hx
  have hca : ContinuousAt ψ x := hcont.continuousAt hW
  have h1 : {y | |ψ y| < ρ} ∈ 𝓝 x := by
    have := hca.abs
    exact this (Iio_mem_nhds hψx)
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp h1
  refine ⟨min η (2 * r₀), lt_min hη (by linarith), min_le_right _ _, fun y hy => ?_⟩
  exact (hsub (ball_subset_ball (min_le_left _ _) hy)).le

theorem sSup_goodRadii_pos {ψ : (Fin d → ℝ) → ℝ} {ρ r₀ : ℝ} {x : Fin d → ℝ}
    (hne : (goodRadii ψ ρ r₀ x).Nonempty) : 0 < sSup (goodRadii ψ ρ r₀ x) := by
  obtain ⟨a, ha⟩ := hne
  exact lt_of_lt_of_le ha.1 (le_csSup (bddAbove_goodRadii ψ ρ r₀ x) ha)

theorem sSup_goodRadii_le {ψ : (Fin d → ℝ) → ℝ} {ρ r₀ : ℝ} {x : Fin d → ℝ}
    (hne : (goodRadii ψ ρ r₀ x).Nonempty) : sSup (goodRadii ψ ρ r₀ x) ≤ 2 * r₀ :=
  csSup_le hne fun _ hr => hr.2.1

/-- On the ball of radius `r_{s,x}` the function `|ψ|` is at most `ρ`. -/
theorem abs_le_of_mem_ball_sSup {ψ : (Fin d → ℝ) → ℝ} {ρ r₀ : ℝ} {x : Fin d → ℝ}
    (hne : (goodRadii ψ ρ r₀ x).Nonempty) {y : Fin d → ℝ}
    (hy : y ∈ ball x (sSup (goodRadii ψ ρ r₀ x))) : |ψ y| ≤ ρ := by
  obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup hne (mem_ball.mp hy)
  exact ha.2.2 y (mem_ball.mpr hlt)

/-- **Lemma 4.3.**  The supremum norm of `ψ` on the ball of radius `r_{s,x}` is at least `ρ`. -/
theorem supGe_ball_sSup {ψ : (Fin d → ℝ) → ℝ} {ρ r₀ : ℝ} {x₀ x : Fin d → ℝ}
    (hr₀ : 0 < r₀) (hx : x ∈ ball x₀ r₀) (hcont : ContinuousOn ψ (ball x₀ (3 * r₀)))
    (hsupB : SupGe ψ (ball x₀ r₀) ρ) (hne : (goodRadii ψ ρ r₀ x).Nonempty) :
    SupGe ψ (ball x (sSup (goodRadii ψ ρ r₀ x))) ρ := by
  set R := sSup (goodRadii ψ ρ r₀ x) with hR
  have hRpos : 0 < R := sSup_goodRadii_pos hne
  have hRle : R ≤ 2 * r₀ := sSup_goodRadii_le hne
  rcases eq_or_lt_of_le hRle with hReq | hRlt
  · -- `R = 2r₀`: the ball contains `B(x₀, r₀)`
    refine hsupB.mono ?_
    intro y hy
    rw [mem_ball] at hy ⊢
    have hxx : dist x x₀ < r₀ := mem_ball.mp hx
    calc dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle _ _ _
      _ < r₀ + r₀ := by rw [dist_comm x₀ x]; linarith
      _ = 2 * r₀ := by ring
      _ = R := hReq.symm
  · -- `R < 2r₀`: otherwise `R` could be increased
    intro c hc
    by_contra hcon
    push_neg at hcon
    have hballc : ∀ z ∈ ball x R, |ψ z| ≤ c := by
      intro z hz
      exact not_lt.mp (fun h => absurd h (not_lt.mpr (hcon z hz)))
    set W := ball x₀ (3 * r₀) with hW
    have hcbW : closedBall x R ⊆ W := by
      intro y hy
      have h1 : dist y x ≤ R := mem_closedBall.mp hy
      have h2 : dist x x₀ < r₀ := mem_ball.mp hx
      rw [hW, mem_ball]
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ < 2 * r₀ + r₀ := by linarith
        _ = 3 * r₀ := by ring
    have hclosed : ∀ y ∈ closedBall x R, |ψ y| ≤ c := by
      intro y hy
      have hyW : y ∈ W := hcbW hy
      have hca : ContinuousAt ψ y := hcont.continuousAt (isOpen_ball.mem_nhds hyW)
      have hycl : y ∈ closure (ball x R) := by
        rwa [closure_ball x hRpos.ne']
      have : (𝓝[ball x R] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hycl
      exact le_of_tendsto (hca.abs.continuousWithinAt (s := ball x R))
        (eventually_mem_nhdsWithin.mono hballc)
    set U := W ∩ (fun y => |ψ y|) ⁻¹' Iio ρ with hU
    have hUopen : IsOpen U := hcont.abs.isOpen_inter_preimage isOpen_ball isOpen_Iio
    have hsubU : closedBall x R ⊆ U := by
      intro y hy
      exact ⟨hcbW hy, lt_of_le_of_lt (hclosed y hy) hc⟩
    obtain ⟨δ, hδ, hthick⟩ :=
      (isCompact_closedBall x R).exists_thickening_subset_open hUopen hsubU
    rw [thickening_closedBall hδ hRpos.le] at hthick
    have hmem : min (δ + R) (2 * r₀) ∈ goodRadii ψ ρ r₀ x := by
      refine ⟨lt_min (by linarith) (by linarith), min_le_right _ _, fun y hy => ?_⟩
      exact (hthick (ball_subset_ball (min_le_left _ _) hy)).2.le
    have hle := le_csSup (bddAbove_goodRadii ψ ρ r₀ x) hmem
    rw [← hR] at hle
    have : R < min (δ + R) (2 * r₀) := lt_min (by linarith) hRlt
    linarith

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
