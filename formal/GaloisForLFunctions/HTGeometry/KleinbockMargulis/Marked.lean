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

/-- **Lemma 4.4.**  Around a point of `B` at which some `|ψ_s|` drops below `ρ` there is a ball
`B(x, r)` of radius at most `2r₀` on which one distinguished `ψ_{s₁}` stays at most `ρ`, while
every `ψ_s` still has supremum norm at least `ρ`. -/
theorem exists_marking_radius {ψ : ι → (Fin d → ℝ) → ℝ} {S : Set ι} {ρ r₀ : ℝ} {x₀ x : Fin d → ℝ}
    (hr₀ : 0 < r₀) (hx : x ∈ ball x₀ r₀)
    (hcont : ∀ s ∈ S, ContinuousOn (ψ s) (ball x₀ (3 * r₀)))
    (hsup : ∀ s ∈ S, SupGe (ψ s) (ball x₀ r₀) ρ)
    (hfin : {s | s ∈ S ∧ |ψ s x| < ρ}.Finite) (hne : ∃ s ∈ S, |ψ s x| < ρ) :
    ∃ (r : ℝ) (s₁ : ι), 0 < r ∧ r ≤ 2 * r₀ ∧ s₁ ∈ S ∧
      (∀ y ∈ ball x r, |ψ s₁ y| ≤ ρ) ∧ ∀ s ∈ S, SupGe (ψ s) (ball x r) ρ := by
  classical
  set H : Set ι := {s | s ∈ S ∧ |ψ s x| < ρ} with hH
  have hHne : H.Nonempty := by obtain ⟨s, hs, hs'⟩ := hne; exact ⟨s, hs, hs'⟩
  have hx3 : x ∈ ball x₀ (3 * r₀) := ball_subset_ball (by linarith) hx
  have hradne : ∀ s ∈ H, (goodRadii (ψ s) ρ r₀ x).Nonempty := fun s hs =>
    goodRadii_nonempty hr₀ hx3 (hcont s hs.1) hs.2
  obtain ⟨s₁, hs₁H, hs₁max⟩ :=
    Set.exists_max_image H (fun s => sSup (goodRadii (ψ s) ρ r₀ x)) hfin hHne
  refine ⟨sSup (goodRadii (ψ s₁) ρ r₀ x), s₁, sSup_goodRadii_pos (hradne s₁ hs₁H),
    sSup_goodRadii_le (hradne s₁ hs₁H), hs₁H.1,
    fun y hy => abs_le_of_mem_ball_sSup (hradne s₁ hs₁H) hy, ?_⟩
  intro s hs
  by_cases hsH : s ∈ H
  · exact (supGe_ball_sSup hr₀ hx (hcont s hs) (hsup s hs) (hradne s hsH)).mono
      (ball_subset_ball (hs₁max s hsH))
  · have : ρ ≤ |ψ s x| := by
      by_contra hcon
      exact hsH ⟨hs, not_le.mp hcon⟩
    exact supGe_of_mem (mem_ball_self (sSup_goodRadii_pos (hradne s₁ hs₁H))) this

/-! ### Besicovitch summation -/

/-- Assembling local estimates on the balls `B(x, r_x)`, `x ∈ E`, by Besicovitch's covering
theorem: the multiplicity of the extracted subcovering is bounded by `N_d`, and each ball is
contained in `B(x₀, 3r₀)`, whose volume is `3^d |B(x₀, r₀)|`. -/
theorem measure_inter_le_of_local {E : Set (Fin d → ℝ)} {x₀ : Fin d → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hE : E ⊆ ball x₀ r₀) (rad : E → ℝ) (hrad : ∀ j, 0 < rad j) (hrad' : ∀ j, rad j ≤ 2 * r₀)
    (A : Set (Fin d → ℝ)) (K : ℝ≥0∞)
    (hloc : ∀ j : E, volume (ball (j : Fin d → ℝ) (rad j) ∩ A)
      ≤ K * volume (ball (j : Fin d → ℝ) (rad j))) :
    volume (E ∩ A)
      ≤ (Besicovitch.multiplicity (Fin d → ℝ) : ℝ≥0∞) * ((3 : ℝ≥0∞) ^ d * K)
        * volume (ball x₀ r₀) := by
  classical
  set N := Besicovitch.multiplicity (Fin d → ℝ) with hN
  set q : Besicovitch.BallPackage E (Fin d → ℝ) :=
    { c := fun j => (j : Fin d → ℝ)
      r := rad
      rpos := hrad
      r_bound := 2 * r₀
      r_le := hrad' } with hq
  obtain ⟨u, hu_disj, hu_cover⟩ :=
    Besicovitch.exist_disjoint_covering_families (Besicovitch.one_lt_goodτ (Fin d → ℝ))
      (Besicovitch.isEmpty_satelliteConfig_multiplicity (Fin d → ℝ)) q
  -- each closed ball of the package lies in `B(x₀, 3r₀)`
  have hsubball : ∀ j : E, closedBall (j : Fin d → ℝ) (rad j) ⊆ ball x₀ (3 * r₀) := by
    intro j y hy
    have h1 : dist y (j : Fin d → ℝ) ≤ rad j := mem_closedBall.mp hy
    have h2 : dist (j : Fin d → ℝ) x₀ < r₀ := mem_ball.mp (hE j.2)
    have h3 : rad j ≤ 2 * r₀ := hrad' j
    rw [mem_ball]
    calc dist y x₀ ≤ dist y (j : Fin d → ℝ) + dist (j : Fin d → ℝ) x₀ := dist_triangle _ _ _
      _ < 2 * r₀ + r₀ := by linarith
      _ = 3 * r₀ := by ring
  -- for each colour, the disjoint balls have total volume at most `|B(x₀, 3r₀)|`
  have hcount : ∀ i : Fin N, (u i).Countable := by
    intro i
    refine (hu_disj i).countable_of_nonempty_interior fun j _ => ?_
    exact ⟨(j : Fin d → ℝ), isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall
      (mem_ball_self (hrad j))⟩
  have hsum : ∀ i : Fin N, ∑' j : (u i), volume (ball ((j : E) : Fin d → ℝ) (rad (j : E)))
      ≤ volume (ball x₀ (3 * r₀)) := by
    intro i
    have h1 : ∑' j : (u i), volume (closedBall ((j : E) : Fin d → ℝ) (rad (j : E)))
        = volume (⋃ j ∈ u i, closedBall ((j : E) : Fin d → ℝ) (rad (j : E))) :=
      (measure_biUnion (hcount i) (hu_disj i) (fun j _ => measurableSet_closedBall)).symm
    calc ∑' j : (u i), volume (ball ((j : E) : Fin d → ℝ) (rad (j : E)))
        ≤ ∑' j : (u i), volume (closedBall ((j : E) : Fin d → ℝ) (rad (j : E))) :=
          ENNReal.tsum_le_tsum fun j => measure_mono ball_subset_closedBall
      _ = volume (⋃ j ∈ u i, closedBall ((j : E) : Fin d → ℝ) (rad (j : E))) := h1
      _ ≤ volume (ball x₀ (3 * r₀)) :=
          measure_mono (iUnion₂_subset fun j _ => hsubball j)
  -- the covering estimate
  have hcov : E ∩ A ⊆ ⋃ i : Fin N, ⋃ j ∈ u i, (ball ((j : E) : Fin d → ℝ) (rad (j : E)) ∩ A) := by
    rintro y ⟨hyE, hyA⟩
    have : y ∈ range q.c := ⟨⟨y, hyE⟩, rfl⟩
    obtain ⟨-, ⟨i, rfl⟩, hy⟩ := hu_cover this
    simp only [mem_iUnion, exists_prop] at hy ⊢
    obtain ⟨j, hj, hyj⟩ := hy
    exact ⟨i, j, hj, hyj, hyA⟩
  calc volume (E ∩ A)
      ≤ ∑' i : Fin N, volume (⋃ j ∈ u i, (ball ((j : E) : Fin d → ℝ) (rad (j : E)) ∩ A)) :=
        le_trans (measure_mono hcov) (measure_iUnion_le _)
    _ ≤ ∑' _i : Fin N, K * volume (ball x₀ (3 * r₀)) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        calc volume (⋃ j ∈ u i, (ball ((j : E) : Fin d → ℝ) (rad (j : E)) ∩ A))
            ≤ ∑' j : (u i), volume (ball ((j : E) : Fin d → ℝ) (rad (j : E)) ∩ A) :=
              measure_biUnion_le _ (hcount i) _
          _ ≤ ∑' j : (u i), K * volume (ball ((j : E) : Fin d → ℝ) (rad (j : E))) :=
              ENNReal.tsum_le_tsum fun j => hloc (j : E)
          _ = K * ∑' j : (u i), volume (ball ((j : E) : Fin d → ℝ) (rad (j : E))) :=
              ENNReal.tsum_mul_left
          _ ≤ K * volume (ball x₀ (3 * r₀)) := mul_le_mul_left' (hsum i) K
    _ = (N : ℝ≥0∞) * (K * volume (ball x₀ (3 * r₀))) := by
        rw [tsum_fintype]
        simp [Finset.sum_const, Finset.card_univ]
    _ = (N : ℝ≥0∞) * ((3 : ℝ≥0∞) ^ d * K) * volume (ball x₀ r₀) := by
        have hv : volume (ball x₀ (3 * r₀)) = (3 : ℝ≥0∞) ^ d * volume (ball x₀ r₀) := by
          rw [Real.volume_pi_ball _ (by linarith : (0:ℝ) < 3 * r₀),
            Real.volume_pi_ball _ hr₀]
          rw [show (2 : ℝ) * (3 * r₀) = 3 * (2 * r₀) by ring, mul_pow,
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (3:ℝ) ^ Fintype.card (Fin d)),
            ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3)]
          simp
        rw [hv]
        ring

/-! ### Theorem 4.1 -/

/-- The Besicovitch covering constant of `ℝ^d` is at least `1`. -/
theorem one_le_besicovitch_multiplicity (d : ℕ) : 1 ≤ Besicovitch.multiplicity (Fin d → ℝ) := by
  have h := Besicovitch.card_le_multiplicity (E := (Fin d → ℝ)) (s := ({0} : Finset (Fin d → ℝ)))
    (by simp) (by simp)
  simpa using h

/-- **Theorem 4.1.**  The unmarked points of `B = B(x₀, r₀)` have measure at most
`k C (3^d N_d)^k (ε/ρ)^α |B|`. -/
theorem measure_not_marked_le {C α ρ : ℝ} (hC : 0 < C) (hα : 0 < α) (hρ : 0 < ρ) (k : ℕ) :
    ∀ (S : Set ι) (ψ : ι → (Fin d → ℝ) → ℝ) (x₀ : Fin d → ℝ) (r₀ : ℝ), 0 < r₀ →
      LengthLE S k →
      (∀ s ∈ S, ContinuousOn (ψ s) (ball x₀ (3 ^ k * r₀))) →
      (∀ s ∈ S, IsGood C α (ψ s) (ball x₀ (3 ^ k * r₀))) →
      (∀ s ∈ S, SupGe (ψ s) (ball x₀ r₀) ρ) →
      (∀ x ∈ ball x₀ (3 ^ k * r₀), {s | s ∈ S ∧ |ψ s x| < ρ}.Finite) →
      ∀ ε : ℝ, 0 < ε →
        volume {z ∈ ball x₀ r₀ | ¬ IsMarked ε ρ S ψ z}
          ≤ ENNReal.ofReal ((k : ℝ) * C
              * ((3 : ℝ) ^ d * (Besicovitch.multiplicity (Fin d → ℝ) : ℝ)) ^ k
              * (ε / ρ) ^ α) * volume (ball x₀ r₀) := by
  classical
  set N := Besicovitch.multiplicity (Fin d → ℝ) with hNdef
  set M : ℝ := (3 : ℝ) ^ d * (N : ℝ) with hMdef
  have hNpos : 1 ≤ (N : ℝ) := by exact_mod_cast one_le_besicovitch_multiplicity d
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    rw [hMdef]; nlinarith
  induction k with
  | zero =>
    intro S ψ x₀ r₀ hr₀ hlen _ _ _ _ ε hε
    have hS : S = ∅ := hlen.eq_empty
    have hempty : {z ∈ ball x₀ r₀ | ¬ IsMarked ε ρ S ψ z} = ∅ := by
      ext z
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro _
      exact isMarked_of_forall_le (by simp [hS])
    rw [hempty]
    simp
  | succ k ih =>
    intro S ψ x₀ r₀ hr₀ hlen hcont hgood hsup hfin ε hε
    have hMk : (1 : ℝ) ≤ M ^ k := one_le_pow₀ hM1
    have hεραnn : (0 : ℝ) ≤ (ε / ρ) ^ α := Real.rpow_nonneg (by positivity) _
    -- inclusions between the various balls
    have hb3 : ball x₀ (3 * r₀) ⊆ ball x₀ (3 ^ (k + 1) * r₀) := by
      refine ball_subset_ball ?_
      have : (3 : ℝ) ≤ 3 ^ (k + 1) := by
        calc (3:ℝ) = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have hb1 : ball x₀ r₀ ⊆ ball x₀ (3 ^ (k + 1) * r₀) := by
      refine ball_subset_ball ?_
      have : (1 : ℝ) ≤ 3 ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hcont3 : ∀ s ∈ S, ContinuousOn (ψ s) (ball x₀ (3 * r₀)) := fun s hs =>
      (hcont s hs).mono hb3
    -- the "bad" set
    set E : Set (Fin d → ℝ) := {x ∈ ball x₀ r₀ | ∃ s ∈ S, |ψ s x| < ρ} with hEdef
    set NM : Set (Fin d → ℝ) := {z | ¬ IsMarked ε ρ S ψ z} with hNMdef
    have hEB : E ⊆ ball x₀ r₀ := fun _ hx => hx.1
    have hstep1 : {z ∈ ball x₀ r₀ | ¬ IsMarked ε ρ S ψ z} ⊆ E ∩ NM := by
      rintro z ⟨hzB, hznm⟩
      refine ⟨⟨hzB, ?_⟩, hznm⟩
      by_contra hcon
      push_neg at hcon
      exact hznm (isMarked_of_forall_le hcon)
    -- choose a marking radius at every point of `E`
    have hEx : ∀ j : E, ∃ (r : ℝ) (s₁ : ι), 0 < r ∧ r ≤ 2 * r₀ ∧ s₁ ∈ S ∧
        (∀ y ∈ ball (j : Fin d → ℝ) r, |ψ s₁ y| ≤ ρ) ∧
        ∀ s ∈ S, SupGe (ψ s) (ball (j : Fin d → ℝ) r) ρ := by
      intro j
      exact exists_marking_radius hr₀ j.2.1 hcont3 hsup (hfin _ (hb1 j.2.1)) j.2.2
    choose rad sel hradpos hradle hselmem hselle hselsup using hEx
    -- the local estimate on each ball `B(x, r_x)`
    have hlocal : ∀ j : E, volume (ball (j : Fin d → ℝ) (rad j) ∩ NM)
        ≤ ENNReal.ofReal (((k : ℝ) + 1) * C * M ^ k * (ε / ρ) ^ α)
          * volume (ball (j : Fin d → ℝ) (rad j)) := by
      intro j
      set x : Fin d → ℝ := (j : Fin d → ℝ) with hx
      set r : ℝ := rad j with hr
      set s₁ : ι := sel j with hs₁
      have hxB : x ∈ ball x₀ r₀ := j.2.1
      have hxx₀ : dist x x₀ < r₀ := mem_ball.mp hxB
      have hrpos : 0 < r := hradpos j
      have hrle : r ≤ 2 * r₀ := hradle j
      have hincl1 : ball x r ⊆ ball x₀ (3 ^ (k + 1) * r₀) := by
        intro y hy
        have h1 : dist y x < r := mem_ball.mp hy
        have h2 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
        rw [mem_ball]
        calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
          _ < 2 * r₀ + r₀ := by linarith
          _ = 3 * r₀ := by ring
          _ ≤ 3 ^ (k + 1) * r₀ := by
              have : (3:ℝ) * 1 ≤ 3 * 3 ^ k := by linarith
              rw [pow_succ]
              nlinarith
      have hincl2 : ball x (3 ^ k * r) ⊆ ball x₀ (3 ^ (k + 1) * r₀) := by
        intro y hy
        have h1 : dist y x < 3 ^ k * r := mem_ball.mp hy
        have h2 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
        have h3 : (3:ℝ) ^ k * r ≤ 3 ^ k * (2 * r₀) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) k]
        rw [mem_ball]
        calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
          _ < 3 ^ k * (2 * r₀) + r₀ := by linarith
          _ ≤ 3 ^ (k + 1) * r₀ := by rw [pow_succ]; nlinarith
      -- Lemma 4.6 splits the unmarked points of `B(x, r)`
      have hsplit : ball x r ∩ NM
          ⊆ {z ∈ ball x r | ¬ IsMarked ε ρ (subPoset S {s₁}) ψ z}
            ∪ {z ∈ ball x r | |ψ s₁ z| < ε} := by
        rintro z ⟨hz, hznm⟩
        by_cases hm : IsMarked ε ρ (subPoset S {s₁}) ψ z
        · right
          refine ⟨hz, ?_⟩
          by_contra hlt
          push_neg at hlt
          exact hznm (IsMarked.of_subPoset (hselmem j) hlt (hselle j z hz) hm)
        · exact Or.inl ⟨hz, hm⟩
      -- the induction hypothesis on the shortened poset
      have hIH := ih (subPoset S {s₁}) ψ x r hrpos (hlen.subPoset_singleton (hselmem j))
        (fun s hs => (hcont s (subPoset_subset _ _ hs)).mono hincl2)
        (fun s hs => (hgood s (subPoset_subset _ _ hs)).mono_set hincl2)
        (fun s hs => hselsup j s (subPoset_subset _ _ hs))
        (fun y hy => (hfin y (hincl2 hy)).subset
          (fun s hs => ⟨subPoset_subset _ _ hs.1, hs.2⟩))
        ε hε
      -- the goodness estimate for the distinguished function
      have hgoodj : IsGood C α (ψ s₁) (ball x r) := (hgood s₁ (hselmem j)).mono_set hincl1
      have hmeas := hgoodj.measure_mul_ofReal_rpow_le hC.le hα x hrpos (subset_refl _) hε hρ.le
        (hselsup j s₁ (hselmem j))
      have hρα : (0:ℝ) < ρ ^ α := Real.rpow_pos_of_pos hρ _
      have hsecond : volume {z ∈ ball x r | |ψ s₁ z| < ε}
          ≤ ENNReal.ofReal (C * (ε / ρ) ^ α) * volume (ball x r) := by
        have hkey : volume {z ∈ ball x r | |ψ s₁ z| < ε} * ENNReal.ofReal (ρ ^ α)
            ≤ ENNReal.ofReal (C * (ε / ρ) ^ α) * volume (ball x r) * ENNReal.ofReal (ρ ^ α) := by
          refine hmeas.trans (le_of_eq ?_)
          rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ C * (ε / ρ) ^ α)]
          congr 2
          rw [Real.div_rpow hε.le hρ.le]
          field_simp
        exact (ENNReal.mul_le_mul_iff_left (by simpa using hρα) ENNReal.ofReal_ne_top).mp hkey
      calc volume (ball x r ∩ NM)
          ≤ volume ({z ∈ ball x r | ¬ IsMarked ε ρ (subPoset S {s₁}) ψ z}
              ∪ {z ∈ ball x r | |ψ s₁ z| < ε}) := measure_mono hsplit
        _ ≤ volume {z ∈ ball x r | ¬ IsMarked ε ρ (subPoset S {s₁}) ψ z}
              + volume {z ∈ ball x r | |ψ s₁ z| < ε} := measure_union_le _ _
        _ ≤ ENNReal.ofReal ((k : ℝ) * C * M ^ k * (ε / ρ) ^ α) * volume (ball x r)
              + ENNReal.ofReal (C * (ε / ρ) ^ α) * volume (ball x r) := add_le_add hIH hsecond
        _ = ENNReal.ofReal ((k : ℝ) * C * M ^ k * (ε / ρ) ^ α + C * (ε / ρ) ^ α)
              * volume (ball x r) := by
            rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal (((k : ℝ) + 1) * C * M ^ k * (ε / ρ) ^ α) * volume (ball x r) := by
            refine mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _
            have h1 : C * (ε / ρ) ^ α ≤ C * M ^ k * (ε / ρ) ^ α := by
              nlinarith [mul_nonneg (mul_nonneg hC.le hεραnn) (sub_nonneg.mpr hMk)]
            have h2 : ((k:ℝ) + 1) * C * M ^ k * (ε / ρ) ^ α
                = (k:ℝ) * C * M ^ k * (ε / ρ) ^ α + C * M ^ k * (ε / ρ) ^ α := by ring
            rw [h2]
            linarith
    -- assemble by Besicovitch
    have hfinal := measure_inter_le_of_local hr₀ hEB rad hradpos hradle NM
      (ENNReal.ofReal (((k : ℝ) + 1) * C * M ^ k * (ε / ρ) ^ α)) hlocal
    refine le_trans (measure_mono hstep1) (hfinal.trans (le_of_eq ?_))
    congr 1
    have h3 : (3 : ℝ≥0∞) ^ d = ENNReal.ofReal ((3:ℝ) ^ d) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    rw [← ENNReal.ofReal_natCast N, h3,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (3:ℝ) ^ d),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]
    congr 1
    push_cast
    rw [hMdef]
    ring

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
