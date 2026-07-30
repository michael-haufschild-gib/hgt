import GaloisForLFunctions.RHTower.AllPairQuantumReturnRigidityLaw
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Directional quantum-return geometry

For a joint energy assignment in an arbitrary real Hilbert space, the
balanced return of a labelled pair in a chosen time direction is the cosine
of the directional energy gap.  The complete family of all labelled-pair,
all-direction return records reconstructs the joint energy configuration up
to exactly two affine operations: one common translation and, possibly, one
global inversion.

Neither the label type nor the Hilbert space is assumed finite-dimensional.
The same return field therefore fixes the cardinal rank of the affine
energy-gap span even for infinite joint spectra and infinite-dimensional
parameter spaces.
-/

noncomputable section

namespace RHTower

open scoped RealInnerProductSpace

/-- Balanced return record of a labelled energy pair along one direction in
an arbitrary real Hilbert parameter space. -/
def directionalPairReturnRecord
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (i j : I) (time : V) : ℝ :=
  (1 + Real.cos (inner ℝ time (energy i - energy j))) / 2

/-- Equality of the complete directional return fields determines the square
of every directional labelled gap. -/
theorem directionalPairReturn_eq_all_imp_inner_sq_eq
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (h :
      ∀ i j time,
        directionalPairReturnRecord left i j time =
          directionalPairReturnRecord right i j time) :
    ∀ i j direction,
      inner ℝ direction (left i - left j) ^ 2 =
        inner ℝ direction (right i - right j) ^ 2 := by
  intro i j direction
  apply cos_mul_eq_cos_mul_all_imp_sq_eq
  intro t
  have ht := h i j (t • direction)
  simp only [directionalPairReturnRecord, real_inner_smul_left] at ht
  linarith

/-- A real Hilbert vector is determined up to sign by the squares of all its
directional projections. -/
theorem inner_sq_all_eq_imp_eq_or_neg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y : V}
    (h : ∀ u : V, inner ℝ u x ^ 2 = inner ℝ u y ^ 2) :
    y = x ∨ y = -x := by
  let A := inner ℝ x x
  let B := inner ℝ y y
  let C := inner ℝ x y
  have hA : A ^ 2 = C ^ 2 := by
    dsimp [A, C]
    exact h x
  have hB : C ^ 2 = B ^ 2 := by
    dsimp [B, C]
    simpa [real_inner_comm] using h y
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact real_inner_self_nonneg
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact real_inner_self_nonneg
  have hAB : A = B := by
    nlinarith
  have hfactor : (C - A) * (C + A) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hsame | hneg
  · left
    have hCA : C = A := sub_eq_zero.mp hsame
    have hinner : inner ℝ (y - x) (y - x) = 0 := by
      simp only [inner_sub_left, inner_sub_right]
      rw [show inner ℝ y x = C by
        dsimp [C]
        exact real_inner_comm x y]
      dsimp [A, B, C] at hAB hCA ⊢
      nlinarith
    have hzero : y - x = 0 :=
      (inner_self_eq_zero (𝕜 := ℝ)).mp hinner
    exact sub_eq_zero.mp hzero
  · right
    have hCA : C = -A := by linarith
    have hinner : inner ℝ (y + x) (y + x) = 0 := by
      simp only [inner_add_left, inner_add_right]
      rw [show inner ℝ y x = C by
        dsimp [C]
        exact real_inner_comm x y]
      dsimp [A, B, C] at hAB hCA ⊢
      nlinarith
    have hzero : y + x = 0 :=
      (inner_self_eq_zero (𝕜 := ℝ)).mp hinner
    exact eq_neg_of_add_eq_zero_left hzero

/-- Every labelled gap is individually determined up to sign by the complete
directional return field. -/
theorem directionalPairReturn_eq_all_imp_gap_eq_or_neg
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (h :
      ∀ i j time,
        directionalPairReturnRecord left i j time =
          directionalPairReturnRecord right i j time) :
    ∀ i j,
      right i - right j = left i - left j ∨
        right i - right j = -(left i - left j) := by
  intro i j
  exact inner_sq_all_eq_imp_eq_or_neg
    (directionalPairReturn_eq_all_imp_inner_sq_eq left right h i j)

/-- Pairwise sign ambiguities cannot be selected independently: compatibility
of every labelled triangle forces one common affine orientation. -/
theorem pairwise_gap_eq_or_neg_rigidity
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (hgap :
      ∀ i j,
        right i - right j = left i - left j ∨
          right i - right j = -(left i - left j)) :
    (∃ shift : V, ∀ i, right i = left i + shift) ∨
      (∃ shift : V, ∀ i, right i = -left i + shift) := by
  classical
  by_cases hconst : ∀ i j, left i = left j
  · let base : I := Classical.choice ‹Nonempty I›
    left
    refine ⟨right base - left base, ?_⟩
    intro i
    have hleft : left i = left base := hconst i base
    rcases hgap i base with hright | hright
    · have hright' : right i = right base := by
        apply sub_eq_zero.mp
        simpa [hleft] using hright
      rw [hright', hleft]
      abel
    · have hright' : right i = right base := by
        apply sub_eq_zero.mp
        simpa [hleft] using hright
      rw [hright', hleft]
      abel
  · push Not at hconst
    obtain ⟨base, anchor, hanchor⟩ := hconst
    have ha : left anchor - left base ≠ 0 :=
      sub_ne_zero.mpr hanchor.symm
    rcases hgap anchor base with hab | hab
    · left
      refine ⟨right base - left base, ?_⟩
      intro i
      rcases hgap i base with hi | hi
      · calc
          right i = (right i - right base) + right base := by abel
          _ = (left i - left base) + right base := by rw [hi]
          _ = left i + (right base - left base) := by abel
      · rcases hgap i anchor with hia | hia
        · refine ext_inner_left ℝ fun z => ?_
          have habz := congrArg (fun v => inner ℝ z v) hab
          have hiz := congrArg (fun v => inner ℝ z v) hi
          have hiaz := congrArg (fun v => inner ℝ z v) hia
          simp only [inner_sub_right, inner_neg_right,
            inner_add_right] at habz hiz hiaz ⊢
          linarith
        · exfalso
          apply ha
          refine ext_inner_left ℝ fun z => ?_
          have habz := congrArg (fun v => inner ℝ z v) hab
          have hiz := congrArg (fun v => inner ℝ z v) hi
          have hiaz := congrArg (fun v => inner ℝ z v) hia
          simp only [inner_sub_right, inner_neg_right,
            inner_zero_right] at habz hiz hiaz ⊢
          linarith
    · right
      refine ⟨right base + left base, ?_⟩
      intro i
      rcases hgap i base with hi | hi
      · rcases hgap i anchor with hia | hia
        · exfalso
          apply ha
          refine ext_inner_left ℝ fun z => ?_
          have habz := congrArg (fun v => inner ℝ z v) hab
          have hiz := congrArg (fun v => inner ℝ z v) hi
          have hiaz := congrArg (fun v => inner ℝ z v) hia
          simp only [inner_sub_right, inner_neg_right,
            inner_zero_right] at habz hiz hiaz ⊢
          linarith
        · refine ext_inner_left ℝ fun z => ?_
          have habz := congrArg (fun v => inner ℝ z v) hab
          have hiz := congrArg (fun v => inner ℝ z v) hi
          have hiaz := congrArg (fun v => inner ℝ z v) hia
          simp only [inner_sub_right, inner_neg_right,
            inner_add_right] at habz hiz hiaz ⊢
          linarith
      · calc
          right i = (right i - right base) + right base := by abel
          _ = -(left i - left base) + right base := by rw [hi]
          _ = -left i + (right base + left base) := by abel

/-- Complete directional pair returns reconstruct an arbitrary nonempty
joint-energy geometry up to translation and global inversion. -/
theorem directionalPairReturnRecord_rigidity
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (h :
      ∀ i j time,
        directionalPairReturnRecord left i j time =
          directionalPairReturnRecord right i j time) :
    (∃ shift : V, ∀ i, right i = left i + shift) ∨
      (∃ shift : V, ∀ i, right i = -left i + shift) := by
  exact pairwise_gap_eq_or_neg_rigidity left right
    (directionalPairReturn_eq_all_imp_gap_eq_or_neg left right h)

theorem directionalPairReturnRecord_translation_invariant
    {I V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (shift : V) :
    ∀ i j time,
      directionalPairReturnRecord
          (fun k => energy k + shift) i j time =
        directionalPairReturnRecord energy i j time := by
  intro i j time
  simp [directionalPairReturnRecord]

theorem directionalPairReturnRecord_inversion_invariant
    {I V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (shift : V) :
    ∀ i j time,
      directionalPairReturnRecord
          (fun k => -energy k + shift) i j time =
        directionalPairReturnRecord energy i j time := by
  intro i j time
  unfold directionalPairReturnRecord
  have hgap :
      (-energy i + shift) - (-energy j + shift) =
        -(energy i - energy j) := by
    abel
  rw [hgap, inner_neg_right, Real.cos_neg]

/-- **Directional quantum-return geometry law.**  Two arbitrary nonempty
joint-energy families have identical balanced-pair return data in every time
direction if and only if they differ by one common translation and,
possibly, one global inversion. -/
theorem directionalPairReturnRecord_complete_iff
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V) :
    (∀ i j time,
        directionalPairReturnRecord left i j time =
          directionalPairReturnRecord right i j time) ↔
      (∃ shift : V, ∀ i, right i = left i + shift) ∨
        (∃ shift : V, ∀ i, right i = -left i + shift) := by
  constructor
  · exact directionalPairReturnRecord_rigidity left right
  · rintro (⟨shift, hright⟩ | ⟨shift, hright⟩) i j time
    · have hrightFun : right = fun k => left k + shift :=
        funext hright
      rw [hrightFun]
      exact
        (directionalPairReturnRecord_translation_invariant
          left shift i j time).symm
    · have hrightFun : right = fun k => -left k + shift :=
        funext hright
      rw [hrightFun]
      exact
        (directionalPairReturnRecord_inversion_invariant
          left shift i j time).symm

/-- Real span of every labelled joint-energy gap. -/
def jointTemporalModule
    {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : I → V) : Submodule ℝ V :=
  Submodule.span ℝ
    (Set.range fun p : I × I => energy p.1 - energy p.2)

/-- Cardinal affine rank of a joint-energy geometry. -/
def jointTemporalDimension
    {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : I → V) : Cardinal :=
  Module.rank ℝ (jointTemporalModule energy)

theorem jointTemporalModule_translation_invariant
    {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : I → V) (shift : V) :
    jointTemporalModule (fun i => energy i + shift) =
      jointTemporalModule energy := by
  unfold jointTemporalModule
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    simp only [sub_eq_add_neg]
    abel
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    simp only [sub_eq_add_neg]
    abel

theorem jointTemporalModule_inversion_invariant
    {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (energy : I → V) (shift : V) :
    jointTemporalModule (fun i => -energy i + shift) =
      jointTemporalModule energy := by
  apply le_antisymm
  · rw [jointTemporalModule, Submodule.span_le]
    rintro x ⟨p, rfl⟩
    have hmem :
        energy p.1 - energy p.2 ∈ jointTemporalModule energy :=
      Submodule.subset_span ⟨p, rfl⟩
    have hgap :
        (-energy p.1 + shift) - (-energy p.2 + shift) =
          -(energy p.1 - energy p.2) := by
      abel
    change
      (-energy p.1 + shift) - (-energy p.2 + shift) ∈
        jointTemporalModule energy
    rw [hgap]
    exact (jointTemporalModule energy).neg_mem hmem
  · rw [jointTemporalModule, Submodule.span_le]
    rintro x ⟨p, rfl⟩
    have hmem :
        (-energy p.1 + shift) - (-energy p.2 + shift) ∈
          jointTemporalModule (fun i => -energy i + shift) :=
      Submodule.subset_span ⟨p, rfl⟩
    have hgap :
        energy p.1 - energy p.2 =
          -((-energy p.1 + shift) -
            (-energy p.2 + shift)) := by
      abel
    change
      energy p.1 - energy p.2 ∈
        jointTemporalModule (fun i => -energy i + shift)
    rw [hgap]
    exact
      (jointTemporalModule (fun i => -energy i + shift)).neg_mem hmem

/-- The complete directional return field fixes observer joint-temporal
dimension, including arbitrary infinite cardinal rank. -/
theorem directionalPairReturn_eq_all_imp_jointTemporalDimension_eq
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (h :
      ∀ i j time,
        directionalPairReturnRecord left i j time =
          directionalPairReturnRecord right i j time) :
    jointTemporalDimension left =
      jointTemporalDimension right := by
  rcases directionalPairReturnRecord_rigidity left right h with
    ⟨shift, hright⟩ | ⟨shift, hright⟩
  · have hrightFun : right = fun k => left k + shift :=
      funext hright
    rw [hrightFun]
    unfold jointTemporalDimension
    rw [jointTemporalModule_translation_invariant]
  · have hrightFun : right = fun k => -left k + shift :=
      funext hright
    rw [hrightFun]
    unfold jointTemporalDimension
    rw [jointTemporalModule_inversion_invariant]

/-! ## Instantaneous reconstruction by return curvature -/

/-- Projection of a joint-energy family onto one real time direction. -/
def directionalEnergyProjection
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (time : V) : I → ℝ :=
  fun i => inner ℝ time (energy i)

/-- The directional formula is the genuine two-level projective return of
the scalar spectrum obtained by projection onto that direction. -/
theorem directionalPairReturnRecord_eq_projectedPairReturnRecord
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (i j : I) (time : V) :
    directionalPairReturnRecord energy i j time =
      labelledPairReturnRecord
        (directionalEnergyProjection energy time) i j 1 := by
  rw [labelledPairReturnRecord_eq_cos]
  unfold directionalPairReturnRecord directionalEnergyProjection
  rw [inner_sub_right]
  congr 3
  ring

/-- Negative twice the short-time second derivative of a balanced pair
return in one direction. -/
def directionalPairReturnCurvature
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (i j : I) (direction : V) : ℝ :=
  -2 * deriv
    (deriv (fun s : ℝ =>
      directionalPairReturnRecord energy i j (s • direction))) 0

/-- Exact short-time law: pair-return curvature is one half of the negative
second derivative, hence the squared directional energy gap. -/
theorem directionalPairReturnRecord_secondDeriv_zero
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (i j : I) (direction : V) :
    deriv
      (deriv (fun s : ℝ =>
        directionalPairReturnRecord energy i j (s • direction))) 0 =
      -(inner ℝ direction (energy i - energy j) ^ 2) / 2 := by
  let a := inner ℝ direction (energy i - energy j)
  have hpath :
      (fun s : ℝ =>
        directionalPairReturnRecord energy i j (s • direction)) =
        fun s : ℝ => (1 + Real.cos (s * a)) / 2 := by
    funext s
    unfold directionalPairReturnRecord
    rw [real_inner_smul_left]
  rw [hpath]
  have hfirst :
      deriv (fun s : ℝ => (1 + Real.cos (s * a)) / 2) =
        fun s : ℝ => (-Real.sin (s * a) * a) / 2 := by
    funext s
    have hcos :=
      (Real.hasDerivAt_cos (s * a)).comp s
        ((hasDerivAt_id s).mul_const a)
    have hsum := (hasDerivAt_const s (1 : ℝ)).add hcos
    exact (((hsum.div_const 2).congr_deriv (by ring)).congr_of_eventuallyEq (by
      filter_upwards with x
      simp only [Pi.add_apply, Function.comp_apply, id_eq])).deriv
  rw [hfirst]
  have hsin :=
    (Real.hasDerivAt_sin (0 * a)).comp 0
      ((hasDerivAt_id 0).mul_const a)
  have hscaled := (hsin.neg.mul_const a).div_const 2
  convert hscaled.deriv using 1
  all_goals norm_num
  all_goals ring

theorem directionalPairReturnCurvature_eq_inner_sq
    {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (i j : I) (direction : V) :
    directionalPairReturnCurvature energy i j direction =
      inner ℝ direction (energy i - energy j) ^ 2 := by
  rw [directionalPairReturnCurvature,
    directionalPairReturnRecord_secondDeriv_zero]
  ring

/-- The infinitesimal return-curvature field already reconstructs the full
joint-energy geometry; observations at nonzero times are unnecessary for
identifiability. -/
theorem directionalPairReturnCurvature_rigidity
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (h :
      ∀ i j direction,
        directionalPairReturnCurvature left i j direction =
          directionalPairReturnCurvature right i j direction) :
    (∃ shift : V, ∀ i, right i = left i + shift) ∨
      (∃ shift : V, ∀ i, right i = -left i + shift) := by
  apply pairwise_gap_eq_or_neg_rigidity left right
  intro i j
  apply inner_sq_all_eq_imp_eq_or_neg
  intro direction
  rw [← directionalPairReturnCurvature_eq_inner_sq,
    ← directionalPairReturnCurvature_eq_inner_sq]
  exact h i j direction

theorem directionalPairReturnCurvature_translation_invariant
    {I V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (shift : V) :
    ∀ i j direction,
      directionalPairReturnCurvature
          (fun k => energy k + shift) i j direction =
        directionalPairReturnCurvature energy i j direction := by
  intro i j direction
  rw [directionalPairReturnCurvature_eq_inner_sq,
    directionalPairReturnCurvature_eq_inner_sq]
  congr 2
  abel

theorem directionalPairReturnCurvature_inversion_invariant
    {I V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (energy : I → V) (shift : V) :
    ∀ i j direction,
      directionalPairReturnCurvature
          (fun k => -energy k + shift) i j direction =
        directionalPairReturnCurvature energy i j direction := by
  intro i j direction
  rw [directionalPairReturnCurvature_eq_inner_sq,
    directionalPairReturnCurvature_eq_inner_sq]
  have hgap :
      (-energy i + shift) - (-energy j + shift) =
        -(energy i - energy j) := by
    abel
  rw [hgap, inner_neg_right]
  ring

/-- **Instantaneous quantum-return geometry law.**  Equality of only the
second-order return curvature at the origin, for every labelled pair and
direction, is equivalent to equality of the full joint-energy geometry up to
translation and global inversion. -/
theorem directionalPairReturnCurvature_complete_iff
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V) :
    (∀ i j direction,
        directionalPairReturnCurvature left i j direction =
          directionalPairReturnCurvature right i j direction) ↔
      (∃ shift : V, ∀ i, right i = left i + shift) ∨
        (∃ shift : V, ∀ i, right i = -left i + shift) := by
  constructor
  · exact directionalPairReturnCurvature_rigidity left right
  · rintro (⟨shift, hright⟩ | ⟨shift, hright⟩) i j direction
    · have hrightFun : right = fun k => left k + shift :=
        funext hright
      rw [hrightFun]
      exact
        (directionalPairReturnCurvature_translation_invariant
          left shift i j direction).symm
    · have hrightFun : right = fun k => -left k + shift :=
        funext hright
      rw [hrightFun]
      exact
        (directionalPairReturnCurvature_inversion_invariant
          left shift i j direction).symm

/-- **An instant determines every return.**  Equality of the complete
second-order return-curvature field at the origin is equivalent to equality
of every balanced-pair return probability at every parameter time. -/
theorem directionalPairReturnCurvature_eq_all_iff_returnRecord_eq_all
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V) :
    (∀ i j direction,
        directionalPairReturnCurvature left i j direction =
          directionalPairReturnCurvature right i j direction) ↔
      ∀ i j time,
        directionalPairReturnRecord left i j time =
          directionalPairReturnRecord right i j time := by
  rw [directionalPairReturnCurvature_complete_iff,
    directionalPairReturnRecord_complete_iff]

/-- Instantaneous return curvature fixes joint temporal dimension, including
arbitrary infinite cardinal rank. -/
theorem directionalPairReturnCurvature_eq_all_imp_jointTemporalDimension_eq
    {I V : Type*} [Nonempty I]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (left right : I → V)
    (h :
      ∀ i j direction,
        directionalPairReturnCurvature left i j direction =
          directionalPairReturnCurvature right i j direction) :
    jointTemporalDimension left =
      jointTemporalDimension right := by
  rcases directionalPairReturnCurvature_rigidity left right h with
    ⟨shift, hright⟩ | ⟨shift, hright⟩
  · have hrightFun : right = fun k => left k + shift :=
      funext hright
    rw [hrightFun]
    unfold jointTemporalDimension
    rw [jointTemporalModule_translation_invariant]
  · have hrightFun : right = fun k => -left k + shift :=
      funext hright
    rw [hrightFun]
    unfold jointTemporalDimension
    rw [jointTemporalModule_inversion_invariant]

end RHTower
