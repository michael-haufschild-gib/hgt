import GaloisForLFunctions.RHTower.Deninger.DeningerFinestComplete
import GaloisForLFunctions.RHTower.Deninger.DeningerFinestClosed
import GaloisForLFunctions.RHTower.Deninger.DeningerScaleFactorization
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# The test space of the `p`-adic integers

Infinitely many pairwise disjoint nonempty compact open sets give infinitely many linearly
independent indicators, so the locally constant test space of such a space is not finite
dimensional.  The `p`-adic integers carry such a family: the balls around the powers of `p` of
radius their own norm are clopen, compact, nonempty and pairwise disjoint, the last because all
triangles are isosceles in an ultrametric space.

The `p`-adic integers are compact, Hausdorff, totally disconnected and second countable, so the
whole theory applies to them: their test space is nuclear, sequentially complete, has all
subspaces closed and nuclear, and embeds densely in `L²` of any Haar measure.  That makes the
theory non-vacuous on a space of the kind the adelic test scale is built from.

* `deningerTestSpace_not_finiteDimensional` : disjoint compact opens give infinite dimension.
* `deningerPadicBall` : the separating family of balls in `ℤ_[p]`.
* `deningerPadicTest_isNuclearSpace`, `_seqComplete`, `_not_finiteDimensional` : the test space of
  `ℤ_[p]`.
* `deningerPadicTestToL2_denseRange` : and its dense embedding in `L²`.
-/

namespace RHTower

open MeasureTheory

section InfiniteDimensional

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- **Infinitely many disjoint nonempty compact open sets make the test space infinite
dimensional**, their indicators being linearly independent. -/
theorem deningerTestSpace_not_finiteDimensional (U : ℕ → Set Y)
    (hU : ∀ n, U n ∈ deningerCompactOpens Y) (hne : ∀ n, (U n).Nonempty)
    (hdisj : ∀ m n, m ≠ n → Disjoint (U m) (U n)) :
    ¬ FiniteDimensional ℝ (DeningerTestSpace Y) := by
  classical
  intro hfin
  set e : ℕ → DeningerTestSpace Y :=
    fun n => ⟨Set.indicator (U n) 1, deningerIndicator_mem (hU n)⟩ with hedef
  have hli : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro s g hg m hm
    obtain ⟨y, hy⟩ := hne m
    have hcoord : ((∑ i ∈ s, g i • e i : DeningerTestSpace Y) : Y → ℝ) y = g m := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single m]
      · show g m • Set.indicator (U m) (1 : Y → ℝ) y = g m
        rw [Set.indicator_of_mem hy]
        simp
      · intro i _ him
        have hyi : y ∉ U i := by
          intro hmem
          exact (Set.disjoint_left.mp (hdisj i m him) hmem) hy
        show g i • Set.indicator (U i) (1 : Y → ℝ) y = 0
        rw [Set.indicator_of_notMem hyi]
        simp
      · intro hms
        exact absurd hm hms
    rw [hg] at hcoord
    simpa using hcoord.symm
  haveI : Finite ℕ := hli.finite_of_isNoetherian
  exact not_finite ℕ

end InfiniteDimensional

section PadicBalls

variable (p : ℕ) [Fact p.Prime]

/-- The ball around `p ^ n` of radius its own norm: a compact open set of `ℤ_[p]`. -/
noncomputable def deningerPadicBall (n : ℕ) : Set ℤ_[p] :=
  Metric.ball ((p : ℤ_[p]) ^ n) (‖(p : ℤ_[p]) ^ n‖)

theorem deningerPadicBall_norm_pos (n : ℕ) : 0 < ‖(p : ℤ_[p]) ^ n‖ := by
  rw [PadicInt.norm_p_pow]
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  positivity

theorem deningerPadicBall_mem (n : ℕ) :
    deningerPadicBall p n ∈ deningerCompactOpens ℤ_[p] := by
  have hclopen : IsClopen (deningerPadicBall p n) :=
    IsUltrametricDist.isClopen_ball _ _
  exact ⟨hclopen.2, hclopen.1.isCompact⟩

theorem deningerPadicBall_nonempty (n : ℕ) : (deningerPadicBall p n).Nonempty :=
  ⟨(p : ℤ_[p]) ^ n, Metric.mem_ball_self (deningerPadicBall_norm_pos p n)⟩

theorem deningerPadicBall_norm_lt {m n : ℕ} (h : m < n) :
    ‖(p : ℤ_[p]) ^ n‖ < ‖(p : ℤ_[p]) ^ m‖ := by
  rw [PadicInt.norm_p_pow, PadicInt.norm_p_pow]
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  refine zpow_lt_zpow_right₀ hp ?_
  exact_mod_cast Int.neg_lt_neg (by exact_mod_cast h)

theorem deningerPadicBall_disjoint {m n : ℕ} (h : m ≠ n) :
    Disjoint (deningerPadicBall p m) (deningerPadicBall p n) := by
  have key : ∀ {a b : ℕ}, a < b →
      Disjoint (deningerPadicBall p a) (deningerPadicBall p b) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    have h1 : ‖x - (p : ℤ_[p]) ^ a‖ < ‖(p : ℤ_[p]) ^ a‖ := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hxa
    have h2 : ‖x - (p : ℤ_[p]) ^ b‖ < ‖(p : ℤ_[p]) ^ b‖ := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hxb
    have hlt := deningerPadicBall_norm_lt p hab
    have hne : ‖(p : ℤ_[p]) ^ a‖ ≠ ‖(p : ℤ_[p]) ^ b‖ := ne_of_gt hlt
    have hsub : ‖(p : ℤ_[p]) ^ a - (p : ℤ_[p]) ^ b‖ = ‖(p : ℤ_[p]) ^ a‖ := by
      have hneg : ‖(-((p : ℤ_[p]) ^ b))‖ = ‖(p : ℤ_[p]) ^ b‖ := norm_neg _
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := (p : ℤ_[p]) ^ a) (y := -((p : ℤ_[p]) ^ b)) (by rw [hneg]; exact hne)
      rw [sub_eq_add_neg, this, hneg, max_eq_left hlt.le]
    have hsplit : (p : ℤ_[p]) ^ a - (p : ℤ_[p]) ^ b
        = ((p : ℤ_[p]) ^ a - x) + (x - (p : ℤ_[p]) ^ b) := by abel
    have hbound : ‖(p : ℤ_[p]) ^ a - (p : ℤ_[p]) ^ b‖
        ≤ max ‖(p : ℤ_[p]) ^ a - x‖ ‖x - (p : ℤ_[p]) ^ b‖ := by
      rw [hsplit]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [hsub] at hbound
    have h1' : ‖(p : ℤ_[p]) ^ a - x‖ < ‖(p : ℤ_[p]) ^ a‖ := by
      rwa [← norm_neg, neg_sub]
    have h2' : ‖x - (p : ℤ_[p]) ^ b‖ < ‖(p : ℤ_[p]) ^ a‖ := lt_trans h2 hlt
    have : ‖(p : ℤ_[p]) ^ a‖ < ‖(p : ℤ_[p]) ^ a‖ :=
      lt_of_le_of_lt hbound (max_lt h1' h2')
    exact absurd this (lt_irrefl _)
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact key hlt
  · exact (key hlt).symm

end PadicBalls

section PadicTestSpace

variable (p : ℕ) [Fact p.Prime]

/-- **The test space of the `p`-adic integers is not finite dimensional.** -/
theorem deningerPadicTest_not_finiteDimensional :
    ¬ FiniteDimensional ℝ (DeningerTestSpace ℤ_[p]) :=
  deningerTestSpace_not_finiteDimensional (deningerPadicBall p) (deningerPadicBall_mem p)
    (deningerPadicBall_nonempty p) fun _ _ h => deningerPadicBall_disjoint p h

/-- **The test space of the `p`-adic integers is nuclear.** -/
theorem deningerPadicTest_isNuclearSpace :
    DeningerIsNuclearSpace (fun q : Seminorm ℝ (DeningerTestSpace ℤ_[p]) => q) :=
  deningerTestSpace_isNuclearSpace

/-- **The test space of the `p`-adic integers is sequentially complete.** -/
theorem deningerPadicTest_seqComplete {x : ℕ → DeningerTestSpace ℤ_[p]}
    (hx : DeningerFinestCauchy (𝕜 := ℝ) x) : ∃ a, DeningerFinestTendsto (𝕜 := ℝ) x a :=
  deningerTestSpace_seqComplete hx

/-- **Every subspace of it is nuclear.** -/
theorem deningerPadicTest_subspace_isNuclearSpaceC (F : Submodule ℝ (DeningerTestSpace ℤ_[p])) :
    DeningerIsNuclearSpaceC (fun q : Seminorm ℝ (DeningerTestSpace ℤ_[p]) =>
      deningerRestrictSeminorm F q) :=
  deningerTestSubspace_isNuclearSpaceC F

/-- **Every subspace of it is closed.** -/
theorem deningerPadicTest_subspace_closed (F : Submodule ℝ (DeningerTestSpace ℤ_[p]))
    {g : DeningerTestSpace ℤ_[p]} (hg : g ∉ F) :
    ∃ (q : Seminorm ℝ (DeningerTestSpace ℤ_[p])) (c : ℝ), 0 < c ∧ ∀ v ∈ F, c ≤ q (g - v) :=
  deningerTestSubspace_closed F hg

variable [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] (μ : Measure ℤ_[p]) [μ.IsAddHaarMeasure]

/-- **The test space of `ℤ_[p]` embeds injectively in `L²` of a Haar measure.** -/
theorem deningerPadicTestToL2_injective :
    Function.Injective (deningerTestToL2 μ) :=
  deningerTestToL2_injective μ

/-- **The test space of `ℤ_[p]` is dense in `L²` of a Haar measure.** -/
theorem deningerPadicTestToL2_denseRange : DenseRange (deningerTestToL2 μ) :=
  deningerTestToL2_denseRange μ

/-- **The three step scale over `ℤ_[p]`.** -/
theorem deningerPadicTestScale_three_step {q : Seminorm ℝ (DeningerTestSpace ℤ_[p])} {C : ℝ}
    (h : ∀ g, ‖deningerTestToL2 μ g‖ ≤ C * q g) :
    DenseRange (deningerSeminormMkC q) ∧ DenseRange (deningerSeminormFactorC h) ∧
      ∀ g, deningerSeminormFactorC h (deningerSeminormMkC q g) = deningerTestToL2 μ g :=
  deningerTestScale_three_step μ h

end PadicTestSpace

end RHTower
