import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel

/-!
# Constitutive split-formation parallax

Split formations into one common carrier generate their own comparison law.  A third formation
reads the residual erased by a second, four formations obey an exact coherence identity, and a
finite resolving family reconstructs the residual.  Positive repeated work is bounded exactly on
the residual kernel.
-/

open scoped BigOperators
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

universe u v w

variable {R : Type u} [CommRing R]
variable {X : Type v} [AddCommGroup X] [Module R X]
variable {Z : Type w} [AddCommGroup Z] [Module R Z]

/-- A formation of one source into a common carrier, together with exact recovery. -/
structure SplitLinearFormation (R : Type u) (X : Type v) (Z : Type w)
    [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Z] [Module R Z] where
  form : X →ₗ[R] Z
  recover : Z →ₗ[R] X
  recover_form : recover.comp form = LinearMap.id

namespace SplitLinearFormation

variable (F : SplitLinearFormation R X Z)

@[simp]
theorem recover_form_apply (x : X) : F.recover (F.form x) = x := by
  have h := LinearMap.congr_fun F.recover_form x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Regenerate-after-recovery projection in the common carrier. -/
def projection : Z →ₗ[R] Z := F.form.comp F.recover

@[simp]
theorem projection_apply (z : Z) : F.projection z = F.form (F.recover z) := rfl

theorem projection_idempotent : F.projection.comp F.projection = F.projection := by
  ext z
  simp [projection]

end SplitLinearFormation

/-- What target formation `Fj` recovers from source formed by `Fi`: `p_j f_i`. -/
def compressedComparison
    (Fi Fj : SplitLinearFormation R X Z) : X →ₗ[R] X :=
  Fj.recover.comp Fi.form

@[simp]
theorem compressedComparison_self (F : SplitLinearFormation R X Z) :
    compressedComparison F F = LinearMap.id :=
  F.recover_form

/-- Part of `Fi` erased by recovery through `Fj`: `f_i - f_j p_j f_i`. -/
def hiddenResidual
    (Fi Fj : SplitLinearFormation R X Z) : X →ₗ[R] Z :=
  Fi.form - Fj.form.comp (compressedComparison Fi Fj)

/-- Failure of compressed comparisons to compose through `Fj`. -/
def ternaryInterference
    (Fi Fj Fk : SplitLinearFormation R X Z) : X →ₗ[R] X :=
  compressedComparison Fi Fk -
    (compressedComparison Fj Fk).comp (compressedComparison Fi Fj)

@[simp]
theorem recover_hiddenResidual
    (Fi Fj : SplitLinearFormation R X Z) :
    Fj.recover.comp (hiddenResidual Fi Fj) = 0 := by
  ext x
  simp [hiddenResidual, compressedComparison]

/-- Exact formation split into the part recovered by `Fj` and its hidden residual. -/
theorem form_split
    (Fi Fj : SplitLinearFormation R X Z) :
    Fj.form.comp (compressedComparison Fi Fj) + hiddenResidual Fi Fj = Fi.form := by
  ext x
  simp [hiddenResidual]

/-- Generated parallax law: a third formation reads exactly the residual hidden by the second. -/
theorem ternaryInterference_eq_recover_hiddenResidual
    (Fi Fj Fk : SplitLinearFormation R X Z) :
    ternaryInterference Fi Fj Fk = Fk.recover.comp (hiddenResidual Fi Fj) := by
  ext x
  simp [ternaryInterference, compressedComparison, hiddenResidual]

/-- Four-formation conservation: the fourth interference is constrained by the first three. -/
theorem ternaryInterference_bianchi
    (Fi Fj Fk Fl : SplitLinearFormation R X Z) :
    (compressedComparison Fk Fl).comp (ternaryInterference Fi Fj Fk) +
        ternaryInterference Fi Fk Fl =
      ternaryInterference Fi Fj Fl +
        (ternaryInterference Fj Fk Fl).comp (compressedComparison Fi Fj) := by
  ext x
  simp [ternaryInterference, compressedComparison]

/-- A finite family is resolving when its regenerate-after-recovery projections sum to identity. -/
def IsResolvingFamily {ι : Type*} [Fintype ι]
    (F : ι → SplitLinearFormation R X Z) : Prop :=
  ∑ k, (F k).projection = LinearMap.id

/-- A resolving family reconstructs the entire hidden residual from all ternary interferences. -/
theorem hiddenResidual_reconstruction
    {ι : Type*} [Fintype ι]
    (F : ι → SplitLinearFormation R X Z)
    (hF : IsResolvingFamily F) (i j : ι) :
    hiddenResidual (F i) (F j) =
      ∑ k, (F k).form.comp (ternaryInterference (F i) (F j) (F k)) := by
  classical
  ext x
  rw [LinearMap.sum_apply]
  change hiddenResidual (F i) (F j) x =
    ∑ k, (F k).form (ternaryInterference (F i) (F j) (F k) x)
  simp_rw [show ∀ k, ternaryInterference (F i) (F j) (F k) x =
      (F k).recover (hiddenResidual (F i) (F j) x) by
    intro k
    exact LinearMap.congr_fun
      (ternaryInterference_eq_recover_hiddenResidual (F i) (F j) (F k)) x]
  have hx := LinearMap.congr_fun hF (hiddenResidual (F i) (F j) x)
  rw [LinearMap.sum_apply] at hx
  simpa [IsResolvingFamily, SplitLinearFormation.projection] using hx.symm

/-- All other formation organs predict the formed contribution of one withheld organ. -/
theorem withheldFormation_contribution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → SplitLinearFormation R X Z)
    (hF : IsResolvingFamily F) (i j m : ι) :
    (F m).form.comp (ternaryInterference (F i) (F j) (F m)) =
      hiddenResidual (F i) (F j) -
        ∑ k ∈ Finset.univ.erase m,
          (F k).form.comp (ternaryInterference (F i) (F j) (F k)) := by
  rw [hiddenResidual_reconstruction F hF i j,
    ← Finset.sum_erase_add Finset.univ
      (fun k => (F k).form.comp (ternaryInterference (F i) (F j) (F k)))
      (Finset.mem_univ m)]
  abel

/-- Under resolution, every ternary view vanishes exactly when the hidden law vanishes. -/
theorem hiddenResidual_eq_zero_iff_all_interference_eq_zero
    {ι : Type*} [Fintype ι]
    (F : ι → SplitLinearFormation R X Z)
    (hF : IsResolvingFamily F) (i j : ι) :
    hiddenResidual (F i) (F j) = 0 ↔
      ∀ k, ternaryInterference (F i) (F j) (F k) = 0 := by
  constructor
  · intro h k
    rw [ternaryInterference_eq_recover_hiddenResidual, h]
    simp
  · intro h
    rw [hiddenResidual_reconstruction F hF i j]
    simp [h]

/-- Closed fusion capstone: parallax is generated, coherent, and jointly reconstructive. -/
theorem splitFormationParallax_capstone
    {ι : Type*} [Fintype ι]
    (F : ι → SplitLinearFormation R X Z)
    (hF : IsResolvingFamily F) (i j k l : ι) :
    ternaryInterference (F i) (F j) (F k) =
        (F k).recover.comp (hiddenResidual (F i) (F j)) ∧
      (compressedComparison (F k) (F l)).comp
            (ternaryInterference (F i) (F j) (F k)) +
          ternaryInterference (F i) (F k) (F l) =
        ternaryInterference (F i) (F j) (F l) +
          (ternaryInterference (F j) (F k) (F l)).comp
            (compressedComparison (F i) (F j)) ∧
      hiddenResidual (F i) (F j) =
        ∑ q, (F q).form.comp (ternaryInterference (F i) (F j) (F q)) ∧
      (hiddenResidual (F i) (F j) = 0 ↔
        ∀ q, ternaryInterference (F i) (F j) (F q) = 0) := by
  exact ⟨ternaryInterference_eq_recover_hiddenResidual _ _ _,
    ternaryInterference_bianchi _ _ _ _,
    hiddenResidual_reconstruction F hF i j,
    hiddenResidual_eq_zero_iff_all_interference_eq_zero F hF i j⟩

/-! ## Positive global properness -/

/-- Positive work reported by every formation in a finite resolving family. -/
def parallaxEnergy
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X) : ℝ :=
  ∑ k, ‖ternaryInterference (F i) (F j) (F k) x‖ ^ (2 : ℕ)

/-- Hilbert realization: formation is isometric and recovery is its inner-product adjoint. -/
def IsIsometricAdjointFormation
    {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : SplitLinearFormation ℝ X Z) : Prop :=
  (∀ x, ‖F.form x‖ = ‖x‖) ∧
    ∀ x z, ⟪F.form x, z⟫_ℝ = ⟪x, F.recover z⟫_ℝ

/-- Fusion-frame inequality, restricted to the residual kernel of formation `j`. -/
def IsResidualFusionFrame
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (j : ι) (A B : ℝ) : Prop :=
  ∀ z, (F j).recover z = 0 →
    A * ‖z‖ ^ (2 : ℕ) ≤ ∑ k, ‖(F k).recover z‖ ^ (2 : ℕ) ∧
      (∑ k, ‖(F k).recover z‖ ^ (2 : ℕ)) ≤ B * ‖z‖ ^ (2 : ℕ)

/-- Orthogonal defect identity for two isometric adjoint split formations. -/
theorem hiddenResidual_norm_sq
    {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (Fi Fj : SplitLinearFormation ℝ X Z)
    (hi : IsIsometricAdjointFormation Fi)
    (hj : IsIsometricAdjointFormation Fj) (x : X) :
    ‖hiddenResidual Fi Fj x‖ ^ (2 : ℕ) =
      ‖x‖ ^ (2 : ℕ) - ‖compressedComparison Fi Fj x‖ ^ (2 : ℕ) := by
  have hkernel : Fj.recover (hiddenResidual Fi Fj x) = 0 := by
    change (Fj.recover.comp (hiddenResidual Fi Fj)) x = 0
    rw [recover_hiddenResidual]
    rfl
  have horth :
      ⟪Fj.form (compressedComparison Fi Fj x), hiddenResidual Fi Fj x⟫_ℝ = 0 := by
    rw [hj.2]
    simp [hkernel]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (Fj.form (compressedComparison Fi Fj x)) (hiddenResidual Fi Fj x) horth
  have hsplit := LinearMap.congr_fun (form_split Fi Fj) x
  have hsplit' : Fj.form (compressedComparison Fi Fj x) + hiddenResidual Fi Fj x =
      Fi.form x := by
    simpa using hsplit
  rw [hsplit', hi.1, hj.1] at hpy
  have hpy' : ‖x‖ ^ (2 : ℕ) =
      ‖compressedComparison Fi Fj x‖ ^ (2 : ℕ) + ‖hiddenResidual Fi Fj x‖ ^ (2 : ℕ) := by
    simpa only [pow_two] using hpy
  calc
    ‖hiddenResidual Fi Fj x‖ ^ (2 : ℕ) =
        (‖compressedComparison Fi Fj x‖ ^ (2 : ℕ) + ‖hiddenResidual Fi Fj x‖ ^ (2 : ℕ)) -
          ‖compressedComparison Fi Fj x‖ ^ (2 : ℕ) := by abel
    _ = ‖x‖ ^ (2 : ℕ) - ‖compressedComparison Fi Fj x‖ ^ (2 : ℕ) := by rw [← hpy']

/-- Fusion-frame conservation bounds the full ternary energy by the hidden residual norm. -/
theorem parallaxEnergy_fusionFrame_bounds
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X) {A B : ℝ}
    (hframe : IsResidualFusionFrame F j A B) :
    A * ‖hiddenResidual (F i) (F j) x‖ ^ (2 : ℕ) ≤ parallaxEnergy F i j x ∧
      parallaxEnergy F i j x ≤ B * ‖hiddenResidual (F i) (F j) x‖ ^ (2 : ℕ) := by
  have hkernel : (F j).recover (hiddenResidual (F i) (F j) x) = 0 := by
    change ((F j).recover.comp (hiddenResidual (F i) (F j))) x = 0
    rw [recover_hiddenResidual]
    rfl
  have hbounds := hframe (hiddenResidual (F i) (F j) x) hkernel
  simpa only [parallaxEnergy,
    show ∀ k, ternaryInterference (F i) (F j) (F k) x =
        (F k).recover (hiddenResidual (F i) (F j) x) by
      intro k
      exact LinearMap.congr_fun
        (ternaryInterference_eq_recover_hiddenResidual (F i) (F j) (F k)) x] using hbounds

/-- Parseval residual frames give exact positive conservation. -/
theorem parallaxEnergy_parseval
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X)
    (hframe : IsResidualFusionFrame F j 1 1) :
    parallaxEnergy F i j x = ‖hiddenResidual (F i) (F j) x‖ ^ (2 : ℕ) := by
  have h := parallaxEnergy_fusionFrame_bounds F i j x hframe
  simpa using le_antisymm h.2 h.1

/-- Full positive conservation after identifying the residual as an orthogonal defect. -/
theorem parallaxEnergy_parseval_eq_source_defect
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X)
    (hi : IsIsometricAdjointFormation (F i))
    (hj : IsIsometricAdjointFormation (F j))
    (hframe : IsResidualFusionFrame F j 1 1) :
    parallaxEnergy F i j x =
      ‖x‖ ^ (2 : ℕ) - ‖compressedComparison (F i) (F j) x‖ ^ (2 : ℕ) := by
  rw [parallaxEnergy_parseval F i j x hframe,
    hiddenResidual_norm_sq (F i) (F j) hi hj x]

theorem parallaxEnergy_nonneg
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X) :
    0 ≤ parallaxEnergy F i j x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem parallaxEnergy_eq_zero_iff
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X) :
    parallaxEnergy F i j x = 0 ↔
      ∀ k, ternaryInterference (F i) (F j) (F k) x = 0 := by
  constructor
  · intro h k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q (_ : q ∈ Finset.univ) =>
        sq_nonneg ‖ternaryInterference (F i) (F j) (F q) x‖)).mp h
      k (Finset.mem_univ k)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hk)
  · intro h
    simp [parallaxEnergy, h]

theorem hiddenResidual_apply_eq_zero_iff_all_interference_apply_eq_zero
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z)
    (hF : IsResolvingFamily F) (i j : ι) (x : X) :
    hiddenResidual (F i) (F j) x = 0 ↔
      ∀ k, ternaryInterference (F i) (F j) (F k) x = 0 := by
  constructor
  · intro h k
    have hk := LinearMap.congr_fun
      (ternaryInterference_eq_recover_hiddenResidual (F i) (F j) (F k)) x
    simpa [h] using hk
  · intro h
    have hrec := LinearMap.congr_fun (hiddenResidual_reconstruction F hF i j) x
    rw [LinearMap.sum_apply] at hrec
    simpa [h] using hrec

/-- Scalar Archimedean properness: an indefinitely repeated nonzero work block is unbounded. -/
theorem natMultiple_bounded_iff_zero (c : ℝ) :
    (∃ C : ℝ, ∀ q : ℕ, |(q : ℝ) * c| ≤ C) ↔ c = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hc
    have hpos : 0 < |c| := abs_pos.mpr hc
    obtain ⟨q, hq⟩ := exists_nat_gt (C / |c|)
    have hstrict : C < (q : ℝ) * |c| := (div_lt_iff₀ hpos).mp hq
    have hbound := hC q
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)] at hbound
    exact (not_lt_of_ge hbound) hstrict
  · rintro rfl
    exact ⟨0, by intro q; simp⟩

/-- Work accumulated by repeating one complete formation block `q` times. -/
def repeatedParallaxWork
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z) (i j : ι) (x : X) (q : ℕ) : ℝ :=
  (q : ℝ) * parallaxEnergy F i j x

/-- Global properness: uniformly bounded repeated work selects exactly the neutral residual kernel. -/
theorem repeatedParallaxWork_bounded_iff_hiddenResidual_eq_zero
    {ι : Type*} [Fintype ι]
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ι → SplitLinearFormation ℝ X Z)
    (hF : IsResolvingFamily F) (i j : ι) (x : X) :
    (∃ C : ℝ, ∀ q : ℕ, |repeatedParallaxWork F i j x q| ≤ C) ↔
      hiddenResidual (F i) (F j) x = 0 := by
  rw [show (∃ C : ℝ, ∀ q : ℕ, |repeatedParallaxWork F i j x q| ≤ C) ↔
      parallaxEnergy F i j x = 0 by
    simpa [repeatedParallaxWork] using
      natMultiple_bounded_iff_zero (parallaxEnergy F i j x)]
  exact (parallaxEnergy_eq_zero_iff F i j x).trans
    (hiddenResidual_apply_eq_zero_iff_all_interference_apply_eq_zero F hF i j x).symm

end GaloisForLFunctions.HTGeometry
