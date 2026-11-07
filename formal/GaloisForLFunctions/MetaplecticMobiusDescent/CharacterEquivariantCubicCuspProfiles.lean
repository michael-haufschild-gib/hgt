/-
Character-equivariant cusp cutoffs adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.HighCubicCuspsAreLocallyFinite

/-!
# Character-equivariant sums of high-cusp profiles

Distinct principal cusp cosets cannot both have height above one.
The resulting profile sum has at most one nonzero term and transforms by
the actual cubic character. This defines the incoming seed without a
convergence assumption.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma cosetHeight_rightEquiv (M : levelThree) (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight (rightEquiv M x) w = cosetHeight x (complexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf (N*M)) w = cosetHeight (cosetOf N) (complexMatrix M • w)
    rw [cosetHeight_cosetOf,cosetHeight_cosetOf,map_mul,mul_smul]

lemma high_coset_unique (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace)
    (x y : CuspCosets) (hx : Y<cosetHeight x w) (hy : Y<cosetHeight y w) : x=y := by
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      by_contra hne
      have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0≠0 := by
        intro hc
        have hT : M*N⁻¹ ∈ cuspStabilizer := (mem_cuspStabilizer_iff _).mpr hc
        exact hne ((cosetOf_eq_iff M N).mpr ⟨M*N⁻¹,hT,by group⟩)
      have hp := integral_hyperbolicHeight_mul_le_one
        ((M*N⁻¹ : levelThree) : SL(2,O)) hc (complexMatrix N • w)
      rw [integralComplexMatrix_levelThree,map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change Y<cosetHeight (cosetOf M) w at hx
      change Y<cosetHeight (cosetOf N) w at hy
      rw [cosetHeight_cosetOf] at hx hy
      have hm := lt_of_le_of_lt hY hx
      have hn := lt_of_le_of_lt hY hy
      nlinarith only [hp,hm,hn,mul_pos (sub_pos.mpr hm) (sub_pos.mpr hn)]

lemma high_cosets_finite (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace) :
    Set.Finite {x : CuspCosets | Y<cosetHeight x w} := by
  have h : Set.Subsingleton {x : CuspCosets | Y<cosetHeight x w} :=
    fun x hx y hy => high_coset_unique Y hY w x y hx hy
  exact h.finite

def cuspCutoffTerm (Y : ℝ) (F : ℝ → ℂ) (x : CuspCosets) (w : HyperbolicSpace) : ℂ :=
  if Y<cosetHeight x w then (cosetCharacter x)⁻¹ * F (cosetHeight x w) else 0

lemma cuspCutoffTerm_finiteSupport (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x => cuspCutoffTerm Y F x w) := by
  apply (high_cosets_finite Y hY w).subset
  intro x hx
  by_contra hn
  simp only [Function.mem_support] at hx
  change ¬Y<cosetHeight x w at hn
  exact hx (by simp [cuspCutoffTerm,hn])

lemma cuspCutoffTerm_summable (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Summable (fun x => cuspCutoffTerm Y F x w) :=
  summable_of_hasFiniteSupport (cuspCutoffTerm_finiteSupport Y hY F w)

def cuspCutoffCorrection (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑'x,cuspCutoffTerm Y F x w

lemma cuspCutoffTerm_automorphy (Y : ℝ) (F : ℝ → ℂ) (M : levelThree)
    (x : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm Y F x (complexMatrix M • w) =
      complexCharacter M * cuspCutoffTerm Y F (rightEquiv M x) w := by
  have hM : complexCharacter M≠0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  simp only [cuspCutoffTerm,cosetHeight_rightEquiv,cosetCharacter_rightEquiv]
  split_ifs <;> simp [mul_inv_rev,hM,mul_assoc,mul_left_comm,mul_comm]

theorem cuspCutoffCorrection_automorphy (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (M : levelThree) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (complexMatrix M • w) = complexCharacter M*cuspCutoffCorrection Y F w := by
  have hsum := cuspCutoffTerm_summable Y hY F w
  have hreindex := (rightEquiv M).hasSum_iff.mpr hsum.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact (cuspCutoffTerm_summable Y hY F (complexMatrix M • w)).hasSum.unique
    (hscale.congr_fun (fun x => cuspCutoffTerm_automorphy Y F M x w))

lemma cuspCutoffCorrection_eq (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (w : HyperbolicSpace) (x : CuspCosets) (hx : Y<cosetHeight x w) :
    cuspCutoffCorrection Y F w = (cosetCharacter x)⁻¹*F (cosetHeight x w) := by
  unfold cuspCutoffCorrection
  rw [tsum_eq_single x]
  · simp [cuspCutoffTerm,hx]
  · intro y hy
    have hn : ¬Y<cosetHeight y w := fun hh => hy (high_coset_unique Y hY w y x hh hx)
    simp [cuspCutoffTerm,hn]

#print axioms high_coset_unique
#print axioms cuspCutoffCorrection_automorphy
#print axioms cuspCutoffCorrection_eq
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
