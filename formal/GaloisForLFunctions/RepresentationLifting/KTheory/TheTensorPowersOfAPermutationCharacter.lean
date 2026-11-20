import GaloisForLFunctions.RepresentationLifting.KTheory.PermutationVirtualFreeness
import GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacterPairing
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The kernel contribution to permutation tensor multiplicities

The permutation module on k-tuples is the kth tensor power of the
permutation module. Slonim's separation of the identity term becomes
an exact separation of the action kernel in this family. Every other
group element moves at least two points. This gives a uniform geometric
error for the multiplicity of every finite-dimensional representation.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset Filter Topology
noncomputable section
open scoped Classical

variable (G X : Type*) [Group G] [Fintype G] [MulAction G X] [Fintype X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem fixedCount_card (Y : Type*) [MulAction G Y] [Fintype Y] (g : G) :
    permutationFixedCount G Y g=Fintype.card {y : Y // g • y=y} :=
  (Fintype.card_of_subtype (univ.filter (fun y : Y => g • y=y)) (fun _ => by simp)).symm

/-- A group element fixes a tuple exactly when it fixes every coordinate. -/
theorem permutationFixedCount_tuples (k : ℕ) (g : G) :
    permutationFixedCount G (Fin k → X) g=(permutationFixedCount G X g)^k := by
  let e : {f : Fin k → X // g • f=f} ≃ (Fin k → {x : X // g • x=x}) := {
    toFun f i := ⟨f.val i,congrFun f.property i⟩
    invFun x := ⟨fun i => (x i).val,funext fun i => (x i).property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [fixedCount_card,fixedCount_card,Fintype.card_congr e,Fintype.card_fun,Fintype.card_fin]

/-- Losing one fixed point forces a second loss, its image under the permutation. -/
theorem permutationFixedCount_le_card_sub_two (g : G) (hg : ¬∀ x : X, g • x=x) :
    permutationFixedCount G X g≤Fintype.card X-2 := by
  obtain ⟨x,hx⟩ := not_forall.mp hg
  let F := univ.filter (fun y : X => g • y=y)
  have hy : g • (g • x)≠g • x := fun he => hx ((MulAction.injective g) he)
  have hin : {x,g • x}⊆univ \ F := by
    intro y hh
    rcases mem_insert.mp hh with rfl|hh
    · simp [F,hx]
    · obtain rfl := mem_singleton.mp hh
      simp [F,hy]
  have hh := card_le_card hin
  rw [card_pair hx.symm,card_sdiff_of_subset (filter_subset _ _),card_univ] at hh
  change F.card≤_
  omega

/-- Multiplicity as a genuine equivariant Hom dimension on the k-tuple action. -/
def permutationPowerMultiplicity (ρ : Representation ℂ G V) (k : ℕ) : ℕ :=
  Module.finrank ℂ (ρ.IntertwiningMap (Representation.ofMulAction ℂ G (Fin k → X)))

theorem permutationPowerMultiplicity_moment (ρ : Representation ℂ G V) (k : ℕ) :
    (Nat.card G:ℂ)*(permutationPowerMultiplicity G X ρ k:ℂ) =
      ∑ g : G, (permutationFixedCount G X g:ℂ)^k*ρ.character g⁻¹ := by
  unfold permutationPowerMultiplicity
  rw [←representationCharacterPairing_eq_finrank,characterPairing,←mul_assoc,mul_inv_cancel₀ (NeZero.ne _),one_mul]
  apply sum_congr rfl
  intro g _
  have he := permutationVirtualRepresentation_apply G (Fin k → X) g
  change (Representation.ofMulAction ℂ G (Fin k → X)).character g=_ at he
  rw [he,permutationFixedCount_tuples,Nat.cast_pow]

/-- The surviving term is the sum of the test character over the action kernel. -/
def permutationKernelCharacter (ρ : Representation ℂ G V) : ℂ :=
  ∑ g ∈ univ.filter (fun g : G => ∀ x : X, g • x=x), ρ.character g⁻¹

/-- Exponential error at each tensor power. The base is (n-2)/n with
truncated subtraction in the cardinal, so the estimate also covers a singleton. -/
theorem permutationPowerMultiplicity_geometric_error [Nonempty X] (ρ : Representation ℂ G V) (k : ℕ) :
    ‖(Nat.card G:ℂ)*(permutationPowerMultiplicity G X ρ k:ℂ)/(Fintype.card X:ℂ)^k-
      permutationKernelCharacter G X ρ‖ ≤
      (((Fintype.card X-2:ℕ):ℝ)/(Fintype.card X:ℝ))^k * ∑ g : G, ‖ρ.character g⁻¹‖ := by
  let n := Fintype.card X
  have hn : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have normed (g : G) : ((permutationFixedCount G X g:ℂ)^k*ρ.character g⁻¹)/(n:ℂ)^k =
      ((permutationFixedCount G X g:ℂ)/(n:ℂ))^k*ρ.character g⁻¹ := by rw [div_pow]; ring
  rw [permutationPowerMultiplicity_moment,sum_div,permutationKernelCharacter,sum_filter,←sum_sub_distrib]
  calc
    _ ≤ ∑ g : G, ‖((permutationFixedCount G X g:ℂ)^k*ρ.character g⁻¹)/(n:ℂ)^k-
          (if ∀ x : X, g • x=x then ρ.character g⁻¹ else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ g : G, (((n-2:ℕ):ℝ)/(n:ℝ))^k*‖ρ.character g⁻¹‖ := by
      apply sum_le_sum
      intro g _
      rw [normed]
      by_cases hg : ∀ x : X, g • x=x
      · rw [if_pos hg,(permutationFixedCount_eq_card_iff G X g).mpr hg]
        change ‖((n:ℂ)/n)^k*_ - _‖ ≤ _
        rw [div_self hn,one_pow,one_mul,sub_self,norm_zero]
        positivity
      · rw [if_neg hg,sub_zero,norm_mul,norm_pow,norm_div,Complex.norm_natCast,Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (Nat.cast_le.mpr (permutationFixedCount_le_card_sub_two G X g hg))
            (Nat.cast_nonneg _)) k) (norm_nonneg _)
    _ = _ := (mul_sum ..).symm

/-- Normalized tensor-power multiplicities converge to the full kernel
contribution, for every finite permutation action with nonempty underlying set. -/
theorem permutationPowerMultiplicity_limit [Nonempty X] (ρ : Representation ℂ G V) :
    Tendsto (fun k : ℕ => (Nat.card G:ℂ)*(permutationPowerMultiplicity G X ρ k:ℂ)/
      (Fintype.card X:ℂ)^k) atTop (𝓝 (permutationKernelCharacter G X ρ)) := by
  let n := Fintype.card X
  have hn : 0<n := Fintype.card_pos
  have hr : ((n-2:ℕ):ℝ)/(n:ℝ)<1 := (div_lt_one (by exact_mod_cast hn)).mpr
    (by exact_mod_cast (show n-2<n by omega))
  have hl := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).mul_const
    (∑ g : G, ‖ρ.character g⁻¹‖)
  rw [zero_mul] at hl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (permutationPowerMultiplicity_geometric_error G X ρ) hl

#print axioms permutationFixedCount_le_card_sub_two
#print axioms permutationPowerMultiplicity_moment
#print axioms permutationPowerMultiplicity_geometric_error
#print axioms permutationPowerMultiplicity_limit
end
end GaloisForLFunctions.RepresentationLifting
