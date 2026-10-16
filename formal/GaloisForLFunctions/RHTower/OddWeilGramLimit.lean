import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation
import GaloisForLFunctions.RHTower.OddSectorAnyPoleWeightJointRigidity
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick

/-!
# Finite odd Weil Gram kernels and their limits

The actual odd cone makes every compact odd test family a positive
semidefinite complex Gram kernel. Mixed admissibility, finite expansion,
and Hermitian symmetry are proved without full-cone positivity.
Pointwise limits preserve the complete finite Gram condition.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent
open WeilSpectral

theorem admissible_weilTest_mixed {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Admissible (EF.weilTest f g) :=
  ⟨(EF.weilTest_contDiff hf hg.continuous hfc).continuous,
    EF.weilTest_hasCompactSupport hfc hgc,
    LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf hfc hg hgc⟩

theorem weilTest_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    EF.weilTest (∑ i ∈ s, c i • f i) (∑ i ∈ s, c i • f i) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * conj (c j)) • EF.weilTest (f i) (f j) := by
  classical
  funext x
  rw [weilTest_apply]
  have he : ∀ u : ℝ,
      (∑ i ∈ s, c i • f i) u * conj ((∑ i ∈ s, c i • f i) (u - x)) =
        ∑ i ∈ s, ∑ j ∈ s, (c i * conj (c j)) * (f i u * conj (f j (u - x))) := by
    intro u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [he]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum s fun j _ =>
    (integrable_mul_conj_shift (hf i) (hfc i) (hf j) x).const_mul _)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j _ =>
    (integrable_mul_conj_shift (hf i) (hfc i) (hf j) x).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, weilTest_apply]

theorem weilFullFunctional_finset_gram (lam : ℕ → ℝ) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    weilFullFunctional lam (EF.weilTest (∑ i ∈ s, c i • f i) (∑ i ∈ s, c i • f i)) =
      ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * weilFullFunctional lam (EF.weilTest (f i) (f j)) := by
  rw [weilTest_finset_sum s c f (fun i => (hf i).continuous) hfc]
  rw [weilFullFunctional_sum lam s fun i _ => Admissible.sum s fun j _ =>
    (admissible_weilTest_mixed (hf i) (hfc i) (hf j) (hfc j)).smul _]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weilFullFunctional_sum lam s fun j _ =>
    (admissible_weilTest_mixed (hf i) (hfc i) (hf j) (hfc j)).smul _]
  simp_rw [weilFullFunctional_smul]

theorem tilde_weilTest_mixed (f g : ℝ → ℂ) : EF.tilde (EF.weilTest f g) = EF.weilTest g f := by
  funext x
  rw [EF.tilde, weilTest_apply, weilTest_apply, ← integral_conj,
    ← integral_add_right_eq_self (fun u => g u * conj (f (u - x))) x]
  congr 1
  funext u
  simp only [sub_neg_eq_add, map_mul, conj_conj, add_sub_cancel_right]
  ring

theorem isPSDKernel_weilOdd {X : Type*} {lam : ℕ → ℝ}
    (hW : WeilPositiveOddAt 1 lam) (f : X → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hodd : ∀ i x, f i (-x) = -f i x) :
    IsPSDKernel fun x y => weilFullFunctional lam (EF.weilTest (f x) (f y)) := by
  classical
  refine ⟨fun x y => ?_, fun c => ?_⟩
  · rw [← weilFullFunctional_tilde, tilde_weilTest_mixed]
  · let F : ℝ → ℂ := ∑ i ∈ c.support, c i • f i
    have hF : ContDiff ℝ 2 F := by
      have he : F = fun x => ∑ i ∈ c.support, c i • f i x := by
        funext x
        simp [F]
      rw [he]
      exact ContDiff.sum (s := c.support) (fun i _ => (hf i).const_smul (c i))
    have hFc : HasCompactSupport F := by
      dsimp [F]
      induction c.support using Finset.induction_on with
      | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℂ))
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hfc a).smul_left.add ih
    have hFo : ∀ x, F (-x) = -F x := by
      intro x
      simp only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [hodd, mul_neg]
      rw [Finset.sum_neg_distrib]
    have hp := hW F hF hFc hFo
    rw [EvenSector.weilPoleWeightFunctional_one] at hp
    dsimp only [F] at hp
    rw [weilFullFunctional_finset_gram lam c.support c f hf hfc] at hp
    change 0 ≤ (∑ y ∈ c.support, ∑ x ∈ c.support,
      conj (c y) * c x * weilFullFunctional lam (EF.weilTest (f x) (f y))).re
    rw [Finset.sum_comm]
    convert hp using 1
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring

theorem isPSDKernel_limit {X : Type*} {K : ℕ → X → X → ℂ} {L : X → X → ℂ}
    (hK : ∀ j, IsPSDKernel (K j))
    (hl : ∀ x y, Tendsto (fun j => K j x y) atTop (𝓝 (L x y))) : IsPSDKernel L := by
  classical
  refine ⟨fun x y => ?_, fun c => ?_⟩
  · have h1 : Tendsto (fun j => conj (K j x y)) atTop (𝓝 (conj (L x y))) :=
      Complex.continuous_conj.tendsto _ |>.comp (hl x y)
    have h2 := hl y x
    have he : (fun j => conj (K j x y)) = fun j => K j y x :=
      funext fun j => (hK j).conj_symm x y
    rw [he] at h1
    exact tendsto_nhds_unique h1 h2
  · have ht : Tendsto (fun j => ∑ y ∈ c.support, ∑ x ∈ c.support,
        conj (c y) * c x * K j x y) atTop
        (𝓝 (∑ y ∈ c.support, ∑ x ∈ c.support, conj (c y) * c x * L x y)) :=
      tendsto_finsetSum c.support fun y _ => tendsto_finsetSum c.support fun x _ =>
        (hl x y).const_mul _
    exact ge_of_tendsto' (Complex.continuous_re.tendsto _ |>.comp ht) fun j => (hK j).nonneg c

end RHTower.OddResolvent
