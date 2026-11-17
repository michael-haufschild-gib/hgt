import GaloisForLFunctions.RepresentationLifting.Actions.SmoothConnectedActions
import GaloisForLFunctions.RepresentationLifting.Differential.NilpotentDividedPowerConnection
import GaloisForLFunctions.HTGeometry.InvolutiveSubspaceParityDecomposition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Smooth real GL₂ actions and the characteristic-two boundary

Every smooth action of GL₂(ℝ) kills all scalar matrices
and is determined by a unique involution acting on negative determinants.
In characteristic different from two, every invariant subspace splits into
the two sign sectors. In characteristic two, actions are classified by a
unique square-zero residue N, with negative determinants acting as 1 + N.
Every such residue occurs, including an explicit nonsplit two-dimensional
extension.

The determinant descent from arXiv:2611.20896, Lemma 2.2, combines with
connectedness of positive real scalars to remove any central-character
premise over ℝ. The characteristic-two example gives the exact obstruction
to extending the semisimplicity conclusion to that characteristic.
Smoothness means that each vector is fixed on some identity neighborhood.
-/

noncomputable section
open Filter Topology Matrix
namespace GaloisForLFunctions.RepresentationLifting.RealGL2

private theorem real_unit_square {u : ℝˣ} (hu : 0 < (u : ℝ)) : ∃ v : ℝˣ, v ^ 2 = u := by
  let v : ℝˣ := Units.mk0 (Real.sqrt (u : ℝ)) (ne_of_gt (Real.sqrt_pos.mpr hu))
  refine ⟨v, Units.ext ?_⟩
  change Real.sqrt (u : ℝ) ^ 2 = (u : ℝ)
  exact Real.sq_sqrt hu.le

/-- Killing scalar squares over the reals leaves precisely the determinant sign. -/
theorem square_killing_hom {H : Type*} [Group H] (χ : ℝˣ →* H)
    (hχ : ∀ u : ℝˣ, χ (u ^ 2) = 1) (u : ℝˣ) :
    χ u = if 0 < (u : ℝ) then 1 else χ (-1) := by
  have hp (v : ℝˣ) (hv : 0 < (v : ℝ)) : χ v = 1 := by
    obtain ⟨w, rfl⟩ := real_unit_square hv
    exact hχ w
  by_cases hu : 0 < (u : ℝ)
  · rw [if_pos hu]
    exact hp u hu
  · rw [if_neg hu]
    have hn : (u : ℝ) < 0 := (lt_or_gt_of_ne u.ne_zero).resolve_right hu
    have hm : χ (-u) = 1 := hp (-u) (by simpa using neg_pos.mpr hn)
    have he : u = (-1 : ℝˣ) * (-u) := by simp
    rw [he, map_mul, hm, mul_one]

/-- A real sign character with values in an arbitrary involution. -/
def signAction {H : Type*} [Group H] (J : H) (hJ : J * J = 1) : ℝˣ →* H where
  toFun u := if 0 < (u : ℝ) then 1 else J
  map_one' := by simp
  map_mul' u v := by
    have hnu : ¬ 0 < (u : ℝ) → (u : ℝ) < 0 :=
      fun h => (lt_or_gt_of_ne u.ne_zero).resolve_right h
    have hnv : ¬ 0 < (v : ℝ) → (v : ℝ) < 0 :=
      fun h => (lt_or_gt_of_ne v.ne_zero).resolve_right h
    by_cases hu : 0 < (u : ℝ) <;> by_cases hv : 0 < (v : ℝ)
    · simp only [Units.val_mul, if_pos hu, if_pos hv, if_pos (mul_pos hu hv), one_mul]
    · simp only [Units.val_mul, if_pos hu, if_neg hv,
        if_neg (not_lt.mpr (mul_neg_of_pos_of_neg hu (hnv hv)).le), one_mul]
    · simp only [Units.val_mul, if_neg hu, if_pos hv,
        if_neg (not_lt.mpr (mul_neg_of_neg_of_pos (hnu hu) hv).le), mul_one]
    · simp only [Units.val_mul, if_neg hu, if_neg hv,
        if_pos (mul_pos_of_neg_of_neg (hnu hu) (hnv hv)), hJ]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The determinant-sign action of an involution on a real GL₂ module. -/
def determinantSignAction (J : V ≃ₗ[k] V) (hJ : J * J = 1) :
    GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V) :=
  (signAction J hJ).comp GeneralLinearGroup.det

/-- Every determinant-sign action is smooth, without any finite-dimensionality assumption. -/
theorem determinantSignAction_smooth (J : V ≃ₗ[k] V) (hJ : J * J = 1) (v : V) :
    ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), determinantSignAction J hJ g v = v := by
  have hc : Continuous (fun g : GeneralLinearGroup (Fin 2) ℝ =>
      (GeneralLinearGroup.det g : ℝ)) := Units.continuous_val.comp GeneralLinearGroup.continuous_det
  have hp : ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ),
      0 < (GeneralLinearGroup.det g : ℝ) :=
    hc.continuousAt.eventually (eventually_gt_nhds (by simp))
  filter_upwards [hp] with g hg
  change (if 0 < (GeneralLinearGroup.det g : ℝ) then (1 : V ≃ₗ[k] V) else J) v = v
  rw [if_pos hg]
  rfl

/-- Scalar matrices act trivially because their determinants are positive squares. -/
theorem determinantSignAction_scalar (J : V ≃ₗ[k] V) (hJ : J * J = 1) (u : ℝˣ) :
    determinantSignAction J hJ (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  change (if 0 < (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) u) : ℝ)
    then (1 : V ≃ₗ[k] V) else J) = 1
  rw [GeneralLinearGroup.det_scalar]
  simp only [Fintype.card_fin]
  change (if 0 < (u : ℝ) ^ 2 then (1 : V ≃ₗ[k] V) else J) = 1
  exact if_pos (sq_pos_of_ne_zero u.ne_zero)

private def expUnit (t : ℝ) : ℝˣ := Units.mk0 (Real.exp t) (Real.exp_ne_zero t)

private theorem continuous_expUnit : Continuous expUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · exact Real.continuous_exp
  · change Continuous (fun t : ℝ => (Real.exp t)⁻¹)
    exact Real.continuous_exp.inv₀ Real.exp_ne_zero

private theorem continuous_scalar :
    Continuous (GeneralLinearGroup.scalar (Fin 2) : ℝˣ → GeneralLinearGroup (Fin 2) ℝ) := by
  simp_rw [Units.continuous_iff, ← map_inv, GeneralLinearGroup.coe_scalar]
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun u : ℝˣ => if i = j then (u : ℝ) else 0)
    split_ifs <;> fun_prop
  · apply continuous_matrix
    intro i j
    change Continuous (fun u : ℝˣ => if i = j then ((u⁻¹ : ℝˣ) : ℝ) else 0)
    split_ifs <;> fun_prop

/-- Every smooth real GL₂ action kills its entire center. -/
theorem smooth_scalar_trivial
    (ρ : GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), ρ g v = v)
    (u : ℝˣ) : ρ (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  have hp (v : ℝˣ) (hv : 0 < (v : ℝ)) : ρ (GeneralLinearGroup.scalar (Fin 2) v) = 1 := by
    have h0 : GeneralLinearGroup.scalar (Fin 2) (expUnit 0) = 1 := by
      have he : expUnit 0 = 1 := by ext; exact Real.exp_zero
      rw [he, map_one]
    have heq := ConnectedActions.connected_family_trivial ρ hρ
      (fun t : ℝ => GeneralLinearGroup.scalar (Fin 2) (expUnit t))
      (continuous_scalar.comp continuous_expUnit) 0 h0 (Real.log (v : ℝ))
    have hv' : expUnit (Real.log (v : ℝ)) = v := Units.ext (Real.exp_log hv)
    simpa only [hv'] using heq
  by_cases hu : 0 < (u : ℝ)
  · exact hp u hu
  · have hn : (u : ℝ) < 0 := (lt_or_gt_of_ne u.ne_zero).resolve_right hu
    have hm : ρ (GeneralLinearGroup.scalar (Fin 2) (-u)) = 1 :=
      hp (-u) (by simpa using neg_pos.mpr hn)
    obtain ⟨χ, hχ, _⟩ := ConnectedActions.smooth_det_factor ρ hρ
    have hneg : ρ (GeneralLinearGroup.scalar (Fin 2) (-1 : ℝˣ)) = 1 := by
      rw [← hχ]
      change χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (-1 : ℝˣ))) = 1
      rw [GeneralLinearGroup.det_scalar]
      simp
    have hu' : u = (-1 : ℝˣ) * (-u) := by simp
    rw [hu', map_mul, map_mul, hneg, hm, one_mul]

/-- Every smooth real GL₂ action is determined by one involution and determinant sign. -/
theorem smooth_sign_classification
    (ρ : GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), ρ g v = v) :
    ∃! J : V ≃ₗ[k] V, J * J = 1 ∧ ∀ g,
      ρ g = if 0 < (GeneralLinearGroup.det g : ℝ) then 1 else J := by
  obtain ⟨χ, hχ, _⟩ := ConnectedActions.smooth_det_factor ρ hρ
  have he (g : GeneralLinearGroup (Fin 2) ℝ) : χ (GeneralLinearGroup.det g) = ρ g :=
    congrArg (fun f : GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V) => f g) hχ
  have hs (u : ℝˣ) : χ (u ^ 2) = 1 := by
    have h := (he (GeneralLinearGroup.scalar (Fin 2) u)).trans (smooth_scalar_trivial ρ hρ u)
    simpa only [GeneralLinearGroup.det_scalar, Fintype.card_fin] using h
  have hj : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hf (g : GeneralLinearGroup (Fin 2) ℝ) :
      ρ g = if 0 < (GeneralLinearGroup.det g : ℝ) then 1 else χ (-1) := by
    rw [← he]
    exact square_killing_hom χ hs _
  refine ⟨χ (-1), ⟨hj, hf⟩, ?_⟩
  intro J hJ
  obtain ⟨g, hg⟩ := (GeneralLinearGroup.det_surjective : Function.Surjective
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℝ →* ℝˣ)) (-1 : ℝˣ)
  have h := (hJ.2 g).symm.trans (hf g)
  simpa only [hg, Units.val_neg, Units.val_one, neg_pos,
    not_lt_of_ge zero_le_one, if_false] using h

/-- In characteristic different from two every invariant subspace splits into the two determinant-sign sectors. -/
theorem smooth_invariant_subspace_splits (h2 : (2 : k) ≠ 0)
    (ρ : GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), ρ g v = v) :
    ∃ J : V ≃ₗ[k] V, J * J = 1 ∧
      (∀ g, ρ g = if 0 < (GeneralLinearGroup.det g : ℝ) then 1 else J) ∧
      ∀ U : Submodule k V, (∀ g, U.map (ρ g).toLinearMap ≤ U) →
        U = (U ⊓ GaloisForLFunctions.HTGeometry.involutiveEvenSubspace J) ⊔
          (U ⊓ GaloisForLFunctions.HTGeometry.involutiveOddSubspace J) := by
  obtain ⟨J, ⟨hJ, he⟩, _⟩ := smooth_sign_classification ρ hρ
  refine ⟨J, hJ, he, ?_⟩
  intro U hU
  have hj (v : V) : J (J v) = v := congrArg (fun e : V ≃ₗ[k] V => e v) hJ
  apply GaloisForLFunctions.HTGeometry.invariantSubspace_eq_even_sup_odd J hj h2 U
  obtain ⟨g, hg⟩ := (GeneralLinearGroup.det_surjective : Function.Surjective
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℝ →* ℝˣ)) (-1 : ℝˣ)
  have heq : ρ g = J := by
    simpa only [hg, Units.val_neg, Units.val_one, neg_pos,
      not_lt_of_ge zero_le_one, if_false] using he g
  simpa only [heq] using hU g

variable [CharP k 2]

include k in
private theorem twice_zero (v : V) : v + v = 0 := by
  rw [← two_smul k, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]

/-- In characteristic two, an involution is the identity plus a square-zero residue. -/
theorem involution_residue_square (J : V ≃ₗ[k] V) (hJ : J * J = 1) :
    (J.toLinearMap - 1) ^ 2 = 0 := by
  have hj (v : V) : J (J v) = v := congrArg (fun e : V ≃ₗ[k] V => e v) hJ
  ext v
  change J (J v - v) - (J v - v) = 0
  rw [map_sub, hj]
  have hv := twice_zero (k := k) v
  have hw := twice_zero (k := k) (J v)
  calc
    v - J v - (J v - v) = (v + v) - (J v + J v) := by abel
    _ = 0 := by rw [hv, hw, sub_self]

/-- Every square-zero residue produces an involution in characteristic two. -/
def squareZeroInvolution (N : Module.End k V) (hN : N ^ 2 = 0) : V ≃ₗ[k] V where
  toFun v := v + N v
  invFun v := v + N v
  left_inv v := by
    have hn : N (N v) = 0 := LinearMap.congr_fun hN v
    change (v + N v) + N (v + N v) = v
    rw [map_add, hn, add_zero, add_assoc, twice_zero (k := k), add_zero]
  right_inv v := by
    have hn : N (N v) = 0 := LinearMap.congr_fun hN v
    change (v + N v) + N (v + N v) = v
    rw [map_add, hn, add_zero, add_assoc, twice_zero (k := k), add_zero]
  map_add' v w := by rw [map_add]; abel
  map_smul' c v := by
    change c • v + N (c • v) = c • (v + N v)
    rw [map_smul, smul_add]

theorem squareZeroInvolution_sq (N : Module.End k V) (hN : N ^ 2 = 0) :
    squareZeroInvolution N hN * squareZeroInvolution N hN = 1 := by
  ext v
  exact (squareZeroInvolution N hN).left_inv v

/-- Every smooth real GL₂ action in characteristic two is a unique square-zero sign action. -/
theorem smooth_action_classification
    (ρ : GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), ρ g v = v) :
    ∃! N : Module.End k V, N ^ 2 = 0 ∧ ∀ g,
      (ρ g).toLinearMap = if 0 < (GeneralLinearGroup.det g : ℝ) then 1 else 1 + N := by
  obtain ⟨J, ⟨hJ, hsign⟩, _⟩ := smooth_sign_classification ρ hρ
  let N := J.toLinearMap - 1
  have hn : N ^ 2 = 0 := involution_residue_square J hJ
  have hf (g : GeneralLinearGroup (Fin 2) ℝ) :
      (ρ g).toLinearMap = if 0 < (GeneralLinearGroup.det g : ℝ) then 1 else 1 + N := by
    rw [hsign]
    split_ifs
    · rfl
    · change J.toLinearMap = 1 + (J.toLinearMap - 1)
      abel
  refine ⟨N, ⟨hn, hf⟩, ?_⟩
  intro M hM
  obtain ⟨g, hg⟩ := (GeneralLinearGroup.det_surjective : Function.Surjective
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℝ →* ℝˣ)) (-1 : ℝˣ)
  have heq := (hf g).symm.trans (hM.2 g)
  simp only [hg, Units.val_neg, Units.val_one, neg_pos, not_lt_of_ge zero_le_one, if_false] at heq
  exact (add_left_cancel heq).symm

/-- Every square-zero residue realizes the classification by an actual smooth action with trivial center. -/
theorem squareZero_action_realizes (N : Module.End k V) (hN : N ^ 2 = 0) :
    ∃ ρ : GeneralLinearGroup (Fin 2) ℝ →* (V ≃ₗ[k] V),
      (∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), ρ g v = v) ∧
      (∀ u : ℝˣ, ρ (GeneralLinearGroup.scalar (Fin 2) u) = 1) ∧
      ∀ g, (ρ g).toLinearMap = if 0 < (GeneralLinearGroup.det g : ℝ) then 1 else 1 + N := by
  let J := squareZeroInvolution N hN
  let hJ := squareZeroInvolution_sq N hN
  refine ⟨determinantSignAction J hJ, determinantSignAction_smooth J hJ,
    determinantSignAction_scalar J hJ, ?_⟩
  intro g
  change (if 0 < (GeneralLinearGroup.det g : ℝ) then (1 : V ≃ₗ[k] V) else J).toLinearMap = _
  split_ifs <;> rfl

/-- The nonzero free square-zero residue has no invariant retraction onto its fixed line. -/
theorem squareZeroShift_no_retraction :
    ¬ ∃ π : (k × k) →ₗ[k] k,
      (∀ a, π (a, 0) = a) ∧
      ∀ v, π (squareZeroInvolution (DividedPower.squareZeroShift k k)
        (DividedPower.squareZeroShift_sq k k) v) = π v := by
  rintro ⟨π, hline, hinv⟩
  have h := hinv (0, 1)
  change π ((0, 1) + (1, 0)) = π (0, 1) at h
  rw [map_add, hline] at h
  exact one_ne_zero (add_left_cancel (h.trans (add_zero _).symm))

/-- A smooth real GL₂ action with trivial center need not split in characteristic two. -/
theorem exists_nonsplit_smooth_action :
    ∃ ρ : GeneralLinearGroup (Fin 2) ℝ →* ((k × k) ≃ₗ[k] (k × k)),
      (∀ v, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℝ), ρ g v = v) ∧
      (∀ u : ℝˣ, ρ (GeneralLinearGroup.scalar (Fin 2) u) = 1) ∧
      ¬ ∃ π : (k × k) →ₗ[k] k, (∀ a, π (a, 0) = a) ∧ ∀ g v, π (ρ g v) = π v := by
  obtain ⟨ρ, hs, hc, he⟩ := squareZero_action_realizes
    (DividedPower.squareZeroShift k k) (DividedPower.squareZeroShift_sq k k)
  refine ⟨ρ, hs, hc, ?_⟩
  rintro ⟨π, hline, hπ⟩
  apply squareZeroShift_no_retraction (k := k)
  refine ⟨π, hline, ?_⟩
  obtain ⟨g, hg⟩ := (GeneralLinearGroup.det_surjective : Function.Surjective
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℝ →* ℝˣ)) (-1 : ℝˣ)
  have hg' := he g
  simp only [hg, Units.val_neg, Units.val_one, neg_pos, not_lt_of_ge zero_le_one, if_false] at hg'
  intro v
  have hv := LinearMap.congr_fun hg' v
  exact (congrArg π hv).symm.trans (hπ g v)

#print axioms exists_nonsplit_smooth_action

#print axioms smooth_action_classification
#print axioms smooth_invariant_subspace_splits
#print axioms smooth_sign_classification
#print axioms smooth_scalar_trivial
#print axioms squareZero_action_realizes
#print axioms squareZeroShift_no_retraction
end GaloisForLFunctions.RepresentationLifting.RealGL2
