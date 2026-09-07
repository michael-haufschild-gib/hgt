import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularEnergyDomain
import GaloisForLFunctions.HTGeometry.FriedrichsFormOperator
import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent

/-!
The constructed modular energy domain supplies its actual self-adjoint form operator and a unique finite-energy weak response to the full angular forcing at every actual Xi occurrence on both physical branches.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMQuadraticMixedSource
noncomputable section

/-- The actual positive form operator of the modular value-plus-gradient energy. -/
def energyOperator : Space →ₗ.[ℂ] Space := friedrichsFormOperator embedding

/-- Self-adjointness follows from the constructed faithful, dense modular form domain. -/
theorem energyOperator_selfAdjoint : IsSelfAdjoint energyOperator :=
  friedrichsFormOperator_isSelfAdjoint embedding embedding_injective embedding_dense

private theorem physical_parameter_nonreal (q : XiZeroCopy) (minusBranch : Bool) :
    (parameter q minusBranch).im ≠ 0 := by
  cases minusBranch
  · exact (xi_resolvent_parameter_nonreal q).2
  · exact (xi_resolvent_parameter_nonreal q).1

private theorem physical_shift_nonreal (q : XiZeroCopy) (minusBranch : Bool) :
    (1-parameter q minusBranch).im ≠ 0 := by
  simpa using neg_ne_zero.mpr (physical_parameter_nonreal q minusBranch)

/-- The constructed modular operator has an actual inverse at both physical Xi parameters. -/
theorem physical_resolvent_bijective (q : XiZeroCopy) (minusBranch : Bool) :
    Function.Bijective (shiftedMap energyOperator (1-parameter q minusBranch)) :=
  bijective_shiftedMap energyOperator_selfAdjoint (physical_shift_nonreal q minusBranch)

/-- The exact completed energy retains scalar mass and both original frame derivatives. -/
theorem energy_inner_decomposition (v h : energyDomain) :
    inner ℂ v h = inner ℂ (embedding v) (embedding h) +
      ∑ i : Fin 2, inner ℂ ((v : EnergySpace) i.succ) ((h : EnergySpace) i.succ) := by
  change inner ℂ (v : EnergySpace) (h : EnergySpace) = _
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  rfl

/-- The variational form of the full actual cusp-subtracted forced angular equation. -/
def WeakSolution (q : XiZeroCopy) (minusBranch : Bool) (h : energyDomain) : Prop :=
  ∀ v : energyDomain, inner ℂ v h - (1-parameter q minusBranch)*inner ℂ (embedding v) (embedding h) =
    -inner ℂ (embedding v) (forcingVector q minusBranch)

/-- The variational equation is exactly the gradient form for `(Delta-L)h=F`,
with the native invariant measure, both derivatives and the complete forcing retained. -/
theorem weakSolution_iff_gradient (q : XiZeroCopy) (minusBranch : Bool) (h : energyDomain) :
    WeakSolution q minusBranch h ↔
      ∀ v : energyDomain,
        (∑ i : Fin 2, inner ℂ ((v : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) +
          parameter q minusBranch*inner ℂ (embedding v) (embedding h) =
            -inner ℂ (embedding v) (forcingVector q minusBranch) := by
  unfold WeakSolution
  apply forall_congr'
  intro v
  rw [energy_inner_decomposition]
  have he (a b L : ℂ) : a+b-(1-L)*a = b+L*a := by ring
  rw [he]

/-- Every actual Xi occurrence on both physical branches has a full finite-energy angular
weak response in the constructed modular domain. No form-domain or inverse premise is supplied. -/
theorem exists_full_forcing_weak_response (q : XiZeroCopy) (minusBranch : Bool) :
    ∃ h : energyDomain, WeakSolution q minusBranch h := by
  obtain ⟨x,hx⟩ := (physical_resolvent_bijective q minusBranch).2 (-forcingVector q minusBranch)
  have hrange : (x : Space) ∈ (formEmbeddingCovariance embedding).range := by
    simpa only [energyOperator,friedrichsFormOperator,closedDenseInverse_domain] using x.property
  obtain ⟨y,hy⟩ := hrange
  have hAy : energyOperator x = y := by
    have happ := friedrichsFormOperator_apply_covariance embedding embedding_injective embedding_dense y
    have he : x = ⟨formEmbeddingCovariance embedding y,happ.1⟩ := Subtype.ext hy.symm
    exact (congrArg energyOperator he).trans happ.2
  let h : energyDomain := embedding.adjoint y
  have hJ : embedding h = (x : Space) := hy
  have hforce : y - (1-parameter q minusBranch) • embedding h = -forcingVector q minusBranch := by
    change energyOperator x - (1-parameter q minusBranch) • (x : Space) = _ at hx
    rw [hAy,← hJ] at hx
    exact hx
  refine ⟨h,?_⟩
  intro v
  have he := congrArg (fun w : Space => inner ℂ (embedding v) w) hforce
  rw [inner_sub_right,inner_smul_right,inner_neg_right] at he
  change inner ℂ v (embedding.adjoint y) - _ = _
  rw [embedding.adjoint_inner_right]
  exact he

/-- Nonreal physical parameter makes the full energy-domain response unique. -/
theorem full_forcing_weak_response_unique (q : XiZeroCopy) (minusBranch : Bool)
    (h k : energyDomain) (hh : WeakSolution q minusBranch h) (hk : WeakSolution q minusBranch k) :
    h = k := by
  let w : energyDomain := h-k
  have he : inner ℂ w w -(1-parameter q minusBranch)*inner ℂ (embedding w) (embedding w) = 0 := by
    calc
      _ = (inner ℂ w h -(1-parameter q minusBranch)*inner ℂ (embedding w) (embedding h)) -
          (inner ℂ w k -(1-parameter q minusBranch)*inner ℂ (embedding w) (embedding k)) := by
        dsimp [w]
        rw [map_sub,inner_sub_right,inner_sub_right]
        ring
      _ = 0 := by rw [hh w,hk w,sub_self]
  have hi := congrArg Complex.im he
  have hwi : (inner ℂ w w).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) w
  have hji : (inner ℂ (embedding w) (embedding w)).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) (embedding w)
  have hjr : (inner ℂ (embedding w) (embedding w)).re = ‖embedding w‖^2 := by
    simpa using! inner_self_eq_norm_sq (𝕜 := ℂ) (embedding w)
  have hp : (1-parameter q minusBranch).im*‖embedding w‖^2 = 0 := by
    rw [Complex.sub_im,Complex.mul_im,hwi,hji,hjr,mul_zero,zero_add,Complex.zero_im,zero_sub] at hi
    exact neg_eq_zero.mp hi
  have hn : ‖embedding w‖^2 = 0 := (mul_eq_zero.mp hp).resolve_left (physical_shift_nonreal q minusBranch)
  have hj : embedding w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hw : w = 0 := embedding_injective (by simpa only [map_zero] using hj)
  exact sub_eq_zero.mp hw

/-- The constructed unique full angular response, for the original source at an actual Xi copy. -/
def weakResponse (q : XiZeroCopy) (minusBranch : Bool) : energyDomain :=
  (exists_full_forcing_weak_response q minusBranch).choose

theorem weakResponse_spec (q : XiZeroCopy) (minusBranch : Bool) :
    WeakSolution q minusBranch (weakResponse q minusBranch) :=
  (exists_full_forcing_weak_response q minusBranch).choose_spec

end
end RHTower.D4BMModularCore
