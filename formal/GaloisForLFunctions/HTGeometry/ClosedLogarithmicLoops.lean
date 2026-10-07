import GaloisForLFunctions.Bottcher.WindDynamics
import Mathlib.Analysis.Normed.Group.Bounded

/-!+# Closed logarithmic lifts of finite packets

Zero degree is exactly the condition making an exponential path lift close.
Finitely many such lifts fit inside one disk, with the same logarithmic basepoint.
-/

open Topology unitInterval Set
open Pi1CMinusZero

namespace GaloisForLFunctions.HTGeometry

/-- A degree-zero loop in the punctured plane has a closed logarithmic lift at zero. -/
theorem exists_closed_log_lift_of_degZ_eq_zero (p : Path one_cs one_cs)
    (hp : degZ ⟦p⟧ = 0) :
    ∃ L : Path (0 : ℂ) 0, ∀ t : I, Complex.exp (L t) = (p t : ℂ) := by
  let Γ : C(I, ℂ) := covexp.liftPath p (e0 : ℂ) (p.source.trans e0.2.symm)
  have h0 : Γ 0 = 0 := covexp.liftPath_zero p (e0 : ℂ) _
  have h1 : Γ 1 = 0 := by
    change (degClass ⟦p⟧ : ℂ) = 0
    rw [degOfFiber_spec]
    change (degZ ⟦p⟧ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0
    rw [hp]
    simp
  refine ⟨⟨Γ, h0, h1⟩, fun t => ?_⟩
  exact congrArg Subtype.val
    (congr_fun (covexp.liftPath_lifts p (e0 : ℂ) (p.source.trans e0.2.symm)) t)

/-- A finite degree-zero loop packet admits closed logarithmic lifts in one disk. -/
theorem exists_bounded_closed_log_lift_packet {ι : Type*} [Finite ι]
    (p : ι → Path one_cs one_cs) (hp : ∀ i, degZ ⟦p i⟧ = 0) :
    ∃ M : ℝ, 0 < M ∧ ∃ L : ι → Path (0 : ℂ) 0,
      ∀ i t, ‖L i t‖ < M ∧ Complex.exp (L i t) = (p i t : ℂ) := by
  choose L hL using fun i => exists_closed_log_lift_of_degZ_eq_zero (p i) (hp i)
  have hcompact : IsCompact (⋃ i, range (L i)) :=
    isCompact_iUnion fun i => isCompact_range (L i).continuous
  obtain ⟨M, hM, hbound⟩ := hcompact.isBounded.exists_pos_norm_lt
  refine ⟨M, hM, L, fun i t => ⟨?_, hL i t⟩⟩
  exact hbound _ (mem_iUnion.mpr ⟨i, mem_range_self t⟩)

/-- Finite normalized degree-zero packets lift at a common logarithm of any nonzero basepoint. -/
theorem exists_bounded_closed_log_lift_packet_at_base {ι : Type*} [Finite ι]
    {b : Cs} (p : ι → Path b b)
    (hp : ∀ i, degZ ⟦Bottcher.transLoop (fun z : Cs => (z : ℂ))
      continuous_subtype_val (fun z => z.2) (p i)⟧ = 0) :
    ∃ M : ℝ, 0 < M ∧ ∃ w0 : ℂ, ‖w0‖ < M ∧ Complex.exp w0 = (b : ℂ) ∧
      ∃ L : ι → Path w0 w0,
        ∀ i t, ‖L i t‖ < M ∧ Complex.exp (L i t) = (p i t : ℂ) := by
  obtain ⟨_, _, L0, hL0⟩ := exists_bounded_closed_log_lift_packet
    (fun i => Bottcher.transLoop (fun z : Cs => (z : ℂ))
      continuous_subtype_val (fun z => z.2) (p i)) hp
  let w0 := Complex.log (b : ℂ)
  have hw0 : Complex.exp w0 = (b : ℂ) := Complex.exp_log b.2
  let L (i : ι) : Path w0 w0 :=
    { toFun := fun t => w0 + L0 i t
      continuous_toFun := continuous_const.add (L0 i).continuous
      source' := by rw [(L0 i).source, add_zero]
      target' := by rw [(L0 i).target, add_zero] }
  have hc : IsCompact ({w0} ∪ ⋃ i, range (L i)) :=
    isCompact_singleton.union (isCompact_iUnion fun i => isCompact_range (L i).continuous)
  obtain ⟨M, hM, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  refine ⟨M, hM, w0, hbound _ (Or.inl rfl), hw0, L, fun i t => ⟨?_, ?_⟩⟩
  · exact hbound _ (Or.inr (mem_iUnion.mpr ⟨i, mem_range_self t⟩))
  · change Complex.exp (w0 + L0 i t) = _
    rw [Complex.exp_add, hw0, (hL0 i t).2]
    change (b : ℂ) * ((p i t : ℂ) / (b : ℂ)) = (p i t : ℂ)
    exact mul_div_cancel₀ _ b.2

end GaloisForLFunctions.HTGeometry
