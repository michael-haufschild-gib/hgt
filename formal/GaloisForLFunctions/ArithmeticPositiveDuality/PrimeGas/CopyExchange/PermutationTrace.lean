import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleWeights
import GaloisForLFunctions.HTGeometry.LatticeL2Shift
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Permuted heat traces of finitely many prime gases

On the full tuple space the trace of a permutation times heat is the product
of the zeta factors of its cycles. On fixed basis labels the same product
is an ordinary trace all the way to the shortest-cycle boundary.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open GaloisForLFunctions.HTGeometry ContinuousLinearMap
open scoped Classical

abbrev LabelSpace (J : Type*) := lp (fun _ : J => ℂ) 2

variable {I : Type*} [Fintype I]

theorem wordHeat_half_norm_sq (s : ℂ) (x : I → ℕ+) : ‖wordHeat (s/2) x‖^2 = ‖wordHeat s x‖ := by
  rw [sq,← norm_mul,← wordHeat_add,add_halves]

theorem wordHeat_half_summable (s : {w : ℂ // 1 < w.re}) :
    Summable (fun x : I → ℕ+ => ‖wordHeat (s.val/2) x‖^2) := by
  simp only [wordHeat_half_norm_sq]
  exact (FamilyContinuationTheory.hasSum_pi_prod (fun (_ : I) n => heat s.val n)
    (fun _ => riemannZeta s.val) (fun _ => heat_hasSum s)
    (fun _ => (heat_abs_summable _).mpr s.property)).2

private def shift (π : Equiv.Perm I) : LabelSpace (I → ℕ+) ≃ₗᵢ[ℂ] LabelSpace (I → ℕ+) :=
  lpDomCongr (p := 2) (by norm_num) (Equiv.arrowCongr π.symm (Equiv.refl ℕ+))

omit [Fintype I] in
private theorem shift_apply (π : Equiv.Perm I) (f : LabelSpace (I → ℕ+)) (x : I → ℕ+) :
    shift π f x = f (x ∘ π) := rfl

private theorem wordHeat_permute (π : Equiv.Perm I) (s : ℂ) (x : I → ℕ+) :
    wordHeat s (x ∘ π) = wordHeat s x := Equiv.prod_comp π (fun i => heat s (x i))

/-- Physical heat propagation followed by a permutation of the copies. -/
def permutedHeat (π : Equiv.Perm I) (s : {w : ℂ // 1 < w.re}) :
    LabelSpace (I → ℕ+) →L[ℂ] LabelSpace (I → ℕ+) :=
  let H := HilbertSchmidt.diagOp (wordHeat (s.val/2)) (wordHeat_half_summable s)
  ((shift π).toLinearIsometry.toContinuousLinearMap ∘L H) ∘L H

theorem permutedHeat_apply (π : Equiv.Perm I) (s : {w : ℂ // 1 < w.re}) (f : LabelSpace (I → ℕ+)) (x : I → ℕ+) :
    permutedHeat π s f x = wordHeat s.val x * f (x ∘ π) := by
  change shift π (HilbertSchmidt.diagOp _ _ (HilbertSchmidt.diagOp _ _ f)) x = _
  rw [shift_apply,HilbertSchmidt.diagOp_apply,HilbertSchmidt.diagOp_apply,← mul_assoc,← wordHeat_add,
    add_halves,wordHeat_permute]

theorem permutedHeat_traceClass (π : Equiv.Perm I) (s : {w : ℂ // 1 < w.re}) :
    (permutedHeat π s).IsTraceClass :=
  ((HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_left _).comp_isTraceClass
    (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

private theorem collapse_fixed (π : Equiv.Perm I) (s : ℂ) :
    (∑' x : I → ℕ+, if x ∘ π = x then wordHeat s x else 0) =
    ∑' x : FixedWord π, wordHeat s x.val := by
  let a (x : I → ℕ+) := if x ∘ π = x then wordHeat s x else 0
  have hs : Function.support a ⊆ Set.range (Subtype.val : FixedWord π → (I → ℕ+)) := by
    intro x hx
    by_cases h : x ∘ π = x
    · exact ⟨⟨x,h⟩,rfl⟩
    · exact (hx (if_neg h)).elim
  change (∑' x, a x) = _
  rw [← Subtype.val_injective.tsum_eq hs]
  exact tsum_congr fun x => if_pos x.property

private theorem diag_trace {J : Type*} [DecidableEq J] (T : LabelSpace J →L[ℂ] LabelSpace J) (hT : T.IsTraceClass) :
    opTrace T = ∑' j, T (lp.single 2 j 1) j := by
  obtain ⟨A,B,hA,hB,hT⟩ := hT
  rw [hT,opTrace_comp_eq_tsum_basis hA hB (HilbertSchmidt.lpBasis J)]
  apply tsum_congr
  intro j
  simp only [HilbertSchmidt.lpBasis_apply,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one]

/-- Full operator trace with an arbitrary copy permutation inserted. -/
theorem permutedHeat_trace (π : Equiv.Perm I) (s : {w : ℂ // 1 < w.re}) :
    opTrace (permutedHeat π s) = cyclePartition π s.val := by
  rw [diag_trace _ (permutedHeat_traceClass π s), ← fixed_sum π s.val (cycleDomain_of_trace π s),
    ← collapse_fixed]
  apply tsum_congr
  intro x
  rw [permutedHeat_apply]
  by_cases h : x ∘ π = x
  · rw [h,if_pos rfl,lp.single_apply_self,mul_one]
  · rw [if_neg h,lp.single_apply_ne _ _ _ h,mul_zero]

private theorem fixed_half (π : Equiv.Perm I) (s : ℂ) (h : InCycleDomain π s) :
    Summable (fun x : FixedWord π => ‖wordHeat (s/2) x.val‖^2) := by
  simpa only [wordHeat_half_norm_sq] using (fixed_summable_iff π s).mpr h

/-- Heat acting on the Hilbert space spanned by fixed basis labels. -/
def fixedHeat (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w}) :
    LabelSpace (FixedWord π) →L[ℂ] LabelSpace (FixedWord π) :=
  let H := HilbertSchmidt.diagOp (fun x : FixedWord π => wordHeat (s.val/2) x.val) (fixed_half π s.val s.property)
  H ∘L H

theorem fixedHeat_apply (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w})
    (f : LabelSpace (FixedWord π)) (x : FixedWord π) :
    fixedHeat π s f x = wordHeat s.val x.val * f x := by
  simp only [fixedHeat,comp_apply,HilbertSchmidt.diagOp_apply,← mul_assoc,← wordHeat_add,add_halves]

theorem fixedHeat_trace (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w}) :
    opTrace (fixedHeat π s) = cyclePartition π s.val := by
  rw [fixedHeat,HilbertSchmidt.opTrace_diagOp_comp,← fixed_sum π s.val s.property]
  exact tsum_congr fun x => by rw [← wordHeat_add,add_halves]

private theorem diag_norm_summable {J : Type*} [DecidableEq J] (T : LabelSpace J →L[ℂ] LabelSpace J)
    (hT : T.IsTraceClass) (w : J → ℂ) (ha : ∀ (f : LabelSpace J) j, T f j = w j * f j) :
    Summable (fun j => ‖w j‖) := by
  obtain ⟨A,B,hA,hB,hT⟩ := hT
  refine (summable_inner_diag_comp hA hB (HilbertSchmidt.lpBasis J)).norm.congr fun j => ?_
  rw [← hT,HilbertSchmidt.lpBasis_apply,lp.inner_single_left]
  simp only [RCLike.inner_apply,map_one,mul_one,ha,lp.single_apply_self]

/-- On the full tuple space permutation insertion preserves the original trace-class boundary. -/
theorem permutedHeat_realization_iff [Nonempty I] (π : Equiv.Perm I) (s : ℂ) :
    (∃ T : LabelSpace (I → ℕ+) →L[ℂ] LabelSpace (I → ℕ+), T.IsTraceClass ∧
      ∀ f x, T f x = wordHeat s x * f (x ∘ π)) ↔ 1 < s.re := by
  constructor
  · rintro ⟨T,⟨A,B,hA,hB,hT⟩,ha⟩
    let R := (shift π.symm).toLinearIsometry.toContinuousLinearMap
    have hTC : (T ∘L R).IsTraceClass := by
      rw [hT]
      exact hA.comp_isTraceClass (hB.comp_right R)
    have hd := diag_norm_summable (T ∘L R) hTC (wordHeat s) (by
      intro f x
      change T (shift π.symm f) x = _
      rw [ha,shift_apply]
      have hcomp : (x ∘ π) ∘ π.symm = x := funext fun j => congrArg x (π.apply_symm_apply j)
      rw [hcomp])
    exact (independent_heat_summable_iff (fun _ : I => s)).mp hd (Classical.arbitrary I)
  · intro hs
    exact ⟨permutedHeat π ⟨s,hs⟩,permutedHeat_traceClass π _,permutedHeat_apply π _⟩

/-- A trace-class realization of the prescribed heat action on fixed labels. -/
def HasFixedHeat (π : Equiv.Perm I) (s : ℂ) : Prop :=
  ∃ T : LabelSpace (FixedWord π) →L[ℂ] LabelSpace (FixedWord π), T.IsTraceClass ∧
    ∀ f x, T f x = wordHeat s x.val * f x

theorem fixedHeat_traceClass_iff (π : Equiv.Perm I) (s : ℂ) : HasFixedHeat π s ↔ InCycleDomain π s := by
  constructor
  · rintro ⟨T,hT,hact⟩
    exact (fixed_summable_iff π s).mp (diag_norm_summable T hT _ hact)
  · intro h
    exact ⟨fixedHeat π ⟨s,h⟩,(HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass
      (HilbertSchmidt.isHilbertSchmidt_diagOp _ _),fixedHeat_apply π ⟨s,h⟩⟩

#print axioms permutedHeat_apply
#print axioms permutedHeat_traceClass
#print axioms permutedHeat_trace
#print axioms permutedHeat_realization_iff
#print axioms fixedHeat_apply
#print axioms fixedHeat_trace
#print axioms fixedHeat_traceClass_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
