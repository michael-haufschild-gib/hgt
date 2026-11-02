import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineNullseries
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PrescribedSplineQuartets

/-!
# Exact spline quartets with bounded local density

The sparse exact nullseries retains unit multiplicities and an unattained
positive width. Sign and conjugation give distinct symmetric quartets,
at most twelve atoms per unit height interval, and mixed natural-cone
coupling bounded by twenty.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma prescribedSplineQuartet_core_interval {ι : Type*} (z : ι → ℂ)
    (i : ι) (b c : Bool) (T : ℝ)
    (hi : (prescribedSplineQuartetAtom z (i,b,c)).im ∈ Set.Icc T (T+1)) :
    (z i).im ∈ Set.Icc (if b=c then T else -T-1) ((if b=c then T else -T-1)+1) := by
  cases b <;> cases c <;>
    simp [prescribedSplineQuartetAtom,Set.mem_Icc] at hi ⊢ <;>
    constructor <;> linarith only [hi.1,hi.2]

/-- Sign and conjugation multiply a uniform three-node height count by at most four. -/
lemma prescribedSplineQuartet_unit_interval_embedding {ι : Type*} (z : ι → ℂ)
    (hcount : ∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3))
    (T : ℝ) : Nonempty
      ({i : ι × Bool × Bool // (prescribedSplineQuartetAtom z i).im ∈ Set.Icc T (T+1)} ↪ Fin 12) := by
  classical
  let e (S : ℝ) : {i : ι // (z i).im ∈ Set.Icc S (S+1)} ↪ Fin 3 := Classical.choice (hcount S)
  let A := {i : ι × Bool × Bool // (prescribedSplineQuartetAtom z i).im ∈ Set.Icc T (T+1)}
  let f : A → Fin 3 × Bool × Bool := fun i =>
    (e (if i.val.2.1=i.val.2.2 then T else -T-1)
      ⟨i.val.1,prescribedSplineQuartet_core_interval z i.val.1 i.val.2.1 i.val.2.2 T i.property⟩,
      i.val.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨i,b,c⟩,hi⟩ ⟨⟨j,b',c'⟩,hj⟩ he
    have hbc : (b,c)=(b',c') := congrArg Prod.snd he
    have hb := congrArg Prod.fst hbc
    have hc := congrArg Prod.snd hbc
    dsimp only at hb hc
    subst b'
    subst c'
    have hh := congrArg Prod.fst he
    have hij : i=j := congrArg Subtype.val ((e (if b=c then T else -T-1)).injective hh)
    subst j
    rfl
  have hcard : Fintype.card (Fin 3 × Bool × Bool)=12 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  let g : (Fin 3 × Bool × Bool) ↪ Fin 12 := {
    toFun := fun j => ⟨(Fintype.equivFin (Fin 3 × Bool × Bool) j).val,by
      rw [← hcard]
      exact (Fintype.equivFin (Fin 3 × Bool × Bool) j).isLt⟩
    inj' := by
      intro i j he
      apply (Fintype.equivFin (Fin 3 × Bool × Bool)).injective
      exact Fin.ext (congrArg (fun v : Fin 12 => v.val) he)
  }
  exact ⟨(⟨f,hf⟩ : A ↪ Fin 3 × Bool × Bool).trans g⟩

/-- Exact unit-multiplicity spline quartets have unattained positive width,
bounded natural two-prime cone coupling, and at most twelve atoms per unit height interval. -/
theorem exists_two_prime_sparse_prescribed_spline_cone_model {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ),
      Function.Injective z ∧ Function.Injective (prescribedSplineQuartetAtom z) ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧ (∀ i, 1 ≤ (z i).im) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, splineMomentCoefficient (z i) ≠ 0) ∧
      Summable (fun i => ‖splineMomentCoefficient (z i)‖) ∧
      (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2 ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ T : ℝ, Nonempty ({i : ι // (z i).im ∈ Set.Icc T (T+1)} ↪ Fin 3)) ∧
      (∀ T : ℝ, Nonempty ({i : ι × Bool × Bool //
        (prescribedSplineQuartetAtom z i).im ∈ Set.Icc T (T+1)} ↪ Fin 12)) ∧
      (∀ t : ℝ, Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i))) ∧
      (∀ t : PositiveCone (Real.log p) (Real.log q),
        HasSum (fun i => splineMomentCoefficient (z i)*Complex.exp ((t.val : ℂ)*z i)) 0) ∧
      (∀ m n : ℕ, ‖prescribedSplineQuartetKernel z (m*Real.log p+n*Real.log q)-
        prescribedSplineQuartetKernel z (m*Real.log p)-prescribedSplineQuartetKernel z (n*Real.log q)+
        prescribedSplineQuartetKernel z 0‖ ≤ 20) := by
  obtain ⟨ι,hι,z,hinj,hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hlocal,hall,hzero⟩ :=
    exists_two_prime_sparse_prescribed_spline_nullseries hp hq hpq hd hdD
  refine ⟨ι,hι,z,hinj,prescribedSplineQuartetAtom_injective hinj
    (fun i => hd.trans_le (hstrip i).1) (fun i => zero_lt_one.trans_le (him i)),
    hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hlocal,
    prescribedSplineQuartet_unit_interval_embedding z hlocal,hall,hzero,?_⟩
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  exact prescribed_spline_quartet_coupling_le_twenty z ha hb hs hmass
    (fun i => hd.le.trans (hstrip i).1) hzero

#print axioms prescribedSplineQuartet_unit_interval_embedding
#print axioms exists_two_prime_sparse_prescribed_spline_cone_model
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
