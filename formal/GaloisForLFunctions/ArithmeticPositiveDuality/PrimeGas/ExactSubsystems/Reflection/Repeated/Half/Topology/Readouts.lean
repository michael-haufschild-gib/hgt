import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Topology.Bands
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Mixed.Holes

/-! # Optimal dimension for comparing continuous unlabeled measurements under reflection -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Topology

open Finset Metric _root_.HTGeometry

abbrev Readout (n q : ℕ) := (Fin n → ℝ) → (Fin q → ℝ)

def Unlabeled {n q : ℕ} (F : Readout n q) := ∀ E G, Matches E G → F E=F G

/-- Fewer than half the spectral dimensions cannot separate every asymmetric list from
its reversal, even with arbitrary continuous nonlinear measurements. -/
theorem readout_collision {n q : ℕ} (hq : q < cutoff n) (F : Readout n q) (hc : Continuous F)
    (hu : Unlabeled F) : ∃ E : Fin n → ℝ, (∑ i, E i)=0 ∧ ¬Reflects E ∧ F E=F (fun i => -E i) := by
  let p := n-(2*q+3)
  have size : Fintype.card (Bands q p)=n := by
    simp only [Bands,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]
    unfold p cutoff at *
    omega
  let e := Fintype.equivFinOfCardEq size
  let A := fun (z : EuclideanSpace ℝ (Fin (q+1))) (i : Fin n) => levels z (e.symm i)
  have continuousA : Continuous A := continuous_pi fun i => levels_continuous (e.symm i)
  let score := fun z => WithLp.toLp 2 (F (A z))
  have hs : Continuous score := (PiLp.continuous_toLp 2 (fun _ : Fin q => ℝ)).comp (hc.comp continuousA)
  obtain ⟨z,hz,hEq⟩ := BorsukUlam.borsuk_ulam score hs.continuousOn
  have transfer : Matches (levels (p := p) z) (A z) :=
    ⟨e,fun x => by change levels z x = levels z (e.symm (e x)); rw [e.symm_apply_apply]⟩
  have reverse : Matches (A (-z)) (fun i => -A z i) := by
    refine ⟨(e.symm.trans (swap q p)).trans e,fun i => ?_⟩
    change levels (-z) (e.symm i) = -levels z (e.symm (e (swap q p (e.symm i))))
    rw [e.symm_apply_apply,antipodal]
  have same : F (A z)=F (A (-z)) := congrArg (WithLp.ofLp : EuclideanSpace ℝ (Fin q) → Fin q → ℝ) hEq
  refine ⟨A z,(Equiv.sum_comp e.symm (levels z)).trans (sum_levels z),?_,same.trans (hu _ _ reverse)⟩
  rintro ⟨d,hd⟩
  exact asymmetric hz ⟨d,(Mixed.pairs_congr transfer d).mpr hd⟩

/-- A fixed temperature schedule needs only the unlabeled input list. -/
def thermal {n q : ℕ} (t : Fin q → ℝ) : Readout n q := fun E j => finiteGibbsPartition (t j) E

theorem thermal_continuous {n q : ℕ} (t : Fin q → ℝ) : Continuous (thermal (n := n) t) := by
  apply continuous_pi
  intro j
  change Continuous (fun E : Fin n → ℝ => ∑ i, Real.exp (-(t j)*E i))
  exact continuous_finsetSum univ fun i _ => Real.continuous_exp.comp ((continuous_const (y := -(t j))).mul (continuous_apply i))

theorem thermal_unlabeled {n q : ℕ} (t : Fin q → ℝ) : Unlabeled (thermal (n := n) t) :=
  fun _ _ h => funext fun j => partition_congr h (t j)

/-- The obstruction holds for any choice of real probe temperatures, including noninteger
and negative temperatures. -/
theorem arbitrary_temperatures {n q : ℕ} (hq : q < cutoff n) (t : Fin q → ℝ) :
    ∃ E : Fin n → ℝ, (∑ i, E i)=0 ∧ ¬Reflects E ∧
      ∀ j, finiteGibbsPartition (t j) E=finiteGibbsPartition (-(t j)) E := by
  obtain ⟨E,hm,hn,eq⟩ := readout_collision hq (thermal t) (thermal_continuous t) (thermal_unlabeled t)
  exact ⟨E,hm,hn,fun j => by rw [partition_negative]; exact congrFun eq j⟩

def Resolves (n q : ℕ) := ∃ F : Readout n q, Continuous F ∧ Unlabeled F ∧ ∀ E, (∑ i, E i)=0 →
  (F E=F (fun i => -E i) ↔ Reflects E)

/-- The first integer heat traces meet the universal lower bound for continuous readouts
whose values on a spectrum and its negative are compared. -/
theorem resolves_iff (n q : ℕ) : Resolves n q ↔ cutoff n ≤ q := by
  constructor
  · rintro ⟨F,hc,hu,complete⟩
    by_contra! small
    obtain ⟨E,hm,hn,eq⟩ := readout_collision small F hc hu
    exact hn ((complete E hm).mp eq)
  · intro bound
    let t := fun j : Fin q => (j.val : ℝ)+1
    refine ⟨thermal t,thermal_continuous t,thermal_unlabeled t,fun E hm => ?_⟩
    have center := centered_eq_of_sum_zero hm
    constructor
    · intro eq
      apply (centered_heat_iff_reflects E).mp
      rw [center,Fintype.card_fin]
      intro j hj hjn
      let i : Fin q := ⟨j-1,by omega⟩
      have realj : t i=(j : ℝ) := by
        change ((j-1 : ℕ) : ℝ)+1=(j : ℝ)
        exact_mod_cast (show j-1+1=j by omega)
      rw [partition_negative E]
      have hit := congrFun eq i
      change finiteGibbsPartition (t i) E=finiteGibbsPartition (t i) (fun x => -E x) at hit
      rwa [realj] at hit
    · intro hr
      have pair := (reflects_iff_centered_pair E).mp hr
      rw [center,pairs_iff_matches] at pair
      funext i
      simpa only [thermal,zero_sub] using partition_congr pair (t i)

#print axioms readout_collision
#print axioms arbitrary_temperatures
#print axioms resolves_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Topology
