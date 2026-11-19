import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringHirotaFlow
import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScatteringTau
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# A globally positive determinant solving the cubic Hirota hierarchy

The determinant of identity plus the weighted coherence matrix equals
the exponential wave expansion at every point. This identifies its
bilinear derivatives and supplies a uniform lower bound, even when
several labels carry the same momentum.
-/

noncomputable section
open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScattering
open CubicHierarchy CubicHierarchy.WaveList HilbertMetric.CauchyDephasing

private theorem subset_powerset {α : Type*} [DecidableEq α] (xs : List α) (hx : xs.Nodup)
    (F : List α → ℝ) (G : Finset α → ℝ) (agree : ∀ a, a.Sublist xs → F a=G a.toFinset) :
    WaveList.subsetSum xs F=∑ s ∈ xs.toFinset.powerset, G s := by
  induction xs generalizing F G with
  | nil => simpa only [WaveList.subsetSum,List.toFinset_nil,powerset_empty,sum_singleton] using agree [] (.refl _)
  | cons x xs ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp hx
    rw [WaveList.subsetSum,List.toFinset_cons,sum_powerset_insert (fun h => fresh (List.mem_toFinset.mp h))]
    exact congrArg₂ (·+·) (ih nd F G fun a h => agree a (h.cons x))
      (ih nd (fun a => F (x::a)) (fun s => G (insert x s)) fun a h => by
        simpa only [List.toFinset_cons] using agree (x::a) (h.cons_cons x))

private theorem phase_rates {n : ℕ} (r : Fin n → ℝ) :
    phase (List.ofFn (fun i => Real.exp (r i)))=(Matrix.of fun i j => coherence (r i) (r j)).det := by
  induction n with
  | zero => simp [phase,pairWeight,pairDen,List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ,phase_cons,coherence_det_cons,ih (fun i => r i.succ)]
    congr 1
    simp only [product,List.map_ofFn,List.prod_ofFn,Function.comp_def]
    apply prod_congr rfl
    intro i _
    simp only [exchange,contrast,div_pow]
    rw [add_comm (Real.exp (r 0)),show (Real.exp (r 0)-Real.exp (r i.succ))^2=
      (Real.exp (r i.succ)-Real.exp (r 0))^2 by ring]

private theorem waveTerm_list {n : ℕ} (r a : Fin n → ℝ) (l : List (Fin n)) (hl : l.Nodup) :
    amplitude (fun i => Real.exp (r i)) (fun i => Real.exp (a i)) l=waveTerm r a l.toFinset := by
  let s := l.toFinset
  let e := s.orderIsoOfFin rfl
  let idx := fun i : Fin s.card => (e i : Fin n)
  let sorted := List.ofFn idx
  have mono : Function.Injective idx := Subtype.val_injective.comp e.injective
  have perm : l.Perm sorted := by
    apply (List.perm_ext_iff_of_nodup hl (List.nodup_ofFn_ofInjective mono)).mpr
    intro z
    rw [List.mem_ofFn]
    constructor
    · intro hz
      let v : s := ⟨z,List.mem_toFinset.mpr hz⟩
      exact ⟨e.symm v,congrArg Subtype.val (e.apply_symm_apply v)⟩
    · rintro ⟨i,rfl⟩
      exact List.mem_toFinset.mp (e i).property
  rw [amplitude,phase_perm (perm.map _),product,(perm.map _).prod_eq]
  simp only [sorted,List.map_ofFn,Function.comp_def,List.prod_ofFn,phase_rates,coherence_det_eq_scattering]
  exact mul_comm _ _

/-- Propagate each log-amplitude with the positive cubic momentum. -/
def evolvingAmplitude {n : ℕ} (r a : Fin n → ℝ) (x t : ℝ) (i : Fin n) :=
  a i+(Real.exp (r i)*x+Real.exp (r i)^3*t)

def determinantFlow {n : ℕ} (r a : Fin n → ℝ) (x t : ℝ) :=
  (1+waveMatrix r (evolvingAmplitude r a x t)).det

/-- The analytic tau function is exactly the project coherence determinant
at all space-time points and with arbitrary log-momenta and log-amplitudes. -/
theorem determinant_eq_tau {n : ℕ} (r a : Fin n → ℝ) (x t : ℝ) :
    determinantFlow r a x t=tau (fun i => Real.exp (r i)) (fun i => Real.exp (a i)) (List.finRange n) x t := by
  let b := evolvingAmplitude r a x t
  have h : WaveList.subsetSum (List.finRange n)
      (amplitude (fun i => Real.exp (r i)) (fun i => Real.exp (b i))) =
      ∑ s : Finset (Fin n), waveTerm r b s := by
    simpa only [List.toFinset_finRange,powerset_univ] using
      subset_powerset (List.finRange n) (List.nodup_finRange n) _ (waveTerm r b)
        (fun l h => waveTerm_list r b l (h.nodup (List.nodup_finRange n)))
  rw [determinantFlow,tau_determinant,← h]
  change WaveList.subsetSum _ (amplitude _ (fun i => Real.exp (b i)))=WaveList.subsetSum _ (amplitude _ _)
  congr 2
  funext i
  exact Real.exp_add _ _

/-- All five bilinear PDEs hold on a single everywhere-positive determinant. -/
theorem determinant_solves_hirota {n : ℕ} (r a : Fin n → ℝ) (w : Weights) (x t : ℝ) :
    1≤determinantFlow r a x t ∧ hirota w (determinantFlow r a) x t=0 := by
  refine ⟨tau_at_least_one _ _,?_⟩
  rw [show determinantFlow r a=tau (fun i => Real.exp (r i)) (fun i => Real.exp (a i))
    (List.finRange n) from funext fun xx => funext fun tt => determinant_eq_tau r a xx tt]
  exact tau_solves_hirota w (fun i => ⟨Real.exp (r i),Real.exp_pos _⟩) _ _ _ _

#print axioms determinant_eq_tau
#print axioms determinant_solves_hirota
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScattering
