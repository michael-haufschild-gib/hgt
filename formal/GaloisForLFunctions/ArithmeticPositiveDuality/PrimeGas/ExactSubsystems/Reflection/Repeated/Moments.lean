import GaloisForLFunctions.HTGeometry.FiniteMomentDivisorReconstruction
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-! # Finite spectra from finitely many unlabeled moment readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated

open Finset
open _root_.HTGeometry (finiteGibbsPartition)

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Matching includes the multiplicity of each measured value. -/
def Matches {I J V : Type*} (f : I → V) (g : J → V) := ∃ e : I ≃ J, ∀ x, f x = g (e x)

def moment (f : X → ℝ) (j : ℕ) := ∑ x, (f x)^j

theorem moment_congr {f : X → ℝ} {g : Y → ℝ} (h : Matches f g) (j : ℕ) :
    moment f j = moment g j := by
  obtain ⟨e,he⟩ := h
  exact Fintype.sum_equiv e _ _ fun x => congrArg (fun v : ℝ => v^j) (he x)

private theorem match_fibers {V : Type*} (f : X → V) (g : Y → V)
    (h : univ.val.map f = univ.val.map g) : Matches f g := by
  classical
  have fiber (v : V) : Fintype.card {x // f x=v} = Fintype.card {y // g y=v} := by
    have eq := congrArg (Multiset.countP (· = v)) h
    rw [Multiset.countP_map,Multiset.countP_map] at eq
    simp only [Fintype.card_subtype]
    exact eq
  let w := fun v => Fintype.equivOfCardEq (fiber v)
  exact ⟨((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight w)).trans (Equiv.sigmaFiberEquiv g),
    fun x => ((w (f x)) ⟨x,rfl⟩).property.symm⟩

private def atoms (f : X → ℝ) : Multiset ℂ := univ.val.map fun x => (f x : ℂ)

private theorem atom_moment (f : X → ℝ) (j : ℕ) :
    ((atoms f).map (fun z => z^j)).sum = (moment f j : ℂ) := by
  simp only [atoms,Multiset.map_map,moment,Complex.ofReal_sum,Complex.ofReal_pow]
  rfl

/-- Orders zero through the size of the first state space characterize equality up to
relabeling, including when the two state spaces initially have different sizes. -/
theorem matches_iff_moments (f : X → ℝ) (g : Y → ℝ) :
    Matches f g ↔ ∀ j ≤ Fintype.card X, moment f j = moment g j := by
  refine ⟨fun h j _ => moment_congr h j,?_⟩
  intro h
  have h₀ := h 0 (Nat.zero_le _)
  simp only [moment,pow_zero,sum_const,card_univ,nsmul_eq_mul,mul_one] at h₀
  have sizes : Fintype.card X = Fintype.card Y := Nat.cast_injective (R := ℝ) h₀
  have eq : atoms f = atoms g := by
    apply multiset_eq_of_powerSum_eq_le
    · simpa only [atoms,Multiset.card_map,← Finset.card_def,card_univ] using sizes
    · intro j hj
      rw [atom_moment,atom_moment]
      exact congrArg (fun r : ℝ => (r : ℂ)) (h j (by simpa only [atoms,Multiset.card_map,← Finset.card_def,card_univ] using hj))
  obtain ⟨e,he⟩ := match_fibers (fun x => (f x : ℂ)) (fun y => (g y : ℂ)) eq
  exact ⟨e,fun x => Complex.ofReal_injective (he x)⟩

theorem partition_moment (E : X → ℝ) (j : ℕ) :
    finiteGibbsPartition (j : ℝ) E = moment (fun x => Real.exp (-E x)) j := by
  refine sum_congr rfl fun i _ => ?_
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- A finite list of integer-temperature heat traces identifies every energy and its multiplicity. -/
theorem matches_iff_partitions (E : X → ℝ) (F : Y → ℝ) :
    Matches E F ↔ ∀ j ≤ Fintype.card X, finiteGibbsPartition (j : ℝ) E = finiteGibbsPartition (j : ℝ) F := by
  simp only [partition_moment,← matches_iff_moments]
  constructor <;> rintro ⟨e,he⟩ <;> refine ⟨e,fun x => ?_⟩
  · exact congrArg (fun r : ℝ => Real.exp (-r)) (he x)
  · exact neg_injective (Real.exp_injective (he x))

#print axioms matches_iff_moments
#print axioms matches_iff_partitions

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated
