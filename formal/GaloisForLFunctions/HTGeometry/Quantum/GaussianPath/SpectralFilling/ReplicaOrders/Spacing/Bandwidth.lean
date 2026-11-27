import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.PhysicalRecords
import GaloisForLFunctions.RHTower.Sieve.SeparatedCount
import Mathlib.Data.Nat.Choose.Bounds

/-! # Bandwidth constraint on the observable replica spacing -/
open Set Filter Finset MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

private theorem occupancy_count (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    Fintype.card (ReplicaMultiplicityIndex I q)=(Fintype.card I+q-1).choose q := by
  rw [Fintype.card_coe,←Finset.map_sym_eq_piAntidiag,Finset.card_map,Finset.sym_univ,Finset.card_univ,
    Sym.card_sym_eq_choose]

/-- All order-q sums lie in an interval q times the one-level bandwidth.
Counting each distinct occupancy once gives the binomial packing bound. -/
private theorem packing {I : Type*} [Fintype I] [DecidableEq I] (E : I → ℝ) (q : ℕ)
    {a b γ : ℝ} (hγ : 0 < γ) (hab : a ≤ b) (he : ∀ i, E i ∈ Icc a b)
    (hg : ∀ p z : ReplicaMultiplicityIndex I q, p≠z →
      γ ≤ |replicaMultiplicityEnergy E p.val-replicaMultiplicityEnergy E z.val|) :
    (((Fintype.card I+q-1).choose q:ℕ):ℝ) ≤ (q:ℝ)*(b-a)/γ+1 := by
  classical
  let F (p : ReplicaMultiplicityIndex I q) := replicaMultiplicityEnergy E p.val
  have hin (p : ReplicaMultiplicityIndex I q) : (q:ℝ)*a ≤ F p ∧ F p ≤ (q:ℝ)*a+q*(b-a) := by
    have hs : ∑ i, (p.val i:ℝ) = q := by exact_mod_cast (Finset.mem_piAntidiag.mp p.property).1
    constructor
    · rw [←hs,Finset.sum_mul]
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (he i).1 (Nat.cast_nonneg _)
    · calc _ ≤ ∑ i, (p.val i:ℝ)*b :=
             sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (he i).2 (Nat.cast_nonneg _)
           _ = _ := by rw [←Finset.sum_mul,hs]; ring
  have h := RHTower.Sieve.card_le_of_separated (s:=univ) (u:=F) hγ
    (mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hab)) (fun i _ j _ => hg i j) (fun i _ => hin i)
  simpa only [Finset.card_univ,occupancy_count] using h

/-- The observed and deterministic spacing certificate, at every order on
one frozen chain, obeys the bandwidth constraint of all distinct sums. -/
theorem gaussian_spacing_bandwidth :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ q : ℕ, let B := (D+q-1).choose q
        (B:ℝ) ≤ (q:ℝ)*circuitHamiltonianSpectralWidth H/recordGap k E q+1 := by
  filter_upwards [gaussian_record_gaps] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H E q B
  let e := H.2.isHermitian.eigenvalues
  let e₀ := univ.inf' univ_nonempty e
  let e₁ := univ.sup' univ_nonempty e
  have hE (i) : E i ∈ Icc e₀ e₁ :=
    ⟨Finset.inf'_le e (mem_univ ((qubitConfigFin K).symm i)),
      Finset.le_sup' e (mem_univ ((qubitConfigFin K).symm i))⟩
  have hab : e₀ ≤ e₁ := (hE 0).1.trans (hE 0).2
  simpa only [Fintype.card_fin] using packing E q (recordGap_pos k E q) hab hE (hk q)

/-- The permutation floor upper estimate times the occupied cardinality
is at least one, including for orders greater than the number of levels. -/
theorem inverse_factorial_le_multisets {D : ℕ} (hD : 0 < D) (q : ℕ) :
    (D:ℝ)^q/(q.factorial:ℝ) ≤ (((D+q-1).choose q:ℕ):ℝ) := by
  simpa only [show D+q-1+1-q=D by omega] using (Nat.pow_le_choose q (D+q-1) (α:=ℝ))

#print axioms gaussian_spacing_bandwidth
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
