import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.DisjointMoments
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction
import GaloisForLFunctions.QuantumAlg.Util.MatrixExpInvolution

/-! # Partition function of a layer of disjoint Pauli interactions -/
open Matrix Finset NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section
variable {N : ℕ} {ι : Type*} [DecidableEq ι]
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem exp_supported {S : Finset (Fin N)} {H : Reg N} (h : IsSiteSupported S H) :
    IsSiteSupported S (exp H) := by
  have hs := isSiteSupported_unitaryEvolution (IsSiteSupported.complex_smul Complex.I h) 1
  simpa only [unitaryEvolution,one_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg] using hs

/-- The normalized trace of the exponential factors over disjoint supports,
with no commutation condition inside any one support. -/
theorem disjoint_trace_factors (s : Finset ι) (S : ι → Finset (Fin N)) (F : ι → Reg N)
    (z : ι → ℂ) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hp : ∀ i ∈ s, IsSiteSupported (S i) (F i))
    (hz : ∀ i ∈ s, (exp (F i)).trace=z i*(Fintype.card (Fin N → Bool):ℂ)) :
    (exp (∑ i ∈ s, F i)).trace = (Fintype.card (Fin N → Bool):ℂ) * ∏ i ∈ s, z i := by
  classical
  have hs (u : Finset ι) (T : Finset (Fin N))
      (h : ∀ i ∈ u, IsSiteSupported T (F i)) : IsSiteSupported T (∑ i ∈ u, F i) := by
    induction u using Finset.induction_on with
    | empty => simpa only [sum_empty] using IsSiteSupported.zero T
    | @insert i v hi ih =>
      rw [sum_insert hi]
      exact (h i (mem_insert_self ..)).add (ih fun j hj => h j (mem_insert_of_mem hj))
  let d : ℂ := Fintype.card (Fin N → Bool)
  have hd₀ : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  change (exp (∑ i ∈ s, F i)).trace=d*_
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,exp_zero,Matrix.trace_one,prod_empty,mul_one,d]
  | @insert i s hi ih =>
    have hin := mem_insert_self i s
    have inc (j : ι) (hj : j ∈ s) := mem_insert_of_mem (b:=i) hj
    have hd' : Disjoint (S i) (s.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro v hv h
      obtain ⟨j,hj,hv'⟩ := mem_biUnion.mp h
      exact Finset.disjoint_left.mp (hd i hin j (inc j hj) (fun e => hi (e ▸ hj))) hv hv'
    have h₁ := hp i hin
    have h₂ := hs s (s.biUnion S) fun j hj =>
      IsSiteSupported.mono (fun _ hk => mem_biUnion.mpr ⟨j,hj,hk⟩)
        (hp j (inc j hj))
    have hcomm := commute_of_isSiteSupported_disjoint hd' h₁ h₂
    have hfac := SpanningDensity.FixedHorizon.disjoint_trace_product hd' (exp_supported h₁) (exp_supported h₂)
    change d*(exp (F i)*exp (∑ j ∈ s, F j)).trace = _ at hfac
    have hrest := ih (fun j hj k hk => hd j (inc j hj) k (inc k hk))
      (fun j hj => hp j (inc j hj)) (fun j hj => hz j (inc j hj))
    rw [sum_insert hi,prod_insert hi,QuantumAlg.exp_add_of_commute_ℂ hcomm]
    apply mul_left_cancel₀ hd₀
    rw [hfac,hz i hin,hrest]
    change (z i*d)*(d*_) = _
    ring

/-- Each disjoint traceless involution contributes one hyperbolic cosine
to the normalized trace at complex field strength. -/
theorem disjoint_complex_partition (s : Finset ι) (S : ι → Finset (Fin N)) (P : ι → Reg N)
    (b : ι → ℂ) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hp : ∀ i ∈ s, IsSiteSupported (S i) (P i))
    (hinv : ∀ i ∈ s, P i*P i=1) (htr : ∀ i ∈ s, (P i).trace=0) :
    (exp (∑ i ∈ s, (b i) • P i)).trace =
      (Fintype.card (Fin N → Bool):ℂ) * ∏ i ∈ s, Complex.cosh (b i) := by
  apply disjoint_trace_factors s S _ _ hd (fun i hi => IsSiteSupported.complex_smul (b i) (hp i hi))
  intro i hi
  rw [QuantumAlg.exp_smul_of_mul_self_eq_one _ (hinv i hi),Matrix.trace_add,
    Matrix.trace_smul,Matrix.trace_smul,htr i hi,smul_zero,add_zero,Matrix.trace_one]
  rfl

/-- Independent sites factor the normalized trace. Each traceless involution
contributes exactly one hyperbolic cosine, at every real temperature. -/
theorem disjoint_partition (s : Finset ι) (S : ι → Finset (Fin N)) (P : ι → Reg N)
    (b : ι → ℝ) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hp : ∀ i ∈ s, IsSiteSupported (S i) (P i))
    (hinv : ∀ i ∈ s, P i*P i=1) (htr : ∀ i ∈ s, (P i).trace=0) :
    (exp (∑ i ∈ s, (b i:ℂ) • P i)).trace =
      (Fintype.card (Fin N → Bool):ℂ) * ∏ i ∈ s, Complex.cosh (b i) :=
  disjoint_complex_partition s S P (fun i => (b i:ℂ)) hd hp hinv htr

#print axioms disjoint_partition
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
