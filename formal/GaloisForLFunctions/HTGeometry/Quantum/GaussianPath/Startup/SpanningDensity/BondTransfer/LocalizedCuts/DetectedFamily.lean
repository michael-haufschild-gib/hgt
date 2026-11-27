import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.Propagation.BondReporter
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.DetectedCuts

/-! # Counting detectable crossed bonds with a fixed localization radius -/
open Matrix Finset Real RHTower GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon
noncomputable section
variable {n : ℕ}

/-- A quarter-error circuit cannot cross many detectable edges with the same
orientation. Coloring by distance isolates the tests, and truncating at p
neighbor layers costs only a p-th power of the local interaction mass. -/
theorem local_detected_cut_count (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (p k : ℕ) {t r B : ℝ} (ht : 0≤t) (hr : 0<r) (hB : 0≤B) (cap : ∀ l, |u l|≤B)
    (hlocal : 2*(2*(21*(2*(p:ℝ)+2))*B)^p*t^p≤r/16) (hk : 16<(k:ℝ)*r)
    (z : ℂ) (hz : ‖z‖=1) (hfit : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4) :
    (detectable c u t r).card<2*(2*p+4)*(k*k) := by
  classical
  by_contra! hm
  let m := k*k
  have hkpos : 0<k := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h,Nat.cast_zero,zero_mul] at hk
    norm_num at hk
  obtain ⟨S,e,hi,hcut,he,hsep⟩ := oriented_subfamily (by omega : 0<2*p+4) c
    (detectable c u t r) (filter_subset ..) hm
  let U := unitaryEvolution (pathHamiltonian u) t
  let M (i : Fin m) := bondNeighborhood (e i) (p+1)
  have hd (i j : Fin m) (hij : i≠j) : Disjoint (M i) (M j) := by
    apply disjoint_left.mpr
    intro v h₁ h₂
    have hv := bondNeighborhood_range _ _ h₁
    have hv' := bondNeighborhood_range _ _ h₂
    have hne : (e i).val≠(e j).val := fun h => hij (hi (Fin.ext h))
    rcases lt_or_gt_of_ne hne with h|h
    · have := hsep i j h
      omega
    · have := hsep j i h
      omega
  choose X hs hnorm herr using fun i : Fin m => local_bond_reporter u (e i) p t ht
  let F (i : Fin m) := Uᴴ*bondOutput (e i)*U*bondInput (e i)
  have hleak (i : Fin m) : ‖F i-X i‖≤r/16 := by
    have hE := bondNeighborhood_mass (e i) p u hB (fun l _ => cap l)
    have h := pow_le_pow_left₀ (mul_nonneg zero_le_two (sum_nonneg fun _ _ => abs_nonneg _))
      (mul_le_mul_of_nonneg_left hE zero_le_two) p
    rw [←mul_assoc 2 (21*(2*(p:ℝ)+2)) B] at h
    exact (herr i).trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h zero_le_two) (pow_nonneg ht _)).trans hlocal)
  let d : ℂ := Fintype.card (Fin (n+2)→Bool)
  have hmean (i : Fin m) : r-r/16≤‖(X i).trace/d‖ := by
    have hh := (mem_filter.mp (he i).1).2.le
    change r≤|(d⁻¹*(unitaryEvolution (pathHamiltonian u) (-t)*bondOutput (e i)*U*bondInput (e i)).trace).re| at hh
    rw [EigenlineSignals.adjoint_evolution ⟨_,isSelfAdjoint_pathHamiltonian u⟩ t] at hh
    have h₁ : r≤‖d⁻¹*(F i).trace‖ := hh.trans (Complex.abs_re_le_norm _)
    have h₂ := (norm_normalizedTrace_sub_le_l2OpNorm (F i) (X i)).trans (hleak i)
    have h₃ := norm_sub_norm_le (d⁻¹*(F i).trace) (d⁻¹*(X i).trace)
    change ‖d⁻¹*(F i).trace-d⁻¹*(X i).trace‖≤r/16 at h₂
    rw [div_eq_mul_inv,mul_comm (X i).trace]
    linarith only [h₁,h₂,h₃]
  have hU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
  have hov := packet_overlap (m:=m) (Nat.mul_pos hkpos hkpos) U C.eval.val hU C.eval.2
    (fun i => bondOutput (e i)) (fun i => bondInput (e i)) X M
    (fun i => finitePauliMatrix_isHermitian _) (fun i => bond_input_hermitian _)
    (fun i => (norm_finitePauliMatrix _).le) (fun i => bond_input_norm _) hnorm hs hd
    (by linarith only [hr] : 0<r-r/16) hmean hleak
    (fun i j hij => oriented_bond_orthogonal C S hcut (hi.ne hij) (he i).2.1 (he j).2.1 (he i).2.2)
  have hlow := overlap_of_fit _ _ hU C.eval.2 z hz hfit
  have hhigh := overlap_of_square_packets hr (by norm_num : (0:ℝ)<1/2)
    (by linarith only [hr] : r/16≤r/4) (by linarith only [hr] : r/16≤r*(1/2)/8)
    (by linarith only [hk]) _ hov
  linarith only [hhigh,hlow]

#print axioms local_detected_cut_count
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
