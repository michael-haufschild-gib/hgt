import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.ResidueCompression
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw

/-! # Modular diversity of the windings at a first return -/

open Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- No date up to the first s-gate visit may have a winding whose
compressed submultiple already fits the empty circuit after the origin.
The supplied date can have any enclosing arc width R. -/
theorem first_residue_bound {N : ℕ} (H : selfAdjoint (Register N)) {a ε t R : ℝ} (s : ℕ)
    (ha : 0 < a) (hε : ε ∈ Ioo (0:ℝ) (sqrt 2))
    (ht : t ≤ firstVisit H a s ε) (hR : 0 ≤ R) {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (horigin : a*(d:ℝ) ≤ t)
    {b z} (hz : Anchored (fun i => -H.2.isHermitian.eigenvalues i/(2*π)) t R b z) :
    let M := Q^(residues z d).card
    d ≤ M ∨ physicalArc ε < 2/Q+((M:ℝ)/d)*R := by
  intro M
  by_contra! h
  obtain ⟨j,hj,hJ,b',p,hp⟩ := compressed_visit hz hd hQ
  let f := (j:ℝ)/d
  have hd' := Nat.cast_pos (α:=ℝ).mpr hd
  have ht₀ := (mul_pos ha hd').trans_le horigin
  have hJ' : (j:ℝ) ≤ M := by exact_mod_cast hJ
  have hf : f < 1 := (div_lt_one hd').mpr (hJ'.trans_lt (by exact_mod_cast h.1))
  have ht' : a ≤ f*t := by
    have ha' := (le_div_iff₀ hd').mpr horigin
    calc a ≤ t/(d:ℝ) := ha'
         _ ≤ (j:ℝ)*(t/d) := le_mul_of_one_le_left (div_nonneg ht₀.le hd'.le) (by exact_mod_cast hj)
         _ = f*t := by dsimp only [f]; ring
  have hwidth := (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hJ' hd'.le) hR) (2/(Q:ℝ))).trans h.2
  have hh := (anchored_iff (physicalArc_spec hε.1 hε.2).1.1.le).mpr
    ⟨b',p,fun i => ⟨(hp i).1,(hp i).2.trans hwidth⟩⟩
  obtain ⟨z',hz',C,hC,he⟩ := (physical_visit H hε.1 hε.2 (f*t)).mp hh
  have hdate := (firstVisit_isLeast H a s hε.1).2
    (show f*t ∈ PrecisionReturns.visitSet H a s ε from ⟨ht',z',hz',C,hC.trans (Nat.zero_le s),he⟩)
  exact (mul_lt_of_lt_one_left ht₀ hf).not_ge (ht.trans hdate)

/-- In particular, every winding at the first scalar return has enough
distinct nonzero residues to keep 2 Q^m above each admissible denominator. -/
theorem scalar_winding_diversity {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (ha : 0 < a) (hε : ε ∈ Ioo (0:ℝ) (sqrt 2)) {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q)
    (hgrid : 4/(Q:ℝ) ≤ physicalArc ε) (horigin : a*(d:ℝ) ≤ firstVisit H a 0 ε)
    {b z} (hz : Anchored (fun i => -H.2.isHermitian.eigenvalues i/(2*π))
      (firstVisit H a 0 ε) (physicalArc ε) b z) :
    d < 2*Q^(residues z d).card := by
  let M := Q^(residues z d).card
  have hm : 0 < M := pow_pos hQ _
  have hr := (physicalArc_spec hε.1 hε.2).1.1
  rcases first_residue_bound H 0 ha hε le_rfl hr.le hd hQ horigin hz with h | h
  · change d ≤ M at h
    change d < 2*M
    omega
  · by_contra! hn
    have hd' := Nat.cast_pos (α:=ℝ).mpr hd
    have hf : (M:ℝ)/(d:ℝ) ≤ 1/2 := by
      apply (div_le_div_iff₀ hd' (by norm_num : (0:ℝ)<2)).mpr
      rw [one_mul,mul_comm]
      exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_right hf hr.le
    change physicalArc ε < 2/(Q:ℝ)+((M:ℝ)/d)*physicalArc ε at h
    rw [show (4:ℝ)/Q=2*(2/Q) by ring] at hgrid
    linarith only [hgrid,h,hh]

#print axioms first_residue_bound
#print axioms scalar_winding_diversity
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
