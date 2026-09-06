import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SparseCapacity

/-!
# The physical unit-cost norming section

Radial normalization after deleting the unused terminal gap gives a
nonnegative unit-cost probe without changing that terminal zero. Its
response dominates the original monotone unit-budget probe. Coalescence
then yields a physical sparse unit-cost probe with no smaller response.

For every positive pairing degree the full monotone capacity is therefore
exactly the supremum on this unit section, the carrier of the path complex.
The unit section is distinct from its contractible closed cone.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem radialProbe_terminalFree {n : ℕ} (g : Fin (n+2) → ℝ) :
    terminalFreeProbe (radialProbe (terminalFreeProbe g))=radialProbe (terminalFreeProbe g) := by
  ext q
  by_cases hq : q.val+1=n+2
  · simp only [terminalFreeProbe,if_pos hq]
    symm
    unfold radialProbe
    split_ifs
    · have hne : q ≠ 0 := by
        intro heq
        have hv := congrArg Fin.val heq
        change q.val=0 at hv
        omega
      exact if_neg hne
    · simp only [terminalFreeProbe,if_pos hq,abs_zero,zero_div]
  · simp only [terminalFreeProbe,if_neg hq]

def physicalUnitValues {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) : Set ℝ :=
  {y | ∃ g : Fin (2*d) → ℝ, (∀ q, 0 ≤ g q) ∧ variation g=1 ∧
    separatedSupport g ∧ (∀ q, q.val+1=2*d → g q=0) ∧
    y=|familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) g|}

theorem physicalUnitValues_subset {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) :
    physicalUnitValues E c ⊆ physicalSparseValues E c := by
  rintro y ⟨g,hnn,hvar,hsep,hterminal,hy⟩
  exact ⟨g,hnn,hvar.le,hsep,hterminal,hy⟩

theorem physicalUnitValues_bddAbove {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ) :
    BddAbove (physicalUnitValues E c) := by
  obtain ⟨B,hB⟩ := physicalSparseValues_bddAbove E c
  exact ⟨B,fun _ hy => hB (physicalUnitValues_subset E c hy)⟩

theorem physicalUnit_norming {r m : ℕ}
    (E : Fin m → ((Fin (r+1) ⊕ Fin (r+1)) ≃ Fin (2*(r+1)))) (c : Fin m → ℝ)
    (g : Fin (2*(r+1)) → ℝ) :
    ∃ y ∈ physicalUnitValues E c,
      |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) (monotoneProbe g)| ≤ y := by
  let F := familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
  let p := terminalFreeProbe (monotoneProbe g)
  let q := radialProbe (n := 2*r+1) p
  have hpnn : ∀ i, 0 ≤ p i := by
    intro i
    dsimp only [p,terminalFreeProbe]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  have hpvar : variation p ≤ 1 :=
    (terminalFreeProbe_variation (monotoneProbe g)).trans (monotoneProbe_budget g)
  have hqnn : ∀ i, 0 ≤ q i := (radialProbe_data p).1
  have hqvar : variation q=1 := radialProbe_variation p
  have hqterm : terminalFreeProbe q=q := radialProbe_terminalFree (monotoneProbe g)
  have hpabs : (fun i => |p i|)=p := funext (fun i => abs_of_nonneg (hpnn i))
  have hscale : p=fun i => variation p*q i := by
    have hh := (radialProbe_data p).2.2
    exact hpabs.symm.trans hh
  have hpq : |F p| ≤ |F q| := by
    have he : F p=variation p^(r+1)*F q := by
      conv_lhs => rw [hscale]
      exact familyValue_scale _ _ q (variation p)
    rw [he,abs_mul,abs_pow,abs_of_nonneg (variation_nonneg p)]
    have hpow := pow_le_pow_left₀ (variation_nonneg p) hpvar (r+1)
    rw [one_pow] at hpow
    exact (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans_eq (one_mul _)
  obtain ⟨h,hnn,hvar,hzeros,hdom,hsep,hcount⟩ := enumeratedFamily_monotone_coalescence E c q
  have hdom' : |F q| ≤ |F h| := by
    simpa only [abs_of_nonneg (hqnn _)] using hdom
  refine ⟨|F h|,⟨h,hnn,hvar.trans hqvar,hsep,?_,rfl⟩,?_⟩
  · intro i hi
    apply hzeros
    have hh := congrFun hqterm i
    have hi' : i.val+1=2*r+1+1 := by omega
    simpa only [terminalFreeProbe,if_pos hi'] using hh.symm
  · have hsame : F p=F (monotoneProbe g) := enumeratedFamily_terminalFree E c _
    change |F (monotoneProbe g)| ≤ |F h|
    rw [← hsame]
    exact hpq.trans hdom'

theorem physicalUnitValues_nonempty {r m : ℕ}
    (E : Fin m → ((Fin (r+1) ⊕ Fin (r+1)) ≃ Fin (2*(r+1)))) (c : Fin m → ℝ) :
    (physicalUnitValues E c).Nonempty := by
  obtain ⟨y,hy,_⟩ := physicalUnit_norming E c (fun _ => 0)
  exact ⟨y,hy⟩

theorem monotoneCapacity_physical_unit {r m : ℕ}
    (E : Fin m → ((Fin (r+1) ⊕ Fin (r+1)) ≃ Fin (2*(r+1)))) (c : Fin m → ℝ) :
    monotoneCapacity (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)=
      sSup (physicalUnitValues E c) := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨g,rfl⟩
    obtain ⟨z,hz,hdom⟩ := physicalUnit_norming E c g
    exact hdom.trans (le_csSup (physicalUnitValues_bddAbove E c) hz)
  · apply csSup_le (physicalUnitValues_nonempty E c)
    intro y hy
    rw [monotoneCapacity_physical_sparse]
    exact le_csSup (physicalSparseValues_bddAbove E c) (physicalUnitValues_subset E c hy)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
