import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Exact phase spectra cannot split into a rectangular sum at a nonzero time -/
open Filter MeasureTheory Matrix
namespace GaloisForLFunctions.HTGeometry.DisconnectedSpectra
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Columnwise energy differences between two rows satisfy no integer
relation. The coefficients lift to opposite weights in those rows. -/
theorem row_gap_independent (E : A × B→ℝ) (hE : MaximallyProjectiveEnergy E) {a b : A} (hab : a≠b) :
    RationallyIndependentFrequency (fun j => E (a,j)-E (b,j)) := by
  classical
  intro k hk
  let row (i : A) (p : A × B) : ℤ := if p.1=i then k p.2 else 0
  have hr (i : A) : ∑ p, row i p=∑ j, k j := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp [row]
  have hw (i : A) : ∑ p, (row i p:ℝ)*E p=∑ j, (k j:ℝ)*E (i,j) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp [row,ite_mul]
  let v (p : A × B) := row a p-row b p
  have hbal : SpectralCharacterBalanced v := by
    unfold SpectralCharacterBalanced v
    rw [Finset.sum_sub_distrib,hr,hr,sub_self]
  have hsum : ∑ p, (v p:ℝ)*E p=0 := by
    simp only [v,Int.cast_sub,sub_mul,Finset.sum_sub_distrib,hw]
    simpa only [finiteTorusCharacterDetuning,mul_sub,Finset.sum_sub_distrib] using hk
  have hz := hE v hbal hsum
  funext j
  simpa [v,row,hab] using congrFun hz (a,j)

/-- In any proposed rectangular labeling, the phases of a nonzero
Gaussian time cannot consist of one phase for each row plus one for
each column. Repeated values and label permutations are allowed. -/
theorem no_rectangular_spectrum (E : A × B→ℝ) (hE : MaximallyProjectiveEnergy E) (a b : A)
    (hab : a≠b) (ref : B) (hcard : 3 ≤ Fintype.card B) (t : ℝ) (ht : t≠0) :
    ¬ ∃ (l : A→UnitAddCircle) (r : B→UnitAddCircle), ∀ i j, screwPhase E t (i,j)=l i+r j := by
  rintro ⟨l,r,h⟩
  let g (j : B) := E (a,j)-E (b,j)
  have hi := row_gap_independent E hE hab
  have hg : MaximallyProjectiveEnergy g := fun k _ hk => hi k hk
  apply ht (hg.no_nonzeroExactAnchoredReturn ref hcard t ?_)
  have hd (j : B) : screwPhase g t j=l a-l b := by
    have hsub : screwPhase g t j=screwPhase E t (a,j)-screwPhase E t (b,j) := by
      simp only [screwPhase,g,←AddCircle.coe_sub]
      congr 1
      ring
    rw [hsub,h,h,add_sub_add_right_eq_sub]
  funext j
  have hh : screwPhase (projectiveFrequency g ref) t j=screwPhase g t j.val-screwPhase g t ref := by
    simp only [screwPhase,projectiveFrequency,←AddCircle.coe_sub]
    congr 1
    ring
  rw [hh,hd,hd,sub_self,Pi.zero_apply]

/-- The entire Gaussian orbit avoids exact two-factor spectra in every
labeling of every prefix with nontrivial factors of sizes at least 2 and 3. -/
theorem gaussian_no_rectangular_spectrum :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ m n : ℕ, 2 ≤ m → 3 ≤ n → ∀ e : Fin m × Fin n ≃ (Fin (k+3)→Bool),
      ∀ t : ℝ, t≠0 → ¬ ∃ (l : Fin m→UnitAddCircle) (r : Fin n→UnitAddCircle),
        ∀ i j, screwPhase E t (e (i,j))=l i+r j := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro E m n hm hn e t ht
  let a : Fin m := ⟨0,by omega⟩
  let b : Fin m := ⟨1,by omega⟩
  let ref : Fin n := ⟨0,by omega⟩
  exact no_rectangular_spectrum _ ((hω k).comp_equiv e) a b (by intro he; exact Nat.zero_ne_one (congrArg Fin.val he))
    ref (by simpa only [Fintype.card_fin] using hn) t ht

#print axioms gaussian_no_rectangular_spectrum
end
end GaloisForLFunctions.HTGeometry.DisconnectedSpectra
