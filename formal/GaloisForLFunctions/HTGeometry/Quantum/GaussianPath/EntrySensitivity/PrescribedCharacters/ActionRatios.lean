import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.GaussianContacts

/-! # Prescribed real actions on a typical fixed Gaussian spectrum -/

open Matrix MeasureTheory Set Finset
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
open FirstGate
noncomputable section

abbrev Label (k : ℕ) := Fin (k+3) → Bool

/-- Physical energy levels of one prefix. -/
def energy (ω : PathPauliDisorder) (k : ℕ) : Label k → ℝ :=
  (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues

private theorem fixed_weight (k : ℕ) (c : Label k → ℝ) (hb : ∑ i, c i=0) (hn : c≠0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∑ i, c i*energy ω k i ≠ 0 := by
  let N := k+3
  let n := k+1
  let P := chainPauliFin N
  let q := qubitConfigFin N
  let w := c ∘ q.symm
  have hw : ∑ j, w j=0 := (Equiv.sum_comp q.symm c).trans hb
  have hw' : w≠0 := by
    intro h
    apply hn
    funext i
    simpa only [w,Function.comp_apply,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun h (q i)
  have hac : centredProductGaussian (Fin (Fintype.card (ChainLabel N))) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous (Fintype.card (ChainLabel N))
      one_ne_zero (fun _ => 0)
  have h := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae (hac.ae_le
    (ae_no_fixed_real_relation P (chainPauliFin_spectrumEscapesRealRelations k) w hw hw'))
  filter_upwards [h,gaussian_path_all_prefixes_maximally_projective] with ω hω hs
  let u := pathPauliDisorderShell ω n
  let θ := fun i => u (pathCoeffEquiv n i)
  let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
  have hroot (j : Fin (2^N)) :
      matrixCharpolyRelation (spectralEnsembleMatrix P θ,(E (q.symm j):ℂ))=0 := by
    rw [←reindex_pathHamiltonian u]
    simpa only [E,matrixCharpolyRelation,←Matrix.eval_charpoly,Matrix.charpoly_reindex] using
      hermitianEigenvalue_matrixCharpolyRelation (pathHamiltonian u)
        (isSelfAdjoint_pathHamiltonian u).isHermitian (q.symm j)
  have hne := hω (E ∘ q.symm) ((hs k).injective.comp q.symm.injective) hroot
  exact fun hz => hne ((Equiv.sum_comp q.symm (fun j => c j*E j)).trans hz)

/-- The coefficients may be chosen from a prescribed countable set
after observing the draw. No nonzero balanced row so chosen annihilates
any physical prefix. -/
theorem gaussian_countable_weights (S : Set ℝ) (hs : S.Countable) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ c : Label k → ℝ, (∀ i, c i ∈ S) →
      (∑ i, c i)=0 → (∑ i, c i*energy ω k i)=0 → c=0 := by
  letI : Countable S := hs.to_subtype
  have h (k : ℕ) (c : Label k → S) : ∀ᵐ ω ∂pathPauliDisorderLaw,
      (∑ i, (c i).val)=0 → (∑ i, (c i).val*energy ω k i)=0 → (fun i => (c i).val)=0 := by
    by_cases hb : (∑ i, (c i).val)=0
    · by_cases hn : (fun i => (c i).val)=0
      · exact .of_forall fun _ _ _ => hn
      · exact (fixed_weight k _ hb hn).mono fun _ hh _ hzero => (hh hzero).elim
    · exact .of_forall fun _ hh => (hb hh).elim
  filter_upwards [ae_all_iff.mpr (fun k => ae_all_iff.mpr (h k))] with ω hω k c hc
  exact hω k (fun i => ⟨c i,hc i⟩)

/-- If two balanced integer actions at the same date hit a
prescribed countable set of real values, their coefficient vectors
satisfy the same proportion at every level. -/
theorem gaussian_two_actions (S : Set ℝ) (hs : S.Countable) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ t : ℝ, ∀ m n : Label k → ℤ,
      (∑ i, m i)=0 → (∑ i, n i)=0 →
      let a := t*∑ i, (m i:ℝ)*energy ω k i
      let b := t*∑ i, (n i:ℝ)*energy ω k i
      a ∈ S → b ∈ S → ∀ i, b*(m i:ℝ)=a*(n i:ℝ) := by
  letI : Countable S := hs.to_subtype
  let f (u : S × S × ℤ × ℤ) := u.1.val*(u.2.2.1:ℝ)-u.2.1.val*(u.2.2.2:ℝ)
  filter_upwards [gaussian_countable_weights (range f) (countable_range f)] with ω hω k t m n hm hn
  intro a b ha hb
  let c (i : Label k) := b*(m i:ℝ)-a*(n i:ℝ)
  have hc (i) : c i ∈ range f := ⟨(⟨b,hb⟩,⟨a,ha⟩,m i,n i),rfl⟩
  have hm' : ∑ i, (m i:ℝ)=0 := by exact_mod_cast hm
  have hn' : ∑ i, (n i:ℝ)=0 := by exact_mod_cast hn
  have hbal : ∑ i, c i=0 := by
    simp only [c,sum_sub_distrib,←mul_sum,hm',hn',mul_zero,sub_zero]
  have hw : ∑ i, c i*energy ω k i=0 := by
    simp only [c,sub_mul,mul_assoc,sum_sub_distrib,←mul_sum]
    dsimp only [a,b]
    ring
  exact fun i => sub_eq_zero.mp (congrFun (hω k c hc hbal hw) i)

#print axioms gaussian_two_actions
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
