import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.FiniteSupport

/-! # A sparse positive clock cancelling an arbitrary finite frequency set -/
open Finset Set
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

private theorem real_parts (ws : List ℝ) (f : ℝ → ℂ) (a : ℝ) :
    (average ws (fun t => ((f t).re:ℂ)) a).re=(average ws f a).re ∧
    (average ws (fun t => ((f t).im:ℂ)) a).re=(average ws f a).im := by
  induction ws generalizing a with
  | nil => exact ⟨rfl,rfl⟩
  | cons w ws ih =>
    let b := a+Real.pi/|w|
    obtain ⟨ha₁,ha₂⟩ := ih a
    obtain ⟨hb₁,hb₂⟩ := ih b
    simp only [average,show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.div_ofReal_re,Complex.div_ofReal_im,
      Complex.add_re,Complex.add_im,ha₁,ha₂,show a+Real.pi/|w|=b from rfl,hb₁,hb₂,and_self]

/-- The same physical dates preserve all complex readings, with two
real coordinates per probe. -/
theorem compress_complex {n : ℕ} (ws : List ℝ) (a : ℝ) (f : ℝ → Fin n → ℂ) :
    ∃ p t : Fin (n+n+1) → ℝ, (∀ i, 0≤p i) ∧ (∑ i, p i=1) ∧
      (∀ i, t i∈dates ws a) ∧ ∀ j, ∑ i, (p i:ℂ)*f (t i) j=average ws (fun u => f u j) a := by
  let g (t : ℝ) := Fin.addCases (fun i => (f t i).re) (fun i => (f t i).im)
  obtain ⟨p,t,hp,hm,ht,hg⟩ := compress_readings ws a g
  refine ⟨p,t,hp,hm,ht,fun j => ?_⟩
  obtain ⟨hr,hi⟩ := real_parts ws (fun u => f u j) a
  apply Complex.ext
  · rw [Complex.re_sum,←hr]
    simpa only [g,Fin.addCases_left,Complex.re_ofReal_mul] using hg (Fin.castAdd n j)
  · rw [Complex.im_sum,←hi]
    simpa only [g,Fin.addCases_right,Complex.im_ofReal_mul] using hg (Fin.natAdd n j)

/-- Only two real readings per distinct nonzero frequency are needed
to replace all binary half-period subsums by a sparse positive clock. -/
theorem sparse_clock (F : Finset ℝ) (a : ℝ) : ∃ p t : Fin (F.card+F.card+1) → ℝ,
    (∀ i, 0≤p i) ∧ (∑ i, p i=1) ∧ (∀ i, t i∈Icc a (a+length F.toList)) ∧
      ∀ w∈F, w≠0 → ∑ i, (p i:ℂ)*wave w (t i)=0 := by
  let e := F.equivFin
  obtain ⟨p,t,hp,hm,ht,hf⟩ := compress_complex F.toList a (fun t i => wave (e.symm i).val t)
  refine ⟨p,t,hp,hm,fun i => dates_in_record F.toList a (ht i),?_⟩
  intro w hw hne
  have h := hf (e ⟨w,hw⟩)
  simp only [Equiv.symm_apply_apply] at h
  exact h.trans (annihilate F.toList hne ⟨w,mem_toList.mpr hw,rfl⟩ a)

#print axioms sparse_clock
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
