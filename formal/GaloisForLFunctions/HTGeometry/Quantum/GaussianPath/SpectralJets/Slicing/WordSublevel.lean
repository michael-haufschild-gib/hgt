import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.GaussianStrip

/-! # Spectral detuning below a witnessed mixed derivative -/

open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R] [Nontrivial R]

/-- A word of order at most L with response at least a controls the probability
of detuning below a times the L-th power of the strip ratio. Each letter
contributes one coordinate strip at the same price. -/
theorem gaussian_jet_word_sublevel (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (hmap : (fun j => (A j).map φ) = P)
    (hP : ∀ j, (P j).IsHermitian) (m : Fin D → ℝ) (w : List (Fin n))
    {L : ℕ} (hw : w.length ≤ L) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr' : r ≤ 1) :
    let p := map φ (characteristic A)
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      {θ | θ ∈ simpleEnsembleLocus hP ∧ |sortedMode hP p m [] θ| < a*r^L ∧ a ≤ |sortedMode hP p m w θ|} ≤
      (w.length : ℝ≥0∞)*((jetLineIntervals D L : ℝ≥0∞)*ENNReal.ofReal (16*r)) := by
  classical
  intro p
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let b (s : ℕ) := a*r^(L-s)
  let F (v : List (Fin n)) (θ : Fin n → ℝ) :=
    if θ ∈ simpleEnsembleLocus hP then |sortedMode hP p m v θ| else b v.length
  have hstrip (i : Fin n) (v : List (Fin n)) (hs : ∃ u, w = u ++ i::v) :
      μ {θ | F v θ < b v.length ∧ b (v.length+1) ≤ F (i::v) θ} ≤
        (jetLineIntervals D L : ℝ≥0∞)*ENNReal.ofReal (16*r) := by
    obtain ⟨u,hu⟩ := hs
    have hv : (i::v).length ≤ L := by rw [hu,List.length_append] at hw; omega
    have he : L-v.length = (L-(v.length+1))+1 := by simp only [List.length_cons] at hv; omega
    have hthr : b v.length = b (v.length+1)*r := by simp only [b,he,pow_succ,mul_assoc]
    have ht : 0 < b (v.length+1) := mul_pos ha (pow_pos hr _)
    apply (measure_mono (t := {θ | θ ∈ simpleEnsembleLocus hP ∧ |sortedMode hP p m v θ| < b (v.length+1)*r ∧
        b (v.length+1) ≤ |sortedMode hP p m (i::v) θ|}) ?_).trans
      (gaussian_sorted_jet_strip A φ P hmap hP m v i hv ht hr.le)
    intro θ hθ
    change F v θ < b v.length ∧ _ at hθ
    by_cases h : θ ∈ simpleEnsembleLocus hP
    · exact ⟨h,by simpa only [F,if_pos h,hthr] using hθ.1,by simpa only [F,if_pos h] using hθ.2⟩
    · exact (lt_irrefl _ (by simpa only [F,if_neg h] using hθ.1)).elim
  apply (measure_mono (t := {θ | F [] θ < b 0 ∧ b w.length ≤ F w θ}) ?_).trans
    (sublevel_le_word_length μ F b w _ hstrip)
  intro θ hθ
  have hba : b w.length ≤ a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr' (n := L-w.length)) ha.le
  exact ⟨by simpa only [F,if_pos hθ.1,b,Nat.sub_zero] using hθ.2.1,
    by simpa only [F,if_pos hθ.1] using hba.trans hθ.2.2⟩

#print axioms gaussian_jet_word_sublevel
end
end GaloisForLFunctions.HTGeometry.SpectralJets
