import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.LineLevels
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.Thresholds

/-! # A strip bound for rational functions of simple spectral roots -/

open MvPolynomial Matrix MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- On the regular part of an affine line, a function with a rational spectral
derivative has a small strip wherever its derivative is large. The bound
allows the selection of eigenvalues to vary along the line. -/
theorem regular_rational_strip_volume (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (z : ι → Polynomial ℂ) (hz : ∀ i, (z i).natDegree ≤ 1)
    (E : ℝ → Fin D → ℂ) (m : Fin D → ℂ) (q d : MvPolynomial (Option ι) ℂ)
    (ht : ∀ (t : ℝ) (k : ℕ), eval (fun i => (z i).eval (t:ℂ)) (M^k).trace = ∑ j, E t j^k)
    (f : ℝ → ℝ) (hf : ∀ t : ℝ, let x := fun i => (z i).eval (t:ℂ)
        regularPacket x (E t) d → DifferentiableAt ℝ f t ∧ ContinuousAt (deriv f) t ∧
          ∃ s, ((deriv f t : ℝ) : ℂ) = rationalValue x (E t) m q d s)
    {T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r) :
    volume {t : ℝ | regularPacket (fun i => (z i).eval (t:ℂ)) (E t) d ∧ |f t| < T*r ∧ T ≤ |deriv f t|} ≤
      ((D*(d.totalDegree+2*D) + 2*((D+2*D*D+1)^D*(1+q.totalDegree+D*d.totalDegree+1)) + 1 : ℕ) : ℝ≥0∞)*
        ENNReal.ofReal (16*r) := by
  classical
  by_cases h : ∃ t : ℝ, regularPacket (fun i => (z i).eval (t:ℂ)) (E t) d
  · obtain ⟨t₀,h₀⟩ := h
    obtain ⟨c,hc,C,hcard,hcut⟩ := exists_line_level_cuts M hM z hz E m q d ht h₀
      (show 0 ≤ T/4 by positivity) (show T/4 < T/2 by linarith)
    have hg (t : ℝ) (h : t ∉ C) := hf t (hcut t h).1
    have hav (t : ℝ) (h : t ∉ C) : |deriv f t| ≠ c := by
      obtain ⟨s,hs⟩ := (hg t h).2.2
      obtain ⟨hp,hn⟩ := (hcut t h).2 s
      intro he
      rcases le_or_gt 0 (deriv f t) with hpos | hneg
      · rw [abs_of_nonneg hpos] at he
        exact hp (hs.symm.trans (congrArg Complex.ofReal he))
      · rw [abs_of_neg hneg] at he
        exact hn (hs.symm.trans (by rw [← he]; simp))
    apply (measure_mono (fun t ht => ht.2)).trans
    apply (strip_of_variable_cut f C hT hr hc.1.le (by linarith only [hc.2])
      (fun t h => ⟨(hg t h).1,(hg t h).2.1⟩) hav).trans
    exact mul_le_mul_left (by exact_mod_cast Nat.succ_le_succ hcard) _
  · have hempty : {t : ℝ | regularPacket (fun i => (z i).eval (t:ℂ)) (E t) d ∧
        |f t| < T*r ∧ T ≤ |deriv f t|} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun t ht => h ⟨t,ht.1⟩
    rw [hempty,measure_empty]
    exact bot_le

#print axioms regular_rational_strip_volume
end
end GaloisForLFunctions.HTGeometry.SpectralJets
