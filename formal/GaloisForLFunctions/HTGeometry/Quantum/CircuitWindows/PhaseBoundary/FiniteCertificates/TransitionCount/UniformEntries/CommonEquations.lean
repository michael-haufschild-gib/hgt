import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.OrbitContacts
import Mathlib.Topology.Algebra.MvPolynomial

/-! # One finite family of gate-entry equations for all Hamiltonians and errors -/

open Set Filter Topology Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
open PrecisionReturns
noncomputable section

/-- Evaluate the polynomial in tolerance after evaluating its coefficients
at the real and imaginary matrix coordinates. -/
def testEval {N : ℕ} := appendEval (entryEval (N:=N) (RingHom.id ℝ))

private theorem affordable_tests (N s : ℕ) :
    FinitelyCertified (testEval (N:=N)) {z | HasProjectiveCircuitApproximation N |z.2| s z.1} := by
  let ρ := entryEval (N:=N) (RingHom.id ℝ)
  have hc (p : EntryPolynomial N ℝ) : Continuous (fun M => ρ M p) := by
    apply p.continuous_eval.comp
    apply continuous_pi
    rintro ⟨i,j,b⟩
    have h : Continuous (fun M : Square (Bits N) => M i j) :=
      (continuous_apply j).comp (continuous_apply i)
    cases b
    · exact Complex.continuous_re.comp h
    · exact Complex.continuous_im.comp h
  have hm : MatrixRep (appendEval ρ) (fun z : Square (Bits N)×ℝ => z.1) := by
    intro i j
    refine ⟨⟨C (MvPolynomial.X (i,j,false)),fun z => ?_⟩,
      ⟨C (MvPolynomial.X (i,j,true)),fun z => ?_⟩⟩ <;>
      simp only [appendEval,eval₂RingHom_apply,eval₂_C,ρ,entryEval,
        MvPolynomial.eval₂Hom_X',Bool.false_eq_true,if_false,if_true]
  apply affordable_finite (continuous_appendEval ρ hc) hm s (fun z => |z.2|) _ (fun _ => abs_nonneg _)
  exact ⟨X^2,fun z => by simp only [appendEval,eval₂RingHom_apply,eval₂_pow,eval₂_X,sq_abs]⟩

/-- One finite list, chosen before the spectrum, eigenvectors and tolerance,
detects every entry from outside. The chosen test vanishes at entry and is
nonzero at all sufficiently close preceding times, including at tangencies. -/
theorem common_first_entry_tests (N s : ℕ) :
    ∃ F : Finset (Polynomial (EntryPolynomial N ℝ)),
      ∀ {d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N))),
      ∀ ε > (0:ℝ), ∀ a : ℝ, ε < orbitCircuitDistance H s a →
        let v := firstVisit H a s ε
        let P (t : ℝ) := testEval (relativeOrbit e H t,ε)
        ∃ p∈F, P v p=0 ∧ ∀ᶠ t in 𝓝[<] v, P t p≠0 := by
  obtain ⟨F,hF⟩ := affordable_tests N s
  refine ⟨F,?_⟩
  intro d e H ε he a hout v P
  obtain ⟨hav,hv,hprev⟩ := firstVisit_left_contact H s a he hout
  let z (t : ℝ) := (relativeOrbit e H t,ε)
  have hcost (t : ℝ) :
      HasProjectiveCircuitApproximation N |(z t).2| s (z t).1 ↔ orbitCircuitDistance H s t≤ε := by
    rw [hasProjectiveCircuitApproximation_iff_infDist,abs_of_pos he,infDist_relativeOrbit]
  obtain ⟨p,hp,hz,hlocal⟩ := hF (z v) ((hcost v).mpr hv.le)
  refine ⟨p,hp,hz,?_⟩
  have hc : Continuous z := (continuous_relativeOrbit e H).prodMk continuous_const
  have ht := (hc.continuousAt (x:=v)).tendsto.eventually hlocal
  have hleft : ∀ᶠ t in 𝓝[<] v, a<t := nhdsWithin_le_nhds (lt_mem_nhds hav)
  filter_upwards [nhdsWithin_le_nhds ht,hleft,(self_mem_nhdsWithin : Iio v∈𝓝[<] v)] with t h ht₁ ht₂
  exact fun hzero => (hprev t ⟨ht₁,ht₂⟩).not_ge ((hcost t).mp (h hzero))

#print axioms common_first_entry_tests
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TransitionCount.UniformEntries
