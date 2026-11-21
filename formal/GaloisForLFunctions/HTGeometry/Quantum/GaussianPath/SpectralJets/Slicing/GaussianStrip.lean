import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedLine
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.GaussianSlices
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.RationalStrips

/-! # Gaussian probability of consecutive derivative strips for Hermitian pencils -/

open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R] [Nontrivial R]

/-- A bound for the number of line intervals for any jet of order at most L. -/
def jetLineIntervals (D L : ℕ) : ℕ :=
  let b := 2*L*D
  D*(b+2*D) + 2*((D+2*D*D+1)^D*(1+(1+b)+D*b+1)) + 1

private theorem sorted_trace (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (hP : ∀ a, (P a).IsHermitian)
    (θ : Fin n → ℝ) (k : ℕ) :
    eval (realEmbed θ) ((pencil P)^k).trace = ∑ j, (sortedEnsembleSpectrum hP θ j : ℂ)^k := by
  let E := (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues
  have he : (eval (realEmbed θ)).mapMatrix (pencil P) = spectralEnsembleMatrix P θ := by
    have hm (j : Fin n) : (P j).map (RingHom.id ℂ) = P j := by ext; rfl
    change (eval₂Hom (RingHom.id ℂ) (realEmbed θ)).mapMatrix (pencil P) = ∑ j, realEmbed θ j • P j
    rw [eval_pencil]
    simp only [hm]
  rw [← trace_mapMatrix,map_pow,he,trace_pow_eq_sum_eigenvalues_pow (isHermitian_spectralEnsembleMatrix hP θ)]
  exact (Equiv.sum_comp (Tuple.sort E) (fun j => (E j : ℂ)^k)).symm

/-- On a Gaussian Hermitian linear family, uniformly in all real weights, a
strip between two consecutive derivative thresholds has probability at most
sixteen times the threshold ratio times the algebraic line-interval count. -/
theorem gaussian_sorted_jet_strip (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R →+* ℂ)
    (P : Fin n → Matrix (Fin D) (Fin D) ℂ) (hmap : (fun a => (A a).map φ) = P)
    (hP : ∀ a, (P a).IsHermitian) (m : Fin D → ℝ) (w : List (Fin n)) (i : Fin n)
    {L : ℕ} (hw : (i::w).length ≤ L) {T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r) :
    let p := map φ (characteristic A)
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      {θ | θ ∈ simpleEnsembleLocus hP ∧ |sortedMode hP p m w θ| < T*r ∧ T ≤ |sortedMode hP p m (i::w) θ|} ≤
        (jetLineIntervals D L : ℝ≥0∞)*ENNReal.ofReal (16*r) := by
  intro p
  let v := i::w
  let q := numerator p v
  let d := (pderiv none p)^(2*v.length)
  have hdeg : p.totalDegree ≤ D := (Finset.sup_mono (support_map_subset φ (characteristic A))).trans
    (characteristic_degree A)
  have hb : 2*v.length*p.totalDegree ≤ 2*L*D :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hw) hdeg
  have hd : d.totalDegree ≤ 2*L*D := (totalDegree_pow _ _).trans
    ((Nat.mul_le_mul_left _ (totalDegree_partial_le none p)).trans hb)
  have hq : q.totalDegree ≤ 1+2*L*D := (numerator_degree p v).trans (Nat.add_le_add_left hb 1)
  have hcount : D*(d.totalDegree+2*D) + 2*((D+2*D*D+1)^D*(1+q.totalDegree+D*d.totalDegree+1)) + 1 ≤
      jetLineIntervals D L := by
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.mul_le_mul_left D (Nat.add_le_add_right hd _))
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add_left hq 1) (Nat.mul_le_mul_left D hd)) 1)))) 1
  apply gaussian_update_slices i
  · exact (isOpen_simpleEnsembleLocus hP).measurableSet.inter
      ((measurableSet_lt (measurable_sortedMode hP p m w).abs measurable_const).inter
        (measurableSet_le measurable_const (measurable_sortedMode hP p m v).abs))
  intro y
  let u := Function.update y i
  let z := coordinatePolynomials y i
  let E (t : ℝ) (j : Fin D) : ℂ := sortedEnsembleSpectrum hP (u t) j
  let f (t : ℝ) := sortedMode hP p m w (u t)
  have he (t : ℝ) : (fun j => (z j).eval (t:ℂ)) = realEmbed (u t) := coordinatePolynomials_eval y i t
  have ht (t : ℝ) (k : ℕ) : eval (fun j => (z j).eval (t:ℂ)) ((pencil P)^k).trace = ∑ j, E t j^k := by
    rw [he]; exact sorted_trace P hP (u t) k
  have hreg (t : ℝ) : regularPacket (fun j => (z j).eval (t:ℂ)) (E t) d ↔ u t ∈ simpleEnsembleLocus hP := by
    rw [he]; exact regularPacket_sorted_iff A φ hmap hP (u t) _
  have hdiff (t : ℝ) (h : u t ∈ simpleEnsembleLocus hP) : HasDerivAt f (sortedMode hP p m v (u t)) t :=
    hasDerivAt_sortedMode_update A φ hmap hP m w y i t h
  have hstrip := regular_rational_strip_volume (pencil P) (pencil_degree P) z
    (coordinatePolynomials_degree y i) E (fun j => (m j:ℂ)) q d ht f (fun t h => by
      have hs := (hreg t).mp h
      refine ⟨(hdiff t hs).differentiableAt,continuousAt_deriv_sortedMode_update A φ hmap hP m w y i t hs,id,?_⟩
      rw [(hdiff t hs).deriv,he]
      exact sortedMode_eq_rationalValue A φ hmap hP m v hs) hT hr
  apply (measure_mono (t := {t : ℝ | regularPacket (fun j => (z j).eval (t:ℂ)) (E t) d ∧
      |f t| < T*r ∧ T ≤ |deriv f t|}) ?_).trans
    (hstrip.trans (mul_le_mul_left (by exact_mod_cast hcount) _))
  intro t h
  exact ⟨(hreg t).mpr h.1,h.2.1,(h.2.2.trans_eq (congrArg abs (hdiff t h.1).deriv.symm))⟩

#print axioms gaussian_sorted_jet_strip
end
end GaloisForLFunctions.HTGeometry.SpectralJets
