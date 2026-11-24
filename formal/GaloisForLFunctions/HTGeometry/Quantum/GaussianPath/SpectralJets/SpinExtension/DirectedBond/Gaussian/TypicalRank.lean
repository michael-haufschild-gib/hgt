import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.Witness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.RealWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # Almost-sure full spectral rank through order 2N−1 on the frozen chain -/
open Matrix MvPolynomial Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Degree and Gaussian lower-tail estimates for a nonzero physical minor
with derivative order growing only linearly in the number of spins. -/
theorem low_order_detector_tail (n : ℕ) :
    let N := n+1
    let L := 2*n+1
    let B := 2^N*(2*(1+2*L*2^N))
    ∃ rows : Fin (2^N)→Option (List (Coordinates N)),
      (∀ i w, w∈rows i → w.length≤L) ∧
      map GaussianInt.toComplex (pathDetector N L rows)≠0 ∧
      (pathDetector N L rows).totalDegree≤B ∧
      ∀ r : ℝ, 0<r → r≤1 →
        (Measure.pi fun _ : Coordinates N => gaussianReal 0 1)
          {x | ‖eval₂Hom GaussianInt.toComplex (fun a => (x a:ℂ)) (pathDetector N L rows)‖<r^B}
          ≤ ENNReal.ofReal (2*(B:ℝ)*r) := by
  intro N L B
  obtain ⟨k,w,_,hw,θ,hθ⟩ := physical_detector_witness n false
  let v (i) := (w i).map (fieldIndex n)
  let rows := detectorRows k v
  have hL : ∀ i u, u∈rows i → u.length≤L :=
    detectorRows_bound k v (fun i => by simpa only [v,L,order,List.length_map] using hw i)
  have hn : map GaussianInt.toComplex (pathDetector N L rows)≠0 := by
    intro he
    apply hθ
    exact (eval_map _ _ _).symm.trans (congrArg (eval (fun i => (θ i:ℂ))) he |>.trans (map_zero _))
  exact ⟨rows,hL,hn,pathDetector_degree N L rows hL,fun _ => pathDetector_lower_tail_of_nonzero N L rows hL hn⟩

/-- On every prefix of one frozen Gaussian draw, deterministic physical coordinate
words of order at most 2N−1 give a nonsingular projective response matrix for
the analytic germs of its Hermitian energy levels. -/
theorem gaussian_full_projective_rank :
    ∃ (k₀ : (k : ℕ)→Fin (2^(k+3))) (v : (k : ℕ)→Fin (2^(k+3))→List (Fin (k+3))),
      (∀ k i, ∃ u, Suffix (k+2) u ∧ v k i=letters false u) ∧
      (∀ k i, (v k i).length≤2*(k+2)+1) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
        let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        let x := fun i => (θ i:ℂ)
        let hH := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) θ
        ∃ F : Fin (2^(k+3))→(Coordinates (k+3)→ℂ)→ℂ,
          (∀ l, AnalyticAt ℂ (F l) x ∧ F l x=(hH.eigenvalues l:ℂ) ∧ ∀ᶠ z in 𝓝 x,
            matrixCharpolyRelation (∑ a, z a • chainPauliFin (k+3) a,F l z)=0) ∧
          (of fun i l => if i=k₀ k then (1:ℂ) else mixed ((v k i).map (fieldIndex (k+2))) (F l) x).det≠0 := by
  choose k₀ v hv hl hr using fun k => physical_detector_witness (k+2) false
  refine ⟨k₀,v,hv,hl,?_⟩
  let rows k := detectorRows (k₀ k) (fun i => (v k i).map (fieldIndex (k+2)))
  let Q k := pathDetector (k+3) (2*(k+2)+1) (rows k)
  have hω (k) := (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae
    (gaussian_ae_of_real_witness GaussianInt.toComplex (Q k) (v:=1) one_ne_zero (hr k))
  filter_upwards [ae_all_iff.mpr hω,gaussian_path_mixed_spectral_jet_detectors] with ω hdet hbranch
  intro k θ x hH
  obtain ⟨F,h,hf,heval⟩ := hbranch k
  have hb := detectorRows_bound (k₀ k) (fun i => (v k i).map (fieldIndex (k+2)))
    (fun i => by simpa only [List.length_map] using hl k i)
  have he : eval₂Hom GaussianInt.toComplex x (jetGram (integralGenerators (k+3)) (2*(k+2)+1) (rows k)) =
      ((of fun i l => rowValue (rows k i) (F l) x).det * ∏ l, h l^(2*(2*(k+2)+1)))^2 :=
    heval (2*(k+2)+1) (rows k) hb
  have hn := hdet k
  change eval₂Hom GaussianInt.toComplex x (jetGram _ _ (rows k))≠0 at hn
  rw [he] at hn
  have hd : (of fun i l => rowValue (rows k i) (F l) x).det≠0 := by
    intro hz
    simp only [hz,zero_mul,zero_pow (by decide : 2≠0),ne_self_iff_false] at hn
  refine ⟨F,fun l => (hf l).2,?_⟩
  have hrows : (of fun i l => if i=k₀ k then (1:ℂ) else mixed ((v k i).map (fieldIndex (k+2))) (F l) x) =
      of fun i l => rowValue (rows k i) (F l) x := by
    ext i l
    by_cases hi : i=k₀ k <;> simp [rows,detectorRows,rowValue,hi]
  rwa [hrows]

#print axioms gaussian_full_projective_rank
#print axioms low_order_detector_tail
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
