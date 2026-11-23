import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.DiagonalPackets.PolynomialPhases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonalLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Any prescribed computational phase packet on a finite physical path -/
open Matrix Polynomial MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.DiagonalPackets
open PrescribedTimes
noncomputable section

private theorem generic_near (k : ℕ) (x₀ : PrefixIndex (k+1) → ℝ)
    {S : Set (PrefixIndex (k+1) → ℝ)} (hS : S∈𝓝 x₀) :
    ∃ u : PathShell (k+1), (fun i => u (pathCoeffEquiv (k+1) i))∈S ∧
      MaximallyProjectiveEnergy (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues := by
  let read (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hS
  let lo (i : PrefixIndex (k+1)) := x₀ i-r/2
  let hi (i : PrefixIndex (k+1)) := x₀ i+r/2
  let E := univ.pi fun i => Icc (lo i) (hi i)
  have hm : MeasurableSet E := MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc
  have hp : 0 < pathPauliDisorderLaw (read ⁻¹' E) := by
    rw [(gaussian_pauli_prefix_coordinates_law (k+1)).measure_preimage hm.nullMeasurableSet]
    exact measure_pi_gaussian_box_pos lo hi (fun i => by dsimp [lo,hi]; linarith only [hr])
  by_contra hn
  apply hp.ne'
  apply ae_iff.mp
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw
  intro hbox
  have hnorm : ‖read ω-x₀‖≤r/2 := (pi_norm_le_iff_of_nonneg (half_pos hr).le).mpr fun i => by
    have hc : read ω i∈Icc (lo i) (hi i) := hbox i (mem_univ _)
    rw [Pi.sub_apply,Real.norm_eq_abs,abs_le]
    dsimp only [lo,hi] at hc
    constructor <;> linarith only [hc.1,hc.2]
  exact hn ⟨_,hball (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hnorm.trans_lt (half_lt_self hr))),hw k⟩

/-- Varying only onsite and nearest-neighbour coefficients at a prescribed
nonzero date approximates every computational diagonal phase packet up
to phase. The calibration permits arbitrary real coupling strengths. -/
theorem finite_path_diagonal_calibration (k : ℕ) (θ : (Fin (k+3)→Bool)→ℝ)
    {t ε : ℝ} (ht : t≠0) (hε : 0<ε) :
    ∃ u : PathShell (k+1), ∃ z : ℂ, ‖z‖=1 ∧
      ‖unitaryEvolution (pathHamiltonian u) t -
        z • diagonal (fun i => Complex.exp (-(Complex.I*(θ i:ℂ))))‖ < ε := by
  classical
  let n := k+1
  let base := sepCarrier n 1 0
  let x₀ := fun i => base (pathCoeffEquiv n i)
  let E := pathDiagEnergy base
  have hi : Function.Injective E := by
    intro i j h
    by_contra hn
    have hg := abs_sub_pathDiagEnergy_sepCarrier_ge (n:=n) (A:=1) (b:=0) zero_le_one le_rfl hn
    change 2*1-2*0*((n:ℝ)+1)≤|E i-E j| at hg
    rw [h,sub_self,abs_zero] at hg
    norm_num at hg
  let p := Lagrange.interpolate Finset.univ E θ
  have hp (i) : p.eval (E i)=θ i := Lagrange.eval_interpolate_at_node θ hi.injOn (Finset.mem_univ i)
  let D := diagonal (fun i => Complex.exp (-(Complex.I*(θ i:ℂ))))
  have hbase : numberedGenerator n x₀=diagonal (fun i => (E i:ℂ)) :=
    (numberedGenerator_shell base).trans (pathHamiltonian_eq_diagonal base (sepCarrier_offDiag 1 0))
  have he : polynomialPhase p (numberedGenerator n x₀)=D := by
    rw [hbase,polynomialPhase_diagonal]
    simp only [hp,D]
  have hgen : Continuous (numberedGenerator n) := by unfold numberedGenerator; fun_prop
  have hcont := (continuous_polynomialPhase p).comp hgen
  have hn : (fun x => polynomialPhase p (numberedGenerator n x)) ⁻¹' Metric.ball D (ε/2) ∈ 𝓝 x₀ :=
    hcont.continuousAt.preimage_mem_nhds (he ▸ Metric.ball_mem_nhds _ (half_pos hε))
  obtain ⟨u,hu,hmax⟩ := generic_near k x₀ hn
  have hclose : ‖polynomialPhase p (pathHamiltonian u)-D‖ < ε/2 := by
    have h := Metric.mem_ball.mp hu
    rwa [numberedGenerator_shell,dist_eq_norm] at h
  let e := (qubitConfigFin (k+3)).trans (prefixPhaseEnergyEquiv k)
  obtain ⟨v,_,z,hz,hv⟩ := approaches_polynomialPhase e (isSelfAdjoint_pathHamiltonian u).isHermitian
    hmax p (half_pos hε)
  let a := v/t
  have hscale : pathHamiltonian (a • u)=(a:ℂ) • pathHamiltonian u := by
    have hm := (pathHamiltonianLM (k+1)).map_smul a u
    refine hm.trans ?_
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
    rfl
  refine ⟨a • u,z,hz,?_⟩
  rw [hscale,unitaryEvolution_smul_generator,show a*t=v from div_mul_cancel₀ v ht]
  have hσ : ‖z • polynomialPhase p (pathHamiltonian u)-z • D‖<ε/2 := by
    rwa [←smul_sub,norm_smul,hz,one_mul]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (z • polynomialPhase p (pathHamiltonian u)) _).trans_lt
    ((add_lt_add hv hσ).trans_eq (add_halves _))

#print axioms finite_path_diagonal_calibration
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.DiagonalPackets
