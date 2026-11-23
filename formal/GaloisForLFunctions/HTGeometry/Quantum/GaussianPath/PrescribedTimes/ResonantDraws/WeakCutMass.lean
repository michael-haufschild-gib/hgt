import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationCover
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.SplitSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.Passage

/-! # A ninth-power lower bound for the prescribed scalar probability -/
open Set MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open WeakBonds WeakBonds.SingleCut
noncomputable section

/-- At every date a weak bond and a common phase return on its two
sides contribute an explicit probability to the empty-circuit event.
Only nine coordinates pay an inverse-time price. -/
theorem gaussian_weak_cut_scalar_mass (n : ℕ) (a : Fin (n+1)) (t : ℝ) :
    let M : ℕ := 256^(2^(leftBlock a).card+2^(rightBlock a).card)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    (2*gaussianDensityFloor)^9*(1/(1800*(1+|t|)))^9 ≤
      (M:ℝ)^(Fintype.card (PrefixIndex n)+1)*μ.real {x | pathGateDistance n 0 x t ≤ 1/10} := by
  intro M μ
  let T := 1+|t|
  let δ := 1/(1800*T)
  let K := coefficientBox (bondSites a) δ univ
  let E := {x | pathGateDistance n 0 x t ≤ 1/10}
  have hT : 0 < T := by dsimp only [T]; positivity
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδ₁ : δ ≤ 1 := (div_le_one (by positivity : 0<1800*T)).mpr (by dsimp only [T]; linarith only [abs_nonneg t])
  have hM : 0 < (M:ℝ) := by dsimp only [M]; positivity
  have he : MeasurableSet E := measurableSet_Iic.preimage (continuous_distance_at_time n 0 t).measurable
  have hf : (2*gaussianDensityFloor)^9*δ^9 ≤ μ.real K := by
    simpa only [bondSites_card,probReal_univ,one_pow,mul_one] using
      coefficientBox_floor (bondSites a) univ hδ hδ₁
  refine hf.trans (rational_grid_price M K E he ?_)
  intro x hx
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  have hx' (i : PrefixIndex n) : u (pathCoeffEquiv n i)=x i := by
    simp only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply]
  have hw (i : PrefixIndex n) (hi : i∈bondSites a) : |u (pathCoeffEquiv n i)| ≤ 1/(1800*T) := by
    have hh := hx i (mem_univ i)
    change x i∈(if i∈bondSites a then Icc (-δ) δ else univ) at hh
    rw [hx']
    exact abs_le.mpr (by simpa only [if_pos hi,mem_Icc] using hh)
  obtain ⟨q,hq,hqM,hfit⟩ := cut_integer_return u a (t/M) 255
  change q ≤ M at hqM
  let v := (t/(M:ℝ))*q
  have hv : |v| ≤ T := by
    rw [show v=t*((q:ℝ)/M) by dsimp only [v]; ring,abs_mul,abs_of_nonneg (div_nonneg (Nat.cast_nonneg q) hM.le)]
    have hratio : (q:ℝ)/M ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast hqM)
    have hvt := mul_le_mul_of_nonneg_left hratio (abs_nonneg t)
    dsimp only [T]
    linarith only [hvt]
  have hnear := weak_error u a hT hw v hv
  have hfull := (norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (pathHamiltonian u) v)
    (unitaryEvolution (pathHamiltonianCut u a) v) 1).trans (add_le_add hnear hfit)
  have hcost : HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) 0 (unitaryEvolution (pathHamiltonian u) v) := by
    refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
    rw [TwoQubitCircuit.one_eval,one_smul]
    apply hfull.trans
    norm_num
    linarith only [pi_lt_four]
  have hgen : numberedGenerator n x=pathHamiltonian u := by
    simpa only [hx'] using numberedGenerator_shell u
  refine ⟨q,hq,hqM,?_⟩
  change pathGateDistance n 0 (((q:ℝ)/M) • x) t ≤ 1/10
  rw [distance_dilate,show (q:ℝ)/M*t=v by dsimp only [v]; ring,pathGateDistance,hgen]
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp hcost

#print axioms gaussian_weak_cut_scalar_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
