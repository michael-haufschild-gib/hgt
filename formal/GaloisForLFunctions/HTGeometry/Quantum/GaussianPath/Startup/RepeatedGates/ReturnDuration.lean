import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.QuadraticFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ExitInfimum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.ReturnAnnulus

/-! # Duration of a spanning-budget visit near a scalar return -/
open MeasureTheory Filter Set Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section

/-- From any scalar visit at half tolerance, the first failure of N−1
gates in either time direction has lag of exact order √ε on a fixed prefix. -/
theorem gaussian_spanning_exit_duration :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
      let N := n+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (n+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∀ v : ℝ, HasProjectiveCircuitApproximation N (ε/2) 0 (unitaryEvolution H.val v) →
        ∀ d : ℝ, |d|=1 →
          sInf {t : ℝ | 0 ≤ t ∧ ¬HasProjectiveCircuitApproximation N ε (n+2) (unitaryEvolution H.val (v+d*t))}
            ∈ Icc (sqrt (ε/b)) (sqrt (ε/a)) := by
  filter_upwards [gaussian_quadratic_bond_floor] with ω hw n
  intro N H
  obtain ⟨a,b,ha,hb,hfit,hfloor⟩ := hw n
  obtain ⟨R,hR,hlocal⟩ := Metric.eventually_nhds_iff.mp hfloor
  let T := R/2
  have hT : 0 < T := half_pos hR
  have ha' : 0 < a/2 := half_pos ha
  have hb' : 0 < 2*b := mul_pos two_pos hb
  refine ⟨a/2,2*b,ha',hb',?_⟩
  have hlim : Tendsto (fun ε : ℝ => sqrt (ε/(a/2))) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => sqrt (x/(a/2))) := continuous_sqrt.comp (continuous_id.div_const _)
    have hl := hcont.continuousAt (x:=0)
    rw [ContinuousAt,zero_div,sqrt_zero] at hl
    exact hl.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually_lt_const hT,self_mem_nhdsWithin] with ε hsmall hε
  have he : 0 < ε := hε
  intro v hv d hd
  have hd₂ : d^2=1 := by rw [←sq_abs,hd,one_pow]
  apply FirstAscent.first_exit_bracket _ (sqrt_nonneg _) hsmall
  · intro t ht
    have ht₂ : t^2 ≤ ε/(2*b) :=
      (pow_le_pow_left₀ ht.1 ht.2 2).trans_eq (sq_sqrt (div_nonneg he.le hb'.le))
    have hcost := (le_div_iff₀ hb').mp ht₂
    obtain ⟨z,hz,C,hC,herr⟩ := affordable_add_time H hv (hfit (d*t))
    refine ⟨z,hz,C,by omega,herr.trans ?_⟩
    rw [mul_pow,hd₂,one_mul]
    linarith only [hcost]
  · intro t ht h
    have hr : dist (d*t) 0 < R := by
      rw [Real.dist_eq,sub_zero,abs_mul,hd,one_mul,abs_of_nonneg ht.1]
      exact ht.2.trans_lt (half_lt_self hR)
    have hn := affordable_add_time H h (hv.neg_time H)
    simp only [Nat.add_zero,show v+d*t+-v=d*t by ring] at hn
    obtain ⟨z,hz,C,hC,herr⟩ := hn
    have hf := (hlocal hr C hC z hz).trans herr
    rw [mul_pow,hd₂,one_mul] at hf
    apply (le_sqrt ht.1 (div_nonneg he.le ha'.le)).mpr
    apply (le_div_iff₀ ha').mpr
    linarith only [hf,he.le]

#print axioms gaussian_spanning_exit_duration
end
end GaloisForLFunctions.HTGeometry.RepeatedGates
