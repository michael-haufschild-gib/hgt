import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PhysicalDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # First physical crossing above the one-sweep gate budget -/
open Matrix MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section

private abbrev Hprefix (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩

/-- First distance-1/10 crossing for a circuit with q gates beyond
one pass over the physical bonds. -/
def excessDate (ω : PathPauliDisorder) (n q : ℕ) :=
  sInf {t : ℝ | 0≤t ∧ 1/10≤orbitCircuitDistance (Hprefix ω n) (n+1+q) t}

private theorem least_crossing {f : ℝ→ℝ} (hc : Continuous f) (h₀ : f 0<1/10)
    {v : ℝ} (hv : 0≤v) (hhigh : 1/10≤f v) :
    let E := {t : ℝ | 0≤t ∧ 1/10≤f t}
    let τ := sInf E
    IsLeast E τ ∧ f τ=1/10 := by
  intro E τ
  have hne : E.Nonempty := ⟨v,hv,hhigh⟩
  have hb : BddBelow E := ⟨0,fun _ ht => ht.1⟩
  have hclosed : IsClosed E := isClosed_Ici.inter (isClosed_le continuous_const hc)
  have hτ : τ∈E := hclosed.csInf_mem hne hb
  have hmin : IsLeast E τ := ⟨hτ,fun _ h => csInf_le hb h⟩
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc hτ.1 hc.continuousOn
    (show 1/10∈Icc (f 0) (f τ) from ⟨h₀.le,hτ.2⟩)
  have huτ : u=τ := le_antisymm hu.2 (hmin.2 ⟨hu.1,he.ge⟩)
  exact ⟨hmin,huτ ▸ he⟩

/-- Every sublinear excess above the bond count has a first crossing
at a date tending to zero. Its square times N stays bounded below.
The excess can depend on the full frozen Hamiltonian. -/
theorem gaussian_first_excess_date :
    ∃ b>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ q : ℕ → ℕ,
      Tendsto (fun n => (q n:ℝ)/(n+1:ℕ)) atTop (𝓝 0) →
      let u := fun n => excessDate ω n (q n)
      Tendsto u atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        b≤(n+2:ℕ)*(u n)^2 ∧ orbitCircuitDistance (Hprefix ω n) (n+1+q n) (u n)=1/10 ∧
        ∀ t∈Ico 0 (u n), orbitCircuitDistance (Hprefix ω n) (n+1+q n) t<1/10 := by
  let a (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have ha (j) : 0<a j := by dsimp only [a]; positivity
  choose c hc hfloor using fun j => gaussian_strict_spanning_floor (T:=a j) (ha j)
  obtain ⟨_,B,_,hB,hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨1/(840*B),by positivity,?_⟩
  filter_upwards [hmass,ae_all_iff.mpr hfloor] with ω hω hf
  intro q hq u
  let f (n : ℕ) := orbitCircuitDistance (Hprefix ω n) (n+1+q n)
  let E (n : ℕ) := {t : ℝ | 0≤t ∧ 1/10≤f n t}
  have htest (j : ℕ) : ∀ᶠ n : ℕ in atTop, 1/4<f n (a j) := by
    filter_upwards [hf j,hq.eventually_lt_const (hc j)] with n hn hs
    apply lt_of_not_ge
    intro h
    have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr h
    have hh := hn (a j) (by rw [abs_of_pos (ha j)]; exact ⟨le_rfl,le_rfl⟩) (n+1+q n) hfit
    have hlo := (div_lt_iff₀ (by positivity : 0<((n+1:ℕ):ℝ))).mp hs
    rw [Nat.cast_add (n+1)] at hh
    linarith only [hh,hlo]
  have hleast : ∀ᶠ n : ℕ in atTop, IsLeast (E n) (u n) ∧ f n (u n)=1/10 := by
    filter_upwards [htest 0] with n hn
    have hid : f n 0 ≤ 0 := by
      apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
      refine ⟨1,norm_one,TwoQubitCircuit.one _,Nat.zero_le _,?_⟩
      simp [unitaryEvolution,TwoQubitCircuit.one_eval]
    exact least_crossing (orbitCircuitDistance_lipschitz _ _).continuous (hid.trans_lt (by norm_num))
      (ha 0).le ((by norm_num : (1/10:ℝ)≤1/4).trans hn.le)
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨j,hj⟩ := exists_nat_gt (1/ε)
    have hε' : a j<ε := by
      apply (div_lt_iff₀ (by positivity : 0<(j:ℝ)+1)).mpr
      linarith only [(div_lt_iff₀ hε).mp hj,hε]
    filter_upwards [hleast,htest j] with n hn ht
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hn.1.1.1]
    exact (hn.1.2 ⟨(ha j).le,(by norm_num : (1/10:ℝ)≤1/4).trans ht.le⟩).trans_lt hε'
  · filter_upwards [hleast,hω] with n hn hbulk
    let v := u n
    let x := pathPauliDisorderShell ω n
    obtain ⟨z,hz,C,hC,he⟩ := BondProducts.bond_sweep_error x v hn.1.1.1 1 one_pos
    have hsize : C.gateCount≤n+1+q n := by rw [hC,one_mul]; omega
    have hh : f n v≤v^2/(1:ℕ)*(84*‖x‖^2) :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp ⟨z,hz,C,hsize,he⟩
    rw [show f n v=1/10 from hn.2,Nat.cast_one,div_one] at hh
    refine ⟨(div_le_iff₀ (by positivity : 0<840*B)).mpr ?_,hn.2,?_⟩
    · have hm := mul_le_mul_of_nonneg_left hbulk.2 (sq_nonneg v)
      change v^2*‖x‖^2≤_ at hm
      nlinarith only [hh,hm]
    · intro t ht
      exact lt_of_not_ge (fun h => ht.2.not_ge (hn.1.2 ⟨ht.1,h⟩))

#print axioms gaussian_first_excess_date
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
