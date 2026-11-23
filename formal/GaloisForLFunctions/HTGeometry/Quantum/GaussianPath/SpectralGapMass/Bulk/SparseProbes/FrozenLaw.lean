import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.SparseProbes.LocalTrace
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CubicMass

/-! # Sublinear circuits have the same optimal critical-time trace overlap as the identity -/
open MeasureTheory Matrix Finset Filter
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
noncomputable section

/-- Connected part of the normalized trace for a circuit and the evolution. -/
def probeCovariance {n : ℕ} (u : PathShell n) (t : ℝ) (C : TwoQubitCircuit (n+2)) :=
  let U := unitaryEvolution (pathHamiltonian u) t
  regTrace (C.eval.valᴴ*U)-regTrace C.eval.valᴴ*regTrace U

/-- A gate touches at most two sites and each site meets at most 21
Pauli terms. Cauchy–Schwarz bounds their total squared coupling. -/
theorem circuit_incident_fourth {n : ℕ} (u : PathShell n) (t : ℝ) (C : TwoQubitCircuit (n+2)) :
    (2* |t| *Real.sqrt (∑ l ∈ C.touchedSites.biUnion pathIncidentLabels, (u l)^2))^4 ≤ 672*t^4*C.gateCount*(∑ l : PathLabel n, |u l|^4) := by
  let L := C.touchedSites.biUnion pathIncidentLabels
  let m := ∑ l ∈ L, (u l)^2
  have hm : 0≤m := sum_nonneg fun _ _ => sq_nonneg _
  have hc : (L.card:ℝ) ≤ 42*(C.gateCount:ℝ) := by
    have h : L.card ≤ 42*C.gateCount := calc
      _ ≤ 21*C.touchedSites.card := pathIncident_union_card C.touchedSites
      _ ≤ 21*(2*C.gateCount) := Nat.mul_le_mul_left 21 C.card_touchedSites_le
      _ = _ := by ring
    exact_mod_cast h
  have hs := sq_sum_le_card_mul_sum_sq (s:=L) (f:=fun l => (u l)^2)
  have he (l : PathLabel n) : ((u l)^2)^2=|u l|^4 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,sq_abs]
  simp only [he] at hs
  have hmass : m^2 ≤ 42*(C.gateCount:ℝ)*(∑ l : PathLabel n, |u l|^4) :=
    hs.trans (mul_le_mul hc (sum_le_sum_of_subset_of_nonneg (subset_univ L)
      (fun _ _ _ => by positivity)) (sum_nonneg fun _ _ => by positivity) (by positivity))
  have ht : |t|^4=t^4 := by simp only [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs]
  have hr : (Real.sqrt m)^4=m^2 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt hm]
  calc (2* |t| *Real.sqrt m)^4 = 16*t^4*m^2 := by rw [mul_pow,mul_pow,ht,hr]; norm_num
       _ ≤ _ := (mul_le_mul_of_nonneg_left hmass (by positivity : 0≤16*t^4)).trans_eq (by ring)

/-- The incident mass bounds every circuit's normalized trace covariance. -/
theorem circuit_covariance_fourth {n : ℕ} (u : PathShell n) (t : ℝ) (C : TwoQubitCircuit (n+2)) :
    ‖probeCovariance u t C‖^4 ≤ 672*t^4*C.gateCount*(∑ l : PathLabel n, |u l|^4) := by
  have h := supported_trace_covariance C.touchedSites u t C.eval C.isSiteSupported_touchedSites
  exact (pow_le_pow_left₀ (norm_nonneg _) h 4).trans (circuit_incident_fourth u t C)

/-- Uniform on a single frozen chain. At critical times Nt² bounded,
any fixed improvement in normalized trace overlap requires an extensive
gate budget. -/
theorem gaussian_circuit_covariance :
    ∃ K>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ (t : ℝ) (C : TwoQubitCircuit (n+2)),
        ‖probeCovariance (pathPauliDisorderShell ω n) t C‖^4 ≤
          K*((n+2:ℕ)*t^2)^2*((C.gateCount:ℝ)/(n+2:ℕ)) := by
  obtain ⟨B,hB,h⟩ := LocalPatches.gaussian_power_mass 4
  refine ⟨672*B,by positivity,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro t C
  apply (circuit_covariance_fourth _ t C).trans
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by
    field_simp [show ((n+2:ℕ):ℝ)≠0 by positivity]
    ring)

/-- The empty circuit asymptotically attains the best normalized trace
overlap with every sublinear budget throughout bounded Nt². Circuit and
time schedules can both be selected after seeing the entire disorder. -/
theorem gaussian_empty_overlap_optimal :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (C : (n : ℕ)→TwoQubitCircuit (n+2)) (t : ℕ→ℝ) (B : ℝ),
      (∀ᶠ n : ℕ in atTop, (n+2:ℕ)*(t n)^2≤B) →
      Tendsto (fun n => ((C n).gateCount:ℝ)/(n+2:ℕ)) atTop (𝓝 0) →
      Tendsto (fun n => probeCovariance (pathPauliDisorderShell ω n) (t n) (C n)) atTop (𝓝 0) ∧
      ∀ ε>0, ∀ᶠ n : ℕ in atTop, let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (t n)
        ‖regTrace ((C n).eval.valᴴ*U)‖ ≤ ‖regTrace U‖+ε := by
  obtain ⟨K,hK,h⟩ := gaussian_circuit_covariance
  filter_upwards [h] with ω hw
  intro C t B hB hcost
  let z (n : ℕ) := probeCovariance (pathPauliDisorderShell ω n) (t n) (C n)
  have hz : Tendsto z atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let b := |B|+1
    have hb : 0<b := by dsimp only [b]; positivity
    have hd : 0<K*b^2 := by positivity
    filter_upwards [hw,hB,hcost.eventually_lt_const (div_pos (pow_pos hε 4) hd)] with n hn ht hc
    have he : (n+2:ℕ)*(t n)^2 ≤ b := ht.trans ((le_abs_self B).trans (le_add_of_nonneg_right zero_le_one))
    have hsq := pow_le_pow_left₀ (by positivity) he 2
    have hh := (hn (t n) (C n)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq hK.le) (by positivity))
    have hsmall := (lt_div_iff₀ hd).mp hc
    rw [mul_comm _ (K*b^2)] at hsmall
    rw [dist_zero_right]
    exact lt_of_not_ge (fun bad => ((pow_le_pow_left₀ hε.le bad 4).trans hh).not_gt hsmall)
  refine ⟨hz,fun ε hε => ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hz ε hε] with n hn
  intro U
  rw [dist_zero_right] at hn
  let W := (C n).eval.valᴴ
  have hW := norm_regTrace_le_one (Unitary.star_mem (C n).eval.property)
  have h₁ := norm_add_le (z n) (regTrace W*regTrace U)
  change ‖(regTrace (W*U)-regTrace W*regTrace U)+regTrace W*regTrace U‖ ≤ _ at h₁
  rw [sub_add_cancel,norm_mul] at h₁
  exact h₁.trans (by linarith only [hn,mul_le_of_le_one_left (norm_nonneg (regTrace U)) hW])

#print axioms gaussian_circuit_covariance
#print axioms gaussian_empty_overlap_optimal
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
