import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PhysicalDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # First physical crossing above the one-sweep gate budget -/
open Matrix MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
noncomputable section

private abbrev Hprefix (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩

/-- First elapsed time from v at which the circuit distance reaches η
at a budget q gates above one pass over the physical bonds. -/
def firstExcessAfter (ω : PathPauliDisorder) (n q : ℕ) (v η : ℝ) :=
  sInf {u : ℝ | 0≤u ∧ η≤orbitCircuitDistance (Hprefix ω n) (n+1+q) (v+u)}

private theorem least_crossing {f : ℝ→ℝ} {η : ℝ} (hc : Continuous f) (h₀ : f 0<η)
    {v : ℝ} (hv : 0≤v) (hhigh : η≤f v) :
    let E := {t : ℝ | 0≤t ∧ η≤f t}
    let τ := sInf E
    IsLeast E τ ∧ f τ=η := by
  intro E τ
  have hne : E.Nonempty := ⟨v,hv,hhigh⟩
  have hb : BddBelow E := ⟨0,fun _ ht => ht.1⟩
  have hclosed : IsClosed E := isClosed_Ici.inter (isClosed_le continuous_const hc)
  have hτ : τ∈E := hclosed.csInf_mem hne hb
  have hmin : IsLeast E τ := ⟨hτ,fun _ h => csInf_le hb h⟩
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc hτ.1 hc.continuousOn
    (show η∈Icc (f 0) (f τ) from ⟨h₀.le,hτ.2⟩)
  have huτ : u=τ := le_antisymm hu.2 (hmin.2 ⟨hu.1,he.ge⟩)
  exact ⟨hmin,huτ ▸ he⟩

/-- From any sublinear-budget visit, the first departure above the
one-sweep budget plus the initial and excess gates tends to zero. Its
square times N stays bounded below. The origins may be actual first
visits selected after observing the entire frozen trajectory. -/
theorem gaussian_first_excess_after_visit {δ η : ℝ} (hmargin : δ<η) (hpay : δ+η≤1/4) :
    ∃ b>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (v : ℕ → ℝ) (s q : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop, HasProjectiveCircuitApproximation (n+2) δ (s n)
        (unitaryEvolution (Hprefix ω n).val (v n))) →
      Tendsto (fun n => ((2*s n+q n:ℕ):ℝ)/(n+1:ℕ)) atTop (𝓝 0) →
      let u := fun n => firstExcessAfter ω n (s n+q n) (v n) η
      Tendsto u atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        b≤(n+2:ℕ)*(u n)^2 ∧ orbitCircuitDistance (Hprefix ω n) (n+1+(s n+q n)) (v n+u n)=η ∧
        ∀ t∈Ico 0 (u n), orbitCircuitDistance (Hprefix ω n) (n+1+(s n+q n)) (v n+t)<η := by
  let a (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have ha (j) : 0<a j := by dsimp only [a]; positivity
  choose c hc hfloor using fun j => gaussian_strict_spanning_floor (T:=a j) (ha j)
  obtain ⟨_,B,_,hB,hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨(η-δ)/(84*B),div_pos (sub_pos.mpr hmargin) (by positivity),?_⟩
  filter_upwards [hmass,ae_all_iff.mpr hfloor] with ω hω hf
  intro v s q hv hq u
  let J (n : ℕ) := n+1+(s n+q n)
  let f (n : ℕ) (t : ℝ) := orbitCircuitDistance (Hprefix ω n) (J n) (v n+t)
  let E (n : ℕ) := {t : ℝ | 0≤t ∧ η≤f n t}
  have htest (j : ℕ) : ∀ᶠ n : ℕ in atTop, η<f n (a j) := by
    filter_upwards [hf j,hq.eventually_lt_const (hc j),hv] with n hn hs hanc
    apply lt_of_not_ge
    intro h
    have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ (J n) η).mpr h
    have he := affordable_add_time (Hprefix ω n) (hanc.neg_time _) hfit
    rw [show -(v n)+(v n+a j)=a j by ring] at he
    obtain ⟨z,hz,C,hC,herr⟩ := he
    have hh := hn (a j) (by rw [abs_of_pos (ha j)]; exact ⟨le_rfl,le_rfl⟩)
      (s n+J n) ⟨z,hz,C,hC,herr.trans hpay⟩
    have hlo := (div_lt_iff₀ (by positivity : 0<((n+1:ℕ):ℝ))).mp hs
    dsimp only [J] at hh
    push_cast at hh hlo
    linarith only [hh,hlo]
  have hleast : ∀ᶠ n : ℕ in atTop, IsLeast (E n) (u n) ∧ f n (u n)=η := by
    filter_upwards [htest 0,hv] with n hn hanc
    have hid : f n 0 ≤ δ := by
      obtain ⟨z,hz,C,hC,he⟩ := hanc
      dsimp only [f]
      rw [add_zero]
      apply (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
      exact ⟨z,hz,C,hC.trans (by dsimp only [J]; omega),he⟩
    have hcont : Continuous (f n) := (orbitCircuitDistance_lipschitz _ _).continuous.comp
      (continuous_const.add continuous_id)
    exact least_crossing hcont (hid.trans_lt hmargin) (ha 0).le hn.le
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨j,hj⟩ := exists_nat_gt (1/ε)
    have hε' : a j<ε := by
      apply (div_lt_iff₀ (by positivity : 0<(j:ℝ)+1)).mpr
      linarith only [(div_lt_iff₀ hε).mp hj,hε]
    filter_upwards [hleast,htest j] with n hn ht
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hn.1.1.1]
    exact (hn.1.2 ⟨(ha j).le,ht.le⟩).trans_lt hε'
  · filter_upwards [hleast,hω,hv] with n hn hbulk hanc
    let x := pathPauliDisorderShell ω n
    let g := (u n)^2/(1:ℕ)*(84*‖x‖^2)
    obtain ⟨z,hz,C,hC,he⟩ := BondProducts.bond_sweep_error x (u n) hn.1.1.1 1 one_pos
    have hinc : HasProjectiveCircuitApproximation (n+2) g (n+1)
        (unitaryEvolution (Hprefix ω n).val (u n)) := ⟨z,hz,C,by simpa only [one_mul] using hC.le,he⟩
    obtain ⟨z',hz',D,hD,hpaid⟩ := affordable_add_time (Hprefix ω n) hanc hinc
    have hh : f n (u n)≤δ+g := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
      ⟨z',hz',D,hD.trans (by dsimp only [J]; omega),hpaid⟩
    rw [hn.2] at hh
    dsimp only [g,Nat.cast_one,div_one] at hh
    refine ⟨(div_le_iff₀ (by positivity : 0<84*B)).mpr ?_,hn.2,?_⟩
    · have hm := mul_le_mul_of_nonneg_left hbulk.2 (sq_nonneg (u n))
      change (u n)^2*‖x‖^2≤_ at hm
      linarith only [hh,hm]
    · intro t ht
      exact lt_of_not_ge (fun h => ht.2.not_ge (hn.1.2 ⟨ht.1,h⟩))

#print axioms gaussian_first_excess_after_visit

/-- At the identity, the first physical departure above one sweep plus
any sublinear excess is later than a constant times the inverse square
root of the length and earlier than every fixed positive date. -/
theorem gaussian_first_excess_from_identity :
    ∃ b>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ q : ℕ → ℕ,
      Tendsto (fun n => (q n:ℝ)/(n+1:ℕ)) atTop (𝓝 0) →
      let u := fun n => firstExcessAfter ω n (q n) 0 (1/10)
      Tendsto u atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        b≤(n+2:ℕ)*(u n)^2 ∧ orbitCircuitDistance (Hprefix ω n) (n+1+q n) (u n)=1/10 ∧
        ∀ t∈Ico 0 (u n), orbitCircuitDistance (Hprefix ω n) (n+1+q n) t<1/10 := by
  obtain ⟨b,hb,h⟩ := gaussian_first_excess_after_visit
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)+1/10≤1/4)
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hw
  intro q hq u
  have h₀ (n : ℕ) : HasProjectiveCircuitApproximation (n+2) 0 0
      (unitaryEvolution (Hprefix ω n).val 0) := by
    refine ⟨1,norm_one,TwoQubitCircuit.one _,le_rfl,?_⟩
    simp [TwoQubitCircuit.one_eval,unitaryEvolution]
  simpa only [Nat.mul_zero,Nat.zero_add,zero_add] using
    hw (fun _ => 0) (fun _ => 0) q (Eventually.of_forall h₀) (by simpa only [Nat.mul_zero,Nat.zero_add] using hq)

#print axioms gaussian_first_excess_from_identity

/-- Actual first physical-error visit at s gates after the first robust
near-Hilbert crossing on this prefix. -/
def firstLowAfterCrossing (ω : PathPauliDisorder) (n s : ℕ) : ℝ :=
  let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let σ := PrescribedTimes.crossingOrigin n (nearHilbertContinuousCircuitBudget (n+2)) (9/80) x
  firstCircuitVisit (Hprefix ω n) s σ

/-- After the actual first low-budget visit, the first subsequent
1/8 crossing at one bond sweep above that budget occurs at vanishing
elapsed time, bounded below by a constant multiple of 1/√N. -/
theorem gaussian_first_low_visit_rebound :
    ∃ b>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ,
      Tendsto (fun n => (s n:ℝ)/(n+1:ℕ)) atTop (𝓝 0) →
      let v := fun n => firstLowAfterCrossing ω n (s n)
      let u := fun n => firstExcessAfter ω n (s n) (v n) (1/8)
      Tendsto u atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        b≤(n+2:ℕ)*(u n)^2 ∧ orbitCircuitDistance (Hprefix ω n) (n+1+s n) (v n+u n)=1/8 ∧
        ∀ t∈Ico 0 (u n), orbitCircuitDistance (Hprefix ω n) (n+1+s n) (v n+t)<1/8 := by
  obtain ⟨b,hb,h⟩ := gaussian_first_excess_after_visit
    (by norm_num : (1/10:ℝ)<1/8) (by norm_num : (1/10:ℝ)+1/8≤1/4)
  refine ⟨b,hb,?_⟩
  filter_upwards [h] with ω hw
  intro s hs v u
  have hv (n : ℕ) : HasProjectiveCircuitApproximation (n+2) (1/10) (s n)
      (unitaryEvolution (Hprefix ω n).val (v n)) :=
    (PrecisionReturns.firstVisit_isLeast (Hprefix ω n) _ (s n) (by norm_num : (0:ℝ)<1/10)).1.2
  have hlim : Tendsto (fun n => ((2*s n+0:ℕ):ℝ)/(n+1:ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.add_zero,Nat.cast_mul,Nat.cast_ofNat,mul_div_assoc,mul_zero] using hs.const_mul (2:ℝ)
  simpa only [Nat.add_zero] using hw v s (fun _ => 0) (Eventually.of_forall hv) hlim

#print axioms gaussian_first_low_visit_rebound
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks
