import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.SingleBond
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Outliers.ThresholdMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.Feedback.RepeatedBudget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.ComponentCuts

/-! # Component-merging calls at linear precision -/
open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
open RepeatedGates.PhysicalBlocks
noncomputable section


/-- For any prescribed loss fraction, a sufficiently small ratio of error
to time forces almost one sweep's worth of component-merging calls. -/
theorem gaussian_merger_allowance {c : ℝ} (hc : 0<c) :
    ∃ h∈Ioc (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      let u := pathPauliDisorderShell ω n
      ∀ t∈Ioc (0:ℝ) h, ∀ ε : ℝ, 2*ε≤t*h → ∀ (F : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
        ‖unitaryEvolution (pathHamiltonian u) t-z • F.eval.val‖≤ε →
        N+(redundant (circuitWord F):ℝ)≤(F.gateCount:ℝ)+c*N/16 := by
  obtain ⟨_,_,C,hC,hweak⟩ := gaussian_weak_edge_counts
  obtain ⟨D,hD,hout⟩ := gaussian_tenth_power_outliers
  let A := max C D
  have hA : 0<A := hC.trans_le (le_max_left ..)
  let h := min 1 (c/(64*A))
  have hh : 0<h := lt_min zero_lt_one (div_pos hc (mul_pos (by norm_num) hA))
  have hh₁ : h≤1 := min_le_left ..
  have hprod : h*(64*A)≤c := (le_div_iff₀ (mul_pos (by norm_num) hA)).mp (min_le_right ..)
  obtain ⟨J,hJ⟩ := exists_nat_ge (4*2^20/h^20)
  refine ⟨h,⟨hh,hh₁⟩,?_⟩
  filter_upwards [hweak,hout] with ω hw hx
  filter_upwards [hw,hx,eventually_ge_atTop J] with n hweak' hbad hsize
  intro N u t ht ε hsignal F z hz he
  let K : ℝ := (n+2:ℕ)
  have hK : 0≤K := Nat.cast_nonneg _
  have hNK : K≤2*N := by dsimp only [K,N]; exact_mod_cast (by omega : n+2≤2*(n+1))
  have hgrid : 4*2^20≤K*h^20 := (div_le_iff₀ (pow_pos hh 20)).mp
    (hJ.trans (Nat.cast_le.mpr (show J≤n+2 by omega)))
  have hwh := (hweak' h hh hh₁ hgrid).2
  have hcost (x B : ℝ) (hB : B≤A) (hx : 0≤x) (hx' : x≤h) :
      B*K*x≤c*N/32 := by
    have hw₁ := mul_le_mul hB hx' hx hA.le
    have hw₂ := mul_le_mul_of_nonneg_right hw₁ hK
    have hw₃ := mul_le_mul_of_nonneg_right hprod hK
    linarith only [hw₂,hw₃,mul_le_mul_of_nonneg_left hNK hc.le]
  have hp (y : ℝ) (hy : 0≤y) (h₁ : y≤1) (m : ℕ) (hm : 1 ≤ m) : y^m≤y := by
    simpa only [pow_one] using pow_le_pow_of_le_one hy h₁ hm
  have hweakN := hwh.trans (hcost (h^9) C (le_max_left ..) (pow_nonneg hh.le _) (hp _ hh.le hh₁ _ (by decide)))
  have houtN := (hbad t ht.1).trans (hcost (t^10) D (le_max_right ..) (pow_nonneg ht.1.le _)
    ((hp _ ht.1.le (ht.2.trans hh₁) _ (by decide)).trans ht.2))
  have hcap : 0<3348*t := mul_pos (by norm_num) ht.1
  obtain ⟨cut,hparts⟩ := component_cut F
  have hcross := fine_crossed_edges ω F cut ht.1 hh (one_div_pos.mpr hcap).le
    (by rw [mul_one_div,div_self hcap.ne']) (ε:=ε) hsignal z hz he
  have hR := repeat_budget (circuitWord F)
  rw [Fintype.card_fin,circuitWord_length] at hR
  have hgate : n+1+redundant (circuitWord F)≤F.gateCount+(weakEdges u h).card+(exceptionalEdges u (1/(3348*t))).card := by
    change (crossed cut).card≤(weakEdges u h).card+(exceptionalEdges u (1/(3348*t))).card at hcross
    omega
  have hg := (Nat.cast_le (α:=ℝ)).mpr hgate
  push_cast only [Nat.cast_add,Nat.cast_one] at hg
  have heq : (n:ℝ)+1=N := by dsimp only [N]; rw [Nat.cast_add,Nat.cast_one]
  change ((weakEdges u h).card:ℝ)≤c*N/32 at hweakN
  change ((exceptionalEdges u (1/(3348*t))).card:ℝ)≤c*N/32 at houtN
  linarith only [hg,hweakN,houtN,heq]

#print axioms gaussian_merger_allowance
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
