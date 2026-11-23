import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingProfile.Slack
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.Scale

/-! # Exponential protection for budgets approaching the first crossing threshold -/
open Set Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.LocalPatches.CrossingProfile
open PrescribedTimes ShortWindows IncrementClocks
noncomputable section

/-- Every date in an exponential interval around the actual first robust
crossing admits a coarse fit and excludes a fine fit with exponentially
small relative slack in the near-Hilbert budget. -/
theorem gaussian_first_crossing_exponential_slack {γ α : ℝ} (hγ : 0 ≤ γ) (hγα : γ < α) (hα : α < 1) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let x := prefixPoint k ω
      let σ := crossingOrigin (k+1) P (9/80) x
      let L := ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
      let T := (2:ℝ)^(γ*(N:ℝ))
      L ≤ P ∧ (∀ t : ℝ, |t| ≤ T →
        pathGateDistance (k+1) (P+L) x (σ+t) ≤ 1/8 ∧
        1/10 < pathGateDistance (k+1) (P-L) x (σ+t)) ∧
        T < crossingWait (k+1) P (P-L) x := by
  filter_upwards [gaussian_crossing_budget_profile] with ω hw
  filter_upwards [hw,(tendsto_add_atTop_nat 3).eventually (binary_compiler_envelope hγ hγα),
    (tendsto_add_atTop_nat 3).eventually (binary_compiler_envelope (hγ.trans hγα.le) hα)] with k hk hsmall hlarge
  intro N P x σ L T
  let u := (2:ℝ)^(α*(N:ℝ))
  let F := (2:ℝ)^(5*N.sqrt+17)
  have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hF : 128 ≤ F := by
    exact (show (128:ℝ)=2^7 by norm_num).trans_le (pow_le_pow_right₀ (by norm_num) (by omega : 7 ≤ 5*N.sqrt+17))
  have hu : 0 < u := rpow_pos_of_pos (by norm_num) _
  have hL : (L:ℝ) ≤ u := Nat.floor_le hu.le
  have hD : (N:ℝ)*(1+u)*F ≤ (2:ℝ)^N := by simpa only [one_mul,rpow_natCast] using hlarge
  have hpay : (L:ℝ)*(64*((N:ℝ)+1)) ≤ (2:ℝ)^N := by
    apply le_trans _ hD
    have h₁ := mul_le_mul hL (show 64*((N:ℝ)+1) ≤ 128*(N:ℝ) by linarith only [hN])
      (by positivity : 0 ≤ 64*((N:ℝ)+1)) hu.le
    have h₂ := mul_le_mul_of_nonneg_left hF (show 0 ≤ (N:ℝ)*(1+u) by positivity)
    linarith only [h₁,h₂,hN]
  have hj : L ≤ P := (Nat.le_div_iff_mul_le (by positivity : 0 < 64*(N+1))).mpr (by exact_mod_cast hpay)
  have he (t : ℝ) (ht : |t| ≤ T) : pathGateDistance (k+1) (P+L) x (σ+t) ≤ 1/8 ∧
      1/10 < pathGateDistance (k+1) (P-L) x (σ+t) := by
    have hcost : (N:ℝ)*(1+|t|)*F ≤ u := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl ht) (Nat.cast_nonneg N)) (by positivity : 0 ≤ F)).trans hsmall
    have huN : u ≤ (2:ℝ)^N := by
      have hr := rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (mul_le_mul_of_nonneg_right hα.le (Nat.cast_nonneg (α:=ℝ) N))
      simpa only [one_mul,rpow_natCast] using hr
    have hvol : (N:ℝ)*(1+|t|) ≤ (2:ℝ)^N :=
      (le_mul_of_one_le_right (by positivity) (by linarith only [hF] : 1 ≤ F)).trans
        (hcost.trans huN)
    obtain ⟨j,hjcost,hup,hlo⟩ := hk t N hvol
    have hjL : j ≤ L := Nat.le_floor (hjcost.trans hcost)
    obtain ⟨z,hz,C,hC,hh⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ (P+j) (1/8:ℝ)).mpr hup
    have hdown : P-L+j ≤ P := (Nat.add_le_add_left hjL (P-L)).trans_eq (Nat.sub_add_cancel hj)
    exact ⟨(hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C,hC.trans (Nat.add_le_add_left hjL P),hh⟩,
      hlo _ hdown⟩
  refine ⟨hj,he,?_⟩
  apply lt_of_not_ge
  intro h
  obtain ⟨v,hv,hh⟩ := (crossingWait_le_iff (k+1) P (P-L) x T).mp h
  have hdist : |v-σ| ≤ T := by rw [abs_of_nonneg (sub_nonneg.mpr hv.1)]; linarith only [hv.2]
  have hno := (he (v-σ) hdist).2
  rw [show σ+(v-σ)=v by ring] at hno
  exact hno.not_ge hh

#print axioms gaussian_first_crossing_exponential_slack
end
end GaloisForLFunctions.HTGeometry.LocalPatches.CrossingProfile
