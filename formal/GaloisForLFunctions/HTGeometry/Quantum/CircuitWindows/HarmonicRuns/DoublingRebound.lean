import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.SharpRate
import Mathlib.Analysis.Real.Pi.Bounds

/-! # A plateau-scale circuit cost at twice an affordable observation date -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

private theorem squared_entropy (Q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      let D := 2^n
      let J := D/(128*(n+1))
      let F := ((J:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(J:ℝ)/δ)^32)^J
      ((Q:ℝ)*F)^2*zeroGateArcDensity D (1/54) < (1/36:ℝ)^D := by
  let z := Real.sqrt (1/54)
  have hz : 0 < z := Real.sqrt_pos.mpr (by norm_num)
  have hz2 : z^2 = 1/54 := Real.sq_sqrt (by norm_num)
  have h4 : z^4*2 < (1/6:ℝ)^4 := by rw [show z^4 = (z^2)^2 by ring,hz2]; norm_num
  have hl := Real.log_lt_log (by positivity : 0 < z^4*2) h4
  rw [Real.log_mul (pow_ne_zero _ hz.ne') (by norm_num),Real.log_pow,Real.log_pow] at hl
  have hlog : Real.log z+32*Real.log 2/(128:ℕ) < Real.log (1/6) := by
    norm_num only [Nat.cast_ofNat] at *
    linarith only [hl]
  have he := positive_budget_exponent 128 (by decide) δ z (1/6) hδ hz (by norm_num) hlog
  have hdim : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [he,hdim.eventually_ge_atTop (Q^2)] with n hn hQ
  intro D J F
  have hp : 0 ≤ F := by dsimp [F]; positivity
  have h₁ : F*zeroGateArcDensity D z < (1/6:ℝ)^D := hn
  have h₂ := pow_lt_pow_left₀ h₁ (mul_nonneg hp (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.le _)))
    (by decide : (2:ℕ) ≠ 0)
  have hQ' : (Q:ℝ)^2 ≤ D := by exact_mod_cast hQ
  have hpowers : (z^(D-1))^2 = (1/54:ℝ)^(D-1) := by rw [←pow_mul,mul_comm (D-1) 2,pow_mul,hz2]
  calc
    _ = (Q:ℝ)^2*(F^2*(D:ℝ)*(1/54:ℝ)^(D-1)) := by dsimp [zeroGateArcDensity]; ring
    _ ≤ (D:ℝ)*(F^2*(D:ℝ)*(1/54:ℝ)^(D-1)) := mul_le_mul_of_nonneg_right hQ' (by positivity)
    _ = (F*zeroGateArcDensity D z)^2 := by
      simp only [zeroGateArcDensity,mul_pow,hpowers]
      ring
    _ < _ := h₂
    _ = _ := by rw [←pow_mul,mul_comm D 2,pow_mul]; norm_num

/-- The two tests tolerate independent offsets without changing their joint
frequency bound. A small accuracy margin remains for continuous windows. -/
theorem offset_pair_upper :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ u : Fin 2 → ℝ, ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, volume.real
        (offsetRunSet H (D/(128*(N+1))) (101/1000) u ∩ Icc a T)/(T-a) < (1/36:ℝ)^D := by
  let y : ℝ := 1/29
  let γ : ℝ := 1/27-y
  have hγ : 0 < γ := by norm_num [γ,y]
  obtain ⟨Q,g,hg⟩ := finite_forward_grid hγ
  let δ := zeroGateArcTolerance y-101/1000
  have hδ : 0 < δ := sub_pos.mpr ((by norm_num [y] : 101/1000 < 3*y).trans_le
    (three_mul_le_arcTolerance (by norm_num [y]) (by norm_num [y])))
  have he := (tendsto_add_atTop_nat 3).eventually (squared_entropy Q hδ)
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  filter_upwards [he] with k hk
  intro N D H u a
  apply offset_mesh_bound H (hω k) _ (by decide : 0 < 2) u hδ (by norm_num [y] : 0 ≤ y) hγ.le
    (by norm_num [γ,y]) g hg (by dsimp [δ]; linarith : 101/1000+δ ≤ zeroGateArcTolerance y) a
  simpa only [show (y+γ)/(2:ℕ) = 1/54 by norm_num [y,γ]] using hk

/-- Increasing the gate budget preserves every visit at the same accuracy. -/
theorem visit_mono {n : ℕ} (H : selfAdjoint (Register n)) (ε : ℝ) {s j : ℕ} (hs : s ≤ j) :
    visitSet H s ε ⊆ visitSet H j ε := by
  rintro t ⟨c,hc,C,hC,he⟩
  exact ⟨c,hc,C,hC.trans hs,he⟩

/-- Empty-circuit visits alone provide this common lower denominator at
error 1/10, from every observation origin. -/
theorem affordable_lower {n : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (a : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ s : ℕ, (1/32:ℝ)^(2^n:ℕ) <
      volume.real (visitSet H s (1/10) ∩ Icc a T)/(T-a) := by
  let D := (2:ℕ)^n
  let r : Icc (0:ℝ) (1/2) := ⟨1/32,by norm_num,by norm_num⟩
  have htol : zeroGateArcTolerance r ≤ (1/10:ℝ) := by
    have hsin := Real.sin_le (show 0 ≤ Real.pi*(1/32)/2 by positivity)
    dsimp only [zeroGateArcTolerance,r]
    linarith only [hsin,Real.pi_lt_d2]
  have hD : 1 ≤ D := one_le_pow₀ (by decide)
  have hlo : (1/32:ℝ)^D < zeroGateArcDensity D r := by
    rw [show (1/32:ℝ)^D = (1/32:ℝ)*(1/32:ℝ)^(D-1) by rw [←pow_succ',Nat.sub_add_cancel hD]]
    apply mul_lt_mul_of_pos_right _ (by positivity)
    exact (by norm_num : (1/32:ℝ)<1).trans_le (by exact_mod_cast hD)
  filter_upwards [(maximallyProjective_zeroGateOccupation_from_start H hi r a).eventually_const_lt hlo,
    eventually_gt_atTop a] with T ht hT s
  apply ht.trans_le
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  apply measureReal_mono (inter_subset_inter_left _ ?_) (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  intro t h
  obtain ⟨c,hc,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr h
  exact ⟨c,hc,C,hC.trans (Nat.zero_le _),herr.trans htol⟩

/-- Among dates t affordable with any s≤D/[128(N+1)] gates, fewer than
(8/9)ᴰ also admit that full budget at 2t. Both tests use error 1/10. -/
theorem gaussian_plateau_after_doubling :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let J := D/(128*(N+1))
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ s ≤ J,
        volume.real (({t | t ∈ visitSet H s (1/10) ∧ 2*t ∈ visitSet H J (1/10)} : Set ℝ) ∩ Icc a T) /
          volume.real (visitSet H s (1/10) ∩ Icc a T) < (8/9:ℝ)^D := by
  filter_upwards [offset_pair_upper,gaussian_path_all_prefixes_maximally_projective] with ω hu hω
  filter_upwards [hu] with k hk
  intro N D J H a
  filter_upwards [hk (fun _ => 0) a,affordable_lower H (hω k) a,eventually_gt_atTop a] with T hhi hlos hT s hs
  let A := {t | t ∈ visitSet H s (1/10) ∧ 2*t ∈ visitSet H J (1/10)}
  have enlarge {i : ℕ} (hi : i ≤ J) : visitSet H i (1/10) ⊆ visitSet H J (101/1000) := by
    rintro t ⟨c,hc,C,hC,he⟩
    exact ⟨c,hc,C,hC.trans hi,he.trans (by norm_num)⟩
  have hi : A ⊆ offsetRunSet H J (101/1000) (fun _ : Fin 2 => 0) := by
    intro t ht i
    fin_cases i
    · simpa using enlarge hs ht.1
    · simpa [one_add_one_eq_two] using enlarge le_rfl ht.2
  have mono {S R : Set ℝ} (h : S ⊆ R) :
      volume.real (S ∩ Icc a T)/(T-a) ≤ volume.real (R ∩ Icc a T)/(T-a) :=
    div_le_div_of_nonneg_right (measureReal_mono (inter_subset_inter_left _ h)
      (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) (sub_nonneg.mpr hT.le)
  have hx := (mono hi).trans_lt hhi
  have hy := hlos s
  have hl : 0 < (1/32:ℝ)^D := by positivity
  rw [← div_div_div_cancel_right₀ (sub_pos.mpr hT).ne']
  apply (div_lt_div_of_pos_right hx (hl.trans hy)).trans_le
  have hbnd := div_le_div_of_nonneg_left (by positivity : 0 ≤ (1/36:ℝ)^D) hl hy.le
  exact hbnd.trans_eq (by rw [←div_pow]; norm_num)

#print axioms gaussian_plateau_after_doubling
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
