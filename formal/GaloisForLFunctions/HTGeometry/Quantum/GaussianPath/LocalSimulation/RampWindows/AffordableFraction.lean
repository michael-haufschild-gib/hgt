import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.VolumeBound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation

/-! # Affordable time forced by one low-cost date in a physical observation -/

open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
open SharpOccupation
noncomputable section

/-- With an extra budget of b gates, use whichever is longer of the
identity approximation and the local simulation window. -/
def transportRadius {N : ℕ} (H : selfAdjoint (Register N)) (b d : ℕ) (T : ℝ) : ℝ :=
  min T (max (1 / (100 * (1 + ‖H.val‖))) ((b : ℝ) / (N * (2 : ℝ)^(5*d.sqrt+17)) - 1))

private theorem scalar_increment {N : ℕ} (H : selfAdjoint (Register N)) {v : ℝ}
    (hv : |v| ≤ 1 / (100 * (1 + ‖H.val‖))) :
    HasProjectiveCircuitApproximation N (1/100 : ℝ) 0 (unitaryEvolution H.val v) := by
  have hcap := (le_div_iff₀ (by positivity : 0 < 100 * (1 + ‖H.val‖))).mp hv
  have hnorm : ‖H.val‖ * |v| ≤ 1/100 := by nlinarith only [hcap, abs_nonneg v]
  have hzero : unitaryEvolution H.val 0 = 1 := by simp [unitaryEvolution]
  refine ⟨1, norm_one, TwoQubitCircuit.one N, le_rfl, ?_⟩
  rw [one_smul, TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution H.val v - 1‖ ≤ 1/100
  simpa only [hzero, sub_zero] using (norm_unitaryEvolution_time_sub_le H.2 v 0).trans
    (show ‖H.val‖ * |v-0| ≤ 1/100 by simpa only [sub_zero] using hnorm)

private theorem mass_of_increments {N s b : ℕ} (H : selfAdjoint (Register N))
    {A T r : ℝ} (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T)
    (inc : ∀ v : ℝ, |v| ≤ r →
      HasProjectiveCircuitApproximation N (1/100 : ℝ) b (unitaryEvolution H.val v))
    (hit : ((visitSet H s (1/10)) ∩ Icc A (A+T)).Nonempty) :
    r/T ≤ visitFraction H (s+b) (11/100) A (A+T) := by
  obtain ⟨t, ht, htA, htT⟩ := hit
  -- Slide a closed interval of length r against the nearer observation endpoint.
  let l := max A (t-r)
  have hlt : l ≤ t := max_le htA (sub_le_self _ hr)
  have hend : l+r ≤ A+T := by
    change max A (t-r) + r ≤ A+T
    apply (le_sub_iff_add_le.mp (max_le _ _))
    · linarith only [hrT]
    · linarith only [htT]
  have hsub : Icc l (l+r) ⊆ visitSet H (s+b) (11/100) ∩ Icc A (A+T) := by
    intro u hu
    have huv : |u-t| ≤ r := abs_le.mpr ⟨by linarith only [le_max_right A (t-r), hu.1],
      by linarith only [hu.2, hlt]⟩
    have hfit := affordable_add_time H (x:=t) (y:=u-t) ht (inc _ huv)
    rw [show t+(u-t)=u by ring] at hfit
    rw [show (1/10+1/100 : ℝ) = 11/100 by norm_num] at hfit
    exact ⟨hfit, (le_max_left ..).trans hu.1, hu.2.trans hend⟩
  have hmass := measureReal_mono (μ:=volume) hsub
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [Real.volume_real_Icc_of_le (le_add_of_nonneg_right hr), add_sub_cancel_left] at hmass
  simpa only [visitFraction, add_sub_cancel_left] using div_le_div_of_nonneg_right hmass hT.le

/-- On every sufficiently large frozen prefix, one physical fit anywhere
in a record forces a specified fraction of that same record to be affordable.
Both the record and the budgets can be chosen after observing the draw. -/
theorem gaussian_affordable_fraction_of_one_fit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      ∀ (A T : ℝ) (s b d : ℕ), 0 < T → (N : ℝ)*(1+T) ≤ (2 : ℝ)^d →
        (visitSet H s (1/10) ∩ Icc A (A+T)).Nonempty →
        transportRadius H b d T / T ≤ visitFraction H (s+b) (11/100) A (A+T) := by
  filter_upwards [gaussian_path_spacetime_upper] with ω hω
  filter_upwards [hω] with n hn
  intro N u H A T s b d hT hvol hit
  let F := (2 : ℝ)^(5*d.sqrt+17)
  have hNF : 0 < (N : ℝ)*F := mul_pos (by dsimp [N]; positivity) (by dsimp [F]; positivity)
  have hr : 0 ≤ transportRadius H b d T :=
    le_min hT.le ((by positivity : 0 ≤ 1/(100*(1+‖H.val‖))).trans (le_max_left ..))
  apply mass_of_increments H hT hr (min_le_left ..) _ hit
  intro v hv
  have hw := hv.trans (min_le_right ..)
  rcases le_max_iff.mp hw with hscalar | hlocal
  · obtain ⟨z, hz, C, hC, he⟩ := scalar_increment H hscalar
    exact ⟨z, hz, C, hC.trans (Nat.zero_le _), he⟩
  · have hvT := hv.trans (min_le_left ..)
    obtain ⟨j, hfit, hj⟩ := hn v d ((mul_le_mul_of_nonneg_left
      (add_le_add (le_rfl : (1:ℝ) ≤ 1) hvT) (Nat.cast_nonneg N)).trans hvol)
    change |v| ≤ (b : ℝ)/(N*F)-1 at hlocal
    have hcost := (le_div_iff₀ hNF).mp (show 1+|v| ≤ (b : ℝ)/(N*F) by linarith only [hlocal])
    change (j : ℝ) ≤ (N : ℝ)*(1+|v|)*F at hj
    have hle : (j : ℝ) ≤ b := hj.trans (by linarith only [hcost])
    obtain ⟨z, hz, C, hC, he⟩ := hfit
    exact ⟨z, hz, C, hC.trans (by exact_mod_cast hle), he⟩

private theorem slope_le_radius {N : ℕ} (hN : 0 < N) (H : selfAdjoint (Register N))
    {a T : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) (hT : 0 < T) (d : ℕ) :
    a/(200*(1+‖H.val‖)*(2:ℝ)^(5*d.sqrt+17)) ≤
      transportRadius H ⌈a*(N:ℝ)*T⌉₊ d T / T := by
  let F := (2 : ℝ)^(5*d.sqrt+17)
  let g := 1+‖H.val‖
  let b := ⌈a*(N:ℝ)*T⌉₊
  let w := max (1/(100*g)) ((b:ℝ)/(N*F)-1)
  have hg : 1 ≤ g := le_add_of_nonneg_right (norm_nonneg _)
  have hF : 1 ≤ F := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hg0 := zero_lt_one.trans_le hg
  have hF0 := zero_lt_one.trans_le hF
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < 200*g*F := by positivity
  have hden₁ : 1 ≤ 200*g*F :=
    (show (1:ℝ) ≤ 200 by norm_num).trans
      ((le_mul_of_one_le_right (by norm_num : (0:ℝ) ≤ 200) hg).trans
        (le_mul_of_one_le_right (by positivity) hF))
  have hscalar : 1 ≤ w*(100*g) := (div_le_iff₀ (by positivity)).mp (le_max_left ..)
  have hw : 0 ≤ w := (by positivity : 0 ≤ 1/(100*g)).trans (le_max_left ..)
  have hgrowth : w+1 ≤ 200*g*w := by nlinarith only [hscalar, mul_le_mul_of_nonneg_right hg hw]
  have hprice : (b:ℝ) ≤ (w+1)*(N*F) := (div_le_iff₀ (mul_pos hn hF0)).mp
    (by linarith only [show (b:ℝ)/(N*F)-1 ≤ w from le_max_right ..])
  have hcap : a*T ≤ w*(200*g*F) := by
    apply (mul_le_mul_iff_right₀ hn).mp
    calc
      (N:ℝ)*(a*T) = a*N*T := by ring
      _ ≤ b := Nat.le_ceil _
      _ ≤ (w+1)*(N*F) := hprice
      _ ≤ (200*g*w)*(N*F) := mul_le_mul_of_nonneg_right hgrowth (mul_pos hn hF0).le
      _ = (N:ℝ)*(w*(200*g*F)) := by ring
  change a/(200*g*F) ≤ min T w / T
  apply (le_div_iff₀ hT).mpr
  apply le_min
  · exact (mul_le_mul_of_nonneg_right ((div_le_one hden).mpr (ha.2.trans hden₁)) hT.le).trans_eq (one_mul T)
  · rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr hcap

/-- A low reading anywhere in [T,2T] charges the affordable fraction of
that very octave. The loss at scales d of order N is subexponential in N. -/
theorem gaussian_ramp_octave_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      ∀ (T a : ℝ) (d : ℕ), 0 < T → a ∈ Ioc (0 : ℝ) 1 → (N:ℝ)*(1+T) ≤ (2:ℝ)^d →
        let b := ⌈a*(N:ℝ)*T⌉₊
        (visitSet H b (1/10) ∩ Icc T (2*T)).Nonempty →
        a/(200*(1+‖H.val‖)*(2:ℝ)^(5*d.sqrt+17)) ≤ visitFraction H (2*b) (11/100) T (2*T) := by
  filter_upwards [gaussian_affordable_fraction_of_one_fit] with ω hω
  filter_upwards [hω] with n hn
  intro N u H T a d hT ha hd b hit
  rw [two_mul] at hit
  simpa only [two_mul] using
    (slope_le_radius (by dsimp [N]; omega) H ha hT d).trans (hn T T b b d hT hd hit)

#print axioms gaussian_affordable_fraction_of_one_fit
#print axioms gaussian_ramp_octave_occupation
end
end GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows
