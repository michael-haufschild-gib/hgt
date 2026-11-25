import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns.PhysicalWaits
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.HilbertWindows

/-! # A ninth-power obstruction for spectral-window confidence -/

open Set MeasureTheory Filter ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open PrescribedTimes CircuitWindings AntipodalHorizons
noncomputable section

private theorem fullTurnMass_le_window (k m w s : ℕ) (ε L : ℝ) (hm : m+1≤w) (hw : (w:ℝ)≤L) :
    fullTurnMass (k+1) w ε≤pathPauliDisorderLaw.real (gateWindow k m s 0 L ε) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage
    (measurable_turnEvent k w ε).nullMeasurableSet
  apply he.symm.le.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  let u := pathPauliDisorderShell ω (k+1)
  let x := fun i => u (pathCoeffEquiv (k+1) i)
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
  let q := (w:ℝ)-((m:ℝ)+1/2)
  have h₀ : 0≤q := by
    have hh : (m:ℝ)+1≤(w:ℝ) := by exact_mod_cast hm
    dsimp only [q]; linarith only [hh]
  have hL : q≤0+L := by
    rw [zero_add]
    exact (sub_le_self _ (by positivity)).trans hw
  have ht : date E (topLevel k) 0 m q=fullTurn (k+1) w x := by
    rw [fullTurn,intrinsic_sorted_width]
    dsimp only [date,q,E]; ring
  refine ⟨q,⟨h₀,hL⟩,?_⟩
  rw [ht]
  have hd : pathGateDistance (k+1) 0 x (fullTurn (k+1) w x)≤ε := hω.2
  rw [pathGateDistance,show numberedGenerator (k+1) x=pathHamiltonian u from numberedGenerator_shell u] at hd
  obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hd
  exact ⟨z,hz,C,hC.trans (Nat.zero_le s),hfit⟩

/-- For a window covering all candidate multiples of the starting
turn, even the empty circuit supplies a ninth-power mass floor.
The finite alternative applies to every gate budget. -/
theorem gaussian_window_or_ninth_price {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℕ, 1≤B ∧ ∃ c>(0:ℝ), ∀ k m s : ℕ, ∀ L : ℝ,
      let M := B^(blockDimension (k+1))
      L<((m:ℝ)+1)*(M:ℝ) ∨
        c≤((m:ℝ)+1)^9*(M:ℝ)^10*pathPauliDisorderLaw.real (gateWindow k m s 0 L ε) := by
  obtain ⟨B,hB,c,hc,h⟩ := gaussian_full_turn_price hε
  refine ⟨B,hB,c,hc,?_⟩
  intro k m s L M
  rcases lt_or_ge L (((m:ℝ)+1)*(M:ℝ)) with hl|hl
  · exact Or.inl hl
  obtain ⟨w,hw,hh⟩ := h (k+1) m
  have hcand : (w:ℝ)≤((m:ℝ)+1)*(M:ℝ) := by exact_mod_cast hw.2
  exact Or.inr (hh.trans (mul_le_mul_of_nonneg_left (fullTurnMass_le_window k m w s ε L hw.1
    (hcand.trans hl)) (by positivity)))

/-- At the first winding attaining exponential confidence on an
(8/7)^D-period window, nine powers of the winding already pay the
exponential price up to the two-block spectral dimension. -/
theorem gaussian_first_ninth_plateau_winding :
    ∃ ρ∈Ioo (0:ℝ) 1, ∃ B : ℕ, 1≤B ∧ ∃ c>(0:ℝ), ∀ᶠ k : ℕ in atTop,
      let D : ℕ := 2^(k+3)
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let M := B^(blockDimension (k+1))
      let W := {m : ℕ | pathPauliDisorderLaw.real (gateWindow k m P 0
        ((1/(7/8:ℝ))^D) (1/8))≤ρ^(D-3)}
      sInf W∈W ∧ c*(1/ρ)^(D-3) ≤ (((sInf W:ℕ):ℝ)+1)^9*(M:ℝ)^10 := by
  have he : (1/8:ℝ)∈Ioo (0:ℝ) (sqrt 2) :=
    ⟨by norm_num,(by norm_num : (1/8:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))⟩
  obtain ⟨r,hr,hlate⟩ := gaussian_near_hilbert_antipodal_window he
  let ρ := max r (7/8:ℝ)
  have hρ : ρ∈Ioo (0:ℝ) 1 := ⟨hr.1.trans_le (le_max_left ..),max_lt hr.2 (by norm_num)⟩
  obtain ⟨B,hB,c,hc,h⟩ := gaussian_window_or_ninth_price (ε:=1/8) (by norm_num)
  refine ⟨ρ,hρ,B,hB,min 1 c,lt_min zero_lt_one hc,?_⟩
  filter_upwards [hlate] with k hk
  intro D P M W
  have hne : W.Nonempty := ((hk 0).mono (fun _ hm =>
    hm.le.trans (pow_le_pow_left₀ hr.1.le (le_max_left r (7/8:ℝ)) _))).exists
  let m := sInf W
  have hm : m∈W := Nat.sInf_mem hne
  refine ⟨hm,?_⟩
  have hM : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M from pow_pos (Nat.zero_lt_one.trans_le hB) _)
  have h₁ : 1≤(m:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) m]
  rcases h k m P ((1/(7/8:ℝ))^D) with hl|hl
  · have hbase : 1/ρ≤1/(7/8:ℝ) := one_div_le_one_div_of_le (by norm_num) (le_max_right ..)
    have hp : (1/ρ)^(D-3)≤(1/(7/8:ℝ))^D :=
      (pow_le_pow_left₀ (one_div_pos.mpr hρ.1).le hbase _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
    calc
      _ ≤ (1/ρ)^(D-3) := mul_le_of_le_one_left (by positivity) (min_le_left 1 c)
      _ ≤ ((m:ℝ)+1)*(M:ℝ) := hp.trans hl.le
      _ ≤ _ := mul_le_mul (by simpa only [pow_one] using pow_le_pow_right₀ h₁ (by decide : 1≤9))
        (by simpa only [pow_one] using pow_le_pow_right₀ hM (by decide : 1≤10)) (Nat.cast_nonneg _) (by positivity)
  · have hh := (min_le_right 1 c).trans (hl.trans (mul_le_mul_of_nonneg_left hm (by positivity)))
    rw [one_div,inv_pow,←div_eq_mul_inv,div_le_iff₀ (pow_pos hρ.1 _)]
    exact hh

#print axioms gaussian_window_or_ninth_price
#print axioms gaussian_first_ninth_plateau_winding
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
