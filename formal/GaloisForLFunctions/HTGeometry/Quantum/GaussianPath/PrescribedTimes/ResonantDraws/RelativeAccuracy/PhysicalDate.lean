import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.RelativeAccuracy.SelectedMean
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.RelativeAccuracy.RayFraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.RelativeAccuracy.Prices
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.ScalarScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.VariablePrecision.ScalarWindows

/-! # Relative scalar probabilities at finite prescribed delays -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
noncomputable section
open SharpOccupation FirstPassageSelection SpectralJets

/-- One deadline and the relative error of five times two to minus M hold for every delay, every
homogeneous origin and every measurable expansion-closed selection. -/
theorem gaussian_relative_scalar_snapshot (A₀ : ℕ) :
    ∃ C : ℕ, ∀ k : ℕ,
      let n := k+1
      let N := k+3
      let D : ℕ := 2^N
      let M := D^(A₀+1)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      ∀ x : ℝ, 1/(2:ℝ)^M≤x → x+1/(2:ℝ)^(M^2)≤1/2 →
      ∀ t ≥ (2:ℝ)^(D^C), ∀ o : (PrefixIndex n → ℝ) → ℝ, Measurable o →
        (∀ a > (0:ℝ), ∀ y, a*o (a • y)=o y) →
      ∀ B : Set (PrefixIndex n → ℝ), MeasurableSet B → expansionClosed B →
        let p := zeroGateArcDensity D x
        let E := {y | pathGateDistance n 0 y (o y+t)≤zeroGateArcTolerance x}
        |μ.real (B ∩ E)-μ.real B*p| ≤ 5*p*(1/(2:ℝ)^M) := by
  let D (k : ℕ) := 2^(k+3)
  let M (k : ℕ) := (D k)^(A₀+1)
  have hM : PolynomialInDimension M := ⟨A₀+1,fun _ => le_rfl⟩
  let q (k : ℕ) := (M k)^3
  have hq : PolynomialInDimension q := ⟨(A₀+1)*3,fun k => by dsimp only [q,M,D]; rw [pow_mul]⟩
  obtain ⟨c,hclock⟩ := gaussian_scalar_confidence_bits (fun k => (M k)^2) q
    hM.square hq
  let G (k : ℕ) := (2:ℝ)^((D k)^c)
  have hG : LogPolynomialInDimension G := LogPolynomialInDimension.twoPow ⟨c,fun _ => le_rfl⟩
  obtain ⟨C,hC⟩ := (((LogPolynomialInDimension.twoPow hM).mul hG).mul
    (LogPolynomialInDimension.twoPow hq)).bound
  refine ⟨C,fun k => ?_⟩
  intro n N D₀ M₀ μ x hx hx' t ht o ho hcov B hm hB p E
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let h := 1/(2:ℝ)^(q k)
  let δ := 1/(2:ℝ)^(M₀^2)
  let v := 1/(2:ℝ)^M₀
  let b := 1+h
  let m := Fintype.card (PrefixIndex n)
  have hD : 8≤D₀ := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by dsimp only [N]; omega : 3≤N)
  have hDM : D₀≤M₀ := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<D₀) (by omega : 1≤A₀+1)
  have hv : 0<v := one_div_pos.mpr (pow_pos (by norm_num) _)
  have hv' : v≤1/2 := one_div_le_one_div_of_le zero_lt_two (by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 1≤M₀))
  have hm' : m≤12*D₀ := by
    have hh : m≤12*N := by
      dsimp only [m]
      rw [Fintype.card_congr (pathCoeffEquiv n)]
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
      dsimp only [n,N]; omega
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n:=N)).le)
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hh : 0<h := by dsimp only [h]; positivity
  have hb : 1<b := lt_add_of_pos_right _ hh
  have hb' : b-1=h := by dsimp only [b]; ring
  have hg : 0<G k := pow_pos (by norm_num) _
  have ht' : 0<t := (pow_pos (by norm_num) _).trans_le ht
  have hT : (2:ℝ)^M₀*G k≤(b-1)*t := by
    have hc : (2:ℝ)^M₀*G k*(2:ℝ)^(q k)≤t := (hC k).trans ht
    rw [hb',show h*t=t/(2:ℝ)^(q k) by dsimp only [h]; ring]
    exact (le_div_iff₀ (by positivity)).mpr hc
  have htime : G k≤v*((b-1)*t) := by
    rw [show v*((b-1)*t)=((b-1)*t)/(2:ℝ)^M₀ by dsimp only [v]; ring,le_div_iff₀ (by positivity)]
    simpa only [mul_comm (G k)] using hT
  obtain ⟨hdx,hp,hp',hprice⟩ := scalar_snapshot_prices D₀ m M₀ hD hDM hm' hx
    ((le_add_of_nonneg_right hδ.le).trans hx')
  let X := fun ω i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  obtain ⟨A,hA,hgood⟩ := hclock k
  have hAa : pathPauliDisorderLaw A ≤ ENNReal.ofReal (3*h) := by
    simpa only [_root_.one_div_pow,h] using hA
  have hmp := gaussian_pauli_prefix_coordinates_law n
  have hmain := selected_error X hmp B E hm (measurable_origin_event n 0 _ t o ho) hB hb
    ⟨hp.le,hp'⟩ (r:=4*p*v) (by positivity) (by positivity) A hAa (by
      filter_upwards [hgood,gaussian_path_all_prefixes_maximally_projective] with ω hw hmax hω
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      rw [ray_fraction k 0 ω _ hb ht' o hcov]
      have he := FiniteRecords.scalar_accuracy_with_margin H (hmax k) (hv.trans_le hx) hδ.le hg hv hv' (hw hω)
        hdx hx' (o (X ω)+t) ((b-1)*t) htime
      have hv := mul_le_mul_of_nonneg_right he (abs_nonneg p)
      rw [←abs_mul] at hv
      calc
        _ = |(visitFraction H 0 (zeroGateArcTolerance x) (o (X ω)+t) (o (X ω)+t+(b-1)*t)/p-1)*p| := by
          congr 1; field_simp [hp.ne']
        _ ≤ _ := hv.trans_eq (by rw [abs_of_pos hp]; ring))
  change 3*h+2*(b^m-1)≤p*v at hprice
  exact hmain.trans (by linarith only [hprice])

#print axioms gaussian_relative_scalar_snapshot
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
