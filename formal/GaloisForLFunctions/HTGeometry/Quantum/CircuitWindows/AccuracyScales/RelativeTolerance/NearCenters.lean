import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.RelativeTolerance.PolynomialMargin
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.RecurrentCenters

/-! # Near-maximum centers with a polynomial tolerance margin -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
open MaximumIntervals SharpOccupation
noncomputable section

/-- An exponential interval around each center retains an arbitrarily
large fixed fraction of the actual maximum, up to the increment budget.
The explicit center density uses an inverse-cubic scalar tolerance. -/
theorem gaussian_relative_center_density :
    ∀ᵐ e : ℝ ∂volume, e ∈ Ioc (0:ℝ) (11/25) → ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ r > (1:ℝ), ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H := chainGenerator ω k
        let L := ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
        let η := 1/(2*(N:ℝ)^3)
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∃ S : Set ℝ, MeasurableSet S ∧
            (∀ a : ℝ, Tendsto (fun T : ℝ => volume.real (S ∩ Icc a T)/(T-a))
              atTop (𝓝 ((D:ℝ)*(physicalArc η)^(D-1)))) ∧
            ∀ z ∈ S, ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z+t)) →
                (m:ℝ)+1 ≤ r*((j:ℝ)+(L:ℝ)+1) := by
  filter_upwards [gaussian_prescribed_relative_maximum] with e hrel he
  filter_upwards [hrel he.1,gaussian_pauli_prefix_maximum_and_occupation_quantiles,
    gaussian_path_all_prefixes_maximally_projective,LocalPatches.gaussian_exponential_precision_compiler]
    with ω hw hmax hspec hsim
  intro r hr γ α hγ hγα hα
  filter_upwards [hw r hr,hmax,hsim 4 γ α hγ hγα hα.le] with k hk hlarge hs
  intro N D H L η
  obtain ⟨m,n,hm,hn,_,hscale⟩ := hk
  obtain ⟨p,hp,hpmax,_⟩ := hlarge e he
  obtain ⟨v,hv⟩ := required_at_some_date hpmax
  have hmP := hp.trans_le (hv m (hm.1 v))
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (by dsimp only [N]; omega : 1≤N)
  have hNp : 0 < (N:ℝ) := zero_lt_one.trans_le hN
  have hη : 0 < η := by dsimp only [η]; positivity
  have heη : η ≤ 1 := (div_le_one (by positivity : 0<2*(N:ℝ)^3)).mpr
    (by linarith only [one_le_pow₀ hN (n:=3)])
  have hsmall : η < sqrt 2 := heη.trans_lt ((lt_sqrt zero_le_one).mpr (by norm_num))
  have hpaid : 2*η ≤ 1/(N:ℝ)^3 := by dsimp only [η]; rw [le_div_iff₀ (pow_pos hNp _)]; field_simp
  have hp' : (N:ℝ) ≤ (2:ℝ)^N := by exact_mod_cast (Nat.lt_two_pow_self (n:=N)).le
  have h2 : (2:ℝ) ≤ (2:ℝ)^N := by
    change (2:ℝ)^1 ≤ (2:ℝ)^N
    exact pow_le_pow_right₀ (by norm_num) (by dsimp only [N]; omega)
  have hmarg : 1/(2:ℝ)^(4*N) ≤ η := by
    apply one_div_le_one_div_of_le (by positivity : 0<2*(N:ℝ)^3)
    calc
      2*(N:ℝ)^3 ≤ (2:ℝ)^N*((2:ℝ)^N)^3 := mul_le_mul h2 (pow_le_pow_left₀ hNp.le hp' _) (by positivity) (by positivity)
      _ = _ := by rw [←pow_mul,←pow_add]; congr 1; omega
  have hs' (t : ℝ) (ht : |t| ≤ (2:ℝ)^(γ*(N:ℝ))) := LocalPatches.approx_enlarge (hs t ht) hmarg (le_refl L)
  obtain ⟨S,hS,hden,hsur⟩ := centers_of_maximum_clearance H (hspec k) hη hsmall hpaid hn hs'
  refine ⟨m,hmP,hm,S,hS,hden,?_⟩
  intro z hz t ht j hj
  have h := (hsur z hz).2 t ht j hj
  apply hscale.trans
  apply mul_le_mul_of_nonneg_left _ (zero_lt_one.trans hr).le
  exact_mod_cast Nat.add_le_add_right h 1

#print axioms gaussian_relative_center_density
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
