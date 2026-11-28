import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.CertificateScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Exponential forecast scales at the original plateau crossing -/

open Filter MeasureTheory Real Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open IncrementClocks PrescribedTimes ShortWindows
noncomputable section

/-- Every exponential base below two is eventually reached before the original
first robust crossing. The orbit uses the same Gaussian prefix at every date. -/
theorem date_before_crossing {τ : ℝ} (hτ : 0<τ) (hτ' : τ<2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let K := k+3
      τ^K ≤ crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget K) (9/80) (prefixPoint k ω) := by
  obtain ⟨_,hfirst⟩ := gaussian_path_first_crossing_near_dimension_wait
  have hlog : logb 2 τ<1 := (logb_lt_logb (by norm_num : (1:ℝ)<2) hτ hτ').trans_eq
    (logb_self_eq_one (by norm_num : (1:ℝ)<2))
  have hevent := (tendsto_add_atTop_nat 3).eventually (crossingWidth_exponent_ratio.eventually_const_lt hlog)
  filter_upwards [hfirst] with ω hw
  filter_upwards [hw,hevent] with k hk hl
  intro K
  let P := nearHilbertContinuousCircuitBudget K
  let H := (⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩ :
    selfAdjoint (Matrix (Fin K→Bool) (Fin K→Bool) ℂ))
  have hd (j : ℕ) (t : ℝ) : pathGateDistance (k+1) j (prefixPoint k ω) t=orbitCircuitDistance H j t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [show numberedGenerator (k+1) (prefixPoint k ω)=H.val from numberedGenerator_shell _]
  obtain ⟨σ,hσ,_,he,hbelow,_⟩ := hk
  have hW : 0<crossingWidth K := pow_pos (by norm_num) _
  have hor := crossingOrigin_eq_of_first (hW.trans hσ).le ((hd P σ).trans he)
    (fun t ht => (hd P t).trans_lt (hbelow t ht))
  rw [hor]
  apply le_trans _ hσ.le
  apply ((logb_lt_logb_iff (by norm_num : (1:ℝ)<2) (pow_pos hτ _) hW).mp ?_).le
  rw [logb_pow]
  change logb 2 τ<logb 2 (crossingWidth K)/(K:ℝ) at hl
  simpa only [mul_comm (K:ℝ)] using (lt_div_iff₀ (by dsimp only [K]; positivity : 0<(K:ℝ))).mp hl

/-- A sixth-root sublevel price supports every geometric list with base a
such that a⁶<2. The auxiliary bases separate the price from the Hilbert scale. -/
theorem forecast_bases {a : ℝ} (h₆ : a^6<2) :
    ∃ b τ : ℝ, a<b ∧ b^6<τ ∧ τ<2 := by
  have hnear : ∀ᶠ y in 𝓝 a, y^6<(2:ℝ) := (continuous_pow 6).continuousAt.eventually_lt continuousAt_const h₆
  have hmore : ∀ᶠ y in 𝓝[>] a, a<y := self_mem_nhdsWithin
  obtain ⟨b,hb,hb'⟩ := (hmore.and (hnear.filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨τ,hτ,hτ'⟩ := exists_between hb'
  exact ⟨b,τ,hb,hτ,hτ'⟩

/-- At date τᴷ the polynomial prefactor for the cubic shape is absorbed
whenever the inverse uncertainty base b satisfies b⁶<τ. -/
theorem forecast_scales {b τ : ℝ} (hb : 1<b) (hτ : b^6<τ) (x : ℝ) (hx : 0≤x) :
    ∀ᶠ K : ℕ in atTop, 16*x≤τ^K*sqrt (K:ℝ) ∧
      16000*x*(sqrt (13*(K:ℝ)))^5 < τ^K*((2/3)*(b⁻¹^K)^6) := by
  have hb₀ := zero_lt_one.trans hb
  have hτ₁ := (one_le_pow₀ hb.le : 1≤b^6).trans_lt hτ
  let q := τ/b^6
  have hq : 1<q := (one_lt_div (pow_pos hb₀ 6)).mpr hτ
  let C := 16000*x*13^5
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 5 hq).const_mul C
  have he := hlim.eventually_lt_const (by simp only [mul_zero]; norm_num : C*0<2/3)
  filter_upwards [he,(tendsto_pow_atTop_atTop_of_one_lt hτ₁).eventually_ge_atTop (16*x),
    eventually_ge_atTop 1] with K hpoly hdate hK
  have hn : 1≤(K:ℝ) := by exact_mod_cast hK
  have hs : sqrt (13*(K:ℝ))≤13*(K:ℝ) := sqrt_le_iff.mpr
    ⟨by positivity,by nlinarith only [hn,sq_nonneg ((K:ℝ)-1)]⟩
  have heq : τ^K*((2/3)*(b⁻¹^K)^6)=(2/3)*q^K := by
    rw [show (b⁻¹^K)^6=(b⁻¹^6)^K by rw [←pow_mul,←pow_mul,Nat.mul_comm K 6]]
    simp only [q,div_eq_mul_inv,mul_pow,inv_pow]
    ring
  constructor
  · exact hdate.trans (le_mul_of_one_le_right (pow_nonneg (zero_lt_one.trans hτ₁).le _) (one_le_sqrt.mpr hn))
  · change C*((K:ℝ)^5/q^K)<2/3 at hpoly
    rw [←mul_div_assoc] at hpoly
    rw [heq]
    apply lt_of_le_of_lt _ ((div_lt_iff₀ (pow_pos (zero_lt_one.trans hq) _)).mp hpoly)
    calc
      _ ≤ 16000*x*(13*(K:ℝ))^5 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sqrt_nonneg _) hs _) (by positivity)
      _ = _ := by dsimp only [C]; ring

#print axioms date_before_crossing
#print axioms forecast_scales
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
