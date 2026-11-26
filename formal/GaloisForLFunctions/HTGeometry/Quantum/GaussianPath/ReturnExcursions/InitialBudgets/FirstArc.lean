import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings.DipAntipodes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock
import GaloisForLFunctions.HTGeometry.ArcsineSeries

/-! # An exclusion interval beginning inside the very first spectral arc -/

open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.InitialBudgets
open FirstAscent FirstAscent.ThermodynamicEdges PrecisionReturns
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
noncomputable section

/-- Up to the 11/100 scalar boundary the empty circuit fits. From that
boundary through a polynomial time even a positive density of gates
fails at 1/10. At the first antipode the exclusion has margin 1/8. -/
theorem gaussian_common_gap :
    ∃ κ>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let W := physicalWidth ω n
      let H := shellOperator (pathPauliDisorderShell ω n)
      let a := 4*arcsin (11/200)/W
      let b := π/W
      let T := δ*K/(log K)^2
      0<W ∧ a∈Icc (0:ℝ) b ∧ b≤T ∧
      (∀ t∈Icc (0:ℝ) a, HasProjectiveCircuitApproximation (n+2) (11/100) 0 (unitaryEvolution H.val t)) ∧
      ∀ s : ℕ, (s:ℝ)≤κ*K → 1/8<orbitCircuitDistance H s b ∧
        ∀ t∈Icc a T, 1/10<orbitCircuitDistance H s t := by
  obtain ⟨k,hk,δ,hδ,hlate⟩ := gaussian_extensive_from_first_antipode (e:=1/8) (by norm_num)
  obtain ⟨v,_,hv,_,hclock⟩ := gaussian_initial_clock
  obtain ⟨_,B,_,hB,hmass⟩ := gaussian_path_eventual_coefficient_mass
  let R := π/v
  have hR : 0<R := div_pos pi_pos hv
  let u := (1/200)/(2*R)
  have hu : 0<u := div_pos (by norm_num) (mul_pos two_pos hR)
  let κ := min k (u^2/(42*B))
  have hκ : 0<κ := lt_min hk (div_pos (sq_pos_of_pos hu) (by positivity))
  refine ⟨κ,hκ,δ,hδ,?_⟩
  let size := fun n : ℕ => ((n+2:ℕ):ℝ)
  have htop : Tendsto size atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hratio : Tendsto (fun n => (log (size n))^2/size n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp htop
  filter_upwards [hlate,hclock,hmass] with ω hl hc hm
  filter_upwards [hl,hc,hm,hratio.eventually_lt_const hδ,htop.eventually (eventually_ge_atTop R)]
    with n hl hc hm hlog hsize
  intro K W H a b T
  have hK₁ : 1<K := by dsimp only [K]; exact_mod_cast (show 1<n+2 by omega)
  have hK := zero_lt_one.trans hK₁
  have hWlo : v*K≤W := hc.1
  have hW := (mul_pos hv hK).trans_le hWlo
  have hb : b≤1 := by
    apply (div_le_iff₀ hW).mpr
    rw [one_mul]
    exact ((div_le_iff₀ hv).mp hsize).trans (by simpa only [mul_comm] using hWlo)
  have hT : 1≤T := by
    apply (le_div_iff₀ (sq_pos_of_pos (log_pos hK₁))).mpr
    rw [one_mul]
    exact ((div_lt_iff₀ hK).mp hlog).le
  have ha : 0≤a := div_nonneg (mul_nonneg (by norm_num) (arcsin_nonneg.mpr (by norm_num))) hW.le
  have hab : a≤b := by
    have h := GaloisForLFunctions.arcsin_le_pi_half_mul (11/200) (by norm_num) (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith only [h,pi_pos]) hW.le
  have hbt := hb.trans hT
  refine ⟨hW,⟨ha,hab⟩,hbt,?_,?_⟩
  · intro t ht
    apply (hc.2.2 t ⟨ht.1,ht.2.trans hab⟩ (11/100) (by norm_num)).mpr
    change t≤4*arcsin ((11/100:ℝ)/2)/W
    rw [show (11/100:ℝ)/2=11/200 by norm_num]
    exact ht.2
  intro s hs
  have hs' := hs.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hK.le)
  refine ⟨hl b ⟨le_rfl,hbt⟩ s hs',?_⟩
  intro t ht
  by_cases htb : b≤t
  · exact (by norm_num : (1/10:ℝ)<1/8).trans (hl t ⟨htb,ht.2⟩ s hs')
  have ht₀ := ha.trans ht.1
  have hbr := (le_of_not_ge htb)
  have hscalar : 21/200<orbitCircuitDistance H 0 t := by
    apply lt_of_not_ge
    intro h
    have hh := (hc.2.2 t ⟨ht₀,hbr⟩ (21/200) (by norm_num)).mp
      ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h)
    have hlt := strictMonoOn_arcsin (by norm_num : (21/200:ℝ)/2∈Icc (-1) 1)
      (by norm_num : (11/200:ℝ)∈Icc (-1) 1) (by norm_num)
    exact ((div_lt_div_iff_of_pos_right hW).mpr (mul_lt_mul_of_pos_left hlt (by norm_num : (0:ℝ)<4))).not_ge
      (ht.1.trans hh)
  have hKt : K*t≤R := by
    apply (le_div_iff₀ hv).mpr
    have h := mul_le_mul_of_nonneg_left hWlo ht₀
    nlinarith only [h,(le_div_iff₀ hW).mp hbr]
  have hrad : sqrt ((42*B)*((s:ℝ)/K))≤u := by
    rw [←sqrt_sq hu.le]
    apply sqrt_le_sqrt
    exact (mul_le_mul_of_nonneg_left (((div_le_iff₀ hK).mpr hs).trans (min_le_right ..))
      (by positivity)).trans_eq (by field_simp : (42*B)*(u^2/(42*B))=u^2)
  have h := ShortCircuitReplay.scaled_advantage (pathPauliDisorderShell ω n) s (K*t) hB.le hm.2
  change orbitCircuitDistance H 0 (K*t/K)≤orbitCircuitDistance H s (K*t/K)+
    2*|K*t| *sqrt ((42*B)*((s:ℝ)/K)) at h
  rw [show K*t/K=t by field_simp,abs_of_nonneg (mul_nonneg hK.le ht₀)] at h
  have hcost := mul_le_mul (mul_le_mul_of_nonneg_left hKt zero_le_two) hrad
    (sqrt_nonneg _) (mul_nonneg zero_le_two hR.le)
  have heq : 2*R*u=1/200 := by dsimp only [u]; field_simp
  linarith only [hscalar,h,hcost,heq]

#print axioms gaussian_common_gap
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.InitialBudgets
