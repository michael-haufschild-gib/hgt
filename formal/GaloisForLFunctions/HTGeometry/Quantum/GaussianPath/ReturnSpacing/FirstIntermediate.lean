import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.SeparatedOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # First interval of intermediate complexity after the initial robust crossing -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing
noncomputable section
open SharpOccupation LocalPatches
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private theorem eventually_quadratic_half_budget (J : ℕ) :
    ∀ᶠ N : ℕ in atTop, J*N^2 ≤ nearHilbertContinuousCircuitBudget N/2 := by
  have ht := polynomial_subcritical 3
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1/128),eventually_ge_atTop J] with N hn hJ
  change ((N:ℝ)+1)*(((N^3:ℕ):ℝ)+1)/(2:ℝ)^N<1/128 at hn
  push_cast at hn
  have hh := (div_lt_iff₀ (by positivity : 0<(2:ℝ)^N)).mp hn
  have hNN : (N^3*2*(64*(N+1)):ℕ) ≤ 2^N := by
    exact_mod_cast (show (N:ℝ)^3*2*(64*(N+1)) ≤ 2^N by nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) N])
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  have h₁ : J*N^2 ≤ N^3 := (Nat.mul_le_mul_right _ hJ).trans_eq (by ring)
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h₁)).trans hNN

private theorem size_le_travel_scale {N : ℕ} (hh : 64 ≤ N.sqrt) : (N:ℝ) ≤ (2:ℝ)^(N-10*N.sqrt) := by
  let h := N.sqrt
  have hd := ReturnExcursions.dimension_dominates_speed hh
  have hN : N+1 ≤ (h+1)^2 := by rw [pow_two]; exact Nat.lt_succ_sqrt N
  have hn : N ≤ 2^h := (Nat.le_succ N).trans (hN.trans ((by omega : (h+1)^2 ≤ 64*(h+1)^2).trans hd))
  have hmul := Nat.mul_le_mul_right h (show 11 ≤ h by dsimp [h]; omega)
  have hsq := Nat.sqrt_le N
  change h*h ≤ N at hsq
  have he : h ≤ N-10*h := by omega
  exact_mod_cast hn.trans (Nat.pow_le_pow_right (by decide : 0<2) he)

/-- From the chain's first near-Hilbert crossing, the first center of an
entire intermediate-cost interval is attained. It lies at least R/2 before
the first scalar visit at error 1/10−1/N, where R=N^(1/48)/4. -/
theorem gaussian_first_intermediate_interval :
    ∃ c : ℝ, ∃ J : ℕ, 0<c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let R := (N:ℝ)^((48:ℝ)⁻¹)/4
      ∃ σ v w : ℝ, 0<σ ∧ orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        IsLeast (PrecisionReturns.visitSet H σ 0 (1/10-1/(N:ℝ))) v ∧
        IsLeast (Ici σ ∩ intermediateCenters H (c*Real.sqrt N) (J*N^2) (R/8)) w ∧
        σ+localCrossingWidth N<w ∧ w+R/2 ≤ v := by
  obtain ⟨c,J,hc,hh⟩ := gaussian_deep_visit_centers
  obtain ⟨q,hfirst⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  refine ⟨c,J,hc,?_⟩
  filter_upwards [hh,hfirst,ReturnExcursions.gaussian_robust_travel_time,gaussian_local_robust_travel_time]
    with ω hcent hσ ht hw
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hcent,hσ,ht,hw,
    (tendsto_add_atTop_nat 3).eventually (eventually_quadratic_half_budget J),
    eventually_ge_atTop (64*64)] with k hcσ hdate htravel hwidth hP hlarge
  intro N H P R
  obtain ⟨σ,hpos,he,hprior,_,_⟩ := hdate
  have hσpos : 0<σ := (by positivity : (0:ℝ)<2^(N-10*N.sqrt)).trans hpos
  have hN : (20:ℝ) ≤ N := by exact_mod_cast (show 20 ≤ N by dsimp [N]; omega)
  have hprec : 1/(N:ℝ) ≤ 1/20 :=
    (div_le_div_iff_of_pos_left (by norm_num : (0:ℝ)<1) (by linarith only [hN]) (by norm_num)).mpr hN
  let η := 1/10-1/(N:ℝ)
  have hη : 0<η := by dsimp [η]; linarith only [hprec]
  have htol : η+1/N ≤ 1/10 := (sub_add_cancel _ _).le
  let v := PrecisionReturns.firstVisit H σ 0 η
  have hv := PrecisionReturns.firstVisit_isLeast H σ 0 hη
  have hV : v∈visitSet H 0 η := hv.1.2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsize : R/2 ≤ (N:ℝ) := by
    have hr := Real.rpow_le_rpow_of_exponent_le (by linarith only [hN] : 1 ≤ (N:ℝ)) (by norm_num : (48:ℝ)⁻¹ ≤ 1)
    rw [Real.rpow_one] at hr
    dsimp [R]
    linarith only [hr,hN]
  let d := R/2
  have hvt := htravel σ v he.ge 0 (Nat.zero_le _)
    (approx_enlarge hV (sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) N))) le_rfl)
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hv.1.1)] at hvt
  have hdv := (hsize.trans (size_le_travel_scale (Nat.le_sqrt.mpr (by dsimp [N]; omega)))).trans_lt hvt
  change d < v-σ at hdv
  have hstart : σ ≤ v-d := by linarith only [hdv]
  let S := intermediateCenters H (c*Real.sqrt N) (J*N^2) (R/8)
  have hhit : v-d∈S := hcσ v η htol hV (-d) (by rw [abs_neg,abs_of_nonneg (div_nonneg hR (by norm_num))])
  have hne : (Ici σ ∩ S).Nonempty := ⟨v-d,hstart,hhit⟩
  have hclosed : IsClosed (Ici σ ∩ S) := isClosed_Ici.inter (isClosed_intermediateCenters _ _ _ _)
  have hbd : BddBelow (Ici σ ∩ S) := ⟨σ,fun _ h => h.1⟩
  let w := sInf (Ici σ ∩ S)
  have hmin : IsLeast (Ici σ ∩ S) w := ⟨hclosed.csInf_mem hne hbd,fun _ h => csInf_le hbd h⟩
  have hW := ((mem_intermediateCenters _ _ _ _ _).mp hmin.1.2 w
    (by rw [sub_self,abs_zero]; positivity)).1
  have hsep := hwidth σ w he.ge (J*N^2) hP hW
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hmin.1.1)] at hsep
  change localCrossingWidth N < w-σ at hsep
  have hbound :=  hmin.2 (show v-d∈Ici σ ∩ S from ⟨hstart,hhit⟩)
  exact ⟨σ,v,w,hσpos,he,hprior,hv,hmin,by linarith only [hsep],(le_sub_iff_add_le).mp hbound⟩

#print axioms gaussian_first_intermediate_interval
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing
