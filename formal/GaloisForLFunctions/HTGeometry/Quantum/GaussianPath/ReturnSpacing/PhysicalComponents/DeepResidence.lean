import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.MaximalSpan
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.AfterScalar.FirstRebound

/-! # Last affordable lag and total residence after a deep scalar visit -/
open Set Filter MeasureTheory Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open FirstAscent AfterScalar SharpOccupation
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem fit_before_exit {N s : ℕ} (H : selfAdjoint (Reg N)) {v t : ℝ}
    (ht : 0≤t) (he : t<exitLag H s v) : v+t ∈ visitSet H s (1/10) := by
  by_contra h
  exact (not_le_of_gt he) (csInf_le ⟨0,fun _ hx => hx.1⟩ ⟨ht,h⟩)

/-- A full initial residence before a deep return limits how late one can
still be affordable after it. The largest lag is attained even if the
affordable dates have gaps. -/
theorem gaussian_deep_residence :
    ∃ b c C : ℝ, ∃ M : ℕ, 0<b ∧ 0<c ∧ 0<C ∧ 0<M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        ∀ v : ℝ, HasProjectiveCircuitApproximation N (1/(N:ℝ)^2) 0 (unitaryEvolution H.val v) →
          ∀ s : ℕ, 0<s → M*s≤N →
            let F := (s:ℝ)*sqrt (log (N/s))/(N:ℝ)^2
            let τ := 4*arcsin (1/20)/W
            let S := {t ∈ Icc (0:ℝ) b | v+t ∈ visitSet H s (1/10)}
            Icc 0 (τ+c*F) ⊆ S ∧ S ⊆ Icc 0 (τ+C*F) ∧
              IsGreatest S (sSup S) ∧ sSup S-τ ∈ Icc (c*F) (C*F) ∧
              volume.real S-τ ∈ Icc (c*F) (C*F) := by
  obtain ⟨b,d,C,m,hb,hd,hC,hm,hw⟩ := gaussian_maximal_physical_span
  obtain ⟨f,_,k,hf,_,hk,he⟩ := gaussian_deep_return_exit
  let c := min (d/2) (f/2)
  let M := max m (max k 2)
  have hc : 0<c := lt_min (half_pos hd) (half_pos hf)
  refine ⟨b/2,c,C,M,half_pos hb,hc,hC,hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [hw,he] with ω hw he
  filter_upwards [hw,he] with n hw he
  intro N H W v hv s hs hsize F τ S
  have hsize' (j : ℕ) (hj : j≤M) : j*s≤N := (Nat.mul_le_mul_right s hj).trans hsize
  have hm' := hsize' m (le_max_left ..)
  have hk' := hsize' k ((le_max_left ..).trans (le_max_right ..))
  have htwo := hsize' 2 ((le_max_right ..).trans (le_max_right ..))
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hs' : 0<(s:ℝ) := Nat.cast_pos.mpr hs
  have hrat : 2≤(N:ℝ)/s := (le_div_iff₀ hs').mpr (by exact_mod_cast htwo)
  have hF : 0<F := div_pos (mul_pos hs' (sqrt_pos.mpr (log_pos (by linarith only [hrat])))) (sq_pos_of_pos hN)
  have hτ : 0≤τ := div_nonneg (mul_nonneg (by norm_num) (arcsin_pos.mpr (by norm_num)).le)
    (circuitHamiltonianSpectralWidth_nonneg H)
  let lo := τ+c*F
  have hlo : 0≤lo := add_nonneg hτ (mul_nonneg hc.le hF.le)
  have hcf := mul_lt_mul_of_pos_right ((min_le_right .. : c≤f/2).trans_lt (half_lt_self hf)) hF
  have fit (u : ℝ) (hu : HasProjectiveCircuitApproximation N (1/(N:ℝ)^2) 0 (unitaryEvolution H.val u))
      (t : ℝ) (ht : t∈Icc 0 lo) : u+t ∈ visitSet H s (1/10) := by
    apply fit_before_exit H ht.1
    have hh := (he u hu s hs hk').1
    change f*F≤exitLag H s u-τ at hh
    have ht' : t≤τ+c*F := ht.2
    linarith only [ht',hcf,hh]
  let Q := {t ∈ Icc (0:ℝ) b | ∃ u ∈ visitSet H s (1/10), u+t ∈ visitSet H s (1/10)}
  have hv0 : v ∈ visitSet H s (1/10) := by simpa only [add_zero] using fit v hv 0 ⟨le_rfl,hlo⟩
  have hQ : BddAbove Q := ⟨b,fun _ h => h.1.2⟩
  have hQb : sSup Q≤b := csSup_le ⟨0,⟨le_rfl,hb.le⟩,v,hv0,by simpa only [add_zero] using hv0⟩ (fun _ h => h.1.2)
  have hwidth := hw s hs hm'
  change sSup Q-8*arcsin (1/20)/W ∈ Icc (d*F) (C*F) at hwidth
  have hτ' : 8*arcsin (1/20)/W=2*τ := by dsimp only [τ]; ring
  rw [hτ'] at hwidth
  have hroom : lo≤b/2 := by
    have hcd := mul_le_mul_of_nonneg_right (min_le_left .. : c≤d/2) hF.le
    dsimp only [lo]
    linarith only [hcd,hwidth.1,hQb]
  have hneg := HasProjectiveCircuitApproximation.neg_time H (fit (-v) (hv.neg_time H) lo ⟨hlo,le_rfl⟩)
  have hleft : v-lo ∈ visitSet H s (1/10) := by
    rwa [show -(-v+lo)=v-lo by ring] at hneg
  have hlow : Icc 0 lo ⊆ S := fun t ht => ⟨⟨ht.1,ht.2.trans hroom⟩,fit v hv t ht⟩
  have hup : S ⊆ Icc 0 (τ+C*F) := by
    rintro t ⟨ht,hvisit⟩
    have hmem : t+lo∈Q := ⟨⟨add_nonneg ht.1 hlo,by linarith only [ht.2,hroom]⟩,v-lo,hleft,
      by rwa [show v-lo+(t+lo)=v+t by ring]⟩
    have hbound := le_csSup hQ hmem
    dsimp only [lo] at hbound
    exact ⟨ht.1,by linarith only [hbound,hwidth.2,mul_nonneg hc.le hF.le]⟩
  have hloS := hlow (right_mem_Icc.mpr hlo)
  have hcl : IsClosed S := by
    apply isClosed_Icc.inter
    simp only [visitSet,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le ((orbitCircuitDistance_lipschitz H s).continuous.comp (continuous_const.add continuous_id)) continuous_const
  have hgreat := hcl.isGreatest_csSup ⟨lo,hloS⟩ ⟨b/2,fun _ h => h.1.2⟩
  have hfin : volume S≠⊤ := measure_ne_top_of_subset hup measure_Icc_lt_top.ne
  have h1 := measureReal_mono (μ:=volume) hlow hfin
  have h2 := measureReal_mono (μ:=volume) hup measure_Icc_lt_top.ne
  rw [Real.volume_real_Icc_of_le hlo,sub_zero] at h1
  rw [Real.volume_real_Icc_of_le (add_nonneg hτ (mul_nonneg hC.le hF.le)),sub_zero] at h2
  have hal := hgreat.2 hloS
  have hau := (hup hgreat.1).2
  dsimp only [lo] at hal h1
  exact ⟨hlow,hup,hgreat,⟨by linarith only [hal],by linarith only [hau]⟩,
    ⟨by linarith only [h1],by linarith only [h2]⟩⟩

#print axioms gaussian_deep_residence

/-- Last lag and occupied time at the first deep scalar visit following
the distinguished crossing of the near-Hilbert gate budget. -/
theorem gaussian_first_deep_residence :
    ∃ b c C : ℝ, ∃ M : ℕ, 0<b ∧ 0<c ∧ 0<C ∧ 0<M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          let v := PrecisionReturns.firstVisit H σ 0 (1/(N:ℝ)^2)
          ∀ s : ℕ, 0<s → M*s≤N →
            let F := (s:ℝ)*sqrt (log (N/s))/(N:ℝ)^2
            let τ := 4*arcsin (1/20)/circuitHamiltonianSpectralWidth H
            let S := {t ∈ Icc (0:ℝ) b | v+t ∈ visitSet H s (1/10)}
            Icc 0 (τ+c*F) ⊆ S ∧ S ⊆ Icc 0 (τ+C*F) ∧
              IsGreatest S (sSup S) ∧ sSup S-τ ∈ Icc (c*F) (C*F) ∧
              volume.real S-τ ∈ Icc (c*F) (C*F) := by
  obtain ⟨b,c,C,M,hb,hc,hC,hM,h⟩ := gaussian_deep_residence
  refine ⟨b,c,C,M,hb,hc,hC,hM,?_⟩
  filter_upwards [h,LocalPatches.gaussian_first_crossing_local_width] with ω hh hw
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hh,hw] with k hk hs
  intro N H P
  obtain ⟨σ,hσ,heq,hpre,_⟩ := hs
  have hpos := (show 0 ≤ LocalPatches.localCrossingWidth N by
    unfold LocalPatches.localCrossingWidth; positivity).trans_lt hσ
  refine ⟨σ,hpos,heq,hpre,?_⟩
  intro v
  exact hk v (PrecisionReturns.firstVisit_isLeast H σ 0
    (show 0<1/(N:ℝ)^2 by dsimp only [N]; positivity)).1.2

#print axioms gaussian_first_deep_residence
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
