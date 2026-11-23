import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.DurationCharge
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CircuitWindows.ComponentSweep
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.EntryStatistics

/-! # A microscopic circuit-transfer error at most genuine scalar entries -/
open Filter MeasureTheory Real Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
open EmptyVisitFlux SharpOccupation Depth
noncomputable section

private theorem fraction_long {E : Set ℝ} {a h rate M α : ℝ} (hh : 0<h) (hr : 0<rate)
    (F : ℝ → Finset ℝ) (hF : ∀ u T, u∈F T → u∈Icc a T ∧ Entry E u)
    (hf : Tendsto (fun T => ((F T).card:ℝ)/(T-a)) atTop (𝓝 rate))
    (ho : Tendsto (fun T => volume.real (E∩Icc a T)/(F T).card) atTop (𝓝 M))
    (ha : M<h*α) : ∀ᶠ T : ℝ in atTop,
      ((longVisits E h (F T)).card:ℝ)/(F T).card < α := by
  have ht : Tendsto (fun T : ℝ => T-a) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have hz := (ht.const_div_atTop h).div hf hr.ne'
  rw [zero_div] at hz
  have hzero : Tendsto (fun T => h/(F T).card) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [eventually_gt_atTop a] with T hT
    exact div_div_div_cancel_right₀ (sub_pos.mpr hT).ne' _ _
  have hv := ho.add hzero
  rw [add_zero] at hv
  filter_upwards [hv.eventually_lt_const ha] with T hT
  have hc := div_le_div_of_nonneg_right (duration_charge E a T h hh.le (F T) (fun u => hF u T))
    (Nat.cast_nonneg (F T).card)
  rw [add_div,mul_div_right_comm] at hc
  exact (mul_lt_mul_iff_left₀ hh).mp (by simpa only [mul_comm h] using hc.trans_lt hT)

/-- Outside at most a fraction proportional to 1/L of entries, every
circuit affordable anywhere in the same scalar component transfers to its
entry with N−1 more gates and additional error O(L²/D²). The same good
entries work for all budgets and all inner tolerances. -/
theorem gaussian_typical_component_sweep :
    ∃ C B : ℝ, 0<C ∧ 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun i => -H.2.isHermitian.eigenvalues i
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ ρ∈Ioo (0:ℝ) (sqrt 2), ∀ L>0, ∀ α : ℝ, C/L<α → ∀ᶠ T : ℝ in atTop,
          let F := entriesAfter E (physicalArc ρ) σ T
          ∃ A ⊆ F, ((F \ A).card:ℝ)/F.card < α ∧ ∀ u∈A, ∀ v≥u, Icc u v ⊆ visitSet H 0 ρ →
            v-u<L/((D:ℝ)*sqrt N) ∧ ∀ s δ, v∈visitSet H s δ → u∈visitSet H (s+(N-1)) (δ+B*L^2/D^2) := by
  classical
  obtain ⟨c,C,hc,_,hflux⟩ := SpectralGapMass.gaussian_crossing_rate_and_residence
  obtain ⟨_,b,_,hb,hM⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨1/c,84*b,by positivity,by positivity,?_⟩
  filter_upwards [hflux,hM,gaussian_empty_visit_flux] with ω hflux hM hentries
  filter_upwards [hflux,(tendsto_add_atTop_nat 1).eventually hM] with k hflux hM
  intro N D H P E
  obtain ⟨σ,hσ,he,hbefore,hstat⟩ := hflux
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro ρ hρ L hL α hα
  let x := physicalArc ρ
  let F := entriesAfter E x σ
  let V := visitSet H 0 ρ
  let h := L/((D:ℝ)*sqrt N)
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hD : 0<(D:ℝ) := by dsimp only [D]; positivity
  have hroot := sqrt_pos.mpr hN
  have hh : 0<h := div_pos hL (mul_pos hD hroot)
  have hx := (physicalArc_spec hρ.1 hρ.2).1
  obtain ⟨hcount,hrate,hocc,hmean⟩ := hstat ρ hρ
  have hr := (mul_pos (pow_pos hx.1 (D-2)) (mul_pos (mul_pos hc (pow_pos hD 2)) hroot)).trans_le hrate.1
  have htime : (D:ℝ)*x/pairTurnRate E<h*α := by
    apply hmean.2.trans_lt
    have hx' : x<1 := hx.2.trans (by norm_num)
    have h₁ := (div_lt_iff₀ hL).mp hα
    have h₂ := (div_lt_iff₀ hc).mp (show 1/c<α*L from h₁)
    dsimp only [h]
    apply (div_lt_iff₀ (mul_pos (mul_pos hc hD) hroot)).mpr
    calc x < 1 := hx'
         _ < α*L*c := h₂
         _ = _ := by field_simp [hD.ne',hroot.ne']; ring
  have hF (u T) (hu : u∈F T) : u∈Icc σ T ∧ Entry V u := by
    have hmem := (hentries k ρ hρ.1 hρ.2).1
    obtain ⟨ht,ha⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hu₀,huT,hentry⟩ := (hmem ..).mp ht
    exact ⟨⟨le_of_not_gt (fun hw => ha ((hmem ..).mpr ⟨hu₀,hw.le,hentry⟩)),huT⟩,hentry⟩
  filter_upwards [fraction_long hh hr F hF hcount hocc htime] with T hT
  let bad := longVisits V h (F T)
  let A := F T \ bad
  have hbad : F T \ A ⊆ bad := by
    intro u hu
    obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp hu
    by_contra hb
    exact hn (Finset.mem_sdiff.mpr ⟨hu,hb⟩)
  refine ⟨A,Finset.sdiff_subset,lt_of_le_of_lt (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_le_card hbad)) (Nat.cast_nonneg _)) hT,?_⟩
  intro u hu v huv hseg
  have hlag : v-u<h := by
    by_contra! hl
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hu).1,
      fun z hz => hseg ⟨hz.1,hz.2.trans (by linarith only [hl])⟩⟩)
  refine ⟨hlag,?_⟩
  intro s δ hv
  let p := pathPauliDisorderShell ω (k+1)
  obtain ⟨z,hz,C,hC,hfit⟩ := BondProducts.bond_sweep_error p (v-u) (sub_nonneg.mpr huv) 1 (by decide)
  have hbound : (v-u)^2*(84*‖p‖^2) ≤ (84*b)*L^2/D^2 := calc
    _ ≤ h^2*(84*(b*(N:ℝ))) := mul_le_mul
      ((sq_le_sq₀ (sub_nonneg.mpr huv) hh.le).mpr hlag.le)
      (mul_le_mul_of_nonneg_left hM.2 (by norm_num)) (by positivity) (sq_nonneg _)
    _ = _ := by
      dsimp only [h]
      rw [div_pow,mul_pow,Real.sq_sqrt hN.le]
      field_simp [hN.ne',hD.ne']
  simp only [Nat.cast_one,div_one] at hfit
  have hback : HasProjectiveCircuitApproximation N ((84*b)*L^2/D^2) (N-1) (unitaryEvolution H.val (v-u)) :=
    ⟨z,hz,C,by simpa only [one_mul] using hC.le,hfit.trans hbound⟩
  have hw := affordable_add_time H hv (hback.neg_time H)
  rwa [show v+ -(v-u)=u by ring] at hw

#print axioms gaussian_typical_component_sweep
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
