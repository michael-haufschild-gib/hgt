import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Kinematics.DurationCounts

/-! # Residence tails at the mean time scale following the first crossing -/
open MeasureTheory Finset Filter Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open EmptyVisitFlux SharpOccupation SpectralGapMass.Bulk
noncomputable section

private theorem depth_travel {D m h q : ℝ} (hm : 0<m) (hmD : m≤D) (hq : 0<q)
    (hh : q<h) (hD : q*h/(h-q)≤D) :
    q/D≤1-exp (-h/m) := by
  have hD₀ := hm.trans_le hmD
  have hpos := hq.trans hh
  have hadd := add_pos hm hpos
  have ha : exp (-h/m)≤m/(m+h) := by
    rw [show -h/m= -(h/m) by ring,Real.exp_neg,inv_eq_one_div,div_le_div_iff₀ (exp_pos _) hadd,one_mul]
    calc m+h = m*(h/m+1) := by field_simp [hm.ne']; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (add_one_le_exp _) hm.le
  have hb := (div_le_iff₀ (sub_pos.mpr hh)).mp hD
  have hc : q/D≤h/(m+h) := (div_le_div_iff₀ hD₀ hadd).mpr (by
    linarith only [hb,mul_le_mul_of_nonneg_left hmD hq.le])
  exact hc.trans (by rw [show h/(m+h)=1-m/(m+h) by field_simp [hadd.ne']; ring]; linarith only [ha])

/-- Long residences have positive frequency on the scale 2πr/(D√N).
An entry reaching relative depth exp(−h/(D−2)) must stay this long
unless its closing energy gap exceeds b√N. -/
theorem gaussian_residence_tail_lower :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a b h λ : ℝ, 0<a → 0<b → a*b<h →
      λ<exp (-h)-exp (-(b^2/48)) → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D : ℕ := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget N
        let E := fun i => -H.2.isHermitian.eigenvalues i
        ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          ∀ ρ∈Ioo (0:ℝ) (sqrt 2), let r := physicalArc ρ
            let L := 2*π*r*a/((D:ℝ)*sqrt N)
            let A := entriesAfter E r σ
            ∀ᶠ T : ℝ in atTop, λ<((longVisits (visitSet H 0 ρ) L (A T)).card:ℝ)/(A T).card := by
  filter_upwards [gaussian_first_crossing_closing_gaps,gaussian_scalar_component_depth] with ω hg hd
  intro a b h λ ha hb hab hλ
  obtain ⟨F,hF,hmarks⟩ := hg b hb.le
  have hlim := hF.const_sub (exp (-h))
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp (tendsto_add_atTop_nat 3)
  filter_upwards [hmarks,hlim.eventually_const_lt hλ,
    hpow.eventually (eventually_ge_atTop (a*b*h/(h-a*b)))] with k hk hfrac hlarge
  intro N D H P E
  obtain ⟨σ,hσ,he,hprior,hs⟩ := hk
  refine ⟨σ,hσ,he,hprior,?_⟩
  intro ρ hρ r L A
  let M := D-2
  let m : ℝ := M
  have hDN : 2<D := by
    exact (by norm_num : 2<(2:ℕ)^3).trans_le (Nat.pow_le_pow_right (by norm_num) (by dsimp only [N]; omega))
  have hm : 0<m := by exact_mod_cast (show 0<M by dsimp only [M]; omega)
  have hD : 0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  have hw : a*b/(D:ℝ) ≤ 1-exp (-h/m) := depth_travel hm (by exact_mod_cast Nat.sub_le D 2)
    (mul_pos ha hb) hab (by simpa only [D,N,Nat.cast_pow,Nat.cast_ofNat,Function.comp_apply] using hlarge)
  have hr := (physicalArc_spec hρ.1 hρ.2).1
  let d := r*exp (-h/m)
  have hd₀ : 0<d := mul_pos hr.1 (exp_pos _)
  have hdr : d≤r := mul_le_of_le_one_right hr.1.le (exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ((mul_pos ha hb).trans hab).le) hm.le))
  let δ := zeroGateArcTolerance d
  have hid : d∈Icc (0:ℝ) (1/2) := ⟨hd₀.le,hdr.trans hr.2.le⟩
  have hδ : δ∈Ioc (0:ℝ) ρ := by
    have hz := strictMonoOn_zeroGateArcTolerance (show (0:ℝ)∈Icc 0 (1/2:ℝ) by constructor <;> norm_num) hid hd₀
    have hh := strictMonoOn_zeroGateArcTolerance.monotoneOn hid (Ioo_subset_Icc_self hr) hdr
    exact ⟨by simpa only [δ,zeroGateArcTolerance,mul_zero,zero_div,sin_zero] using hz,
      hh.trans_eq (physicalArc_spec hρ.1 hρ.2).2⟩
  have hδ' : δ∈Ioo (0:ℝ) (sqrt 2) := ⟨hδ.1,hδ.2.trans_lt hρ.2⟩
  have heq : physicalArc δ=d := strictMonoOn_zeroGateArcTolerance.injOn
    (Ioo_subset_Icc_self (physicalArc_spec hδ'.1 hδ'.2).1) hid (physicalArc_spec hδ'.1 hδ'.2).2
  have hratio : (physicalArc δ/r)^M=exp (-h) := by
    rw [heq,show d/r=exp (-h/m) by dsimp only [d]; field_simp [hr.1.ne'],←Real.exp_nat_mul]
    congr 1
    change m*(-h/m)= -h
    field_simp [hm.ne']
  have hchild : Tendsto (fun T : ℝ =>
      ((reached (visitSet H 0 ρ) (visitSet H 0 δ) (A T)).card:ℝ)/(A T).card)
      atTop (𝓝 ((physicalArc δ/r)^M)) := hd k σ hσ.le ρ hρ δ hδ
  rw [hratio] at hchild
  have hcut := (hchild.sub (hs ρ hρ)).eventually_const_lt hfrac
  have hv : 0<sqrt (N:ℝ) := by dsimp only [N]; positivity
  have hL : L*(b*sqrt N/(2*π))≤r-physicalArc δ := by
    rw [heq,show L*(b*sqrt N/(2*π))=r*(a*b/(D:ℝ)) by dsimp only [L]; field_simp [hv.ne',hD.ne']; ring]
    exact (mul_le_mul_of_nonneg_left hw hr.1.le).trans_eq (by dsimp only [d]; ring)
  filter_upwards [hcut] with T hT
  have hcard := depth_mark_cover (pathPauliDisorderShell ω (k+1)) σ T hρ hδ' hb (heq.trans_le hdr) L hL
  have h₁ : ((reached (visitSet H 0 ρ) (visitSet H 0 δ) (A T)).card:ℝ) ≤
      (longVisits (visitSet H 0 ρ) L (A T)).card+
      (((selectedDates E (fastPairs (pathPauliDisorderShell ω (k+1)) b) r T) \ entryDates E r σ).card:ℝ) := by
    exact_mod_cast hcard
  exact hT.trans_le (by rw [←sub_div]; exact div_le_div_of_nonneg_right
    (by linarith only [h₁]) (Nat.cast_nonneg _))

#print axioms gaussian_residence_tail_lower
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
