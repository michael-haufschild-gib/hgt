import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion.BudgetDistance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.SubcriticalWait

/-! # Last above-sweep crossing before the original first low return -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks PrecisionReturns SharpOccupation
noncomputable section
private abbrev Reg (K : ℕ) := Matrix (Fin K→Bool) (Fin K→Bool) ℂ

/-- Upper and lower bounds on first-passage lags bound both ends of
the open sublevel interval containing the original first low visit. -/
theorem terminal_descent_of_passages {p : ℕ} (F : ℕ→ℝ→ℝ) {b L : ℝ} (hL : 0<L)
    (hw : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ (v : ℝ) (r q : ℕ), let m : ℝ := (2*r+q:ℕ)
        m≤b*N → HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H.val v) →
        let τ := firstExcessAfter ω n (r+q) v (9/80)
        let f (x : ℝ) := orbitCircuitDistance H (n+1+(r+q)) (v+x)
        τ∈Icc 0 1 ∧ τ^p≤F n m ∧ L≤((n+2:ℕ):ℝ)*τ^2 ∧
          f τ=9/80 ∧ ∀ x∈Ico 0 τ, f x<9/80) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let N : ℝ := (k+2:ℕ)
      let H : selfAdjoint (Reg K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget K
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ w∈Ico 0 σ, orbitCircuitDistance H P w<9/80) ∧
        ∀ r q : ℕ, let m : ℝ := (2*r+q:ℕ)
          m≤b*N → let v := firstVisit H σ r (1/10)
          let f := orbitCircuitDistance H (k+2+(r+q))
          ∃ a z : ℝ, σ≤a ∧ a<v ∧ v<z ∧ f a=9/80 ∧ f z=9/80 ∧
            (∀ w∈Ioo a z, f w<9/80) ∧ firstVisit H a r (1/10)=v ∧
            ∀ x∈({v-a,z-v} : Set ℝ), L≤(K:ℝ)*x^2 ∧
              x^p≤F (k+1) m := by
  obtain ⟨_,hx⟩ := gaussian_hilbert_first_crossing
  have hbig := ReturnExcursions.Iterated.eventually_half_budget (polynomial_subcritical 2)
  filter_upwards [hw,hx] with ω hw hx
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,hx,(tendsto_add_atTop_nat 3).eventually hbig,
    eventually_ge_atTop ⌈b⌉₊] with k hpass hfirst hbig hk
  intro K N H P
  have hP : P≤2^K/(16*(K+1)) := by
    apply Nat.div_le_div_left <;> dsimp only [P,nearHilbertContinuousCircuitBudget,K] <;> omega
  obtain ⟨σ,hσ,he,hpre,_⟩ := hfirst P hP
  refine ⟨σ,hσ,he,hpre,?_⟩
  intro r q m hm v f
  have hv := firstVisit_isLeast H σ r (by norm_num : (0:ℝ)<1/10)
  let l := firstExcessAfter ω (k+1) (r+q) (-v) (9/80)
  let u := firstExcessAfter ω (k+1) (r+q) v (9/80)
  obtain ⟨hl,hlUpper,hl2,hle,hleft⟩ := hpass (-v) r q hm (hv.1.2.neg_time H)
  obtain ⟨hu,huUpper,hu2,hue,hright⟩ := hpass v r q hm hv.1.2
  have pos (t : ℝ) (ht : 0≤t) (ht₂ : L≤(K:ℝ)*t^2) : 0<t := by
    apply lt_of_le_of_ne ht
    rintro rfl
    norm_num at ht₂
    exact hL.not_ge ht₂
  have hl₀ : 0<l := pos l hl.1 hl2
  have hu₀ : 0<u := pos u hu.1 hu2
  have refl (x : ℝ) : f (-v+x)=f (v-x) := by
    rw [show -v+x= -(v-x) by ring]
    exact orbitCircuitDistance_neg_time H _ _
  have hinside (w : ℝ) (hw : w∈Ioo (v-l) (v+u)) : f w<9/80 := by
    rcases le_total w v with hc|hc
    · have h := hleft (v-w) ⟨sub_nonneg.mpr hc,by change v-w<l; linarith only [hw.1]⟩
      change f (-v+(v-w))<_ at h
      rwa [refl,sub_sub_cancel] at h
    · have h := hright (w-v) ⟨sub_nonneg.mpr hc,by change w-v<u; linarith only [hw.2]⟩
      change f (v+(w-v))<_ at h
      rwa [show v+(w-v)=w by ring] at h
  have hbudget : k+2+(r+q)≤P := by
    have hN : 0≤N := Nat.cast_nonneg _
    have hbk : b≤(k:ℝ) := (Nat.le_ceil b).trans (Nat.cast_le.mpr hk)
    have hcount := hm.trans (mul_le_mul_of_nonneg_right hbk hN)
    change ((2*r+q:ℕ):ℝ)≤(k:ℝ)*(k+2:ℕ) at hcount
    have hn : 2*r+q≤k*(k+2) := by exact_mod_cast hcount
    have hsq : k+2+(r+q)≤K^2 := by
      dsimp only [K]
      nlinarith only [hn]
    exact hsq.trans (hbig.trans (Nat.div_le_self _ _))
  have hhigh : 9/80≤f σ := by
    rw [←he]
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    obtain ⟨z,hz,C,hC,he'⟩ := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val σ)
      (k+2+(r+q)) (f σ)).mpr le_rfl
    exact ⟨z,hz,C,hC.trans hbudget,he'⟩
  have hsa : σ≤v-l := le_of_not_gt fun h =>
    (hinside σ ⟨h,hv.1.1.trans_lt (lt_add_of_pos_right v hu₀)⟩).not_ge hhigh
  have hnext := firstVisit_isLeast H (v-l) r (by norm_num : (0:ℝ)<1/10)
  have hsame := le_antisymm (hnext.2 ⟨sub_le_self v hl₀.le,hv.1.2⟩)
    (hv.2 ⟨hsa.trans hnext.1.1,hnext.1.2⟩)
  change f (-v+l)=9/80 at hle
  refine ⟨v-l,v+u,hsa,sub_lt_self v hl₀,lt_add_of_pos_right v hu₀,(refl l).symm.trans hle,
    hue,hinside,hsame,?_⟩
  simp only [sub_sub_cancel,add_sub_cancel_left]
  intro x hx
  rcases hx with h|h
  · subst x; exact ⟨hl2,hlUpper⟩
  · change x=u at h
    subst x; exact ⟨hu2,huUpper⟩

#print axioms terminal_descent_of_passages
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
