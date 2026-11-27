import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.AfterVisit.Rebound
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion.BudgetDistance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget

/-! # The final near-sweep descent before the original first low return -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrecisionReturns SharpOccupation
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- The maximal open interval around a visit on which the near-sweep
budget has distance below ρ has two attained endpoints. Each side has
the same missing-gate power law, without symmetry of the particular dip. -/
theorem gaussian_low_visit_interval :
    ∃ γ>0, ∃ Q>0, ∃ l>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ d s : ℕ, 0<d → 2*s≤d → (d:ℝ)≤γ*K → Q*K^11≤(d:ℝ)^20 →
        ∀ v : ℝ, HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) →
          ∀ ρ∈Icc (9/80:ℝ) (1/8), let f := orbitCircuitDistance H (n+1-d)
          ∃ a b : ℝ, a<v ∧ v<b ∧ f a=ρ ∧ f b=ρ ∧ (∀ w∈Ioo a b, f w<ρ) ∧
            (v-a)^9*(d:ℝ)^10∈Icc (l*K) (L*K) ∧ (b-v)^9*(d:ℝ)^10∈Icc (l*K) (L*K) := by
  obtain ⟨γ,hγ,Q,hQ,l,hl,L,hL,hstep⟩ := gaussian_visit_crossing_scale
  refine ⟨γ,hγ,Q,hQ,l,hl,L,hL,?_⟩
  filter_upwards [hstep] with ω hw
  filter_upwards [hw] with n hn
  intro K H d s hd hs hdg hsc v hv ρ hρ f
  obtain ⟨u,hm,he,hlo,hhi⟩ := hn d s hd hs hdg hsc v hv ρ hρ
  obtain ⟨r,hr,he',hlo',hhi'⟩ := hn d s hd hs hdg hsc (-v) (hv.neg_time H) ρ hρ
  have hK : 0<K := by dsimp only [K]; positivity
  have pos (x : ℝ) (hx : 0≤x) (h : l*K≤x^9*(d:ℝ)^10) : 0<x := by
    apply lt_of_le_of_ne hx
    intro hz
    rw [←hz,zero_pow (by decide),zero_mul] at h
    exact (mul_pos hl hK).not_ge h
  have href (x : ℝ) : f (-v+x)=f (v-x) := by
    rw [show -v+x= -(v-x) by ring]
    exact orbitCircuitDistance_neg_time H _ _
  change f (-v+r)=ρ at he'
  rw [href] at he'
  refine ⟨v-r,v+u,sub_lt_self _ (pos _ hr.1.1 hlo'),lt_add_of_pos_right _ (pos _ hm.1.1 hlo),
    he',he,?_,?_,?_⟩
  · intro w hw
    by_contra! h
    rcases le_total w v with hvw|hvw
    · have heq : f (-v+(v-w))=f w := (href _).trans (by rw [sub_sub_cancel])
      have hh := hr.2 (show v-w∈{x : ℝ | 0≤x ∧ ρ≤f (-v+x)} from
        ⟨sub_nonneg.mpr hvw,by rwa [heq]⟩)
      linarith only [hw.1,hh]
    · have hh := hm.2 (show w-v∈{x : ℝ | 0≤x ∧ ρ≤f (v+x)} from
        ⟨sub_nonneg.mpr hvw,by rwa [show v+(w-v)=w by ring]⟩)
      linarith only [hw.2,hh]
  · simpa only [sub_sub_cancel] using (show r^9*(d:ℝ)^10∈Icc (l*K) (L*K) from ⟨hlo',hhi'⟩)
  · simpa only [add_sub_cancel_left] using (show u^9*(d:ℝ)^10∈Icc (l*K) (L*K) from ⟨hlo,hhi⟩)

private theorem sweep_le_plateau : ∀ᶠ N : ℕ in atTop, N≤nearHilbertContinuousCircuitBudget N := by
  filter_upwards [(polynomial_subcritical 1).eventually_lt_const (by norm_num : (0:ℝ)<1/64)] with N h
  apply (Nat.le_div_iff_mul_le (by positivity : 0<64*(N+1))).mpr
  have hh := (div_lt_iff₀ (by positivity : 0<(2:ℝ)^N)).mp h
  simp only [pow_one] at hh
  have hp : (N:ℝ)*(64*((N:ℝ)+1))≤(2:ℝ)^N := by nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) N]
  exact_mod_cast hp

/-- In the original first excursion, the last near-sweep 9/80 crossing
before the actual s-gate return lies after or at the first near-Hilbert
crossing. From this last crossing the actual remaining wait is of order
(K/d¹⁰)^(1/9), uniformly in the missing count d. -/
theorem gaussian_first_dip_terminal_interval :
    ∃ γ>(0:ℝ), ∃ Q>(0:ℝ), ∃ l>(0:ℝ), ∃ L>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let H : selfAdjoint (Reg K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget K
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ w∈Ico 0 σ, orbitCircuitDistance H P w<9/80) ∧
        ∀ d s : ℕ, 0<d → 2*s≤d → (d:ℝ)≤γ*K → Q*(K:ℝ)^11≤(d:ℝ)^20 →
          let v := firstVisit H σ s (1/10)
          let f := orbitCircuitDistance H (k+2-d)
          ∃ a b : ℝ, σ≤a ∧ a<v ∧ v<b ∧ f a=9/80 ∧ f b=9/80 ∧
            (∀ w∈Ioo a b, f w<9/80) ∧ firstVisit H a s (1/10)=v ∧
            (v-a)^9*(d:ℝ)^10∈Icc (l*K) (L*K) ∧ (b-v)^9*(d:ℝ)^10∈Icc (l*K) (L*K) := by
  obtain ⟨γ,hγ,Q,hQ,l,hl,L,hL,hvisit⟩ := gaussian_low_visit_interval
  obtain ⟨_,hcross⟩ := gaussian_hilbert_first_crossing
  refine ⟨γ,hγ,Q,hQ,l,hl,L,hL,?_⟩
  filter_upwards [hvisit,hcross] with ω hw hx
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hw,hx,(tendsto_add_atTop_nat 3).eventually sweep_le_plateau]
    with k hn hfirst hbudget
  intro K H P
  have hP : P≤2^K/(16*(K+1)) := by
    apply Nat.div_le_div_left <;> dsimp [P,nearHilbertContinuousCircuitBudget,K] <;> omega
  obtain ⟨σ,hσ,he,hpre,_⟩ := hfirst P hP
  refine ⟨σ,hσ,he,hpre,?_⟩
  intro d s hd hs hdg hsc v f
  have hv := firstVisit_isLeast H σ s (by norm_num : (0:ℝ)<1/10)
  obtain ⟨a,b,ha,hb,hfa,hfb,hint,hlo,hhi⟩ := hn d s hd hs hdg hsc v hv.1.2 (9/80)
    (by constructor <;> norm_num)
  have hhigh : 9/80≤f σ := by
    rw [←he]
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val σ)
      (k+2-d) (f σ)).mpr le_rfl
    exact ⟨z,hz,C,hC.trans ((show k+2-d≤K by dsimp only [K]; omega).trans hbudget),hfit⟩
  have hsa : σ≤a := le_of_not_gt fun h => (hint σ ⟨h,hv.1.1.trans_lt hb⟩).not_ge hhigh
  have hu := firstVisit_isLeast H a s (by norm_num : (0:ℝ)<1/10)
  have hv' : firstVisit H a s (1/10)=v := le_antisymm (hu.2 ⟨ha.le,hv.1.2⟩)
    (hv.2 ⟨hsa.trans hu.1.1,hu.1.2⟩)
  exact ⟨a,b,hsa,ha,hb,hfa,hfb,hint,hv',hlo,hhi⟩

#print axioms gaussian_low_visit_interval
#print axioms gaussian_first_dip_terminal_interval
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
