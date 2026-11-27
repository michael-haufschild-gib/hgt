import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.AfterVisit.CommonReturn
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Successive near-sweep excursions from the original first low return -/

open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open PrecisionReturns SharpOccupation RepeatedGates.PhysicalBlocks
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- From the first actual low visit after the near-Hilbert crossing, record the first
low return following each near-sweep ascent. Every permitted deficit and height
gives the identical record. The individual ascent times have the deficit power law,
each inter-visit gap is superlinear, and their long-time mean has the sharp
doubly exponential rate at projective operator error one tenth. -/
theorem gaussian_deficit_excursions :
    ∃ κ>(0:ℝ), ∃ δ>(0:ℝ), ∃ γ>(0:ℝ), ∃ Q>(0:ℝ), ∃ l>(0:ℝ), ∃ L>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ a b : ℝ, 0<a → a<physicalArc (1/10) → physicalArc (1/10)<b → ∀ᶠ k : ℕ in atTop,
        let n := k+1
        let K := n+2
        let H : selfAdjoint (Reg K) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        ∀ s : ℕ, ((2*s:ℕ):ℝ)≤κ*K →
          let v := firstLowAfterCrossing ω n s
          ∃ t : ℕ→ℝ, t 0=v ∧
            (∀ i, δ*(K:ℝ)^(65/64:ℝ)<t (i+1)-t i ∧
              ∀ d : ℕ, 0<d → 2*s≤d → (d:ℝ)≤γ*K → Q*(K:ℝ)^11≤(d:ℝ)^20 →
                ∀ ρ∈Icc (9/80:ℝ) (1/8), ∃ τ : ℝ,
                  IsLeast {h : ℝ | 0≤h ∧ ρ≤orbitCircuitDistance H (n+1-d) (t i+h)} τ ∧
                  orbitCircuitDistance H (n+1-d) (t i+τ)=ρ ∧
                  l*K≤τ^9*(d:ℝ)^10 ∧ τ^9*(d:ℝ)^10≤L*K ∧
                  t (i+1)=firstVisit H (t i+τ) s (1/10)) ∧
            ∀ᶠ i : ℕ in atTop, 1/b^(2^K)<(t i-v)/i ∧ (t i-v)/i<1/a^(2^K) := by
  obtain ⟨κ,hκ,A,_,δ,hδ,γ,hγ,Q,hQ,l,hl,L,hL,hstep⟩ := gaussian_deficit_common_return
  refine ⟨min κ 1,lt_min hκ zero_lt_one,δ,hδ,γ,hγ,Q,hQ,l,hl,L,hL,?_⟩
  filter_upwards [hstep,gaussian_physical_return_rates] with ω hs hr
  intro a b ha ha' hb
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) := ⟨by norm_num,(lt_sqrt (by norm_num)).mpr (by norm_num)⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hs,
    hr (fun N => N^1) (polynomial_subcritical 1) (1/10) he a b ha ha' hb] with k hw hrate
  intro n K H s hbudget v
  have hK : 0≤(K:ℝ) := Nat.cast_nonneg _
  have hcap : (2*s:ℕ)≤(K:ℝ) := hbudget.trans
    ((mul_le_mul_of_nonneg_right (min_le_right κ (1:ℝ)) hK).trans_eq (one_mul _))
  have hsize : 2*s≤K := by exact_mod_cast hcap
  have hfit : HasProjectiveCircuitApproximation K (1/10) s (unitaryEvolution H.val v) :=
    (firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2
  obtain ⟨t,hrec,hmean⟩ := (hrate s (show s≤K^1 by rw [pow_one]; omega) v).2
  have hpair : ((s+s:ℕ):ℝ)≤κ*K := by
    rw [←two_mul]
    exact hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hK)
  refine ⟨t,hrec.1,?_,hmean⟩
  intro i
  have hv : HasProjectiveCircuitApproximation K (1/10) s (unitaryEvolution H.val (t i)) := by
    cases i with
    | zero => rwa [hrec.1]
    | succ j => exact (hrec.2 j).1.2
  have hnext := (hrec.2 i).unique (firstVisit_isLeast H (t i+1) s (by norm_num : (0:ℝ)<1/10))
  obtain ⟨hgap,_,hx⟩ := hw (t i) s s hpair hv
  refine ⟨?_,?_⟩
  · rw [hnext]
    linarith only [hgap]
  · intro d hd hsd hdg hdQ ρ hρ
    obtain ⟨τ,hm,he,hlo,hhi,_,_,hw'⟩ := hx d hd hsd hdg hdQ ρ hρ
    exact ⟨τ,hm,he,hlo,hhi,hnext.trans hw'.symm⟩

#print axioms gaussian_deficit_excursions
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
