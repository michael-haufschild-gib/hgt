import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialBudgets.CommonDate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PhysicalWindow

/-! # Invariance of the first low date through more than one gate per bond -/

open Real Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.InitialBudgets
open FirstAscent FirstAscent.ThermodynamicEdges PrecisionReturns PrescribedTimes
noncomputable section

/-- Advancing the origin up to the first visit preserves that visit,
including when the new origin equals the visit. -/
theorem firstVisit_before_first {n : ℕ} (H : selfAdjoint (PrecisionReturns.Register n))
    (s : ℕ) {e a b : ℝ} (he : 0<e) (hab : a≤b) (hb : b≤firstVisit H a s e) :
    firstVisit H b s e=firstVisit H a s e := by
  have ha := firstVisit_isLeast H a s he
  have hm := firstVisit_isLeast H b s he
  exact le_antisymm (hm.2 ⟨hb,ha.1.2⟩) (ha.2 ⟨hab.trans hm.1.1,hm.1.2⟩)

/-- Given any fixed positive deadline, a positive excess over one gate
per bond is reached by that deadline. All smaller first crossings from
identity, at every robust height in [9/80,1/4], have identical subsequent
first low dates at each budget through a positive fraction of K. -/
theorem gaussian_spanning_common_first_excursion {d : ℝ} (hd : 0<d) :
    ∃ c>0, ∃ κ>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let W := physicalWidth ω n
      let H := shellOperator (pathPauliDisorderShell ω n)
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      let σ₀ := crossingOrigin n 0 (9/80) x
      let p := zeroGateArcDensity (2^(n+2)) (SharpOccupation.physicalArc (1/10)/2)
      ∀ j : ℕ, (j:ℝ)≤(1+c)*((n+1:ℕ):ℝ) → ∀ ρ∈Icc (9/80:ℝ) (1/4),
        let σ := crossingOrigin n j ρ x
        σ∈Icc σ₀ d ∧ ρ≤orbitCircuitDistance H j σ ∧ ∀ s : ℕ, (s:ℝ)≤κ*K →
          let v := firstVisit H σ s (1/10)
          v=firstVisit H (π/W) s (1/10) ∧ δ*K/(log K)^2<v ∧
            p*v≤4*arcsin (1/20)/W := by
  obtain ⟨c,hc,hh⟩ := RepeatedGates.PhysicalBlocks.gaussian_strict_spanning_floor (T:=d) hd
  obtain ⟨κ,hκ,δ,hδ,hg⟩ := gaussian_common_first_excursion
  refine ⟨c,hc,κ,hκ,δ,hδ,?_⟩
  let size := fun n : ℕ => ((n+2:ℕ):ℝ)
  have htop : Tendsto size atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hr : Tendsto (fun n => (log (size n))^2/size n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp htop
  filter_upwards [hh,hg] with ω hh hg
  filter_upwards [hh,hg,hr.eventually_lt_const (div_pos hδ hd)] with n hh hg hr
  intro K W H x σ₀ p j hj ρ hρ σ
  have hK₁ : 1<K := by dsimp only [K]; exact_mod_cast (show 1<n+2 by omega)
  have hK := zero_lt_one.trans hK₁
  have htime : d≤δ*K/(log K)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (log_pos hK₁))).mpr
    have hz := (div_lt_div_iff₀ hK hd).mp hr
    linarith only [hz]
  have heq (i : ℕ) (t : ℝ) : pathGateDistance n i x t=orbitCircuitDistance H i t := by
    rw [pathGateDistance,numberedGenerator_shell (pathPauliDisorderShell ω n)]
    rfl
  have hu : 1/4<orbitCircuitDistance H j d := by
    apply lt_of_not_ge
    intro h
    exact (hh d (by rw [abs_of_pos hd]; exact ⟨le_rfl,le_rfl⟩) j
      ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr h)).not_ge hj
  have hbr := crossingOrigin_in_bracket (x:=x) (j:=j) (ρ:=ρ) (a:=σ₀) hd.le
    (by rw [heq]; exact hρ.2.trans hu.le) (by
      intro t ht
      let S := {w : ℝ | 0≤w ∧ 9/80≤pathGateDistance n 0 x w}
      have hlow : orbitCircuitDistance H 0 t<9/80 := by
        apply lt_of_not_ge
        intro h
        exact ht.2.not_ge (csInf_le (s:=S) ⟨0,fun _ hw => hw.1⟩ ⟨ht.1,by rwa [heq]⟩)
      obtain ⟨z,hz,C,hC,hfit⟩ := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
        (le_refl (orbitCircuitDistance H 0 t))
      rw [heq]
      exact ((hasProjectiveCircuitApproximation_iff_infDist _ j _).mp
        ⟨z,hz,C,hC.trans (Nat.zero_le j),hfit⟩).trans_lt (hlow.trans_le hρ.1))
  refine ⟨hbr.1,(heq j σ) ▸ hbr.2,?_⟩
  intro s hs v
  have hsmall := (hg 0 (by simpa only [Nat.cast_zero] using mul_nonneg hκ.le hK.le) (9/80)
    (by constructor <;> norm_num)).2.2 s hs
  have hdate : firstVisit H σ s (1/10)=firstVisit H σ₀ s (1/10) :=
    firstVisit_before_first H s (by norm_num) hbr.1.1 (hbr.1.2.trans (htime.trans hsmall.2.1.le))
  change firstVisit H σ s (1/10)=_ ∧ _<firstVisit H σ s (1/10) ∧ p*firstVisit H σ s (1/10)≤_
  rwa [hdate]

#print axioms firstVisit_before_first
#print axioms gaussian_spanning_common_first_excursion
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.InitialBudgets
