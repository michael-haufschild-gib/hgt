import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialBudgets.FirstArc
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.ScalarFloor

/-! # The common first return after initial robust crossings at linear budgets -/

open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.InitialBudgets
open FirstAscent FirstAscent.ThermodynamicEdges PrecisionReturns PrescribedTimes
open SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
noncomputable section

/-- A closed crossing set which contains b and misses [0,a) has an
attained first crossing in [a,b]. -/
theorem crossingOrigin_in_bracket {n j : ℕ} {x : PrefixIndex n→ℝ} {ρ a b : ℝ}
    (hb : 0≤b) (hh : ρ≤pathGateDistance n j x b)
    (he : ∀ t∈Ico (0:ℝ) a, pathGateDistance n j x t<ρ) :
    crossingOrigin n j ρ x∈Icc a b ∧ ρ≤pathGateDistance n j x (crossingOrigin n j ρ x) := by
  let S := {t : ℝ | 0≤t ∧ ρ≤pathGateDistance n j x t}
  have hne : S.Nonempty := ⟨b,hb,hh⟩
  have hlo : BddBelow S := ⟨0,fun _ h => h.1⟩
  have hc : IsClosed S := isClosed_Ici.inter
    (isClosed_le continuous_const ((continuous_distance n j).comp (continuous_const.prodMk continuous_id)))
  have hm := hc.csInf_mem hne hlo
  change sInf S∈Icc a b ∧ ρ≤pathGateDistance n j x (sInf S)
  exact ⟨⟨le_of_not_gt fun h => (he _ ⟨hm.1,h⟩).not_ge hm.2,csInf_le hlo ⟨hb,hh⟩⟩,hm.2⟩

/-- From identity, all budgets j through a fixed positive fraction of
the wires reach every robust height in [9/80,1/8] on the first arc.
For each low budget s all those crossings lead to the same first
1/10 visit. Its lower and upper deadlines use the original sample. -/
theorem gaussian_common_first_excursion :
    ∃ κ>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let W := physicalWidth ω n
      let H := shellOperator (pathPauliDisorderShell ω n)
      let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
      let a := 4*arcsin (11/200)/W
      let b := π/W
      let T := δ*K/(log K)^2
      let p := zeroGateArcDensity (2^(n+2)) (SharpOccupation.physicalArc (1/10)/2)
      ∀ j : ℕ, (j:ℝ)≤κ*K → ∀ ρ∈Icc (9/80:ℝ) (1/8),
        let σ := crossingOrigin n j ρ x
        σ∈Icc a b ∧ ρ≤orbitCircuitDistance H j σ ∧ ∀ s : ℕ, (s:ℝ)≤κ*K →
          let v := firstVisit H σ s (1/10)
          v=firstVisit H b s (1/10) ∧ T<v ∧ p*v≤4*arcsin (1/20)/W := by
  obtain ⟨κ,hκ,δ,hδ,h⟩ := gaussian_common_gap
  obtain ⟨_,_,_,_,hc⟩ := gaussian_initial_clock
  refine ⟨κ,hκ,δ,hδ,?_⟩
  filter_upwards [h,hc] with ω hω hc
  filter_upwards [hω,hc] with n hn hclock
  intro K W H x a b T p j hj ρ hρ σ
  obtain ⟨hW,ha,hb,he,hgap⟩ := hn
  have hdist (t : ℝ) : pathGateDistance n j x t=orbitCircuitDistance H j t := by
    rw [pathGateDistance,numberedGenerator_shell (pathPauliDisorderShell ω n)]
    rfl
  have hbr := crossingOrigin_in_bracket (x:=x) (j:=j) (ρ:=ρ) (a:=a) (b:=b)
    (ha.1.trans ha.2) (by rw [hdist]; exact hρ.2.trans (hgap j hj).1.le) (by
      intro t ht
      obtain ⟨z,hz,C,hC,hfit⟩ := he t ⟨ht.1,ht.2.le⟩
      have hf : HasProjectiveCircuitApproximation (n+2) (11/100) j (unitaryEvolution H.val t) :=
        ⟨z,hz,C,hC.trans (Nat.zero_le j),hfit⟩
      rw [hdist]
      exact ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hf).trans_lt
        ((by norm_num : (11/100:ℝ)<9/80).trans_le hρ.1))
  refine ⟨hbr.1,(hdist σ) ▸ hbr.2,?_⟩
  intro s hs v
  have hg {y : ℝ} (hy : y∈Icc a T) :=
    firstVisit_on_gap H s (1/10) (1/10) (by norm_num) le_rfl (hgap s hs).2 hy
  obtain ⟨hdate,hσ⟩ := hg (show σ∈Icc a T from ⟨hbr.1.1,hbr.1.2.trans hb⟩)
  have hb' := (hg (show b∈Icc a T from ⟨ha.2,hb⟩)).2
  refine ⟨hσ.trans hb'.symm,hdate,?_⟩
  change p*firstVisit H σ s (1/10)≤_
  rw [hσ]
  have hU := PrefixDeadlines.HaarWindows.static_scalar_deadline H
    (by norm_num : (1/10:ℝ)∈Ioo (0:ℝ) 2) s a ha.1
  apply hU.trans
  let d := 4*arcsin (1/20)/W
  have hd : 0≤d := div_nonneg (mul_nonneg (by norm_num) (arcsin_nonneg.mpr (by norm_num))) hW.le
  have hsub : SharpOccupation.visitSet H 0 (1/10) ∩ Icc 0 a ⊆ Icc 0 d := by
    intro t ht
    have hf := (hclock.2.2 t ⟨ht.2.1,ht.2.2.trans ha.2⟩ (1/10) (by norm_num)).mp ht.1
    change t≤4*arcsin ((1/10:ℝ)/2)/W at hf
    rw [show (1/10:ℝ)/2=1/20 by norm_num] at hf
    exact ⟨ht.2.1,hf⟩
  have hv := measureReal_mono (μ:=volume) hsub (measure_Icc_lt_top.ne)
  rw [Real.volume_real_Icc_of_le hd,sub_zero] at hv
  exact hv

#print axioms gaussian_common_first_excursion
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.InitialBudgets
