import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.PrimeProbes

/-! # Testing every gate budget on a fixed register from finite prime samples -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws
noncomputable section

/-- A false certificate fits every sample at some budget while the same
budget misses an actual date. One large finite sample controls this
probability simultaneously at every budget through M. -/
theorem recover_budget_sublevels (k r M : ℕ) (ε : ℝ) (afterReturn : Bool)
    {δ : ℝ} (hδ : 0<δ) :
    let n := k+1
    let P := nearHilbertContinuousCircuitBudget (k+3)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n P (9/80)
    let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
    ∃ Q : ℕ, ∀ S : Finset Nat.Primes, Q≤S.card → ∀ᶠ t : ℝ in atTop,
      μ.real {x | ∃ s≤M, x∉orbitBudget n s ε ∧
        ∀ p : S, pathGateDistance n s x (o x+Real.log ((p.val:ℕ):ℝ)*t)≤ε} < δ := by
  classical
  intro n P μ σ o
  let η := δ/(M+1:ℕ)
  have hM : (0:ℝ)<(M+1:ℕ) := by positivity
  have hη : 0<η := div_pos hδ hM
  let F (i : Fin (M+1)) (S : Finset Nat.Primes) (t : ℝ) :=
    (orbitBudget n i.val ε)ᶜ ∩ {x | ∀ p : S, pathGateDistance n i.val x (o x+Real.log ((p.val:ℕ):ℝ)*t)≤ε}
  have hb (i : Fin (M+1)) : ∃ Q : ℕ, ∀ S : Finset Nat.Primes, Q≤S.card →
      ∀ᶠ t : ℝ in atTop, μ.real (F i S t)<η := by
    obtain ⟨L,hS,hL⟩ := prime_probes_recover_maximum k r i.val ε afterReturn
      (orbitBudget n i.val ε)ᶜ (isClosed_orbitBudget ..).measurableSet.compl
    change Tendsto L atTop (𝓝 (μ.real ((orbitBudget n i.val ε)ᶜ ∩ orbitBudget n i.val ε))) at hL
    rw [compl_inter_self,measureReal_empty] at hL
    obtain ⟨Q,hQ⟩ := eventually_atTop.mp (hL.eventually_lt_const hη)
    exact ⟨Q,fun S h => (hS S).eventually_lt_const (hQ S.card h)⟩
  choose N hN using hb
  refine ⟨Finset.univ.sup N,?_⟩
  intro S hS
  have ht : ∀ᶠ t : ℝ in atTop, ∀ i, μ.real (F i S t)<η := eventually_all.mpr
    fun i => hN i S ((Finset.le_sup (f:=N) (Finset.mem_univ i)).trans hS)
  filter_upwards [ht] with t ht
  have hsub : {x | ∃ s≤M, x∉orbitBudget n s ε ∧
      ∀ p : S, pathGateDistance n s x (o x+Real.log ((p.val:ℕ):ℝ)*t)≤ε} ⊆ ⋃ i, F i S t := by
    rintro x ⟨s,hs,hw⟩
    exact mem_iUnion.mpr ⟨⟨s,Nat.lt_succ_of_le hs⟩,hw⟩
  apply lt_of_le_of_lt ((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _))
  calc (∑ i, μ.real (F i S t)) < ∑ _i : Fin (M+1), η :=
         Finset.sum_lt_sum (fun i _ => (ht i).le) ⟨0,Finset.mem_univ _,ht 0⟩
       _ = δ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,η]; field_simp

#print axioms recover_budget_sublevels
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
