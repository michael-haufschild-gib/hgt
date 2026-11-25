import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings.SubcriticalWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.FrozenSchedule

/-! # First physical positive-budget return after a prescribed extremal antipode -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open AntipodalHorizons SharpOccupation
noncomputable section

/-- Elapsed physical time until the first actual s-gate fit, including
the origin if it already fits. -/
def circuitWait (k n s : ℕ) (ε : ℝ) (ω : PathPauliDisorder) :=
  PrecisionReturns.firstVisit (register k ω) (origin k n ω) s ε-origin k n ω

/-- A first visit within L periods is inside the closed physical window.
The visit time is attained because the circuit target is compact. -/
theorem short_wait_hits (k n s : ℕ) {ε : ℝ} (hε : 0<ε) (ω : PathPauliDisorder)
    (hs : Function.Injective (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues)
    {L : ℝ} (h : circuitWait k n s ε ω*periodRate k ω≤L) :
    ω∈gateWindow k n s 0 L ε := by
  let H := register k ω
  let a := origin k n ω
  let t := PrecisionReturns.firstVisit H a s ε
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))
    (fun l => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l))
  let i := topLevel k
  let j : Level k := 0
  obtain ⟨e,he⟩ := physical_sorted_order k ω hs
  have hsimple : Function.Injective E := by
    intro b c hbc
    apply e.symm.injective
    apply hs
    rwa [he,he,e.apply_symm_apply,e.apply_symm_apply]
  have hji : j < i := top_pos k
  have hg : 0<E i-E j := sub_pos.mpr (lt_of_le_of_ne (monotone_sortedTuple _ hji.le) (hsimple.ne hji.ne))
  have ht := (PrecisionReturns.firstVisit_isLeast H a s hε).1
  let q := (t-a)*periodRate k ω
  have hq : 0≤q := mul_nonneg (sub_nonneg.mpr ht.1) (div_nonneg hg.le two_pi_pos.le)
  refine ⟨q,⟨hq,(zero_add L).symm ▸ h⟩,?_⟩
  have hstep : date E i j n q=a+q*(2*π/(E i-E j)) := by dsimp only [a,origin,date,E,i,j]; ring
  have hcancel : periodRate k ω*(2*π/(E i-E j))=1 := by
    change ((E i-E j)/(2*π))*(2*π/(E i-E j))=1
    field_simp [hg.ne',two_pi_pos.ne']
  have hdate : date E i j n q=t := by rw [hstep,show q=(t-a)*periodRate k ω from rfl,mul_assoc,hcancel,mul_one]; abel
  change HasProjectiveCircuitApproximation _ _ _ (unitaryEvolution H.val (date E i j n q))
  rw [hdate]
  exact ht.2

private theorem wait_le_empty (k n s : ℕ) {ε : ℝ} (hε : 0<ε) (ω : PathPauliDisorder) :
    circuitWait k n s ε ω≤elapsed k n ε ω := by
  let H := register k ω
  let a := origin k n ω
  obtain ⟨ht,c,hc,C,hC,hfit⟩ := (PrecisionReturns.firstVisit_isLeast H a 0 hε).1
  exact sub_le_sub_right ((PrecisionReturns.firstVisit_isLeast H a s hε).2
    ⟨ht,c,hc,C,hC.trans (Nat.zero_le s),hfit⟩) _

/-- Summable exclusion of full spectral periods converts to exclusion in
physical time for any larger base, since the bandwidth is O(K). -/
theorem frozen_physical_wait_of_gate_windows {s : ℕ→ℕ} {ε y b : ℝ} (hε : 0<ε) (hy : 0<y) (hyb : y<b)
    (hwindow : ∃ ρ∈Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop, ∀ q : ℝ, ∀ᶠ n : ℕ in atTop,
      let D : ℕ := 2^(k+3)
      pathPauliDisorderLaw.real (gateWindow k n (s (k+3)) q ((1/y)^D) ε)<ρ^(D-3)) :
    ∃ A : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, A k ≤ n k) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let D : ℕ := 2^(k+3)
        (1/b)^D < circuitWait k (n k) (s (k+3)) ε ω := by
  obtain ⟨ρ,hρ,hlate⟩ := hwindow
  obtain ⟨C,hC,hR⟩ := gaussian_periodRate
  have hbp := hy.trans hyb
  let B (k n : ℕ) := gateWindow k n (s (k+3)) 0 ((1/y)^(2^(k+3))) ε
  have hB : ∀ᶠ k : ℕ in atTop, ∀ᶠ n : ℕ in atTop, pathPauliDisorderLaw.real (B k n)<ρ^k := by
    filter_upwards [hlate] with k hk
    have hdim : k ≤ 2^(k+3)-3 := by have := Nat.lt_two_pow_self (n:=k+3); omega
    exact (hk 0).mono fun n hn => hn.trans_le (pow_le_pow_of_le_one hρ.1.le hρ.2.le hdim)
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  obtain ⟨A,hA⟩ := frozen_event_cutoff pathPauliDisorderLaw B hρ hB
  refine ⟨A,?_⟩
  intro n hn
  have hdim : Tendsto (fun k : ℕ => 2^(k+3)) atTop atTop :=
    tendsto_atTop_mono (fun k => (show k≤k+3 by omega).trans (Nat.lt_two_pow_self (n:=k+3)).le) tendsto_id
  have hfast := hdim.eventually (FirstClockIndex.linear_mul_pow_eventually_lt C (one_div_pos.mpr hbp)
    (one_div_lt_one_div_of_lt hy hyb))
  filter_upwards [hA n hn,hR,gaussian_path_all_prefixes_maximally_projective] with ω hω hr hsimple
  filter_upwards [hω,hr,hfast] with k hmiss hrate hexp
  intro D
  let Δ := circuitWait k (n k) (s (k+3)) ε ω
  have hΔ : 0≤Δ := sub_nonneg.mpr (PrecisionReturns.firstVisit_isLeast (register k ω)
    (origin k (n k) ω) (s (k+3)) hε).1.1
  by_contra! hshort
  have hkd : ((k+3:ℕ):ℝ) ≤ (D:ℝ)+1 := (Nat.cast_le.mpr (Nat.lt_two_pow_self (n:=k+3)).le).trans (le_add_of_nonneg_right zero_le_one)
  have hcount : Δ*periodRate k ω ≤ C*((D:ℝ)+1)*(1/b)^D := calc
    Δ*periodRate k ω ≤ Δ*(C*(k+3:ℕ)) := mul_le_mul_of_nonneg_left hrate hΔ
    _ ≤ (1/b)^D*(C*((D:ℝ)+1)) := mul_le_mul hshort (mul_le_mul_of_nonneg_left hkd hC.le) (by positivity) (pow_nonneg (one_div_nonneg.mpr hbp.le) _)
    _ = _ := mul_comm ..
  exact hmiss (short_wait_hits k (n k) _ hε ω (hsimple k).injective (hcount.trans hexp.le))

/-- For each subcritical budget, including every polynomial budget, the
first physical return after a single prescribed late winding has a doubly
exponential lower and upper time bound on the same frozen Gaussian chain.
The two extreme energies determine the time origin. -/
theorem gaussian_two_sided_circuit_wait :
    ∃ c : ℕ, ∀ s : ℕ→ℕ, subcriticalBudget s → ∀ ε∈Ioo (0:ℝ) (sqrt 2), ∀ b∈Ioo (physicalArc ε) 1,
      ∃ A : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, A k ≤ n k) →
        ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
          let D : ℕ := 2^(k+3)
          let Δ := circuitWait k (n k) (s (k+3)) ε ω
          (1/b)^D<Δ ∧ Δ≤2*(2:ℝ)^(D^c) := by
  obtain ⟨c,hu⟩ := gaussian_elapsed_upper
  refine ⟨c,?_⟩
  intro s hs ε hε b hb
  obtain ⟨y,hxy,hyb⟩ := exists_between hb.1
  have hy := (physicalArc_spec hε.1 hε.2).1.1.trans hxy
  obtain ⟨A,hA⟩ := frozen_physical_wait_of_gate_windows hε.1 hy hyb
    (gaussian_subcritical_gate_window hs hε ⟨hxy,hyb.trans hb.2⟩)
  refine ⟨A,?_⟩
  intro n hn
  filter_upwards [hA n hn,hu] with ω hω hup
  filter_upwards [hω,hup ε hε] with k hlow hupper
  exact ⟨hlow,(wait_le_empty k (n k) _ hε.1 ω).trans (hupper (origin k (n k) ω))⟩

#print axioms gaussian_two_sided_circuit_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
