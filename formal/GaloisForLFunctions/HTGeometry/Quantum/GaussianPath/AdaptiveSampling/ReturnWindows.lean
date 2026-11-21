import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.GaussianRate
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # Continuous return windows from observation times on any affine lattice -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section
open SharpOccupation

private theorem translated_mass {A : Set ℝ} (hA : MeasurableSet A) (a τ u : ℝ) (M : ℕ) :
    (timeLaw a τ M).real ((fun t => t+u) ⁻¹' A) = (timeLaw (a+u) τ M).real A := by
  let μ := (PMF.uniformOfFintype (Fin (M+1))).toMeasure
  let f (i : Fin (M+1)) := a+(i.val:ℝ)*τ
  let g (i : Fin (M+1)) := a+u+(i.val:ℝ)*τ
  have hp : MeasurableSet ((fun t : ℝ => t+u) ⁻¹' A) :=
    hA.preimage (show Measurable (fun t : ℝ => t+u) by fun_prop)
  change ((Measure.map f μ) ((fun t : ℝ => t+u) ⁻¹' A)).toReal = ((Measure.map g μ) A).toReal
  rw [Measure.map_apply (measurable_of_finite f) hp,Measure.map_apply (measurable_of_finite g) hA]
  have he : f ⁻¹' ((fun t : ℝ => t+u) ⁻¹' A) = g ⁻¹' A := by
    ext i
    change (a+(i.val:ℝ)*τ+u ∈ A) ↔ (a+u+(i.val:ℝ)*τ ∈ A)
    rw [add_right_comm]
  rw [he]

/-- A hit anywhere in a continuous window is visible in one of its unit
subintervals. The resulting bound counts lattice starts, including windows
whose only hit lies strictly between observations. -/
private theorem window_bound {n j k : ℕ} {H : selfAdjoint (Register n)} {ε η p W τ : ℝ}
    (hW : 0 ≤ W) (hp : 0 ≤ p) (hunit : windowHits H j ε 1 ⊆ visitSet H k η)
    (hocc : ∀ a : ℝ, ∀ᶠ M : ℕ in atTop, (timeLaw a τ M).real (visitSet H k η) < p) (a : ℝ) :
    ∀ᶠ M : ℕ in atTop, (timeLaw a τ M).real (windowHits H j ε W) ≤ (W+1)*p := by
  classical
  let L := ⌊W⌋₊+1
  let shift (i : Fin L) := (i.val:ℝ)
  let A := visitSet H k η
  have hA : MeasurableSet A := by
    rw [show A = {t | orbitCircuitDistance H k t ≤ η} from
      Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _]
    exact (isClosed_le (orbitCircuitDistance_lipschitz H k).continuous continuous_const).measurableSet
  let B (i : Fin L) := (fun u : ℝ => u+shift i) ⁻¹' A
  have hsub : windowHits H j ε W ⊆ ⋃ i : Fin L, B i := by
    rintro u ⟨v,hv,hvisit⟩
    let i : Fin L := ⟨⌊v-u⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hv.2]))⟩
    have hl : shift i ≤ v-u := Nat.floor_le (sub_nonneg.mpr hv.1)
    have hr : v-u < shift i+1 := Nat.lt_floor_add_one _
    exact mem_iUnion.mpr ⟨i,hunit ⟨v,⟨by linarith only [hl],by linarith only [hr]⟩,hvisit⟩⟩
  have hb (i : Fin L) : ∀ᶠ M : ℕ in atTop, (timeLaw a τ M).real (B i) ≤ p := by
    filter_upwards [hocc (a+shift i)] with M hM
    exact (translated_mass hA a τ (shift i) M).le.trans hM.le
  filter_upwards [Filter.eventually_all.mpr hb] with M hm
  calc
    _ ≤ ∑ i : Fin L, (timeLaw a τ M).real (B i) :=
      (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le B)
    _ ≤ (L:ℝ)*p := by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [L]; push_cast; linarith only [Nat.floor_le hW]) hp

private theorem unit_overhead :
    ∀ᶠ n : ℕ in atTop, nearHilbertContinuousCircuitBudget n+n^4 ≤ 2^n/(32*(n+1)) := by
  have ht := (polynomial_subcritical 4).eventually_lt_const (by norm_num : (0:ℝ)<1/64)
  filter_upwards [ht] with n hn
  have h := (div_lt_iff₀ (by positivity : 0 < (2:ℝ)^n)).mp hn
  push_cast at h
  have he : (n:ℝ)^4*(64*((n:ℝ)+1)) ≤ (2:ℝ)^n := by nlinarith only [h,Nat.cast_nonneg (α := ℝ) n]
  have hP : n^4 ≤ nearHilbertContinuousCircuitBudget n := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    exact_mod_cast he
  let P := nearHilbertContinuousCircuitBudget n
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  calc
    _ ≤ (P+P)*(32*(n+1)) := Nat.mul_le_mul_right _ (Nat.add_le_add_left hP P)
    _ = P*(64*(n+1)) := by ring
    _ ≤ 2^n := Nat.div_mul_le_self _ _

/-- On almost every fixed chain, every nonzero period and every origin
give a doubly exponentially small fraction of lattice starts whose
continuous forward window of length (3/2)ᴰ contains any P-gate return. -/
theorem gaussian_all_periods_continuous_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a τ : ℝ, τ ≠ 0 → ∀ᶠ M : ℕ in atTop,
        (timeLaw a τ M).real (windowHits H (nearHilbertContinuousCircuitBudget N) (1/10)
          ((3/2:ℝ)^D)) ≤ 2*(3/4:ℝ)^D := by
  filter_upwards [gaussian_physical_half_power,gaussian_unit_hit_enlargement] with ω hocc hunit
  filter_upwards [hocc,hunit (3/20) (by norm_num),(tendsto_add_atTop_nat 3).eventually unit_overhead]
    with k hk hu hbudget
  intro N D H a τ hτ
  let P := nearHilbertContinuousCircuitBudget N
  have hs := hu P (1/10)
  norm_num only [show (1/10:ℝ)+3/20 = 1/4 by norm_num] at hs
  have hb (c : ℝ) := (hk c τ hτ).mono fun M hm => hm (P+N^4) hbudget
  have ht := window_bound (W := (3/2:ℝ)^D) (by positivity) (by positivity) hs hb a
  have hW : 1 ≤ (3/2:ℝ)^D := one_le_pow₀ (by norm_num)
  filter_upwards [ht] with M hm
  apply hm.trans
  calc
    _ ≤ (2*(3/2:ℝ)^D)*(1/2:ℝ)^D := mul_le_mul_of_nonneg_right (by linarith only [hW]) (by positivity)
    _ = _ := by rw [mul_assoc,←mul_pow]; norm_num

/-- Sample from the first robust crossing at integer multiples of its own
first return wait. Index one is a genuine s-gate visit. An exponentially
small fraction of all indices see even a P-gate visit in the full following
window, whose length is doubly exponential in the qubit count. -/
theorem gaussian_first_wait_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ : ℝ, 0 < σ ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ < v ∧ IsLeast {t | σ ≤ t ∧ t ∈ visitSet H s (1/10)} v ∧
          ∀ᶠ M : ℕ in atTop, (timeLaw σ (v-σ) M).real
            (windowHits H P (1/10) ((3/2:ℝ)^D)) ≤ 2*(3/4:ℝ)^D := by
  obtain ⟨_,hfirst⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [hfirst,gaussian_all_periods_continuous_wait] with ω hω hclock
  filter_upwards [hω,hclock] with k hk hc
  intro N D H P
  obtain ⟨σ,hpos,heq,hprior,_,hs⟩ := hk
  have hB : 0 < (2:ℝ)^(N-10*N.sqrt) := by positivity
  refine ⟨σ,hB.trans hpos,heq,hprior,?_⟩
  intro s hsp
  obtain ⟨v,hv,hmin,_,_⟩ := hs s hsp
  have hσv : σ < v := (lt_add_of_pos_right σ hB).trans hv
  exact ⟨v,hσv,hmin,hc σ (v-σ) (sub_pos.mpr hσv).ne'⟩

#print axioms gaussian_first_wait_clock
#print axioms gaussian_all_periods_continuous_wait
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
