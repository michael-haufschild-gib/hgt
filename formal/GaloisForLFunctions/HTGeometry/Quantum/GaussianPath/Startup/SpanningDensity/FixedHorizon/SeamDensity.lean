import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.WeakStrips

/-! # Most path bonds have a weak interaction nearby on either side -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

def absentStrip (γ : ℝ) (R j : ℕ) : Set PathPauliDisorder :=
  {ω | ∀ i : Fin R, ¬ weakRow γ ω (j+i.val)}

theorem measurable_absentStrip (γ : ℝ) (R j : ℕ) : MeasurableSet (absentStrip γ R j) := by
  have h (k : ℕ) : MeasurableSet {ω | weakRow γ ω k} := by
    change MeasurableSet {ω : PathPauliDisorder | ∀ q : Fin 3 × Fin 3, |ω (k,.inr q)|≤γ}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun _ => measurableSet_le (measurable_pi_apply _).abs measurable_const
  unfold absentStrip
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (h _).compl

def failedStrips (γ : ℝ) (R e : ℕ) := absentStrip γ R (e-R) ∪ absentStrip γ R (e+1)

def missedBonds (n R : ℕ) (γ : ℝ) (ω : PathPauliDisorder) : Finset (Fin (n+1)) := by
  classical
  exact Finset.univ.filter fun e => ω∈failedStrips γ R e.val

/-- Given a permitted fraction and failure probability, one fixed radius
suffices for all physical prefixes. Only bonds within that radius of a
chain endpoint still need to be excluded for geometric reasons. -/
theorem gaussian_seam_density {γ η β : ℝ} (hγ : 0<γ) (hη : 0<η) (hβ : 0<β) :
    ∃ R : ℕ, 0<R ∧ ∀ n : ℕ, pathPauliDisorderLaw.real
      {ω | η*(n+1:ℕ) ≤ ((missedBonds n R γ ω).card:ℝ)} ≤ β := by
  classical
  obtain ⟨q,hq,hm⟩ := gaussian_weak_strip hγ
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq.1 hq.2
  obtain ⟨R,hR,hr⟩ := ((eventually_gt_atTop 0).and
    (hlim.eventually_lt_const (half_pos (mul_pos hη hβ)))).exists
  refine ⟨R,hR,?_⟩
  intro n
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by unfold μ pathPauliDisorderLaw; infer_instance
  let S (e : Fin (n+1)) := failedStrips γ R e.val
  have hS (e) : MeasurableSet (S e) := (measurable_absentStrip ..).union (measurable_absentStrip ..)
  have hprob (j : ℕ) : μ.real (absentStrip γ R j)=q^R :=
    hm R (fun i => j+i.val) (fun _ _ h => Fin.ext (Nat.add_left_cancel h))
  have hb (e) : μ.real (S e) ≤ η*β := by
    apply (measureReal_union_le (μ:=μ) _ _).trans
    rw [hprob,hprob]
    linarith only [hr]
  let f (e : Fin (n+1)) := (S e).indicator (fun _ => (1:ℝ))
  let X (ω : PathPauliDisorder) := ∑ e, f e ω
  have hi (e) : Integrable (f e) μ := (integrable_const _).indicator (hS e)
  have hX (ω) : X ω=((missedBonds n R γ ω).card:ℝ) := by
    simpa only [X,f,S,missedBonds,Set.indicator_apply] using
      (Finset.sum_boole (R:=ℝ) (fun e : Fin (n+1) => ω∈failedStrips γ R e.val) Finset.univ)
  have hnn : 0 ≤ᵐ[μ] X := Filter.Eventually.of_forall fun ω => by
    change 0 ≤ X ω
    rw [hX]
    exact Nat.cast_nonneg _
  let N : ℝ := (n+1:ℕ)
  have hn : 0 < N := by dsimp only [N]; positivity
  have hav : ∫ ω, X ω ∂μ ≤ N*(η*β) := by
    dsimp only [X]
    rw [integral_finsetSum _ (fun e _ => hi e)]
    calc _ ≤ ∑ _e : Fin (n+1), η*β := Finset.sum_le_sum fun e _ => by
           rw [show (∫ ω, f e ω ∂μ)=μ.real (S e) from integral_indicator_one (hS e)]
           exact hb e
         _ = _ := by simp [N,nsmul_eq_mul]
  have hmark := (mul_meas_ge_le_integral_of_nonneg hnn (integrable_finsetSum _ (fun e _ => hi e))
    (η*N)).trans hav
  have hbound := (mul_le_mul_iff_right₀ (mul_pos hη hn)).mp (hmark.trans_eq
    (show N*(η*β)=(η*N)*β by ring))
  simpa only [hX,N] using hbound

/-- At an interior center the two successful infinite-path strips give
actual physical boundaries at distance at most R, with both edge norms
controlled by their Gaussian coordinates. -/
theorem brackets_of_not_missed {n R : ℕ} (ω : PathPauliDisorder) {e : Fin (n+1)} {γ : ℝ}
    (hl : R≤e.val) (hr : e.val+R≤n) (h : e∉missedBonds n R γ ω) :
    ∃ a b : Fin (n+1), a<e ∧ e<b ∧ e.val≤a.val+R ∧ b.val≤e.val+R ∧
      ‖edgePart (pathPauliDisorderShell ω n) a‖ ≤ 9*γ ∧
      ‖edgePart (pathPauliDisorderShell ω n) b‖ ≤ 9*γ := by
  classical
  have hh : ω∉failedStrips γ R e.val := fun he => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have h₁ : ¬∀ i : Fin R, ¬weakRow γ ω (e.val-R+i.val) := fun h => hh (Or.inl h)
  have h₂ : ¬∀ i : Fin R, ¬weakRow γ ω (e.val+1+i.val) := fun h => hh (Or.inr h)
  push Not at h₁ h₂
  obtain ⟨i,hi⟩ := h₁
  obtain ⟨j,hj⟩ := h₂
  let a : Fin (n+1) := ⟨e.val-R+i.val,by have := i.isLt; omega⟩
  let b : Fin (n+1) := ⟨e.val+1+j.val,by have := j.isLt; omega⟩
  have hiR := i.isLt
  have hjR := j.isLt
  refine ⟨a,b,?_,?_,?_,?_,edge_norm_of_weak ω a hi,edge_norm_of_weak ω b hj⟩
  · change e.val-R+i.val<e.val
    omega
  · change e.val<e.val+1+j.val
    omega
  · change e.val≤e.val-R+i.val+R
    omega
  · change e.val+1+j.val≤e.val+R
    omega

#print axioms gaussian_seam_density
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
