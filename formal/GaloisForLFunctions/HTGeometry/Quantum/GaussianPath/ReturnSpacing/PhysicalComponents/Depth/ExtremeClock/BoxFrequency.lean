import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.ExtremeClock.MaximumBox
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PairFrequency
import GaloisForLFunctions.HTGeometry.TorusHomBiLipschitz
import Mathlib.MeasureTheory.Group.AddCircle

/-! # Frequency of maximum-duration cells on the extreme-gap clock -/
open MeasureTheory Filter Real Set Metric
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem box_mass {I : Type*} [Fintype I] (d : I→ℝ) (hd : ∀ i, d i∈Icc (0:ℝ) (1/2)) :
    let C := Set.pi (univ : Set I) (fun i => closedBall (0:UnitAddCircle) (d i))
    MeasurableSet C ∧ volume (frontier C)=0 ∧ volume.real C=∏ i, (2*d i) := by
  intro C
  let O := Set.pi (univ : Set I) (fun i => ball (0:UnitAddCircle) (d i))
  have hC : IsClosed C := isClosed_set_pi (fun _ _ => isClosed_closedBall)
  have hO : IsOpen O := isOpen_set_pi finite_univ (fun _ _ => isOpen_ball)
  have hsub : O⊆C := Set.pi_mono fun _ _ => ball_subset_closedBall
  have he : C=ᵐ[volume] O := Measure.ae_eq_set_pi (fun _ _ => AddCircle.closedBall_ae_eq_ball)
  refine ⟨hC.measurableSet,measure_mono_null ?_ (ae_le_set.mp he.le),?_⟩
  · change closure C \ interior C ⊆ C \ O
    rw [hC.closure_eq]
    exact sdiff_subset_sdiff_right (hO.subset_interior_iff.mpr hsub)
  · rw [Measure.real,show volume C=∏ i, volume (closedBall (0:UnitAddCircle) (d i)) from Measure.pi_pi _ _,
      ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [AddCircle.volume_closedBall,min_eq_right (by linarith only [(hd i).2] : 2*d i≤1),
        ENNReal.toReal_ofReal (mul_nonneg two_pos.le (hd i).1)]

private theorem norm_residual (x : ℝ) : ‖(x:UnitAddCircle)‖=|residual x| := by
  let u := AddCircle.equivIco (1:ℝ) (-(1/2)) (x:UnitAddCircle)
  have hu : |(u:ℝ)|≤1/2 := abs_le.mpr ⟨u.property.1,by linarith only [u.property.2]⟩
  have he : ((u:ℝ):UnitAddCircle)=(x:UnitAddCircle) := AddCircle.coe_equivIco
  exact (congrArg norm he.symm).trans (norm_coe_eq_abs hu)

/-- The normalized-gap clock hits its full-duration box with probability
equal to the product of the individual spectator widths. The limit is over
actual consecutive integer ticks of the fixed physical spectrum. -/
theorem maximum_cell_frequency {I : Type*} [Fintype I] [DecidableEq I] (E : I→ℝ)
    (hE : MaximallyProjectiveEnergy E) (p q : I) (he : E q < E p)
    (hb : ∀ i, E q≤E i ∧ E i≤E p) (shift : ℕ) {r : ℝ} (hr : r∈Ioo (0:ℝ) (1/2)) :
    let θ := fun i => (E i-E q)/(E p-E q)
    let J := {i : I // i≠q}
    let b : J := ⟨p,fun h => he.ne (congrArg E h.symm)⟩
    let K := {j : J // j≠b}
    Tendsto (fun M : ℕ => (countTicks (fun k => offsets θ ((shift+k:ℕ):ℤ) r=Icc (-r) r) (M+1):ℝ)/(M+1))
      atTop (𝓝 (∏ i : K, 2*(r*min (θ i.val.val) (1-θ i.val.val)))) := by
  intro θ J b K
  let W := E p-E q
  let τ := 2*π/W
  let ω := projectiveFrequency E q
  let d (i : I) := r*min (θ i) (1-θ i)
  have hW : 0<W := sub_pos.mpr he
  have hp : θ p=1 := div_self hW.ne'
  have hq : θ q=0 := by simp only [θ,sub_self,zero_div]
  have ht (i) : θ i∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr (hb i).1) hW.le,(div_le_one hW).mpr (sub_le_sub_right (hb i).2 _)⟩
  have hd (i : I) : d i∈Icc (0:ℝ) (1/2) :=
    ⟨mul_nonneg hr.1.le (le_min (ht i).1 (sub_nonneg.mpr (ht i).2)),
      (mul_le_of_le_one_right hr.1.le ((min_le_left ..).trans (ht i).2)).trans hr.2.le⟩
  let C := Set.pi (univ : Set K) (fun i => closedBall (0:UnitAddCircle) (d i.val.val))
  obtain ⟨hm,hnull,hvol⟩ := box_mass (fun i : K => d i.val.val) (fun i => hd i.val.val)
  have hτ : 0<τ := div_pos (by positivity) hW
  have hpin : τ*ω b=(1:ℤ)*(2*π) := by
    change 2*π/W*W=_
    rw [div_mul_cancel₀ _ hW.ne']; norm_num
  have h := pinned_continuity_set_frequency ω (maximallyProjectiveEnergy_projectiveFrequency_independent E hE q)
    b hτ.ne' 1 hpin ((shift:ℝ)*τ) C hm hnull
  rw [hvol] at h
  have hdate (k : ℕ) (i : K) :
      finiteClockPhasePoint (fun j : K => ω j.val) ((shift:ℝ)*τ+k*τ) i=((((shift+k:ℕ):ℝ)*θ i.val.val:ℝ):UnitAddCircle) := by
    change ((((shift:ℝ)*τ+(k:ℝ)*τ)*(E i.val.val-E q)/(2*π):ℝ):UnitAddCircle)=_
    congr 1
    rw [Nat.cast_add]
    dsimp only [τ,θ]
    change ((shift:ℝ)*(2*π/W)+(k:ℝ)*(2*π/W))*(E i.val.val-E q)/(2*π)=
      ((shift:ℝ)+k)*((E i.val.val-E q)/W)
    field_simp [hW.ne',pi_ne_zero]
  have hiff (k : ℕ) : offsets θ ((shift+k:ℕ):ℤ) r=Icc (-r) r ↔
      finiteClockPhasePoint (fun j : K => ω j.val) ((shift:ℝ)*τ+k*τ)∈C := by
    rw [maximal_offsets_iff θ p q hp hq _ hr.1.le]
    constructor
    · intro hh i _
      rw [mem_closedBall,dist_zero_right,hdate,norm_residual]
      exact_mod_cast hh i.val.val
    · intro hh i
      by_cases hiq : i=q
      · subst i
        have hz := residual_int 0
        simp only [Int.cast_zero] at hz
        simp only [hq,mul_zero,hz,abs_zero,sub_zero,min_eq_left zero_le_one,le_refl]
      by_cases hip : i=p
      · subst i
        simp only [hp,mul_one,residual_int,abs_zero,sub_self,min_eq_right zero_le_one,mul_zero,le_refl]
      let j : K := ⟨⟨i,hiq⟩,fun h => hip (congrArg Subtype.val h)⟩
      have hj := hh j (mem_univ _)
      change _∈closedBall (0:UnitAddCircle) (d i) at hj
      rw [mem_closedBall,dist_zero_right,hdate,norm_residual] at hj
      exact_mod_cast hj
  simpa only [funext (fun k => propext (hiff k))] using h

#print axioms maximum_cell_frequency
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux.ExtremeClock
