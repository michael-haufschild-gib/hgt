import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.PairFrequency

/-! # Counting pair contacts per unit of physical time -/
open Filter Topology Set
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section

/-- Indices of all nonnegative ticks a+kτ at or before T. -/
def tickIndices (a τ T : ℝ) : Finset ℕ :=
  if T<a then ∅ else Finset.range (⌊(T-a)/τ⌋₊+1)

theorem mem_tickIndices {a τ T : ℝ} (hτ : 0<τ) (k : ℕ) :
    k ∈ tickIndices a τ T ↔ a+(k:ℝ)*τ ≤ T := by
  by_cases h : T<a
  · rw [tickIndices,if_pos h]
    have hnon := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hτ.le
    simp only [Finset.notMem_empty,false_iff]
    linarith only [hnon,h]
  · rw [tickIndices,if_neg h,Finset.mem_range,Nat.lt_succ_iff,Nat.le_floor_iff
      (div_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hτ.le),le_div_iff₀ hτ]
    constructor <;> intro hk <;> linarith only [hk]

private theorem tick_rate (test : ℕ → Prop) (a τ p : ℝ) (hτ : 0<τ)
    (hf : Tendsto (fun N : ℕ => (countTicks test (N+1):ℝ)/(N+1)) atTop (𝓝 p)) :
    Tendsto (fun T : ℝ => (({k ∈ tickIndices a τ T | test k}.card:ℕ):ℝ)/T) atTop (𝓝 (p/τ)) := by
  classical
  let q (T : ℝ) := (T-a)/τ
  have hq : Tendsto q atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (a+b*τ)] with T hT
    exact (le_div_iff₀ hτ).mpr (by linarith only [hT])
  have hc := hf.comp (tendsto_nat_floor_atTop.comp hq)
  have hh : Tendsto (fun T : ℝ => ((⌊q T⌋₊:ℝ)+1)/q T) atTop (𝓝 1) := by
    have h := (tendsto_nat_floor_div_atTop.comp hq).add (hq.const_div_atTop 1)
    simpa only [add_zero,Function.comp_apply,←add_div] using h
  have hqT : Tendsto (fun T : ℝ => q T/T) atTop (𝓝 (1/τ)) := by
    have h := ((tendsto_id (x := (atTop : Filter ℝ))).const_div_atTop a).const_sub 1
    have h' := h.div_const τ
    rw [sub_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    dsimp only [q,id]
    field_simp
  have h := (hc.mul hh).mul hqT
  rw [mul_one,mul_one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop a] with T hT
  have hqt : 0 < q T := div_pos (sub_pos.mpr hT) hτ
  dsimp only [Function.comp_apply,Pi.mul_apply]
  rw [tickIndices,if_neg hT.not_gt]
  change (countTicks test (⌊q T⌋₊+1):ℝ)/(↑⌊q T⌋₊+1)*((↑⌊q T⌋₊+1)/q T)*(q T/T) =
    (countTicks test (⌊q T⌋₊+1):ℝ)/T
  field_simp

/-- Physical-time rate of ticks satisfying any test of known tick frequency. -/
alias filtered_tick_rate := tick_rate

/-- Distinct real dates at which this one ordered pair is marked in [0,T]. -/
def markedDates {I : Type*} (E : I → ℝ) (i j : I) (r : ℝ) (A : Set UnitAddCircle) (T : ℝ) : Finset ℝ := by
  classical
  let τ := 2*Real.pi/(E i-E j)
  let date := pairDate E i j r
  exact if E j < E i then
    ((tickIndices ((1-r)*τ) τ T).filter (fun k => pairFace A (fun z => E z/(2*Real.pi)) r (date k) i j)).image date
    else ∅

/-- Each descending energy pair contributes its frequency of complete
turns times the conditional probability of an enclosing pair contact. -/
theorem markedDates_rate {I : Type*} [Fintype I] [DecidableEq I] (E : I → ℝ)
    (hi : MaximallyProjectiveEnergy E) (i j : I) (r : Icc (0:ℝ) (1/2))
    (A : Set UnitAddCircle) (hA : A ∈ ({openArc r,forwardUnitArc r} : Set (Set UnitAddCircle))) :
    Tendsto (fun T : ℝ => ((markedDates E i j r A T).card:ℝ)/T) atTop
      (𝓝 ((r:ℝ)^(Fintype.card I-2)*(max 0 (E i-E j)/(2*Real.pi)))) := by
  classical
  by_cases he : E j < E i
  · let τ := 2*Real.pi/(E i-E j)
    have hg := sub_pos.mpr he
    have hp : 0<τ := by dsimp only [τ]; positivity
    have hinj : Function.Injective (pairDate E i j r) := by
      intro k l h
      change (1-(r:ℝ)+(k:ℝ))*τ=(1-(r:ℝ)+(l:ℝ))*τ at h
      exact_mod_cast (add_left_cancel (mul_right_cancel₀ hp.ne' h) : (k:ℝ)=(l:ℝ))
    have h := tick_rate _ ((1-(r:ℝ))*τ) τ _ hp (pair_contact_frequency E hi i j he r A hA)
    rw [max_eq_right hg.le,show (r:ℝ)^(Fintype.card I-2)*((E i-E j)/(2*Real.pi)) =
      (r:ℝ)^(Fintype.card I-2)/τ by dsimp only [τ]; field_simp]
    simpa only [markedDates,if_pos he,Finset.card_image_of_injective _ hinj] using h
  · simp only [markedDates,if_neg he,Finset.card_empty,Nat.cast_zero,zero_div,
      max_eq_left (sub_nonpos.mpr (le_of_not_gt he)),mul_zero,tendsto_const_nhds]

#print axioms markedDates_rate
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
