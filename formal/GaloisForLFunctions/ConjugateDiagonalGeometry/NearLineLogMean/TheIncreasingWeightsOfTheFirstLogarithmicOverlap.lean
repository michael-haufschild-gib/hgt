import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.FourEnergyMeasurementsRecoverAdjacentCorrelations
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.IncreasingWindowMeasurementsControlTheCesaroMean

/-!
# The adjacent-pair weights increase across the first overlap band

The decrease in spacing between consecutive logarithms outweighs the
decay of the critical square-root amplitude. Each measurement is
therefore a positive, increasing row on the ordinary adjacent products.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology
noncomputable section

/-- The normalized coefficient on the raw product at sites n and n+1. -/
def adjacentWeight (d : ℝ) (n : ℕ) : ℝ :=
  max (d - adjacentLogGap n) 0 / d / (Real.sqrt n * Real.sqrt ((n:ℝ)+1))

/-- The difference of successive log gaps dominates the reciprocal square
of their shared endpoint. -/
theorem adjacent_log_gap_curvature {n : ℕ} (hn : 0 < n) :
    1 / ((n:ℝ)+1)^2 ≤ adjacentLogGap n - adjacentLogGap (n+1) := by
  let x : ℝ := n
  have hx : 0 < x := Nat.cast_pos.mpr hn
  have h₁ : 0 < x+1 := by positivity
  have h₂ : 0 < x+2 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos (sq_pos_of_pos h₁) (mul_pos hx h₂))
  have hid : 1 - ((x+1)^2 / (x*(x+2)))⁻¹ = 1/(x+1)^2 := by
    rw [inv_div]
    field_simp [h₁.ne']
    ring
  rw [hid, Real.log_div (pow_ne_zero _ h₁.ne') (mul_ne_zero hx.ne' h₂.ne'),
    Real.log_pow, Real.log_mul hx.ne' h₂.ne'] at h
  simp only [adjacentLogGap,Nat.cast_succ]
  change 1/(x+1)^2 ≤ (Real.log (x+1)-Real.log x)-(Real.log (x+1+1)-Real.log (x+1))
  rw [show x+1+1=x+2 by ring]
  linarith only [h]

private theorem raw_weight_step {n : ℕ} (hn : 0<n) {d : ℝ} (hd : d*((n:ℝ)+2) ≤ 2) :
    max (d-adjacentLogGap n) 0 / (n:ℝ) ≤
      max (d-adjacentLogGap (n+1)) 0 / ((n:ℝ)+1) := by
  have hx : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have h₁ : 0 < (n:ℝ)+1 := by positivity
  have h₂ : 0 < (n:ℝ)+2 := by positivity
  have hcurv := mul_le_mul_of_nonneg_left (adjacent_log_gap_curvature hn) hx.le
  have hrat : 2 / ((n:ℝ)+2) ≤ 1/((n:ℝ)+1)+(n:ℝ)*(1/((n:ℝ)+1)^2) := by
    field_simp [h₁,h₂]
    nlinarith only [hx]
  have hstep : (d-adjacentLogGap n)*((n:ℝ)+1) ≤ (d-adjacentLogGap (n+1))*(n:ℝ) := by
    nlinarith only [hcurv,(adjacent_log_gap_bounds hn).1,hrat,(le_div_iff₀ h₂).mpr hd]
  by_cases h : 0 ≤ d-adjacentLogGap n
  · rw [max_eq_left h,div_le_div_iff₀ hx h₁]
    exact hstep.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.le)
  · rw [max_eq_right (le_of_not_ge h),zero_div]
    exact div_nonneg (le_max_right _ _) h₁.le

private theorem adjacent_weight_factor {n : ℕ} (hn : 0 < n) (d : ℝ) :
    adjacentWeight d n =
      (max (d-adjacentLogGap n) 0/(n:ℝ)) * Real.sqrt ((n:ℝ)/((n:ℝ)+1)) / d := by
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hs := Real.mul_self_sqrt hn'.le
  rw [adjacentWeight,Real.sqrt_div hn'.le]
  by_cases hd : d=0
  · simp [hd]
  have ha := (Real.sqrt_pos.mpr hn').ne'
  have hb := (Real.sqrt_pos.mpr (show 0<(n:ℝ)+1 by positivity)).ne'
  field_simp [hn'.ne',ha,hb,hd]
  linear_combination (max (d-adjacentLogGap n) 0)*hs.symm

/-- The normalized raw-product coefficients increase up to the end of
every prefix at bandwidth at most twice the inverse length. -/
theorem adjacent_weight_step {n : ℕ} (hn : 0<n) {d : ℝ} (hd : 0≤d)
    (hscale : d*((n:ℝ)+2) ≤ 2) : adjacentWeight d n ≤ adjacentWeight d (n+1) := by
  have hw := raw_weight_step hn hscale
  rw [adjacent_weight_factor hn,adjacent_weight_factor (Nat.succ_pos n)]
  simp only [Nat.cast_succ]
  apply div_le_div_of_nonneg_right _ hd
  apply mul_le_mul hw _ (Real.sqrt_nonneg _) (div_nonneg (le_max_right _ _) (by positivity))
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [sq_nonneg (0:ℝ)]

private theorem adjacent_weight_nonneg {d : ℝ} (hd : 0 ≤ d) (n : ℕ) : 0 ≤ adjacentWeight d n :=
  div_nonneg (div_nonneg (le_max_right _ _) hd) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private theorem tail_weight_lower {n : ℕ} (hn : 0 < n) {d M c : ℝ}
    (hd : 0 < d) (hc : 0 ≤ c) (hend : (n:ℝ)+1 ≤ M)
    (hgap : 1 ≤ (1-c)*(d*(n:ℝ))) : c/M ≤ adjacentWeight d n := by
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hs : 0 < Real.sqrt n * Real.sqrt ((n:ℝ)+1) := by positivity
  have hu : Real.sqrt n * Real.sqrt ((n:ℝ)+1) ≤ M :=
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith : (n:ℝ) ≤ (n:ℝ)+1))
      (Real.sqrt_nonneg _)).trans ((Real.mul_self_sqrt (by positivity : 0 ≤ (n:ℝ)+1)).le.trans hend)
  have hrec : 1/(n:ℝ) ≤ (1-c)*d := (div_le_iff₀ hn').mpr (by linarith only [hgap])
  have ht : c ≤ max (d-adjacentLogGap n) 0/d := (le_div_iff₀ hd).mpr
    ((by linarith only [(adjacent_log_gap_bounds hn).2,hrec] : c*d ≤ d-adjacentLogGap n).trans (le_max_left _ _))
  exact (div_le_div_of_nonneg_left hc hs hu).trans (div_le_div_of_nonneg_right ht hs.le)

/-- Any moving bandwidth bounded away from the bottom of the band gives
a uniformly positive total weight. A fixed fraction of the last indices
already carries this mass. -/
theorem increasing_adjacent_rows_of_scale_margin (d : ℕ → ℝ) {η : ℝ} (hη : 0<η)
    (hband : ∀ᶠ N : ℕ in atTop, 1+η ≤ d N*((N:ℝ)+2) ∧ d N*((N:ℝ)+2) ≤ 2) :
    ∃ m : ℝ, 0 < m ∧ (∀ᶠ N : ℕ in atTop,
      increasingRowAt (fun N j => adjacentWeight (d N) (j+1)) N ∧
      m ≤ ∑ j ∈ range (N+1), adjacentWeight (d N) (j+1)) := by
  let t := η/(2*(1+η))
  let c := η/(2+η)
  have ht : 0<t := div_pos hη (by positivity)
  have hc : 0<c := div_pos hη (by positivity)
  have hhalf : t ≤ 1/2 := by
    dsimp only [t]
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hη])
  have htc : (1-c)*(1-t)*(1+η)=1 := by
    dsimp only [c,t]
    field_simp [show (1:ℝ)+η ≠ 0 by positivity,show (2:ℝ)+η ≠ 0 by positivity]
    ring
  have hc1 : 0 ≤ 1-c := sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by linarith only [hη]))
  refine ⟨c*t/2,by positivity,?_⟩
  filter_upwards [hband,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (2/t)] with N hb hN
  let M := (N:ℝ)+2
  let K := ⌊t*M⌋₊
  have hM : 0 < M := by dsimp only [M]; positivity
  have hd : 0 < d N := pos_of_mul_pos_left (lt_of_lt_of_le (by linarith only [hη] : 0<1+η) hb.1) hM.le
  have hbig : 2 ≤ t*M := by
    have h := (div_le_iff₀ ht).mp hN
    dsimp only [M]
    nlinarith only [h,ht]
  have hk : (K:ℝ) ≤ t*M := Nat.floor_le (mul_nonneg ht.le hM.le)
  have hk' : t*M < (K:ℝ)+1 := Nat.lt_floor_add_one _
  have hkhalf : (K:ℝ) ≤ M/2 :=
    hk.trans (by nlinarith only [mul_le_mul_of_nonneg_right hhalf hM.le])
  have hkN : K ≤ N+1 := by
    have h : (K:ℝ) ≤ (N:ℝ)+1 := by dsimp only [M] at hkhalf; linarith only [hkhalf,Nat.cast_nonneg (α:=ℝ) N]
    exact_mod_cast h
  have hkpos : 0 < K := Nat.cast_pos.mp (by linarith only [hk',hbig] : 0<(K:ℝ))
  have htail (j : ℕ) (hj : N+1-K ≤ j) (hend : j ≤ N) : c/M ≤ adjacentWeight (d N) (j+1) := by
    have hn : (N:ℝ)+1 ≤ (j:ℝ)+K := by exact_mod_cast (show N+1 ≤ j+K by omega)
    have hn' : (1-t)*M ≤ ((j+1:ℕ):ℝ) := by
      rw [Nat.cast_succ]
      dsimp only [M] at hn ⊢
      dsimp only [M] at hk
      nlinarith only [hn,hk]
    apply tail_weight_lower (Nat.succ_pos _) hd hc.le
    · dsimp only [M]
      simpa only [Nat.cast_succ] using (by exact_mod_cast (show j+1+1 ≤ N+2 by omega) :
        (j:ℝ)+1+1 ≤ (N:ℝ)+2)
    · have h₁ := mul_le_mul_of_nonneg_left hn' hd.le
      have h₂ := mul_le_mul_of_nonneg_left hb.1 (by linarith only [hhalf] : 0≤1-t)
      change 1 ≤ (1-c)*(d N*((j+1:ℕ):ℝ))
      calc
        1 = (1-c)*((1-t)*(1+η)) := by linarith only [htc]
        _ ≤ _ := mul_le_mul_of_nonneg_left (h₂.trans (by dsimp only [M] at h₁; linarith only [h₁])) hc1
  have hrow : increasingRowAt (fun N j => adjacentWeight (d N) (j+1)) N := by
    refine ⟨adjacent_weight_nonneg hd.le _, (div_pos hc hM).trans_le (htail N (by omega) le_rfl), ?_⟩
    intro j hj
    apply adjacent_weight_step (Nat.succ_pos _) hd.le
    have h : ((j+1:ℕ):ℝ)+2 ≤ (N:ℝ)+2 := by exact_mod_cast (show j+1+2 ≤ N+2 by omega)
    exact (mul_le_mul_of_nonneg_left h hd.le).trans hb.2
  refine ⟨hrow,?_⟩
  let I := Ico (N+1-K) (N+1)
  have hcard : I.card = K := by dsimp only [I]; rw [Nat.card_Ico]; omega
  have hsub : I ⊆ range (N+1) := fun j hj => mem_range.mpr (mem_Ico.mp hj).2
  calc
    c*t/2 ≤ (K:ℝ)*(c/M) := by
      rw [←mul_div_assoc (K:ℝ) c M,le_div_iff₀ hM]
      nlinarith only [mul_le_mul_of_nonneg_left
        (by linarith only [hk',hbig] : t*M/2 ≤ (K:ℝ)) hc.le]
    _ = ∑ _j ∈ I, c/M := by rw [sum_const,hcard,nsmul_eq_mul]
    _ ≤ ∑ j ∈ I, adjacentWeight (d N) (j+1) :=
      sum_le_sum fun j hj => htail j (mem_Ico.mp hj).1 (by have := (mem_Ico.mp hj).2; omega)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => adjacent_weight_nonneg hd.le _)

#print axioms increasing_adjacent_rows_of_scale_margin

#print axioms adjacent_log_gap_curvature
#print axioms adjacent_weight_step
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
