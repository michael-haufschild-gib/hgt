import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.IncreasingWindowMeasurementsControlTheCesaroMean

/-!
# The exact Cesàro norm of an increasing window

Abel summation expresses an increasing row as one positive endpoint
coefficient and negative coefficients on all earlier means. Their
total variation is twice the scaled endpoint minus the row mass.
A sequence with all previous means equal to −1 and final mean equal
to 1 attains this value.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology _root_.RHTower
noncomputable section

/-- Total variation of a row expressed in ordinary Cesàro means. -/
def cesaroRowNorm (w : ℕ → ℕ → ℝ) (N : ℕ) :=
  2*((N:ℝ)+1)*w N N - ∑ j ∈ range (N+1), w N j

private def increment (w : ℕ → ℕ → ℝ) (N j : ℕ) := w N (j+1)-w N j

private theorem observation_by_parts (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (N : ℕ) :
    weightedPrefix x w N = deningerPartialSum x N*w N N -
      ∑ j ∈ range N, deningerPartialSum x j*increment w N j := by
  have hflip : (∑ j ∈ range N, deningerPartialSum x j*(w N j-w N (j+1))) =
      -(∑ j ∈ range N, deningerPartialSum x j*increment w N j) := by
    rw [←sum_neg_distrib]
    exact sum_congr rfl fun j _ => by dsimp only [increment]; ring
  rw [weightedPrefix,deningerAbelSummation x (w N) N,hflip,sub_eq_add_neg]

private theorem increment_mass (w : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range N, ((j:ℝ)+1)*increment w N j =
      ((N:ℝ)+1)*w N N - ∑ j ∈ range (N+1), w N j := by
  have h := observation_by_parts (fun _ => 1) w N
  simp only [weightedPrefix,one_mul,deningerPartialSum,sum_const,card_range,nsmul_eq_mul,
    mul_one,Nat.cast_succ] at h
  linarith only [h]

/-- A uniform error C on the prefixes costs at most twice the endpoint
weight times C. The coefficient of the linear prefix error is sharp. -/
theorem observation_le_cesaro_row_norm (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (N : ℕ)
    (hfirst : 0 ≤ w N 0) (hend : 0 ≤ w N N) (hstep : ∀ j<N, w N j ≤ w N (j+1))
    {C b : ℝ} (hC : 0 ≤ C)
    (hp : ∀ j≤N, |deningerPartialSum x j| ≤ C+b*((j:ℝ)+1)) :
    |weightedPrefix x w N| ≤ 2*C*w N N + b*cesaroRowNorm w N := by
  have hΔ (j : ℕ) (hj : j∈range N) : 0 ≤ increment w N j := sub_nonneg.mpr (hstep _ (mem_range.mp hj))
  have htail : (∑ j ∈ range N, |deningerPartialSum x j*increment w N j|) ≤
      ∑ j ∈ range N, (C+b*((j:ℝ)+1))*increment w N j := by
    apply sum_le_sum
    intro j hj
    rw [abs_mul,abs_of_nonneg (hΔ j hj)]
    exact mul_le_mul_of_nonneg_right (hp j (mem_range.mp hj).le) (hΔ j hj)
  have htel : ∑ j ∈ range N, increment w N j = w N N-w N 0 := sum_range_sub _ _
  have he : (∑ j ∈ range N, (C+b*((j:ℝ)+1))*increment w N j) =
      C*(w N N-w N 0)+b*(((N:ℝ)+1)*w N N-∑ j ∈ range (N+1), w N j) := by
    have expand (j : ℕ) : (C+b*((j:ℝ)+1))*increment w N j =
        C*increment w N j+b*(((j:ℝ)+1)*increment w N j) := by ring
    simp_rw [expand]
    rw [sum_add_distrib,←mul_sum,←mul_sum,htel,increment_mass]
  rw [observation_by_parts]
  refine (abs_sub _ _).trans ((add_le_add (le_refl _) ((abs_sum_le_sum_abs _ _).trans htail)).trans ?_)
  rw [abs_mul,abs_of_nonneg hend,he,cesaroRowNorm]
  nlinarith only [mul_le_mul_of_nonneg_right (hp N le_rfl) hend,mul_nonneg hC hfirst]

private def extremizer (N j : ℕ) : ℝ := if j = N then 2*(N:ℝ)+1 else -1

private theorem extremal_prefix {j N : ℕ} (hj : j<N) :
    deningerPartialSum (extremizer N) j = -((j:ℝ)+1) := by
  unfold deningerPartialSum
  have h : ∀ i ∈ range (j+1), extremizer N i = -1 := fun i hi =>
    if_neg (by have := mem_range.mp hi; omega)
  rw [sum_congr rfl h,sum_const,card_range,nsmul_eq_mul,Nat.cast_succ]
  ring

/-- The norm is attained, for every row and cutoff, among inputs whose
ordinary means have absolute value at most one at every preceding cutoff. -/
theorem cesaro_row_norm_attained (w : ℕ → ℕ → ℝ) (N : ℕ) :
    ∃ x : ℕ → ℝ, (∀ j ≤ N, |deningerPartialSum x j| ≤ (j:ℝ)+1) ∧
      weightedPrefix x w N = cesaroRowNorm w N := by
  have hbefore : ∑ j ∈ range N, extremizer N j = -(N:ℝ) := by
    calc
      _ = ∑ _j ∈ range N, (-1:ℝ) := sum_congr rfl fun j hj => if_neg (mem_range.mp hj).ne
      _ = _ := by simp
  have hlast : deningerPartialSum (extremizer N) N = (N:ℝ)+1 := by
    rw [deningerPartialSum,sum_range_succ,hbefore,extremizer,if_pos rfl]
    ring
  refine ⟨extremizer N,fun j hj => ?_,?_⟩
  · rcases hj.lt_or_eq with h|rfl
    · rw [extremal_prefix h,abs_neg,abs_of_nonneg (by positivity)]
    · rw [hlast,abs_of_nonneg (by positivity)]
  · rw [observation_by_parts,hlast]
    have hsum : (∑ j ∈ range N, deningerPartialSum (extremizer N) j*increment w N j) =
        -(∑ j ∈ range N, ((j:ℝ)+1)*increment w N j) := by
      rw [←sum_neg_distrib]
      exact sum_congr rfl fun j hj => by rw [extremal_prefix (mem_range.mp hj),neg_mul]
    rw [hsum,increment_mass,cesaroRowNorm]
    ring

private theorem prefix_bound_of_cesaro_zero (x : ℕ → ℝ)
    (hx : Tendsto (fun N : ℕ => deningerPartialSum x N/((N:ℝ)+1)) atTop (𝓝 0))
    {b : ℝ} (hb : 0 < b) : ∃ C : ℝ, 0≤C ∧ ∀ j, |deningerPartialSum x j| ≤ C+b*((j:ℝ)+1) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hx b hb)
  let C := ∑ j ∈ range K, |x j|
  have hC : 0≤C := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C,hC,fun j => ?_⟩
  by_cases hj : K ≤ j
  · have h := hK j hj
    change dist (deningerPartialSum x j/((j:ℝ)+1)) 0 < b at h
    have hjp : 0 < (j:ℝ)+1 := by positivity
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hjp,div_lt_iff₀ hjp] at h
    linarith only [h,hC]
  · refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum_of_subset_of_nonneg
      (range_mono (by omega : j+1 ≤ K)) (fun i _ _ => abs_nonneg (x i))).trans ?_)
    exact le_add_of_nonneg_right (by positivity)

/-- Bounded scaled endpoint weights suffice for ordinary cancellation
to give convergence of the possibly changing observations. -/
theorem increasing_window_readings_of_cesaro_zero (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) {H : ℝ}
    (hH : 0<H) (hrow : ∀ᶠ N : ℕ in atTop, increasingRowAt w N ∧ ((N:ℝ)+1)*w N N ≤ H)
    (hx : Tendsto (fun N : ℕ => deningerPartialSum x N/((N:ℝ)+1)) atTop (𝓝 0)) :
    Tendsto (weightedPrefix x w) atTop (𝓝 0) := by
  have hden : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop b).mono fun _ h =>
      h.trans (le_add_of_nonneg_right zero_le_one)
  have he : Tendsto (fun N => w N N) atTop (𝓝 0) := by
    apply squeeze_zero' (hrow.mono fun _ h => h.1.2.1.le) ?_
      (Tendsto.div_atTop (tendsto_const_nhds (x:=H)) hden)
    filter_upwards [hrow] with N hr
    exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hr.2])
  rw [Metric.tendsto_nhds]
  intro ε hε
  let b := ε/(4*H)
  have hb : 0<b := div_pos hε (by positivity)
  obtain ⟨C,hC,hp⟩ := prefix_bound_of_cesaro_zero x hx hb
  have hterm := he.const_mul (2*C)
  rw [mul_zero] at hterm
  filter_upwards [hrow,hterm.eventually_lt_const (half_pos hε)] with N hr ht
  rw [Real.dist_eq,sub_zero]
  have hh := observation_le_cesaro_row_norm x w N hr.1.1 hr.1.2.1.le hr.1.2.2 hC (fun j _ => hp j)
  have hmass : 0 ≤ ∑ j ∈ range (N+1), w N j := by
    apply sum_nonneg
    intro j hj
    have hmono (j : ℕ) (hj : j≤N) : 0 ≤ w N j := by
      induction j with
      | zero => exact hr.1.1
      | succ j ih => exact (ih (by omega)).trans (hr.1.2.2 j (by omega))
    exact hmono j (Nat.lt_succ_iff.mp (mem_range.mp hj))
  have hnorm : cesaroRowNorm w N ≤ 2*H := by unfold cesaroRowNorm; linarith only [hmass,hr.2]
  have hpaid : b*(2*H)=ε/2 := by dsimp only [b]; field_simp [hH.ne']; ring
  have hsmall := mul_le_mul_of_nonneg_left hnorm hb.le
  change 2*C*w N N < ε/2 at ht
  linarith only [hh,ht,hsmall,hpaid]

/-- If the row masses tend to P and stay positive, every ordinary limit
is measured with exactly the same factor P. The converse holds for
arbitrary real sequences, including unbounded inputs. -/
theorem increasing_observation_iff_cesaro_limit (x : ℕ → ℝ) (w : ℕ → ℕ → ℝ) (a : ℝ)
    {m H P : ℝ} (hm : 0 < m) (hH : 0 < H)
    (hr : ∀ᶠ N : ℕ in atTop, increasingRowAt w N ∧ m ≤ ∑ j ∈ range (N+1), w N j)
    (hend : ∀ᶠ N : ℕ in atTop, ((N:ℝ)+1)*w N N ≤ H)
    (hP : Tendsto (fun N => ∑ j ∈ range (N+1), w N j) atTop (𝓝 P)) :
    Tendsto (fun N : ℕ => deningerPartialSum x N/((N:ℝ)+1)) atTop (𝓝 a) ↔
      Tendsto (weightedPrefix x w) atTop (𝓝 (a*P)) := by
  let y (j : ℕ) := x j-a
  have hprev (N : ℕ) : deningerPartialSum y N/((N:ℝ)+1) =
      deningerPartialSum x N/((N:ℝ)+1)-a := by
    simp only [y,deningerPartialSum,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,Nat.cast_succ]
    field_simp [show (N:ℝ)+1≠0 by positivity]
  have hobs (N : ℕ) : weightedPrefix y w N = weightedPrefix x w N-a*∑ j ∈ range (N+1), w N j := by
    simp only [weightedPrefix,y,sub_mul,sum_sub_distrib,mul_sum]
  have hma := hP.const_mul a
  constructor
  · intro hx
    have hy : Tendsto (fun N : ℕ => deningerPartialSum y N/((N:ℝ)+1)) atTop (𝓝 0) := by
      simp_rw [hprev]
      simpa only [sub_self] using hx.sub_const a
    have hw := increasing_window_readings_of_cesaro_zero y w hH
      ((hr.mono fun _ h => h.1).and hend) hy
    have h := hw.add hma
    rw [zero_add] at h
    exact h.congr fun N => by rw [hobs,sub_add_cancel]
  · intro hw
    have hy : Tendsto (weightedPrefix y w) atTop (𝓝 0) := by
      have h := hw.sub hma
      rw [sub_self] at h
      exact h.congr fun N => (hobs N).symm
    have hc := cesaro_zero_of_increasing_window_readings y w hm hr hy
    have h := hc.add_const a
    rw [zero_add] at h
    exact h.congr fun N => by rw [hprev,sub_add_cancel]

#print axioms increasing_observation_iff_cesaro_limit

#print axioms observation_le_cesaro_row_norm
#print axioms cesaro_row_norm_attained
#print axioms increasing_window_readings_of_cesaro_zero
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
