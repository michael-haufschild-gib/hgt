import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheHalfIntegerLimitsOfTheFirstSquarefreeBandwidth
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ACubeRootGapForConsecutiveSquarefreePairs

/-!
# The age expansion of the first squarefree bandwidth

Subtracting successive Taylor terms changes the derivative of the
logarithm by an exact geometric factor. The mean value theorem on the
last adjacent integer interval keeps the same intermediate point for
the difference of its endpoint values.
-/
noncomputable section
open Filter Finset
open scoped Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

/-- Integral of the monomial of degree j over the last unit age interval. -/
def ageMoment (j : ℕ) (s : ℝ) := (s^(j+1)-(s-1)^(j+1))/((j:ℝ)+1)

private def primitive (N : ℝ) (m : ℕ) (x : ℝ) :=
  Real.log x + ∑ j∈range m,((N-x)/N)^(j+1)/((j:ℝ)+1)

private theorem primitive_deriv {N x : ℝ} (hN : 0 < N) (hx : 0 < x) (m : ℕ) :
    HasDerivAt (primitive N m) (((N-x)/N)^m/x) x := by
  induction m with
  | zero => simpa [primitive,one_div] using Real.hasDerivAt_log hx.ne'
  | succ m ih =>
    have hbase : HasDerivAt (fun t : ℝ => (N-t)/N) (-1/N) x := by
      simpa only [zero_sub] using ((hasDerivAt_const x N).sub (hasDerivAt_id x)).div_const N
    have hp := ((hbase.pow (m+1)).div_const ((m:ℝ)+1))
    have sum := ih.add hp
    have hf : primitive N (m+1) = fun t => primitive N m t+
        ((N-t)/N)^(m+1)/((m:ℝ)+1) := by ext t;simp only [primitive,sum_range_succ,add_assoc]
    rw [hf]
    convert sum using 1
    simp only [Nat.cast_succ,Nat.add_sub_cancel]
    rw [pow_succ]
    field_simp [hN.ne',hx.ne',show (m:ℝ)+1≠0 by positivity]
    <;> ring

/-- Exact positive remainder after m age moments. A single point ξ of
the last occupied interval represents the entire difference. -/
theorem squarefree_bandwidth_mean_value_remainder {N : ℕ} (hN : 2 ≤ N) (m : ℕ) :
    let k := (lastSquarefreeNeighbor N:ℝ)
    let s := (squarefreePairAge N:ℝ)
    ∃ ξ : ℝ, k < ξ ∧ ξ < k+1 ∧
      (N:ℝ)^m*(firstSquarefreeBandwidth N-
        ∑ j∈range m, ageMoment j s/(N:ℝ)^(j+1))=((N:ℝ)-ξ)^m/ξ := by
  let k := (lastSquarefreeNeighbor N:ℝ)
  let s := (squarefreePairAge N:ℝ)
  obtain ⟨hk,hkN,_⟩ := last_squarefree_neighbor_spec hN
  have kp : 0 < k := Nat.cast_pos.mpr hk
  have xn : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have age : s=(N:ℝ)-k := Nat.cast_sub hkN.le
  obtain ⟨ξ,hξ,he⟩ := exists_hasDerivAt_eq_slope (primitive (N:ℝ) m)
    (fun x => (((N:ℝ)-x)/N)^m/x) (show k < k+1 by linarith)
    (fun t ht => (primitive_deriv xn (kp.trans_le ht.1) m).continuousAt.continuousWithinAt)
    (fun t ht => primitive_deriv xn (kp.trans ht.1) m)
  refine ⟨ξ,hξ.1,hξ.2,?_⟩
  have hterm (j : ℕ) :
      (((N:ℝ)-(k+1))/N)^(j+1)/((j:ℝ)+1)-(((N:ℝ)-k)/N)^(j+1)/((j:ℝ)+1)=
        -ageMoment j s/(N:ℝ)^(j+1) := by
    rw [age,ageMoment,show (N:ℝ)-(k+1)=((N:ℝ)-k)-1 by ring,div_pow,div_pow]
    ring
  have hg : firstSquarefreeBandwidth N=Real.log (k+1)-Real.log k := by
    simp only [firstSquarefreeBandwidth,adjacentLogGap,Nat.cast_add,Nat.cast_one,k]
  have hdiff : primitive (N:ℝ) m (k+1)-primitive (N:ℝ) m k=
      firstSquarefreeBandwidth N-∑ j∈range m,ageMoment j s/(N:ℝ)^(j+1) := by
    rw [hg,primitive,primitive,add_sub_add_comm,←sum_sub_distrib]
    simp_rw [hterm,neg_div]
    rw [sum_neg_distrib,sub_eq_add_neg]
  rw [hdiff,show k+1-k=1 by ring,div_one] at he
  change (N:ℝ)^m*(firstSquarefreeBandwidth N-
      ∑ j∈range m,ageMoment j s/(N:ℝ)^(j+1))=_
  rw [←he,div_pow]
  field_simp [xn.ne',(kp.trans hξ.1).ne']

/-- The complete remainder lies between explicit endpoint prices. -/
theorem squarefree_bandwidth_remainder_interval {N : ℕ} (hN : 2 ≤ N) (m : ℕ) :
    let k := (lastSquarefreeNeighbor N:ℝ)
    let s := (squarefreePairAge N:ℝ)
    let r := (N:ℝ)^m*(firstSquarefreeBandwidth N-
      ∑ j∈range m,ageMoment j s/(N:ℝ)^(j+1))
    (s-1)^m/(k+1) ≤ r ∧ r ≤ s^m/k := by
  let k := (lastSquarefreeNeighbor N:ℝ)
  let s := (squarefreePairAge N:ℝ)
  obtain ⟨hk,hkN,_⟩ := last_squarefree_neighbor_spec hN
  have kp : 0 < k := Nat.cast_pos.mpr hk
  have step : k+1 ≤ N := by exact_mod_cast hkN
  have hs : s=(N:ℝ)-k := Nat.cast_sub hkN.le
  obtain ⟨ξ,hlo,hhi,he⟩ := squarefree_bandwidth_mean_value_remainder hN m
  have hξ := kp.trans hlo
  have hpos : 0 ≤ s-1 := by linarith only [hs,step]
  have hsmall : s-1 ≤ (N:ℝ)-ξ := by linarith only [hs,hhi]
  have hlarge : (N:ℝ)-ξ ≤ s := by linarith only [hs,hlo]
  change (s-1)^m/(k+1) ≤ _ ∧ _ ≤ s^m/k
  rw [he]
  constructor
  · exact div_le_div₀ (pow_nonneg hpos _) (pow_le_pow_left₀ hpos hsmall m) hξ hhi.le
  · exact div_le_div₀ (pow_nonneg (hpos.trans hsmall) _) (pow_le_pow_left₀ (hpos.trans hsmall) hlarge m) kp hlo.le

private theorem cubic_age_price :
    Tendsto (fun N : ℕ => (squarefreePairAge N:ℝ)^3/(lastSquarefreeNeighbor N:ℝ)) atTop (𝓝 0) := by
  have hcube := last_squarefree_pair_cube_root_saving.pow 3
  have ratio := last_squarefree_neighbor_ratio.inv₀ one_ne_zero
  have h := hcube.mul ratio
  simp only [zero_pow (by decide : 3≠0),zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hn
  have hk := (last_squarefree_neighbor_spec hn).1
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hc : ((N:ℝ)^(1/3:ℝ))^3=N := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le];norm_num
  change (((squarefreePairAge N:ℝ)/(N:ℝ)^(1/3:ℝ))^3)*
    (((lastSquarefreeNeighbor N:ℝ)/(N:ℝ))⁻¹)=_
  rw [div_pow,hc,inv_div]
  field_simp [hp.ne',(Nat.cast_pos.mpr hk : 0 < (lastSquarefreeNeighbor N:ℝ)).ne']

/-- The first three remainder estimates tend to zero on the full sequence,
uniformly through the unbounded ages forced by the Chinese remainder theorem. -/
theorem squarefree_bandwidth_uniform_remainder {m : ℕ} (hm : m ≤ 3) :
    Tendsto (fun N : ℕ => (N:ℝ)^m*(firstSquarefreeBandwidth N-
      ∑ j∈range m,ageMoment j (squarefreePairAge N:ℝ)/(N:ℝ)^(j+1))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ cubic_age_price
  · filter_upwards [eventually_ge_atTop 2] with N hn
    obtain ⟨hk,hkn,_⟩ := last_squarefree_neighbor_spec hn
    have hs : (1:ℝ) ≤ (squarefreePairAge N:ℝ) := by
      exact_mod_cast (show 1 ≤ squarefreePairAge N from Nat.sub_pos_of_lt hkn)
    exact (div_nonneg (pow_nonneg (sub_nonneg.mpr hs) m) (by positivity)).trans
      (squarefree_bandwidth_remainder_interval hn m).1
  · filter_upwards [eventually_ge_atTop 2] with N hn
    have hs : (1:ℝ) ≤ (squarefreePairAge N:ℝ) := by
      exact_mod_cast (show 1 ≤ squarefreePairAge N from Nat.sub_pos_of_lt (last_squarefree_neighbor_spec hn).2.1)
    exact (squarefree_bandwidth_remainder_interval hn m).2.trans
      (div_le_div_of_nonneg_right (pow_le_pow_right₀ hs hm) (Nat.cast_nonneg _))

/-- Subtracting the age from the quadratic bandwidth correction leaves
the same half-unit offset at every large cutoff. -/
theorem squarefree_bandwidth_uniform_half_unit :
    Tendsto (fun N : ℕ => squarefreeBandwidthCorrection N-(squarefreePairAge N:ℝ)) atTop (𝓝 (-(1/2:ℝ))) := by
  have h := (squarefree_bandwidth_uniform_remainder (by decide : 2 ≤ 3)).sub_const (1/2:ℝ)
  rw [zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  have hn' : (N:ℝ)≠0 := (Nat.cast_pos.mpr hn : 0 < (N:ℝ)).ne'
  simp only [squarefreeBandwidthCorrection,sum_range_succ,sum_range_zero,zero_add,ageMoment,
    Nat.cast_zero,Nat.cast_one,pow_one,div_one,sub_sub_cancel]
  field_simp [hn']
  <;> ring

/-- Third-order correction after removing the measured age. The residual
offset is one third even along sequences of diverging ages. -/
theorem squarefree_bandwidth_uniform_third_unit :
    Tendsto (fun N : ℕ => (N:ℝ)^3*(firstSquarefreeBandwidth N-1/(N:ℝ)-
        ((squarefreePairAge N:ℝ)-1/2)/(N:ℝ)^2)-
      (squarefreePairAge N:ℝ)*((squarefreePairAge N:ℝ)-1)) atTop (𝓝 (1/3:ℝ)) := by
  have h := (squarefree_bandwidth_uniform_remainder (by decide : 3 ≤ 3)).add_const (1/3:ℝ)
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  have hn' : (N:ℝ)≠0 := (Nat.cast_pos.mpr hn : 0 < (N:ℝ)).ne'
  simp only [sum_range_succ,sum_range_zero,zero_add,ageMoment,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
    pow_one,div_one,sub_sub_cancel]
  field_simp [hn']
  <;> ring

/-- The nearest half-integer is selected by the age on the entire tail. -/
theorem exact_age_from_the_bandwidth_correction :
    ∀ᶠ N : ℕ in atTop, ⌈squarefreeBandwidthCorrection N⌉₊=squarefreePairAge N := by
  filter_upwards [eventually_ge_atTop 2,
    squarefree_bandwidth_uniform_half_unit.eventually_const_lt (by norm_num : (-1:ℝ) < -(1/2:ℝ)),
    squarefree_bandwidth_uniform_half_unit.eventually_lt_const (by norm_num : -(1/2:ℝ) < 0)]
    with N hn hl hu
  apply le_antisymm (Nat.ceil_le.mpr (by linarith only [hu])) 
  by_contra! hsmall
  have hc : (⌈squarefreeBandwidthCorrection N⌉₊:ℝ)+1 ≤ (squarefreePairAge N:ℝ) := by exact_mod_cast hsmall
  have := Nat.le_ceil (squarefreeBandwidthCorrection N)
  linarith only [hl,hc,this]

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
