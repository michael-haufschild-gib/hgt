import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSharpCesaroNormOfAnIncreasingWindow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheMassProfileOfTheFirstLogarithmicOverlap

/-!
# The best-conditioned bandwidth for adjacent correlations

Normalize an overlap row by its mass so that it returns the value
of every constant input. In ordinary prefix-mean coordinates its
norm tends to 2(1−1/λ)/(log λ−1+1/λ)−1. This decreases strictly
through the first band. Its blowup at the threshold is 4/(λ−1).
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology Set
noncomputable section

private def endpointShare (x : ℝ) := 1-x⁻¹

/-- Limiting operator norm of a mass-normalized row in prefix-mean coordinates. -/
def calibratedAdjacentNorm (x : ℝ) := 2*endpointShare x/adjacentMassProfile x-1

private theorem scaled_endpoint {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 1≤x) :
    endpointShare x-1/((n:ℝ)+1) ≤ (n:ℝ)*adjacentWeight (x/((n:ℝ)+1)) n ∧
    (n:ℝ)*adjacentWeight (x/((n:ℝ)+1)) n ≤ endpointShare x := by
  let M := (n:ℝ)+1
  let d := x/M
  let s := Real.sqrt n*Real.sqrt M
  let q := max (d-adjacentLogGap n) 0 / d
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hM : 0<M := by dsimp only [M]; positivity
  have hx' := zero_lt_one.trans_le hx
  have hd : 0<d := div_pos hx' hM
  have hs : 0<s := mul_pos (Real.sqrt_pos.mpr hn') (Real.sqrt_pos.mpr hM)
  have hmono := Real.sqrt_le_sqrt (show (n:ℝ) ≤ M by dsimp only [M]; linarith)
  have hlo := mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg (n:ℝ))
  have hhi := mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg M)
  rw [Real.mul_self_sqrt hn'.le] at hlo
  rw [Real.mul_self_sqrt hM.le] at hhi
  have hq : 0≤q := div_nonneg (le_max_right _ _) hd.le
  have hqeq : q = max (1-adjacentLogGap n/d) 0 := by
    rw [show q=max (d-adjacentLogGap n) 0/d from rfl,←max_div_div_right hd.le,sub_div,div_self hd.ne',zero_div]
  have hg := adjacent_log_gap_bounds hn
  have hgl : 1/x ≤ adjacentLogGap n/d := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hg.1 hd.le)
    change 1/x=(1/M)/(x/M)
    field_simp [hM.ne',hx'.ne']
  have hgu : adjacentLogGap n/d ≤ M/((n:ℝ)*x) := by
    refine (div_le_div_of_nonneg_right hg.2 hd.le).trans_eq ?_
    dsimp only [d]
    field_simp [hM.ne',hx'.ne',hn'.ne']
    <;> ring
  have hql : 1-M/((n:ℝ)*x) ≤ q := by rw [hqeq]; exact (sub_le_sub_left hgu 1).trans (le_max_left _ _)
  have hqu : q ≤ endpointShare x := by
    rw [hqeq,endpointShare]
    exact max_le (by simpa only [one_div] using sub_le_sub_left hgl 1)
      (sub_nonneg.mpr (inv_le_one_of_one_le₀ hx))
  have he : (n:ℝ)*adjacentWeight (x/((n:ℝ)+1)) n = ((n:ℝ)/s)*q := by
    change (n:ℝ)*(q/s)=_
    ring
  rw [he]
  constructor
  · calc
      _ = ((n:ℝ)/M)*(1-M/((n:ℝ)*x)) := by
        dsimp only [endpointShare,M]
        field_simp [hn'.ne',hx'.ne',show (n:ℝ)+1≠0 by positivity]
        <;> ring
      _ ≤ ((n:ℝ)/M)*q := mul_le_mul_of_nonneg_left hql (div_nonneg hn'.le hM.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hn'.le hs hhi) hq
  · exact (mul_le_mul ((div_le_one hs).mpr hlo) hqu hq zero_le_one).trans_eq (one_mul _)

/-- Both the norm and the calibration are measured at the same cutoff. -/
theorem calibrated_adjacent_norm_limit {x : ℝ} (hx : 1 < x) :
    let d (N : ℕ) := x/((N:ℝ)+2)
    let w (N j : ℕ) := adjacentWeight (d N) (j+1)
    Tendsto (fun N : ℕ => cesaroRowNorm w N / adjacentMass (N+2) (d N))
      atTop (𝓝 (calibratedAdjacentNorm x)) := by
  let d (N : ℕ) := x/((N:ℝ)+2)
  let w (N j : ℕ) := adjacentWeight (d N) (j+1)
  have hN : Tendsto (fun N : ℕ => (N:ℝ)+2) atTop atTop := by
    exact tendsto_atTop.mpr fun b => ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop b).mono
      fun _ h => h.trans (le_add_of_nonneg_right (by norm_num))
  have hi : Tendsto (fun N : ℕ => 1/((N:ℝ)+2)) atTop (𝓝 0) := Tendsto.div_atTop tendsto_const_nhds hN
  have hlow := (tendsto_const_nhds (x:=endpointShare x)).sub hi
  rw [sub_zero] at hlow
  have he : Tendsto (fun N : ℕ => ((N:ℝ)+1)*w N N) atTop (𝓝 (endpointShare x)) := by
    have hh (N : ℕ) := scaled_endpoint (Nat.succ_pos N) hx.le
    simp only [Nat.cast_succ,add_assoc,one_add_one_eq_two] at hh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
      (.of_forall fun N => (hh N).1) (.of_forall fun N => (hh N).2)
  have hm : Tendsto (fun N : ℕ => adjacentMass (N+2) (d N)) atTop (𝓝 (adjacentMassProfile x)) := by
    have h := (adjacent_mass_at_scaled_bandwidth hx.le).comp (tendsto_add_atTop_nat 2)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,d] using h
  have hmass (N : ℕ) : (∑ j ∈ range (N+1), w N j) = adjacentMass (N+2) (d N) := by
    rw [adjacentMass,sum_Ico_eq_sum_range,show N+2-1=N+1 by omega]
    exact sum_congr rfl fun j _ => by simp only [w,add_comm 1 j]
  have h := (((he.const_mul 2).sub hm).div hm (adjacent_mass_profile_pos hx).ne')
  rw [sub_div,div_self (adjacent_mass_profile_pos hx).ne'] at h
  apply h.congr
  intro N
  change (2*(((N:ℝ)+1)*w N N)-adjacentMass (N+2) (d N))/adjacentMass (N+2) (d N) = _
  rw [cesaroRowNorm,hmass]
  ring

private theorem hasDerivAt_share {x : ℝ} (hx : x≠0) : HasDerivAt endpointShare (1/x^2) x := by
  unfold endpointShare
  simpa only [zero_sub,neg_neg,one_div] using!
    (hasDerivAt_const (x:=x) (c:=(1:ℝ))).sub (hasDerivAt_inv hx)

private theorem hasDerivAt_profile {x : ℝ} (hx : x≠0) :
    HasDerivAt adjacentMassProfile ((x-1)/x^2) x := by
  have h := ((Real.hasDerivAt_log hx).sub_const 1).add (hasDerivAt_inv hx)
  convert h using 1
  <;> first | rfl | (field_simp [hx]; ring)

/-- Larger scaled bandwidth strictly reduces the calibrated Cesàro norm. -/
theorem calibrated_adjacent_norm_strictAntiOn : StrictAntiOn calibratedAdjacentNorm (Ioi 1) := by
  have hder (x : ℝ) (hx : 1<x) : HasDerivAt calibratedAdjacentNorm
      (2*(Real.log x+1-x)/(x^2*(adjacentMassProfile x)^2)) x := by
    have h := ((((hasDerivAt_share (zero_lt_one.trans hx).ne').const_mul 2).div
      (hasDerivAt_profile (zero_lt_one.trans hx).ne') (adjacent_mass_profile_pos hx).ne').sub_const 1)
    convert h using 1
    <;> first | rfl | (unfold adjacentMassProfile endpointShare; field_simp [(zero_lt_one.trans hx).ne']; ring)
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    have h : 1<x := interior_subset hx
    rw [(hder x h).deriv]
    have hl := Real.log_lt_sub_one_of_pos (zero_lt_one.trans h) h.ne'
    exact div_neg_of_neg_of_pos (by linarith only [hl]) (mul_pos (sq_pos_of_pos (zero_lt_one.trans h))
      (sq_pos_of_pos (adjacent_mass_profile_pos h)))

/-- Bandwidth 2/M uniquely minimizes the limiting norm in the range
where every surviving pair of sites is adjacent. -/
theorem widest_adjacent_bandwidth_is_unique_minimum {x : ℝ} (hx : 1<x) (hu : x≤2) :
    calibratedAdjacentNorm 2 ≤ calibratedAdjacentNorm x ∧
    (calibratedAdjacentNorm 2 = calibratedAdjacentNorm x ↔ x=2) := by
  rcases hu.lt_or_eq with h|rfl
  · have hh := calibrated_adjacent_norm_strictAntiOn hx (by norm_num [Set.mem_Ioi] : (2:ℝ)∈Set.Ioi 1) h
    exact ⟨hh.le,⟨fun he => (hh.ne he).elim,fun he => (h.ne he).elim⟩⟩
  · simp

private theorem nonneg_from_one (f f' : ℝ → ℝ) (h1 : f 1 = 0)
    (hf : ∀ x, 1 ≤ x → HasDerivAt f (f' x) x) (hpos : ∀ x, 1 ≤ x → 0 ≤ f' x)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 1) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (fun y hy => (hf y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hf y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hpos y (interior_subset hy))
  rw [←h1]
  exact hm (mem_Ici.mpr le_rfl) hx hx

/-- Global quadratic bounds on the mass as the overlap opens. Both
bounds have the same leading coefficient at inverse length. -/
theorem adjacent_mass_profile_quadratic_bounds {x : ℝ} (hx : 1 ≤ x) :
    (1-x⁻¹)^2 ≤ 2*adjacentMassProfile x ∧ 2*adjacentMassProfile x ≤ (x-1)*(1-x⁻¹) := by
  constructor
  · apply sub_nonneg.mp
    apply nonneg_from_one (fun y => 2*adjacentMassProfile y-(endpointShare y)^2)
      (fun y => 2*(y-1)^2/y^3) (by norm_num [adjacentMassProfile,endpointShare]) _ _ hx
    · intro y hy
      have hn := (zero_lt_one.trans_le hy).ne'
      have h := ((hasDerivAt_profile hn).const_mul 2).sub ((hasDerivAt_share hn).pow 2)
      convert h using 1
      <;> first | rfl | (norm_num [endpointShare]; field_simp [hn] <;> ring)
    · intro y hy
      exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (pow_nonneg (zero_le_one.trans hy) _)
  · apply sub_nonneg.mp
    apply nonneg_from_one (fun y => (y-1)*endpointShare y-2*adjacentMassProfile y)
      (fun y => (y-1)^2/y^2) (by norm_num [adjacentMassProfile,endpointShare]) _ _ hx
    · intro y hy
      have hn := (zero_lt_one.trans_le hy).ne'
      have h := (((hasDerivAt_id' y).sub_const 1).mul (hasDerivAt_share hn)).sub
        ((hasDerivAt_profile hn).const_mul 2)
      convert h using 1
      <;> first | rfl | (dsimp only [endpointShare]; field_simp [hn]; ring)
    · exact fun y _ => div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The calibrated norm diverges with exact residue four at the
bottom of the first band. -/
theorem calibrated_adjacent_norm_threshold :
    Tendsto (fun x : ℝ => (x-1)*calibratedAdjacentNorm x) (𝓝[>] 1) (𝓝 4) := by
  have bounds (x : ℝ) (hx : 1<x) : 4-(x-1) ≤ (x-1)*calibratedAdjacentNorm x ∧
      (x-1)*calibratedAdjacentNorm x ≤ 4+3*(x-1) := by
    have hp := adjacent_mass_profile_pos hx
    have ht : x*endpointShare x=x-1 := by
      rw [endpointShare,mul_sub,mul_one,mul_inv_cancel₀ (zero_lt_one.trans hx).ne']
    have h := adjacent_mass_profile_quadratic_bounds hx.le
    change (endpointShare x)^2 ≤ _ ∧ _ ≤ (x-1)*endpointShare x at h
    have he : (calibratedAdjacentNorm x+1)*adjacentMassProfile x=2*endpointShare x := by
      rw [calibratedAdjacentNorm,sub_add_cancel,div_mul_cancel₀ _ hp.ne']
    have hh := congrArg (fun z : ℝ => (x-1)*z) he
    have hlow : 4 ≤ (x-1)*(calibratedAdjacentNorm x+1) :=
      (mul_le_mul_iff_left₀ hp).mp (by nlinarith only [hh,h.2])
    have hhigh : (x-1)*(calibratedAdjacentNorm x+1) ≤ 4*x :=
      (mul_le_mul_iff_left₀ hp).mp (by
        nlinarith only [hh,mul_le_mul_of_nonneg_left h.1 (zero_lt_one.trans hx).le,
          congrArg (fun z : ℝ => z*endpointShare x) ht])
    exact ⟨by linarith only [hlow],by linarith only [hhigh]⟩
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht := hid.sub_const 1
  rw [sub_self] at ht
  have hl := (tendsto_const_nhds (x:=(4:ℝ))).sub ht
  have hu := (tendsto_const_nhds (x:=(4:ℝ))).add (ht.const_mul 3)
  rw [sub_zero] at hl
  rw [mul_zero,add_zero] at hu
  have hright : ∀ᶠ x : ℝ in 𝓝[>] 1, 1 < x := self_mem_nhdsWithin
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
    (hright.mono fun x hx => (bounds x hx).1) (hright.mono fun x hx => (bounds x hx).2)


end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
