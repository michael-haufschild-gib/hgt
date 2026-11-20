import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheIncreasingWeightsOfTheFirstLogarithmicOverlap

/-!
# The total unsigned weight of the first overlap band

The reciprocal critical amplitude and the logarithmic spacing both lie
between 1/(n+1) and 1/n. Their product differs from the reciprocal
difference by at most the difference of the reciprocal squares.
These errors telescope, giving the explicit profile log(λ) − 1 + 1/λ.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology
noncomputable section

private def recip (n : ℕ) : ℝ := 1/(n:ℝ)

private def intensity (n : ℕ) : ℝ := 1/(Real.sqrt n * Real.sqrt ((n:ℝ)+1))

private theorem intensity_bounds {n : ℕ} (hn : 0<n) :
    recip (n+1) ≤ intensity n ∧ intensity n ≤ recip n := by
  have hx : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hs := Real.sqrt_le_sqrt (by linarith : (n:ℝ) ≤ (n:ℝ)+1)
  have hlo := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (n:ℝ))
  have hup := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg ((n:ℝ)+1))
  rw [Real.mul_self_sqrt hx.le] at hlo
  rw [Real.mul_self_sqrt (by positivity : 0≤(n:ℝ)+1)] at hup
  simp only [recip,intensity,Nat.cast_succ]
  exact ⟨one_div_le_one_div_of_le (hx.trans_le hlo) hup, one_div_le_one_div_of_le hx hlo⟩

private def profileStep (d : ℝ) (n : ℕ) :=
  adjacentLogGap n - (recip n-recip (n+1))/d

private def stepError (d : ℝ) (n : ℕ) :=
  recip n-recip (n+1) + ((recip n)^2-(recip (n+1))^2)/d

private theorem active_error {n : ℕ} (hn : 0<n) {d : ℝ} (hd : 0<d) (hactive : recip n ≤ d) :
    |adjacentWeight d n - profileStep d n| ≤ stepError d n := by
  have hx : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hg : recip (n+1) ≤ adjacentLogGap n ∧ adjacentLogGap n ≤ recip n := by
    simpa only [recip,Nat.cast_succ] using adjacent_log_gap_bounds hn
  have hs := intensity_bounds hn
  have h₀ : 0 ≤ recip (n+1) := by unfold recip; positivity
  have hR := hg.1.trans hg.2
  have htel : recip n - recip (n+1) = recip n*recip (n+1) := by
    simp only [recip,Nat.cast_succ]
    field_simp [hx.ne',show (n:ℝ)+1 ≠ 0 by positivity]
    ring
  have hab : |intensity n-adjacentLogGap n| ≤ recip n-recip (n+1) :=
    abs_le.mpr ⟨by linarith only [hs.1,hg.2],by linarith only [hs.2,hg.1]⟩
  have hlow := mul_le_mul hg.1 hs.1 h₀ (h₀.trans hg.1)
  have hupp := mul_le_mul hg.2 hs.2 (h₀.trans hs.1) (h₀.trans hR)
  have hprod : |adjacentLogGap n*intensity n-(recip n-recip (n+1))| ≤
      (recip n)^2-(recip (n+1))^2 := by
    rw [htel]
    have hl := mul_le_mul_of_nonneg_right hR h₀
    have hu := mul_le_mul_of_nonneg_left hR (h₀.trans hR)
    exact abs_le.mpr ⟨by nlinarith only [hlow,hu],by nlinarith only [hupp,hl]⟩
  have he : adjacentWeight d n - profileStep d n =
      (intensity n-adjacentLogGap n)-(adjacentLogGap n*intensity n-(recip n-recip (n+1)))/d := by
    rw [adjacentWeight, profileStep, max_eq_left (sub_nonneg.mpr (hg.2.trans hactive))]
    unfold intensity
    have hs₀ := (Real.sqrt_pos.mpr hx).ne'
    have hs₁ := (Real.sqrt_pos.mpr (show 0<(n:ℝ)+1 by positivity)).ne'
    field_simp [hs₀,hs₁,hd.ne']
    ring
  rw [he]
  refine (abs_sub _ _).trans (add_le_add hab ?_)
  rw [abs_div,abs_of_pos hd]
  exact div_le_div_of_nonneg_right hprod hd.le

private theorem sum_drop (f : ℕ → ℝ) {L M : ℕ} (hLM : L≤M) :
    ∑ n ∈ Ico L M, (f n-f (n+1)) = f L-f M := by
  induction M, hLM using Nat.le_induction with
  | base => simp
  | succ M h ih => rw [sum_Ico_succ_top h,ih]; ring

/-- Absolute approximation on an active tail. The two error terms depend
only on the lower endpoint, uniformly in the upper cutoff. -/
theorem active_adjacent_profile {L M : ℕ} (hL : 0 < L) (hLM : L ≤ M) {d : ℝ}
    (hd : 0 < d) (hstart : 1/(L:ℝ) ≤ d) :
    |(∑ n ∈ Ico L M, adjacentWeight d n) -
      (Real.log M-Real.log L-(1/(L:ℝ)-1/(M:ℝ))/d)| ≤ 1/(L:ℝ)+(1/(L:ℝ))^2/d := by
  have hsum : ∑ n ∈ Ico L M, adjacentLogGap n = Real.log M-Real.log L := by
    have ht := sum_drop (fun n => Real.log (n:ℝ)) hLM
    have he (n : ℕ) : adjacentLogGap n = -(Real.log n-Real.log (n+1:ℕ)) := by
      unfold adjacentLogGap
      ring
    simp_rw [he]
    rw [sum_neg_distrib,ht]
    ring
  have hprofile : ∑ n ∈ Ico L M, profileStep d n =
      Real.log M-Real.log L-(1/(L:ℝ)-1/(M:ℝ))/d := by
    simp only [profileStep]
    rw [sum_sub_distrib,←sum_div,hsum,sum_drop recip hLM]
    rfl
  rw [←hprofile,←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun n hn => active_error
    (hL.trans_le (mem_Ico.mp hn).1) hd ((one_div_le_one_div_of_le (Nat.cast_pos.mpr hL)
      (Nat.cast_le.mpr (mem_Ico.mp hn).1)).trans hstart))).trans ?_)
  simp only [stepError,sum_add_distrib,←sum_div,sum_drop recip hLM,
    sum_drop (fun n => (recip n)^2) hLM]
  change recip L-recip M+((recip L)^2-(recip M)^2)/d ≤ recip L+(recip L)^2/d
  rw [sub_div]
  linarith only [show 0≤recip M by unfold recip; positivity,div_nonneg (sq_nonneg (recip M)) hd.le]

/-- Total unsigned coefficient on adjacent products at cutoff M. -/
def adjacentMass (M : ℕ) (d : ℝ) := ∑ n ∈ Ico 1 M, adjacentWeight d n

/-- The limiting response of the unsigned adjacent products. -/
def adjacentMassProfile (scale : ℝ) := Real.log scale - 1 + scale⁻¹

/-- Every fixed scale strictly above inverse length has positive limiting mass. -/
theorem adjacent_mass_profile_pos {x : ℝ} (hx : 1<x) : 0<adjacentMassProfile x := by
  have hpos := zero_lt_one.trans hx
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hpos)
    (ne_of_lt (inv_lt_one_of_one_lt₀ hx))
  rw [Real.log_inv] at h
  unfold adjacentMassProfile
  linarith only [h]

/-- Each normalized adjacent weight is at most the reciprocal of its left endpoint. -/
theorem adjacent_weight_le_reciprocal {n : ℕ} (hn : 0<n) {d : ℝ} (hd : 0<d) :
    adjacentWeight d n ≤ 1/(n:ℝ) := by
  have hg : 0 ≤ adjacentLogGap n :=
    (by positivity : 0≤1/((n:ℝ)+1)).trans (adjacent_log_gap_bounds hn).1
  have h := (div_le_one hd).mpr (max_le (sub_le_self d hg) hd.le)
  exact (div_le_div_of_nonneg_right h (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).trans
    (intensity_bounds hn).2

/-- Uniform finite-cutoff approximation. Only the single edge crossing
the continuous lower endpoint can be partially resolved. -/
theorem adjacent_mass_profile_error (M : ℕ) {d : ℝ} (hd : 0<d) (hsmall : d≤1/2)
    (hband : 1≤d*(M:ℝ)) :
    |adjacentMass M d-adjacentMassProfile (d*M)| ≤ 5*d := by
  let L := ⌈1/d⌉₊
  have hl : 1/d ≤ (L:ℝ) := Nat.le_ceil _
  have hu : (L:ℝ) < 1/d+1 := Nat.ceil_lt_add_one (one_div_nonneg.mpr hd.le)
  have hLM : L≤M := Nat.ceil_le.mpr ((div_le_iff₀ hd).mpr (by linarith only [hband]))
  have h₁ : (2:ℝ) ≤ L := ((le_div_iff₀ hd).mpr (by linarith only [hsmall])).trans hl
  have hL : 2 ≤ L := by exact_mod_cast h₁
  have hLp : 0<(L:ℝ) := by linarith only [h₁]
  have hM : 0<(M:ℝ) := hLp.trans_le (Nat.cast_le.mpr hLM)
  let A := L-1
  have hA : 0<A := by dsimp only [A]; omega
  have hAL : A+1=L := by dsimp only [A]; omega
  have ha : (A:ℝ)+1=L := by exact_mod_cast hAL
  have hz : 1 ≤ d*(L:ℝ) := by linarith only [(div_le_iff₀ hd).mp hl]
  have hz' : d*(L:ℝ) < 1+d := by
    have hh := mul_lt_mul_of_pos_right hu hd
    rw [add_mul,div_mul_cancel₀ _ hd.ne',one_mul] at hh
    linarith only [hh]
  have hstart : 1/(L:ℝ) ≤ d := (div_le_iff₀ hLp).mpr hz
  have hpre : (∑ n ∈ Ico 1 L, adjacentWeight d n) = adjacentWeight d A := by
    apply sum_eq_single A
    · intro n hn hne
      have hpos := (mem_Ico.mp hn).1
      have hj : n+1 ≤ A := by have := (mem_Ico.mp hn).2; omega
      have hgap : d ≤ 1/((n:ℝ)+1) := by
        apply (le_div_iff₀ (by positivity)).mpr
        have hk : (n:ℝ)+1 ≤ A := by exact_mod_cast hj
        linarith only [mul_le_mul_of_nonneg_left hk hd.le,
          mul_lt_mul_of_pos_left (by linarith only [ha,hu] : (A:ℝ)<1/d) hd,div_mul_cancel₀ (1:ℝ) hd.ne']
      rw [adjacentWeight,max_eq_right (sub_nonpos.mpr (hgap.trans (adjacent_log_gap_bounds hpos).1))]
      simp
    · exact fun h => (h (mem_Ico.mpr ⟨hA,by omega⟩)).elim
  have hh := active_adjacent_profile (by omega : 0<L) hLM hd hstart
  have herr : 1/(L:ℝ)+(1/(L:ℝ))^2/d ≤ 2*d := by
    have hs := mul_le_mul hstart hstart (by positivity : (0:ℝ)≤1/L) hd.le
    have he : (1/(L:ℝ))^2/d ≤ d := (div_le_iff₀ hd).mpr (by nlinarith only [hs])
    linarith only [hstart,he]
  have htop : |adjacentWeight d A| ≤ 2*d := by
    have hn : 0≤adjacentWeight d A := div_nonneg (div_nonneg (le_max_right _ _) hd.le)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [abs_of_nonneg hn]
    apply (adjacent_weight_le_reciprocal hA hd).trans
    apply (div_le_iff₀ (Nat.cast_pos.mpr hA)).mpr
    have hle : (L:ℝ) ≤ 2*A := by linarith only [ha,h₁]
    nlinarith only [hz,mul_le_mul_of_nonneg_left hle hd.le]
  let C := Real.log M-Real.log L-(1/(L:ℝ)-1/(M:ℝ))/d
  have hdiff : C-adjacentMassProfile (d*M) = 1-(d*(L:ℝ))⁻¹-Real.log (d*L) := by
    dsimp only [C,adjacentMassProfile]
    rw [Real.log_mul hd.ne' hM.ne',Real.log_mul hd.ne' hLp.ne']
    field_simp [hd.ne',hM.ne',hLp.ne']
    ring
  have hC : |C-adjacentMassProfile (d*M)| ≤ d := by
    rw [hdiff]
    have hi := inv_le_one_of_one_le₀ hz
    have hp := zero_lt_one.trans_le hz
    exact abs_le.mpr ⟨by linarith only [hi,hz',Real.log_le_sub_one_of_pos hp],
      by linarith only [Real.one_sub_inv_le_log_of_pos hp,hd]⟩
  have hjoin := sum_Ico_consecutive (f:=adjacentWeight d) (by omega : 1≤L) hLM
  have hdecomp : adjacentMass M d - adjacentMassProfile (d*M) =
      adjacentWeight d A + ((∑ n ∈ Ico L M, adjacentWeight d n)-C) + (C-adjacentMassProfile (d*M)) := by
    rw [adjacentMass,←hjoin,hpre]
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add htop (hh.trans herr))) hC).trans_eq
    (by ring))

/-- At the exact scale λ/M the mass converges to log λ − 1 + 1/λ.
In particular the response is zero at the bottom of the overlap band. -/
theorem adjacent_mass_at_scaled_bandwidth {scale : ℝ} (hscale : 1 ≤ scale) :
    Tendsto (fun M : ℕ => adjacentMass M (scale/(M:ℝ))) atTop (𝓝 (adjacentMassProfile scale)) := by
  have hz : Tendsto (fun M : ℕ => scale/(M:ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hh := hz.const_mul 5
  rw [mul_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ hh
  filter_upwards [eventually_ge_atTop (1:ℕ),hz.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with M hM hsmall
  have hp : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  have hd := div_pos (zero_lt_one.trans_le hscale) hp
  have he := div_mul_cancel₀ scale hp.ne'
  rw [Real.norm_eq_abs]
  simpa only [he] using adjacent_mass_profile_error M hd hsmall.le (by simpa only [he] using hscale)

/-- Below inverse length every adjacent pair has zero weight. -/
theorem adjacent_mass_below_inverse_length {M : ℕ} {d : ℝ} (hd : 0≤d) (hband : d*(M:ℝ) ≤ 1) :
    adjacentMass M d=0 := by
  apply sum_eq_zero
  intro n hn
  obtain ⟨hn₁,hnM⟩ := mem_Ico.mp hn
  have hle : (n:ℝ)+1 ≤ M := by exact_mod_cast (Nat.succ_le_of_lt hnM)
  have hsmall : d ≤ 1/((n:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr
    ((mul_le_mul_of_nonneg_left hle hd).trans hband)
  rw [adjacentWeight,max_eq_right (sub_nonpos.mpr (hsmall.trans (adjacent_log_gap_bounds hn₁).1))]
  simp

/-- For any bandwidth sequence whose scaled length tends to one,
even arbitrary bounded adjacent products give a vanishing measurement.
The absolute measurement at this boundary cannot distinguish sign cancellation. -/
theorem automatic_cancellation_at_inverse_length (x : ℕ → ℝ) (d : ℕ → ℝ)
    (hx : ∀ n, |x n|≤1) (hscale : Tendsto (fun M : ℕ => d M*(M:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun M : ℕ => ∑ n ∈ Ico 1 M, x n*adjacentWeight (d M) n) atTop (𝓝 0) := by
  have hd : Tendsto d atTop (𝓝 0) := by
    apply (Tendsto.div_atTop hscale (tendsto_natCast_atTop_atTop (R:=ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with M hM
    exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (by omega))
  have hP : Tendsto (fun M : ℕ => adjacentMassProfile (d M*M)) atTop (𝓝 0) := by
    have h := ((hscale.log one_ne_zero).sub_const 1).add (hscale.inv₀ one_ne_zero)
    simpa only [adjacentMassProfile,Real.log_one,inv_one,zero_sub,neg_add_cancel] using h
  have hu := hP.add (hd.const_mul 5)
  rw [mul_zero,zero_add] at hu
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ hu
  filter_upwards [hscale.eventually_const_lt zero_lt_one,hd.eventually_lt_const
    (by norm_num : (0:ℝ)<1/2)] with M hb hs
  have hpos : 0<d M := pos_of_mul_pos_left hb (Nat.cast_nonneg M)
  have hweight (n : ℕ) : 0≤adjacentWeight (d M) n :=
    div_nonneg (div_nonneg (le_max_right _ _) hpos.le) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simp only [sub_zero,Real.norm_eq_abs]
  calc
    _ ≤ ∑ n ∈ Ico 1 M, |x n*adjacentWeight (d M) n| := abs_sum_le_sum_abs _ _
    _ ≤ adjacentMass M (d M) := sum_le_sum fun n _ => by
      rw [abs_mul,abs_of_nonneg (hweight _)]
      exact mul_le_of_le_one_left (hweight _) (hx _)
    _ ≤ _ := by
      rcases le_total 1 (d M*M) with h|h
      · have hh := (abs_le.mp (adjacent_mass_profile_error M hpos hs.le h)).2
        linarith only [hh]
      · rw [adjacent_mass_below_inverse_length hpos.le h]
        change 0≤Real.log (d M*M)-1+(d M*M)⁻¹+5*d M
        linarith only [Real.one_sub_inv_le_log_of_pos hb,hpos]

#print axioms automatic_cancellation_at_inverse_length

#print axioms adjacent_mass_profile_error
#print axioms adjacent_mass_at_scaled_bandwidth

#print axioms active_adjacent_profile
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
