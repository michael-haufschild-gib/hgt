import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheLowerCountingOrderOfMertensExcursions
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# All positive moments of the reciprocal Mertens weights

Place weight |M(k)|/k at k and normalize by their total through N. The
sum of the q-th powers of these probabilities has logarithmic exponent
max(1-q,-qΘ). The two branches come from the numerous subcritical
excursions and the first atom of unnormalized weight one, respectively.
-/

noncomputable section
open Finset Filter Topology
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

def reciprocalMertensWeight (k : ℕ) := ‖mobiusMertensPartialSum k‖/(k:ℝ)

def reciprocalMertensMoment (q : ℝ) (N : ℕ) :=
  ∑ k ∈ Icc 1 N, (reciprocalMertensWeight k)^q

private theorem nonneg_weight (k : ℕ) : 0≤reciprocalMertensWeight k :=
  div_nonneg (norm_nonneg _) (Nat.cast_nonneg k)

/-- The first reciprocal cell has exactly unit weight. -/
theorem reciprocal_mertens_weight_one : reciprocalMertensWeight 1=1 := by
  simp [reciprocalMertensWeight,←sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum,mobCoeff_one]

/-- The first cell gives a unit lower bound at every positive cutoff. -/
theorem reciprocal_mertens_moment_one_le (q : ℝ) {N : ℕ} (hn : 1≤N) : 1≤reciprocalMertensMoment q N := by
  unfold reciprocalMertensMoment
  calc (1 : ℝ) = (reciprocalMertensWeight 1)^q := by rw [reciprocal_mertens_weight_one,Real.one_rpow]
       _ ≤ _ := single_le_sum (f:=fun k => (reciprocalMertensWeight k)^q)
         (fun k _ => Real.rpow_nonneg (nonneg_weight k) q)
         (show (1:ℕ)∈Icc 1 N from mem_Icc.mpr ⟨le_rfl,hn⟩)

/-- Above the larger of the summability edge and zero, power counting
gives a uniform bound on all integer cutoffs. -/
theorem reciprocal_mertens_moment_upper {q v : ℝ} (hq : 0<q)
    (hv : max 0 (1+q*(zetaZeroAbscissa-1))<v) :
    ∃ B : ℝ, 0≤B ∧ ∀ N, reciprocalMertensMoment q N ≤ B*((N:ℝ)+1)^v := by
  have hv0 := (le_max_left ..).trans_lt hv
  have hv' := (le_max_right ..).trans_lt hv
  let a := 1+(v-1)/q
  have ha : zetaZeroAbscissa<a := by
    have h : zetaZeroAbscissa-1 < (v-1)/q := (lt_div_iff₀ hq).mpr (by linarith only [hv'])
    dsimp only [a]; linarith only [h]
  have ha0 : 0≤a := by linarith only [half_le_zetaZeroAbscissa,ha]
  have hpow : (a-1)*q=v-1 := by dsimp only [a]; field_simp [hq.ne']; ring
  obtain ⟨A,hA,hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
  rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa)=a by ring] at hM
  let C := A*2^a
  have hC : 0≤C := mul_nonneg hA (by positivity)
  refine ⟨C^q*(1+1/v),mul_nonneg (Real.rpow_nonneg hC _) (by positivity),fun N => ?_⟩
  have row (j : ℕ) : (reciprocalMertensWeight (j+1))^q ≤ C^q*((j:ℝ)+1)^(v-1) := by
    let x := (j:ℝ)+1
    have h1 : 1≤x := le_add_of_nonneg_left (Nat.cast_nonneg j)
    have xp := zero_lt_one.trans_le h1
    have h := hM (j+1)
    rw [Nat.cast_succ] at h
    have hcap := Real.rpow_le_rpow (by positivity : 0≤x+1)
      (by linarith only [h1] : x+1≤2*x) ha0
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) xp.le] at hcap
    have hj : reciprocalMertensWeight (j+1) ≤ C*x^(a-1) := by
      unfold reciprocalMertensWeight
      rw [Nat.cast_succ]
      apply (div_le_iff₀ xp).mpr
      rw [Real.rpow_sub xp,Real.rpow_one]
      exact (h.trans (mul_le_mul_of_nonneg_left hcap hA)).trans_eq (by dsimp only [C]; field_simp)
    have hh := Real.rpow_le_rpow (nonneg_weight _) hj hq.le
    rwa [Real.mul_rpow hC (Real.rpow_nonneg xp.le _),←Real.rpow_mul xp.le,hpow] at hh
  have hs := sum_le_sum (s:=range N) (fun j _ => row j)
  rw [←mul_sum] at hs
  rw [reciprocalMertensMoment,_root_.RHTower.sum_Icc_eq_sum_range_shift]
  exact hs.trans ((mul_le_mul_of_nonneg_left (ArithmeticGaugeTheory.sum_rpow_sub_one_le hv0 N)
    (Real.rpow_nonneg hC _)).trans_eq (by ring))

/-- Each subcritical height supplies a full counting exponent, even
under the critical-line configuration. Division by the running index
costs at most one power at the final cutoff. -/
theorem reciprocal_mertens_moment_lower {q c : ℝ} (hq : 0<q)
    (hc : c<1+q*(zetaZeroAbscissa-1)) :
    ∀ᶠ N : ℕ in atTop, ((N:ℝ)+1)^c < reciprocalMertensMoment q N := by
  have hΘ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  have hfrac : 1+(c-1)/q < zetaZeroAbscissa := by
    have h : (c-1)/q < zetaZeroAbscissa-1 := (div_lt_iff₀ hq).mpr (by linarith only [hc])
    linarith only [h]
  obtain ⟨b,hb,hbΘ⟩ := exists_between (max_lt hΘ hfrac)
  have hb1 := hbΘ.le.trans zetaZeroAbscissa_le_one
  have hb' := (le_max_right 0 _).trans_lt hb
  have hc' : c-q*(b-1)<1 := by
    have hh := (div_lt_iff₀ hq).mp (show (c-1)/q<b-1 by linarith only [hb'])
    linarith only [hh]
  let d := c-q*(b-1)
  filter_upwards [all_cutoffs_many_mertens_excursions hbΘ hc' 1 1] with N hpop
  let E := mertensExcursions b 1 N
  let X := (N:ℝ)+1
  have xp : 0<X := by dsimp only [X]; positivity
  have hs : E ⊆ Icc 1 N := by
    intro k hk
    obtain ⟨hkn,hk'⟩ := mem_filter.mp hk
    refine mem_Icc.mpr ⟨?_,Nat.lt_succ_iff.mp (mem_range.mp hkn)⟩
    by_contra! hz
    have he : k=0 := by omega
    subst k
    have himpossible : (1:ℝ)<0 := by simpa [shiftedMertensReal] using hk'
    exact (by norm_num : ¬(1:ℝ)<0) himpossible
  have row (k : ℕ) (hk : k∈E) : X^(q*(b-1)) ≤ (reciprocalMertensWeight k)^q := by
    obtain ⟨h1,hN⟩ := mem_Icc.mp (hs hk)
    have kpos : 0<(k:ℝ) := Nat.cast_pos.mpr h1
    have kxp : 0<(k:ℝ)+1 := by positivity
    have hw := Real.rpow_le_rpow_of_nonpos kxp (add_le_add (Nat.cast_le.mpr hN) (le_refl (1:ℝ)))
      (sub_nonpos.mpr hb1)
    have hm := (mem_filter.mp hk).2
    change 1*((k:ℝ)+1)^b < |shiftedMertensReal k| at hm
    rw [one_mul,←norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at hm
    have hrow : ((k:ℝ)+1)^(b-1) ≤ reciprocalMertensWeight k := by
      apply (le_div_iff₀ kpos).mpr
      have h := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one : (k:ℝ)≤k+1)
        (Real.rpow_nonneg kxp.le (b-1))
      rw [Real.rpow_sub kxp,Real.rpow_one,div_mul_cancel₀ _ kxp.ne'] at h
      rw [Real.rpow_sub kxp,Real.rpow_one]
      exact h.trans hm.le
    rw [mul_comm q (b-1),Real.rpow_mul xp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg xp.le _) (hw.trans hrow) hq.le
  have he := (sum_le_sum row).trans (sum_le_sum_of_subset_of_nonneg hs
    (fun k _ _ => Real.rpow_nonneg (nonneg_weight k) q))
  rw [sum_const,nsmul_eq_mul] at he
  rw [one_mul] at hpop
  have h := mul_lt_mul_of_pos_right hpop (Real.rpow_pos_of_pos xp (q*(b-1)))
  change X^d*X^(q*(b-1)) < _ at h
  rw [←Real.rpow_add xp,show d+q*(b-1)=c by dsimp only [d]; ring] at h
  exact h.trans_le he

/-- Ordinary logarithmic order of the unnormalized q-th moment. The
zero branch includes the critical value and needs no strict zero gap. -/
theorem reciprocal_mertens_moment_log_order {q : ℝ} (hq : 0<q) :
    Tendsto (fun N : ℕ => Real.log (reciprocalMertensMoment q N)/Real.log ((N:ℝ)+1))
      atTop (𝓝 (max 0 (1+q*(zetaZeroAbscissa-1)))) := by
  have hX : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro c hc
    by_cases hc0 : c<0
    · filter_upwards [eventually_ge_atTop 1] with N hn
      exact hc0.trans_le (div_nonneg (Real.log_nonneg (reciprocal_mertens_moment_one_le q hn))
        (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg N))))
    · have h := (lt_max_iff.mp hc).resolve_left hc0
      filter_upwards [reciprocal_mertens_moment_lower hq h,eventually_ge_atTop 1] with N hm hn
      have hx := lt_add_of_pos_left 1 (Nat.cast_pos.mpr hn : 0<(N:ℝ))
      have hp := zero_lt_one.trans hx
      have hl := Real.log_lt_log (Real.rpow_pos_of_pos hp _) hm
      rw [Real.log_rpow hp] at hl
      exact (lt_div_iff₀ (Real.log_pos hx)).mpr hl
  · intro c hc
    obtain ⟨v,hv,hvc⟩ := exists_between hc
    obtain ⟨B,hB,hcap⟩ := reciprocal_mertens_moment_upper hq hv
    filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hvc)).comp hX).eventually_gt_atTop B,
      eventually_ge_atTop 1] with N hlarge hn
    have hx := lt_add_of_pos_left 1 (Nat.cast_pos.mpr hn : 0<(N:ℝ))
    have hp := zero_lt_one.trans hx
    have ht := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hp v)
    change _ < ((N:ℝ)+1)^(c-v)*((N:ℝ)+1)^v at ht
    rw [←Real.rpow_add hp,sub_add_cancel] at ht
    have hl := Real.log_lt_log (zero_lt_one.trans_le (reciprocal_mertens_moment_one_le q hn)) ((hcap N).trans_lt ht)
    rw [Real.log_rpow hp] at hl
    exact (div_lt_iff₀ (Real.log_pos hx)).mpr hl

theorem reciprocal_mertens_first_moment (N : ℕ) :
    reciprocalMertensMoment 1 N=mertensAbelMass N := by
  simp only [reciprocalMertensMoment,reciprocalMertensWeight,Real.rpow_one,mertens_abel_mass_eq]

/-- The normalized moment exponent is max(1−q,−qΘ). The first term
is the uniform-law exponent and the second is forced by the atom at 1. -/
theorem normalized_reciprocal_mertens_moment_order {q : ℝ} (hq : 0<q) :
    Tendsto (fun N : ℕ => Real.log (reciprocalMertensMoment q N/(mertensAbelMass N)^q) /
      Real.log ((N:ℝ)+1)) atTop (𝓝 (max (1-q) (-q*zetaZeroAbscissa))) := by
  have h₁ := reciprocal_mertens_moment_log_order (q:=1) zero_lt_one
  have he : max 0 (1+1*(zetaZeroAbscissa-1))=zetaZeroAbscissa := by
    rw [show 1+1*(zetaZeroAbscissa-1)=zetaZeroAbscissa by ring]
    exact max_eq_right (by linarith only [half_le_zetaZeroAbscissa])
  simp only [reciprocal_mertens_first_moment,he] at h₁
  have h := (reciprocal_mertens_moment_log_order hq).sub (h₁.const_mul q)
  have ht : max 0 (1+q*(zetaZeroAbscissa-1))-q*zetaZeroAbscissa = max (1-q) (-q*zetaZeroAbscissa) := by
    rcases le_total 0 (1+q*(zetaZeroAbscissa-1)) with hv|hv
    · rw [max_eq_right hv,max_eq_left (by linarith only [hv] : -q*zetaZeroAbscissa≤1-q)]
      ring
    · rw [max_eq_left hv,max_eq_right (by linarith only [hv] : 1-q≤-q*zetaZeroAbscissa)]
      ring
  rw [ht] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  have hp := zero_lt_one.trans_le (reciprocal_mertens_moment_one_le q hn)
  have hm := zero_lt_one.trans_le (reciprocal_mertens_moment_one_le 1 hn)
  rw [reciprocal_mertens_first_moment] at hm
  rw [Real.log_div hp.ne' (Real.rpow_pos_of_pos hm q).ne',Real.log_rpow hm]
  ring

/-- At and below order two the normalized exponent is universal. -/
theorem low_reciprocal_mertens_moment_order {q : ℝ} (hq : 0<q) (hq2 : q≤2) :
    Tendsto (fun N : ℕ => Real.log (reciprocalMertensMoment q N/(mertensAbelMass N)^q) /
      Real.log ((N:ℝ)+1)) atTop (𝓝 (1-q)) := by
  have he : -q*zetaZeroAbscissa ≤ 1-q := by
    linarith only [mul_le_mul_of_nonneg_left half_le_zetaZeroAbscissa hq.le,hq2]
  simpa only [max_eq_left he] using normalized_reciprocal_mertens_moment_order hq

/-- Every fixed order strictly greater than two separates the
critical-line case from every positive zero width. -/
theorem rh_iff_high_reciprocal_mertens_moment_order {q : ℝ} (hq : 2<q) :
    RiemannHypothesis ↔
      Tendsto (fun N : ℕ => Real.log (reciprocalMertensMoment q N/(mertensAbelMass N)^q) /
        Real.log ((N:ℝ)+1)) atTop (𝓝 (-q/2)) := by
  have hq0 := (by norm_num : (0:ℝ)<2).trans hq
  have h := normalized_reciprocal_mertens_moment_order hq0
  have hleft : 1-q < -q/2 := by linarith only [hq]
  rw [←zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor
  · intro he
    rw [he,show -q*(1/2)= -q/2 by ring,max_eq_right hleft.le] at h
    exact h
  · intro hr
    have he := tendsto_nhds_unique h hr
    rcases le_total (1-q) (-q*zetaZeroAbscissa) with hle|hle
    · rw [max_eq_right hle] at he
      have hz : q*(zetaZeroAbscissa-1/2)=0 := by linarith only [he]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hq0.ne')
    · rw [max_eq_left hle] at he
      exact (hleft.ne he).elim

#print axioms low_reciprocal_mertens_moment_order
#print axioms rh_iff_high_reciprocal_mertens_moment_order
#print axioms reciprocal_mertens_moment_upper
#print axioms reciprocal_mertens_moment_lower
#print axioms reciprocal_mertens_moment_log_order
#print axioms normalized_reciprocal_mertens_moment_order
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
