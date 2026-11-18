import GaloisForLFunctions.RHTower.Sieve.Buchstab.LaplaceIdentity

/-!
# Two-sided oscillation on every sliding unit interval

The centered weighted value is the negative tail integral one unit earlier.
A fixed sign throughout a unit window propagates forward by the positive
delay equation. The tail identity would force eventual equality to the limit.
Backward differentiation would then make the initial reciprocal branch constant.
-/

namespace RHTower.Sieve.Buchstab
open Set Filter MeasureTheory Topology
noncomputable section

private def errorAt (s x : ℝ) := s*(buchstab x-enclosureLimit)

private theorem weighted_primitive (s : ℝ) (x : Ici (1:ℝ)) :
    x.val*errorAt s x = s*(1-enclosureLimit)+∫ t in (0:ℝ)..(x.val-1), errorAt s t := by
  rw [errorAt,show (∫ t in (0:ℝ)..(x.val-1), errorAt s t) =
      s*(∫ t in (0:ℝ)..(x.val-1), buchstab t-enclosureLimit) from intervalIntegral.integral_const_mul _ _,
    intervalIntegral.integral_sub (intervalIntegrable_buchstab _ _) intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  linear_combination s*buchstab_weighted x

/-- Exact negative-tail identity for the actual limiting error. -/
theorem buchstab_weighted_error_tail (x : Ici (1:ℝ)) :
    x.val*(buchstab x-enclosureLimit) =
      -(∫ t in Ioi (x.val-1), buchstab t-enclosureLimit) := by
  have hi : IntegrableOn (fun t => buchstab t-enclosureLimit) (Ioi (0:ℝ)) := by
    simpa only [zero_mul,Real.exp_zero,mul_one] using integrable_buchstab_correction 0
  have hh := intervalIntegral.integral_interval_add_Ioi (b:=x.val-1) hi
    (hi.mono_set (Ioi_subset_Ioi (sub_nonneg.mpr x.property)))
  have hw := weighted_primitive 1 x
  simp only [errorAt,one_mul] at hw
  rw [integral_buchstab_correction] at hh
  linarith only [hh,hw]

private theorem signed_tail (s : ℝ) (x : Ici (1:ℝ)) :
    x.val*errorAt s x = -(∫ t in Ioi (x.val-1), errorAt s t) := by
  rw [errorAt,show (∫ t in Ioi (x.val-1), errorAt s t) =
    s*(∫ t in Ioi (x.val-1), buchstab t-enclosureLimit) from integral_const_mul _ _]
  linear_combination s*buchstab_weighted_error_tail x

private theorem interval_error (s a b : ℝ) : IntervalIntegrable (errorAt s) volume a b :=
  ((intervalIntegrable_buchstab a b).sub intervalIntegrable_const).const_mul s

private theorem weighted_increment (s : ℝ) (x y : Ici (1:ℝ)) :
    y.val*errorAt s y = x.val*errorAt s x + ∫ t in (x.val-1)..(y.val-1), errorAt s t := by
  rw [weighted_primitive,weighted_primitive,add_assoc,intervalIntegral.integral_add_adjacent_intervals
    (interval_error s _ _) (interval_error s _ _)]

private theorem sign_forward (s : ℝ) (a : Ici (1:ℝ))
    (h : ∀ t ∈ Icc a.val (a.val+1), 0 ≤ errorAt s t) :
    ∀ t ∈ Ici a.val, 0 ≤ errorAt s t := by
  have hstep (n : ℕ) : ∀ t ∈ Icc (a.val+n) (a.val+n+1), 0 ≤ errorAt s t := by
    induction n with
    | zero => simpa using h
    | succ n ih =>
      intro t ht
      simp only [Nat.cast_succ] at ht
      let b := a.val+n+1
      have hb : 1 ≤ b := by dsimp [b]; linarith only [show 1 ≤ a.val from a.property,Nat.cast_nonneg (α:=ℝ) n]
      have hbt : b ≤ t := by dsimp [b]; linarith [ht.1]
      have htb : t ≤ b+1 := by dsimp [b]; linarith [ht.2]
      have hpos : 0 < t := zero_lt_one.trans_le (hb.trans hbt)
      have hI : 0 ≤ ∫ z in (b-1)..(t-1), errorAt s z :=
        intervalIntegral.integral_nonneg (by linarith) (fun z hz => ih z
          ⟨by dsimp [b] at hz; linarith [hz.1], by change z ≤ b; linarith [hz.2]⟩)
      have h₀ := ih b ⟨by dsimp [b]; linarith,le_rfl⟩
      have hw := weighted_increment s ⟨b,hb⟩ ⟨t,hb.trans hbt⟩
      exact nonneg_of_mul_nonneg_right (hw ▸ add_nonneg (mul_nonneg (zero_le_one.trans hb) h₀) hI) hpos
  intro t ht
  have ha : 0 ≤ t-a.val := sub_nonneg.mpr ht
  have hfloor := Nat.floor_le ha
  have hfloor' := Nat.lt_floor_add_one (t-a.val)
  exact hstep ⌊t-a.val⌋₊ t ⟨by linarith,by linarith⟩

private theorem shift_constant {r : ℝ} (hr : 1 ≤ r)
    (hc : ∀ x, r+1 < x → buchstab x=enclosureLimit) :
    ∀ x, r < x → buchstab x=enclosureLimit := by
  intro x hx
  have hy : 2 < x+1 := by linarith
  have he : buchstab =ᶠ[𝓝 (x+1)] (fun _ => enclosureLimit) := by
    filter_upwards [lt_mem_nhds (show r+1<x+1 by linarith)] with y h
    exact hc y h
  have hD := (hasDerivAt_buchstab ⟨x+1,hy⟩).deriv
  have hz := he.deriv_eq
  rw [deriv_const,hD] at hz
  have hh : buchstab x = buchstab (x+1) := sub_eq_zero.mp
    ((div_eq_zero_iff.mp (by simpa only [add_sub_cancel_right] using hz)).resolve_right (by linarith))
  exact hh.trans (hc _ (by linarith))

/-- Eventual equality to the limit is impossible, even on a ray starting
arbitrarily far to the right. -/
theorem buchstab_not_eventually_constant : ¬ (∀ᶠ t in atTop, buchstab t=enclosureLimit) := by
  intro h
  obtain ⟨a,ha⟩ := eventually_atTop.1 h
  let n := ⌈a⌉₊
  have h₀ : ∀ t : ℝ, (n:ℝ)+1 < t → buchstab t=enclosureLimit := by
    intro t ht
    exact ha t ((Nat.le_ceil a).trans (by linarith))
  have back (k : ℕ) : (∀ t : ℝ, (k:ℝ)+1 < t → buchstab t=enclosureLimit) →
      ∀ t : ℝ, 1<t → buchstab t=enclosureLimit := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      apply ih
      apply shift_constant (r:=(k:ℝ)+1) (by linarith [Nat.cast_nonneg (α:=ℝ) k])
      simpa only [Nat.cast_succ] using hk
  have hconst := back n h₀
  have h₁ := buchstab_cell 0 1 ⟨zero_le_one,le_rfl⟩
  have h₂ := buchstab_cell 0 (1/2) ⟨by norm_num,by norm_num⟩
  norm_num [profile,intervalMass] at h₁ h₂
  linarith only [hconst 2 (by norm_num),hconst (3/2) (by norm_num),h₁,h₂]

private theorem signed_negative (s : ℝ) (hs : s ≠ 0) (a : Ici (1:ℝ)) :
    ∃ t ∈ Icc a.val (a.val+1), errorAt s t < 0 := by
  by_contra! hn
  have hprop := sign_forward s a hn
  apply buchstab_not_eventually_constant
  filter_upwards [eventually_ge_atTop (a.val+1)] with x hx
  have hxa : a.val ≤ x := by linarith
  have hx₁ : 1 ≤ x := a.property.trans hxa
  have hI : 0 ≤ ∫ t in Ioi (x-1), errorAt s t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => hprop t (show a.val ≤ t by linarith [show x-1<t from ht])
  have hw := signed_tail s ⟨x,hx₁⟩
  have he : errorAt s x = 0 := le_antisymm
    (nonpos_of_mul_nonpos_right (hw.trans_le (neg_nonpos.mpr hI)) (zero_lt_one.trans_le hx₁)) (hprop x hxa)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)

/-- Every sliding unit interval beyond the support edge contains values
strictly below and strictly above the limiting density. -/
theorem buchstab_oscillates_each_unit (a : Ici (1:ℝ)) :
    (∃ u ∈ Icc a.val (a.val+1), buchstab u < enclosureLimit) ∧
    (∃ v ∈ Icc a.val (a.val+1), enclosureLimit < buchstab v) := by
  constructor
  · simpa [errorAt] using signed_negative 1 one_ne_zero a
  · simpa [errorAt] using signed_negative (-1) (by norm_num) a

/-- Every open interval of length one contains an exact crossing level. -/
theorem buchstab_attains_limit_each_unit (a : Ici (1:ℝ)) :
    ∃ t ∈ Ioo a.val (a.val+1), buchstab t = enclosureLimit := by
  obtain ⟨⟨u,hu,hu'⟩,⟨v,hv,hv'⟩⟩ := buchstab_oscillates_each_unit a
  rcases le_total u v with huv | hvu
  · obtain ⟨z,hz,he⟩ := intermediate_value_Ioo huv
      (continuousOn_buchstab.mono fun x hx => a.property.trans (hu.1.trans hx.1))
      (show enclosureLimit ∈ Ioo (buchstab u) (buchstab v) from ⟨hu',hv'⟩)
    exact ⟨z,⟨hu.1.trans_lt hz.1,hz.2.trans_le hv.2⟩,he⟩
  · obtain ⟨z,hz,he⟩ := intermediate_value_Ioo' hvu
      (continuousOn_buchstab.mono fun x hx => a.property.trans (hv.1.trans hx.1))
      (show enclosureLimit ∈ Ioo (buchstab u) (buchstab v) from ⟨hu',hv'⟩)
    exact ⟨z,⟨hv.1.trans_lt hz.1,hz.2.trans_le hu.2⟩,he⟩

/-- The Euler limit is characterized intrinsically as the only real value
attained on every open unit interval of the positive tail. -/
theorem buchstab_common_unit_range :
    (⋂ a : Ici (1:ℝ), buchstab '' Ioo a.val (a.val+1)) = {enclosureLimit} := by
  ext c
  constructor
  · intro hc
    have h (n : ℕ) := mem_iInter.mp hc (⟨(n:ℝ)+1,show (1:ℝ) ≤ (n:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) n]⟩ : Ici (1:ℝ))
    choose x hx hval using h
    have htop : Tendsto x atTop atTop := tendsto_atTop_mono
      (fun n => (show (n:ℝ) ≤ x n from (by linarith only : (n:ℝ) ≤ (n:ℝ)+1).trans (show (n:ℝ)+1 < x n from (hx n).1).le)) tendsto_natCast_atTop_atTop
    have hh := tendsto_buchstab_atTop.comp htop
    have hc' : Tendsto (fun n : ℕ => c) atTop (𝓝 enclosureLimit) := by
      simpa only [Function.comp_def,hval] using hh
    exact tendsto_nhds_unique tendsto_const_nhds hc'
  · rintro (rfl : c=enclosureLimit)
    exact mem_iInter.mpr buchstab_attains_limit_each_unit

#print axioms buchstab_attains_limit_each_unit
#print axioms buchstab_common_unit_range
#print axioms buchstab_weighted_error_tail
#print axioms buchstab_not_eventually_constant
#print axioms buchstab_oscillates_each_unit
end
end RHTower.Sieve.Buchstab
