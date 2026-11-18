import GaloisForLFunctions.RHTower.Sieve.Buchstab.GlobalDelay

/-!
# Exact range of the Buchstab function beyond its initial cell

The first logarithmic branch peaks at the omega constant `w exp w = 1`.
The tangent inequality for the logarithm proves the peak is unique.
Every later cell is a weighted mean with a strictly smaller endpoint,
so none can attain it again.
-/

namespace RHTower.Sieve.Buchstab
open Set MeasureTheory Filter Topology
noncomputable section

private theorem exists_log_root : ∃ w ∈ Ioo (1/2 : ℝ) 1, Real.log w + w = 0 := by
  let f := fun x : ℝ => Real.log x + x
  have hhalf : (0:ℝ) < 1/2 := by norm_num
  have hlo : f (1/2) < 0 := by
    dsimp [f]
    linarith only [Real.log_lt_sub_one_of_pos hhalf (by norm_num)]
  have hhi : 0 < f 1 := by simp [f]
  have hc : ContinuousOn f (Icc (1/2:ℝ) 1) :=
    (Real.continuousOn_log.mono fun x hx => (hhalf.trans_le hx.1).ne').add continuousOn_id
  obtain ⟨w,hw,he⟩ := intermediate_value_Icc (by norm_num : (1/2:ℝ) ≤ 1) hc
    (show (0:ℝ) ∈ Icc (f (1/2)) (f 1) from ⟨hlo.le,hhi.le⟩)
  refine ⟨w, ⟨lt_of_le_of_ne hw.1 (fun h => ?_), lt_of_le_of_ne hw.2 (fun h => ?_)⟩, he⟩
  · subst w
    exact hlo.ne he
  · subst w
    exact hhi.ne' he

/-- The positive solution of `w exp w = 1`. -/
def omegaConstant : ℝ := Classical.choose exists_log_root

theorem omegaConstant_mem : omegaConstant ∈ Ioo (1/2 : ℝ) 1 :=
  (Classical.choose_spec exists_log_root).1

private theorem omega_pos : 0 < omegaConstant := lt_trans (by norm_num) omegaConstant_mem.1

private theorem log_omega : Real.log omegaConstant = -omegaConstant := by
  linarith only [(Classical.choose_spec exists_log_root).2]

theorem omegaConstant_mul_exp : omegaConstant * Real.exp omegaConstant = 1 := by
  calc
    _ = Real.exp (Real.log omegaConstant + omegaConstant) := by rw [Real.exp_add, Real.exp_log omega_pos]
    _ = 1 := by rw [log_omega, neg_add_cancel, Real.exp_zero]

/-- Offset from the start of the logarithmic branch at which the maximum occurs. -/
def peakOffset : ℝ := 1 / omegaConstant - 1

theorem peakOffset_mem : peakOffset ∈ Ioo (0:ℝ) 1 := by
  have h₁ : 1 < 1 / omegaConstant := (lt_div_iff₀ omega_pos).mpr (by simpa using omegaConstant_mem.2)
  have h₂ : 1 / omegaConstant < 2 := (div_lt_iff₀ omega_pos).mpr (by linarith [omegaConstant_mem.1])
  exact ⟨by dsimp [peakOffset]; linarith, by dsimp [peakOffset]; linarith⟩

private theorem peak_eq_iff (x : ℝ) : omegaConstant * (1+x) = 1 ↔ x = peakOffset := by
  dsimp [peakOffset]
  constructor
  · intro h
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff omega_pos.ne').mpr
    linarith only [show (x+1)*omegaConstant = omegaConstant*(1+x) by ring, h]
  · rintro rfl
    field_simp [omega_pos.ne']
    <;> ring

/-- The deficit from the maximum is the logarithmic tangent deficit,
evaluated at the scaled argument. -/
theorem peak_deficit (x : Ici (0:ℝ)) :
    (2+x.val) * (omegaConstant - profile 1 x.val) =
      omegaConstant*(1+x.val) - 1 - Real.log (omegaConstant*(1+x.val)) := by
  have hp : 0 < 1+x.val := by linarith [x.property]
  have hd : 2+x.val ≠ 0 := by linarith [x.property]
  rw [profile_one_formula x, Real.log_mul omega_pos.ne' hp.ne', log_omega]
  field_simp [hd]
  <;> ring

theorem profile_one_le_peak (x : Ici (0:ℝ)) : profile 1 x.val ≤ omegaConstant := by
  have hp : 0 < 1+x.val := by linarith [x.property]
  have hd : 0 < 2+x.val := by linarith [x.property]
  have hz := Real.log_le_sub_one_of_pos (mul_pos omega_pos hp)
  have h : 0 ≤ (2+x.val) * (omegaConstant-profile 1 x.val) := by rw [peak_deficit x]; linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp h)

theorem profile_one_eq_peak_iff (x : Ici (0:ℝ)) : profile 1 x.val = omegaConstant ↔ x.val = peakOffset := by
  have hp : 0 < 1+x.val := by linarith [x.property]
  have hd : 0 < 2+x.val := by linarith [x.property]
  constructor
  · intro h
    by_contra hn
    have hh := Real.log_lt_sub_one_of_pos (mul_pos omega_pos hp) (fun he => hn ((peak_eq_iff _).mp he))
    have he := peak_deficit x
    rw [h, sub_self, mul_zero] at he
    linarith
  · intro h
    have he := peak_deficit x
    rw [(peak_eq_iff _).mpr h, Real.log_one, sub_self, sub_zero] at he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hd.ne')).symm

private theorem propagate_strict (n : ℕ) (hend : profile n 1 < omegaConstant)
    (hall : ∀ z ∈ Icc (0:ℝ) 1, profile n z ≤ omegaConstant)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : profile (n+1) x < omegaConstant := by
  have hi := intervalIntegral.integral_mono_on hx.1 ((profile_continuous n).intervalIntegrable (μ := volume) 0 x)
    (intervalIntegrable_const (c := omegaConstant)) (fun z hz => hall z ⟨hz.1,hz.2.trans hx.2⟩)
  have hI : (∫ z in (0:ℝ)..x, profile n z) ≤ x*omegaConstant := by simpa using hi
  rw [profile_succ_mean n hx.1, div_lt_iff₀ (show 0 < (n:ℝ)+2+x by linarith [Nat.cast_nonneg (α := ℝ) n,hx.1])]
  nlinarith only [hI, mul_lt_mul_of_pos_left hend (show 0 < (n:ℝ)+2 by positivity)]

/-- Every point from the third cell onward lies strictly below the first peak. -/
theorem later_profile_lt_peak (n : ℕ) : ∀ x ∈ Icc (0:ℝ) 1, profile (n+2) x < omegaConstant := by
  induction n with
  | zero =>
    apply propagate_strict 1
    · apply lt_of_le_of_ne (profile_one_le_peak ⟨1,zero_le_one⟩)
      intro h
      exact peakOffset_mem.2.ne ((profile_one_eq_peak_iff ⟨1,zero_le_one⟩).mp h).symm
    · exact fun z hz => profile_one_le_peak ⟨z,hz.1⟩
  | succ n ih =>
    exact propagate_strict (n+2) (ih 1 ⟨zero_le_one,le_rfl⟩) (fun z hz => (ih z hz).le)

/-- The entire tail starting at argument two has exactly the same range as the
interval from two to its first maximum. -/
theorem profile_tail_range :
    (⋃ n : ℕ, profile (n+1) '' Icc (0:ℝ) 1) = Icc (1/2) omegaConstant := by
  have hnest (n : ℕ) : Icc (enclosure n).1 (enclosure n).2 ⊆ Icc (enclosure 0).1 (enclosure 0).2 := by
    induction n with
    | zero => exact Subset.rfl
    | succ n ih => exact (enclosure_nested n).trans ih
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
    refine ⟨(hnest _ (profile_mem_enclosure _ x hx)).1, ?_⟩
    cases n with
    | zero => exact profile_one_le_peak ⟨x,hx.1⟩
    | succ n => exact (later_profile_lt_peak n x hx).le
  · intro y hy
    have hstart : profile 1 0 = 1/2 := by norm_num [profile_glue, profile, intervalMass]
    have hpeak := (profile_one_eq_peak_iff ⟨peakOffset, peakOffset_mem.1.le⟩).mpr rfl
    have h := intermediate_value_Icc peakOffset_mem.1.le (profile_continuous 1).continuousOn
    obtain ⟨x,hx,hxy⟩ := h (show y ∈ Icc (profile 1 0) (profile 1 peakOffset) by rwa [hstart,hpeak])
    exact mem_iUnion.mpr ⟨0, x, ⟨hx.1,hx.2.trans peakOffset_mem.2.le⟩,hxy⟩

private theorem tail_cell {u : ℝ} (hu : 2 ≤ u) :
    ∃ n : ℕ, ∃ x ∈ Icc (0:ℝ) 1, u = (n:ℝ)+2+x ∧ buchstab u = profile (n+1) x := by
  let n := ⌊u-2⌋₊
  let x := u-2-(n:ℝ)
  have hx : x ∈ Icc (0:ℝ) 1 := by
    dsimp [x,n]
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le (sub_nonneg.mpr hu))
    · linarith only [Nat.lt_floor_add_one (u-2)]
  have he : u = (n:ℝ)+2+x := by dsimp [x]; ring
  refine ⟨n,x,hx,he,?_⟩
  convert buchstab_cell (n+1) x hx using 2
  push_cast
  linarith only [he]

/-- Exact range on the real ray starting at two. -/
theorem buchstab_tail_range : buchstab '' Ici (2:ℝ) = Icc (1/2) omegaConstant := by
  rw [← profile_tail_range]
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨n,x,hx,_,he⟩ := tail_cell hu
    exact mem_iUnion.mpr ⟨n,x,hx,he.symm⟩
  · intro hz
    obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
    refine ⟨((n+1:ℕ):ℝ)+1+x,?_,buchstab_cell (n+1) x hx⟩
    change 2 ≤ _
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n,hx.1]

/-- The first peak is attained at exactly one real argument on the tail. -/
theorem buchstab_eq_peak_iff (u : Ici (2:ℝ)) :
    buchstab u = omegaConstant ↔ u.val = 1+1/omegaConstant := by
  obtain ⟨n,x,hx,he,hv⟩ := tail_cell u.property
  constructor
  · intro h
    rw [hv] at h
    cases n with
    | zero =>
      have hh := (profile_one_eq_peak_iff ⟨x,hx.1⟩).mp h
      dsimp [peakOffset] at hh
      push_cast at he
      linarith
    | succ n => exact False.elim ((later_profile_lt_peak n x hx).ne h)
  · intro h
    have hh := buchstab_cell 1 peakOffset ⟨peakOffset_mem.1.le,peakOffset_mem.2.le⟩
    rw [(profile_one_eq_peak_iff ⟨peakOffset,peakOffset_mem.1.le⟩).mpr rfl] at hh
    convert hh using 2
    rw [h,peakOffset]
    push_cast
    ring

private theorem log_branch_gt_half {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) : 1/2 < profile 1 x := by
  have ha : 0 < 1+x := by linarith [hx.1]
  have ha₁ : (1+x)⁻¹ ≠ 1 := by
    rw [ne_eq,inv_eq_one]
    linarith [hx.1]
  have hlog := Real.log_lt_sub_one_of_pos (inv_pos.mpr ha) ha₁
  rw [Real.log_inv] at hlog
  have hi : (1+x)⁻¹ ≤ 1-x/2 := by
    rw [← one_div,div_le_iff₀ ha]
    nlinarith only [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2)]
  rw [profile_one_formula ⟨x,hx.1.le⟩,lt_div_iff₀ (show 0 < 2+x by linarith)]
  linarith

private theorem later_gt_half (n : ℕ) (x : Icc (0:ℝ) 1) : 1/2 < profile (n+2) x := by
  have hnest (k : ℕ) : Icc (enclosure (k+2)).1 (enclosure (k+2)).2 ⊆
      Icc (enclosure 2).1 (enclosure 2).2 := by
    induction k with
    | zero => exact Subset.rfl
    | succ k ih => exact (enclosure_nested (k+2)).trans ih
  have hl := (hnest n (profile_mem_enclosure _ x x.property)).1
  have h₁ := log_branch_gt_half (x := 1) ⟨zero_lt_one,le_rfl⟩
  have hbase : (enclosure 1).1 = 1/2 := by
    change profile 0 1 + ((1/2:ℝ)-profile 0 1)/3 = 1/2
    norm_num [profile,intervalMass]
  change profile 1 1 + ((enclosure 1).1-profile 1 1)/((1:ℕ)+3:ℝ) ≤ profile (n+2) x at hl
  rw [hbase] at hl
  norm_num at hl
  linarith

/-- The tail minimum is attained only at the corner at two. -/
theorem buchstab_eq_half_iff (u : Ici (2:ℝ)) : buchstab u = 1/2 ↔ u.val = 2 := by
  obtain ⟨n,x,hx,he,hv⟩ := tail_cell u.property
  constructor
  · intro h
    rw [hv] at h
    cases n with
    | zero =>
      rcases eq_or_lt_of_le hx.1 with h₀ | hp
      · rw [← h₀] at he
        simpa using he
      · exact False.elim ((log_branch_gt_half ⟨hp,hx.2⟩).ne' h)
    | succ n => exact False.elim ((later_gt_half n ⟨x,hx⟩).ne' h)
  · intro h
    rw [h]
    have hh := buchstab_cell 0 1 ⟨zero_le_one,le_rfl⟩
    norm_num [profile,intervalMass] at hh
    exact hh

private theorem initial_value {u : ℝ} (hu : u ∈ Icc (1:ℝ) 2) : buchstab u = 1/u := by
  apply (eq_div_iff (zero_lt_one.trans_le hu.1).ne').mpr
  rw [mul_comm,buchstab_weighted ⟨u,hu.1⟩,integral_buchstab_initial
    (show u-1 ∈ Icc (0:ℝ) 1 from ⟨by linarith [hu.1],by linarith [hu.2]⟩),add_zero]

private theorem log_value {u : ℝ} (hu : u ∈ Icc (2:ℝ) 3) :
    buchstab u = (1+Real.log (u-1))/u := by
  have hx : u-2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have h := buchstab_cell 1 (u-2) hx
  rw [show ((1:ℕ):ℝ)+1+(u-2) = u by norm_num; ring,
    profile_one_formula ⟨u-2,hx.1⟩] at h
  simpa only [show 1+(u-2) = u-1 by ring,show 2+(u-2) = u by ring] using h

/-- At the first delay junction the one-sided slopes differ by exactly one half. -/
theorem buchstab_slopes_two :
    HasDerivWithinAt buchstab (-(1/4)) (Iic 2) 2 ∧ HasDerivWithinAt buchstab (1/4) (Ici 2) 2 := by
  have hl : HasDerivAt (fun u : ℝ => 1/u) (-(1/4)) 2 := by
    convert (hasDerivAt_const (2:ℝ) (1:ℝ)).div (hasDerivAt_id 2) (by norm_num) using 1 <;> norm_num
  have hshift : HasDerivAt (fun u : ℝ => u-1) 1 2 := (hasDerivAt_id (2:ℝ)).sub_const 1
  have hl' := hshift.log (by norm_num : (2:ℝ)-1 ≠ 0)
  have hr : HasDerivAt (fun u : ℝ => (1+Real.log (u-1))/u) (1/4) 2 := by
    convert (hl'.const_add 1).div (hasDerivAt_id _) (by norm_num) using 1 <;> norm_num
  constructor
  · apply hl.hasDerivWithinAt.congr_of_eventuallyEq _ (initial_value ⟨by norm_num,le_rfl⟩)
    filter_upwards [Ioc_mem_nhdsLE (show (1:ℝ)<2 by norm_num)] with t ht
    exact initial_value ⟨ht.1.le,ht.2⟩
  · apply hr.hasDerivWithinAt.congr_of_eventuallyEq _ (log_value ⟨le_rfl,by norm_num⟩)
    filter_upwards [Ico_mem_nhdsGE (show (2:ℝ)<3 by norm_num)] with t ht
    exact log_value ⟨ht.1,ht.2.le⟩

/-- The initial jump and the first delay corner are the complete real
singular set for first-order differentiability. -/
theorem buchstab_differentiableAt_iff (u : ℝ) :
    DifferentiableAt ℝ buchstab u ↔ u ≠ 1 ∧ u ≠ 2 := by
  constructor
  · intro h
    constructor
    · rintro rfl
      have hleft : Tendsto buchstab (𝓝[<] (1:ℝ)) (𝓝 0) := tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (if_neg (not_le.mpr hz)).symm)
      have he := tendsto_nhds_unique hleft (h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      rw [initial_value ⟨le_rfl,by norm_num⟩] at he
      norm_num at he
    · rintro rfl
      obtain ⟨hl,hr⟩ := buchstab_slopes_two
      have h₁ := (h.hasDerivAt.hasDerivWithinAt (s := Iic 2)).derivWithin (uniqueDiffWithinAt_Iic 2)
      have h₂ := (h.hasDerivAt.hasDerivWithinAt (s := Ici 2)).derivWithin (uniqueDiffWithinAt_Ici 2)
      rw [hl.derivWithin (uniqueDiffWithinAt_Iic 2)] at h₁
      rw [hr.derivWithin (uniqueDiffWithinAt_Ici 2)] at h₂
      linarith
  · rintro ⟨h₁,h₂⟩
    rcases lt_or_gt_of_ne h₁ with hlo | hhi
    · apply ((hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq ?_).differentiableAt
      filter_upwards [gt_mem_nhds hlo] with z hz
      exact if_neg (not_le.mpr hz)
    · rcases lt_or_gt_of_ne h₂ with hlo | hhi'
      · have hd := (hasDerivAt_const u (1:ℝ)).div (hasDerivAt_id u) (zero_lt_one.trans hhi).ne'
        apply (hd.congr_of_eventuallyEq ?_).differentiableAt
        filter_upwards [Ioo_mem_nhds hhi hlo] with z hz
        exact initial_value ⟨hz.1.le,hz.2.le⟩
      · exact (hasDerivAt_buchstab ⟨u,hhi'⟩).differentiableAt

#print axioms omegaConstant_mul_exp
#print axioms profile_one_eq_peak_iff
#print axioms later_profile_lt_peak
#print axioms profile_tail_range
#print axioms buchstab_tail_range
#print axioms buchstab_eq_peak_iff
#print axioms buchstab_eq_half_iff
#print axioms buchstab_slopes_two
#print axioms buchstab_differentiableAt_iff

end
end RHTower.Sieve.Buchstab
