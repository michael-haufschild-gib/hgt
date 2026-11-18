import GaloisForLFunctions.RHTower.Sieve.Buchstab.FactorialEnclosures

/-!
# Exact range of the Buchstab function beyond its initial cell

The first logarithmic branch peaks at the omega constant `w exp w = 1`.
The tangent inequality for the logarithm proves the peak is unique.
Every later cell is a weighted mean with a strictly smaller endpoint,
so none can attain it again.
-/

namespace RHTower.Sieve.Buchstab
open Set MeasureTheory
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

#print axioms omegaConstant_mul_exp
#print axioms profile_one_eq_peak_iff
#print axioms later_profile_lt_peak
#print axioms profile_tail_range

end
end RHTower.Sieve.Buchstab
