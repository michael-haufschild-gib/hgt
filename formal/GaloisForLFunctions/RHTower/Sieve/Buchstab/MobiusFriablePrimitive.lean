import GaloisForLFunctions.RHTower.MobiusFriableIntegerSeamProfile
import GaloisForLFunctions.RHTower.Sieve.Buchstab.UnitOscillation

/-!
# The global Möbius friable delay solution

The logarithmic branch for the Möbius parameter extends uniquely by
the positive delay equation. Its derivative is Buchstab's function,
and the solution itself is the shifted weighted Buchstab function.
-/

namespace RHTower.Sieve.Buchstab
open Set Filter MeasureTheory Topology
noncomputable section

/-- The global continuation of the constant initial branch. -/
def friablePrimitive (u : ℝ) := 1 + ∫ t in (0:ℝ)..u, buchstab t

theorem continuous_friablePrimitive : Continuous friablePrimitive :=
  continuous_const.add (intervalIntegral.continuous_primitive intervalIntegrable_buchstab 0)

theorem friablePrimitive_initial (u : Icc (0:ℝ) 1) : friablePrimitive u = 1 := by
  rw [friablePrimitive,integral_buchstab_initial u.property,add_zero]

/-- The shifted weighted identity identifies the two global delay problems. -/
theorem friablePrimitive_shift (u : Ici (0:ℝ)) :
    friablePrimitive u = (u.val+1)*buchstab (u.val+1) := by
  have hu := u.property
  simpa only [friablePrimitive,add_sub_cancel_right] using
    (buchstab_weighted ⟨u.val+1,show 1 ≤ u.val+1 by linarith [show 0 ≤ u.val from hu]⟩).symm

theorem friablePrimitive_hasDerivAt (u : Ioi (1:ℝ)) :
    HasDerivAt friablePrimitive (buchstab u) u.val := by
  exact (intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_buchstab 0 u.val)
    measurable_buchstab.stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousOn_buchstab.continuousAt (Ici_mem_nhds u.property))).const_add 1

/-- For positive arguments past the initial interval, u F'(u) = F(u-1). -/
theorem friablePrimitive_delay (u : Ioi (1:ℝ)) :
    HasDerivAt friablePrimitive (friablePrimitive (u.val-1)/u.val) u.val := by
  have he := friablePrimitive_shift ⟨u.val-1,sub_nonneg.mpr u.property.le⟩
  simp only [sub_add_cancel] at he
  rw [he,mul_div_cancel_left₀ _ (zero_lt_one.trans u.property).ne']
  exact friablePrimitive_hasDerivAt u

/-- The same primitive extends both the logarithmic solution and the
post-junction derivative already defined for the Möbius friable profile. -/
theorem friablePrimitive_seam :
    EqOn friablePrimitive mobiusFriableDelayBelowTwo (Icc 1 2) ∧
    EqOn (deriv friablePrimitive) mobiusFriableDelayDerivativeAboveTwo (Icc 2 3) := by
  have hb (u : Icc (2:ℝ) 3) : buchstab u = (1+Real.log (u.val-1))/u.val := by
    have hx : u.val-2 ∈ Icc (0:ℝ) 1 := ⟨by linarith [u.property.1],by linarith [u.property.2]⟩
    have h := buchstab_cell 1 (u.val-2) hx
    rw [show ((1:ℕ):ℝ)+1+(u.val-2) = u.val by push_cast; ring,profile_one_formula ⟨u.val-2,hx.1⟩] at h
    simpa only [show 1+(u.val-2) = u.val-1 by ring,show 2+(u.val-2) = u.val by ring] using h
  constructor
  · intro x hx
    have h := friablePrimitive_shift ⟨x,zero_le_one.trans hx.1⟩
    rw [h,hb ⟨x+1,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩]
    simp only [add_sub_cancel_right,mobiusFriableDelayBelowTwo]
    field_simp [show x+1 ≠ 0 by linarith [hx.1]]
  · intro x hx
    exact (friablePrimitive_hasDerivAt ⟨x,show (1:ℝ)<x by linarith [hx.1]⟩).deriv.trans (hb ⟨x,hx⟩)

/-- The initial condition and the delay equation determine the solution
on the entire ray. Two solutions with equal past differ by a constant
on the next interval, fixed by their common left endpoint. -/
theorem friablePrimitive_unique (g : ℝ → ℝ) :
    (ContinuousOn g (Ici 0) ∧ EqOn g (fun _ => 1) (Icc 0 1) ∧
      ∀ x : Ioi (1:ℝ), HasDerivAt g (g (x.val-1)/x.val) x.val) →
    EqOn g friablePrimitive (Ici 0) := by
  rintro ⟨hc,hi,hd⟩
  let f := fun x => g x - friablePrimitive x
  have step (n : ℕ) : ∀ x ∈ Icc (n:ℝ) ((n:ℝ)+1), f x = 0 := by
    induction n with
    | zero =>
      intro x hx
      simp only [Nat.cast_zero,zero_add] at hx
      exact sub_eq_zero.mpr ((hi hx).trans (friablePrimitive_initial ⟨x,hx⟩).symm)
    | succ n ih =>
      intro x hx
      simp only [Nat.cast_succ] at hx
      let a := (n:ℝ)+1
      have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α:=ℝ) n]
      have ha₀ := ih a ⟨by dsimp [a]; linarith,le_rfl⟩
      rcases hx.1.eq_or_lt with he|hax
      · exact he ▸ ha₀
      have hf : ContinuousOn f (Icc a x) :=
        (hc.sub continuous_friablePrimitive.continuousOn).mono fun y hy =>
          zero_le_one.trans (ha.trans hy.1)
      have hh (y : ℝ) (hy : y ∈ Ioo a x) : HasDerivAt f 0 y := by
        have hz : 1 < y := ha.trans_lt hy.1
        have he := sub_eq_zero.mp (ih (y-1) ⟨by dsimp [a] at hy; linarith [hy.1],by linarith [hy.2,hx.2]⟩)
        simpa only [f,he,sub_self] using (hd ⟨y,hz⟩).sub (friablePrimitive_delay ⟨y,hz⟩)
      obtain ⟨y,hy,he⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0:ℝ)) hax hf hh
      have hh' := (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr hax.ne')
      exact (sub_eq_zero.mp hh').trans ha₀
  intro x hx
  apply sub_eq_zero.mp
  exact step ⌊x⌋₊ x ⟨Nat.floor_le hx,(Nat.lt_floor_add_one x).le⟩

/-- The affine asymptote has an exact signed tail remainder. -/
theorem friablePrimitive_affine_remainder (u : Ici (0:ℝ)) :
    friablePrimitive u-(u.val+1)*enclosureLimit = -(∫ t in Ioi u.val, buchstab t-enclosureLimit) := by
  rw [friablePrimitive_shift,← mul_sub]
  simpa only [add_sub_cancel_right] using buchstab_weighted_error_tail
    ⟨u.val+1,show 1 ≤ u.val+1 by linarith [show 0 ≤ u.val from u.property]⟩

/-- The graph intersects its limiting affine line in every open sliding
unit interval starting at a nonnegative real argument. -/
theorem friablePrimitive_crosses_asymptote (u : Ici (0:ℝ)) :
    ∃ t ∈ Ioo u.val (u.val+1), friablePrimitive t = (t+1)*Real.exp (-Real.eulerMascheroniConstant) := by
  obtain ⟨x,hx,he⟩ := buchstab_attains_limit_each_unit
    ⟨u.val+1,show 1 ≤ u.val+1 by linarith [show 0 ≤ u.val from u.property]⟩
  have hlo : u.val+1<x := hx.1
  have hhi : x<(u.val+1)+1 := hx.2
  refine ⟨x-1,⟨by linarith,by linarith⟩,?_⟩
  rw [friablePrimitive_shift ⟨x-1,show 0 ≤ x-1 by linarith [show 0 ≤ u.val from u.property]⟩,
    sub_add_cancel,he,enclosureLimit_eq_exp_neg_euler]

#print axioms friablePrimitive_shift
#print axioms friablePrimitive_delay
#print axioms friablePrimitive_seam
#print axioms friablePrimitive_unique
#print axioms friablePrimitive_affine_remainder
#print axioms friablePrimitive_crosses_asymptote
end
end RHTower.Sieve.Buchstab
