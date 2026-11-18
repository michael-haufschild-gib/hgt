import GaloisForLFunctions.RHTower.Sieve.Buchstab.FactorialEnclosures
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The global Buchstab function

Gluing the unit cells and extending by zero below one gives a bounded
measurable function on the real line. The weighted function is exactly
one plus the translated primitive above the cutoff, including at all
integer junctions.
-/

namespace RHTower.Sieve.Buchstab
open Set MeasureTheory Filter Topology
noncomputable section

/-- Buchstab's function with the sieve convention below its support. -/
def buchstab (u : ℝ) : ℝ :=
  if 1 ≤ u then profile ⌊u-1⌋₊ (u-1-(⌊u-1⌋₊:ℕ)) else 0

private theorem cell_interior (n : ℕ) (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    buchstab ((n:ℝ)+1+x) = profile n x := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hu : 1 ≤ (n:ℝ)+1+x := by linarith [hx.1]
  have hf : ⌊(n:ℝ)+1+x-1⌋₊ = n := (Nat.floor_eq_iff (by linarith)).mpr
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [buchstab, if_pos hu, hf, show (n:ℝ)+1+x-1-n = x by ring]

/-- Both adjacent coordinate systems give the same value at each shared endpoint. -/
theorem buchstab_cell (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    buchstab ((n:ℝ)+1+x) = profile n x := by
  rcases lt_or_eq_of_le hx.2 with h | rfl
  · exact cell_interior n x ⟨hx.1,h⟩
  · rw [← profile_glue n, ← cell_interior (n+1) 0 ⟨le_rfl,zero_lt_one⟩]
    congr 1
    push_cast
    ring

private theorem offset_mem {u : ℝ} (hu : 1 ≤ u) :
    u-1-(⌊u-1⌋₊:ℕ) ∈ Icc (0:ℝ) 1 := by
  exact ⟨sub_nonneg.mpr (Nat.floor_le (by linarith)), by linarith [Nat.lt_floor_add_one (u-1)]⟩

/-- Global real-axis bound and nonnegativity, including the jump at one. -/
theorem buchstab_mem_unit (u : ℝ) : buchstab u ∈ Icc (0:ℝ) 1 := by
  rw [buchstab]
  split_ifs with hu
  · have h (k : ℕ) : Icc (enclosure k).1 (enclosure k).2 ⊆ Icc (enclosure 0).1 (enclosure 0).2 := by
      induction k with
      | zero => exact Subset.rfl
      | succ k ih => exact (enclosure_nested k).trans ih
    have hb := h _ (profile_mem_enclosure _ _ (offset_mem hu))
    exact ⟨le_trans (by norm_num [enclosure]) hb.1,hb.2⟩
  · exact ⟨le_rfl,zero_le_one⟩

theorem measurable_buchstab : Measurable buchstab := by
  have hp : Measurable (fun p : ℕ × ℝ => profile p.1 p.2) :=
    measurable_from_prod_countable_left fun n => (profile_continuous n).measurable
  have hn : Measurable (fun u : ℝ => ⌊u-1⌋₊) := (measurable_id.sub measurable_const).nat_floor
  apply Measurable.ite (measurableSet_Ici (a := (1:ℝ))) _ measurable_const
  exact hp.comp (hn.prodMk ((measurable_id.sub measurable_const).sub hn.natCast))

theorem intervalIntegrable_buchstab (a b : ℝ) : IntervalIntegrable buchstab volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (integrableOn_const (C := (1:ℝ))).mono' measurable_buchstab.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (buchstab_mem_unit x).1] using (buchstab_mem_unit x).2

/-- No mass accumulates before the left endpoint of the support. -/
theorem integral_buchstab_initial {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (∫ t in (0:ℝ)..u, buchstab t) = 0 := by
  have he : (∫ t in (0:ℝ)..u, buchstab t) = ∫ _ in (0:ℝ)..u, (0:ℝ) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hu.1] at ht
    exact if_neg (not_le.mpr (ht.2.trans_le hu.2))
  simpa using he

private theorem mass_primitive (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    intervalMass n x = 1 + ∫ t in (0:ℝ)..((n:ℝ)+x), buchstab t := by
  induction n generalizing x with
  | zero => simp [intervalMass,integral_buchstab_initial hx]
  | succ n ih =>
    have he : (∫ t in (0:ℝ)..x, profile n t) =
        ∫ t in ((n:ℝ)+1)..((n:ℝ)+1+x), buchstab t := by
      have h := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := x) buchstab ((n:ℝ)+1)
      rw [add_zero] at h
      rw [← h]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx.1] at ht
      exact (buchstab_cell n t ⟨ht.1,ht.2.trans hx.2⟩).symm
    change intervalMass n 1 + (∫ t in (0:ℝ)..x, profile n t) = _
    rw [ih _ ⟨zero_le_one,le_rfl⟩,he,Nat.cast_succ,add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_buchstab _ _)
        (intervalIntegrable_buchstab _ _)]

/-- Exact integrated delay equation for every argument on the support. -/
theorem buchstab_weighted (u : Ici (1:ℝ)) :
    u.val * buchstab u.val = 1 + ∫ t in (0:ℝ)..(u.val-1), buchstab t := by
  let n := ⌊u.val-1⌋₊
  let x := u.val-1-(n:ℝ)
  have hx : x ∈ Icc (0:ℝ) 1 := offset_mem u.property
  have hu : (n:ℝ)+1+x = u.val := by dsimp [x]; ring
  have hc : buchstab u.val = profile n x := by simpa only [hu] using buchstab_cell n x hx
  calc
    _ = intervalMass n x := by
      rw [hc, profile, max_eq_left hx.1, hu]
      field_simp [show u.val ≠ 0 by linarith [u.property]]
    _ = _ := by rw [mass_primitive n x hx, show (n:ℝ)+x = u.val-1 by dsimp [x]; ring]

/-- Away from the initial jump, Buchstab's function is continuous even at integer junctions. -/
theorem continuousOn_buchstab : ContinuousOn buchstab (Ici (1:ℝ)) := by
  let P := fun x : ℝ => ∫ t in (0:ℝ)..x, buchstab t
  have hp : Continuous P := intervalIntegral.continuous_primitive intervalIntegrable_buchstab 0
  have hc : ContinuousOn (fun u : ℝ => (1+P (u-1))/u) (Ici 1) :=
    (continuous_const.add (hp.comp (continuous_id.sub continuous_const))).continuousOn.div
      continuousOn_id (fun u hu => ne_of_gt (zero_lt_one.trans_le hu))
  apply hc.congr
  intro u hu
  apply (eq_div_iff (ne_of_gt (zero_lt_one.trans_le hu))).mpr
  simpa only [mul_comm] using buchstab_weighted ⟨u,hu⟩

/-- The cell enclosures give a uniform error bound in the actual real argument. -/
theorem buchstab_factorial_error (u : Ici (1:ℝ)) :
    |buchstab u.val - enclosureLimit| ≤ 1 / ((⌊u.val-1⌋₊+2).factorial : ℝ) := by
  rw [buchstab,if_pos u.property]
  exact profile_limit_error _ ⟨_,offset_mem u.property⟩

/-- The real-variable limit exists along every approach to positive infinity. -/
theorem tendsto_buchstab_atTop : Tendsto buchstab atTop (𝓝 enclosureLimit) := by
  have hn : Tendsto (fun u : ℝ => ⌊u-1⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_sub_const 1)
  have hf : Tendsto (fun u : ℝ => (((⌊u-1⌋₊+2).factorial : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (factorial_tendsto_atTop.comp ((tendsto_add_atTop_nat 2).comp hn))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (tendsto_inv_atTop_zero.comp hf)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
  simpa only [Function.comp_apply, Real.norm_eq_abs, one_div] using buchstab_factorial_error ⟨u,hu⟩

#print axioms buchstab_weighted
#print axioms continuousOn_buchstab
#print axioms buchstab_factorial_error
#print axioms tendsto_buchstab_atTop

end
end RHTower.Sieve.Buchstab
