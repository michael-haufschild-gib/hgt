import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.DigitContinuation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedShift.PoleCalculus

/-!
# The center selected by quantum composition

Translation transfers the simple poles of the balanced partition to the
next vertical line with an affine residue. Exactly the midpoint shift of
the digit displacements annuls this transfer at every harmonic.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open BalancedContinuation

abbrev Shift := {a : ℝ // -1 < a}
abbrev Strip := {z : ℂ // -(3/2) < z.re}
abbrev lower (t : ExceptionalTime) (j : ℕ) (k : ℤ) := point t j k-1

private theorem translated_mem (s : Strip) : -(1/2) < (s.val+1).re := by
  rw [Complex.add_re,Complex.one_re]
  linarith only [s.property]

private theorem moved_num (t : ExceptionalTime) (j : ℕ) (s : Strip) :
    AnalyticAt ℂ (fun z => numerator t j (z+1)) s.val :=
  (numerator_analytic t j ⟨_,translated_mem s⟩).comp (f := fun z : ℂ => z+1)
    (analyticAt_id.add analyticAt_const)

private theorem moved_scale (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => denominator t j (z+1)) s :=
  (scaleFactor_analytic _ _).comp (analyticAt_id.add analyticAt_const)

private theorem analytic_difference (t : ExceptionalTime) (j : ℕ) (s : Strip) :
    AnalyticAt ℂ (fun z => quadraticNumerator t j z-z*(center t j:ℂ)*numerator t j (z+1)) s.val :=
  (quadratic_analytic t j s).sub ((analyticAt_id.mul analyticAt_const).mul (moved_num t j s))

private theorem background_analytic (t : ExceptionalTime) (j : ℕ) (a : Shift) (s : Strip)
    (hs : denominator t j s.val ≠ 0) : AnalyticAt ℂ (background t j a.val) s.val :=
  (correction_analytic t j zero_lt_one (by linarith only [a.property]) s).add
    ((analytic_difference t j s).div (scaleFactor_analytic _ _) hs)

theorem extension_meromorphic (t : ExceptionalTime) (j : ℕ) (a : Shift) (s : Strip) :
    MeromorphicAt (extension t j a.val) s.val := by
  have hb := (correction_analytic t j (b := 1) (a := a.val) zero_lt_one
    (by linarith only [a.property]) s).meromorphicAt
  have hq := (analytic_difference t j s).meromorphicAt.div (scaleFactor_analytic (logRadix t j).val s.val).meromorphicAt
  have hp := (moved_num t j s).meromorphicAt.div (moved_scale t j s.val).meromorphicAt
  have hm : AnalyticAt ℂ (fun z : ℂ => z*((center t j:ℂ)-(a.val:ℂ))) s.val :=
    analyticAt_id.mul analyticAt_const
  exact (hb.add hq).add (hm.meromorphicAt.mul hp)

private theorem lower_re (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    (lower t j k).re = -(1/2) := by
  change (1/2:ℝ)-1 = -(1/2)
  ring

private theorem lower_mem (t : ExceptionalTime) (j : ℕ) (k : ℤ) : -(3/2) < (lower t j k).re := by
  rw [lower_re]
  norm_num

private theorem primary_ne_zero (t : ExceptionalTime) (j : ℕ) (s : ℂ) (hs : s.re ≠ 1/2) :
    denominator t j s ≠ 0 := by
  intro hz
  obtain ⟨k,hk⟩ := (scaleFactor_zero_iff (logRadix t j) s).mp hz
  exact hs (congrArg Complex.re hk)

private theorem lower_scale_ne (t : ExceptionalTime) (j : ℕ) (k : ℤ) :
    denominator t j (lower t j k) ≠ 0 :=
  primary_ne_zero t j _ (by rw [lower_re]; norm_num)

private theorem lower_data (t : ExceptionalTime) (j : ℕ) (a : Shift) (k : ℤ) :
    let u := lower t j k
    let f := extension t j a.val
    let m := u*((center t j:ℂ)-(a.val:ℂ))*numerator t j (point t j k)
    HTGeometry.laurentCoeff f u (-1) = m/(2*((logRadix t j).val:ℂ)) ∧
      (meromorphicOrderAt f u < 0 ↔ m ≠ 0) ∧ (meromorphicOrderAt f u = (-1:ℤ) ↔ m ≠ 0) := by
  let u := lower t j k
  let E := fun z => denominator t j (z+1)
  let N := fun z : ℂ => z*((center t j:ℂ)-(a.val:ℂ))*numerator t j (z+1)
  have hu : u+1 = point t j k := sub_add_cancel _ _
  have hzero : E u = 0 := by
    change denominator t j (u+1) = 0
    rw [hu]
    exact (scaleFactor_zero_iff _ _).mpr ⟨k,rfl⟩
  have he : HasDerivAt (denominator t j) (2*((logRadix t j).val:ℂ)) (u+1) := by
    rw [hu]
    exact scaleFactor_derivative _ _
  have hd : HasDerivAt E (2*((logRadix t j).val:ℂ)) u := by
    simpa only [E,Function.comp_def,id_eq,mul_one] using he.comp u ((hasDerivAt_id u).add_const 1)
  have hN : AnalyticAt ℂ N u :=
    (analyticAt_id.mul analyticAt_const).mul (moved_num t j ⟨u,lower_mem t j k⟩)
  have h := simple_scale (background_analytic t j a ⟨u,lower_mem t j k⟩ (lower_scale_ne t j k))
    hN (moved_scale t j u) hzero (by
      change deriv E u ≠ 0
      rw [hd.deriv]
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne'))
  have hf : (fun z => background t j a.val z + N z/E z) = extension t j a.val := by
    funext z
    exact congrArg (background t j a.val z+·) (mul_div_assoc _ _ _)
  dsimp only at h
  rw [hf,show deriv (fun z => denominator t j (z+1)) u = _ from hd.deriv] at h
  simpa only [N,hu] using h

/-- Residue on the translated clock line in terms of the measured leading residue. -/
theorem shifted_residue (t : ExceptionalTime) (j : ℕ) (a : Shift) (k : ℤ) :
    HTGeometry.laurentCoeff (extension t j a.val) (lower t j k) (-1) =
      lower t j k*((center t j:ℂ)-(a.val:ℂ))*
        HTGeometry.laurentCoeff (continuation t j) (point t j k) (-1) := by
  rw [(lower_data t j a k).1,clock_residue]
  ring

private theorem coefficient_nonzero (t : ExceptionalTime) (j : ℕ) (a : Shift) (k : ℤ) :
    lower t j k*((center t j:ℂ)-(a.val:ℂ))*numerator t j (point t j k) ≠ 0 ↔
      a.val ≠ center t j ∧ meromorphicOrderAt (continuation t j) (point t j k) = (-1:ℤ) := by
  have hu : lower t j k ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    rw [lower_re,Complex.zero_re] at h
    norm_num at h
  have hc : (center t j:ℂ)-(a.val:ℂ) ≠ 0 ↔ a.val ≠ center t j := by
    rw [sub_ne_zero]
    exact not_congr (Complex.ofReal_inj.trans eq_comm)
  rw [mul_ne_zero_iff,mul_ne_zero_iff,hc,clock_pole_iff,and_iff_right hu]

/-- Each translated pole is simple; it survives exactly when the shift misses the center
and the corresponding isometric harmonic is a pole. -/
theorem shifted_pole_iff (t : ExceptionalTime) (j : ℕ) (a : Shift) (k : ℤ) :
    (meromorphicOrderAt (extension t j a.val) (lower t j k) < 0 ↔
      meromorphicOrderAt (extension t j a.val) (lower t j k) = (-1:ℤ)) ∧
    (meromorphicOrderAt (extension t j a.val) (lower t j k) = (-1:ℤ) ↔
      a.val ≠ center t j ∧ meromorphicOrderAt (continuation t j) (point t j k) = (-1:ℤ)) := by
  obtain ⟨_,hn,hs⟩ := lower_data t j a k
  exact ⟨hn.trans hs.symm,hs.trans (coefficient_nonzero t j a k)⟩

private theorem scale_off (t : ExceptionalTime) (j : ℕ) (s : ℂ) (h : ∀ k : ℤ, s ≠ point t j k) :
    denominator t j s ≠ 0 := by
  intro hz
  obtain ⟨k,hk⟩ := (scaleFactor_zero_iff (logRadix t j) s).mp hz
  exact h k hk

theorem analytic_off_clocks (t : ExceptionalTime) (j : ℕ) (a : Shift)
    (s : {z : ℂ // -(3/2) < z.re ∧ ∀ k : ℤ, z ≠ point t j k ∧ z ≠ lower t j k}) :
    AnalyticAt ℂ (extension t j a.val) s.val := by
  have hs := background_analytic t j a ⟨s.val,s.property.1⟩ (scale_off t j _ fun k => (s.property.2 k).1)
  have he := scale_off t j (s.val+1) fun k h => (s.property.2 k).2 ((eq_sub_iff_add_eq).mpr h)
  exact hs.add ((analyticAt_id.mul analyticAt_const).mul
    ((moved_num t j ⟨s.val,s.property.1⟩).div (moved_scale t j _) he))

/-- The centered representative is holomorphic throughout the enlarged half-plane away
from the original clock lattice, including all translated clock points. -/
theorem centered_analytic (t : ExceptionalTime) (j : ℕ)
    (s : {z : ℂ // -(3/2) < z.re ∧ ∀ k : ℤ, z ≠ point t j k}) :
    AnalyticAt ℂ (extension t j (center t j)) s.val := by
  have he : extension t j (center t j) = background t j (center t j) := by
    funext z
    simp only [extension,sub_self,mul_zero,zero_mul,add_zero]
  rw [he]
  exact background_analytic t j ⟨center t j,by linarith only [center_pos t j]⟩
    ⟨s.val,s.property.1⟩ (scale_off t j s.val s.property.2)

private theorem lower_real_pole (t : ExceptionalTime) (j : ℕ) (a : Shift) :
    meromorphicOrderAt (extension t j a.val) (lower t j 0) < 0 ↔ a.val ≠ center t j := by
  rw [(shifted_pole_iff t j a 0).1,(shifted_pole_iff t j a 0).2,
    and_iff_left (first_clock_poles t j ⟨0,Or.inl rfl⟩)]

theorem real_regular_iff_center (t : ExceptionalTime) (j : ℕ) (a : Shift) :
    AnalyticAt ℂ (extension t j a.val) (lower t j 0) ↔ a.val = center t j := by
  constructor
  · intro h
    by_contra hn
    exact ((lower_real_pole t j a).mpr hn).not_ge h.meromorphicOrderAt_nonneg
  · intro he
    rw [he]
    apply centered_analytic t j ⟨_,lower_mem t j 0,?_⟩
    intro k hk
    have h := congrArg Complex.re hk
    rw [lower_re] at h
    change -(1/2:ℝ) = 1/2 at h
    norm_num at h

/-- Probability conservation at every pole of the enlarged continuation uniquely determines
the energy-label shift. An uncentered real pole already violates conservation. -/
theorem all_poles_isometric_iff_center (t : ExceptionalTime) (j : ℕ) (a : Shift) :
    (∀ s : {z : ℂ // -(3/2) < z.re ∧ meromorphicOrderAt (extension t j a.val) z < 0},
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x) ↔ a.val = center t j := by
  constructor
  · intro hall
    by_contra hn
    have hs := (split_isometric_iff _).mp (hall ⟨lower t j 0,lower_mem t j 0,(lower_real_pole t j a).mpr hn⟩)
    rw [lower_re] at hs
    norm_num at hs
  · rintro he ⟨z,hz,hp⟩
    apply (split_isometric_iff _).mpr
    by_contra hs
    have h : ∀ k : ℤ, z ≠ point t j k := fun k hk => hs (congrArg Complex.re hk)
    rw [he] at hp
    exact hp.not_ge (centered_analytic t j ⟨z,hz,h⟩).meromorphicOrderAt_nonneg

/-- Signed child displacement in the affine coordinates X+a. -/
def displacement (t : ExceptionalTime) (j : ℕ) (a : ℝ) (d : Fin (radix t j)) :=
  (d.val:ℝ)-(base t j-1)*a

theorem symmetric_digits_iff_center (t : ExceptionalTime) (j : ℕ) (a : ℝ) :
    (∀ d : Fin (radix t j), displacement t j a d+displacement t j a d.rev = 0) ↔ a = center t j := by
  let C := radix t j
  have hC : (1:ℝ) < C := by exact_mod_cast radix_gt_one t j
  have hB : base t j-1 ≠ 0 := by rw [base_sq]; nlinarith only [hC, sq_pos_of_pos (sub_pos.mpr hC)]
  have hc : 2*(base t j-1)*center t j = (C:ℝ)-1 := by
    rw [base_sq,center]
    change 2*((C:ℝ)^2-1)*(1/(2*(C+1))) = (C:ℝ)-1
    field_simp [show (C:ℝ)+1 ≠ 0 by positivity]
    ring
  have hd (d : Fin C) : displacement t j a d+displacement t j a d.rev = (C:ℝ)-1-2*(base t j-1)*a := by
    have h : d.val+d.rev.val+1=C := by rw [Fin.val_rev]; omega
    have hr : (d.val:ℝ)+(d.rev.val:ℝ)+1=C := by exact_mod_cast h
    unfold displacement
    linarith only [hr]
  constructor
  · intro hall
    have h := hall ⟨0,Nat.zero_lt_one.trans (radix_gt_one t j)⟩
    rw [hd,← hc] at h
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hB)
    linarith only [h]
  · rintro rfl d
    rw [hd, hc, sub_self]

#print axioms extension_meromorphic
#print axioms shifted_residue
#print axioms shifted_pole_iff
#print axioms analytic_off_clocks
#print axioms centered_analytic
#print axioms real_regular_iff_center
#print axioms all_poles_isometric_iff_center
#print axioms symmetric_digits_iff_center

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
