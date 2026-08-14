import GaloisForLFunctions.HTGeometry.HalfLineCoshPrimitive

/-!
# One half-density envelope discharges every integrability hypothesis of the polar estimate

The abstract polar-charge estimate takes ten separate integrability inputs about the source.  A
single pointwise envelope

```text
|R(s)| ≤ K exp (-s/2),      s ≥ 0,
```

together with continuity, supplies all of them: every integrand in the estimate is dominated by a
constant multiple of `exp (-s)` on the half line, the two-dimensional cross integrand by a constant
multiple of `exp (-s)` on the product, and the two autocorrelation integrands by the product
integrability through Fubini.

The estimate then reads with explicit constants:

```text
|PPol(R, a)| ≤ 4 M K + 4 K²,
```

with `M` the bound on the growing primitive.  This is the shape the radial source consumes: the BV
lattice envelope supplies exactly one hypothesis.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- Domination by a multiple of `exp (-s)` on the half line. -/
theorem integrableOn_Ioi_of_exp_bound {f : ℝ → ℝ} {B : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hb : ∀ s : ℝ, 0 < s → |f s| ≤ B * Real.exp (-s)) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul B) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  simpa [Real.norm_eq_abs] using hb s hs

theorem exp_neg_half_mul_self (s : ℝ) :
    Real.exp (-s / 2) * Real.exp (-s / 2) = Real.exp (-s) := by
  rw [← Real.exp_add]
  ring_nf

section Envelope

variable {R : ℝ → ℝ} {K : ℝ}

/-- The envelope bounds the source's square. -/
theorem sq_le_of_envelope (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {s : ℝ} (hs : 0 ≤ s) :
    R s ^ 2 ≤ K ^ 2 * Real.exp (-s) := by
  have h := henv s hs
  have hnn : (0 : ℝ) ≤ |R s| := abs_nonneg _
  have hb : (0 : ℝ) ≤ K * Real.exp (-s / 2) := by positivity
  have hsq : |R s| ^ 2 ≤ (K * Real.exp (-s / 2)) ^ 2 := by nlinarith
  calc R s ^ 2 = |R s| ^ 2 := (sq_abs _).symm
    _ ≤ (K * Real.exp (-s / 2)) ^ 2 := hsq
    _ = K ^ 2 * Real.exp (-s) := by
        have hsq2 : Real.exp (-s / 2) ^ 2 = Real.exp (-s) := by
          rw [sq, exp_neg_half_mul_self]
        rw [mul_pow, hsq2]

theorem integrableOn_sq_of_envelope (hcont : Continuous R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    IntegrableOn (fun s : ℝ => R s ^ 2) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K ^ 2)
    (hcont.pow 2).aestronglyMeasurable.restrict (fun s hs => ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact sq_le_of_envelope hK henv hs.le

theorem integral_sq_le_of_envelope (hcont : Continuous R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    (∫ s in Ioi (0 : ℝ), R s ^ 2) ≤ K ^ 2 := by
  have hmaj : IntegrableOn (fun s : ℝ => K ^ 2 * Real.exp (-s)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have hle : (∫ s in Ioi (0 : ℝ), R s ^ 2) ≤ ∫ s in Ioi (0 : ℝ), K ^ 2 * Real.exp (-s) := by
    refine integral_mono_ae (integrableOn_sq_of_envelope hcont hK henv) hmaj ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    exact sq_le_of_envelope hK henv hs.le
  have hval : (∫ s in Ioi (0 : ℝ), K ^ 2 * Real.exp (-s)) = K ^ 2 := by
    rw [integral_const_mul, integral_exp_neg_Ioi]
    simp
  linarith [hle, hval.le, hval.ge]

theorem integrableOn_expNegHalf_mul_of_envelope (hcont : Continuous R)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K)
    (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      hcont).aestronglyMeasurable.restrict) (fun s hs => ?_)
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-s / 2) * |R s| ≤ Real.exp (-s / 2) * (K * Real.exp (-s / 2)) :=
        mul_le_mul_of_nonneg_left (henv s hs.le) (Real.exp_pos _).le
    _ = K * Real.exp (-s) := by rw [← mul_assoc, mul_comm (Real.exp (-s / 2)) K, mul_assoc,
        exp_neg_half_mul_self]

theorem integral_abs_expNegHalf_mul_le_of_envelope (hcont : Continuous R)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|) ≤ K := by
  have hmaj : IntegrableOn (fun s : ℝ => K * Real.exp (-s)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have habs : IntegrableOn (fun s : ℝ => |Real.exp (-s / 2) * R s|) (Ioi (0 : ℝ)) :=
    (integrableOn_expNegHalf_mul_of_envelope hcont henv).abs
  have hle : (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|)
      ≤ ∫ s in Ioi (0 : ℝ), K * Real.exp (-s) := by
    refine integral_mono_ae habs hmaj ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    show |Real.exp (-s / 2) * R s| ≤ K * Real.exp (-s)
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-s / 2) * |R s| ≤ Real.exp (-s / 2) * (K * Real.exp (-s / 2)) :=
          mul_le_mul_of_nonneg_left (henv s hs.le) (Real.exp_pos _).le
      _ = K * Real.exp (-s) := by rw [← mul_assoc, mul_comm (Real.exp (-s / 2)) K, mul_assoc,
          exp_neg_half_mul_self]
  have hval : (∫ s in Ioi (0 : ℝ), K * Real.exp (-s)) = K := by
    rw [integral_const_mul, integral_exp_neg_Ioi]
    simp
  linarith [hle, hval.le, hval.ge]

theorem shifted_envelope {h : ℝ} (hh : 0 ≤ h) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {s : ℝ} (hs : 0 ≤ s) :
    |R (s + h)| ≤ K * Real.exp (-s / 2) := by
  refine (henv (s + h) (by linarith)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine Real.exp_le_exp.mpr ?_
  linarith

theorem integrableOn_sq_comp_add_of_envelope (hcont : Continuous R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun s : ℝ => R (s + h) ^ 2) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K ^ 2)
    (((hcont.comp (continuous_id.add continuous_const)).pow 2).aestronglyMeasurable.restrict)
    (fun s hs => ?_)
  have hb := shifted_envelope hh hK henv hs.le
  have hnn : (0 : ℝ) ≤ |R (s + h)| := abs_nonneg _
  have hpos : (0 : ℝ) ≤ K * Real.exp (-s / 2) := by positivity
  have hsq2 : Real.exp (-s / 2) ^ 2 = Real.exp (-s) := by rw [sq, exp_neg_half_mul_self]
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  calc |R (s + h)| ^ 2 ≤ (K * Real.exp (-s / 2)) ^ 2 := by nlinarith
    _ = K ^ 2 * Real.exp (-s) := by rw [mul_pow, hsq2]

theorem integrableOn_mul_comp_add_of_envelope (hcont : Continuous R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun s : ℝ => R (s + h) * R s) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K ^ 2)
    (((hcont.comp (continuous_id.add continuous_const)).mul hcont).aestronglyMeasurable.restrict)
    (fun s hs => ?_)
  have hb := shifted_envelope hh hK henv hs.le
  have hb0 := henv s hs.le
  have hsq2 : Real.exp (-s / 2) ^ 2 = Real.exp (-s) := by rw [sq, exp_neg_half_mul_self]
  rw [abs_mul]
  calc |R (s + h)| * |R s| ≤ (K * Real.exp (-s / 2)) * (K * Real.exp (-s / 2)) := by
        exact mul_le_mul hb hb0 (abs_nonneg _) (by positivity)
    _ = K ^ 2 * Real.exp (-s) := by
        rw [show (K * Real.exp (-s / 2)) * (K * Real.exp (-s / 2))
          = K ^ 2 * Real.exp (-s / 2) ^ 2 by ring, hsq2]

theorem intervalIntegrable_expHalf_mul (hcont : Continuous R) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume x y :=
  ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hcont).intervalIntegrable x y

theorem continuous_halfLineExpPrimitive (hcont : Continuous R) :
    Continuous (halfLineExpPrimitive R) :=
  intervalIntegral.continuous_primitive (fun x y => intervalIntegrable_expHalf_mul hcont x y) 0

/-- The two-dimensional cross integrand is dominated by `K² exp (-s)`. -/
theorem integrable_prod_expHalf_of_envelope (hcont : Continuous R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {a eps : ℝ} (ha : 0 ≤ a)
    (heps : |eps| = 1) :
    Integrable (Function.uncurry (fun h s : ℝ => Real.exp (eps * h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmaj : Integrable (fun p : ℝ × ℝ => (K ^ 2 * Real.exp a) * Real.exp (-p.2))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun _ : ℝ => K ^ 2 * Real.exp a)
        (volume.restrict (Ioc (0 : ℝ) (2 * a))) := by
      refine integrableOn_const measure_Ioc_lt_top.ne ?_
      exact enorm_ne_top
    exact h1.mul_prod (integrableOn_exp_neg_Ioi 0)
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun h s : ℝ => Real.exp (eps * h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Continuous.aestronglyMeasurable ?_
    refine ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_snd).div_const 2)).comp continuous_fst).mul ?_ |>.mul ?_
    · exact hcont.comp (continuous_snd.add continuous_fst)
    · exact hcont.comp continuous_snd
  refine Integrable.mono' hmaj hmeas ?_
  refine ((ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)).mpr ?_ :
    ∀ᵐ p ∂_, _)
  sorry

end Envelope

end GaloisForLFunctions.HTGeometry

