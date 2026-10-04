import GaloisForLFunctions.RHTower.XiOrdinateCosineMass
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineSource
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy

/-!
# The RH mean law of the literal reciprocal sine response

Under RH every reciprocal frequency is the inverse ordinate, `(xiSpectralPoint q)⁻¹ = 1/γ_q`, so
the literal response is the real multiplicity-exact sine trace

```text
F(t) = Σ_q sin(t/γ_q)/γ_q = 2 Σ_{γ_q > 0} sin(t/γ_q)/γ_q .
```

Dominated termwise integration (`|sin(t/γ)/γ| ≤ |t|/γ²`) gives `∫_0^T F = Σ_q (1 - cos(T/γ_q))`,
the ordinate cosine mass, whose unconditional asymptotic yields the mean law

```text
(1/T) ∫_0^T F(t) dt = (1/2) log T + O(1)          (T ≥ 2π).
```
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Under RH the spectral point of a copy is its ordinate. -/
theorem xiSpectralPoint_eq_ordinate_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiSpectralPoint q = (xiCopyOrdinate q : ℂ) := by
  have hre := xi_divisor_support_re_eq_half_of_rh hRH q.1
  apply Complex.ext
  · simp [xiSpectralPoint, xiCopyOrdinate]
  · simp [xiSpectralPoint, xiCopyOrdinate, hre]

/-- Under RH each sine atom is the real atom `sin(t/γ)/γ`. -/
theorem liEvenCrossActualClockSineAtom_eq_of_rh (hRH : RiemannHypothesis) (t : ℝ)
    (q : XiZeroCopy) :
    liEvenCrossActualClockSineAtom t q =
      ((Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q : ℝ) : ℂ) := by
  unfold liEvenCrossActualClockSineAtom
  rw [xiSpectralPoint_eq_ordinate_of_rh hRH q]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem abs_sin_div_ordinate_le (t : ℝ) (q : XiZeroCopy) :
    |Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q| ≤ |t| * (1 / xiCopyOrdinate q ^ 2) := by
  have hγ := xiCopyOrdinate_ne_zero q
  rw [abs_div]
  have h := Real.abs_sin_le_abs (x := t / xiCopyOrdinate q)
  rw [abs_div] at h
  calc |Real.sin (t / xiCopyOrdinate q)| / |xiCopyOrdinate q| ≤
        |t| / |xiCopyOrdinate q| / |xiCopyOrdinate q| :=
        div_le_div_of_nonneg_right h (abs_nonneg _)
    _ = |t| * (1 / xiCopyOrdinate q ^ 2) := by
        rw [← sq_abs (xiCopyOrdinate q)]
        field_simp

theorem summable_sin_div_ordinate (t : ℝ) :
    Summable (fun q : XiZeroCopy => Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q) :=
  Summable.of_norm_bounded (summable_inv_sq_xiCopyOrdinate.mul_left |t|)
    fun q => by rw [Real.norm_eq_abs]; exact abs_sin_div_ordinate_le t q

/-- **Exact multiplicity response under RH.**  `F(t) = Σ_q sin(t/γ_q)/γ_q`. -/
theorem liEvenCrossActualClockResponse_eq_tsum_ordinate_of_rh (hRH : RiemannHypothesis)
    (t : ℝ) :
    liEvenCrossActualClockResponse t =
      ∑' q : XiZeroCopy, Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q := by
  rw [liEvenCrossActualClockResponse_eq_re_tsum_sine]
  simp_rw [liEvenCrossActualClockSineAtom_eq_of_rh hRH t]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

theorem xiZeroCopyConjEquiv_ordinate (q : XiZeroCopy) :
    xiCopyOrdinate (xiZeroCopyConjEquiv q) = -xiCopyOrdinate q := by
  have h : (((xiZeroCopyConjEquiv q).1 : XiDivisorSupport) : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := by
    simp [xiZeroCopyConjEquiv, xiZeroConjEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrRight,
      Equiv.sigmaCongrLeft]
  unfold xiCopyOrdinate
  rw [h, Complex.conj_im]

/-- **Positive-ordinate form under RH.**  `F(t) = 2 Σ_{γ_q > 0} sin(t/γ_q)/γ_q`, every
analytic multiplicity copy counted once. -/
theorem liEvenCrossActualClockResponse_eq_two_mul_tsum_pos_of_rh (hRH : RiemannHypothesis)
    (t : ℝ) :
    liEvenCrossActualClockResponse t =
      2 * ∑' q : {q : XiZeroCopy // 0 < xiCopyOrdinate q},
        Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q := by
  classical
  set f : XiZeroCopy → ℝ := fun q => Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q
  have hf : Summable f := summable_sin_div_ordinate t
  have hsplit := Summable.tsum_add_tsum_compl (s := {q : XiZeroCopy | 0 < xiCopyOrdinate q})
    (hf.subtype _) (hf.subtype _)
  have hconj : ∀ q, f (xiZeroCopyConjEquiv q) = f q := by
    intro q
    simp only [f, xiZeroCopyConjEquiv_ordinate, div_neg, Real.sin_neg]
    ring
  have hmem : ∀ q, q ∈ {q : XiZeroCopy | 0 < xiCopyOrdinate q} ↔
      xiZeroCopyConjEquiv q ∈ ({q : XiZeroCopy | 0 < xiCopyOrdinate q})ᶜ := by
    intro q
    simp only [mem_setOf_eq, mem_compl_iff, xiZeroCopyConjEquiv_ordinate, not_lt,
      neg_nonpos]
    constructor
    · exact le_of_lt
    · intro h
      exact lt_of_le_of_ne h (Ne.symm (xiCopyOrdinate_ne_zero q))
  have hcompl : (∑' q : ↥({q : XiZeroCopy | 0 < xiCopyOrdinate q})ᶜ, f q) =
      ∑' q : ↥{q : XiZeroCopy | 0 < xiCopyOrdinate q}, f q := by
    rw [← (xiZeroCopyConjEquiv.subtypeEquiv hmem).tsum_eq]
    apply tsum_congr
    intro q
    exact hconj q
  rw [liEvenCrossActualClockResponse_eq_tsum_ordinate_of_rh hRH, ← hsplit, hcompl, two_mul]
  rfl

/-- Under RH the clock integral of the literal response is the ordinate cosine mass. -/
theorem integral_liEvenCrossActualClockResponse_of_rh (hRH : RiemannHypothesis) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, liEvenCrossActualClockResponse t = xiOrdinateCosineMass T := by
  have hF : ∀ t, liEvenCrossActualClockResponse t =
      ∑' q : XiZeroCopy, Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q :=
    liEvenCrossActualClockResponse_eq_tsum_ordinate_of_rh hRH
  have hterm : ∀ q : XiZeroCopy, ∫ t in (0 : ℝ)..T,
      Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q = 1 - Real.cos (T / xiCopyOrdinate q) := by
    intro q
    have hγ := xiCopyOrdinate_ne_zero q
    have hd : ∀ t, HasDerivAt (fun t => -Real.cos (t / xiCopyOrdinate q))
        (Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => t / xiCopyOrdinate q) (1 / xiCopyOrdinate q) t :=
        (hasDerivAt_id' t).div_const _
      have h := h1.cos.neg
      have e : -(-Real.sin (t / xiCopyOrdinate q) * (1 / xiCopyOrdinate q)) =
          Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q := by ring
      rw [e] at h
      exact h
    have hc : Continuous fun t => Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q := by
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hc.intervalIntegrable _ _)]
    simp
    ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun (q : XiZeroCopy) (t : ℝ) => Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q)
    (f := liEvenCrossActualClockResponse) (μ := volume) (a := 0) (b := T)
    (fun q t => |T| * (1 / xiCopyOrdinate q ^ 2))
    (fun q => (by fun_prop : Continuous fun t : ℝ =>
      Real.sin (t / xiCopyOrdinate q) / xiCopyOrdinate q).aestronglyMeasurable)
    (fun q => Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs]
      refine (abs_sin_div_ordinate_le t q).trans ?_
      have htT : |t| ≤ |T| := by
        rcases le_total 0 T with h | h
        · rw [uIoc_of_le h] at ht
          rw [abs_of_nonneg h, abs_of_nonneg ht.1.le]; exact ht.2
        · rw [uIoc_of_ge h] at ht
          rw [abs_of_nonpos h, abs_of_nonpos ht.2]; linarith [ht.1]
      exact mul_le_mul_of_nonneg_right htT (by positivity))
    (Eventually.of_forall fun t _ => summable_inv_sq_xiCopyOrdinate.mul_left |T|)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ => by
      rw [hF t]; exact (summable_sin_div_ordinate t).hasSum)
  simp_rw [hterm] at hsum
  exact hsum.tsum_eq.symm

/-- **RH mean law.**  Under RH, `(1/T)∫_0^T F(t) dt = (1/2) log T + O(1)` for `T ≥ 2π`. -/
theorem exists_abs_mean_liEvenCrossActualClockResponse_sub_half_log_le_of_rh
    (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 * Real.pi ≤ T →
      |(∫ t in (0 : ℝ)..T, liEvenCrossActualClockResponse t) / T - Real.log T / 2| ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_abs_xiOrdinateCosineMass_div_sub_le
  refine ⟨C, hC, fun T hT => ?_⟩
  rw [integral_liEvenCrossActualClockResponse_of_rh hRH]
  exact h T hT

end RHTower
