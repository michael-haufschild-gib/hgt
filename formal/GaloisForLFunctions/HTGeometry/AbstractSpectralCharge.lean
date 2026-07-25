import GaloisForLFunctions.HTGeometry.AbstractSpectralFamily

/-!
# The displacement charge and its neutrality

For a point `p = R + i J` of an admissible spectral family put

`chi = Im (p ^ 2) = 2 R J`.

Two facts organise the whole displacement calculus.

*Charge coordinates.*  The interface bound `|J| < 1/2` is exactly `|chi| < R`.  So admissibility is
a comparison between the charge and the height, not a separate normalisation, and the charge
vanishes precisely on the real locus.

*Neutrality.*  The conjugating involution of the family sends `chi` to `-chi` while fixing the
height.  Hence every sum of the charge against a height-determined weight vanishes identically:

`sum_i weight sigma i * chi_i = 0`.

No linear functional of the displacement can therefore see anything, whatever the family: the first
possibly non-vanishing displacement functional is quadratic.  This is why the trace of an admissible
family is real on the positive axis, and why the defect and the energy — both quadratic — are the
smallest invariants that detect the real locus.
-/

open Complex

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

theorem re_pos (i : ι) : 0 < (F.pt i).re := lt_of_lt_of_le F.base_pos (F.base_le i)

/-- The displacement charge of a point: the imaginary part of its square. -/
def charge (i : ι) : ℝ := ((F.pt i) ^ 2).im

theorem charge_eq (i : ι) : F.charge i = 2 * ((F.pt i).re * (F.pt i).im) := by
  rw [charge, pow_two, Complex.mul_im]; ring

/-- The charge vanishes exactly on the real locus. -/
theorem charge_eq_zero_iff (i : ι) : F.charge i = 0 ↔ (F.pt i).im = 0 := by
  rw [charge_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h2 | hprod
    · norm_num at h2
    · rcases mul_eq_zero.mp hprod with hre | him
      · exact absurd hre (ne_of_gt (F.re_pos i))
      · exact him
  · intro h; rw [h]; ring

/-- **Charge coordinates.**  The admissibility bound on displacements is exactly the comparison of
the charge with the height. -/
theorem abs_charge_lt_re (i : ι) : |F.charge i| < (F.pt i).re := by
  have hr := F.re_pos i
  have hj := F.abs_im_lt i
  rw [charge_eq, abs_mul, abs_mul, abs_of_pos hr]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [abs_nonneg ((F.pt i).im)]

/-! ### The conjugating involution reverses the charge -/

theorem re_pt_inv (i : ι) : (F.pt (F.inv i)).re = (F.pt i).re := by
  rw [F.conj_stable i, Complex.conj_re]

theorem charge_inv (i : ι) : F.charge (F.inv i) = -F.charge i := by
  rw [charge, charge, F.conj_stable i, ← map_pow, Complex.conj_im]

theorem weight_inv (σ : ℝ) (i : ι) : F.weight σ (F.inv i) = F.weight σ i := by
  rw [weight, weight, F.re_pt_inv i]

/-- **Every odd summable function on an admissible family sums to zero.**  The conjugating
involution is a bijection of the index set, so reindexing a function it negates gives back minus its
own sum. -/
theorem tsum_eq_zero_of_inv_odd {f : ι → ℝ}
    (hodd : ∀ i, f (F.inv i) = -f i) : ∑' i : ι, f i = 0 := by
  have hre : ∑' i : ι, f (F.inv i) = ∑' i : ι, f i := F.inv.tsum_eq f
  have hneg : ∑' i : ι, f (F.inv i) = -∑' i : ι, f i := by
    rw [tsum_congr hodd, tsum_neg]
  have hkey : ∑' i : ι, f i = -∑' i : ι, f i := hre.symm.trans hneg
  linarith

/-! ### Summability of the charge against the weight -/

theorem abs_charge_le_re (i : ι) : |F.charge i| ≤ (F.pt i).re := (F.abs_charge_lt_re i).le

theorem summable_weight_mul_charge {σ : ℝ} (hσ : 0 < σ) :
    Summable fun i => F.weight σ i * F.charge i := by
  have hhalf : Summable fun i : ι => F.weight (σ / 2) i := F.summable_weight (by linarith)
  refine Summable.of_norm_bounded (hhalf.mul_left (2 / σ)) fun i => ?_
  have hr := F.re_pos i
  have hchg := F.abs_charge_le_re i
  have hbound : (F.pt i).re ≤ 2 / σ * Real.exp (σ / 2 * (F.pt i).re) := by
    have hexp : σ / 2 * (F.pt i).re ≤ Real.exp (σ / 2 * (F.pt i).re) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have hcoef : (0 : ℝ) ≤ 2 / σ := by positivity
    have h2 := mul_le_mul_of_nonneg_left hexp hcoef
    have hid : 2 / σ * (σ / 2 * (F.pt i).re) = (F.pt i).re := by
      field_simp
    rw [hid] at h2
    exact h2
  have hw : 0 < F.weight σ i := F.weight_pos σ i
  have hwid : F.weight σ i * Real.exp (σ / 2 * (F.pt i).re) = F.weight (σ / 2) i := by
    rw [weight, weight, ← Real.exp_add]
    congr 1
    ring
  calc ‖F.weight σ i * F.charge i‖ = F.weight σ i * |F.charge i| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
    _ ≤ F.weight σ i * (2 / σ * Real.exp (σ / 2 * (F.pt i).re)) :=
        mul_le_mul_of_nonneg_left (hchg.trans hbound) hw.le
    _ = 2 / σ * F.weight (σ / 2) i := by rw [← hwid]; ring

/-- **Charge neutrality.**  For every admissible family and every real time the weighted total
displacement charge vanishes.  Linear functionals of the displacement are therefore identically
zero: no first-order statistic of an admissible spectrum can distinguish it from a real one. -/
theorem tsum_weight_mul_charge_eq_zero {σ : ℝ} (hσ : 0 < σ) :
    ∑' i : ι, F.weight σ i * F.charge i = 0 := by
  refine F.tsum_eq_zero_of_inv_odd fun i => ?_
  rw [F.weight_inv σ i, F.charge_inv i]
  ring

/-! ### The trace is real on the positive axis -/

theorem im_term_inv {σ : ℝ} (i : ι) :
    (F.term (σ : ℂ) (F.inv i)).im = -(F.term (σ : ℂ) i).im := by
  rw [term, term, F.conj_stable i]
  have hmul : -(σ : ℂ) * (starRingEnd ℂ) (F.pt i) = (starRingEnd ℂ) (-(σ : ℂ) * F.pt i) := by
    rw [map_mul, map_neg, Complex.conj_ofReal]
  rw [hmul, Complex.exp_conj, Complex.conj_im]

/-- **The trace of an admissible family is real on the positive real axis.**  This is charge
neutrality at the level of the trace: the imaginary part of each term is odd under the conjugating
involution. -/
theorem im_traceC_ofReal_eq_zero {σ : ℝ} (hσ : 0 < σ) : (F.traceC (σ : ℂ)).im = 0 := by
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hsum : Summable fun i : ι => F.term (σ : ℂ) i := (F.summable_norm_term hre).of_norm
  rw [traceC, Complex.im_tsum hsum]
  exact F.tsum_eq_zero_of_inv_odd fun i => F.im_term_inv i

end AbstractSpectralFamily

end

end HTGeometry
