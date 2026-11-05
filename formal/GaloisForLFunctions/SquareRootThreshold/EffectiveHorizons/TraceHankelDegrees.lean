import GaloisForLFunctions.RHTower.TraceHankelConverse
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Finite-degree detection of nonreal trace-Hankel atoms

A real orbit separator kills the finite spectrum outside half the target
modulus. Its radial monomial suppresses the remaining trace geometrically.
An explicit exponent gives a negative certificate in every principal ideal
whose generator does not vanish at the target, with a finite degree bound.
-/

open Complex Polynomial Filter Topology

noncomputable section
namespace RHTower

/-- The exact geometric radial decay of the phase-corrected orbit separator. -/
theorem norm_eval_phaseCorrectedSeparatorPolynomial_le_geometric
    {F : Finset ℂ} {α z c : ℂ} (hα0 : α ≠ 0) (him : α.im ≠ 0)
    (hz : ‖z‖ ≤ ‖α‖) (n : ℕ) :
    ‖evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n) z‖ ≤
      phaseCorrectedSeparatorNormBound F α c * (‖z‖ / ‖α‖) ^ n := by
  let sep := realOrbitSeparator F α
  let d := c / evalRealPolynomial sep α
  let u := α / (‖α‖ : ℂ)
  let ratio : ℝ := ‖z‖ / ‖α‖
  have hrpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
      div_self (ne_of_gt hrpos)]
  have hv_norm (n : ℕ) : ‖d * u⁻¹ ^ n‖ = ‖d‖ := by
    rw [norm_mul, norm_pow, norm_inv, hu_norm, inv_one, one_pow, mul_one]
  have hnormle (n : ℕ) :
      ‖evalRealPolynomial (phaseCorrectedSeparatorPolynomial F α c n) z‖ ≤
        phaseCorrectedSeparatorNormBound F α c * ratio ^ n := by
    have hzle : ‖z‖ ≤ ‖α‖ := hz
    have hsepbound := norm_evalRealPolynomial_le sep hzle
    have hinterp := norm_evalRealLinearInterpolator_le
      (α := α) (v := d * u⁻¹ ^ n) (z := z) him
    rw [hv_norm] at hinterp
    have himabs : 0 < |α.im| := abs_pos.mpr him
    have hfactor :
        1 + (|α.re| + ‖z‖) / |α.im| ≤
          1 + (|α.re| + ‖α‖) / |α.im| := by
      gcongr
    have hinterp' : ‖evalRealPolynomial
        (realLinearInterpolator α (d * u⁻¹ ^ n)) z‖ ≤
        (1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖ :=
      hinterp.trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg d))
    have hscale :
        ‖evalRealPolynomial ((C (‖α‖⁻¹) * X) ^ n) z‖ = ratio ^ n := by
      rw [evalRealPolynomial_pow, evalRealPolynomial_scaleX, norm_pow, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hrpos))]
      congr 1
      dsimp [ratio]
      rw [inv_mul_eq_div]
    rw [phaseCorrectedSeparatorPolynomial]
    change ‖evalRealPolynomial
      (sep * realLinearInterpolator α (d * u⁻¹ ^ n) * (C (‖α‖⁻¹) * X) ^ n) z‖ ≤ _
    rw [evalRealPolynomial_mul, evalRealPolynomial_mul, norm_mul, norm_mul, hscale]
    dsimp [phaseCorrectedSeparatorNormBound]
    change _ ≤ (evalRealPolynomialNormBound sep ‖α‖ *
      ((1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖)) * ratio ^ n
    have hsepBoundNonneg : 0 ≤ evalRealPolynomialNormBound sep ‖α‖ :=
      evalRealPolynomialNormBound_nonneg sep (norm_nonneg α)
    have hinterpBoundNonneg :
        0 ≤ (1 + (|α.re| + ‖α‖) / |α.im|) * ‖d‖ := by positivity
    gcongr
  exact hnormle n

/-- A square-root phase makes the target weighted square exactly `-1`. -/
def traceHankelNegativePhase (α : ℂ) : ℂ := Complex.sqrt (-1 / α)

theorem mul_traceHankelNegativePhase_sq {α : ℂ} (hα : α ≠ 0) :
    α * traceHankelNegativePhase α ^ 2 = -1 := by
  have hs : Complex.sqrt (-1 / α) ^ 2 = -1 / α := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (-1 / α) 2
  rw [traceHankelNegativePhase, hs]
  field_simp

/-- The radial power needed to make a tail with majorant `E²M` smaller than one half. -/
def traceHankelRadialExponent (E M : ℝ) : ℕ :=
  ⌈Real.log (1 + 2 * E ^ 2 * M) / Real.log 4⌉₊ + 1

theorem traceHankelRadialExponent_tail_lt_half {E M : ℝ} (hM : 0 ≤ M) :
    E ^ 2 * M * (1 / 4 : ℝ) ^ traceHankelRadialExponent E M < 1 / 2 := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have harg : 0 < 1 + 2 * E ^ 2 * M := by positivity
  have hceil := Nat.le_ceil (Real.log (1 + 2 * E ^ 2 * M) / Real.log 4)
  have hn : Real.log (1 + 2 * E ^ 2 * M) / Real.log 4 <
      (traceHankelRadialExponent E M : ℝ) := by
    simp only [traceHankelRadialExponent, Nat.cast_add, Nat.cast_one]
    linarith
  rw [div_lt_iff₀ hlog4] at hn
  have he := Real.exp_lt_exp.mpr hn
  rw [Real.exp_log harg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at he
  rw [one_div, inv_pow, ← div_eq_mul_inv, div_lt_iff₀ (by positivity :
    0 < (4 : ℝ) ^ traceHankelRadialExponent E M)]
  linarith

private theorem natDegree_realConjQuadratic_le (α : ℂ) :
    (realConjQuadratic α).natDegree ≤ 2 := by
  unfold realConjQuadratic
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp only [natDegree_X_pow, le_refl]
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp

private theorem natDegree_realLinearInterpolator_le (α c : ℂ) :
    (realLinearInterpolator α c).natDegree ≤ 1 := by
  unfold realLinearInterpolator
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp only [natDegree_C]; omega
  · exact (natDegree_C_mul_le _ _).trans (by simp)

theorem natDegree_realOrbitSeparator_le (F : Finset ℂ) (α : ℂ) :
    (realOrbitSeparator F α).natDegree ≤ 2 * F.card := by
  classical
  unfold realOrbitSeparator
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ _β ∈ F.filter (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α), 2 :=
      Finset.sum_le_sum fun β _ => natDegree_realConjQuadratic_le β
    _ ≤ 2 * F.card := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      have h := Finset.card_filter_le F (fun β => β ≠ α ∧ β ≠ (starRingEnd ℂ) α)
      omega

theorem natDegree_phaseCorrectedSeparatorPolynomial_le
    (F : Finset ℂ) (α c : ℂ) (n : ℕ) :
    (phaseCorrectedSeparatorPolynomial F α c n).natDegree ≤ 2 * F.card + 1 + n := by
  unfold phaseCorrectedSeparatorPolynomial
  refine natDegree_mul_le.trans ?_
  have hsep := natDegree_realOrbitSeparator_le F α
  have hlin := natDegree_realLinearInterpolator_le α
    (c / evalRealPolynomial (realOrbitSeparator F α) α * (α / (‖α‖ : ℂ))⁻¹ ^ n)
  have hp : ((C (‖α‖⁻¹) * X : ℝ[X]) ^ n).natDegree ≤ n := by
    refine natDegree_pow_le.trans ?_
    have hx : (C (‖α‖⁻¹) * X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (by simp)
    simpa using Nat.mul_le_mul_left n hx
  have hprod := @natDegree_mul_le ℝ _ (realOrbitSeparator F α)
    (realLinearInterpolator α
      (c / evalRealPolynomial (realOrbitSeparator F α) α * (α / (‖α‖ : ℂ))⁻¹ ^ n))
  omega

/-- Coefficient majorant for an ideal generator times its normalized orbit separator. -/
def traceHankelIdealMajorant (F : Finset ℂ) (α : ℂ) (a : ℝ[X]) : ℝ :=
  evalRealPolynomialNormBound a ‖α‖ *
    phaseCorrectedSeparatorNormBound F α
      (traceHankelNegativePhase α / evalRealPolynomial a α)

/-- An explicit polynomial exposing a nonreal atom of a trace-class spectrum. -/
def traceHankelIdealDetector (F : Finset ℂ) (α : ℂ) (a : ℝ[X]) (M : ℝ) : ℝ[X] :=
  phaseCorrectedSeparatorPolynomial F α
    (traceHankelNegativePhase α / evalRealPolynomial a α)
    (traceHankelRadialExponent (traceHankelIdealMajorant F α a) M)

theorem natDegree_traceHankelIdealDetector_le (F : Finset ℂ) (α : ℂ) (a : ℝ[X]) (M : ℝ) :
    (traceHankelIdealDetector F α a M).natDegree ≤ 2 * F.card + 1 +
      traceHankelRadialExponent (traceHankelIdealMajorant F α a) M :=
  natDegree_phaseCorrectedSeparatorPolynomial_le _ _ _ _

/-- A half-radius outer spectrum gives an explicit strict negative trace-Hankel certificate.
The degree depends only on its finite separator and a bound for total spectral mass. -/
theorem traceHankelIdealDetector_negative {ι : Type*} (lam : ι → ℂ)
    (hsum : Summable lam) (M : ℝ) (hmass : (∑' i, ‖lam i‖) ≤ M)
    (i₀ : ι) (him : (lam i₀).im ≠ 0) (a : ℝ[X])
    (ha : evalRealPolynomial a (lam i₀) ≠ 0) (S : Finset ι)
    (hS : ∀ i, i ∈ S ↔ ‖lam i₀‖ / 2 ≤ ‖lam i‖) :
    (∑' i, lam i * evalRealPolynomial
      (a * traceHankelIdealDetector (S.image lam) (lam i₀) a M) (lam i) ^ 2).re < -1 / 2 := by
  classical
  let α : ℂ := lam i₀
  let F : Finset ℂ := S.image lam
  let c : ℂ := traceHankelNegativePhase α
  let d : ℂ := c / evalRealPolynomial a α
  let E : ℝ := traceHankelIdealMajorant F α a
  let n : ℕ := traceHankelRadialExponent E M
  let p : ℝ[X] := phaseCorrectedSeparatorPolynomial F α d n
  let q : ℝ[X] := a * p
  let f : ι → ℂ := fun i => lam i * evalRealPolynomial q (lam i) ^ 2
  have hα0 : α ≠ 0 := by
    intro h
    exact him (by change α.im = 0; rw [h]; rfl)
  have hr : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hM : 0 ≤ M := (tsum_nonneg fun i => norm_nonneg (lam i)).trans hmass
  have hA : 0 ≤ evalRealPolynomialNormBound a ‖α‖ :=
    evalRealPolynomialNormBound_nonneg a (norm_nonneg α)
  have hC : 0 ≤ phaseCorrectedSeparatorNormBound F α d :=
    phaseCorrectedSeparatorNormBound_nonneg F him
  have hE : 0 ≤ E := mul_nonneg hA hC
  have had : evalRealPolynomial a α * d = c := mul_div_cancel₀ c ha
  have htarget : evalRealPolynomial q α = c := by
    change evalRealPolynomial (a * phaseCorrectedSeparatorPolynomial F α d n) α = c
    rw [evalRealPolynomial_mul, eval_phaseCorrectedSeparatorPolynomial_target hα0 him, had]
  have hconj : evalRealPolynomial q ((starRingEnd ℂ) α) = (starRingEnd ℂ) c := by
    rw [evalRealPolynomial_conj, htarget]
  have hphase : α * c ^ 2 = -1 := mul_traceHankelNegativePhase_sq hα0
  have hi₀S : i₀ ∈ S := (hS i₀).mpr (by change ‖α‖ / 2 ≤ ‖α‖; linarith)
  have hzero (i : ι) (hi : i ∈ S) (hne : lam i ≠ α)
      (hnec : lam i ≠ (starRingEnd ℂ) α) : evalRealPolynomial q (lam i) = 0 := by
    have hiF : lam i ∈ F := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hp := eval_phaseCorrectedSeparatorPolynomial_outer_zero
      (c := d) hiF hne hnec n
    change evalRealPolynomial p (lam i) = 0 at hp
    simp only [q, evalRealPolynomial_mul, hp, mul_zero]
  have hbound (i : ι) : ‖evalRealPolynomial q (lam i)‖ ≤ E := by
    by_cases hi : ‖lam i‖ ≤ ‖α‖
    · have hp := norm_eval_phaseCorrectedSeparatorPolynomial_le (F := F) (c := d) hα0 him hi n
      change ‖evalRealPolynomial p (lam i)‖ ≤ _ at hp
      change ‖evalRealPolynomial (a * p) (lam i)‖ ≤
        evalRealPolynomialNormBound a ‖α‖ * phaseCorrectedSeparatorNormBound F α d
      rw [evalRealPolynomial_mul, norm_mul]
      exact mul_le_mul (norm_evalRealPolynomial_le a hi) hp (norm_nonneg _) hA
    · have hiS : i ∈ S := (hS i).mpr (by change ‖α‖ / 2 ≤ ‖lam i‖; linarith)
      have hne : lam i ≠ α := fun h => hi (by rw [h])
      have hnec : lam i ≠ (starRingEnd ℂ) α := fun h => hi (by rw [h, norm_conj])
      rw [hzero i hiS hne hnec, norm_zero]
      exact hE
  have hnorm (i : ι) : ‖f i‖ ≤ E ^ 2 * ‖lam i‖ := by
    dsimp only [f]
    rw [norm_mul, norm_pow]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (norm_nonneg (lam i))
  have hfNorm : Summable (fun i => ‖f i‖) :=
    (hsum.norm.mul_left (E ^ 2)).of_nonneg_of_le (fun i => norm_nonneg _) hnorm
  have hf : Summable f := hfNorm.of_norm
  have htailBound (i : ι) (hi : i ∉ S) :
      ‖f i‖ ≤ (E ^ 2 * (1 / 4 : ℝ) ^ n) * ‖lam i‖ := by
    have hiSmall : ‖lam i‖ < ‖α‖ / 2 := lt_of_not_ge (fun h => hi ((hS i).mpr h))
    have hiR : ‖lam i‖ ≤ ‖α‖ := by linarith
    have hratio : ‖lam i‖ / ‖α‖ ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
    have hp := norm_eval_phaseCorrectedSeparatorPolynomial_le_geometric
      (F := F) (c := d) hα0 him hiR n
    have hdecay : ‖evalRealPolynomial p (lam i)‖ ≤
        phaseCorrectedSeparatorNormBound F α d * (1 / 2 : ℝ) ^ n := by
      refine hp.trans (mul_le_mul_of_nonneg_left ?_ hC)
      exact pow_le_pow_left₀ (by positivity) hratio n
    have hq : ‖evalRealPolynomial q (lam i)‖ ≤ E * (1 / 2 : ℝ) ^ n := by
      dsimp only [q]
      rw [evalRealPolynomial_mul, norm_mul]
      have h := mul_le_mul (norm_evalRealPolynomial_le a hiR) hdecay (norm_nonneg _) hA
      exact h.trans_eq (mul_assoc _ _ _).symm
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have hpow : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
      rw [← pow_mul, show n * 2 = 2 * n by omega, pow_mul]
      norm_num
    dsimp only [f]
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖lam i‖ * (E * (1 / 2 : ℝ) ^ n) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
      _ = (E ^ 2 * (1 / 4 : ℝ) ^ n) * ‖lam i‖ := by rw [mul_pow, hpow]; ring
  have htailMass : (∑' i : {i // i ∉ S}, ‖lam i‖) ≤ M := by
    have hsplit := hsum.norm.sum_add_tsum_subtype_compl S
    have hpos : 0 ≤ ∑ i ∈ S, ‖lam i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith only [hsplit, hpos, hmass]
  have htailNorm : ‖∑' i : {i // i ∉ S}, f i‖ < 1 / 2 := by
    have htailSummable := hsum.norm.subtype (fun i => i ∉ S)
    have hnormSummable := hfNorm.subtype (fun i => i ∉ S)
    calc
      _ ≤ ∑' i : {i // i ∉ S}, ‖f i‖ := norm_tsum_le_tsum_norm hnormSummable
      _ ≤ ∑' i : {i // i ∉ S}, (E ^ 2 * (1 / 4 : ℝ) ^ n) * ‖lam i‖ :=
        hnormSummable.tsum_le_tsum (fun i => htailBound i i.2)
          (htailSummable.mul_left _)
      _ = (E ^ 2 * (1 / 4 : ℝ) ^ n) * ∑' i : {i // i ∉ S}, ‖lam i‖ := tsum_mul_left
      _ ≤ (E ^ 2 * (1 / 4 : ℝ) ^ n) * M :=
        mul_le_mul_of_nonneg_left htailMass (by positivity)
      _ = E ^ 2 * M * (1 / 4 : ℝ) ^ n := by ring
      _ < 1 / 2 := traceHankelRadialExponent_tail_lt_half hM
  have houter (i : ι) (hi : i ∈ S) : (f i).re ≤ 0 := by
    by_cases hia : lam i = α
    · simp only [f, hia, htarget, hphase, neg_re, one_re]
      norm_num
    · by_cases hic : lam i = (starRingEnd ℂ) α
      · simp only [f, hic, hconj, ← map_pow, ← map_mul, hphase]
        norm_num
      · dsimp only [f]
        rw [hzero i hi hia hic]
        norm_num
  have htargetRe : (f i₀).re = -1 := by
    change (α * evalRealPolynomial q α ^ 2).re = -1
    rw [htarget, hphase]
    norm_num
  have houterSum : (∑ i ∈ S, f i).re ≤ -1 := by
    rw [Complex.re_sum]
    have hrest : ∑ i ∈ S.erase i₀, (f i).re ≤ 0 :=
      Finset.sum_nonpos fun i hi => houter i (Finset.mem_erase.mp hi).2
    have hsplit := Finset.sum_erase_add S (fun i => (f i).re) hi₀S
    rw [htargetRe] at hsplit
    linarith
  have hsplit := congrArg Complex.re (hf.sum_add_tsum_subtype_compl S)
  rw [Complex.add_re] at hsplit
  have htailRe := Complex.re_le_norm (∑' i : {i // i ∉ S}, f i)
  change (∑' i, f i).re < -1 / 2
  linarith

/-- A spectral mass bound controls the number of atoms above half a fixed modulus. -/
theorem card_le_ceil_of_half_norm_mass {ι : Type*} (lam : ι → ℂ)
    (hsum : Summable lam) (M : ℝ) (hmass : (∑' i, ‖lam i‖) ≤ M)
    {r : ℝ} (hr : 0 < r) (S : Finset ι)
    (hS : ∀ i ∈ S, r / 2 ≤ ‖lam i‖) : S.card ≤ ⌈2 * M / r⌉₊ := by
  have hlow := Finset.card_nsmul_le_sum S (fun i => ‖lam i‖) (r / 2) hS
  rw [nsmul_eq_mul] at hlow
  have hsumS := hsum.norm.sum_le_tsum S (fun i _ => norm_nonneg (lam i))
  have hcard : (S.card : ℝ) ≤ 2 * M / r := by
    rw [le_div_iff₀ hr]
    nlinarith only [hlow, hsumS, hmass]
  have hceil := hcard.trans (Nat.le_ceil (2 * M / r))
  exact_mod_cast hceil

#print axioms traceHankelIdealDetector_negative
#print axioms natDegree_traceHankelIdealDetector_le
#print axioms card_le_ceil_of_half_norm_mass

end RHTower
