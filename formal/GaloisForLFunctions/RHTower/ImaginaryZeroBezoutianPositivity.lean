/-
# An even order-one function with imaginary zeros has a positive Bezoutian

For an even entire function of order one whose zeros all lie on the imaginary axis, the Hermitian
kernel

`B(w,v) = (f'(w) conj (f v) + f w conj (f' v)) / (w + conj v)`

is positive semidefinite on the open right half plane.

Hadamard factorization writes `f` as a constant times `w^m` times the genus-one canonical product
over its own divisor, and evenness removes the exponential factor.  The logarithmic derivative is
then the Mittag-Leffler series over the divisor, and each imaginary pole contributes one rank-one
Gram term because `(w - it) + conj (v - it) = w + conj v`.  Multiplying by `f w conj (f v)` is a
diagonal congruence.
-/
import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.HTGeometry.ImaginaryPoleBezoutianGram
import GaloisForLFunctions.HTGeometry.TsumRankOnePosSemidef

noncomputable section

open Complex Filter Topology Metric Set
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.CountableDivisor
open GaloisForLFunctions.EntireQuotient GaloisForLFunctions.HTGeometry
open scoped ComplexOrder

namespace RHTower.OrderOneHadamard

/-- Splitting off the monomial at the origin preserves the order-one growth class. -/
theorem exists_orderOneEnvelope_monomial_quotient {f g : ℂ → ℂ} {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hfac : ∀ z, f z = z ^ m * g z) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ z : ℂ, ‖g z‖ ≤ Real.exp (C' * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  have hcont : ContinuousOn (fun z : ℂ => ‖g z‖) (Metric.closedBall (0 : ℂ) 1) := by
    intro w _
    exact ((hg w (Set.mem_univ w)).continuousAt.continuousWithinAt).norm
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  set M : ℝ := max 1 M₀ with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMlognn : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set C' : ℝ := max C (Real.log M / Real.log 2) with hC'
  have hC'nn : 0 ≤ C' := le_trans hC (le_max_left _ _)
  refine ⟨C', hC'nn, fun z => ?_⟩
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hshape2 : Real.log 2 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    have h1 : Real.log 2 ≤ Real.log (2 + ‖z‖) := Real.log_le_log (by norm_num) (by linarith)
    nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  have hshapenn : (0 : ℝ) ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := le_trans hlog2.le hshape2
  by_cases hzu : ‖z‖ ≤ 1
  · have hmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzu
    have hb := hM₀ z hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    have hgM : ‖g z‖ ≤ M := le_trans hb (le_max_right _ _)
    refine le_trans hgM ?_
    rw [← Real.exp_log (by linarith : (0:ℝ) < M)]
    refine Real.exp_le_exp.mpr ?_
    have hstep : Real.log M / Real.log 2 * Real.log 2 ≤ C' * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
      have h1 : Real.log M / Real.log 2 ≤ C' := le_max_right _ _
      nlinarith [div_nonneg hMlognn hlog2.le]
    rw [div_mul_cancel₀ _ hlog2.ne'] at hstep
    nlinarith [hstep]
  · have hz1 : (1 : ℝ) < ‖z‖ := lt_of_not_ge hzu
    have hpow : (1 : ℝ) ≤ ‖z‖ ^ m := one_le_pow₀ hz1.le
    have hfz : ‖f z‖ = ‖z‖ ^ m * ‖g z‖ := by rw [hfac z, norm_mul, norm_pow]
    have hgle : ‖g z‖ ≤ ‖f z‖ := by
      rw [hfz]
      nlinarith [norm_nonneg (g z)]
    refine le_trans hgle (le_trans (hbound z) (Real.exp_le_exp.mpr ?_))
    have hCC : C ≤ C' := le_max_left _ _
    nlinarith [hshapenn]

variable {f : ℂ → ℂ}

/-- **The imaginary-divisor Bezoutian is positive semidefinite.**  For an even entire function of
order one whose zeros all lie on the imaginary axis, every finite Gram matrix of the Bezoutian
kernel over the open right half plane is positive semidefinite. -/
theorem posSemidef_bezoutian_of_imaginary_zeros {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (himag : ∀ z : ℂ, f z = 0 → z.re = 0)
    {n : ℕ} (w : Fin n → ℂ) (hw : ∀ j, 0 < (w j).re) :
    (Matrix.of fun j k =>
      (deriv f (w j) * (starRingEnd ℂ) (f (w k)) + f (w j) * (starRingEnd ℂ) (deriv f (w k)))
        / (w j + (starRingEnd ℂ) (w k))).PosSemidef := by
  classical
  -- split off the zero at the origin
  obtain ⟨g, hg, hg0, hgord, hgfac⟩ := exists_monomial_factorization hf hford
  obtain ⟨m, hgfac⟩ : ∃ m : ℕ, ∀ z, f z = z ^ m * g z := ⟨_, hgfac⟩
  have hgc : Continuous g := by
    have : Differentiable ℂ g := fun z => (hg z (Set.mem_univ z)).differentiableAt
    exact this.continuous
  -- the quotient is even
  have hpar : ∀ z : ℂ, z ≠ 0 → ((-1 : ℂ)) ^ m * g (-z) = g z := by
    intro z hz
    have h1 := hgfac (-z)
    rw [heven z] at h1
    have h2 := hgfac z
    have h3 : (-z) ^ m * g (-z) = z ^ m * g z := by rw [← h1, ← h2]
    rw [neg_pow] at h3
    have hzm : (z : ℂ) ^ m ≠ 0 := pow_ne_zero _ hz
    refine mul_right_cancel₀ hzm ?_
    linear_combination h3
  have hg0eq : ((-1 : ℂ)) ^ m * g 0 = g 0 := by
    have hcont1 : Filter.Tendsto (fun z : ℂ => ((-1 : ℂ)) ^ m * g (-z)) (𝓝[≠] (0 : ℂ))
        (𝓝 (((-1 : ℂ)) ^ m * g 0)) := by
      have hc : ContinuousAt (fun z : ℂ => ((-1 : ℂ)) ^ m * g (-z)) 0 :=
        (continuous_const.mul (hgc.comp continuous_neg)).continuousAt
      have hcw : Filter.Tendsto (fun z : ℂ => ((-1 : ℂ)) ^ m * g (-z)) (𝓝[≠] (0 : ℂ))
          (𝓝 (((-1 : ℂ)) ^ m * g (-(0 : ℂ)))) := hc.continuousWithinAt
      rwa [neg_zero] at hcw
    have hcont2 : Filter.Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
      hgc.continuousAt.continuousWithinAt
    have heq : (fun z : ℂ => ((-1 : ℂ)) ^ m * g (-z)) =ᶠ[𝓝[≠] (0 : ℂ)] g := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hpar z hz
    exact tendsto_nhds_unique (hcont1.congr' heq) hcont2
  have hsign : ((-1 : ℂ)) ^ m = 1 := by
    have h : (((-1 : ℂ)) ^ m - 1) * g 0 = 0 := by linear_combination hg0eq
    rcases mul_eq_zero.mp h with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hg0
  have hgeven : ∀ z, g (-z) = g z := by
    intro z
    by_cases hz : z = 0
    · rw [hz, neg_zero]
    · have := hpar z hz
      rwa [hsign, one_mul] at this
  -- the quotient inherits the growth and the divisor
  obtain ⟨C', hC', hgbound⟩ := exists_orderOneEnvelope_monomial_quotient hC hg hbound hgfac
  have hgford : ∀ z, analyticOrderAt g z ≠ ⊤ := by
    intro z
    rcases hgord z with h | h
    · rw [h]; exact hford z
    · subst h
      rw [(hg 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hg0]
      exact ENat.coe_ne_top 0
  have hgimag : ∀ z : ℂ, g z = 0 → z.re = 0 := by
    intro z hz
    by_cases h0 : z = 0
    · exact absurd (h0 ▸ hz) hg0
    · exact himag z (by rw [hgfac z, hz, mul_zero])
  -- Hadamard
  have hgP := eq_const_mul_hadamardProduct_of_even hC' hg hg0 hgford hgeven hgbound
  set P : ℂ → ℂ := hadamardProduct g with hP
  set a : ZeroCopy g → ℂ := zeroCopyPoint g with ha
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hg hg0
  have hsum : Summable (fun q : ZeroCopy g => 1 / ‖a q‖ ^ 2) :=
    summable_inv_sq_zeroCopyPoint hC' hg hg0 hgbound
  have hazero : ∀ q, g (a q) = 0 := by
    intro q
    by_contra hne
    have hord : analyticOrderAt g (a q) = 0 :=
      (hg (a q) (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hne
    have hdiv : (MeromorphicOn.divisor g Set.univ) (a q) ≠ 0 := q.1.2
    apply hdiv
    rw [divisor_univ_eq_analyticOrder hg, hord]
    simp
  have haim : ∀ q, (a q).re = 0 := fun q => hgimag _ (hazero q)
  have haeq : ∀ q, a q = ((a q).im : ℝ) * Complex.I := by
    intro q
    apply Complex.ext
    · simp [haim q]
    · simp
  -- the right half plane avoids the divisor
  have hwne : ∀ j, ∀ q, w j ≠ a q := by
    intro j q h
    have := hw j
    rw [h, haim q] at this
    exact lt_irrefl 0 this
  have hw0 : ∀ j, w j ≠ 0 := by
    intro j h
    have := hw j
    rw [h] at this
    simp at this
  have hgw : ∀ j, g (w j) ≠ 0 := by
    intro j h
    have := hw j
    rw [hgimag _ h] at this
    exact lt_irrefl 0 this
  have hfw : ∀ j, f (w j) ≠ 0 := by
    intro j
    rw [hgfac (w j)]
    exact mul_ne_zero (pow_ne_zero _ (hw0 j)) (hgw j)
  have hPw : ∀ j, P (w j) ≠ 0 :=
    fun j => canonicalProductE1Indexed_ne_zero a hane hsum (hwne j)
  -- the logarithmic derivative
  have hPan : AnalyticOnNhd ℂ P Set.univ := hadamardProduct_analytic hg hg0 hsum
  have hLf : ∀ j, deriv f (w j) = ((m : ℂ) / w j + logDeriv P (w j)) * f (w j) := by
    intro j
    have hfeq : f = fun z : ℂ => z ^ m * (g 0 * P z) := by
      funext z
      rw [hgfac z, hgP z]
    have hPderiv : HasDerivAt P (deriv P (w j)) (w j) :=
      (hPan (w j) (Set.mem_univ _)).differentiableAt.hasDerivAt
    have hmono : HasDerivAt (fun z : ℂ => z ^ m) ((m : ℂ) * w j ^ (m - 1)) (w j) := by
      simpa using hasDerivAt_pow m (w j)
    have hprod : HasDerivAt f
        ((m : ℂ) * w j ^ (m - 1) * (g 0 * P (w j)) + w j ^ m * (g 0 * deriv P (w j))) (w j) := by
      rw [hfeq]
      exact hmono.mul (HasDerivAt.const_mul (g 0) hPderiv)
    have hfval : f (w j) = w j ^ m * (g 0 * P (w j)) := by rw [hgfac (w j), hgP (w j)]
    have hlog : logDeriv P (w j) = deriv P (w j) / P (w j) := rfl
    have hwj : w j ≠ 0 := hw0 j
    have hPj : P (w j) ≠ 0 := hPw j
    have h1 : (m : ℂ) / w j * (w j ^ m * (g 0 * P (w j)))
        = (m : ℂ) * w j ^ (m - 1) * (g 0 * P (w j)) := by
      rcases m with _ | m'
      · simp
      · rw [pow_succ, Nat.add_sub_cancel]
        field_simp
    have h2 : deriv P (w j) / P (w j) * (w j ^ m * (g 0 * P (w j)))
        = w j ^ m * (g 0 * deriv P (w j)) := by
      field_simp
    rw [hprod.deriv, hfval, hlog, add_mul, h1, h2]

  -- the Carathéodory kernel
  set K : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun j k =>
      (((m : ℂ) / w j + logDeriv P (w j))
        + (starRingEnd ℂ) ((m : ℂ) / w k + logDeriv P (w k)))
        / (w j + (starRingEnd ℂ) (w k)) with hK
  have hKsplit : ∀ j k : Fin n, K j k
      = (((Real.sqrt m : ℝ) : ℂ) * (w j)⁻¹) *
          (starRingEnd ℂ) (((Real.sqrt m : ℝ) : ℂ) * (w k)⁻¹)
        + ∑' q : ZeroCopy g, (w j - a q)⁻¹ * (starRingEnd ℂ) ((w k - a q)⁻¹) := by
    intro j k
    show (((m : ℂ) / w j + logDeriv P (w j))
        + (starRingEnd ℂ) ((m : ℂ) / w k + logDeriv P (w k)))
        / (w j + (starRingEnd ℂ) (w k)) = _
    have hden : w j + (starRingEnd ℂ) (w k) ≠ 0 := add_conj_ne_zero (hw j) (hw k)
    have hlogj : logDeriv P (w j) = ∑' q : ZeroCopy g, ((w j - a q)⁻¹ + (a q)⁻¹) :=
      logDeriv_canonicalProductE1Indexed hane hsum (hwne j)
    have hlogk : logDeriv P (w k) = ∑' q : ZeroCopy g, ((w k - a q)⁻¹ + (a q)⁻¹) :=
      logDeriv_canonicalProductE1Indexed hane hsum (hwne k)
    have hsumj : Summable (fun q : ZeroCopy g => (w j - a q)⁻¹ + (a q)⁻¹) := by
      refine (summable_canonicalProductE1LogDerivTerm hane hsum (hwne j)).neg.congr (fun q => ?_)
      have hneg : w j - a q = -(a q - w j) := by ring
      rw [hneg, inv_neg]
      ring
    have hsumk : Summable (fun q : ZeroCopy g => (w k - a q)⁻¹ + (a q)⁻¹) := by
      refine (summable_canonicalProductE1LogDerivTerm hane hsum (hwne k)).neg.congr (fun q => ?_)
      have hneg : w k - a q = -(a q - w k) := by ring
      rw [hneg, inv_neg]
      ring
    have hsumkc : Summable (fun q : ZeroCopy g =>
        (starRingEnd ℂ) ((w k - a q)⁻¹ + (a q)⁻¹)) :=
      hsumk.map (starRingEnd ℂ) (by fun_prop)
    -- the monomial part
    have hzeroI : ((0 : ℝ) : ℂ) * Complex.I = 0 := by simp
    have hmonokernel : ((w j)⁻¹ + (starRingEnd ℂ) ((w k)⁻¹)) / (w j + (starRingEnd ℂ) (w k))
        = (w j)⁻¹ * (starRingEnd ℂ) ((w k)⁻¹) := by
      have hrk := bezoutian_imaginary_pole_rankOne (0 : ℝ) (hw j) (hw k)
      simpa [hzeroI] using hrk
    -- the divisor part
    have hterm : ∀ q : ZeroCopy g,
        (((w j - a q)⁻¹ + (a q)⁻¹) + (starRingEnd ℂ) ((w k - a q)⁻¹ + (a q)⁻¹))
            / (w j + (starRingEnd ℂ) (w k))
          = (w j - a q)⁻¹ * (starRingEnd ℂ) ((w k - a q)⁻¹) := by
      intro q
      have hcancel : (a q)⁻¹ + (starRingEnd ℂ) ((a q)⁻¹) = 0 := by
        have hre : ((a q)⁻¹).re = 0 := by
          rw [Complex.inv_re, haim q]
          simp
        have hac := Complex.add_conj ((a q)⁻¹)
        rw [hre] at hac
        simpa using hac
      have hrk := bezoutian_imaginary_pole_rankOne ((a q).im) (hw j) (hw k)
      rw [← haeq q] at hrk
      calc (((w j - a q)⁻¹ + (a q)⁻¹) + (starRingEnd ℂ) ((w k - a q)⁻¹ + (a q)⁻¹))
              / (w j + (starRingEnd ℂ) (w k))
          = ((w j - a q)⁻¹ + (starRingEnd ℂ) ((w k - a q)⁻¹))
              / (w j + (starRingEnd ℂ) (w k)) := by
            rw [map_add]
            congr 1
            linear_combination hcancel
        _ = (w j - a q)⁻¹ * (starRingEnd ℂ) ((w k - a q)⁻¹) := hrk
    rw [hlogj, hlogk]
    have hconjsum : (starRingEnd ℂ) (∑' q : ZeroCopy g, ((w k - a q)⁻¹ + (a q)⁻¹))
        = ∑' q : ZeroCopy g, (starRingEnd ℂ) ((w k - a q)⁻¹ + (a q)⁻¹) :=
      Complex.conjCLE.map_tsum
    rw [map_add, hconjsum]
    have hadd : ((m : ℂ) / w j + ∑' q : ZeroCopy g, ((w j - a q)⁻¹ + (a q)⁻¹)
          + ((starRingEnd ℂ) ((m : ℂ) / w k)
            + ∑' q : ZeroCopy g, (starRingEnd ℂ) ((w k - a q)⁻¹ + (a q)⁻¹)))
        = ((m : ℂ) / w j + (starRingEnd ℂ) ((m : ℂ) / w k))
          + ∑' q : ZeroCopy g, (((w j - a q)⁻¹ + (a q)⁻¹)
              + (starRingEnd ℂ) ((w k - a q)⁻¹ + (a q)⁻¹)) := by
      rw [Summable.tsum_add hsumj hsumkc]
      ring
    rw [hadd, add_div]
    congr 1
    · have hmj : (m : ℂ) / w j = (m : ℂ) * (w j)⁻¹ := by rw [div_eq_mul_inv]
      have hmk : (starRingEnd ℂ) ((m : ℂ) / w k)
          = (m : ℂ) * (starRingEnd ℂ) ((w k)⁻¹) := by
        rw [map_div₀, Complex.conj_natCast, div_eq_mul_inv, map_inv₀]
      have hsq : ((Real.sqrt m : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ) = (m : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg m)]
        norm_num
      rw [hmj, hmk, ← mul_add, mul_div_assoc, hmonokernel, map_mul, Complex.conj_ofReal]
      calc (m : ℂ) * ((w j)⁻¹ * (starRingEnd ℂ) ((w k)⁻¹))
          = (((Real.sqrt m : ℝ) : ℂ) * ((Real.sqrt m : ℝ) : ℂ)) *
              ((w j)⁻¹ * (starRingEnd ℂ) ((w k)⁻¹)) := by rw [hsq]
        _ = ((Real.sqrt m : ℝ) : ℂ) * (w j)⁻¹ *
              (((Real.sqrt m : ℝ) : ℂ) * (starRingEnd ℂ) ((w k)⁻¹)) := by ring
    · rw [div_eq_mul_inv, ← tsum_mul_right]
      refine tsum_congr (fun q => ?_)
      rw [← div_eq_mul_inv]
      exact hterm q
  have hKpsd : K.PosSemidef := by
    have h1 : (Matrix.of fun j k =>
        (((Real.sqrt m : ℝ) : ℂ) * (w j)⁻¹) *
          (starRingEnd ℂ) (((Real.sqrt m : ℝ) : ℂ) * (w k)⁻¹)).PosSemidef :=
      posSemidef_rankOne (fun j => ((Real.sqrt m : ℝ) : ℂ) * (w j)⁻¹)
    have h2 : (Matrix.of fun j k =>
        ∑' q : ZeroCopy g, (w j - a q)⁻¹ * (starRingEnd ℂ) ((w k - a q)⁻¹)).PosSemidef :=
      posSemidef_tsum_rankOne (fun q j => (w j - a q)⁻¹)
        (fun j k => summable_resolvent_pair hane hsum (hwne j) (hwne k))
    have hKeq : K = (Matrix.of fun j k =>
        (((Real.sqrt m : ℝ) : ℂ) * (w j)⁻¹) *
          (starRingEnd ℂ) (((Real.sqrt m : ℝ) : ℂ) * (w k)⁻¹))
        + (Matrix.of fun j k =>
          ∑' q : ZeroCopy g, (w j - a q)⁻¹ * (starRingEnd ℂ) ((w k - a q)⁻¹)) := by
      ext j k
      rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply]
      exact hKsplit j k
    rw [hKeq]
    exact h1.add h2
  -- the diagonal congruence
  have hBeq : (Matrix.of fun j k =>
      (deriv f (w j) * (starRingEnd ℂ) (f (w k)) + f (w j) * (starRingEnd ℂ) (deriv f (w k)))
        / (w j + (starRingEnd ℂ) (w k)))
      = Matrix.of fun j k => f (w j) * K j k * (starRingEnd ℂ) (f (w k)) := by
    ext j k
    rw [Matrix.of_apply, Matrix.of_apply]
    show (deriv f (w j) * (starRingEnd ℂ) (f (w k)) + f (w j) * (starRingEnd ℂ) (deriv f (w k)))
        / (w j + (starRingEnd ℂ) (w k))
      = f (w j) * ((((m : ℂ) / w j + logDeriv P (w j))
        + (starRingEnd ℂ) ((m : ℂ) / w k + logDeriv P (w k)))
        / (w j + (starRingEnd ℂ) (w k))) * (starRingEnd ℂ) (f (w k))
    have hden : w j + (starRingEnd ℂ) (w k) ≠ 0 := add_conj_ne_zero (hw j) (hw k)
    rw [hLf j, hLf k, map_mul]
    field_simp
  rw [hBeq]
  exact posSemidef_congr_diagonal hKpsd (fun j => f (w j))

end RHTower.OrderOneHadamard
