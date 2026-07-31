import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport
import GaloisForLFunctions.RHTower.GammaDampedDirichletSeries

/-!
# Complex phase-damped Möbius Hardy source

Real inward damping and imaginary logarithmic phase are combined in one actual square-summable
Möbius source.  Imaginary displacement is unitary, so the Hilbert norm depends only on the real
part.  Nevertheless, source overlap and Fisher-tangent coefficient recover the full holomorphic
squarefree Euler overlap and Fisher numerator on every safe complex Hardy node.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Complex moving damping: real displacement changes mass, imaginary displacement is a
unitary logarithmic phase. -/
def infiniteMobiusCriticalComplexDampedSignedWeight
    (sigma : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  Complex.exp
      (-((u.im * (sigma - 1) * Real.log n : ℝ) : ℂ) * Complex.I) *
    infiniteMobiusCriticalDampedSignedWeight sigma u.re n

theorem infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp
    (sigma : ℝ) (u : ℂ) (n : ℕ) :
    infiniteMobiusCriticalComplexDampedSignedWeight sigma u n =
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        infiniteMobiusSignedWeight sigma n := by
  rw [infiniteMobiusCriticalComplexDampedSignedWeight,
    infiniteMobiusCriticalDampedSignedWeight, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext
  · simp
    ring
  · simp

theorem norm_infiniteMobiusCriticalComplexDampedSignedWeight
    (sigma : ℝ) (u : ℂ) (n : ℕ) :
    ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma u n‖ =
      ‖infiniteMobiusCriticalDampedSignedWeight sigma u.re n‖ := by
  rw [infiniteMobiusCriticalComplexDampedSignedWeight, norm_mul]
  rw [show
      -((u.im * (sigma - 1) * Real.log n : ℝ) : ℂ) * Complex.I =
        ((-(u.im * (sigma - 1) * Real.log n) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.norm_exp_ofReal_mul_I, one_mul]

theorem norm_infiniteMobiusCriticalComplexDampedSignedWeight_sq
    {sigma : ℝ} (u : ℂ) (hsigma : 1 < sigma) (n : ℕ) :
    ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma u n‖ ^ 2 =
      Real.exp (-(u.re * (sigma - 1) * Real.log n)) ^ 2 *
        squarefreeMobiusProbability sigma n := by
  rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight,
    infiniteMobiusCriticalDampedSignedWeight, norm_mul, mul_pow,
    norm_infiniteMobiusSignedWeight_sq hsigma, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma u n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    (summable_squarefreeMobiusProbability hsigma)
  intro n
  rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight_sq u hsigma]
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hexp : Real.exp (-(u.re * (sigma - 1) * Real.log n)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr
      (mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hsigma.le)) hlog)
  have hexp0 := Real.exp_pos (-(u.re * (sigma - 1) * Real.log n))
  have hsquare : Real.exp (-(u.re * (sigma - 1) * Real.log n)) ^ 2 ≤ 1 := by
    nlinarith
  exact mul_le_of_le_one_left
    (squarefreeMobiusProbability_nonneg hsigma n) hsquare

/-- Complex damping is an actual Hilbert vector whenever its real displacement is inward. -/
def infiniteMobiusCriticalComplexDampedSignedWeightLp
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalComplexDampedSignedWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight hsigma hu)⟩

theorem norm_infiniteMobiusCriticalComplexDampedSignedWeightLp_sq_le_one
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    ‖infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu‖ ^ 2 ≤ 1 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  calc
    (∑' n : ℕ,
        ‖infiniteMobiusCriticalComplexDampedSignedWeight sigma u n‖ ^ 2) ≤
        ∑' n : ℕ, squarefreeMobiusProbability sigma n := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [norm_infiniteMobiusCriticalComplexDampedSignedWeight_sq u hsigma]
        have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
        have hexp :
            Real.exp (-(u.re * (sigma - 1) * Real.log n)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact neg_nonpos.mpr
            (mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hsigma.le)) hlog)
        have hsquare :
            Real.exp (-(u.re * (sigma - 1) * Real.log n)) ^ 2 ≤ 1 := by
          nlinarith [Real.exp_pos
            (-(u.re * (sigma - 1) * Real.log n))]
        exact mul_le_of_le_one_left
          (squarefreeMobiusProbability_nonneg hsigma n) hsquare
      · exact
          summable_norm_sq_infiniteMobiusCriticalComplexDampedSignedWeight
            hsigma hu
      · exact summable_squarefreeMobiusProbability hsigma
    _ = 1 := tsum_squarefreeMobiusProbability hsigma

/-- Uniform Hardy-column bound: imaginary displacement has no cost, in any dimension. -/
theorem norm_infiniteMobiusCriticalComplexDampedSignedWeightLp_le_one
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    ‖infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu‖ ≤ 1 := by
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa only [one_pow] using
    norm_infiniteMobiusCriticalComplexDampedSignedWeightLp_sq_le_one hsigma hu

private theorem complexDamping_mul_squarefreeMobiusMass
    (sigma : ℝ) (u : ℂ) (n : ℕ) :
    Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ) =
      if Squarefree n then
        1 / (n : ℂ) ^
          ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ))
      else 0 := by
  rw [ofReal_squarefreeMobiusMass_eq]
  split_ifs with hsq
  · have hn0 : n ≠ 0 := by
      intro hn
      subst n
      exact not_squarefree_zero hsq
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    rw [Complex.cpow_def_of_ne_zero hnC, Complex.cpow_def_of_ne_zero hnC,
      hlog, div_eq_mul_inv, div_eq_mul_inv, ← Complex.exp_neg,
      ← Complex.exp_neg]
    simp only [one_mul]
    rw [← Complex.exp_add]
    congr 1
    ring
  · simp

private theorem LSeries_logMul_squarefreeCoeff_eq_partition_mul_fixedCurrent
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (LSeries.logMul squarefreeCoeff) s =
      GaloisForLFunctions.squarefreePartition s *
        GaloisForLFunctions.squarefreeFixedCurrent s := by
  have habs :
      LSeries.abscissaOfAbsConv squarefreeCoeff < s.re := by
    exact lt_of_le_of_lt abscissaOfAbsConv_squarefreeCoeff_le
      (by exact_mod_cast hs)
  have hiter := LSeries_iteratedDeriv (f := squarefreeCoeff) 1 habs
  have heq :
      LSeries squarefreeCoeff =ᶠ[nhds s]
        GaloisForLFunctions.squarefreePartition := by
    have hopen : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hopen] with z hz
    simpa [GaloisForLFunctions.squarefreePartition] using
      lSeries_squarefreeCoeff hz
  rw [heq.iteratedDeriv_eq 1] at hiter
  simp only [iteratedDeriv_one, Function.iterate_one] at hiter
  have hnonzero :
      GaloisForLFunctions.squarefreePartition s ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero hs
  have hfixed :=
    GaloisForLFunctions.neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent hs
  rw [logDeriv_apply] at hfixed
  calc
    LSeries (LSeries.logMul squarefreeCoeff) s =
        -deriv GaloisForLFunctions.squarefreePartition s := by
      linear_combination hiter
    _ = GaloisForLFunctions.squarefreePartition s *
          (-(deriv GaloisForLFunctions.squarefreePartition s /
            GaloisForLFunctions.squarefreePartition s)) := by
      field_simp
    _ = GaloisForLFunctions.squarefreePartition s *
          GaloisForLFunctions.squarefreeFixedCurrent s := by
      rw [hfixed]

private theorem tsum_complexDamping_mass_mul_log
    {sigma : ℝ} {u : ℂ}
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    (∑' n : ℕ,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ) *
          ((Real.log n : ℝ) : ℂ)) =
      GaloisForLFunctions.squarefreePartition
          ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)) *
        GaloisForLFunctions.squarefreeFixedCurrent
          ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)) := by
  rw [←
    LSeries_logMul_squarefreeCoeff_eq_partition_mul_fixedCurrent hshift]
  unfold LSeries
  apply tsum_congr
  intro n
  rw [show
    Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ) *
          ((Real.log n : ℝ) : ℂ) =
      (if Squarefree n then
        1 / (n : ℂ) ^
          ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ))
      else 0) * ((Real.log n : ℝ) : ℂ) by
        rw [complexDamping_mul_squarefreeMobiusMass]]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [not_squarefree_zero, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.logMul, squarefreeCoeff]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    rw [hlog]
    split_ifs <;> ring

private theorem summable_complexDamping_mass
    {sigma : ℝ} {u : ℂ}
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    Summable (fun n : ℕ =>
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ)) := by
  have habs :
      LSeries.abscissaOfAbsConv squarefreeCoeff <
        ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re :=
    lt_of_le_of_lt abscissaOfAbsConv_squarefreeCoeff_le
      (by exact_mod_cast hshift)
  have hsum :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re habs
  unfold LSeriesSummable at hsum
  apply hsum.congr
  intro n
  rw [complexDamping_mul_squarefreeMobiusMass]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [not_squarefree_zero, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, squarefreeCoeff]
    split_ifs <;> ring

private theorem summable_complexDamping_mass_mul_log
    {sigma : ℝ} {u : ℂ}
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    Summable (fun n : ℕ =>
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ) *
          ((Real.log n : ℝ) : ℂ)) := by
  have habs :
      LSeries.abscissaOfAbsConv squarefreeCoeff <
        ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re :=
    lt_of_le_of_lt abscissaOfAbsConv_squarefreeCoeff_le
      (by exact_mod_cast hshift)
  have hsum :=
    LSeriesSummable_logMul_of_lt_re habs
  unfold LSeriesSummable at hsum
  apply hsum.congr
  intro n
  rw [complexDamping_mul_squarefreeMobiusMass]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [not_squarefree_zero, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.logMul, squarefreeCoeff]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
    rw [hlog]
    split_ifs <;> ring

private theorem tsum_complexDamping_mass
    {sigma : ℝ} {u : ℂ}
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    (∑' n : ℕ,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ)) =
      GaloisForLFunctions.squarefreePartition
        ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)) := by
  rw [show (∑' n : ℕ,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
        (squarefreeMobiusMass sigma n : ℂ)) =
      ∑' n : ℕ,
        if Squarefree n then
          1 / (n : ℂ) ^
            ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ))
        else 0 by
    apply tsum_congr
    intro n
    exact complexDamping_mul_squarefreeMobiusMass sigma u n]
  exact tsum_squarefree_cpow hshift

/-- The complex phase-damped source overlap is the full holomorphic squarefree Euler overlap.
Imaginary displacement is carried by a unitary logarithmic phase, so no new norm cost occurs. -/
theorem inner_infiniteMobiusSignedWeight_complexDamped_eq_squarefreeBoundaryOverlap
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    inner ℂ (infiniteMobiusSignedWeightLp sigma hsigma)
        (infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu) =
      GaloisForLFunctions.squarefreeBoundaryOverlap
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusSignedWeightLp,
    infiniteMobiusCriticalComplexDampedSignedWeightLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ,
      infiniteMobiusCriticalComplexDampedSignedWeight sigma u n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
      ∑' n : ℕ,
        (if Squarefree n then
          1 / (n : ℂ) ^
            ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ))
        else 0) / (squarefreeMobiusTotal sigma : ℂ) by
    apply tsum_congr
    intro n
    rw [infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp]
    have hnorm : infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_infiniteMobiusSignedWeight_sq hsigma]
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
          infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) * ((Real.log n : ℝ) : ℂ)) *
          (infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) by ring,
      hnorm, squarefreeMobiusProbability, Complex.ofReal_div]
    rw [← mul_div_assoc,
      complexDamping_mul_squarefreeMobiusMass]]
  rw [tsum_div_const,
    tsum_squarefree_cpow hshift,
    ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
  rfl

/-- The same complex phase-damped Hilbert source reports the full holomorphic squarefree Fisher
numerator, not merely its restriction to real inward rays. -/
theorem inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalComplexDampedSignedWeightLp sigma u hsigma hu) =
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) u := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusCriticalFisherTangentLp,
    infiniteMobiusCriticalComplexDampedSignedWeightLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ,
      infiniteMobiusCriticalComplexDampedSignedWeight sigma u n *
        (starRingEnd ℂ)
          (infiniteMobiusCriticalFisherTangentWeight sigma n)) =
      ((-2 * (sigma - 1 : ℝ) : ℝ) : ℂ) /
          (squarefreeMobiusTotal sigma : ℂ) *
        ∑' n : ℕ,
          (Complex.exp
                (-u * ((sigma - 1 : ℝ) : ℂ) *
                  ((Real.log n : ℝ) : ℂ)) *
              (squarefreeMobiusMass sigma n : ℂ) *
                ((Real.log n : ℝ) : ℂ) -
            ((squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ) *
              (Complex.exp
                  (-u * ((sigma - 1 : ℝ) : ℂ) *
                    ((Real.log n : ℝ) : ℂ)) *
                (squarefreeMobiusMass sigma n : ℂ))) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [infiniteMobiusCriticalComplexDampedSignedWeight_eq_exp,
      infiniteMobiusCriticalFisherTangentWeight]
    simp only [map_mul, conj_ofReal]
    have hnorm : infiniteMobiusSignedWeight sigma n *
        (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
        (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_infiniteMobiusSignedWeight_sq hsigma]
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log n : ℝ) : ℂ)) *
          infiniteMobiusSignedWeight sigma n *
          (((-2 * (sigma - 1) *
              (Real.log n - squarefreeMobiusLogMoment 1 sigma) : ℝ) : ℂ) *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
        ((-2 * (sigma - 1) : ℝ) : ℂ) *
          (Complex.exp
              (-u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log n : ℝ) : ℂ)) *
            (infiniteMobiusSignedWeight sigma n *
              (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) *
            (((Real.log n -
              squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ))) by
        push_cast
        ring,
      hnorm, squarefreeMobiusProbability, Complex.ofReal_div]
    push_cast
    ring]
  have hlog :=
    summable_complexDamping_mass_mul_log (sigma := sigma) (u := u) hshift
  have hmass :=
    summable_complexDamping_mass (sigma := sigma) (u := u) hshift
  have hsigmaC : 1 < (sigma : ℂ).re := by
    simpa using hsigma
  have htotal :
      (squarefreeMobiusTotal sigma : ℂ) =
        GaloisForLFunctions.squarefreePartition (sigma : ℂ) := by
    rw [ofReal_squarefreeMobiusTotal_eq_zetaRatio hsigma]
    rfl
  have hbase :
      GaloisForLFunctions.squarefreePartition (sigma : ℂ) ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero hsigmaC
  rw [hlog.tsum_sub (hmass.mul_left
      ((squarefreeMobiusLogMoment 1 sigma : ℝ) : ℂ)),
    tsum_mul_left,
    tsum_complexDamping_mass_mul_log hshift,
    tsum_complexDamping_mass hshift,
    htotal,
    ofReal_squarefreeMobiusLogMoment_one_eq_fixedCurrent hsigma,
    GaloisForLFunctions.squarefreeFisherScore_eq_fixedCurrent_difference
      hsigmaC hshift]
  simp only [GaloisForLFunctions.squarefreeBoundaryOverlap]
  field_simp [hbase]
  push_cast
  ring

/-- At every safe complex Hardy node, the actual complex phase-damped Hilbert coefficient feeds
the singular Gamma transport and reconstructs the completed squarefree logarithmic current. -/
theorem squarefreeMobiusGammaCurrentTransportV_actualComplexNode
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    squarefreeMobiusGammaCurrentTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (fun _ =>
          inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma u hsigma hu))
        u =
      GaloisForLFunctions.completedSquarefreeFixedCurrent
        ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)) := by
  have hsigmaC : 1 < (sigma : ℂ).re := by
    simpa using hsigma
  have hepsilon : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  rw [← squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent
    hsigmaC hshift hepsilon]
  unfold squarefreeMobiusGammaCurrentTransportV
  rw [inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
    hsigma hu hshift]

/-- The actual complex Hardy-node coefficient also feeds the full Gamma/Xi weld. -/
theorem squarefreeMobiusGammaXiWardTransportV_actualComplexNode
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (hshift :
      1 < ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)).re) :
    squarefreeMobiusGammaXiWardTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (fun _ =>
          inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalComplexDampedSignedWeightLp
              sigma u hsigma hu))
        u =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          ((sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ))) := by
  have hsigmaC : 1 < (sigma : ℂ).re := by
    simpa using hsigma
  have hepsilon : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  rw [← squarefreeMobiusGammaXiWardTransportV_eq_continuedSource
    hsigmaC hshift hepsilon]
  unfold squarefreeMobiusGammaXiWardTransportV
  unfold squarefreeMobiusGammaCurrentTransportV
  rw [inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
    hsigma hu hshift]

end RHTower
