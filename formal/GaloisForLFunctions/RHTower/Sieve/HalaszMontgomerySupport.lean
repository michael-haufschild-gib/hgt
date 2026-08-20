import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryIntegral
import GaloisForLFunctions.RHTower.Sieve.LogPolyRestrict
import GaloisForLFunctions.RHTower.Sieve.LowHeightPoly

/-!
# The integral Halász–Montgomery bound with a restricted support

`Sieve/HalaszMontgomeryIntegral` bounds the mean square of a Dirichlet polynomial of length `N` by
the row mass of the kernel `∑_{n < N} n^{iv}`.  When the coefficients are supported on a sparse set
— for Matomäki–Radziwiłł's exceptional half, on the *primes* of a range — that kernel is far larger
than the one the duality actually produces: only the frequencies in the support occur, so the kernel
is `∑_{n ∈ S} n^{iv}`, whose value at `v = 0` is `#S` rather than `N`.

For a prime support that is a gain of a full logarithm, twice: once in the kernel and once in the
coefficient energy.  It is exactly the difference between Matomäki–Radziwiłł's Lemma 9 (integers)
and Lemma 11 (primes), and it is what makes the exceptional half of their argument work.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The logarithmic-phase kernel of a restricted support. -/
def supportKernel {N : ℕ} (S : Finset (Fin N)) (v : ℝ) : ℂ :=
  ∑ n ∈ S, Complex.exp (((v * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)

theorem continuous_supportKernel {N : ℕ} (S : Finset (Fin N)) : Continuous (supportKernel S) :=
  continuous_finsetSum _ fun _ _ => continuous_phase _

/-- The duality identity, with the sum restricted to the support. -/
theorem setIntegral_normSq_dirPoly_eq_dual_support {N : ℕ} (a : Fin N → ℂ)
    (S : Finset (Fin N)) (ha : ∀ n, n ∉ S → a n = 0) {T : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    ((∫ t in E, ‖dirPoly N a t‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ S, a n * dualCoeff N a E n := by
  rw [setIntegral_normSq_dirPoly_eq_dual a hE hEs]
  refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
  intro n _ hn
  rw [ha n hn, zero_mul]

/-- Cauchy–Schwarz over the support. -/
theorem setIntegral_normSq_dirPoly_sq_le_support {N : ℕ} (a : Fin N → ℂ)
    (S : Finset (Fin N)) (ha : ∀ n, n ∉ S → a n = 0) {T : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    (∫ t in E, ‖dirPoly N a t‖ ^ 2) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2) * ∑ n ∈ S, ‖dualCoeff N a E n‖ ^ 2 := by
  classical
  have hid := setIntegral_normSq_dirPoly_eq_dual_support a S ha hE hEs
  have habs : |∫ t in E, ‖dirPoly N a t‖ ^ 2|
      ≤ ∑ n ∈ S, ‖a n‖ * ‖dualCoeff N a E n‖ := by
    have h1 : ‖((∫ t in E, ‖dirPoly N a t‖ ^ 2 : ℝ) : ℂ)‖
        ≤ ∑ n ∈ S, ‖a n * dualCoeff N a E n‖ := by
      rw [hid]
      exact norm_sum_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    simpa only [norm_mul] using h1
  have hcs : (∑ n ∈ S, ‖a n‖ * ‖dualCoeff N a E n‖) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2) * ∑ n ∈ S, ‖dualCoeff N a E n‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsq : (∫ t in E, ‖dirPoly N a t‖ ^ 2) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ * ‖dualCoeff N a E n‖) ^ 2 := by
    have := abs_nonneg (∫ t in E, ‖dirPoly N a t‖ ^ 2)
    nlinarith [habs, sq_abs (∫ t in E, ‖dirPoly N a t‖ ^ 2)]
  linarith [hsq, hcs]

/-- **The dual energy over the support is the restricted-kernel double integral.** -/
theorem sum_normSq_dualCoeff_support_eq {N : ℕ} (a : Fin N → ℂ) (S : Finset (Fin N))
    {T : ℝ} {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) :
    ((∑ n ∈ S, ‖dualCoeff N a E n‖ ^ 2 : ℝ) : ℂ)
      = ∫ t in E, ∫ u in E, supportKernel S (t - u)
          * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u := by
  classical
  have hcA : Continuous (dirPoly N a) := continuous_dirPoly N a
  have hcconj : Continuous fun t : ℝ => (starRingEnd ℂ) (dirPoly N a t) :=
    Complex.continuous_conj.comp hcA
  have hint : ∀ g : ℝ → ℂ, Continuous g → IntegrableOn g E := fun g hg =>
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  set d : Fin N → ℂ := fun n =>
    ∫ u in E, Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      * dirPoly N a u with hd
  have hinner : ∀ t : ℝ, (∫ u in E, supportKernel S (t - u)
        * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u)
      = ∑ n ∈ S, (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t)) * d n := by
    intro t
    have hsplit : ∀ u : ℝ, supportKernel S (t - u)
          * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u
        = ∑ n ∈ S, (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
            * (starRingEnd ℂ) (dirPoly N a t))
            * (Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
              * dirPoly N a u) := by
      intro u
      rw [supportKernel, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hprod : Complex.exp ((((t - u) * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hprod]
      ring
    rw [MeasureTheory.setIntegral_congr_fun hEm fun u _ => hsplit u]
    have hswap := MeasureTheory.integral_finsetSum
      (μ := volume.restrict E) (s := S)
      (f := fun n u => (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
          * (starRingEnd ℂ) (dirPoly N a t))
          * (Complex.exp (((-u * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) * dirPoly N a u))
      (fun n _ => hint _ (continuous_const.mul
        (((continuous_phase (Real.log ((n : ℕ) + 1))).comp continuous_neg).mul hcA)))
    rw [hswap, hd]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.setIntegral_congr_fun hEm fun t _ => hinner t]
  have hswap2 := MeasureTheory.integral_finsetSum
    (μ := volume.restrict E) (s := S)
    (f := fun n t => (Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
        * (starRingEnd ℂ) (dirPoly N a t)) * d n)
    (fun n _ => hint _ (((continuous_phase (Real.log ((n : ℕ) + 1))).mul hcconj).mul
      continuous_const))
  rw [hswap2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hconj_e : ∀ s : ℝ,
      (starRingEnd ℂ) (Complex.exp (((s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
        = Complex.exp (((-s * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    intro s
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hdconj : d n = (starRingEnd ℂ) (dualCoeff N a E n) := by
    rw [hd, dualCoeff, ← integral_conj]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [map_mul, hconj_e u, Complex.conj_conj]
  have hc : (∫ t in E, Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)
      * (starRingEnd ℂ) (dirPoly N a t)) = dualCoeff N a E n := rfl
  rw [MeasureTheory.integral_mul_const, hc, hdconj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- **The integral Halász–Montgomery bound for a restricted support.**  Only the kernel of the
support enters — for prime-supported coefficients this is Matomäki–Radziwiłł's Lemma 11 in integral
form. -/
theorem setIntegral_normSq_dirPoly_le_HM_support {N : ℕ} (a : Fin N → ℂ) (S : Finset (Fin N))
    (ha : ∀ n, n ∉ S → a n = 0) {T M : ℝ} {E : Set ℝ}
    (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T)
    (hrow : ∀ t ∈ E, (∫ u in E, ‖supportKernel S (t - u)‖) ≤ M)
    (hcol : ∀ u ∈ E, (∫ t in E, ‖supportKernel S (t - u)‖) ≤ M) (hM0 : 0 ≤ M) :
    (∫ t in E, ‖dirPoly N a t‖ ^ 2) ≤ M * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  have hI0 : (0 : ℝ) ≤ ∫ t in E, ‖dirPoly N a t‖ ^ 2 :=
    MeasureTheory.setIntegral_nonneg hEm fun t _ => sq_nonneg _
  have hE0 : (0 : ℝ) ≤ ∑ n ∈ S, ‖a n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := setIntegral_normSq_dirPoly_sq_le_support a S ha hEm hEs
  have hdual : (∑ n ∈ S, ‖dualCoeff N a E n‖ ^ 2)
      = ‖∫ t in E, ∫ u in E, supportKernel S (t - u)
          * (starRingEnd ℂ) (dirPoly N a t) * dirPoly N a u‖ := by
    have hid := sum_normSq_dualCoeff_support_eq a S hEm hEs
    have hnn : (0 : ℝ) ≤ ∑ n ∈ S, ‖dualCoeff N a E n‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  have h3 := setIntegral_double_kernel_le (A := dirPoly N a) (K := supportKernel S)
    (continuous_dirPoly N a) (continuous_supportKernel S) hEs hEm hrow hcol
  rw [← hdual] at h3
  have hsq : (∫ t in E, ‖dirPoly N a t‖ ^ 2) ^ 2
      ≤ (∑ n ∈ S, ‖a n‖ ^ 2) * (M * ∫ t in E, ‖dirPoly N a t‖ ^ 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h3 hE0)
  rcases eq_or_lt_of_le hI0 with heq | hpos
  · rw [← heq]
    positivity
  · nlinarith [hsq, hpos]

end

end RHTower.Sieve

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The kernel is bounded by the size of the support. -/
theorem norm_supportKernel_le_card {N : ℕ} (S : Finset (Fin N)) (v : ℝ) :
    ‖supportKernel S v‖ ≤ (S.card : ℝ) := by
  rw [supportKernel]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ S,
      ‖Complex.exp (((v * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I)‖ = 1 := fun n _ => by
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem measurableSet_farSet (t v₀ : ℝ) : MeasurableSet {u : ℝ | v₀ ≤ |t - u|} := by
  have hcont : Continuous fun u : ℝ => |t - u| := (continuous_const.sub continuous_id).abs
  exact measurableSet_le measurable_const hcont.measurable

/-- **The row mass of a support kernel from a two-regime bound.**  Near the diagonal the kernel is
bounded by the size of the support; away from it, by whatever cancellation is available.  This is
the shape in which the Route-T twisted prime sum
(`Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le`) enters the exceptional half. -/
theorem setIntegral_norm_supportKernel_le {N : ℕ} (S : Finset (Fin N)) {E : Set ℝ} {T v₀ G : ℝ}
    (hEs : E ⊆ Set.Icc (-T) T) (hT : 0 ≤ T) (hv₀ : 0 ≤ v₀) (hG : 0 ≤ G)
    (hfar : ∀ v : ℝ, v₀ ≤ |v| → ‖supportKernel S v‖ ≤ G) (t : ℝ) :
    (∫ u in E, ‖supportKernel S (t - u)‖) ≤ 2 * v₀ * (S.card : ℝ) + 2 * T * G := by
  classical
  set F : Set ℝ := {u : ℝ | v₀ ≤ |t - u|} with hFdef
  have hFm : MeasurableSet F := measurableSet_farSet t v₀
  have hcont : Continuous fun u : ℝ => ‖supportKernel S (t - u)‖ :=
    ((continuous_supportKernel S).comp (continuous_const.sub continuous_id)).norm
  have hintOn : IntegrableOn (fun u : ℝ => ‖supportKernel S (t - u)‖) E :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set hEs
  have hEfin : volume E < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hEs) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hsplit := integral_inter_add_sdiff (μ := volume) hFm hintOn
  -- the far part
  have hmEF : volume.real (E ∩ F) ≤ 2 * T := by
    have h1 : volume (E ∩ F) ≤ volume (Set.Icc (-T) T) :=
      measure_mono (Set.inter_subset_left.trans hEs)
    rw [Real.volume_Icc] at h1
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by linarith)] at h2
    have : T - -T = 2 * T := by ring
    rw [this] at h2
    exact h2
  have hAfin : volume (E ∩ F) < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_left) hEfin
  have hA : (∫ u in E ∩ F, ‖supportKernel S (t - u)‖) ≤ 2 * T * G := by
    have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E ∩ F)
      (f := fun u : ℝ => ‖supportKernel S (t - u)‖) (C := G) hAfin
      (fun u hu => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hfar _ hu.2)
    have hle : (∫ u in E ∩ F, ‖supportKernel S (t - u)‖)
        ≤ ‖∫ u in E ∩ F, ‖supportKernel S (t - u)‖‖ := le_abs_self _
    have hstep : G * volume.real (E ∩ F) ≤ G * (2 * T) :=
      mul_le_mul_of_nonneg_left hmEF hG
    calc (∫ u in E ∩ F, ‖supportKernel S (t - u)‖)
        ≤ ‖∫ u in E ∩ F, ‖supportKernel S (t - u)‖‖ := hle
      _ ≤ G * volume.real (E ∩ F) := hnorm
      _ ≤ G * (2 * T) := hstep
      _ = 2 * T * G := by ring
  -- the near part
  have hmEd : volume.real (E \ F) ≤ 2 * v₀ := by
    have hsub : E \ F ⊆ Set.Icc (t - v₀) (t + v₀) := by
      intro u hu
      have hlt : |t - u| < v₀ := lt_of_not_ge hu.2
      have habs := abs_lt.1 hlt
      exact ⟨by linarith [habs.2], by linarith [habs.1]⟩
    have h1 : volume (E \ F) ≤ volume (Set.Icc (t - v₀) (t + v₀)) := measure_mono hsub
    rw [Real.volume_Icc] at h1
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by linarith)] at h2
    have heq : t + v₀ - (t - v₀) = 2 * v₀ := by ring
    rw [heq] at h2
    exact h2
  have hDfin : volume (E \ F) < ⊤ := lt_of_le_of_lt (measure_mono Set.sdiff_subset) hEfin
  have hcard0 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hB : (∫ u in E \ F, ‖supportKernel S (t - u)‖) ≤ 2 * v₀ * (S.card : ℝ) := by
    have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E \ F)
      (f := fun u : ℝ => ‖supportKernel S (t - u)‖) (C := (S.card : ℝ)) hDfin
      (fun u _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_supportKernel_le_card S _)
    have hle : (∫ u in E \ F, ‖supportKernel S (t - u)‖)
        ≤ ‖∫ u in E \ F, ‖supportKernel S (t - u)‖‖ := le_abs_self _
    have hstep : (S.card : ℝ) * volume.real (E \ F) ≤ (S.card : ℝ) * (2 * v₀) :=
      mul_le_mul_of_nonneg_left hmEd hcard0
    calc (∫ u in E \ F, ‖supportKernel S (t - u)‖)
        ≤ ‖∫ u in E \ F, ‖supportKernel S (t - u)‖‖ := hle
      _ ≤ (S.card : ℝ) * volume.real (E \ F) := hnorm
      _ ≤ (S.card : ℝ) * (2 * v₀) := hstep
      _ = 2 * v₀ * (S.card : ℝ) := by ring
  linarith [hsplit, hA, hB]

end

end RHTower.Sieve


namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The kernel conjugates under frequency reversal. -/
theorem supportKernel_neg {N : ℕ} (S : Finset (Fin N)) (v : ℝ) :
    supportKernel S (-v) = (starRingEnd ℂ) (supportKernel S v) := by
  rw [supportKernel, supportKernel, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem norm_supportKernel_neg {N : ℕ} (S : Finset (Fin N)) (v : ℝ) :
    ‖supportKernel S (-v)‖ = ‖supportKernel S v‖ := by
  rw [supportKernel_neg, RCLike.norm_conj]

/-- The `Fin`-indexed support attached to a set of integers below the cutoff. -/
def finSupport (B : Finset ℕ) (N : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun n : Fin N => (n : ℕ) + 1 ∈ B)

/-- **The support kernel is the Dirichlet polynomial of the indicator.** -/
theorem supportKernel_eq_dirPoly (B : Finset ℕ) (N : ℕ) (v : ℝ) :
    supportKernel (finSupport B N) v
      = dirPoly N (fun n : Fin N => restrictCoeff B (fun _ => (1 : ℂ)) ((n : ℕ) + 1)) v := by
  classical
  rw [supportKernel, dirPoly, finSupport, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [restrictCoeff]
  by_cases hn : (n : ℕ) + 1 ∈ B
  · rw [if_pos hn, if_pos hn, one_mul]
  · rw [if_neg hn, if_neg hn, zero_mul]

/-- **The support kernel is the Gallagher polynomial of the constant one.** -/
theorem supportKernel_eq_logPoly_one {B : Finset ℕ} {N : ℕ} (hB : B ⊆ Finset.Icc 1 N) (v : ℝ) :
    supportKernel (finSupport B N) v = logPoly (fun _ => (1 : ℂ)) B (v / (2 * Real.pi)) := by
  have h := logPoly_subset_eq_dirPoly (fun _ => (1 : ℂ)) hB (v / (2 * Real.pi))
  rw [supportKernel_eq_dirPoly B N v, h]
  congr 1
  field_simp

/-- **The support kernel is the phase sum over the range.**  No arithmetic hypothesis: for a range
of primes the right-hand side is minus the prime polynomial, which is the form the Route-T twisted
prime sum bounds. -/
theorem supportKernel_eq_sum_unitLogPhase {B : Finset ℕ} {N : ℕ} (hB : B ⊆ Finset.Icc 1 N)
    (v : ℝ) :
    supportKernel (finSupport B N) v = ∑ p ∈ B, unitLogPhase (v / (2 * Real.pi)) p := by
  rw [supportKernel_eq_logPoly_one hB v, logPoly]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [one_mul, unitLogPhase]

/-- **The integral Halász–Montgomery bound with the far-field of the phase sum supplied.**  For a
range of primes the kernel is the range's prime polynomial, so its far-field bound is the Route-T
twisted prime sum, and the diagonal is the number of primes rather than the length. -/
theorem setIntegral_normSq_dirPoly_le_HM_phaseSupport {N : ℕ} (a : Fin N → ℂ) {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 N)
    (ha : ∀ n, n ∉ finSupport B N → a n = 0) {T v₀ G : ℝ} {E : Set ℝ}
    (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-T) T) (hT : 0 ≤ T) (hv₀ : 0 ≤ v₀) (hG : 0 ≤ G)
    (hfar : ∀ v : ℝ, v₀ ≤ |v| →
      ‖∑ p ∈ B, unitLogPhase (v / (2 * Real.pi)) p‖ ≤ G) :
    (∫ t in E, ‖dirPoly N a t‖ ^ 2)
      ≤ (2 * v₀ * ((finSupport B N).card : ℝ) + 2 * T * G)
          * ∑ n ∈ finSupport B N, ‖a n‖ ^ 2 := by
  have hfar' : ∀ v : ℝ, v₀ ≤ |v| → ‖supportKernel (finSupport B N) v‖ ≤ G := by
    intro v hv
    rw [supportKernel_eq_sum_unitLogPhase hB v]
    exact hfar v hv
  have hM0 : (0 : ℝ) ≤ 2 * v₀ * ((finSupport B N).card : ℝ) + 2 * T * G := by positivity
  refine setIntegral_normSq_dirPoly_le_HM_support a (finSupport B N) ha hEm hEs ?_ ?_ hM0
  · exact fun t _ => setIntegral_norm_supportKernel_le (finSupport B N) hEs hT hv₀ hG hfar' t
  · intro u _
    have hrow := setIntegral_norm_supportKernel_le (finSupport B N) hEs hT hv₀ hG hfar' u
    refine le_trans (le_of_eq ?_) hrow
    refine MeasureTheory.setIntegral_congr_fun hEm fun t _ => ?_
    rw [show t - u = -(u - t) by ring, norm_supportKernel_neg]

end

end RHTower.Sieve
