import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarGramTransport
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement

/-!
# Actual-source admission of the full signed prime–polar pairing

A source-derived cutoff controls the autocorrelation and every right-annular
average, independently of the annulus parameters. The literal infinite atom
sequence has finite support and is absolutely summable. All polar and Chebyshev
work terms are integrable on the half-line, not merely totalized integrals.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

private def supportRadius (f : C_c(ℝ, ℝ)) : ℝ :=
  Classical.choose (exists_pos_autocorr_support_radius f.hasCompactSupport)

/-- A cutoff depending only on the actual source, not on its annular transport. -/
def sourceCutoff (f : C_c(ℝ, ℝ)) : ℕ := ⌈Real.exp (supportRadius f)⌉₊

theorem cutoff_mono : Monotone cutoff := by
  intro N M hNM
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hNM 2)

/-- The chosen logarithmic endpoint lies strictly beyond the correlation support. -/
theorem autocorr_eq_zero_of_sourceCutoff_le (f : C_c(ℝ, ℝ)) {x : ℝ}
    (hx : cutoff (sourceCutoff f) ≤ x) : autocorr f x = 0 := by
  have hD : supportRadius f < cutoff (sourceCutoff f) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    have hc : Real.exp (supportRadius f) ≤ (sourceCutoff f : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  apply (Classical.choose_spec (exists_pos_autocorr_support_radius f.hasCompactSupport)).2
  exact hD.trans_le (hx.trans (le_abs_self x))

/-- Every positive right-annular average shares the same upper support cutoff. -/
theorem correlationAverage_eq_zero_of_sourceCutoff_le (f : C_c(ℝ, ℝ))
    (a b : ℝ) {x : ℝ} (hx : cutoff (sourceCutoff f) ≤ x) :
    correlationAverage f a b x = 0 := by
  have hab : Real.exp a ≤ Real.exp a + Real.exp b := le_add_of_nonneg_right (Real.exp_pos b).le
  rw [correlationAverage, annularAverage_eq_shift, intervalIntegral.integral_of_le hab]
  have hi : (∫ y in Ioc (Real.exp a) (Real.exp a + Real.exp b), autocorr f (x + y)) = 0 := by
    calc
      _ = ∫ _y in Ioc (Real.exp a) (Real.exp a + Real.exp b), (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro y hy
        apply autocorr_eq_zero_of_sourceCutoff_le f
        linarith [Real.exp_pos a, hy.1]
      _ = 0 := integral_zero _ _
  change (∫ y in Ioc (Real.exp a) (Real.exp a + Real.exp b), autocorr f (x + y)) / Real.exp b = 0
  rw [hi, zero_div]

theorem correlationAverageSlope_eq_zero_of_sourceCutoff_le (f : C_c(ℝ, ℝ))
    (a b : ℝ) {x : ℝ} (hx : cutoff (sourceCutoff f) ≤ x) :
    correlationAverageSlope f a b x = 0 := by
  unfold correlationAverageSlope
  rw [autocorr_eq_zero_of_sourceCutoff_le f (by linarith [Real.exp_pos a, Real.exp_pos b]),
    autocorr_eq_zero_of_sourceCutoff_le f (by linarith [Real.exp_pos a]), sub_self, zero_div]

/-- The literal atom sequence starts at n=2. -/
def primeTerm (H : ℝ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then primeWeight n * H (Real.log n) else 0

/-- Literal infinite prime measure minus the full positive-half-line polar integral. -/
def fullPairing (H : ℝ → ℝ) : ℝ :=
  (∑' n : ℕ, primeTerm H n) - ∫ x in Ici (0 : ℝ), polarDensity x * H x

private theorem primeTerm_tail (H : ℝ → ℝ) (N : ℕ)
    (ht : ∀ x, cutoff N ≤ x → H x = 0) (n : ℕ) (hn : n ∉ Finset.Icc 2 (N+2)) :
    primeTerm H n = 0 := by
  by_cases h2 : 2 ≤ n
  · have hN : N+2 < n := by simp only [Finset.mem_Icc] at hn; omega
    have hlog : cutoff N ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hN.le)
    simp only [primeTerm, if_pos h2, ht _ hlog, mul_zero]
  · simp only [primeTerm, if_neg h2]

/-- Finite atom support follows from an actual upper tail bound. -/
theorem primeTerm_finiteSupport_of_tail (H : ℝ → ℝ) (N : ℕ)
    (ht : ∀ x, cutoff N ≤ x → H x = 0) : (Function.support (primeTerm H)).Finite := by
  apply (Finset.finite_toSet (Finset.Icc 2 (N+2))).subset
  intro n hn
  by_contra hout
  exact hn (primeTerm_tail H N ht n hout)

private theorem summable_abs_primeTerm_of_tail (H : ℝ → ℝ) (N : ℕ)
    (ht : ∀ x, cutoff N ≤ x → H x = 0) : Summable (fun n => |primeTerm H n|) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 2 (N+2))
  intro n hn
  rw [primeTerm_tail H N ht n hn, abs_zero]

theorem summable_abs_primeTerm_autocorr (f : C_c(ℝ, ℝ)) :
    Summable (fun n => |primeTerm (autocorr f) n|) :=
  summable_abs_primeTerm_of_tail _ (sourceCutoff f)
    (fun _ hx => autocorr_eq_zero_of_sourceCutoff_le f hx)

theorem summable_abs_primeTerm_average (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Summable (fun n => |primeTerm (correlationAverage f a b) n|) :=
  summable_abs_primeTerm_of_tail _ (sourceCutoff f)
    (fun _ hx => correlationAverage_eq_zero_of_sourceCutoff_le f a b hx)

/-- Finite-window integrability plus an actual zero tail admits a half-line integral. -/
theorem integrableOn_halfLine_of_tail (q : ℝ → ℝ) (N : ℕ)
    (hi : IntegrableOn q (Icc 0 (cutoff N)))
    (ht : ∀ x, cutoff N ≤ x → q x = 0) : IntegrableOn q (Ici 0) := by
  apply hi.of_forall_sdiff_eq_zero measurableSet_Ici
  intro x hx
  apply ht
  by_contra! hn
  exact hx.2 ⟨hx.1, hn.le⟩

/-- The actual zero tail makes the half-line integral equal to its finite truncation. -/
theorem integral_halfLine_eq_of_tail (q : ℝ → ℝ) (N : ℕ)
    (ht : ∀ x, cutoff N ≤ x → q x = 0) :
    (∫ x in Ici (0 : ℝ), q x) = ∫ x in Icc 0 (cutoff N), q x := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
    (fun _ hx => hx.1)
  intro x hx
  apply ht
  by_contra! hn
  exact hx.2 ⟨hx.1, hn.le⟩

theorem integrableOn_polar_autocorr (f : C_c(ℝ, ℝ)) :
    IntegrableOn (fun x => polarDensity x * autocorr f x) (Ici 0) := by
  apply integrableOn_halfLine_of_tail (fun x => polarDensity x * autocorr f x) (sourceCutoff f)
    ((continuous_polarDensity.mul (continuous_autocorr_compact f)).integrableOn_Icc)
  intro x hx
  rw [autocorr_eq_zero_of_sourceCutoff_le f hx, mul_zero]

theorem integrableOn_polar_average (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    IntegrableOn (fun x => polarDensity x * correlationAverage f a b x) (Ici 0) := by
  apply integrableOn_halfLine_of_tail (fun x => polarDensity x * correlationAverage f a b x)
    (sourceCutoff f)
    ((continuous_polarDensity.mul (continuous_correlationAverage f a b)).integrableOn_Icc)
  intro x hx
  rw [correlationAverage_eq_zero_of_sourceCutoff_le f a b hx, mul_zero]

/-- The literal original-source pairing has finite atom support, absolute convergence,
and an integrable polar term, all derived from the source. -/
theorem autocorr_fullPairing_admissible (f : C_c(ℝ, ℝ)) :
    (Function.support (primeTerm (autocorr f))).Finite ∧
      Summable (fun n => |primeTerm (autocorr f) n|) ∧
      IntegrableOn (fun x => polarDensity x * autocorr f x) (Ici 0) :=
  ⟨primeTerm_finiteSupport_of_tail _ (sourceCutoff f)
    (fun _ hx => autocorr_eq_zero_of_sourceCutoff_le f hx),
    summable_abs_primeTerm_autocorr f, integrableOn_polar_autocorr f⟩

/-- Annular transport preserves automatic admission to the full signed pairing. -/
theorem average_fullPairing_admissible (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (Function.support (primeTerm (correlationAverage f a b))).Finite ∧
      Summable (fun n => |primeTerm (correlationAverage f a b) n|) ∧
      IntegrableOn (fun x => polarDensity x * correlationAverage f a b x) (Ici 0) :=
  ⟨primeTerm_finiteSupport_of_tail _ (sourceCutoff f)
    (fun _ hx => correlationAverage_eq_zero_of_sourceCutoff_le f a b hx),
    summable_abs_primeTerm_average f a b, integrableOn_polar_average f a b⟩

/-- Half-line and finite-window signed pairings agree once the actual tail vanishes. -/
theorem fullPairing_eq_pairing_of_tail (H : ℝ → ℝ) (N : ℕ)
    (ht : ∀ x, cutoff N ≤ x → H x = 0) : fullPairing H = pairing N H := by
  have hs : (∑' n, primeTerm H n) =
      ∑ n ∈ Finset.Icc 2 (N+2), primeWeight n * H (Real.log n) := by
    rw [tsum_eq_sum (primeTerm_tail H N ht)]
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (Finset.mem_Icc.mp hn).1
  have hi := integral_halfLine_eq_of_tail (fun x => polarDensity x * H x) N
    (fun x hx => by rw [ht x hx, mul_zero])
  rw [fullPairing, hs, hi, pairing_eq_literal]
  rfl

/-- Exact stabilization of the original full signed pairing at every larger source cutoff. -/
theorem fullPairing_autocorr_eq (f : C_c(ℝ, ℝ)) (N : ℕ) (hN : sourceCutoff f ≤ N) :
    fullPairing (autocorr f) = pairing N (autocorr f) :=
  fullPairing_eq_pairing_of_tail _ N fun _ hx =>
    autocorr_eq_zero_of_sourceCutoff_le f ((cutoff_mono hN).trans hx)

/-- The same source cutoff works for every positive right-annular average. -/
theorem fullPairing_average_eq (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ)
    (hN : sourceCutoff f ≤ N) :
    fullPairing (correlationAverage f a b) = pairing N (correlationAverage f a b) :=
  fullPairing_eq_pairing_of_tail _ N fun _ hx =>
    correlationAverage_eq_zero_of_sourceCutoff_le f a b ((cutoff_mono hN).trans hx)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
