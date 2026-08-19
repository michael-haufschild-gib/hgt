import GaloisForLFunctions.RHTower.CausalL2LaplaceHolomorphy
import GaloisForLFunctions.RHTower.MobiusCausalSourceLimit
import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovTransform
import GaloisForLFunctions.RHTower.MobiusPowerSumBoundaryLaplace

/-!
# The causal Laplace transform of the critical Möbius vector

Interchanging the Möbius sum with the elementary identity
`∫_{log n}^∞ e^{-wt} dt = n^{-w}/w` turns the causal transform of
`m₀(t) = ∑_{n ≤ e^t} μ(n)/n` into `1/(w ζ(1+w))` on the whole open right half plane.
-/

open MeasureTheory Set Filter ArithmeticFunction LSeries
open scoped Topology LSeries.notation Moebius

namespace RHTower

noncomputable section

/-- The `n`-th atom of the causal Möbius transform. -/
def mertensLaplaceAtom (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Set.indicator (Ici (Real.log n)) (fun s : ℝ => Complex.exp (-(w * (s : ℂ)))) t
    * mobiusRealWeight 1 n

theorem norm_mertensLaplaceAtom (w : ℂ) (n : ℕ) (t : ℝ) :
    ‖mertensLaplaceAtom w n t‖
      = Set.indicator (Ici (Real.log n)) (fun s : ℝ => Real.exp (-(w.re * s))) t
        * ‖mobiusRealWeight 1 n‖ := by
  rw [mertensLaplaceAtom, norm_mul]
  congr 1
  by_cases h : t ∈ Ici (Real.log n)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]

theorem log_natCast_nonneg (n : ℕ) : 0 ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- On the positive ray the shifted half-line is a.e. the plain half-line. -/
theorem ioi_inter_ici_ae {a : ℝ} (ha : 0 ≤ a) :
    (Ioi (0 : ℝ) ∩ Ici a : Set ℝ) =ᵐ[volume] Ioi a := by
  have h1 : Ioi a ⊆ Ioi (0 : ℝ) ∩ Ici a := by
    intro t ht
    exact ⟨lt_of_le_of_lt ha (mem_Ioi.mp ht), le_of_lt (mem_Ioi.mp ht)⟩
  have h2 : (Ioi (0 : ℝ) ∩ Ici a : Set ℝ) ⊆ Ici a := fun t ht => ht.2
  have hnull : volume (Ici a \ Ioi a) = 0 := by
    have : (Ici a \ Ioi a : Set ℝ) = {a} := by
      ext t
      simp only [Set.mem_sdiff, mem_Ici, mem_Ioi, mem_singleton_iff, not_lt]
      constructor
      · rintro ⟨h3, h4⟩; linarith
      · rintro rfl; exact ⟨le_rfl, le_rfl⟩
    rw [this]
    exact Real.volume_singleton
  refine (MeasureTheory.ae_eq_set).mpr ⟨?_, ?_⟩
  · refine measure_mono_null ?_ hnull
    intro t ht
    exact ⟨h2 ht.1, ht.2⟩
  · have hempty : (Ioi a \ (Ioi (0 : ℝ) ∩ Ici a) : Set ℝ) = ∅ := by
      ext t
      simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro ht
      exact h1 ht
    rw [hempty]
    exact measure_empty

/-! ## The atom integrals -/

theorem integrableOn_mertensLaplaceAtom {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    IntegrableOn (mertensLaplaceAtom w n) (Ioi (0 : ℝ)) volume := by
  unfold mertensLaplaceAtom
  refine Integrable.mul_const ?_ _
  exact (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hw).indicator
    measurableSet_Ici

theorem integral_mertensLaplaceAtom {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), mertensLaplaceAtom w n t)
      = mobiusRealWeight 1 n * (Complex.exp (-(w * ((Real.log n : ℝ) : ℂ))) / w) := by
  simp only [mertensLaplaceAtom]
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_congr_set (ioi_inter_ici_ae (log_natCast_nonneg n)),
    GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul_shift hw (Real.log n)]
  ring

theorem integral_norm_mertensLaplaceAtom {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖mertensLaplaceAtom w n t‖)
      = ‖mobiusRealWeight 1 n‖ * (Real.exp (-(w.re * Real.log n)) / w.re) := by
  simp only [norm_mertensLaplaceAtom]
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_congr_set (ioi_inter_ici_ae (log_natCast_nonneg n)),
    integral_Ioi_exp_neg_mul_shift hw (Real.log n)]
  ring

/-! ## The pointwise sum -/

theorem tsum_mertensLaplaceAtom {w : ℂ} {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, mertensLaplaceAtom w n t)
      = Complex.exp (-(w * (t : ℂ))) * criticalMertensVector t := by
  classical
  set M : ℕ := ⌊Real.exp t⌋₊ with hM
  have hzero : ∀ n ∉ Finset.range (M + 1), mertensLaplaceAtom w n t = 0 := by
    intro n hn
    have hMn : M < n := by simpa [Nat.lt_succ_iff] using hn
    have hexp : Real.exp t < (n : ℝ) := (Nat.floor_lt (Real.exp_pos t).le).mp hMn
    have hn1 : 1 ≤ n := by
      by_contra hcon
      have hn0 : n = 0 := by omega
      rw [hn0] at hexp
      simp only [Nat.cast_zero] at hexp
      exact absurd hexp (not_lt.mpr (Real.exp_pos t).le)
    have hlog : t < Real.log n := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have := Real.log_lt_log (Real.exp_pos t) hexp
      rwa [Real.log_exp] at this
    simp only [mertensLaplaceAtom]
    rw [Set.indicator_of_notMem (by simp only [mem_Ici]; linarith), zero_mul]
  rw [tsum_eq_sum hzero]
  have hval : ∀ n ∈ Finset.range (M + 1),
      mertensLaplaceAtom w n t = Complex.exp (-(w * (t : ℂ))) * mobiusRealWeight 1 n := by
    intro n hn
    have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hlogle : Real.log n ≤ t := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · rw [hn0]
        simpa using ht.le
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        have hne : (n : ℝ) ≤ Real.exp t := by
          calc (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnM
            _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
        have := Real.log_le_log hnpos hne
        rwa [Real.log_exp] at this
    simp only [mertensLaplaceAtom]
    rw [Set.indicator_of_mem (by simp only [mem_Ici]; linarith), mul_comm]
  rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
  congr 1
  rw [criticalMertensVector, Set.indicator_of_mem (mem_Ioi.mpr ht), mobiusWeightedPartial, hM]

/-! ## The transform identity -/

theorem cexp_neg_mul_log_eq_cpow {w : ℂ} {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (-(w * ((Real.log n : ℝ) : ℂ))) = (n : ℂ) ^ (-w) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hnpos.le, Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  congr 1
  ring

theorem weight_mul_cexp_eq_term {w : ℂ} (n : ℕ) :
    mobiusRealWeight 1 n * Complex.exp (-(w * ((Real.log n : ℝ) : ℂ)))
      = LSeries.term (↗μ) (1 + w) n := by
  by_cases hn : n = 0
  · subst hn
    simp [mobiusRealWeight]
  · have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cexp_neg_mul_log_eq_cpow (w := w) hn, mobiusRealWeight_eq_term,
      LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.ofReal_one, Complex.cpow_add _ _ hne, Complex.cpow_one,
      Complex.cpow_neg]
    field_simp

theorem integral_norm_atom_le {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖mertensLaplaceAtom w n t‖) ≤ (n : ℝ) ^ (-(1 + w.re)) / w.re := by
  rw [integral_norm_mertensLaplaceAtom hw n]
  by_cases hn : n = 0
  · subst hn
    simp [mobiusRealWeight]
    positivity
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hexp : Real.exp (-(w.re * Real.log n)) = (n : ℝ) ^ (-w.re) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    have hw1 : ‖mobiusRealWeight 1 n‖ ≤ (n : ℝ) ^ (-(1 : ℝ)) := norm_mobiusRealWeight_le 1 n
    have hsplit : (n : ℝ) ^ (-(1 + w.re)) = (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (-w.re) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    rw [hexp, hsplit, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hw1 (by positivity)

theorem summable_integral_norm_mertensLaplaceAtom {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖mertensLaplaceAtom w n t‖) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (integral_norm_atom_le hw) ?_
  · exact MeasureTheory.integral_nonneg (fun t => norm_nonneg _)
  · exact (Real.summable_nat_rpow.mpr (by linarith : -(1 + w.re) < -1)).div_const _

/-- **The causal Laplace transform of the critical Möbius vector.**  On the open right half plane
it is the reciprocal-zeta causal symbol. -/
theorem causalTransform_criticalMertensVector {w : ℂ} (hw : 0 < w.re) :
    causalTransform criticalMertensVector w = centeredSchurLimit w := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun (n : ℕ) (t : ℝ) => mertensLaplaceAtom w n t)
    (fun n => integrableOn_mertensLaplaceAtom hw n)
    (summable_integral_norm_mertensLaplaceAtom hw)
  have hpoint : ∫ t in Ioi (0 : ℝ), (∑' n : ℕ, mertensLaplaceAtom w n t)
      = causalTransform criticalMertensVector w := by
    rw [causalTransform]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [tsum_mertensLaplaceAtom (mem_Ioi.mp ht), neg_mul]
  rw [← hpoint, ← hswap]
  have hterm : ∀ n : ℕ, (∫ t in Ioi (0 : ℝ), mertensLaplaceAtom w n t)
      = LSeries.term (↗μ) (1 + w) n / w := by
    intro n
    rw [integral_mertensLaplaceAtom hw n, ← weight_mul_cexp_eq_term (w := w) n]
    ring
  rw [tsum_congr hterm]
  have hre : 1 < ((1 : ℂ) + w).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hzeta : (∑' n : ℕ, LSeries.term (↗μ) (1 + w) n) = (riemannZeta (1 + w))⁻¹ :=
    LSeries_moebius_eq_inv_riemannZeta hre
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  rw [tsum_div_const, hzeta, centeredSchurLimit]
  have hznz : riemannZeta (1 + w) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  field_simp

end

end RHTower
