import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceAbelInterpolation

noncomputable section
open Finset
namespace RHTower

theorem criticalChild_weighted_quotient_normal_form
    (M p : ℕ) (hp : 0 < p) (hqp : 1 ≤ M / p) :
    Real.sqrt p * mobiusDivisorCriticalChildSource M p =
      Real.sqrt M * psiDefect (M / p) +
      Real.sqrt p *
        ((∑ k ∈ Ico 1 (M / p),
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) -
          Real.sqrt (M / p : ℕ) * psiDefect (M / p)) := by
  rw [mobiusDivisorCriticalChildSource_eq_psiAbel M p hqp]
  have hc := divisorPrimeClipWeight_mul_step M p hp
  have hs : Real.sqrt (p * (M / p) : ℕ) =
      Real.sqrt p * Real.sqrt (M / p : ℕ) := by
    push_cast
    exact Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) p) _
  rw [hs] at hc
  calc
    Real.sqrt p *
      ((∑ k ∈ Ico 1 (M / p),
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) +
        divisorPrimeClipWeight M p *
          (Real.sqrt (M / p + 1 : ℕ) - Real.sqrt (M / p : ℕ)) *
          psiDefect (M / p))
      = Real.sqrt p * (∑ k ∈ Ico 1 (M / p),
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) +
        (divisorPrimeClipWeight M p * Real.sqrt p *
          (Real.sqrt (M / p + 1 : ℕ) - Real.sqrt (M / p : ℕ))) *
          psiDefect (M / p) := by ring
    _ = _ := by rw [hc]; ring

/-- On a fixed quotient band, the entire clipped prime sum reduces to a
prime count and a square-root-weighted prime sum. -/
theorem criticalChild_weighted_fixed_quotient_band
    (M n : ℕ) (P : Finset ℕ) (hn : 1 ≤ n)
    (hP : ∀ p ∈ P, 0 < p ∧ M / p = n) :
    (∑ p ∈ P, Real.sqrt p * mobiusDivisorCriticalChildSource M p) =
      (P.card : ℝ) * Real.sqrt M * psiDefect n +
      (∑ p ∈ P, Real.sqrt p) *
        ((∑ k ∈ Ico 1 n,
          (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) -
          Real.sqrt n * psiDefect n) := by
  have hterm (p : ℕ) (hp : p ∈ P) :
      Real.sqrt p * mobiusDivisorCriticalChildSource M p =
        Real.sqrt M * psiDefect n +
        Real.sqrt p *
          ((∑ k ∈ Ico 1 n,
            (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) -
            Real.sqrt n * psiDefect n) := by
    obtain ⟨hp0, hquot⟩ := hP p hp
    simpa only [hquot] using
      criticalChild_weighted_quotient_normal_form M p hp0 (by simpa only [hquot] using hn)
  rw [sum_congr rfl hterm]
  rw [sum_add_distrib, sum_mul]
  simp only [sum_const, nsmul_eq_mul]
  ring

/-- Exact quotient-band disintegration of a finite weighted critical-child
prime sample. The arithmetic source enters through two scalar coefficients
per quotient; the prime geometry enters only through band count and its
square-root-weighted sum. -/
theorem criticalChild_weighted_sum_eq_quotient_bands
    (M : ℕ) (U : Finset ℕ)
    (hU : ∀ p ∈ U, 0 < p ∧ p ≤ M) :
    (∑ p ∈ U, Real.sqrt p * mobiusDivisorCriticalChildSource M p) =
      ∑ n ∈ U.image (fun p => M / p), (
        ((U.filter (fun p => M / p = n)).card : ℝ) *
            Real.sqrt M * psiDefect n +
          (∑ p ∈ U.filter (fun p => M / p = n), Real.sqrt p) *
            ((∑ k ∈ Ico 1 n,
                (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) -
              Real.sqrt n * psiDefect n)) := by
  have hfilter : U.filter (fun p => M / p ∈ U.image (fun p => M / p)) = U := by
    apply filter_eq_self.mpr
    intro p hp
    exact mem_image_of_mem _ hp
  have hpart := Finset.sum_fiberwise_eq_sum_filter U (U.image (fun p => M / p))
    (fun p => M / p) (fun p => Real.sqrt p * mobiusDivisorCriticalChildSource M p)
  rw [hfilter] at hpart
  rw [← hpart]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 ≤ n := by
    obtain ⟨p, hp, hpn⟩ := mem_image.mp hn
    obtain ⟨hp0, hpM⟩ := hU p hp
    rw [← hpn]
    exact Nat.one_le_div_iff hp0 |>.mpr hpM
  apply criticalChild_weighted_fixed_quotient_band M n
    (U.filter (fun p => M / p = n)) hn1
  intro p hp
  exact ⟨(hU p (mem_filter.mp hp).1).1, (mem_filter.mp hp).2⟩

end RHTower
