import GaloisForLFunctions.HTGeometry.ProfileBoundedSeries
import GaloisForLFunctions.HTGeometry.NonlinearMailletAux
import GaloisForLFunctions.HTGeometry.EulerADETruncation

/-!
# The Taylor defect at a truncation is negligible against the profile

Linearizing an analytic differential polynomial along a truncation `Y` of a formal solution leaves a
defect that is a **finite** sum

```text
taylorDefect (jets Y) (jets H) P = ∑_α aeval (jets Y) (T α) · jetMonomialValue (jets H) α ,
```

with `jetDegree α ≥ 2` on the whole support and every `T α` carrying convergent coefficients.  Each
summand is therefore a convergent series times a jet monomial of degree at least two in the tail
`H`, and the tail vanishes below order `N+1`.

Splitting one factor off the monomial and applying the two-tail convolution bound gives every
summand the shifted profile `Θ(N+1) Θ(n−N−1)`.  Since `Θ(n−N−1)` is smaller than `Θ(n−ν)` by a factor
of order `n^{−s(N+1−ν)}`, and the truncation order `N` is free, the whole defect can be made
negligible against any prescribed power of the index times `Θ(n−ν)`.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- **The Taylor defect at a truncation obeys the shifted profile bound.** -/
theorem exists_norm_coeff_taylorDefect_le {m N : ℕ} {s β : ℝ} (hs : 0 < s) (hirr : Irrational s)
    (hβ : 0 < β) (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P)
    {Y H : PowerSeries ℂ} (hY : IsGevreySeries 0 Y)
    (hHprof : ∀ j : Fin (m + 1), HasProfileBound s β (eulerJetVector (m := m) H j))
    (hH0 : ∀ j : Fin (m + 1),
      (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ eulerJetVector (m := m) H j) :
    ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ n : ℕ,
      ‖PowerSeries.coeff n
          (taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P)‖
        ≤ c * ((n : ℝ) + 1) ^ a *
          (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
  classical
  obtain ⟨T, hT2, hTco, hTsum⟩ :=
    hasTaylorDefectFamily (A := PowerSeries ℂ) convergentSubsemiring P
      (fun σ => (mem_convergentSubsemiring).mpr (hP σ))
  -- each summand obeys the bound
  have hex : ∀ α : (Fin (m + 1) →₀ ℕ), ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ n : ℕ,
      (α ∈ T.support →
        ‖PowerSeries.coeff n
            (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α) *
              jetMonomialValue (eulerJetVector (m := m) H) α)‖
          ≤ c * ((n : ℝ) + 1) ^ a *
            (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)))) := by
    intro α
    by_cases hα : α ∈ T.support
    · have hTα : IsAnalyticDifferentialPolynomial (T α) :=
        fun σ => (mem_convergentSubsemiring).mp (hTco α σ)
      have hDconv : IsGevreySeries 0
          (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α)) :=
        isGevreySeries_aeval_eulerJetVector le_rfl (T α) hTα hY
      have hD : HasProfileBound s β (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α)) :=
        hasProfileBound_of_isGevreySeries_zero hs hirr hβ hDconv
      obtain ⟨c, a, hc, hb⟩ :=
        norm_coeff_mul_jetMonomialValue_le_of_two_le hs hβ hD hHprof hH0 (hT2 α hα)
      exact ⟨c, a, hc, fun n _ => hb n⟩
    · exact ⟨0, 0, le_rfl, fun n hn => absurd hn hα⟩
  choose c a hc hb using hex
  refine ⟨∑ α ∈ T.support, c α, T.support.sup a, Finset.sum_nonneg fun α _ => hc α, fun n => ?_⟩
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hEnd : (0 : ℝ) < gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)) :=
    mul_pos (gammaProfile_pos hs.le hβ _) (gammaProfile_pos hs.le hβ _)
  have hterm : ∀ α ∈ T.support,
      ‖PowerSeries.coeff n
          (MvPolynomial.aeval (eulerJetVector (m := m) Y) (T α) *
            jetMonomialValue (eulerJetVector (m := m) H) α)‖
        ≤ c α * ((n : ℝ) + 1) ^ (T.support.sup a) *
          (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
    intro α hα
    refine le_trans (hb α n hα) ?_
    refine mul_le_mul_of_nonneg_right ?_ hEnd.le
    refine mul_le_mul_of_nonneg_left ?_ (hc α)
    exact pow_le_pow_right₀ hbase (Finset.le_sup hα)
  rw [hTsum (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H), Finsupp.sum, map_sum]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

end GaloisForLFunctions.HTGeometry
