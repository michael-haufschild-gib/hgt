import GaloisForLFunctions.RHTower.Sieve.ZetaOneLineBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogPrimeSum

/-!
# Zeta on a compact box to the right of the one-line

`ZetaOneLineBound.lean` bounds `‖ζ‖` below on a compact segment of the line `re s = 1`.  The Euler
comparison of `ZetaLogPrimeSum.lean` is available only for `re s > 1`, so the two do not meet: the
segment bound cannot be fed to the prime sum.

Thickening the segment to the box `[1, 1+η] × [ε, T]` repairs that.  The box is compact, `ζ` is
continuous on it (the pole is excluded because `t ≥ ε > 0`) and nonvanishing (because `re s ≥ 1`), so
`‖ζ‖` attains a positive minimum there.  Every `σ > 1` in the box then carries the comparison, and

    ∑'_p cos(t log p)/p^σ  ≥  log c − ∑'_p p^{-2σ},

uniformly for `σ ∈ (1, 1+η]` and `t ∈ [ε, T]`.

This is the compact form of the input `MoebiusDistance.lean` calls "the zero-free-region input the
corpus does not have": it is unconditional and elementary, but its constant `c` degrades with `T`,
which is exactly why the uniform-in-`T` statement still needs a genuine zero-free region.
-/

namespace RHTower.Sieve

open Complex

/-- A point of the box is never the pole. -/
theorem box_ne_one {ε σ t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
  intro hcon
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hcon] at him
  simp at him
  linarith

/-- The real part on the box is at least one. -/
theorem one_le_re_box {σ t : ℝ} (hσ : 1 ≤ σ) :
    (1 : ℝ) ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
  simpa using hσ

/-- **Quantitative nonvanishing of zeta on a compact box right of the one-line.** -/
theorem exists_pos_lower_bound_zeta_box {ε T η : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (hη : 0 ≤ η) :
    ∃ c > 0, ∀ σ ∈ Set.Icc (1 : ℝ) (1 + η), ∀ t ∈ Set.Icc ε T,
      c ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set K : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) (1 + η) ×ˢ Set.Icc ε T with hK
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := by
    refine ⟨(1, ε), ?_, ?_⟩
    · exact ⟨le_refl 1, by linarith⟩
    · exact ⟨le_refl ε, hεT⟩
  have hcont : ContinuousOn
      (fun q : ℝ × ℝ => ‖riemannZeta ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)‖) K := by
    intro q hq
    obtain ⟨-, hq2⟩ := hq
    have hne1 : ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ≠ 1 := box_ne_one hε hq2.1
    have hdiff : DifferentiableAt ℂ riemannZeta ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) :=
      differentiableAt_riemannZeta hne1
    have hmap : ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) q := by
      fun_prop
    have hcomp : ContinuousAt
        (fun q : ℝ × ℝ => riemannZeta ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) q :=
      ContinuousAt.comp (g := riemannZeta)
        (f := fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) hdiff.continuousAt hmap
    exact (hcomp.norm).continuousWithinAt
  obtain ⟨q₀, hq₀, hmin⟩ := hcompact.exists_isMinOn hne hcont
  refine ⟨‖riemannZeta ((q₀.1 : ℂ) + (q₀.2 : ℂ) * Complex.I)‖, ?_, ?_⟩
  · have hz : riemannZeta ((q₀.1 : ℂ) + (q₀.2 : ℂ) * Complex.I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (one_le_re_box hq₀.1.1)
    exact norm_pos_iff.2 hz
  · intro σ hσ t ht
    exact hmin (show (σ, t) ∈ K from ⟨hσ, ht⟩)

/-- **The prime sum on the box.**  The Euler comparison transported by the box bound. -/
theorem le_tsum_re_prime_cpow_box {ε T η : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (hη : 0 ≤ η) :
    ∃ c > 0, ∀ σ ∈ Set.Ioc (1 : ℝ) (1 + η), ∀ t ∈ Set.Icc ε T,
      Real.log c
          - (∑' p : Nat.Primes,
              ‖((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2)
        ≤ ∑' p : Nat.Primes, (((p : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))).re := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_lower_bound_zeta_box hε hεT hη
  refine ⟨c, hc, ?_⟩
  intro σ hσ t ht
  have hσ1 : (1 : ℝ) < σ := hσ.1
  have hre : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ1
  have hcomp := abs_log_norm_riemannZeta_sub_tsum_re_le hre
  have hzle : c ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
    hbound σ ⟨le_of_lt hσ1, hσ.2⟩ t ht
  have hlog : Real.log c ≤ Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
    Real.log_le_log hc hzle
  have habs := abs_le.1 hcomp
  linarith [habs.1, habs.2]

end RHTower.Sieve
