import GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue
import GaloisForLFunctions.RHTower.Sieve.PrimitiveRatioDecomposition

/-!
# The primitive-ratio form of the generalized mean value identity

`GeneralizedDirichletMeanValue.genPoly_meanValue` is the exact mean square of an exponential sum with
*arbitrary* real frequencies `λ_n`.  `RHTower.Sieve.sum_offDiagPairs_eq_sum_ratio` collapses an
off-diagonal double sum over `[1,N]²` onto coprime pairs.  The two combine exactly when the frequencies
are **completely additive on the positive integers**, `λ(dm) = λ(d) + λ(m)`, because then the frequency
*differences* are ratio-only:

`λ(dm) − λ(dn) = λ(m) − λ(n)`.

This isolates the property that makes the collapse work.  It is not special to `λ_n = log n`: any
completely additive frequency map does it — `c · log n`, `Ω(n)`, `log` of a completely multiplicative
positive function, and so on.  Conversely the collapse fails for `λ_n = n^{1/d}` with `d ≥ 1`, which is
the frequency map of a degree-`d` twist; the failure is exactly the failure of complete additivity, so
this theorem draws the line between the two regimes named in the parent file's introduction.

`RHTower.Sieve.DirichletOffDiagonalCorrelation.integral_normSq_dirPoly_sub_diag_ratio` is the case
`λ_n = log n` of this statement, obtained there directly; the point of this file is that the identity has
nothing to do with `log` beyond its additivity.
-/

namespace HTGeometry

open Finset RHTower.Sieve

noncomputable section

/-- **The generalized mean value identity in primitive-ratio form.**  For completely additive
frequencies the off-diagonal is a sum over coprime pairs, each carrying a single oscillatory integral
and the correlation of the coefficients along that ratio. -/
theorem genPoly_meanValue_ratio (a : ℕ → ℂ) (lam : ℕ → ℝ)
    (hadd : ∀ d m : ℕ, 1 ≤ d → 1 ≤ m → lam (d * m) = lam d + lam m) (N : ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), genPoly a lam (Finset.Icc 1 N) t
        * (starRingEnd ℂ) (genPoly a lam (Finset.Icc 1 N) t))
      = (U : ℂ) * (∑ n ∈ Finset.Icc 1 N, a n * (starRingEnd ℂ) (a n))
        + ∑ q ∈ primitiveRatioPairs N,
            (∑ d ∈ ratioScales N q.1 q.2, a (d * q.2) * (starRingEnd ℂ) (a (d * q.1)))
              * oscInt (lam q.2 - lam q.1) T U := by
  classical
  rw [genPoly_meanValue a lam (Finset.Icc 1 N) T U]
  congr 1
  rw [← sum_offDiagPairs_eq_double N
      (fun x y => a y * (starRingEnd ℂ) (a x) * oscInt (lam y - lam x) T U),
    sum_offDiagPairs_eq_sum_ratio N
      (fun x y => a y * (starRingEnd ℂ) (a x) * oscInt (lam y - lam x) T U)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [primitiveRatioPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hm1, _⟩, hn1, _⟩, _, _⟩ := hq
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [ratioScales, Finset.mem_filter, Finset.mem_Icc] at hd
  rw [hadd d q.1 hd.1.1 hm1, hadd d q.2 hd.1.1 hn1]
  ring_nf

/-- The classical case `λ_n = log n`. -/
theorem genPoly_meanValue_ratio_log (a : ℕ → ℂ) (N : ℕ) (T U : ℝ) :
    (∫ t in T..(T + U), genPoly a (fun n => Real.log (n : ℝ)) (Finset.Icc 1 N) t
        * (starRingEnd ℂ) (genPoly a (fun n => Real.log (n : ℝ)) (Finset.Icc 1 N) t))
      = (U : ℂ) * (∑ n ∈ Finset.Icc 1 N, a n * (starRingEnd ℂ) (a n))
        + ∑ q ∈ primitiveRatioPairs N,
            (∑ d ∈ ratioScales N q.1 q.2, a (d * q.2) * (starRingEnd ℂ) (a (d * q.1)))
              * oscInt (Real.log (q.2 : ℝ) - Real.log (q.1 : ℝ)) T U :=
  genPoly_meanValue_ratio a _ (fun d m hd hm => by
    have hd0 : ((d : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      exact ne_of_gt this
    have hm0 : ((m : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact ne_of_gt this
    push_cast
    exact Real.log_mul hd0 hm0) N T U

end

end HTGeometry
