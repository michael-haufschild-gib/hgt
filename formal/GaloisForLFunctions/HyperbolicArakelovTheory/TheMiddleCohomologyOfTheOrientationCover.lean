import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeQuadraticOrientationCounts
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# The middle cohomology of the orientation cover over ℤ

The topological branch of the programme (B120) asks for an orientation cover over the integers: a
double cover defined by a trace discriminant whose fibre over `n` has `1 + μ(n)` points, and asks for
its cohomology. Over `𝔽_q[T]` the factor-trace cover (Stickelberger) has total count `qⁿ` exactly: the
centred count vanishes and the cover has no middle cohomology.

Over ℤ the cover exists: the real points of the discriminant of `primeQuadraticPolynomial n` number
`1 + μ(n)` (`RenormalizedIntersectionArithmeticCounts.primeQuadraticOrientation_card`), and the
disjoint union over `n ≤ N` has `N + M(N)` points (`primeQuadraticOrientationCount_eq`). Its centred
count `D(N) = #cover − N` (`coverDefect`) plays the role of the trace on the middle cohomology. This
file determines its size.

**Theorems.**
* `coverDefect_omega`: **the middle cohomology does not vanish, and has weight at least `½`.** There is
  `c > 0` with `D(N) > c√N` and `D(N) < −c√N` for infinitely many `N`, unconditionally: the zeros of `ζ`
  on the critical line (Hardy) make the Mellin transform of `M` singular there
  (`RHTower.mertens_omega_pm_sqrt`).
* `riemannHypothesis_iff_coverDefect_le`: **the weight is exactly `½` iff RH.**
  `|D(N)| ≤ C_δ(N + 1)^{½+δ}` for every `δ > 0` is equivalent to RH (Littlewood's criterion,
  `RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis`).

So the cover over ℤ is the opposite of the cover over `𝔽_q[T]`: its middle cohomology is never zero,
its weight is never below `½`, and the Riemann hypothesis is the statement that this weight is `½`, the
purity of the cover. A self-map with bounded local indices and Lefschetz number `#cover` would bound
`|D(N)|` by the dimension of that cohomology times `N^{½}`; the prime-vertex indices of
`RenormalizedIntersectionArithmeticCounts` localize `1 − M(N)` but are unbounded.
-/

open Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open RenormalizedIntersectionArithmeticCounts

/-- The centred count `#(cover over [1, N]) − N` of the discriminant orientation cover. -/
def coverDefect (N : ℕ) : ℤ := (primeQuadraticOrientationCount N : ℤ) - N

/-- The centred count is the Mertens sum. -/
theorem coverDefect_eq (N : ℕ) :
    coverDefect N = ∑ n ∈ Icc 1 N, ArithmeticFunction.moebius n := by
  rw [coverDefect, primeQuadraticOrientationCount_eq]; ring

theorem coverDefect_eq_mertensPartialSum (N : ℕ) :
    ((coverDefect N : ℤ) : ℂ) = RHTower.mobiusMertensPartialSum N := by
  rw [coverDefect_eq, RHTower.mobiusMertensPartialSum, Int.cast_sum]
  refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
  · rw [mem_range]; have := (mem_Icc.mp hn).2; omega
  · have h0 : n = 0 := by
      by_contra h
      exact hn' (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, by have := mem_range.mp hn; omega⟩)
    subst h0
    simp

theorem coverDefect_eq_mertensFunctionReal (x : ℝ) :
    (coverDefect ⌊x⌋₊ : ℝ) = RHTower.mertensFunctionReal x := by
  rw [coverDefect_eq, RHTower.mertensFunctionReal, Int.cast_sum]

/-- **The weight of the orientation cover is `½` iff RH.** -/
theorem riemannHypothesis_iff_coverDefect_le :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(coverDefect N : ℝ)| ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
  rw [← RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis,
    RHTower.MobiusMertensAllStrictHalfPowerBound]
  have e : ∀ N : ℕ, ‖RHTower.mobiusMertensPartialSum N‖ = |(coverDefect N : ℝ)| := fun N => by
    rw [← coverDefect_eq_mertensPartialSum, Complex.norm_intCast]
  simp only [e]

/-- **The middle cohomology of the orientation cover does not vanish: `D(N) = Ω_±(√N)`.** -/
theorem coverDefect_omega :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ N : ℕ in atTop, c * Real.sqrt N < coverDefect N) ∧
      ∃ᶠ N : ℕ in atTop, (coverDefect N : ℝ) < -(c * Real.sqrt N) := by
  obtain ⟨c, hc, hpos, hneg⟩ := RHTower.mertens_omega_pm_sqrt
  have hsq : ∀ x : ℝ, 0 ≤ x → Real.sqrt (⌊x⌋₊ : ℝ) ≤ Real.sqrt x := fun x hx =>
    Real.sqrt_le_sqrt (Nat.floor_le hx)
  refine ⟨c, hc, frequently_atTop.mpr fun N₀ => ?_, frequently_atTop.mpr fun N₀ => ?_⟩
  · obtain ⟨x, hx, hM⟩ := frequently_atTop.mp hpos (N₀ : ℝ)
    have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
    refine ⟨⌊x⌋₊, Nat.le_floor hx, ?_⟩
    rw [coverDefect_eq_mertensFunctionReal]
    nlinarith [hsq x hx0]
  · obtain ⟨x, hx, hM⟩ := frequently_atTop.mp hneg (N₀ : ℝ)
    have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
    refine ⟨⌊x⌋₊, Nat.le_floor hx, ?_⟩
    rw [coverDefect_eq_mertensFunctionReal]
    nlinarith [hsq x hx0]

end GaloisForLFunctions.HyperbolicArakelovTheory
