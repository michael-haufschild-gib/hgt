import GaloisForLFunctions.RHTower.ConnesTwistedChartFourier

/-!
# §VII (16)-(19): the Selberg periodization of a kernel

§VII (16)-(19) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

To compute the trace of an operator on the quotient `X_S = A_S / O_S^*`, Connes proceeds as in the
Selberg trace formula: an operator on `A_S` given by a kernel `k` that commutes with the lattice
action, i.e.

  `k(q x, q y) = k(x, y)`,                                                    (19)

descends to the quotient with the *periodized* kernel `K(x,y) = ∑_q k(x, q y)`, and its trace is

  `Tr(T) = ∑_{q ∈ O_S^*} ∫_D k(x, q x) dx`                                    (17)

where `D` is a fundamental domain.  This module proves the two structural facts behind (17):

* `connesPeriodizedKernel_invariant` - the periodized kernel is genuinely a kernel on the
  quotient, i.e. invariant under the diagonal action (this is where (19) is used, and the proof is
  a reindexing of the sum by conjugation, so it needs no commutativity);
* `connes_selberg_trace` - the diagonal integral of the periodized kernel over a fundamental
  domain is the sum (17), by the Fubini-Tonelli exchange `integral_tsum`;
* `connes_selberg_trace_of_summable` - the same with the hypothesis in the form Connes verifies
  (geometric convergence of `∑_q ∫_D ‖k(x,qx)‖ dx`).

Everything is stated for an arbitrary countable group acting on an arbitrary measure space, so it
applies verbatim to `O_S^*` acting on `A_S`.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {A : Type*} {G : Type*} [Group G] [MulAction G A]

/-- **§VII (17), the periodized kernel.**  The kernel on the quotient `A / G` obtained from a
kernel on `A` by averaging over the lattice. -/
def connesPeriodizedKernel (k : A → A → ℂ) (x y : A) : ℂ := ∑' q : G, k x (q • y)

/-- **§VII (19).**  A kernel invariant under the diagonal action periodizes to a kernel invariant
under the diagonal action; the proof reindexes the sum by conjugation, so no commutativity of the
lattice is used. -/
theorem connesPeriodizedKernel_invariant {k : A → A → ℂ}
    (hk : ∀ (g : G) (x y : A), k (g • x) (g • y) = k x y) (g : G) (x y : A) :
    connesPeriodizedKernel (G := G) k (g • x) (g • y)
      = connesPeriodizedKernel (G := G) k x y := by
  have hterm : ∀ q : G, k (g • x) (q • (g • y)) = k x ((g⁻¹ * q * g) • y) := by
    intro q
    have h := hk g x ((g⁻¹ * q * g) • y)
    rw [← h, ← mul_smul, ← mul_smul]
    congr 2
    group
  have hreindex : (∑' q : G, k x ((g⁻¹ * q * g) • y)) = ∑' p : G, k x (p • y) := by
    have h := ((Equiv.mulRight g).trans (Equiv.mulLeft g⁻¹)).tsum_eq (fun p : G => k x (p • y))
    refine Eq.trans ?_ h
    refine tsum_congr fun q => ?_
    congr 2
    show g⁻¹ * q * g = g⁻¹ * (q * g)
    rw [mul_assoc]
  calc connesPeriodizedKernel (G := G) k (g • x) (g • y)
      = ∑' q : G, k (g • x) (q • (g • y)) := rfl
    _ = ∑' q : G, k x ((g⁻¹ * q * g) • y) := tsum_congr hterm
    _ = ∑' p : G, k x (p • y) := hreindex
    _ = connesPeriodizedKernel (G := G) k x y := rfl

variable [MeasurableSpace A] [Countable G]

/-- **§VII (17).**  The trace of the periodized kernel over a fundamental domain is the sum of the
translated diagonals. -/
theorem connes_selberg_trace {μ : Measure A} {D : Set A} {k : A → A → ℂ}
    (hmeas : ∀ q : G, AEStronglyMeasurable (fun x : A => k x (q • x)) (μ.restrict D))
    (hsum : (∑' q : G, ∫⁻ x in D, ‖k x (q • x)‖ₑ ∂μ) ≠ ⊤) :
    (∫ x in D, connesPeriodizedKernel (G := G) k x x ∂μ)
      = ∑' q : G, ∫ x in D, k x (q • x) ∂μ := by
  simp only [connesPeriodizedKernel]
  exact MeasureTheory.integral_tsum hmeas hsum

/-- **§VII (17), with the hypothesis in the form Connes verifies.**  If each translated diagonal is
integrable on the fundamental domain and the `L¹` masses are summable - which is the geometric
convergence of Connes' Lemma 1 - then the trace formula holds. -/
theorem connes_selberg_trace_of_summable {μ : Measure A} {D : Set A} {k : A → A → ℂ}
    (hint : ∀ q : G, IntegrableOn (fun x : A => k x (q • x)) D μ)
    (hsum : Summable fun q : G => ∫ x in D, ‖k x (q • x)‖ ∂μ) :
    (∫ x in D, connesPeriodizedKernel (G := G) k x x ∂μ)
      = ∑' q : G, ∫ x in D, k x (q • x) ∂μ := by
  refine connes_selberg_trace (fun q => (hint q).aestronglyMeasurable) ?_
  have hval : ∀ q : G, (∫⁻ x in D, ‖k x (q • x)‖ₑ ∂μ)
      = ENNReal.ofReal (∫ x in D, ‖k x (q • x)‖ ∂μ) :=
    fun q => (ofReal_integral_norm_eq_lintegral_enorm (hint q)).symm
  have hnn : ∀ q : G, 0 ≤ ∫ x in D, ‖k x (q • x)‖ ∂μ :=
    fun q => integral_nonneg fun x => norm_nonneg _
  have hrw : (∑' q : G, ∫⁻ x in D, ‖k x (q • x)‖ₑ ∂μ)
      = ENNReal.ofReal (∑' q : G, ∫ x in D, ‖k x (q • x)‖ ∂μ) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    exact tsum_congr hval
  rw [hrw]
  exact ENNReal.ofReal_ne_top

end

end GaloisForLFunctions.RHTower
