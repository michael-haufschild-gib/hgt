# q-Gamma five-chart reconstruction and marked presentation-rigidity law — Lean certification

- **ID:** ULF-QG5R-1
- **Paper card:**
  `q-gamma-five-chart-reconstruction-and-marked-presentation-rigidity-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.QGammaFiveChart`,
  `GaloisForLFunctions.HTGeometry.MarkedCyclicRigidity`,
  `GaloisForLFunctions.HTGeometry.AbsConvergentPowerSeries`,
  `GaloisForLFunctions.HTGeometry.QGammaGNSChart`
- **Reused from ULF-QGPRH-1:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveQGammaProcess`,
  `GaloisForLFunctions.HTGeometry.QPochhammer`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## The certified object

For a nome `0 < q < 1` the five presentations of the card are all present as Lean objects: the
parameter `q : RealEulerNome`; the probability law `qLaw q` on `ℝ`; the characteristic process
`qChar q`; the marked GNS triple `(QGammaSpace, qUnitary q, qOmega q)`; and the analytic response
`qResponseFun q` near the origin.

## Certified declarations

### §2 — reconstruction

The atoms `x_n = n log q − log(1−q)` strictly decrease (`qGammaAtom_strictAnti`), so `x_0` is the
unique largest one (`qGammaAtom_le_zero`, equation (5)) and `nome_eq_one_sub_exp_neg` is
equation (6), `q = 1 − exp(−x_0)`.

- **Chart 2.**  `qLaw q = Measure.sum (fun n => ENNReal.ofReal (w_n) • dirac (x_n))` with
  `qLaw_univ` and the `IsProbabilityMeasure` instance, `qLaw_singleton_atom` (`μ{x_k} = w_k`, using
  the injectivity of the atom map) and `qLaw_singleton_eq_zero`.  `nome_eq_of_qLaw_eq`: if two laws
  agree then neither can have an atom above the other's largest atom, so the largest atoms agree
  and the nomes agree.
- **Chart 3.**  `charFun_qLaw`: the mathlib characteristic function of `qLaw q` is exactly
  `qChar q`, proved by `integral_sum_measure` against the Dirac sum with the bounded-kernel
  integrability lemma `integrable_qCharKernel`.  `nome_eq_of_qChar_eq` then runs mathlib's Fourier
  uniqueness `MeasureTheory.Measure.ext_of_charFun`.
- **Chart 5.**  `analyticOnNhd_qResponseFun` upgrades the corpus's term-by-term differentiation on
  `qStrip` to analyticity; `qStrip` is convex, hence preconnected, and contains both the origin and
  the entire imaginary axis, so `nome_eq_of_response_germ_eq` continues a germ identity at `0` to
  the identity of the characteristic processes.

### §3 — marked GNS rigidity

`exists_unique_marked_intertwiner` is Theorem 3.1 in full generality: for a group `G` acting by
linear isometry equivalences on complex Hilbert spaces with cyclic vectors and equal matrix
coefficients there is a *unique* marked intertwining unitary.

The proof is the GNS uniqueness argument.  `inner_orbit` computes every orbit Gram entry from the
matrix coefficient; `ker_cyclicMap_eq` deduces that the two orbit maps `(G →₀ ℂ) → H` have the same
kernel; `cyclicTransfer` is the induced map between the cyclic spans, built with `Submodule.liftQ`
along `LinearMap.quotKerEquivRange`, and `norm_cyclicTransfer` makes it isometric.  mathlib's
`LinearIsometry.extend` is finite-dimensional only, so the extension to the whole space is built
here from `ContinuousLinearMap.extend` (`markedMap`), and both the marking `markedMap_omega`, the
intertwining `markedMap_intertwine` and the uniqueness are density arguments against the cyclic
span.

### §4 — the five-chart corollary

`qUnitary q` is the diagonal unitary group `U_t = ` multiplication by `exp(i t x_n)` on
`QGammaSpace = lp (fun _ : ℕ => ℂ) 2`; diagonal unitaries of `ℓ²` are not in mathlib and are built
here (`lpPhaseLM`, `norm_lpPhaseLM`, `lpPhaseEquiv`).  `qUnitary_qOmega` identifies its orbit with
the corpus's `qOrbit`, so `qChar_eq_inner` is equation (4).

`dense_span_qOrbit` is the minimality clause: a vector `v` orthogonal to the whole orbit yields
coefficients `a_n = √w_n · v_n` bounded by `‖v‖ (√q)ⁿ`, hence a power series convergent on a disc
of radius `q^{−1/4} > 1`; the orthogonality relations say precisely that this series vanishes on the
whole unit circle, and `powerCoeff_eq_zero_of_circle` then kills every coefficient, so `v = 0`.

`markedEquivalent_of_qChar_eq` and `qChar_eq_of_markedEquivalent` are the two directions of chart 4,
and `qGamma_fiveChart_tfae` is Corollary 4.1:

`q = q' ↔ μ_q = μ_{q'} ↔ C_q = C_{q'} ↔ 𝓖_q ≃ 𝓖_{q'} ↔ [F_q]_0 = [F_{q'}]_0`.

### §5 — invariance

`markedEquivalent_invariance`: marked process equivalence forces equality of the nome, hence of the
atoms, weights, moments, tilted weights, probability law and analytic response.  Equation (14), the
withheld tilt response, was certified in ULF-QGPRH-1 as `qTilt_response_eq` and is therefore
invariant too.

## New infrastructure absent from mathlib

- Diagonal unitaries of `ℓ²` (multiplication by a unimodular sequence).
- The uniqueness of marked cyclic unitary presentations over an arbitrary group, with the extension
  of an isometry from a dense subspace of an infinite-dimensional Hilbert space.
- Vanishing of the coefficients of an absolutely convergent power series that vanishes on the unit
  circle.
- The atomic q-Gamma law as a measure, its singleton masses, and the identification of its
  characteristic function with the q-Gamma characteristic process.

## Verification

`#print axioms` on `qGamma_fiveChart_tfae`, `qGamma_fourChart_tfae`,
`exists_unique_marked_intertwiner`, `dense_span_qOrbit`, `nome_eq_of_qChar_eq`,
`nome_eq_of_response_germ_eq`, `charFun_qLaw`, `markedEquivalent_invariance` and
`powerCoeff_eq_zero_of_circle` reports only `propext`, `Classical.choice`, `Quot.sound`.  No project
postulate, interface hypothesis, or computation proof is used.  Targeted foreground
`lake env lean` on every new module is green, and the dedicated field umbrella
`GaloisForLFunctions.HTGeometry.UniversalLawField` builds green (11,541 jobs).
