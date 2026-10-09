# Remove the arithmetic-grid premise from L² translation independence

Status: formalized; direct leaf and axiom audits passed, 2026-10-09.

## Exact premise and corpus evidence

`HTGeometry/L2TranslationPolynomialIndependence.lean` proves independence
of translates at i*h for h≠0. Its polynomial Fourier-multiplier argument
uses equal spacing. Target: arbitrary distinct real shifts a_i, retaining
the original nonzero L² vector condition and adding no analytic premise.

Local corpus ingredients:

- `HurwitzExp.expLin_linearIndependent` in `Hurwitz/ExpIndependence.lean`:
  distinct complex exponential functions are linearly independent.
- `Bottcher.analyticOnNhd_zeros_countable` in `Bottcher/ZeroSet.lean`:
  a nonzero entire function has countably many complex zeros.
- `MellinL2.fourier_additiveTranslation` in `RHTower/L2MellinUnitary.lean`:
  translating a complex L² vector multiplies its Fourier transform by
  `fourierPhase a x = exp(2π i a x)`.
- Installed Lean's `Lp.coeFn_finsetSum` permits finite sums of L² classes
  to be evaluated almost everywhere without a separate induction.

Only local Lean sources consulted. Local search surfaced the arithmetic
theorem and exponential independence; no external novelty claim is made.

## Dependency-closed paper proof

Let a:Fin n→ℝ be injective and c:Fin n→ℂ be nonzero. Put
β_i=(2πa_i)i and G(z)=Σ_i c_i exp(β_i z). The β_i are distinct. Hurwitz
exponential independence implies G is not identically zero. G is entire,
so Bottcher's zero-set theorem makes its complex zero set countable.
Complex.ofReal is injective; its preimage of that set is countable and
therefore Lebesgue null on ℝ. Since G(x)=Σ_i c_i fourierPhase(a_i,x),
the Fourier multiplier P(x) is nonzero almost everywhere. This strengthens
the old multiplier step to countable exceptional real frequencies.

For nonzero f in complex L², suppose Σ_i c_i T(a_i)f=0. Plancherel and
the existing translation theorem give Σ_i c_i phaseMul(a_i)(F)=0,
where F is the Fourier transform of f. Almost-everywhere evaluation of
the finite sum gives P(x)F(x)=0 almost everywhere. If c≠0, the multiplier
result forces F=0 as an L² vector, contradicting Fourier injectivity and
f≠0. Therefore c=0, proving linear independence.

As an exact relation classification, for any f (including zero),

    Σ_i c_i T(a_i)f=0 iff f=0 or c=0.

This removes the nonzero-vector premise from the relation theorem by
classifying the degenerate case explicitly. No compact support, smoothness,
decay, arithmetic-grid, or rational-independence condition is introduced.

## Intended consequence / limit

This removes a real restriction in the current corpus and supplies a
candidate route to finite paired-log kernel classification. The latter is
not claimed here: repeated logarithmic coordinates and passage from the
actual autocorrelation function to its L² class still require exact audits.

## Work log

- [x] Search corpus; inspect all three ingredient statements and proofs.
- [x] Write paper proof before new Lean code.
- [x] Verify mathlib and cross-corpus APIs in /tmp scratch Lean.
- [x] Prove countable multiplier zeros and almost-everywhere nonvanishing.
- [x] Prove arbitrary-shift L² independence and exact relation classification.
- [x] Direct leaf check, umbrella wiring, complete axiom audit.
- [x] Index and lint; record exact results; remove owned scratch files.

## Formal declarations and validation

New leaf:
`formal/GaloisForLFunctions/HTGeometry/L2TranslationExponentialIndependence.lean`.
Namespace: `GaloisForLFunctions.HTGeometry`.

- `fourierPhase_sum_zeros_countable`: a nontrivial character combination at
  arbitrary distinct real shifts has countably many real zeros.
- `fourierPhase_sum_ne_zero_ae`: the corresponding multiplier is nonzero
  almost everywhere.
- `linearIndependent_L2_translates`: arbitrary distinct translates of any
  nonzero complex L² vector are linearly independent.
- `sum_smul_L2_translates_eq_zero_iff`: the exact relation classification
  includes zero source vectors: a relation vanishes iff f=0 or c=0.

The final direct `lake --old env lean <leaf> -o <olean>` check passed on its
first run, without warnings. All four public declarations passed a separate
/tmp `#print axioms` audit, using exactly `propext`, `Classical.choice`, and
`Quot.sound`. The HTGeometry umbrella import occurs once; the olean postdates
the source. `scripts/formal_tools.py index` exited 0, and a module-filtered
local search found all four declarations in the correct module.

Final `scripts/formal_tools.py lint` exited 1 with exactly one unrelated
unreachable-module error: `HTGeometry.QKrawtchoukCompanionTriangular`.
No proof-debt error was reported. No full or umbrella build, external search,
numerical experiment, or heartbeat adjustment. The initial API command was
accidentally launched outside `formal`; its explicit unknown-module failure
was corrected by running the same check from `formal`, where it passed.

The older arithmetic theorem remains intact. This leaf supplies the stronger
API, rather than changing its existing callers or unrelated proofs.

## Follow-up formalized

The actual autocorrelation now has a nonzero L² lift, an almost-everywhere
translation bridge, and faithful finite translate synthesis. Grouping the
logarithmic coordinates gives the exact finite paired-log kernel: all
coefficients at n ≥ 2 vanish, and the coefficients at 0 and 1 sum to zero.
See [finite paired-log kernel classification](finite-paired-log-kernel-classification.md)
for the paper proof, two Lean leaves, and verification record. This result
does not establish injectivity for infinite summable coefficient families.

Full corpus-research goal remains active.
