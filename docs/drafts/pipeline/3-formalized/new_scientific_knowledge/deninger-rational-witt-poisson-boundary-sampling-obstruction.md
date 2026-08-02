# Rational-Witt Poisson-boundary sampling obstruction

- **ID:** `deninger-rational-witt-poisson-boundary-sampling-obstruction`
- **Stage:** 3-formalized
- **Type:** EXACT NO-GO WITH SECONDARY-REGULATOR SURVIVOR
- **Label:** `DAC_DENINGER_WRAT_POISSON_BOUNDARY_SAMPLING_OBSTRUCTION`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** literal prime evaluation of Meyer's Poisson output does not annihilate the
  Poisson-boundary range at any prime. Hence the source-derived Schwartz--Witt Bessel map is an
  analytic cochain map only; it cannot descend to middle cohomology without a nontrivial
  secondary or quotient-correcting term.

## 1. Boundary witness

Let \(h_n\) be the self-dual Hermite--Schwartz family and put
\[
 b=h_4-h_4(0)h_0.
\]
The exact profile is
\[
 b(x)
 =8x^2\left(2x^2-\frac3\pi\right)e^{-\pi x^2}
 =16x^2\left(x^2-\frac3{2\pi}\right)e^{-\pi x^2}.                 \tag{1}
\]
Thus \(b\) is exactly sixteen times the repository's previously constructed
`meyerPoissonTest`; it is not a newly selected test designed for this obstruction.

Both \(h_0\) and \(h_4\) are fixed by Fourier transform. Therefore \(b\) is even,
\(b(0)=0\), and \(\widehat b(0)=0\). Hence
\[
 b\in H_\cap,
\]
Meyer's two-endpoint source domain.

## 2. Strict prime leakage

For every \(x\ge2\), formula `(1)` and \(\pi>3\) give \(b(x)>0\). For every prime \(p\),
all terms in
\[
 (Zb)(p)=\sum_{n\ge1}b(np)                                      \tag{2}
\]
are therefore strictly positive. A second-order Schwartz seminorm gives
\[
 |b(np)|\le q_{2,0}(b)n^{-2},
\]
so `(2)` is absolutely convergent, with no numerical computation or prime-distribution
theorem. Consequently
\[
 \boxed{(Zb)(p)>0\quad\text{for every prime }p.}                 \tag{3}
\]

## 3. Quotient obstruction

Let \(Z:H_\cap\to H_-\) be any linear realization of Meyer's Poisson map and let
\(\operatorname{ev}_p:H_-\to\mathbb C\) be compatible with literal evaluation:
\[
 \operatorname{ev}_p(Zf)=(Zf)(p).
\]
Equation `(3)` gives
\[
 \operatorname{range}Z\not\subseteq\ker\operatorname{ev}_p.
\]
Therefore no map
\[
 H_-/\operatorname{range}Z\longrightarrow\mathbb C
\]
can factor literal prime evaluation. This is stronger than saying that a proposed proof is
missing boundary compatibility: boundary compatibility is false for raw evaluation.

## 4. Rational-Witt first-mode consequence

For nonzero \(v_p\in L^2(B_p)\), the naive polarized first-mode boundary value is
\[
 p^{-1/2}(Zb)(p)\,T_p(v_p).
\]
Every factor is nonzero: half-density is positive, `(3)` holds, and \(T_p\) is injective. Hence
this vector is nonzero. Taking \(v_p\) from any nonzero finite packet function, the finite
rational-Witt bridge supplies an actual arithmetic-Frobenius-fixed Wrat witness whose raw
first-mode sample detects the boundary \(Zb\).

Thus neither arithmetic Wrat provenance, radial Schwartz decay, half-density, nor correct local
circle variance repairs cohomological descent by itself.

## 5. Positive survivor

Route L's Cauchy comparison must be a **secondary regulator**. On the separated radial--Wrat
sector it must have the shape
\[
 \mathcal C_p(h,a_p)
 =
 p^{-1/2}\bigl(h(p)-\mathcal H_p(h)\bigr)T_p(a_p),               \tag{4}
\]
where the correction obeys the non-negotiable boundary law
\[
 \mathcal H_p(Zf)=(Zf)(p).                                      \tag{5}
\]
Equivalently, it may be defined directly on a chain homotopy/cone whose boundary component
produces `(5)`. The correction cannot be a residue factor: the earlier residue-factor theorem
shows that every middle cocycle would then vanish. It must use secondary Poisson/Euler
localization data.

Equations `(4)`--`(5)` do not yet construct \(\mathcal H_p\). They identify its exact universal
property and eliminate raw sampling as a possible solution.

## 6. Hostile audit

- **Not rediscovery of the test.** Identity `(1)` explicitly identifies the Hermite witness with
  the existing `meyerPoissonTest`.
- **Not a positivity computation.** Positivity uses only \(p\ge2\), \(\pi>3\), and exact
  Schwartz summability.
- **Not target theatre.** The counterexample lies in the actual Meyer endpoint domain and is fed
  through the literal Poisson sum.
- **Not a contradiction with the Bessel theorem.** Bessel continuity is correct on cochains.
  Failure occurs only when raw evaluation is claimed to descend through boundaries.
- **Not a proof that no regulator exists.** The surviving regulator is secondary and must satisfy
  `(5)`.

## 7. Novelty audit

Primary-source search covered Meyer's nuclear Fréchet spectral quotient, Deninger's rational-Witt
dynamical systems/relevant-complex program, and Paugam's symplectic pairing. Those sources supply
the Poisson quotient, prime closed-orbit geometry, and quotient pairing separately. No located
source states the every-prime positivity `(3)`, the resulting failure of prime evaluation to
factor through Meyer's quotient, or its finite-Wrat first-suspension consequence. New content is
the exact incompatibility theorem and forced secondary-regulator law `(5)`.

## 8. Lean status

Formalized unconditionally in
`GaloisForLFunctions/RHTower/DeningerRationalWittPoissonBoundarySamplingObstruction.lean`.
Capstones:

- `deningerMeyerPrimeBoundaryProbe_meyerSum_pos`;
- `deningerPrimeEvaluation_not_annihilate_meyerRange`;
- `deningerPrimeEvaluation_no_meyerQuotientFactor`;
- `deningerMeyerBoundaryFirstModeValue_ne_zero`;
- `deningerFiniteRationalWitt_exists_witness_nonzero_boundarySampling`.

No `sorry`, `axiom`, `opaque`, `unsafe`, computation, or RH-equivalent assumption is used.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.

## Log

- 2026-08-02 — Explicit Hermite/Meyer boundary identified; strict positivity of every prime
  Poisson sample proved.
- 2026-08-02 — Raw prime evaluation and raw Wrat first-mode sampling proved not to descend through
  Meyer boundaries; secondary-regulator survivor extracted and Lean-formalized.
