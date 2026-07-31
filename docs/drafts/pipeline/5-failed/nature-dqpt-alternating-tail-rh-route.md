# Nature DQPT alternating-tail RH route

- **ID:** `nature-dqpt-alternating-tail-rh-route`
- **Stage:** 5-failed
- **Type:** LITERATURE IMPACT AUDIT / CLOSED RH ROUTE
- **Scientific status:** `[LITERATURE] [BRIDGE] [CLOSED AS AN RH ROUTE]`
- **Primary source:** Shijie Wei et al., *The Riemann Hypothesis manifested in dynamical
  quantum phase transitions*, Nature Communications (2026),
  DOI [`10.1038/s41467-026-74935-8`](https://doi.org/10.1038/s41467-026-74935-8)
- **Local sources:**
  - `docs/s41467-026-74935-8_reference.pdf`;
  - `docs/s41467-026-74935-8_supplementary.pdf`;
  - `docs/s41467-026-74935-8_peer-review.pdf`.
- **Statement:** The paper's engineered DQPT singularity is an exact readout of the already
  encoded Dirichlet eta zero set, not an independent mechanism constraining that set; its strongest
  useful survivor for this project is the reflected alternating-tail slope law below.

## Exact paper mechanism

For \(s=\beta+it\), \(0<\beta<1\), put
\[
 S_N(s)=\sum_{n\leq N}(-1)^{n+1}n^{-s},
 \qquad
 Z_N(\beta)=\sum_{n\leq N}n^{-\beta},
 \qquad
 L_N(\beta,t)=\frac{S_N(s)}{Z_N(\beta)}.
\]
The probe system is engineered so that \(L_N\) is its measured coherence.  Since
\[
 \eta(s)=(1-2^{1-s})\zeta(s),
\]
the limiting numerator has the nontrivial zeta divisor in the open critical strip.

The supplementary proof gives the zero/nonzero rate dichotomy
\[
 -\frac{\log |S_N(s)|}{\log_2 N}
 \longrightarrow
 \begin{cases}
 \beta\log 2,&\zeta(s)=0,\\
 0,&\zeta(s)\neq0.
 \end{cases}
\]
Together with \(Z_N(\beta)\sim N^{1-\beta}/(1-\beta)\), this gives the paper's
free-energy density
\[
 F_1(\beta,t)=
 \begin{cases}
 \log 2,&\zeta(s)=0,\\
 (1-\beta)\log 2,&\zeta(s)\neq0.
 \end{cases}
\]

## Necessary correction: amplitude zero versus rate singularity

The literal thermodynamic coherence does **not** vanish only at zeta zeros.  It vanishes at every
fixed point of the open critical strip.

If \(\eta(s)\neq0\), then
\[
 L_N(\beta,t)
 =(1-\beta)\eta(s)N^{\beta-1}(1+o(1))
 \longrightarrow0.
\]
If \(\eta(s)=0\), the alternating remainder has the sharper expansion
\[
 S_N(s)
 =(-1)^{N+1}\frac12(N+1)^{-s}
   +O_s(N^{-\beta-1}),
\]
so
\[
 L_N(\beta,t)
 =(-1)^{N+1}\frac{1-\beta}{2}N^{-1-it}(1+o(1))
 \longrightarrow0.
\]
Thus only the finite-size decay exponent distinguishes a divisor point.  Statements that the
thermodynamic amplitude itself "vanishes precisely" at nontrivial zeros are too strong.  The
mathematically correct correspondence is:
\[
 \zeta(s)=0
 \quad\Longleftrightarrow\quad
 \text{the coherence has the exceptional }N^{-1}\text{ decay rate}.
\]

The singularity is also a point spike after the \(N\to\infty\) limit.  Away from an exact zero,
however close, the rate is \((1-\beta)\log2\); at the zero it is \(\log2\).  The associated
"entropy density" is negative off the divisor, so it is a rate-function diagnostic, not ordinary
thermodynamic entropy.

## Why it does not supply an RH proof route

1. **Source consumption.**  The spectrum \(E_n=\log n\), thermal weights \(n^{-\beta}\), and parity
   probe \((-1)^{n+1}\) are selected specifically to produce \(\eta(s)\).  Proving that the
   exceptional rate occurs only at \(\beta=1/2\) is exactly RH.
2. **Known quantum-Dirichlet parent.**  Mack et al. (2010) already realize zeta by thermal
   wave-packet dynamics with logarithmic spectrum.  Feiler--Schleich (2015) show that general
   Dirichlet series can be encoded as interfering quantum amplitudes.  The paper adds a DQPT
   rate interpretation, experiment, and circuit complexity, not a new arithmetic constraint.
3. **Wrong reflection for RH.**  Physical time reversal \(t\mapsto-t\) implements
   \(\zeta(\beta-it)=\overline{\zeta(\beta+it)}\), reflection across the real axis.  It does not
   implement the load-bearing functional-equation reflection
   \(s\mapsto1-\overline{s}\) as a same-fibre Hilbert dagger.
4. **Critical-line hard-coding in the second construction.**  Its Hamiltonian contains the
   Riemann--Siegel phase \(\dot\theta(t)\) and is fixed at \(\beta=1/2\).  Its Loschmidt amplitude
   approximates the Hardy \(Z\)-function along the line; it cannot exclude off-line zeros.
5. **No locality or Lee--Yang positivity.**  The exact finite spin representation has arbitrary
   all-orders interactions.  No ferromagnetic, local, stable-polynomial, or reflection-positive
   theorem constrains its Fisher zeros independently of the encoded eta function.
6. **Finite verification is not RH.**  The experiment and high-zero simulations reproduce
   already known finite zero data.  The amplitude-estimation speedup may help numerical probing,
   but cannot certify all heights.

The transparent peer review independently records two scope limitations: the logarithmic spectrum
is artificial, and its density of states has \(S(E)=E\), constant temperature, and infinite heat
capacity.  Authors accepted the first point and recast the system as engineered.

## Strongest positive survivor: reflected tail-slope law

Let \(\rho=\beta+i\gamma\) be any nontrivial zero and
\(\rho^\dagger=1-\overline{\rho}\), which is also a zero.  The sharper alternating-remainder
expansion gives
\[
 \frac{|S_N(\rho)|}{|S_N(\rho^\dagger)|}
 =(N+1)^{1-2\beta}\bigl(1+O_\rho(N^{-1})\bigr).
\tag{1}
\]
Equivalently, the raw source decay rates are \(\beta\) and \(1-\beta\).  Therefore
\[
 \operatorname{Re}\rho=\frac12
 \quad\Longleftrightarrow\quad
 \text{the reflected raw tail rates agree}.
\tag{2}
\]
For the normalized coherence, the zero rate is \(N^{-1}\) on both fibres; the useful reflected
quantity is instead the free-energy spike contrast:
\[
 \Delta F(\rho)=\beta\log2,\qquad
 \Delta F(\rho^\dagger)=(1-\beta)\log2.
\tag{3}
\]

Equations `(1)`--`(3)` are `[BRIDGE]`, not new scientific knowledge or an RH proof.  A theorem
equating the reflected rates or contrasts would force RH, but the paper supplies no such theorem.

## Exact contribution to current HGT/RH research

The survivor is a scalar toy model for the active source-normal Stokes/Bockstein architecture:

```text
generic bulk:     S_N(s) -> eta(s) != 0;
divisor point:    bulk limit vanishes;
first normal:     (N+1)^s S_N(s) -> parity-dependent unit of modulus 1/2;
reflected fibres: normal slopes beta and 1-beta;
missing theorem:  one source-built same-fibre dagger identifies those normals.
```

This gives one useful falsifier for
`arithmetic-stokes-bockstein-universality-law.md`: any proposed source-normal local kernel should
explain why its dyadic parity face recovers the \(1/2\) normal coefficient and the reflected slope
law.  Failure to recover them kills the construction.

It closes none of the load-bearing gaps:

- no ordinary-prime first-trace to Gamma/co-Poisson/Sonin exact-couple morphism;
- no strict source-normal completion;
- no full Xi conormal landing;
- no conormal-faithful localizing prestack;
- no same-fibre dagger naturality.

The repo already contains stronger source results: exact prime Loschmidt purity and cofinal
survival, Xi thermal free-energy RH classifiers, multiplicity-exact divisor tomography,
prime first-trace essential-normal Bockstein, and full Gamma--co-Poisson--Sonin quotient flatness.

## Relentless-interrogation chain

1. **Killed proposal:** DQPT uniqueness at one temperature physically explains RH.
2. **Exact why:** the observable is constructed to equal eta; uniqueness is RH, while literal
   thermodynamic coherence vanishes throughout the strip.
3. **Stronger proposal:** use equality of the two reflected finite-size tail normals rather than
   mere DQPT occurrence.
4. **Second kill:** time reversal supplies only \(t\mapsto-t\), not a same-fibre map between
   \(\beta\) and \(1-\beta\).  Asserting equality of the normals is the missing RH theorem.
5. **Positive survivor:** equations `(1)`--`(3)` give an exact scalar boundary calibration and
   falsifier for any independently constructed dagger/Bockstein.
6. **Representation lesson:** a zeta-valued quantum amplitude is a source readout.  A proof route
   needs a source-native structural law acting before the divisor is read and forcing the
   reflected boundary normals to inhabit one fibre.

## No-go closure

- **Exact killing theorem/mechanism:** \(L_N(\beta,t)\to0\) for every fixed
  \(0<\beta<1\); only its decay exponent changes at the eta divisor, whose location was encoded in
  the observable.
- **Strongest positive survivor:** reflected tail-slope law `(1)` and spike-contrast law `(3)`.
- **New insight:** DQPT readout is an explicit scalar first-normal model; same-fibre reflection,
  not zero detection, remains the sole RH-bearing operation.
- **Status:** paper proof for the underlying tail asymptotic; local corollary paper-proved above;
  external novelty unverified and expected routine; no Lean theorem; no RH impact.

## External parent boundary

- R. Mack et al., *Riemann zeta function from wave-packet dynamics*, Phys. Rev. A 82 (2010),
  DOI [`10.1103/PhysRevA.82.032119`](https://doi.org/10.1103/PhysRevA.82.032119).
- C. Feiler and W. P. Schleich, *Dirichlet series as interfering probability amplitudes for
  quantum measurements*, New J. Phys. 17 (2015),
  DOI [`10.1088/1367-2630/17/6/063040`](https://doi.org/10.1088/1367-2630/17/6/063040).
- C. Gao et al., *Riemann zeros from Floquet engineering a trapped-ion qubit*, npj Quantum
  Information 7 (2021),
  DOI [`10.1038/s41534-021-00446-7`](https://doi.org/10.1038/s41534-021-00446-7).
- G. A. Hiary, *Fast methods to compute the Riemann zeta function*, Ann. Math. 174 (2011),
  DOI [`10.4007/annals.2011.174.2.11`](https://doi.org/10.4007/annals.2011.174.2.11).

## Log

- 2026-07-31 — Obtained article, supplementary information, and transparent peer-review record.
  Audited main construction, asymptotic proofs, quantum-complexity claim, external parents, and
  route-relevant HGT corpus.  Closed as an RH route; extracted reflected tail-slope survivor.
