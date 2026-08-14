# Formation-Excess Mechanics

- **ID:** ULF-FEM-FIELD
- **Stage:** 1-in-progress
- **Type:** FIELD SUBPROGRAMME / CONSTITUTIVE MECHANISM
- **Parent:** Formation Holonomy Mechanics
- **Status:** [MECHANISM PROGRAMME] [ONE SOURCE REALIZATION PROVED] [GENERIC CONTAINER CLASSICAL] [SELECTION OPEN]

## 1. Pivot

Formation Holonomy Mechanics shows that common recovery is flat and that independent information is
vertical.  It does not yet explain how a source formation assigns positive size, spectral content,
information loss, or work to that vertical sector.

Formation-Excess Mechanics studies this missing mechanism.  Its primitive is not an object and not
an analogy with curvature.  It is a law sequence:

\[
 \boxed{
 \text{non-surjective source formation}
 \to \text{excess flag}
 \to \text{positive sector state}
 \to \text{orthogonal defect}
 \to \text{valuation and work}.}
 \tag{FEM.1}
\]

The direct-sum and Wold containers are classical.  Field content can only reside in a
source-generated assignment of weights and in comparison laws that those weights satisfy.

## 2. Primitive grammar

For a formation arrow (f:x\to y), retain:

1. a monomorphism or admitted source transport (J_f:E_x\to E_y);
2. an excess object (K_f=\operatorname{cofib}J_f), or an actual complement when supplied by source;
3. a positive finite state \(\mu_y\) whose restrictions give masses
   \(Z_f^{\mathrm{in}}\) and \(Z_f^{\mathrm{ex}}\);
4. the survival and excess probabilities

\[
 \alpha_f=\frac{Z_f^{\mathrm{in}}}{Z_y},
 \qquad \beta_f=1-\alpha_f;
 \tag{FEM.2}
\]

5. the formation work

\[
 W_f=-\log\alpha_f.
 \tag{FEM.3}
\]

The positive state must be produced before the target endpoint or zero specialization.  Otherwise
\(\alpha_f\) is fitted observer data.

## 3. Proposed field laws

### Law I -- source excess

A non-surjective formation is retained as inherited image plus source-defined excess.  Passing only
to common recovery erases the excess and cannot be repaired by later observers.

### Law II -- positive orthogonalization

When the source supplies a positive atomic state, GNS turns the excess flag into an orthogonal
projection.  Its cyclic expectation is exactly the excess probability:

\[
 \langle\Omega,Q_f\Omega\rangle=\beta_f.
 \tag{FEM.4}
\]

Positivity does not create the flag; it metrizes a flag already produced by source.

### Law III -- valuation fusion

Every additive valuation compatible with the disjoint flag must split.  Spectral trace, moment,
sector mass, and coefficient sum are examples.  A claimed universal scalar must therefore be shown
to arise from a valuation, not assigned independently.

### Law IV -- information chain

For two positive states on the same formation flag, relative entropy separates into:

- a Bernoulli formation term;
- inherited conditional information;
- excess conditional information.

This law distinguishes loss caused by the formation decision from change internal to either sector.

### Law V -- crossed work cocycle

For composable formations (f,g), source compatibility must imply

\[
 \alpha_{gf}=\alpha_g\,g_!(\alpha_f),
 \qquad
 W_{gf}=W_g+g_!(W_f).
 \tag{FEM.5}
\]

The action (g_!) on parameters is part of the source law.  Omitting it creates false ordinary
additivity.

### Law VI -- properness by work

A formation boundary is excluded at finite work when

\[
 \alpha_f\longrightarrow0
 \quad\Longleftrightarrow\quad
 W_f\longrightarrow+\infty.
 \tag{FEM.6}
\]

This is the global formation/properness mechanism needed before selection.  It is useful only when
the boundary and state are source-native.

### Law VII -- refinement coherence

For a factorization of one formation into several source arrows, the excess must refine into ordered
disjoint layers.  GNS sums, spectral valuations, information chains, and work must be invariant under
parenthesization of this refinement.

## 4. First exact source realization

Ramification shells provide a literal realization:

\[
 A_m\xrightarrow{k\mapsto k^r}A_{rm},
 \qquad
 A_{rm}=P_r(A_m)\sqcup X_{m,r}.
\]

Mellin weights give a canonical normalized positive state for \(\sigma>1\).  The resulting survival
probability and work are

\[
 \alpha_{m,r}(\sigma)=\frac{S_m(r\sigma)}{S_{rm}(\sigma)},
 \qquad
 W_{m,r}(\sigma)=\log S_{rm}(\sigma)-\log S_m(r\sigma).
\]

The paper theorem proves simultaneously:

- coefficient/measure formation;
- orthogonal GNS defect;
- cross-fibre spectral clock;
- characteristic-function and heat-trace valuation;
- KL chain rule;
- crossed work cocycle;
- Kummer-sector collision prediction; and
- normalization-wall coercivity.

See

`docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-excess-mechanics/ramification-gibbs-gns-defect-spectral-information-and-boundary-work-law.md`.

## 5. What this does and does not explain

It explains why several apparently different shadows are forced by one source formation:

| shadow | same formation datum |
|---|---|
| coefficient cofiber | excess support |
| GNS/Wold defect | orthogonal excess subspace |
| spectral trace | additive valuation of layers |
| information loss | Bernoulli plus conditional chain |
| proper work | negative log survival |
| Kummer participation | quadratic sector-mass statistic |

It does **not** yet prove that every RH route is a gauge of this mechanism.  It does not derive the
physical critical-line selector.  Its generic categorical and information-theoretic ingredients are
known; only literal source realization and cross-organ consequences can carry research content.

## 6. Acceptance gates

This subprogramme advances beyond one exact realization only after all gates below close:

1. **Second heterogeneous realization:** same laws in a non-ramification organ with independently
   sourced positive weights.
2. **Joint reconstruction:** at least three organ shadows reconstruct the same marked formation flag,
   or an exact theorem states what each irreversibly loses.
3. **Fourth-organ prediction:** derived without using that organ's target formula.
4. **Cofinal properness:** compactness/properness for a genuine infinite formation system, not only a
   scalar boundary limit.
5. **Selection landing:** an RH-bearing source class lands in the zero set of a positive formation
   invariant before specialization.
6. **Presentation discipline:** changing split coordinates leaves the marked weights and work law
   invariant.

Until Gates 1--6 close, Formation-Excess Mechanics is a serious constitutive subprogramme, not the
finished universal field.

