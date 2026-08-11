# Source-response Laplacian, frame properness, and adaptive-escape conjecture

- **ID:** ULF-FLPM-1
- **Stage:** 1 — in progress
- **Type:** FIELD-MECHANISM CONJECTURE / HOSTILE GATE
- **Status:** `[SUPERSEDED BY DEPENDENCY-CLOSED STAGE-2 THEOREM] [NOT RH]`

## 1. Failure that forces the representation

The first candidate was an oriented chamber atlas built from portwise KL chirality. It fails as a
field primitive for three exact reasons.

1. A labelled port family can be supplied after the fact. Without source generation, its chamber
   arrangement encodes arbitrary desired distinctions.
2. For a minimal finite exponential family, the natural/mean parameter correspondence, Bregman
   representation of KL, and support-oriented-matroid geometry are parent mathematics. Applying a
   strictly monotone scalar coordinate to a spanning linear coframe is only reparameterization.
3. The corpus already proves phase reconstruction, recurrent quotient/open lift, norming-face
   Helly witnesses, and orientation non-descent. Recombining those conclusions without a new
   conservation law is redressing.

The killing mechanism is useful: a valid field law must remember **which response maps one source
intervention generated**, and it must distinguish fixed-ray detectability from uniform/adaptive
detectability. The latter distinction is absent from the completed scalar global-formation theorem.

## 2. Source-generated response packet

Let `V` be a real Hilbert space of legal source displacements. Let `I` be a finite nonempty set of
organs, let `W` be a real Hilbert response space, let

\[
 \rho_i:V\longrightarrow W\qquad(i\in I)
 \tag{FL.1}
\]

be bounded linear responses generated from one marked source intervention, and choose weights
`c_i>0`. Put `C=sum_i c_i` and

\[
 \bar\rho={1\over C}\sum_i c_i\rho_i.
 \tag{FL.2}
\]

Define the **formation analysis operator**

\[
 A:V\longrightarrow \bigoplus_{i\in I}W,
 \qquad
 Ax=(\sqrt{c_i}(\rho_i-\bar\rho)x)_i,
 \tag{FL.3}
\]

the **formation energy**

\[
 \mathcal E(x)=\|Ax\|^2,
 \tag{FL.4}
\]

and the **source-response Laplacian**

\[
 L=A^*A.
 \tag{FL.5}
\]

Fixing an anchor `i_0 in I`, define the synchronization kernel

\[
 K=\bigcap_{i\in I}\ker(\rho_i-\rho_{i_0}).
 \tag{FL.6}
\]

Unlike a routewise Gram matrix, `(FL.5)` is formed only after one source arrow has produced the
entire packet `(rho_i x)_i`. Independent routewise repairs are not inputs.

## 3. Exact conjecture

### Conjecture 3.1 — formation-Laplacian conservation and properness

The following statements hold.

1. **Pairwise conservation.** For every `x in V`,

   \[
   \boxed{
   \mathcal E(x)
   =\sum_i c_i\|\rho_i x-\bar\rho x\|^2
   ={1\over C}\sum_{i<j}c_ic_j\|\rho_i x-\rho_jx\|^2.}
   \tag{FL.7}
   \]

2. **Exact synchronization kernel.**

   \[
   \boxed{\ker A=\ker L=K.}
   \tag{FL.8}
   \]

3. **Finite-dimensional quotient properness.** If `V` is finite-dimensional, then on `K^perp`
   there is a largest constant `lambda_F>0` such that

   \[
   \boxed{
   \mathcal E(x)\ge\lambda_F\,\operatorname{dist}(x,K)^2.}
   \tag{FL.9}
   \]

   It is the least positive eigenvalue of `L`. Hence `E` descends to a positive-definite quadratic
   form on `V/K`, and its quotient sublevels are compact.

4. **Scale-orbit selection.** For `d>1` and every `x in V`,

   \[
   \mathcal E(d^nx)=d^{2n}\mathcal E(x),
   \qquad
   \boxed{
   \sup_n\mathcal E(d^nx)<\infty\iff x\in K.}
   \tag{FL.10}
   \]

   In particular, if the response packet separates source displacements (`K={0}`), bounded
   formation work selects `x=0`.

5. **Pluecker reconstruction.** Assume `V,W` are finite-dimensional and let
   `r=dim(K^perp)`. In orthonormal coordinates, let `B` be the matrix of `A|_(K^perp)`. Then

   \[
   \boxed{
   \operatorname{pdet}(L)
   =\det(B^*B)
   =\sum_{|S|=r}\det(B_S)^2.}
   \tag{FL.11}
   \]

   Thus strict selection is equivalent to existence of a finite nonzero source-response minor;
   the positive Laplacian retains squared oriented volumes and forgets their signs.

6. **Adaptive-escape dichotomy.** For arbitrary Hilbert `V`, the following are equivalent:

   - `ran A` is closed;
   - there is `alpha>0` with
     `E(x)>=alpha dist(x,K)^2` for every `x`;
   - no unit sequence `x_n in K^perp` satisfies `E(x_n)->0`.

   Consequently an injective response packet may detect every fixed nonzero displacement and still
   admit adaptive unit displacements whose complete source-response energy tends to zero. This
   happens exactly when its formation frame bound vanishes.

## 4. Why this is stronger than the killed chamber atlas

The chamber atlas recorded signs of supplied coordinates. The Laplacian statement instead derives
four consequences from one source-generated packet:

\[
 \text{relative-response conservation}
 \longrightarrow \text{positive operator}
 \longrightarrow \text{quotient properness}
 \longrightarrow \text{selection/escape dichotomy}.
 \tag{FL.12}
\]

No oriented-matroid hypothesis is needed. The Pluecker packet appears as a theorem about the
positive operator, not as the source of the response maps. Most importantly, `(FL.10)` and the last
clause of Conjecture 3.1 separate two questions that the scalar formation theorem conflated:

- a fixed nonneutral displacement is eventually expelled by dilation;
- an adaptive family can evade every uniform estimate when the lower formation-frame bound is zero.

This is the exact distinction between fixed endpoint routes and moving-null/adaptive/cofinal routes.

## 5. Proof attack

The conjecture appears paper-provable by the following closed chain.

1. Expand the Hilbert variance identity to prove `(FL.7)`.
2. Every summand in `(FL.7)` is nonnegative; vanishing is exactly equality of all responses,
   proving `(FL.8)`.
3. Restrict `A^*A` to `K^perp`. In finite dimension it is positive definite, so the minimum of its
   Rayleigh quotient on the unit sphere is positive. This gives `(FL.9)` and compact quotient
   sublevels.
4. Linearity gives `(FL.10)`.
5. Apply Cauchy--Binet to `B^*B` for `(FL.11)`.
6. Apply the bounded-below/closed-range theorem to `A|_(K^perp)`. Negating the lower bound produces
   the adaptive unit escape sequence.

No arithmetic, compactness of an infinite unit sphere, or RH premise enters. The first possible
proof defect is use of `pdet(L)` when `r=0`; the convention `pdet(0)=1` makes `(FL.11)` valid, or the
statement may explicitly assume `r>0`.

## 6. Hostile significance audit

### Attack A — this is frame/Gram theory

**Verdict:** correct. Kernel, spectral gap, closed range, and Cauchy--Binet are established linear
analysis. The abstract theorem cannot be labelled new scientific knowledge. Its candidate field
content is the coupling to source-coherent response formation and the fixed-versus-adaptive
selection distinction.

### Attack B — arbitrary response maps encode the answer

**Verdict:** fatal unless source marking is enforced. Conjecture 3.1 is a receiver theorem. A route
enters the field only after each `rho_i` is derived functorially from the same pre-target source
intervention. Choosing `rho_i` from desired endpoint signs is circular.

### Attack C — injectivity already solves selection

**Verdict:** false for the intended global problem. Injectivity proves algebraic identifiability and
fixed-ray expulsion. It does not give a uniform lower bound, closed range, compact quotient
sublevels, or control of adaptive histories. The adaptive-escape clause is load-bearing.

### Attack D — increasing rank or hypertranscendence forces properness

**Verdict:** false. Diagonal maps with singular values tending to zero are injective and can have
unbounded rank while their lower frame bound is zero. Hypertranscendence may generate new response
directions without controlling their metric strength.

### Attack E — phase recurrence contradicts formation properness

**Verdict:** false. A compact phase quotient can recur while its lifted response packet has positive
formation energy. Conversely bounded characters may separate points yet have no uniform frame
bound in the admitted completion.

## 7. Internal collision ledger

- `[CORPUS]` `SourceCoherentInterventionSynchronization.lean` already proves pairwise response
  reconstruction and equalizer selection, but not the positive Laplacian, spectral margin, or
  adaptive-escape dichotomy.
- `[CORPUS]` `SharedGaugeQuotientFusion.lean` already proves the scalar weighted pairwise-variance
  identity and refinement conservation, but not the operator/kernel/properness package.
- `[CORPUS]` `NormingFaceFusion.lean` proves Helly witness bounds and cofinal dimension escape for a
  different norming-face defect. It does not identify a response Laplacian or its lower frame wall.
- `[CORPUS]` global formation properness proves fixed one-dimensional scale-orbit selection from a
  canonical Bernoulli reporter. It does not control adaptive displacement sequences.
- `[LOCAL-RESEARCH]` phase/open-lift and oriented-place programmes already kill the claim that phase
  or orientation alone supplies global topology.

## 8. External parent boundary

- Frame operators, observability Gramians, graph Laplacians, synchronization spectra, and the
  bounded-below/closed-range theorem occupy the operator theory.
- Cauchy--Binet and pseudo-determinant Pythagorean identities are explicit in Knill,
  [*Cauchy--Binet for Pseudo-Determinants*](https://arxiv.org/abs/1306.0062).
- Discrete exponential-family support chambers are controlled by oriented matroids in Rauh--Kahle--Ay,
  [*Support Sets in Exponential Families and Oriented Matroid Theory*](https://arxiv.org/abs/0906.5462).
- Dymetman,
  [*Exponential families from a single KL identity*](https://arxiv.org/abs/2604.28036), shows how much
  exponential-family convex duality already follows from one KL identity; this kills any novelty
  claim for the earlier KL-coordinate atlas.
- Current cumulant/Fisher hypergraph work, for example Bal--Klute--Maier--Spannowsky,
  [*From Information Geometry to Jet Substructure*](https://arxiv.org/abs/2605.03063), already
  identifies higher cumulants with local information tensors and hyperedges.

No literature hit found for the exact HGT interpretation coupling source-coherent multi-organ
formation, quotient synchronization, Pluecker selection margin, dilation selection, and adaptive
escape. This absence is not a priority claim. The theorem remains a `[BRIDGE]` unless a literal
source application yields a withheld result.

## 9. Frontier prediction

The theorem predicts a sharp two-level audit for every claimed global selector.

1. **Algebraic gate:** compute `K`. If the RH displacement line lies in `K`, no amount of bounded
   work, recurrence, positivity, or completion can select it.
2. **Uniform gate:** compute the lower formation-frame bound. If it is zero, every fixed
   displacement may be visible while adaptive/cofinal null flags still evade selection.

Therefore a successful global source theorem must prove more than nonzero response. It must prove a
source-generated frame inequality on the completed displacement quotient. This is a new exact
obligation for the universal-law-field programme and a falsifier for purported global selection
arguments.

## 10. Promotion gates

- [x] killed chamber-atlas predecessor recorded with exact reason;
- [x] internal corpus collision audit completed;
- [x] current primary-literature audit completed for the immediate parent mechanisms;
- [x] dependency-closed proof of all six clauses written;
- [x] hostile correctness audit of edge cases (`I` singleton, `K=V`, zero-dimensional quotient,
  nonclosed range, infinite-dimensional quotient);
- [x] promoted exact theorem to Stage 2:
  `formation-laplacian-properness-mechanics/source-response-laplacian-properness-pluecker-and-adaptive-escape-law.md`;
- [x] no Lean work performed before paper-proof promotion; Lean formalization remains pending.
