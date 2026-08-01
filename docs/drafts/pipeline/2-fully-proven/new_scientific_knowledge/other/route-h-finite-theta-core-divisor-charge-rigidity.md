# Route H finite theta-core divisor-charge rigidity

- **ID:** `route-h-finite-theta-core-divisor-charge-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / ROUTE-CLOSURE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../1-in-progress/xi-taylor-theta-tail-core-density-current.md`, Route H
- **Statement:** At every Xi zero, every source-selected odd superaccurate finite theta-tail core
  carries the exact analytic multiplicity as its anisotropic horizontal normalized current. A
  fixed meromorphic gauge changes that charge only by its integer local order, so exact screening
  requires the gauge to contain the Xi divisor with matching multiplicity.

## Goal and non-theatre standard

Route H's remaining premise is already equivalent to RH:

```text
XiCTaylorThetaTailCoreCurrentSublinearUpper D <-> RiemannHypothesis.
```

Another sufficient inequality, decomposition, or conditional zero-free statement therefore does
not count as progress. Closure requires a theorem explaining why every completed source
refinement returns the same obstruction and classifying which coordinate changes can remove it.

The survivor below adds information absent from the iff: the raw finite theta core is a
multiplicity-exact divisor transducer. It also gives a sharp gauge-screening classification. The
result is unconditional but is not an RH proof; it describes what would occur at a hypothetical
off-line zero.

## Frozen theorem

Fix a source-selected odd superaccurate schedule `D`. For `sigma : C`, set

```text
N_n     = n+1,
s_n     = xiTaylorAnisotropicRightApprox sigma N_n,
z_n     = xiCTaylorCenteredPoint s_n,
alpha   = xiCTaylorCenteredPoint sigma,
x_n     = Re(s_n-sigma),
k_n     = xiCTaylorAnisotropicScheduleStage sigma n,
d_n     = D(k_n),
P_n     = xiCTaylorPolynomial (2*d_n+3),
U_n     = xiCTaylorThetaTailCorePolynomial d_n,
E_n     = xiCTaylorThetaTailTopDefectPolynomial d_n.
```

Then `P_n=U_n-E_n`. If `xi(sigma)=0` and

```text
m = analyticOrderAt(xi,sigma).toNat >= 1,
```

the exact Route H charge law is

```text
x_n * orientedPolynomialCurrent(U_n,z_n) / normSq(P_n(z_n)) -> m.       (H.1)
```

The denominator is eventually positive. Equivalently, since `1/N_n <= x_n < 2/N_n`, the raw core
current has positive linear normalized size on every hypothetical divisor fibre, and its
mesh-rescaled value recovers the full multiplicity rather than merely detecting a pole.

For a fixed centered meromorphic gauge `G` with local order `ell` at `alpha`, define its
logarithmic transfer charge by

```text
x_n * Im(logDeriv(P_n,z_n) - logDeriv(G,z_n)).                           (H.2)
```

Then

```text
(H.2) -> m-ell.                                                         (H.3)
```

Thus every analytic unit has `ell=0` and preserves the full charge. A fixed meromorphic gauge
screens the fibre exactly only when `ell=m`; such a gauge already contains the hypothetical Xi
divisor with its exact multiplicity.

## Heavy conjecture / hostile falsification loop

### H1 — positivity of the theta density signs the raw core

**Bold claim.** Positivity, evenness, strict decrease, or the Green relation for the completed
theta density forces the core current to be sublinear.

**Attack.** Compare with the exact finite cores and the completed C2 current. Positive decreasing
densities already admit nonreal finite-core zeros; Planat's completed theta-kernel representation
leaves a sign-indefinite off-diagonal sector; the C2 zero-safe factorization forces an oriented
odd divisor germ at every Xi zero.

**Verdict.** Rejected. Scalar density positivity does not control the off-diagonal Hermitian
phase required by Route H.

### H2 — deeper Haar/Prouhet refinement dissipates the current

**Bold claim.** Increasing arithmetic depth moves the surviving current into smaller rows until
it vanishes.

**Attack.** Use the exact refinement conservation law. Prefix current tends to zero, while the
finite arithmetic remainder tends to four times the unresolved raw core current. Top-row
elimination changes its representation but not its value.

**Verdict.** Rejected. Refinement conserves the obstruction and eventually isolates it.

### H3 — a fixed zero-free analytic gauge screens the pole amplifier

**Bold claim.** Dividing by the zero-free full theta-density phase, or by a better fixed analytic
source gauge, removes the linear anisotropic current.

**Attack.** A local analytic unit has bounded logarithmic derivative. Multiplication by `x_n`,
where `x_n=O(1/N_n)`, sends its contribution to zero. The Taylor section retains charge `m`.

**Verdict.** Rejected. This includes the full-density transfer no-go as one instance.

### H4 — a fixed meromorphic gauge can cancel without knowing the divisor

**Bold claim.** Allowing a singular source gauge makes screening possible without importing zero
data.

**Attack.** The logarithmic residue of a meromorphic germ is its integer order `ell`. Anisotropic
scalarization gives transfer charge `m-ell`.

**Verdict.** Rejected except at the sharp boundary `ell=m`. Exact cancellation forces matching
support and multiplicity, so the gauge already carries the divisor it was meant to prove absent.

### H5 — the crude pole lower bound is the whole obstruction

**Bold claim.** The existing eventual `m/20` lower estimate contains all available local
information.

**Attack.** Retain the horizontal mesh displacement instead of discarding it in a coarse norm
bound; transfer the normalized residue through the superaccurate Taylor and top-defect limits.

**Verdict.** False. The surviving law is the exact limit (H.1), which recovers multiplicity.

### H6 — a nonstationary gauge still belongs to Route H

**Bold claim.** An `n`-dependent gauge with no locally meromorphic limit can cancel the charge and
should be treated as a final refinement of the same route.

**Attack.** Any locally convergent meromorphic family with eventually fixed order falls under
(H.3). Escaping it requires a compensating order/derivative growing at the mesh scale, loss of
local normality, or explicit divisor-dependent singularities.

**Verdict.** Not ruled out, but it changes the mathematical object. Such a construction is a new
non-normal moving-gauge route and must prove source selection independently; it does not reopen
Route H's fixed theta-core/refinement representation.

## Internal-priority audit

- `XiAnisotropicPoleGrowth.lean` proves normalized Xi residue convergence and only the coarse
  eventual lower rate `m/10`.
- `XiCTaylorAnisotropicSublinearGate.lean` transfers this to finite Taylor logarithmic derivatives
  and only records the coarse lower rate `m/20`.
- `XiCTaylorThetaTailCoreCurrentEquivalence.lean` proves the core-current premise equivalent to RH,
  but does not identify the core's limiting charge at a hypothetical zero.
- `XiCTaylorThetaTailCoreCurrentCapstone.lean` proves exact arithmetic refinement conservation,
  but does not recover divisor multiplicity from the raw finite core.
- `ThetaCuspCenterMixedDivisorTomography.lean` proves a zero-safe local multiplicity germ for the
  completed Xi current. It does not transfer that charge to source-selected finite Taylor cores
  or classify fixed gauge screening on the anisotropic mesh.
- `LogarithmicResidueQuantization.lean` supplies the classical meromorphic-order residue theorem,
  but not its Route H anisotropic scalarization or finite-core consequence.

Hence (H.1) is a genuine internal synthesis delta. Because its inputs are classical residue
calculus plus existing repository constructions, classification remains `[BRIDGE]`; no external
priority claim is made.

## External primary-source audit

1. Sondow--Dumitrescu, arXiv:1005.1104, proves horizontal Xi-modulus monotonicity in zero-free
   half-planes and an RH reformulation, not finite theta-core multiplicity recovery.
2. Romik, arXiv:1902.06330, proves orthogonal-polynomial expansions and coefficient asymptotics
   for Xi, not an all-scale off-diagonal current sign or (H.1).
3. Jenkins--McLaughlin, arXiv:1609.05965, proves global growing-degree Taylor asymptotics and
   convergence of bounded spurious-zero fibres to Xi zeros; this supports, rather than removes,
   divisor retention.
4. Dimitrov--Xu, arXiv:1606.05011, treats Wronskians of same-source Fourier/Laplace transforms and
   correlation kernels, not mixed-source finite-core cancellation.
5. Planat, posted 2026-06-01, derives the exact theta-kernel double integral and localizes the
   unresolved critical-aperture positivity to an RH-equivalent off-diagonal sector. It does not
   state (H.1) or the fixed-gauge order classification.
6. Classical logarithmic-residue theory owns the fact that a meromorphic logarithmic derivative
   has residue equal to divisor order. The Route H theorem is therefore not claimed as a new
   residue theorem.

Exact formula and phrase searches found no external finite-theta-core version of (H.1). Absence
from search is not priority evidence; external status remains `[NOVELTY UNVERIFIED]`.

## Dependency-closed paper proof

### Lemma 1 — anisotropic scalarization of a complex residue

Write

```text
delta_n = s_n-sigma = x_n+i*y_n,
Delta_n = z_n-alpha = -i*delta_n = y_n-i*x_n.
```

Mesh geometry gives

```text
1/N_n <= x_n < 2/N_n,       |y_n| < 1/N_n^2,
norm(delta_n^-1) <= N_n.                                             (P1)
```

Let `L_n` be any complex sequence such that

```text
Delta_n*L_n -> q,             q real.                                (P2)
```

The sequence `A_n=Delta_n*L_n` is bounded. Since

```text
L_n = Delta_n^-1*A_n,
```

(P1) gives `norm(L_n)<=C*N_n` eventually. Taking real parts in (P2),

```text
Re(Delta_n*L_n) = y_n*Re(L_n) + x_n*Im(L_n).                         (P3)
```

The first term has absolute value at most `C/N_n`, hence tends to zero. The left side tends to
`q`. Therefore

```text
x_n*Im(L_n) -> q.                                                    (P4)
```

This proof uses no Diophantine property of `sigma` and is valid for repeated zeros and negative
meromorphic orders.

### Lemma 2 — exact finite Taylor charge

The centered coordinate is an affine biholomorphism and preserves analytic order. At
`alpha=xiCTaylorCenteredPoint sigma`, Xi therefore has order `m`, and logarithmic-residue calculus
gives

```text
Delta_n*logDeriv(XiC,z_n) -> m.                                      (P5)
```

Superaccuracy on the anisotropic schedule already proves

```text
norm(logDeriv(P_n,z_n)-logDeriv(XiC,z_n)) -> 0.                       (P6)
```

Because `Delta_n->0`, multiplying (P6) by `Delta_n` preserves the limit in (P5). Apply Lemma 1:

```text
x_n*Im(logDeriv(P_n,z_n)) -> m.                                      (P7)
```

For every polynomial, including at zero under the totalized field convention,

```text
Im(logDeriv(P,z)) = orientedPolynomialCurrent(P,z)/normSq(P(z)).      (P8)
```

The local Xi lower bound and superaccuracy make `P_n(z_n)` nonzero eventually, so (P7)--(P8) are
an ordinary positive-denominator identity on the tail.

### Lemma 3 — top-defect removal is charge-negligible

Use the exact source splitting `P_n=U_n-E_n`. Expanding the Hermitian current gives

```text
J(P_n)=J(U_n)
       -Im(U_n' conjugate(E_n))
       -Im(E_n' conjugate(U_n))
       +J(E_n).                                                       (P9)
```

Hence

```text
|J(U_n)-J(P_n)|
 <= cross_n + norm(E_n')*norm(E_n),                                  (P10)
```

where `cross_n` is the two-term unsigned cross interference already defined in Route H.

The Taylor lower bound is `norm(P_n(z_n)) >= c/N_n^m` after a harmless fixed factor. The defect
value and derivative are each below the superaccurate tolerance, and that tolerance beats every
fixed inverse power. Consequently `2*norm(E_n(z_n))<=norm(P_n(z_n))` eventually. Since
`U_n=P_n+E_n`, the triangle inequality then gives `norm(E_n)<=norm(U_n)`, so the self term in
(P10) is bounded by the second summand of `cross_n`. Thus

```text
|J(U_n)-J(P_n)| <= 2*cross_n                                         (P11)
```

eventually.

The unconditional cross theorem states

```text
cross_n = o(N_n*normSq(P_n(z_n))).                                   (P12)
```

Using `0<x_n<2/N_n`, (P11)--(P12) imply

```text
x_n*(J(U_n)-J(P_n))/normSq(P_n(z_n)) -> 0.                            (P13)
```

Adding (P13) to (P7)--(P8) proves (H.1).

### Lemma 4 — fixed meromorphic gauge classification

Let `G` be meromorphic at `alpha` with integer order `ell`. Classical logarithmic-residue
quantization gives

```text
Delta_n*logDeriv(G,z_n) -> ell.                                      (P14)
```

Lemma 1 gives

```text
x_n*Im(logDeriv(G,z_n)) -> ell.                                      (P15)
```

Subtract (P15) from (P7) to obtain (H.3). If `G` is an analytic unit, `ell=0`. The transfer charge
vanishes exactly when `ell=m`, proving the sharp screening classification.

### Corollary — terminal Route H disposition

At a zero, `m>=1`, so (H.1) forces a positive tail charge. The Route H sublinear premise would,
using `x_n<2/N_n`, force the same charge arbitrarily close to zero. Hence the premise excludes the
zero; the existing equivalence shows this is exactly RH.

Arithmetic/Haar/Prouhet refinements cannot change that conclusion because their exact finite
remainder conserves the raw core current and converges back to it. Fixed analytic gauges preserve
the charge; fixed meromorphic gauges remove it only by importing the divisor. Route H is therefore
complete as a divisor-detection coordinate and exhausted as an independent source proof
mechanism.

## Stage 2 hostile referee audit

- **Weakest lemma:** Lemma 3. Its only quantitative inputs are already proved: local Xi value
  lower bound, superaccurate top-defect value/derivative bounds, and cross interference
  `o(N*normSq(P))`. No sign is assumed.
- **Sign convention:** `z_n-alpha=-i(s_n-sigma)`, so
  `Re((z_n-alpha)L)=y_n Re(L)+x_n Im(L)`. Positive right displacement therefore reads positive
  centered oriented current.
- **Repeated zeros:** `m` is arbitrary positive analytic order; no simplicity premise occurs.
- **Zero safety:** denominator is used only on an eventually nonzero Taylor tail. Raw polynomial
  currents remain totalized before this tail is selected.
- **Circularity:** theorem assumes a zero only to classify its forced current germ. It never
  assumes RH, zero-free regions, simplicity, or a source sign.
- **Quantifiers:** statement holds for every source-selected odd superaccurate schedule and every
  Xi zero, not a sampled schedule or selected zero.
- **Gauge boundary:** classification covers every fixed meromorphic germ. It deliberately does
  not claim to cover non-normal moving gauges; those constitute a different route.
- **Novelty:** internal delta is exact and nontrivial; external classification remains
  `[NOVELTY UNVERIFIED]`.

## Formalization obligations

- [ ] Formalize anisotropic complex-residue scalarization.
- [ ] Formalize exact finite Taylor horizontal charge limit.
- [ ] Formalize current perturbation bound and eventual top-defect domination.
- [ ] Formalize raw finite theta-core multiplicity charge (H.1).
- [ ] Formalize fixed meromorphic gauge order transfer (H.3).
- [ ] Wire new module into `RHTower.lean`.
- [ ] Run foreground file check, targeted module build, lint, and axiom audit.

## No-go closure

- **Exact killing theorem/mechanism:** (H.1) makes the raw finite theta core a
  multiplicity-exact divisor detector; exact refinement conservation returns the same current.
- **Strongest positive survivor:** full finite-core charge tomography plus the fixed meromorphic
  gauge screening law `m-ell`.
- **New insight:** Route H's current is not uncontrolled source noise. It is the conserved Xi
  divisor charge. A source-only cancellation must either prove the divisor absent or introduce a
  matching singularity carrying the same divisor data.
- **Status:** dependency-closed paper proof complete; Lean formalization pending.

## Log

- 2026-08-01 — exact RH-equivalent endpoint and all completed refinements audited.
- 2026-08-01 — heavy conjecture/falsification loop isolated finite-core multiplicity charge as
  strongest survivor.
- 2026-08-01 — external primary-source audit and dependency-closed paper proof completed.
