# Global Calderón chirality-kernel reduction

- **ID:** `deninger-global-calderon-chirality-kernel-reduction`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Label:** `DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION`
- **Parent:** `deninger-arithmetic-calderon-global-chirality-kernel`
- **Statement:** global chirality-kernel vanishing reduces to exact
  positive Cauchy-data transversality and relative Cauchy uniqueness;
  no uniform lower bound is required.

## Set-up

Let \(E\) be the real Hilbert boundary-data space, \(L\subset E\) the
closed arithmetic incidence subspace, and
\[
  A:E\longrightarrow E
\]
the global Dirichlet-to-Neumann operator.  Its Calderón Cauchy data
are \(\operatorname{graph}A\), while incidence Cauchy data lie in the
linear conormal
\[
  N^*L=L\times L^\perp.
\]
Let \(H^1_{\mathrm{rel}}\) be relative harmonic middle cohomology,
\(S:H^1_{\mathrm{rel}}\to H^1_{\mathrm{rel}}\) the arithmetic
chirality representative, and
\(\gamma:H^1_{\mathrm{rel}}\to E\) its boundary trace.

Assume:

1. \(A\) has a Green energy
   \[
     \langle Ax,x\rangle=\mathcal E(x);
   \]
2. \(\mathcal E(x)\ge0\), and
   \(\mathcal E(x)=0\Rightarrow x=0\);
3. \(Sx=0\) implies
   \[
     (\gamma x,A\gamma x)
       \in\operatorname{graph}A\cap N^*L;
   \]
4. relative Cauchy uniqueness holds:
   \[
     Sx=0,\quad\gamma x=0\quad\Longrightarrow\quad x=0.
   \]

## Theorem

`[PROVED HERE] [DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION]`

Under assumptions 1--4,
\[
  \ker S=0.
\]

### Proof

Assumptions 1--2 imply strict positivity without a uniform gap.  If
\(x\ne0\), then \(\mathcal E(x)\ne0\); together with
\(\mathcal E(x)\ge0\), this gives
\[
  \langle Ax,x\rangle>0.                                    \tag{1}
\]

Take \(u\in\ker S\).  By assumption 3,
\[
  (\gamma u,A\gamma u)\in
  \operatorname{graph}A\cap(L\times L^\perp).
\]
Hence \(\gamma u\in L\), \(A\gamma u\in L^\perp\), and
\[
  \langle A\gamma u,\gamma u\rangle=0.
\]
Strict positivity `(1)` forces \(\gamma u=0\).  Assumption 4 then
forces \(u=0\).

## Arithmetic effect

This removes two unnecessary demands from
`DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL`:

- finite-stage spectral gaps need not be uniform;
- injectivity need not be passed abstractly through a nonclosed
  limit.

Required source statements are instead exact and geometric:

1. global Green energy is nonnegative and detects zero;
2. the chirality-zero boundary equation is precisely the
   Calderón-graph/conormal intersection;
3. zero full Cauchy data determine a relative harmonic class.

For a quadratic Green energy, item 2 is an Euler--Lagrange identity.
Writing the allowed boundary positions as \(L\), constrained
stationarity is
\[
  x\in L,\qquad
  \langle y,Ax\rangle=0\quad(y\in L).                         \tag{1a}
\]
The second condition is exactly \(Ax\in L^\perp\), so `(1a)` is
equivalent to
\[
  (x,Ax)\in\operatorname{graph}A\cap N^*L.
\]
Thus source work need only identify \(Sx=0\) with the constrained
Green Euler--Lagrange equation; graph/conormal membership then follows
formally.

Local Dirichlet energy, positive Hodge--Koszul contraction, and the
completed Arakelov endpoint sequence are intended to prove item 1.
Global Green--Stokes and the derived Tate--Milnor incidence relation
prove item 2.  Unique continuation on each generic, prime-cusp, and
real-apex chart plus overlap descent proves item 3.

The theorem does not construct these arithmetic source objects; it
identifies the minimal inputs that close their chirality kernel.

## Restricted all-place energy

Let \(\mathcal E_i(x)\ge0\) be a summable family of local energies and
assume
\[
  \bigl(\forall i,\ \mathcal E_i(x)=0\bigr)\Longrightarrow x=0.
                                                               \tag{2}
\]
Then
\[
  \mathcal E_{\mathrm{arith}}(x)
    =\sum_i\mathcal E_i(x)
\]
is nonnegative and detects zero.  Indeed, each term is bounded above
by the nonnegative sum.  If the sum is zero, every term is both
nonnegative and at most zero, hence vanishes; `(2)` gives \(x=0\).

This is the exact all-place passage needed by the kernel theorem.
Local coercivity constants may tend to zero.  Required analytic input
is summability in the restricted source energy channel, not a
place-uniform spectral gap.

Relative Cauchy uniqueness also has an exact descent form.  If zero
global Cauchy data give zero local Cauchy data on every chart, local
unique continuation kills every chart restriction, and chart
restrictions jointly separate global classes, then assumption 4
follows.  Thus no separate global unique-continuation principle is
needed beyond compatibility and descent of the proved local
principles.

## Lean status

Formalized in
`GaloisForLFunctions.RHTower.DeningerArithmeticPositiveCalderonKoszul`
as:

- `deningerCalderonGraph_conormal_iff_stationary`;
- `deningerConstrainedGreenStationary_eq_zero_of_positive`;
- `deningerStrictPositive_of_greenEnergy_detects_zero`;
- `deningerGlobalChirality_kernel_eq_bot`;
- `deningerGlobalChirality_kernel_eq_bot_of_greenEnergy`;
- `deningerTsumEnergy_nonnegative_and_detects_zero`;
- `deningerGlobalChirality_kernel_eq_bot_of_tsumEnergy`;
- `deningerRelativeCauchyUnique_of_localRestrictions`.

Checked against the card: `deningerGlobalChirality_kernel_eq_bot`
takes exactly assumptions 1--4 — strict positivity of the Green form,
the identification of the chirality-zero boundary equation with the
Calderón-graph/conormal intersection, and relative Cauchy uniqueness —
and concludes `ker S = ⊥`, by the card's argument: the intersection is
trivial, so the trace vanishes, and assumption 4 then kills the class.
`deningerStrictPositive_of_greenEnergy_detects_zero` derives the
strict positivity `(1)` from assumption 1 in the card's form
(nonnegative energy that detects zero, with no uniform gap), and
`_of_greenEnergy` and `_of_tsumEnergy` are the resulting packaged
theorems for a single energy and for the restricted all-place sum
`(2)`.

### Verification

- Direct command: `lake env lean` on the module — passes with no
  errors and no warnings.
- Cached module build: completes.
- Scratch `#print axioms` on all eight declarations: only `propext`,
  `Classical.choice`, `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: exact kernel reduction identified
- [x] 1 → 2 fully-proven: complete proof
- [x] 2 → 3 formalized: the kernel theorem, the energy criteria and the
      relative Cauchy uniqueness lemma, with cached build and axiom audit
- [ ] 3 → 4 publication-ready: assumptions 1--4 are the open arithmetic
      inputs — this card reduces the kernel question to them, it does not
      construct them

## References

- Karsten Fritzsch, Daniel Grieser, Elmar Schrohe, *The Calderón
  Projector for Fibred Cusp Operators*, arXiv:2006.04645.
- `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`.
- `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION`.

## Log

- 2026-07-27 — Replaced limit-stability and uniform-gap formulations
  by exact global Green-energy transversality and relative Cauchy
  uniqueness.
- 2026-08-01 — Closed the stage-3 gate: verified the module states the
  card's theorem under exactly assumptions 1--4, then ran the cached
  build and the declaration-axiom audit.  No new Lean was needed.
