# Global arithmetic Calderón chirality kernel

- **ID:** `deninger-arithmetic-calderon-global-chirality-kernel`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** the closed Hodge-symmetric arithmetic Calderón
  almost-involution has zero kernel on relative middle cohomology.

## Operator

Finite Kummer packets carry the exact chirality
\[
  S_\alpha=\operatorname{sgn}(D_{\ell,\alpha}),\qquad
  S_\alpha^*=S_\alpha,\qquad S_\alpha^2=1.                   \tag{1}
\]
Prime extended-cusp and real orientation-sign packets carry the
corresponding exchange involutions.  Glue their closed relations
through all Tate--Milnor incidence cells and the Meyer
\(Z\)/Fourier corrections.  After positive Hodge completion, let
\[
  S:\mathcal H^1_{\mathrm{arith}}
    \longrightarrow\mathcal H^1_{\mathrm{arith}}             \tag{2}
\]
be the resulting bounded self-adjoint representative.

Meyer's nuclear almost-polarization theorem predicts
\[
  S^2-1\in\mathcal N.                                       \tag{3}
\]

## Conjecture

`[CONJECTURE] [DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL]`

On endpoint-reduced arithmetic middle cohomology,
\[
  \ker S=0.                                                   \tag{4}
\]

More precisely, if a harmonic source class \(x\) satisfies \(Sx=0\),
the global Green identity and the full relative Milnor incidence
decompose its energy into nonnegative local terms:
\[
  \mathcal E_{\mathrm{arith}}(x)
  =
  \sum_\alpha
    \mathcal E_\alpha(x_\alpha)
  +\mathcal E_{\mathrm{inc}}(x).                              \tag{5}
\]
Equality \(Sx=0\) forces every term in `(5)` to vanish.  Local
Calderón trace isometry kills every nonconstant boundary packet;
positive Hodge--Koszul contraction kills finite Milnor momentum
directions; completed Arakelov endpoint exactness removes constant,
prime-residue, and real-apex remnants.  Therefore \(x=0\).
The exact positive-energy input is
`DAC_GLOBAL_GREEN_ENERGY_RADICAL`.

The abstract implication is now a theorem:
`DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION`.  It shows that `(4)`
follows from exactly three source statements:

1. the global Dirichlet-to-Neumann Green energy is nonnegative and
   detects zero;
2. \(Sx=0\) sends full Cauchy data into the intersection of the
   global Calderón graph with the Tate--Milnor incidence conormal;
3. a relative harmonic class with zero full Cauchy data vanishes.

No place-uniform lower bound is required.  Strict positivity follows
pointwise from nonnegativity plus zero-energy detection.

## Consequence

Since the nuclear ideal is compact, `(3)` makes \(S\) Fredholm.
Self-adjointness and `(4)` imply surjectivity and bounded
invertibility.  `DAC_POLAR_SIGN_LIFT_NUCLEAR_ALMOST_PROJECTOR` then
constructs the canonical exact involution
\[
  C=S|S|^{-1}
\]
and exact complementary orthogonal Hardy projectors
\[
  \Pi_\pm=(1\pm C)/2.
\]

Thus the completed-projector problem is reduced to the geometric
zero-energy classification `(5)`, not a stage-uniform spectral-gap
estimate.

## Proof program

1. Prove Hodge self-adjointness of `(2)` from the global Green
   relation and real orientation signs.
2. Prove `(3)` by passing Meyer's convolution-local nuclear defects
   through the strict source complex and harmonic projector.
3. Establish the exact global energy decomposition `(5)`, including
   cross-ray Milnor and \(Z\)/Fourier terms, and prove that its
   vanishing detects zero boundary data.
4. Prove that \(Sx=0\) is the constrained Green Euler--Lagrange
   equation.  `DAC_GREEN_EULER_LAGRANGE_GRAPH_CONORMAL` then converts
   it exactly to the Calderón-graph/incidence-conormal equation.
5. Apply local trace isometry and
   `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` to classify zero-energy
   packets.
6. Use the strict completed Arakelov sequence to show the remaining
   augmentation packet is an endpoint class, hence zero in relative
   \(H^1\).
7. Apply `DAC_LOCAL_FULL_CAUCHY_UNIQUENESS` on every chart and prove
   that full Cauchy restriction maps jointly separate classes in the
   strict Rost--Schmid totalization.  Then apply
   `DAC_RELATIVE_CAUCHY_UNIQUENESS_DESCENT`.
8. Apply `DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION`, conclude
   `(4)`, and apply the polar-sign theorem.

## Falsifiers

- Finite-stage kernel vanishing alone is insufficient; new kernel can
  appear after a nonclosed infinite limit.
- Dropping the restricted \(L^1\) product-formula channel may leave a
  zero-energy prime-residue packet.
- A nuclear defect without self-adjointness does not make kernel and
  cokernel agree.
- A constant/endpoint packet must be removed by the actual
  \(H^0/H^2\) sequence, not declared absent.
- No zeta zero or Paugam upper/lower zero-sector choice may define
  \(S\).

## Current boundary

- Finite graph/conormal intersection and complementary-sum
  transversality: paper- and Lean-proved.
- Summable nonnegative local energies detect zero globally without a
  uniform gap: paper- and Lean-proved.
- Local full-Cauchy uniqueness on Kummer, prime-cusp, and real-apex
  charts: paper-proved.
- Relative Cauchy uniqueness descent logic: Lean-proved.
- Open: strict global Green energy identity, identification of
  \(Sx=0\) with constrained Green stationarity, and compatibility of
  full chart traces with Rost--Schmid/coarse descent.

## Gates

- [x] 0 → 1 in-progress: exact operator and zero-energy attack
- [ ] 1 → 2 fully-proven: global energy decomposition and kernel
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-27 — Replaced an unnecessary uniform gap conjecture by
  global kernel vanishing.  Nuclear Fredholmness recovers the gap
  automatically.
- 2026-07-27 — Reduced global kernel vanishing to Green-energy
  detection, graph/conormal boundary reduction, and relative Cauchy
  uniqueness; formal abstract theorem direct-checks in Lean.
