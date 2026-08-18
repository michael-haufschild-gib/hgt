# Source-horizontal Euler--Wold independent Krein Xi-residue transport

- **ID:** `source-horizontal-euler-wold-independent-krein-xi-residue-transport`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `source-horizontal-euler-gamma-cubic-negative-renormalized-channel` and Route-P
  completed Gamma/Julia Xi-divisor descent
- **Statement:** Transport literal negative Euler depth atoms and positive Wold prime counterterms
  through the same completed two-variable Gamma/polar residue as independent outer Krein legs,
  retaining the complete four-orientation Julia block, Xi-copy multiplicity, and the existing BV
  endpoint signed block; their coefficient-faithful combined landing is exactly the negative
  normalized summable defect.

## Goal

Close the residue-transport obligation exposed by the pre-Xi cubic producer without inserting an
arbitrary post-selection scalar. Determine whether faithful transport itself removes the primitive
budget wall or whether it exposes a stricter nonlinear physical-selection obligation.

## Frozen conjecture

Let

```text
g_rho(u) = ((u-pole(rho))(-i T_Gamma(u))(u+1-1/2))/m_rho,
t_q = 2 Re(rho-1/2),
O(c) = B(c)+B(conj c)+B(-conj c)+B(-c).
```

The corpus proves `g_rho -> rho-1/2` and `O(c)=diag(4||c||^2,4)`. For a real source
coefficient `a`, define the completed cubic orbit carrier

```text
C_a(c,q;u,v) = ((g_q(u)+g_q*(v))^3/(4 Re(rho-1/2)^3)) O(c) a.
```

The frozen claim is that the following literal specializations form three independent outer legs
on every retained Xi copy:

1. the already-proved BV endpoint signed source block;
2. negative Euler atoms
   `a_(p,k,N)=-(log p)^3 k^2 p^(-k)/H_N^3`;
3. positive Wold prime counterterms
   `b_(p,N)=woldCoeff(1,p)(log p)^2/H_N^3`.

Successive Gamma residues land the second and third legs in

```text
-2 G_N/H_N^3 O(c),    +2 W_N/H_N^3 O(c),
```

respectively. The BV leg lands unchanged in its existing signed endpoint block. Summing the two
new legs only after residue gives

```text
-2 D_N/H_N^3 O(c),    D_N=G_N-W_N>0,
```

which is nonzero at every finite clock and tends entrywise to zero. Summing identical selected
copy landings over the actual support fibre multiplies every component by exact analytic
multiplicity. No prime label, depth coefficient `k^2`, Schwarz orientation, or BV endpoint entry is
collapsed before its own residue theorem.

## Heavy-conjecture loop

### C1 -- arbitrary coefficient tensoring

`a(g_q+g_q*)^3` has the required residue for every scalar `a`.

**Verdict:** `[BRIDGE]`, scientifically insufficient. Arbitrary `a` can be pasted onto the source
carrier and does not show Euler/Wold source naturality or label preservation.

### C2 -- local-jet tensor family before summation

Use the literal Euler local third derivative at every `(p,k)` and the literal Wold prime
deformation coefficient at every `p`; transport each separately, then form finite prime sums and
the convergent depth series.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK`. Unlike C1, coefficients are fixed before Xi
selection by proved source derivatives. Strict positive defect proves the two families are not
duplicate presentations. Complete orientation orbit is retained as a matrix, not replaced by its
scalar corner.

### Predicted hostile consequence

Any linear coefficient-faithful reporter which sees both new legs with their source signs sees only
`-D_N/H_N^3 -> 0`. Therefore the transport cannot by itself provide an order-one negative physical
budget. If the conjecture is proved, the next open core is a nonlinear/non-spectral physical
selection which retains the Euler leg while treating the Wold leg as regulator data without
deleting its coefficient.

## Internal frontier

- `[CORPUS]` `tendsto_frankensteinCCMGammaCenteredResidueGauge`: multiplicity-normalized completed
  source residue recovers centered Xi coordinate.
- `[CORPUS]` `routePJuliaSharedOrientationOrbitBlock_eq_diagonal`: all four
  FE--Schwarz--Krein orientations remain in one exact matrix block.
- `[CORPUS]` `tendsto_frankensteinCCMGammaWoldBVKreinSignedSourceBlock`: existing BV endpoint block
  descends through selected residue.
- `[CORPUS]` `sourceHorizontalEulerGammaCubicNegativeAtom_eq_depthSum`: exact Euler depth
  coefficient is `k^2`.
- `[CORPUS]` `sourceHorizontalEulerGammaCubicMoment_eq_wold_add_defect` and
  `summable_sourceHorizontalEulerGammaWoldCubicDefect`: strict positive coefficientwise defect is
  summable.
- `[CORPUS]` `routePPrimitiveGammaJuliaXiActualSupportFiber_card`: actual selected copy fibre has
  exact analytic multiplicity.

## External boundary

Paugam's Connes--Meyer spectral pairing supplies unconditional functional-equation symplectic
exchange, not the present selected signed source splitting. Connes--Consani's semilocal framework
locates Weil positivity in compressed trace operators and states that the semilocal positivity
problem implies RH. Their later single-prime moment theory produces `q=1/p` Lambert-series moments,
but not an Euler-third-jet/Wold-counterterm independent Krein residue bundle. Meyer and Connes give
spectral/trace realizations of zeros and explicit formulae, not this coefficientwise selected
transport. Exact priority remains `[NOVELTY UNVERIFIED]`.

## Falsifiers

1. Any specialization which inserts only aggregate `G_N` after residue is scalar decoration and
   falsifies source faithfulness.
2. Any carrier which takes `Re` before the two source limits is not holomorphic completed descent.
3. Any direct sum which replaces `O(c)` by `4||c||^2` loses four-orientation structure.
4. Any multiplicity claim based only on a scalar factor, without actual support-fibre copies, loses
   copy faithfulness.
5. If combined landing is order one rather than normalized summable defect, a sign or double count
   is wrong.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, hostile falsifiers, internal/external frontier
- [ ] 1 -> 2 fully-proven: dependency-closed paper proof and hostile audit
- [ ] 2 -> 3 formalized: exact Lean module, leaf build, axiom audit
- [ ] 3 -> 4 publication-ready

## Approach

Prove one generic two-variable coefficient transport lemma, but admit only literal source-derived
Euler-depth and Wold-prime specializations into the capstone. Keep three outer components as a
function into `Matrix (Fin 2) (Fin 2) C`: BV, Euler, Wold. Use componentwise `Tendsto`, existing
four-orientation matrix identity, finite-sum linearity, exact depth `tsum`, and actual support-fibre
cardinality. Finish with strict finite defect and normalized-zero classification.

## Log

- 2026-08-18 -- C1 downgraded to bridge; C2 frozen after internal and bounded primary-literature
  audit.
