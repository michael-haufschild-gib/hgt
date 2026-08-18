# Source-horizontal Euler--Wold independent Krein Xi-residue transport

- **ID:** `source-horizontal-euler-wold-independent-krein-xi-residue-transport`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Status:** `[FORMALIZED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED] [NOT RH]`
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

The corpus proves `g_rho -> rho-1/2` and `O(c)=diag(4||c||^2,4)`. For hostile comparison only,
a real coefficient `a` defines the completed cubic orbit kernel

```text
K_a(c,q;u,v) = a ((g_q(u)+g_q*(v))^3/(4 Re(rho-1/2)^3)) O(c).
```

The frozen claim does **not** admit `a` as producer data. Introduce an independent real source
variable before either Gamma limit and form

```text
E_(p,k)(s,u,v) = p^(-k s)/k * K_1(c,q;u,v),
W_p(t,u,v) = sourceHorizontalWoldPrimeDeformation(p,t) * K_1(c,q;u,v).
```

Form one bivariate completed source by adding these two carriers. The third partial source
derivatives are taken first. They are forced respectively to
`-(log p)^3 k^2 p^(-k) K_1` at `s=1` and
`woldCoeff(1,p)(log p)^2 K_1` at `t=0`. Only then are the two completed Gamma residues taken.
The two jets occupy intrinsic source bidegrees `(3,0)` and `(0,3)`; their mixed `(3,3)` jet is zero.
These literal source jets form three independent outer legs on every retained Xi copy:

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

### C2 -- tagged local-jet direct sum

Use the literal Euler local depth source at every `(p,k)` and the literal Wold prime deformation at
every `p`; take third source derivatives while Gamma variables remain free, then take completed
residues, and only afterward form finite prime sums and the convergent depth series. Tag the two
landings by an external `Fin 2` index.

**Verdict:** `[FALSIFIED]` as a claim of genuine independence. The two landed matrices are scalar
multiples of the same orientation block. An external tag would declare independence rather than
derive it.

### C3 -- bivariate source-jet grading

Put Euler and Wold deformations in independent source coordinates `(s,t)` before tensoring with the
completed Gamma kernel. Define the legs as partial third jets of the resulting bivariate source.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK`. Independence is now the canonical
`Sym^3(ds)` versus `Sym^3(dt)` grading, and the mixed third-by-third jet vanishes because the source
is additively separated. No coefficient parameter occurs: coefficients are derivatives while
Gamma variables remain unselected. Strict positive defect proves the two pure jets are not
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

[Paugam's Connes--Meyer spectral pairing](https://arxiv.org/abs/0803.0199) supplies unconditional
functional-equation symplectic exchange, not the present selected signed source splitting.
[Connes--Consani's semilocal framework](https://arxiv.org/abs/2006.13771) locates Weil positivity in
compressed trace operators and states that the semilocal positivity problem implies RH. Their
[single-prime moment theory](https://arxiv.org/abs/2403.01247) produces `q=1/p` Lambert-series
moments, but not an Euler-third-jet/Wold-counterterm independent Krein residue bundle.
[Meyer](https://arxiv.org/abs/math/0412277) and
[Connes](https://arxiv.org/abs/math/9811068) give spectral/trace realizations of zeros and explicit
formulae, not this coefficientwise selected transport. Exact priority remains
`[NOVELTY UNVERIFIED]`.

## Falsifiers

1. Any specialization which inserts only aggregate `G_N` after residue, rather than differentiating
   the source-variable carrier before residue, is scalar decoration and falsifies source
   faithfulness.
2. Any claimed independence represented only by an external finite tag, without independent source
   variables and zero mixed jet, is formal theatre.
3. Any carrier which takes `Re` before the two source limits is not holomorphic completed descent.
4. Any direct sum which replaces `O(c)` by `4||c||^2` loses four-orientation structure.
5. Any multiplicity claim based only on a scalar factor, without actual support-fibre copies, loses
   copy faithfulness.
6. If combined landing is order one rather than normalized summable defect, a sign or double count
   is wrong.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, hostile falsifiers, internal/external frontier
- [x] 1 -> 2 fully-proven: dependency-closed paper proof and hostile audit
- [x] 2 -> 3 formalized: exact Lean module, leaf build, axiom audit
- [ ] 3 -> 4 publication-ready

## Approach

Use a generic two-variable Gamma kernel only as target. Construct one additive bivariate source in
independent Euler/Wold variables, prove its two pure third-jet tensor laws and vanishing mixed jet,
and admit only those derivative specializations into the capstone. Keep BV, Euler, and Wold
components in the induced source-jet grading with values in `Matrix (Fin 2) (Fin 2) C`. Use
componentwise `Tendsto`, existing
four-orientation matrix identity, finite-sum linearity, exact depth `tsum`, and actual support-fibre
cardinality. Finish with strict finite defect and normalized-zero classification.

## Dependency-closed paper proof

### 1. Literal bivariate source

Fix a retained copy `q`, put `z=rho-1/2`, `r=Re z>0`, and let

```text
K(c,q;u,v)=((g_rho(u)+g_conj(rho)(v))^3/(4r^3)) O(c).
```

For the `N`th ordered-prime clock `H_N=log p_N`, set `X_N=p_N+1` and define

```text
E_N(s)=primeEulerLogBelow(s,X_N),
W_N(t)=sum_(j<=N) sourceHorizontalWoldPrimeDeformation(p_j,t),
F_N(s,t;u,v)=H_N^(-3)(E_N(s)+W_N(t)) K(c,q;u,v).
```

All sums in `E_N` and `W_N` are finite near the differentiation points. Existing smoothness
theorems make both third derivatives legitimate. Since `K` is constant in `(s,t)`, the standard
constant-tensor derivative law gives

```text
partial_s^3 F_N(1,t;u,v)=H_N^(-3) E_N'''(1) K(c,q;u,v),
partial_t^3 F_N(s,0;u,v)=H_N^(-3) W_N'''(0) K(c,q;u,v).       (1)
```

After the first derivative, each right side is independent of the other source coordinate.
Consequently

```text
partial_t^3 partial_s^3 F_N(1,0;u,v)=0.                       (2)
```

Thus the two legs are intrinsic bidegrees `(3,0)` and `(0,3)`, not externally tagged copies of one
matrix.

### 2. Source coefficients retain prime and depth labels

Primes below `X_N=p_N+1` are exactly `p_0,...,p_N`. The proved Euler third-jet law and the ordered
prime enumeration therefore give

```text
E_N'''(1)=-G_N,
G_N=sum_(j<=N) G_(p_j).
```

For every prime, the proved local identity is

```text
G_p=(log p)^3 sum_(k>=1) k^2 p^(-k).                          (3)
```

Equivalently, each summand in `(3)` is the third derivative at `s=1` of
`p^(-ks)/k`: differentiating three times multiplies by `(-k log p)^3`, and division by `k`
leaves `-k^2(log p)^3p^(-k)`. This is the Euler sign and exact valuation multiplicity.

Finite differentiation of the Wold source and its proved local third-jet theorem give

```text
W_N'''(0)=sum_(j<=N) woldCoeff(1,p_j)(log p_j)^2=W_N.          (4)
```

Equations `(3)` and `(4)` prove coefficient faithfulness before either Gamma residue.

### 3. Completed Gamma/polar descent preserves the bigrading

The completed source gauge satisfies

```text
g_rho(u)->z,      g_conj(rho)(v)->conj z.
```

The two limits use independent variables. Taking them successively in either pure source jet of
`(1)` gives

```text
(z+conj z)^3/(4r^3)=(2r)^3/(4r^3)=2.                         (5)
```

No real-part operation is applied to `u` or `v`; `r` is the fixed selected conormal scale.
Combining `(1)`, `(4)`, and `(5)` yields the two selected landings

```text
L_E(N,c,q)=-2(G_N/H_N^3) O(c),
L_W(N,c,q)=+2(W_N/H_N^3) O(c).                               (6)
```

The matrix `O(c)` remains literally
`B(c)+B(conj c)+B(-conj c)+B(-c)` throughout. Hence all four orientations, including the common
environment pivot and its cancellation of cross terms, survive residue descent.

### 4. BV endpoint is an unchanged third component

The existing CCM/Gamma BV theorem already transports its complex first landing to

```text
diag(E_BV(N,c),-E_BV(N,c)),
E_BV(N,c)=8||c||^2 endpointThirdJet_N.
```

Taking the product of this proved BV source component with the two bigraded pure jets introduces no
new equality: projection to the BV component is definitionally the old source block and its residue
is definitionally the old selected signed landing. Thus endpoint defect and Krein sign are
preserved exactly.

### 5. Actual support-fibre multiplicity

For any `r` in `XiRightSupportFiber(q)`, support equality gives the same centered coordinate,
conjugate pole, and conormal scale as `q`. Hence `(6)` is identical on every actual copy. The corpus
identifies that finite fibre with `Fin(xiSupportMultiplicity(rho))`; summing the copywise landing
therefore gives

```text
sum_(r in support fibre) L_*(N,c,r)
  = xiSupportMultiplicity(rho) L_*(N,c,q)                    (7)
```

for `*=E,W`, and likewise componentwise for the BV landing. This retains analytic multiplicity by
actual copy summation rather than inserting a guessed scalar.

### 6. Exact combined landing and classification

The proved coefficientwise split is `G_N=W_N+D_N`, with every local defect strictly positive and
the defect series summable. Adding the two independent landings only after their separate residue
proofs gives

```text
L_E+L_W=-2(D_N/H_N^3)O(c).                                  (8)
```

Since `Finset.range(N+1)` contains at least the first prime, `D_N>0`. For `c!=0`,
`O(c)=diag(4||c||^2,4)` is positive definite, so `(8)` is strictly negative definite and in
particular nonzero at every finite clock. Summability gives `D_N` a finite limit while
`H_N^3->infinity`; therefore `(8)` tends entrywise to zero. The same remains true after the fixed
finite multiplicity factor in `(7)`.

This proves the frozen statement. It also proves the predicted hostile consequence: any linear
coefficient-faithful forgetful map which adds the Euler and Wold grades sees only the normalized
summable defect, not an order-one negative budget.

## Hostile proof audit

- **Not scalar decoration:** Euler and Wold coefficients arise as partial third derivatives of the
  bivariate source while `(u,v)` remain free. No coefficient argument exists in the producer.
- **Not artificial independence:** equation `(2)` proves source bigrading and zero mixed jet before
  direct-sum packaging.
- **No hidden RH:** the theorem is universally quantified over an existing retained copy. If RH
  holds the copy type is empty; no existence of an off-line zero is assumed or derived.
- **No simple-zero premise:** gauge divides by exact analytic multiplicity and support-fibre sum
  restores that multiplicity.
- **No orientation scalarization:** the target is the full `2x2` shared-orbit matrix, not only its
  physical corner.
- **No premature cancellation:** Euler and Wold residue theorems are separate; `(8)` is formed only
  afterward.
- **Sharp failure:** faithful linear physical addition necessarily tends to zero. Using the Euler
  order-one limit while silently discarding its positive Wold regulator would violate the frozen
  coefficient-faithful transport.

## Formal verdict

`[FORMALIZED] [AXIOM-AUDITED] [PRE-XI SOURCE DERIVATIVES] [NOVELTY UNVERIFIED] [NOT RH]`.
`SourceHorizontalEulerWoldIndependentKreinXiResidueTransport.lean` closes the residue-transport
obligation unconditionally. New `[OPEN CORE]` is a source-derived nonlinear or
non-spectral physical selection on the bigraded landing which can retain Euler's order-one negative
action while carrying Wold regulator data faithfully; every linear grade-forgetting reporter is
now classified by `(8)` and cannot do this.

## Log

- 2026-08-18 -- C1 downgraded to bridge; C2 frozen after internal and bounded primary-literature
  audit.
- 2026-08-18 -- hostile attack rejected externally tagged independence; C3 replaces it by intrinsic
  bivariate source-jet grading and a zero mixed jet.
- 2026-08-18 -- dependency-closed proof and hostile audit completed; exact C3 promoted to Stage 2.
- 2026-08-18 -- C3 formalized; exact leaf build passed. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Global static lint remains blocked by six unrelated,
  pre-existing unreachable HTGeometry modules.
