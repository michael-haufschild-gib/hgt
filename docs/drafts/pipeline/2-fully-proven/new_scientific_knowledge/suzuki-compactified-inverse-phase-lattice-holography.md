# Suzuki compactified inverse-phase lattice holography

- **ID:** `suzuki-compactified-inverse-phase-lattice-holography`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Lane:** Suzuki cofinal divisor compactification and measure transference
- **Parents:** `suzuki-donoghue-defect-spectral-measure-law`,
  `suzuki-global-phase-conjugacy-divisor-flow`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), together with its proved
  finite-aperture Livsic--Donoghue consequences
- **Statement:** Cayley compactification makes every normalized Suzuki inverse phase sharply
  `1/2`-Lipschitz.  Values and first derivatives on one fixed odd-`pi` phase lattice recover the
  complete moving Donoghue probability, and every cofinal sequence splits canonically into a
  labeled atomic survivor plus a positive residual measure created by phase-label escape.
- **RH used:** no
- **Computation used:** no

## Frontier problem

Global phase conjugacy solved finite-shift pole continuation, but left a topology mismatch in the
cofinal aperture limit.  Physical poles move on the noncompact real line, Clark weights change,
and locally uniform convergence of upper-half-plane carriers does not preserve point derivatives
at a moving boundary divisor.

The correct state is neither the carrier alone nor the real spectral measure alone.  Compactify
the physical line by `arctan` and pull every pole back to its fixed lifted phase label.  This turns
the entire divisor probability into a fixed-lattice first jet of one uniformly Lipschitz function.

## Setup

For any aperture and admissible shift, let

```text
Theta(x)=exp(i phi(x)),
phi(0)=pi,
phi : R -> R an increasing real-analytic bijection,
m=i(1+Theta)/(1-Theta).                                  (1)
```

Let `nu` be the canonical even-extension Donoghue spectral probability and

```text
dmu(t)=(1+t^2)dnu(t).
```

At an even-extension pole `x`,

```text
Theta(x)=1,
q(x)=phi'(x)>0,
mu({x})=2/q(x),
nu({x})=2/[q(x)(1+x^2)].                                (2)
```

Define the centered inverse phase and its Cayley compactification:

```text
X(y)=phi^(-1)(pi+y),
U(y)=arctan(X(y)).                                       (3)
```

The fixed even Clark lattice is

```text
y_k=(2k-1)pi,       k in Z.                              (4)
```

Indeed `pi+y_k=2pi k`, so `x_k=X(y_k)` is the `k`th even-extension pole.

## Theorem A: sharp compactified inverse-phase geometry `[PROVED HERE]`

The function `U` is real analytic, odd, and strictly increasing, with

```text
-pi/2 < U(y) < pi/2,
U(0)=0.                                                  (5)
```

It satisfies the sharp derivative law and bound

```text
U'(y)=1/[q(X(y))(1+X(y)^2)],
0<U'(y)<=1/2.                                            (6)
```

Consequently

```text
|U(y)-U(z)| <= |y-z|/2                                  (7)
```

for all real `y,z`.  The constant `1/2` is sharp.  Equality on an interval means that the residual
inner phase is constant there; global equality gives the single Cayley/ground carrier.

### Proof

The common anchor `Theta(i)=0` factors one upper-half-plane Blaschke factor:

```text
Theta(z)=b_i(z) S(z),
b_i(z)=(z-i)/(z+i),                                     (8)
```

where `S` is meromorphic inner.  On the real axis choose compatible phases

```text
phi=beta+sigma,
beta'(x)=2/(1+x^2),
sigma'(x)>=0.                                            (9)
```

The nonnegative residual speed is the boundary Poisson-kernel sum of the residual inner factor,
including any nonnegative exponential speed.  Thus

```text
q(x)=phi'(x)>=2/(1+x^2).                                (10)
```

Since `phi(X(y))=pi+y`, inverse differentiation gives

```text
X'(y)=1/q(X(y)).                                        (11)
```

Composing with `arctan` proves the identity in `(6)`, and `(10)` proves its upper bound.  The mean
value theorem gives `(7)`.

Oddness follows from the already proved symmetry `m(-x)=-m(x)`.  The relation
`m=-cot(phi/2)` and the normalization `phi(0)=pi` give

```text
phi(-x)=2pi-phi(x),
X(-y)=-X(y),
U(-y)=-U(y).                                             (12)
```

This proves Theorem A.

## Theorem B: fixed-lattice holography of the full spectral probability `[PROVED HERE]`

At every lattice point `(4)`,

```text
x_k=tan(U(y_k)),
p_k:=nu({x_k})=2U'(y_k)>0.                               (13)
```

Moreover

```text
sum_(k in Z) p_k=1.                                      (14)
```

Therefore the complete normalized Donoghue probability is reconstructed by the fixed-lattice
`C^1` jet of `U`:

```text
nu=sum_(k in Z) 2U'(y_k) delta_(tan(U(y_k))).            (15)
```

### Proof

The first identity in `(13)` is `tan(arctan x_k)=x_k`.  At `y_k`, equations `(6)` and `(2)` give

```text
2U'(y_k)
 =2/[q(x_k)(1+x_k^2)]
 =nu({x_k}).                                             (16)
```

The Donoghue deficiency vector is cyclic and normalized, so its pure-point spectral measure has
total mass one.  Summing `(16)` proves `(14)`--`(15)`.

The result is stronger than separate pole and residue convergence: one function on a fixed phase
line contains both, and its derivative samples are already probability weights rather than
unnormalized Nevanlinna residues.

## Theorem C: unconditional cofinal compactness and residual classification `[PROVED HERE]`

Let `U_n` be any sequence arising from arbitrary apertures and arbitrary admissible shifts.  Let

```text
p_(n,k)=2U_n'(y_k),
sigma_n=(arctan)_* nu_n
       =sum_k p_(n,k) delta_(U_n(y_k)).                  (17)
```

After passage to a subsequence, there exist:

1. an odd nondecreasing `1/2`-Lipschitz function

   ```text
   U_infinity : R -> [-pi/2,pi/2],
   U_infinity(0)=0,                                     (18)
   ```

   such that `U_n -> U_infinity` locally uniformly;

2. limits

   ```text
   p_k=lim_n p_(n,k) in [0,1],                           (19)
   ```

   simultaneously for every `k in Z`;

3. a probability measure `sigma` on the compact interval `[-pi/2,pi/2]` such that
   `sigma_n -> sigma` weakly.

Put

```text
u_k=U_infinity(y_k),
sigma_lab=sum_k p_k delta_(u_k).                         (20)
```

Then

```text
sum_k p_k<=1,
sigma>=sigma_lab,
sigma_res:=sigma-sigma_lab>=0,
sigma_res(total)=1-sum_k p_k.                            (21)
```

Thus every cofinal degeneration has an exact canonical decomposition

```text
compactified spectral limit
 = fixed-label atomic survivor + phase-label-escape residual. (22)
```

### Proof

Theorem A makes the family uniformly bounded and equi-Lipschitz on every compact phase interval.
Arzela--Ascoli plus a diagonal exhaustion gives locally uniform convergence and `(18)`.  The
numbers `p_(n,k)` lie in `[0,1]`; a second diagonal extraction gives `(19)` on the countable
lattice.  Compactness of probability measures on the compact projective interval gives a weak
limit `sigma`.

Fatou's lemma applied to the counting measure gives `sum p_k<=1`.  For every finite set `F` of
labels,

```text
sum_(k in F) p_(n,k) delta_(U_n(y_k))
 ->sum_(k in F) p_k delta_(u_k).                         (23)
```

The difference between `sigma_n` and the left side of `(23)` is positive.  Passing to the weak
limit shows that `sigma` dominates every finite partial survivor.  Monotone exhaustion of `Z`
gives `(21)`.

No derivative of `U_infinity` is asserted at the lattice: derivative convergence is stored in the
separate labels `p_k`.  This avoids a false `C^1` compactness claim.

## Corollary: exact criterion for tight pure-point survival `[PROVED HERE]`

Suppose along the extracted subsequence that

```text
sum_k p_k=1,
|u_k|<pi/2 for every k.                                  (24)
```

Then `sigma_res=0`, the physical measures are tight on `R`, and

```text
nu_n -> nu_infinity
     =sum_k p_k delta_(tan u_k)                          (25)
```

weakly.  If additionally `p_k>0` for every `k` and `u_k` is strictly increasing in `k`, the limit
has an infinite simple two-sided labeled divisor.

Indeed pointwise convergence of the probabilities `p_(n,k)` to a probability `p_k` implies
`ell^1(Z)` convergence.  A finite label head captures all but arbitrarily small mass; positions in
that head converge to finite `tan u_k`.  This proves both tightness and `(25)` by testing bounded
continuous functions.

Conversely, failure of `(24)` separates two independent defects:

```text
1-sum_k p_k > 0    : phase-label escape / unlabeled residual mass,
|u_k|=pi/2         : fixed-label physical escape to projective infinity. (26)
```

Coalescence `u_j=u_k` is a third, explicitly visible loss of simple divisor labels.

## Exact placement of the two known Suzuki boundary states

The compactification distinguishes the universal boundaries without ambiguity.

### Free clock homogenization

For the free carrier,

```text
x_(a,k)=(k-1/2)pi/a,
p_(a,k)=coth(a)/[a(1+x_(a,k)^2)].                        (27)
```

For every fixed phase label, `U_a(y_k)->0` and `p_(a,k)->0`: no fixed labeled atom survives.  Yet
the compactified probabilities converge to the pushforward of Cauchy probability under `arctan`,
namely normalized Lebesgue measure on `(-pi/2,pi/2)`.  Hence

```text
U_infinity=0,
sigma_lab=0,
sigma_res=du/pi.                                         (28)
```

Clock homogenization is therefore *pure phase-label residual mass*, not mysterious loss of the
probability normalization.

### Ground Cayley escape

For the ground carrier `m(z)=z`, the compactified generalized inverse phase is the clipped ramp

```text
U_ground(y)=clip(y/2,-pi/2,pi/2).                        (29)
```

The spectral probability escapes to the two projective endpoints.  Thus ground escape is visible
as endpoint mass/saturation, qualitatively different from the uniform residual in `(28)`.

These are exact boundary profiles; no numerical experiment is involved.

## What this changes at the RH frontier

The previously requested inverse-phase compactness theorem is now unconditional.  The cofinal
state space is compact after replacing moving real divisors by

```text
(U_n, sigma_n, (p_(n,k))_(k in Z)).                      (30)
```

The open producer is no longer vague "tightness plus weights."  It is the source theorem

```text
sigma_res=0,
|U_infinity(y_k)|<pi/2,
p_k>0 and target Xi lattice identities for every k.      (31)
```

Prime tangent tomography and finite-shift holonomy can now be asked to control fixed lattice jets
`U_n(y_k), U_n'(y_k)`, the topology in which the full normalized measure is exactly reconstructed.
This removes the earlier mismatch between high-clock source observables and moving Clark atoms.

It does not prove `(31)` and does not identify the Xi divisor.  It supplies the compact state,
sharp defect decomposition, and exact necessary-and-sufficient pure-point survival gate on which a
source argument can act.

## Hostile audit

1. **No hidden RH positivity.**  The only positivity is the finite-aperture inner phase speed and
   the normalized spectral probability, both unconditional for every admissible shift.
2. **No arbitrary shift selector.**  Compactness holds for every aperture/shift sequence.
3. **No false `C^1` convergence.**  Locally uniform profile convergence and pointwise lattice-jet
   convergence are extracted separately.
4. **No lost mass hidden by `arctan`.**  The compactified measures retain total mass one; missing
   fixed-label mass is the explicit positive residual `sigma_res`.
5. **No finite-atom overclaim.**  Infinite simple survival requires `p_k>0` and strict label
   separation for all `k`, stated explicitly.
6. **No generic compactness presented as RH.**  The theorem solves the topology and classification
   wall.  Vanishing of the residual and Xi identification remain source problems.
7. **Sharpness.**  The Cayley factor attains the `1/2` speed cap.  The free and ground states attain
   different boundary strata, so neither defect term can be removed.

## Literature and priority audit

The generic facts that meromorphic inner functions possess increasing analytic phases and Clark
weights are inverse angular derivatives are classical; see Hatinoğlu,
*Uniqueness theorems for meromorphic inner functions and canonical systems*,
[arXiv:2110.12384](https://arxiv.org/abs/2110.12384).  The Blaschke-factor Poisson-kernel phase
decomposition and Arzela--Ascoli theorem are likewise classical and are not claimed as new.

Suzuki does not introduce the normalized Donoghue probability, global phase chart, compactified
inverse phase, fixed-lattice derivative weights, or residual decomposition `(21)`.  Exact phrase
and concept searches of Suzuki's source, the repository, and arXiv found no source-specific theorem
of this form.  Candidate novelty is the exact synthesis `(3)`--`(31)`, particularly
`p_k=2U'(y_k)` and the canonical labeled-atomic/residual splitting of every cofinal Suzuki limit.
Specialist priority review remains required.

## Lean target

Formalize the dependency-closed exact core:

```text
suzukiCenteredInversePhase
suzukiCompactifiedInversePhase
suzukiCenteredInversePhase_phase
tan_suzukiCompactifiedInversePhase
suzukiAnchoredPhaseSpeed_floor
hasDerivAt_suzukiCenteredInversePhase
hasDerivAt_suzukiCompactifiedInversePhase
suzukiCompactifiedInversePhase_speed_mem
suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv
hasSum_two_mul_suzukiCompactifiedDeriv_one
suzukiCompactifiedInversePhase_lipschitz
```

The concrete inner factorization, spectral-measure sum, and measure-level compactness theorem
remain paper-level until Suzuki's operator and Clark measure are represented in Lean.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, exact module build green, axiom audit clean
- [ ] 3 -> 4 publication-ready: standalone paper, specialist priority review
- [x] unconditional compactified inverse-phase subsequential compactness
- [x] exact fixed-lattice reconstruction of support and probability weights
- [x] canonical labeled-survivor/residual decomposition
- [ ] source proof that the cofinal residual vanishes
- [ ] Xi divisor identification
- [ ] RH

## Log

- 2026-07-21 — created in Stage 1 after global phase conjugacy exposed inverse-phase lattice
  derivatives as the exact remaining cofinal state.
- 2026-07-21 — sharp anchored phase floor, compactified Lipschitz profile, fixed-lattice probability
  holography, cofinal residual decomposition, and pure-point survival criterion proved; promoted to
  Stage 2.
- 2026-07-21 — dependency-closed structural core formalized in
  `SuzukiCompactifiedPhaseProfile.lean`; exact module build, SOTA import, capstone axiom audit,
  global formal lint, and diff audit passed; promoted to Stage 3.
