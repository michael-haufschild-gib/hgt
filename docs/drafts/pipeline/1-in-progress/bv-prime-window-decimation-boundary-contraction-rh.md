# BV prime-window decimation boundary contraction to RH

- **ID:** `bv-prime-window-decimation-boundary-contraction-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, TOP-DOWN RH ROUTE, SOURCE GRAM CONSTRUCTION
- **Scientific status:** `[OPEN] [NON-CIRCULAR TARGET ISOLATED] [NOT AN RH PROOF]`
- **Parents:**
  `../2-fully-proven/not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/bv-prime-window-laurent-orientation-polarization.md`
- **Statement:** A source-defined positive scale-zero completion of the integer-dilation orbit of
  one fixed sharp BV prime window, on which square-index decimation is contractive and every
  uncensored Laurent functional is continuous, proves RH.

## Goal

Close the remaining common horizontal charge without assuming a sign on any zero residue.  The
desired theorem must construct positivity from the finite prime-polar coefficients themselves.  It
must not use zero locations, a divisor-indexed norm, Weil positivity, real-rootedness, or the
subpower coefficient estimate being pursued on the separate sharp-window route.

## 1. Fixed source orbit

Take the sharp window

```text
W(x)=1_[1,2](x)                                          (1)
```

and fix an integer `r>=2`; `r=2` is sufficient.  For odd `j in Z`, let `p_j` be the canonical
prime-polar coefficient of `W_j(x)=W(r^j x)`.  Put `q=r^2` and

```text
(D_q a)(N)=a(qN).                                        (2)
```

The proved coefficient law gives

```text
D_q p_j=p_(j+2).                                         (3)
```

Let

```text
P_W=span_C{p_j : j odd}.                                 (4)
```

This is a source-defined algebraic orbit.  No zero is used to define it.

At every zeta zero `rho` with `Re(rho)>1/2`, the dyadic sharp Mellin transform is nonzero.  Laurent
residue therefore defines a nonzero linear functional on `P_W`:

```text
ell_rho(p_j)=R_j(rho)
             =2m_rho r^(j(rho-1/2))M_W(rho+1/2).        (5)
```

Equations `(3)` and `(5)` give the exact covariance

```text
ell_rho(D_q a)=r^(2rho-1) ell_rho(a),   a in P_W.        (6)
```

## 2. Abstract contraction endpoint `[PROVED]`

Suppose there is a positive semidefinite Hermitian form `G` on `P_W` such that:

```text
(C1) the Hausdorff completion H_G is defined from prime-window coefficients only;
(C2) D_q extends to a contraction on H_G;
(C3) every ell_rho with Re(rho)>1/2 extends continuously and nontrivially to H_G. (7)
```

By Riesz representation, `ell_rho(a)=<a,k_rho>_G` for a nonzero `k_rho`.  Equation `(6)` implies

```text
D_q^* k_rho=conjugate(r^(2rho-1)) k_rho.                 (8)
```

The adjoint of a contraction has no eigenvalue of modulus greater than one, so

```text
r^(2Re(rho)-1)<=1.                                       (9)
```

For a right off-critical zero the left side is strictly greater than one, a contradiction.
Therefore no right off-critical zero exists.  Functional-equation reflection excludes the left
half and proves RH.

This endpoint is not the assumption that each residue norm is contractive.  One source form and
one coefficient operator must work simultaneously on the full algebraic dilation orbit before any
zero functional is evaluated.

## 3. Exact source Stein inequality

Write

```text
G_(i,j)=G(p_i,p_j).                                      (10)
```

Condition `(C2)` is equivalent to the finite-matrix Stein inequality

```text
sum_(i,j) c_i conjugate(c_j)
  (G_(i,j)-G_(i+2,j+2)) >= 0                            (11)
```

for every finitely supported coefficient family `c`.  Before completion, the exact decimation
identity gives the finite-cutoff positive relation

```text
sum_(N<=qX) |sum_i c_i p_i(N)|^2
 -sum_(N<=X) |sum_i c_i p_(i+2)(N)|^2
 =sum_(N<=qX, q does not divide N) |sum_i c_i p_i(N)|^2 >=0. (12)
```

Thus the sign needed in `(11)` is already present at every finite cutoff.  The open issue is not
positivity but a scale-zero limiting or finite-part procedure that simultaneously:

1. preserves the positive off-multiple defect in `(12)`;
2. produces finite Gram values on the orbit `P_W`;
3. makes the Laurent functionals `(5)` continuous and nonzero;
4. is canonical from the prime-window source and independent of the Xi divisor.

This is a constraint problem: construct one positive solution of a source Stein inequality with
faithful boundary evaluations.  No dynamical propagation of zeta zeros is requested.

## 4. Exact open core

> **[OPEN CORE]** Construct a canonical positive, scale-zero renormalized Gram form on `P_W` which
> is a boundary limit of the finite coefficient Grams, satisfies `(11)`, and admits the
> meromorphic Laurent functionals `(5)` as bounded nonzero functionals.

A useful equivalent formulation is a source-to-boundary graph map

```text
J:P_W -> H_G                                             (13)
```

with `J D_q=D_q J`, contractive target decimation, and continuous pole evaluation after canonical
BV continuation.  The graph must retain the principal-part coordinate rather than quotient it
away.

## 5. Firewalls and positive consequences

### Ordinary Dirichlet--Hardy space

It cannot be the completion in `(7)`.  Any coefficient source with an uncensored zeta pole is not
square summable: its ordinary Dirichlet series would otherwise be holomorphic on `Re(s)>1/2`,
contradicting the formal BV pole theorem.  This rules out a direct invocation of the
Hedenmalm--Lindqvist--Seip space.

**Positive requirement:** the completion must be a singular graph or boundary form carrying both
coefficient and principal-part coordinates.

### Polynomially weighted coefficient spaces

On the weight `sum |a(N)|^2N^(-2alpha)`, decimation has norm at most `q^alpha`.  The same argument
then yields only `Re(rho)<=1/2+alpha`.  Sending `alpha` to zero requires precisely a subpower source
estimate, which is a different active route.

**Positive requirement:** this card seeks a genuinely scale-zero boundary form directly; it does
not duplicate the subpower coefficient theorem.

### Inflating isometry is not the inverse on Laurent fibres

Let `S_q` insert a sequence on the indices divisible by `q`.  Although `D_qS_q=1` on coefficients,
the proved off-multiple layer has nonzero residue

```text
Res(F_j-q^(-s)F_(j+2))=(1-r^(-2))R_j.                  (14)
```

Therefore a faithful completion cannot collapse the off-multiple layer and declare `S_q` to be
the inverse of dilation on the one-dimensional Laurent fibre.

**Positive requirement:** retain the off-multiple defect as a genuine source boundary component;
only contractivity of `D_q`, not an artificial unitary identification, is admissible.

### Divisor-selected residue norm

Defining `G` by summing squared Laurent residues over zeros would make `(C3)` automatic, but its
positivity or contraction is already the RH orientation condition.

**Positive requirement:** `G` must be obtained from the finite coefficient identity `(12)` or an
equivalent prime/Gamma boundary formula before the divisor is read.

## 6. Analytic-provider no-go and singular survivor

Pole cancellation does expose the Laurent residue as an ordinary analytic jet, but an ordinary
analytic RKHS graph is impossible here. If critical-line point evaluation were continuous and
nonzero throughout an interval and exact decimation covariance held globally, every Riesz kernel
would be a peripheral eigenvector of the adjoint contraction:

```text
D_q^* k_(1/2+it)=conj(r^(2it)) k_(1/2+it).              (15)
```

On a subinterval shorter than one character period, the eigenvalues in `(15)` are distinct.
Peripheral eigenvectors of a contraction are orthogonal, so separability permits only countably
many of them. The interval is uncountable. The formal theorem is
`HTGeometry.countable_of_injective_peripheral_eigenvector_family`; its route application is
recorded in
`../3-formalized/not_new_scientific_knowledge/bv-copoisson-analytic-graph-peripheral-spectrum-no-go.md`.

Thus the viable construction must be singular:

```text
finite coefficient Stein positivity
  -> contractive source quotient with covariance modulo (Lambda)
  -> exact eigencharacter only on co-Poisson annihilator fibres
  -> bounded nonzero Laurent/conormal functional on those fibres
  -> contraction endpoint (8)--(9)
  -> RH.                                                  (16)
```

The multiplier-ideal defect is mandatory. It must absorb ordinary critical-line evaluations,
otherwise the continuum peripheral-spectrum contradiction returns. The exact open theorem is now
construction of this divisor-blind quotient norm and proof that its countable annihilator fibres
retain the Laurent principal part.

## 7. Literature calibration

- H. Hedenmalm, P. Lindqvist, and K. Seip,
  [*A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*](https://arxiv.org/abs/math/9512211),
  provides the ordinary square-summable coefficient model and explains why coefficient
  decimation is a natural contraction there; the meromorphic prime-polar orbit lies outside it.
- K. Seip, [*Zeros of functions in Hilbert spaces of Dirichlet series*](https://arxiv.org/abs/1206.2815),
  supplies bounded analytic evaluation in the Dirichlet--Hardy half-plane, but no meromorphic
  principal-part graph.
- J.-F. Burnol,
  [*Two complete and minimal systems associated with the zeros of the Riemann zeta function*](https://www.numdam.org/articles/10.5802/jtnb.434/),
  supplies source-defined Sonine zero evaluators.  It does not identify the BV coefficient
  decimation with a contraction on those spaces.
- J.-F. Burnol,
  [*Entrelacement de co-Poisson*](https://www.numdam.org/articles/10.5802/aif.2268/),
  is the closest source for a distributional boundary graph, but the Stein inequality `(11)` and
  the Laurent continuity in `(C3)` are not consequences stated there.

## Corpus interfaces

- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowContinuation.lean`
- `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDivisorTomography.lean`
- `formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowCancellation.lean`
- `formal/GaloisForLFunctions/RHTower/CCMSharpPrimeWindowSubpowerGate.lean`
- `../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-berezin-diagonal-reflection-law.md`
- `burnol-hedenmalm-boundary-null-graph-completion-rh.md`

## Gates

- [x] exact source dilation orbit
- [x] exact Laurent eigenfunctional covariance
- [x] abstract contraction-to-RH endpoint
- [x] finite-cutoff source Stein positivity
- [x] ordinary Dirichlet--Hardy completion excluded
- [x] polynomial-weight route separated from the active subpower route
- [x] inflation/coisometry shortcut excluded by the off-multiple residue
- [x] pole-cancelled ordinary analytic RKHS provider excluded by peripheral-spectrum countability
- [x] singular multiplier-ideal quotient classified as the strongest surviving provider
- [ ] construct the canonical scale-zero Gram renormalization
- [ ] construct contractive covariance modulo the co-Poisson multiplier ideal
- [ ] prove Laurent/conormal evaluation continuity only on annihilator fibres
- [ ] verify source purity without divisor-selected weights
- [ ] formalize only after the analytic construction exists on paper
- [ ] compose an unconditional proof of RH
