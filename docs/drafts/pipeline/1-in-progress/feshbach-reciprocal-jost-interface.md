# A massless Schur channel forces reciprocal Jost momentum

- **ID:** `feshbach-reciprocal-jost-interface`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM / LOCAL DIFFERENTIAL PENCIL / QFT SOURCE PROBLEM
- **Scientific status:** `[ALGEBRAIC CORE PROVED] [JOST DETERMINANT BRIDGE PROVED]`
  `[WICK-ROTATED MASS LADDER PROVED] [POSITIVE LOCAL GFF BRIDGE PROVED]`
  `[INTERACTING POSITIVE-QFT COMPLETION OPEN]`
  `[NOVELTY UNVERIFIED]`
- **Scope:** general hypertranscendental quantum scattering and integrable QFT; no RH or
  distinguished special-function input
- **Parent:** `../2-fully-proven/needs-audit/q-ladder-reflectionless-reciprocal-jost-qft.md`
- **Statement:** Eliminating a locally coupled massless auxiliary channel produces the exact
  reciprocal spectral law `k^2=g^2/p^2`.  Its Schur-relative Fredholm determinant is the inverse
  Jost transmission coefficient, so the reciprocal determinant CDD amplitude is the boundary
  response of a local differential pencil.  This pencil is not yet a microscopic interacting QFT:
  its naive Euclidean quadratic form is indefinite, and any purely Gaussian completion has trivial
  bulk two-particle scattering.

## Why this card exists

The parent theorem gives a smooth local reflectionless Hamiltonian whose geometric bound-state
ladder has hypertranscendental transmission `T(k)`, and proves the exact scattering-data identity

```text
S_C(theta) = -T(kappa C/sinh(theta))^2.                         (1)
```

The remaining physical source problem was the reciprocal map in `(1)`.  Inserting it by hand is a
correct bridge between two scattering theories, but not a common microscopic derivation.  This
card isolates a local mechanism which forces the map and then states precisely what that mechanism
still does not prove.

## Setup

Let

```text
H_0 = -d^2/dx^2,
H   = H_0 + V(x)                                                   (2)
```

on `L^2(R_x)`, where `V` is real and integrable.  Let `y` be a second coordinate, `g>0`, and
consider two fields depending on `(x,y)` with the local differential pencil

```text
K_V = [[ H,             g I ],
       [ g I,   -d^2/dy^2 I ]].                                   (3)
```

After Fourier transformation only in `y`, a nonzero momentum `p` gives

```text
K_V(p) = [[H,   g I],
          [g I, p^2 I]].                                          (4)
```

The two entries may be assigned different engineering dimensions by rescaling the two fields.  No
dimensionless identification is being assumed.

Equation `(3)` is local in both coordinates.  It is anisotropic and degenerate: the first field has
no `y` kinetic term and the second has no `x` kinetic term.  It should therefore be called a local
differential pencil or constrained interface until a positive physical quantization is supplied.

## Claim A -- a massless channel forces reciprocal spectral momentum `[PROVED]`

The second row of `K_V(p)(phi,chi)^T=0` gives

```text
chi = -g p^(-2) phi.                                              (5)
```

Substitution into the first row gives

```text
(H - g^2/p^2) phi = 0.                                           (6)
```

Equivalently, block Gaussian elimination gives the exact factorization

```text
K_V(p)
 = [[I, g p^(-2) I], [0,I]]
   [[H-g^2/p^2, 0], [g I,p^2 I]].                                (7)
```

Thus the induced one-dimensional scattering energy and momentum are

```text
z = k^2 = g^2/p^2,             k = g/p                           (8)
```

with the physical boundary prescription inherited from `z+i0`.  The inversion is not a special
function identity and is not inserted into the scattering coefficient.  It is the propagator
`p^(-2)` of the eliminated gapless channel.

This is the same algebraic mechanism as Feshbach projection and the Schur complement: eliminating
one sector inserts its resolvent into the effective operator of the other.  General Schur theory
supplies spectral equivalence under operator-domain hypotheses.  The particular massless scalar
block in `(4)` is what makes that resolvent exactly reciprocal quadratic momentum.

## Claim B -- the Schur-relative determinant is the inverse transmission `[PROVED]`

Factor `V=uv` in the standard Birman--Schwinger form and define, for
`Im(sqrt(z))>0`,

```text
Delta_H(z)
 = det(I + u (H_0-z)^(-1) v).                                    (9)
```

For `V in L^1(R)`, the operator inside `(9)` differs from the identity by a trace-class operator.
The Jost--Pais/Fredholm theorem identifies

```text
Delta_H(z) = F_H(z),                                             (10)
```

where `F_H` is the full-line Jost function.  If `H` is self-adjoint, then for `k>0`,

```text
T_H(k) = F_H(k^2+i0)^(-1).                                      (11)
```

Define the Schur-relative response of `(4)` against the free pencil by

```text
D_V(p) = Delta_H(g^2/p^2),                                      (12)
```

first off the continuous spectrum and then by the boundary value in `(11)`.  Equations
`(8)`--`(12)` give

```text
D_V(p+i0)^(-1) = T_H(g/p)                                      (13)
```

up to the equivalent orientation convention for the boundary side.

In finite volume, `(12)` is the ordinary ratio of the determinants of the two Schur complements
of `K_V(p)` and `K_0(p)`.  On the full line, `(9)` is the correct Fredholm replacement.  This card
does **not** silently identify an ill-defined quotient of two infinite determinants; the
trace-class perturbation determinant is the definition of the relative response.

## Claim C -- exact recovery of the geometric CDD amplitude `[PROVED AS RESPONSE DATA]`

Take the geometric reflectionless Hamiltonian of the parent card,

```text
T_q(k) = product_(n>=0) (k+i kappa q^n)/(k-i kappa q^n),
0<q<1,                                                          (14)
```

and set `g=kappa C`, `C>1`.  Then `(13)` gives

```text
D_q(p+i0)^(-1) = T_q(kappa C/p).                               (15)
```

At external on-shell relative momentum `p=sinh(theta)`,

```text
-D_q(sinh(theta)+i0)^(-2)
 = -T_q(kappa C/sinh(theta))^2
 = -product_(n>=0)
     ((1+i q^n sinh(theta)/C)/(1-i q^n sinh(theta)/C))^2.      (16)
```

The right side is exactly the regular geometric CDD function which reconstructs the local
interacting factorizing QFT in the parent card.  Consequently the previously kinematic reciprocal
map has the following local source mechanism:

```text
massless auxiliary propagation p^(-2)
  -> Schur spectral energy k^2=g^2/p^2
  -> inverse Jost Fredholm determinant
  -> reciprocal determinant CDD response.                     (17)
```

For the finite positive-shell family, use a finite direct sum of reflectionless Hamiltonians and
couplings `g_j`.  Fredholm determinants multiply, so the same construction produces the complete
finite product response and its prescribed channel multiplicities.

The hypertranscendence is unchanged.  If `D_q(p)^(-2)` were differentially algebraic in `p`, then
the algebraic square-root and rational substitution `p=g/k` would make `T_q(k)` differentially
algebraic, contradicting the parent theorem.

## Claim D -- Wick rotation converts the threshold ladder into an external mass tower `[PROVED AT THE PENCIL LEVEL]`

There is a second, cosmological consequence of the same mechanism.  Give the auxiliary channel a
nonnegative gap `m_*`:

```text
K_(V,m_*)(p_E) = [[H, g I],
                  [g I, (p_E^2+m_*^2) I]].                     (17a)
```

Let `psi_n` be a normalized bound state of the reflectionless Hamiltonian,

```text
H psi_n = -kappa_n^2 psi_n.                                    (17b)
```

On the two-dimensional coefficient sector generated by `psi_n`, eliminating the nondynamical
first field gives the exact Euclidean kernel

```text
p_E^2 + m_*^2 + g^2/kappa_n^2.                                 (17c)
```

Equivalently, after `p_E^2=-s`, the determinant of the restricted block vanishes at

```text
s = M_n^2,
M_n^2 = m_*^2 + g^2/kappa_n^2.                                 (17d)
```

Thus every negative internal bound level becomes a positive external mass pole.  For the geometric
ladder `kappa_n=kappa q^n`,

```text
M_n^2 = m_*^2 + (g/kappa)^2 q^(-2n).                           (17e)
```

This is the same divisor reversal that made the CDD amplitude regular, now read as a spectrum:
internal levels accumulating at zero become external masses escaping to infinity.

In four-dimensional de Sitter space a scalar principal-series clock has

```text
mu_n = sqrt(M_n^2/H_dS^2 - 9/4).                               (17f)
```

Choose the source-natural threshold gap

```text
m_*^2 = (9/4) H_dS^2.                                         (17g)
```

Then `(17e)`--`(17g)` give the **exact**, not asymptotic, geometric clock law

```text
mu_n = mu_0 q^(-n),        mu_0 = g/(H_dS kappa).               (17h)
```

If `q=P^(-1)` for an integer `P>=2`, then `mu_n=mu_0 P^n`.  The universal de Sitter production
exponent consequently has the Mahler form

```text
sum_(n>=0) exp(-pi mu_n) exp(i mu_n u)
 = sum_(n>=0) W^(P^n),
W = exp(mu_0(-pi+i u)).                                        (17i)
```

This is precisely the analytic HT germ in the live sibling card
`mahler-cosmological-collider-tower.md`.  The new result removes the geometric frequency tower as
a free mathematical choice at the **linear pole level**: it is the reciprocal image of the local
q-ladder bound spectrum, and the de Sitter threshold shift makes the principal-series frequency
exactly geometric.

It does not yet derive the complete primordial correlator.  Equality `(17i)` additionally assumes
that the normalized exchange residues are shell-independent after the known spin and kinematic
factors are removed.  Nor does it make the full pencil stable.  For a continuum eigenvalue
`lambda>0` of `H`, eliminating the first field gives

```text
p_E^2 + m_*^2 - g^2/lambda.                                    (17j)
```

Because the reflectionless continuum reaches `lambda=0`, the unprojected continuum contains
tachyonic directions.  Projecting only onto the negative bound subspace would remove them but is a
nonlocal spectral projection.  A local positive completion must decouple, cancel, gauge-remove, or
otherwise stabilize this continuum without destroying `(17d)`--`(17h)`.  This is now a concrete
falsifiable source problem rather than an unspecified request for a geometric cosmological tower.

## Positive output repair

The separate proved bridge
`../2-fully-proven/not_new_scientific_knowledge/reciprocal-q-ladder-kallen-lehmann-field.md`
pushes the canonical negative bound-state counting measure through `(17d)`.  The resulting
positive polynomially bounded Kallen--Lehmann measure defines a local generalized free Wightman
field, and its Euclidean two-point function is HT.  This repairs positivity at the output-QFT
level and gives the exact de Sitter clock `(17h)`, but it is Gaussian and uses a spectral
projection nonlocal in `x`.  It therefore does not close the common interacting dynamics sought
on this card.

## Exact physical interpretation currently earned

Claims A--C prove a local **linear-response/interface** realization of the reciprocal Jost data.
They show that the inversion can be forced by a local massless propagating channel.  Depending on
the quantization and boundary conditions, `(3)` can be read as a coupled-wave or defect response
problem, and `(12)` as its relative spectral determinant.

They do not prove that `(3)` is a stable relativistic quantum field theory or that `(16)` is its
bulk two-particle scattering matrix.

## No-go 1 -- the naive Euclidean pencil is not positive `[PROVED]`

For real `p!=0`, the lower-right block `p^2 I` is strictly positive.  If `K_V(p)` were a
nonnegative self-adjoint block operator, its Schur complement would be nonnegative.  But its Schur
complement is

```text
H - g^2/p^2.                                                    (18)
```

For a short-range one-dimensional Hamiltonian, the essential spectrum of `(18)` contains
`[-g^2/p^2,infinity)`.  Hence `(18)` is not nonnegative, even when `V=0`.  Therefore `K_V(p)` is
not a positive Euclidean covariance kernel.

This obstruction is structural, not a defect of the geometric potential.  Adding positive
auxiliary blocks does not help if their exact final Schur complement remains `(18)`: positivity of
the parent would again force positivity of the complement.  A viable completion must instead use
analytic continuation, a constrained/gauge quotient, an indefinite transfer formalism with a
positive physical subspace, or a different nonlinear realization.

## No-go 2 -- a Gaussian determinant is not an interacting bulk S-matrix `[PROVED]`

A theory whose complete action is the quadratic form `(3)` is Gaussian.  Its connected
four-point function vanishes, so LSZ reduction gives no nontrivial bulk two-particle scattering.
It may have nontrivial one-particle transmission through an interface and a nontrivial vacuum or
spectral determinant, but it cannot by itself have the interacting CDD amplitude `(16)` as a bulk
two-particle S-matrix.

This kills a tempting but false promotion:

```text
block determinant = effective response or action,             yes;
block determinant = interacting relativistic S without
additional dynamics,                                          no.  (19)
```

Nazarov's block-determinant scattering action is useful parent theory for determinant-valued
transport responses, but it does not close the LSZ/QFT step here.

## Conjecture -- massless-channel reciprocal Jost completion

> `[CONJECTURE]` There exists a local interacting completion with a positive physical Hilbert
> space in which a massless constrained channel induces the exact Schur law `(8)`, the geometric
> reflectionless Hamiltonian is fixed by a local self-similar Darboux constraint, and the exact
> elastic two-particle amplitude on the physical subspace is the boundary response `(16)`.

This conjecture is deliberately stronger than constructing another QFT from prescribed scattering
data.  The parent Lechner net already proves that such a local interacting QFT exists.  The new
theorem must exhibit a common dynamics which explains why its amplitude is the reciprocal Jost
determinant.

## Required promotion theorem

A successful construction must prove all of the following without inserting `(14)` or `(16)` as
input:

1. **Local source:** a local action, Hamiltonian, defect algebra, or operator interface produces
   the massless Schur sector and the geometric spectral ladder.
2. **Physical positivity:** a positive-energy Hilbert space or a reflection-positive Euclidean
   reconstruction survives elimination of unphysical degrees of freedom.
3. **Exact scattering:** LSZ, Haag--Ruelle, or an operator-algebraic scattering theorem gives
   `S_2(theta)=-D_q(sinh(theta)+i0)^(-2)` nonperturbatively.
4. **No extra singularities:** auxiliary channels introduce no additional physical-strip poles,
   cuts, particle production, or inelastic sectors that destroy factorization.
5. **Locality/completeness:** the resulting observables are local and the asymptotic particle
   states are complete.
6. **Constraint selection:** the one-shell `q`-law follows from the microscopic constraint rather
   than from a selected solution written into the action.

Failure of any one of these leaves Claims A--C as a local response mechanism, not a QFT source
theorem.

## Live attack branches

1. **Gauge/Krein completion.**  Seek a Dirac- or transfer-type first-order parent whose indefinite
   auxiliary sector is removed by a constraint while the physical quotient is positive.
2. **Integrable defect fusion.**  Interpret `(3)` as a defect transfer operator, then prove that
   fusing the two asymptotic Jost channels produces a bulk factorizing amplitude.
3. **Non-Gaussian determinant exactness.**  Find an interaction, supersymmetric cancellation, or
   localization theorem for which the determinant response is exact rather than merely one-loop.
4. **Operator-algebraic interface.**  Construct a functor from the reflectionless scattering
   system and its massless Schur channel to the Borchers triple/local net, with `(16)` derived on
   asymptotic states.
5. **No-go escalation.**  Test whether spectral positivity or crossing forbids every positive
   completion with an exact `1/p^2` Schur pole.  A rigorous impossibility theorem would itself
   sharply classify the reciprocal-QFT bridge.

## Anti-theatre and novelty gate

The following are established parent theory and are not claimed as discoveries:

- Feshbach projection produces energy-dependent effective operators by eliminating channels;
- Schur complements give spectral equivalence for block operator matrices;
- the full-line inverse transmission coefficient is a Fredholm/Jost determinant;
- determinant actions occur in quantum transport;
- quadratic Gaussian theories have trivial connected bulk scattering.

Targeted source searches did not find the exact chain `(17)` applied to a geometric infinite-soliton
Hamiltonian and then identified with a regular hypertranscendental factorizing-QFT amplitude.
That negative evidence is not a novelty proof.  The card remains at stage 1 until a specialist
formula-level audit and the positive interacting completion are complete.

The algebraic core alone is not medal-level: it is a short Schur-complement observation.  Its value
is that it replaces an unexplained reciprocal substitution with a local gapless-channel mechanism
and reduces the open problem to positivity plus exact interacting promotion.  Only closure of that
promotion theorem clears the significance gate.

## Lean boundary

The live HTGeometry corpus was checked before opening this card.  It already formalizes the finite
geometric shell law, convergence, endpoint selection, and uniqueness of the CDD boundary response.
The new content here is an analytic unbounded-operator/Fredholm/Jost interface and a QFT positivity
problem.  No unconditional reusable Lean theorem at the substantive boundary is presently
available, and another finite block-matrix identity would be wrapper theatre.  No Lean edit or
build is justified for this card.

## Primary literature

- H. Feshbach, *Unified Theory of Nuclear Reactions*, Annals of Physics **5** (1958), 357--390,
  <https://doi.org/10.1016/0003-4916(58)90007-1>.
- H. Feshbach, *Unified Theory of Nuclear Reactions*, Reviews of Modern Physics **36** (1964),
  1076--1078, <https://doi.org/10.1103/RevModPhys.36.1076>.
- B. Gerhat, *Schur complement dominant operator matrices*,
  <https://arxiv.org/abs/2205.11653>.
- F. Gesztesy and K. A. Makarov, *(Modified) Fredholm Determinants for Operators with
  Matrix-Valued Semi-Separable Integral Kernels Revisited*,
  <https://arxiv.org/abs/math/0312267>.
- V. V. Shamshutdinova, K. N. Pichugin, I. Rotter, and B. F. Samsonov, *Feshbach
  projection-operator formalism to resonance scattering on Bargmann-type potentials*,
  <https://arxiv.org/abs/0809.4848>.
- Y. V. Nazarov, *Block-determinant formalism for an action of a multi-terminal scatterer*,
  <https://arxiv.org/abs/1507.03039>.
- N. Arkani-Hamed and J. Maldacena, *Cosmological Collider Physics*,
  <https://arxiv.org/abs/1503.08043>.
- M. Duetsch and K.-H. Rehren, *Generalized free fields and the AdS-CFT correspondence*,
  <https://arxiv.org/abs/math-ph/0209035>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>.

## Gates

- [x] local differential pencil written without a special-function input
- [x] exact reciprocal spectral law proved by Schur elimination
- [x] Fredholm boundary response identified with inverse Jost transmission
- [x] geometric reciprocal determinant CDD identity recovered
- [x] Wick-rotated reciprocal bound-state mass ladder derived
- [x] exact geometric de Sitter principal-series clock obtained by the threshold gap
- [x] positive-bound-sector/unstable-continuum split identified
- [x] reciprocal bound spectrum promoted to a positive local generalized free field
- [x] its Euclidean two-point function proved hypertranscendental
- [x] naive Euclidean positivity obstruction proved
- [x] Gaussian-to-interacting-S false promotion ruled out
- [x] novelty and significance claims limited to the surviving conjunction
- [x] live HTGeometry checked; no wrapper formalization opened
- [ ] positive interacting common completion constructed
- [ ] exact non-Gaussian/LSZ or operator-algebraic scattering theorem proved
- [ ] microscopic local constraint selects the geometric ladder
- [ ] external formula-level novelty audit complete
