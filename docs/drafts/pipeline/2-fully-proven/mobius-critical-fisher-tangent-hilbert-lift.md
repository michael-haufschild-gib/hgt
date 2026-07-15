# The critical squarefree-Mobius Fisher tangent has exactly four units of Hilbert energy

- **ID:** `mobius-critical-fisher-tangent-hilbert-lift`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HT-TO-RH SOURCE VECTOR
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `../3-formalized/not_new_scientific_knowledge/mobius-critical-fisher-stein-contact-law.md`
  - `not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
- **Statement:** The four-unit critical contact score is the Hilbert tangent of the normalized
  squarefree-Mobius source state.  Its positive and signed Laplace transforms are matrix
  coefficients of one canonical contraction semigroup and the Mobius parity involution.

## Source Hilbert state

For `sigma>1`, put `epsilon=sigma-1` and

```text
Z(sigma)=sum_d mu(d)^2 d^(-sigma)=zeta(sigma)/zeta(2sigma).       (1)
```

Let `H_sq` be `ell^2` of the squarefree positive integers, with standard basis `e_d`, and define

```text
psi_sigma(d)=Z(sigma)^(-1/2) mu(d)d^(-sigma/2),
L e_d=(log d)e_d.                                                (2)
```

Then `||psi_sigma||=1`.  Write

```text
m_sigma=<psi_sigma,L psi_sigma>
       =-d/dsigma log Z(sigma).                                  (3)
```

The completed critical tangent is

```text
chi_sigma=4 epsilon d/dsigma psi_sigma
         =-2 epsilon (L-m_sigma)psi_sigma.                        (4)
```

This definition uses only the normalized squarefree-Mobius source.  It contains no Xi zero,
completed quotient, target norm, or fitted operator.

## Exact Fisher-energy theorem `[PROVED HERE]`

One has

```text
<psi_sigma,chi_sigma>=0,                                         (5)

||chi_sigma||^2
 =4 epsilon^2 Var_sigma(log d)
 =4 epsilon^2 d^2/dsigma^2 log Z(sigma),                         (6)

lim_(sigma->1+) ||chi_sigma||^2=4.                               (7)
```

### Proof

Differentiating `(1)` under the absolutely convergent squarefree Dirichlet series gives

```text
d/dsigma psi_sigma
 =-(1/2)(L-m_sigma)psi_sigma.                                   (8)
```

Centeredness proves `(5)`, and the exponential-family variance identity proves `(6)` directly.
For the limit, let

```text
G(sigma)=(sigma-1)zeta(sigma),       G(1)=1.                     (9)
```

Near `1`,

```text
log Z(sigma)
 =-log epsilon+log G(sigma)-log zeta(2sigma).                    (10)
```

The last two terms are twice continuously differentiable near `1`.  Hence

```text
d^2/dsigma^2 log Z(sigma)=epsilon^(-2)+O(1),                    (11)
```

and `(7)` follows. `QED`

Thus the four-unit source budget is not merely numerically equal to the Euler-pole energy.  It is
the limiting Fisher metric of the actual normalized Mobius channel.

## Positive and signed matrix coefficients `[PROVED HERE]`

Let

```text
T_(sigma,u)=exp(-u epsilon L),       u>=0,                       (12)
J e_d=mu(d)e_d.                                                    (13)
```

On squarefree support, `J` is a unitary involution, `T_(sigma,u)` is a positive contraction, and
they commute.  The existing positive boundary-layer transform and signed response are exactly

```text
<psi_sigma,T_(sigma,u)psi_sigma>
 =B_sigma(u)
 =Z(sigma+u epsilon)/Z(sigma),                                  (14)

<psi_sigma,J T_(sigma,u)psi_sigma>
 =zeta(2sigma)/(zeta(sigma)zeta(sigma+u epsilon))
 =tau_sigma(u epsilon/pi).                                      (15)
```

The tangent coefficient is

```text
<chi_sigma,T_(sigma,u)psi_sigma>
 =2(partial_u B_sigma(u)+epsilon m_sigma B_sigma(u)).            (16)
```

Moreover, locally uniformly for `u>=0`,

```text
B_sigma(u) -> 1/(1+u),
epsilon m_sigma -> 1,

<chi_sigma,T_(sigma,u)psi_sigma>
 ->2u/(1+u)^2.                                                  (17)
```

The right side is the Laplace transform of the completed contact score

```text
2(1-y)e^(-y)1_(y>0),                                           (18)
```

already formalized in the parent Fisher--Stein card.

### Proof

Equations `(14)` and `(15)` are the squarefree and Mobius Dirichlet-series identities.  For `(16)`,
differentiate `(14)` in `u` and use `(4)`:

```text
partial_u B_sigma(u)
 =-epsilon E_sigma[(log d)e^(-u epsilon log d)].                 (19)
```

The factorization `(10)`, evaluated at `sigma+u epsilon`, proves the locally uniform limit in
`(17)` together with its first `u` derivative.  Equation `(18)` then follows from

```text
integral_0^infinity 2(1-y)e^(-(1+u)y)dy=2u/(1+u)^2.              (20)
```

`QED`

## The singular-boundary no-go and positive HT statement

Equations `(7)` and `(17)` do not prove RH.  The signed coefficient in `(15)` is of order
`epsilon^2`; the critical contact law uses the renormalized boundary functional

```text
epsilon^(-2)<psi_sigma,J T_(sigma,u)psi_sigma>.                  (21)
```

Multiplication by `epsilon^(-2)` is not a uniformly bounded Hilbert operation.  Therefore the
scalar positive/signed contact cancellation cannot be promoted by saying that `J` is unitary or
that `T` is contractive.

**Positive general-HT statement.**  The critical source has two different geometric components:

```text
tangential component: chi_sigma, bounded in the Fisher Hilbert metric;
normal component:     epsilon^(-2)J-boundary response, singular in H_sq.   (22)
```

A successful completed source object must be a rigged boundary pair whose tangent Hilbert norm and
normal source functional are sewn before the critical limit.  The standard factorial Fock colimit
and an ordinary bounded source colligation cannot carry `(22)`; the projective/source-rigged clock
is load-bearing rather than optional terminology.

## RH-facing consequence

The exact remaining producer can now be stated without an arbitrary norm-four input:

> Lift the complementary floor/Mobius incidence and the Gamma/Sonin boundary renormalization to a
> source-defined disturbance which sends the concrete Fisher tangent `chi_sigma` to the
> anti-causal Xi seam.  If the lift is nonexpansive before the critical limit and converges in the
> boundary relative-trace topology, then `(7)` gives `||ell_E||_2^2<=4`, hence RH by the existing
> Cauchy-energy theorem.

The source vector and its energy are proved here.  The lift is not.

## Literature gate

- Zeta distributions as discrete exponential families and their information geometry are known;
  see Frank Nielsen, *A note on some information-theoretic divergences between Zeta
  distributions*, arXiv `2104.10548`.
- Score/Fisher identities for one-parameter exponential families are standard.
- Probabilistic Mobius heuristics for RH occur in the literature, but they do not construct this
  squarefree critical tangent or a completed Xi boundary lift.
- The targeted search found no literature source combining `(4)`--`(17)` with Suzuki's completed
  contact channel or an HT source-rigged continuation.  The exact literature novelty of the
  Hilbert lift remains open pending specialist audit.

The theorem is retained because it fixes the only admissible four-unit source vector for this
route, not because Fisher language by itself is new.

## Gates

- [x] normalized squarefree-Mobius Hilbert state constructed
- [x] exact tangent formula and centeredness proved
- [x] exact Fisher norm formula proved
- [x] critical four-unit limit proved
- [x] positive and signed matrix coefficients identified
- [x] completed contact-score coefficient limit proved
- [x] singular normal-boundary obstruction isolated positively
- [ ] independent literature novelty audit
- [ ] source-rigged tangent-to-Xi lift constructed
- [ ] four-unit Xi boundary estimate
- [ ] RH
