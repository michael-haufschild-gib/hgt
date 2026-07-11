# Infinitesimal Euler leakage has a positive Cauchy-energy threshold

- **ID:** `infinitesimal-euler-leakage-cauchy-energy-threshold`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `euler-leakage-residue-mode-expansion.md`;
  `infinitesimal-hardy-leakage-horizontal-layer-resolvent.md`
- **Statement:** For a finite right-half zero divisor, the first-order anti-causal profile of the
  shifted completed-function quotient is an exponential sum with coefficient `2m` at a zero of
  multiplicity `m`.  Its unweighted `L^2(0,infinity)` energy is a strictly entrywise-positive
  Cauchy Gram form.  A single nontrivial-strip layer forces energy strictly greater than `4`, with
  no cancellation between different ordinates.

## Setup

Let a centered self-dual Cartwright completion have a finite right-half divisor

```text
rho_j=1/2+a_j+i gamma_j,
a_j>0,
```

with multiplicities `m_j>=1`, after equal zeros are combined.  For the shifted quotient

```text
Theta_omega(z)
 = Xi(1/2-omega-iz)/Xi(1/2+omega-iz),
```

let `ell_omega(t)` denote its logarithmic wrong-support inverse Mellin profile on `t>0`, with the
same Paley--Wiener normalization as the leakage kernel.  Equivalently, the anti-causal kernel is
`ell_omega(x+y)` after reflecting the output half-line.

Critical-line zeros contribute only to the causal Hardy side.  The finite right-half divisor is
the complete anti-causal contribution.

## Theorem A: universal first-order residue profile

There is local `L^2(0,infinity)` convergence

```text
omega^(-1) ell_omega(t) -> ell_1(t),                     (1)
```

and

```text
ell_1(t)
 = 2 sum_j m_j exp(-(a_j+i gamma_j)t).                   (2)
```

The coefficient depends only on the zero multiplicity, not on `Xi'(rho_j)` or any higher jet.

### Proof

Away from the real boundary zeros,

```text
(Theta_omega-1)/omega -> -2 Xi'/Xi
```

locally uniformly.  At a zero `rho` of order `m`, the logarithmic derivative has a simple pole of
residue `m`.  Under the pole coordinate

```text
z_rho=-gamma+i a,
```

the anti-Hardy part of the derivative symbol is therefore the simple Cauchy pole whose reflected
Paley--Wiener profile is

```text
2m exp(-(a+i gamma)t).
```

This also follows directly from the finite residue-mode formula.  For a simple zero its leakage
coefficient is

```text
-Xi(rho-2omega)/Xi'(rho)=2omega+O(omega^2).
```

For order `m`, differentiating the local quotient at `omega=0` replaces the order-`m` quotient
block by the logarithmic derivative residue `2m`; all higher exponential-polynomial terms are
`O(omega^2)` after the common limit `Theta_0=1`.  The finite sum permits termwise convergence on
every compact `t`-interval and in `L^2` because every `a_j` is positive.  This proves `(1)`--`(2)`.

## Theorem B: positive Cauchy energy

Define

```text
E_Xi^off=integral_0^infinity |ell_1(t)|^2 dt.             (3)
```

Then

```text
E_Xi^off
 = 4 sum_(j,k) m_j m_k
     (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2).        (4)
```

Every summand in `(4)` is strictly positive.  In particular,

```text
E_Xi^off >= 2 sum_j m_j^2/a_j.                           (5)
```

### Proof

Expand the square in `(3)` and integrate each finite exponential term:

```text
integral_0^infinity
 exp(-(a_j+a_k)t) exp(-i(gamma_j-gamma_k)t) dt
 = 1/(a_j+a_k+i(gamma_j-gamma_k)).                       (6)
```

The term with indices `(k,j)` is the conjugate of `(6)`.  Summing the ordered pairs therefore
replaces `(6)` by its real part and gives `(4)`.  Since `a_j+a_k>0`, every displayed real part is
strictly positive.  Retaining only `j=k` gives

```text
4m_j^2 (2a_j)/(2a_j)^2=2m_j^2/a_j,
```

which proves `(5)`.

## Corollary: absolute strip threshold

For the Riemann Xi function every nontrivial right-half zero satisfies

```text
0<a_j<1/2.
```

Therefore the existence of even one off-line zero implies

```text
E_Xi^off>4.                                               (7)
```

Consequently, whenever the global first-order anti-causal profile is defined in `L^2`,

```text
E_Xi^off<=4  ->  no right-half zero  ->  RH.              (8)
```

If the infinite right-half divisor does not define an `L^2` profile, assign
`E_Xi^off=+infinity`; it cannot satisfy the bound in `(8)`.

## Route C consequence

Different ordinates do not create destructive interference in the unweighted first-order profile
energy.  The Cauchy Gram kernel in `(4)` is entrywise positive, and its diagonal alone has the
critical-strip threshold.  Thus an ordinate-by-ordinate projection is unnecessary for an absolute
exclusion theorem.

The remaining arithmetic statement can be written entirely before a residue expansion:

1. differentiate the shifted Euler quotient at `omega=0` on an Euler line;
2. take its wrong-support inverse Mellin component by contour transport;
3. prove that the resulting profile has squared `L^2` norm at most `4`.

`[OPEN CORE]` Prove this bound from the completed Euler--Gamma--theta source without assuming an
inner/Herglotz condition or reconstructing the Xi divisor.  Equations `(4)`--`(8)` prove the
consequence of such a bound, not the source bound itself.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` After the residue profile is given, `(4)` is the elementary Gram
matrix of finitely many decaying exponentials and `(7)` is the classical zero-free-strip width
inserted into its diagonal.  The result is a useful noncancellation bridge but fails the
parent-theory and anti-theatre gates.

Scientific novelty would begin with the unconditional Euler-source estimate in the open core.

## Gates

- [x] 0 -> 1: global phase cancellation and the first-order residue coefficient isolated.
- [x] 1 -> 2: profile limit, positive Cauchy energy, and absolute strip threshold proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the source-side energy estimate is open and the
  present finite exponential Gram calculation is standard parent theory.
- [ ] 3 -> 4: no unconditional RH proof.
