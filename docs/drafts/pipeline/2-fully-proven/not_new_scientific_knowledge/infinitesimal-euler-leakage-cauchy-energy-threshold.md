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

## Theorem B: the infinitesimal source is exactly von Mangoldt--Gamma

Put `s=1/2-iz`.  On `Re s>1`,

```text
partial_omega Theta_omega(z)|_(omega=0)
 = -2 Xi'(s)/Xi(s)
 = -2/s-2/(s-1)+log pi-psi(s/2)
   +2 sum_(n>=1) Lambda(n)n^(-s).                         (3)
```

The same fact is visible directly in Suzuki's causal source coefficients

```text
c_omega(n)=n^omega product_(p|n)(1-p^(-2omega)):

partial_omega c_omega(n)|_(omega=0)=2 Lambda(n).          (4)
```

### Proof

Logarithmic differentiation of

```text
Theta_omega(z)=Xi(s-omega)/Xi(s+omega)
```

at zero gives the first equality in `(3)`.  Insert

```text
Xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2
```

and `-zeta'/zeta=sum_n Lambda(n)n^(-s)` to obtain the second equality.

For `(4)`, if `n=p^k`, the unique vanishing factor at `omega=0` has derivative `2log p`, while the
derivative of `n^omega` is multiplied by that factor's zero.  Hence the derivative is
`2log p=2Lambda(p^k)`.  If `n` has at least two distinct prime divisors, the product vanishes to
order at least two and its first derivative is zero; for `n=1` it is also zero.  This is exactly
`2Lambda(n)` in every case.

Thus the first-order causal source is completely explicit and positive on its arithmetic
prime-power part.  The anti-causal profile `(2)` is the boundary-continuation defect of this fixed
source, not an additional freely chosen object.

The second Euler tangent is equally explicit:

```text
partial_omega^2 c_omega(n)|_(omega=0)
 =4 (Lambda * Lambda)(n),                                (5)
```

where `*` is Dirichlet convolution.  Indeed the logarithm of
`zeta(s-omega)/zeta(s+omega)` is odd in `omega`, so the second derivative of the quotient at zero
is the square of its first derivative.  Comparing absolutely convergent Dirichlet series on
`Re s>1` proves `(5)`.  Equivalently, direct expansion shows that a prime power `p^k` contributes
`4(k-1)(log p)^2`, an integer with two distinct prime supports contributes the two ordered
von-Mangoldt factorizations, and more than two distinct prime supports contribute zero.

## Theorem C: positive Cauchy energy

Define

```text
E_Xi^off=integral_0^infinity |ell_1(t)|^2 dt.             (6)
```

Then

```text
E_Xi^off
 = 4 sum_(j,k) m_j m_k
     (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2).        (7)
```

Every summand in `(7)` is strictly positive.  In particular,

```text
E_Xi^off >= 2 sum_j m_j^2/a_j.                           (8)
```

### Proof

Expand the square in `(6)` and integrate each finite exponential term:

```text
integral_0^infinity
 exp(-(a_j+a_k)t) exp(-i(gamma_j-gamma_k)t) dt
 = 1/(a_j+a_k+i(gamma_j-gamma_k)).                       (9)
```

The term with indices `(k,j)` is the conjugate of `(9)`.  Summing the ordered pairs therefore
replaces `(9)` by its real part and gives `(7)`.  Since `a_j+a_k>0`, every displayed real part is
strictly positive.  Retaining only `j=k` gives

```text
4m_j^2 (2a_j)/(2a_j)^2=2m_j^2/a_j,
```

which proves `(8)`.

## Theorem D: source-side Toeplitz curvature construction

Let `U_omega=M_(Theta_omega)` on boundary `L^2`, and write its causal and anti-causal columns as

```text
T_omega=P_+ U_omega|H^2_+,
L_omega=P_- U_omega|H^2_+.
```

Since `|Theta_omega|=1` almost everywhere,

```text
I-T_omega^*T_omega=L_omega^*L_omega.                    (10)
```

For the finite right-half divisor of Theorem A, the normalized leakage has an operator-norm limit
`D=lim_(omega->0+) omega^(-1)L_omega`.  Therefore

```text
C_E
 :=lim_(omega->0+) omega^(-2)(I-T_omega^*T_omega)
 =D^*D>=0.                                               (11)
```

After Paley--Wiener identification, `D` has Hankel kernel `ell_1(x+y)`, and `C_E` has kernel

```text
C_E(y,z)
 =integral_0^infinity
    conjugate(ell_1(x+y)) ell_1(x+z) dx.                 (12)
```

In particular,

```text
C_E(0,0)=E_Xi^off.                                      (13)
```

### Proof

For `f in H^2_+`, unitarity of multiplication gives

```text
||f||^2=||T_omega f||^2+||L_omega f||^2.
```

Polarization proves `(10)`.  Divide by `omega^2` and use the operator-norm convergence of
`omega^(-1)L_omega` to obtain `(11)`.  The kernel-composition formula gives `(12)`, and setting
`y=z=0` gives `(13)`.

Thus the positive energy has a construction from the completed shifted source before a divisor
expansion: it is the boundary corner of the second-order loss of causal Toeplitz isometry.  The
first two Euler tangents `(4)`--`(5)` show that this curvature is the Schur defect between the
one-prime von-Mangoldt tangent and the two-prime Dirichlet-convolution tangent.

## Theorem E: contractivity alone cannot bound the curvature corner

The universal Toeplitz contraction

```text
0<=I-T_omega^*T_omega<=I
```

does not imply any finite upper bound for `C_E(0,0)`.  In the one-layer model of multiplicity `m`,

```text
C_E(0,0)=2m^2/a,
```

which tends to infinity as the fixed displacement `a` decreases to zero, although every
`T_omega` remains a contraction.

This is not a contradiction: evaluation of the limiting integral kernel at the boundary corner is
not a bounded functional of the operator norm.  Consequently the open `<=4` theorem must use an
arithmetic regularity or boundary law of the Euler--Gamma source.  Positivity of the Schur defect,
unimodularity of `Theta_omega`, and Toeplitz contractivity do not supply it.

## Corollary: absolute strip threshold

For the Riemann Xi function every nontrivial right-half zero satisfies

```text
0<a_j<1/2.
```

Therefore the existence of even one off-line zero implies

```text
E_Xi^off>4.                                              (14)
```

Consequently, whenever the global first-order anti-causal profile is defined in `L^2`,

```text
E_Xi^off<=4  ->  no right-half zero  ->  RH.             (15)
```

If the infinite right-half divisor does not define an `L^2` profile, assign
`E_Xi^off=+infinity`; it cannot satisfy the bound in `(15)`.

## Route C consequence

Different ordinates do not create destructive interference in the unweighted first-order profile
energy.  The Cauchy Gram kernel in `(7)` is entrywise positive, and its diagonal alone has the
critical-strip threshold.  Thus an ordinate-by-ordinate projection is unnecessary for an absolute
exclusion theorem.

The remaining arithmetic statement can be written entirely before a residue expansion:

1. differentiate the shifted Euler quotient at `omega=0` on an Euler line;
2. take its wrong-support inverse Mellin component by contour transport;
3. prove that the resulting profile has squared `L^2` norm at most `4`.

`[OPEN CORE]` Prove this bound from the completed Euler--Gamma--theta source without assuming an
inner/Herglotz condition or reconstructing the Xi divisor.  Equations `(7)`--`(15)` prove the
consequence of such a bound, not the source bound itself.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` After the residue profile is given, `(7)` is the elementary Gram
matrix of finitely many decaying exponentials and `(14)` is the classical zero-free-strip width
inserted into its diagonal.  The result is a useful noncancellation bridge but fails the
parent-theory and anti-theatre gates.

Scientific novelty would begin with the unconditional Euler-source estimate in the open core.

## Gates

- [x] 0 -> 1: global phase cancellation and the first-order residue coefficient isolated.
- [x] 1 -> 2: profile limit, positive Cauchy energy, and absolute strip threshold proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the source-side energy estimate is open and the
  present finite exponential Gram calculation is standard parent theory.
- [ ] 3 -> 4: no unconditional RH proof.
