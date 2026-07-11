# The exponential abscissa of the CCM polar--prime defect is the transverse zero barrier

- **ID:** `ccm-critical-mellin-defect-abscissa-rh-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / EXACT POSITIVE RH CARRIER / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Laplace--Stieltjes continuation, the logarithmic derivative of zeta, and the
  classical von Koch bound under RH
- **Statement:** If the cumulative finite-aperture polar--prime defect has exponential type at most
  `theta`, then zeta has no zero with real part greater than `1/2+theta`. In particular, RH is
  equivalent to subexponential growth of that defect. Thus the exact positive scalar resource a
  CCM boundary proof must transport is zero exponential type of the critical Mellin carrier.

## 1. The defect and its source transform

Let

```text
A(h)=sum_(n<=exp(h))Lambda(n)n^(-1/2),
R(h)=4sinh(h/2)-A(h),       h>=0.                              (1)
```

The exact source identity from `ccm-polar-prime-critical-mellin-defect-law.md` is

```text
L_R(z):=integral_0^infinity exp(-z h)dR(h)
 =1/(z-1/2)+1/(z+1/2)+zeta'(z+1/2)/zeta(z+1/2)                (2)
```

for `Re z>1/2`.

## 2. Growth-to-zero-free theorem

Fix `theta>=0`. Assume that for every `epsilon>0` there is `C_epsilon` such that

```text
|R(h)|<=C_epsilon exp((theta+epsilon)h),       h>=0.          (3)
```

Then every nontrivial zero `rho` of zeta satisfies

```text
Re rho<=1/2+theta.                                           (4)
```

### Proof

Fix `epsilon>0`. Since `R(0)=0`, Stieltjes integration by parts gives

```text
L_R(z)=z integral_0^infinity exp(-z h)R(h)dh                  (5)
```

whenever `Re z>theta+epsilon`. Assumption `(3)` makes the right side absolutely and locally
uniformly convergent there, hence holomorphic.

On the nonempty overlap `Re z>1/2`, `(5)` equals the meromorphic expression `(2)`. The identity
theorem therefore continues that expression holomorphically to `Re z>theta+epsilon`. A nontrivial
zero `rho` with `Re rho>1/2+theta+epsilon` would give an uncancelled pole of `zeta'/zeta` at

```text
z=rho-1/2.                                                   (6)
```

The two rational terms in `(2)` have poles only at `plus_or_minus 1/2` and cannot cancel `(6)`.
Thus no such zero exists. Letting `epsilon` decrease to zero proves `(4)`. `QED`

The pole at `z=1/2` is harmless: the pole of `1/(z-1/2)` cancels the pole of `zeta'/zeta` at
`s=1`, exactly as required by `(5)`.

## 3. Exact RH criterion

The following are equivalent:

```text
(i)  RH;
(ii) for every epsilon>0, R(h)=O_epsilon(exp(epsilon h));
(iii) limsup_(h->infinity) log(1+|R(h)|)/h=0.                  (7)
```

The implication `(ii)->(i)` is the theorem above with `theta=0`; functional-equation reflection
then puts every nontrivial zero on the line. Conditions `(ii)` and `(iii)` are equivalent by the
definition of the limsup.

For `(i)->(ii)`, use the classical von Koch consequence of RH

```text
Psi(X)-X=O(sqrt(X)log(X)^2),                                 (8)
```

where `Psi(X)=sum_(n<=X)Lambda(n)`. The exact partial-summation identity

```text
R(h)
 =1-2exp(-h/2)-exp(-h/2)(Psi(exp(h))-exp(h))
  -(1/2)integral_1^(exp(h))(Psi(t)-t)t^(-3/2)dt              (9)
```

then gives

```text
R(h)=O(1+h^3).                                               (10)
```

Indeed the endpoint error in `(9)` is `O(h^2)`, and the integral is
`O(integral_1^(exp(h)) log(t)^2/t dt)=O(h^3)`. Polynomial growth implies `(ii)`.

Thus `(7)` is an exact scalar RH criterion. It is a repackaging of classical prime-error theory,
not a proof of the required bound.

## 4. Quantitative zero-free regions

Define the upper exponential type

```text
omega_R=limsup_(h->infinity) log(1+|R(h)|)/h.                 (11)
```

The growth-to-zero-free theorem gives the unconditional implication

```text
sup_rho Re rho <=1/2+omega_R.                                (12)
```

More generally, any proved bound `R(h)=O(exp(theta h)h^M)` gives the zero-free half-plane

```text
Re s>1/2+theta.                                              (13)
```

The prime number theorem supplies only `omega_R<=1/2`; its classical de la Vallée Poussin error
improves the subexponential factor relative to `exp(h/2)` but not the exponent `1/2`. The CCM/RH
threshold is the strict recession

```text
omega_R=0.                                                   (14)
```

## 5. Positive CCM consequence

The fixed-quartet amplification theorem used an attained transverse displacement. Equations
`(7)`--`(14)` remove that hypothesis: all possible off-line layers, attained or not, are jointly
encoded by the exponential abscissa of one source-defined cumulative defect.

Every viable CCM boundary implementation must therefore prove one of the following equivalent
positive statements:

```text
R has zero exponential type;
the Laplace source L_R has no pole in Re z>0;
the completed logarithmic source has no transverse divisor pole;
the exact even polar--Euler frame has its required lower bound at every aperture.   (15)
```

Only the first three equivalences concern divisor exclusion directly; the last is the even Weil
criterion through `ccm-polar-euler-frame-minus-level-law.md`. Finite-prime main-term cancellation
gives `R=o(exp(h/2))`, but a proof must cross all the way to zero exponential type.

## Classification and Lean decision

The theorem is the standard Laplace-abscissa/zero-free-region argument applied to the corrected
CCM carrier, with the classical von Koch estimate for the converse. It is a decisive route
normalization but not new scientific knowledge.

The formal tree contains finite prime sums and logarithmic-derivative identities but not the
Laplace--Stieltjes continuation or the analytic zeta zero/pole interface used in `(2)`--`(6)`.
Formalizing only the elementary limsup implication would not establish `(7)`, so no Lean file is
added.

## Gates

- [x] Laplace transform of the critical Mellin defect identified
- [x] exponential growth bound converted to a zero-free half-plane
- [x] nonattained transverse layers handled simultaneously
- [x] subexponential defect growth proved equivalent to RH
- [x] positive zero-type CCM carrier law extracted
- [ ] prove `omega_R=0` from the Euler--Gamma source
- [ ] RH
