# Suzuki completion annihilates the positive Euler main pole

- **ID:** `suzuki-euler-pole-archimedean-moment-annihilation`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; SEARCH/BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Suzuki's shifted-Xi Mellin kernel;
  `suzuki-archimedean-primitive-forced-sign-change.md`
- **Statement:** The positive shifted-Euler coefficient series has its leading pole at
  `s=1+omega`, but the archimedean Mellin kernel has a simple zero at exactly that point.  The
  completed source cancels the positive main term identically.  Therefore a Tauberian argument that
  uses only the leading positive Euler asymptotic has no surviving term from which to deduce the
  sign of Suzuki's completed tail.

## Setup

Put

```text
gamma(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2,
Xi(s)=gamma(s)zeta(s).
```

For `omega>0`, define the Euler and archimedean factors

```text
C_omega(s)=zeta(s-omega)/zeta(s+omega),
G_omega(s)=gamma(s-omega)/gamma(s+omega).                (1)
```

Suzuki's kernel satisfies

```text
integral_0^1 g_omega(x)x^s dx/x=G_omega(s),              (2)
```

and the completed product is

```text
G_omega(s)C_omega(s)=Xi(s-omega)/Xi(s+omega).            (3)
```

## Theorem A: exact pole-zero cancellation

At `s_0=1+omega`,

```text
Res_(s=s_0) C_omega(s)=1/zeta(1+2omega)>0,               (4)
```

while `G_omega` has a simple zero and

```text
G_omega(s)
 =(s-s_0)/(2gamma(1+2omega))+O((s-s_0)^2).              (5)
```

Consequently

```text
lim_(s->s_0)G_omega(s)C_omega(s)
 =1/(2Xi(1+2omega))
 =Xi(1)/Xi(1+2omega).                                   (6)
```

### Proof

The zeta function has residue one at `1`, giving `(4)`.  The pole-clearing factor `gamma` has a
simple zero at `1`, and direct differentiation gives

```text
gamma'(1)=1/2.
```

The denominator `gamma(1+2omega)` is nonzero, which proves `(5)`.  Multiplying `(4)` and `(5)` gives

```text
1/(2gamma(1+2omega)zeta(1+2omega))=1/(2Xi(1+2omega)).
```

Finally `Xi(1)=1/2`, proving `(6)`.

## Theorem B: exact archimedean moment annihilation

The source kernel and its integrated primitive obey

```text
integral_0^1 g_omega(x)x^(1+omega) dx/x=0,               (7)

integral_0^1 g_omega^(1)(x)x^(1+omega) dx/x=0.           (8)
```

### Proof

Equation `(7)` is `(2)` evaluated at `s=1+omega`, because `gamma(1)=0`.  For `Re s>1/2`, Fubini's
theorem applied to

```text
g_omega^(1)(x)=integral_x^1 sqrt(y/x)g_omega(y)dy/y
```

gives

```text
integral_0^1 g_omega^(1)(x)x^s dx/x
 =G_omega(s)/(s-1/2).                                   (9)
```

Evaluate `(9)` at `s=1+omega` to obtain `(8)`.

## Route C consequence

The coefficient Dirichlet series `C_omega` has positive coefficients and a positive leading
residue.  Ordinarily this pole supplies the dominant term in a summatory or smoothed Tauberian
asymptotic.  Equations `(5)`, `(7)`, and `(8)` show that the completed archimedean factor annihilates
that term exactly.

Therefore none of the following can establish the required one-sign or curvature bound:

1. positivity of the Euler coefficients;
2. the leading pole of their Dirichlet series;
3. a Tauberian main term derived from that pole; or
4. a finite refinement that does not reach the next singularity frontier.

After the source pole is canceled, the meromorphic singularities relevant to boundary asymptotics
are the shifted nontrivial-zero poles of `Xi(s-omega)/Xi(s+omega)`.  Reading those poles directly is
the divisor formulation again.  A live Route C proof needs a source inequality controlling the
fully canceled remainder without locating its singularities first.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The theorem is the elementary pole-clearing identity in Suzuki's
published Mellin factorization.  It is a useful Tauberian obstruction but not new analytic number
theory.

## Gates

- [x] 0 -> 1: positive-main-term proposal and completion zero isolated.
- [x] 1 -> 2: residues, moment annihilation, and completed finite value proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the open content is a bound for the canceled
  all-prime remainder.
- [ ] 3 -> 4: no scientific-novelty claim.
