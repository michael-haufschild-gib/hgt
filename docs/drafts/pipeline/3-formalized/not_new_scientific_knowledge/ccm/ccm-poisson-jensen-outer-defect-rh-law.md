# The CCM Poisson half-weight has one exact outer-entropy defect

- **ID:** `ccm-poisson-jensen-outer-defect-rh-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SCALAR OUTER-RANGE DEFECT / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** half-plane Poisson--Jensen factorization, Hardy outer range theory, and
  `ccm-completed-quotient-weighted-schur-seam-law.md`
- **Statement:** The failure of the completed Poisson--Muntz multiplier to have dense Hardy range is
  measured by one nonnegative Poisson--Jensen defect. It is the negative logarithm of the
  denominator Blaschke product and is a strictly positive sum over every off-line zero beyond the
  chosen horizontal layer. Its vanishing at one positive point is equivalent to the corresponding
  shifted RH half-plane. Thus a cofinal finite-prime construction must preserve outer entropy, not
  merely converge locally uniformly or remain zero-free at each finite stage.

## 1. Hardy-normalized arithmetic multiplier

Fix `omega>0`, put

```text
s=1/2+omega+z,                                             (1)
```

and choose an integer `m` large enough that

```text
d_(omega,m)(z)=s(s-1)zeta(s)/(1+z)^m                      (2)
```

belongs to `H-infinity(Re z>0)`. The pole of zeta at `s=1` is removable in `(2)`. The polynomial
normalization is zero-free in the right half-plane, and the factors omitted from the completed xi
function are also zero-free there. Consequently the right-half-plane zeros of `(2)` are exactly

```text
b_rho=rho-(1/2+omega),
xi(rho)=0,
Re rho>1/2+omega,                                         (3)
```

with multiplicity.

Write the inner--outer factorization

```text
d_(omega,m)=B_omega O_(omega,m).                          (4)
```

The normalized multiplier extends meromorphically across the boundary and has zero mean type, so
there is no singular inner factor. Thus `B_omega` is the Blaschke product of exactly the divisor
`(3)`.

## 2. The outer-entropy defect

For `x>0`, define

```text
E_omega(x)
 =x/pi * integral_R log|d_(omega,m)(it)|/(x^2+t^2) dt
  -log|d_(omega,m)(x)|.                                   (5)
```

The integral is understood in the standard Poisson--Jensen sense; the polynomial normalization
makes its positive part integrable, while isolated boundary zeros have locally integrable
logarithms. Then

```text
E_omega(x)=-log|B_omega(x)|                               (6)

 =1/2 sum_(Re rho>1/2+omega) m_rho
    log(
      ((x+a_rho)^2+gamma_rho^2)
      /((x-a_rho)^2+gamma_rho^2)
    ),                                                     (7)
```

where

```text
a_rho=Re rho-1/2-omega>0,
gamma_rho=Im rho.                                         (8)
```

Both sides are independent of the sufficiently large normalizing exponent `m`.

### Proof

On the imaginary boundary, `|B_omega|=1` almost everywhere. The outer factor therefore has the
same boundary logarithmic modulus as `d_(omega,m)`, and the outer Poisson representation gives

```text
log|O_(omega,m)(x)|
 =x/pi * integral_R log|d_(omega,m)(it)|/(x^2+t^2) dt.    (9)
```

Taking logarithmic moduli in `(4)` and subtracting proves `(6)`.

For a zero `b=a+i gamma` in the right half-plane, use the elementary Blaschke factor

```text
b_b(z)=(z-b)/(z+conjugate(b))                             (10)
```

up to an irrelevant unimodular constant. At the positive real point `x`,

```text
-log|b_b(x)|
 =1/2 log(((x+a)^2+gamma^2)/((x-a)^2+gamma^2)).           (11)
```

Summing `(11)` over the Blaschke divisor with multiplicity proves `(7)`. The sum converges by the
Blaschke condition. Any change in `m` multiplies `(2)` by a zero-free outer rational factor, whose
Poisson--Jensen defect is zero. This proves normalization independence. `QED`

## 3. Positivity and exact detection

Each summand in `(7)` is strictly positive because `x>0` and `a_rho>0`. Hence

```text
E_omega(x)>=0,                                            (12)
```

and, for any one fixed `x>0`,

```text
E_omega(x)=0
 iff B_omega=1
 iff closure(Ran M_(d_(omega,m)))=H2_+
 iff xi has no zero in Re rho>1/2+omega.                  (13)
```

Thus a scalar equality at one positive point detects the complete, possibly infinite,
denominator model space. It is not a finite-height or ordinate-only statistic: every off-line zero
contributes with its horizontal displacement and multiplicity.

For a nonexceptional sequence `omega_j downarrow 0`, RH is equivalent to

```text
E_(omega_j)(x)=0 for every j                              (14)
```

at one arbitrarily chosen `x>0`.

## 4. Cofinal outer-entropy theorem sufficient for RH

Let `d_(j,N)` be bounded finite-source multipliers on the right half-plane, normalized compatibly
with `(2)`. Fix one `x>0` and define their Poisson--Jensen defects `E_(j,N)(x)` by the analogue of
`(5)`. Suppose, for every fixed `j`, that

```text
log|d_(j,N)(x)| ->log|d_(omega_j,m_j)(x)|,                 (15)

x/pi * integral_R log|d_(j,N)(it)|/(x^2+t^2) dt
 ->x/pi * integral_R log|d_(omega_j,m_j)(it)|/(x^2+t^2)dt, (16)

E_(j,N)(x)->0.                                             (17)
```

Subtracting the two limits gives

```text
E_(omega_j)(x)=0.                                         (18)
```

If `(15)`--`(17)` hold for a cofinal sequence `omega_j downarrow 0`, equation `(14)` proves RH.
For outer finite multipliers, `(17)` is automatic; in a more general finite construction it is the
statement that the finite inner defect disappears.

This is an alternative to zero-preserving locally uniform convergence. If zero-free finite
multipliers already converge locally uniformly and nontrivially to the target on the whole right
half-plane, Hurwitz's theorem directly makes the target zero-free, so the entropy condition is
redundant. The value of `(15)`--`(17)` is that it replaces that full divisor topology by one
interior scalar and one logarithmic boundary functional.

Therefore a second positive finite-prime completion format is an **outer-entropy-preserving
convergence theorem** carrying

```text
one interior logarithmic value
  + one Poisson logarithmic boundary value
  + vanishing finite inner defect
  + the exact completed source normalization.             (19)
```

Finite self-adjointness, finite positivity, ordinary Hardy contractivity, and unweighted strong
operator convergence do not supply `(16)`.

## 5. Dephased real-spectrum CCM transfer

The finite CCM spectral factors have a known exponential mean type. The Poisson--Jensen statement
must remove that phase before comparing them with the zero-mean-type target.

Let `f_N` be bounded-type functions on the right half-plane with no zeros there and factorization

```text
f_N(z)=exp(-tau_N z)O_N(z),       tau_N>=0,                (20)
```

where `O_N` is outer. Then, for every `x>0`,

```text
x/pi * integral_R log|f_N(it)|/(x^2+t^2)dt
 =log|f_N(x)|+tau_N x.                                    (21)
```

Suppose that for a target `d_(omega,m)` and one fixed `x>0`,

```text
log|f_N(x)|+tau_N x ->log|d_(omega,m)(x)|,                (22)

x/pi * integral_R log|f_N(it)|/(x^2+t^2)dt
 ->x/pi * integral_R log|d_(omega,m)(it)|/(x^2+t^2)dt.    (23)
```

Passing to the limit in `(21)` gives `E_omega(x)=0`, and hence the shifted zero-free half-plane by
`(13)`.

For an even real-rooted finite spectral factor `F_N`, the rotated function

```text
z |->F_N(i(omega+z))                                      (24)
```

has all its zeros on the vertical line `Re z=-omega`; therefore it has no right-half-plane
Blaschke factor. After the explicit polynomial normalization and removal of its known aperture
mean type, it has the form `(20)`. Consequently, if `(22)`--`(23)` hold for the normalized CCM
factors along a cofinal sequence `omega_j downarrow 0`, then RH follows.

This is strictly less phase information than locally uniform convergence of the entire
determinants: only harmonic logarithmic modulus data are transported. It is not implied by finite
real-rootedness itself. The positive CCM target is

```text
dephased interior log convergence
  + Poisson-weighted boundary log convergence
  -> preservation of zero Blaschke entropy
  -> RH.                                                    (25)
```

The aperture phase cannot simply be discarded: its contribution is the explicit term `tau_N x`
in `(21)`. This is the scalar Poisson--Jensen counterpart of the negative Cauchy background in
`ccm-euler-pick-logderivative-transfer-boundary-law.md`.

## 6. Relation to the half-unit seam

At exponential weights `0<=a<=omega`, the denominator line remains to the right of `Re s=1`, so
the corresponding normalized multiplier has no inner zero factor and its outer defect is zero.
At the target weight `a=omega+1/2`, the defect becomes `(5)`--`(7)`. Thus crossing the invariant
half-unit seam has one exact scalar cost:

```text
loss of outer Poisson equality
 =creation of B_omega
 =birth of the Cauchy-jet model-space defect.              (26)
```

This is the scalar determinant of the domain defect isolated in the weighted-Schur theorem.

## 7. Scientific classification and Lean decision

The theorem is the standard half-plane Poisson--Jensen formula applied to the shifted zeta
multiplier. Outer stability under logarithmic-boundary convergence is classical Hardy theory. The
source-specific assembly is useful but scientifically non-new.

The formal tree lacks Hardy inner--outer factorization, Poisson logarithmic integrals, and the
analytic zeta multiplier. Formalizing the positivity of a finite logarithmic sum would not certify
the infinite factorization or `(16)`. No Lean file is added.

## Gates

- [x] Hardy-normalized arithmetic multiplier constructed
- [x] exact outer-entropy defect defined
- [x] positive zero-divisor expansion proved
- [x] vanishing at one point proved equivalent to shifted RH
- [x] normalization independence proved
- [x] cofinal scalar outer-entropy transfer theorem proved sufficient for RH
- [x] dephased real-spectrum scalar transfer theorem proved sufficient for RH
- [ ] prove logarithmic-boundary convergence `(16)` from the CCM finite source
- [ ] RH

## Lean status

`[FORMALIZED]` — supersedes the "No Lean file is added" decision recorded above, which is stale.
That decision judged that positivity of a finite logarithmic sum alone would not certify the
infinite factorization; the module below formalizes the card's *own* computations — the exact
Blaschke defect `(10)`–`(11)`, its positivity and exact detection `(12)`–`(13)`, the dephasing
identity `(20)`–`(21)`, and the limit subtraction `(15)`–`(18)` — and leaves the inner–outer
factorization and the Poisson representation explicitly as cited parents.

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMPoissonJensenOuterDefect.lean`
(10 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired
into `formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `halfPlaneBlaschke`, `normSq_ofReal_sub`, `normSq_ofReal_add_conj`, `norm_sq_halfPlaneBlaschke` —
  **equation (10)**: the elementary factor `(z-b)/(z+conj b)` and its exact squared modulus
  `((x-a)²+γ²)/((x+a)²+γ²)` at a real point.
- `outerDefectTerm`, `neg_log_norm_halfPlaneBlaschke` — **equation (11)**:
  `-log|b_b(x)| = ½ log(((x+a)²+γ²)/((x-a)²+γ²))`, proved including the degenerate point.
- `outerDefectTerm_nonneg` — **equation (12)**: every term is nonnegative for `x > 0`, `a > 0`.
- `outerDefectTerm_pos` — the strict form away from the degenerate point: each off-line zero
  contributes strictly, with its horizontal displacement `a_ρ` and ordinate `γ_ρ`.
- `sum_outerDefect_eq_zero_iff` — **equation (13), finite form**: a finite defect sum with positive
  multiplicities vanishes exactly when the divisor beyond the layer is empty.  This is the exact
  detection statement, at the level the card's own argument establishes it.
- `log_norm_meanType_interior`, `log_norm_meanType_boundary` — **equations (20)–(21)**: the
  exponential mean type `e^{-τ z}` is unimodular on the imaginary axis and shifts the interior
  logarithmic modulus by exactly `-τ x`, which is the term `τ_N x` the card insists cannot be
  discarded.
- `defect_limit_eq_zero` — **equations (15)–(18)**: if the interior and boundary logarithmic data
  converge and the finite defects tend to zero, the limiting defect is zero.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the Hardy inner–outer factorization `(4)` and the absence of a singular inner factor;
- the Poisson representation `(9)` of the outer factor and the Poisson–Jensen integral `(5)`;
- the Blaschke convergence condition for the infinite product;
- the analytic zeta multiplier `(2)` and its right half-plane zero set `(3)`.
