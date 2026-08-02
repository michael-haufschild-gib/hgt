# Suzuki interior seams have no half-log corona; the borderline dipole creates a forced jump

- **ID:** `suzuki-interior-seam-indicial-dipole-exclusion`
- **Stage:** 2-fully-proven
- **Type:** EXACT PAIRED INDICIAL CLASSIFICATION / INTERIOR-CORONA EXCLUSION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Input:** `suzuki-paired-seam-carleman-logistic-normal-form.md`

## 1. Result

The physical half-log indicial root is a boundary phenomenon.  It is not an independent root at
an interior prime seam.

Use the paired profiles and fixed-window logarithmic jump from the predecessor card.  Suppose, for
some \(0<\tau<1\),

```text
F_+(L)=beta_+ L^(-tau)+o(L^(-tau)),
F_-(L)=beta_- L^(-tau)+o(L^(-tau)),                     (1)
```

in the log-conormal sense, so the exact Gamma remainder is lower by two inverse-log orders.  Then

```text
(J_0u)(+exp(-L))
 =L^(1-tau)/(1-tau)
   [(1-2tau)beta_+-beta_-]
  +o(L^(1-tau)),                                        (2+)

(J_0u)(-exp(-L))
 =L^(1-tau)/(1-tau)
   [(1-2tau)beta_--beta_+]
  +o(L^(1-tau)).                                        (2-)
```

In vector form, with the orientation swap

```text
J(beta_+,beta_-)=(beta_-,beta_+),
```

the interior indicial matrix is

```text
I_tau=[(1-2tau)I-J]/(1-tau).                            (3)
```

Its eigenvalues on symmetric and antisymmetric orientations are

```text
lambda_sym(tau)=-2tau/(1-tau),
lambda_anti(tau)=2.                                     (4)
```

Therefore \(I_\tau\) is invertible for every \(0<\tau<1\).  In particular:

```text
bounded interior forcing
 -> beta_+=beta_-=0
for every paired order 0<tau<1.                          (5)
```

At the borderline \(\tau=1\), boundedness first forces antisymmetry:

```text
F_+(L)= beta/L+o(1/L),
F_-(L)=-beta/L+o(1/L).                                  (6)
```

This logarithmic dipole does not disappear.  For the unit-normalized principal symbol
\(2\log|\xi|\), it creates the one-sided limits

```text
lim_(x downarrow 0) J_0u(x)=+2beta+C,
lim_(x uparrow 0) J_0u(x)=-2beta+C,                     (7)
```

where \(C\) is the common continuous contribution of the cutoff and lower-order source.  Hence

```text
jump_0(J_0u)=4beta.                                     (8)
```

If Suzuki's complete right-hand side is continuous at the seam, `(8)` forces \(\beta=0\).

Thus an interior seam has neither:

```text
an independent half-log L^(-1/2) root,
nor an independent dipole L^(-1) root.                  (9)
```

The first admissible conormal singularity is a **forced descendant** of order \(>1\).  A physical
endpoint half-log source \(L^{-1/2}\), translated to an interior seam, is inverted to the already
proved order \(L^{-3/2}\).  This is consistent with the exact coefficient \(1/4\) and proves that
the two physical endpoint roots are the only grade-zero conormal trace coordinates.

This closes finite-grade root support.  It does not exclude an all-orders-flat, nonconormal
interior state; that is exactly what the global tempered-orbit Gamma theorem must remove.

## 2. Same-side leading term

For \(0<\tau<1\),

```text
2L F_+(L)-integral_0^L F_+(t)dt

=2beta_+ L^(1-tau)
 -beta_+ L^(1-tau)/(1-tau)
 +o(L^(1-tau))

=[(1-2tau)/(1-tau)]
  beta_+ L^(1-tau)+o(L^(1-tau)).                        (10)
```

The lower endpoint of the integral and a harmless initial cutoff change only \(O(1)\).  The exact
Gamma remainder satisfies

```text
(R F_+)(L)=O(L^(-tau-2))+O(exp(-L/2)),                  (11)
```

and \(q(L)F_+(L)=O(e^{-L}L^{-\tau})\), so neither contributes at order
\(L^{1-\tau}\).

## 3. Cross-side leading term

The Carleman response is

```text
(C F_-)(L)
 =integral_0^infinity
   F_-(v)/[1+exp(v-L)]dv.                               (12)
```

For \(v<L-O(1)\), the logistic cutoff equals one up to an exponentially localized error; for
\(v>L+O(1)\), it is exponentially small.  Karamata's elementary integral asymptotic therefore
gives

```text
(C F_-)(L)
 =beta_- L^(1-tau)/(1-tau)+o(L^(1-tau)).                (13)
```

Substituting `(10)` and `(13)` into the exact paired normal form proves `(2+)`.  Reflection proves
`(2-)`. `QED`

## 4. Matrix classification

The swap \(J\) has eigenvalue \(+1\) on vectors \((z,z)\) and \(-1\) on
\((z,-z)\).  Equation `(3)` therefore has eigenvalues

```text
[(1-2tau)-1]/(1-tau)=-2tau/(1-tau),

[(1-2tau)+1]/(1-tau)=2,                                 (14)
```

which proves `(4)`.  If both components of \(J_0u\) are bounded, divide `(2+)`--`(2-)` by
\(L^{1-\tau}\) and let \(L\to\infty\).  Invertibility gives
\((\beta_+,\beta_-)=0\), proving `(5)`.

The missing symmetric root at \(\tau=0\) is the common value \(u(0)\), which was subtracted in the
definition of \(F_\pm\).  It is regular data, not a corona coordinate.

## 5. Borderline order one

For \(F_\pm(L)=\beta_\pm/L+o(1/L)\), the same-side primitive and cross response have logarithmic
leading terms:

```text
2L F_+(L)-integral_0^L F_+(t)dt
 =2beta_+-beta_+ log L+o(log L),

(C F_-)(L)=beta_- log L+o(log L).                       (15)
```

Therefore boundedness of the right-oriented equation forces

```text
beta_++beta_-=0.                                        (16)
```

The reflected equation gives the same condition.  This proves `(6)`.

To compute the remaining jump, use the local Fourier Abelian law.  With a smooth cutoff,

```text
u_beta(x)=beta sign(x)/log(1/|x|)
```

has high-frequency transform

```text
widehat(u_beta)(xi)
 =2beta/(i xi log|xi|)
  +o(1/[|xi|log|xi|]).                                  (17)
```

The fixed-window jump `(2)` has principal symbol

```text
2log|xi|+O(1).                                          (18)
```

Multiplying `(17)` by `(18)` gives

```text
4beta/(i xi)+o(1/|xi|).                                 (19)
```

Since the Fourier transform of \(\operatorname{sign}(x)\) is \(2/(i\xi)\) in this convention,
the singular output is \(2\beta\operatorname{sign}(x)\).  Every bounded smooth multiplier and
every compactly localized smoother kernel contributes a function continuous at zero.  This proves
`(7)`--`(8)`. `QED`

The coefficient is normalization-sensitive only through the principal logarithmic coefficient.
For a symbol \(\kappa\log|\xi|+O(1)\), the jump is \(2\kappa\beta\), still nonzero.

## 6. Suzuki source consequence

At a valuation seam, Suzuki's lower-order terms have the following regularity.

- Scalar/eigenvalue multiplication preserves continuity.
- The polar convolution is locally Lipschitz.
- A prime translate is continuous unless the translated point is another already marked seam.
- A marked lower-grade conormal source has an explicit one-sided order and is handled by
  the order-raising recurrence.

Therefore no unmarked interior center can supply either the divergent power in `(2)` or the step
jump `(8)`.  At a marked center, `(3)` gives the exact response order and the positive
prime-valuation recurrence supplies its coefficient.  Induction over every finite grade gives:

```text
grade-zero conormal trace:
  supported only at the two physical endpoints;

interior conormal state:
  forced, orientation-marked, and of grade at least one. (20)
```

Exact spatial collisions do not change this statement because opposite one-sided orientations are
retained separately.

This proves root-only support for every finite conormal grade.  The remaining global issue is not
a hidden interior half-log channel; it is whether an all-orders-flat paired state survives the
infinite dense orbit.  The bounded nonnormal carrier and Gamma-strip coercivity were constructed
precisely for that residual.

## 7. Hostile audit

1. **Conormal scope explicit.**  The theorem does not infer an expansion for an arbitrary weak
   completed mode.
2. **No \(\tau=1\) limit substitution.**  Borderline logarithms are computed separately.
3. **Continuity is load-bearing at order one.**  Boundedness permits the antisymmetric dipole;
   continuity of the complete forcing kills its step.
4. **No flat-sector claim.**  Profiles such as \(e^{-\sqrt L}\) lie beyond every power in `(1)`.
5. **No collision cancellation.**  Paired orientations and source marks remain distinct.
6. **No RH claim.**  Infinite assembly, flat-sector annihilation, nonzero root return, and raw
   Evans positivity remain.

## 8. Novelty boundary

Indicial matrices, slowly varying Abelian laws, and logarithmic dipoles are classical mechanisms.
Candidate-new source knowledge is the exact Suzuki paired classification:

```text
interior Carleman coupling changes the boundary half-log
indicial law;
all orders 0<tau<1 are invertible;
the sole order-one dipole creates a nonzero source jump;
therefore only physical endpoints carry grade-zero corona.     (21)
```

Corpus search found the one-sided half-log root and prime order-raising law, but not the paired
matrix `(3)`, dipole jump `(8)`, or root-support consequence `(20)`.  External priority remains
unaudited.

## 9. Lean decision

Faithful formalization requires slowly varying Fourier Abelian asymptotics and the principal
symbol of the logarithmic jump.  These are absent from Lean.  A two-by-two determinant theorem
would certify only `(4)`, not the source claims `(2)` or `(8)`, and would be theatre.  Formalization
is deferred to the complete paired-orbit analytic module.

## Gates

- [x] compute paired indicial matrix for every `0<tau<1`
- [x] prove it is invertible
- [x] exclude an interior half-log root
- [x] classify the borderline order-one dipole
- [x] compute its nonzero logarithmic-operator jump
- [x] exclude it under continuous Suzuki forcing
- [x] prove physical roots are the only finite-grade conormal trace coordinates
- [ ] prove arbitrary completed modes admit the required finite-grade expansions
- [ ] annihilate the all-orders-flat paired sector
- [ ] assemble the infinite weighted orbit equation
- [ ] prove trace-zero completed modes enter `H1_0`
- [ ] prove completed Evans injectivity
- [ ] RH or whole-Connes no-go
