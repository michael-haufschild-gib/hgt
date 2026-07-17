# The constrained prolate floor selects positive Fourier parity

- **ID:** `constrained-prolate-fourier-parity-floor-separation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`, provisional pending
  independent proof audit; `[NOT AN RH PROOF]`
- **Parent:** `constrained-prolate-two-mode-ground-state.md` and Fuchs fixed-index asymptotics
- **Statement:** After imposing the zero-integral constraint, the positive compressed-Fourier
  prolate floor is asymptotically lower than the negative compressed-Fourier floor by a factor of
  order `lambda^(-4)`. The two floors are selected respectively by the `h_0-h_4` and `h_2-h_6`
  Hermite contrasts.

## Setup

Let `T_lambda=P_lambda F P_lambda` on the real even subspace of
`L2([-lambda,lambda])`, with the Fourier convention of the CCM cards. Write

```text
T_lambda h_(n,lambda)=sigma_n chi_n(lambda)h_(n,lambda),
sigma_n=(-1)^(n/2),
0<chi_n(lambda)<1                                      (1)
```

for even `n`. Put

```text
d_n(lambda)=1-chi_n(lambda)^2.                         (2)
```

The positive and negative compressed-Fourier sectors are

```text
H_lambda^+=closure span{h_(4j,lambda):j>=0},
H_lambda^-=closure span{h_(4j+2,lambda):j>=0}.         (3)
```

In each sector compress the leakage operator `B_lambda=I-T_lambda^2` to the zero-integral
hyperplane. Denote the resulting ground eigenvalues by

```text
mu_+(lambda),  mu_-(lambda).                           (4)
```

## Theorem

As `lambda->infinity`,

```text
mu_+(lambda)/d_4(lambda) ->8/11,                       (5)
mu_-(lambda)/d_6(lambda) ->8/13.                       (6)
```

If `A_n>0` are the Fuchs constants

```text
d_n(lambda)
 ~A_n lambda^(2n+1)exp(-4*pi*lambda^2),                (7)
```

then

```text
mu_+(lambda)/mu_-(lambda)
 ~[13 A_4/(11 A_6)]lambda^(-4) ->0.                   (8)
```

Consequently, for all sufficiently large `lambda`,

```text
mu_+(lambda)<mu_-(lambda),
mu_-(lambda)-mu_+(lambda)~mu_-(lambda).                (9)
```

The negative-sector ground is simple. If `nu_-(lambda)` is its next constrained eigenvalue, then

```text
liminf_(lambda->infinity)
  [nu_-(lambda)-mu_-(lambda)]/d_6(lambda)>=5/13.       (10)
```

After a choice of sign, its normalized source eigenvector converges at rate `O(lambda^(-7))` to
the normalized zero-integral `h_2-h_6` Hermite contrast.

## Proof

Equation `(5)` and the corresponding positive-sector simplicity are
`constrained-prolate-two-mode-ground-state.md`. It remains to prove `(6)` and compare the scales.

### 1. Negative-sector secular equation

Put

```text
e_j=h_(4j+2,lambda),
delta_j=d_(4j+2)(lambda),
ell_j=integral_R e_j(x)dx.                             (11)
```

Evaluation of `(1)` at zero gives

```text
ell_j=-chi_(4j+2)(lambda)e_j(0).                       (12)
```

The integral functional is bounded on the supported Hilbert space, so

```text
sum_(j>=0)ell_j^2<=2lambda.                            (13)
```

On the hyperplane `ell^perp`, a constrained eigenvector with eigenvalue `mu` has coordinates,
up to a common scalar,

```text
v_j=ell_j/(delta_j-mu),                                (14)
```

and hence satisfies

```text
F_-(mu)=sum_(j>=0)ell_j^2/(delta_j-mu)=0.              (15)
```

The function is strictly increasing between consecutive poles. In particular it has exactly one
root `mu_-` in `(delta_0,delta_1)`, and that root is simple.

### 2. Hermite constraint coordinates

For the normalized Hermite functions in this Fourier convention,

```text
h_(2m)(0)^2=sqrt(2) binom(2m,m)/4^m.                   (16)
```

Prolate-to-Hermite convergence and `(12)` therefore give

```text
ell_0^2 -> h_2(0)^2=1/sqrt(2),
ell_1^2 -> h_6(0)^2=5/(8sqrt(2)).                      (17)
```

Thus

```text
ell_0^2/(ell_0^2+ell_1^2)->8/13.                      (18)
```

### 3. The infinite tail is lower order

Fuchs' asymptotic `(7)` gives

```text
delta_0/delta_1=O(lambda^(-8)),
delta_1/delta_2=O(lambda^(-8)).                        (19)
```

The zero of the first two terms of `(15)` is

```text
mu_2
 =(ell_0^2 delta_1+ell_1^2 delta_0)
   /(ell_0^2+ell_1^2).                                 (20)
```

For `mu in (delta_0,delta_1)`, `(13)` and `(19)` give

```text
0<sum_(j>=2)ell_j^2/(delta_j-mu)
 <=2lambda/(delta_2-delta_1).                          (21)
```

The derivative of the two-pole part of `(15)` is bounded below by `c delta_1^(-2)` on the interval
between `mu_-` and `mu_2`. The mean value theorem therefore yields

```text
0<=mu_2-mu_-
 <=C lambda delta_1^2/(delta_2-delta_1),
(mu_2-mu_-)/delta_1=O(lambda^(-7)).                    (22)
```

Equations `(18)`--`(20)` and `delta_0/delta_1->0` prove `(6)`.

The same coordinate formula `(14)` shows that the tail-to-head norm ratio is

```text
O(sqrt(lambda)delta_1/delta_2)=O(lambda^(-15/2)),      (23)
```

while `(22)` changes the normalized first-two direction by `O(lambda^(-7))`. This proves the stated
source-vector convergence.

### 4. Negative-sector gap and parity separation

Codimension-one min--max interlacing gives

```text
delta_0<=mu_-<=delta_1<=nu_-.
```

Together with `(6)`, this proves `(10)`. Finally `(5)`--`(7)` give `(8)`, and `(9)` follows.

## CCM interpretation

Positive and negative compressed-Fourier sources produce, up to their exterior Fourier leakage,
the inversion-even and inversion-odd aperture vectors used by Connes--Consani. The theorem therefore
supplies a positive source-level asymptotic parity selector:

```text
zero-integral prolate concentration
  -> positive-Fourier/inversion-even floor
     lower than the negative-Fourier/inversion-odd floor
     by a factor asymptotic to C lambda^(-4).           (24)
```

This does not yet prove that the true restricted Weil ground is even. The live transfer theorem is
now sharply positive: a bilinear radial-prolate Weil-tail comparison preserving the parity-floor
ratio `(8)` automatically supplies cofinal even dominance, while a relative form estimate within
the positive sector supplies simplicity and the determinant seed.

## Novelty and significance audit

The local-corpus audit covered the full pipeline, failed cards, formal tree, reports, consolidated
research, worklogs, and git history. It found:

- Connes--Consani already construct both sign families of raw prolate contrasts and numerically
  compare the negative-sign/odd family, whose first Hermite limit is of `h_2-h_6` type, with the odd
  Weil matrix. That family is parent input, not novelty.
- `constrained-prolate-two-mode-ground-state.md` and
  `constrained-prolate-fixed-mode-spectral-ladder.md` prove the exact constrained variational theory
  only in the positive `4j` sector.
- The semilocal all-even Jacobi--prolate residue tower is a different Route-B operator lane and does
  not contain the present compressed-Fourier constraint problem.
- No prior local claim gives the negative-sector constrained floor, `8/13`, the `5/13` gap, or the
  cross-sector ratio `(8)`.

The external search through July 2026 likewise found classical unconstrained PSWF eigenvalue
asymptotics, general concentration bounds, and the CCM raw odd family, but no theorem with these
variational constants. The proof is not a restatement of Fuchs: Fuchs supplies the diagonal scales,
while the codimension-one secular problem and cross-sector comparison produce the claimed parity
selection.

Provisional significance: **5/10**. The theorem gives a rigorous and falsifiable parity fingerprint
for the CCM source model and a polynomially strong even/odd separation. Its RH significance depends
entirely on the still-open bilinear transfer to the true Weil form.

## References

- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.
- A. Connes, C. Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

`formal/GaloisForLFunctions/RHTower/ConstrainedProlateOperator.lean` now supplies the concrete
compressed Fourier, concentration, leakage, and zero-integral constrained operators.
`ProlateSecularEquation.lean` supplies the finite secular root and interlacing theorems, while
`FuchsProlateScale.lean` supplies the exact fixed-index rate model.

`formal/GaloisForLFunctions/RHTower/TwoModeFuchsLimit.lean` now formalizes the complete finite
Fuchs-model parity calculation.  The declarations
`ccm_negativeSector_twoMode_weight_eq`,
`ccm_negativeSector_twoMode_ground_leakage_ratio`, and
`ccm_negativeSector_twoMode_ground_gap_ratio` prove the exact `8/13` ground and complementary
`5/13` gap limits for the `h_2`--`h_6` contrast, while
`ccm_negativeSector_twoMode_ground_gap_eventually_ge` proves the corresponding unnormalized
eventual lower bound for every constant below `5/13`.  The declaration
`ccm_twoMode_parity_floor_ratio_tendsto_zero` combines these with the positive-sector `8/11` law
and the exact Fuchs index separation to prove that the positive two-mode floor divided by the
negative two-mode floor tends to zero.  Its quantified form
`ccm_twoMode_parity_floor_eventually_lt_mul` proves that for every `c>0`, the positive floor is
eventually strictly below `c` times the negative floor.  The sharper declaration
`ccm_twoMode_parity_floor_scaled_ratio` proves the exact rescaled limit
`lambda^4 mu_+(lambda)/mu_-(lambda) -> 13 A_4/(11 A_6)`.  All declarations are unconditional and
axiom-clean.

The remaining Lean boundary is the analytic passage from these two-mode Fuchs models to the exact
infinite-dimensional constrained optimizers: the normalized prolate-to-Hermite mode convergence,
uniform secular-tail estimate, the `O(lambda^(-7))` eigenvector rate, and min--max transfer to the
true second constrained eigenvalue.  The card therefore remains in stage 2.

## Gates

- [x] negative-sector constrained secular root proved
- [x] exact constant `8/13` proved
- [x] negative-sector gap constant `5/13` proved
- [x] positive/negative floor ratio `C lambda^(-4)` proved
- [x] negative-sector two-mode Fuchs-rate `8/13` and `5/13` limits formalized in Lean
- [x] every constant below `5/13` formalized as an eventual negative-sector gap lower bound
- [x] two-mode positive/negative floor ratio tending to zero formalized in Lean
- [x] quantified eventual parity dominance `mu_+ < c mu_-` formalized for every `c>0`
- [x] sharp two-mode `lambda^4`-rescaled parity coefficient formalized in Lean
- [x] targeted literature search found no parent theorem
- [ ] transfer the two-mode laws to the exact infinite-dimensional constrained floors in Lean
- [ ] independent proof audit
- [ ] bilinear transfer of parity separation to the true restricted Weil form
