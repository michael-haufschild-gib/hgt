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

The **passage to the exact infinite-dimensional constrained optimizers is now formalized** for
the Fuchs-rate model in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateParityExactTransfer.lean`, on top of the
uniform infinite-tail secular estimate of `ConstrainedProlateInfiniteSecular.lean`.  The
negative-sector Hermite weight `8/13` and complement `5/13` are evaluated exactly from
`h_2(0)² = 1/√2`, `h_6(0)² = 5/(8√2)` (`ccm_negativeSector_hermite_weight_eq` and its
complement).  The offset radial Fuchs family `d_j = M_j λ^{8j+5}e^{−4πλ²}` (indices `4j+2`) is
proved to satisfy the ordered-triple-with-floor structure and the `λ·d_1/(d_2−d_1) → 0` tail rate
(`fuchsRate_radial_offset2_struct`, `fuchsRate_step4_tail_ratio_tendsto_zero` — the latter for
every base index).  Consequently, for the exact infinite constrained ground roots (not two-mode
truncations):

- `ccm_fuchsModel_negativeSector_root_ratio_tendsto` — `μ_-(λ)/d_6(λ) → 8/13`, eq. `(6)`;
- `ccm_fuchsModel_negativeSector_gap_ratio_tendsto` — the complementary `5/13` of eq. `(10)`;
- `ccm_fuchsModel_negativeSector_spectralGap_eventually` — every `c < 5/13` eventually separates
  all competing secular zeros (the negative-sector simplicity/gap statement);
- `ccm_fuchsModel_parity_floor_ratio_tendsto_zero` — `μ_+(λ)/μ_-(λ) → 0`, eq. `(9)`;
- `ccm_fuchsModel_parity_floor_scaled_ratio_tendsto` — `λ⁴μ_+(λ)/μ_-(λ) → 13A_4/(11A_6)`,
  the sharp form of eq. `(8)`.

All are axiom-clean, with the Fuchs constants abstract (positivity plus tempered growth
`A_2 ≤ C^j A_{j+2}`).  The hypotheses still open for the *true prolate operator* are the ℓ-side
inputs: square-summability, the Bessel bound `Σℓ² ≤ 2λ`, and the prolate-to-Hermite limits of
the first two coordinates in each sector — plus Fuchs asymptotics identifying the true leakages
with the Fuchs family.

The exact normalized eigenvector statement is now formalized in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateParityDistanceCCM.lean`.
`ccm_tendsto_min_norm_lp_normalize_sub_negativeTwoModeSeed` constructs both the exact secular
eigenvector and its two-mode `h_2-h_6` seed as literal `lp 2` vectors and proves that the minimum
of the two squared normalized distances (the two sign choices) tends to zero.  The offset-Fuchs
ordering, root location, square-summability of the secular vector, nonvanishing, head alignment,
and `λ·d_6/(d_10-d_6) → 0` tail collapse are all discharged.  Only the same explicit true-prolate
coordinate hypotheses remain.

The stronger quantitative rate is now formalized in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateFullDistanceRate.lean`.
`ccmNegative_normalized_ground_distance_eventually_le` gives an explicit pointwise constant, and
`ccmNegative_normalized_ground_distance_isBigO` proves the literal unsquared sign-optimized
normalized `lp 2` distance is `O(λ^{-7})`.  This comparison is with the same-aperture two-mode
`h_2-h_6` seed, so no quantitative prolate-to-Hermite error is required; the coordinate limits are
used only for eventual nonvanishing and a fixed head floor.  The theorem is axiom-clean (only
`propext`, `Classical.choice`, and `Quot.sound`).

The exact central binomial evaluations and Hermite floor weight ratios are unconditionally formalized in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateHermiteParityEvaluation.lean`.
`hermiteOriginSq_zero`, `hermiteOriginSq_one`, `hermiteOriginSq_two`, `hermiteOriginSq_three` prove
$h_0(0)^2 = \sqrt{2}$, $h_2(0)^2 = \sqrt{2}/2$, $h_4(0)^2 = 3\sqrt{2}/8$, $h_6(0)^2 = 5\sqrt{2}/16$;
`positive_sector_hermite_floor_ratio_eq` proves the exact positive floor weight $8/11$;
`negative_sector_hermite_floor_ratio_eq` proves the exact negative floor weight $8/13$;
`parity_floor_weight_ratio_eq` proves the exact weight ratio $(8/11)/(8/13) = 13/11$; and
`parity_floor_fuchs_constant_ratio_eq` evaluates the scaled constant factor $(8/11 \cdot A_4) / (8/13 \cdot A_6) = 13 A_4 / (11 A_6)$.
The card remains in stage 2 pending the listed true-operator identifications.

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
- [x] exact infinite-dimensional constrained floors: `8/13`, `5/13`, quantified gap, parity
  collapse `(9)`, and sharp `lambda^4` coefficient `(8)` formalized in Lean for the Fuchs-rate
  model (ℓ-side inputs as explicit hypotheses)
- [x] normalized full-`ℓ²` negative-sector eigenvector convergence up to sign formalized in Lean
- [x] quantitative `O(lambda^(-7))` unsquared normalized eigenvector rate in Lean, with an explicit
  eventual constant (`ccmNegative_normalized_ground_distance_eventually_le` and
  `ccmNegative_normalized_ground_distance_isBigO`)
- [ ] true-operator ℓ-side inputs (Bessel bound, prolate-to-Hermite limits) and Fuchs
  identification in Lean
- [ ] independent proof audit
- [ ] bilinear transfer of parity separation to the true restricted Weil form

## Lean progress — the oscillator-ladder pin, and what the prolate-to-Hermite gate now needs

The open gate on this card is the pair of true-operator ℓ-side inputs: the prolate-to-Hermite
coordinate limits and the Fuchs identification.  Their common foundation is now formal, and the
last step turned out to be an identity rather than an asymptotic argument.

What the corpus already owned (no new work): the whole commuting-operator layer —
`HTGeometry/SturmSelfAdjoint.lean`, `HTGeometry/ProlateKernelSymmetry.lean`,
`RHTower/ProlateCommutationKernel.lean` (`prolateAction_bandEigen_eq_smul`: an eigenfunction of the
finite Fourier transform solves the prolate ODE), `RHTower/SlepianBandCommutation.lean`,
`RHTower/FuchsProlateScale.lean` (the exact scaling identity `prolateSLAction_sqrtScale`),
`RHTower/HermiteOscillatorEigen.lean` (`hermiteSLAction_hermiteFun`: eigenvalue `−(2n+1)`), and
`RHTower/ProlateHermiteRescale.lean`, whose
`exists_even_prolateHermiteRescale_of_signedMode` gives every live signed mode a smooth even global
profile whose Hermite rescaling satisfies, **with no convergence premise**,

```text
hermiteSLAction u + (c·s)·u = (ξ² u″ + 2ξ u′)/c ,      c = 2πλ² .
```

New (wired, axiom-clean):

```text
HTGeometry/WholeLineWronskianSymmetry.lean
    integral_deriv_eq_zero_of_tendsto_zero   a derivative whose primitive tends to 0 at ±∞
                                             integrates to 0 over the line
    hasDerivAt_wronskian                     (u′v − uv′)′ = u″v − uv″
    integral_secondDeriv_pairing_eq_zero
    integral_secondDeriv_mul_comm            ∫ u″v = ∫ u v″ for a vanishing Wronskian

RHTower/ProlateOscillatorLadderPin.lean
    hasDerivAt_hermiteFun, hasDerivAt_deriv_hermiteFun
    hermitePairing_pin (n) :
        hermiteSLAction u + μ·u = D  ⟹  (μ − (2n+1))·⟨u, φₙ⟩ = ⟨D, φₙ⟩
    abs_sub_oscillatorLadder_eq (n) :
        |μ − (2n+1)| = |⟨D, φₙ⟩| / |⟨u, φₙ⟩|
```

The `ξ²` potential cancels identically — it appears with the same sign on both sides of the
integration by parts — so no spectral theorem, no operator domain and no quasimode inequality is
used.  Applied to the prolate identity above,

```text
|c·s(c) − (2n+1)| = |⟨ξ²u″ + 2ξu′, φₙ⟩| / (c · |⟨u, φₙ⟩|) .
```

**Consequently the whole remaining analytic content of this card's prolate-to-Hermite gate is one a
priori bound**: that the defect pairing `⟨ξ²u″ + 2ξu′, φₙ⟩` stays bounded relative to `⟨u, φₙ⟩` as
the bandwidth grows.  That is a statement about a single rescaled profile against a single Gaussian
weight; it needs no expansion and no uniformity in the index.  With it, the eigenvalue is pinned to
the oscillator ladder at rate `1/c`, the same pairing pins the eigenvector, and
`ℓ_j = χ_{4j}·e_j(0)` with `χ → 1` delivers the coordinate limits `ℓ_j → |ĥ_{4j}(0)|` whose targets
`2^{1/4}` and `√3·2^{−5/4}` are already formal in `HermiteOriginConstraintTargets.lean`.

## Lean progress — the defect pairing needs no derivative bound at all

The note above reduced this card's prolate-to-Hermite gate to a single a priori bound on the defect
pairing `⟨ξ²u″ + 2ξu′, φₙ⟩`.  That bound is no longer needed in that form: the pairing transfers
entirely onto the Hermite side.

`GaloisForLFunctions/HTGeometry/WholeLineWronskianSymmetry.lean` (extended, wired):

```text
integral_deriv_mul_eq_neg     ∫ u′v = −∫ u v′ when u v → 0 at both ends
```

`GaloisForLFunctions/RHTower/ProlateDefectTransfer.lean` (wired):

```text
hermiteSqWeight n x           = x² φₙ(x)          (with its two derivatives)
hermiteLinWeight n x          = 2x φₙ(x)          (with its derivative)
integral_prolateDefect_transfer :
    ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²φₙ″ + 2ξφₙ′⟩
integral_prolateDefect_transfer_explicit :
    ⟨ξ²u″ + 2ξu′, φₙ⟩ = ⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩
prolateLadder_pin_hermiteSide :
    (μ − (2n+1))·⟨u, φₙ⟩ = ⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩ / c
```

Two integrations by parts — one of second order against the weight `ξ²φₙ`, one of first order
against `2ξφₙ` — move both derivatives of the profile onto the Hermite factor, and
`φₙ″ = (ξ² − 2n − 1)φₙ` makes the surviving weight completely explicit.  The `4ξφₙ′` produced by the
second-order transfer and the `−2ξφₙ′` produced by the first-order one combine to `2ξφₙ′`, and the
two `±2φₙ` cancel.

**Consequence for this card.**  The distance from the rescaled eigenvalue `c·s(c)` to the `n`-th rung
of the oscillator ladder is now, exactly,

```text
|c·s(c) − (2n+1)| = |⟨u, ξ²(ξ² − 2n − 1)φₙ + 2ξφₙ′⟩| / (c · |⟨u, φₙ⟩|) ,
```

in which **no derivative of the prolate profile appears**.  What remains is a comparison of two
pairings of the profile against fixed Gaussian-decaying weights — the numerator against
`ξ²(ξ²−2n−1)φₙ + 2ξφₙ′` and the denominator against `φₙ` — plus the decay hypotheses that make the
two integrations by parts legitimate.  That is a non-degeneracy statement about one function against
one fixed weight, not an asymptotic expansion.

## Lean progress — the eigenvalue half of the prolate-to-Hermite gate closes

The residue recorded in the previous section was a lower bound on `|⟨u, φₙ⟩|`, uniform in the
bandwidth.  It is not an obstruction: the Hermite rescaling *flattens* the profile, so the pairing
has an explicit limit.

`GaloisForLFunctions/RHTower/ProlateCentreValuePairing.lean` (wired):

```text
tendsto_div_sqrt_atTop            ξ/√c → 0
tendsto_integral_rescaled_mul     ∫ Φ(ξ/√c) W(ξ) dξ ⟶ Φ(0) · ∫ W        (W integrable)
tendsto_zero_of_ladderPin
    d(c)·⟨u_c, V⟩ = ⟨u_c, W⟩/c ,  Φ(0)·∫V ≠ 0   ⟹   d(c) → 0
```

The pairing limit is dominated convergence with the two cheapest possible hypotheses on `Φ`:
continuity at the origin and boundedness.  Both are free — the profile is continuous by
construction, and `abs_le_of_bandTransform_eigen` makes it decay, hence bounded.

Applied to the ladder pin with `V = φₙ` and `W = ξ²(ξ²−2n−1)φₙ + 2ξφₙ′`, the denominator pairing
tends to `Φ(0)·∫φₙ` and the numerator pairing stays bounded, so

```text
c·s(c) − (2n+1) ⟶ 0 .
```

The nonvanishing hypothesis `Φ(0)·∫φₙ ≠ 0` is not an extra asymptotic input.  `∫φₙ ≠ 0` holds for
the even Hermite indices this card uses.  And `Φ(0) ≠ 0` follows from the data already in hand,
by ODE uniqueness rather than by assumption: the profile is **even**, so `Φ′(0) = 0`; the prolate
equation `(1 − x²)Φ″ − 2xΦ′ − c²x²Φ = χΦ` has leading coefficient `1` at `x = 0`, so the origin is
an ordinary point; hence `Φ(0) = 0` together with `Φ′(0) = 0` would force `Φ ≡ 0`, contradicting
`Φ ≠ 0`.

(An earlier draft of this note claimed `Φ(0) ≠ 0` was supplied by
`exists_even_prolateHermiteRescale_of_signedMode`'s hypothesis `evenProlateSignedValue a n ≠ 0`.
That is not so: `evenProlateSignedValue` is the signed *eigenvalue* `sgVal (evenTimeBandFourier a) n`,
not the centre value.  The uniqueness argument above is what supplies it.)

**Status of this card's gate.**  The *eigenvalue* half of the prolate-to-Hermite limit —
`c·s(c) → 2n+1`, equivalently the fixed-index prolate eigenvalue asymptotic at leading order — is
now a Lean theorem given the instantiation.  What the card still needs beyond it is the
*eigenvector* half, `ℓ_j(λ) → |ĥ_{4j}(0)|`, and the Fuchs identification of the leakage rates.
