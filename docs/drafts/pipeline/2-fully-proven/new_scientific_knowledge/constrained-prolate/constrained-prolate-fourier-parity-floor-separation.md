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

## Correction — the eigenvalue half is not closed by the centre-value pairing

An earlier note on this card recorded that the *eigenvalue* half `c·s(c) → 2n+1` "is now a Lean
theorem given the instantiation", via `RHTower/ProlateCentreValuePairing.lean`
(`tendsto_zero_of_ladderPin`).  That is wrong, and the reason is structural rather than technical.

`tendsto_integral_rescaled_mul` and `tendsto_zero_of_ladderPin` take **one fixed** profile `Φ` and
let the bandwidth act only through the rescaling `Φ(ξ/√c)`; the flattening that produces
`Φ(0)·∫V` in the limit is dominated convergence for that single function.  The prolate family does
not have that shape: its profile `Φ_c` is itself the `c`-dependent eigenfunction, so there is no
fixed `Φ` to rescale.  The two theorems remain correct and reusable, but they do not instantiate
here.

### What the eigenvalue half actually needs

With the window machinery now in place the missing input is one classical rigidity statement:

```text
if v ∈ L²(ℝ) is even and solves  v″ = (ξ² − μ) v  on all of ℝ,  then μ = 2n+1 for some even n,
and v is a multiple of the corresponding Hermite function.
```

Given it, both halves follow from the same argument.  Normalize `Ψ_c = u_c/u_c(0)` (legitimate:
`Φ(0) ≠ 0` is `SlepianKernelScaledFubini.value_zero_ne_of_even_joint_prolate_band_eigen`).  The
separation constants `μ_c` are bounded, so along any subsequence `μ_c → μ*`, and
`tendsto_prolateProfile_window` gives `Ψ_c → Ψ*` locally uniformly with `Ψ*″ = (ξ² − μ*)Ψ*`,
`Ψ*(0) = 1`, `Ψ*′(0) = 0`.  The normalized second-moment bound
`∫ξ²Ψ_c² ≤ μ_c ∫Ψ_c²` (now formal as `integral_rescaled_secondMoment_le`) makes the family tight, so
`∫_{-K}^{K}Ψ_c²` is bounded below a constant multiple of `∫Ψ_c²` uniformly, `Ψ* ∈ L²`, and the
rigidity statement forces `μ* = 2n+1` and `Ψ* = φ_n/φ_n(0)`.  Every subsequential limit is the same,
so the full limits hold — the eigenvalue half — and the coordinate limit then follows in the
scale-free form recorded above.

The corpus owns the oscillator ladder on Schwartz space
(`HTGeometry/SchwartzOscillatorAlgebra.lean`, `HTGeometry/HermiteOrthogonality.lean` with
`creationCLM`, `annihilationCLM` and the commutator `BA − AB = 4π`,
`HTGeometry/HermiteNumberOperator.lean`), but not the passage from *an `L²` solution of the ODE* to
that ladder, which is where the rigidity statement has to be built: `A = d/dξ + ξ` satisfies
`A†A = −d²/dξ² + ξ² − 1`, so `‖Av‖² = (μ−1)‖v‖²` forces `μ ≥ 1`, `Av` solves the same equation at
`μ−2`, and iterating must terminate, with `Av = 0` solved only by `Ce^{−ξ²/2}`.

## The polynomial factor of `(β)` is the logarithmic correction to the WKB action

A corpus audit locates `(β)`'s obstruction precisely, and removes the first half of it.

### Where the corpus already stands

The reduction of the leakage to an exterior/interior mass ratio is **already formal**, and was not
recorded on this card: `ConstrainedProlatePointwiseRepresentative`'s
`evenTimeLimitedFourierRepresentative_exterior_energy` gives, for every time-limited `f`,

```text
∫_{y ≤ −a} |q|² + ∫_{y > a} |q|²  =  ‖f‖² − ‖T_a f‖² ,       q = the Fourier representative,
```

and `evenProlateSignedFourierRepresentative_exterior_energy_eq_leakage` specializes it to a live
signed mode: the leakage `1 − σ_n(a)²` **is** the exterior energy of the mode's Fourier
representative.  So `(β)` was already an ODE statement, not an operator statement.  Downstream,
`ProlateTurningLayer` turns exact mass balance into a leakage bound:

```text
leakage_lower_of_radial_mass_bounds :
  outside = inside · leakage / value²,  outside ≥ 1/(32c²),  inside ≤ 4e(c/√s)e^{2c(1−s)}
    ⟹  leakage ≥ (√s/(256 e c³))·e^{−2c(1−s)} .
```

### Why that bound cannot reach Fuchs, and what the missing factor is

Both the interior bound and the endpoint bound above use the crude WKB estimate
`∫_{√s}^{b} √((y²−s)/(1−y²)) dy ≤ 1 − s` (`integral_prolateWKB_le_aperture`,
`exp_neg_aperture_le_endpoint`).  At a fixed mode `s ≍ (2n+1)/c`, so `e^{−2c(1−s)}` is a *constant*
times `e^{−2c}`, whereas the Fuchs leakage is `c^{n+1/2} e^{−2c}`.  The whole polynomial factor is
missing, and it is missing for a definite reason: the WKB action

```text
A(s) = ∫_{√s}^{1} √((y²−s)/(1−y²)) dy = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ
```

is not `1 − O(s)` but `1 + (s/4)·log s + O(s)`, and it is the *logarithmic* term that produces the
power of `c`:

```text
c·A(s) = c + (cs/4)·log s + O(cs) = c − ((cs)/4)·log c + O(1)      when c·s is bounded,
```

so `e^{−2cA(s)} = c^{(cs)/2} e^{−2c}·Θ(1)`, and with `c s = 2n+1` that is exactly `c^{n+1/2}e^{−2c}`.

### The sharp action, proved

`formal/GaloisForLFunctions/RHTower/ProlateWKBSharpAction.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
prolateAngleAction s = ∫_{arcsin √s}^{π/2} √(sin²θ − s) dθ

prolateAngleAction_sub_bounds :
   0 ≤ 1 + (s/4)·log s − A(s) ≤ 3 s               for 0 < s ≤ 1
```

Both bounds are explicit and one-signed.  The proof:

* the substitution `y = sin θ` removes the endpoint singularity, so every integral in sight is of a
  continuous function on a compact interval;
* `sin θ − √(sin²θ − s) = s/(2 sin θ) + ρ`, `0 ≤ ρ ≤ s²/(2 sin³θ)` — proved as
  `sub_sqrt_sq_sub_bounds`, the two inequalities being `(u−w)² ≥ 0` and
  `s u² + s² − 2u³(u−w) = w(2u+w)(u−w)²`;
* the main term integrates **exactly**: `log tan(θ/2)` differentiates to `1/sin θ`
  (`hasDerivAt_log_tan_half`) and `tan(t/2) = √s/(1+√(1−s))` at the turning angle
  (`tan_half_arcsin_sqrt`), so
  `∫_t^{π/2} dθ/sin θ = −(log s)/2 + log(1+√(1−s))` (`integral_one_div_sin_eq`);
* the correction is `O(s)` by Jordan's inequality `sin θ ≥ 2θ/π` together with
  `arcsin √s ≥ √s`, giving `∫_t^{π/2} dθ/sin³θ ≤ π³/(16 s)` (`integral_one_div_sin_cube_le`);
* the three leftover terms `1−√(1−s)`, `(s/2)log(1+√(1−s))` and the correction are each nonnegative
  and each at most `s`, whence the one-sided form.

Getting the *sharp* constant of the `s·log s` term is the whole point: replacing the exact cosecant
antiderivative by the comparison `1/sin θ ≍ 1/θ` would leave a factor-`π/2` uncertainty in that
coefficient, which is a factor `c^{±(2n+1)/4}` in the leakage — enough to destroy the ladder.

### Transport to the band variable, and the improved endpoint bound

Same module:

```text
prolateWKBProfile s y = √((y²−s)/(1−y²))
prolateWKB_eq_mul_profile :   prolateWKB c (−s c²) y = c · prolateWKBProfile s y     (c ≥ 0)
integral_prolateWKBProfile_eq :
   ∫_{√s}^{b} prolateWKBProfile s = ∫_{arcsin √s}^{arcsin b} √(sin²θ − s)            (b < 1)
integral_prolateWKB_le_angleAction :
   ∫_{√s}^{b} prolateWKB c (−s c²) ≤ c · A(s)
exp_neg_angleAction_le_endpoint :
   Φ(√s)·exp(−c·A(s)) ≤ Φ(b)
exp_neg_sharp_le_endpoint :
   Φ(√s)·exp(−(c + (cs/4)·log s)) ≤ Φ(b)
```

The last two are the sharp replacements for the corpus's `exp_neg_aperture_le_endpoint`, whose
conclusion is only `Φ(√s)·e^{−c} ≤ Φ(b)`.  The gain is the factor `s^{−cs/4}`; squared, and with
`c s = 2n+1`, that is exactly the Fuchs power `c^{n+1/2}`.  The change of variables is done on
`[√s, b]` with `b < 1`, i.e. strictly inside the band where the integrand is continuous, which is
also the form in which the corpus's Riccati comparison consumes it; the endpoint limit `b → 1` is
`ProlateForbiddenEndpoint`'s business and is untouched.

### What `(β)` still needs

With the sharp action in hand, three items remain, and all three are ODE estimates on the same
solution:

1. **The endpoint upper bound.**  The corpus owns the Riccati *sub*solution direction
   (`prolateWKB_subsolution`, `prolateLogDeriv_le_prolateWKB`), which gives `Φ(1) ≥ …`.  The reverse
   needs a Riccati *super*solution — the Liouville–Green profile `√q + q′/(4q) − b/2` — so that
   `Φ(1) ≤ Φ(√s)·poly·e^{−c A(s)}`.
2. **The interior normalization from below.**  `integral_sq_le_turning_amplitude_envelope` bounds
   `∫_{−1}^1 Φ²` above by `4e(c/√s)Φ(√s)²`; the matching lower bound `∫_{−1}^1 Φ² ≥ κ (c/√s)^{-1}…`
   — really `∫_{−1}^1 Φ² ≍ Φ_max² c^{−1/2}` — is what fixes the remaining half-power.
3. **The exterior mass upper bound.**  Only `outside ≥ 1/(32c²)` is proved; the companion
   `outside ≤ C Φ(1)²/c` comes from the Bessel-type behaviour at the regular singular point, for
   which `ProlateTwoBranch` and the Dunster layer already supply the amplitude.

Items 1–3 together with `prolateAngleAction_sub_bounds` give the two-sided envelope, and the
`FuchsEnvelope` consumer tolerates a slack of `±3/2` in the exponent, so none of the three has to be
sharp in its constants — only in its power of `c`.

## `(β)` item 1 closed: the endpoint bound in the *decaying* direction

The previous entry listed three ODE estimates still needed for `(β)`.  The first — an upper bound
for the endpoint value with the sharp WKB rate — is now proved, and by an argument that needs no
approximation theory at all.

### Why the obvious route fails, and what replaces it

The corpus's endpoint bound `le_endpoint_prolateWKB` comes from the Riccati *sub*solution property
of the WKB profile: `v = −Φ′/Φ ≤ √q`, hence `Φ(1) ≥ Φ(y₀)·exp(−∫√q)`.  The reverse inequality
`v ≥ √q − …` cannot come from a supersolution — the profile `√q + q′/(4q) − b/2` is *not* one; its
Riccati defect changes sign at `2y² = 1 + s`, exactly where the corpus's outer band begins.

It follows instead from **positivity alone**.  Beyond the turning point the Sturm flux has one sign
(`deriv_nonpos_of_turning`), so `v ≥ 0` on the *whole* remaining band; and the profile `√Q` is a
repeller from below for `v′ = v² + Bv − Q`: once `v` is below `√Q` it decreases, and once it
decreases it falls faster, so it reaches `0` and then crosses it in bounded time.  A `v` that stays
nonnegative on a window therefore cannot have started far below `√Q`.

`formal/GaloisForLFunctions/HTGeometry/RiccatiNoDip.lean`, wired into the `HTGeometry` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
sub_sub_div_le_of_riccati_nonneg :
  v′ = v² + B v − Q  on [y₀,y₁],  v ≥ 0 there,  Q ≥ S² ,  0 ≤ B ≤ M
    ⟹  v(y₀) ≥ S − M − 2/(y₁ − y₀)
```

The proof is two applications of the corpus's `riccati_le_of_le_of_supersolution` against explicit
**affine** supersolutions: first the drop `m − κ(y − y₀)` with `κ = S² − Mm − m²`, which forces
`v` to reach `0` strictly inside the window, and then the descent `−λ(y − z)` from that zero, which
forces `v` below `0` — contradicting nonnegativity.  Both affine functions are supersolutions only
because of the algebra `m + M < S − 2/L ⟹ κ > 2S/L`, which is where the constant `2` in the
statement comes from.

### The prolate instance and the endpoint bound

`formal/GaloisForLFunctions/RHTower/ProlateEndpointUpperBound.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
prolatePotential_mono, prolateDrift_mono, prolateDrift_nonneg
    both Riccati coefficients are monotone on the nonnegative part of the band
prolateLogDeriv_nonneg
    beyond the turning point a positive mode has nonnegative Riccati derivative
prolateWKB_sub_le_prolateLogDeriv :
    prolateWKB c χ y₀ − 2y₁/(1−y₁²) − 2/(y₁−y₀)  ≤  prolateLogDeriv Φ y₀
prolate_endpoint_le :
    Φ b ≤ Φ a · exp(−∫_a^b (prolateWKB c χ t − 2(b+l)/(1−(b+l)²) − 2/l))
```

The last is the mirror of `exp_neg_aperture_le_endpoint`, in the direction the leakage upper bound
needs.  Its loss against the pure WKB rate is `(b−a)·(drift at `b+l` + 2/l)`, and both terms are
polynomial in the bandwidth once `l` is taken comparable to `1 − b`: the drift is `O(1/(1−b))` and
`2/l` likewise, so with `1 − b ≍ c^(−2)` the whole loss is `O(1)` in the exponent — no power of the
Gaussian clock is lost.  The integration step is
`GaloisForLFunctions.HTGeometry.le_mul_exp_integral_of_logDeriv_le'`, the windowed form added to
`EnvelopeFromLogDerivative.lean` alongside `mul_exp_integral_le_of_logDeriv_ge'` and
`exists_continuous_eqOn_Icc`.

### The action from below, with the endpoint tail

`ProlateWKBSharpAction.lean` gained the matching lower bound for the WKB integral, so the exponent
above is controlled by the sharp angular action rather than by the crude `c`:

```text
arcsin_le_pi_div_two_mul :   arcsin x ≤ (π/2)·x                        (Jordan, inverted)
angleAction_tail_le :        ∫_{arcsin b}^{π/2} √(sin²θ − s) ≤ (π/2)·√(1−b²)
sub_le_integral_prolateWKB :
    c·A(s) − c·(π/2)·√(1−b²)  ≤  ∫_{√s}^{b} prolateWKB c (−s c²)
```

With `1 − b ≍ c^(−2)` the tail `c√(1−b²)` is `O(1)`, so `∫_{√s}^{b} prolateWKB = c·A(s) + O(1)`
on both sides — `integral_prolateWKB_le_angleAction` above, and this below.

### Status of the three items

1. **Endpoint upper bound** — done, as above.
2. **Interior normalization from below** — open.  The corpus's
   `integral_sq_le_turning_amplitude_envelope` bounds `∫_{−1}^1 Φ²` above by `4e(c/√s)Φ(√s)²`,
   which is `c^(3/2)` where the truth is `c^(−1/2)`; the two-power gap is the largest single loss
   in the current chain and closing it needs the concentration of the mode in the allowed window
   `|y| ≤ √s` of width `≍ c^(−1/2)` together with the exponential decay just proved.
3. **Exterior mass upper bound** — open.  Only `outside ≥ 1/(32c²)` exists; the companion
   `outside ≤ C·Φ(1)²/c` comes from the Bessel behaviour at the regular singular point.

With the endpoint bound now two-sided at the sharp rate, items 2 and 3 are both statements about
*masses*, not about decay rates, and neither needs any further WKB input.

## `(β)` item 2: the band Sturm energy and the interior mass from below

The second of the three remaining estimates asked for a lower bound on the aperture mass in terms of
the mode's value at the turning point.  The obstruction was the *rate* at which the mode may fall
just past the turning point: the flux representation
`(1−y²)Φ′(y) = −∫_y^1 (χ + c²t²)Φ` gives only `|Φ′/Φ| = O(c²)` there, and a decay window of width
`c^(−2)` costs two powers of the bandwidth against the true width `c^(−1/2)`.

`formal/GaloisForLFunctions/RHTower/ProlateBandFluxEnergy.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`, replaces `O(c²)` by `O(c)`:

```text
prolateWeightedPotential c χ y = (1 − y²)(χ + c²y²)
prolateBandEnergy c χ Φ y      = ((1−y²)Φ′)² − (1−y²)(χ + c²y²)Φ²

hasDerivAt_prolateBandEnergy :   E′ = −P′·Φ²        (the two cross terms cancel identically)
prolateBandEnergy_one :          E(1) = 0           (the weight vanishes at the endpoint)
prolateBandEnergy_nonpos :       E ≤ 0 past the maximum of P
prolateBandEnergy_le_of_inner :  E(y) ≤ (P(ystar) − P(y))·Φ(y)²  below it
prolateFlux_sq_le :              ((1−y²)Φ′(y))² ≤ K·Φ(y)²        whenever P ≤ K on the band
```

The two branches are the same identity read in the two directions in which `P` is monotone.  Past
the maximum of `P` the energy increases and vanishes at the endpoint, so it is nonpositive there;
below the maximum the energy at the top is nonpositive and the increase of `P` bounds the rest, the
monotonicity of `Φ` turning the integrand `P′Φ²` into `P′Φ(y)²`.  Since
`max P = c²(1−s)²/4`, the resulting flux bound is `|(1−y²)Φ′| ≤ (c(1−s)/2)·Φ` — one full power of
`c` better than the flux representation, uniformly on the band and with no initial data.

Its two consequences, in the same module:

```text
neg_mul_le_deriv_of_fluxBound :  −(√K/(1−t²))·Φ(t) ≤ Φ′(t)
exp_mul_le_prolate :             Φ(a)·exp(−∫_a^b √K/(1−t²)) ≤ Φ(b)
mass_lower_of_fluxBound :
   (b−a)·(Φ(a)·exp(−∫_a^b √K/(1−t²)))² ≤ ∫_a^b Φ²
```

With `K = c²(1−s)²/4` and a window of length `b − a ≍ 1/c` the exponent is `O(1)`, so

```text
∫_a^b Φ² ≥ κ·c^(−1)·Φ(a)² ,
```

against the true `c^(−1/2)`: the loss is now `c^(1/2)`, down from `c^(3/2)` for the flux-representation
route and from `c^(2)` for the corpus's `integral_sq_le_turning_amplitude_envelope` used in reverse.
That is inside the `±3/2` slack the `FuchsEnvelope` consumer allows.

### Remaining

Only item 3 of the three: the exterior mass from above, `outside ≤ C·Φ(1)²/c`, which is the Bessel
behaviour at the regular singular point `y = 1` and for which `ProlateTwoBranch` and the Dunster
layer already supply the amplitude.  Items 1 and 2 — the endpoint bound in both directions at the
sharp WKB rate, and the interior mass from below — are proved.

## Precision accounting for `(β)`, and the correction it forces

The previous two entries recorded items 1 and 2 as "closed".  They are proved, but a precision
audit shows only item 2 is sharp enough for the `FuchsEnvelope` consumer.  Recording the arithmetic
so no later session re-derives it.

### The slack the consumer actually allows

`FuchsEnvelope`'s three conclusions use only `fuchsRate C (e j) λ < fuchsRate c (e j + 4) λ`, i.e.
that the *upper* power at one ladder index is below the *lower* power at the next.  In the aperture
variable the ladder step is `8`, and the aperture-weighted tail rate costs one more, so a two-sided
estimate with multiplicative slacks `c^{σ₊}`, `c^{σ₋}` around the true value is admissible exactly
when

```text
σ₊ + σ₋ < 7/2          (c = 2πλ², so a factor c^σ is λ^{2σ}).
```

### Item 2 is inside the budget

`mass_lower_of_fluxBound` with `K = c²(1−s)²/4` and window `[√s, √s + 1/c]` has
`∫ √K/(1−t²) = O(1)`, so `inside ≥ κ·c^(−1)·Φ(√s)²` against the true `c^(−1/2)`: `σ = 1/2`.

### Item 1 is not, and why

`prolate_endpoint_le_log` — the improved form, with the comparison window taken proportional to the
distance to the endpoint rather than fixed — has loss exactly

```text
∫_a^b 6/(1−t) dt = 6·(log(1−a) − log(1−b))            (integral_six_div_one_sub)
```

which is the best this method gives: optimizing the window fraction `θ` in
`2/θ + 1/(1−θ)` bottoms out near `5.83`, and pushing the no-dip constant `2` down to its floor `1`
only reaches `4`.  The endpoint bound must be carried to `1 − b ≍ c^(−2)` — any farther out and the
uncovered WKB tail `∫_b^1 √q ≍ c√(1−b)` itself blows up — so the loss is `(1−b)^(−6) ≍ c^(12)`.
That is `σ₊ ≈ 12`, far outside `7/2`.

The reason is structural: the no-dip bound `v ≥ √Q − M − 2/L` compares a profile `√Q ≍ c(1−t)^(−1/2)`
against a loss `≍ (1−t)^(−1)`, and the two cross exactly at `1 − t ≍ c^(−2)` — precisely the scale
the argument has to reach.  No choice of window repairs that; the method is sharp in the exponential
rate and inherently `c^(O(1))` in the prefactor.

So `RiccatiNoDip` and `prolate_endpoint_le_log` stand as unconditional theorems — uniform, with no
initial data and no approximation theory — but they are not the tool that closes `(β)`.

### What is the tool

The corpus already owns the sharp endpoint analysis, on the *radial* side, with explicit constants
and `O(1/c)` relative error — which is `σ = 0`:

```text
ProlateDunsterEndpointCoefficientBounds
    abs_radialProlate_regularCoefficient_crossing_le            |F_regular| ≤ 18/c
    abs_radialProlate_logCoefficient_sub_pi_div_four_crossing_le |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer
    abs_radialProlate_sub_regularModel_le
        the endpoint-normalized radial profile differs from the regular Bessel model by
        O(1/c) times the common Bessel amplitude, uniformly beyond the matching point
ProlateDunsterEndpointVolterra, ProlateDunsterEndpointWronskian, ProlateDunsterBesselOffDiagonal,
ProlateTwoBranch  (the Liouville–Green amplitude and its two-branch form)
```

These are unconditional and already carry the `1/c` relative precision that `(β)` needs.  So the
route for **item 3** — and for the sharp replacement of item 1 — is not new WKB theory but the
computation of the exterior mass of the *Bessel model*:

```text
∫_1^∞ (model)² ≍ R(1)²/c ,
```

after which `abs_radialProlate_sub_regularModel_le` transfers it to the actual profile with `O(1/c)`
relative error.  The model integral is elementary in the Liouville–Green variable: with
`z = κ√(2u)`, `u = t − 1`, `κ² = c²(1−s)`,

```text
∫_0^1 J₀(κ√(2u))² du = (1/κ²)∫_0^{κ√2} J₀(z)² z dz ≍ 1/κ ≍ 1/c ,
```

and the far field contributes `O(1/c)` through the `1/t` decay of the amplitude.  What that needs
from mathlib or from the corpus is `∫ J₀² z dz` — the Bessel Parseval/`J₀² + J₁²` identity — plus
the corpus's own amplitude bounds.

### Revised status of the three items

1. **Endpoint upper bound** — proved unconditionally at the sharp exponential rate with a
   `c^(O(1))` prefactor (`prolate_endpoint_le_log`); *not* sharp enough on its own, superseded for
   `(β)` by the Dunster transfer.
2. **Interior mass from below** — proved, `σ = 1/2`, inside the budget.
3. **Exterior mass** — open; reduces to the Bessel-model mass integral above, with the transfer
   already unconditional in the corpus.

## `(β)` item 3 closed: the exterior mass is `O(1/c)`

`formal/GaloisForLFunctions/RHTower/ProlateExteriorMassBound.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
radialProlateExteriorMassConstant = 9/10 + 2π·K² + 2T/5
integral_Ioi_profileDensity_le_half
integral_Ioi_crossing_radialProlate_sq_le :
    ∫_{x > 1 + 9/(8c²)} R² ≤ (2πK² + 2T/5)/c
integral_Ioc_one_crossing_radialProlate_sq_le :
    ∫_{1}^{1 + 9/(8c²)} R² ≤ 9/(2c²)
integral_Ioi_one_radialProlate_sq_le :
    ∫_{x > 1} R(x)² dx ≤ radialProlateExteriorMassConstant / c
```

for every endpoint-normalized (`R 1 = 1`) exact radial solution, `0 ≤ s ≤ 1/2`, `c ≥ 5`.  `K` is
`lgBesselCommonEnvelopeConstant` and `T` is `radialProlateDensityTransferConstant`.

No new analysis was needed: the corpus already owned both halves and they had not been combined.
`integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le` transfers the exact density
`c·R²` to the regular Bessel density in `L¹` with error `2T/c`, and
`integral_Ioi_radialProlateBesselDensity_le` dominates the Bessel density by a *bandwidth-free*
multiple of the arcsine profile density, whose total tail mass `integral_Ioi_profileDensity` is
`1/2`.  So the exact exterior density has total mass `O(1)`, and since the density carries the
factor `c`, the mass of `R²` itself is `O(1/c)`.  The collar `[1, 1 + 9/(8c²)]` between the singular
endpoint and the Dunster matching point is covered by `abs_radialProlate_le_two_endpoint` (`|R| ≤ 2`)
times its length, contributing `9/(2c²)`.

That is the sharp order: `σ = 0`.

## The single remaining bottleneck, stated exactly

With items 2 and 3 sharp, the leakage ratio `d/(1−d) = outside/inside` is controlled except for one
factor.  Normalizing `Φ(1) = 1`:

```text
outside ≤ C/c                                     (item 3, σ = 0)
inside  ≥ κ·c^(−1)·Φ(√s)²                          (item 2, σ = 1/2)
Φ(√s)  ≥ Φ(b)·exp(∫_{√s}^b prolateWKB − 6·log((1−√s)/(1−b)))   (item 1)
```

and `Φ(b) ≥ Φ(1) = 1` for free, because `Φ` is antitone past the turning point.  Every factor is
sharp except the last: item 1's loss `6·log((1−√s)/(1−b))` with `1 − b ≍ c^(−2)` is `c^(−12)`, and it
enters `inside` **squared**, so `σ₊ ≈ 24` against a budget of `7/2`.

So the whole of `(β)` now rests on one quantity:

> the barrier ratio `Φ(√s)/Φ(1)`, to relative precision `c^(±3/2)`.

Both directions of it are proved at the sharp exponential rate — `exp_neg_sharp_le_endpoint` below
and `prolate_endpoint_le_log` above — and both carry a `c^(O(1))` prefactor.  Closing the gap is the
band-side analogue of what the corpus's Dunster layer already does on the radial side: Liouville–Green
error control with an `O(1/c)` error-control function, rather than the crude Riccati comparison.  The
tools on the radial side that would be mirrored are

```text
CCMFirstRowDunsterModel      the Bessel model, its derivatives, and the common envelope constant
ProlateDunsterEndpointVolterra    endpoint-anchored Volterra transport
ProlateDunsterEndpointCoefficientBounds   |F_regular| ≤ 18/c,  |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer     the uniform O(1/c) transfer beyond the matching point
```

and the band-side model is not Bessel but parabolic-cylinder (Hermite) at the turning point
`y = √s`, with a Liouville–Green region between the two.  `HTGeometry.LiouvilleTransformation` and
`HTGeometry.LiouvilleGreenErrorBound` supply the transformation and the *oscillatory* Volterra error
bound already; what is missing is the **exponential** (barrier) analogue of
`abs_le_exp_of_oscillatoryLG`, with kernel `sinh` in place of `sin`.  That is one module of the same
shape as the oscillatory one, and it is the last unconditional input `(β)` needs.

## The barrier error bound — the last named input for `(β)`

The previous entry identified the remaining bottleneck as the barrier ratio `Φ(√s)/Φ(1)` to
relative precision `c^(±3/2)`, and named the missing tool: the **exponential** analogue of the
corpus's oscillatory Liouville–Green error bound, with kernel `sinh` in place of `sin`.  It is now
proved.

`formal/GaloisForLFunctions/HTGeometry/GronwallBackward.lean` and
`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenExponentialErrorBound.lean`, both wired into
the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
integral_comp_reflect
abs_le_exp_integral_of_volterra_bound_backward
continuous_integral_tail
abs_sub_one_le_exp_sub_one_of_volterra_bound_backward

expLGKernel u ξ t = (1 − exp(−2u(t−ξ)))/2
expLGKernel_nonneg, expLGKernel_le_half, abs_expLGKernel_le_half
IsExponentialLGSolution b u ψ V a :
    ∀ ξ ∈ [a,b],  V ξ = 1 + (1/u) ∫_ξ^b κ(ξ,t) ψ(t) V(t) dt
volterra_defect_of_exponentialLG
volterra_bound_of_exponentialLG
abs_le_exp_of_exponentialLG :
    |V ξ| ≤ exp((1/2u) ∫_ξ^b |ψ|)
abs_sub_one_le_exp_sub_one_of_exponentialLG :
    |V ξ − 1| ≤ exp((1/2u) ∫_ξ^b |ψ|) − 1
```

Two things make this the right statement rather than the naive one.  First, the anchor: on a
barrier the recessive branch accumulates from the *right*, so the Volterra equation integrates from
the far endpoint back, and the Grönwall inequality has to be reflected — that is
`GronwallBackward`, obtained from the corpus's forward inequality by the substitution
`u ↦ a + b − u` (`integral_comp_reflect`).  Second, the normalization: the raw kernel
`sinh(u(ξ−t))` is unbounded, and the entire content of writing `V(ξ) = e^{u(ξ−a)}W(ξ)` is that the
normalized kernel `e^{u(ξ−t)} sinh(u(t−ξ)) = (1 − e^{−2u(t−ξ)})/2` lies in `[0, 1/2]`.  The error
control is then the *mass* `∫_ξ^b |ψ|` of the perturbation, not a pointwise bound times the length —
which is what makes the estimate survive a barrier of length `≍ c`.

Applied to the prolate barrier after the Liouville transformation
(`HTGeometry.LiouvilleTransformation`), `ψ` is the LG defect `A''/A − g/f`, whose mass over the
barrier is `O(1/c)` away from the turning point, so the bound reads `|V − 1| ≤ e^{O(1/c)} − 1 =
O(1/c)` — precision `σ = 0`, against the `σ ≈ 12` of the Riccati route.

### What `(β)` still needs, after this

The pieces are now: sharp action (`prolateAngleAction_sub_bounds`), interior mass from below
(`mass_lower_of_fluxBound`, `σ = 1/2`), exterior mass from above
(`integral_Ioi_one_radialProlate_sq_le`, `σ = 0`), and the barrier error bound above (`σ = 0`).
What remains is *assembly*, in three steps, none of which needs a new estimate:

1. Perform the Liouville transformation on the prolate barrier explicitly — produce the `ξ`, `A`,
   `ψ` of `hasDerivAt_liouvilleTransform` for `q = (χ + c²y²)/(1 − y²)` — and check that the
   prolate mode's normalized transform satisfies `IsExponentialLGSolution`.
2. Bound the mass `∫ |ψ|` of the LG defect over `[y₀, 1 − δ]` by `O(1/c)`; this is the same
   computation the corpus already performs on the radial side in
   `CCMRadialProlateDefect.integral_volterra_exponent_le`.
3. Cross the turning layer at `y = √s`, where LG fails: the corpus's `ProlateTurningLayer` already
   propagates the amplitude across it at a fixed cost `exp(1)`, so this contributes `σ = 0`.

Step 2 is the only one with content, and its radial twin is already proved.

## The barrier Liouville–Green package is complete

The previous entry named "one module of the same shape as the oscillatory one" as the last
unconditional input.  It is built, and with it the barrier analogue of the corpus's oscillatory
Liouville–Green layer is complete end to end.

`formal/GaloisForLFunctions/HTGeometry/PerturbedBarrierVolterra.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
barrierCoshTail, barrierSinhTail, barrierKernelTail, barrierKernelTailDeriv
barrierKernelTail_eq          the separated form IS ∫_ξ^b sinh(u(ξ−t)) ψ W
hasDerivAt_barrierKernelTail       K′ = u(cosh·C − sinh·S)     (the lower-limit terms cancel)
hasDerivAt_barrierKernelTailDeriv  K″ = u²K − u ψ W            (via cosh² − sinh² = 1)
barrier_volterra_eq :
    W″ = (u² + ψ)W ,  W(b) = e^{−u(b−a)} ,  W′(b) = −u e^{−u(b−a)}
      ⟹  W ξ = e^{−u(ξ−a)} − (1/u)·∫_ξ^b sinh(u(ξ−t)) ψ W
isExponentialLGSolution_of_ode :
    hence  ξ ↦ e^{u(ξ−a)} W ξ  satisfies  IsExponentialLGSolution
abs_barrier_normalized_sub_one_le :
    |e^{u(ξ−a)} W ξ − 1| ≤ exp((1/2u)·∫_ξ^b |ψ|) − 1
barrier_two_sided :
    (2 − E)·e^{−u(ξ−a)} ≤ W ξ ≤ E·e^{−u(ξ−a)} ,   E = exp((1/2u)·∫_ξ^b |ψ|)
```

Three things had to be right.  The **anchor**: recessive data is imposed at `b`, and the Volterra
kernel integrates back from there, because forward integration of a recessive branch is unstable —
that is why `GronwallBackward` was needed.  The **separation**: `sinh(u(ξ−t)) = sinh(uξ)cosh(ut) −
cosh(uξ)sinh(ut)` splits the kernel integral into two ordinary tail primitives, so its first
derivative loses the lower-limit terms exactly (they cancel) and its second derivative is
`u²K − uψW`; the equation then follows from the corpus's uniqueness for `v″ = P v`
(`LinearSecondOrderUnique.secondOrder_eq_at`) applied to the difference against the zero solution.
The **normalization**: `e^{u(ξ−t)}sinh(u(ξ−t)) = −(1 − e^{−2u(t−ξ)})/2 ∈ [−1/2, 0]`, which is what
turns an unbounded kernel into a contraction and makes the error control the *mass* `∫_ξ^b |ψ|`
rather than a pointwise bound times the length — the difference between an estimate that survives a
barrier of length `≍ c` and one that does not.

`barrier_two_sided` is precisely the `σ = 0` replacement for `prolate_endpoint_le_log`: the relative
error is `E − 1`, and for the prolate barrier `∫|ψ| = O(1/c)` gives `E − 1 = O(1/c²)`.

### `(β)`: what is left

```text
sharp action                      prolateAngleAction_sub_bounds          ✔
interior mass from below          mass_lower_of_fluxBound        σ = 1/2 ✔
exterior mass from above          integral_Ioi_one_radialProlate_sq_le  σ = 0 ✔
barrier estimate, both sides      barrier_two_sided              σ = 0   ✔
```

Only the instantiation remains, and it is two steps:

1. **Liouville transformation of the prolate barrier.**  Produce `ξ = ∫√Q`, `A = Q^{1/4}`, and the
   defect `ψ = Q^{−1/4}(Q^{−1/4})″` for `Q = (χ + c²y²)/(1 − y²)`, and check the two identities of
   `HTGeometry.hasDerivAt_liouvilleTransform` (`X′² = 1/f(X)` and `A²X′` constant).
2. **The defect mass.**  `∫ |ψ| dξ = ∫ |Q^{−1/4}(Q^{−1/4})″| dy = O(1/c)` away from the turning
   point, because `Q ≍ c²` there so `Q^{−1/4} ≍ c^{−1/2}` and its second derivative is again
   `≍ c^{−1/2}`.  The radial twin of this computation is already proved as
   `CCMRadialProlateDefect.integral_volterra_exponent_le`.

The turning layer at `y = √s`, where Liouville–Green fails, is crossed by the corpus's
`ProlateTurningLayer` at the fixed cost `exp(1)`, i.e. `σ = 0`.

## The turning layer drops out of the leakage upper bound

A re-derivation of the assembly removes the hardest remaining region.  The previous plan anchored
the interior mass at the turning point `y = √s` and therefore had to cross the Airy layer, where
neither Liouville–Green nor the flux bound is sharp: the uniform flux bound `|(1−y²)Φ′| ≤ (c/2)Φ`
integrates to `c√s ≍ √c` over `[√s, 2√s]`, and the LG defect mass diverges like `τ^(−3/2)` as the
turning point is approached.

Anchor the interior mass at `2√s` instead.  Then:

```text
inside  ≥ κ·c^(−1)·Φ(2√s)²        mass_lower_of_fluxBound on [2√s, 2√s + 1/c],
                                   where ∫ √K/(1−t²) = O(1)
outside ≤ (C/c)·Φ(1)²             integral_Ioi_one_radialProlate_sq_le, homogeneous
Φ(1) ≤ Φ(1−ε)                     free: Φ is antitone past the turning point
leakage = outside·value²/inside   the exact mass balance
```

so

```text
leakage ≤ (C/κ)·(Φ(1−ε)/Φ(2√s))² ,
```

and the only analytic input left is the barrier ratio on `[2√s, 1−ε]` — **strictly inside the
region where Liouville–Green is valid**.  The Airy layer `[√s, 2√s]` never appears, and neither
does the endpoint collar `[1−ε, 1]`, because monotonicity of `Φ` supplies the inequality in the
direction the upper bound needs.

The two truncations cost nothing:

```text
∫_{√s}^{2√s} √q  ≈ (2√2/3)·c·s = (2√2/3)(2n+1) = O(1)
∫_{1−ε}^{1} √q   ≈ c√ε = O(1)     for ε ≍ c^(−2)
```

so `∫_{2√s}^{1−ε} √q = c·A(s) + O(1)` — the sharp action up to a bounded factor, `σ = 0`.  And the
LG defect mass on `[2√s, 1−ε]` is `O(1)`: near the turning point the integrand
`Q^{−1/4}(Q^{−1/4})″` scales as `c^{−1}s^{−1}τ^{−5/2}` against `dy = √s dτ`, and `c·s = 2n+1` is
bounded, so the mass is `C_n·τ₀^{−3/2}` with `τ₀ = 1`; near `y = 1` it is `c^{−1}(1−y²)^{−3/2}`,
integrating to `c^{−1}ε^{−1/2} = O(1)`.

### The scalar step, proved

`formal/GaloisForLFunctions/RHTower/ProlateLeakageUpperScalar.lean`, wired into the `RHTower`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
leakage_upper_of_mass_bounds :
    outside = inside·leakage/value² ,  L ≤ inside ,  outside ≤ U ,  value² ≤ 1
      ⟹  leakage ≤ U/L
leakage_upper_of_prolate_masses :
    with the exterior mass supplied by integral_Ioi_one_radialProlate_sq_le,
      leakage ≤ (radialProlateExteriorMassConstant / c) / L
```

This is the companion the corpus lacked: `ProlateTurningLayer.leakage_lower_of_radial_mass_bounds`
reads the same balance in the other direction.  Note that the concentration value only helps —
`value² ≤ 1` — so no lower bound on it is needed.

### `(β)`'s upper half, remaining

One item: instantiate `HTGeometry.barrier_two_sided` on `[2√s, 1−ε]`, which needs the Liouville
transformation of the prolate normal form
`Q̂ = (χ + c²y²)/(1−y²) + (1−y²)^(−2)` and the `O(1)` bound on `∫|Q̂^{−1/4}(Q̂^{−1/4})″|`.  Then
`Φ(1−ε)/Φ(2√s) ≤ E·exp(−∫_{2√s}^{1−ε}√Q̂)` with `E = O(1)`, and
`leakage ≤ C·e^{−2cA(s)} = C·c^(n+1/2)e^{−2c}` — the Fuchs upper bound.

The lower half needs the two reversed inputs: `outside` from below at the sharp order (the corpus
has only `≥ 1/(32c²)`, lossy by `c`) and `inside` from above (`integral_sq_le_turning_amplitude_envelope`,
lossy by `c²`).  Both are mass estimates, not decay estimates, and both are now the only places
where the turning layer still enters.

## Liouville–Green in the original variable — no change of variable, no inverse function

The obstruction to instantiating the barrier estimate was never the analysis: it was that Olver's
theorem is stated in the Liouville variable `ξ = ∫√Q`, whose inverse has no closed form, so applying
it requires constructing that inverse in Lean.  That detour is unnecessary.

Writing the exact solution of `Φ'' = QΦ` as `Φ = G·R` against the Liouville–Green approximant
`G = A e^{−Ξ}`, `A = Q^{−1/4}`, `Ξ' = A^{−2}`, the Wronskian `H = Φ'G − ΦG'` satisfies
`H' = −A''e^{−Ξ}Φ`, and the ratio satisfies `R' = H e^{2Ξ}/A²`.  A single integration by parts,
against the primitive `(e^{2Ξ(t)} − e^{2Ξ(y)})/2` of `e^{2Ξ}/A²` chosen to vanish at `y`, collapses
the nested integral to **one** Volterra equation with a bounded kernel — no Fubini, no change of
variable, the phase entering only as the explicit function `Ξ`.

`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenPhaseErrorBound.lean` and
`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenOde.lean`, both wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
lgPhaseKernel Ξ ξ t = (1 − exp(−2(Ξ t − Ξ ξ)))/2 ,   0 ≤ · ≤ 1/2 when Ξ ξ ≤ Ξ t
IsPhaseLGSolution b Ξ ψ R a :  R ξ = 1 − ∫_ξ^b lgPhaseKernel Ξ ξ t · ψ t · R t
phase_volterra_defect, phase_volterra_bound
abs_le_exp_of_phaseLG,  abs_sub_one_le_exp_sub_one_of_phaseLG,  phaseLG_two_sided

lgApprox, lgApproxDeriv, lgWronskian, lgRatio
hasDerivAt_lgApprox        G' = (A' − 1/A) e^{−Ξ}
hasDerivAt_lgApproxDeriv   G'' = (A'' + A^{−3}) e^{−Ξ} = Q G + A'' e^{−Ξ}
hasDerivAt_lgWronskian     H' = −(Φ · A'' · e^{−Ξ})
hasDerivAt_lgRatio         R' = H e^{2Ξ}/A²
isPhaseLGSolution_lgRatio  the Volterra equation, by the integration by parts above
lgRatio_two_sided :
    2 − E ≤ Φ(y)/(A(y)e^{−Ξ(y)}) ≤ E ,        E = exp(½ ∫_y^b |A A''|)
```

`A A'' = Q^{−1/4}(Q^{−1/4})''` is exactly Olver's error-control density, and the estimate is stated
with `y`-integrals throughout.  For the prolate barrier `∫|A A''| = O(1)` on `[2√s, 1−ε]`, so
`E = O(1)`: precision `σ = 0`.

### The remaining obstruction, stated exactly

`lgRatio_two_sided` describes the solution *normalized to the approximant at the right endpoint* —
the recessive branch.  The prolate mode is a different solution, and the Wronskian
`W = Φ'Φ_r − ΦΦ_r'` between them is constant, with

```text
Φ(b)/Φ(y) ≤ Φ_r(b)/Φ_r(y)      ⟺      W ≤ 0      ⟺      v ≥ w at one point,
```

`v = −Φ'/Φ` and `w = −Φ_r'/Φ_r`.  A *small* `W` is not enough: the dominant branch grows by
`e^{2Ξ(b)}`, so only the sign is usable.  And `v ≥ w` at a point is again a lower bound on `v` of
precision `O(1)` against `√Q` — which is what Liouville–Green itself would provide, so the argument
closes on itself.

What breaks the circle is the boundary condition the mode actually satisfies.  Note that
`Ξ(1) = ∫^1 √Q` **converges** (`√Q ≍ c(1−y)^{−1/2}`), so at `y = 1` the recessive/dominant
distinction degenerates — as it must, `y = 1` being a regular singular point where the natural basis
is (analytic, logarithmic), not (recessive, dominant).  The prolate mode is the analytic one, and
its decomposition in the Liouville–Green basis is fixed by matching at that point.

That is precisely what the corpus's Dunster layer already does on the *radial* side
(`ProlateDunsterEndpointCoefficientBounds`: `|F_regular| ≤ 18/c`, `|F_log − π/4| ≤ 141/c`).  The
band-side mirror of that layer — Frobenius/Bessel matching at `y = 1⁻` — is the one remaining input
for `(β)`'s upper half, and it is a construction of the same shape as one the corpus already owns.

## The bridge from the Liouville–Green branch to the actual mode, and the endpoint model identified

`lgRatio_two_sided` describes one distinguished solution — the one normalized to the approximant at
the right endpoint.  The bridge to an arbitrary solution of the same equation is the Wronskian, and
it is now formal.

`formal/GaloisForLFunctions/HTGeometry/DecayRatioComparison.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
solutionWronskian Φ Φ' Ψ Ψ' y = Φ' y · Ψ y − Φ y · Ψ' y
hasDerivAt_solutionWronskian, solutionWronskian_const     it is constant along v'' = P v
solutionWronskian_nonpos_iff :   W ≤ 0  ↔  Φ'/Φ ≤ Ψ'/Ψ
ratio_le_of_solutionWronskian_nonpos :
    W ≤ 0  ⟹  Φ(b)/Φ(a) ≤ Ψ(b)/Ψ(a)
```

So the leakage upper bound reduces to **one sign**: with `Ψ` the Liouville–Green branch and `Φ` the
prolate mode, `W ≤ 0` transfers the whole two-sided estimate to the mode.  Only the sign is usable —
on a barrier the two branches differ by `e^{2Ξ(b)}`, so a merely small `W` carries no information.

### What fixes the sign, computed

The sign is decided at `y = 1`, and the endpoint model is now identified explicitly.  Writing
`u = 1 − y` and `K = χ + c²`, the Sturm form `((1−y²)Φ')' = (χ + c²y²)Φ` becomes, to leading order,

```text
(u Φ_u)_u = (K/2) Φ ,
```

and the substitution `z = √(2K u)` — so `z ≍ 1` exactly when `1 − y ≍ c^(−2)`, the scale at which
the Liouville–Green window must stop — turns it into

```text
Φ_zz + (1/z) Φ_z − Φ = 0 ,
```

the **modified** Bessel equation of order zero.  So the band-side endpoint model is `I₀`, `K₀` — not
`J₀`, `Y₀`; the band side of the endpoint is the forbidden region, whereas the radial side that the
corpus's Dunster layer already treats is the allowed one.

The mode is analytic at `y = 1`, hence the `I₀` branch, and `I₀` is the branch that *grows inward* —
which is the Liouville–Green recessive branch.  So the sign is the expected one, and the content of
the remaining work is the quantitative matching at `z ≍ 1`.

Two consequences worth recording.  First, the normal-form potential

```text
Q̂ = (χ + c²y²)/(1−y²) − (1−y²)^(−2)
```

is **negative** for `1 − y² < 1/K`: the barrier ends at exactly the scale `c^(−2)`, and beyond it the
normal form is the Euler equation `W'' + W/(4(1−y)²) = 0` of an exponent-`(0,0)` singularity, whose
solutions are `√u` and `√u log u`.  That is why no crude comparison of `v` against `√Q̂` can decide
the sign there — both are `Θ(c²)` at the matching point and the constants decide.

Second, this is a construction of the same shape as one the corpus owns: the radial layer
(`CCMFirstRowDunsterModel`, `ProlateDunsterEndpointVolterra`,
`ProlateDunsterEndpointCoefficientBounds`, `ProlateDunsterUniformTransfer`) does exactly this with
`besselJ0` in place of `I₀`.  mathlib has neither; the corpus built `besselJ0` for the radial side,
and the band side needs `besselI0` built the same way.

### `(β)`'s upper half, remaining

```text
sharp action                     prolateAngleAction_sub_bounds              ✔
interior mass from below         mass_lower_of_fluxBound            σ = 1/2 ✔
exterior mass from above         integral_Ioi_one_radialProlate_sq_le  σ = 0 ✔
mass balance → leakage           leakage_upper_of_mass_bounds              ✔
Liouville–Green, original variable  lgRatio_two_sided                σ = 0 ✔
branch → actual mode             ratio_le_of_solutionWronskian_nonpos      ✔
```

One item: the modified-Bessel endpoint layer at `z = c√(2(1−y))`, giving `W ≤ 0`.

## The modified Bessel function of order zero, built

The endpoint model identified in the previous entry needs `I₀`, which mathlib does not have and the
corpus did not have either — it built `besselJ0` for the radial side and nothing for the band side.

`formal/GaloisForLFunctions/RHTower/BesselIZeroODE.lean`, wired into the `RHTower` umbrella, axioms
`[propext, Classical.choice, Quot.sound]`:

```text
besselI0 u            = (1/π) ∫_0^π cosh(u sin θ) dθ
besselI0Deriv u       = (1/π) ∫_0^π sin θ · sinh(u sin θ) dθ
besselI0SecondDeriv u = (1/π) ∫_0^π sin²θ · cosh(u sin θ) dθ

abs_sinh_le, cosh_le_cosh_of_abs_le, abs_mul_sin_le
hasDerivAt_besselI0, hasDerivAt_besselI0Deriv        differentiation under the integral
integral_sin_mul_sinh_eq                            the integration by parts
besselI0SecondDeriv_sub_besselI0
besselI0_ode :   I₀'' + I₀'/u − I₀ = 0
besselI0_zero, besselI0_pos, besselI0Deriv_nonneg, monotoneOn_besselI0
besselI0Deriv_le_besselI0,  besselI0_logDeriv_le_one :   I₀'/I₀ ≤ 1
```

The construction mirrors the corpus's `besselJ0` line for line with the circular functions replaced
by hyperbolic ones; the one structural difference is the domination.  `cos` is bounded, `cosh` is
not, so differentiation under the integral sign is justified on `Metric.ball u 1` with the bounds
`sinh(|u|+1)` and `cosh(|u|+1)` rather than on the whole line with the bound `1`.

`besselI0_logDeriv_le_one` is the one qualitative fact the matching will use: pointwise
`sin θ · sinh(u sin θ) ≤ cosh(u sin θ)` because `sin θ ≤ 1` and `sinh ≤ cosh`, so the analytic
branch's logarithmic derivative never exceeds that of `e^z`.

### What the matching still needs

With `I₀` in hand, the band-side endpoint layer is the mirror of the corpus's radial one:

```text
radial (allowed, J₀)                        band (forbidden, I₀)
CCMFirstRowDunsterModel                     the I₀ model at z = c√(2(1−y))
ProlateDunsterEndpointWronskian             endpoint Wronskian values
ProlateDunsterEndpointVolterra              endpoint-anchored transport
ProlateDunsterEndpointCoefficientBounds     |F_regular| ≤ 18/c, |F_log − π/4| ≤ 141/c
ProlateDunsterUniformTransfer               the uniform O(1/c) transfer
```

and its output is the sign `W ≤ 0` that `ratio_le_of_solutionWronskian_nonpos` consumes.  Note that
the comparison cannot be done by inspecting `I₀'/I₀` against the Liouville–Green profile directly:
in the `z` variable both are `1 + O(1/z)` at the matching point `z ≍ 1`, so the constants decide,
which is exactly what the Volterra transfer computes.

## The band-side comparison equation

`formal/GaloisForLFunctions/RHTower/BesselIZeroModel.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
besselIModel c ξ x            = I₀(c ξ x)
besselIModelDeriv, besselIModelSecondDeriv
hasDerivAt_besselIModel, hasDerivAt_besselIModelDeriv
besselIModel_ode :
    V'' + (ξ'/ξ − ξ''/ξ') V' − c² (ξ')² V = 0
```

exactly, for every `c` and every phase `ξ`, with nothing approximated: the second derivative
contributes `c²ξ'² I₀ − (cξ'²/ξ) I₀' + c ξ'' I₀'` by `besselI0_ode`, and the first-order coefficient
is exactly the negative of the two `I₀'` terms.

This is the band-side counterpart of `CCMFirstRowDunsterModel.lgBesselModel_ode`, with the sign of
the zero-order term reversed — the band endpoint is the forbidden region.  It is stated for an
arbitrary phase rather than for a fixed one, so the choice of band-side Liouville variable can be
made when the defect estimate is written.

### The band-side layer, remaining

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed, xiAmplitude         the band Liouville variable               —
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

whose output is the sign `W ≤ 0` consumed by `ratio_le_of_solutionWronskian_nonpos`.

## The band-side Liouville variable

`formal/GaloisForLFunctions/RHTower/BandEndpointPhase.lean`, wired into the `RHTower` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

```text
bandEndpointPhase s y = ∫_{arcsin y}^{π/2} √(sin²θ − s) dθ
bandEndpointPhase_one, bandEndpointPhase_nonneg, bandEndpointPhase_pos
prolateWKBProfile_eq_div :   √((y²−s)/(1−y²)) = √(y²−s)/√(1−y²)
hasDerivAt_bandEndpointPhase :  Ξ_s' (y) = −√((y²−s)/(1−y²))
sq_prolateWKBProfile :          (Ξ_s')² = (y²−s)/(1−y²)
```

so `c²(Ξ_s')² = (χ + c²y²)/(1−y²)` exactly with `χ = −sc²` — the phase for which the modified-Bessel
model `I₀(c Ξ_s)` carries the right leading potential.

The point of the angular form is that it is not an improper integral at all: `∫_y^1 √((t²−s)/(1−t²))dt`
has an inverse-square-root singularity at the endpoint, but `∫_{arcsin y}^{π/2} √(sin²θ − s) dθ` is a
continuous integrand on a compact interval, and the `y`-derivative comes out by the chain rule
against `Real.hasDerivAt_arcsin`.  The same device removed the singularity from the sharp action
earlier on this card.

`Ξ_s` vanishes at `y = 1` and behaves like `√(1−s)·√(2(1−y))` there, so `c Ξ_s ≍ 1` exactly when
`1 − y ≍ c^(−2)` — the scale at which the Liouville–Green window stops and the endpoint model takes
over, which is what makes the two windows overlap.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed                      bandEndpointPhase, hasDerivAt_…           ✔
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The model drift is elementary — the square root cancels

The comparison equation's first-order coefficient is `Ξ'/Ξ − Ξ''/Ξ'`, and the second term looked as
though it would carry the square root of the WKB profile.  It does not.

`BandEndpointPhase.lean` (extended; wired, axioms `[propext, Classical.choice, Quot.sound]`):

```text
hasDerivAt_prolateWKBArg :
    d/dy [(y²−s)/(1−y²)] = 2y(1−s)/(1−y²)²
hasDerivAt_prolateWKBProfile :
    Ξ'' = −P' ,   P' = (2y(1−s)/(1−y²)²)/(2P)
bandModelDrift s y = y(1−s)/((1−y²)(y²−s))
secondDeriv_div_deriv_bandEndpointPhase :
    Ξ''/Ξ' = bandModelDrift s y
```

The cancellation is exact: `Ξ''/Ξ' = P'/P = (2y(1−s)/(1−y²)²)/(2P²)` and `P² = (y²−s)/(1−y²)`, so the
profile disappears entirely and the ratio is a rational function of `y` with the two poles one
expects — at the turning point `y² = s` and at the endpoint `y² = 1`.

Near the endpoint `bandModelDrift → 1/(2(1−y))` and `Ξ'/Ξ → −1/(2(1−y))`, so the comparison drift
`B_m = Ξ'/Ξ − Ξ''/Ξ' → −1/(1−y)`, whose contribution `B_m²/4 + B_m'/2 → 1/(4(1−y)²) − 1/(2(1−y)²)`
cancels the `−1/(1−y²)² → −1/(4(1−y)²)` of the true normal form.  That cancellation of the leading
`(1−y)^(−2)` singularities is exactly why the band defect is `O(1)` rather than `O(c²)`, and it is
now a computation on explicit rational functions rather than an asymptotic claim.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed                      bandEndpointPhase, hasDerivAt_…           ✔
xiSpeedDeriv                                  hasDerivAt_prolateWKBProfile,
                                              secondDeriv_div_deriv_…                   ✔
lgNormalFormDefect + its mass bound           the band defect, O(1)                     —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The comparison defect: the algebraic collapse

`formal/GaloisForLFunctions/HTGeometry/LiouvilleGreenDriftAlgebra.lean`, wired into the `HTGeometry`
umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

```text
lgDrift Ξ Ξ' D y = Ξ'(y)/Ξ(y) − D(y)
hasDerivAt_lgDrift :   B' = Ξ''/Ξ − (Ξ')²/Ξ² − D'
lgDrift_normalForm :   with Ξ'' = Ξ'·D,
    B²/4 + B'/2 = −(Ξ')²/(4Ξ²) + D²/4 − D'/2
lgDrift_normalForm_of_hasDerivAt
```

`B = Ξ'/Ξ − Ξ''/Ξ'` is the first-order coefficient of the comparison equation `besselIModel_ode`, and
`B²/4 + B'/2` is what it contributes on passing to normal form.  The identity says the cross terms
`Ξ'D/Ξ` cancel and — the point — **no `Ξ''/Ξ` survives**: the model's normal-form potential is built
from `(Ξ')²/Ξ²` and from `D` alone.

For the prolate band `D = bandModelDrift` is rational (the previous entry), so the whole comparison
carries exactly one transcendental ingredient, `(Ξ')²/Ξ²`.  Writing the defect against the true
normal-form potential `Q̂ = c²(Ξ')² − (1−y²)^(−2)` and noting that the two `c²(Ξ')²` cancel — that is
what the phase was chosen for — the defect is

```text
(Ξ')²/(4Ξ²) − 1/(1−y²)² − D²/4 + D'/2 ,
```

with no `c` in it at all.  At the endpoint each of the four terms is `Θ((1−y)^(−2))` — respectively
`1/16`, `−1/4`, `−1/16`, `+1/4` times `(1−y)^(−2)` — and they sum to zero.  That is the cancellation
that makes the comparison defect `O(1)` rather than `O(c²)`, and it is now an identity between
explicit functions rather than an asymptotic assertion.

### The band-side layer

```text
radial (allowed, J₀)                          band (forbidden, I₀)
besselJ0, besselJ0_ode                        besselI0, besselI0_ode                    ✔
CCMFirstRowDunsterModel.lgBesselModel_ode     besselIModel_ode                          ✔
xiEndpointPhase, xiSpeed, xiSpeedDeriv        bandEndpointPhase + both derivatives      ✔
lgNormalFormDefect (its algebra)              lgDrift_normalForm                        ✔
its mass bound                                the O(1) mass bound                       —
ProlateDunsterEndpointWronskian               endpoint Wronskian values                 —
ProlateDunsterEndpointVolterra                endpoint-anchored transport               —
ProlateDunsterEndpointCoefficientBounds       |F_regular|, |F_log − π/4| = O(1/c)       —
```

## The card's stated bottleneck is closed: the barrier ratio, two-sided

The bottleneck recorded above was

> the barrier ratio `Phi(y0)/Phi(1)`, to relative precision `c^(±3/2)`.

`RHTower/ProlateBarrierRatioTwoSided.lean` (wired, axiom-clean) delivers both directions with the
*same* sharp exponential:

```
prolateBand_sq_le_exp_bandPhase
    Phi(y0)^2  <=  C · exp(2 c Xi_s(y0) + Lambda)

prolateBand_barrier_ratio_two_sided
    exp(c Xi_s(y0) + 6 log((1-alpha)/(1-y0))) / (6 pi sqrt(c Xi_s(alpha)))  <=  Phi(y0)
      and the square bound above
```

with `C = 1 + (1-alpha^2)(barrier(alpha) + 6/(1-alpha))^2 / (c^2(alpha^2-s))` and
`Lambda = prolateScaleLog s y0 alpha = log((alpha^2-s)(1-y0^2)/((y0^2-s)(1-alpha^2)))`.

Since both bounds carry `exp(c Xi_s(y0))`, the relative precision is the product of the two
prefactors: `sqrt(C exp Lambda)` and `6 pi sqrt(c Xi_s(alpha))`.  With `y0 = 2 sqrt s`, `alpha` a
fixed collar edge, `cs = 2n+1` and `s ~ 1/c`,

```
exp Lambda = O(1/s) = O(c) ,     C = O(1) ,     c Xi_s(alpha) = O(c) ,
```

so the relative precision is `O(sqrt c) · O(sqrt c) = O(c)` — inside the required `c^(3/2)`.

The route that achieves this is *not* the parabolic-cylinder / Liouville-Green package the earlier
entry proposed.  It is the **Sturm amplitude envelope at a matched scale**
(`HTGeometry/SturmAmplitudeEnvelope.lean`): for `(pR')' + QR = 0` and any scale `K`,

```
G = R^2 + (pR')^2/K ,     |G'/G|  <=  sqrt K · |1/p - Q/K|  +  |K'|/K .
```

Taking `K = -Qp` in the band makes `1/p - Q/K = 2/p`, hence `sqrt K (2/p) = 2 c P(y)` — *exactly
twice the WKB rate* — and the entire extra cost is the logarithmic variation of the scale, two
elementary logarithms.  Taking `K = c^2 s` on the allowed interval `[0, 2 sqrt s]` gives
`|1/p - Q/K| = 1/(1-y^2) - 1 + y^2/s in [0,5]` and `sqrt K = c sqrt s`, so the turning layer is
crossed at cost `exp(10 c s)`, a constant for a fixed mode.  No turning-point model function is
needed at all: neither Airy, nor parabolic cylinder, nor a Liouville-Green error-control function.

Consequences already landed:

```
RHTower/ProlateApertureMassSharp.lean
    prolate_allowed_sq_le, sturmAmplitude_const_le_three_mul_band,
    prolateBandAmplitude_le_uniform, prolate_sq_le_aperture_envelope,
    integral_sq_le_aperture_envelope, integral_sq_le_exp_sharp_action_amplitude
RHTower/ProlateLeakageLowerSharp.lean
    integral_Ioi_radialProlate_sq_ge_half,
    prolate_leakage_ge_exp_sharp_amplitude, prolate_leakage_ge_explicit
```

`prolate_leakage_ge_explicit` is the leakage lower bound at the standard matching point
`y0 = 2 sqrt s`, entirely elementary in its constants:

```
besselEnergyFloor/(864 c)
  / (2 (2 (3C+1) exp(2c(1 + (s/4) log s) + log((alpha^2-s)/(3s)) + log((1-4s)/(1-alpha^2))
                      + 10 c s)))
    <=  leakage .
```

Both halves of `(beta)` are now Lean-proved, axiom-clean, and inside the precision budget
(`sigma_+ + sigma_- = 5/2 < 7/2`).

## `(beta)` delivered: the leakage, two-sided, at the sharp action

`RHTower/ProlateLeakageTwoSided.lean` (wired, axiom-clean):

```
prolate_leakage_two_sided

  besselEnergyFloor/(864 c)
    / (2 (2 (3C+1) exp(2c(1 + (s/4) log s)
                        + log((alpha^2-s)/(3s)) + log((1-4s)/(1-alpha^2)) + 10 c s)))
      <=  leakage  <=
  radialProlateExteriorMassConstant/c
    · ((6 pi sqrt(c Xi_s(alpha)))^2 exp(2 E) / (b - 2 sqrt s))
    · exp(-2(c Xi_s(2 sqrt s) + 6 log((1-alpha)/(1-2 sqrt s))))
```

with `E = (c b + 12)(b - 2 sqrt s)/(1 - b^2)` and `C` the anchor constant.  Both directions carry the
same exponential `exp(-2 c Xi_s(2 sqrt s))`, and `Xi_s(2 sqrt s) <= A(s) = 1 + (s/4) log s + O(s)`,
so with `cs = 2n+1` and `s ~ 1/c` the shared exponential is `exp(-2c) c^{n+1/2}` up to a bounded
factor.  The gap between the two prefactors is `c^{5/2}`, inside the card's budget of `7/2`.

The last new input was the interior mass from below, `RHTower/ProlateInteriorMassLower.lean`:

```
prolateFlux_sq_le_band            |(1-t^2) Phi'| <= (1-t^2)(barrier(t) + 6/(1-t)) |Phi|
one_sub_sq_mul_band_barrier_le    (1-t^2)(barrier(t) + 6/(1-t))  <=  c b + 12      (t <= b)
prolate_window_mass_lower         (b-y0)(Phi(y0) exp(-(cb+12)(b-y0)/(1-b^2)))^2 <= int_{y0}^b Phi^2
prolate_aperture_mass_lower       the same against the full aperture
```

At `y0 = 2 sqrt s` the barrier constant `c b + 12` is `O(sqrt c)` for a fixed mode, so a window of
width `1/(c b + 12)` costs a bounded exponential and contributes `Phi(y0)^2/(c b + 12)` — the true
order.  No turning-point model function (Airy, parabolic cylinder, Liouville-Green error control)
is used anywhere in either direction.

## Lean progress — the coordinate half of `(3)`: the tail machinery

The remaining item on this card was the coordinate limit `ell_j(lambda) -> a_j`.  Its two analytic
ingredients are now theorems, in `RHTower/SecondMomentTailBound.lean` (wired, axiom-clean).

The obstruction is that an `L^2` bound alone does **not** control the tail of `int Psi_c`: the tail
of a unit-`L^2` function can carry all its `L^1` mass.  What controls it is the *second moment*,
which the corpus already bounds (`integral_rescaled_secondMoment_le`).  The bound is Cauchy-Schwarz,
but it is obtained here with no Hoelder machinery at all:

```
abs_le_secondMoment_split      |f(xi)| <= (t/2)(1/xi^2) + (1/(2t)) xi^2 f(xi)^2     (t, xi > 0)
integral_Ioi_one_div_sq        int_{xi > K} xi^(-2)  =  1/K
integrableOn_Ioi_one_div_sq
integral_Ioi_abs_le_param      int_{xi > K} |f|  <=  t/(2K) + (1/(2t)) int_{xi > K} xi^2 f^2
integral_Ioi_abs_le_sqrt       int_{xi > K} |f|  <=  sqrt(N/K)      when the moment is <= N
```

The pointwise split is the identity

```
(t/2)(1/xi^2) + (1/(2t)) xi^2 f^2 - |f|  =  (t - xi^2 |f|)^2 / (2 t xi^2) ,
```

and setting `t = sqrt(N K)` balances the two halves, recovering the sharp constant.  So a family
with a uniform second-moment bound `N` has integral tails `<= sqrt(N/K)`, uniformly — as small as
one likes.

The second ingredient is the passage from that to the limit of the integrals:

```
tendsto_integral_of_compact_of_tail
    convergence of  int_{[-K,K]} F_i  for every K,  plus uniformly small tails,
    gives  int F_i -> int f
```

the three-epsilon argument, stated for an arbitrary filter so it applies to the bandwidth family
directly.

With `tendsto_prolateProfile_oscProfile` for the compact half and
`integral_rescaled_secondMoment_le` for the tails, these give `int Psi_c -> int Psi^*` — and with
`Psi^* = phi_n/phi_n(0)` from the rigidity theorem, that is the coordinate limit `(3)`.

## Lean progress — the tail hypothesis, instantiated for the prolate family

`RHTower/ProlateTailIntegralBound.lean` (wired, axiom-clean) discharges, for the actual normalized
prolate profiles, the tail hypothesis that `tendsto_integral_of_compact_of_tail` consumes:

```
intervalIntegral_secondMoment_mono   the window second moment dominates any sub-interval's
normalizedProlate_tail_le           |int_K^{sqrt c} Psi_c|  <=  sqrt(N/K)
normalizedProlate_tail_lt           and it is below any target delta once  K > N/delta^2
```

The input is the corpus's own `normalizedProlate_secondMoment_le`; the mechanism is the
second-moment tail bound.  The bound is uniform in the bandwidth: `N` is any bound for the window
second moment, which `normalizedProlate_total_mass_le` supplies with a constant depending only on
the window and the separation bound.

So all three ingredients of the coordinate half of `(3)` are now theorems:

```
compact half   tendsto_prolateProfile_oscProfile        (corpus)
tail half      normalizedProlate_tail_lt                (new)
transfer       tendsto_integral_of_compact_of_tail      (new)
```

and by evenness of the profile (`even_normalizedProlateProfile`) the negative tail is the same.

## Lean progress — the growing-window transfer, and `(3)`'s coordinate half assembled

`RHTower/SecondMomentTailBound.lean` now carries both halves of the transfer the prolate family
needs, plus the growing-window form its integrals actually have:

```
tendsto_setIntegral_Icc_of_tendsto_of_bounded
    pointwise convergence + a uniform bound  ==>  convergence of the window integrals
    (dominated convergence on a finite-measure window)

tendsto_intervalIntegral_growing_window
    integrals over every fixed window converge to g K,  g K -> A,
    and the tails past any large enough cut are uniformly small
      ==>  int_{-R_i}^{R_i} F_i -> A
```

The second is the shape the prolate integrals have: the window is `[-sqrt c, sqrt c]` and grows with
the bandwidth, so neither a fixed-domain dominated-convergence argument nor a fixed-tail argument
applies directly.  The proof is the four-epsilon split

```
int_{-R}^{R} F_i - A
  = (int_{-K}^{K} F_i - g K) + (g K - A) + int_{-R}^{-K} F_i + int_{K}^{R} F_i ,
```

with `K` chosen past both the tail threshold and the window-value threshold.

The three inputs for the prolate family are now all theorems:

```
pointwise convergence   tendsto_prolateProfile_oscProfile   (corpus)
uniform bound           normalizedProlate_phase_le          (corpus)
uniform tails           normalizedProlate_tail_lt           (this session)
```

so the coordinate half of `(3)`, `ell_j(lambda) -> a_j`, has every ingredient in Lean.  What is left
is to instantiate the transfer at the prolate family with those three, which is substitution rather
than mathematics.

## The normalization step of `(3)` is now a theorem, not bookkeeping

Two modules, both wired and axiom-clean.

```
HTGeometry/ShapeRatioDilation.lean
  intervalIntegral_dilate      int_{-aR}^{aR} b f(x/a)      = a b   int_{-R}^{R} f
  intervalIntegral_dilate_sq   int_{-aR}^{aR} (b f(x/a))^2  = a b^2 int_{-R}^{R} f^2
  shapeRatio_dilate            ( int_{-aR}^{aR} b f(x/a) )^2 / int_{-aR}^{aR} (b f(x/a))^2
                                   =  a . ( int_{-R}^{R} f )^2 / int_{-R}^{R} f^2
  shapeRatio_amplitude_invariant

RHTower/ProlateCoordinateNormalization.lean
  tendsto_sqrt_mul_prolateGround_coordSq
      sqrt c . ( int_{-1}^{1} Phi_c )^2 / int_{-1}^{1} Phi_c^2   ->   2 sqrt(pi)
```

The shape ratio is quadratic over quadratic, so the amplitude cancels exactly, and the dilation
survives once because the numerator is squared *after* integrating.  That is the whole content of
the "rescaling ambiguity" the card flagged: the normalised profile is
`Psi_c(xi) = Phi_c(xi/sqrt c) / Phi_c(0)`, which is `beta f(x/alpha)` with `alpha = sqrt c` and
`beta = 1/Phi_c(0)`, and the matching window `[-sqrt c, sqrt c]` corresponds to `R = 1` — the
eigenfunction's own interval.  So the corpus limit `2 sqrt(pi)` for the normalised profile transfers
verbatim, with the single factor `sqrt c`.

One point that was not bookkeeping: the transfer needs `Phi_c(0) != 0`, and no positivity of the
ground state is available in the corpus family data.  It is not needed.  If `Phi_c(0)` vanished the
normalised profile would be identically zero (Lean's `div_zero`), so its shape ratio would be `0`;
since the ratio tends to `2 sqrt(pi) != 0`, it is eventually nonzero, hence `Phi_c(0) != 0` for all
large `c` — which is all a limit statement needs.  The proof extracts the amplitude bound from the
limit itself.

So `(3)` at `j = 0` is now unconditional *in the card's own normalization*, with the constant
`2 sqrt(pi)` explicit.  What remains on this card is the Fuchs asymptotic with its constant `A_n`.

## The third input of the `(8)` threading is now a theorem too

`RHTower/SecularTailVanishing.lean` (wired, axiom-clean).

```
sum_subset_le_of_sum_le    a bound on a nonnegative sum bounds every subsum
tendsto_tail_div_slack     0 <= T(c) <= C ,  M(c) -> infinity   ==>   T(c)/(M(c)-1) -> 0
```

Only two facts about the family are used: the infinite tail of the coordinate masses is bounded, and
the gap slack grows.  The first is a Bessel inequality — the masses of a normalised vector against an
orthonormal family sum to at most one, so *every* subfamily sum obeys the same bound uniformly in
`c`, which is what `sum_subset_le_of_sum_le` records.

With this the threading table is complete as Lean theorems:

```
(3)  coordinate limits  ell_j -> a_j    =>  S -> A,  L -> B     tendsto_prolateGround_shapeRatio
                                                                 + ProlateCoordinateNormalization
(beta) two-sided leakage ladder         =>  eps -> 0            tendsto_consecutive_leakage_ratio
     bounded tail + growing slack       =>  T/(M-1) -> 0        tendsto_tail_div_slack
     -----------------------------------------------------------------------------
(8)  tendsto_secular_ratio_of_limits    =>  mu_k / d_{k+1} -> A/(A+B)
```

Every implication *and* every input shape is now formal.  What the card still owes is the
instantiation of the two-sided leakage estimates at consecutive modes, and the coordinate limits at
indices `j > 0`; the ground index `j = 0` is closed.

## The normalization transfer, for an arbitrary mode

`RHTower/ProlateShapeRatioTransfer.lean` (wired, axiom-clean).

```
tendsto_sqrt_mul_shapeRatio_of_normalized
    for ANY family Phi and ANY nonzero L,

    shape ratio of the normalised profile over [-sqrt c, sqrt c]  ->  L
      ==>   sqrt c . ( int_{-1}^{1} Phi_c )^2 / int_{-1}^{1} Phi_c^2   ->   L
```

The passage from the rescaled, amplitude-normalised profile to the eigenfunction's own variable uses
nothing about which mode is involved: the shape ratio is quadratic over quadratic, so the amplitude
cancels and the dilation survives once.  The amplitude `Phi_c(0)` cannot vanish for large `c`,
because a vanishing amplitude makes the normalised profile identically zero and its shape ratio `0`,
contradicting `L != 0` — so no positivity input is needed for any mode either.

The ground case proved earlier is the instance `L = 2 sqrt(pi)`.  For an index `j > 0` the *only*
missing input is the profile limit of that mode; the normalization step is already discharged for
all of them at once.

## Lean progress — the rung-`n` trial Rayleigh bound, and why the defect is a square

`RHTower/HermiteRungRayleighDefect.lean` (wired, axiom-clean).

```
hermiteRungDefect n xi        -xi^2 phi_n'' phi_n - 2 xi phi_n' phi_n
integral_hermiteRungDefect    int_{-R}^{R} defect
                                = int_{-R}^{R} xi^2 (phi_n')^2 - [ xi^2 phi_n phi_n' ]_{-R}^{R}
tendsto_sq_mul_hermiteFun_atTop / _atBot      x^2 phi_n(x) -> 0
tendsto_hermiteRungBoundary                   the boundary term vanishes
exists_deriv_hermiteFun_ne_zero, exists_window_deriv_ne_zero, exists_pos_window_integral
eventually_hermiteRungDefect_pos              the defect is eventually positive
hermiteTrial c n x = phi_n(sqrt c . x)
prolate_hermiteTrial_integrand
eventually_prolate_hermiteTrial_rayleigh_gt
      ** for large bandwidth,  -(2n+1) c . int trial^2  <  int (L_c trial) . trial **
```

### The point: no Hermite moments are needed

The corpus already owned the pointwise quasi-eigenfunction identity
(`prolateSLAction_hermiteFun`): the rescaled Hermite function returns the ladder value `-(2n+1)c`
plus the two correction terms `-xi^2(xi^2-2n-1)phi_n` and `-2 xi phi_n'`.  Deciding the *sign* of
their integral looks like it needs the oscillator moments `<xi^2>` and `<xi^4>` — with the ladder
values it comes to `(n^2+n+3/2)/2` times the mass, positive but computed.

It needs neither.  The two correction terms are exactly the two terms produced by differentiating
`xi^2 phi_n`, so a *single* integration by parts against `phi_n'` collapses them to

```text
int xi^2 (phi_n')^2  -  [ xi^2 phi_n phi_n' ] ,
```

a square minus a boundary term.  The square is positive because `phi_n'` cannot vanish identically
(otherwise `phi_n` is constant, hence `0` by decay, contradicting that a Hermite polynomial is
monic), and the boundary term is a polynomial times a Gaussian, so it vanishes.  The sign is
therefore structural, not numerical.

### Where this sits in the excited-mode programme

`tendsto_prolateProfile_hermiteRung` already gives the prolate-to-Hermite convergence at rung `n`
**given** `mu_n(c) -> 2n+1`, and `tendsto_sqrt_mul_shapeRatio_of_normalized` already transports any
profile limit to the card's normalization.  So the coordinate limits `(3)` at `j > 0` are blocked on
exactly one input: a family of modes whose separation constants converge to the `n`-th rung.

The ground case `n = 0` is settled by a two-sided sandwich (`exists_tendsto_bandwidthSeparation_one`):
a Gaussian trial gives `mu < 1` at every bandwidth, and the uncertainty estimate gives every mode
`mu >= 1 - o(1)`.  This section supplies the *upper-bound half* of the same sandwich at rung `n`:
the rung-`n` trial beats the ladder value `-(2n+1)c`.  What is still missing is the selection step —
the variational machine `exists_even_joint_prolate_eigen_gt_of_rayleigh_gt` produces *one* mode above
a Rayleigh threshold, and the excited case needs the counting version: an `(n+1)`-dimensional trial
space above the threshold produces `n+1` independent modes above it.  That is a min-max statement for
the band operator, and mathlib has the spectral theorem only in finite dimensions, so it has to be
built here.

## Lean progress — the min–max counting principle for the band operator

Three modules, all wired and axiom-clean.

```
HTGeometry/SymmetricFormEigenvalueThreshold.lean
  inner_le_of_orthogonal_to_eigenvectors_above
      a vector orthogonal to every eigenvector of a symmetric operator with eigenvalue above
      theta has quadratic form at most theta.|x|^2   (finite dimension)

RHTower/ProlateHighModeOrthogonalRayleigh.lean
  exists_eigenRep_of_prolate_eigenvector
      an eigenvector of the prolate operator on an even band eigenspace is realized by an even
      joint band/prolate eigenfunction
  rayleigh_le_of_orthogonal_to_high_modes
      ** a trial function orthogonal to every even joint mode above -K has prolate Rayleigh
         quotient at most -K **
  exists_high_mode_not_orthogonal          contrapositive: a trial above -K meets a high mode
  exists_high_mode_notMem_of_orthogonal_trial
      the induction step: a trial orthogonal to a subspace W and above -K meets a high mode
      whose band class is outside W

RHTower/ProlateHighModeCounting.lean
  IsHighModeClass c K w                     w is the band class of an even joint mode above -K
  bandClass_finsetSum                       the band class of a finite linear combination
  exists_linearIndependent_highModeClasses
      ** an (n+1)-dimensional space of even trial functions whose Rayleigh quotients all exceed
         -K produces n+1 LINEARLY INDEPENDENT modes above -K **
```

### What was missing and how it is supplied

The corpus's variational machine (`exists_even_joint_prolate_eigen_gt_of_rayleigh_gt`) produces
*one* mode above a Rayleigh threshold: it decomposes the trial vector over the eigenspaces of the
compact band operator and, if *every* mode were below the threshold, bounds each eigenspace's
quadratic form by the threshold.  An excited ladder needs the counting version, and the only step
that changes is the per-eigenspace bound: the component is bounded not because all prolate
eigenvalues there are below the threshold, but because it is orthogonal to the eigenvectors above
it.  That is the finite-dimensional half of the min–max principle — mathlib's spectral theorem
exists only in finite dimension, which is exactly where it is applied, on one eigenspace of a
compact operator.

The induction then costs nothing extra: with `k` modes already produced, the `n+1` trial
coefficients satisfy only `k` orthogonality conditions, so rank–nullity gives a nonzero combination
orthogonal to all of them; its Rayleigh quotient still exceeds the threshold, so it meets a mode
above it, and that mode cannot lie in the span of the previous ones.

### What remains for the rung-`n` separation constant

Two inputs, both now sharply delimited.

1. **The trial space estimate.**  `eventually_prolate_hermiteTrial_rayleigh_gt` (previous section)
   gives the Rayleigh bound for a *single* rung-`n` Hermite trial.  The counting theorem consumes
   the bound for every nonzero *combination* of the rungs `0..n`.  By Hermite orthogonality the
   leading term of a combination is `-sum_i a_i^2 (2i+1) c |phi_i|^2 >= -(2n+1) c |.|^2`, so the
   combination bound holds with the same `K = (2n+1)c + O(1)`; what it needs formally is the
   truncated Hermite orthogonality (`integral_hermiteFun_mul_eq`, already in the tree) together
   with a uniform bound on the cross defects.

2. **The ordering.**  The counting theorem gives `n+1` independent modes above `-K`; turning that
   into "`mu_n <= 2n+1 + o(1)`" requires enumerating the separation constants, and the matching
   lower bound `mu_n >= 2n+1 - o(1)` requires the reverse count — for which the natural route is
   the same machine applied to the oscillator comparison.

## Lean progress — the excited-rung profile limit, and the ordering item was already closed

Two new modules, both wired into `RHTower.lean`, built, axiom-clean.

### The ordering item is not open

The previous section listed as remaining "**the ordering** — turning `n+1` independent modes above
`−K` into `μ_n ≤ 2n+1 + o(1)`, and the matching lower bound".  That is already a theorem in this
tree, and had simply not been recorded on this card:

```
ProlateCanonicalOscillatorLower.tendsto_indexedOscillatorSeparation_atTop (n)
    μ_n(a) → 4n+1               the n-th CANONICAL even mode, by index
ProlateCanonicalOscillatorLower.tendsto_signedModeRadialBandwidth_mul_s_atTop (n)
    the same on the original aperture axis
ProlateIndexedSeparationOrder.signedModeRadialData_s_strictMono
    the canonical index order IS the separation order
```

The first is `(α)` of the corpus audit — *both* halves, exactly, with no `ε` and no hypothesis; the
third is the index identification the audit had proposed to bypass by re-indexing.  So `(α)` needs
nothing further, and the counting theorem of the previous two sections is a second, independent
route to its upper half rather than a prerequisite.

### The excited-rung profile limit

With `(α)` in hand the card's own bottleneck for `(3)` at `j > 0` — "the *only* missing input is
the profile limit of that mode" — is a substitution into the rung window limit, once the window
hypotheses are weakened to `∀ᶠ`, which is all a family parametrized by the aperture can satisfy.

```
RHTower/ProlateIndexedProfileRungLimit.lean
  tendsto_prolateProfile_hermiteRung_eventually
      the rung window limit with EVENTUAL hypotheses — the Grönwall envelope dominates
      the distance wherever the hypotheses hold, and a squeeze needs them only eventually
  tendsto_indexedOscillatorProfile_hermiteRung
      ** φ_{2n}(0) · Ψ_n(a, x)  →  φ_{2n}(x)  on every window [0,K] **
```

The initial phase vector matches exactly: the canonical profile has value `1` and derivative `0` at
the origin, and an even Hermite function has vanishing derivative there
(`deriv_hermiteFun_zero_of_even`), so scaling by `φ_{2n}(0)` is the whole normalization.  The rung
is `2n` because `2·(2n)+1 = 4n+1` is the limit of the `n`-th *even* separation constant.

### The excited-rung total mass

```
RHTower/ProlateIndexedTotalMass.lean
  abs_sq_sub_sq_le                  |u² − v²| ≤ 2B|u − v| for |u|,|v| ≤ B
  eventually_indexedRung_windowDist the window distance bound on the FULL window [−K,K],
                                    the negative half by evenness of both functions
  tendsto_indexedRung_windowMass    ∫_{−K}^{K}(φ_{2n}(0)Ψ_n)² → ∫_{−K}^{K}φ_{2n}²
  tendsto_indexedRung_totalMass
      ** φ_{2n}(0)² · ∫_{−√c}^{√c} Ψ_n²  →  ∫_ℝ φ_{2n}² **
```

The window–total squeeze is the corpus's `tendsto_total_of_window`; its two tail inputs are
`window_le_total` and `window_tail_le_of_secondMoment` fed by the aperture virial in its indexed
form `indexedOscillatorSecondMoment_le : SM ≤ μ_n · TM`, with `μ_n ≤ 4n+2` eventually.  The window
convergence is *quantitative*, not dominated: a difference of squares is the Grönwall distance times
twice a uniform amplitude, and `norm_integral_le_of_norm_le_const` turns that into the integral
bound.  This avoids needing the aperture filter to be countably generated, which it is not known to
be here.

This is the excited-rung counterpart of `tendsto_prolateGround_centreMass` and
`tendsto_prolateGround_profileIntegral`, which the card had only for `j = 0`.  Since
`ProlateShapeRatioTransfer.tendsto_sqrt_mul_shapeRatio_of_normalized` already discharges the
normalization step "for ANY family and ANY nonzero `L`", the remaining work on `(3)` at `j > 0` is
the identification of the canonical indexed family with the card's `e_j`, i.e. the bookkeeping
between `signedModeRadialData` and `evenProlateConstraintCoord` — not a new limit.

## Lean progress — the shape ratio at every rung, and the nonvanishing it needs

Two more modules, wired, built, axiom-clean.  With these the card's own criterion for `(3)` at
`j > 0` — "the *only* missing input is the profile limit of that mode" — is met.

```
RHTower/ProlateIndexedProfileIntegral.lean
  integrable_hermiteFun, integral_hermiteFun_sq_pos_line, tendsto_intervalIntegral_hermiteFun
        (moved to RHTower/HermiteLineIntegral.lean)
  indexedRungAmplitude_ne_zero      φ_{2n}(0) ≠ 0, forced by the total-mass limit itself
  tendsto_indexedRung_windowIntegral
  tendsto_indexedRung_profileIntegral
        ** φ_{2n}(0) · ∫_{−√c}^{√c} Ψ_n  →  ∫_ℝ φ_{2n} **
  tendsto_indexedRung_shapeRatio
        ** (∫_{−√c}^{√c}Ψ_n)² / ∫_{−√c}^{√c}Ψ_n²  →  (∫_ℝφ_{2n})² / ∫_ℝφ_{2n}² **
```

The amplitude cancels in the shape ratio, so the limit is amplitude-free — which is what
`ProlateShapeRatioTransfer.tendsto_sqrt_mul_shapeRatio_of_normalized` consumes.  The amplitude is
nonzero for a reason that needs no Hermite evaluation: if `φ_{2n}(0)` vanished, the total-mass limit
of the previous section would read `0 = ∫_ℝφ_{2n}²`, and the right side is positive.

The growing-window transfer is the corpus's `tendsto_intervalIntegral_growing_window'`; its four
inputs at the indexed family are interval integrability (continuity), window convergence (the
Grönwall envelope again), exhaustion of the Hermite mass by symmetric windows, and uniform tails
from the second-moment bound `SM ≤ μ_n · TM` with `TM` bounded by the total-mass limit.

### The nonvanishing of the Hermite first moment

`tendsto_sqrt_mul_shapeRatio_of_normalized` requires `L ≠ 0`, i.e. `∫_ℝ φ_{2n} ≠ 0`.  That is now a
theorem, with no special-function evaluation:

```
RHTower/HermiteLineIntegral.lean            (wired, axiom-clean)
  hermiteFun_add_two          φ_{n+2} = √2·x·φ_{n+1} − (n+1)·φ_n
  deriv_hermiteFun_succ       φ_{n+1}′ = √2(n+1)·φ_n − x·φ_{n+1}
  integrable_id_mul_hermiteFun, integrable_deriv_hermiteFun_succ
  integral_deriv_hermiteFun_succ      ∫_ℝ φ_{n+1}′ = 0
  integral_id_mul_hermiteFun_succ     ∫_ℝ x·φ_{n+1} = √2(n+1)·∫_ℝ φ_n
  integral_hermiteFun_add_two   ** ∫_ℝ φ_{n+2} = (n+1)·∫_ℝ φ_n **
  integral_hermiteFun_two_mul_pos / _ne_zero
      ** every even Hermite first moment is positive **
```

The two pointwise identities are the polynomial three-term recursion (`Polynomial.hermite_succ`
together with the corpus's Appell law `derivative_hermite_succ`) read through the Gaussian factor,
which is common to all three terms.  The only analysis is that a Hermite function and its derivative
are polynomials times a Gaussian, hence integrable, and that the derivative therefore integrates to
zero — the boundary term `φ(R) − φ(−R)` vanishes.  Substituting the second identity into the first
gives the two-step recursion, and `φ_0` is a Gaussian, so induction gives positivity at every even
rung.  No value of any integral is computed.

### What is left on `(3)`

Only re-indexing.  `tendsto_sqrt_mul_shapeRatio_of_normalized` is stated along `atTop` in the
*bandwidth*; the canonical indexed family is parametrized by the *aperture*, and
`indexedOscillatorBandwidth a = 2πa²` is the change of variable between them.  Composing the two —
or restating the transfer along an arbitrary filter — turns `tendsto_indexedRung_shapeRatio` into
the card's normalized `(3)` at every even rung, with limit `(∫φ_{2n})²/∫φ_{2n}²`, now known to be
nonzero.

## `(3)` IS CLOSED AT EVERY EVEN RUNG

`RHTower/ProlateIndexedCoordinateLimit.lean` (wired, built, axioms
`[propext, Classical.choice, Quot.sound]`).

```
tendsto_sqrt_mul_shapeRatio_of_normalized'
    the normalization transfer along an ARBITRARY filter and index type, the bandwidth given by
    any eventually positive function of the index
hermiteShapeRatio_ne_zero (n)
    (∫_ℝ φ_{2n})² / ∫_ℝ φ_{2n}²  ≠  0
tendsto_indexedRung_coordinateLimit (n)
    ** √c · ( ∫_{−1}^{1} R_n )² / ∫_{−1}^{1} R_n²  →  (∫_ℝφ_{2n})² / ∫_ℝφ_{2n}²  **
```

`R_n` is the canonical endpoint-normalized radial datum of the `n`-th signed (greedy) even prolate
mode, `c = 2πa²` its bandwidth, and the limit is nonzero.  This is the card's `(3)` in the card's own
normalization, at **every** even rung — the ground case `n = 0` was
`ProlateCoordinateNormalization.tendsto_sqrt_mul_prolateGround_coordSq`, and the excited cases were
the card's stated remaining analytic input.

The only generalization needed of the corpus's transfer was the filter: its proof is a pointwise
dilation identity (`HTGeometry.shapeRatio_dilate`) followed by a filter congruence, and nothing in it
refers to `atTop` on the bandwidth axis.  The canonical family is parametrized by the aperture, so
the primed version applies verbatim with `c = indexedOscillatorBandwidth`.

### Status of the three constrained-prolate cards after this

```
(α)  differential ordering  μ_n → 4n+1          tendsto_indexedOscillatorSeparation_atTop
     index order = separation order             signedModeRadialData_s_strictMono
(3)  coordinate limits at every even rung       tendsto_indexedRung_coordinateLimit
(β)  two-sided leakage ladder                   tendsto_consecutive_leakage_ratio
                                                 + prolate_leakage_two_sided
(4),(5),(10),(10a),(11)                          HermiteCentreValueClosedForm,
                                                 HermiteContrastLadder
(8)  interlacing + location + threading          SecularEquationInterlacing,
                                                 SecularTailVanishing,
                                                 tendsto_secular_ratio_of_limits
counting principle for excited modes            exists_linearIndependent_highModeClasses
                                                 + eventually_hermiteTrial_combination_rayleigh_gt
```

What remains is the identification bookkeeping between the two indexings of the same modes: the
analytic layer produces `signedModeRadialData a n`, the constrained tower consumes
`evenProlateConstraintCoord a n = ∫_{−a}^{a} (evenProlateSignedMode a n)`, and both are built from
the same greedy index `n`.  Converting `tendsto_indexedRung_coordinateLimit` into
`hl : ‖evenProlateConstraintCoord lam j‖ → constrainedProlateHermiteCoordinate j` is the remaining
step, together with the evaluation of the Hermite shape ratio
`(∫φ_{2n})²/∫φ_{2n}²` against the card's `constrainedProlateHermiteCoordinate` — for which
`integral_hermiteFun_add_two` supplies the recursion on the numerator and the corpus's
`HermiteCentreValueClosedForm` the closed form on the other side.

## Lean progress — the Hermite moments in closed form, and the limit in the card's own constant

Two more modules, wired, built, axiom-clean.

```
RHTower/HermiteMomentClosedForm.lean
  hermiteFun_one_eq, deriv_hermiteFun_zero
  hermiteFun_succ_uniform      φ_{m+1} = √2·x·φ_m − m·φ_{m−1}, bottom rung included
  deriv_hermiteFun_add_id_mul  φ_m′ + x·φ_m = √2·m·φ_{m−1}, bottom rung included
  integrable_hermiteFun_mul, integrable_id_mul_hermiteFun_mul
  integral_hermiteFun_mul_eq_zero_of_ne   whole-line orthogonality
  integral_deriv_hermiteFun_mul_succ      ∫_ℝ (φ_mφ_{m+1})′ = 0
  integral_id_mul_hermiteFun_mul_succ     ∫_ℝ x φ_m φ_{m+1} = (√2/2)(m+1)∫φ_m²
  integral_hermiteFun_sq_succ    ** ∫_ℝ φ_{m+1}² = (m+1)·∫_ℝ φ_m² **
  integral_hermiteFun_zero_val   ∫_ℝ φ_0 = √(2π)
  integral_hermiteFun_zero_sq    ∫_ℝ φ_0² = √π
  hermiteShapeRatio n := (∫φ_n)²/∫φ_n²
  hermiteShapeRatio_two_mul      ** = 2√π · binom(2k,k)/4^k  at rung 2k **
  hermiteShapeRatio_four_mul     ** = 2√π · binom(4j,2j)/16^j  at rung 4j **
  hermiteShapeRatio_four_mul_eq_coordinate_sq
      ** = √(2π) · (constrainedProlateHermiteCoordinate j)²  **

RHTower/ProlateIndexedConstrainedCoordinate.lean
  tendsto_indexedRung_constrainedCoordinate
      ** √c · ( ∫_{−1}^{1} R_{2j} )² / ∫_{−1}^{1} R_{2j}²  →  √(2π) · a_j²  **
```

The two uniform pointwise identities are what makes the bottom rung need no case split: writing the
shifted term with the coefficient `m` (so it dies at `m = 0`) covers `φ_1 = √2xφ_0` and
`φ_0′ = −xφ_0` with the same statement.  Pairing them against `φ_{m+1}` and using that the
derivative of a product of Hermite functions integrates to zero evaluates the cross moment, and
substituting into the three-term recursion gives the `L²` recursion; the same technique gave the
first-moment recursion in the previous section.  The two Gaussian values then fix both sequences,
and the ratio follows the central-binomial recursion `(k+1)C_{k+1} = 2(2k+1)C_k` — the *same*
recursion the corpus's `hermiteOriginValue_sq_two_mul` runs, which is why the analytic limit and the
card's combinatorial weight agree on the nose, with the single constant `√(2π)` between them.

So the card's `(3)` now holds at every Fourier-even rung **in the card's own normalization**, with
the card's own coefficient `a_j = constrainedProlateHermiteCoordinate j`.

### The one remaining link, stated exactly

`hl : ‖evenProlateConstraintCoord lam j‖ → constrainedProlateHermiteCoordinate j` needs the
identification of the two descriptions of the same mode:

```text
evenProlateConstraintCoord a n  =  ∫_{−a}^{a} evenProlateSignedPointwiseSource a n
                                                   (ae_eq_evenProlateSignedPointwiseSource)
signedModeRadialData a n .Phi   =  an even band eigenfunction of bandTransform (2πa²)
                                    with the SAME eigenvalue evenProlateSignedValue a n ^ 2
```

Both are even eigenfunctions of the same unit-scale band transform at the same eigenvalue, so
`ProlateBandEigenvalueSimplicity` / `evenProlateSignedMode_proportional_of_sq_eq` makes them
proportional, and the shape ratio is scale-invariant
(`HTGeometry.shapeRatio_amplitude_invariant`).  With `‖u_n‖_{L²[−a,a]} = 1`
(`integral_norm_sq_evenProlateSignedPointwiseSource_eq_one`) the constraint coordinate squared *is*
the shape ratio of the aperture-scaled mode, and the aperture rescaling is
`HTGeometry.shapeRatio_dilate` once more.  This link is missing at `j = 0` as well — the corpus's
ground coordinate limit is stated for the variationally selected ground family, not for
`evenProlateSignedMode` — so closing it closes every index at once.

## `hl` IS CLOSED — the constrained coordinate converges to its Hermite value

`RHTower/ProlateConstraintCoordinateLimit.lean` (wired, built, axioms
`[propext, Classical.choice, Quot.sound]`).

```
exists_unitExtension_eq_const_mul_radialPhi
    ONE complex constant relates the two descriptions of a signed prolate mode
evenProlateSignedPointwiseSource_eq_const_mul_radialPhi
    S(a·x) = z · Phi(x) on the open aperture
integral_evenProlateSignedPointwiseSource_eq          ∫_{−a}^{a} S = z·a·∫_{−1}^{1}Phi
integral_norm_sq_evenProlateSignedPointwiseSource_aperture
                                                       |z|²·a·∫_{−1}^{1}Phi² = 1
norm_sq_evenProlateConstraintCoord_eq
    ** ‖ℓ_n(a)‖² = a · (∫_{−1}^{1}Phi)² / ∫_{−1}^{1}Phi² **
shapeRatio_radialR_eq_radialPhi        endpoint normalization does not move the shape ratio
tendsto_norm_sq_evenProlateConstraintCoord
tendsto_norm_evenProlateConstraintCoord
tendsto_norm_evenProlateConstraintCoord_atTop
    ** ‖evenProlateConstraintCoord lam (2j)‖ → constrainedProlateHermiteCoordinate j **
```

This is the `hl` that
`ConstrainedProlateBesselClockUniversalityLaw.ClockEnvelope.constrainedProlateBessel_exactEigenpair_and_allRawDefects`
consumes, for the Fourier-even renumbering `j ↦ 2j`; the Bessel input already tolerates an arbitrary
injective renumbering (`tsum_evenProlateConstraintCoord_comp_sq_le`), which is exactly what the
corpus audit proposed in place of the total-positivity comparison of the two orderings.

### How the two descriptions were matched

The analytic layer carries a signed mode as its canonical radial datum `Phi` — an even smooth
**real** band eigenfunction at the squared signed value — while the constrained tower carries it as
its pointwise source `S`, a **complex** function whose aperture integral is the constraint
coordinate.  Nothing in the corpus related them, and the two are not equal.

What relates them is that *both channels* of the unit-band extension of `S` are real band
eigenfunctions at that same eigenvalue
(`bandTransform_evenProlateSignedUnitExtension_re_global` / `_im_global`), so
`continuous_real_bandEigen_proportional` makes each a real multiple of `Phi`; recombining them
through `Complex.re_add_im` gives a single complex constant `z` with `S(a·x) = z·Phi(x)` on the open
aperture.  The `L²` normalization of the mode then fixes `|z|²`, the constant cancels in the
quotient, and the constraint coordinate squared is exactly the aperture-scaled shape ratio of `Phi`
— the quantity whose limit the previous sections compute.  No positivity, no simplicity of the
eigenvalue, and no ordering comparison is used: only that a live band eigenvalue has a
one-dimensional continuous real eigenline, which the corpus already proves.

### Status

The analytic gate of the constrained-prolate lane is closed:

```text
(α)  μ_n → 4n+1, index order = separation order        corpus
(3)  coordinate limits, every even rung                 tendsto_indexedRung_coordinateLimit
     in the card's normalization                        tendsto_indexedRung_constrainedCoordinate
hl   ‖ℓ_{2j}(lam)‖ → a_j                                tendsto_norm_evenProlateConstraintCoord_atTop
(4),(5),(10),(10a),(11)                                 corpus
(8)  interlacing, location, threading                   corpus
(β)  two-sided leakage ladder                           corpus
Bessel Σℓ² ≤ 2a, any injective renumbering              corpus
```

## The clock law now has NO coordinate hypothesis

`RHTower/ProlateConstrainedClockCapstone.lean` (wired, built, axiom-clean).

```
ClockEnvelope.constrainedProlateEven_exactEigenpair_and_allRawDefects
    ** every clock envelope gives, for the Fourier-even constraint coordinates
       ℓ lam j = ‖evenProlateConstraintCoord lam (2j)‖, an eventual exact eigenpair at each
       depth and the collapse of all preceding normalized raw defects — with no hypothesis
       about the coordinates at all **
```

The renumbering `j ↦ 2j` costs nothing: squared summability passes to a subfamily
(`Summable.comp_injective`) and the aperture Bessel bound was already proved for an arbitrary
injective renumbering (`tsum_evenProlateConstraintCoord_comp_sq_le`).  The previous section's `hl`
supplies the coordinate limits.

### What the ladder card still owes: one `FuchsEnvelope` instance

The only hypothesis left in that capstone is `ClockEnvelope D e E`, which by
`FuchsEnvelope.toClockEnvelope` is a `FuchsEnvelope D e` for the actual leakage family
`D lam j = 1 − σ_{2j}(lam)²` with `e j = 4j` — i.e. `(β)` in envelope form:

```text
step   e (j+1) = e j + 4                                        immediate for e j = 4j
nonneg, mono                                                    from the signed values
lower  ∃ c > 0, eventually  c·lam^{8j+1}·e^{−4πλ²} ≤ D lam j
upper  ∃ C > 0, eventually  D lam j ≤ C·lam^{8j+1}·e^{−4πλ²}
```

`prolate_leakage_two_sided` is exactly the two-sided estimate that produces `lower` and `upper`, but
it is stated for a mode presented by explicit data and carries side conditions — `8 ≤ c`,
`s ≤ 1/8`, `4 ≤ c·s`, a collar `α` with `600(1−α) ≤ 1/4`, positivity of `Φ` on `[2√s, 1]`, the flux
ODE, and integrability of `R²` past the endpoint.  Instantiating it at the canonical indexed family
means checking each of those for `signedModeRadialData lam (2j)` at all large `lam`, using
`indexedOscillatorSeparation` for `s` (so `c·s → 8j+1`).  Note the side condition `4 ≤ c·s` is
satisfied for every `j ≥ 1` but **not** for the ground index, where `c·s → 1`: the ground leakage
needs the separate ground estimate.  That instantiation is the remaining item of `(β)`, and with it
the ladder card's `(8)` becomes unconditional.

## `(β)` INSTANTIATED — the two-sided leakage estimate holds at the canonical indexed family

`RHTower/ProlateIndexedLeakageTwoSided.lean` (wired, built, axioms
`[propext, Classical.choice, Quot.sound]`).

```
prolateLeakageCollar := 1 − 1/2400        600·(1 − α) = 1/4 exactly
integral_Ioi_sq_signedModeRadialData
    the HALF-line exterior mass: ∫_{Ioi 1} R² = (∫_{−1}^{1}R²)·(leakage/2)/σ²
prolateLeakageLower / prolateLeakageUpper  the two explicit bounds at the fixed collar and cut b = 1/2
eventually_signedLeakage_two_sided (n) (hn : 1 ≤ n)
    ** ∀ᶠ a in atTop,
         prolateLeakageLower c s ≤ (1 − σ_n(a)²)/2 ≤ prolateLeakageUpper c s **
```

This is the item the card recorded as "what the card still owes … the instantiation of the two-sided
leakage estimates at consecutive modes".  Every hypothesis of `prolate_leakage_two_sided` is
discharged at the canonical radial datum of the `n`-th signed even mode:

```text
smoothness, evenness, R 1 = 1                      SignedModeRadialData.IsExact
prolateSLAction R = −(s c²)R                       IsExact + s = −chi/c²
positivity on [2√s, 1]                             prolate_pos_on_right_of_radial_turning
                                                    (it gives [√s,1], and 2√s ≥ √s)
the flux form of the ODE                           IsExact's ODE, one linear combination
IntegrableOn R² (Ioi 1)                            integrable_sq_signedModeRadialData
the mass identity                                  integral_outside_sq_..._leakage_ratio, halved
1/2 ≤ σ² ≤ 1, leakage ≥ 0                          evenProlateSignedValue_sq_tendsto_one,
                                                    one_sub_evenProlateSignedValue_sq_nonneg
```

and every numerical side condition is eventual because `c = 2πa² → ∞` while `c·s → 4n+1`:

```text
8 ≤ c,  1728K/floor ≤ c,  64(4n+2) ≤ c             c → ∞
0 < s,  s ≤ 1/64 ≤ 1/8,  2√s ≤ 1/4 ≤ α            c·s bounded, c → ∞
4 ≤ c·s                                            c·s → 4n+1 > 4    ← needs n ≥ 1
1/2 < α < 1, 600(1−α) ≤ 1/4                        the fixed collar
c²(1 − 2t²) ≤ −s c² on [α,1]                       2α² − 1 ≥ 1/64 ≥ s
1 ≤ c·bandEndpointPhase s α                        sqrt_mul_arccos_le_bandEndpointPhase gives the
                                                    aperture-free positive lower bound
                                                    κ = √(α²−1/64)·arccos α, and c ≥ 1/κ
2√s < b = 1/2 < 1                                  2√s ≤ 1/4
```

The one index the estimate cannot reach is the ground index, exactly as the previous section
recorded: there `c·s → 1 < 4`.

### What remains for `(8)`

`tendsto_consecutive_leakage_ratio` consumes the two bounds in the shape
`0 ≤ f(c) ≤ A c^a E(c)` and `B c^b E(c) ≤ g(c)` with `a < b` and `E(c) = e^{−2c}`.  So the remaining
step is the *asymptotic reading* of `prolateLeakageUpper` at index `k` and `prolateLeakageLower` at
index `k+1`: expanding `c·bandEndpointPhase s (2√s)` and `2c(1 + (s/4)log s)` as `c → ∞` with
`c·s → 4n+1` turns both into `c^{±(4n+1)/2}·e^{−2c}` up to bounded factors, and the exponents then
separate by `4`.  That expansion, plus the ground-index upper bound, is what `(8)` still owes.

## Lean progress — the sharp turning-scale asymptotic of the band phase

`RHTower/BandEndpointPhaseTurning.lean` (wired, built, axioms
`[propext, Classical.choice, Quot.sound]`).

The remaining analytic step of `(8)` is reading the exponentials of the two leakage bounds.  The
lower bound needs nothing: its exponent is *exactly* `2c(1 + (s/4)log s) = 2c − (cs/2)log(1/s)`.  The
upper bound's exponent is `−2c·Ξ_s(2√s)`, so what is needed is the size of `1 − Ξ_s(2√s)`.  That is
now a theorem:

```
invSinAntideriv θ = ½(log(1+cos θ) − log(1−cos θ))     an antiderivative of −1/sin on (0,π)
integral_inv_sin     ∫_{θ₀}^{π/2} dθ/sin θ = invSinAntideriv θ₀
integral_inv_sin_le  ∫_{θ₀}^{π/2} dθ/sin θ ≤ log 2 − log(sin θ₀)
sin_sub_sqrt_le      u − √(u²−s) ≤ s/(2√(1−K⁻²)·u)          whenever u ≥ K√s
one_sub_bandEndpointPhase_turning_le
    ** 1 − Ξ_s(2√s) ≤ 4s + K²s + (s/(2√(1−K⁻²)))·(log 2 − log(K√s)) **     (K ≥ 2, K√s ≤ 1/2)
```

The elementary integral `∫dθ/sin θ` is not in mathlib; its antiderivative is verified directly, and
the endpoint value `log 2 − log sin θ₀` comes from `(1+cos)/(1−cos) = (1+cos)²/sin² ≤ 4/sin²`.

The decomposition is the card's own: writing `1 = ∫_0^{π/2} sin θ dθ`,

```text
1 − Ξ_s(2√s) = ∫_0^{arcsin 2√s} sin θ dθ  +  ∫_{arcsin 2√s}^{π/2}(sin θ − √(sin²θ − s)) dθ ,
```

the head is `1 − √(1−4s) ≤ 4s`; the tail splits at the height `K√s`, below which the defect is at
most `sin θ` (contributing `≤ K²s`) and above which `sin_sub_sqrt_le` applies.

### Why the free parameter `K` matters

With `s ≈ μ/c` and `μ = c·s → 4n+1`, the estimate reads

```text
2c(1 − Ξ_s(2√s))  ≤  (1/(2√(1−K⁻²)))·(cs)·log(1/s) + O(1)
                   =  (1 + O(K⁻²))·(cs/2)·log c + O(1) ,
```

so the upper bound's polynomial exponent is `(1+ε_K)·μ/2 + O(1)` while the lower bound's is exactly
`μ/2 − 1`.  Consecutive indices give `μ_{k+1} − μ_k = 4`, and the two `O(1)` losses cost `3/2`
together, so the ratio's exponent is `−1/2 + ε_K·μ_k`: choosing `K` large enough for the fixed index
`k` makes it negative, which is precisely what `tendsto_consecutive_leakage_ratio` consumes.  A crude
bound with the coefficient `1/√3` or Jordan's inequality would *not* suffice — it fails from `k = 2`
on — which is why the split at `K√s` is the right shape.

## Lean progress — both leakage bounds reduced to `power × action`

`RHTower/ProlateLeakageRatioBounds.lean` (wired, built, axioms
`[propext, Classical.choice, Quot.sound]`).

The explicit two-sided estimate is heavy; for the ladder only its shape matters, and both sides are
now reduced to it:

```
prolateLeakageUpper_le   (c ≥ 8, 0 < s ≤ 1/64)
    ** prolateLeakageUpper c s ≤ leakageUpperConst · c · exp(−2c·Ξ_s(2√s)) **
barrierFactor_le
    the barrier factor of the lower bound is at most 4 + 5/(1−α)
prolateLeakageLower_ge   (c ≥ 8, 0 < s ≤ 1/64)
    ** leakageLowerConst · (s/c) · exp(−(2c(1 + (s/4)·log s) + 10c s)) ≤ prolateLeakageLower c s **
```

Everything dropped is bounded by an explicit constant:

```text
the collar phase           bandEndpointPhase s α ≤ 2√(1−α)          (the sharp endpoint bound)
the transport loss         2((c·b+12)(b−2√s)/(1−b²)) ≤ 5            because b − 2√s = 1/c,
                                                                    so c·b·(1/c) = 2√s + 1/c
the collar logarithms      exp(−12(log(1−α) − log(1−2√s))) ≤ (1−α)^{−12}
the barrier factor         (1−α²)(barrier + 6/(1−α))²/(c²(α²−s)) ≤ 4 + 5/(1−α)
                                                                    since barrier = c·√(1−s)·α/√(1−α²)
the mass logarithms        exp(log((α²−s)/(3s)) + log((1−4s)/(1−α²))) ≤ 1/(3s(1−α²))
```

Choosing the cut one *inverse bandwidth* above the turning scale is what makes the transport loss
bounded while costing only one power of `c`: with `b − 2√s = c^{−1/2}` the loss would be `e^{Θ(√c)}`,
which no power of `c` can absorb, and with `b` fixed it would be `e^{Θ(c)}`.  The instantiation of
the previous section was updated accordingly (`prolateLeakageCut c s = 2√s + 1/c`).

### What is left of `(8)`

Only the reading of the two actions as powers of the bandwidth, which is now pure algebra:

```text
lower:  2c(1 + (s/4)·log s) = 2c − (c s/2)·log(1/s)                          exact identity
upper:  2c·Ξ_s(2√s) ≥ 2c − (1 + O(K⁻²))·(c s/2)·log(1/s) − O(1)              previous section
```

so with `c·s → 4n+1` the upper bound is `O(c^{(1+ε)(4n+1)/2 + 1})·e^{−2c}` and the lower bound is
`Ω(c^{(4n+1)/2 − 1})·e^{−2c}`.  For consecutive *Fourier-even* indices the corpus index jumps by two,
so `μ` jumps by `8` and the exponents separate with room to spare; the ground index still needs its
own upper bound, since `4 ≤ c·s` fails there.
