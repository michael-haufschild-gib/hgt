# Suzuki negative-shift defect escape

- **ID:** `suzuki-negative-shift-defect-escape`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / SUZUKI SCREW ROUTE / SHIFT-SELECTION NO-GO
- **Scientific status:** `[PAPER-PROVED] [CANDIDATE NEW SOURCE-SPECIFIC NO-GO]`
  `[GENERIC INPUTS KNOWN] [PRIORITY UNVERIFIED] [NOT AN RH PROOF] [NO NUMERICAL EVIDENCE]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), Theorem 1.5 and the discussion after Corollary 1.6.
- **Statement:** For every cofinal aperture sequence, admissible shifts can be chosen sufficiently
  negative that Suzuki's canonically anchored Livsic quotients converge locally uniformly to zero
  on the upper half-plane.  Therefore noncollapse and shift independence cannot hold uniformly
  over all shifts below the restricted Weil floor.

## Exact source family

For fixed `a>0`, let `A_a` be Suzuki's lower-bounded self-adjoint restricted Weil operator and let
`lambda_a=inf spec(A_a)`.  For `lambda<lambda_a`, put

```text
T_(a,lambda)=A_a-lambda I,
v_(a,lambda,+)=T_(a,lambda)^(-1) exp(x),
v_(a,lambda,-)=T_(a,lambda)^(-1) exp(-x).
```

Parity gives `v_- (x)=v_+(-x)`.  With

```text
F_(a,lambda)(z)=integral_(-a)^a v_(a,lambda,+)(x) exp(izx) dx,
```

the finite-aperture Livsic carrier already isolated in the project is

```text
Theta_(a,lambda)(z)
 =((z-i)F_(a,lambda)(z))/((z+i)F_(a,lambda)(-z)).        (1)
```

Suzuki's all-angle reality theorem makes `(1)` Schur on the upper half-plane and anchors it by
`Theta_(a,lambda)(i)=0`.

## Negative-shift escape theorem `[PAPER-PROVED]`

Let `a_n -> infinity`.  Then there exist `lambda_n<lambda_(a_n)` such that

```text
Theta_(a_n,lambda_n) -> 0                                (2)
```

locally uniformly on the upper half-plane.

The proof has three dependency-closed steps.

1. For fixed `a`, write `lambda=-r`.  The standard lower-bounded self-adjoint resolvent law gives

   ```text
   r(A_a+rI)^(-1)f -> f in L2(-a,a),       r->infinity. (3)
   ```

   Applied to `exp(+x)` and `exp(-x)`, Fourier Cauchy--Schwarz upgrades `(3)` locally uniformly in
   `z`.  The common factor `r` cancels from `(1)`.

2. The limiting free-interval carrier is exactly

   ```text
   Theta_a^free(z)
    =(exp(-2a)-exp(2iaz))/(1-exp(-2a)exp(2iaz)).          (4)
   ```

   On every compact `K` in the upper half-plane, if
   `delta=min_(z in K) Im z>0`, then

   ```text
   sup_K |exp(2iaz)| <= exp(-2a delta),
   sup_K |Theta_a^free|
    <= (exp(-2a)+exp(-2a delta))
       /(1-exp(-2a)exp(-2a delta)) -> 0.                 (5)
   ```

3. Choose an exhaustion `K_1 subset K_2 subset ...` of the upper half-plane.  For each `n`, use
   `(3)` at aperture `a_n` to choose `lambda_n` so negative that

   ```text
   sup_(K_n)|Theta_(a_n,lambda_n)-Theta_(a_n)^free|<1/n.
   ```

   Equations `(5)` and the exhaustion prove `(2)`.

## Defect-angle survivor

The first anchored jet has an exact source meaning.  Define

```text
kappa_(a,lambda)=2i Theta'_(a,lambda)(i).                 (6)
```

Direct differentiation of `(1)` gives

```text
kappa_(a,lambda)
 =F_(a,lambda)(i)/F_(a,lambda)(-i)
 =<v_-,v_+>_T/||v_+||_T^2.                              (7)
```

Writing `v_e=(v_++v_-)/2` and `v_o=(v_+-v_-)/2`, parity makes these the even and odd defect
components and gives

```text
kappa_(a,lambda)
 =(||v_e||_T^2-||v_o||_T^2)
  /(||v_e||_T^2+||v_o||_T^2),       |kappa|<1.           (8)
```

Thus the first obstruction to collapse is a normalized even--odd defect-energy imbalance, not the
restricted Weil floor itself.

`(8)` is formal in `formal/GaloisForLFunctions/HTGeometry/PositiveOperatorInner.lean`:
`inner_eq_evenPart_sq_sub_oddPart_sq` (the pairing is the energy *difference*),
`norm_sq_eq_evenPart_sq_add_oddPart_sq` (equal norms — the parity input — make the *sum* the common
energy), and `inner_div_norm_sq_eq_imbalance` for the quotient.

**Correction to the displayed bound.**  `|kappa|<1` needs *both* defect components nonzero, not only
the odd one: `abs_imbalance_lt_one` carries both hypotheses, and
`imbalance_eq_one_of_oddPart_eq_zero` / `imbalance_eq_neg_one_of_evenPart_eq_zero` show the bound is
attained at each degenerate end.  So the strict inequality is exactly the statement that both
components survive, which is what makes it a noncollapse certificate.  For the free carrier,

```text
kappa_a^free=2a/sinh(2a) -> 0.                           (9)
```

`(9)` is formal in `formal/GaloisForLFunctions/HTGeometry/HyperbolicModulus.lean`:
`freeDefectAngle_eq` computes the free quotient as `2a/sinh(2a)` from the two free integrals — the
pairing is the aperture length and the energy is a hyperbolic sine — and
`tendsto_freeDefectAngle_atTop` gives the collapse, via `exp_div_four_le_sinh` (the hyperbolic sine
dominates a quarter of the exponential beyond one).  Both integrals were already proved for
`suzuki-donoghue-defect-spectral-measure-law`; `(9)` needed only their quotient.

A nonzero lower bound for `|kappa|` is generically only a sufficient source-side noncollapse
certificate: an arbitrary nonzero Schur limit may have a higher-order zero at `i`. For the exact
normalized Xi Livsic target, however, this generic loophole is now closed unconditionally:

```text
77/85 < kappa_Xi=2i Theta_Xi'(i) < 1.
```

Thus first-order survival is **necessary** for Xi identification, and the corresponding source
parity shares must satisfy

```text
p_even>81/85,       0<p_odd<4/85.
```

Locally uniform convergence of Suzuki's disk-conjugated finite carriers forces their exact
source defect angles to tend to `kappa_Xi`. Higher-order-only escape remains possible for generic
Livsic targets but cannot be Suzuki's Xi endpoint. The exact theorem and source connector are in
`suzuki-xi-first-defect-jet-gap.md`, `SuzukiXiFirstDefectJet.lean`, and
`SuzukiXiFirstDefectJetSource.lean`.

## Positive survivor: projective defect compactification

The negative-shift theorem exposes a positive carrier rather than only a failed quantifier.
Multiplying a positive source operator `T` by any scalar `c>0` sends its normalized deficiency
vectors to `v_+/c,v_-/c`.  Both Fourier terms in `(1)` acquire the same factor `1/c`, so

```text
Theta_(cT)=Theta_T.                                      (10)
```

Thus the finite-aperture carrier lives on the **projective positive resolvent ray** of `T`, not on
its absolute scale.  The normalized two-defect Gram state is

```text
G_def(T)
 =1/(2N) [[N,C],[C,N]],
N=||v_+||_T^2=||v_-||_T^2,
C=<v_-,v_+>_T.                                          (11)
```

It is invariant under `(10)`.  Its parity eigenvectors are `(1,1)` and `(1,-1)`, with eigenvalues

```text
p_even=(1+kappa)/2=||v_e||_T^2/(||v_e||_T^2+||v_o||_T^2),
p_odd =(1-kappa)/2=||v_o||_T^2/(||v_e||_T^2+||v_o||_T^2). (12)
```

Hence `kappa` is not an arbitrary derivative: it is the signed polarization of a canonical
two-state defect density matrix.

`(11)`--`(12)` are formal in `PositiveOperatorInner.lean`.  `defectGramState` is the normalized
two-defect state; `defectGramState_mulVec_even` and `defectGramState_mulVec_odd` show the parity
vectors `(1,1)` and `(1,-1)` are eigenvectors with eigenvalues `(1 ± kappa)/2`, and
`defectGramState_isHermitian` that the state is symmetric, so the parity decomposition is
orthogonal.  `parity_weights` shows those eigenvalues are each component's share of the total defect
energy and sum to one, and `parity_weight_nonneg` that both are nonnegative.  So the polarization really is a two-state
probability, which is what makes the density-matrix reading exact rather than suggestive.  The far-negative projective endpoint is the universal free
state, whose polarization is `(9)` and tends to zero cofinally.  The no-go therefore identifies an
actual boundary stratum in the moduli of Suzuki carriers.

There is an unconditional source-defined chart away from the arbitrary absolute shift.  For every
`tau>0`, choose

```text
lambda_a^(tau)=lambda_a-tau,
T_a^(tau)=A_a-lambda_a I+tau I.                          (13)
```

Then `lambda_a^(tau)<lambda_a` for every aperture, and the bottom of `T_a^(tau)` is exactly `tau`.

`(13)`'s mechanism is formal in `PositiveOperatorInner.lean`: `tInner_add_smul_id` shows adding a
multiple of the identity raises the induced form by exactly that multiple of the squared norm, so
`tInner_shift_lower_bound` shifts any lower bound by the same amount and
`tInner_shift_floor_eq_shift` puts the bottom at `tau` for a source normalized to its own bottom.
The chart is therefore source-relative by construction: no absolute scale enters.
This **ground-centered projective family** exists without RH and cannot be confused with the
RH-bearing unshifted choice `lambda=0`.  It is the canonical family on which to ask the next
noncollapse question.

The forward research program forced by the theorem is therefore exact:

```text
ground-centered projective resolvents `(13)`
  -> prove survival of one fixed anchored defect jet
  -> identify the resulting nonzero Schur limit
  -> only then compare it with the global Xi/de Branges carrier. (14)
```

This replaces the false request for all-shift independence with a concrete, unconditional shift
selection and a measurable defect-survival invariant.  It does not assert that `(13)` already
survives cofinally; that is the new source-side problem.

## Hostile audit

1. **Normalization.** Suzuki's proof fixes the basis by
   `T v_+=exp(x)` and `T v_-=exp(-x)`, not merely by equal norms.  Hence the same positive scalar
   `r` multiplies both Fourier transforms and cancels from `(1)`.
2. **Quotient passage.** The free denominator in `(4)` is nonzero on the upper half-plane because
   `|exp(-2a)exp(2iaz)|<1`.  On a compact set it therefore has a positive minimum.  Suzuki's
   finite-shift denominators are nonzero there by the all-angle Hermite--Biehler theorem.  Uniform
   numerator and denominator convergence consequently gives uniform quotient convergence.
3. **First jet: generic versus Xi.** Aleman--Martin--Ross recall that arbitrary contractive
   analytic functions vanishing at `i` occur as Livsic functions if nondense symmetric relations
   are allowed. Higher powers of the Cayley factor show that `(7)` can vanish while a generic
   carrier is nonzero. This does not leave an Xi loophole: the exact normalized Xi carrier has
   first defect jet in `(77/85,1)`, so every Xi-identifying source family must preserve first order.
4. **No circularity.** The shifts tend away from the RH-bearing value `lambda=0`; no positivity of
   `A_a` or assumption about the Weil floor is used.
5. **Exact scope.** The theorem refutes uniform noncollapse over all admissible shift schedules.  It
   does not by itself refute equality of a specially reparametrized finite-aperture spectrum, nor
   does it identify a viable canonical shift.

## Literature collision audit

The strong resolvent law `(3)`, the free differentiation model, and the general Livsic
characteristic-function formalism are classical.  Aleman--Martin--Ross (2012) give the general
Livsic representation and show that the characteristic function is a complete unitary invariant;
Belyi--Makarov--Tsekanovskii (2014) relate its Cayley transform to normalized Donoghue/Herglotz
functions.  These sources prevent novelty claims for `(3)`, `(4)`, or `(6)` separately.

Suzuki's June 2026 paper explicitly says that control of `lambda<lambda_a` is important and expects
shift independence in the positive regime, but it does not analyze the negative-shift end, derive
the free carrier `(4)`, identify the cofinal collapse `(2)`, or extract the parity defect angle
`(7)`--`(8)`.  Targeted searches of the cited Livsic/de Branges literature found no application of
this escape mechanism to Suzuki's screw family.  The exact source-specific no-go is therefore a
candidate new result pending specialist priority review.

## No-go closure

- **Exact killing mechanism:** the allowed half-line `lambda<lambda_a` contains arbitrarily
  negative shifts, where the source resolvent forgets `A_a` and approaches the free interval.
- **Strongest positive survivor:** the projective carrier law `(10)`, the defect Gram spectrum
  `(11)`--`(12)`, and the unconditional ground-centered chart `(13)`.  A viable cofinal family must
  retain a nontrivial anchored defect jet in that chart.
- **New insight:** the shift parameter is a projective compactification coordinate.  Arbitrary
  negative shifts hit the universal free boundary; the live route is ground-centered defect
  survival, not admissible-shift independence.
- **Status:** dependency-closed paper proof, now formalized end to end in Lean; generic parent
  theory classified as known; exact source-specific priority remains unverified.  The source
  operator is represented by its defining interface — densely defined, real lower bound,
  admissible real shifts surjective — which is exactly the data Suzuki's `A_a` carries and which
  the strong resolvent law needs.  An explicit construction of the restricted Weil integral
  operator is still absent, so the Lean theorem is a universally quantified statement that covers
  `A_a` the moment that operator is exhibited.


## Lean status of the escape theorem

The three steps of the paper proof are formalized separately and then composed.  Every statement
is unconditional; no RH input, no numerical estimate, and no spectral theorem occurs.

1. **Strong resolvent law `(3)`** — `formal/GaloisForLFunctions/HTGeometry/LowerBoundedSourceResolvent.lean`.
   `LowerBoundedSource` carries a dense domain, an operator, a real lower bound `floor` for the
   quadratic form, and surjectivity of every shift `A + r` with `floor + r > 0`.  That is the
   standard criterion separating a lower-bounded self-adjoint operator from a merely symmetric
   one; symmetry itself is never used.  `norm_shift_ge` is the bound `‖(A+r)x‖ ≥ (floor+r)‖x‖`,
   `shift_smul_sub` is the exact domain identity `(A+r)(r x_g - g) = -A g`, and
   `exists_threshold_norm_smul_sub_lt` / `tendsto_smul_solution` give
   `r (A + r)⁻¹ f → f` for every vector, with a threshold valid for every solution of the shifted
   equation simultaneously.  No resolvent operator is constructed and no uniform boundedness
   principle is used.  `freeSource` witnesses that the structure is inhabited.

2. **Fourier Cauchy–Schwarz upgrade** — `formal/GaloisForLFunctions/HTGeometry/ApertureFourierPairing.lean`.
   On `L²(-a, a)` the transform `F_v(z) = ∫ v x exp(i z x) dx` is the inner product against an
   explicit exponential vector (`apertureChar`), so `norm_apertureFourier_sub_le_of_im_bound`
   converts `L²` convergence into convergence of the transforms that is uniform on every set of
   bounded imaginary height, with the explicit constant `√(2a)·exp(|Im z| a)`.
   `apertureFourier_apertureExp_eq` evaluates the free transform in closed form.

3. **Free carrier `(4)` and the quotient passage** —
   `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiNegativeShiftEscape.lean`.
   `suzukiApertureCarrier_smul` is the projective invariance `(10)` at the level of densities, so
   the common factor `r` cancels.  `suzukiApertureCarrier_apertureExp` proves that the Fourier
   carrier of the free density `exp x` is exactly `suzukiFreeLivsic a`, i.e. equation `(4)`; the
   anchor point `z = i` is handled by the vanishing Cayley numerator on both sides.
   `norm_freeDenominator_ge` and `norm_suzukiFreeLivsic_le_bound` supply the explicit strip
   constants, and `norm_suzukiApertureCarrier_sub_free_le` is the uniform quotient estimate.
   `exists_shift_threshold_carrier_close` is the fixed-aperture escape: beyond an explicit shift
   threshold every deficiency vector produces a carrier within the prescribed tolerance of the
   free carrier on the prescribed strip.

The composite is `suzuki_negativeShift_escape`: for every cofinal aperture sequence and every
family of lower-bounded sources there are shifts `λ_n < λ_{a_n}` whose carriers converge to the
zero Schur function locally uniformly on the upper half-plane — exactly equation `(2)`.  The
diagonal uses the strips `1/(n+1) ≤ Im z`, `‖z‖ ≤ n+1` together with the already formalized free
boundary limit `suzukiFreeLivsic_tendstoUniformlyOn_upperStrip`.
`suzuki_negativeShift_escape_freeSource` instantiates the whole statement with explicitly
constructed deficiency vectors, so the hypotheses are demonstrably satisfiable.

Axiom audit of every declaration above: `[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] exact source formula and admissible shift half-line isolated
- [x] free carrier and proposed collapse estimate derived
- [x] defect-angle/parity formula derived
- [x] projective invariance and defect Gram spectrum derived
- [x] unconditional ground-centered shift chart isolated
- [x] hostile paper-proof audit closed
- [x] primary-literature collision audit closed at the source-specific level
- [x] dependency-closed projective/free-boundary survivor formalized in Lean
- [x] concrete restricted-Weil resolvent escape theorem formalized in Lean: formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiNegativeShiftEscape.lean
- [ ] source-side cofinal shift selected with defect angle tending to `kappa_Xi∈(77/85,1)`,
      even share `>81/85`, odd share `<4/85`, and persistent ground leakage
- [ ] RH

## Log

- 2026-07-21 — created after the arbitrary-shift noncollapse conjecture failed, promoted to Stage
  2 after the paper proof closed, and connected to the separately formalized projective Gram,
  parity, ground-chart, and compact-open free-boundary survivors in
  `SuzukiProjectiveDefectBoundary.lean`.
- 2026-07-31 — negative-shift escape theorem formalized unconditionally in Lean: strong resolvent
  law, aperture Fourier pairing, free-carrier identification, uniform quotient passage, and the
  cofinal diagonal, together with a non-vacuity witness.
- 2026-08-01 — `(8)` formalized, with a correction.  The even/odd decomposition is pure inner-product
  geometry and needs no operator: the pairing is the energy difference, and equal norms — the parity
  input — make the sum the common energy.  But the displayed `|kappa| < 1` requires **both**
  components nonzero, not just the odd one; a vanishing even part gives `kappa = -1` exactly.
  `abs_imbalance_lt_one` now carries both hypotheses and the two boundary lemmas record when equality
  holds.  This sharpens rather than weakens the card's point: the strict bound *is* the assertion
  that both defect components survive.  Six new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(9)` formalized: `freeDefectAngle_eq` gives the free defect angle as `2a/sinh(2a)`
  and `tendsto_freeDefectAngle_atTop` its collapse.  Both defining integrals — the pairing
  `int 1 = 2a` and the energy `int e^{2s} = sinh 2a` — were already proved for the Donoghue card, so
  `(9)` reduced to taking their quotient plus an exponential-domination bound.  With `(8)` from the
  previous entry, the defect-angle survivor section is formal apart from the source-side lower bound
  it leaves open.  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(12)` formalized.  `parity_weights` turns the imbalance into the pair of parity
  weights and proves they sum to one; `parity_weight_nonneg` gives nonnegativity.  Together these
  make the card's "signed polarization of a canonical two-state defect density matrix" exact: the
  weights are a genuine probability pair, each being one component's share of the total defect
  energy.  Combined with `(8)` and `(9)` from the previous entries, the defect-angle and
  projective-compactification content of this card is formal apart from the source-side lower bound
  it leaves open.  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(11)` formalized alongside `(12)`.  `defectGramState` is the normalized two-defect
  Gram state and the parity vectors are shown to be its eigenvectors with the parity weights as
  eigenvalues, the state being symmetric so the decomposition is orthogonal.  With the weights
  already proved to be a nonnegative pair summing to one, the card's "canonical two-state defect
  density matrix" is now literally that — an explicit symmetric matrix with a spectral decomposition
  into parity components and a probability spectrum.  Three new declarations, targeted build green,
  axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(13)`'s shift mechanism formalized.  `tInner_add_smul_id` gives the exact effect of
  adding a multiple of the identity to the induced form, from which `tInner_shift_lower_bound` and
  `tInner_shift_floor_eq_shift` place the bottom at the shift value for a source normalized to its
  own bottom.  This is what makes the chart source-relative: the bottom is determined by the shift
  alone, with no absolute scale entering — the property the section needs to escape "the arbitrary
  absolute shift".  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — exact Xi endpoint removes the card's generic higher-order loophole.
  Multiplicity-exact squared-zero moments and unconditional divisor geometry give
  `77/85<kappa_Xi<1`; locally uniform source convergence forces finite defect angles to this value.
  Therefore any Xi-identifying family has even/odd shares in `(81/85,1)×(0,4/85)` and, under the
  ground-pole estimate, leakage eventually above `(1-kappa_Xi)/4>0`. Paper proof and unconditional
  Lean are in `suzuki-xi-first-defect-jet-gap.md`, `SuzukiXiFirstDefectJet.lean`, and
  `SuzukiXiFirstDefectJetSource.lean`. This narrows source selection; it does not supply it.
