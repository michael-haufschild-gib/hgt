# Arithmetic Orientation Theory (AOT)

Namespace `GaloisForLFunctions.ArithmeticOrientationTheory`; umbrella `ArithmeticOrientationTheory.lean`.

**Question.** Which sign- and integer-valued invariants of arithmetic sources survive passage to
unbounded aperture, horizon, damping and height — and which counting theorems compute them?

AOT makes orientation the primitive object. A signed incidence form carries its switching class; a
divisor row its companion (parity) class; a reading the question whether it separates a datum from
its flip; a test space at a node divisor the dimension of its sections; an unpaid weight an ideal of
the critical Wiener algebra and its obstruction hull. Theorems are identities, classifications and
counts; estimates are corollaries. RH appears only in exact equivalences or as the conclusion of one
stated inequality.

---

## 1. Place in the research

Recurring obstructions in the corpus are information lost by a reading: magnitudes and complete-period
data identify sources whose signed receivers differ; finite apertures admit off-line extensions;
positivity says nothing about upper bounds. An orientation invariant records the sign, reflection or
arithmetic distinction a limit must keep. AOT supplies frustration index and mass; the per-tower
rank-one law; the Nyquist rank bound (rank–nullity RR for readings); the even flip read at the prime 2;
the critical Wiener algebra $\mathcal W_{1/2}$ with repairing ideals and obstruction hulls; section cones;
the receiver index theorem; the width dictionary, width functor and the **selectivity battery**.

Supporting framework for routes HF, ACS, AIP, PM, MC. Every dictionary entry is an equivalence; progress
is a bound in one of its units.

| Neighbour | Interface |
|---|---|
| ScaleSignedIncidenceCriticality | Readings, shadows, resolution; AOT adds flips, faithfulness, closure of blindness |
| SignedArithmeticEnergyIncidence | Balance, holonomy, local payment; AOT attaches index and mass |
| ArithmeticIncidencePositivity | Ratio/product atoms; AOT proves the tower rank-one law |
| TransHorizonIncidenceMechanics | Even flip, parity barrier, `CriticalWiener`; AOT proves monoid/algebra structure |
| BezoutValuationIncidence | Damping chain; flow transports orientation |
| ArithmeticCastelnuovoSeveri | Scaling surface, effectivity axioms; section cones are their section-count form |
| ArithmeticCriticalityTheory | Prime anti-diagonal non-Z-type obstruction = frustration |
| ArithmeticContinuationAndCriticalEnergy | Aperture jump = shell flux |
| SquareRootThreshold, BiScaleUncertainty, TransThresholdPairCorrelation | Nyquist threshold $N\asymp T$ = square-root threshold |
| ArithmeticDefectRigidity | Cofactor escape modules; Wiener actions on them |
| ArithmeticOrientationGeometry, ArithmeticLocalDivisorGeometry | Orbit orientation; local source-divisor geometry |

---

## 2. Why

**One invariant, many units.** $\Delta=\sup|\Re\rho-\tfrac12|$ is read exactly by every receiver: damping
($\Theta-\tfrac12$), aperture ($\mu(A)\ge0\ \forall A$), growth (linear Chebyshev band), index (one positive
square), effectivity (RR + ample). `widthDictionary_tfae` is the change of coordinates; a new unit is not a proof.

**Loss of orientation.** Unconditional estimates sit at width ½ (+ VK). Closing mechanisms fail by losing
orientation: amplitude readings are blind (payment is a function of Ramanujan amplitudes iff $\varepsilon>\tfrac12$,
and blindness is closed under post-processing); finite data admit off-line extensions; positivity does not
see the frustrated rank-one pole charge. Index theory and algebraic effectivity are how mathematics keeps
orientation through limits; neither exists on $\mathbb Z\times$(scale). AOT builds their finite exact parts.

---

## 3. Objects and language

| Orientation | Signed forms | Damped weights | Readings | Sections | Wiener algebra |
|---|---|---|---|---|---|
| orientation | switching class | even flip $c^\flat$ | flip $\kappa$ | — | unit orbit |
| index | frustration index $\nu(c)$ | $W_c(2)$ | — | $h^0(A)$ | $\operatorname{rank}\mathcal W/P(c)$ |
| trivial | balanced | $W_c(2)=0$ | $\kappa$-fixed | — | $P(c)=\top$ (paid) |
| faithful | sign-vector energy | first pronic moment | `OrientationFaithful` | rank | obstruction hull |
| blind | energy of $|c|$ | amplitude reading | `Invisible` | — | — |

Lean entry points: `signedDirichletForm`, `groundEnergy`, `frustrationIndex`, `frustrationMass`;
`ratioCorr`, `productCorr`, `towerMellin`, `towerOddPrimeSide`, `cosetToeplitz`, `continuumPrimeTower`;
`h0`, `h1`, `frobeniusMass`, `dirichletSampling`; `Orientation`, `OrientationFaithful`, `Invisible`,
`evenFlip`, `amplitudeReading`; `WienerAlgebraAt σ`, `BohrPoint`, `bohrEval`, `paidIdeal`, `obstructionHull`,
`translatedOffLineZeroHull`, `operatorHull`; `sectionEffectivityCone`, `sourceSectionCone`,
`gradedChebyshevSectionCone`; `poleJetMatrix`, `nodeDivisorEulerChar` $=e^s+s-1-\psi(e^s)$; `widthFunctor`.

**Words.** *Faithful*: separates every datum from its flip; *blind*: invisible to it. *Frustration*:
misaligned overlaps after the best switching. *Tower*: prime powers of one prime. *Section*: a test
annihilated by a reading; *Nyquist bound*: sections $\le$ dim − (Frobenius mass)/(frame bound). *Paid*:
receiver bounded; *repairing ideal* $P(c)$: kernels whose convolution pays $c$; *obstruction hull*: Bohr points
annihilating $P(c)$.

---

## 4. Mechanisms

### Frustration and the odd Weil ledger
1. **Index controls ground energy.** Switching-invariant; ground energy $\le4\nu_w/n$; zero iff balanced (connected
   patterns); signed Cheeger lower bound $\mu\ge h^2/(4D)$.
2. **Where the odd ledger frustrates.** Only on prime-sum pairs. Lattice samples ($\log$ of integers) are
   **balanced at every aperture**; the prime triangle has index exactly 2; sparse samples: index = anti-aligned
   prime-sum count; collar-skimming samples reach $2M|Q|$ at every positive weight; $(0,3/10]$ is
   frustration-free. Frustration is a **continuum** phenomenon between lattice points.

### Tower structure of the odd prime side
3. **Rank-one law.** Tower product part $=\log p(S_p(q)^2-q(1)^2)$; ratio part = sum over $p$-free cosets of
   one-sided Toeplitz forms; KMS–Cholesky gives $\ge-\log p\sum_{n\ge2}q(n)^2$; odd side independent of $q(1)$.
   The shifted pair reverses every comparison for $|a|\ge1$.
4. **Lattice shared payment up to a finite head.** Horizon-uniform Schur dominance: for every $X$, prime set
   and arbitrary-sign $q$, odd prime side + archimedean diagonal $\ge\frac1{16}\sum_{n\ge256}nq(n)^2-106\sum_{n\le255}q(n)^2$;
   nonnegative on profiles supported in $[25,X]$.
5. **Continuum towers.** Reflection Cholesky identity; all primes at once $\ge-12e^A\int_0^AF^2$ — prime-set uniform
   but exponential in the aperture.

### Readings and sections
6. **Oriented readings.** Blindness closed under composition, joins, coarsening; resolving a flipping predicate
   forces faithfulness; complete-period quadratic data are sign-orbit blind.
7. **Even flip read at 2.** $M(c^\flat)-M(c)=2\log2\,W_c(2)$; amplitude readings are blind; parity floor.
8. **Nyquist rank bound.** $h^0+\text{rank}=\dim$, $h^0-h^1=\dim-\#$nodes, $h^0\le\dim-\text{mass}/K$; Dirichlet
   polynomials at separated heights via large values; log-free frame constant balanced at $T=2eN$: the
   **diagonal is the square-root aperture**; above it $h^0\ge N-T$.
9. **Selectivity beyond rank.** $h^0$, rank, $h^1$ are reweighting-invariant (cannot separate $\Lambda$ from the
   shifted pair); Frobenius mass can; box defect $E(s)=h^0$-supply $-h^1$-obstruction; aperture $h^1$ correction
   characterizes Bézout on the odd section cone, paid on $(0,181/500]$.
10. **Section cones.** $\{h^0\ge1\}$ cones calibrate (read the form). Sign-free Bézout: $\delta(x,y)^2\le\Phi(x)\Phi(y)$;
    RR + Bézout ⇔ $\Phi^+=$ defect; finite linear reading cones fail Bézout. Over $\mathbb F_q$ Rosati cones have
    Bézout + ample always, RR iff zero reflection defect (golden datum fails RR). Over $\mathbb Z$ the graded
    Chebyshev cone has RR at every aperture; Bézout at all apertures ⇔ RH.
11. **Receiver index theorem.** Pole orders = section codimensions; zero multiplicities = jet section counts;
    node-divisor Euler characteristic from the reflected prime–polar ledger.
12. **Trichotomy of readings.** Sub-Nyquist sign-factored readings are depth-blind; escapes cost trans-Nyquist
    precision $\beta^2L^3$, magnitude ratios, or third-kind mass data.

### The critical Wiener algebra
13. **Monoid and algebra.** `CriticalWiener` is a submultiplicative monoid; paid class is a union of unit orbits;
    $\mathcal W_\sigma$ is a Banach algebra with spectrum the Bohr polydisk; Wiener's lemma; half-plane form needs a
    uniform lower bound (nonvanishing is not enough); local factor unit ⇔ all $|\alpha_i|<p^\sigma$.
14. **Unpayability on the polydisk.** Unpaid ⇔ nonempty obstruction hull; $d^{-\varepsilon}$ → pole point;
    oscillating probe → $\{\rho,\bar\rho\}$ unless $\zeta(\rho)=0$; codimension counts points; ideals record
    multiplicity (same hull, strictly smaller non-radical ideal).
15. **Index formula for the Möbius receiver.** Paid ⇔ $P=\top$ ⇔ hull ∅ ⇔ rank 0; translated off-line zeros
    $\rho-\varepsilon$ are obstructions and their number $\le$ codimension (equality above the width). Order
    level: every repairing kernel vanishes at $\rho-\varepsilon$ to order $\ge\operatorname{ord}\zeta(\rho)-\operatorname{ord}\zeta(\rho-\varepsilon)$;
    finite jets and boundary values interpolate jointly, so visible multiplicities + boundary points bound the
    paid-quotient rank, also on unit orbits and for Liouville. On the critical boundary any order loss makes
    $\mu d^{-\varepsilon}$ unpaid.
16. **Orientation-faithful norm.** Both flip members paid ⇔ pole coordinates $P=P_e=0$.
17. **Wiener actions on modules.** Bounded multiplicative sequences extend to contractive homomorphisms;
    operator hull ⊆ annihilator hull, equal under closed range; faithful cofactor modules have full annihilator
    hull while operator spectra contract.

### Transport and dictionaries
18. **Damping flow preserves orientation** on residue combinations.
19. **Aperture transport.** Two-gauge step jump = boundary-shell flux $\ge0$; RH ⇔ spectral jumps sum to $\mu(A_0)$;
    fixed-margin additive transport refuted by the Gaussian ceiling.
20. **Width dictionary and functor.** Graded and forcing versions; `widthFunctor` full, faithful,
    iso-reflecting; six $\zeta$-receivers isomorphic; battery models are non-objects.

---

## 5. Pillar theorems

1. **Frustration controls ground energy** (`groundEnergy_le_frustrationMass`, `le_groundEnergy_of_cheeger`).
2. **Odd ledger: lattice balanced, frustration = prime-sum count** (`isBalanced_lattice`,
   `frustrationIndex_oddWeilLedger_of_sparse`, `exists_collarPos_frustrationIndex_eq_two_mul`).
3. **Tower laws** (`sum_vonMangoldt_productCorr_prime_pow`, `towerOddPrimeSide_eq_cholesky`,
   `sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255`).
4. **Nyquist rank bound and its diagonal** (`h0_le_nyquist`, `nyquist_diagonal_and_squareRoot_threshold_synthesis`).
5. **Even flip at 2** (`firstPronicMoment_evenFlip_sub`, `not_resolves_amplitude_receiverBounded`).
6. **Wiener's lemma on the Bohr polydisk** (`isUnit_iff_forall_bohrEval_ne_zero`).
7. **Unpayability located and counted** (`not_receiverBounded_iff_exists_obstruction`,
   `card_le_rank_quotient_paidIdeal_moebius`, `visibleTranslatedZetaOrder_le_paid_kernel_order`).
8. **Section-cone boundary laws** (`sourceSectionCone_bezout_of_defect_sq_le`,
   `rosatiSourceCone_riemannRoch_iff_reflection_zero`, `riemannHypothesis_iff_all_aperture_gradedChebyshev_bezout`).
9. **Receiver index theorem** (`receiver_index_theorem`).
10. **Width dictionary** (`widthDictionary_tfae`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Frustration is a small-sample artefact | Unbounded with aperture |
| Lattice ledger frustrates | Balanced at every aperture; frustration lives between lattice points |
| Lattice shared payment = RH progress | Restricted test class; continuum bound still costs $e^A$ |
| $h^0$ counts nodes | Dimension of annihilated tests |
| Rank counts are selective | Reweighting-invariant; use Frobenius mass or $E(s)$ |
| Even flip changes amplitudes | Every amplitude reading is blind to it |
| Critical Wiener kernels form a group | A monoid; units = no zero on the polydisk |
| No zero on $\Re s\ge\tfrac12$ ⇒ unit | Needs a uniform lower bound |
| Hull is a complete invariant | Ideal records multiplicity |
| Annihilator hull of a cofactor module localizes | Faithful modules have full hull |
| Section effectivity cone is independent effectivity | Membership reads $x^2\ge0$; calibration only |
| Bézout + ample on Rosati cones ⇒ Weil | Golden datum has both; RR is the selective axiom |
| A new unit is progress | Dictionary entries are equivalences |

---

## 7. Open problems

1. **Frustration → $\mu(A)$.** A lower bound on $\mu(A)$ from the switching class of the actual continuum ledger
   (signed Cheeger constant with archimedean/polar budgets).
2. **Continuum shared payment.** An aperture-uniform continuum all-prime bound (now $-12e^A\int F^2$); the lattice
   head $n\le255$ (signed direct coset correlations at small $n$).
3. **Selective section count at/beyond the diagonal**, coupled to Frobenius mass or $E(s)$, stronger than the mean
   value theorem and passing the battery. (If the only sections are those the large sieve counts, the field's
   contribution is its dictionary and battery.)
4. **A source energy that is not the defect**: arithmetic $\Phi$ with $\delta(x,y)^2\le\Phi(x)\Phi(y)$ and RR from its
   definition — ACS's open core in section form.
5. **Index formula below the width**: is $\operatorname{hull}(\mu d^{-\varepsilon})$ exactly the translated off-line zero
   hull, and the rank the zero count with multiplicity? The reverse inclusion is open.
6. **Ideals beyond hulls**: is $P(c)$ determined by hull + local orders?
7. **Aperture jump estimate**: a quantitative bound on the signed new-prime correlation.
8. **A faithful reading that is an estimate** in one trichotomy branch at its precision cost.
9. **Wiener index for cofactor modules** that localizes on the actual escape module.

---

## 8. Selectivity battery

A width-moving claim must pass every applicable test:

| Test | Content | Anchor |
|---|---|---|
| golden datum | Beurling $1-5X+5X^2$ impure | `goldenDatum_beurling_not_pure` |
| shifted pair | fails for $\zeta(s-a)\zeta(s+a)$ | `not_summable_shiftedPairVonMangoldt_windowDilationExponent` |
| parity twins | separate $\mu$/twin, Fermi/flip | `fermi_evenFlip_parityPair` |
| nodes | fatal at $\log4$, free at $\log6$ | `zeroPoleBlindPositiveOn_iff` |
| ceiling | floors decay like $\exp(-\pi e^{2(A-2)})$ | `exists_le_floorLoss_of_floor` |
| finite data | bounded readings admit off-line extensions | `resolutionLimit_width_aperturePositivity` |
| rate | use the prime rate in full | `riemannHypothesis_iff_isLeast_primeRate` |
| function field | reproduce curve Hodge index | `curve_hodgeIndex_tfae` |
| integrality | exactly one positive square | `riemannHypothesis_iff_one_positive_square` |
| precision | depth $\beta$ at scale $L$ costs $\beta^2L^3$ | `branchOne_transNyquist_precision_cost` |

Tools to build: a frustration-to-ground-energy bound for the continuum ledger; a selective section count
beyond the diagonal; an arithmetic source energy with sign-free Bézout and RR.

---

## 9. Principles

Counts before estimates; gauge first (check covariance under the flip); name the reading and whether it is
faithful; pay rank-one charges globally; tag every result with its unit; accompany positivity claims by their
failure on the battery. Capstones take data only; analytic inputs are proved corpus theorems.
