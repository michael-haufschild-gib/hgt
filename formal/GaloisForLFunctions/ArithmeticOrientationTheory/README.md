# Arithmetic Orientation Theory (AOT)

Namespace `GaloisForLFunctions.ArithmeticOrientationTheory` (sub-namespaces `WienerAlgebraAt`,
`WeightedWhiteNoise`, `CriticalKernelAction`); umbrella `ArithmeticOrientationTheory.lean`; 77 modules.

## 1. Motivation

Every closing mechanism in the corpus fails by forgetting a sign: amplitude data cannot see the
even flip, complete-period data cannot see sign twists, rank counts cannot see reweighting,
positivity cannot see the rank-one pole charge. AOT makes orientation the primitive object and asks
which sign- and integer-valued invariants survive unbounded aperture, horizon and damping, and which
exact counting theorems compute them. Results are identities, classifications and counts; RH enters
only through exact equivalences.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Signed Dirichlet form | `signedDirichletForm`, `groundEnergy` | $\sum|c_{ij}|(x_i+\operatorname{sgn}c_{ij}x_j)^2$, switching-covariant |
| Frustration | `frustrationIndex`, `frustrationMass` | misaligned overlaps after the best switching |
| Tower data | `ratioCorr`, `productCorr`, `towerMellin`, `towerOddPrimeSide`, `cosetToeplitz` | odd prime side of one prime tower |
| Cholesky tails | `kmsTail`, `cosetTail`, `continuumPrimeTower` | innovation coordinates of a tower |
| Archimedean diagonal | `archReflectedDiagWeight` | $W_{\rm arch}(n)\approx n/2$ |
| Shared charge | `primeTowerCharge`, `activeTowerWeight` | per-site tower cost after cancellation |
| Readings | `Orientation`, `OrientationFaithful`, `Invisible` (SSIC) | flips and what a reading sees |
| Even flip | `evenFlip`, `amplitudeReading` | $c^\flat=c+(\delta_1-2\delta_2)\star c_e$ |
| Sections | `h0`, `h1`, `frobeniusMass`, `HasFrameBound`, `dirichletSampling` | kernel/cokernel of a reading matrix |
| Wiener algebra | `WienerAlgebraAt σ`, `CriticalWiener` (THIM), `IsWienerUnit` | $\ell^1$ Dirichlet algebra at $\Re s=\sigma$ |
| Spectrum | `BohrPoint`, `bohrEval`, `halfPlanePoint`, `polePoint` | closed polydisk over primes |
| Repair | `paidIdeal`, `obstructionHull`, `operatorHull` | kernels that pay $c$; common zeros |
| Zero data | `translatedOffLineZeroHull`, `visibleTranslatedZetaOrder` | $\rho-\varepsilon$, uncancelled order |
| Orbits | `WienerUnitOrbit`, `WienerMonoidOrbit` | unit equivalence, monoid preorder |
| Orientation norm | `orientNorm`, `polePairing`, `smoothFlipKernel` | coordinates $(P,P_e)$ of a kernel |
| Section cones | `sectionEffectivityCone`, `sourceSectionCone`, `gradedChebyshevSectionCone` | effectivity from $h^0$ |
| Receiver index | `poleJetMatrix`, `nodeDivisorEulerChar`, `apertureH1ChebyshevCorrection` | pole jets; $E(s)=e^s+s-1-\psi(e^s)$ |
| Aperture transport | `apertureSpectralJump`, `ceilingScaledGroundEnergy` | $\mu(a)-\mu(b)$; $e^{\beta}\mu$ |
| Width category | `ReceiverObject`, `widthFunctor`, `IsZeroWidthObject` | receivers over $[0,\tfrac12]$ |

## 3. Language

- **Faithful / blind**: a reading separates every datum from its flip / is constant on flip classes.
  Blindness is closed under post-processing, joins and coarsening.
- **Frustration**: overlaps of the wrong sign that no switching removes. **Balanced** = index 0.
- **Tower**: the powers of one prime; **coset**: $p$-free label $a'$ with sites $p^ia'$.
- **Paid**: receiver bounded. **Repairing ideal** $P(c)$: kernels $k$ with $k\star c$ paid.
  **Hull**: Bohr points killing $P(c)$. **Index**: $\operatorname{rank}\mathcal W_{1/2}/P(c)$.
- **Visible order**: $\operatorname{ord}_\rho\zeta-\operatorname{ord}_{\rho-\varepsilon}\zeta$, the pole order of
  $1/\zeta(s+\varepsilon)$ not cancelled by $\zeta(s)$.
- **Tied point**: radii at all primes come from one $\Re s$ (half-plane points); untied points exist.
- **Unit**: any of the equivalent width coordinates (damping, aperture, index, effectivity, growth).

## 4. Mechanisms

**Frustration.**
1. Ground energy $\le4\nu_w/n$; zero iff balanced (connected); signed Cheeger $\mu\ge h^2/(4D)$; frustration
   discounts the local budget by $h^2/(8D)$.
2. Odd Weil ledger: only prime-sum overlaps can frustrate; the lattice $\{\log n\}$ is balanced at every
   aperture; prime triangle $\nu=2$; matched samples $2|Q|$ at small weight but quenched at full weight;
   collar-skimming samples $\nu=2M|Q|$ (100% frustrated) at full weight; $(0,3/10]$ frustration-free.
   Frustrated configurations are still paid along canonical paths.

**Prime towers.**
3. Rank-one law: tower product part $=\log p\,(S_p(q)^2-q(1)^2)$; ratio part = one-sided Toeplitz forms on
   $p$-free cosets; odd side independent of $q(1)$.
4. KMS–Cholesky: odd side $=\log p\,[\text{Cholesky energy}-\text{mass}]$; the Hankel square is the zeroth
   Cholesky mode of the unit coset and cancels. Continuum: reflection Cholesky, one diagonal mass pays
   every power of one prime.
5. Archimedean domination: $\log p\,S_p^{+2}\le\tfrac12$ arch diagonal per tower; summed over all towers,
   odd side + arch diagonal $\ge\frac1{12}\sum_{n\ge25}nq(n)^2$ for profiles supported in $[25,X]$, and
   $\ge\frac1{16}\sum_{n\ge256}nq^2-106\sum_{n\le255}q^2$ in general — horizon- and prime-set-uniform.
   Continuum: all primes $\ge-12e^A\int_0^AF^2$.
6. Shifted pair $\zeta(s-a)\zeta(s+a)$: tower product part is rank two; Cauchy–Schwarz ratio diverges;
   $|a|\ge1$ reverses both dominations, already for one point mass.

**Readings and sections.**
7. Even flip read at 2: $M(c^\flat)-M(c)=2\log2\,W_c(2)$; amplitudes and complete-period data are blind
   (sign orbit $(\mathbb Z/2)^{N-1}$); amplitude reading does not resolve payment.
8. Nyquist: $h^0-h^1=\dim-\#\text{nodes}$, $h^0\le\dim-\text{mass}/K$; log-free frame constant
   $\tfrac{5\pi}2T+5\pi eN$; at 1-separated heights injectivity fails exactly past the square-root
   aperture, which equals the lattice Nyquist aperture.
9. Counts are reweighting-invariant ($h^0$ of $\Lambda$ = of shifted pair); Frobenius mass and $E(s)$ are
   selective. $h^0$-supply $-$ $h^1$-obstruction $=E(s)$ on boxes; on apertures
   defect + $E$-correction = archimedean budget.
10. Section cones: $\{h^0\ge1\}$ cones read $x^2$; Ample, RR, Bézout each ⇔ Hodge index. Source cones:
    RR ∧ Bézout ⇔ $\Phi^+=$ defect; finite linear/Fourier readings never Bézout; Rosati cones have Bézout +
    Ample on every curve datum, RR ⇔ zero reflection defect.
11. Trichotomy: sub-Nyquist sign readings are depth-blind; escapes cost $\beta^2L^3$ (aperture),
    $\tfrac12\beta^2L^2$ (magnitude ratio) or $2L\le\beta^2\ell^3$ (mass/dilution).

**Critical Wiener algebra.**
12. $\mathcal W_\sigma\cong\ell^1$ Banach algebra, spectrum = Bohr polydisk; Wiener's lemma; half-plane form
    needs a uniform lower bound; local factor unit ⇔ $|\alpha|<p^\sigma$ (Satake threshold).
13. Payment is a unit invariant; paid class is a forward sink of the monoid; ideal ascends, hull and index
    descend along monoid moves; single-point ideals obey a stabilizer/annihilator dichotomy.
14. Localization: unpaid ⇔ hull nonempty. Smooth power → pole point; oscillating probe → $\{\rho,\bar\rho\}$,
    empty iff $\zeta(\rho)=0$; superpositions of probes never cancel; tower twists obstruct whole
    hyperplanes and untied points.
15. Möbius receiver: repairing kernels vanish at $\rho-\varepsilon$ to the visible order (interior and
    critical boundary); finite jets interpolate in $\mathcal W$, so
    $\sum$ visible orders + #boundary poles $\le$ index; Liouville is unit-equivalent to Möbius.
16. Orientation coordinates: over $o$ or $d^{-\varepsilon}$ the flip acts on $(P,P_e)$ by
    $(P+(1-2^\varepsilon)P_e,-P_e)$; both members paid ⇔ $P=P_e=0$; for multiplicative $f$,
    $P_e\propto f(2)$.
17. Operator vs annihilator hull: equal under closed range; weighted cofactor modules are faithful with
    full annihilator hull while spectra contract.

**Transport and dictionaries.**
18. Damping flow transports residue-combination signs exactly.
19. Aperture: step jump = shell flux $\ge0$; RH ⇔ spectral jumps sum to $\mu(A_0)$; additive fixed-margin
    transport refuted by the Gaussian ceiling; ceiling-renormalized $e^\beta\mu$ is bounded.
20. Width dictionary (8-, 13-, 14-, 15-way), graded version, width functor; all $\zeta$-receivers isomorphic.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Frustration brackets ground energy | `groundEnergy_le_frustrationMass`, `le_groundEnergy_of_cheeger` | unconditional |
| Lattice balanced; prime triangle $\nu=2$ | `isBalanced_lattice`, `frustrationIndex_primeTriangle` | unconditional |
| Full-weight frustration unbounded | `exists_collarPos_frustrationIndex_eq_two_mul` | unconditional |
| Rank-one tower law | `sum_vonMangoldt_productCorr_prime_pow`, `towerOddPrimeSide_eq` | unconditional |
| Tower = Cholesky − mass | `towerOddPrimeSide_eq_cholesky`, `continuumTower_reflection_cholesky` | unconditional |
| Horizon-uniform tower domination | `sum_towerOddPrimeSide_add_archDiag_ge_tail_sub_head_255` | unconditional, odd part only |
| Continuum all-prime payment | `sum_continuumPrimeTower_ge_neg_twelve_exp` | unconditional, loss $e^A$ |
| Even flip at 2 | `firstPronicMoment_evenFlip_sub`, `not_resolves_amplitude_receiverBounded` | unconditional |
| Nyquist bound and diagonal | `h0_le_nyquist`, `nyquist_diagonal_and_squareRoot_threshold_synthesis` | unconditional |
| Wiener's lemma (polydisk, half-plane) | `isUnit_iff_forall_bohrEval_ne_zero`, `WienerAlgebraAt.isUnit_iff_exists_le_norm_lSeries` | unconditional |
| Unpayability localized | `not_receiverBounded_iff_exists_obstruction`, `obstructionHull_oscillating_nonempty_iff` | unconditional |
| Visible zero orders bound the index | `sum_visible_orders_add_boundary_card_le_paid_index` | unconditional lower bound |
| Section cones add nothing | `sectionEffectivityCone_tfae`, `sourceSectionCone_riemannRoch_and_bezout_iff` | unconditional |
| Rosati Bézout without purity | `rosatiSourceCone_riemannRoch_iff_reflection_zero` | unconditional |
| Receiver index theorem | `receiver_index_theorem` | unconditional |
| Width dictionary | `widthDictionary_tfae`, `categoricalWidthDictionary_tfae` | equivalences |

## 6. Tools

**Developed.**
- Switching calculus: cut formula, sparse rigidity, sub-sample monotonicity, fibre superadditivity, co-area.
- Tower toolkit: regrouping by towers, coset decomposition, KMS–Cholesky, top-site cancellation,
  multiplicative Schur split with divisor reindexing, $\sum\Lambda(m)/(m\sqrt m)\le8$, dyadic Chebyshev.
- Reading calculus: closure of blindness, refinement, shadows, trichotomy with precision costs.
- Reading matrices: rank–trace law, Sobolev/cell/harmonic reweightings preserving $h^0,h^1$.
- $\mathcal W_\sigma$: Banach algebra, Gelfand spectrum, coefficient functionals, sequence extensions of
  contractive multiplicative families, coordinate min-modulus untying, Kronecker approximation.
- Repair calculus: ideal sums/intersections, convolution locality, conjugation symmetry, separated
  characters onto $\mathbb C^\iota$, finite jet and mixed-data interpolation, cleared continuation identity.
- Orbit calculus: unit equivalence, monoid preorder, Dirichlet cancellation for $c(1)\ne0$.
- Selectivity battery as non-objects: `selectivityBattery_goldenDatum_nonObject`,
  `selectivityBattery_shiftedPair_nonObject`, `selectivityBattery_parityTwins_nonObject`,
  `selectivityBattery_nodes_nonObject`, `selectivityBattery_finiteAperture_nonObject`,
  `selectivityBattery_rate_and_precision`.

**To build.**
- A lower bound on $\mu(A)$ from the switching class of the continuum ledger (Cheeger with
  archimedean/polar budgets).
- Signed coset correlations on the lattice head $n\le255$; an aperture-uniform continuum tower bound.
- An exact index formula below the zero width (reverse inclusion of hulls).
- A source energy $\Phi\ne$ defect with $\delta(x,y)^2\le\Phi(x)\Phi(y)$ and RR from its definition.
- A selective section count at/beyond the diagonal coupled to Frobenius mass or $E(s)$.
- An operator-hull index on the actual cofactor escape module (ADR).

## 7. Open questions

1. Is $\operatorname{hull}(\mu d^{-\varepsilon})$ exactly the translated off-line zero hull below the zero
   width, with index = visible zero count with multiplicity? (Proved only where both are empty.)
2. Is $P(c)$ determined by hull plus local orders? (Hull alone is not: non-radical ideals; same ideal,
   hull and index in distinct unit orbits.)
3. Does frustration of the continuum ledger bound $\mu(A)$ from below?
4. Can the continuum all-prime loss $12e^A$ be replaced by a subexponential function of the aperture?
5. A quantitative relative step $q_j\mu(A_j)\le\mu(A_{j+1})$ compatible with the Gaussian ceiling.
6. A faithful reading that is also an estimate in one trichotomy branch at its stated precision cost.
7. Does an orientation coordinate (like $f(2)$ for multiplicative weights) exist for the full Weil form?

## 8. Traps

| Trap | Truth |
|---|---|
| Frustration is a small-sample effect | Unbounded at full weight on collar packings |
| Matched-sample frustration $2|Q|$ | Small-$\alpha$ artefact; quenched at $\alpha=\beta=1$ |
| Frustration = failure of positivity | Frustrated triangles are paid on canonical paths |
| Lattice ledger frustrates | Balanced at every aperture; frustration lives between lattice points |
| Tower domination ⇒ Weil positivity | Odd tower part + arch diagonal only; head $n\le255$ and continuum $e^A$ remain |
| Rank counts are selective | $h^0$, rank, $h^1$ are reweighting-invariant |
| Even flip changes amplitudes | Every amplitude and complete-period reading is blind to it |
| No zero on $\Re s\ge\tfrac12$ ⇒ unit | `not_isUnit_threeTermKernel`; need a uniform bound |
| Hull is a complete invariant | Ideal records multiplicity (`not_isRadical_paidIdeal_logPower`) |
| Ideal + hull + index classify unpaid weights | `iterThreeTermConv_smoothPower_chain`: infinitely many unit orbits |
| Hulls live on the half-plane | `exists_obstruction_not_tied` |
| Annihilator hull localizes | Faithful modules have full hull (`WeightedWhiteNoise.hull_eq_univ`) |
| Section/source cones give new effectivity | Exact representation moves all of Hodge index into Bézout |
| Golden datum fails Bézout on mass cones | Mass (Rosati) cones have Bézout + Ample; RR is selective |
| Index lower bound ⇒ index formula | Equality only right of the zero width, where both sides are empty |
| Width functor is deep | The category is a preorder by construction; content = width equalities |
| RH ⇔ ∃ relative step | Soft: $q=0$ works under RH |
| Additive aperture transport | Refuted by the Gaussian ceiling; only relative transport survives |
| Even flip is a symmetry | One-way monoid move on the Möbius receiver |
| Names in `ConcreteReceiverScales` | Declared in APT, SRT, ACompT namespaces |
| Clean compile output | Several modules end with `#print axioms` commands |

## 9. Context

| Direction | Programmes (module imports) |
|---|---|
| Uses | RHTower 22, TransHorizonIncidenceMechanics 21, ArithmeticCastelnuovoSeveri 16, HTGeometry 8, SquareRootThreshold 7, SignedArithmeticEnergyIncidence 5, ScaleSignedIncidenceCriticality 5, BiScaleUncertainty 4, arithmetic-positivity-theory 3, BezoutValuationIncidence 2, ArithmeticIncidencePositivity 2, ArithmeticCriticalityTheory 2, ArithmeticContinuationAndCriticalEnergy 2, ArithmeticCompensationTheory 2 |
| Used by | ArithmeticDefectRigidity 16, BiarithmeticGeometry 8, ArithmeticCastelnuovoSeveri 4, SelectivePositivityAndThresholdLaws 2, ScaleSignedIncidenceCriticality 1, BiarithmeticGaugeGeometry 1, ArithmeticOrientationGeometry 1, ArithmeticIncidencePositivity 1, ArithmeticCorrespondencePositivity 1, MainTheorems |

| Neighbour | Interface |
|---|---|
| ScaleSignedIncidenceCriticality | readings, shadows, `Invisible`; AOT adds flips, faithfulness, trichotomy |
| SignedArithmeticEnergyIncidence | odd Weil ledger, balance, canonical paths; AOT adds index and mass |
| TransHorizonIncidenceMechanics | `CriticalWiener`, pole laws, Fermi/Möbius receivers; AOT supplies algebra, spectrum, ideals |
| ArithmeticIncidencePositivity | ratio/product atoms, total crossing kernel; AOT proves tower laws and arch domination |
| ArithmeticCastelnuovoSeveri | polar surfaces, source cones, curve data; AOT gives section-count forms and boundary rigidity |
| SquareRootThreshold, BiScaleUncertainty | Nyquist aperture, Chebyshev gauge; AOT identifies diagonal = square-root aperture |
| ArithmeticDefectRigidity, BiarithmeticGeometry | consume Wiener actions, hulls, cofactor modules, jets |

## 10. Big picture

AOT says the RH problem is a problem of orientation, not of size. Every reading that throws away sign
information — amplitudes, complete periods, rank counts, finite apertures — provably cannot decide the
question, and every reading that keeps it pays a precision cost quadratic in the depth it certifies.
The prime side of the Weil form is not mysterious locally: each prime tower is a Cholesky energy minus a
mass, the frustrating part is one rank-one square per prime, and the archimedean diagonal already
dominates all towers at once except for a bounded head and a continuum loss exponential in the aperture.
The real difficulty is global coupling, not any single prime.

The Wiener-algebra side shows that payment has a genuine index theory: unpayability is located on a
compact spectrum, counts zeros of $\zeta$ with multiplicity, and is invariant under units. But every
proved statement is a lower bound; the matching upper bound — that the obstruction is exactly the
off-line zeros — is RH-strength. Likewise, every effectivity or section formulation, once made exact,
returns the Hodge index unchanged. The lesson for the programme: reformulations are coordinates on one
width line, and frustration is abundant yet paid. Progress requires an estimate that keeps orientation
through the limit — a selective count, a source energy not equal to the defect, or control of the
continuum coupling between towers.
