# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Research map of HTGeometry, HilbertMetric, and RHTower

**Corpus cutoff:** 9 August 2026, committed snapshot
**743880c61278b0a75cba2c64f968530f27053e81**.

Formal status means theorem declarations reachable from the committed HTGeometry, HilbertMetric,
or RHTower umbrellas at this snapshot. A proof present only in a paper card is marked
paper-proved or provisional. A Lean file not reached by a committed umbrella is not counted as
formal frontier. The map records present state, not research chronology.

## Abstract

This paper maps every proof architecture toward the Riemann hypothesis currently instantiated by
the corpus. Routes are quotiented by their first unresolved source theorem, not by shared
vocabulary or final RH criterion. Each dossier states endpoint, proved mechanism, obstruction,
open core, and retired subclasses. Lean declarations are authoritative; paper claims are
separated from formal ones.

Neither RH nor its negation is proved. The independent live routes are C1, D2, E, G, L, O, P, Q,
R, T, and U. The unlettered CCM-FU lane is also live. Route N is terminalized: its final
zero-fracture premise is RH-equivalent. Routes T and U are new independent
architectures exposed by the enlarged corpus:

- **Route T** converts the mass-shifted Xi divisor geometry into one exact critical outgoing
  current and then into a finite centered von Mangoldt polynomial inside a moving mass light cone.
- **Route U** follows the first loss of positivity in the shifted-Xi Hankel tower and identifies
  its crossing form with a completed Euler--Gamma extension of an adaptive null flag.

These are not renamed versions of existing routes. Route T has a first-order critical
von-Mangoldt flux endpoint, whereas E has squarefree Möbius parity transport and terminalized N
has a prime-normal domain classifier. Route U has an adaptive finite Hankel null-face crossing endpoint,
whereas G seeks a cofinal Suzuki two-angle meromorphic carrier and P seeks one compact positive
moment measure.

Current corpus also advances four older frontiers. Route E now has explicit source-predeclared physical
relations and exact source-faithful shell laws; relation formation is no longer missing. Route O
has Lean-closed exact compact and exterior Bessel/prolate primitives, while its RH-bearing gap
remains control of the whole ground space. Route R now contains a fully formal Burnol first-wall
Bockstein limit and Stokes landing. The shared R/L/CCM horizontal carrier is itself constructed,
prime-labelled, multiplicity-exact, reflection-odd, and source-oriented before scalarization;
only its independent annihilation remains. Route C1 now has an unconditional source involution and
most analytic components of the eigen-pair prime--Gamma identification; the full identification is
paper-closed but not yet completely certified in Lean. None of these additions creates another
independent route.

## 1. Reading rules and status vocabulary

**Endpoint** is a proved implication or equivalence whose conclusion is RH. It is a receiver, not
evidence for its premise.

**Open core** is first unproved source statement after all proved connectors are removed. An
assumption equivalent to RH is not called progress.

**Closed mechanism** means corpus proves advertised construction cannot provide required
information. Closure is scoped: it does not refute every future mechanism using similar language.

**Positive survivor** is strongest nontrivial theorem exposed by a failed route: rigidity,
classification, exact boundary, or replacement design constraint.

**Independent route** requires a literal source object, an unconditional chain to an RH endpoint,
and a first unresolved producer not identical under the corpus's source-isogeny comparisons to an
existing route.

## 2. Global verdict

| Route | Status | First unresolved source theorem |
|---|---|---|
| A | terminalized | none below its RH-equivalent source orientation |
| CCM-FU | open, unlettered | cofinal noncompact four-unit Ward incidence |
| B | retired | fixed-width scalar mechanism exhausted |
| C1 | open, advanced | singular positive closure/descent of identified eigen-pair Weil form or CCM intersection pairing |
| C2 | retired | detector saturated |
| D | retired | finite prime--archimedean Hankel mechanism exhausted |
| D2 | open | finite high-frequency ceiling for continued literal prime--Gamma source |
| E | open, advanced | unit-capacity entropy-complement/physical-shell relation with normalized seam recurrence |
| F | retired | finite-height Sonin transfer has wrong asymptotic order |
| G | open, narrowed | source-selected two-angle Suzuki carrier and Xi/de Branges transfer |
| G2 | retired | required germ is RH-equivalent |
| H | retired | finite Taylor/theta current loses required source information |
| I | retired | exact collision with C2 width |
| J | retired negatively | unrenormalized energy budget impossible |
| K | retired | all-order survivor belongs to P |
| L | open, advanced | resolved Euler--Gamma/Möbius source annihilator and faithful physical specialization |
| M | terminalized | remaining source-flatness statement is RH |
| N | terminalized, receiver merged with R wall | none below RH-equivalent zero Kadison fracture on every Xi conormal |
| O | open, advanced | whole-ground profile exhaustion and reduced-resolvent control |
| P | open | source-built compact completed-seam Thorin/Markov measure |
| Q | open, secondary | selected source-ratio gate or direct Cassini saturation |
| R | open, advanced | pre-divisor singular Stokes/Cartier annihilation of constructed horizontal carrier |
| S | upstream | source algebraicity or divisor-preserving dynamics with typed Xi handoff |
| T | open, new | cofinal cancellation of centered von Mangoldt atoms in mass light cone |
| U | open, new | strict completed-source orientation of every adaptive shifted-Hankel null flag |

The live independent count is eleven lettered routes plus CCM-FU. This count is conditional only
on current corpus identification: future comparison could merge routes, and a constructed
post-J principal-relative current would add another.

## 3. Common source architecture and merger verdict

The corpus constructs a source atlas far beyond classical scalar criteria:

1. Wold activation gives zeta ratios and logarithmic derivatives.
2. Squarefree breadth and prime-power depth are separated before scalarization.
3. Möbius depth differences, Fisher damping, primitive von Mangoldt promotion, and Gamma
   whitening are explicit.
4. Regular and singular source-to-Xi landings retain divisor and multiplicity jets.
5. Reflection is tracked before positive energy, determinant, or scalar frequency fusion.

Several apparent routes share one horizontal obstruction. Route R's graded determinant anomaly,
Route L's monodromy/Green obstruction, and the CCM Bockstein are source-isogenous realizations of
one reflection-odd horizontal class. Increasing vector dimension, Kummer depth, or route count
does not raise this atlas rank. The common operation previously missing was:

~~~
SOURCE-ZERO-TO-HORIZONTAL-CARRIER:
construct a source-derived relation which retains and orients the horizontal class before
bounded scalarization, while preserving prime labels, divisor multiplicity, and both reflection
orientations.
~~~

`SourceZeroHorizontalCarrier.lean` closes this operation without bounded scalarization. For every
Xi-divisor multiplicity copy it pairs complete-resolution reflection displacement with the full
ordinary-prime Gamma Bockstein family. Ordered adjacent source ratios recover the exact horizontal
grade; both components reverse under `rho ↦ 1-conj rho`; source-tail log times every prime
component is strictly positive exactly off the critical line. The physical Rees--corona landing
retains prime, depth, divisor, and multiplicity provenance.

This completes carrier construction and orientation, not annihilation. Lean proves global carrier
vanishing equivalent to RH. The common open core is now an independent source law pairing the two
retained cofinal orientations so the constructed carrier vanishes, without codiagonalization or
another bounded label-blind observer. Route L asks for this through a singular resolved
source-to-physical comparison; Route R asks for it through singular Cartier/Stokes
non-amplification. These target realizations remain distinct even though they retain the same
horizontal class.

This does not merge C1, D2, E, G, L, N, O, P, Q, R, T, and U into one serial super-route.
They have different admission and producer theorems. It says R/L/CCM comparisons cannot be counted
as independent evidence merely because they use different target geometries.

The remaining problems are therefore not mostly missing connector lemmas. They are source
selection, source-relative coercivity, singular boundary annihilation/positive closure, or
genuinely oscillatory all-prime cancellation before information-losing completion.

## 4. Route dossiers

### Route A — literal CCM first clock [TERMINALIZED]

**Endpoint.** The completed first-clock scalar is nonnegative exactly under its RH orientation.

**Closed chain.** Fixed source-faithful physical-phase transports are identity. Every nonidentity
transport has an explicit phase-connection defect. Aperture-dependent positive Markov transports
exist exactly when the original source scalar is nonnegative; universal feasibility is RH.

**Verdict.** Route A is closed as an independent source-producing mechanism, not as a proof of RH.
First-clock tail bounds, Bohr restatements, and positive mixers cannot reopen it.

**Positive survivor.** Phase-natural rigidity and barycentric orientation completeness provide
exact tests for any proposed successor.

### CCM-FU — four-unit source-codiagonal incidence [OPEN]

**Endpoint.** A moving Gamma/Sonin/Hodge incidence carrying the continued Xi Ward column with
nonincreasing four-unit energy yields the required Ward orientation.

**Proved chain.** The squarefree Fisher lower corner has exactly four critical energy units.
Critical source converges weakly but not strongly, escapes every fixed compact synthesis, and every
internal Xi jet has a source-defined square-summable physical horizon.

**Open core.** Construct a prelimit cofinal noncompact family joining that corner and physical jet
horizon to continued Xi Ward column while preserving source provenance and four-unit budget.

**Dead subclasses.** Fixed compact operators, abstract RKHS realizations, and postlimit
codiagonalization are formally inadequate.

### Route B — fixed-width rectangular Weil floor [RETIRED]

Finite rectangular source, completed lag, prime wall, and reconstruction are extensively
formalized. Positive quadrature and fixed-width scalar transport do not supply a source
orientation. Any successful variable-width or relation-valued replacement changes primitive and
is a new route.

### Route C1 — complete Xi--Weil / Hedenmalm positivity [OPEN]

**Endpoint.** Positivity of complete Xi--Weil form on faithful singular domain implies RH.

**Lean-closed chain.** Corpus contains Hedenmalm source Weil form, folded Dirac defect, and exact
antidiagonal Gram law. Source involution `f(x) ↦ conj(f(-x))` is involutive and realizes the
Xi--Weil sharp operation after source Fourier transform. Theta-cusp seed has exact zero mean.
The transform-convention bridge, eigen-pair line integrability, far-right von Mangoldt line-series
swap, Xi-derivative substrip decay, and generic widening-rectangle vertical-edge vanishing are
formalized and umbrella-reachable.

**Paper-closed connector, incomplete Lean certification.** On the decisive eigen-pair class, the
prime plus Gamma pairing is identified with the antidiagonal Hermitian Gram by a pinned
single-pole Guinand--Weil rectangle argument. This closes the prime-identification gate at paper
level, not positivity, and falsifies the prior wall-grade obstruction conjecture on this decisive
class. Lean still lacks the final Fourier inversion/convolution evaluation and
rectangle assembly at this committed cutoff.

The CCM branch separately has exact nonunital strong cyclic quotient, closed restriction quotient,
descended Lefschetz action, Real structure, Clifford transgression, and nonzero Haar--Mellin
separator. Untwisted Lefschetz action is Real-even; multiplication by i supplies canonical
anti-Real transgression.

**Open core.** Either:

1. construct a source-derived singular common domain and positive/nondegenerate closure for the
   identified eigen-pair Weil form, including multiplicity/Jordan directions, without assuming
   divisor location or simplicity; complete the two remaining Lean connector stages; or
2. construct positive CCM bivariant/intersection trace pairing on exact quotient, prove Hodge sign,
   and identify it with Weil pairing.

No premise may assume complete Weil positivity or divisor location.

### Route C2 — theta-cusp center-mixed current [RETIRED]

Finite theta detector is saturated and its missing width is exactly RH-bearing. It contributes
interfaces to Q, not an independent producer.

### Route D — finite prime--archimedean Hankel sign [RETIRED]

Finite moment reconstruction and local Hankel positivity cannot orient all-degree completed
source. The surviving all-degree compact moment problem is Route P; the continued high-frequency
tail is Route D2.

### Route D2 — continued prime--archimedean ceiling [OPEN]

**Endpoint.**

~~~
ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove 4  iff  RH.
~~~

**Proved chain.** Central band through frequency four is verified. Any finite upper ceiling on
imaginary continued relative trace above four extends by reflection and excludes off-line poles.
If RH is false, continued source is cofinally unbounded, not merely wrong-signed locally.

**Open core.** Derive any finite uniform ceiling from literal analytically continued prime--Gamma
source in critical strip and frequency greater than four. Euler-convergent sieve tails and larger
finite verified bands do not cross this continuation wall.

### Route E — squarefree Möbius parity transport [OPEN]

**Endpoint.** A source-predeclared physical transport with square-root Gibbs cost, unit incoming
capacity, full interval Hall control, and normalized friable/one-large-prime seam flux yields
critical Mertens cancellation and RH.

**Closed arithmetic reductions.**

- two-or-more-large-prime remainder and positive valuation depth are negligible;
- hard face is squarefree depth zero at central Wold breadth;
- every fixed off-normal breadth tail is controlled;
- coprime opposite-sign supply and prime-anchor capacity exist;
- every fixed finite Wold-moment reader is parity-blind;
- polynomial patch seams telescope as exact coboundaries;
- scalar phase nodes and finite differential-algebraic Euler-germ constructions cannot see free
  infinite prime-clock orbit;
- critical-mesh energy and several variance endpoints are RH-equivalent receivers, not producers.

**Explicit physical sources now constructed.** Relation formation is no longer open.

1. Grade-recurrent entropy-spread relation supplies source-predeclared opposite-parity cells,
   weighted near-Hall expansion, seam-crossing cells, row admission, and mixed-cost control, but
   loses a subpower factor before unit capacity.
2. Whole-anchor reservoir/E3 relation has reciprocal row mass and polylogarithmic column loss.
3. Product-truncated reservoirs retain a fixed proportion of central harmonic mass under
   subpower displacement.
4. Source-faithful Euler tilt identifies literal Gibbs multiplier and forces a bounded physical
   log-product shell at slightly supercritical moving Euler edge.
5. Entropy-complement breadth mixture recovers full factorial mass across coupled reservoir/token
   branches and keeps every terminal at opposite Möbius parity.

Lean formally closes critical terminal variance minimax, physical-saddle antiscale barrier,
shell-conditioned parity--energy regression, product-truncated reservoir mass, source-faithful
Euler-tilt unit shell, parity-coalesced full-mass cube, and harmonic reservoir capacity. Paper cards
prove stronger relation-level convolution laws where noted.

**Actual open core.**

~~~
ENTROPY-COMPLEMENT-UNIT-SHELL-ROUGH-CONVOLUTION:
for one fixed source-predeclared weighted relation, prove
(i) joint short-interval lower mass for coupled breadth branches outside square-root Gibbs mass;
(ii) unit incoming load, or unmatched mass <= X^(1/2+o(1)) together with global column
     chi-square <= X^(o(1));
(iii) normalized zero/one-large-prime seam charge;
(iv) recurrence accumulation with alternating finite-volume signs and total quadratic
     displacement X^(o(1)).
~~~

Equivalent analytic formulation is source-faithful recurrence-weighted shell covariance, retaining
off-diagonal shell phases. Positive Laplace averaging is impossible because literal unit shell is
not monotone and diagonal shell transversality does not control cross-shell covariance.

**Blunt verdict.** Old statement “define R_X” is obsolete. Missing theorem is unit physical
capacity plus recurrence/seam orientation for already explicit relation families.

### Route F — all-prime Sonin transfer [RETIRED]

Finite-height Sonin/Burnol completions and compact multiplicative corrections have wrong order or
collapse source. Any order-one pre-Gamma packet-diagonal successor is a new route.

### Route G — Suzuki two-angle meromorphic source [OPEN]

**Endpoint.** A source-admitted Suzuki Hermite--Biehler/de Branges carrier implies RH.

**Closed chain and constraints.**

- finite self-adjoint extensions, anti-Pick identities, residue signs, Herglotz representation,
  and support theorem are formalized;
- parity Hankel blocks have infinite rank and, after first prime seam, infinite positive and
  negative index; finite-rank and Pontryagin comparisons are dead;
- proposed one-angle holomorphically gauged entire limit is impossible;
- compact-core deficiency phase selection collapses in global limit;
- regular unit-response, finite-Rees, fixed compact completion, and positivity-preserving
  semigroup subclasses are closed;
- exact Xi first-defect cone forces nontrivial even/odd source shares;
- generic positive resolvent geometry, pointwise exponential sourcing, torque sign, and fixed
  covariance do not orient required transfer.

**Open core.** Construct on one cofinal aperture family a source-predeclared parity profile before
scalar fusion; prove either literal bottom-reflection cone or exact measure-level credit/debt
budget; produce pre-divisor tangent roots and two-angle analytic lifts; prove source admission and
first/second-jet meromorphic convergence to Xi/de Branges target. Current sharp local gate is a
source-specific reflection/skewness budget, not generic positivity.

### Route G2 — relative-Volterra source-germ weld [RETIRED]

The required analytic germ is already RH-equivalent. Mapping-cone or Volterra packaging does not
create its source.

### Route H — Xi Taylor/theta current [RETIRED]

Moving completed-source polynomial parity and finite Taylor currents lose orientation after even
factorization. A relation-valued indefinite successor would be a new route.

### Route I — sharp dyadic prime window [RETIRED]

Its surviving width equals the already saturated C2 coordinate. No independent premise remains.

### Route J — Julia compound-Poisson energy [RETIRED NEGATIVELY]

**Closed theorem.** For L_m=6 log m, m>=25, and symbolic Chebyshev threshold,

~~~
E_bad(x,L_m) >= log(m)/20
~~~

for every Julia scale x. Hence no uniform unrenormalized energy budget exists. Zero scale restores
rank-one coherence and the bad energy tends to square of total boundary mass.

**Consequences.** Off-diagonal cancellation cannot remove positive unit diagonal; post hoc
diagonal subtraction destroys one-node capacity; bounded polarizations are under-capacity; the
unrestricted residual capacity is RH itself.

**Positive survivor.** A viable successor must be a principal-relative current defined before
good/bad projection, nonseparable and non-coboundary. Existing instance belongs to Route R. A
different literal construction would be a new route.

### Route K — quadratic spectral realization [RETIRED]

Quadratic mechanism fails. Strongest all-order marked-prime/quartic survivor transfers to compact
moment Route P.

### Route L — Deninger/Green/Hodge source descent [OPEN]

**Endpoint.** A strict source-first chain comparison makes actual Burnol/Deninger coefficient a
boundary reader value; reader kills boundary, forcing K_n(rho)=0 and Re(rho)=1/2.

**Lean-closed components.**

- completed Xi Green operator and explicit nonzero primitive;
- coefficient-faithful Green-to-Calderón--Witt incidence;
- relative Tate boundary and faithful top-coordinate recovery;
- Burnol conormal identity E_n^B(rho)=K_n(rho) and critical-line classification;
- ordinary-integer Hochschild/BV boundary and exact physical failure
  n(g_n(s)-g_n(s#))=K_n(s);
- all-cross-prime Koszul compatibility, retaining complete Xi coefficient as residual kernel;
- genuine rational-adelic relative complex and strict prime/depth/divisor/jet-faithful Route-R
  chain map.

Further source work constructs M_zeta, Euler-depleted strict admission, cofinal prime
periodization tomography, half-density Floquet energy, exact Möbius--Fourier commutator with
Poisson kernel, canonical Möbius right inversion, and actual Gamma/co-Poisson boundary/Green
transport. Critical Floquet subtraction is exact centered von Mangoldt autocorrelation, but every
nonnegative diagonal prime repair is indefinite by explicit two-bump witnesses.

**Paper-closed but not promoted as formal route closure.** All-prime-first Euler--Gamma/Möbius
transgression has strict PNT endpoint, contragredient physical/Fourier connection, and unsquared
Green--Stokes law with boundary image equal to Möbius--Fourier commutator.

**Open core.**

~~~
DAC_DENINGER_RESOLVED_GREEN_SOURCE_ANNIHILATOR:
construct degree-two rational-Witt/Milnor source realization and prove
Omega_(mu,Gamma)=S_mu G_Gamma D=0,
then identify resulting resolved boundary coefficient-faithfully with existing physical
Burnol/Deninger landing before divisor specialization.
~~~

It must retain prime labels, multiplicity jets, and actual F0 physical reader. Fixed prime-2/3
transport is sharp RH-equivalent endpoint falsifier, not admissible premise. Generic mapping cones,
Koszul exactness, cyclic traces, KMS untwisting, or declaring physical vector a boundary merely
relocate or erase K_n.

### Route M — Gamma--Jacobi singular reader [TERMINALIZED]

Source-faithful reader is formalized. Remaining anchored cofinal flatness is equivalent to RH, so
there is no lower source producer within Route M.

### Route N — Hedenmalm prime-normal boundary [TERMINALIZED]

**Endpoint.** Sub-log-square source-derived endpoint-doublet energy at Xi zeros forces centered
imaginary coordinate to vanish.

**Lean-closed source and energy identities.** For continuous aperture `L`, center and covariant
aperture derivatives of one theta-source interval recover its odd and even endpoints. Their Fourier
transforms factor through the exact same completed divisor:

~~~
F(E_L) = S_even(m_L) XiC,
F(O_L) = -i S_odd(m_L) XiC.
~~~

At prime aperture `L=log p`, `m_L` is exactly the marked prime half-character. The full endpoint
energy has no vertical clock and obeys

~~~
E_end,N(z) = 4 sum_(p<=N) 1/p + 2 E_rad,N(Im(z)/2).
~~~

Hence its sub-log-square domain is exactly `Im(z)=0`. Ordinary first spectral jets pay a sharp
`sum (log p)^2/p` cost because odd scalar soldering is not connection-invariant; demanding one
ordinary-jet estimate through the full Jordan tower silently adds a simplicity-strengthened wall.
Multiplicity transport must remain in the marked endpoint bundle and is separate from grade-zero
admission.

**Retired shortcut.** Compact source inverse plus reflection does not give dissipativity. Its exact
rank-two adjoint defect is indefinite, and on root modes its boundary charge is proportional to the
spectral imaginary part. The sign premise is already RH-equivalent.

**Further source closure.** Fixed theta Hilbert fibres cannot simultaneously bound translations and
retain the detector; moving fibres absorb the detector. Canonical `L2(k^-1 dx)` landing fails for
every prime aperture by an exact double-exponential endpoint divergence. Moving horizons instead
split into one universal `k(0)/sqrt(p)` boundary atom plus a summable residual. The canonical
Gamma-sewn Möbius soft source, after its source-generated Fisher half-transport, produces exactly
this `p^-1/2` atom. With positive damping `u`, its marked energy is

~~~
p^(-1-u+Im z)+p^(-1-u-Im z),
~~~

and is summable exactly when `|Im z|<u`. At the sharp horizon `u=|t|`, Route N's positive doublet
and Route R's oriented Gamma--Bockstein are the same prime-harmonic essential class modulo `ell1`.
More sharply, the difference of the two Route N channel energies is its canonical Krein charge
`Q_t(p)=p^(-|t|)(p^(-t)-p^t)/p`. The grade-independent source Fisher gauge
`g(p)=p^2/(p+1)^2`, uniformly bounded with bounded reciprocal, satisfies the exact identity
`R_t(p)=g(p)Q_t(p)`. Hence it induces an automorphism of the fixed all-prime quotient carrying
Route N's marked Krein class exactly to Route R's wall class. Orientation is not missing; positive
scalarization had erased it. The Krein charge is summable exactly at neutral grade `t=0`.

Ambient conormal completion is now excluded. For the Fredholm cokernel vector
`g_z(x)=k(x)exp(-i conjugate(z)x)`, weighted mass is exactly
`normSq(g_z(x))/k(x)=|k(x)sourceChar(2z,x)|`; hence every Xi root conormal already belongs to the
weighted theta source space. Yet for every fixed `0<u<1/2`, the ambient conormal `z=iu` fails the
marked damping-`u` fibre. No total ambient base change exists, even without boundedness or
linearity. Completion must follow localization to divisor-supported Fredholm torsion.

The remaining singularity is now explicit. The Krein charge recovers the positive transverse
modular clock character by

~~~
1 + sign(t) p Q_t(p) = p^(-2|t|).
~~~

Away from neutral grade, `p` is the unique diagonal recovery coefficient. It sends the summable
witness `p^-2` to nonsummable `p^-1`, so it cannot preserve `ell1` or act on the fixed quotient.
After the bounded Fisher gauge, Route R's unique recovery is `p/g(p)=(p+1)^2/p` and has the same
obstruction. Hence “singular base change” is exactly one unbounded prime-clock deconvolution.
On Xi support, scalar Cartier atom survival and Route N Krein summability have the same support;
the scalar derived fibre contracts off line precisely when the fixed-trace obstruction survives.

The positive cocycle is now identified with existing product-sector geometry, not merely compared
by its zero set. At critical horizon the two marked channel masses are `p^-1` and
`p^(-1-2|t|)`; their ratio is exactly `p^(-2|t|)`. Their square-root gap obeys

~~~
H_t(p)=(p^-1/2-p^(-1/2-|t|))^2
      =p Q_t(p)^2/(1+p^-|t|)^2.
~~~

Moreover these amplitudes are literally square roots of the existing critical/twisted Wold
valuation masses, and their product is its cross mass `p^(-1-|t|)`. Hence, for the existing squared
local Wold thermofield Hellinger factor `F_t(p)`,

~~~
1-F_t(p)
 =H_t(p)/(1-p^(-1-|t|))^2
 =[p Q_t(p)^2/(1+p^-|t|)^2]/(1-p^(-1-|t|))^2.
~~~

The full normalized thermofield defect is summable exactly at neutral grade. Thus Route N's
Krein wall, transverse modular cocycle, Kakutani numerator, and Wold thermofield sector are exact
polarizations of one Gamma-sewn doublet. Finite Wold thermofield vectors and finite Boolean
contractions already exist; rebuilding them is not an open theorem.

The source dyadic split localizes this doublet further. Squarefree parity odds equal the geometric
Wold parameter, so

~~~
odds_t(p)/odds_0(p)=p^(-2|t|),
odds_t(p)-odds_0(p)=sign(t)Q_t(p).
~~~

The paired-depth residual carries the squared modular ratio, but its twisted-minus-critical
sequence is summable for every `t`; the parity displacement is summable exactly at `t=0`.
Therefore the fixed-quotient modular class is entirely squarefree and the higher dyadic tower is a
regular correction. The generic Boolean--Wold coupling is no longer missing.

Algebraic conormal attachment is also closed. The source-defined squarefree Mellin reporter is
`Z_sq(s)=zeta(s)/zeta(2s)`. On `1/2<Re(s)<1`, `zeta(2s)^-1` is an analytic nonzero unit, while the
archimedean Xi factor is another analytic nonzero unit. Consequently

~~~
ord_s Z_sq = ord_s zeta = ord_s Xi,
~~~

including every multiplicity. The squarefree reporter already carries the complete strict-right
Xi zero germ. What is not supplied by analytic-unit equality is survival and normality of that germ
in the critical exceptional topology.

The remaining projective identification is now exact. Gamma-sewn grade selects
`z_t(p)=-|t| log p`; on `P^1(F_p)` its marked-to-bulk odds are
`exp(2z_t(p))/p=p^(-1-2|t|)`, exactly the twisted squarefree-parity odds. Neutral grade is the
uniform Weyl-fixed projective source. Foreign producer/reporter leakage satisfies

~~~
L_t(p)=H_t(p)(p-1)/(p+p^(-2|t|)),
(1/3)H_t(p) <= L_t(p) <= H_t(p),
sum_p L_t(p)<infinity iff t=0.
~~~

Thus finite projective realization and the all-prime sector classifier are closed. This also
rules out an unexplained same-sector normality premise: scalar projective/Fock completion deletes
every off-neutral germ by orthogonality, so asserting scalar survival would restate the desired
grade. Missing object is source-derived continuation--record correspondence and a source theorem
that Xi conormals have zero complementary record.

All surviving scalar reporters now collapse to one local fracture

~~~
D_t(p)=1-p^(-2|t|)=-sign(t)pQ_t(p),
H_t(p)=D_t(p)^2/[p(1+p^(-|t|))^2],
L_t(p)=D_t(p)^2(p-1)/[p(1+p^(-|t|))^2(p+p^(-2|t|))],
log(1-D_t(p))/(2log p)=-|t|.
~~~

Hence Krein orientation, Kakutani distance, Wold defect, projective leakage, and Poisson/Kadison
impurity are linear or quadratic shadows of one duality--adjunction mismatch. They cannot be
counted as independent pressures toward RH or used cyclically to prove each other vanishes.

Completion preserves this mismatch by reciprocal transfer. With
`A_t(p)=p^(2|t|)`, the inward Sonin survival is `1-D_t(p)=A_t(p)^(-1)`. Every actual strict-right
zero produces a nonzero co-Poisson conormal ladder whose norm tends to infinity. The two reciprocal
edge images have exact Hermitian trace excess

~~~
M_t(p)=D_t(p)^2/(1-D_t(p))=A_t(p)+A_t(p)^(-1)-2,
||T^+y_(j+1)||^2+||T^-y_(j+1)||^2=(2+M_t(p))||y_j||^2.
~~~

The co-Poisson connection is nevertheless flat on its whole quotient. Thus connection curvature
cannot kill the off-line class; its invariant is nonmetricity. At prime dilation ratio, normalized
Burnol holonomy is the oriented coordinate

~~~
H_t(p)=A_t(p)-A_t(p)^(-1)=D_t(p)(2-D_t(p))/(1-D_t(p)),
H_t(p)^2=M_t(p)(M_t(p)+4).
~~~

Route N's positive fracture and Route R's signed holonomy therefore lie on one hyperbolic mass
shell. Reflection reverses `H` and preserves `M`; their conjunction supplies no independent
inequality.

The upstream source-incidence pivot is now exact. Along every nonconstant affine source line from
`Re sigma>1` meeting a strict-right Xi zero of multiplicity `m`, the squarefree overlap `B` and its
division-free Fisher numerator `F` satisfy

~~~
ord(B)=m,  ord(F)=m-1,
not exists analytic q with F=Bq,
lim (v-u)F(v)/B(v)=2m.
~~~

Thus the former charged-graph divisibility gate is impossible. Its positive survivor is the
conormal residue. Centered scaling identifies it exactly with the exceptional Xi affine-current
residue

~~~
[-(rho-1/2)/2]·[2m]=-(rho-1/2)m,
~~~

whose real part is strictly negative for every strict-right zero. Fisher conormal, source normal
cone, and position-times-multiplicity current are one conserved oriented incidence, not three
pressures.

C28 identifies this current with Route T mass propagation. For reciprocal escape `A>1`, put

~~~
u_A=(A+A^(-1))/2,  h_A=(A-A^(-1))/2.
~~~

Then `sqrt(u_A^2-h_A^2)=1`, Burnol holonomy is `2h_A`, nonmetricity is `2u_A-2`, and the Route T
phase has unique saddle `x_*=-a h_A=-(a/2)H`. C27 affine residue is multiplicity times
`-log(A)/(2log p)`. Thus residue, Sonin escape, holonomy, nonmetricity, and mass saddle are
rapidity/orientation/energy/stationary coordinates of one boost charge.

**Terminal no-go.** For an actual Xi divisor copy `q`, put `t(q)=Re(q)-1/2` and
`D_Xi(q,p)=1-p^(-2|t(q)|)`. C21 proves, for every fixed ordinary prime,

~~~
D_Xi(q,p)=0 iff Re(q)=1/2,
[for all q, D_Xi(q,p)=0] iff RH.
~~~

Every hypothetical strict-right squarefree Xi germ has positive defect. Functional-equation
reflection may exchange a free off-line conormal pair; it does not fix either member. Thus zero
complementary record, same-sector normality, projective multiplicative-domain purity, and
duality--adjunction equality are the already retired internal-reflection rank-noncreation premise,
not a Route N producer. Strongest positive survivor is the C19--C28 exact
projective/fracture/escape/holonomy dictionary: every Route N wall is a trace or orientation
polarization of one conserved reciprocal mismatch, while its Fisher source conormal is the
oriented affine residue/rapidity conserved before that transport.
Live work passes to arithmetic injection of this boost charge before divisor formation. Route T's
von-Mangoldt mass current is the exact pre-divisor carrier: timelike prime frequencies have one
saddle, spacelike frequencies have none, and the glancing null layer remains open. The old
overlap-divisibility target remains retired. Route N contributes receiver and diagnostic invariant,
plus exact coordinates for the source law Route T must control.

### Route O — Connes restricted-Weil/prolate ground space [OPEN]

**Endpoint.** Cofinal restricted-Weil floor tending to zero, or nonnegative true floor, is
equivalent to RH.

**Lean-closed finite and comparison layers.**

- literal finite restricted-Weil matrix, reflection, real-rooted completion, and selected floor;
- nested-floor monotonicity and no-evacuation: one negative trial vector pins all later floors;
- pole-uniform prolate normal form, simple-pole cancellation, finite defect mass, and endpoint
  envelope;
- exact compact Bessel primitive, transported exterior primitive, two-branch exact channel,
  polar source, endpoint energy, full primitive, and dilated endpoint laws.

This advances formal status beyond “concrete radial PSWF realization missing.” Core special-function
primitive and exterior channel are now Lean-closed. Remaining formal backlog includes precise
occupancy/promotion statements and final assembly comparisons.

**Provisional paper result.** Complete radial prime response, Poisson center, critical-Mellin
coupling, polar contribution, and constrained prolate seed give

~~~
QW_lambda(a_lambda,a_lambda)
 = D_arch d_lambda log(2*pi*lambda^2)+O(d_lambda),  D_arch>0,
~~~

so explicit seed has eventually positive Rayleigh value r_lambda tending to zero. This result
still needs hostile audit against current Lean realization before full promotion.

**Open core.** Prove source-derived profile exhaustion of every normalized near-ground sequence:

~~~
u_n = prolate ladder
    + translated two-edge boundary
    + prime-phase escape
    + coercive bulk
    + o(1),
~~~

with intact polar--prime cross terms and relative bulk coercivity. Then orient surviving boundary
channel or prove true floor nonnegative. More seed asymptotics, finite real-zero determinants, or
renamed Rayleigh comparisons do not advance this wall.

### Route P — completed-seam Thorin/Markov representation [OPEN]

**Endpoint.**

~~~
compact completed-seam Thorin representation
 iff compact completed-seam Markov representation
 iff RH.
~~~

**Proved content.** Markov germ recovers all normalized prime--archimedean moments. Any positive
compact witness is unique and equals canonical reciprocal-square Xi-divisor measure. Theta boundary
transport and Route K all-order survivor both land here.

**Open core.** Construct one finite positive compact measure from literal coupled
prime--polar--Gamma/theta source and prove local Thorin/Markov identity without zero locations or
pre-assumed positive moment functional.

**Dead mechanisms.** Uniqueness does not imply existence. Separating polar factor as independent
positive Thorin atom fails at invariant quarter-gap; pole--zeta cancellation must occur before
positive decomposition.

### Route Q — theta--Cassini boundary saturation [OPEN / SECONDARY]

**Endpoint.** Cassini inward saturation, source dominance, transverse-charge vanishing, and RH are
equivalent.

**Unconditional chain.** Theta source gives aperture-independent positive likelihood, positive
finite Hankel blocks, analytic boundary-to-seam continuation, and unique selected exponent
alpha_*>4. Its calibrated reciprocal carrier lies in (0,1/81) and contracts adjacent moments by
1/81.

**Open core.** Decide source inequality

~~~
normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81.
~~~

Failure retires selected carrier; success still needs all-degree closure. Independent alternative
is direct Cassini--Jensen/jet saturation from theta source. Fixed compact Markov branch is P.

### Route R — primitive-current singular continuation [OPEN]

**Architecture.** Route R is corpus-native, not a classical route with cosmetic changes. Its
primitive is a nonseparable prime/depth--divisor arithmetic differential before frequency
separation:

~~~
theta(i,j)=m_i lambda_j-m_j lambda_i.
~~~

Lean proves nonzero triangle curvature, no vertex potential, no clock-difference representation,
reflection-doubled graded-determinant counterboundary, positive resolved Hermitian frame, and exact
fixed-Cartier descent obstruction. A rational-adelic prime-isotropy relative complex retains
ordinary-prime class and maps strictly, with divisor and leading-jet faithfulness, to resolved
actual-Xi complex. Bilateral Stokes regulator kills source boundaries and detects retained class
with period one.

**Burnol realization now closed further.**

- all-prime Hilbert Cartier entrance wall and Poisson-subordinate smooth wall;
- cofinite singular wall trace and folded-mode Witt bridge;
- actual zero-divided first-wall source, source mass/decay/exterior mass, crossing correlation,
  residue polarization, and reflected source;
- uniform integrable Bockstein majorant, continuity of crossing correlation, forward/reflected
  Bockstein-reading limits, exact head-flux limit, collar-depth limit, no constant plateau, and
  equality with same-fibre dyadic Stokes boundary norm difference;
- divided-shift evaluation nonvanishing and fixed-source leakage inequality;
- exact zero-transfer forward/cosine head gains;
- fixed positive two-head energy
  E_a(f)=|h_a(f)|^2+|h_a(Cf)|^2;
- every right-half Xi divisor strictly amplifies this energy, so source-derived non-amplification
  implies RH.

The shared source-zero carrier now supplies exact prime-labelled orientation of the same horizontal
coordinate before scalarization and lands coefficient-faithfully in the physical Rees--corona
class. This is a detector and a carrier theorem: its global vanishing is equivalent to RH. Gamma
orientation therefore does not create the missing annihilation. Ordinary completed collar kills
the singular residue; the decisive law must act before the polar factor erases the Bockstein line.

**Open core.** Prove from pre-divisor Euler--Gamma--Stokes structure one equivalent annihilation or
non-amplification law:

1. coefficient-faithful singular Cartier comparison carrying resolved boundary to fixed physical
   Xi conormal;
2. pairing/annihilation of the two retained ordered cofinal orientations of the already-constructed
   horizontal carrier;
3. non-amplification of fixed two-head Burnol energy under Cartier zero-transfer.

These are faces of same source-isogeny radical, not three independent routes. Ambient L2 isometry,
Sonin membership, transported positivity, determinant-one reflection, associated-grade
preservation, or target norm pullback cannot prove them.

### Route S — source algebraicity and dynamical mirrors [UPSTREAM]

HTGeometry hypertranscendence, source algebraicity, and dynamical rigidity may constrain possible
source maps, but no current theorem carries such constraint to Xi divisor orientation. Route S is
research infrastructure, not yet an RH proof route.

### Route T — mass-shifted critical outgoing current [OPEN — NEW]

**Endpoint.** For every legal a>1/2, sigma>0, and 1/2<d<a, Lean proves

~~~
RH
 iff uniform boundedness in u>=0 of
    sum_(2<=n<=floor(exp(d*u/(d-1/2))))
      (vonMangoldt(n)-1) n^(-1/2) F_u(log n),
~~~

equivalently uniform boundedness of exact mass-test pairing with finite centered Dirichlet
polynomial.

**Proved mechanism.**

1. Mass-shifted Xi spectral trace converts transverse zero width into vertical growth.
2. Completed Chebyshev error flux admits exact Volterra-adjoint identity; polar and explicit faces
   are uniformly bounded.
3. Critical cofinal atoms equal legal bottom Euler source in limit.
4. Continuous interpolation and floor sawtooth are uniformly bounded.
5. Conjugation reduces to u>=0.
6. Superluminal logarithmic-time tail is uniformly bounded.
7. Complete-cell Abel summation reduces cone to centered atoms; partial cell and terminal
   remainder are bounded.
8. Finite sum--integral exchange preserves joint mass and arithmetic phases.
9. Integer face, true-prime reduction, prime-square tail, and cosine form are formalized in
   committed umbrella.
10. Exact phase classification: `log n<u` gives one timelike saddle
    `x_*=-a log(n)/sqrt(u^2-log(n)^2)` with phase `a sqrt(u^2-log(n)^2)`; `log n>=u` gives no
    stationary point. Route N reciprocal escape embeds into this same unit-proper-time boost shell.
11. Exact spacelike contour optimization: for propagation argument
    `zeta=(sigma+i*u)^2+h^2`, Lean proves `Re sqrt(zeta)^2` is the attained maximum curved-contour
    damping quadratic. In `0<u<h`, this rate strictly exceeds both `h-u` and
    `sqrt(h^2-u^2)`. The induced critical balance slope
    `a/sqrt(a^2-1/4)` is strictly smaller than the limiting horizontal-strip slope
    `a/(a-1/2)` for every `a>1/2`.
12. Exact branch-free transform: `x=a*sinh(t)` converts the mass Fourier transform into a
    full-line entire hyperbolic integral with kernel
    `a*cosh(t)*exp(-(sigma+i*u)a*cosh(t))*exp(-i*h*a*sinh(t))`.
13. Exact one-sided curved deformation and Lorentz reduction: for every `0<=theta<pi/2`, the
    contour may be shifted to `t-i*theta`; its norm is bounded by
    `2*a*exp(r)*K_1(a*q)`, where
    `q^2=(sigma*cos(theta)+h*sin(theta))^2-(u*sin(theta))^2` and
    `r=arsinh(u*sin(theta)/q)`.
14. Optimal full-exponent lift: Lean proves C29's maximizing first-quadrant contour is an actual
    interior angle, identifies `q=Re sqrt((sigma+i*u)^2+h^2)`, and proves
    `K_1(s)<=exp(-(s-s0))*K_1(s0)` for `0<s0<=s`. Hence no fixed fraction of the optimal exponent
    is lost, and the absolute spacelike cone reaches the sharp slope `a/sqrt(a^2-1/4)`.
15. Sharp-spacelike atom closure: on every fixed cone
    `log n>=alpha*u`, `alpha>a/sqrt(a^2-1/4)`, Lean proves uniform boost bound
    `exp(r)<=(alpha+1)/(alpha-1)`, exponent
    `p=1/2+a*sqrt(1-alpha^-2)>1`, absolute summability against `Lambda(n)+1`, and a
    cutoff-independent bound for the exact finite centered-atom sub-sum. The full finite cone is
    exactly this bounded sub-sum plus its complementary `log n<alpha*u` sum.
16. Arbitrarily sharp residual localization: for every `alpha>1`, Lean constructs a legal
    `a>1/2` with `a/sqrt(a^2-1/4)<alpha`, then proves RH equivalent to uniform boundedness of the
    exact complementary finite sum supported on `log n<alpha*u`. Hence remaining obstruction
    persists in every strict enlargement of true timelike-plus-glancing cone, however thin.

**Open core.** Prove cofinal cancellation of centered von Mangoldt atoms inside finite mass light
cone, preferably through exact joint pairing before norms. Safe-line Perron bounds hit critical
zero barrier; termwise absolute estimates lose square root; local Lipschitz control sees mass
radiation; Toeplitz and pinned-Volterra metrics cannot kill constant boundary-cohomology class.
The full-exponent curved-contour/Bessel lift and cutoff-uniform absolute summation are proved on
every strict cone `log n>=alpha*u`, `alpha>a/sqrt(a^2-1/4)`. Exact Lean partition and C34 criterion
isolate residual finite sum `log n<alpha*u` for every `alpha>1`; control this arbitrarily sharp
timelike-plus-glancing layer in exact joint pairing.
Exact nonstationarity alone remains
insufficient because reciprocal phase derivative degenerates at null face; required advance is
source-derived centered von Mangoldt cancellation before divisor formation or termwise norms.

**Why independent.** T begins with completed Chebyshev/von Mangoldt current and a mass-dependent
light cone. It neither transports Möbius parity as E does nor classifies theta-domain energy as N
does. Its first unresolved theorem is an oscillatory first-order all-prime flux law.

### Route U — shifted-Xi null-face Krein--Lorentz flow [OPEN — NEW]

**Endpoint.** Far-right shifted Hankel forms are positive. If positivity first fails while moving
toward target, first crossing is singular. Excluding every right-half first crossing by strict
positive completed-source crossing proves required shifted-Hankel positivity and RH.

**Lean-closed mechanism.**

1. Far-right positive definiteness and existence/classification of first crossing.
2. Singular Hankel face has canonical monic null polynomial with real simple roots and flat
   quadrature.
3. First unseen affine extension coordinate equals
   L_y(XP^2)=[P,XP]_y, first Krein crossing, terminal flux, completed source jet, and
   projective prime--Gamma imbalance.
4. Current finite face can realize arbitrary extension remainder; face invariants alone do not
   determine sign.
5. Shifted Xi form splits exactly as longitudinal Hilbert energy minus transverse charge.
   Conjugation makes mixed unmarked channels orthogonal, while marked Lorentz shear survives.
6. Null polynomial produces isometric lightlike flag; saturated-gap derivative is negative
   multiple of crossing.
7. In source window crossing equals actual prime--Gamma moment pairing and first extension of
   exact archimedean/discrepancy cancellation.
8. Gamma right-upper admission positively normalizes mixed feature to same Lorentz shear and
   preserves quartet aggregate; it adds no sign. The admitted Gamma--Lorentz landing and adaptive
   coefficient landing are committed and umbrella-reachable at cutoff.
9. Exact mass-shift determinant germ has first nonzero coefficient
   `det(H_head)(-1)^d choose(2n+d,d) delta_(2n+d)`; all lower coefficients vanish.
10. Head positive definiteness persists analytically. Hence a genuine two-sided cone loss has odd
    contact `d=2m+1`, never the even/Hamburger orientation.
11. Every genuine crossing therefore yields an adaptively lifted null reporter `R=P X^m`, all lower
    flat defects zero, and the exact completed-source obstruction `L_y(XR^2)<0`.
12. Polarizing lower defects gives a totally isotropic lifted flag. Its final two reporters
    `P X^m,P X^(m+1)` have exact completed-source Gram determinant `-delta^2<0`; hypothetical
    crossing is birth of one nondegenerate hyperbolic plane, not merely one wrong-signed scalar.
13. Canonical redundant positive frames construct exact polynomial-independent duals. Their total
    nodal leverage is feature dimension, and arbitrary finite target capacity is exactly an
    inverse-Gram relative moment trace.
14. Critical-line canonical capacity is unconditionally summable for every fixed frame and can be
    absorbed into a finite positive prefix. The capacity obstruction is therefore purely
    off-critical.
15. Odd contact `2m+1` annihilates every square in `P · Poly_{≤m}`. After restriction to the
    critical/off-critical divisor split, critical-line energy is strict positive and the
    off-critical form is strict negative on this entire `(m+1)`-dimensional space.
16. Strict negativity localizes to a finite FE--Schwarz quartet completion even for an infinite
    off-critical divisor; diffuse tails and asymmetric truncations cannot hide the index.
17. The intrinsic negative coordinate is indexed by the conjugation-folded shifted node
    `(Re lambda,|Im lambda|)`, not by Xi copies. Odd contact forces at least `m+1` distinct folded
    nodes. Thus multiplicity, quartet duplication, and accidental collisions provide no extra
    inertia. For a finite off-critical cover `T`, the sharp ceiling is
    `m < #(folded nodes in T) <= |T|`; the former `m<2|T|` bound is weaker.
18. Folded-node equivalence and finite count are invariant under every nonnegative mass shift.
    Hence the adaptive crossing's orbit-rank burden transports exactly to shift one, where nodes
    are `xiSquaredSeamOneCoordinate` and moments are jets of the fixed Cassini entire-source
    logarithmic derivative.
19. This orbit transport is the shadow of an exact all-jet law. For every `y>0`, the full adaptive
    moment tower equals normalized jets of the one fixed Cassini source at the moving center
    `1-y`: `-2 D^n(logDeriv Psi)(1-y)=n! M_y(n)`. Consequently every Hankel entry, lower flat
    defect, polynomial functional, and crossing-induced negative shifted square transports
    identically, not merely by node count. The fixed-source crossing law is valid beyond the
    prime--Gamma window.
20. At the first nonconstant face, write `F(y)=Re M_y(0)` and `H=1/F`. Actual differentiation
    gives `det H_2=-(F^3/2)H''`, while the canonical linear null reporter's terminal flux is
    `F^2 H'''/6`. Hence flat-negative degree-one contact is exactly `H''=0,H'''<0`. On the theta
    strip, `H(t^2)=t*thetaCuspHyperbolicPartition(t)/thetaCuspHyperbolicFlux(t)` and all three
    radial jets are actual derivatives, so the same event is exactly `tq''=q',q'''<0` for this
    explicit quotient `q`.
21. Put `A=thetaCuspHyperbolicFlux/thetaCuspHyperbolicPartition` and let its first three actual
    derivatives be the theta Esscher variance, third cumulant, and fourth cumulant. The explicit
    contact polynomial
    `N=-A^2-tAA'-t^2AA''+2t^2(A')^2` satisfies
    `N=4t^3A^3H''(t^2)=-8t^6 det H_2(t^2)`. Its actual derivative is
    `N'=-3AA'+3t(A')^2-3tAA''+3t^2A'A''-t^2AA'''`. At `N=0`, curvature cancellation gives
    `N'=tA^3q'''`. Thus bad degree-one contact is exactly the source event `N=0,N'<0`.

**Open core.** Exclude the now isolated off-critical negative-index obstruction on every actual
adaptive genuine-crossing flag. Equivalently, rule out strict negativity of the off-critical
divisor form on the self-selected space `P · Poly_{≤m}`. Its terminal marked scalar is

~~~
0 <= L_y(X (P X^m)^2),
~~~

where `m` is selected by first nonzero flat defect and all preceding defects vanish. This contradicts
the Lean-closed consequence `L_y(X(P X^m)^2)<0`. At ordinary contact `m=0`, strict positivity is the
previous `[P,XP]>0` / negative saturated-gap derivative target; determinant parity now covers every
higher stationary contact and removes the even branch. Critical-line tail control and adaptive-to-
fixed-source transport are closed and no longer belong to the open core. Write
`Psi=xiSquaredSeamCassiniSource`; the exact remaining theorem is a source-specific zero-free-center
rigidity law: the jet sequence of `-2 Psi'/Psi` at any real center `1-y`, `y>0`, cannot satisfy an
odd flat-Padé contact with the genuine-crossing orientation. It must consume the vanished lower
defects and self-selected null polynomial. Count alone is inadequate: a zero global Cassini orbit
count is RH itself. Generic Weil budget bounds are inapplicable because the corpus's refunded-index
construction supplies only lower bounds. In degree one the exact source target is now smaller:
prove `N(t)=0 -> N'(t)>=0` for the explicit theta Esscher cumulant polynomial in item 21. This is
equivalent to excluding a negative third radial jet at Euler contact of `q=t*partition/flux`.
Proving global concavity of `q(t)` in `t^2` would suffice but is not required and is not claimed.
Higher-degree flags still require the full adaptive Padé-contact law.

**Dead subclasses.** Generic moment positivity, positive atoms, tied-power sectors, positive/root
location, stochastic order, factorial-normalized carriers, fixed corona continuous reporters,
Gamma lifetime, per-orbit three-point positivity, and reflection aggregation all admit exact
counterexamples or merely transport existing sign.

**Why independent.** U is a first-crossing extension problem on an adaptive finite null flag.
Route G instead needs a cofinal two-angle meromorphic source and Xi transfer; P needs one global
compact positive measure. Neither route's producer implies U's adaptive Euler--Gamma crossing
orientation.

## 5. Candidate routes not yet instantiated

### Post-J principal-relative current

Would be new route only after literal source object, non-coboundary incidence, and unconditional RH
handoff are constructed. Current concrete realization is R.

### Order-one pre-Gamma Sonin successor

Would replace F's wrong-order finite-height transfer. No source operator and chain exist yet.

### Nyman--Beurling / Baez--Duarte finite sections

New Lean corpus formalizes criterion, Gram matrices, detectors, least squares, finite-section
determinants, Möbius residuals, and obstructions. This is important infrastructure but classical
receiver architecture. No new unconditional approximation producer was found; it is not counted
as Route V.

### HTGeometry universal-law-field and analytic receiver infrastructure

New umbrella-reachable modules prove compact-carrier representation for continuous functionals on
compact-open map spaces, dense finite-support prime-quadrant tangent graphs, local
Poisson/Stieltjes absolute-continuity criteria, finite-matrix spectral-density decay and Dyson
identities, exact separable Bures/Alberti approximation and compact-target minimax laws, explicit
finite-amplifier pattern/width caps, Abelian zeta-gas normalization, and full finite one-replica
Pauli generation. These are substantial
generic source and receiver theorems, but none has a typed map to a live route's first unresolved
arithmetic theorem.

The derived-selection and constraint-relativity families sharpen the negative classification.
Their Riemann pullback is nontrivial exactly on the critical line, so using it as a selector is an
RH-equivalent receiver. Faithful re-encoding, fixed defect closure, bounded/static observers,
unframed rank-one naturality, symmetric source inheritance, and finite word filtrations cannot
promote the missing law. A common multiplicative regularizer is also formally blind to subleading
differences between systems sharing one nonzero leading term: convergence for one forces same
regularized limit for the other. Compact-carrier existence therefore does not construct P's
positive source measure; dense prime tangents do not supply a singular sign; Bures minimax and
zeta-gas normalization do not supply arithmetic incidence. This batch adds no independent route.
Its positive route-design survivor is precise: genuinely new law may live in irreducible
unbounded-arity interaction or in a cofinal future-sensitive reporter invisible to every fixed
proper face. Such a construction becomes a route only after an arithmetic source instance and an
unconditional Xi handoff are built; neither exists in committed corpus.

### Hedenmalm theta entire determinants and new finite traces

These sharpen C1/N/P/Q receivers and finite identities. Without a source-derived singular domain,
sub-log-square bound, or compact positive measure, they do not define independent route.

## 6. Fundamental nature of remaining problems

Across live routes, first unresolved statements fall into five mathematical classes.

| Class | Routes | Missing knowledge |
|---|---|---|
| singular source descent | C1, L, R, CCM-FU | positive closure or coefficient-faithful annihilation of retained boundary class before scalar quotient |
| all-prime oscillatory transport | D2, E, T | cancellation or finite ceiling retaining arithmetic phase and physical normalization |
| adaptive spectral orientation | G, U | source-conditioned sign on moving boundary/null data, beyond generic positivity |
| whole-space coercivity | N, O | classify all low-energy/closed-domain escape directions, not one test vector |
| positive carrier existence | P, Q | build literal compact measure after coupled pole--zeta--Gamma cancellation |

This explains repeated stalls. Classical functional analysis supplies receivers once sign,
boundedness, or coercivity is present. Corpus no-gos show these properties are not inherited from
ambient positivity, faithful re-encoding, local exactness, finite moments, bounded observer
towers, isometry, compact-carrier representation, or determinant packaging. The shared horizontal
carrier theorem sharpens this diagnosis: retained class and its orientation are already present;
missing theorem is an arithmetic law forcing its annihilation. More generally, decisive theorem
must act on source before completion removes reflection-odd, phase-sensitive, or adaptive boundary
coordinate.

## 7. Retired mechanism ledger

The following constructions are closed at advertised strength:

- finite local selectors and bounded label-blind codiagonals;
- universal Gaussian/CCR/Fock positivity without source incidence;
- finite Hankel or determinant positivity presented as all-degree source positivity;
- fixed-width rectangular Weil floors;
- finite-height Sonin transfer and compact multiplicative repairs;
- one-angle entire Suzuki characteristic convergence;
- finite-index parity/Pontryagin comparison for Suzuki kernel;
- fixed finite Wold moments and polynomial seam patching as Möbius cancellation;
- finite positive amplifier patterns as a uniform boundary bridge: their certified exclusion
  width is capped at inverse scale;
- scalar phase nodes and finite differential-algebraic prime-germ readers;
- unrenormalized Julia energy, post hoc diagonal subtraction, and bounded residual polarization;
- separable prime-depth incidence and vertex-gauge cycle holonomy;
- fixed clock-jet spectra, unordered scalar frequency fusion, and positive Gamma shorting;
- target-pulled metrics, ordinary Cartier exactness, and generic mapping cones as R/L producers;
- new seed asymptotics or finite real-zero determinants as substitute for O whole-ground control;
- uniqueness/determinacy as substitute for P carrier existence;
- positive Gamma orientation as substitute for U adaptive crossing sign.

Every retired route remains retired unless new work changes primitive or defeats its exact no-go.

## 8. Literature exchange and novelty boundary

Primary literature supplies parent languages but not current Tier-1 source theorems.

- Hedenmalm's 2026 differential-pair spectral realization gives a new spectral interpretation of
  zeta zeros, but no T outgoing-current bound, N source-domain estimate, or U null-flag
  orientation: https://arxiv.org/abs/2606.17494
- Suzuki's 2026 screw-function formulation gives finite-interval self-adjoint operators and a
  conjectural limiting program, but no source-selected G transfer or U completed-source crossing
  sign: https://arxiv.org/abs/2606.09096
- Berg--Szwarc characterize Hankel determinant/positivity subtleties; determinant nonnegativity
  does not supply PSD of every adaptive U face: https://arxiv.org/abs/1405.7267
- Salazar obtains total positivity from positive moment representations; this does not orient
  signed adaptive discrepancy after shifted-Xi factorial normalization:
  https://arxiv.org/abs/2606.31647

Scoped searches found no exact external collision for T's complete mass-light-cone reduction or
U's Hilbert--charge/null-flag/Lorentz chain. This is evidence for corpus novelty, not proof of
historical priority. Specialist review remains required.

External results worth formalizing must be unconditional, source-specific, absent from corpus, and
must narrow first open premise. Additional abstract RH criteria, generic spectral models, or
moment theorems do not meet this bar.

## 9. Disproof frontier

One rigorously certified off-line Xi zero disproves RH. Equivalent finite negative witnesses are
already formalized through restricted-Weil floors, continued prime--archimedean tails, Hankel
faces, and several determinant criteria. No such witness exists in corpus.

Most explicit source-level disproof candidate is growing-order squared-Xi reverse-Bessel radial
jet. Orders through eighteen are positive; moving-prime comparison from order nineteen onward is
open. Numerical evidence is not accepted as proof or disproof.

## 10. Research priorities

### Shortest live chains

1. **R:** derive fixed two-head Burnol non-amplification or equivalent singular Cartier
   annihilation of already-oriented horizontal carrier from pre-divisor Euler--Gamma--Stokes
   structure.
2. **L:** prove resolved source annihilator Omega_(mu,Gamma)=0 and identify it with actual physical
   Burnol/Deninger landing.
3. **T:** prove uniform mass-light-cone centered von Mangoldt pairing.
4. **U:** prove strict completed-source crossing on every adaptive shifted-Hankel null flag.
5. **E:** prove entropy-complement unit-shell capacity, normalized seam flux, and recurrence
   accumulation for fixed relation.
6. **C1/CCM-FU:** complete C1 eigen-pair prime identification in Lean, then construct singular
   positive closure or intersection/Ward incidence on already-built recipients.
7. **O:** prove low-energy profile exhaustion and bulk coercivity for whole restricted-Weil ground
   space.
8. **G:** construct source-selected two-angle carrier and transfer it to Xi target.
9. **D2/N:** obtain literal high-frequency ceiling or closed source-normal endpoint-doublet landing.
10. **P/Q:** construct compact positive carrier or settle selected source-ratio gate.

### Work unlikely to move frontier

- more RH-equivalent scalar coordinates;
- finite-prefix positivity;
- generic compactness without source admission;
- more Route O seed asymptotics without ground-space classification;
- more Route E moments or seam patch algebra without unit physical incidence;
- more Route R frames or orientation detectors without independent singular source annihilation;
- more Route U positive carriers without adaptive null-flag sign;
- builds or formalization of conjectures whose mathematical source theorem is not proved.

## 11. Principal Lean anchors

### Shared source and RH endpoints

- formal/GaloisForLFunctions/RHTower/RiemannTower.lean
- formal/GaloisForLFunctions/RHTower/RHCharacterizations.lean
- formal/GaloisForLFunctions/RHTower/WoldEulerActivationHolonomy.lean
- formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeDisintegration.lean
- formal/GaloisForLFunctions/RHTower/WoldSieveNormalConeVonMangoldt.lean
- formal/GaloisForLFunctions/RHTower/SourceZeroHorizontalCarrier.lean

### C1

- formal/GaloisForLFunctions/RHTower/XiWeilSourceInvolution.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspSeedZeroMean.lean
- formal/GaloisForLFunctions/RHTower/HedenmalmLineTransformBridge.lean
- formal/GaloisForLFunctions/RHTower/EigenPairLineIntegrable.lean
- formal/GaloisForLFunctions/RHTower/VonMangoldtLineSeriesSwap.lean
- formal/GaloisForLFunctions/RHTower/XiCDerivStripDecay.lean
- formal/GaloisForLFunctions/HTGeometry/VerticalEdgeVanishing.lean

### E

- formal/GaloisForLFunctions/RHTower/RouteECriticalTerminalVarianceMinimax.lean
- formal/GaloisForLFunctions/RHTower/RouteEPhysicalSaddleAntiscaleBarrier.lean
- formal/GaloisForLFunctions/RHTower/RouteEPhysicalShellParityEnergyRegression.lean
- formal/GaloisForLFunctions/RHTower/RouteEProductTruncatedReservoirMass.lean
- formal/GaloisForLFunctions/RHTower/RouteESourceFaithfulEulerTiltUnitShell.lean
- formal/GaloisForLFunctions/RHTower/Sieve/HarmonicReservoirCapacity.lean

### L and R

- formal/GaloisForLFunctions/RHTower/DeningerMeyerReflectedGaussianCompletedSourceGreen.lean
- formal/GaloisForLFunctions/RHTower/DeningerCalderonWittCompletedXiGreenIncidenceComparison.lean
- formal/GaloisForLFunctions/RHTower/DeningerBurnolConormalRadialTopBoundaryComparison.lean
- formal/GaloisForLFunctions/RHTower/DeningerOrdinaryIntegerBVGreenStokesRadialComparison.lean
- formal/GaloisForLFunctions/RHTower/CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean
- formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldCurvedSourceDifferential.lean
- formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldPositiveStokesPolarization.lean
- formal/GaloisForLFunctions/RHTower/BurnolFirstWallZeroDividedSource.lean
- formal/GaloisForLFunctions/RHTower/BurnolBocksteinLimit.lean
- formal/GaloisForLFunctions/RHTower/BurnolCartierZeroTransferHeadGain.lean
- formal/GaloisForLFunctions/RHTower/BurnolCartierZeroTransferHeadPolarization.lean

### O

- formal/GaloisForLFunctions/RHTower/CCMPublishedRestrictedWeilMatrix.lean
- formal/GaloisForLFunctions/RHTower/CCMNestedFloorNoEvacuation.lean
- formal/GaloisForLFunctions/RHTower/CCMRadialProlateDefect.lean
- formal/GaloisForLFunctions/RHTower/ProlateExactChannel.lean
- formal/GaloisForLFunctions/RHTower/ProlateFullPrimitive.lean

### T

- formal/GaloisForLFunctions/RHTower/XiMassCriticalOutgoingCurrent.lean
- formal/GaloisForLFunctions/RHTower/XiMassCriticalOutgoingOpenCore.lean
- formal/GaloisForLFunctions/RHTower/XiMassCriticalDiscreteRemainderCone.lean
- formal/GaloisForLFunctions/RHTower/XiMassCriticalCenteredAtomCone.lean
- formal/GaloisForLFunctions/RHTower/XiMassCriticalCenteredDirichletCone.lean
- formal/GaloisForLFunctions/RHTower/XiMassCriticalPrimeSquareTail.lean

### U

- formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryExtensionClass.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryKreinCrossing.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryQuadrature.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelFirstCrossing.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelNullPolynomialRoots.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryHilbertChargeFlow.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelAdmittedGammaLorentzLanding.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryPadeContactParity.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedHankelCassiniSourceJet.lean

## Final frontier statement

Corpus has constructed source, completed landing, many positive geometries, and exact RH
receivers. It also proves why bounded label-blind completion, generic positivity, local exactness,
finite moments, isometry, and determinant packaging erase or fail to orient RH-bearing
coordinate.

Current frontier consists of eleven genuinely different source problems, concentrated in
singular descent, oscillatory all-prime transport, adaptive boundary orientation, whole-space
coercivity, and positive carrier existence. Routes T and U are real additions. Source-horizontal,
Burnol, eigen-pair, Gamma--Lorentz, and universal-law-field additions narrow existing routes or
strengthen receiver/no-go infrastructure; they do not add a twelfth route. New
Nyman--Beurling formalization likewise strengthens a classical receiver; it does not add Route V.

RH remains open. Any claim of progress must now prove one named source theorem above, refute one
route with an exact no-go and positive survivor, or construct a literal new source architecture
with an unconditional handoff not source-isogenous to an existing route.
