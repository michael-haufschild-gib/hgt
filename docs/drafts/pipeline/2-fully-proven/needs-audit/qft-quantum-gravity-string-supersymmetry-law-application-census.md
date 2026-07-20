# QFT, quantum-cosmology, string/M-theory, and supersymmetry law-application census

- **ID:** `qft-quantum-gravity-string-supersymmetry-law-application-census`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** RESEARCH CENSUS / APPLICATION AND NO-GO LEDGER
- **Audit date:** 2026-07-20
- **Scope:** named laws, equations, identities, actions, dualities, and exact constructions found
  from the canonical English Wikipedia topic pages and linked named-formula pages, supplemented by
  focused Google-style searches and primary literature for every live candidate
- **Statement:** Every reviewed formula family receives an explicit corpus match and one of
  `APPLIED`, `LIVE`, `BLOCKED`, `NO-GO`, or `OUT-OF-SCOPE`; physics vocabulary alone is not progress.

## Goal and reproducible completion boundary

Determine which parts of QFT, QED, quantum cosmology, string theory, M-theory, and supersymmetry can
produce unconditional mathematics in this project's HTGeometry, RHTower, or HilbertMetric surfaces.
The useful outputs are exact new theorems, genuine hypothesis discharge, stronger connectors, and
sharp negative classifications.

The web is open-ended, so "every formula on Google" is made reproducible as follows.  The audit
starts from the canonical English Wikipedia pages for the six named domains, follows every named
law/equation/action/duality linked from their technical sections, and runs the focused query families
recorded below.  Algebraically equivalent presentations are one row.  A row is complete only after
the live project source, generated API, formalized cards, fully-proven cards, and failed cards have
been searched.  Every `LIVE` row must then receive a primary-source formula audit.  New pages or
future search results after the audit date are outside this frozen census and require a new audit.

No numerical experiment or computation is admissible evidence in this programme.

## Verdict language

- `APPLIED-LEAN`: exact unconditional project theorem with a direct corpus consumer.
- `APPLIED-PAPER`: dependency-closed paper theorem; Lean promotion still open.
- `LIVE`: exact candidate with a named open core and a plausible direct consumer.
- `BLOCKED`: the algebraic shell exists, but the source-defined physical object or analytic theorem
  is absent; a wrapper would be theatre.
- `NO-GO`: the formula is already known to preserve DA, cancel, lose positivity, or factor through
  a blind quotient, with the positive survivor stated.
- `OUT-OF-SCOPE`: the formula has no defined object in the present problem spaces and supplies no
  legitimate theorem interface.

## QFT census

| Law or formula family | Corpus match | Verdict and exact effect |
|---|---|---|
| Euler--Lagrange and path-integral stationarity | finite differential equations, Gibbs/Ward integration by parts | `BLOCKED`: no rigorous infinite-dimensional path-integral carrier; finite polynomial differential systems are DA and cannot source HT by themselves. |
| Canonical equal-time CCR/CAR | bounded-operator and finite Clifford/principal-symbol APIs | `BLOCKED`: the corpus has algebraic commutator/anticommutator shells but no Wightman field representation, unbounded domains, or source vacuum.  An abstract CCR wrapper would not create a QFT. |
| Spin--statistics theorem | constant-field scalar/spinor determinant comparison only | `OUT-OF-SCOPE`: the theorem needs relativistic covariance, locality, positive energy, and a positive Hilbert metric; those source axioms are not instantiated.  A Gamma quotient named “spin-statistics” is not this theorem. |
| Wick/Isserlis factorization | `WickKolchinProfile`, Gaussian face closure, `EulerSquarefreeWickDefect` | `APPLIED-LEAN/PAPER`: Gaussian finite-jet closure and the exact raw-Euler four-point Wick obstruction are available; the positive survivor is the face-complete connected/Wick-reduced interaction profile. |
| Dyson series and Feynman rules | finite perturbative Gamma and graph carriers | `NO-GO` for frontier HT: every fixed finite diagram/finitely closed differential system is DA.  An infinite resummation can matter only after convergence and a source observable are proved. |
| Faddeev--Popov determinant and ghosts | BRST/Hodge bounded algebra | `BLOCKED`: no gauge-orbit measure, gauge-fixing map, ghost field algebra, or determinant is present.  BRST nilpotence alone does not construct the Faddeev--Popov source. |
| Noether current conservation | `FrozenConstraint`, `QuantumConstraintWard` | `APPLIED-LEAN`: physical-kernel preservation and scalar Ward values; no spacetime current is invented. |
| Ward--Takahashi identity | finite-family Ward and constraint-ideal theorems | `LIVE`: generic contraction/ideal laws exist, but the QED off-shell vertex/propagator finite-difference reporter is not constructed. |
| Schwinger--Dyson hierarchy | `theta-cusp-liouville-schwinger-dyson-ward` | `APPLIED-LEAN`: the theta atom is an exact Gibbs Ward image; the two remaining source inequalities are not discharged. |
| Dyson propagator equation / Bethe--Salpeter hierarchy | no source propagator or two-particle kernel | `BLOCKED`: a formal resolvent identity would not construct the QFT reporter. |
| LSZ reduction | `sectoral-kolchin-signature-quantum-fields` | `LIVE`: exact open core is a derivation-preserving LSZ/Haag--Ruelle reporter from compact-local connected four-point data to HT scattering. |
| Haag--Ruelle scattering | geometric CDD Haag--Kastler route | `LIVE`: wedge-local and two-particle form-factor transfers are proved; intrinsic compact-local connected four-point transfer remains open. |
| Kallen--Lehmann spectral representation | `reciprocal-q-ladder-kallen-lehmann-field` | `APPLIED-PAPER`: positive generalized-free-field spectral realization exists; it is not evidence of interaction. |
| Wightman axioms / locality | geometric CDD local-QFT card; compact-local form factors | `LIVE`: constructive factorizing-QFT input is external; face-complete connected-sector locality is open. |
| CPT theorem | reflection/charge-conjugation Gamma symmetries only | `BLOCKED`: no Poincare-covariant local field net carrying the required antiunitary symmetry is constructed.  Special-function reflection is not CPT. |
| Cluster decomposition | connected-correlator and face-complete Wick--Kolchin profiles | `APPLIED-PAPER` as an interaction diagnostic; `BLOCKED` for a source QFT cluster theorem and quantitative spacelike decay. |
| Haag's theorem | LSZ/Haag--Ruelle route | `NO-GO` for identifying interacting and free fields by one global interaction-picture unitary.  The positive survivor is the asymptotic/local reporter route already isolated by the LSZ open core. |
| Reeh--Schlieder and modular nuclearity | Lechner inverse-scattering cards | `APPLIED-PARENT`: these construct local observables and cyclicity in the external factorizing-QFT parent; the missing project theorem is still the derivation-compatible compact-local reporter. |
| Osterwalder--Schrader reflection positivity | `ReflectionPositiveHankel`, finite KMS modules | `APPLIED-LEAN` only for finite/reflection-Hankel surfaces; `BLOCKED` for a full Euclidean QFT reconstruction. |
| Unitarity and optical theorem | `involutive-scattering-optical-master-constraint` | `APPLIED-LEAN`: involutive scattering gives a positive master constraint; no interacting cross section is inferred. |
| Cosmological optical theorem / cutting | cosmological flat-space HT transfer card | `LIVE`: the algebraic Laurent-coefficient transfer exists; a source-built cosmological model and gauge-invariant in-in survival are open. |
| KMS detailed balance | `FiniteKMSDetailedBalance`, `FiniteKMSFluctuationDissipation`, RHTower KMS family | `APPLIED-LEAN`: extensive finite and countable response laws; full operator-algebraic type-III realization is not claimed. |
| Fluctuation--dissipation | `FiniteKMSFluctuationDissipation` | `APPLIED-LEAN`: finite value law; no continuum QFT extrapolation. |
| Callan--Symanzik equation | finite RG/clock cards | `NO-GO`: a finite closed differential RG system is DA; HT requires a non-finite completion or HT source, not the RG label. |
| Beta-function flow / fixed points | Bethe/Ising/tree RG modules | `APPLIED-LEAN` for exact finite models; `BLOCKED` for a physical QFT whose running coupling carries a new HT invariant. |
| BRST nilpotence and cohomology | `BRSTHodgeConstraint`, `KoszulCohomology` | `APPLIED-LEAN`: nilpotence, Hodge Hamiltonian, Hermitian supercharges, projection-corner discharge, and the one-equation Green/Hodge connector are directly checked and axiom-audited. |
| BV classical/quantum master equation | no graded BV algebra or odd Laplacian | `BLOCKED`: the positive operator master constraint is not the BV quantum master equation; conflating them is forbidden. |
| Gauge anomaly / Wess--Zumino consistency | anomaly and Ward cards | `BLOCKED` in general: several finite incidence anomalies exist, but no source-defined local QFT anomaly complex supplies the RH orientation. |
| Operator-product expansion / conformal bootstrap | Laurent-coefficient, jet, and thermal-CFT Gamma APIs | `BLOCKED`: no source OPE algebra, convergence radius, crossing-positive conformal blocks, or intrinsic structure constants.  A finite OPE truncation is DA and cannot create HT by itself. |
| Goldstone theorem / Higgs mechanism | positive master constraints only | `OUT-OF-SCOPE` until a source symmetry, vacuum orbit, conserved current, and mass matrix are built. |
| Effective action / Coleman--Weinberg potential | constant-field QED Gamma determinants | `APPLIED-LEAN` to exact determinant carriers; `BLOCKED` for a full field-dependent effective action and renormalized variational equation. |
| Crossing symmetry | Gamma reflection, CDD crossing | `APPLIED-LEAN/PAPER`: exact reflection/orbit classifications; crossing alone does not force HT or RH. |
| Renormalized perturbation series | dimensional-regularization Gamma boundary | `APPLIED-LEAN` for exact one-loop Gamma carriers; `NO-GO` for claiming finite perturbation theory as an HT source without a non-finite completion. |

Canonical census sources include the Wikipedia pages for the
[Ward--Takahashi identity](https://en.wikipedia.org/wiki/Ward%E2%80%93Takahashi_identity),
[Schwinger--Dyson equation](https://en.wikipedia.org/wiki/Schwinger%E2%80%93Dyson_equation),
[LSZ formula](https://en.wikipedia.org/wiki/LSZ_reduction_formula),
[Kallen--Lehmann representation](https://en.wikipedia.org/wiki/K%C3%A4ll%C3%A9n%E2%80%93Lehmann_spectral_representation),
[Callan--Symanzik equation](https://en.wikipedia.org/wiki/Callan%E2%80%93Symanzik_equation),
[Wick's theorem](https://en.wikipedia.org/wiki/Wick%27s_theorem),
[spin--statistics theorem](https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem),
[operator-product expansion](https://en.wikipedia.org/wiki/Operator_product_expansion),
[BRST](https://en.wikipedia.org/wiki/BRST_quantization), and
[BV formalism](https://en.wikipedia.org/wiki/Batalin%E2%80%93Vilkovisky_formalism).

## QED census

| Law or formula family | Corpus match | Verdict and exact effect |
|---|---|---|
| Maxwell and Dirac field equations | generic bounded constraints only | `OUT-OF-SCOPE` until the actual unbounded PDE/operator domains are built. |
| QED Lagrangian and covariant derivative `D_mu=partial_mu+ieA_mu` | generic connection/constraint notation only | `BLOCKED`: no spinor bundle, gauge potential, action, or source Euler--Lagrange operator. |
| Local U(1) gauge invariance | frozen/Dirac constraints | `APPLIED-LEAN` as abstract kernel/ideal preservation; no QED state space is claimed. |
| QED Ward--Takahashi vertex identity | Ward layer | `LIVE`: could transfer HT from an inverse-propagator finite difference to a contracted vertex, but the exact source propagator and shift theorem must be constructed first. |
| Photon transversality / Ward identity | constraint Ward value | `APPLIED-LEAN` abstractly; `BLOCKED` for an actual polarization tensor. |
| Dyson resummation | resolvent identities | `NO-GO`: formal geometric/resolvent algebra does not prove convergence or a physical self-energy. |
| Kallen--Lehmann photon/electron spectral form | generalized-free-field cards | `BLOCKED`: gauge positivity can fail and no QED spectral density is present. |
| Euler--Heisenberg effective action | constant-field Gamma determinants | `APPLIED-LEAN` only at the exact scalar/spinor determinant Gamma carriers; the full nonlinear field action is not formalized. |
| Schwinger/Sauter pair production | `SauterBogoliubovGammaBoundary` | `APPLIED-LEAN`: exact Gamma-orbit cancellation/HT boundary and observable readout. |
| Landau-level scalar/spinor determinants | `ConstantFieldQEDGammaClock` | `APPLIED-LEAN`: quotient and product are HT, duplication gives one double-scale clock, and DA renormalization cannot identify the carriers. |
| Vacuum polarization and running charge | beta/Callan--Symanzik row | `NO-GO` for finite-loop HT claims; no nonperturbative QED source is present. |
| Landau pole | no exact nonperturbative QED coupling | `OUT-OF-SCOPE`; a perturbative pole is not an HT theorem. |
| Lamb shift / anomalous magnetic moment | parameter values, not variable-channel laws | `OUT-OF-SCOPE` under the no-computation and source-object rules. |
| Furry charge-conjugation cancellation | reflection/orbit charge machinery | `BLOCKED`: a genuine charge-conjugation-graded QED correlator must precede any application. |
| Compton scattering / Klein--Nishina formula | rational, trigonometric, and finite Gamma closure | `NO-GO` for HT: the tree-level angular/energy cross section is differentially algebraic in its kinematic variable.  It can be an exact benchmark observable but cannot source a new HT law. |
| Moller, Bhabha, and pair-annihilation tree cross sections | finite rational kinematics | `NO-GO`: fixed tree formulas are DA and no source scattering representation is present. |
| Thomson, Larmor, bremsstrahlung, and synchrotron formulas | finite algebraic/Bessel/Airy response families | `NO-GO` for HT at fixed order because the standard carriers satisfy finite differential equations; a non-finite source tower would need a separate theorem. |
| Soft-photon theorem, Bloch--Nordsieck exponentiation, KLN cancellation | gauge/ideal and exponential-observation APIs | `BLOCKED`: the corpus lacks the infrared Fock/dressed-state category and inclusive measure.  Multiplication by a nonzero DA soft factor preserves an existing HT class but does not create one. |
| Uehling potential and fixed-loop vacuum polarization | finite-loop special-function layer | `NO-GO` for new HT without a nonperturbative completion; no physical QED source operator is built. |
| Chiral/axial anomaly | finite incidence anomaly cards | `BLOCKED`: no Dirac complex, regulated current divergence, or index-theoretic QED source. |
| Casimir energy | trace/determinant shells | `BLOCKED`: boundary conditions, renormalized spectral difference, and physical stress tensor are absent. |

The canonical external formula sources include
[QED](https://en.wikipedia.org/wiki/Quantum_electrodynamics),
[Ward--Takahashi](https://en.wikipedia.org/wiki/Ward%E2%80%93Takahashi_identity), and the
[Euler--Heisenberg Lagrangian](https://en.wikipedia.org/wiki/Euler%E2%80%93Heisenberg_Lagrangian),
plus the [Klein--Nishina formula](https://en.wikipedia.org/wiki/Klein%E2%80%93Nishina_formula).
Primary-source matching for the constant-field determinant row is already recorded on its stage-3
card.

## Quantum-cosmology census

| Law or formula family | Corpus match | Verdict and exact effect |
|---|---|---|
| Wheeler--DeWitt Hamiltonian constraint `H Psi=0` | `FrozenConstraint`, quantum master constraint | `APPLIED-LEAN`: physical kernels, weak observables, Ward values, and finite-family master constraint; no functional Wheeler--DeWitt operator is claimed. |
| Momentum/diffeomorphism constraints | finite joint constraints | `BLOCKED`: finite-family algebra is ready; the unbounded local constraint algebra and anomaly freedom are absent. |
| DeWitt superspace metric | HilbertMetric and archived superspace cards | `NO-GO` as a mere analogy; a source-defined positive/indefinite form with a direct consumer is required. |
| Minisuperspace reduction | finite frozen-constraint model | `APPLIED` only as a bounded finite abstraction; it supplies no new cosmology. |
| Problem of time / Page--Wootters clock | clock and frozen-constraint infrastructure | `BLOCKED`: no conditional-state construction or physical clock subsystem has been built. |
| Hartle--Hawking no-boundary path integral | no-boundary backlog | `BLOCKED`: contour, measure, and source wavefunction are absent; boundary rhetoric cannot select zeta. |
| Vilenkin tunnelling boundary condition | no source wavefunction | `OUT-OF-SCOPE` until a concrete minisuperspace equation and boundary category exist. |
| Friedmann equations | finite autonomous ODE | `NO-GO`: standard finite Friedmann systems are DA; they cannot create HT without HT matter/source data or a non-finite completion. |
| Loop-quantum-cosmology Hamiltonian recurrence | shift/difference-Galois and frozen-constraint infrastructure | `BLOCKED`: the primary equation is a second-order step-4 recurrence in the discrete volume lattice, but no intrinsic meromorphic interpolation or differential-field boundary category is selected.  Difference-Galois HT cannot be inferred from arbitrary interpolation. |
| Effective LQC modified Friedmann/bounce equation | finite algebraic autonomous system | `NO-GO` for HT: the effective bounce law is DA.  The positive content is singularity avoidance, not a new differential-transcendence carrier. |
| Scalar field as emergent time in LQC | frozen constraint and group averaging | `APPLIED-PARENT/LEAN-SHELL`: physical-kernel and averaging APIs are ready; the polymer Hilbert space and positive self-adjoint LQC difference operator are not constructed. |
| Mukhanov--Sasaki mode equation | finite second-order linear ODE | `NO-GO`: every fixed-mode solution is differentially algebraic over its coefficient field.  HT would have to enter through a source-built infinite spectrum or non-finite completion. |
| Hamilton--Jacobi--Einstein / WKB and tunnelling instantons | `WkbEdgeProfile`, Liouville--Green amplitudes | `APPLIED-LEAN` for finite asymptotic algebra; `NO-GO` for claiming HT from any fixed finite WKB order.  Source Stokes/resurgent completion remains external. |
| BKL/Mixmaster map | symbolic/dynamical analogies only | `BLOCKED`: finite piecewise-rational iterates are DA; no intrinsic infinite orbit generating function or cosmological reporter is built. |
| Decoherent/consistent histories | trace and projection shells | `OUT-OF-SCOPE` until a history algebra, decoherence functional, and source state exist. |
| Bogoliubov particle production in de Sitter | `DeSitterBogoliubovGammaBoundary`, intensity observability | `APPLIED-LEAN`: exact Gamma response and phase/intensity separation; no primordial observable is inferred. |
| Bunch--Davies detailed balance | de Sitter ultrametric detector | `APPLIED-PAPER/LEAN`: exact detector response; prescribed detector tower is an apparatus, not a cosmological-wavefunction discovery. |
| Cosmological wavefunction total-energy singularity | flat-space HT transfer card | `LIVE`: Laurent specialization is formalized; actual local cosmological realization and in-in/gauge survival are open. |
| Cosmological optical theorem | same card | `LIVE/BLOCKED`: parent cutting law is known; the project needs a source-built HT flat-space coefficient. |
| Cosmological collider infinite tower | Mahler collider card | `LIVE`: must derive the tower from a unitary source, not prescribe HT initial data. |
| Observational transfer functions | conservativity-spectrum theorem | `APPLIED-PAPER/LEAN`: compact reporters can be injective yet unstably blind; actual cosmological transfer compactness remains open. |

External anchors are the Wikipedia pages for the
[Wheeler--DeWitt equation](https://en.wikipedia.org/wiki/Wheeler%E2%80%93DeWitt_equation),
[quantum cosmology](https://en.wikipedia.org/wiki/Quantum_cosmology),
[minisuperspace](https://en.wikipedia.org/wiki/Minisuperspace),
[Hartle--Hawking proposal](https://en.wikipedia.org/wiki/Hartle%E2%80%93Hawking_proposal), and
[Friedmann equations](https://en.wikipedia.org/wiki/Friedmann_equations), together with
[loop quantum cosmology](https://en.wikipedia.org/wiki/Loop_quantum_cosmology).

## String-theory census

| Law or formula family | Corpus match | Verdict and exact effect |
|---|---|---|
| Nambu--Goto action | no worldsheet area functional | `OUT-OF-SCOPE`: no geometric measure/minimal-surface carrier. |
| Polyakov action and `T_ab=0` | constraint and Ward APIs | `BLOCKED`: abstract constraints do not constitute a worldsheet CFT. |
| Weyl invariance / trace constraint | constraint ideals | `BLOCKED`: no worldsheet stress tensor or anomaly coefficient. |
| Virasoro constraints/algebra | finite constraints, principal-symbol modules | `BLOCKED`: no central extension or physical string Fock representation. |
| Critical-dimension anomaly cancellation | generalized Clifford/principal-symbol work | `OUT-OF-SCOPE` without a worldsheet central-charge computation. |
| Worldsheet OPE / vertex-operator algebra | Laurent, residue, and jet APIs | `BLOCKED`: no mutually local vertex operators, state--field correspondence, or OPE convergence theorem. |
| Regge trajectory, string mass formula, and level matching | Gamma pole/orbit and lattice APIs | `APPLIED` as bookkeeping for four-point poles; `NO-GO` for HT because the affine mass/level laws are DA. |
| GSO projection and worldsheet fermion parity | finite involutive group-average projection | `APPLIED-LEAN` to the abstract projection/idempotence interface; `BLOCKED` for the actual worldsheet parity representation, mutual locality, and modular-invariance proof. |
| Open-string Veneziano amplitude | `VenezianoGammaRatioBoundary` | `APPLIED-LEAN`: DA exactly at integer channel separation and HT otherwise. |
| Closed-string Virasoro--Shapiro amplitude | new double-copy card/module | `APPLIED-LEAN CANDIDATE`: exact reflection gauge times squared Veneziano normal form; same DA/HT lattice. |
| KLT open/closed double copy | same normal form | `APPLIED-LEAN`: double copy doubles Gamma-orbit charge without moving its cancellation lattice. |
| BCJ color--kinematics double copy | only the four-point KLT/Gamma specialization | `BLOCKED`: no color Lie algebra, Jacobi-satisfying numerator representation, or general gravity reporter.  The Virasoro--Shapiro theorem is not a proof of BCJ duality. |
| Koba--Nielsen `n`-point integrals | finite differential-system no-go | `BLOCKED`: no moduli-space integral or all-`n` differential classification. |
| String mass-shell/pole tower | Gamma pole/orbit APIs | `APPLIED` to four-point Gamma carriers; not a construction of the full string spectrum. |
| T-duality `R <-> alpha'/R`, momentum/winding exchange | projective reciprocal and mirror modules | `BLOCKED`: reciprocal algebra exists, but no compactified string spectrum is defined; analogy alone is not a theorem. |
| S-duality `g <-> 1/g` | projective inversion modules | `OUT-OF-SCOPE` until a source coupling family and dual observables are constructed. |
| U-duality | no exceptional charge lattice | `OUT-OF-SCOPE`. |
| Mirror symmetry / Landau--Ginzburg duality | projective-horizon LG duality core | `APPLIED-LEAN CANDIDATE`: exact projective algebra exists; physical Calabi--Yau/worldsheet identification remains external. |
| Modular invariance | elliptic-Gamma/orbifold modules | `BLOCKED`: modular-looking special functions do not prove a string partition-function modular law. |
| Genus expansion `sum_g g_s^(2g-2) A_g` | finite-product/sum closure | `NO-GO` for every fixed genus truncation; `BLOCKED` for the infinite completion because convergence, nonperturbative definition, and a source observable are absent. |
| Green--Schwarz anomaly cancellation | finite anomaly shells | `OUT-OF-SCOPE` without the ten-dimensional anomaly polynomial, gauge/gravitational curvatures, and two-form transformation law. |
| Chan--Paton factors | finite matrix and group-action APIs | `BLOCKED`: no endpoint state category or open-string gauge algebra. |
| Tachyon condensation / string-field potential | no string field algebra | `OUT-OF-SCOPE`; a scalar potential analogy cannot stand in for the star-product action. |
| Generalized string uncertainty relation | HilbertMetric uncertainty/Gram shells | `NO-GO` for HT: the displayed algebraic inequality cannot create a differential-transcendence source; no physical position/T-dual measurement pair is instantiated. |
| Topological-string/Gromov--Witten expansion | period and elliptic-Gamma infrastructure | `BLOCKED`: special-function resemblance is insufficient without moduli-space invariants and the exact generating series. |
| Worldsheet beta functions / spacetime field equations | finite RG row | `NO-GO` for HT from a finite closed beta system; actual sigma-model coefficients are absent. |
| D-branes and Dirac--Born--Infeld action | no DBI/exterior-form carrier | `OUT-OF-SCOPE`. |
| Hagedorn density/temperature | geometric CDD finite-real TBA obstruction | `APPLIED-PAPER/NO-GO`: finite real TBA does not close the desired HT QFT; complex continuation and central charge remain open. |
| Cardy formula / CFT central charge | thermal-CFT Gamma response | `BLOCKED`: response kernels exist, but no state-counting theorem or central charge is constructed. |
| AdS/CFT / holographic duality | multiple horizon cards | `BLOCKED` unless an actual bulk/boundary reporter is built; “horizon” terminology is not itself AdS/CFT. |
| String field BRST/BV master equation | BRST row | `BLOCKED`: bounded BRST/Hodge algebra is reusable, but no string field star algebra/action exists. |

Canonical external anchors include the Wikipedia pages for the
[Polyakov action](https://en.wikipedia.org/wiki/Polyakov_action),
[string theory](https://en.wikipedia.org/wiki/String_theory),
[T-duality](https://en.wikipedia.org/wiki/T-duality),
[S-duality](https://en.wikipedia.org/wiki/S-duality),
[mirror symmetry](https://en.wikipedia.org/wiki/Mirror_symmetry_%28string_theory%29),
[Veneziano amplitude](https://en.wikipedia.org/wiki/Veneziano_amplitude), and
[bosonic string theory](https://en.wikipedia.org/wiki/Bosonic_string_theory), plus the
[GSO projection](https://en.wikipedia.org/wiki/GSO_projection) and
[double-copy theory](https://en.wikipedia.org/wiki/Double_copy_theory).

## M-theory census

| Law or formula family | Corpus match | Verdict and exact effect |
|---|---|---|
| Eleven-dimensional supergravity action | no spin/vielbein/3-form field theory | `OUT-OF-SCOPE`: importing the formula would create no project theorem. |
| Supermembrane worldvolume action | no membrane embedding or kappa-symmetry carrier | `OUT-OF-SCOPE`. |
| Four-form Bianchi identity `dF_4=0` | Koszul/exterior analogies only | `BLOCKED`: no differential-form source or spacetime manifold. |
| Four-form equation `d*F_4 + (1/2)F_4 wedge F_4=0` | quadratic constraint analogies | `BLOCKED`: the Chern--Simons term cannot be represented by a generic square wrapper. |
| M2 electric / M5 magnetic duality | no brane charge lattice | `OUT-OF-SCOPE`. |
| M2/M5 BPS near-horizon geometries | positive master constraints only | `BLOCKED`: no source central charge, tension, or supergravity solution. |
| M2/M5 tension and Planck-length scaling | scale/period arithmetic only | `NO-GO` for HT: the dimensional power laws are algebraic; no brane state space is present. |
| Flux quantization / Chern--Simons level | integral lattice and cohomology analogies only | `BLOCKED`: no differential cohomology class, four-form flux, or eleven-manifold. |
| Type-IIA strong-coupling/11th-circle relation | scale/period modules | `OUT-OF-SCOPE` without string coupling and compactification data. |
| BFSS matrix-model conjecture | finite matrix/principal-symbol modules | `BLOCKED`: finite matrix algebra is not a large-`N` M-theory limit; no convergence theorem exists. |
| IKKT matrix model | same | `OUT-OF-SCOPE` absent action and large-`N` limit. |
| ABJM Chern--Simons-matter / `AdS4 x S7` duality | no ABJM field content | `OUT-OF-SCOPE`. |
| Freund--Rubin compactification | no 11D form/Einstein equations | `OUT-OF-SCOPE`. |
| Horava--Witten `E8 x E8` boundary anomaly cancellation | finite anomaly/constraint shells | `OUT-OF-SCOPE` until the boundary gauge fields, anomaly polynomial, and modified Bianchi identity are source-defined. |
| Six-dimensional `(2,0)` theory / AGT and geometric-Langlands reductions | no source SCFT or compactification functor | `OUT-OF-SCOPE`; projective or period analogies cannot instantiate these conjectural correspondences. |
| Killing-spinor/BPS calibration equations | positive master constraints only | `BLOCKED`: the spin bundle, supercovariant derivative, and calibrated charge are absent. |
| `G2`/Calabi--Yau compactification | period and mirror infrastructure | `BLOCKED`: no torsion-free special-holonomy metric or compactification spectrum is constructed. |
| M-theory S/T/U-duality web | reciprocal/projective algebra only | `BLOCKED`: useful only after source observables and an invariant reporter are defined. |

External anchors are [M-theory](https://en.wikipedia.org/wiki/M-theory),
[eleven-dimensional supergravity](https://en.wikipedia.org/wiki/Eleven-dimensional_supergravity),
[matrix theory](https://en.wikipedia.org/wiki/Matrix_theory_%28physics%29), and
[ABJM theory](https://en.wikipedia.org/wiki/ABJM_superconformal_field_theory).

## Supersymmetry census

| Law or formula family | Corpus match | Verdict and exact effect |
|---|---|---|
| Super-Poincare anticommutator | bounded `N=2` BRST/Hodge algebra | `APPLIED-LEAN`: equal-square Hermitian supercharges and anticommutation are checked; this is a static bounded `N=2` algebra, not a relativistic representation. |
| Nilpotent complex charge `Q^2=0`, `H={Q,Q*}` | `BRSTHodgeConstraint` | `APPLIED-LEAN`: kernel intersection, Ward values, commutation, projection-corner nilpotence, and one-equation Green discharge are axiom-audited. |
| Supersymmetry transformations / closure of the algebra | bounded `N=2` supercharges | `APPLIED-LEAN` only for the static bounded algebra; `BLOCKED` for off-shell spacetime fields, translations, and auxiliary-field closure. |
| Superspace covariant-derivative anticommutators | finite Clifford/principal-symbol modules | `BLOCKED`: no Grassmann/supermanifold carrier or physical superfield representation. |
| SUSY partner Hamiltonians `Q*Q`, `QQ*` | finite master constraint | `APPLIED-LEAN`: exact intertwining and trace equality. |
| Ordinary Witten index `Tr((-1)^F exp(-beta H))` | fermion-number selector card | `NO-GO`: finite/trace-class partner traces cancel and factor through a blind quotient; positive survivor is a possible non-Fredholm zero-energy spectral-shift defect. |
| Non-Fredholm regularized Witten index | same card | `LIVE`: requires a source-built coupled Sonin/prime--Gamma supercharge and trace-class relative resolvent difference. |
| BPS bound `M>=|Z|` | positive master constraints | `BLOCKED`: positivity algebra is available, but no source central charge or mass operator; a generic shifted-square theorem would be parent-grade only. |
| Bogomolny first-order equations | theta Morse zero mode | `APPLIED-LEAN` in one-dimensional SUSY-QM form, not as monopole gauge fields. |
| SUSY-QM factorization | theta-cusp Morse ground state | `APPLIED-LEAN`: exact supercharge, zero mode, partner potentials, and Born observable. |
| Shape invariance | same | `APPLIED-LEAN`: exact theta-specific partner shift; remaining buffered moments are not proved. |
| Witten Laplacian / Hodge decomposition | BRST/Hodge and theta cards | `APPLIED-LEAN`; full source-specific spectral-gap consequence remains open. |
| Supercurrent Ward identity | generic constraint Ward API | `BLOCKED` for a source supercurrent, stress tensor, and contact terms; the abstract Ward value is already available once those are built. |
| Bose--fermi mass supertrace and Coleman--Weinberg supertrace | graded-matrix trace and partner-trace theorems | `APPLIED-LEAN` for finite supercommutator cancellation; `BLOCKED` for physical mass matrices and a renormalized effective potential. |
| Goldstino theorem / super-Higgs mechanism | positive master constraint only | `OUT-OF-SCOPE` until spontaneous SUSY breaking, a supercurrent pole, local supergravity, and gravitino mass are defined. |
| Supersymmetric localization / Q-exact deformation | Ward/ideal invariance only | `BLOCKED`: no path-integral measure or fixed-point formula; ideal invariance is not localization. |
| Holomorphic nonrenormalization | meromorphic Gamma/HT field | `BLOCKED`: holomorphy alone does not identify a QFT superpotential or quantum correction map. |
| `N=4` vanishing beta function | finite RG no-go | `OUT-OF-SCOPE`: no SYM theory is defined; `beta=0` would be DA, not an HT source. |
| NSVZ beta function | finite RG/quotient APIs | `NO-GO` as an HT source when treated as a finite differential flow; no supersymmetric gauge theory or exact anomalous dimension is instantiated. |
| F-terms, D-terms, superpotential | projective Landau--Ginzburg cards | `BLOCKED/APPLIED-CANDIDATE`: algebraic LG duality exists; physical superspace identification remains external. |
| Seiberg--Witten curve and periods | period/elliptic-Gamma infrastructure | `BLOCKED`: no source gauge theory, prepotential, or BPS spectrum. |
| Nekrasov instanton localization | partition/elliptic-Gamma families | `BLOCKED`: special-function resemblance is insufficient without the exact instanton partition formula. |
| BPS protection/nonrenormalization | no central-charge family | `BLOCKED`; cannot discharge a project hypothesis without source mass/charge operators. |
| Superconformal Ward identities | thermal-CFT Gamma response | `APPLIED-LEAN` to an exact reflected-Gamma kernel; no full SCFT is claimed. |
| Topological twist/cohomology | Koszul/BRST cohomology | `BLOCKED`: the algebraic complex exists, but no source twist or four-manifold invariant. |
| R-symmetry and fermion-parity projection | finite group averages | `APPLIED-LEAN` to the abstract projection surface; `BLOCKED` for a source supersymmetric representation and anomaly check. |
| Soft SUSY breaking / MSSM mass and coupling relations | no MSSM field content | `OUT-OF-SCOPE`; parameter relations and phenomenological values do not define a project variable-channel theorem. |

External anchors include the Wikipedia pages for
[supersymmetry](https://en.wikipedia.org/wiki/Supersymmetry),
[supersymmetry algebra](https://en.wikipedia.org/wiki/Supersymmetry_algebra),
[supersymmetric quantum mechanics](https://en.wikipedia.org/wiki/Supersymmetric_quantum_mechanics),
[Witten index](https://en.wikipedia.org/wiki/Witten_index),
[BPS bound](https://en.wikipedia.org/wiki/Bogomol%27nyi%E2%80%93Prasad%E2%80%93Sommerfield_bound),
[supersymmetric localization](https://en.wikipedia.org/wiki/Supersymmetric_localization),
[nonrenormalization theorems](https://en.wikipedia.org/wiki/Supersymmetry_nonrenormalization_theorems), and
[Seiberg--Witten theory](https://en.wikipedia.org/wiki/Seiberg%E2%80%93Witten_theory), together with
the [supertrace](https://en.wikipedia.org/wiki/Supertrace).

## Live programme extracted from the census

1. **Closed/open string differential boundary — COMPLETE:** exact paper proof, hostile formula
   review, Lean module, axiom audit, index/lint, final build, and stage-3 promotion all pass.
2. **LSZ/Haag--Ruelle Kolchin transfer:** scientifically highest QFT gap, but it requires a genuine
   compact-local reporter; no Lean wrapper until the analytic theorem exists.
3. **Cosmological wavefunction transfer:** coefficient specialization is ready; source construction,
   gauge-invariant in-in survival, and observation stability are the physical open core.
4. **Non-Fredholm Witten-index defect:** finite trace cancellation is closed; construct the source
   supercharge and relative resolvent before formal spectral-shift work.
5. **QED Ward--Takahashi HT transfer:** potentially new, but only after an actual inverse propagator,
   contracted vertex, and derivation/translation-compatible reporter are defined.
6. **BRST/Hodge source audit — COMPLETE:** the bounded operator surface and both direct consumers
   are checked, axiom-audited, optimized, and promoted; source-specific `P` and `G` construction
   remains separate.

## Formula-level primary-source audit of every `LIVE` row

The audit below checks the load-bearing formula or construction, not merely the topic name.  It
also records why the parent formula does or does not discharge a project interface.

| Live family | Primary formula/construction checked | Project verdict after formula audit |
|---|---|---|
| Ward--Takahashi / QED vertex | The gauge identity has the finite-difference form `q_mu Gamma^mu(p+q,p) = S^{-1}(p+q)-S^{-1}(p)`; explicit vertex work separates the longitudinal part fixed by this identity from transverse components.  Sources: Takahashi's identity as used in Kizilersu--Reenders--Pennington, Phys. Rev. D 52 (1995), 1242, and the explicit inverse-propagator finite-difference derivation in Phys. Rev. D 101 (2020), 074507. | The existing Ward/ideal API can consume the contraction only after `S^{-1}` and `Gamma` are source-built in one differential field and translation is proved compatible with the chosen derivation.  Neither object exists in the corpus, so the row remains `LIVE`; an abstract Ward wrapper would be conditional theatre. |
| LSZ, Haag--Ruelle, Wightman locality | Lechner's factorizing-QFT construction first builds wedge-local fields, then obtains compact-local observable algebras from modular nuclearity, proves the inverse-scattering identification and asymptotic completeness.  Source: arXiv:math-ph/0601022. | This validates the physical source category already used by the geometric CDD cards, but it does not supply the missing derivation-compatible map from intrinsic compact-local connected four-point data to the elastic amplitude.  The wedge-PFG coefficient precursor is exact; the compact-local reporter remains `LIVE`. |
| Cosmological total-energy singularity and optical theorem | At vanishing total energy, the perturbative wavefunction's scattering facet reduces to the flat-space S-matrix; unitarity gives relations among wavefunction coefficients and links total-energy poles to flat-space amplitudes.  Sources: Benincasa, arXiv:1811.02515; Goodhew--Jazayeri--Pajer, arXiv:2009.02898. | The formal leading-Laurent-coefficient theorem already transfers `HT(A_flat)` to `HT(Psi)`.  The primary results are perturbative parent input, not a source-built HT cosmology.  Local cosmological realization, gauge-invariant in-in survival, and observational stability remain `LIVE`. |
| Cosmological-collider tower | A massive field produces squeezed-limit power-law/oscillatory mass and spin signatures; ordinary Bunch--Davies heavy signals carry Boltzmann suppression, while non-BD states can remove it.  Sources: Arkani-Hamed--Maldacena, arXiv:1503.08043; Yin, arXiv:2309.05244.  Continuous spectra have a distinct damped squeezed limit: Aoki, arXiv:2301.07920. | These sources justify the single-frequency physics and show that state choice changes the suppression; they do not force the exact geometric spectrum `mu_k=p^k` or shell-universal residues.  The Mahler tower therefore remains `LIVE`, with source selection—not the HT proof—as the open core. |
| Non-Fredholm Witten index | For `H_1=D^*D`, `H_2=DD^*`, the resolvent-regularized index is `lim_(lambda->0-) (-lambda) Tr((H_1-lambda)^{-1}-(H_2-lambda)^{-1})` and equals a zero-energy spectral-shift boundary value under trace-class/Lebesgue-point hypotheses.  Sources: Carey--Gesztesy--Levitina--Sukochev, arXiv:1505.04895; explicit model arXiv:1509.01356. | This is the correct positive survivor of the finite-supertrace no-go.  The project lacks the coupled Sonin/prime--Gamma supercharge, relative trace-class resolvent theorem, and spectral-shift layer, so the route remains `LIVE`; none of those hypotheses is discharged by the bounded BRST module. |

This completes the primary-formula review for every row marked `LIVE`.  It closes no source gap by
fiat: all five surviving routes retain an explicitly named construction or analytic theorem.

## Focused search log

The formula census used query families combining each domain with `laws`, `equations`, `identity`,
`action`, `duality`, and the named mechanisms above.  Novelty searches for the selected theorem used
`Virasoro-Shapiro differentially algebraic`, `Virasoro-Shapiro hypertranscendental`,
`Virasoro-Shapiro differential transcendence`, and `closed string amplitude differential algebra
Gamma`.  The returned literature concerns amplitude bootstraps, Regge behavior, KLT/single-valued
periods, or transcendental weight, not differential algebra.  This negative result is not a proof of
priority.

A second canonical-page sweep explicitly tested the previously omitted families `CPT`,
`spin-statistics`, canonical `CCR/CAR`, `Wick/Isserlis`, `Faddeev-Popov`, `OPE`, `Haag`,
`Reeh-Schlieder`, tree-level QED cross sections, infrared QED cancellation, loop quantum cosmology,
Mukhanov--Sasaki, WKB/BKL, worldsheet OPE, GSO, BCJ, genus expansion, Green--Schwarz, M-theory flux
and boundary anomaly laws, superspace closure, supercurrent, supertrace, Goldstino, NSVZ, and soft
breaking.  Each now has an explicit row and corpus verdict.  The LQC recurrence was checked against
Ashtekar--Pawlowski--Singh, arXiv:gr-qc/0607039: its step-4 volume recurrence is genuine, but its
physical state is a lattice sequence, so differential hypertranscendence requires an intrinsic
analytic interpolation that the source does not supply.

## Gates

- [x] Read live formal source, generated API, stage-3 cards, stage-2 cards, and failed routes first.
- [x] Freeze a reproducible Wikipedia/search boundary and verdict vocabulary.
- [x] Give every canonical formula family found in both canonical-page sweeps an explicit application verdict.
- [x] Select one source-pure disjoint theorem and prove it on paper.
- [x] Implement its exact unconditional Lean surface and pass a direct single-file check.
- [x] Complete formula-level primary-source review for every `LIVE` row.
- [x] Complete hostile formula and external novelty review of the Virasoro--Shapiro claim; an
  independent expert review remains a publication gate.
- [x] Validate the BRST/Hodge source-only modules and direct consumers.
- [x] Axiom-audit, regenerate public indexes, run repository lint, and perform the final exact
  module builds while launching at most one owned Lean process at a time.
- [x] Promote only claims whose exact stated gate is met; keep LSZ, cosmology, and non-Fredholm
  constructions explicitly open.

## Log

- 2026-07-20 -- census opened after the internal duplicate audit; first frozen web pass completed,
  Virasoro--Shapiro differential boundary selected as the disjoint exact theorem, and the main
  hypothesis-discharge gaps localized.
- 2026-07-20 -- every `LIVE` row was checked against its load-bearing primary formula.  The checks
  confirmed five precise source/analytic open cores and rejected wrapper-only promotion.  The
  BRST/Hodge module plus semilocal-projection and seam-trace consumers passed direct source checks;
  their capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-20 -- generated API/index consistency, repository lint, five Virasoro--Shapiro capstone
  axiom audits, eight BRST/consumer capstone axiom audits, and all four exact final module builds
  pass.  The census is promoted to stage 2 `needs-audit`; open physical source constructions remain
  at stage 1 and the new theorem remains a novelty candidate rather than a priority claim.
- 2026-07-20 -- a hostile second canonical-page sweep added the omitted foundational, scattering,
  infrared, LQC, worldsheet, double-copy, M-theory, and SUSY-breaking formula families.  The LQC
  difference equation was primary-source checked and rejected as an immediate HT theorem because
  its physical carrier is discrete and no canonical analytic interpolation is selected.
