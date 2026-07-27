# Deninger source-native arithmetic cohomology roadmap

- **ID:** `deninger-source-native-arithmetic-cohomology-roadmap`
- **Stage:** 1-in-progress
- **Type:** MASTER CONSTRUCTION LEDGER
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Statement:** active dependency chain from Deninger's invariant
  leafwise sheaf to RH, excluding CCM/Gamma/Xi-defined source objects.

## Scope lock

The source is Deninger's arithmetic dynamical program:

1. rational-Witt suspension and degreewise invariant leafwise sheaf;
2. Deninger's true-to-approximate derived coefficient
   \(R\alpha_*\mathcal G\);
3. generic Milnor/Steinberg correction and arithmetic
   Rost--Schmid residues;
4. standard finite correspondences and power push/pull;
5. real Arakelov/Milnor--Witt orientation boundary;
6. complex/\(K_{\mathbb R}\)-odd Kähler--Riemann leafwise Hodge
   theory for \(\mathbb Q\), with genuinely no-real quaternionic
   descent required for the all-number-fields extension;
7. prime-orbit/real-fixed-point Lefschetz trace;
8. regularized determinant and spectral divisor.

CCM, Gamma-kernel Hilbert models, and Hilbert spaces indexed by Xi
zeros are not source inputs.  Existing analytic Xi formalization is
used only after the source trace/determinant has been constructed, as
an independently proved comparison target.

## Dependency chain

### 1. Raw Deninger approximation

Source definition:
\[
 \mathscr R_X
 =
 (\pi_*\mathscr R_{\widetilde X})
   ^{\mathbb Q_{>0}}.
\]

- **Proved:** Deninger's definition; \(H^0=\mathbb R\) for his
  arithmetic systems.
- **Proved obstruction:** raw rational-Witt cohomology violates the
  Steinberg relation in degree two, so it cannot be the missing
  arithmetic coefficient.
- **Open:** smooth complete locally convex resolution and
  quotient-adapted derived sections.
- **Card:** `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.

### 2. True-to-approximate derived coefficient

Deninger's source prescription is
\[
 \mathscr E_{\mathrm{Den}}=R\alpha_*\mathcal G,\qquad
 R\Gamma_{\mathrm{Den},c}
 =R\Gamma_c(X_{\mathrm{Den}},\mathscr E_{\mathrm{Den}}),
\]
where the unavailable true space maps to the rational-Witt
approximation.  The coefficient complex may be constructed directly.

- **Proved cover-sheaf construction:**
  \[
   \widetilde{\mathscr E}_{\mathrm{Den},F}
   =
   \mathscr T_{\widetilde X_F}
   \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
   \underline{\mathcal K}^{M}_{F,\mathbb R}.
  \]
  It is a genuine equivariant Tate-graded derived sheaf with
  restriction, Galois, power, and weight maps.
- **Proved chart target:** real shape formality and Milnor
  unit-amalgamation compute the expected chartwise derived-section
  algebra; for algebraic cyclotomic fields it has amplitude
  \([0,1]\).
- **Proved obstruction:** higher stalk Tor survives, so neither global
  cochains nor their Postnikov truncation can define the source sheaf.
- **Proved analytic comparison:** the pro-Stein relative-cell theorem
  computes derived sections in the selected leafwise analytic
  category.
- **Primary corrected coefficient:** form degreewise coarse invariant
  Tate--Milnor coefficients on the actual generic and prime strata,
  push them to Deninger's actual coarse space, and define
  \[
   \mathscr E_{\mathrm{arith}}
   =
   \operatorname{Fib}\!\left(
     Rj_*\mathscr A_\eta
     \to
     \left(
       \widehat{\bigoplus}_p'Ri_{p,*}\mathscr A_p(-1)
       \widehat\oplus\mathscr B_\infty
     \right)[-1]
   \right).
  \]
  `DAC_DERIVED_STRATUM_FIBER_GLOBAL_SECTIONS` proves that its
  hypercohomology is the shifted three-term residue totalization.
- **Open:** arithmetic-operation coherence, full analytic real Betti
  lift, coherent collar independence, reduced leafwise comparison,
  and non-scalar middle completion.  Finite sheaf residues, one-prime
  comparison, strict all-prime pushforward, real Kummer boundary, and
  completed Arakelov trace-kernel exactness are proved.  No equivalence
  between coarse and derived quotient descent is sought.
- **Cards:** `DAC_TRUE_TO_APPROXIMATE_DERIVED_COEFFICIENT`,
  `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`,
  `DAC_DERIVED_STRATUM_FIBER_GLOBAL_SECTIONS`,
  `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`,
  `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`,
  `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.

### 3. Algebraic transfer source

Deninger's exact 2025 theorem is
\[
 W_{\mathrm{rat}}(\mathcal O(X))
 \cong
 \mathbb Z_{\mathrm{tr}}(\mathbb A^1)(X)/
   \mathbb Z_{\mathrm{tr}}(0)(X)
\]
on normal Noetherian affine schemes.

- **Proved:** represented rational-Witt coefficient; finite-flat/qfh
  comparisons in their stated domains; \(F_n=(x^n)_*\),
  \(V_n=(x^n)^*\).
- **Retired:** invented rational-Witt correspondence topos.
- **Open:** analytic character-evaluation realization on the coarse
  suspension, comparison with the Milnor Steinberg correction, and a
  separate Milnor--Witt real-orientation comparison.
- **Card:** `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION`.

### 4. Local coefficient topology

On the Allcock--Vaaler place space:
\[
 f_\alpha(y)=\log\|\alpha\|_y.
\]

- **Proved:** field-independent positive \(L^2\) Kummer form; exact
  place-average valuation residues; normalized norm contractions;
  unique half-Tate weight-one scaling.
- **Retired:** bare \(L^2\) arithmetic coefficient, because product
  formula is dense rather than closed and centered Kummer power is
  scalar.
- **Proved topology scale:**
  \[
  \mathcal S_{\mathrm{Kum}}
   \subset E_{\mathrm{Kum}}
   \subset L^2
   \subset E_{\mathrm{Kum}}'
   \subset\mathcal S_{\mathrm{Kum}}'.
  \]
- **Proved boundary completion:** actual pro-log collar forms give a
  strict section on packet mean-zero residues; together with the real
  Kummer boundary, the completed residue image is the Arakelov trace
  kernel.
- **Proved real lift:** `DAC_ARCHIMEDEAN_KUMMER_HOMOLOGY_CURRENT` and
  `DAC_PRO_STEIN_REAL_BETTI_DERIVED_LIFT` construct the analytic real
  boundary on the relevant pro-Stein coefficient, naturally for
  powers, Galois maps, norms, finite correspondences, and the mixed
  completion.  Collar right inverses are noncanonical proof devices;
  residue and trace-kernel are canonical.
- **Cards:** `DAC_ADELIC_PLACE_AVERAGE_RESIDUE`,
  `DAC_ADELIC_KUMMER_GELFAND_TRIPLE`,
  `DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE`,
  `DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT`.

### 5. Arithmetic dimension and endpoints

The base is the regular arithmetic curve, so its Rost--Schmid complex
has generic and closed-point columns.

- **Proved:** local algebraic Milnor amplitude \([0,1]\); the correctly
  shifted residue fibre has degrees \(0,1,2\); abstract cup/trace
  descent laws.
- **Proved endpoint:** real-linearized Arakelov divisor sequence
  \[
  0\to(K^\times/\mu_K)\otimes\mathbb R
  \to\operatorname{Div}_{\mathrm{Ar}}(K)_\mathbb R
  \to\mathbb R(-1)\to0.
  \]
- **Proved relative reduction:** the rational
  Milnor--Arakelov complex has \(H^0=\mathbb R\),
  \(H^1=0\), \(H^2=\mathbb R(-1)\).  For any successful Deninger
  complex, the cone of its endpoint map has cohomology only in degree
  one and equals the sought spectral \(H^1\).
- **Proved analytic endpoint:** strict completed finite-plus-real
  residue has closed image equal to the Arakelov trace kernel.
- **Proved analytic middle model:** Meyer's Poisson--zeta operator
  \[
   Z:H_\cap\hookrightarrow H_-,\qquad Zf(x)=\sum_{n\ge1}f(nx),
  \]
  is a strict closed embedding defined analytically from the
  positive-integer dilation semigroup.  Its quotient
  \(M_\zeta=H_-/Z(H_\cap)\) is nuclear Frechet and supplies the sought
  nontrivial middle group.
- **Proved source obstruction:** ordinary scalar pullback along
  Deninger's Frobenius deck relation is the identity after descent, so
  its partial sums are \(N\) times the section and cannot realize
  \(Z\).
- **Proved source realization:** Hilbert-bounded logarithmic-modulus
  characters form a canonical dense Galois/Frobenius-stable refinement
  of the generic rational-Witt character space.  On its suspension,
  \(x([P,u])=u\|\ell_P\|\) is a global radial coordinate and
  \[
  [F_nP,u]=[P,nu]=\phi^{\log n}[P,u].
  \]
  Therefore scalar pullback by \(\phi^{\log n}\), unlike deck
  pullback, is exactly \(f(x)\mapsto f(nx)\).
- **Proved angular reduction:** bounded characters split as unitary
  phase times Hilbert modulus.  The nonzero modulus is
  \(S(H_{\rm Kum})\times\mathbb R_{>0}\), and the
  infinite-dimensional sphere is contractible.  Hence it contributes
  no ordinary modulus-angular derived class; unitary phase remains the
  Tate--Milnor coefficient and radius zero remains the real boundary.
  `DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION` upgrades
  this to a continuous chain homotopy after every completed source
  topology.
- **Proved global positive-radius Kähler orbit collar:** every positive
  equivariant radius trivializes its flow space as
  \(x^{-1}(1)\times\mathbb R_{>0}\).  For the Hilbert--Kummer radius,
  the canonical half-density circle
  \[
    \{(p,z):|z|^2=x(p)\}
      \cong x^{-1}(1)\times\mathbb C^\times
  \]
  supplies complex orbit leaves with \(z\mapsto e^{t/2}z\), Kähler area of
  weight one, positive one-form Hodge star, exact Poisson pullbacks,
  and Meyer's critical radial measure.  No conjectural identification
  with the unitary-character phase or Gamma-rank coefficient is used.
  These leaves are closed and the flow is tangent, so this collar is
  only the local metric model.
- **Proved generic arithmetic foliation:**
  `DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION` uses the modulus Euler
  field and Kummer--Kronecker phase field.  Their bracket is
  \([A,K]=K\); Deninger's flow is transverse and scales the leaf
  Kähler form with weight one.
  `DAC_RESIDUAL_DENSE_KUMMER_LEAVES` proves a dense \(G_\delta\) of
  leaves is dense in the unitary phase direction.
- **Proved local arithmetic-boundary Hodge atoms:**
  `DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION` extends the oriented
  conformal leaf and degree-one star over every finite/pro-log prime
  collar as a complete cusp, with exact deck, flow, and residue
  compatibility.  `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX` extends
  it over the real quotient; orientation reversal forces the sign
  local system and gives the positive odd \(J=*c\).
  `DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP` proves the generic affine
  planes converge to these prime-normal atoms on the actual residue
  locus.
- **Proved local arithmetic Hodge domains:**
  `DAC_STANDARD_CHEEGER_MIDDLE_EXTENSION_ARITHMETIC_NO_GO` proves that
  ordinary Cheeger \(L^2\), although canonical because the normal
  links are Witt circles, deletes every nonzero logarithmic residue.
  `DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY` replaces it by the
  exact extended-\(L^2\) prime domain, and
  `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN` constructs the
  unitary-face relative trace quotient, Dirichlet decomposition,
  positive Hodge defect, and Lagrangian Calderón graph.
- **Proved finite derived Hodge compatibility:**
  `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY` shows that a positive
  Calderón graph meets every finite linear Milnor conormal
  transversely, and `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` gives the
  explicit Euler contraction of its full finite derived critical
  cdga.  Thus no finite chart contributes spurious
  position--momentum cohomology; nonuniform nuclear/coarse descent is
  load-bearing.
- **Proved source Green transgression:**
  `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION` identifies Meyer's cutoff
  commutator trace with the multiplicative Green cocycle and isolates
  the \(Z\)- and Fourier-conjugated correction operators that generate
  global cross-ray incidence.
  `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR` proves the source
  positive leg need only be almost-complemented modulo the nuclear
  trace ideal; exact projectors are deferred to positive Hodge
  completion.
- **Proved geometric endpoints:** for the radial lift
  \(Rf(z)=f(|z|^2)\),
  \[
    Rf(0)=f(0),\qquad
    \int_{\mathbb C}Rf\,\omega=(\pi/2)\mathcal Ff(0).
  \]
  Hence Meyer's \(H_\cap\) is exactly the common kernel of cone-apex
  restriction and leafwise top-degree Kähler trace.  The second
  condition is not an extra Fourier boundary point.
- **Proved assembled endpoint/middle complex:**
  `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY` gives
  \(H^0=\mathbb C\), \(H^1=M_\zeta\), and
  \(H^2=\mathbb C(-1)\), with ordinary and reduced cohomology equal.
- **Proved relevant-complex comparison:**
  `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION` identifies the
  pro-Stein \(R\alpha_*\mathcal G\) totalization strictly with the
  assembled Poisson--zeta complex.
- **Open:** `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`:
  glue the proved local domains through every Tate--Milnor relative
  cell into a closed global Lagrangian Cauchy relation, identify its
  Green supertrace with Paugam's cup form, and prove strong-dual
  spectral faithfulness.  Positive completion is now reduced to the
  exact radical conjecture `DAC_GLOBAL_GREEN_ENERGY_RADICAL`: summed
  local Green energy vanishes exactly on closed middle boundaries.
  Nonuniform summable passage, constrained Euler--Lagrange
  graph/conormal reduction, finite complementary transversality, and
  local full-Cauchy uniqueness are proved; strict
  Rost--Schmid/Arakelov classification remains.  The minimal RH
  condition is now
  `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`: construct a
  source-dense smooth Hodge core preserved by every off-axis centered
  resolvent.  `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY` then constrains
  Meyer's order-zero and generalized-jet functionals without requiring
  them to be Hilbert-bounded.  The earlier Riesz condition remains a
  stronger sufficient criterion.  The exact RH-bearing polarization statement is
  `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`: source Calderón
  relations must reproduce Meyer's nuclear relative trace and become
  Paugam's upper/lower splitting only after positive Hodge completion.
  Ordinary finite-rank critical-\(L^2\) reduction is excluded by
  `DAC_FINITE_RANK_TWISTED_CRITICAL_L2_NO_GO`.
- **Cards:** `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`,
  `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`,
  `DAC_TWO_COLUMN_CUP_TRACE_TOTALIZATION`,
  `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`,
  `DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION`,
  `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`,
  `DAC_SCALAR_SUSPENSION_POISSON_TRANSFER_NO_GO`,
  `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`,
  `DAC_DENINGER_FLOW_POISSON_DILATION`,
  `DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION`,
  `DAC_DENINGER_HERMITIAN_RADIAL_LINE_POISSON_HODGE`.

### 6. Source middle hypercohomology

Let \(a:X_W\to\operatorname{Spec}\mathbb Z\) be Deninger's arithmetic
projection and
\[
 \mathscr E_{\mathrm{Den}}
 =
 (\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}}.
\]

- **Proved:** `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE`; the corrected
  degreewise invariant coefficient is a genuine dg-algebra sheaf and
  all commuting source operations descend.
- **Proved source localization:**
  `DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE`; Deninger's character
  space, common Frobenius colimit, suspension, and underived invariant
  coefficient restrict canonically to every
  \(\operatorname{Spec}\mathbb Z[1/N]\).
- **Proved cofinite arithmetic row:**
  `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`; on every
  \(\operatorname{Spec}\mathbb Z[1/N]\), generic prime coordinates
  restrict split-surjectively to primes not dividing \(N\), with
  kernel the \(N\)-unit coordinates.  The sequence stays strict in
  the mixed weighted \(L^1/L^2\) completion.
- **Proved generalized-log prime purity input:**
  `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`; filtered finite
  divisorial log structures construct the disjoint prime normal lines,
  direct-sum residues, and Tate-normalized rational-power action.
  Deninger's Proposition 11.7 identifies their supports with his
  generalized prime divisors.
- **Proved source recollement basis:**
  `DAC_SPECZ_COFINITE_RECOLLEMENT_BASIS`; the actual Zariski topology
  of \(\operatorname{Spec}\mathbb Z\) is the cofinite
  generic-prime star, and every finite prime boundary gives an actual
  open--closed recollement.
- **Optional raw-coarse comparison:**
  `DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`.
  It asks whether ordinary hypercohomology of the raw nonproper coarse
  invariant sheaf agrees with the relevant pro-Stein coefficient.
  Generalized-log analytic purity and strict all-prime passage are
  proved; only the ordinary coarse comparison and its possible
  derived-limit defect remain.  Neither is construction-critical.
- **Construction correction:** the global raw-coefficient comparison
  is now optional.  The construction-critical source is
  `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`, which glues the
  pro-Stein relevant generic coefficient and actual prime stratum
  coefficients by their derived residue fibre.  Finite and real
  residues, strict boundary pushforward, local packet analysis,
  three-term amplitude, operations, and endpoint exactness are proved.
- **Consequence:** the resulting source hypercohomology has degrees
  \(0,1,2\).  Its middle group is defined intrinsically as
  \(H^1_{\mathrm{arith}}(X_W,\mathscr E_{\mathrm{Den}})\), not as a
  quotient-stack comparison fiber.
- **Exact analytic comparison target:**
  `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON` asks for a
  flow-equivariant quasi-isomorphism from this source hypercohomology
  to the Poisson--zeta three-term complex.  Its generic differential is
  \(\sum_{n\ge1}F_n^{-1}=Z\); Poisson summation glues the real collar,
  while the finite Euler factors agree with the prime residue maps.
- **Diagnostic only:** scalar coarse/derived comparison no-go and
  Frobenius homotopy cocycles remain obstruction tests; they are not
  construction dependencies.
- **Cards:** `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE`,
  `DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE`,
  `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`,
  `DAC_SPECZ_COFINITE_RECOLLEMENT_BASIS`,
  `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`,
  `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`,
  `DAC_DERIVED_STRATUM_FIBER_GLOBAL_SECTIONS`,
  `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`,
  `DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`,
  `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`,
  `DAC_LOCAL_FROBENIUS_HOMOTOPY_DEFECT`,
  `DAC_FROBENIUS_COHERENCE_DEFECT_SPECTRUM`.

### 7. Hodge realization

Deninger--Singhof prove for a dense-leaf Kähler--Riemann foliation with
\((\phi^t)^*[\omega]=e^t[\omega]\):
\[
 \Theta_q=\frac q2+S_q,\qquad S_q^*=-S_q.
\]

- **Proved:** leafwise reduced Hodge decomposition, Poincaré duality,
  polarization, and conformal-flow purity under their geometric
  hypotheses; abstract three-term Hodge implication to RH after
  spectral inclusion.  Paugam supplies the unconditional alternating
  middle pairing and odd sign--conjugation \(K_{\mathbb R}\)-operator
  \(C^2=-1\) on the nonreal Connes--Meyer spectral suspension.
- **Proved generic geometry:** affine Kummer leaves, residual phase
  density, transverse conformal flow, local positive star, and
  relevant-complex pushforward.
- **Proved local boundary geometry:** complete pro-log prime cusps,
  logarithmic residue/Hodge compatibility, and the real
  orientation-sign odd \(K_{\mathbb R}\) apex.
- **Proved finite-stage Green data:**
  `DAC_KUMMER_PHASE_POISSON_GREEN_BOUNDARY` constructs the phase
  Poisson semigroup \(e^{-r|D_\ell|}\), positive
  Dirichlet-to-Neumann energy, odd chirality
  \(i\operatorname{sgn}(D_\ell)\), and centered-unitary power action.
  `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN` proves its exact trace
  quotient and Lagrangian Calderón graph.
- **Proved finite derived and source-trace data:**
  `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` contracts the finite
  graph--conormal derived fibre, while
  `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION` identifies the common
  multiplicative cutoff transgression and its arithmetic
  Poisson/Fourier corrections.
- **Proved trace-stratum separation:**
  `DAC_FINITE_PRIME_PRESERVED_STRATUM_CONFLATION_NO_GO` shows that
  finite-prime residue strata cannot be used as preserved-leaf
  conormal support.  Finite primes remain periodic-orbit packets in
  the open flow; conormal/dual-conormal support belongs to a
  conjectural archimedean compactification.  The two localizations
  must be compared, not identified.
- **Primary-source archimedean trace-domain candidate:**
  `DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN` retains the
  full supported normal-Dirac jet tower at the real stationary
  component, with Deninger's transverse exponent \(-2\), and pairs it
  with the strong dual-conormal tower. It is a trace-domain conjecture
  for the generalized Deninger source, not an application of the
  compact smooth foliated-flow theorem and not a substitute for Hodge
  polarization on \(M_\zeta\).
- **Open Hodge gate:** global arithmetic Calderón incidence relation
  and `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`: glue strict
  finite Hardy projectors into Meyer's nuclear almost-polarization,
  construct exact projectors after Hodge completion, identify the
  hereditary relative trace with Paugam's cup form, construct
  `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`, and obtain the
  positive Hodge form on \(M_\zeta\).  Dense off-axis source-resolvent
  stability sees all Meyer generalized jets directly in the strong
  dual; pointwise Riesz representability is optional.
  **Open trace gate:** construction of the archimedean compactification
  and global Rees jet coefficient.  Paugam's displayed positive Hermitian sum
  is only a semisimple critical-line statement; it does not prove
  positivity on generalized zero jets.  Comparison with the raw local
  two-term coefficient is explicitly excluded.
- **No-go boundary:** finite-rank critical-\(L^2\) twists have dense
  multiplier range; bare Kummer-mode \(\ell^2\) has no strongly
  continuous real-flow extension; and unweighted infinite-ray Hilbert
  augmentation has zero quotient seminorm.  Smooth suspension and
  unit augmentation must therefore precede Hilbert completion.
- **Cards:** `DAC_KAHLER_RIEMANN_FLOW_PURITY`,
  `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`,
  `DAC_DERIVED_COEFFICIENT_HILBERT_HODGE_DESCENT`,
  `DAC_POISSON_GEOMETRIC_HODGE_POLARIZATION`,
  `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`,
  `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

### 8. Lefschetz trace

- **Proved analytic character:** Meyer's summable virtual
  representation gives the raw Weil distribution as the alternating
  character of the Poisson--zeta complex, including the exact
  prime-power and archimedean distributions.
- **Proved:** any nondegenerate complex-linear return has positive
  real determinant; primitive orbit length \(\log p\) gives the exact
  coefficient; trace-norm limits preserve traces; compact test
  support sees only finitely many prime powers.  The actual Kummer map
  \(z\mapsto z^p\) cannot be an ordinary smooth nondegenerate return
  germ at \(z=0\), by
  `DAC_ORDINARY_SMOOTH_PRIME_RETURN_GERM_NO_GO`.
- **Open:** identify Meyer's prime terms packetwise with source
  finite-correspondence periodic-orbit packets; separately construct
  the real stationary compactification with exponent \(-2\), prove
  that its full conormal/dual-conormal normal-jet character is the
  \(\Gamma_{\mathbb R}\) distribution, and establish uniform
  smoothing/trace-norm estimates and archimedean convergence.  Prime
  residue comparison is a sheaf-to-orbit comparison, not a
  fixed-stratum identification.
- **Cards:** `DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN`,
  `DAC_REAL_PLACE_FIXED_POINT_LINEARIZATION`,
  `DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`,
  `DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN`.

### 9. Determinant and spectral divisor

- **Proved analytic determinant:** Meyer's exact spectral multiset and
  Deninger's zeta-regularized product theorem give
  \[
   \widehat\zeta(s)
   =
   \frac{\det_\infty((s-\Theta)/2\pi\mid M_\zeta)}
        {(s/2\pi)((s-1)/2\pi)}.
  \]
  Multiplicities are the zero orders, not declared input data.
- **Proved:** equality of logarithmic derivatives plus one
  normalization gives the same uniqueness statement; trace-class
  smoothing of a centered unitary source flow would force compact
  resolvent, discrete finite-multiplicity spectrum, and faithful trace
  character.
- **Open:** transport this determinant through the geometric
  \(R\alpha_*\mathcal G\) comparison and prove packetwise source
  Lefschetz identity.
- **Cards:** `DAC_POISSON_ZETA_REGULARIZED_DETERMINANT`,
  `DAC_ARITHMETIC_LEFSCHETZ_TRACE_COMPARISON`.

### 10. RH derivation

Once source \(H^1\) has positive Hodge form and every nontrivial
\(\xi\)-zero is a genuine source eigenvalue, the existing unconditional
three-term theorem gives
\[
 \operatorname{Re}\rho=\frac12.
\]

- **Lean source:** `DeningerArithmeticThreeTermHodgePurity.lean`.
- **Status:** source coefficient and endpoint candidates have paper-level
  constructions.  Lean currently contains generic three-term/Arakelov
  schemas and Xi-defined analytic comparison models, but no instantiation
  of the generic schema by the actual arithmetic source Poisson map.
  Global nuclear Green/Hodge projection, Hodge--Schwartz
  resolvent-core faithfulness, and source Lefschetz/determinant transport
  remain open.  RH is not proved.

## Exact active critical path

1. **Paper-completed; Lean source instantiation open:** construct
   `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT` from the
   pro-Stein \(R\alpha_*\mathcal G\), finite generalized-log residues,
   archimedean homology current, strict all-prime pushforward, and
   completed Arakelov trace kernel.  This gives intrinsic
   \(H^0=\mathbb R\), \(H^1\), and \(H^2=\mathbb R(-1)\).
2. **Paper-completed; Lean source instantiation open:** sheafify the Hilbert--Kummer fine source and radial
   Schwartz cosheaf; prove strict compatibility among nuclear, mixed
   \(L^1/L^2\), residue-graph, and endpoint topologies in
   `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`.
3. **Paper-completed; Lean source instantiation open:** prove strict nuclear angular cosheaf contraction,
   including retained unitary phase and radius-zero boundary, in
   `DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION`.
4. **Paper-completed at complex/flow/topology level; Lean comparison
   instance open:** apply
   `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION` to identify
   intrinsic reduced \(H^1\) with Meyer's nuclear Fréchet quotient
   \(M_\zeta\), already known to be nonzero, infinite-dimensional, and
   multiplicity-exact.  Source cup/Hodge comparison remains separate.
5. Transport Paugam's cup/trace pairing and audit continuity and
   nondegeneracy on the full generalized-jet topology via
   `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`; Meyer's source
   nuclear almost-polarization and the positive completed Calderón
   projectors, not a zero-indexed splitting, must define the
   upper/lower trace sectors.
6. **Oriented-conformal geometry completed, including arithmetic
   boundaries:** construct
   affine complex Kähler leaves with transverse flow and residual
   density; extend their star through prime cusps and the
   orientation-twisted real apex, with mixed generic/prime overlap
   proved.  Prime extended-\(L^2\) and unitary relative Calderón
   domains are also proved.  Now prove
   `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`: attach every
   Tate--Milnor relative cell before completion, close the global
   Lagrangian Cauchy relation, use Meyer's proved Toeplitz
   transgression and nuclear polarization pair for its
   \(Z\)/Fourier cross terms, identify its completed Hardy relative
   trace with Paugam's cup form, construct a nuclear-continuous source
   Green operator and harmonic projector, and prove faithful positive
   flow-natural Hodge polarization.  For RH, construct a nuclear-dense
   arithmetic Hodge--Schwartz core and prove that every off-axis
   centered resolvent preserves it.  By
   `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY`, this handles all order-zero
   and higher Meyer jets without Hilbert-boundedness assumptions.
   Build the archimedean conormal/dual-conormal trace domain from the
   real Rees jet tower; do not place finite-prime residue packets in
   its preserved support.
   Construct genuinely no-real quaternionic transition data
   separately for functorial extension to all number fields.
7. Identify Meyer's analytic character with the geometric Lefschetz
   distribution in two separated comparisons: finite-prime
   periodic-orbit packets in the open \(J/J'\) sector, and the
   archimedean \(\Gamma_{\mathbb R}\) distribution from the full
   supported/dual-supported jet towers.
8. Transport the already-proved Poisson--zeta regularized determinant
    to source cohomology.
9. Apply the formal Hodge-purity RH theorem; if the polarization is on
    the full jet topology, also apply the Jordan obstruction to obtain
    zero simplicity.

No later step may be used to define an earlier source object.

The old global
`DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON` remains a desirable
comparison with a single raw invariant cover coefficient, but is not
on the construction-critical path.

## Lean audit status

Unconditional algebraic/topological cores have been written in batches.
The coarse-invariant and cofinite divisor-splitting modules pass direct
foreground checks and axiom audits after repairing four Lean 4.30
subtype coercions in the existing three-term dependency.  The
open-quotient restriction core now has a direct Lean module; its
Deninger-specific character-space identification remains sourced by
Deninger's paper.  Only the final umbrella audit may use
`lake build <module>`.

The new strong-dual bridge is formalized in
`DeningerArithmeticDenseResolventPurity.lean`: surjectivity of an
operator difference annihilates its transpose eigenfunctional,
off-axis source-resolvent stability forces weight-one real part, and a
`DeningerHodgeSchwartzResolventXiSpectrum` package derives RH.  Its
required direct `lake env lean` check passes.  This does not assume
the open arithmetic core-density/resolvent theorem; it isolates that
theorem as a structure field.

## Log

- 2026-07-26 — Re-centered source on Deninger's explicit
  \(R\alpha_*\mathcal G\) coefficient and the exact
  Kucharczyk--Scholze Steinberg obstruction; MW retained only as the
  real-orientation enhancement.
- 2026-07-27 — Retired the global-Postnikov cochain detour.  Source
  construction now begins with the genuine equivariant leafwise
  unit-amalgamated sheaf; its chartwise Milnor algebra is a comparison
  theorem, not a definition.
- 2026-07-27 — Retired quotient-stack endpoint/fiber work from the
  dependency graph.  Source core is the arithmetic-projection
  Leray--Rost--Schmid resolution of Deninger's degreewise invariant
  sheaf.
- 2026-07-27 — Proved cofinite open base change and exact split
  divisor strictness.  Retired the unsupported ordinary analytic
  Cartier interpretation of \([p]\), proved the pro-log Kummer
  replacement, and isolated missing source geometry as analytic
  generalized-log purity plus strict pro-recollement comparison on
  the actual arithmetic base.  Retired the auxiliary prime-star space
  as unnecessary.
- 2026-07-27 — promoted Deninger's explicit “relevant complex on the
  approximation” prescription to a concrete derived stratum-residue
  fibre on the actual coarse space.  Proved its global-section
  totalization theorem; raw global coarse-hypercohomology comparison
  is now optional rather than construction-critical.
- 2026-07-27 — inserted Meyer's source-defined Poisson--zeta quotient
  as the exact analytic middle coefficient.  Joined it to the strict
  Milnor--Arakelov endpoint, obtained \(H^0/H^1/H^2\), Weil character,
  Deninger regularized determinant, and Paugam alternating duality.
  Remaining comparison and Hodge gates are stated without CCM.
- 2026-07-27 — applied Deninger's no-real-coefficients theorem to the
  critical path: endpoints are complexifications of even real forms,
  while degree one must descend from a genuinely twisted complex
  \(K_{\mathbb R}\)-odd leaf coefficient.
