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
- **Open:** full coarse analytic real Betti lift and coherent
  flow/Galois/correspondence independence of the collar presentation.
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
- **Proved assembled endpoint/middle complex:**
  `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY` gives
  \(H^0=\mathbb C\), \(H^1=M_\zeta\), and
  \(H^2=\mathbb C(-1)\), with ordinary and reduced cohomology equal.
- **Open:** geometric comparison with \(R\alpha_*\mathcal G\), full
  generalized-jet continuity of cup/trace, and source Hodge
  polarization.
- **Cards:** `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`,
  `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`,
  `DAC_TWO_COLUMN_CUP_TRACE_TOTALIZATION`,
  `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`,
  `DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION`,
  `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`,
  `DAC_SCALAR_SUSPENSION_POISSON_TRANSFER_NO_GO`,
  `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`,
  `DAC_DENINGER_FLOW_POISSON_DILATION`,
  `DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION`.

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
- **Exact open conjecture:**
  `DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`.
  It asserts that \(Ra_*\mathscr E_{\mathrm{Den}}\) has two analytic
  rows and that each row has the length-one arithmetic-curve
  Rost--Schmid resolution, with one real orientation skyscraper.
- **Open geometric core:** the analytic Tate--Milnor coefficient must
  satisfy purity for the already constructed pulled-back generalized
  log divisor, followed by strict passage through the filtered system
  of actual finite recollements, with no derived-limit defect.  The
  retired stronger claim that \([p]\) itself is an ordinary analytic
  Cartier function is unnecessary and unsupported.
- **Construction correction:** the global raw-coefficient comparison
  is now optional.  The construction-critical source is
  `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`, which glues the
  actual coarse generic and prime stratum coefficients by their
  derived residue fibre.  Its categorical global-section and
  three-term amplitude theorem is proved; residue construction,
  strict boundary pushforward, and local packet analysis remain.
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
- **Open:** arithmetic pro-laminated/virtual leaf realization,
  pushforward comparison with the full Rost--Schmid plus real-boundary
  totalization, odd \(K_{\mathbb R}\) degree-one operator, reduced
  comparison, conformal metric, and positive
  Hodge form on \(M_\zeta\).  Paugam's displayed positive Hermitian sum
  is only a semisimple critical-line statement; it does not prove
  positivity on generalized zero jets.  Comparison with the raw local
  two-term coefficient is explicitly excluded.
- **Cards:** `DAC_KAHLER_RIEMANN_FLOW_PURITY`,
  `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`,
  `DAC_DERIVED_COEFFICIENT_HILBERT_HODGE_DESCENT`,
  `DAC_POISSON_GEOMETRIC_HODGE_POLARIZATION`.

### 8. Lefschetz trace

- **Proved analytic character:** Meyer's summable virtual
  representation gives the raw Weil distribution as the alternating
  character of the Poisson--zeta complex, including the exact
  prime-power and archimedean distributions.
- **Proved:** complex-line prime return has positive real determinant;
  primitive orbit length \(\log p\) gives the exact coefficient;
  trace-norm limits preserve traces; compact test support sees only
  finitely many prime powers.
- **Open:** identify Meyer's prime terms packetwise with source
  fixed-orbit distributions; construct source holomorphic prime return
  maps, real stationary
  packet with exponent \(-2\), finite-stage Kähler tower, uniform
  smoothing/trace-norm estimates, and archimedean convergence.
- **Cards:** `DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN`,
  `DAC_REAL_PLACE_FIXED_POINT_LINEARIZATION`,
  `DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`.

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
- **Status:** implication written; source existence and spectral
  comparison gates above remain open.  RH is not proved.

## Exact active critical path

1. Complete Galois, residue, finite-correspondence, and power coherence
   in `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`; its pro-Stein
   derived-section clause is already paper-proved.  Sheafify the
   Hilbert--Kummer refinement and its global radial Schwartz cosheaf.
   Use the proved discrete-flow realization of every Poisson dilation;
   scalar deck pullback remains ruled out by
   `DAC_SCALAR_SUSPENSION_POISSON_TRANSFER_NO_GO`.
2. Use `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE` separately on the actual
   generic and prime strata.
3. Apply the proved `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE` and
   `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`: the analytic
   Kummer generator square and every finite Steinberg/higher
   Tate--Milnor residue cell are constructed.  Apply the proved real
   Kummer boundary; construct its full analytic real Betti lift and
   operation coherence.
4. Apply the proved
   `DAC_PRIME_PACKET_PRO_STEIN_KUMMER_COMPARISON`: each individual
   packet is profinite-times-circle, its prime coefficient is fine
   with amplitude \([0,0]\), and the valuation line is a strict scalar
   summand of the full packet modes.
5. Apply proved `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`: individual
   packet sheaves are first arithmetic-derived-pushed to
   \(\operatorname{Spec}\mathbb Z\), where the mixed restricted sum is
   a flasque cofinite sheaf and derived global sections are the strict
   packet sum.  Sectionwise global summability on arbitrary Deninger
   opens is retired.
6. Form the shifted
   `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`; apply the
   proved shifted-fibre global-section theorem.
7. Apply `DAC_STRICT_PRO_LOG_COLLAR_SECTION` and
   `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL` to obtain
   real endpoint forms \(H^0_{\mathbb R}=\mathbb R\),
   \(H^2_{\mathbb R}=\mathbb R(-1)\), then complexify them to the even
   \(K_{\mathbb R}\)-objects \(\mathbb C\) and \(\mathbb C(-1)\);
   prove the multiplicative signature window and operation-compatible
   reduced comparison.
8. Prove `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`; this
   identifies intrinsic reduced \(H^1\) with Meyer's nuclear Frechet
   quotient \(M_\zeta\), already known to be nonzero,
   infinite-dimensional, and multiplicity-exact.
9. Transport Paugam's cup/trace pairing and audit continuity and
   nondegeneracy on the full generalized-jet topology.
10. Construct the complex Kähler arithmetic leaf realization, with odd
    \(K_{\mathbb R}\) degree-one operator, and its positive
    flow-natural Hodge polarization.  For the \(\mathbb Q\) object an
    additional real form is allowed.  Construct genuinely no-real
    quaternionic transition data separately for functorial extension
    to all number fields.
11. Identify Meyer's analytic prime/archimedean character packetwise
    with the geometric Lefschetz distribution.
12. Transport the already-proved Poisson--zeta regularized determinant
    to source cohomology.
13. Apply the formal Hodge-purity RH theorem; if the polarization is on
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
