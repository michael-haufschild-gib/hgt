# Relative Picard Hodge passivity on the absolute arithmetic curve

- **ID:** `field-one-relative-picard-hodge-passivity`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL CONSTRUCTION / RH PROGRAM
- **Parent:** `docs/the field with one element.md`
- **Statement:** construct, before any Xi-divisor evaluation, a faithful positive relative
  Hodge realization of the continued prime--archimedean two-pole kernel from the absolute
  \(\mathbb F_1\)-curve and its arithmetic Picard pair.

## Goal

Let
\[
  X_{\mathrm{abs}}=(\operatorname{Spec}\mathbb Z)_{\mathbb F_1},\qquad
  (\widetilde{\operatorname{Pic}},\widetilde\eta)
  =
  \left(
    \widetilde{\operatorname{Pic}}
      (\overline{\operatorname{Spec}\mathbb Z}),
    \Theta(\eta)
  \right).
\]
Here the later universal-cover audit resolves \(\widetilde\eta\) as the image of the full generic
stratum \(\widetilde X_\eta\simeq C_{\mathbb Q}\), not as an assumed singleton.
Connes--Consani construct \(X_{\mathrm{abs}}\), the arithmetic Picard/Jacobian monoids,
the Abel--Jacobi image, and a semilocal trace formula whose divergent
\(2h(1)\log\lambda\) term is the regular representation attached to
\(\widetilde\eta\).  They explicitly suggest cohomology of the pair
\((\widetilde{\operatorname{Pic}},\widetilde\eta)\).

The target is not a declaration that this relative cohomology is positive.  It is an explicit
source construction which, if it exists, forces the already formalized predicate
`CCMContinuedTwoPoleSourcePassivity`:

1. compare spherical absolute, compactified \(\mathbb F_1\)-module, and analytic Schwartz
   coefficient sheaves, then extend analytic coefficients to the arithmetic curve and
   derive-push them to Picard monoid along universal Abel--Jacobi;
2. construct two-pole classes from the prime--Gamma source, without Xi zeros;
3. construct a faithful odd Hodge form on these classes;
4. prove that its norm is exactly the continued prime--archimedean two-pole energy;
5. prove unnormalized, lossless convergence from semilocal stages to the global continued form.

The repository already proves unconditionally
\[
  \mathrm{RH}
  \Longleftrightarrow
  \texttt{CCMContinuedTwoPoleSourcePassivity}.
\]
Thus only Steps 1--5 are research content.  Rephrasing passivity as existence of Gram vectors is
not progress.

## Gates

- [x] 0 → 1 in-progress: well-posed source object, exact RH consumer, hostile tests, and
      non-circular construction obligations identified
- [ ] 1 → 2 fully-proven: relative complex, Hodge form, exact kernel identity, and faithful
      cofinal convergence proved on paper
- [ ] 2 → 3 formalized: exact dependency-closed construction and RH capstone proved in Lean
- [ ] 3 → 4 publication-ready: standalone construction, proof, and machine certificate

## Primary-source boundary

`[LITERATURE]` Connes--Consani, *On the Absolute Geometry of
\(\operatorname{Spec}\mathbb Z\)*, construct \(X_{\mathrm{abs}}\).  At each prime \(p\), its
complex points contain the Tate curve
\[
  E_p\simeq C_p\times\widetilde X_\infty,\qquad
  C_p=\mathbb R_+^\times/p^\mathbb Z,
\]
so the arithmetic longitude has length \(\log p\) and the phase circle is independent of \(p\).
The paper constructs no middle cohomology, Hodge index theorem, or RH proof.

`[LITERATURE]` Connes--Consani, *On the Jacobian of
\(\overline{\operatorname{Spec}\mathbb Z}\)*, construct the arithmetic Picard/Jacobian monoids,
the extended Abel--Jacobi map, and the semilocal trace formula
\[
  \operatorname{Tr}(\theta(h)R_\lambda)
  =
  2h(1)\log\lambda+
  \sum_{v\in S}\int_{\mathbb Q_v^\times}^{\prime}
    \frac{h(u^{-1})}{|1-u|}\,d^\ast u+o(1).
\]
They interpret the divergent term as the generic-point contribution and suggest the relative
pair above.  The paper states no positivity or RH theorem.

`[CORPUS]` `CCMTwoPoleSourceCriterion.lean` supplies the exact source-side endpoint.  With
\[
  T(z)=\text{continued prime--archimedean relative trace},\qquad
  K(z,w)=\frac{T(\overline w)-T(z)}{z-\overline w},
\]
the rank-two energy
\[
  \mathcal E(z,w;a,b)
  =
  |a|^2K(z,z)+a\overline bK(z,w)
  +b\overline aK(w,z)+|b|^2K(w,w)
\]
is the Xi--Weil square of the corresponding two-pole packet.  Positivity of
\(\operatorname{Re}\mathcal E\) on the continued source domain is equivalent to RH.

`[CORPUS] [LEAN-PROVED]` Source-positive odd Hodge atoms already exist and must be reused rather
than postulated again:

- `DeningerArithmeticRectangularQuaternionicHodge.lean` constructs the local moving rectangular
  operator \(J_r\), proves \(J_r^2=-1\), strict positive energy, energy preservation, and the
  centered half-density law without Xi data;
- `DeningerArithmeticGammaRankRegular.lean` constructs on
  \(\ell^2(G\sqcup G)\)
  \[
    J_0(a,b)=(-\overline b,\overline a),
  \]
  proves \(J_0^2=-1\), antiunitarity, and norm preservation on a dense source core and its
  completion.

Therefore C6 does not ask for an abstract positive operator.  It asks for closed,
cup-isometric, \(J_0\)-stable descent of these source atoms to the universal-cover relative
complex, followed by exact identification with the continued packet energy.

`[TYPE SEPARATION]` Three primary-source coefficient systems are not yet one object:

1. spherical absolute sheaf
   \(\mathcal F=\Theta^{-1}\mathbb F_1[T]\) on \(\operatorname{Spec}\mathbb Z\);
2. Eilenberg--MacLane/unit-ball structure sheaf
   \(\mathcal O_X\) on \(\overline{\operatorname{Spec}\mathbb Z}\);
3. analytic Schwartz crossed-product sheaf
   \(\mathscr A_{\mathrm{src}}\) on \(\operatorname{Spec}\mathbb Z\).

A valid absolute-\(\mathbb F_1\) route must construct comparison/base-change functors among them
and prove transport of prime Frobenius, products, archimedean metric boundary, and
\(C_{\mathbb Q}\)-action.  Placing them in one diagram is not a comparison theorem.

## Iterative conjecture audit

### C0. Absolute \(\mathbb F_1\)-curve alone proves RH

- **Status:** `[FALSIFIED AS AN INFERENCE]`
- **Killing mechanism:** the constructed curve supplies stalks, untilts, Weil torsors, and Tate
  curves, but no middle cohomology or positive polarization.
- **Strongest positive survivor:** prime orbit lengths and a doctrine-specific absolute
  arithmetic carrier are now concrete.
- **New insight:** “missing \(\mathbb F_1\)-curve” is obsolete; missing theorem is faithful global
  Hodge/intersection positivity.

### C1. Distributional Lefschetz trace implies positivity

- **Status:** `[FALSIFIED]`
- **Killing mechanism:** a trace identity is linear and signed; it does not make the associated
  Hermitian form positive.  The repository's measured-index theorem proves that normalized
  traces can miss finite or density-zero infinite off-line defects.
- **Strongest positive survivor:** the trace formula fixes the local terms and locates the generic
  divergence geometrically.
- **New insight:** relative excision must be followed by a faithful norm construction, not a
  normalized trace.

### C2. Removing the generic point automatically leaves a positive form

- **Status:** `[FALSIFIED AS A FORMAL IMPLICATION]`
- **Killing mechanism:** a mapping cone removes a contribution but has no general positivity
  theorem.  Subtracting a divergent regular representation can leave an indefinite finite part.
- **Strongest positive survivor:** the pair
  \((\widetilde{\operatorname{Pic}},\widetilde\eta)\) is the canonical place to formulate the
  renormalized object.
- **New insight:** positivity must arise from a star, cup product, and faithful completion on the
  relative complex.

### C3. A Hilbert-space Gram realization of \(K\) proves RH geometrically

- **Status:** `[FALSIFIED AS CIRCULAR]`
- **Killing mechanism:** existence of vectors \(b_z\) with
  \(K(z,w)=\langle b_z,b_w\rangle\) is exactly positive definiteness of \(K\), hence the
  formalized RH-equivalent statement.
- **Strongest positive survivor:** an explicit local-to-global boundary operator would be a
  legitimate producer if defined without \(K\)'s spectral divisor or assumed positivity.
- **New insight:** construction data and equality proof must precede completion.

### C4. Semilocal sheaf directly on finite Picard truncations

- **Status:** `[FALSIFIED AS ILL-TYPED]`
- **Killing mechanism:** Connes--Consani's crossed-product sheaf is on
  \(\operatorname{Spec}\mathbb Z\), not on the Picard monoid.  No spaces
  \(\widetilde{\operatorname{Pic}}_S\), points \(\widetilde\eta_S\), or coefficient pullbacks
  with the previously proposed types were constructed.
- **Strongest positive survivor:** the Abel--Jacobi map supplies a canonical route for a derived
  direct image, while semilocal sets \(S\) index source opens and their restriction maps.
- **New insight:** coefficient transport and archimedean extension are independent construction
  gates which must precede relative Picard cohomology.

### C5. Push directly from the compactified arithmetic curve and excise one point

- **Status:** `[FALSIFIED AS WRONG SOURCE MAP]`
- **Killing mechanism:** the geometric support theorem uses the universal Abel--Jacobi embedding
  \[
    \widetilde{\Theta}:
    \widetilde{\operatorname{Spec}\mathbb Z}
      \hookrightarrow
    \widetilde{\operatorname{Pic}}
      (\overline{\operatorname{Spec}\mathbb Z}),
  \]
  not a direct map from the compactified curve carrying all framed/rooted data.  The generic
  regular representation is a stratum/fiber of the universal cover, not justified as a singleton
  coefficient restriction.
- **Strongest positive survivor:** pull the arithmetic coefficient sheaf to the universal cover,
  push along \(\widetilde\Theta\), and excise the full image of the generic stratum.
- **New insight:** universal-cover and generic-stratum geometry are part of the source type, not
  optional decorations.

### C6. Universal-cover relative Picard boundary realization

`[CONJECTURE] [F1_RELATIVE_PICARD_HODGE_PASSIVITY]`

Let \(X=\overline{\operatorname{Spec}\mathbb Z}\), let
\(\pi:\widetilde X\to X\) be Connes--Consani's universal adelic cover, and let
\[
  \widetilde\Theta:
  \widetilde X\hookrightarrow
  \widetilde{\operatorname{Pic}}
    (\overline{\operatorname{Spec}\mathbb Z})
\]
be the universal Abel--Jacobi embedding.  Let \(\mathscr A_{\mathrm{src}}\) be the semilocal
crossed-product sheaf on \(\operatorname{Spec}\mathbb Z\), characterized on source opens by
\[
  \mathscr A_{\mathrm{src}}(S^c)
  =
  \mathcal S(\mathbb A_S)\rtimes\mathbb Z_S^\times .
\]
There is an archimedean derived extension \(\mathscr A_{\mathrm{ar}}\) to \(X\), compatible with
the Gamma local term.  Pull it to \(\widetilde X\) and put
\[
  \mathscr B
  =
  R\widetilde\Theta_\ast L\pi^\ast\mathscr A_{\mathrm{ar}}
\]
on \(\widetilde{\operatorname{Pic}}\).  With
\(\widetilde X_\eta\simeq C_{\mathbb Q}\) the full generic stratum of \(\widetilde X\), put
\(Z_\eta=\widetilde\Theta(\widetilde X_\eta)\), and let
\(i_\eta:Z_\eta\hookrightarrow\widetilde{\operatorname{Pic}}\).  Define the relative object
\[
  C_{\mathrm{rel}}
  =
  \operatorname{Fib}\!\left(
    R\Gamma(\widetilde{\operatorname{Pic}},\mathscr B)
      \longrightarrow
    R\Gamma(Z_\eta,Li_\eta^\ast\mathscr B)
  \right).
\]
All pullbacks, pushforwards, fibers, cup products, and completions occur in a
\(C_{\mathbb Q}\)-equivariant derived category; forgetting equivariance would discard the scaling
flow whose generator carries the purity statement.  The conjecture requires:

1. a doctrine-aware comparison zigzag from spherical absolute sheaf through compactified
   \(\mathbb F_1\)-module sheaf to \(\mathscr A_{\mathrm{src}}\), with each edge's exact loss
   ledger and separate proofs for any retained prime Frobenius and archimedean boundary data;
2. a \(C_{\mathbb Q}\)-equivariant cup-compatible map from the already constructed divisor-free
   prime--Gamma packet cohomology on the honest Euler sectors to
   \(H^1(C_{\mathrm{rel}})\);
3. a source-controlled resolvent/packet continuation producing classes \(\beta_z\) for every
   admissible continued pole \(z\), without Xi-divisor indexing;
4. a closed cup-isometric embedding of the existing rectangular/Gamma-rank odd Hodge source core,
   with the relative relation subspace proved \(J_0\)-stable;
5. descent of \(J_0\) to an antiunitary \(J^2=-1\) on relative cohomology and the faithful norm
   \(\|x\|^2=\operatorname{tr}(x\smile Jx)\);
6. unnormalized isometric control of the source-open restriction system, so no finite or
   density-zero direction is quotiented away on passage to the generic stalk;
7. an exact source identity
   \[
     \left\|a\beta_z+b\beta_w\right\|^2
     =
     \operatorname{Re}\mathcal E(z,w;a,b)
   \]
   on the full continued two-pole domain.

This is stronger than semilocal trace convergence and weaker in logical presentation than
postulating RH: the coefficient extension, derived direct image, source classes, Hodge form, and
kernel identity must be constructed from the absolute curve, Abel--Jacobi map, local
crossed-product sheaf, and prime--Gamma boundary before any Xi-divisor comparison.

**Verdict:** `SURVIVES THIRD TYPE AUDIT`; all seven numbered clauses remain open as a combined
arithmetic construction.  The existence and exact category of
\(\mathscr A_{\mathrm{ar}}\), \(L\pi^\ast\), \(R\widetilde\Theta_\ast\), and the generic-stratum
restriction are themselves explicit sub-gates. Ordinary spherical scalar extension is now
excluded as an equivalence, so Clause 1 must be a loss-aware zigzag.

### C7. Ordinary spherical scalar extension is the arithmetic localization

- **Status:** `[FALSIFIED] [PAPER-PROVED] [LEAN-FORMALIZED]`
- **Killing mechanism:** for every additive monoid \(M\) and \(p\ge2\), augmentation
  \(\mathbb Z[M]\to\mathbb Z\) detects scalar \(p\) as a nonunit. Its image is a unit in
  \(\mathbb Z[1/p]\), so no \(\mathbb Z\)-algebra equivalence can identify the two.
- **Strongest positive survivor:** augmentation followed by localization constructs a canonical
  \(\mathbb Z\)-algebra map \(\mathbb Z[M]\to\mathbb Z[1/p]\).
- **Exact loss ledger:** every monomial maps to \(1\); if \(M\) is nontrivial, this comparison is
  noninjective. It cannot transport Frobenius-monomial or exponent data faithfully.
- **Lean certificate:**
  `GaloisForLFunctions.HTGeometry.FieldOneSphericalLocalizationNoGo`.
- **New insight:** RP0 cannot be one base-change equivalence. It needs a diagram retaining
  spherical exponent/Frobenius data on one branch while separately comparing arithmetic and
  analytic coefficients.

### C8. Spherical monomials land inside the semilocal Bruhat--Schwartz algebra

- **Status:** `[FALSIFIED AS ILL-TYPED]`
- **Killing mechanism:** the candidate image
  \(\chi_h(x)=\alpha_S(hx)\) has unit modulus and full support, hence is not a
  Bruhat--Schwartz function on noncompact \(\mathbb A_S\).
- **Strongest positive survivor:** multiplication by \(\chi_h\) is a continuous automorphism of
  \(\mathcal S(\mathbb A_S)\), unitary on \(L^2(\mathbb A_S)\).
- **Paper theorem:** for every fixed finite \(S\ni\{\infty,p\}\), these Weyl multipliers form a
  faithful representation of \(\mathbb Z[1/p]\), satisfy
  \(W_{h/p}^{\,p}=W_h\), and obey
  \(\theta(u)W_h\theta(u)^{-1}=W_{u^{-1}h}\).
- **Lean status:** abstract character/root/faithfulness and full archimedean Schwartz
  preservation/invertibility/faithfulness are formalized. Existing `L2MellinUnitary.lean`
  supplies the archimedean \(L^2\) unitary multiplier.
  `FieldOneLocallyConstantWeylMultiplier.lean` formalizes finite-place
  compact-support/local-constancy preservation, inverse/root laws, and scaling covariance for
  an arbitrary locally constant additive character.
  `FieldOnePadicWeylCharacter.lean` constructs at every prime a nontrivial locally constant
  character trivial on \(\mathbb Z_p\), normalized at \(p^{-1}\), and instantiates that
  multiplier. The extension is noncanonical beyond its prescribed depth-one subgroup.
  `FieldOnePadicStandardWeylCharacter.lean` replaces it with the canonical compatible
  all-depth character, proves every \(p^{-n}\) normalization and exact kernel
  \(\mathbb Z_p\), and instantiates the multiplier.
  `FieldOneFiniteAdeleWeylCharacter.lean` assembles the local characters canonically over the
  finite restricted product, proves finite support, local constancy, nontriviality, and the
  finite-adele Weyl composition law.
  `FieldOneFiniteAdeleDiagonalReciprocity.lean` proves diagonal cancellation with the negative
  real character on every \(\mathbb Z[1/p]\), exactly the exponent group of a fixed-prime
  perfection stage. `FieldOneRationalPrimaryReciprocity.lean` uses pairwise-coprime
  prime-power factorization and Bézout coefficients to prove the full rational diagonal law.
  `FieldOneSemilocalBruhatWeylTensor.lean` formalizes the algebraic
  \(\mathcal S(\mathbb R)\otimes C_c^{\mathrm{lc}}(\mathbb A_f)\) carrier and its normalized
  real--finite Weyl automorphisms.
  `FieldOneFiniteAdeleIntegralBruhatTest.lean` proves the integral finite adeles compact open,
  constructs their nonzero characteristic Bruhat test, and formalizes finite-zero contraction.
  `FieldOneSemilocalArchimedeanFaithfulness.lean` proves that semilocal operator equality forces
  equality of real coordinates and hence that the rational diagonal action is faithful.
  `UnitModulusL2Multiplier.lean` supplies a general unit-modulus \(L^2\) unitary, while
  `FieldOneFiniteAdeleL2WeylMultiplier.lean` instantiates finite-adele Borel Haar \(L^2\),
  proves unitarity, embeds Bruhat tests, and proves exact extension compatibility.
  `FieldOneSemilocalL2WeylMultiplier.lean` proves the full product-Haar semilocal unitary action.
  `FieldOneFiniteAdeleSelfDuality.lean` proves finite-character primitivity and faithful finite
  Bruhat action; `FieldOneSemilocalFullFaithfulness.lean` proves full algebraic semilocal
  faithfulness by the two zero-contractions. `FieldOneSemilocalBruhatToL2.lean` constructs the
  canonical algebraic Schwartz--Bruhat-to-product-\(L^2\) map and proves exact Weyl equivariance
  without a finite-adele sigma-finiteness premise. `FunctionTensorProduct.lean` proves uniqueness
  of algebraic separated-function tensors, and `FieldOneSemilocalBruhatL2Embedding.lean` combines
  this with the swapped open-positive product measure and continuous representatives to prove
  injectivity. `FieldOneSemilocalBruhatHilbertCompletion.lean` pulls back the product-\(L^2\)
  inner product, identifies the abstract completion with the closed algebraic image, and extends
  the Weyl action unitarily with exact intertwining.
  `L2SeparatedProductDensity.lean` and
  `FieldOneSemilocalBruhatL2Density.lean` now prove full-product density,
  identify the abstract completion canonically with all semilocal product
  \(L^2\), and prove completed and ambient Weyl faithfulness.
  `L2HilbertTensorProduct.lean` and
  `FieldOneSemilocalFactorwiseHilbertTensor.lean` construct the independent
  factorwise Hilbert completion, identify it canonically with the semilocal
  Bruhat completion, and prove pure-tensor compatibility. Sheaf compatibility
  remains open.
- **Card:** `docs/drafts/pipeline/2-fully-proven/field-one-spherical-weyl-multiplier-bridge.md`.
- **New insight:** the Frobenius-faithful RP0 target is the multiplier/endomorphism sheaf of the
  analytic coefficients, not the coefficient sheaf itself.

### C9. Full semilocal `L²` completion automatically supplies relative Picard cohomology

- **Status:** `[FALSIFIED AS AN INFERENCE]`
- **Attack:** combine the primary-source sheaf
  \(\mathscr O\rtimes\mathbf G_m\) on
  \(\operatorname{Spec}\mathbb Z\) with the now-proved equivalence between
  the semilocal Bruhat Hilbert completion and full product-Haar \(L^2\), then
  regard the result as the desired Hilbert coefficient sheaf on
  \(\widetilde{\operatorname{Pic}}\).
- **Killing mechanism:** the crossed-product sheaf is algebraic and lives on
  \(\operatorname{Spec}\mathbb Z\); the Hilbert completion is one analytic
  fiber and does not by itself define restriction maps, an archimedean
  extension, a derived pullback, or a derived Abel--Jacobi pushforward.
  Connes--Consani's 2026 Jacobian paper says the Picard-pair cohomology is
  suggested by the trace geometry, not constructed. Their Riemann--Roch
  strategy also records the characteristic-one \(H^1\) problem as open,
  with null elements obstructing the available Čech construction.
- **Strongest positive survivor:** the full semilocal product-Haar \(L^2\)
  space, its dense Bruhat core, and its faithful Weyl action are canonical
  boundary data for the global additive adelic fiber. They are not yet the
  finite-\(S\) quotient Hilbert spaces of the trace formula. Any proposed
  \(\mathscr A_{\mathrm{ar}}\) must construct an explicit comparison rather
  than identify these types by notation.
- **New insight:** RP0 now contains a falsifiable normed-sheaf comparison
  gate: sheaf compatibility must be constructed, not inferred from
  fiberwise density or completion.

### C10. The completed archimedean--finite carrier is the finite-\(S\) trace fiber

- **Status:** `[FALSIFIED BY TYPE COMPARISON]`
- **Attack:** use the proved completion of
  \(\mathcal S(\mathbb R)\otimes C_c^{\mathrm{lc}}(\mathbb A_f)\) as
  \(L^2(\mathbb Z_S^\times\backslash\mathbb A_S)\) in the semilocal sheaf.
- **Killing mechanism:** `FieldOneGlobalAdeleComparison.lean` proves
  \(\mathbb R\times\mathbb A_f\cong\mathbb A_{\mathbb Q}\) as a ring and
  topological space. This is the full additive adele ring. The source trace
  fiber for finite \(S\ni\infty\) is the quotient
  \(L^2(\mathbb Z_S^\times\backslash\mathbb A_S)\), and its action is
  multiplicative scaling by
  \(C_{\mathbb Q,S}=\mathbb Z_S^\times\backslash\mathbb A_S^\times\).
  The formalized action is instead an additive-character multiplier action
  on unquotiented global adelic \(L^2\).
- **Strongest positive survivor:** the new Lean comparison transports the
  standard additive character to mathlib's rational adele ring, proves it
  nontrivial, and proves global additive reciprocity: it vanishes on every
  principal rational adele.
- **New gate:** C11 constructs finite-\(S\) products, orbit quotients, and
  multiplicative scaling. Quotient measure, its Hilbert representation, and
  compatible restriction maps remain prerequisites for sectionwise
  completion or derived Picard transport.

### C11. Direct finite-stage class space and idele-class action

- **Status:** `[FORMALIZED ALGEBRAICALLY AND TOPOLOGICALLY]`
- **Attack:** construct
  \(\mathbb A_S=\mathbb R\times\prod_{v\in S_f}\mathbb Q_v\), present
  rational \(S\)-units by \(-1\) and primes in \(S_f\), embed them
  diagonally, and descend coordinatewise idele scaling through their orbit
  quotient.
- **Proof:** `FieldOneFiniteStageClassSpace.lean` proves the diagonal map
  injective, constructs
  \(\mathbb Z_S^\times\backslash\mathbb A_S\) and
  \(C_{\mathbb Q,S}\), proves the \(S\)-unit image acts trivially on the
  orbit quotient, and factors the action through \(C_{\mathbb Q,S}\).
  `FieldOneFiniteStageClassTopology.lean` proves the orbit projection is an
  open quotient map and every idele class acts by a homeomorphism.
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`.
- **Boundary:** C13 now adds the descended norm module, but no identification
  with Haar scaling, quotient measure, `L²`, crossed product, restriction
  map, sheaf, trace, positivity, or RH theorem is inferred.

### C12. Quotient topology automatically determines the trace measure

- **Status:** `[FALSIFIED AS AN AUTOMATIC INFERENCE]`
- **Attack:** push product additive Haar measure along the open orbit
  projection.
- **Killing mechanism:** topological quotient data do not select the
  fundamental-domain/disintegration measure. Direct pushforward uses full
  saturated preimages and is not automatically the trace measure.
  `S`-unit invariance itself requires the local Haar modulus and rational
  product formula
  \(|u|_\infty\prod_{v\in S_f}|u|_v=1\).
- **Strongest positive survivor:** continuous idele-class homeomorphisms are
  complete, and C13 proves the product norm character is one on the generated
  diagonal \(S\)-unit subgroup. Next analytic theorem is exactly its
  identification with product-Haar scaling plus measurable quotient
  construction.
- **New gate:** identify local distributive Haar characters with the
  normalized real and adic norms, derive product-measure invariance, then
  construct quotient measure by an audited fundamental-domain or
  disintegration theorem.

### C13. Finite-stage norm module and rational \(S\)-unit product formula

- **Status:** `[FORMALIZED]`
- **Attack:** define
  \(\delta_S(u)=|u_\infty|\prod_{v\in S_f}|u_v|\) and prove it vanishes
  multiplicatively on the quotient subgroup, i.e. equals one on every
  generated rational \(S\)-unit.
- **Proof:** `FieldOneFiniteStageModule.lean` proves own-prime local norm
  \(p^{-1}\), different-prime local norm \(1\), sign and selected-prime
  generator module one, kernel containment for the generated subgroup and
  its diagonal image, and descent
  \[
    \delta_S:C_{\mathbb Q,S}\longrightarrow\mathbb R_{\geq0}.
  \]
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`.
- **Boundary:** this is the product-formula/module stage. It does not identify
  \(\delta_S\) with `MeasureTheory.distribHaarChar`, install an invariant
  measure, construct a measurable quotient, or infer `L²`, trace, positivity,
  or RH.
- **New gate:** mathlib has the abstract distributive Haar character but no
  audited theorem in this toolchain equating its adic factors with the
  normalized adic norm. Prove that local theorem and its finite-product
  assembly before quotient measure descent.

### C14. Finite-stage module equals additive Haar scaling

- **Status:** `[FORMALIZED]`
- **Attack:** calculate the distributive Haar character at every local
  rational completion and assemble it over the finite product.
- **Proof:** `FieldOnePadicHaarScaling.lean` proves the residue-kernel index
  \(p\) and the own-prime factor \(p^{-1}\).
  `FieldOneLocalHaarModule.lean` proves the full arbitrary-unit identity
  \(\operatorname{distribHaarChar}_{\mathbb Q_v}(u)=|u|_v\).
  `FieldOneHaarCharacterProducts.lean` proves binary and finite dependent
  product factorization.
  `FieldOneFiniteStageHaarScaling.lean` proves
  \[
    \operatorname{distribHaarChar}_{\mathbb A_S}(u)=\delta_S(u),
  \]
  identifies the descended character on \(C_{\mathbb Q,S}\), proves exact
  all-idele scaling for every additive Haar measure, and proves invariance
  under every diagonal rational \(S\)-unit.
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`.
- **New insight:** product formula and Haar invariance are no longer separate
  assumptions. Remaining quotient-measure gap is disintegration, not local
  normalization.

### C15. Idele-class Haar \(L^2\) is definitionally the trace fiber

- **Status:** `[FALSIFIED AS AN IDENTIFICATION]`
- **Killing mechanism:** \(C_{\mathbb Q,S}\) is the invertible orbit in the
  additive orbit quotient \(X_S\). Primary-source \(w_S\) uses both the
  additive-product conull statement and a Radon--Nikodym derivative between
  additive and multiplicative Haar. Haar \(L^2(C_{\mathbb Q,S})\) alone does
  not construct \(L^2(X_S)\).
- **Strongest positive survivor:**
  `FieldOneFiniteStageIdeleClassHaarL2.lean` equips the locally compact,
  second-countable idele-class group with Borel left Haar measure and
  constructs its unitary left-regular representation
  \((\lambda(c)f)(x)=f(c^{-1}x)\).
- **New gate:** formalize the orbit-of-one embedding
  \(C_{\mathbb Q,S}\hookrightarrow X_S\), conull complement for the genuine
  quotient measure, the Radon--Nikodym multiplier, and equivariance of
  \(w_S\).

### C16. Extended module and orbit-of-one idele locus

- **Status:** `[FORMALIZED ALGEBRAICALLY AND TOPOLOGICALLY]`
- **Proof:** `FieldOneFiniteStageClassModule.lean` extends the product norm
  to every additive adele, descends it continuously to \(X_S\), constructs
  the orbit-of-one map \(C_{\mathbb Q,S}\to X_S\), proves that map continuous
  and injective, identifies the two modules on its image, and proves
  equivariance under idele-class scaling.
  `FieldOneFiniteStageIdeleLocusMeasure.lean` identifies the coordinatewise
  invertible locus with idele values, proves it open and conull for explicit
  product additive Haar on \(\mathbb A_S\), and proves its idele-class image
  open in \(X_S\).
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`.
- **Boundary:** genuine quotient measure, transport of prequotient nullness
  through a fundamental domain/disintegration, Radon--Nikodym multiplier,
  and \(w_S\) remain open.

## Ranked open cores

Ranking is by logical dependency, not preferred method or effort.

1. `[OPEN CORE RP0 — DOCTRINE COMPARISON]` Compare
   \(\mathcal F\), \(\mathcal O_X\), and \(\mathscr A_{\mathrm{src}}\) with explicit loss
   ledgers. Ordinary scalar extension is not an equivalence, and its canonical
   augmentation--localization edge kills every monomial. Construct a comparison diagram whose
   Frobenius-faithful branch does not factor solely through that edge, and prove separately which
   products, exponent data, prime Frobenius, and archimedean boundary survive. A faithful,
   \(p\)-perfect, scaling-covariant multiplier representation is now paper-proved at each fixed
   semilocal stage. Algebraic real--finite tensor assembly, full semilocal faithfulness,
   finite-adele Haar-\(L^2\) unitarity, and product-Haar semilocal \(L^2\) unitarity are
   Lean-proved. The canonical algebraic-tensor map into product-Haar \(L^2\) and its exact Weyl
   equivariance and injectivity are also Lean-proved. Its induced Hilbert completion is
   Lean-proved canonically equivalent to the full product-Haar \(L^2\), with
   completed unitary Weyl intertwining and faithful completed/ambient actions.
   Independent factorwise Hilbert-tensor identification is also Lean-proved,
   with exact pure-tensor compatibility. The ambient product is now
   Lean-identified with the full rational adele ring, not a finite-\(S\)
   quotient. Finite-\(S\) orbit quotient, semilocal idele class group,
   factored multiplicative scaling, open quotient topology, and scaling
   homeomorphisms are now Lean-proved. Its product norm module, triviality on
   diagonal rational \(S\)-units, and descent to semilocal idele classes are
   also Lean-proved. Identification with product-Haar scaling, exact
   all-idele measure scaling, diagonal \(S\)-unit invariance, idele-class Haar
   `L²`, its unitary left-regular representation, the continuous module on
   \(X_S\), and the continuous injective orbit-of-one map \(C_S\to X_S\) are
   Lean-proved. Its image is Lean-proved open, and the prequotient idele
   locus is Lean-proved open and conull for product additive Haar.
   Additive-orbit quotient measure, Radon--Nikodym comparison
   `L²(X_S) ≃ L²(C_S)`, sheaf-restriction compatibility, and compactified
   extension remain open.
2. `[OPEN CORE RP1 — COEFFICIENT TYPE]` Construct
   \(\mathscr A_{\mathrm{ar}}\) and the \(C_{\mathbb Q}\)-equivariant
   pull--push object \(\mathscr B\).  This is not itself RH-equivalent.
3. `[OPEN CORE RP2 — HONEST-SECTOR COMPARISON]` Map the existing divisor-free prime--Gamma
   packet quotient cup-isometrically into \(H^1(C_{\mathrm{rel}})\) on the absolute Euler sectors.
   This remains before meromorphic continuation.
4. `[OPEN CORE RP3 — SOURCE CONTINUATION AND DESCENT]` Construct continued packet classes and
   prove the relative relation subspace closed and \(J_0\)-stable.  No Xi-divisor basis or
   target-side positive form is allowed.
5. `[OPEN CORE RP4 — FAITHFUL GLOBAL IDENTITY]` Prove the relative Hodge norm equals
   \(\operatorname{Re}\mathcal E\) on the full continued two-pole domain and that no direction is
   lost in globalization.  Together with already proved source positivity of the norm, RP4 gives
   `CCMContinuedTwoPoleSourcePassivity` and hence RH.

RP4 is the first explicit RH-producing sentence.  Any proof of RP4 which imports Weil positivity,
real Xi spectrum, or a Gram representation of \(K\) is circular.

## Hostile acceptance tests

Any proposed realization must fail at least one axiom for each fake:

1. a shifted-Xi completion with the same functional-equation symmetry;
2. a Helson prime-phase twist with flexible continued divisor;
3. a measured or normalized trace which erases a density-zero defect;
4. an indefinite functional-equation pairing renamed a Hilbert metric;
5. a divisor-defined completion whose basis is indexed by Xi zeros;
6. a semilocal system whose negative directions escape at infinity;
7. the naive local Tate flow, whose time-\(\log p\) return is degenerate on the full tangent
   plane.
8. a non-equivariant relative complex which has no induced scaling generator.
9. an ordinary scalar-extension edge falsely declared to preserve spherical exponent or
   Frobenius-monomial data.
10. an additive character falsely declared to be a Bruhat--Schwartz coefficient rather than a
    multiplier.

Passing only the zeta source is not sufficient: the proof must identify exactly which
source-geometric structure rejects each fake without reading its zeros.

## Dependency chain

```text
absolute F1 curve + arithmetic Picard pair
  -> doctrine comparison of spherical, compactified, and analytic sheaves
  -> archimedean extension of the semilocal sheaf
  -> pullback to universal adelic cover
  -> universal Abel-Jacobi derived direct image
  -> generic-stratum relative complex
  -> source two-pole classes
  -> faithful odd Hodge norms
  -> lossless source-open/global continuation
  -> continued two-pole source passivity
  -> RH
```

Only the first geometric objects, the source sheaf on \(\operatorname{Spec}\mathbb Z\), and the
last equivalence are currently established.  No Lean module should be added for C6 before a
dependency-closed paper
proof exists.

## No-go closure

- **Exact killing mechanisms:** C0 lacks cohomology; C1 confuses trace with sign; C2 confuses
  excision with positivity; C3 is the Moore--Aronszajn reformulation of the desired positivity;
  C4 places a sheaf on the wrong space; C5 uses the wrong Abel--Jacobi source and excises a point
  instead of the generic stratum; C7 conflates ordinary monoid-algebra scalar extension with
  arithmetic localization; C8 places full-support characters inside a decaying/compact-support
  coefficient algebra.
- **Strongest positive survivor:** the relative Picard pair canonically separates the generic
  divergence, while the continued two-pole energy is a minimal faithful RH detector.
- **New insight:** the exact bridge is a lossless relative boundary/Hodge construction, not a new
  definition of \(\mathbb F_1\), an absolute Frobenius slogan, or a larger Weil test space.
- **Status:** survivor is source-pure and falsifiable but not paper-proved.

## Log

- 2026-07-26 — Opened after internal corpus audit and primary-source audit through July 2026.
  Four stronger shortcuts were killed; C4 proposed as exact method-neutral bridge between the
  new absolute/Picard geometry and the existing formal RH endpoint.  No computation or Lean build
  used.
- 2026-07-26 — Hostile type audit killed C4: the source sheaf lives on
  \(\operatorname{Spec}\mathbb Z\), while finite Picard truncations were undefined.  C5 repairs
  the types by making archimedean extension and \(R\Theta_\ast\) explicit.  No computation or
  Lean build used.
- 2026-07-26 — Primary-source type audit killed C5: Section 9 supports the trace on the image of
  the universal Abel--Jacobi embedding, and its generic regular representation is a stratum.
  C6 inserts pullback to the universal cover, \(R\widetilde\Theta_\ast\), and full-stratum
  excision.  No computation or Lean build used.
- 2026-07-26 — Algebraic hostile audit killed C7. Ordinary base change leaves scalar \(p\)
  noninvertible, while \(\mathbb Z[1/p]\) inverts it. Lean formalization also constructs the
  canonical augmentation--localization survivor and proves that it collapses all monomials.
- 2026-07-26 — Analytic type audit killed C8 as a coefficient-valued map and repaired it as a
  faithful unitary multiplier representation. Fixed-stage preservation, \(p\)-perfection, and
  scaling covariance are paper-proved; sheaf compatibility remains RP0.
- 2026-07-27 — Type correction C10 led to a direct finite-stage construction.
  Lean now contains \(\mathbb A_S\), generated rational \(S\)-units, their
  diagonal orbit quotient, semilocal idele class group, exact factored
  scaling, open quotient topology, and scaling homeomorphisms. C12 killed
  automatic measure descent; local Haar modulus/product-formula invariance
  and a genuine measurable quotient are next.
- 2026-07-27 — C13 formalized the finite-stage norm module and rational
  \(S\)-unit product formula: own-prime norm \(p^{-1}\), other-prime norm
  \(1\), full kernel containment, and descent to semilocal idele classes.
  Measure gate is now exact identification of this norm module with
  product-Haar `distribHaarChar`, followed by fundamental-domain or
  disintegration quotient construction.
