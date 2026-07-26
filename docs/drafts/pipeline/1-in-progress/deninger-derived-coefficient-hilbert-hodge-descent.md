# Derived-coefficient Hilbert--Hodge descent

- **ID:** `deninger-derived-coefficient-hilbert-hodge-descent`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed analytic core
- **Parent:** `deninger-derived-mw-rational-witt-coefficient`
- **Statement:** After realification and removal of its regulator-null acyclic part, Deninger's
  unit-amalgamated derived Milnor coefficient sheaf, with its
  Milnor--Witt residue/signature descent on the rational-Witt space, admits a
  cohomologically faithful real-place regulator into a closed Hilbert complex whose harmonic
  degree-one realization carries the descended local quaternionic Hodge operator and centered
  unitary Frobenius flow.

## Goal

Construct positive arithmetic \(H^1\) from the coefficient object itself.  This is the exact
bridge from the finite-place complex
\[
 \mathscr A_{\mathrm{flow}}
\]
to Deninger's reduced leafwise cohomology.  It must not use the zeros of \(\zeta\), Weil
positivity, an assumed spectral realization of \(\Xi\), or the Riemann hypothesis.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, attack, falsifiers, literature boundary
- [ ] 1 → 2 fully-proven: construct regulator and prove all descent clauses
- [ ] 2 → 3 formalized: source construction plus abstract Hilbert-complex theorem in Lean
- [ ] 3 → 4 publication-ready: standalone theorem, proof, and Lean certificate

## Literature boundary

For a Riemannian foliation of bounded geometry, the leafwise de Rham complex has
\[
 H^\infty(M;\Lambda\mathcal F)
 =
 \ker\Delta_{\mathcal F}
 \mathbin{\widehat\oplus}
 \overline{\operatorname{im}d_{\mathcal F}}
 \mathbin{\widehat\oplus}
 \overline{\operatorname{im}\delta_{\mathcal F}},
 \qquad
 \bar H^\bullet_{\mathcal F}\simeq\ker\Delta_{\mathcal F}.                \tag{1}
\]
Álvarez López--Kordyukov--Leichtnam explicitly warn that their coefficient extension is not
valid for every Hermitian vector bundle with a flat leafwise connection.  Therefore the
arithmetic coefficient cannot be inserted into `(1)` merely by calling it flat.  A valid
construction must prove one of:

1. the regulator coefficient is an associated transverse natural bundle covered by `(1)`; or
2. its completed differential is a closed densely defined Hilbert complex, so the abstract
   Hilbert-complex decomposition applies directly.

This card uses route 2.  Route 1 remains an optional geometric strengthening.

## Dependency-closed analytic core

`[PROVED HERE] [DAC_ABSTRACT_REDUCED_HODGE_DECOMPOSITION]`

Let \(E=\widehat\bigoplus_q E^q\) be a Hilbert space and let \(Q\) be a closed densely defined
differential with \(Q^2=0\).  Write \(Q^\dagger\) for its adjoint and
\[
 \mathcal H=\ker Q\cap\ker Q^\dagger .
\]
Then
\[
 \ker Q
 =
 \overline{\operatorname{im}Q}
 \mathbin{\widehat\oplus}\mathcal H,                                    \tag{2}
\]
and hence reduced cohomology is canonically and isometrically harmonic:
\[
 \ker Q/\overline{\operatorname{im}Q}\;\cong\;\mathcal H.                \tag{3}
\]
For a bounded differential this follows immediately from
\[
 (\operatorname{im}Q)^\perp=\ker Q^\dagger,\qquad
 \overline{\operatorname{im}Q}\subseteq\ker Q
\]
and orthogonal projection.  The closed-operator case follows from the same closed-range
orthogonal-complement identities for a closed Hilbert complex.

If a unitary \(U\) preserves \(\operatorname{Dom}Q\) and commutes with \(Q\), then it commutes
with \(Q^\dagger\), preserves \(\mathcal H\), and acts unitarily on `(3)`.  In the bounded
model this implication is already formalized by
`deningerUnitary_commutes_adjoint_of_commutes`,
`deningerUnitary_commutes_brstHodgeHamiltonian`, and
`deningerUnitary_maps_brstHarmonic_to_brstHarmonic`.

Thus no separate conjectural “Hodge decomposition” is needed after the arithmetic regulator
has supplied a closed Hilbert complex.  Remaining conjecture is source construction and
compatibility.

## Conjecture

`[CONJECTURE] [DAC_DERIVED_COEFFICIENT_HILBERT_HODGE_DESCENT]`

Let
\[
 \mathscr A_{F,\mathbb R}^{\mathrm{geom}}
 =
 \mathcal R_{X_F}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^M_{F,\mathbb R}
\]
be the primary local derived sheaf coefficient of
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.  An optional Milnor
character realization may later identify it with
\(R\alpha_{F,*}\mathbb R\), but no clause below depends on that
geometrization.  Let
\(\mathscr A_{\mathrm{flow}}\) be its twisted
Rost--Schmid/Galois/power descent.  Full
\(\mathbb A^1\)-localization is excluded by
`deninger-a1-localized-rational-witt-coefficient`.  Let
\(\mathscr A_{\mathrm{arith}}\) and
\[
 C^\bullet_{\mathrm{arith}}
 =R\Gamma(\overline X_W,\mathscr A_{\mathrm{arith}})_{\mathrm{red}}
\]
be the power-localized, descended, unital Betti--Deligne gluing `(A)`--`(C)` of
`DAC_ROST_SCHMID_FLOW_REALIZATION`.  Its completed real realization has the following
properties.

1. **Cohomologically faithful completed regulator.** There is a multiplicative,
   residue-compatible chain map
   \[
     \operatorname{reg}_\infty:
       C^\bullet_{\mathrm{arith}}
       \longrightarrow
       (E^\bullet,Q)
   \]
   with dense image.  Its kernel is the closure of a specified regulator-null acyclic
   subcomplex, and it induces an isometric isomorphism on reduced cohomology after quotienting
   that subcomplex and completing.  Here \(E^\bullet\) is concentrated in leafwise degrees
   \(0,1,2\).  Integral torsion is allowed to vanish under realification and is not part of
   this faithfulness claim.

2. **Closed Hilbert differential.** \(Q\) is closed and densely defined, \(Q^2=0\), and its
   graph topology contains the completed Rost--Schmid residue topology.  Consequently `(2)`
   and `(3)` define
   \[
     H^q_{\mathrm{dyn},c}
       :=\bar H^q(E^\bullet,Q)
       \simeq\ker\Delta_q ,
     \qquad \Delta=QQ^\dagger+Q^\dagger Q.                              \tag{4}
   \]

3. **Cup, trace, and degree-two Poincaré duality.** The MW product and arithmetic
   Grothendieck--Witt trace extend continuously to \(E^\bullet\).  Their degree-two pairing
   is perfect on reduced cohomology and satisfies the differential and Frobenius adjunction
   laws required by the complementary Weil--Arakelov fiber pairing.

4. **Admissible global Hodge operator.** The real Betti--Deligne boundary,
   its complex-conjugation involution, and MW determinant orientation
   construct a closed anti-unitary
   \[
      J:\mathcal H^1\longrightarrow\mathcal H^1,\qquad J^2=-1.           \tag{5}
   \]
   It commutes with every descended residue and centered power map.  The
   Hermitian form
   \[
     \langle x,y\rangle=\operatorname{tr}(x\cup Jy)
   \]
   is positive definite on reduced harmonic \(H^1\).  No Gamma/CCM or
   Xi-divisor Hodge operator is an input.

5. **Centered unitary flow.** Each power correspondence \(F_n\) extends to a closed chain
   map \(T_n\) with weight-one metric law
   \[
      \langle T_nx,T_ny\rangle=n\langle x,y\rangle .
   \]
   Hence \(U_n=n^{-1/2}T_n\) is unitary, commutes with \(Q\), \(Q^\dagger\), \(\Delta\), and
   \(J\), and descends unitarily to \(\mathcal H^1\).  The coherent
   \(\mathbb Q_{>0}\)-suspension extends these maps to a strongly continuous
   \(\mathbb R\)-flow with closed generator
   \[
      \Theta=\tfrac12+S,\qquad S^\dagger=-S.                             \tag{6}
   \]

6. **Compatibility with the arithmetic specialization.** The ordinary and compact-support
   complexes obtained from `(4)` enter the Flach--Morin mapping-fiber equivalence
   \[
     R\Gamma_{\mathrm{ar},c}(\overline{\operatorname{Spec}\mathbb Z},
       \widetilde{\mathbb R}(n))
     \simeq
     \operatorname{Fib}(\Theta-n:R\Gamma_{\mathrm{dyn},c}
       \to R\Gamma_{\mathrm{dyn},c}),                                    \tag{7}
   \]
   and the pairing from clause 3 induces weight-complementary duality
   \(n\leftrightarrow1-n\) in total degree \(3\).

## Regulator factorization forced by the MW pullback

The real-place map should not be invented as one unexplained functional.  Use the homotopy
pullback
\[
 \widetilde{\mathsf M\mathbb Z}
 =
 \mathsf M\mathbb Z
 \mathop{\times}^{h}_{\mathsf M\mathbb Z/2}
 \mathsf W\mathbb Z.                                                       \tag{8}
\]
Construct its two real channels separately:

- the ordinary motivic channel maps through a Betti/Deligne regulator;
- the Witt channel maps through signature and the real-étale realization.  Bachmann's
  equivalence after \(\rho\)-inversion identifies this channel with stable homotopy on the
  real-étale site.

Compatibility mod \(2\) then gives a map out of `(8)` by the universal property of the
homotopy pullback.  Apply this construction to the MW symbol factor of the
leafwise unit-amalgamated coefficient.  The two maps must agree on the free
unit algebra \(\mathscr P_F\); the pushout universal property gives its
regulator.  Then `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON` must
transport it to the chartwise derived-section model.  If the optional
Milnor character realization is later constructed, the same regulator
also transports across
\(R\alpha_{F,*}\mathbb R\simeq\mathscr A^M_{F,\mathrm{geom}}\).
Because the full motivic symbol algebra already contains Steinberg
and all higher syzygies, no separate archimedean Steinberg attachment is allowed.  On
geometric stalks the MW-to-ordinary map is already an equivalence in nonnegative degree.
The regulator must instead compare the descended ordinary rank channel with the real
signature channel and form the arithmetic homotopy pullback.  This separates four
obligations:

1. compatibility of the topological Kummer regulator with the map
   \(\mathcal P_F\to C^*(X_F,\mathbb Z)\);
2. compatibility of the motivic regulator with every relative symbol cell, including
   Steinberg and higher syzygies;
3. signature compatibility with MW residues and determinant twists;
4. a unital rank/signature comparison whose homotopy pullback has exactly one degree-zero
   real constant.

`[CONJECTURE] [DAC_MW_REAL_REGULATOR_PULLBACK]` asserts that these maps exist on every
cyclotomic character chart, agree on \(\mathcal P_F\) and after mod-\(2\) realization,
respect the full relative cell presentation, admit the required unital rank/signature
comparison,
and induce clause 1 after Galois/residue/power descent and boundary gluing.  A mismatch in
the unit square, mod-\(2\) square, any higher symbol cell, or the rank/signature comparison
is a decisive falsifier.

## Step-by-step attack

1. Construct the ordinary and signature/real-étale regulator channels on
   the leafwise sheaf and diagonal motivic symbol algebras.
2. Prove agreement on \(\mathcal P_F\), mod-\(2\) compatibility, and compatibility with the
   full relative motivic cell presentation.
3. Use the pushout universal property to obtain a regulator on the
   leafwise unit-amalgamated coefficient; prove every Steinberg and
   higher-syzygy cell maps to a \(Q\)-boundary.
4. Construct the unital comparison from descended ordinary rank realization to the
   complexified real-signature realization; prove its homotopy pullback has \(H^0=\mathbb R\)
   and retains the twisted MW residue pairing.
5. Prove power-localized descent and compatibility with the unital Betti--Deligne gluing.
6. Prove residue estimates in the graph norm, then close \(Q\).  Do not assume closed range;
   reduced cohomology uses \(\overline{\operatorname{im}Q}\).
7. Construct the boundary conjugation/orientation operator on the
   three-term arithmetic complex.  Prove \(J^2=-1\), residue compatibility,
   power naturality, and positivity directly from the real regulator.
8. Extend centered power maps from the dense regulator image by isometry.  Use the abstract
   unitary BRST--Hodge theorem to descend them to `(4)`.
9. Establish strong continuity of the suspended action and identify its generator.
10. Feed the resulting three-term complex, pairing, and \(\Theta\) into `(7)`.

## Hostile audit and falsifiers

- A flat arithmetic coefficient is not automatically covered by known leafwise Hodge
  theorems.  Clause 2 is mandatory and cannot be replaced by a citation for untwisted forms.
- Density alone does not imply cohomological faithfulness.  Any non-torsion class surviving
  realification and reduced cohomology but killed by the regulator falsifies clause 1; the
  construction would then require all real and finite regulators or a stronger quotient
  theorem.  Torsion killed by tensoring with \(\mathbb R\) is expected and is not a falsifier.
- A positive operator on Gamma/CCM or the Xi target is irrelevant.  Failure
  to construct \(J\) from the real boundary of the actual
  unit-amalgamated coefficient falsifies clause 4.
- Local boundary positivity does not imply descent.  Failure of \(J\) to
  commute with either a unit-amalgamation cell or an MW residue falsifies
  clause 4.
- Pairwise power-map compatibility is insufficient for a flow.  Failure of coherent
  multiplicativity or strong continuity falsifies clause 5.
- No spectral claim occurs in clauses 1--6.  Identifying the spectrum of \(\Theta\) with zeta
  zeros is a later Lefschetz/determinant comparison, not an input here.

**Verdict:** `SURVIVES SOURCE CORRECTION`.  Abstract Hodge decomposition
and unitary descent are not the open mathematics.  Exact open core is the
realified, cohomologically faithful regulator of the leafwise
unit-amalgamated derived coefficient, closedness of its differential, and direct
construction of a positive boundary \(J\) compatible with
unit-amalgamation, residues, and power maps.  No CCM/Gamma Hodge model is a
dependency.

## References

- Christopher Deninger, *Number theory and dynamical systems on foliated spaces*:
  https://arxiv.org/abs/math/0204110
- Christopher Deninger and Wilhelm Singhof,
  *Real polarizable Hodge structures arising from foliations*:
  https://arxiv.org/abs/math/0204111
- Jesús A. Álvarez López, Yuri A. Kordyukov, Eric Leichtnam,
  *Analysis on Riemannian foliations of bounded geometry*:
  https://arxiv.org/abs/1905.12912
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Christopher Deninger, *Rational Witt vectors and associated sheaves*:
  https://arxiv.org/abs/2508.05329
- James D. Lewis, *Real regulators on Milnor complexes*:
  https://arxiv.org/abs/math/0012240
- Tom Bachmann, *Motivic and Real Étale Stable Homotopy Theory*:
  https://arxiv.org/abs/1608.08855
- Andreas Holmström, Jakob Scholbach, *Arakelov motivic cohomology I*:
  https://arxiv.org/abs/1012.2523
- Jacob Lurie, *Higher Algebra*:
  https://www.math.ias.edu/~lurie/papers/HA.pdf
