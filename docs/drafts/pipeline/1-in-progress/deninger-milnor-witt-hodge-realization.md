# Deninger polarized Milnor--Witt/ko flow realization

- **ID:** `deninger-milnor-witt-hodge-realization`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** `deninger-prime-holonomy-groupoid`
- **Source:** `docs/Deninger program.md` · Deninger 2024/2025 ·
  Kucharczyk--Scholze Question 1.10 · Kolderup--Röndigs--Østvær 2025 · Shin 2026
- **Statement:** The missing derived coefficient complex on Deninger's rational-Witt dynamical
  approximation is a polarized flow realization of integral Milnor--Witt motivic cohomology and
  very effective hermitian \(K\)-theory over \(\mathbb Z\), completed by the prime--Gamma source
  norm.

## Goal

Construct arithmetic \(H^0,H^1,H^2\), cup/Poincare duality, and positive odd Hodge theory from
arithmetic source data before any Xi-divisor comparison.  This card targets the exact
\(R\alpha_*\mathscr G\) coefficient complex proposed by Deninger for replacing the unknown true
space by his rational-Witt approximation.

## Gates

- [x] 0 → 1  in-progress: well-posed source, direct Deninger fit, hostile audit
- [ ] 1 → 2  fully-proven: arithmetic correspondence category, realization, and comparison proved
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Forced inputs

1. Deninger's system
   \[
     X_W=\check X_0(\mathbb C)_E\times_{\mathbb Q_{>0}}\mathbb R_{>0}
   \]
   has the correct continuous flow and compact prime packets, but is an infinite-dimensional
   approximation to a conjectural true space \(X_{\mathrm{arith}}\).
2. Deninger states that, given
   \(\alpha:X_{\mathrm{arith}}\to X_W\), the missing cohomology should be computed on \(X_W\)
   using a derived coefficient complex \(R\alpha_*\mathscr G\).
3. Kucharczyk--Scholze prove that the uncorrected rational-Witt space has exterior-algebra
   cohomology and that
   \[
     [a]\smile[1-a]\ne0,
   \]
   whereas arithmetic Milnor \(K\)-theory requires the Steinberg relation
   \(\{a,1-a\}=0\).  Their Question 1.10 asks for a corrected space freely adjoining this
   relation.
4. Deninger 2025 proves, for normal Noetherian affine \(X\),
   \[
     W_{\mathrm{rat}}(\mathcal O(X))
       \simeq \underline{\operatorname{Corr}}(X,\mathbb A^1),
   \]
   and identifies Frobenius and Verschiebung with pushforward and pullback under power maps.
   Ordinary finite correspondences therefore recover exactly the uncorrected rational-Witt
   object.
5. Finite Milnor--Witt correspondences refine ordinary finite correspondences by equipping
   finite cycles with quadratic forms.  Their motivic cohomology has diagonal part equal to
   Milnor--Witt \(K\)-theory, so the Steinberg relation and quadratic orientation are built into
   the same source.
6. `[REDISCOVERED]` Kolderup--Röndigs--Østvær define the integral Milnor--Witt motivic spectrum
   \[
     \widetilde{\mathrm M}\mathbb Z_X
       =\mathrm M\mathbb Z_X
          \times_{\mathrm M\mathbb Z_X/2}\mathrm W\mathbb Z_X
   \]
   for \(X\) essentially smooth over a Dedekind scheme, including
   \(X=\operatorname{Spec}\mathbb Z\), and extend it to arbitrary qcqs schemes by structural
   pullback.  They identify it as the arithmetic very-effective input to hermitian \(K\)-theory.
   Therefore inventing Milnor--Witt motivic cohomology over \(\mathbb Z\) is not an open
   obligation.
7. `[REDISCOVERED]` Very effective hermitian \(K\)-theory
   \(\mathrm{ko}_{\mathbb Z}\) exists without inverting \(2\).  Shin proves that
   \(\mathrm{ko}_S\) is a normed algebra for every qcqs \(S\), while framed-transfer machinery
   supplies finite-syntomic transfers.  This does not by itself construct Deninger's ramified
   power-map action or a flow realization.
8. `[DISPROVED AS STATED]` A bare degree-\(p\) Milnor--Witt transfer is not a positive real
   form.  Its quadratic multiplicity
   \(p_\epsilon\) has rank \(p\) but signature \(0\) for \(p=2\) and \(1\) for odd \(p\), hence is
   indefinite for every prime \(p>1\).  The exact no-go and survivor are recorded in
   `deninger-bare-milnor-witt-transfer-positivity`.
9. Bannwart identifies real Betti realization of very effective hermitian \(K\)-theory with
   connective \(L(\mathbb R)\).  Thus established Betti realization retains signature-type,
   potentially indefinite information; it is not the missing positive Gamma polarization.
10. `[REDISCOVERED / PAPER-CHECKED]` For every \(n\ge1\), the power map
    \(f_n:\mathbb A^1_{\mathbb Z}\to\mathbb A^1_{\mathbb Z}\), \(x\mapsto x^n\), is finite
    syntomic and framed.  Algebraically,
    \[
      \mathbb Z[y][x]/(x^n-y)\simeq\mathbb Z[x]
    \]
    is finite free with basis \(1,x,\ldots,x^{n-1}\); the monic equation \(x^n-y\) is a regular
    sequence of length one.  Shin's framed-transfer construction therefore supplies a framing
    \([L_{f_n}]\simeq0\), even though \(f_n\) is ramified.  Compatibility of these selected
    framings under \(f_mf_n=f_{mn}\) remains a separate coherence theorem.  The
    determinant-orientation part is now proved explicitly: the iterated cotangent matrix reduces
    by two determinant-one changes of basis to an identity block plus the direct
    \(mnx^{mn-1}\) differential.  Only coherent paths in the full \(K\)-theory framing space
    remain.

## Conjecture

`[CONJECTURE] [DAC_MILNOR_WITT_HODGE_REALIZATION]`:

There is a source-defined polarized cyclotomic realization
\[
  \operatorname{Real}^{\mathrm{pol}}_W:
    \left(\widetilde{\mathrm M}\mathbb Z_{\mathbb Z},
          \mathrm{ko}_{\mathbb Z},
          \Gamma_\infty\right)
      \longmapsto
    \mathscr A_{\mathrm{arith}}
      \in D_{\mathrm{flow}}\!\left(X_W;K_{\mathbb R}\right)
                                                               \tag{1}
\]
with the following properties.

1. The forgetful map from Milnor--Witt to ordinary motivic cohomology makes `(1)` recover
   Deninger's finite-correspondence/rational-Witt object before polarization.
2. On generic cyclotomic fibers, the Milnor--Witt layer has torsion-free
   Milnor--Witt \(K\)-cohomology.  In
   particular, the Steinberg class \([a]\smile[1-a]\) is null-homotopic at chain level.
3. The framed finite-syntomic lifts of \(u\mapsto u^n\) give Frobenius/Verschiebung operators.
   Their framings, dualizing twists, composition laws, and Deninger suspension relations are
   proved integrally, including ramification and residue characteristic \(2\).  Prime return has
   period \(\log p\).
4. The unpolarized degree-\(p\) transfer retains its canonical indefinite class \(p_\epsilon\);
   its rank \(p\) determines centered half-density.  No positivity claim is made at this layer.
5. The archimedean Gamma boundary constructs an additional polarization \(J_\infty\) on odd
   realized cohomology:
   \[
     J_\infty^2=-1,\qquad
     \langle x,y\rangle_H=\operatorname{tr}(x\smile J_\infty y),
   \]
   and proves \(\langle x,x\rangle_H>0\) for \(x\ne0\).  Centered power transfers commute with
   \(J_\infty\) and are unitary.  Locally this agrees with
   `deninger-rectangular-quaternionic-hodge`.
6. Prime--Gamma completion of `(1)` is determined by the source divided-difference cup kernel.
   Its reduced hypercohomology is concentrated in degrees \(0,1,2\), with
   \[
     H^0_{\mathrm{arith}}\simeq\mathbb C,\qquad
     H^2_{\mathrm{arith}}\simeq\mathbb C(-1).
   \]
7. Milnor--Witt/hermitian transfer gives chain cup product and Poincare duality; the independent
   Gamma polarization gives the positive Hodge metric.  Centered flow commutes with Hodge before
   spectral comparison.
8. There is a source-constructed dense flow-equivariant comparison from
   \(\overline{\mathbb H}^1(X_W,\mathscr A_{\mathrm{arith}})\) to the already formalized
   completed arithmetic \(H^1\), preserving cup and Green operators.  Xi-divisor coordinates
   may occur only after this map has been defined and proved isometric.

Properties 6--8 would close `[DAC_SOURCE_GREEN_PURITY]`; existing determinant, Lefschetz,
oriented-Hodge, and closed-generator theorems would then derive RH.

## Why Milnor--Witt rather than ordinary Milnor or metaplectic data

- Ordinary finite correspondences are already \(W_{\mathrm{rat}}\) and retain the known
  Steinberg defect.
- Milnor \(K\)-theory repairs additive/Steinberg descent but has no quadratic orientation from
  which to build a Hodge metric.
- A metaplectic double cover supplies square roots but forgets most universal Steinberg data.
- Milnor--Witt correspondences carry finite transfers, Steinberg relations, and quadratic forms
  before any analytic or representation-theoretic pushout.  Metaplectic/quaternionic
  representations may be a later real-realization functor, not the source category.

## Required proof obligations

1. Relate Deninger's ordinary finite correspondences to the integral spectrum
   \(\widetilde{\mathrm M}\mathbb Z_{\mathbb Z}\) and the very-effective slice tower of
   \(\mathrm{ko}_{\mathbb Z}\); do not replace this with the obsolete task of constructing MW
   theory over \(\mathbb Z\).
2. Lift the proved determinant-orientation coherence of the monic ramified power maps to
   coherent paths in the full framed-correspondence infinity-category, then prove the
   Frobenius/Verschiebung identities and dualizing-twist laws.
3. Construct `(1)` and identify its underlying ordinary realization with
   \(X_W\).
4. Construct \(J_\infty\) from the Gamma boundary and prove positivity and centered-transfer
   unitarity.  `deninger-gamma-rank-character-rigidity` shows that strict positivity on the
   hyperbolic class forces the scalar character to be rank and hence forces
   \(n_\epsilon\mapsto n\).  `deninger-hyperbolic-localization-rank-collapse` constructs that
   rank channel algebraically by \(GW\to GW[h^{-1}]\simeq\mathbb Z[1/2]\), so factorization of
   push--pull degree is automatic after base change.  Construction of its positive odd Hilbert
   realization and compatibility with the incidence differential remain mandatory.  A Witt
   class alone cannot discharge this obligation.
5. Build the prime--Gamma analytic completion and prove closedness, density, and discreteness
   properties needed for the determinant.
6. Prove chain-level comparison with the source packet quotient and with the determinant/Lefschetz
   carrier.
7. Prove Hodge-flow naturality without using Xi-zero location, Weil positivity, or an
   RH-equivalent faithful comparison assumption.
8. Realize the finite and cofinal construction in `deninger-mw-gamma-brst-complex`; generic
   colligation existence or finite Hodge theory without the MW incidence boundary does not count.

## Hostile audit

- `[RESOLVED / REDISCOVERED]` Milnor--Witt motivic cohomology over
  \(\operatorname{Spec}\mathbb Z\) already exists as an integral motivic spectrum.
  **Consequence:** frontier is realization and transfer compatibility, not source-spectrum
  existence.
- `[OBJECTION]` Shin's normed structure concerns normed motivic algebras and finite-étale norms;
  Deninger's \(u\mapsto u^p\) is ramified.
  **Required answer:** use and prove compatible framed finite-syntomic transfers, including their
  chosen cotangent-complex framings; never cite normedness alone.
- `[OBJECTION]` Rationalization can kill the \(2\)-primary/quaternionic information.
  **Required answer:** retain integral/hermitian data through real realization; rationalize only
  after the odd \(K_{\mathbb R}\) structure is fixed.
- `[OBJECTION / NO-GO]` Canonical quadratic multiplicity is indefinite over \(\mathbb R\).
  **Required answer:** construct the Gamma polarization independently, then prove it converts the
  source Poincare form into a positive metric and makes centered transfer unitary.
- `[OBJECTION]` Ordinary real Betti realization of \(\mathrm{ko}\) lands in connective
  \(L(\mathbb R)\), not an automatically positive Hilbert theory.
  **Required answer:** Gamma/rectangular polarization must be constructed as additional boundary
  data and related to Betti \(L\)-theory by a proved comparison.
- `[OBJECTION]` Motivic cohomology does not automatically contain the zeta-zero spectrum.
  **Required answer:** the flow suspension, prime--Gamma completion, determinant, and Lefschetz
  comparison are independent mandatory gates.
- `[OBJECTION]` Property 8 can hide RH.
  **Required answer:** comparison must be defined on finite correspondences and proved
  cup-isometric before any divisor evaluation.

## Verdict

`STRENGTHENED SURVIVOR`.  Integral MW/\(\mathrm{ko}\) source existence is literature-covered;
bare-transfer positivity is false.  Surviving open core is a polarized Deninger flow realization
whose Gamma boundary supplies positivity without divisor input.  No realization, comparison,
positivity, or RH claim is yet proved.

## Log

- 2026-07-26 — conjecture created from Deninger 2024's \(R\alpha_*\mathscr G\) prescription,
  Deninger 2025's finite-correspondence theorem, and Kucharczyk--Scholze Question 1.10.
- 2026-07-26 — literature audit found integral Milnor--Witt motivic cohomology over
  \(\mathbb Z\) and normed \(\mathrm{ko}\); obsolete extension obligation removed.
- 2026-07-26 — canonical \(p_\epsilon\) transfer shown indefinite; positivity separated as
  archimedean Gamma polarization.
- 2026-07-26 — proved rank-character rigidity: any positive scalar Gamma realization is forced
  to send \(p_\epsilon\) to \(p\).  This closes uniqueness of the scalar degree law, not
  existence or positivity of the realization.
- 2026-07-26 — hyperbolic localization \(GW[h^{-1}]\) constructed as the canonical rank channel;
  it forces \(p_\epsilon=p\) algebraically.  Remaining existence problem is now the positive
  Hilbert/Hodge realization, not the scalar coefficient algebra.

## References

- H. Kolderup, O. Röndigs, P. A. Østvær,
  *Hermitian K-theory and Milnor-Witt motivic cohomology over Z* (2025):
  https://arxiv.org/abs/2509.16404
- B. Shin, *Norms and Hermitian K-Theory* (2026):
  https://arxiv.org/abs/2602.03021
- J. Bannwart,
  *The real Betti realization of motivic Thom spectra and of very effective Hermitian K-theory*
  (2025): https://arxiv.org/abs/2505.07297
- B. Calmès, Y. Harpaz, D. Nardin,
  *A motivic spectrum representing hermitian K-theory* (2024):
  https://arxiv.org/abs/2402.15136
- F. Déglise, *Notes on Milnor--Witt K-theory* (2023):
  https://deglise.perso.math.cnrs.fr/docs/2023/KMW.pdf
