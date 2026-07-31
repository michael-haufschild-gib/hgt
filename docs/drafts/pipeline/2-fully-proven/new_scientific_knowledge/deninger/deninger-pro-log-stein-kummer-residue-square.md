# Pro-log-Stein Kummer residue square

- **ID:** `deninger-pro-log-stein-kummer-residue-square`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ANALYTIC RESIDUE THEOREM
- **Labels:** `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`,
  `DAC_SOURCE_STRATUM_RESIDUE_SHEAF_MORPHISM_FINITE`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** finite character-lattice log-toric completions construct
  the analytic Kummer generator residue; their filtered equivariant
  colimit gives the finite-place residue morphism on Deninger's
  sheafified Tate--Milnor coefficient.

## Finite log-toric stage

Let \(F\) be a characteristic-zero algebraic field, let \(v\) be a
discrete valuation with algebraically closed residue field \(k\), and put
\[
 V_F=(F^\times/\mu(F))\otimes_{\mathbb Z}\mathbb Q.
\]
Choose a finite-dimensional subspace \(W\subset V_F\) and a full lattice
\(L\subset W\) on which \(v\) is integral.  After replacing \(L\) by a
finite-index lattice, the nonzero homomorphism
\[
 \lambda_v=v|_L:L\longrightarrow\mathbb Z                          \tag{1}
\]
is primitive.  Set
\[
 L_{\geq0}=\{\ell\in L:\lambda_v(\ell)\geq0\}.
\]
Define
\[
 Z_L=\operatorname{Hom}(L,\mathbb C^\times),\qquad
 \overline Z_{L,v}
 =\operatorname{Hom}_{\mathrm{mon}}(L_{\geq0},\mathbb C),           \tag{2}
\]
where monoid maps send \(0\) to \(1\).

Choose \(\pi\in L\) with \(\lambda_v(\pi)=1\).  Then
\[
 L=\ker\lambda_v\oplus\mathbb Z\pi
\]
and
\[
 \overline Z_{L,v}
 \cong
 \operatorname{Hom}(\ker\lambda_v,\mathbb C^\times)
 \times\mathbb C,\qquad
 D_{L,v}\cong
 \operatorname{Hom}(\ker\lambda_v,\mathbb C^\times)\times\{0\}.
                                                                    \tag{3}
\]
Thus \(\overline Z_{L,v}\) is Stein, \(D_{L,v}\) is a smooth divisor,
and its complement is \(Z_L\).

The reduction homomorphism on valuation-zero elements gives a finite
group
\[
 \overline L_v
 =
 \operatorname{im}\!
 \left(\ker\lambda_v\longrightarrow k^\times\right).               \tag{4}
\]
It is finite because \(\ker\lambda_v\) is finitely generated and
\(k^\times\) is torsion.  The finite Deninger injective
residue-character locus is
\[
 Y_{L,v}=\operatorname{Emb}(\overline L_v,\mathbb C^\times),        \tag{5}
\]
embedded in \(D_{L,v}\) by precomposition with reduction.

## Logarithmic residue

Let \(\Omega^\bullet_{\overline Z_{L,v}}(\log D_{L,v})\) be the
holomorphic logarithmic de Rham algebra.  Poincaré residue gives
\[
 \operatorname{Res}_{L,v}:
 \Omega^n_{\overline Z_{L,v}}(\log D_{L,v})
 \longrightarrow
 i_*\Omega^{n-1}_{D_{L,v}}.                                       \tag{6}
\]
Locally every form has a unique expression
\[
 \omega=\alpha+\frac{dz}{z}\wedge\beta,
\qquad
 \operatorname{Res}_{L,v}(\omega)=\beta|_{z=0}.                    \tag{7}
\]
Evaluation on the finite set `(5)`, followed by the fact that its
positive differential forms vanish, gives
\[
 \rho_{L,v}:
 \Omega^\bullet_{\overline Z_{L,v}}(\log D_{L,v})|_{Z_L}
 \longrightarrow
 \operatorname{Map}(Y_{L,v},\mathbb C)(-1)[-1].                   \tag{8}
\]
The degree-zero specialization and `(8)` combine to a map of graded
commutative algebras to a split square-zero extension.

`[PROVED HERE] [DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE]`

For every \(a\in L\),
\[
 \rho_{L,v}\bigl(d\log\chi^a\bigr)
 =
 v(a)\,\mathbf 1_{Y_{L,v}}.                                       \tag{9}
\]
Under the analytic Kummer map and the real Milnor symbol map, `(9)` is
the commutative square
\[
\begin{CD}
 L\otimes\mathbb R @>{a\mapsto d\log\chi^a}>>
 \Omega^1_{\log}(Z_L)\\
 @V{v}VV @VV{\rho_{L,v}}V\\
 \mathbb R @>{c\mapsto c\mathbf1}>>
 \operatorname{Map}(Y_{L,v},\mathbb C).
\end{CD}                                                           \tag{10}
\]
It agrees with the real tame residue
\[
 \partial_v:K_1^M(F)\otimes\mathbb R
 \longrightarrow K_0^M(k)\otimes\mathbb R\cong\mathbb R.           \tag{11}
\]

### Proof

Write \(a=a_0+\lambda_v(a)\pi\), with
\(a_0\in\ker\lambda_v\).  In the coordinate `(3)`,
\[
 \chi^a=\chi^{a_0}z^{\lambda_v(a)}
\]
and hence
\[
 d\log\chi^a
 =
 d\log\chi^{a_0}
 +\lambda_v(a)\frac{dz}{z}.
\]
Formula `(7)` proves `(9)`.  The tame residue in degree one is the
valuation, proving `(10)`--`(11)`.

\(\Omega^\bullet_{\log}\) and `(8)` are written over \(\mathbb C\).
They are equivariant for the antilinear conjugation involution, and
their conjugation-fixed subcomplex gives the real complete locally
convex form used by the arithmetic construction.  The Kummer and Milnor
residue in `(10)` lands in its canonical real constant line.

Changing the uniformizer to \(\pi+u\) in additive lattice notation,
with \(u\in\ker\lambda_v\), replaces \(dz/z\) by
\(dz/z+d\log\chi^u\); the added term has zero residue.  Hence the map is
independent of the splitting used in `(3)`.

For products, `(7)` gives the graded Leibniz rule relative to boundary
specialization.  Equivalently, specialization plus residue is a map to
the split square-zero algebra.  On the Milnor side this is exactly the
realification of Milnor's algebra
\[
 K_*^M(k)[\Pi]/(\Pi^2-\{-1\}\Pi);
\]
\(\{-1\}\) vanishes over \(\mathbb R\).  Thus the two square-zero lifts
agree on the free unit algebra, not only on \(K_1\).

By `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`, they induce a
unique residue on the derived unit-amalgamation pushout at this finite
stage.  Every Steinberg relation, Tate-weight product, and higher
relative cell is therefore automatic.

## Acyclicity and filtered passage

The logarithmic form sheaves in `(6)` are locally free coherent sheaves
on the Stein manifold `(3)`.  Cartan theorem B makes them acyclic.
The Poincaré residue sequence
\[
 0\longrightarrow
 \Omega^n_{\overline Z_{L,v}}
 \longrightarrow
 \Omega^n_{\overline Z_{L,v}}(\log D_{L,v})
 \xrightarrow{\operatorname{Res}}
 i_*\Omega^{n-1}_{D_{L,v}}
 \longrightarrow0                                                 \tag{12}
\]
is strict at the finite Fréchet stage.  Therefore derived global
sections commute with every finite relative Milnor-cell attachment and
with `(8)`.

The logarithmic Poincaré lemma gives
\[
 Rj_*\mathbb C_{Z_L}
 \simeq
 \Omega^\bullet_{\overline Z_{L,v}}(\log D_{L,v}).               \tag{12a}
\]
Consequently replacing unrestricted punctured-torus forms by their
log-extendable model does not change finite-stage generic cohomology.
It only supplies boundary specialization and residue, which the
unrestricted holomorphic algebra lacks.

Finite-index lattice changes are power isogenies.  Enlarging \(W\)
is a coordinate projection.  Pullback of logarithmic forms commutes with
Poincaré residue, so the maps `(8)` form a compatible filtered system.
Taking the exact filtered colimit gives the pro-log cylinder sheaf
\[
 \Omega^\bullet_{\mathrm{cyl},F}(\log v)
 =
 \varinjlim_{(W,L)}
 \Omega^\bullet_{\overline Z_{L,v}}(\log D_{L,v})                  \tag{13}
\]
and a residue morphism to the locally constant functions on the
geometric \(v\)-packet.

The actual Deninger residue characters at a finite stage are precisely
the points `(5)`: a characteristic-\(p\) multiplicative character
evaluates a valuation-zero element through its reduction in \(k^\times\).
Consequently `(13)` is a cylinder-log sheaf on Deninger's actual
generic-plus-\(v\) character subspace, not an auxiliary replacement
space.  The ambient toric boundary may contain extra characters, but
`(8)` restricts to the source-defined locus `(5)` before the filtered
limit.

Tensoring with smooth transverse functions and all Tate weights gives
the suspension-cover residue
\[
 \widetilde\partial_v:
 \widetilde{\mathscr A}_\eta^M
 \longrightarrow
 \widetilde{\mathscr A}_v^M(-1)[-1].                              \tag{14}
\]
It is continuous, has closed scalar image at each prime by
`DAC_DENINGER_PRIME_PACKET_HAAR_RETRACTION`, and commutes with
restriction.

## Equivariance and correspondences

For a positive rational power \(q\),
\[
 v(a^q)=qv(a).
\]
The target normal line in `(14)` has Tate weight \(-1\), so its
\(q^{-1}\) action cancels this factor.  Hence `(14)` is power
equivariant.  Galois maps permute geometric valuations over the same
closed point and preserve `(9)`, so their direct sum descends.

For a finite extension and a valuation \(w|v\), a local parameter
satisfies
\[
 t=u s^{e(w/v)}
\]
with \(u\) a unit.  Therefore
\[
 d\log t=d\log u+e(w/v)d\log s.
\]
Taking Poincaré residues gives the ramification factor, and summing
over \(w|v\) with residue-field trace gives the standard
residue/corestriction identity for Milnor cycle modules.  Thus the
analytic and algebraic finite-correspondence maps agree on the free unit
algebra; universal descent makes `(14)` correspondence-natural.

All operations commute with the \(\mathbb Q_{>0}\)-action on the
suspension cover.  `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE` therefore
passes `(14)` through degreewise underived invariants and gives
\[
 \partial_{p,\mathrm{coarse}}:
 Rj_*\mathscr A_\eta
 \longrightarrow
 Ri_{p,*}\mathscr A_p(-1)[-1]                                    \tag{15}
\]
on Deninger's actual coarse generic and prime strata.

`[PROVED HERE] [DAC_SOURCE_STRATUM_RESIDUE_SHEAF_MORPHISM_FINITE]`

The family `(15)` is the finite-place component of the source stratum
residue morphism.  On every Kummer generator it is the generalized-log
valuation, and it is defined on all relative Tate--Milnor cells.

## Boundary of the theorem

This theorem does not yet:

1. prove that the family over all primes extends to the completed
   restricted sum;
2. construct the real Milnor--Witt/signature component;
3. identify endpoint cohomology after adjoining that real component;
4. prove cup--trace duality, Hodge positivity, Lefschetz trace, or a
   determinant formula.

These are respectively
`DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`,
the real part of `DAC_SOURCE_STRATUM_RESIDUE_SHEAF_MORPHISM`, and the
later arithmetic-cohomology gates.

## Hostile audit

- No ordinary analytic Cartier divisor \([p]\) is asserted.  The
  multiplicity is the valuation in `(1)` and the analytic map is
  Poincaré residue on a chosen log extension.
- Full holomorphic functions on a punctured torus can have essential
  singularities.  The arithmetic coefficient uses the log-extendable
  cylinder subalgebra `(13)`, whose finite-stage inclusion computes the
  same torus cohomology but has a defined residue.
- Extra points of the toric divisor are discarded by restriction to
  the actual residue-character locus `(5)`; they are not added to
  Deninger's space.
- Finite-stage boundary characters are not silently treated as a
  connected divisor.  Their filtered limit is the profinite packet
  transversal proved in
  `DAC_DENINGER_PRIME_PACKET_HAAR_RETRACTION`.
- The theorem constructs each finite component.  It does not commute an
  infinite coproduct with derived global sections.
- No quotient stack, derived group invariants, CCM model, zeta zero, or
  RH premise is used.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  character topology, Definition 10.1, and §§11--12:
  https://arxiv.org/abs/1807.06400
- Pierre Deligne, *Théorie de Hodge II*, logarithmic de Rham complexes
  and Poincaré residue.
- Henri Cartan, Theorem B for coherent analytic sheaves on Stein spaces.
- John Milnor, *Introduction to Algebraic K-Theory*, tame residues.
- `DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF`
- `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`
- `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`
- `DAC_DENINGER_PRIME_PACKET_HAAR_RETRACTION`

## Novelty audit

Finite log-toric residues and real Milnor residues are standard.
New program-level content is their source-compatible assembly:
log-extendable cylinder forms retain the generic pro-Stein comparison,
restrict to Deninger's actual finite residue-character loci, and make
the analytic Kummer boundary equal the arithmetic valuation before
coarse invariants.  This removes the need for unsupported ordinary
Cartier purity of Deninger's generalized function \([p]\).

**Verdict:** `FULLY PROVEN ON PAPER; FINITE-PLACE SOURCE RESIDUE
MORPHISM CONSTRUCTED ON ALL TATE--MILNOR CELLS; ALL-PRIME COMPLETION
AND REAL SIGNATURE REMAIN OPEN`.
