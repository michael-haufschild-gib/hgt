# Deninger rational-Witt finite transverse visibility

- **ID:** `deninger-rational-witt-finite-transverse-visibility`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `deninger-prime-packet-topology-haar-retraction`
- **Statement:** complexified finite cyclotomic orbit traces span every function on each finite
  Frobenius packet; all prime-to-\(p\) stages jointly recover the literal packet quotient, and
  each orbit trace is an arithmetic-Frobenius-fixed element of Deninger's published
  complexified rational-Witt presentation.  Such single-stage rational-Witt restrictions are
  uniformly dense and Haar-\(L^2\)-dense on the literal packet.  Explicit moduli \(8\) and \(15\)
  already give strictly positive literal arithmetic Haar--Green energy at every prime.

## Goal

Close the finite-cyclotomic external-source gate in Route L.  The previous packet Haar target was
faithful but no arithmetic source theorem showed that any mean-zero packet mode reached it.  This
card first proves such reachability from finite cyclotomic evaluation data, identifies every
generator with an arithmetic-Frobenius-fixed element in the published rational-Witt
reduced-monoid-algebra presentation, then proves that the whole directed prime-to-\(p\) system is
cofinal.  Its quotient functions separate every two points of the literal packet and their
single-stage union is dense in the full packet Haar space.

It does **not** construct Deninger's missing relevant complex, the global rational-Witt
derived-section comparison, an all-prime Bessel map from one common source, or Xi spectral
inclusion.

## Gates

- [x] 0 → 1 in-progress: source-pure finite cyclotomic restriction and Fourier attack
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: unconditional Lean modules listed below; targeted builds and axiom audit
- [ ] 3 → 4 publication-ready: external novelty/expert audit and relevant-complex integration

## Published source identification

Deninger's rational-Witt construction supplies the source interpretation used here:

1. for a perfect field \(A\),
   \[
   W_{\mathrm{rat}}(A)
   =
   \bigl(\underline{\mathbb Z}\,\overline A\bigr)^G ;
   \]
2. rational Witt vectors act as complex-valued functions on the associated character space;
3. Teichmüller/monoid elements evaluate through multiplicative characters.

See Deninger, *Dynamical systems for arithmetic schemes* (2018/2024), and Deninger,
*Rational Witt vectors and associated sheaves* (2025), especially the invariant reduced-monoid
description and the map \(W_{\mathrm{rat}}(A)\to C(X_A,\mathbb C)\).

The Lean development uses the right side of Deninger's published finite-field isomorphism as the
chosen presentation:
\[
 \mathbb C\otimes W_{\mathrm{rat}}(\overline{\mathbb F}_p)
 \cong \mathbb C[\overline{\mathbb F}_p^\times].
\]
It formalizes the algebraic closure, its actual multiplicative group, the actual arithmetic
Frobenius, the finite cyclotomic group-algebra inclusions, and character evaluation.  It does not
re-prove Deninger's rational-function-to-reduced-monoid-algebra isomorphism inside Lean.  That
published theorem is an explicit source dependency, not an invented `W_rat` object.

## Finite Fourier theorem

Fix \(n>0\), \(p\) coprime to \(n\), and write
\[
 U_n=(\mathbb Z/n\mathbb Z)^\times,\qquad
 H_{p,n}=\langle p\bmod n\rangle,\qquad
 Q_{p,n}=U_n/H_{p,n}.
\]
For \(j\in\mathbb Z/n\mathbb Z\), define
\[
 e_j(u)=\exp(2\pi iju/n),\qquad
 E_j([u])=\frac1{|H_{p,n}|}\sum_{h\in H_{p,n}}e_j(uh).             \tag{1}
\]

`[PROVED HERE] [DAC_FINITE_FROBENIUS_ORBIT_EVALUATION_SPAN]`

Every function \(F:Q_{p,n}\to\mathbb C\) has an exact expansion
\[
 F(q)=\sum_{j\in\mathbb Z/n\mathbb Z}c_jE_j(q).                   \tag{2}
\]

### Proof

Lift \(F\) to the \(H_{p,n}\)-invariant function \(f:U_n\to\mathbb C\), then extend \(f\) by
zero to \(\mathbb Z/n\mathbb Z\).  Discrete Fourier inversion gives
\[
 f(u)=\sum_j c_j e_j(u).
\]
Average this equality over \(uH_{p,n}\).  The left side remains \(f(u)\) by invariance.  Finite
sum interchange turns the right side into \(\sum_jc_jE_j([u])\), proving `(2)`.  Invariance of
`(1)` follows by reindexing \(H_{p,n}\) under multiplication.

This uses standard finite Fourier inversion.  New content for this project is the exact
Frobenius-orbit restriction theorem and its consequences below, not the DFT itself.

## Uniform nontrivial detector

For a rational prime \(p\), set
\[
 n_p=
 \begin{cases}
 15,&p=2,\\
 8,&p\ne2.
 \end{cases}
\]
Then \((p,n_p)=1\), while \(U_{n_p}\) is noncyclic:
\[
 U_8\ \text{is noncyclic},\qquad
 U_{15}\cong U_3\times U_5\ \text{is noncyclic}.
\]
Since \(H_{p,n_p}\) is cyclic, \(Q_{p,n_p}\) is nontrivial.  Applying `(2)` to a difference of
two point indicators produces coefficients \(c_j\) whose orbit-evaluation combination is
nonzero and has total sum zero on \(Q_{p,n_p}\).

## Weld to the literal packet

Let
\[
 B_p=
 \left(\prod_{\ell\ne p}\mathbb Z_\ell^\times\right)/
 \overline{\langle p\rangle}.
\]
There is a continuous surjective homomorphism
\[
 \pi_p:B_p\twoheadrightarrow Q_{p,n_p}.                           \tag{3}
\]

For odd \(p\), `(3)` is reduction of the \(2\)-adic coordinate modulo \(8\).  For \(p=2\), it is
the product of reductions modulo \(3\) and \(5\), recombined modulo \(15\) by CRT.  Both maps are
surjective.  They send the literal diagonal packet Frobenius to \(p\bmod n_p\).  The preimage of
\(H_{p,n_p}\) is closed and contains \(\langle p\rangle\), hence contains its closure; therefore
the map descends to `(3)`.

Surjectivity makes pullback
\[
 \pi_p^*:\operatorname{Fun}(Q_{p,n_p},\mathbb C)
 \hookrightarrow C(B_p,\mathbb C)                                \tag{4}
\]
injective.  Equations `(2)` and `(4)` show that the entire finite-dimensional image of `(4)` is
spanned by pulled-back Frobenius-orbit root evaluations.  In particular it contains a
nonconstant mode at every prime.

## Cofinal finite-stage recovery of the literal packet

Let
\[
 U_p=\prod_{\ell\ne p}\mathbb Z_\ell^\times,\qquad
 B_p=U_p/\overline{\langle p\rangle}.
\]
For every \(n>0\) coprime to \(p\), CRT and the \(\ell\)-adic coordinate reductions give a
continuous surjective homomorphism
\[
 r_{p,n}:U_p\twoheadrightarrow U_n.
\]
It sends the literal diagonal packet element to \(p\bmod n\), hence descends to
\[
 \bar r_{p,n}:B_p\twoheadrightarrow Q_{p,n}.                     \tag{5}
\]
If \(n\mid m\), reduction from \(m\) to \(n\) makes these maps commute.  The stages are directed
by divisibility.

`[PROVED HERE] [DAC_LITERAL_PACKET_FINITE_CYCLOTOMIC_COFINALITY]`

The literal Frobenius closure is recovered exactly from all finite stages:
\[
 \overline{\langle p\rangle}
 =
 \bigcap_{\substack{n>0\\(n,p)=1}}
 r_{p,n}^{-1}\bigl(\langle p\bmod n\rangle\bigr).                \tag{6}
\]
Consequently the maps `(5)` are jointly injective on \(B_p\): for \(x,y\in B_p\),
\[
 \bigl(\forall n,\ \bar r_{p,n}(x)=\bar r_{p,n}(y)\bigr)
 \quad\Longrightarrow\quad x=y.                                 \tag{7}
\]

### Hard direction of `(6)`

The forward inclusion is closure functoriality.  For the reverse inclusion, embed \(U_p\)
faithfully into the product of its finite prime-power unit quotients.  If \(x\) is outside
\(\overline{\langle p\rangle}\), compactness and the product topology produce a basic open
neighbourhood of \(x\), depending on finitely many prime-power coordinates, which misses the
closure.  Multiply those prime powers to obtain one prime-to-\(p\) modulus \(n\).  Membership of
\(r_{p,n}(x)\) in \(\langle p\bmod n\rangle\) would supply one common exponent whose diagonal
Frobenius power agrees with \(x\) in every selected coordinate, placing that power in the
forbidden neighbourhood.  This contradiction proves `(6)`.

This is stronger than checking every coordinate independently: the composite modulus forces one
simultaneous Frobenius exponent across the selected coordinates.

## Exact dense orbit-evaluation algebra

Let \(\mathcal A_p\subset C(B_p,\mathbb R)\) be the functions which factor through one finite
quotient `(5)`.  Directed refinement makes \(\mathcal A_p\) a real subalgebra: two functions
factoring at different stages both factor through a common multiple.  It contains constants and,
by `(7)`, separates points.  Real Stone--Weierstrass therefore gives
\[
 \overline{\mathcal A_p}^{\,\|\cdot\|_\infty}=C(B_p,\mathbb R).  \tag{8}
\]
The finite Fourier theorem `(2)` says more than cylinder density: every member of
\(\mathcal A_p\), not merely an approximation to it, is one exact finite linear combination of
Frobenius-orbit root evaluations at a single stage.

The canonical map \(C(B_p,\mathbb R)\to L^2(B_p,\mathrm{Haar};\mathbb R)\) has dense range.
Combining this with `(8)` proves
\[
 \overline{\operatorname{im}\bigl(
   \mathcal A_p\longrightarrow L^2(B_p,\mathrm{Haar};\mathbb R)
 \bigr)}
 =
 L^2(B_p,\mathrm{Haar};\mathbb R).                              \tag{9}
\]
Thus finite rational-cyclotomic orbit evaluations do not expose only one transverse witness:
they densely exhaust the literal packet Haar fibre.

## Rational-Witt source admission

Set
\[
 \mathscr W_{p,\mathbb C}
 =
 \mathbb C[\overline{\mathbb F}_p^\times],
\qquad
 \Phi_p([a])=[a^p].
\]
By Deninger's reduced-monoid-algebra presentation and Galois descent,
\(\mathscr W_{p,\mathbb C}^{\Phi_p}\) is the complexified
rational-Witt source over \(\mathbb F_p\).

Choose a primitive \(n\)-th root \(\zeta_n\in\overline{\mathbb F}_p^\times\).  Since
\((n,p)=1\), the map
\[
 \iota_{p,n}:\mathbb C[\mu_n]\hookrightarrow\mathscr W_{p,\mathbb C},
 \qquad e_j\longmapsto[\zeta_n^j]                                 \tag{10}
\]
is injective.  Finite and arithmetic Frobenius commute:
\[
 \Phi_p\iota_{p,n}(e_j)
 =[\zeta_n^{pj}]
 =\iota_{p,n}(e_{pj}).                                            \tag{11}
\]
Define the normalized orbit trace
\[
 \tau_{p,n,j}
 =
 \frac1{|H_{p,n}|}\sum_{h\in H_{p,n}}e_{jh}
 \in\mathbb C[\mu_n].                                             \tag{12}
\]
Right multiplication permutes \(H_{p,n}\), so `(11)` gives
\[
 \Phi_p\bigl(\iota_{p,n}(\tau_{p,n,j})\bigr)
 =\iota_{p,n}(\tau_{p,n,j}).                                      \tag{13}
\]
For the packet character indexed by \(u\in U_n\), direct evaluation gives
\[
 \operatorname{ev}_u(\tau_{p,n,j})
 =
 \frac1{|H_{p,n}|}\sum_{h\in H_{p,n}}
   \exp(2\pi i jhu/n)
 =E_j([u]).                                                       \tag{14}
\]

`[PROVED HERE] [DAC_RATIONAL_WITT_FINITE_PACKET_RESTRICTION_SURJECTIVE]`

Combining `(2)` and `(12)`--`(14)`, every
\(F:Q_{p,n}\to\mathbb C\) has a witness
\[
 w_F=\sum_jc_j\tau_{p,n,j}
 \in\mathbb C[\mu_n]
\]
whose image under `(10)` is fixed by actual arithmetic Frobenius and whose character restriction
is exactly \(F\).  Applied to \(\mathcal A_p\), every member of the uniformly dense and
Haar-\(L^2\)-dense algebra `(8)`--`(9)` therefore has an actual complexified rational-Witt
finite-stage witness.  Finite source admission is now a theorem, not an interpretation attached
after constructing the target.

## Haar and Green consequence

Take a nonconstant complex combination in `(4)`.  At least one of its real and imaginary parts
is nonconstant.  Subtract its normalized Haar average.  The resulting continuous real function
\(f_p\) has
\[
 \operatorname{Av}_p(f_p)=0,\qquad f_p\ne0.                      \tag{15}
\]
Normalized Haar measure has full support, so the continuous-to-\(L^2\) map is injective and
\([f_p]\ne0\) in packet Haar \(L^2\).  The canonical packet/arithmetic Haar linear isometry keeps
it nonzero on
\[
 \operatorname{Aut}(\overline{\mathbb F}_p^\times)/
 \overline{\langle\operatorname{Frob}_p\rangle}.
\]
Embedding this vector at coordinate \(p\) in the all-prime Hilbert sum gives strictly positive
global arithmetic Green energy, because the global Green radical is zero.

Thus Route L's old scalar-collapse problem is not merely avoided by choosing a larger target:
finite cyclotomic source evaluations provably reach nonzero mean-zero energy in that literal
arithmetic target.

## Lean certificate

- `DeningerFiniteFrobeniusOrbitEvaluationSpan.lean`
  - `deningerFiniteFrobeniusOrbitEvaluation_span`
  - `deningerPrimeTransverseFinitePacket_exists_zeroSum_nonzero`
- `DeningerPrimeTransverseEvaluationRestriction.lean`
  - `deningerPrimeTransverseQuotientReduction_surjective`
  - `deningerPrimeTransverseQuotientReduction_pullback_injective`
  - `deningerPrimeTransverseOrbitEvaluation_span_pullback`
  - `deningerPrimeTransverseOrbitEvaluation_exists_nonconstant`
- `DeningerPrimeTransverseEvaluationHaarL2.lean`
  - `deningerPrimeTransverseOrbitEvaluation_exists_nonzero_meanZeroHaarMode`
  - `deningerPrimeTransverseOrbitEvaluation_exists_nonzero_arithmeticHaarMode`
  - `deningerPrimeTransverseOrbitEvaluation_exists_pos_arithmeticGreenEnergy`
- `DeningerPrimeArithmeticHaarL2Comparison.lean`
- `DeningerPrimeArithmeticHaarL2Green.lean`
- `DeningerFiniteFrobeniusEvaluationSystem.lean`
  - `deningerFiniteUnitEvaluation_stageReduction`
  - `deningerFiniteFrobeniusStageFunctionPullback_orbitEvaluation_span`
- `DeningerPrimeFiniteCyclotomicReductionSystem.lean`
  - `deningerPacketFrobeniusClosure_eq_iInf_finiteStages`
  - `deningerPrimeFiniteStageQuotientReduction_jointly_injective`
  - `deningerPrimeFiniteStageRealSubalgebra_dense`
  - `deningerPrimeFiniteStageRealSubalgebra_orbitEvaluation_span`
  - `deningerPrimeFiniteStageRealSubalgebraToHaarL2_denseRange`
- `DeningerRationalWittFiniteEvaluationBridge.lean`
  - `deningerPrimeFiniteCyclotomicWittInclusion_injective`
  - `deningerPrimeFiniteCyclotomicWittInclusion_frobenius`
  - `deningerFiniteCyclotomicWittEvaluation_orbitTrace`
  - `deningerFiniteCyclotomicWittFrobenius_orbitTrace`
  - `deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective`
  - `deningerPrimeFiniteStageRealSubalgebra_has_rationalWittWitness`

All theorem statements are unconditional.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Novelty and theatre audit

- **Known ingredients:** finite DFT; CRT; noncyclicity of \(U_8,U_{15}\); profinite
  finite-coordinate neighbourhoods; Stone--Weierstrass; compact-group Haar functoriality;
  Deninger's invariant reduced-monoid description of rational Witt vectors.
- **New project-level theorem:** full finite Frobenius-packet visibility by orbit traces, exact
  finite-stage recovery `(6)` of the literal Frobenius closure, joint quotient separation `(7)`,
  exact single-stage orbit-evaluation density `(8)`--`(9)`, actual Frobenius-fixed
  rational-Witt admission `(10)`--`(14)`, a uniform \(8/15\) transverse detector, and
  source-generated strictly positive literal arithmetic Green energy.
- **Literature check:** targeted primary-source search found Deninger's packet and rational-Witt
  function maps, but not theorem `(2)`, the uniform detector, or Haar--Green consequence.
  External expert novelty review remains required before publication.
- **Non-circularity:** no Xi divisor, RH, positivity hypothesis, or post hoc divisor-indexed
  Hilbert space appears.  Positivity follows only after an independently constructed source mode
  enters the already faithful arithmetic Haar target.
- **Theatre check:** `(6)`--`(14)` remove two real escape hatches: no hidden packet direction
  evades all finite restrictions, and those restrictions now arise from arithmetic-Frobenius-fixed
  elements of the published rational-Witt presentation.  The proof does not call a generic
  cylinder algebra `W_rat`, confuse rational-Witt geometry with the missing coefficient complex,
  or infer a relevant-complex theorem from Stone--Weierstrass.
- **Remaining hard frontier:** construct the actual relevant coefficient complex on Deninger's
  rational-Witt geometry and prove that its source-to-packet restriction contains the now-formal
  Frobenius-fixed rational-Witt finite stages; prove a global Bessel comparison with simultaneous
  kernel equal to closed middle boundaries; then cup/trace/Hodge and Xi spectral inclusion.
  This theorem does not fake those steps.

## Log

- 2026-08-01 — finite Fourier/orbit-trace span proved; uniform mod-\(8/15\) detector found.
- 2026-08-01 — continuous surjective weld to literal packet quotient proved.
- 2026-08-01 — faithful finite source subspace, nonzero mean-zero Haar mode, literal arithmetic
  mode, and positive all-prime Green energy formalized.
- 2026-08-01 — all prime-to-\(p\) reductions constructed; literal Frobenius closure recovered as
  their exact intersection; finite quotient maps proved jointly injective.
- 2026-08-01 — single-stage finite orbit-evaluation algebra proved uniformly dense and
  Haar-\(L^2\)-dense in the full literal packet.
- 2026-08-01 — finite cyclotomic group algebras embedded injectively into the actual
  \(\mathbb C[\overline{\mathbb F}_p^\times]\) rational-Witt presentation; Frobenius
  intertwining, fixed orbit traces, exact evaluation, and surjective finite restriction
  formalized.
