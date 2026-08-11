# Gamma-six orientation asymmetry and the cofinal residue wall

- **Stage:** 2 — dependency-closed paper proof
- **Type:** SHARP NO-GO / POSITIVE RESIDUE CLASSIFICATION / ROUTE-L FRONTIER CORRECTION
- **Status:** PAPER-PROVED / PROJECT-SPECIFIC NEW KNOWLEDGE / NOT RH / NO LEAN WORK DURING CORPUS REFACTOR
- **Parent:** deninger-mobius-gamma-six-normal-transgression.md
- **Corpus inputs:** MobiusThetaPhysicalSourceToXiLanding.lean,
  DeningerCollarExchange.lean, DeningerAdiabaticContragredient.lean,
  DeningerEulerDepletionTower.lean, AdelicPhaseDefectCharacterBlindnessLaw.lean, and
  RouteRAdelicDefectCharacterBlindness.lean.

## 1. Question corrected by this note

The Gamma-six construction produces both algebraic normal orientations

\[
 [6^m]-1,
 \qquad
 [6^{-m}]-1,
\tag{1}
\]

and finite Tate--Wold primitives for both. It does **not** follow that both orientations are
singular analytic transports of the same vanishing complete source. The distinction is
load-bearing: confusing an algebraic two-sided interval with two analytic singular graph edges
would manufacture the missing Route-L cancellation.

This note proves the exact asymmetry, computes the critical six-tail residue, classifies every
possible scalar counterterm at a Xi zero, and isolates the unique surviving topology problem.

## 2. Only the forward normal is singular on the complete source

Let

\[
 T_m=6^{m/2}U_{m\log6},
 \qquad
 V_m=T_m^{-1}=6^{-m/2}U_{-m\log6}.
\tag{2}
\]

For \(m\ge3\), the corrected complete source and prime-normal residual satisfy

\[
 H_m=V_mR_m,
 \qquad
 H_m\longrightarrow0,
 \qquad
 R_m\longrightarrow\Theta\ne0.
\tag{3}
\]

Here \(R_m=R_{6,m}\) and \(H_m=H_{6,m}\) in the parent paper.

### Theorem 2.1 — analytic orientation asymmetry

On the same complete source \(H_m\), the oriented normal acts by

\[
 \boxed{
 (T_m-T_m^{-1})H_m=R_m-T_m^{-2}R_m
 \longrightarrow\Theta.}
\tag{4}
\]

In particular, the reciprocal face does not cancel the forward vertical endpoint.

### Proof

The first term is \(T_mH_m=R_m\). The second is

\[
 T_m^{-1}H_m=T_m^{-2}R_m.
\]

Since \(U_t\) is unitary,

\[
 \|T_m^{-2}R_m\|=6^{-m}\|R_m\|.
\]

The convergent sequence \(R_m\to\Theta\) is bounded, so this norm tends to zero. Equation
\((4)\) follows. ∎

### Theorem 2.2 — no reciprocal blow-up from a vanishing \(L^2\) source

If \(K_m\in L^2(\mathbb R)\) and

\[
 T_m^{-1}K_m\longrightarrow Y\ne0,
\tag{5}
\]

then

\[
 \|K_m\|=6^{m/2}\|T_m^{-1}K_m\|\longrightarrow\infty.
\tag{6}
\]

Consequently no sequence \(K_m\to0\) can realize a nonzero reciprocal endpoint.

### Proof

Again unitarity gives the equality in \((6)\). The norm on the right of \((5)\) is bounded below
by \(\|Y\|/2\) eventually, proving divergence. ∎

Thus the algebraic identity

\[
 ([6^m]-1)-([6^{-m}]-1)=[6^m]-[6^{-m}]
\tag{7}
\]

has only one singular analytic face in the physical \(L^2\) topology. An opposite face, if it
exists, must live in the contragredient collar or a mixed source/distribution topology. It cannot
be obtained by applying the reciprocal half-density operator to another vanishing \(L^2\) tail.

## 3. The critical six-tail has a nonzero Gamma residue

Write the completed Xi function as

\[
 \Xi(s)=A(s)\zeta(s),
 \qquad
 A(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2).
\tag{8}
\]

The meromorphic continuation of the ordinary six-tail multiplier is

\[
 B_6(s)=\frac1{\zeta(s)}+P_6(s),
 \qquad
 P_6(s)=-1+2^{-s}+3^{-s}+5^{-s}.
\tag{9}
\]

This is the continuation of
\(\sum_{n\ge6}\mu(n)n^{-s}\) from its half-plane of absolute convergence.

### Theorem 3.1 — exact Gamma-residue landing

On the critical strip, the product has the holomorphic identity (and globally the corresponding
meromorphic identity)

\[
 \boxed{
 \Xi(s)B_6(s)=A(s)+\Xi(s)P_6(s).}
\tag{10}
\]

If \(\rho\) is any nontrivial Xi zero, then

\[
 \boxed{
 \bigl(\Xi B_6\bigr)(\rho)=A(\rho)\ne0.}
\tag{11}
\]

### Proof

Equation \((10)\) is \(\Xi/\zeta=A\), followed by distribution. A nontrivial zero satisfies
\(0<\Re\rho<1\), so \(\rho\ne0,1\). The Gamma function has no zeros and no pole at
\(\rho/2\); hence every factor in \(A(\rho)\) is nonzero. The second summand in \((10)\)
vanishes at \(\rho\), proving \((11)\). ∎

The finite correction which produces the exact clock \(6\) therefore preserves the physical
Gamma endpoint; it does not put the critical tail in the Xi-divisible or Meyer--Poisson sector.
This is coefficient fidelity, not annihilation.

### Theorem 3.2 — regular-counterterm impossibility

Let \(E\) be holomorphic near a nontrivial Xi zero \(\rho\). Then

\[
 \bigl(\Xi(B_6+E)\bigr)(\rho)=A(\rho)\ne0.
\tag{12}
\]

More generally, if a meromorphic counterterm \(C\) makes \(\Xi(B_6+C)\) holomorphic and zero at
\(\rho\), then necessarily

\[
 \lim_{s\to\rho}\Xi(s)C(s)=-A(\rho).
\tag{13}
\]

Thus \(C\) must have a pole along the Xi divisor with the exact opposite principal germ. No
finite Dirichlet polynomial, regular Gamma factor, bounded multiplier, or holomorphic Meyer
counterterm can do this.

### Proof

For holomorphic \(E\), \(\Xi(\rho)E(\rho)=0\), so \((12)\) follows from \((11)\). Equation
\((13)\) follows by taking the limit in
\(\Xi(B_6+C)=\Xi B_6+\Xi C\). ∎

This is the precise reason Route L needs singular transport: singularity is forced already by the
local germ, before topology or completion is chosen.

## 4. Functional-equation mate cancels the pole, but not the phase

In the critical strip put

\[
 G(s)=\frac{A(s)}{A(1-s)}.
\tag{14}
\]

The functional equation \(A(s)\zeta(s)=A(1-s)\zeta(1-s)\) gives the meromorphic identity

\[
 \frac{G(s)}{\zeta(1-s)}=\frac1{\zeta(s)}.
\tag{15}
\]

Hence

\[
 \boxed{
 B_6(s)-G(s)B_6(1-s)
 =P_6(s)-G(s)P_6(1-s).}
\tag{16}
\]

All nontrivial-divisor poles cancel before a zero is selected. Multiplication by \(\Xi\) gives an
Xi-divisible paired landing whose quotient is regular throughout the critical strip.

Equation \((16)\) is a genuine positive survivor: it gives a canonical scalar
opposite-pole face and identifies its finite Stokes remainder. It is still not Route-L
annihilation. It expresses reciprocal compatibility for every spectral parameter. It does not
identify forward and reflected phase characters. The corpus theorem
no_phaseDefect_criterion_detects_criticalLine_adelicScaling proves that no predicate depending
only on this reciprocity/coboundary data can force the character itself to be trivial.

The missing comparison must therefore transport the two pole germs with their place and
orientation provenance into the resolved target **before** applying \((16)\). Scalar functional
equation cancellation is too late.

## 5. Exact place-marked Stokes polygon

The same distinction is visible without analytic continuation. In the group algebra of
\(\mathbb Q_{>0}^{\times}\), the positive place path is

\[
 ([6^m]-1)
 +[6^m]([2^{-m}]-1)
 +[3^m]([3^{-m}]-1)=0,
\tag{17}
\]

and the reciprocal path is

\[
 ([6^{-m}]-1)
 +[6^{-m}]([2^m]-1)
 +[3^{-m}]([3^m]-1)=0.
\tag{18}
\]

Both are immediate endpoint telescopes. Subtracting \((18)\) from \((17)\) expresses the arch
face \([6^m]-[6^{-m}]\) as the negative of explicit marked \(2\)- and \(3\)-Euler faces. The
placewise Kummer regulators are

\[
 2m\log6,\qquad -2m\log2,\qquad -2m\log3,
\tag{19}
\]

and their sum is zero.

This is stronger than unmarked scalar averaging because every place face survives until the last
differential. It still does not kill the arch face separately. Under the horizontal character,
the finite faces in \((17)-(18)\) evaluate to exactly

\[
 -\bigl(6^{m\delta}-6^{-m\delta}\bigr).
\tag{20}
\]

Therefore any target reader which discards those faces while retaining the arch face would cease
to be a chain map. Conversely, a reader which sees the whole polygon obtains the tautology
\(K_{6^m}-K_{6^m}=0\), not \(K_{6^m}=0\).

The polygon identifies the required source object, but also proves that product formula alone is
not its annihilator.

## 6. Exact surviving Route-L theorem

The source now forced by \((13)\), \((16)\), and \((17)\)--\((19)\) is a place-marked pair

\[
 \left(
   B_6(s),
   -\frac{A(s)}{A(1-s)}B_6(1-s)
 \right)
\tag{21}
\]

living in a mixed topology with three simultaneous requirements:

1. the \(L^1\)/Rost--Schmid channel keeps the principal-divisor relation and its separate
   \(\infty,2,3\) clock faces, the \(5\)-tail correction, and the cyclotomic denominator
   packets of the honest Steinberg normal;
2. the \(L^2\)/Meyer channel admits the completed Green primitive and its Xi multiplicity jets;
3. the target differential transports the two singular germs before their scalar sum, so the
   fixed Burnol/Deninger reader is cyclic on the **transported principal-divisor boundary**, not
   merely on its already-zero scalar codiagonal.

The denominator layer is now classified in
deninger-gamma-six-cyclotomic-denominator-admission.md. The pre-normal source has infinitely many
tame/Kummer-null but rational-Witt-visible denominator places. Their forward and reciprocal
common-pole residues are both \([-1]-[1]\), so the whole cofinal layer is reflection-even. Its
tensor-square grade \(6^{-m}\) has a nuclear mixed \(\ell^1/\ell^2\) admission, but it cannot
carry the odd physical anomaly. The same tensor-square grade gives the actual two normal
orientations a sharp mixed coefficient admission exactly for \(|\delta|<1\), retaining the fixed
Gamma-six coefficient in grade one. What is not proved is promotion of that coefficient carrier
to the strict Rost--Schmid/Meyer domain and the coefficient-faithful **relative chain
differential** for the odd pole pair \((21)\) into the existing Meyer--Calderón target. This is
the concrete specialization of the adelic Rost--Schmid-to-Hodge problem needed by Route L.

The strict topology is now fixed rather than conjectural. The first surviving Möbius atom forces
tensor-square edge \(6^{-m}\), and the corresponding nuclear critical-edge Köthe domain admits
both evaluated orientations exactly at \(\delta=0\). The common adjacent-grade coface has the
nonzero lower endpoint \(K_6/6\); every fixed finite grade convolution is trivial or a
divisor-dependent receiver; Euler depletion preserves rather than creates Poisson admission.
Full proof:
deninger-gamma-six-critical-edge-coface-rigidity.md.

## 7. Novelty and hostile audit

- The functional equation, the endpoint telescopes \((17)\)--\((18)\), and the abstract product
  formula are classical; no novelty is claimed for them.
- Project-specific new knowledge is the exact incompatibility of the algebraic reciprocal
  Gamma-six normal with a reciprocal vanishing-source transport, equation \((4)\), and the complete
  counterterm classification \((10)\)--\((13)\) for the corrected Möbius six-tail.
- The analysis retracts a stronger interpretation of the parent paper: “two-sided Tate primitive”
  is algebraic, while the complete \(L^2\) source transport is one-sided.
- The functional-equation mate \((16)\) is retained as a positive survivor because it constructs
  the required opposite pole germ. It is explicitly not counted as annihilation.
- No Xi-zero location, reflected phase identification, RH predicate, positivity premise, or
  numerical computation is used.

## 8. Frontier ledger

- [x] prove analytic asymmetry of the two Gamma-six normal orientations
- [x] rule out reciprocal nonzero landing from a vanishing physical \(L^2\) source
- [x] compute exact nonzero Gamma residue of the critical corrected six-tail
- [x] prove every regular/finite counterterm is impossible
- [x] construct canonical functional-equation opposite pole germ
- [x] construct explicit place-marked \(\infty,2,3\) Stokes polygon
- [x] prove reciprocity/polygon cancellation alone is character-blind
- [x] classify and mixed-admit the reflection-even cyclotomic denominator family
- [x] construct sharp mixed coefficient admission of the odd pole pair on \(|\delta|<1\)
- [x] classify the source-forced critical-edge domain and local-coface obstruction
- [ ] prove completed Green landing in both critical-edge orientation slots
- [ ] construct strict Rost--Schmid-to-Meyer realization and relative differential for \((21)\)
- [ ] prove fixed-reader cyclicity on that transported, provenance-retaining boundary
