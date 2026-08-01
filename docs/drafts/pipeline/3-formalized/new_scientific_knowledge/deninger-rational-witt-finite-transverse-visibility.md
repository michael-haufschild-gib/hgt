# Deninger rational-Witt finite transverse visibility

- **ID:** `deninger-rational-witt-finite-transverse-visibility`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `deninger-prime-packet-topology-haar-retraction`
- **Statement:** complexified finite cyclotomic orbit traces span every function on each finite
  Frobenius packet; explicit moduli \(8\) and \(15\) give a faithful nonconstant source subspace
  and strictly positive literal arithmetic Haar--Green energy at every prime.

## Goal

Close the first non-scalar external-source gate in Route L.  The previous packet Haar target was
faithful but no arithmetic source theorem showed that any mean-zero packet mode reached it.  This
card proves such reachability from finite cyclotomic evaluation data and identifies an entire
faithful finite-dimensional source subspace.

It does **not** construct Deninger's missing relevant complex, the global rational-Witt
derived-section comparison, an all-prime Bessel map from one common source, or Xi spectral
inclusion.

## Gates

- [x] 0 → 1 in-progress: source-pure finite cyclotomic restriction and Fourier attack
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: unconditional Lean modules listed below; targeted builds and axiom audit
- [ ] 3 → 4 publication-ready: external novelty/expert audit and integration with a formal
  rational-Witt implementation

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

The Lean development below formalizes the resulting finite cyclotomic evaluation map directly.
It does not yet formalize the published isomorphism with `W_rat`; that remaining library
identification is recorded explicitly rather than replaced by a made-up rational-Witt object.

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

## Haar and Green consequence

Take a nonconstant complex combination in `(4)`.  At least one of its real and imaginary parts
is nonconstant.  Subtract its normalized Haar average.  The resulting continuous real function
\(f_p\) has
\[
 \operatorname{Av}_p(f_p)=0,\qquad f_p\ne0.                       \tag{5}
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

All theorem statements are unconditional.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Novelty and theatre audit

- **Known ingredients:** finite DFT; CRT; noncyclicity of \(U_8,U_{15}\); compact-group Haar
  functoriality; Deninger's invariant reduced-monoid description of rational Witt vectors.
- **New project-level theorem:** full finite Frobenius-packet visibility by orbit traces, a uniform
  \(8/15\) transverse detector at every prime, faithful pullback to the literal packet, and
  source-generated strictly positive literal arithmetic Green energy.
- **Literature check:** targeted primary-source search found Deninger's packet and rational-Witt
  function maps, but not theorem `(2)`, the uniform detector, or Haar--Green consequence.
  External expert novelty review remains required before publication.
- **Non-circularity:** no Xi divisor, RH, positivity hypothesis, or post hoc divisor-indexed
  Hilbert space appears.  Positivity follows only after an independently constructed source mode
  enters the already faithful arithmetic Haar target.
- **Remaining hard frontier:** upgrade one finite detector per prime to the full filtered
  rational-Witt source; prove a global Bessel comparison from the actual relevant complex with
  simultaneous kernel equal to closed middle boundaries; then cup/trace/Hodge and Xi spectral
  inclusion.  This theorem does not fake those steps.

## Log

- 2026-08-01 — finite Fourier/orbit-trace span proved; uniform mod-\(8/15\) detector found.
- 2026-08-01 — continuous surjective weld to literal packet quotient proved.
- 2026-08-01 — faithful finite source subspace, nonzero mean-zero Haar mode, literal arithmetic
  mode, and positive all-prime Green energy formalized.
