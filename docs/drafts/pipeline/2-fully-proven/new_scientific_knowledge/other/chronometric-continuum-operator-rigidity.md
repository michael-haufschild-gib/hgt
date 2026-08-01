# Chronometric graph rigidity for continuum metric gravity

- **ID:** `chronometric-continuum-operator-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / TIME / CAUSALITY / INVERSE LAW
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** dependency-closed paper proof on fixed relational event labels; continuum-indexed
  polarization, graph rigidity, and Ramsey phase recovery are unconditional in Lean;
  diffeomorphism quotient and controlled-QFT realization remain pending.

## Headline

> **No two different laws of gravity can make every clock agree.**

Exact public form:

> **The full nonlinear law of metric gravity is the graph of how calibrated matter changes
> squared clock intervals.**

This is an operator-identification theorem, not a reconstruction of one metric under an assumed
field equation.

## Continuum data

Let \(M\) be a smooth manifold and let \(\mathcal G\) be any class of smooth time-oriented
Lorentzian metrics on \(M\). No perturbative, analytic, globally hyperbolic, or unique-solvability
assumption is needed for the theorem below.

For \(g\in\mathcal G\), define its infinitesimal chronometric field

\[
  \mathsf Q(g)(x,v)=g_x(v,v),\qquad x\in M,\quad v\in T_xM.                 \tag{1}
\]

Operationally, negative values are squared proper-time rates of infinitesimal clock trajectories,
zero is the light-cone boundary, and positive values are obtained by clock-radar/rod calibration.
The mathematical theorem uses the complete signed squared-interval field `(1)`. A clocks-only
realization of its spacelike part remains a separate experimental bridge.

Let \(\mathcal J\) be the set of independently calibrated physical source labels. A gauge-fixed
metric gravity law is a map

\[
  \mathcal E:\mathcal G\longrightarrow\mathcal J.                           \tag{2}
\]

Its chronometric solution graph is

\[
  \Gamma_{\mathrm{chr}}(\mathcal E)
  =
  \{\,(\mathcal E(g),\mathsf Q(g)):g\in\mathcal G\,\}
  \subseteq
  \mathcal J\times \mathsf Q(\mathcal G).                                  \tag{3}
\]

Unlike a source-to-solution function, `(3)` retains every branch when one source has several
solutions.

## Lemma 1 — squared clock intervals determine the metric

The map

\[
  \mathsf Q:\mathcal G\longrightarrow
  \prod_{x\in M}\mathbb R^{T_xM}
\]

is injective.

### Proof

Let \(\mathsf Q(g)=\mathsf Q(h)\). For every \(x\in M\) and \(u,v\in T_xM\), symmetry and
bilinearity give the polarization identities

\[
\begin{aligned}
  2g_x(u,v)
  &=g_x(u+v,u+v)-g_x(u,u)-g_x(v,v),\\
  2h_x(u,v)
  &=h_x(u+v,u+v)-h_x(u,u)-h_x(v,v).
\end{aligned}                                                              \tag{4}
\]

Every diagonal term on the right is a value of `(1)`, so the two right-hand sides agree.
Therefore \(g_x(u,v)=h_x(u,v)\) for all \(x,u,v\), hence \(g=h\). \(\square\)

The proof does not use Lorentz signature: diagonal values determine every symmetric bilinear
field. Lorentz signature supplies the physical clock interpretation.

## Theorem 1b — nine before/after boundaries and one tick determine a four-metric

In a four-dimensional frame \((t,x,y,z)\), consider six axis light-clock directions

\[
  t\pm x,\qquad t\pm y,\qquad t\pm z                                      \tag{4a}
\]

and three mixed Pythagorean directions

\[
  5t+3x+4y,\qquad 5t+3x+4z,\qquad 5t+3y+4z.                               \tag{4b}
\]

Let \(B\) be any symmetric real bilinear form. If all nine directions in `(4a)`--`(4b)` are
\(B\)-null and one calibrated clock gives \(B(t,t)=-1\), then

\[
  [B]_{(t,x,y,z)}=\operatorname{diag}(-1,1,1,1).                           \tag{4c}
\]

### Proof

For each \(e\in\{x,y,z\}\), subtracting
\(B(t+e,t+e)=0\) and \(B(t-e,t-e)=0\) gives \(B(t,e)=0\). Adding them gives
\(B(e,e)=-B(t,t)=1\).

Now expand, for example,

\[
  0=B(5t+3x+4y,5t+3x+4y)
   =25B(t,t)+9B(x,x)+16B(y,y)+24B(x,y).
\]

The first three terms sum to \(-25+9+16=0\), so \(B(x,y)=0\). The other two mixed directions give
\(B(x,z)=B(y,z)=0\). These are all ten independent entries of a symmetric four-metric, proving
`(4c)`. \(\square\)

The nine null channels determine conformal metric in an adapted frame; one timelike tick fixes its
scale. Their count, nine plus one, equals the ten independent entries of a symmetric four-metric.
No minimality claim is made without a separate lower-bound theorem.

## Theorem 2 — continuum chronometric operator rigidity

For any two gravity laws \(\mathcal E_1,\mathcal E_2:\mathcal G\to\mathcal J\),

\[
  \boxed{
  \Gamma_{\mathrm{chr}}(\mathcal E_1)
  =
  \Gamma_{\mathrm{chr}}(\mathcal E_2)
  \quad\Longleftrightarrow\quad
  \mathcal E_1=\mathcal E_2.}                                               \tag{5}
\]

### Proof

The reverse implication is immediate. Suppose the two graphs are equal and fix
\(g\in\mathcal G\). Then

\[
  (\mathcal E_1(g),\mathsf Q(g))
  \in\Gamma_{\mathrm{chr}}(\mathcal E_1)
  =\Gamma_{\mathrm{chr}}(\mathcal E_2).
\]

Thus some \(h\in\mathcal G\) satisfies

\[
  \mathcal E_2(h)=\mathcal E_1(g),
  \qquad
  \mathsf Q(h)=\mathsf Q(g).
\]

Lemma 1 forces \(h=g\), hence \(\mathcal E_2(g)=\mathcal E_1(g)\). Since \(g\) was arbitrary,
\(\mathcal E_1=\mathcal E_2\). \(\square\)

## Corollary 3 — the gravity equation is an inverse clock law

If \(\mathcal E\) is restricted to a region on which it is bijective, then

\[
  \mathcal E
  =
  \left(\mathsf Q\circ\mathcal E^{-1}\right)^{-1}\circ\mathsf Q.              \tag{6}
\]

Here the inverse is taken from \(\mathsf Q(\mathcal G)\) back to \(\mathcal J\). Equivalently, the
source-to-clock map and the metric field equation are inverse descriptions of the same law.

Equation `(5)`, not the notation `(6)`, is the branch-safe universal statement.

## Lemma 4 — exact Ramsey recovery removes detector phase loss

Let \(\mathcal A\) be a unital operator algebra, \(\omega\) a state, and \(U\in\mathcal A\) a
unitary that can be applied on one branch of a two-level clock. Prepare the clock in
\(\lvert+\rangle\), apply

\[
  C_U
  =
  \lvert0\rangle\!\langle0\rvert\otimes 1
  +
  \lvert1\rangle\!\langle1\rvert\otimes U,                                 \tag{7}
\]

and read both equatorial clock quadratures. Direct multiplication gives

\[
  \langle\sigma_x\rangle=\operatorname{Re}\omega(U),
  \qquad
  \langle\sigma_y\rangle=\operatorname{Im}\omega(U)                         \tag{8}
\]

up to the fixed sign convention used for \(\sigma_y\). Thus clock outcome probabilities in two
readout bases recover the complex expectation, not merely its modulus or symmetrized part.

For controlled sequential pulses \(U_1\cdots U_n\), the same calculation recovers
\(\omega(U_1\cdots U_n)\). If

\[
  U_j(\lambda_j)=\exp(i\lambda_j\Phi(f_j))
\]

is a regular family, then

\[
  i^{-n}
  \left.
  \frac{\partial^n}{\partial\lambda_1\cdots\partial\lambda_n}
  \omega\!\left(U_1(\lambda_1)\cdots U_n(\lambda_n)\right)
  \right|_{\lambda=0}
  =
  \omega\!\left(\Phi(f_1)\cdots\Phi(f_n)\right).                            \tag{9}
\]

Consequently a causally ordered, controlled-clock family reconstructs all ordered correlation
distributions that its realizable local unitary pulses separate. The remaining physical
assumption is controllability of those pulses, not a polarization or phase-recovery gap.

## What is new and what is not

Prior work proves substantially harder partial-data geometry theorems: boundary time separation
can determine metric jets; nonlinear wave observations can recover causal diamonds; local QFT
probe schemes can asymptotically measure every observable of a linear scalar field. Those results
are required for a realistic small-laboratory theorem.

The new exact point isolated here is different:

1. vary the calibrated source rather than reconstruct one background;
2. retain the full solution relation rather than assume one solution per source;
3. identify the complete nonlinear metric operator, not only geometry or selected coefficients;
4. prove phase-complete ordered clock tomography by controlled Ramsey readout.

The theorem is not yet a Nature result by itself because `(3)` is complete continuum data. The
Nature-level step is to prove that the restricted chronometric intervention functor of one
laboratory determines `(3)` on its causal diamond.

## Hostile scope audit

1. **Diffeomorphisms:** `(5)` uses fixed relational event and tangent labels. The quotient theorem
   must replace equality by pullback equivalence under clock-label-preserving diffeomorphisms.
2. **Gauge:** `(2)` is gauge-fixed. Extra gravitational fields require reporter-complete
   chronometric data and quotient by local physical field redefinitions.
3. **Clock-only realization:** proper time directly supplies timelike values of `(1)`. A finite
   radar protocol must reconstruct the remaining signed quadratic germ.
4. **Partial laboratories:** data only inside a worldtube do not automatically supply `(3)` in a
   causal diamond. Nonlinear Lorentzian inverse theorems must close that bridge.
5. **Source calibration:** if source labels are allowed to relabel with the theory, `(5)` can be
   defeated trivially. Operational source channels must be fixed independently.
6. **Hidden sectors:** a field absent from both metric response and all reporters remains
   invisible. Such clock-dark sectors are outside the admissible class, not silently identified.
7. **Quantum gravity:** `(5)` identifies classical continuum metric operators. It does not by
   itself reconstruct a quantum gravitational state or path integral.

## Lean obligations

Formalize unconditionally:

1. [complete] diagonal injectivity of an indexed field of symmetric bilinear forms;
2. [complete] graph rigidity for an arbitrary injective observation encoding;
3. [complete] specialization from squared intervals to coordinate-trivialized continuum metric
   fields;
4. [complete] two-quadrature Ramsey recovery;
5. [complete] nine null-order comparisons plus one tick determine a symmetric four-metric;
6. [partial] ordered-product recovery is algebraically formalized in the existing complete clock
   reporter algebra; continuum characteristic-functional differentiation remains open;
7. [open] smooth tangent-bundle/chart lift;
8. [open] quotient lift under label-preserving equivalences.

The existing all-orders symmetric multilinear polarization theorem supplies a stronger reusable
dependency for item 1. Formal artifact:
`formal/GaloisForLFunctions/HTGeometry/ContinuumChronometricGravity.lean`.

## Primary sources and closest collisions

- P. Stefanov, G. Uhlmann, and A. Vasy, *Determination of the spacetime from local time
  measurements*, <https://arxiv.org/abs/1412.1350>.
- C. J. Fewster, I. Jubb, and M. H. Ruep, *Asymptotic measurement schemes for every observable
  of a quantum field theory*, <https://arxiv.org/abs/2203.09529>.
- C. J. Fewster and R. Verch, *Quantum fields and local measurements*,
  <https://arxiv.org/abs/1810.06512>.
- Y. Kurylev, M. Lassas, L. Oksanen, and G. Uhlmann,
  *Inverse problem for Einstein--scalar field equations*,
  <https://arxiv.org/abs/1406.4776>.
- M. Rotondo, *A Detector-Based Inference Framework for Quantum Theory and Spacetime Geometry*,
  <https://arxiv.org/abs/2604.10349>. This reconstructs a detector information metric and selects
  the Einstein--Hilbert term through an effective low-energy ansatz; it does not prove `(5)` or
  recover an unknown gravitational operator from source-indexed clock data.
