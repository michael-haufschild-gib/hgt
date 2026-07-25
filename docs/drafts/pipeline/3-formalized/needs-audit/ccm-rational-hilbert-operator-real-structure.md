# Quaternionic Real structure on rational CCM Hilbert operators

- **ID:** `ccm-rational-hilbert-operator-real-structure`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), novelty needs audit
- **Source:** `kreal-quaternionic-ccm-cokernel` · rational Real-Brauer lane
- **Statement:** conjugation by the no-doubling quaternionic antiunitary on
  \(\ell^2(\mathbb Q^\times)\) is an isometric Real algebra involution preserving the
  Hilbert--Schmidt and trace-class ideals and conjugating ordinary operator trace.

## Setup

Let
\[
  H=\ell^2(\mathbb Q^\times),\qquad
  (Jf)(q)=\operatorname{sgn}(q)\overline{f(-q)}.
\]
The dependency-closed Hilbert-fiber theorem gives \(J^2=-1\) and
\(\|Jf\|=\|f\|\). For \(T\in\mathcal B(H)\), define
\[
  \alpha(T)=JTJ^{-1}=-JTJ.                                \tag{1}
\]
Write \(\delta_q\) for the standard basis vector at \(q\).

## Theorem

`[PROVED HERE]` The map \(\alpha\) has the following properties.

1. For every bounded complex-linear \(T\), \(\alpha(T)\) is bounded complex-linear and
   \[
     \|\alpha(T)\|=\|T\|.                                 \tag{2}
   \]
2. It is a conjugate-linear unital algebra involution:
   \[
   \begin{aligned}
     \alpha(S+T)&=\alpha(S)+\alpha(T),\\
     \alpha(zT)&=\overline z\,\alpha(T),\\
     \alpha(ST)&=\alpha(S)\alpha(T),\\
     \alpha(1)&=1,\qquad \alpha^2(T)=T.                    \tag{3}
   \end{aligned}
   \]
3. It preserves Hilbert--Schmidt operators and their Hilbert--Schmidt norm.
4. It preserves every approximation number:
   \[
     a_n(\alpha(T))=a_n(T),
   \]
   hence preserves trace-class operators, the approximation-number Schatten \(S_1\) ideal,
   and the trace norm exactly.
5. On trace-class operators,
   \[
     \operatorname{Tr}(\alpha(T))
       =\overline{\operatorname{Tr}(T)}.                   \tag{4}
   \]
6. Its fixed algebra is exactly the algebra of bounded quaternionic-linear operators:
   \[
     \alpha(T)=T
       \quad\Longleftrightarrow\quad TJ=JT.                \tag{5}
   \]

Thus the analytic operator target retains the quaternionic Real Brauer type through both its
trace ideal and its trace. No second copy of \(H\) is introduced.

## Proof

Because \(J\) is conjugate-linear, the two occurrences of \(J\) in (1) make \(\alpha(T)\)
complex-linear. Norm preservation of \(J\) gives
\[
  \|\alpha(T)f\|\le \|T\|\,\|f\|,
\]
so \(\|\alpha(T)\|\le\|T\|\). Applying the same inequality to
\(\alpha^2(T)=T\) proves equality. Additivity and conjugate homogeneity are direct.
Using \(J^2=-1\),
\[
  \alpha(S)\alpha(T)
   =(-JSJ)(-JTJ)=-JSTJ=\alpha(ST),
\]
and the same identity proves \(\alpha(1)=1\) and \(\alpha^2=1\).

The standard basis satisfies
\[
  J\delta_q=-\operatorname{sgn}(q)\delta_{-q}.             \tag{6}
\]
Hence
\[
  \sum_q\|\alpha(T)\delta_q\|^2
    =\sum_q\|T\delta_{-q}\|^2
    =\sum_q\|T\delta_q\|^2.                               \tag{7}
\]
Basis independence of Hilbert--Schmidt summability proves claim 3.

If \(T=AB\) with \(A,B\) Hilbert--Schmidt, then
\[
  \alpha(T)=\alpha(A)\alpha(B),
\]
and claim 3 makes the right side another Hilbert--Schmidt factorization. This proves
trace-class preservation. The established equivalence between trace-class factorization and
approximation-number Schatten \(S_1\) proves the equivalent formulation.

For exact approximation numbers, let a finite-rank approximant \(F\) have range in a complex
subspace \(V\). Quaternionic reflection sends \(V\) semilinearly onto another complex subspace
\(JV\). A conjugate-semilinear equivalence is real-linear, and
\[
  \dim_{\mathbb R}V=2\dim_{\mathbb C}V,\qquad
  \dim_{\mathbb R}JV=2\dim_{\mathbb C}JV.
\]
Its real-linear bijectivity therefore gives
\(\dim_{\mathbb C}JV=\dim_{\mathbb C}V\). Thus \(\alpha(F)\) has the same rank bound as \(F\).
Since \(\alpha\) is an operator-norm isometry,
\[
  a_n(\alpha(T))\le a_n(T).
\]
Apply this inequality again and use \(\alpha^2=1\) to get equality. Summing termwise gives exact
trace-norm preservation.

For a trace-class \(T\), basis independence of trace allows evaluation on
\((\delta_q)\). A direct use of (1) and (5) gives
\[
  \langle\delta_q,\alpha(T)\delta_q\rangle
    =\overline{\langle\delta_{-q},T\delta_{-q}\rangle}.
\]
The diagonal is absolutely summable. Conjugation commutes with its sum and negation permutes
\(\mathbb Q^\times\), proving (4).

Finally, if \(TJ=JT\), then
\[
  \alpha(T)=-JTJ=-TJ^2=T.
\]
Conversely, applying \(J\) to \(\alpha(T)f=Tf\) and using \(J^2=-1\) gives
\(T(Jf)=J(Tf)\). This proves (5).

## Hostile audit

- This theorem does not identify the completed CCM operator target with every bounded or
  trace-class operator on \(H\); that is a separate continuity/Schwartz-kernel statement.
- Trace conjugacy is not trace invariance. The fixed real trace appears only on
  \(\alpha(T)=T\).
- The theorem supplies target-side Real descent only. It does not construct twisted cyclic
  \(\operatorname{Tor}\), its cup product, Frobenius generator, or positivity.
- No spectral statement and no form of RH is assumed or proved here.

## Strongest positive survivor

The target-side part of the rational Real-Brauer conjecture is now analytic rather than merely
algebraic: the actual CCM Hilbert operator ideal is stable, its Real structure is isometric, and
ordinary trace is compatible with descent by complex conjugation. Remaining bridge is to prove
that CCM's strong-Schwartz operator-valued image and completed restriction map lie inside this
stable ideal continuously.

## Lean realization

Module:

- `GaloisForLFunctions.RHTower.CCMRationalHilbertOperatorRealStructure`

Formal capstones:

- `ccmRationalMoritaHilbertOperatorRealIsometry`;
- `ccmRationalMoritaHilbertOperatorRealStructure_fixed_iff`;
- `ccmRationalMoritaHilbertOperatorRealStructure_hsNorm`;
- `ccmRationalMoritaHilbertOperatorRealStructure_approxNumber`;
- `ccmRationalMoritaHilbertOperatorRealStructure_traceNorm`;
- `ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass_iff`;
- `ccmRationalMoritaHilbertOperatorRealStructure_memSchattenClass_one_iff`;
- `ccmRationalMoritaHilbertOperatorRealStructure_opTrace`.

## Gates

- [x] 0 → 1: exact operator-level conjecture stated after internal trace audit
- [x] 1 → 2: dependency-closed paper proof above
- [x] 2 → 3: minimal Lean check and cached leaf build green; capstone axiom audit contains only
  `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4: external expert audit and full CCM bornological notation check

## Sources

- Connes--Consani--Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392.
- Christopher Deninger, *There is no "Weil-"cohomology theory with real coefficients for
  arithmetic curves*, arXiv:2204.02714.
- El-kaïoum M. Moutuou, *Graded Brauer groups of a groupoid with involution*,
  arXiv:1202.2057.

## Log

- 2026-07-25 — extracted after formalizing the actual antiunitary on
  \(\ell^2(\mathbb Q^\times)\) and auditing existing project trace-class infrastructure. No
  numerical evidence and no RH assumption used.
- 2026-07-25 — formalized bounded-operator Real isometry, fixed-algebra law,
  Hilbert--Schmidt norm invariance, trace-class and Schatten-\(1\) invariance, and trace
  conjugacy. Minimal `lake env lean`, final cached leaf `lake build`, and foundational axiom
  audit passed.
- 2026-07-25 — strengthened the formal target to exact approximation-number and trace-norm
  invariance. Added generic realification proof for conjugate-semilinear finrank transport.
  Minimal checks and cached leaf builds passed; axiom audit remains foundational only.
