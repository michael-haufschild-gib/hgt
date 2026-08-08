# Rational-adelic H1 observer-coefficient freedom and discriminant law

- **ID:** `rational-adelic-h1-observer-coefficient-freedom-and-discriminant-law`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / SOURCE-DUALITY NO-GO WITH POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [LITERAL RATIONAL-ADELIC SOURCE] [OBSERVER NONUNIQUENESS]`
  `[HAAR STOKES AMBIGUITY] [OBSERVER-DISCRIMINANT LAW] [NOVELTY UNVERIFIED]`
  `[NOT RH] [NO LEAN WRITTEN]`
- **Statement:** Literal prime-isotropy `H1` splits into residual quotient plus normalized Stokes
  line, resolved Xi comparison kills all of it, and source duality leaves full observer coefficient
  free. Reflection-doubled physical observer always avoids origin; avoiding coordinate axes is
  exactly critical-line condition.
- **Inputs:**
  `../../3-formalized/new_scientific_knowledge/ccm/rational-adelic-prime-isotropy-relative-xi-chain-map.md`,
  `relative-law-observer-descent-duality.md`,
  `route-r-raw-resolved-relative-cone-character-law.md`.

## Goal

Test whether mapping-cone duality, period-one Stokes normalization, Haar trace, or reflection can
select physical fixed-ideal observer coefficient. Give exact source cohomology rather than reason
only on distinguished class.

## 1. Source complex and notation

Fix ordinary prime `p`. On rational-adelic Bruhat--Schwartz core `A`, put

\[
 T=\alpha_p-1,
 \qquad \varepsilon=\varepsilon_0.
 \tag{OCF.1}
\]

Prime-isotropy complex is

\[
 C_p^0=A,
 \qquad C_p^1=A\oplus\mathbb C,
 \qquad C_p^2=\mathbb C,
 \tag{OCF.2}
\]

\[
 D_0x=(Tx,\varepsilon x),
 \qquad D_1(y,z)=\varepsilon y.
 \tag{OCF.3}
\]

Fixed-point identity gives `epsilon T=0`. Bilateral Stokes primitive

\[
 R_p:A\to\mathbb C
 \tag{OCF.4}
\]

satisfies

\[
 R_pT=\varepsilon.
 \tag{OCF.5}
\]

Define intrinsic residual quotient

\[
 Q_p=\ker\varepsilon/\operatorname{im}T.
 \tag{OCF.6}
\]

## 2. Theorem A — full source H1 decomposition

There is linear isomorphism

\[
 \boxed{
 H^1(C_p)\cong Q_p\oplus\mathbb C,}
 \tag{OCF.7}
\]

given by

\[
 [(y,z)]\longmapsto([y],z-R_p(y)).
 \tag{OCF.8}
\]

Its inverse is

\[
 ([y],c)\longmapsto[(y,c+R_p(y))].
 \tag{OCF.9}
\]

If `y'=y+Tx`, then

\[
 (y',c+R_p(y'))-(y,c+R_p(y))
 =(Tx,R_pTx)=(Tx,\varepsilon x)=D_0x.
 \tag{OCF.9a}
\]

Hence `(OCF.9)` is independent of representative. Direct substitution proves both composites are
identities.

Retained class satisfies

\[
 [\eta_p]=[(0,1)]\longmapsto(0,1).
 \tag{OCF.10}
\]

### Proof

Degree-one cocycles are

\[
 Z^1(C_p)=\ker\varepsilon\oplus\mathbb C.
 \tag{OCF.11}
\]

Boundary is `(Tx,epsilon x)`. By `(OCF.5)` it equals `(Tx,R_pTx)`. Linear coordinate change

\[
 (y,z)\longmapsto(y,z-R_p(y))
 \tag{OCF.12}
\]

sends boundary subspace onto `im T direct-sum {0}`. Quotient gives `(OCF.7)`--`(OCF.9)`.
`(OCF.10)` is immediate. `[PROVED HERE]`

Splitting depends on chosen Stokes primitive; quotient `Q_p` and distinguished class are intrinsic.

## 3. Theorem B — resolved comparison kills all H1

Strict resolved Route-R comparison satisfies

\[
 \Phi_p^1(y,z)=z\,\delta L_p.
 \tag{OCF.13}
\]

For every cocycle `(y,z)`, right side is boundary `delta(z L_p)`. Therefore

\[
 \boxed{H^1(\Phi_p)=0\text{ on all }H^1(C_p).}
 \tag{OCF.14}
\]

Consequently

\[
 \ker H^1(\Phi_p)=H^1(C_p).
 \tag{OCF.15}
\]

For any complex vector space `V`, observer-descent space is entire dual-valued space

\[
 \boxed{
 \mathcal O_{H^1(\Phi_p)}(V)
 =\operatorname{Hom}(H^1(C_p),V)
 \cong\operatorname{Hom}(Q_p,V)\oplus V.}
 \tag{OCF.16}
\]

Last isomorphism uses chosen Stokes splitting `(OCF.7)`. `[PROVED HERE]`

Thus exact relative-observer duality makes all detecting observers available. It selects none.

## 4. Theorem C — target coefficient is completely free

Let descended Stokes functional be

\[
 \bar I_p([(y,z)])=z-R_p(y).
 \tag{OCF.17}
\]

For every `v in V`, define

\[
 P_v:H^1(C_p)\to V,
 \qquad P_v([x])=\bar I_p([x])v.
 \tag{OCF.18}
\]

Then

\[
 P_v([\eta_p])=v.
 \tag{OCF.19}
\]

Therefore map `v mapsto P_v` is injective. Physical observer is special choice

\[
 P_{t,\rho}=P_{c_\rho[F_{-t}]},
 \tag{OCF.20}
\]

not consequence of abstract duality. `[PROVED HERE]`

## 5. Theorem D — Haar trace produces Stokes ambiguity

Let `epsilon_1:A->C` be literal adelic Haar endpoint trace. Rational inverse scaling invariance
gives

\[
 \varepsilon_1T=0.
 \tag{OCF.21}
\]

Take archimedean Schwartz function and finite Bruhat function

\[
 f(x)=x^2e^{-\pi x^2},
 \qquad \phi=\mathbf1_{\widehat{\mathbb Z}},
 \qquad y=f\otimes\phi\in A.
 \tag{OCF.22}
\]

Here

\[
 \widehat{\mathbb Z}=\prod_q\mathbb Z_q\subset\mathbb A_f
 \tag{OCF.22a}
\]

is compact and open by corpus theorem. Finite adele space is Hausdorff, so this subset is clopen;
its indicator is locally constant with compact support. Therefore

\[
 \phi=\mathbf1_{\widehat{\mathbb Z}}
 \in C_c^{\mathrm{lc}}(\mathbb A_f)
 =\texttt{CCMRationalFiniteBruhatSchwartz}.
 \tag{OCF.22b}
\]

It is not unavailable global constant-one function. Moreover `phi(0)=1`, and normalized finite
Haar measure gives

\[
 \int_{\mathbb A_f}\phi\,d\mu_f
 =\mu_f(\widehat{\mathbb Z})=1.
 \tag{OCF.22c}
\]

Since `f(0)=0`,

\[
 \varepsilon_0(y)=0.
 \tag{OCF.23}
\]

Function `f(x)=x^2e^(-pi x^2)` is Schwartz, `f(0)=0`, and Gaussian moment is

\[
 \int_{\mathbb R}x^2e^{-\pi x^2}\,dx=\frac1{2\pi}.
 \tag{OCF.24}
\]

Hence `y=f tensor phi` lies in literal algebraic tensor core and

\[
 \varepsilon_0(y)=0,
 \qquad
 \varepsilon_1(y)=\frac1{2\pi}\ne0.
 \tag{OCF.24a}
\]

If `y=Tx`, `(OCF.21)` would imply `epsilon_1(y)=0`, contradiction. Hence

\[
 [y]\ne0\in Q_p,
 \qquad Q_p\ne0.
 \tag{OCF.25}
\]

For every `lambda in C`, put

\[
 R_{p,\lambda}=R_p+\lambda\varepsilon_1.
 \tag{OCF.26}
\]

Then

\[
 R_{p,\lambda}T=\varepsilon,
 \tag{OCF.27}
\]

and

\[
 I_{p,\lambda}(y,z)=z-R_{p,\lambda}(y)
 \tag{OCF.28}
\]

kills every `D_0` boundary while `I_(p,lambda)(eta_p)=1`. For distinct lambdas, induced
cohomology covectors are distinct because of `(OCF.24a)`. `[PROVED HERE]`

Explicitly, for `lambda ne mu`,

\[
 \left(\bar I_{p,\lambda}-\bar I_{p,\mu}\right)([(y,0)])
 =-(\lambda-\mu)\varepsilon_1(y)
 =-\frac{\lambda-\mu}{2\pi}\ne0.
 \tag{OCF.28a}
\]

Therefore scaling invariance, source trace, boundary annihilation, and period-one normalization do
not uniquely select scalar Stokes covector. Explicit bilateral orbit prescription chooses `R_p`;
abstract source duality does not.

## 6. Theorem E — reflection-doubled observer discriminant

Let fixed physical quotient

\[
 V=\mathbb C^{\mathcal P}/\ell^1(\mathcal P),
 \tag{OCF.29}
\]

fix actual divisor copy `rho` with `c_rho ne0`, and put

\[
 s_{t,\rho}
 =\left(c_\rho[F_{-t}],c_\rho[F_t]\right)\in V\oplus V.
 \tag{OCF.30}
\]

For every `u in (-1,1)`, corpus proves

\[
 [F_u]=0\iff u<0.
 \tag{OCF.31}
\]

Hence

\[
 s_{t,\rho}\ne0\quad\text{for every }t\in(-1,1),
 \tag{OCF.32}
\]

\[
 t>0\Longrightarrow s_{t,\rho}\in\{0\}\oplus(V\setminus\{0\}),
 \tag{OCF.33}
\]

\[
 t<0\Longrightarrow s_{t,\rho}\in(V\setminus\{0\})\oplus\{0\},
 \tag{OCF.34}
\]

while at `t=0` both coordinates are nonzero. Define coordinate-axis discriminant

\[
 \mathfrak D=(V\oplus\{0\})\cup(\{0\}\oplus V).
 \tag{OCF.35}
\]

Then

\[
 \boxed{
 s_{t,\rho}\notin\mathfrak D\iff t=0.}
 \tag{OCF.36}
\]

Reflection swaps components and preserves `D`. `[PROVED HERE]`

Exact conceptual separation:

- explicitly constructed reflection-doubled physical coefficient, together with summability
  classification, gives **origin avoidance** `(OCF.32)` for every `t in (-1,1)`;
- abstract duality gives neither origin nor axis avoidance because it permits arbitrary
  coefficients, including zero;
- RH requires **observer-discriminant transversality** `(OCF.36)` at every actual-divisor
  specialization `t=t_rho=2 Re(rho)-1`.

At physical `t_rho=2 Re(rho)-1`, global discriminant avoidance is equivalent to RH. It is not
proved premise.

## 7. Hostile conjecture loops

1. **Mapping-cone duality selects physical observer.** Falsified by `(OCF.16)`--`(OCF.20)`.
2. **Period-one normalization uniquely selects Stokes covector.** Falsified by `(OCF.26)`--`(OCF.28)`.
3. **Poincare/Verdier self-duality selects fixed-ideal coefficient.** Falsified as producer: even
   perfect scalar duality leaves arbitrary `v in V`.
4. **Reflection forces both physical orientations.** Falsified: reflection swaps axes and doubled
   state remains nonzero every grade.
5. `[NOT ESTABLISHED BY THIS CARD]` Local/global reciprocity and cofinal continuity may impose
   additional structure. Theorems A--E show only that abstract linear duality, normalization,
   Haar invariance, and reflection alone do not select physical coefficient.
7. **Positive survivor.** Origin/axis distinction and discriminant normal form `(OCF.30)`--`(OCF.36)`.

## 8. RH leverage and open core

This theorem rules out whole class of “duality must select it” arguments. Any future producer must
control each fixed-orientation projection separately, not merely doubled norm, perfect pairing,
reflection covariance, or nonzero total state.

`[OPEN CORE] [SOURCE_OBSERVER_DISCRIMINANT_TRANSVERSALITY]`

> Construct from pre-divisor all-prime Euler--Gamma--adelic source data a mixed source/observer
> coevaluation whose fixed-tail zero-aperture landing is nonzero in both orientation projections.
> Construction must fail explicitly on off-line generalized-prime carrier and may not assume
> trace-ideal membership.

As stated on actual zeros, discriminant avoidance is exactly RH; it cannot be inserted as axiom.

## 9. Novelty boundary

Vector-space splitting, Hom/kernel duality, Haar invariance, and coordinate-axis discriminants are
classical. Candidate new-to-corpus bridge is exact conjunction `(OCF.7)`, `(OCF.14)`, `(OCF.25)`,
Haar-generated Stokes ambiguity, and Route-R observer-discriminant normal form. Priority
unverified; elementary mechanism, no literature novelty claim.

Adjacent primary literature:

- Meyer, adelic Schwartz crossed products: https://arxiv.org/abs/math/0312305
- derived Poitou--Tate duality: https://arxiv.org/abs/1104.1484
- adelic derived-functor formulation: https://arxiv.org/abs/1410.2621
- 2025 K-theoretic extension: https://arxiv.org/abs/2504.14153
- 2025 Cartier duality: https://arxiv.org/abs/2512.13856
- scaling Hamiltonian: https://arxiv.org/abs/1910.14368

None constructs canonical Route-R fixed-`ell1` coefficient section.

## 10. Lean-return note

No Lean work authorized. Existing corpus defines `epsilon_0`, `epsilon_1`, scaling invariance,
source complex, Stokes primitive, strict comparison, and physical nonerasure classification.
Later formal target: decomposition `(OCF.7)`, nonzero `Q_p` witness, Stokes ambiguity, and
discriminant classification. Search corresponding CCM modules before edits.

## Gates

- [x] full source `H1` computed
- [x] resolved map classified on all `H1`
- [x] target-coefficient freedom proved
- [x] explicit Haar Stokes ambiguity proved
- [x] observer-discriminant normal form proved
- [x] duality-selection route hostile-falsified
- [x] independent hostile audit
- [ ] Lean formalization
- [ ] source observer-discriminant transversality
- [ ] RH

## Log

- 2026-08-08 — full `H1`, Haar ambiguity, target-coefficient freedom, and doubled
  observer-discriminant law proved; abstract duality-selection route closed.
