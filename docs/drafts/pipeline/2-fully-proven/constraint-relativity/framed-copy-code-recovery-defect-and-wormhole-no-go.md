# Framed copy-code recovery defect and fixed-code wormhole no-go

- **ID:** `framed-copy-code-recovery-defect-wormhole-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / QUANTUM OPERATIONAL REALIZATION / NO-GO
- **Scientific status:** `[PAPER-PROVED] [NO LEAN WRITTEN OR BUILT] [NOT RH]`
  `[NOT A GRAVITATIONAL WORMHOLE MODEL]`
- **Novelty status:** copy-code and recovery calculations are elementary QEC. Candidate value is
  an exact observer equality for framed provenance plus two architecture no-gos.
- **Parents:** `../../1-in-progress/constraint-relativity/framed-lawstack-dynamics.md` and
  `framed-provenance-curvature-scalar-no-go.md`.

## 1. Purpose

This card asks for a physical realization, not a metaphor. It proves:

1. one framed Choi provenance norm equals a standard optimized recovery defect exactly;
2. exact admitted regional algebras do not determine approximate recoverability;
3. bounded quantities of a fixed finite code cannot equal unbounded DSSYK wormhole length for all
   time.

## 2. Minimal copy code

Let

\[
 \mathcal H_L=\mathcal H_A=\mathcal H_B=\mathbb C^d,
 \qquad d\ge2,
\]

and define isometry

\[
 W|j\rangle=|j\rangle_A|j\rangle_B.
 \tag{2.1}
\]

Let `P=WW^*`. For region `X=A,B,AB`, define admitted logical algebra by code-preserving
representatives

\[
 \mathcal S_X
 =\{W^*\widetilde O_XW:
 [\widetilde O_X,P]=0,
 \ \widetilde O_X\text{ is supported on }X\}.
 \tag{2.2}
\]

Let `mathcal D_d subset M_d(C)` be diagonal masa.

### Theorem 2.1 — exact regional admission

\[
 \boxed{
 \mathcal S_A=\mathcal S_B=\mathcal D_d,
 \qquad
 \mathcal S_{AB}=M_d(\mathbb C).}
 \tag{2.3}
\]

Hence relative operator space is

\[
 \mathcal C_{\mathrm{adm}}=M_d/\mathcal D_d,
 \tag{2.4}
\]

spanned by off-diagonal matrix-unit classes. It is an operator-space quotient, not a quotient
algebra.

#### Proof

For an `A`-supported representative,

\[
 (\widetilde O_A\otimes I)W|j\rangle
 =\widetilde O_A|j\rangle\otimes|j\rangle.
\]

If this equals

\[
 WO|j\rangle=\sum_iO_{ij}|ii\rangle,
\]

comparison of `B` index forces `O_ij=0` for `i!=j`. Every diagonal logical operator is represented
by same diagonal operator on `A`, proving `S_A=D_d`. The `B` proof is identical. Joint support can
use `WE_ijW^*` and therefore represents all `M_d`. QED.

## 3. Framed Choi class and recovery equality

For phases `phi_j`, let

\[
 W_\phi|j\rangle=e^{i\phi_j}|jj\rangle.
\]

Its normalized reference-enriched Choi state is

\[
 \Omega_\phi
 ={1\over d}\sum_{i,j}
 e^{i(\phi_i-\phi_j)}
 |iii\rangle\langle jjj|_{RAB}.
 \tag{3.1}
\]

Put

\[
 \Delta={1\over d}\sum_i|iii\rangle\langle iii|,
 \qquad
 \kappa_\phi=\Omega_\phi-\Delta.
 \tag{3.2}
\]

`kappa_phi` is the framed off-diagonal connecting class.

### Theorem 3.1 — admission/recovery identity

Every proper marginal of `kappa_phi` vanishes:

\[
 \operatorname{Tr}_A\kappa_\phi
 =\operatorname{Tr}_B\kappa_\phi
 =\operatorname{Tr}_R\kappa_\phi=0.
 \tag{3.3}
\]

Let `F_e^opt(A)` be maximal entanglement fidelity, for maximally mixed logical source, after erasing
`B` and applying arbitrary recovery to region `A`. Then

\[
 \boxed{
 \operatorname{Tr}(\kappa_\phi^2)
 =1-{1\over d}
 =1-F_e^{\mathrm{opt}}(A)
 =1-F_e^{\mathrm{opt}}(B).}
 \tag{3.4}
\]

Moreover,

\[
 \boxed{
 I(R:B\mid A)_{\Omega_\phi}=\log d,
 \qquad
 \operatorname{Tr}(\kappa_\phi^2)
 =1-e^{-I(R:B\mid A)}.}
 \tag{3.5}
\]

#### Proof

Tracing any one tensor factor kills every off-diagonal term `i!=j`; `Omega_phi` and `Delta` then
have same marginal, proving `(3.3)`.

Erasing either region leaves completely dephasing channel. Every recovery after dephasing remains
entanglement breaking. For normalized maximally entangled state `Phi_d`, every separable Choi
state `sigma` satisfies

\[
 \langle\Phi_d|\sigma|\Phi_d\rangle\le {1\over d},
\]

and label-preserving recovery attains equality. Thus `F_e^opt=1/d`.

Directly,

\[
 \operatorname{Tr}\Omega_\phi^2=1,
 \qquad
 \operatorname{Tr}\Delta^2={1\over d},
 \qquad
 \operatorname{Tr}(\Omega_\phi\Delta)={1\over d},
\]

which proves `(3.4)`. Every proper GHZ marginal has entropy `log d`; the conditional mutual
information formula gives `I(R:B|A)=log d`, and `(3.5)` follows. QED.

For `d=2`, this is smallest nontrivial example:

\[
 \mathcal S_A=\mathcal S_B=\operatorname{span}\{I,Z\},
 \qquad
 \operatorname{Tr}\kappa^2=1-F_e^{\mathrm{opt}}={1\over2}.
\]

Phase survives in framed class but not scalar norm. Whether phases are gauge depends on declared
source-framed equivalence; endpoint algebras cannot decide.

## 4. Exact-admission insufficiency

Define two-qubit isometry

\[
 W_\theta|0\rangle=|00\rangle,
 \qquad
 W_\theta|1\rangle
 =\cos\theta|10\rangle+\sin\theta|01\rangle,
 \qquad 0<\theta<{\pi\over2}.
 \tag{4.1}
\]

### Theorem 4.1 — constant exact flags, varying recovery

For entire open interval,

\[
 \boxed{\mathcal S_A(\theta)=\mathcal S_B(\theta)=\mathbb CI.}
 \tag{4.2}
\]

Let `gamma=sin^2 theta`, and optimize coherent information over recoveries after channel to `A`,
with maximally mixed logical source. Then

\[
 \boxed{
 I_c^{\mathrm{opt}}(\theta)
 =h_2\left({1-\gamma\over2}\right)
 -h_2\left({\gamma\over2}\right),}
 \tag{4.3}
\]

which decreases strictly from `log 2` toward `-log 2`.

#### Proof

Coefficient comparison shows an `A`-supported code-preserving representative induces only an
upper-triangular logical operator with equal diagonal entries. Adjoint invariance from commutation
with `P` kills off-diagonal entry. Hence only scalars remain; same holds for `B`.

Channel to `A` is amplitude damping. For maximally mixed input,

\[
 S(A)=h_2\left({1-\gamma\over2}\right),
 \qquad
 S(RA)=h_2\left({\gamma\over2}\right).
\]

Postprocessing `A` cannot increase `I(R:A)`, and `I_c=I(R:A)-S(R)`, so identity recovery is
optimal and gives `(4.3)`. Finally,

\[
 {dI_c^{\mathrm{opt}}\over d\gamma}
 =-{1\over2}\log{1+\gamma\over1-\gamma}
  -{1\over2}\log{2-\gamma\over\gamma}<0.
\]

QED.

### Consequence

Exact admission flags cannot encode approximate recovery or backreaction. Framed law object must
retain quantitative channel/Choi data or an approximate-admission filtration.

## 5. Fixed finite-code wormhole no-go

Any fixed finite-dimensional code has bounded normalized recovery quantities:

\[
 0\le1-F_e^{\mathrm{opt}}\le1,
 \qquad
 I(X:Z\mid Y)\le2\log\dim X,
 \qquad
 \|\rho-\sigma\|_2^2\le2.
 \tag{5.1}
\]

In DSSYK/sine-dilaton realization, canonical bulk length satisfies

\[
 \langle\widehat L\rangle=\lambda C_\beta(t),
\]

and at infinite temperature

\[
 \lambda C_0(t)=2\log\cosh(Jt)+O(\lambda),
 \tag{5.2}
\]

which is unbounded as `|t|->infinity`.

### Theorem 5.1

No fixed finite-code recovery defect, conditional mutual information, or normalized Choi norm can
equal DSSYK wormhole length for all time.

#### Proof

Every candidate from `(5.1)` is bounded on fixed finite dimensions; `(5.2)` is unbounded. QED.

A valid realization requires growing dimension/cofinal completion, an extensive unnormalized
observable, or a restricted finite-time window. A fitted time-dependent observer functional does
not count.

## 6. Literature and scope

Operator-algebra QEC is classical. Exact complementary recovery has state-independent area;
approximate recovery and tripartite nonlocal magic can control proto-area response in recent
work: [state-dependent geometry from magic-enriched codes](https://arxiv.org/abs/2603.13475).
Region-adapted reconstruction may not share a common logical algebra:
[entanglement-wedge reconstruction without HQEC](https://arxiv.org/abs/2607.08684).
DSSYK work can identify wormhole length because it has an independently quantized length operator:
[higher-loop wormhole length from Krylov complexity](https://arxiv.org/abs/2606.20220).

The copy code proves an admission/recovery equality. It proves neither gravitational backreaction
nor an RH connection.

## 7. Next falsifiable experiment

For magic-enriched skewed code `V_epsilon=e^(i epsilon G)V_0`:

1. compute exact code-preserving regional algebras;
2. independently tomograph Choi state and optimize recovery;
3. measure proto-area response;
4. test prediction that generic nonzero `epsilon` causes exact-algebra rank collapse while
   recoverability/proto-area vary continuously.

For any later DSSYK claim, one provenance observable must match independently the first three
cumulants of chord-number/bulk-length operator in growing-dimension limit. Matching mean curve is
insufficient.

## 8. Lean handoff notes

No Lean code was written or built. Later formalization can isolate matrix-algebra admission,
finite entropy identities, and elementary boundedness. Approximate QEC optimization and DSSYK
comparison require separate analytic infrastructure.
