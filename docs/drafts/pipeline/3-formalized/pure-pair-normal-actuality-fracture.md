# Actuality is normal to quantum possibility

- **ID:** `pure-pair-normal-actuality-fracture`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / NO-GO / POSITIVE SURVIVOR
- **Parent conjecture:** `../1-in-progress/quantum-disagreement-spacetime-law.md`
- **Statement:** For the standard compatible \(\operatorname{Spin}(10)\) pure pair, every
  first-order deformation through pure states has zero disagreement defect; the
  colour-preserving normal defect is instead exactly one complex weak doublet, hence four real
  directions.
- **Scientific status:** `[PROVED HERE] [PURE-SPINOR COORDINATE PROOF]`
  `[QUATERNIONIC 1+3 SURVIVOR LEAN-PROVED]`
  `[FULL CARTAN DERIVATIVE AND NORMAL STABILIZER LEAN-PROVED]`

## Headline exposed by the theorem

> **Reality does not move through quantum possibilities. It leaves them. Time is conjectured to
> point in that outward direction.**

This headline is a physical conjecture. The theorem below proves the tangent-versus-normal
selection law that motivates it.

## Setup

Let
\[
W=\mathbb C^5=A\oplus B,\qquad
\dim_{\mathbb C}A=3,\qquad \dim_{\mathbb C}B=2,
\]
with \(A=\langle e_1,e_2,e_3\rangle\) and
\(B=\langle e_4,e_5\rangle\). Use the Fock model
\[
S^+=\Lambda^{\mathrm{even}}W^*
=\Lambda^0W^*\oplus\Lambda^2W^*\oplus\Lambda^4W^*
\]
for the positive chiral spinor of \(\operatorname{Spin}(10)\). After choosing a volume form,
write a spinor as
\[
\lambda=(\lambda^+,\lambda_{ab},\lambda^a),
\]
where \(\lambda^a\) is the vector coordinate corresponding to
\(\Lambda^4W^*\cong W\).

The affine pure-spinor cone is cut out by the ten Cartan quadrics
\[
\begin{aligned}
Q^a(\lambda)
&=\lambda^+\lambda^a+
  \frac18\varepsilon^{abcde}\lambda_{bc}\lambda_{de},\\
Q_a(\lambda)
&=\lambda_{ab}\lambda^b.
\end{aligned}
\tag{1}
\]
Their polarization is the multiplicity-one vector bilinear
\[
B_1:\operatorname{Sym}^2S^+\longrightarrow W\oplus W^*.
\]

Take the standard compatible pair
\[
p=1,\qquad q=e^{45}.
\tag{2}
\]
Krasnov identifies this pair with the commuting-complex-structure split
\(\mathbb R^{10}=\mathbb R^6\oplus\mathbb R^4\). Complexifying, the agreement sector is
\(A\oplus A^*\) and the disagreement sector is \(B\oplus B^*\).

## Theorem — tangent fracture is internal; colour-preserving normal fracture is relative

`[PROVED HERE]`

For the pair (2):

1. The differential of \(B_1(p,-)\) on the tangent space to the pure-spinor cone at \(q\) has
   image \(A\), and its projection to \(B\) vanishes identically.
2. The tangent quotient of the pure-spinor cone by the locus jointly pure with \(p\) is
   canonically isomorphic to \(A\). Thus first-order loss of joint purity **through pure states**
   has three complex agreement directions, not the two complex disagreement directions.
3. The projective normal fiber to the pure-spinor tenfold at \(p\) is
   \[
   N_pX\cong W=A\oplus B.
   \]
   Its \(SU(A)\cong SU(3)\)-fixed subspace is exactly \(B\). Therefore a nonzero
   colour-preserving normal failure of individual purity has one complex weak-doublet defect,
   whose underlying real carrier has dimension four.

### Proof

Write an infinitesimal spinor as
\[
\dot\lambda=(s,\alpha,t)
\in\Lambda^0W^*\oplus\Lambda^2W^*\oplus W.
\]

At \(p=(1,0,0)\), differentiating (1) gives
\[
dQ_p(s,\alpha,t)=(t,0).
\tag{3}
\]
Hence the affine tangent space has \(t=0\), while the five-dimensional projective normal fiber is
identified with \(W\) by \(dQ_p\). Under the pair stabilizer,
\[
W=A\oplus B.
\]
The fundamental \(A\) has no nonzero \(SU(3)\)-fixed vector, while \(SU(3)\) acts trivially on
\(B\). Therefore
\[
(N_pX)^{SU(3)}=B.
\tag{4}
\]
This proves part 3. It also gives the usual \(SU(5)\) doublet--triplet split
\[
\mathbf5=(\mathbf3,\mathbf1)_{-1/3}\oplus(\mathbf1,\mathbf2)_{1/2};
\]
the colour-preserving normal channel is the Higgs-type
\((\mathbf1,\mathbf2)_{1/2}\).

At \(q=(0,e^{45},0)\), differentiating the upper five equations in (1) gives
\[
\pi_A(dQ_q\dot\lambda)
\cong *_A\!\left(\pi_{\Lambda^2A^*}\alpha\right),
\tag{5}
\]
while differentiating the lower five gives, on the \(B\)-coordinates,
\[
\pi_{B^*}(dQ_q\dot\lambda)
\cong \iota_t e^{45}.
\tag{6}
\]
The two maps in (5) and (6) are isomorphisms
\(\Lambda^2A^*\cong A\) and \(B\cong B^*\), respectively. Consequently
\[
\dot\lambda\in T_q\widehat X
\quad\Longrightarrow\quad
\pi_{\Lambda^2A^*}\alpha=0,\qquad \pi_Bt=0.
\tag{7}
\]

Polarizing (1) at \(p\) shows
\[
B_1(p,\dot\lambda)=t
\tag{8}
\]
in the \(W\)-half of the vector representation. Equations (7) and (8) imply
\[
\pi_BB_1(p,\dot\lambda)=0
\qquad(\dot\lambda\in T_q\widehat X),
\tag{9}
\]
and arbitrary \(t_A\in A\) is allowed, so the image is exactly \(A\). This proves part 1.

For completeness, the projective lines on the spinor tenfold are parameterized by
\(\operatorname{OGr}(3,10)\). Lines through \(p\), equivalently choices of a common isotropic
three-plane inside the five-plane of \(p\), are parameterized by
\(\operatorname{Gr}(3,5)\), of dimension six. Moving along the selected line adds one parameter,
so the compatible-partner locus for fixed \(p\) has projective dimension seven. Since \(X\) has
dimension ten, its normal inside \(X\) has dimension three. The kernel of (8) on
\(T_q\widehat X\) has the corresponding affine dimension eight, and its quotient maps
isomorphically to \(A\). This proves part 2. \(\square\)

## Exact positive survivor — radial plus weak orbit is \(1+3\)

Identify the underlying real four-space of \(B\cong\mathbb C^2\) with the quaternions
\(\mathbb H\). For every unit \(q\in\mathbb H\), left multiplication by imaginary quaternions
gives
\[
\operatorname{Im}\mathbb H\longrightarrow q^\perp,
\qquad a\longmapsto aq.
\tag{10}
\]
This is an isomorphism. Orthogonality follows from
\[
\langle q,aq\rangle
=\operatorname{Re}\!\left(q\overline{aq}\right)
=|q|^2\operatorname{Re}(\bar a)=0.
\]
For \(x\perp q\), the inverse is \(a=x\bar q\), which is imaginary and obeys \(aq=x\).
Therefore every \(x\in\mathbb H\) has the unique form
\[
x=\langle q,x\rangle q+aq,
\qquad a\in\operatorname{Im}\mathbb H.
\tag{11}
\]

Equation (11) proves more than a dimension match: the three-plane orthogonal to a nonzero
doublet is exactly its infinitesimal left-\(SU(2)\) orbit. Combined with the pointed spin-factor
construction, the same nonzero four-vector supplies:

- one radial direction;
- three weak-orbit directions;
- one Lorentz spin-factor order unit and its \(1+3\) quadratic form.

The complete quaternionic statement, including existence and uniqueness in (11), is unconditional
in
`formal/GaloisForLFunctions/HTGeometry/HiggsCausalOrbit.lean`.

## No-go closure

- **Exact killing theorem/mechanism:** If \(e_2(\varepsilon)\) remains a pure spinor, then the
  first cross-defect \(B_1(p,\dot e_2)\) lies in \(A\). Its disagreement projection to \(B\) is
  identically zero. The earlier claim that a generic pure path leaving the compatible-pair locus
  directly selects the four-dimensional disagreement sector is false.
- **Strongest positive survivor:** The \(SU(3)\)-preserving normal fiber to the pure-state variety
  is exactly \(B\cong\mathbb C^2\), and its real four-carrier has the exact radial-plus-weak-orbit
  \(1+3\) decomposition (11).
- **New insight:** Tangential changes among possibilities report the common/internal three complex
  directions. The candidate spacetime reporter lives normal to individual purity and is selected
  intrinsically by preservation of colour.
- **Status:** Complete theorem formalized unconditionally. The explicit Cartan-coordinate equations,
  tangent classification, pure-tangent no-go, agreement-three surjectivity, transverse
  colour-preserving doublet, and its real dimension four are in
  `formal/GaloisForLFunctions/HTGeometry/PurePairNormalFracture.lean`. The tangent compatibility
  quotient, projective normal-fiber quotient, `SU(3)` action and exact fixed subspace, and joined
  quaternionic `1+3` capstone are in
  `formal/GaloisForLFunctions/HTGeometry/PurePairNormalBundleStabilizer.lean`.

## Post-theorem physical conjecture

`[CONJECTURE FROZEN AFTER THEOREM] [PROOF ROUTE UNKNOWN]`

> **CONJECTURE — ACTUALITY-NORMAL SPACETIME LAW.** Every elementary event is a nonzero,
> colour-preserving normal actualization of a compatible exceptional pure-state pair. Tangential
> motion within pure-state space changes quantum possibility and internal charge but creates no
> spacetime. The colourless normal weak doublet is the event's four-dimensional causal carrier.
> Its radial ray is local time, its weak orbit is local three-space, and its pointed positive cone
> is local future. Event-to-event curvature of these normal rays is gravity.

This conjecture was selected as a truth-hunch from the exact tangent obstruction, normal
doublet--triplet split, observed preservation of colour, and quaternionic orbit identity. It was
not selected because a proof route is visible.

The public form is:

> **Time is the direction reality leaves quantum possibility. The Higgs field points that way.
> Gravity is the failure of those directions to agree.**

## Hostile physics boundary

The theorem does not establish any of the following:

- that a physical measurement or actualization is normal displacement in the Cartan embedding;
- that colour preservation is sufficient to select every physical event;
- that the normal weak doublet is the measured Standard Model Higgs field rather than only the
  same representation;
- that a gauge orbit becomes physical space rather than remaining redundancy;
- a base-free soldering from event carriers to a tangent bundle;
- causal signalling, Einstein dynamics, universal free fall, quantum probabilities, or a finite
  prediction.

The one-field gauge problem is acute. A Higgs direction is gauge-covariant, not itself observable.
A viable theory must turn pre-spacetime weak frame changes into local frame redundancy while
constructing gauge-invariant causal relations. Existing graviweak models use a generalized
one-form soldering field; they do not prove that this scalar exceptional normal channel performs
that job.

## Literature and priority boundary

Prior ingredients:

- Krasnov, [Geometry of \(\operatorname{Spin}(10)\) Symmetry
  Breaking](https://arxiv.org/abs/2209.05088): compatible pair \(1,e^{45}\), exact Standard Model
  stabilizer, and \(6+4\) product structure.
- Kuznetsov, [On linear sections of the spinor tenfold,
  I](https://arxiv.org/abs/1801.00037): \(X=\operatorname{OGr}_+(5,10)\), lines parameterized by
  \(\operatorname{OGr}(3,10)\), quadrics in the vector \(\mathbf{10}\), and
  \(N_{X/\mathbb P(S^+)}\cong\Lambda^4\mathcal U^*\cong\mathcal U(2)\).
- Nesti--Percacci, [Graviweak Unification](https://arxiv.org/abs/0706.3307): a generalized
  soldering one-form as order parameter, metric emergence, and the Coleman--Mandula boundary.
- Dvali--Pokorski, [Naturally Light Higgs Doublet in the Spinor Representation of SUSY
  \(SO(10)\)](https://arxiv.org/abs/hep-ph/9601358): Higgs doublets in a spinorial
  \(\operatorname{Spin}(10)\) setting and doublet--triplet splitting.
- Higgs/metric and emergent-spacetime mechanisms are prior in
  [Sardanashvily](https://arxiv.org/abs/gr-qc/9405013) and
  [Kirsch](https://arxiv.org/abs/hep-th/0503024).

No audited source states the combined tangent no-go, colour-preserving normal selection, exact
weak-orbit/pointed-spin-factor identity, and actuality-normal physical law. Priority remains open
until specialist review.

## Gates

- [x] 0 → 1: exact question and kill condition identified
- [x] 1 → 2: Cartan-coordinate proof and strongest positive survivor dependency-closed on paper
- [x] 2 → 3: exact coordinate tangent/no-go, tangent quotient, projective normal fiber,
  stabilizer-fixed doublet, dimension, and quaternionic survivor formalized and audited
- [ ] 3 → 4: physical actualization, gauge-invariant soldering, gravity, prediction, and hostile
  novelty review passed

## Log

- 2026-07-29 — first-order tangent audit killed the pure-path spacetime-defect mechanism.
  Extracted the colour-preserving normal weak doublet as positive survivor and froze the
  actuality-normal conjecture only after the no-go.
- 2026-07-29 — formalized the exact quaternionic identity that the orthogonal three-plane at a
  nonzero doublet is its infinitesimal weak orbit, with unique radial-plus-orbit decomposition.
- 2026-07-29 — formalized the explicit ten Cartan quadrics at the compatible pair, their complete
  linearized system, the vanishing weak/disagreement reporter for every pure tangent, surjectivity
  onto the agreement three-vector, and the non-tangent real-four colour-preserving channel in
  `HTGeometry/PurePairNormalFracture.lean`.
- 2026-08-01 — closed geometric packaging in
  `HTGeometry/PurePairNormalBundleStabilizer.lean`: tangent compatibility quotient is linearly
  equivalent to the agreement triplet; projective normal fiber is linearly equivalent to
  `A ⊕ B`; an explicit determinant-one unitary `SU(3)` action has fixed subspace exactly `B`;
  its complex and real ranks are two and four; and the capstone includes the exact quaternionic
  radial-plus-orbit decomposition. Direct elaboration, umbrella reachability, formal lint, axiom
  audit, and final module build pass.
