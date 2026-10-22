# Quantum events make spacetime: the four-direction fracture law

- **ID:** `four-dimensional-higgs-event-fracture-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `history-nonseparability-unification-law.md`
- **Statement:** Every elementary quantum event converts one exceptional four-direction
  Higgs polarization into a local \(1+3\) spacetime polarization; gravity is the obstruction to
  making these conversions agree, while the three internal forces are the curvature left inside
  their common Standard Model stabilizer.

## Public headline

> **Space and time are the four directions in which two quantum possibilities disagree. Gravity
> is how that disagreement changes from event to event.**

The particle-physics equivalent is:

> **Space and time are what the Higgs becomes when a quantum event happens.**

The event formulation is:

> **At every quantum event, matter loses four directions—and the universe gains space and time.**

The fuller worldview claim is:

> **Quantum events make spacetime. Gravity is clocks disagreeing about how those events fit into
> one before-and-after.**

“When” is explanatory language, not a time order. The incoming side is logically
pre-localized: the conjecture does not place a Higgs field on a previously supplied spacetime and
then evolve it.

## Frozen conjecture

`[PHYSICAL CONJECTURE; PROOF ROUTE UNKNOWN; DO NOT RESHAPE FOR PROVABILITY]`

Conjecture admission rule: based on everything presently known, the statement below is believed
plausibly true even though no proof route is known. Provability is deliberately excluded from
conjecture selection. Exact theorems later in this card are evidence, constraints, or falsifiers;
they are not weaker substitutes for the conjecture.

There is one pregeometric exceptional event degree with two physically inequivalent
Standard-Model reductions:

1. a matter polarization in which four colourless real directions transform as two weak
   doublets, \(\mathbf2\oplus\mathbf2\);
2. an observable polarization in which the corresponding four directions transform as a weak
   triplet and singlet, \(\mathbf3\oplus\mathbf1\).

An elementary quantum event is the indivisible, necessarily representation-changing conversion
between these polarizations. The outgoing \(\mathbf3\oplus\mathbf1\) is not merely a count: after a
Lorentzian real form is selected, it is the local tangent coordinate of an operational event, with
the singlet giving time and the triplet giving space. Gluing these conversions across events yields
the tetrad. Failure of the gluing to be integrable is gravitational curvature. Curvature that
preserves the local conversion lies in
\(S(U(2)\times U(3))\) and appears at low energy as electromagnetism, the weak force, and the strong
force.

This statement is frozen because current evidence gives a truth-hunch, not because a proof is
visible. No action, quantum measure, conversion map, Einstein limit, or finite prediction is
presently known.

## Why this hunch, rather than an easier theorem

The conjecture is the strongest coherent physical reading of six independently obtained
collisions:

1. [Exceptional event geometry](https://arxiv.org/abs/math/0306329) supplies a chiral matter
   tangent \(16\), a quadratic normal carrier \(10\), and a fundamental observable carrier \(27\).
2. Two exact constructions select the same abstract Standard Model gauge group in that parent
   geometry but select nonconjugate subgroups:
   [Krasnov's pure-spinor/matter embedding](https://arxiv.org/abs/2209.05088) and the
   [Baez--Schwahn nested-Jordan-observable embedding](https://arxiv.org/abs/2606.15235).
3. The same compatible exceptional pure-state pair selects the \(6+4\) product structure, while
   [Baez--Bokor--Boyle](https://arxiv.org/abs/2607.10833) show that its bi-Cayley state space
   transforms as one complete Standard Model fermion generation. Its two maximal isotropic
   five-planes meet in three complex directions, leaving exactly two relative directions on each
   side.
4. On the ten-carrier, the two endpoint colour sectors agree but their colourless sectors are
   exactly
   \[
   \mathbf2\oplus\mathbf2
   \quad\longleftrightarrow\quad
   \mathbf3\oplus\mathbf1.
   \]
   This is the Higgs-versus-spacetime-shaped fracture.
5. A complex doublet produces a positive Hermitian \(2\times2\) outer square whose determinant is
   the \(1+3\) Lorentz form and vanishes exactly on the null cone.
6. Exact representation theory forbids a continuous fixed-carrier interpolation. The conversion,
   if physical, must pass through a singularity, change carrier, or cease to be an exact group
   representation.

None proves the frozen physical identification. Together they make it more than dimensional
numerology and motivate the jump before its proof route is known.

## Exact bridge: the four-direction fracture index

`[PAPER-PROVED KINEMATICS; GENERIC CONSTANCY LEAN-PROVED; E6 BRANCHING NOT YET LEAN]`

Let \(z=-I\) be the central involution of weak \(SU(2)\) on either ten-dimensional complexified
carrier. Its characters are

\[
\chi_{\rm mat}(z)=2,\qquad \chi_{\rm obs}(z)=10.
\]

For an involution on an \(n\)-dimensional complex carrier, the negative eigenspace has dimension
\((n-\chi(z))/2\). Hence

\[
\dim V^-_{\rm mat}=4,\qquad
\dim V^-_{\rm obs}=0,\qquad
\Delta_{\rm fracture}
=\frac{\chi_{\rm obs}(z)-\chi_{\rm mat}(z)}2=4.
\]

The number four is therefore an exact representation-change index: precisely four carrier
directions cease to be weak-odd. It is not yet a derivation of spacetime dimension. The conjectural
jump is that this independently defined fracture index *is* operational tangent dimension.

The generic constancy and endpoint obstruction are unconditional in
`formal/GaloisForLFunctions/HTGeometry/RepresentationFracture.lean`. The Hermitian/null-cone bridge
is unconditional in
`formal/GaloisForLFunctions/HTGeometry/HiggsSpinorNullCone.lean`. Those modules prove kinematics
only.

## Exact bridge: nonconjugacy in \(E_6\)

`[PAPER-PROVED; PRIORITY OPEN; NOT YET LEAN]`

The [Baez--Schwahn observable restriction](https://arxiv.org/html/2606.15235v1) of the complex
\(27\) contains
\(\operatorname{End}(\mathbb C^2)\), and therefore a colourless, neutral weak adjoint
\((\mathbf1,\mathbf3)_0\). The
[standard matter restriction](https://arxiv.org/abs/1704.04219)
\[
27=16\oplus10\oplus1,\qquad
16=\Lambda^{\rm even}(\mathbb C^2\oplus\mathbb C^3),\qquad
10_{\mathbb C}=(\mathbb C^2\oplus\mathbb C^3)
\oplus(\mathbb C^2\oplus\mathbb C^3)^*
\]
contains only weak singlets and doublets.

Conjugacy in \(E_6\) would make the restrictions of the \(27\) equivalent. Any automorphism of the
Standard Model Lie algebra preserves its unique three-dimensional simple ideal, weak
\(\mathfrak{su}(2)\). Presence versus absence of a weak triplet is therefore invariant. The
subgroups are not conjugate in \(E_6\).

This repairs an earlier inconsistent statement in the source card. Searches through the audited
exceptional-Jordan, pure-spinor, GUT, and subgroup literature found the ingredients but no source
stating this comparison. Priority remains open until a specialist classification audit is
complete.

## Upstream jump: spacetime is a defect of joint quantum purity

`[POST-FREEZE PHYSICAL CONJECTURE; EXACT PRIOR PURE-SPINOR SELECTOR; VECTOR-DEFECT BRIDGE OPEN]`

The event ten-carrier need not be inserted independently of quantum matter. The bi-Cayley
hermitian Jordan triple

\[
W=\mathbb O_{\mathbb C}^{\,2}
\]

is the complex chiral spinor \(\mathbf{16}\) of \(\operatorname{Spin}(10)\). In the Jordan-pair
quantum interpretation, its minimal tripotents are pure quantum states. Two collinear minimal
tripotents \(e_1,e_2\) select:

- the exact global group
  \(G_{\rm SM}=(SU(3)\times SU(2)\times U(1))/\mathbb Z_6\);
- the full restriction of \(W\) as one Standard Model fermion generation, including a
  right-handed neutrino;
- the common Peirce-\(\tfrac12\) triple \(M_{3,2}(\mathbb C)\), whose real inner automorphism group
  is \(G_{\rm SM}\).

These are results of
[Baez--Bokor--Boyle](https://arxiv.org/abs/2607.10833), not claims of this programme. Their explicit
tripotents are the same pair of complex structures used in
[Krasnov's pure-spinor characterization](https://arxiv.org/abs/2209.05088). Krasnov proves that
the compatible pair selects the product structure

\[
\mathbb R^{10}=\mathbb R^6\oplus\mathbb R^4
\]

and the aligned Pati--Salam subgroup, with \(G_{\rm SM}\) as the relevant intersection. Thus two
exceptional pure states already select, in one structure, a fermion generation, the exact quantum
gauge group, and the \(6+4\) split used by the event interface.

There is an important no-go. The unique multiplicity-one vector channel in

\[
\operatorname{Sym}^2(\mathbf{16})=\mathbf{10}\oplus\mathbf{126}
\]

defines a spinor bilinear

\[
B_1:\operatorname{Sym}^2 W\longrightarrow V_{10}.
\]

For the compatible pair that selects \(G_{\rm SM}\), the statement that every linear combination
of \(e_1,e_2\) remains a pure spinor is exactly

\[
B_1(e_1,e_2)=0.
\]

The two states therefore do **not** directly produce a nonzero event vector. The strongest positive
survivor is not merely numerical. Each pure spinor selects a maximal isotropic complex five-plane
\(L_i\subset V_{10,\mathbb C}\). Compatibility gives

\[
\dim_{\mathbb C}(L_1\cap L_2)=3.
\]

The intersection and its conjugate produce the real six-plane; the two relative complex
two-planes produce the real four-plane. This is the exact pure-spinor origin of Krasnov's
\(\mathbb R^6\oplus\mathbb R^4\) product structure: common directions give the colour
\(\mathbf3\oplus\overline{\mathbf3}\), while relative directions give the two weak doublets.
The dimension implication \(5,5,3\Rightarrow7,2,2,6,4\) is unconditional in
`formal/GaloisForLFunctions/HTGeometry/PurePairFiveThreeFracture.lean`; Lean does not prove the
pure-spinor intersection hypothesis or any physical identification.

The bilinear supplies a transverse reporter. For a deformation \(e_2(\varepsilon)\) away from the
compatible-pair locus,

\[
v_{\rm event}
=\left.\frac{d}{d\varepsilon}\right|_{\varepsilon=0}
B_1\!\left(e_1,e_2(\varepsilon)\right)\in V_{10}
\]

is the first obstruction to their remaining jointly Cartan-pure. It is a vector-valued event
displacement, not the whole carrier. The unperturbed pair has already selected the carrier and its
Pati--Salam \(6+4\) decomposition.

This motivates a sharper truth-hunch:

> **CONJECTURE — PURE-PAIR ACTUALIZATION LAW.** An elementary quantum event is a transverse failure
> of two compatible exceptional pure states to remain jointly pure. Its first purity defect is the
> \(\mathbf{10}\)-valued event displacement in the carrier already selected by the pair. The
> maximal nonconjugate interface transmits its common six directions, leaves its relative
> four-dimensional Higgs sector as kernel, and creates a four-dimensional Lorentzian cokernel.
> Composition curvature of these defects is the four-force curvature.

Publicly:

> **Space and time begin where quantum possibilities stop fitting together.**

Here “pure” means Cartan pure-spinor/Jordan-tripotent compatibility, not yet ordinary density-matrix
purity, decoherence, or wavefunction collapse. Identifying it with an operational quantum event is
new physics and may be false. The derivative also depends on a transverse direction until a
source-natural normal class or quotient is constructed. No probability law, dynamics, Born-rule
update, causal order, or nonzero-defect theorem has been derived.

New open core:

`PURE-PAIR DEFECT TO EVENT INTERFACE` — construct the intrinsic normal bundle of the compatible
pure-pair locus, prove that the \(B_1\) derivative descends to its physical quotient and selects the
same \(V_{10}=\mathbb H\oplus V_6\) used by the interface, then determine whether its
kernel/cokernel composition defines quantum probabilities and Lorentzian causal order.

### 2026-07-29 correction: the pure tangent reporter is killed

`[EARLIER MECHANISM FALSIFIED] [POSITIVE NORMAL SURVIVOR]`

Direct linearization of the Cartan pure-spinor quadrics at the standard pair
\(e_1=1,e_2=e^{45}\) shows:
\[
\dot e_2\in T_{e_2}\widehat X
\quad\Longrightarrow\quad
B_1(e_1,\dot e_2)\in\mathbb C^3_{\rm agreement}.
\]
The projection of every pure tangent defect to the relative
\(\mathbb C^2_{\rm disagreement}\) is zero. Thus a continuous path through individually pure
states cannot supply the proposed four-dimensional event vector.

The strongest positive survivor lies in the normal fiber to **individual** purity at \(e_1\):
\[
N_{e_1}X\cong
\mathbb C^3_{\rm colour}\oplus\mathbb C^2_{\rm weak}.
\]
Its \(SU(3)\)-fixed subspace is exactly the colourless weak doublet
\(\mathbb C^2_{\rm weak}\), whose underlying real carrier is four-dimensional. The revised
proof-route-blind hunch is therefore that physical actualization is a colour-preserving normal exit
from pure-state space, not tangential motion among pure possibilities.

Publicly:

> **Time is the direction reality leaves quantum possibility. The Higgs field points that way.**

The complete proof and no-go closure are in
`../2-fully-proven/pure-pair-normal-actuality-fracture.md`. The exact quaternionic survivor is
stronger than a dimension count: for a nonzero doublet \(q\in\mathbb H\), its orthogonal
three-plane is exactly the infinitesimal left-weak orbit
\(\{aq:a\in\operatorname{Im}\mathbb H\}\), and every quaternion has a unique
radial-plus-orbit decomposition. This is unconditional in
`formal/GaloisForLFunctions/HTGeometry/HiggsCausalOrbit.lean`.

This correction supersedes the pure-tangent wording of `PURE-PAIR ACTUALIZATION LAW`; it does not
establish that normal displacement is a physical event, that gauge orbit is space, or that event
curvature is gravity.

## Post-freeze candidate realization: the exceptional interface line

`[LITERATURE COMPOSITION; PHYSICAL INTERPRETATION CONJECTURAL; NOT A PROOF ROUTE]`

Let \(J_{\mathbb C}\) be the complexified Albert algebra with the compact \(E_6\)-action, let
\(e=E_1\) be a primitive diagonal idempotent, and let \(\mathbf1=E_1+E_2+E_3\). The affine segment

\[
X_t=e+t(\mathbf1-e)=(1,t,t),\qquad 0\leq t\leq1,
\]

is intrinsic once the matter endpoint \(e\) and observable endpoint \(\mathbf1\) have been selected.
The compact orbit-type classification gives

\[
\operatorname{Stab}_{E_6}(X_0)\cong\operatorname{Spin}(10),\qquad
\operatorname{Stab}_{E_6}(X_t)\cong\operatorname{Spin}(9)\ (0<t<1),\qquad
\operatorname{Stab}_{E_6}(X_1)\cong F_4.
\]

Moreover, from the stabilizer definitions,

\[
\operatorname{Spin}(9)
=\operatorname{Stab}_{F_4}(e)
=\operatorname{Stab}_{E_6}(e)\cap\operatorname{Stab}_{E_6}(\mathbf1)
=\operatorname{Spin}(10)\cap F_4.
\]

Thus the already selected matter and observable parent groups possess a canonical common
interface along the straight exceptional line. This is not an invented product of unrelated
groups. The result follows by composing the compact
[orbit-type classification](https://arxiv.org/abs/1011.0613) with the explicit
[exceptional stabilizer definitions](https://arxiv.org/abs/1010.5936); the group geometry is prior.

This must not be confused with the three complex projective Jordan-rank orbits. Those are rank
one (Cayley plane), rank two (regular Cartan cubic), and rank three (open complement), as described
by [Iliev--Manivel](https://arxiv.org/abs/1102.3618) and
[Huebschmann](https://arxiv.org/abs/math/0104213). For every \(0<t<1\),
\(\det X_t=t^2\neq0\), so the interior of the compact interface line has full Jordan rank three.
Its \(\operatorname{Spin}(9)\) stabilizer comes from the repeated spectral value, not from a
rank-two discriminant. Split-real Jordan-rank orbits already classify
[supergravity black-hole charges](https://arxiv.org/abs/1002.4223), so rank stratification itself
cannot be the discovery.

What the interface line establishes:

- the \(\operatorname{Spin}(10)\), \(\operatorname{Spin}(9)\), and \(F_4\) sequence is exact and
  internal to one exceptional carrier;
- the generic interface symmetry is exactly the intersection of the endpoint parent symmetries;
- a smooth ambient carrier path exists, so exceptional geometry alone does **not** force a
  singular map.

What it does not establish:

- that \(X_t\) is a physical event or that \(t\) is time;
- that either marked Standard Model subgroup, the Higgs/spacetime carrier identification, or a
  conversion law is selected by the line;
- that a physical path must follow this segment;
- that the weak triplet becomes spatial rotation, that the singlet becomes time, or that gluing
  produces a tetrad;
- an action, quantization, Einstein limit, or prediction.

The exact representation-fracture theorem is unaffected: a smooth path of ambient Albert
coordinates is not a continuous family of exact weak-\(SU(2)\) representations joining the two
endpoint characters. A physical realization must still change carrier, change the exact
representation law, or introduce a singular reduction. Which alternative nature selects remains
open.

### Compatibility test: no gauge subgroup simply survives the conversion

`[PAPER-PROVED FROM PRIOR STRUCTURE; PHYSICAL TRANSPORT OPEN]`

Choose \(e=E_3\). Its Peirce-zero Jordan subalgebra is

\[
A=J_0(e)\cong\mathfrak h_2(\mathbb O),
\qquad \mathbf1_A=\mathbf1-e.
\]

Every \(F_4\)-automorphism preserves \(\mathbf1\). Hence preserving \(A\) is equivalent to fixing
\(\mathbf1-e\), and therefore to fixing \(e\):

\[
\operatorname{Stab}_{F_4}(A)=\operatorname{Stab}_{F_4}(e)\cong\operatorname{Spin}(9).
\]

For a compatible \(B\cong\mathfrak h_3(\mathbb C)\), the Baez--Schwahn observable group is

\[
G_{\rm obs}
=\operatorname{Stab}_{F_4}(A)\cap\operatorname{Stab}_{F_4}(B)_0
\subset\operatorname{Spin}(9).
\]

It therefore fixes every \(X_t=e+t(\mathbf1-e)\). The exceptional interface line canonically
supports the observable embedding.

The matter embedding behaves oppositely. On the \(\operatorname{Spin}(10)\) vector carrier,

\[
\mathbb C^{10}
=\big(\mathbb C^2\oplus\mathbb C^3\big)
\oplus\big(\mathbb C^2\oplus\mathbb C^3\big)^*,
\]

so \(G_{\rm mat}\) has no nonzero invariant vector. Every
\(\operatorname{Spin}(9)\subset\operatorname{Spin}(10)\) is the stabilizer of such a vector.
Consequently

\[
G_{\rm mat}\not\subset g\operatorname{Spin}(9)g^{-1}
\quad\text{for every }g\in\operatorname{Spin}(10).
\]

Thus the compact interface is not an ordinary symmetry-breaking path on which one Standard Model
gauge subgroup survives. The phrase “common Standard Model stabilizer” can mean only a common
**abstract group type** until an additional transport law is constructed. A viable event must
identify connections, charges, representations, and anomaly data across nonconjugate embeddings.
Because the embeddings are nonconjugate even in \(E_6\), that transport cannot be an inner
exceptional gauge rotation.

This opens a more precise core:

`NONCONJUGATE GAUGE TRANSPORT` — construct a gauge-independent event correspondence whose two
boundary symmetry groups are \(G_{\rm mat}\) and \(G_{\rm obs}\), whose induced representation
transport realizes the four-direction fracture, and whose composition has a well-defined
curvature. Without this object, neither the three internal forces nor gravity has been unified.

### Exact survivor: the four-for-four interface index

`[PAPER-PROVED; INVOLUTION INDEX LEAN-PROVED; EXPLICIT BRANCHING NOT YET LEAN]`

For the semisimple \(SU(2)\times SU(3)\) core, write the two complex ten-carriers as

\[
\begin{aligned}
V_{\rm mat}
&=C_{\rm mat}\oplus H_{\rm mat},
& C_{\rm mat}&=(\mathbf1,\mathbf3)\oplus(\mathbf1,\overline{\mathbf3}),
& H_{\rm mat}&=(\mathbf2,\mathbf1)\oplus(\mathbf2,\mathbf1),\\
V_{\rm obs}
&=C_{\rm obs}\oplus S_{\rm obs},
& C_{\rm obs}&=(\mathbf1,\mathbf3)\oplus(\mathbf1,\overline{\mathbf3}),
& S_{\rm obs}&=(\mathbf3,\mathbf1)\oplus(\mathbf1,\mathbf1).
\end{aligned}
\]

Here factor order is weak then colour. By irreducibility and Schur's lemma, every equivariant
linear map \(T:V_{\rm mat}\to V_{\rm obs}\) satisfies

\[
H_{\rm mat}\subseteq\ker T,\qquad
\operatorname{im}T\subseteq C_{\rm obs},\qquad
\operatorname{rank}T\leq6.
\]

If \(T\) has maximal possible rank, then

\[
\ker T=H_{\rm mat},\qquad
\operatorname{coker}T\cong S_{\rm obs},\qquad
\dim\ker T=\dim\operatorname{coker}T=4.
\]

Equivalently, the maximal common linear transport is a span through the common colour type,

\[
V_{\rm mat}\twoheadrightarrow C
\lhook\joinrel\longrightarrow V_{\rm obs},
\qquad
C\cong\mathbf3\oplus\overline{\mathbf3}.
\]

This is the sharp positive content exposed by the no-invertible-interface obstruction:

> **Every maximal symmetry-respecting linear bridge removes exactly four matter directions and
> leaves exactly four observable directions unproduced.**

Under the frozen physical conjecture, the kernel is the Higgs \(2+2\) and the cokernel is the
spacetime-shaped \(3+1\). The theorem does **not** convert one into the other. It proves that any
such conversion requires extra nonlinear or quantum event data. Calling the common six-dimensional
type “what passes through” is only representation language until a connection-level transport and
an action are defined.

The source-independent involution core is unconditional in
`formal/GaloisForLFunctions/HTGeometry/EventInterfaceIndex.lean`: on a complex ten-carrier, any
linear map intertwining a trace-two involution with the identity has kernel and cokernel dimension
at least four and range dimension at most six; rank six makes both dimensions exactly four. The
explicit \(SU(2)\times SU(3)\) branching and identification of those subspaces with
\(H_{\rm mat}\), \(C\), and \(S_{\rm obs}\) remain paper-proved but not yet formalized.

This finite-dimensional pattern is compatible with the modern observation that interfaces
between phases with different symmetry-charge assignments can be forced to be noninvertible, but
the available theorem is for symmetry-enriched \(1+1\)-dimensional critical phases
([Prembabu--Shao--Verresen](https://arxiv.org/abs/2512.23706)). It is analogy, not evidence that the
exceptional event exists in \(3+1\) dimensions.

## Causal audit: one event is null; a pair can be a frame

`[STANDARD SPINOR GEOMETRY; EVENT INTERPRETATION CONJECTURAL]`

The outer square of one nonzero doublet \(o\in\mathbb C^2\),

\[
\ell=o\,o^\dagger\in\mathfrak h_2(\mathbb C),
\]

is future-positive and Lorentz-null. It defines one causal ray, not a four-dimensional coordinate
chart or tetrad. Its common \(U(1)\) phase is invisible. This boundary is already unconditional in
`formal/GaloisForLFunctions/HTGeometry/HiggsSpinorNullCone.lean`.

Two linearly independent spinors \(o,\iota\) behave differently. Put

\[
S=(o\ \iota)\in GL(2,\mathbb C),\qquad
X=S S^\dagger=o\,o^\dagger+\iota\,\iota^\dagger.
\]

Then

\[
\det X=|\det S|^2>0,
\]

so \(X\) is timelike. Acting on the Pauli-Hermitian basis gives four independent Hermitian vectors

\[
E_\mu=S\sigma_\mu S^\dagger,
\]

equivalently the standard null tetrad
\(\ell=o o^\dagger\), \(n=\iota\iota^\dagger\),
\(m=o\iota^\dagger\), and \(\bar m=\iota o^\dagger\).
This is ordinary two-spinor/Newman--Penrose geometry, not a discovery; see the
[spin-frame construction](https://arxiv.org/abs/2012.15694) and the standard
[tetrad--spinor bundle correspondence](https://arxiv.org/abs/gr-qc/9502022).

The post-freeze physical refinement suggested by this exact boundary is:

> **One quantum event makes a light ray. Two make spacetime. Gravity is the disagreement between
> such pairs.**

Here “two” must mean a composable pair in a still-undefined relational event groupoid, not two
points in a spacetime already assumed. The claim is compatible with the frozen conjecture: an
elementary conversion supplies null causal data, while gluing conversions must supply a
nondegenerate spin-frame and tetrad. It is a truth-hunch, not a proof strategy.

The minimal candidate gluing variable would be a relative spin-frame

\[
g_{xy}=S_yS_x^{-1}\in GL(2,\mathbb C).
\]

After determinant normalization, its \(SL(2,\mathbb C)\) part transports Lorentz frames; loop
holonomy supplies ordinary spin curvature. The central phase is invisible to Hermitian vectors and
could support a \(U(1)\) connection. None of this is new by itself: it repackages standard spin and
\(\operatorname{Spin}^c\) geometry. Novel physics would require the exceptional noninvertible event
law to select \(S_x\), its composition, the Lorentzian real form, and an action.

### The two-\(SU(2)\) problem

`[LIVE THREAT; EXACT QUATERNIONIC PARENT NOW FOUND]`

The observable weak \(SU(2)\) acts on
\(\mathfrak h_2(\mathbb C)=\mathbf1\oplus\mathbf3\) by conjugation, exactly like compact spatial
frame rotations. If its connection is also declared to be the observed weak-force connection, the
two curvatures are locked. That is incompatible with treating gravity as universal Lorentz
holonomy while the weak force is massive, short-range, and representation-dependent.

The theory therefore needs one of two structures:

1. the event changes the observable \(SU(2)\) representation law into geometric
   \(SL(2,\mathbb C)\), while an independent transported copy remains weak isospin; or
2. exceptional geometry supplies two intrinsically distinct \(SU(2)\) connections and a law
   selecting which is geometric.

The four-carrier itself supplies an exact candidate separation. Write the underlying real
four-space as the quaternions \(\mathbb H\). Unit quaternions give

\[
\operatorname{Spin}(4)=SU(2)_L\times SU(2)_R,\qquad
(u,v):q\longmapsto u q v^{-1}.
\]

Restriction to the left factor, \(u:q\mapsto uq\), complexifies to
\(\mathbf2\oplus\mathbf2\). Restriction to the diagonal subgroup,
\(u:q\mapsto uqu^{-1}\), fixes the real scalar line and rotates the imaginary quaternion
three-plane, hence gives \(\mathbf1\oplus\mathbf3\). At the central element \(-1\), the left action
is \(-I_4\) while diagonal conjugation is \(I_4\). Thus the exact fracture can be read as

\[
SU(2)_L\subset SU(2)_L\times SU(2)_R
\quad\longrightarrow\quad
SU(2)_{\rm diag}\subset SU(2)_L\times SU(2)_R.
\]

This four-space is not external to the exceptional carrier. The standard Pati--Salam restriction
inside \(\operatorname{Spin}(10)\) gives, at representation level,

\[
\operatorname{Spin}(4)\times\operatorname{Spin}(6)
\longrightarrow\operatorname{Spin}(10),
\qquad
\mathbf{10}=(\mathbf2,\mathbf2,\mathbf1)\oplus(\mathbf1,\mathbf1,\mathbf6).
\]

Restricting the bidoublet \((\mathbf2,\mathbf2,\mathbf1)\) through \(SU(2)_L\) gives the matter
\(\mathbf2\oplus\mathbf2\); restricting the same bidoublet through \(SU(2)_{\rm diag}\) gives the
observable \(\mathbf3\oplus\mathbf1\). The \(\operatorname{Spin}(6)\) vector is unchanged and
restricts under colour to \(\mathbf3\oplus\overline{\mathbf3}\). Thus the complete branching has
one structural source:

\[
\underbrace{(\mathbf2,\mathbf2,\mathbf1)}_{\text{left versus diagonal reading}}
\quad\oplus\quad
\underbrace{(\mathbf1,\mathbf1,\mathbf6)}_{\text{transmitted colour carrier}}.
\]

This also recovers the exact central-character arithmetic used by the interface theorem. On the
matter endpoint, the abstract weak central element maps to
\((-1,1,1)\), acts as \(-I_4\oplus I_6\), and has trace \(2\). On the observable endpoint it maps
to \((-1,-1,1)\), acts as \(I_4\oplus I_6\), and has trace \(10\). The Pati--Salam restriction
therefore realizes, rather than merely resembles, the character fracture that forces the
four-dimensional kernel and cokernel.

The Pati--Salam splitting and its relation to the pure-spinor Standard Model subgroup are prior;
see [Krasnov](https://arxiv.org/abs/2209.05088). The candidate-new claim is that its left-to-diagonal
change is an elementary event and that the diagonal four-space is operational tangent space.

Publicly:

> **A quantum event turns handedness into spacetime: a left-only four-space becomes one time plus
> three space, while the other six directions pass through.**

This is standard quaternionic spin geometry, not new representation theory; see the standard
\(\operatorname{Spin}(4)\) pair action and the unit-quaternion conjugation model of \(SO(3)\).
Its relevance here is new only if the exceptional event canonically selects these two embeddings
as its matter and observable endpoints.

The algebraic bridge is unconditional in
`formal/GaloisForLFunctions/HTGeometry/QuaternionicWeakSpacetimeFracture.lean`. Lean proves the
pair-action composition law, left and diagonal restrictions, the opposite actions of central
\(-1\), and the invariant scalar-line plus three-dimensional imaginary-plane decomposition.

This resolves the *representation-parent* question, not the two-connection problem. Both chiral
factors are needed to obtain the Lorentzian vector representation after real-form selection, so
the second factor cannot simply be declared a spare weak group. The viable conjectural mechanism
is instead genuinely noninvertible: the kernel retains the left-factor weak action while the
cokernel carries the diagonal spatial action, producing two descendant connections on different
cohomology bundles even though they are not commuting subgroups on one fiber. Whether such
connection-level descent exists for the nonconjugate exceptional endpoints is unknown.

A Lorentzian real form must still turn the Euclidean \(\operatorname{Spin}(4)\) parent into
\(\operatorname{Spin}^+(1,3)\), the cokernel connection must become gravitational spin transport,
and the kernel connection must survive as observed compact weak isospin. No event action,
real-form selector, mass mechanism, or low-energy connection map is known. The existing
same-corner overlap no-go in
`formal/GaloisForLFunctions/HTGeometry/WeakLorentzOverlap.lean` still blocks identifying the two
connections after the fact.

New open core:

`EVENT SPIN-FRAME COMPLETION` — prove that composable noninvertible events canonically generate a
nondegenerate spin-frame; select the Lorentzian real form of the quaternionic
\(SU(2)_L\times SU(2)_R\) parent; derive distinct gravitational-cokernel and weak-kernel
connections without pretending they are commuting subgroups of one fiber; and make
event-composition holonomy equal gravitational holonomy. If noninvertible cohomology cannot retain
compact weak transport independently of Lorentz transport, the frozen four-force claim is false.

## Candidate event complex: spacetime as the cokernel of matter

`[POST-FREEZE REALIZATION HUNCH; DEFECT-COMPLEX MATHEMATICS PRIOR]`

The exact interface index suggests replacing an impossible invertible conversion by a two-term
event complex

\[
\mathcal E:\qquad
V_{\rm mat}\xrightarrow{\,T\,}V_{\rm obs},
\qquad \operatorname{rank}T=6.
\]

Its two cohomology spaces are

\[
H^{-}(\mathcal E)=\ker T\cong\mathbf2\oplus\mathbf2,\qquad
H^{+}(\mathcal E)=\operatorname{coker}T\cong\mathbf3\oplus\mathbf1.
\]

The quaternionic Pati--Salam parent now supplies the first non-arbitrary local candidate. Write

\[
V_{10}=\mathbb H\oplus V_6.
\]

Give the source \(\mathbb H\) the left \(SU(2)_L\) action and the target \(\mathbb H\) the diagonal
action, while keeping the same \(V_6\) action. Then

\[
T_{\rm PS}(h,c)=(0,c),\qquad
\theta_{\rm PS}:\ker T_{\rm PS}\to\operatorname{coker}T_{\rm PS},\quad
\theta_{\rm PS}(h)=h
\]

has rank six, transmits exactly the common colour carrier, and identifies the two four-spaces as
real vector spaces while changing their representation law. This is canonical relative to a
chosen Pati--Salam splitting and quaternionic real structure. It is not yet a canonical physical
event because the exceptional endpoint data has not been shown to choose those structures
globally or uniquely up to gauge.

This gives a sharper candidate ontology:

> **Spacetime is the four-dimensional failure of matter to pass unchanged through a quantum
> event.**

Or, in exact but less public language:

> **The Higgs is the kernel of an event; spacetime is its cokernel.**

The statement is a conjectural physical reading of the exact index, not a theorem. For an arbitrary
maximal-rank \(T\), the complex does not map its kernel into its cokernel. The Pati--Salam model
above supplies a candidate fiberwise soldering

\[
\theta:\ker T\longrightarrow\operatorname{coker}T
\]

must be supplied. For induced connections on the two cohomology bundles, its typed obstruction is

\[
D^2\theta=F_{\rm coker}\theta-\theta F_{\rm ker}.
\]

The frozen gravity claim is that a base-free event composition law selects \(T\) and \(\theta\),
turns the Lorentzian real form of \(\operatorname{coker}T\) into operational tangent space, and
turns this obstruction into gravitational curvature. At present:

- no canonical isomorphism \(G_{\rm mat}\to G_{\rm obs}\) has been selected;
- \(T_{\rm PS}=0_{\mathbb H}\oplus I_{V_6}\) and
  \(\theta_{\rm PS}=I_{\mathbb H}\) are canonical only after choosing the Pati--Salam split and
  quaternionic real structure; their source-natural exceptional selection is unproved;
- \(\theta_{\rm PS}\) is not yet a tetrad, because no base-free analogue of a tangent-valued
  one-form or discrete edge coframe has been defined;
- the curvature identity is formal connection algebra and does not imply Einstein dynamics;
- the index has virtual rank zero, so nontrivial topology would have to reside in the family index
  class, not the numerical index.

This construction has major prior collisions. Kernels, cokernels, and index classes of tachyon maps
encode D-brane defects and worldvolumes in
[K-matrix/K-homology constructions](https://arxiv.org/abs/hep-th/0108085) and
[exact tachyon condensation](https://arxiv.org/abs/hep-th/0212188). Higgs fields as odd components
of [Quillen superconnections](https://arxiv.org/abs/hep-th/9801040) are also prior. Therefore
“spacetime from a kernel/cokernel complex” or “Higgs as a superconnection” cannot be claimed as new
machinery. The priority-open residue is the exact exceptional nonconjugate

\[
(\mathbf2\oplus\mathbf2)_{\rm kernel}
\quad\leftrightarrow\quad
(\mathbf3\oplus\mathbf1)_{\rm cokernel}
\]

interface and its proposed operational-spacetime interpretation.

New open core:

`CANONICAL EVENT COHOMOLOGY SOLDERING` — derive the abstract gauge-group identification,
the local Pati--Salam formulas \(T_{\rm PS}=0\oplus I_6\) and
\(\theta_{\rm PS}=I_{\mathbb H}\), and their composition from exceptional event axioms rather than
choosing the split. Show that all admissible choices are gauge/field-redefinition equivalent or
derive a finite observable distinguishing them.

## Connection descent: one event, three channels, four curvatures

`[EXACT CONNECTION-ALGEBRA BRIDGE; PHYSICAL SECTOR IDENTIFICATION CONJECTURAL]`

The rank-six map resolves the two-\(SU(2)\) problem at connection level more sharply than a
group-locking story. Locally write

\[
E_{\rm mat}=K_4\oplus I_6,\qquad
E_{\rm obs}=C_4\oplus I_6,\qquad
T=0_{K_4\to C_4}\oplus I_{I_6}.
\]

For completely arbitrary connections \(\nabla_K,\nabla_I,\nabla_C\), set

\[
\nabla_{\rm mat}=\nabla_K\oplus\nabla_I,\qquad
\nabla_{\rm obs}=\nabla_C\oplus\nabla_I.
\]

Then \(T\) is parallel:

\[
\nabla_{\rm obs}T=T\nabla_{\rm mat}.
\]

Conversely, parallelism of a constant-rank \(T\) makes \(\ker T\) invariant, makes
\(\operatorname{im}T\) invariant, and induces a connection on \(\operatorname{coker}T\). Curvature
obeys

\[
F_{\rm obs}T=TF_{\rm mat}.
\]

It is therefore forced to agree only on the transmitted six-plane. It imposes no equality between
the curvature on the incoming kernel and the curvature on the outgoing cokernel. The weak
connection can live on \(K_4\), the gravitational spin connection can live independently on
\(C_4\), and the colour connection can be transmitted on \(I_6\), without postulating two
commuting \(SU(2)\) actions on one fiber. Noninvertibility is doing essential physical work: an
invertible \(T\) would identify all curvature.

The pointwise algebraic content is unconditional in
`formal/GaloisForLFunctions/HTGeometry/EventConnectionDescent.lean`. Lean proves kernel and range
invariance, commutator-curvature descent, arbitrary independent kernel/cokernel endomorphisms for
the split event, and the contrasting conjugacy forced by an invertible bridge. It does not
formalize a manifold connection or any physical sector label.

The candidate unification jump is now:

> **CONJECTURE — EVENT COHOMOLOGY CURVATURE LAW.** Every physical force is a descendant curvature
> of the universal exceptional event complex. Its kernel curvature gives weak isospin; its
> transmitted traceless-unitary curvature gives colour; the determinant compatibility tying the
> weak and colour carriers into \(S(U(2)\times U(3))\) gives hypercharge and, after the event
> selects a neutral direction, electromagnetism; its Lorentzian cokernel curvature gives gravity.
> The off-diagonal covariant variation that relates kernel to cokernel is the common
> Higgs--soldering sector. No force is an independently added gauge factor.

Publicly:

> **The four forces are the four ways a quantum event fails to turn matter perfectly into
> spacetime.**

The exact global Standard Model group matters here. A generic \(U(2)\times U(3)\) connection would
contain two independent abelian curvatures. The determinant-one relation defining
\(S(U(2)\times U(3))\) leaves one, with the \(\mathbb Z_6\) global quotient and charge normalization
already encoded. The event law must derive this relation from the exceptional stabilizer; ranks
\(4/6/4\) alone do not.

Two maps should not be conflated. The event conversion is a plain real-bundle isomorphism

\[
\eta:K_4\longrightarrow C_4
\]

whose weak-to-Lorentz relative curvature may be nonzero. The gravitational solder form is

\[
e:C_4\longrightarrow TM
\]

and is compatible with the gravitational spin connection in the usual way. The earlier composite
\(\theta=e\eta:K_4\to TM\) is not required to be parallel for the weak connection. Indeed, if
\(D\eta=0\), then \(F_C\eta=\eta F_K\), incorrectly locking weak and gravitational curvature.

This bridge is strong but not dynamics. Connection descent is standard mathematics; it does not
derive the event, select Lorentz signature, produce the Einstein equation, fix coupling constants,
give the electroweak mass spectrum, or prove that the surviving abelian curvature is observed
electromagnetism. Its value is narrower and exact: the noninvertible \(4/6/4\) interface has enough
typed room for all four curvatures without identifying weak isospin with spatial rotation.

New open core:

`EVENT DERIVED CONNECTION` — construct one source-natural connection on the exceptional event
two-extension whose induced kernel, image, determinant, and cokernel curvatures have precisely the
Standard Model and Lorentz representations, anomalies, real forms, and low-energy dynamics.

## Failed global jump: the Higgs carrier is the tangent bundle

`[FALSIFIED AS A UNIVERSAL LAW] [STANDARD TOPOLOGY; NOT YET LEAN]`

A rank-six event map has one canonical exact sequence

\[
0\longrightarrow K_4\longrightarrow V_{\rm mat}^{10}
\xrightarrow{T}V_{\rm obs}^{10}\longrightarrow C_4\longrightarrow0.
\]

Equivalently, it is a Yoneda two-extension of \(C_4\) by \(K_4\), factored through the common
six-dimensional transmitted carrier. This packages three distinct physical readings without
adding dimensions:

\[
\text{four matter directions lost}
\quad+\quad
\text{six directions transmitted}
\quad+\quad
\text{four spacetime directions created}.
\]

There is a severe correction. In ordinary complex vector spaces, and in finite-dimensional
representations of a compact group over characteristic zero, every such extension splits. A
pointwise linear extension class therefore cannot be gravity. Any nontrivial class must live in
the global family over composable events, in a nonsemisimple representation-change category, or in
the failure of local splittings to glue.

The topology-level truth-hunch is:

> **CONJECTURE — EVENT SOLDERING TOPOLOGY LAW.** On every regular continuum phase of the event
> theory, the physical real form of the four-dimensional incoming electroweak doublet carrier
> \(\mathcal H_{\mathbb R}\) is soldered isomorphically to the outgoing tangent bundle:
> \[
> \theta:\mathcal H_{\mathbb R}\xrightarrow{\ \cong\ }TM.
> \]
> The weak and gravitational connections remain independent connections; gravity is their
> gauge-covariant failure to be identified by \(\theta\), represented locally by
> \[
> D^2\theta=F_{TM}\theta-\theta F_{\mathcal H}.
> \]

Here the complexified kernel
\(\mathbf2\oplus\mathbf2\) is interpreted as the complexification of the one real quaternionic
weak-doublet carrier \(\mathcal H_{\mathbb R}\), not as eight independent real tangent directions.
The quaternionic left-to-diagonal fracture is the local representation model for \(\theta\).

Publicly:

> **The Higgs field remembers the shape of the universe because it is spacetime on the other side
> of a quantum event.**

### Hostile verdict

The universal bundle-isomorphism statement is false. On \(S^4\), any such isomorphism would force
\[
\langle c_1(\mathcal H)^2,[S^4]\rangle
=2\chi(S^4)+3\sigma(S^4)=4,
\]
but \(H^2(S^4;\mathbb Z)=0\), hence \(c_1(\mathcal H)=0\). More generally, the isomorphism ties weak
second Chern number to spacetime Euler class, while Standard Model \(SU(2)\) gauge theory has
independent instanton sectors on fixed spacetime.

The full no-go and positive survivor are recorded in
`../../../5-failed/higgs-tangent-universal-soldering-topology-law.md`. The event-to-spacetime bridge must
remain noninvertible and configuration-dependent; it cannot be a universal identification of the
internal weak bundle with \(TM\).

Noninvertibility is necessary but not sufficient. For a constant-rank bundle event
\(T:E_{\rm mat}\to E_{\rm obs}\), Grothendieck additivity gives
\[
[\ker T]-[\operatorname{coker}T]=[E_{\rm mat}]-[E_{\rm obs}].
\]
Thus using the same global ten-bundle on both sides still forces stable equality of the weak
kernel and spacetime cokernel classes. Rank change alone does not evade this absolute identity;
localized topology requires additional relative/clutching data of the event map. The exact
paper and Lean theorem is recorded in
`../../../3-formalized/not_new_scientific_knowledge/event-topological-debt-conservation.md`.

New open core:

`EVENT INDEX SOURCE` — derive from base-free exceptional event axioms either a nonzero parent
virtual class \([E_{\rm mat}]-[E_{\rm obs}]\), or a localized relative event class including its
clutching data, and prove that its continuum image is exactly the weak--spacetime topological
mismatch. Defining these bundles over a pre-existing manifold does not count as emergence.

The bundle identification is much stronger than equality of four dimensions. It makes a finite,
parameter-free topological prediction. On a compact oriented Euclidean continuation \(M\), let
\(\mathcal H\) be the complex rank-two electroweak carrier whose realification is
\(\mathcal H_{\mathbb R}\). If \(\theta\) exists and preserves orientation, standard characteristic
class identities give

\[
c_2(\mathcal H)=e(TM),\qquad
c_1(\mathcal H)^2-2c_2(\mathcal H)=p_1(TM).
\]

After evaluation on \([M]\),

\[
\langle c_2(\mathcal H),[M]\rangle=\chi(M),\qquad
\langle c_1(\mathcal H)^2,[M]\rangle=2\chi(M)+3\sigma(M).
\]

Thus weak instanton topology and electroweak determinant flux would be fixed by spacetime Euler
characteristic and signature. These equations are standard consequences of an oriented real
bundle isomorphism; the new and unproved physics is that the event fracture supplies that
isomorphism. They are not yet an empirical prediction because the correct global Standard Model
bundle, Lorentzian-to-Euclidean passage, boundary terms, singular events, and admissible spacetime
class have not been derived.

This sharpens the two-\(SU(2)\) problem rather than hiding it. The weak and chiral Lorentz
\(SU(2)\) factors must be distinct local symmetries acting on the two sides of \(\theta\); the
soldering relates their carriers but need not equate their connections. Existing graviweak
theories already relate a chiral Lorentz \(SU(2)\) to weak isospin
([Nesti--Percacci](https://arxiv.org/abs/0706.3307)), and gravitational Higgs/soldering mechanisms
are prior. Quantum causal histories already put quantum channels on causally ordered events
([Hawkins--Markopoulou--Sahlmann](https://arxiv.org/abs/hep-th/0302111)), while causal sites already
have a categorical tangent structure
([Christensen--Crane](https://arxiv.org/abs/gr-qc/0410104)). None of those precedents supplies the
exceptional nonconjugate \(4/6/4\) two-extension or the displayed electroweak--spacetime
characteristic-class identification.

For base-free composition, the minimal candidate is an event category whose objects are the
two-term complexes and whose arrows are admissible noninvertible chain maps. Reachability can
define causal order only after cycles and parallel-arrow gauge are quotiented so that the result is
a locally finite partial order. Under future/past distinguishing continuum hypotheses, causal
order fixes conformal geometry and event density can fix volume scale; this is the established
causal-reconstruction route, not a new theorem. The missing theorem is that the event category
actually satisfies those hypotheses and that its \(C_4\) cohomology reconstructs the same tangent
bundle.

New open cores:

- `EVENT TWO-EXTENSION GLOBALIZATION` — find the nonsemisimple/global category in which the
  pointwise split \(4/6/4\) sequence has a canonical nonzero obstruction class.
- `HIGGS-TANGENT CHARACTERISTIC MATCH` — construct the real soldering and determine exactly which
  Lorentzian spacetimes, boundaries, singularities, and Standard Model bundles satisfy it.
- `EVENT-ORDER CONTINUUM RECONSTRUCTION` — derive a locally finite causal order and prove its
  continuum conformal, volume, and tangent reconstruction.

## What is genuinely new if true

Existing “gravity as a Higgs field” theories treat a metric, tetrad, or de Sitter vector as a
gravitational Higgs field on a supplied base. Existing exceptional-Jordan models identify a
Standard Model stabilizer of observables. Existing \({\rm Spin}(10)\) models place a matter
generation in a chiral spinor. Existing Goldstone constructions compare a \(3+1\) split with broken
spacetime symmetries.

This conjecture makes a different ontological claim:

- the Standard Model Higgs representation is not merely coupled to spacetime;
- an event is not initially a point *in* spacetime;
- spacetime and the electroweak Higgs are mutually exclusive readings of the same parent event
  directions;
- gravity and the internal forces are complementary curvature components of the conversion
  between those readings.

If true, it would explain why spacetime is four-dimensional, why its signature is \(1+3\), why a
Higgs doublet exists, why gravity couples universally, and why the three other forces have the
Standard Model group, from one event law.

## Seductive variants rejected during formation

These are not the frozen conjecture:

1. **“Four dimensions because Higgs zeros have codimension four.”** A transverse section of a
   real rank-four bundle has a codimension-four zero set, but using this to select ambient
   dimension is circular unless independent physics says elementary events are isolated zeros.
   It was generated by an available theorem, not by evidence, so it is a bridge candidate only.
2. **“Spacetime began at the electroweak transition.”** For the measured Higgs mass the Standard
   Model has a [smooth electroweak crossover](https://arxiv.org/abs/1503.04935), not a
   gauge-invariant hard phase boundary. Standard primordial tensor modes receive a smooth
   [thermodynamic transfer correction](https://arxiv.org/abs/1803.01038), not a hard cutoff
   there. This cosmological headline is presently false or ill-posed.
3. **“The measured \(125\) GeV Higgs boson is the metric.”** This confuses two low-energy fields
   with the conjectured pregeometric parent polarization and conflicts with their spectra.
4. **“Weak isospin is spatial spin.”** Existing formal obstruction rules out identifying a
   nontrivial weak action with a pointwise Lorentz kernel on the same Hermitian corner.
5. **“Nonconjugacy already gives gravity.”** It gives an obstruction, not a soldering field,
   dynamics, equivalence principle, or Einstein equation.

## Hostile-review attack ledger

### 1. Is the number four inserted twice?

`[LIVE THREAT]`

Yes, unless the two reductions are selected independently by exceptional event axioms and the
fracture index is shown to control operational tangent rank. Merely observing
\(4=4\) fails. Required survivor: a uniqueness or reconstruction theorem in which neither
spacetime dimension nor a Higgs doublet is an input.

### 2. Is the conjecture gauge invariant?

`[LIVE THREAT]`

The components and vacuum expectation value of a Higgs doublet are gauge-dependent. A valid theory
must formulate conversion between reductions of a parent bundle or through invariant orbit data,
not convert four chosen components in a gauge. \(H=0\) is invariant, but a zero locus alone does not
define an event law.

The exceptional interface line supplies gauge-independent orbit-type data only after its two
endpoints have been selected. It therefore improves the type of candidate event object but does
not solve endpoint selection or turn the orbit parameter into a physical observable.

### 3. Does it reproduce general relativity?

`[OPEN CORE]`

No. “Curvature of failed gluing” is currently a typed idea, not a derivation. Required:

- a nondegenerate tetrad from the conversion;
- Lorentzian connection and curvature;
- Einstein or controlled modified-Einstein dynamics;
- universal coupling and equivalence principle;
- black-hole and cosmological solutions;
- quantum composition without a background causal order.

### 4. Does it derive all three internal forces?

`[OPEN CORE]`

The common stabilizer has the correct abstract group. That does not derive Yang--Mills dynamics,
chirality, anomaly cancellation, generations, symmetry breaking, masses, mixing, or couplings.
All must emerge from the same event action rather than be appended.

### 5. Why \(E_6\), and why these reductions?

`[LIVE THREAT]`

Conditional intrinsic geometry is not selection. Required: reconstruct the exceptional parent and
both marked reductions from operational event axioms, or identify a finite empirical consequence
that distinguishes this parent from other GUT/pregeometry models.

### 6. Is it prior?

`[SURVIVES CURRENT AUDIT; PRIORITY OPEN]`

Closest prior art contains separate pieces:

- tetrad or metric as a
  [gravitational Higgs](https://arxiv.org/abs/gr-qc/9405013);
- [emergent spacetime from broken diffeomorphism symmetry](https://arxiv.org/abs/hep-th/0503024)
  and [dynamical Cartan symmetry breaking](https://arxiv.org/abs/1311.4481);
- [\(3+1\) Goldstone/Higgs analogies](https://arxiv.org/abs/gr-qc/9607066);
- [exceptional-Jordan Standard Model stabilizers](https://arxiv.org/abs/2606.15235);
- [pure-spinor \({\rm Spin}(10)\) matter](https://arxiv.org/abs/2209.05088);
- [spinor-square exceptional vectors](https://arxiv.org/abs/0911.2255).

No audited source makes the exact nonconjugate
\((\mathbf2\oplus\mathbf2)\leftrightarrow(\mathbf3\oplus\mathbf1)\) event conversion, identifies
its outgoing side as spacetime, and identifies its cross-event integrability defect as gravity.
Absence from search is not proof of priority.

### 7. Does it predict anything finite?

`[FAILS NATURE GATE]`

Not yet. Candidate consequence routes, none claimed:

1. a fixed Higgs--curvature operator or coefficient;
2. the explicit event-soldering topology law
   \(\langle c_2(\mathcal H),[M]\rangle=\chi(M)\) and
   \(\langle c_1(\mathcal H)^2,[M]\rangle=2\chi(M)+3\sigma(M)\), after its physical global
   hypotheses are derived;
3. a restricted gravitational response of coherent Higgs-sector states;
4. a discrete obstruction to smooth scale-dependent spacetime dimension while exact Standard
   Model representation structure persists;
5. a new amplitude relation joining Higgs, graviton, and electroweak channels.

At least one parameter-free finite prediction must be derived before manuscript work.

### 8. Where is hypertranscendence?

`[POST-FREEZE CONJECTURE; UNIVERSAL HISTORY OBJECT NOT YET CONSTRUCTED]`

The finite event complex by itself cannot carry the required hypertranscendence. It is a
ten-dimensional linear object, and arbitrarily complicated finite-rank holonomy can still be
encoded by a fixed linear differential equation. The already retired
`noncommutative-holonomy-word-growth-differential-innovation.md` gives an explicit rank-four
hypergeometric counterexample. Curvature, noncommutativity, and long words therefore do not imply
hypertranscendence.

The truth-hunch concerns the universal compositional history, not an individual local event or
every curved classical solution. Suppose composable event complexes generate a canonical
transition-bearing pro-object

\[
\mathscr H_{\rm event}
=\{\mathcal E_N,\Xi_N:\mathcal E_{N+1}\to\mathcal E_N\}_{N\geq0},
\]

whose transition extensions preserve the four-dimensional incoming kernel, the dual
four-dimensional outgoing cokernel, and the arrows specifying how successive events are glued.
Call a clock reporter *event-conservative* when, up to physical gauge and null-history
equivalence, it preserves those extension classes and reconstructs their kernel/cokernel
incidence—not merely their dimensions, determinants, spectra, or zero sets.

> **CONJECTURE — UNIVERSAL EVENT-HISTORY HYPERTRANSCENDENCE.** Nature's complete event-history
> pro-object admits no finite differential-algebraic relative quotient that is
> event-conservative. Every intrinsic analytic clock reporter that is event-conservative on the
> full object is therefore hypertranscendental over the differential field generated by all local
> event laws.

Publicly:

> **No finite equation in time can contain the whole history of the universe, because time is
> created by the events the equation would have to compress.**

This does not say that no finite local field equations exist, that every metric coefficient is
hypertranscendental, or that nonzero curvature forces hypertranscendence. Minkowski, Schwarzschild,
cosmological, or other high-symmetry reductions may be differentially algebraic specializations.
The claim is that no finite differential-algebraic clock model is faithful to the universal
all-event extension object.

Two pieces of prior mathematics make the form of the conjecture plausible but do not prove it.
Iterated-integral path signatures retain a path up to tree-like equivalence
([Hambly--Lyons](https://arxiv.org/abs/math/0507536);
[Boedihardjo--Geng--Lyons--Yang](https://arxiv.org/abs/1406.7871)), while finite Hankel rank
characterizes finite-state rational noncommutative series via the
Kleene--Schützenberger--Fliess realization theorem. The internal
`hypertranscendental-socle-frame-clock-field.md` conjecture independently predicts that HT
nontermination is failure of every finite DA-relative quotient to remain conservative on a
transition-bearing extension field. The new physical jump is that composable exceptional events
realize such a field and that its persistent \(4/4\) defect is spacetime itself.

Neither nearby theory supplies the required result. A path can have an infinite signature without
producing a hypertranscendental scalar reporter; a non-rational noncommutative series need not
automatically yield the claimed differential-algebraic obstruction; and no event-history reporter
has yet been constructed. Shared growth, zeros, determinants, or curvature would fail the
anti-theatre gate unless two independently defined reporters preserve the same extension arrows,
kernel object, and dual cokernel.

New open core:

`EVENT EXTENSION NONTERMINATION` — construct \(\mathscr H_{\rm event}\), its physical null/gauge
quotient, and two independent intrinsic clock reporters. Prove or falsify their joint
conservativity on the same event extensions, then attack the claimed absence of a finite
DA-relative conservative quotient. A finite conservative quotient or a canonical
differentially-algebraic faithful reporter kills the conjecture.

## Nature editorial gate

[Nature's stated criteria](https://www.nature.com/nature/for-authors/editorial-criteria-and-processes)
require original research of outstanding scientific importance with an interdisciplinary
conclusion. Editors initially ask whether results are novel, arresting, and both immediate and
far-reaching.

- **Original:** exact event-conversion combination survives current search, but specialist
  priority audit remains open.
- **Outstanding importance:** would pass if established; presently a conjecture.
- **Interdisciplinary:** headline is intelligible across physics, mathematics, and general
  readership.
- **Arresting:** passes at conjecture level.
- **Immediate implications:** fails; no parameter-free observable.
- **Far-reaching implications:** passes conditionally.
- **Technical case established:** fails; event object, dynamics, Einstein limit, and experimental
  consequence remain open.

The card therefore remains research input, not a submission draft.

## Incompatible world and kill conditions

The frozen conjecture is false if any of the following is established:

1. the two physical reductions can be identified without representation change after the correct
   parent and global group are specified;
2. the \(27\)-character comparison is wrong;
3. a gauge-independent conversion cannot yield a nondegenerate Lorentzian tetrad;
4. conversion curvature cannot satisfy universal free fall or the observed Einstein limit;
5. the common stabilizer necessarily gives incorrect Standard Model representations or anomalies;
6. an already published theory contains the same parent reductions, event ontology, curvature
   decomposition, and physical identification;
7. every dynamics realizing the conversion violates unitarity, causality, locality in its
   empirical regime, or established Higgs/gravity bounds;
8. a discriminating prediction is derived and falsified.

Failure to find a proof is not a kill condition.

## Research programme

### Gate A — representation and priority closure

- complete specialist audit of \(E_6\) subgroup conjugacy and \(27\) branching;
- write a dependency-closed proof of the character obstruction;
- only then formalize that exact theorem unconditionally in Lean.

### Gate B — gauge-independent event object

- define parent event bundle without a supplied spacetime base;
- define matter and observable reductions intrinsically;
- identify admissible singular or carrier-changing conversions;
- quotient all gauge and field-redefinition redundancy.

### Gate C — gravity

- reconstruct tangent space, causal cone, tetrad, connection, and clock ordering;
- prove conversion holonomy equals gravitational holonomy;
- recover Einstein dynamics and universal coupling in a controlled limit;
- classify all spacetimes and all resulting gravities, not one background.

### Gate D — quantum theory and internal forces

- derive quantum probabilities/composition from event conversion;
- recover \(U(1)\), \(SU(2)\), and \(SU(3)\) curvatures and chiral matter;
- derive anomaly cancellation, Higgs dynamics, generations, masses, and couplings.

### Gate E — hypertranscendence and prediction

- define an operational history observable whose HGT status measures conversion integrability;
- prove any proposed equivalence rather than using hypertranscendence as metaphor;
- derive one parameter-free finite prediction;
- compare with collider, clock, equivalence-principle, gravitational-wave, black-hole, and
  cosmological data.

## Gates

- [x] 0 → 1: bold proof-independent truth-hunch, exact meaning, evidence, incompatible world,
  hostile attack, and kill conditions frozen
- [ ] 1 → 2: complete paper proof and physical derivation; no open dependency
- [ ] 2 → 3: all mathematical claims formalized unconditionally in Lean
- [ ] 3 → 4: parameter-free prediction survives data and hostile novelty review

Current Nature verdict: `[DO NOT WRITE MANUSCRIPT]`.

## Log

- 2026-07-28 — created in 1-in-progress. Frozen after internal corpus audit and primary-literature
  collision search. Proof route deliberately left unknown. Exact representation-fracture and
  null-cone bridges recorded without promoting them to the physical claim.
- 2026-07-28 — rejected isolated-Higgs-zero codimension as primary conjecture because it was
  selected by theorem availability rather than independent physical evidence. Rejected a cosmic
  electroweak birth boundary because the Standard Model electroweak transition is a crossover.
- 2026-07-28 — repaired ambient-conjugacy status: the weak-triplet character mismatch proves the
  two Standard Model reductions nonconjugate in \(E_6\). Priority and Lean gates remain open.
- 2026-07-28 — audited exceptional Jordan rank and compact orbit type. Corrected the tempting but
  false identification of the \(\operatorname{Spin}(9)\) interface with the rank-two Cartan-cubic
  stratum: \(e+t(\mathbf1-e)\) has full Jordan rank for \(t>0\). Recorded the exact compact
  \(\operatorname{Spin}(10)\to\operatorname{Spin}(9)\to F_4\) stabilizer line as a post-freeze
  candidate realization. It supplies no dynamics and does not prove singularity.
- 2026-07-28 — tested both marked Standard Model reductions against the interface. The observable
  subgroup lies in its \(\operatorname{Spin}(9)\) stabilizer; the matter subgroup lies in no
  conjugate \(\operatorname{Spin}(9)\) because it fixes no vector in the \(\mathbf{10}\).
  Ordinary surviving-subgroup symmetry breaking is therefore impossible. New open core:
  `NONCONJUGATE GAUGE TRANSPORT`.
- 2026-07-28 — extracted the sharp positive statement from the interface obstruction. Any
  semisimple-gauge-equivariant linear map kills the four-dimensional matter \(2+2\), lands in the
  common six-dimensional colour type, and has rank at most six. At maximal rank its cokernel is
  exactly the observable \(3+1\). The source-independent involution kernel/rank/cokernel index is
  now unconditional in `HTGeometry/EventInterfaceIndex.lean`; explicit branching remains
  paper-only. This is not a conversion law.
- 2026-07-28 — causal audit separated a null event from a tetrad. One doublet square supplies only
  a null ray; two independent spinors supply a standard spin-frame and null tetrad. Recorded the
  sharper post-freeze hunch “One quantum event makes a light ray. Two make spacetime.” Exposed the
  two-\(SU(2)\) problem: geometric frame rotation and weak isospin require distinct connections.
  New open core: `EVENT SPIN-FRAME COMPLETION`.
- 2026-07-28 — promoted the rank-six interface to a candidate two-term event complex. Its kernel is
  Higgs-shaped and its cokernel is spacetime-shaped, suggesting “Spacetime is the cokernel of
  matter.” Priority audit found kernel/cokernel tachyon defects, K-homology, and Higgs
  superconnections are established machinery. Novelty can only lie in canonical exceptional
  selection and operational/gravitational interpretation. New open core:
  `CANONICAL EVENT COHOMOLOGY SOLDERING`.
- 2026-07-28 — froze the user's conjecture-selection rule: truth-hunch first; proof route later.
  Promoted the HGT link from a proof-shaped research question to
  `UNIVERSAL EVENT-HISTORY HYPERTRANSCENDENCE`. Corrected its scope after the prior holonomy
  no-go: finite-rank curvature or word growth does not force HT. The conjecture concerns a
  gauge-reduced universal extension pro-object and source-conservative clock reporters. Rough-path
  signatures and finite-Hankel-rank realization theory are structural precedents, not proofs. New
  open core: `EVENT EXTENSION NONTERMINATION`.
- 2026-07-28 — identified the rank-six event as a canonical \(4/6/4\) Yoneda two-extension.
  Corrected the local reading: vector-space and compact-representation extensions split, so gravity
  can only be a global/nonsemisimple failure of event splittings to glue. Froze the post-event
  `EVENT SOLDERING TOPOLOGY LAW`: the real electroweak doublet carrier is the emergent tangent
  bundle while weak and gravitational connections remain distinct. Extracted the conditional
  parameter-free characteristic-class relations
  \(\langle c_2,[M]\rangle=\chi(M)\) and
  \(\langle c_1^2,[M]\rangle=2\chi(M)+3\sigma(M)\). Audited graviweak, quantum-causal-history, and
  causal-site collisions; none supplies the exceptional two-extension or this physical
  identification.
- 2026-07-28 — found the exact same-carrier parent of the \(2+2\leftrightarrow1+3\) fracture:
  \(\mathbb H\) under the left-factor versus diagonal embeddings in
  \(\operatorname{Spin}(4)=SU(2)_L\times SU(2)_R\). This supplies the missing second \(SU(2)\) at
  representation level and explains the central-character jump as left \(-I_4\) versus diagonal
  \(I_4\). Formalized the unconditional pair action, central fracture, and scalar-line plus
  imaginary-three-plane decomposition in
  `HTGeometry/QuaternionicWeakSpacetimeFracture.lean`. Hostile correction: both chiral factors are
  needed for Lorentzian vector geometry, so the second is not a spare weak group. The only viable
  current mechanism is noninvertible descent: weak transport on the kernel and gravitational
  transport on the cokernel. Lorentzian real-form selection and that connection descent remain
  open.
- 2026-07-28 — lifted the quaternionic fracture into the standard Pati--Salam branch
  \(\mathbf{10}=(\mathbf2,\mathbf2,\mathbf1)\oplus(\mathbf1,\mathbf1,\mathbf6)\). The matter
  \(2+2\) and observable \(3+1\) are left-factor and diagonal restrictions of the same bidoublet;
  the common \(3+\bar3\) is the transmitted \(\operatorname{Spin}(6)\) vector. This yields the
  first non-arbitrary local event model
  \(T_{\rm PS}=0_{\mathbb H}\oplus I_6\),
  \(\theta_{\rm PS}=I_{\mathbb H}\), conditional on a chosen Pati--Salam/quaternionic split.
  Global exceptional selection, gauge transport, and dynamics remain open.

## Post-freeze bridge: the outgoing four-space already has the algebraic form of gravity

`[BRIDGE: EXACT ALGEBRA LEAN-PROVED] [PHYSICAL SELECTION OPEN]`

The quaternionic cokernel does more than have dimension four.  An oriented four-coframe
\(e^0,e^1,e^2,e^3\) determines the triple

\[
\begin{aligned}
\Sigma^1_\tau&=\tau e^{01}+e^{23},\\
\Sigma^2_\tau&=\tau e^{02}-e^{13},\\
\Sigma^3_\tau&=\tau e^{03}+e^{12}.
\end{aligned}
\]

In the complex exterior algebra these obey the exact matrix law

\[
  \Sigma^i_\tau\wedge\Sigma^j_\tau
  =2\tau\,\delta^{ij}\,e^{0123}.
\]

The volume \(e^{0123}\) is nonzero.  For \(\tau\ne0\), the three \(\Sigma^i_\tau\) are linearly
independent.  At \(\tau=1\) they are the standard Euclidean quaternionic two-forms.  At
\(\tau=i\) they are the standard complex chiral continuation used in Lorentzian self-dual
gravity.  At \(\tau=0\) their entire wedge matrix degenerates.

These statements are proved unconditionally in
`formal/GaloisForLFunctions/HTGeometry/EventPlebanskiSimplicity.lean`.  The proof is in the actual
exterior algebra, not a coordinate surrogate.  It assumes no metric, Hodge star, action, Einstein
equation, or event interpretation.

This meets a nontrivial existing result.  Bhoja and Krasnov,
[*Four-dimensional Riemannian geometry via 2-forms*](https://arxiv.org/abs/2405.15408), prove that
a triple satisfying
\(\Sigma^i\wedge\Sigma^j\sim\delta^{ij}\) determines a Riemannian metric and orientation; its
intrinsic torsion is a uniquely determined \(SO(3)\) connection \(A\) satisfying

\[
  d\Sigma^i+\epsilon^{ijk}A^j\wedge\Sigma^k=0.
\]

They also prove, within the class of local actions quadratic in intrinsic torsion, that
diffeomorphism invariance and local \(SO(3)\) invariance select one action up to overall scale,

\[
  S[\Sigma]=-\frac12\int\epsilon^{ijk}\Sigma^i\wedge A^j\wedge A^k,
\]

and that its critical points are Einstein metrics.  Its first-order form is the Plebanski action.
The uniqueness is not uniqueness among arbitrary nonlocal or higher-derivative theories.  Their
theorem is Riemannian; Lorentzian use requires complex fields and separate reality conditions.

The new structural alignment is therefore:

```text
exceptional compatible pure-state pair
  selects a 6 + 4 carrier split

maximal event interface
  transmits 6 and creates a four-dimensional cokernel

Spin(4) / quaternionic structure on that cokernel
  creates a Plebanski simplicity triple automatically

variation of the triple across events
  has exactly the connection language in which Einstein gravity is selected
```

No step in the last two lines proves that nature uses this event interface.  What has changed is
the gravity gap: the outgoing four-space is no longer merely “spacetime-shaped.”  Conditional on
soldering and causal reality, it carries exactly the algebraic variable from which a metric,
connection, curvature, and the leading Einstein action can be reconstructed.

## Post-freeze conjecture: universal event--Einstein agreement law

`[PHYSICAL CONJECTURE; TRUTH-HUNCH; PROOF ROUTE NOT PART OF STATEMENT]`

> **CONJECTURE — UNIVERSAL EVENT--EINSTEIN AGREEMENT LAW.** Every nondegenerate continuum phase of
> physical event history is the gluing of the four-dimensional cokernels created by elementary
> pure-pair actualizations.  The event law selects the Lorentzian reality condition on their
> canonical complex simplicity triples and solders those cokernels to operational tangent
> directions.  In the long-wavelength vacuum limit, the only local cost of neighbouring events
> failing to agree is quadratic in the intrinsic torsion of that triple and is invariant under
> event relabelling and local rotation of the imaginary-quaternion basis.  Consequently its
> leading stationary histories are precisely Lorentzian Einstein spacetimes.  Gravitational
> curvature is the gauge-invariant obstruction to making all event-created clock frames agree.

Publicly:

> **Every quantum event creates its own spacetime. Gravity is the unique way those spacetimes can
> agree.**

Equivalent clock headline:

> **Gravity is clocks disagreeing about how quantum events fit together.**

This conjecture is intentionally stronger than the proved bridge.  Its truth-hunch is based on the
simultaneous appearance of:

1. a canonically selected exceptional \(6+4\) split from compatible pure states;
2. an exact noninvertible \(4/6/4\) event interface;
3. a quaternionic four-cokernel rather than an arbitrary four-vector space;
4. automatic Plebanski simplicity on that cokernel;
5. uniqueness of the leading invariant intrinsic-torsion action;
6. independent connection descent on kernel, image, and cokernel, which prevents weak isospin from
   being identified with Lorentz transport.

None of those facts was selected because it made the conjecture easy to prove.  They are the
accumulated evidence behind the hunch.  Provability begins after the statement.

### Hostile-review boundary

A hostile reviewer can still correctly reject all of the following stronger claims:

- **Lorentzian signature is derived.** It is not.  The Lean theorem proves the complex
  \(\tau=i\) endpoint is algebraically compatible; it does not select the anti-linear reality
  involution or one negative direction.
- **Einstein gravity is derived from the event law.** It is not.  The Bhoja--Krasnov theorem begins
  with a smooth \(SU(2)\)-structure on a manifold.  The event programme has not derived the
  manifold, soldering map, differentiability, action principle, or Lorentzian extension.
- **The gravity action is absolutely unique.** It is unique only at the stated leading
  two-derivative, intrinsic-torsion-quadratic, local and invariant order.  Higher-curvature,
  nonlocal, singular, or quantum corrections remain possible.
- **Matter coupling is recovered.** The cited theorem gives the vacuum Einstein condition.
  Universal coupling, stress energy, Newton's constant, cosmological constant, and the
  equivalence principle remain open.
- **The two chiral groups are unified with weak \(SU(2)\).** Connection descent proves they can be
  independent; it does not derive their relative coupling or observed chirality.
- **A parameter-free prediction follows.** None follows yet.

### New exact open core

`EVENT PLEBANSKI REALITY AND UNIQUENESS`

Construct or kill the following chain:

1. derive a gauge-independent soldering \(e:C\to TM\) from event composition rather than assume a
   manifold;
2. derive the Lorentzian anti-linear reality condition from the pure-pair defect and prove that it
   selects exactly one time direction;
3. prove that the continuum event mismatch functional has the locality, derivative order, and
   \(SO(3)\) invariance required by the uniqueness theorem;
4. extend the selection argument to the Lorentzian reality slice;
5. derive sourced Einstein equations and universal free fall from the same event connection;
6. show how the kernel/image/cokernel curvature sectors arise from one exceptional invariant
   functional rather than a direct sum of familiar actions;
7. extract a finite dimensionless observable.

The conjecture is false if a physically admissible event continuum satisfying the exceptional
interface has a leading invariant vacuum dynamics inequivalent to Einstein gravity, if causal
reality cannot be selected without extra background structure, or if the event cokernel cannot be
operationally soldered.

- 2026-07-28 — discovered the event--Plebanski bridge.  Formalized the full complex simplicity
  family, its Euclidean, complex-chiral, and degenerate endpoints, nonzero volume, and
  nondegenerate linear independence.  Primary-source audit found a 2026 theorem selecting the
  Einstein action from an \(SO(3)\)-covariant \(SU(2)\)-structure at leading local quadratic order.
  Froze `UNIVERSAL EVENT--EINSTEIN AGREEMENT LAW` without promoting this bridge to a derivation of
  Lorentzian signature, continuum spacetime, sourced dynamics, or any prediction.
- 2026-07-29 — completed the unconditional Cartan-coordinate falsification theorem in
  `HTGeometry/PurePairNormalFracture.lean`: pure motion cannot create the weak four-reporter at
  first order; the colour-preserving weak doublet survives only as a transverse channel. This
  sharpens the event hypothesis from “fracture between pure states” to “actualization leaves the
  pure-state variety.”
- 2026-07-29 — falsified the universal `EVENT SOLDERING TOPOLOGY LAW`. On \(S^4\), the required
  complex-rank-two realification would force \(c_1^2[S^4]=4\), although \(H^2(S^4)=0\). Independent
  electroweak instanton sectors on fixed spacetime give a second collision. Positive survivor:
  a universal internal/tangent identification is impossible.
- 2026-07-29 — proved the event topological-debt law. Constant-rank noninvertibility does not by
  itself free kernel and cokernel topology: their additive difference is exactly the global
  source--target difference and telescopes along composable histories. This forces the new
  `EVENT INDEX SOURCE` core and corrects the earlier, too-weak survivor.
