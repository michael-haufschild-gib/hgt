# Spectral phase-folding locality and addressability law

- **ID:** `spectral-phase-folding-locality-addressability-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / finite-holonomy correction / spectral-addressability law
- **Parents:** `../3-formalized/centralizer-phase-bandwidth-shortcut-extraction-law.md`,
  `path-local-centralizer-tangent-rigidity-law.md`
- **Status:** `[LEAN-PROVED] [FRONTIER ADVANCE] [NOVELTY PROVISIONAL]`
- **Date:** 2026-08-10

## Public sentence

For a generic local many-body Hamiltonian, wrapping a long evolution into a bounded spectral
phase necessarily destroys locality: away from phase collisions every exact local logarithm
retains the full elapsed-time action, and at every time no local logarithm can compress below one
full spectral winding.  The bounded folded logarithm therefore leaves the local Hamiltonian shell
at the first winding.  A shortcut must create the folded phase by a noncommuting transverse
excursion, and every fixed commutator order at finite action addresses only a null subset of the
exponentially large phase torus.

## Why the finite-holonomy conjecture must be replaced

The first parent extracts a large centralizer phase from every approximate shortcut.  The second
parent proves that, for a generic open chain, the local shell intersects the Hamiltonian
centralizer only in `span_R{I,H}`.  It is tempting to infer that finite local-control words cannot
return to the centralizer with a new phase.

That inference is false.  If `A` and `B` are Hermitian, the group commutator

\[
 C_\varepsilon(A,B)
 =e^{-i\varepsilon A}e^{-i\varepsilon B}
  e^{i\varepsilon A}e^{i\varepsilon B}
 =I-\varepsilon^2[A,B]+O(\varepsilon^3)                         \tag{1}
\]

can have a nonzero centralizer component even when both `A` and `B` have zero centralizer
component.  Holonomic quantum control exploits exactly this curvature mechanism.  Tangent
rigidity therefore excludes hidden commuting generators but does not exclude transverse loops.

The positive replacement has two parts.

1. **Locality--action dichotomy.**  Away from phase collisions a long-time unitary has no
   time-compressed local logarithm; at collisions every nonphysical local logarithm costs at
   least one full winding.  Its canonical subwinding logarithm exists only by becoming nonlocal.
2. **Spectral address filtration.**  Transverse holonomy reaches centralizer phases through a
   graded Lie-word filtration.  At every fixed grade and finite action its address set is too small
   to cover a generic many-body phase torus.

These statements are exact.  They do not yet lower-bound arbitrary finite circuits at positive
error.

## 1. Abstract setup

Let `K` be a complex Hilbert space of dimension `D>=3`, and let
`Herm(K)` be its real Hilbert space of Hermitian operators with Hilbert--Schmidt norm.  Let

\[
 H=\sum_{j=1}^D E_jP_j                                             \tag{2}
\]

have simple spectrum.  Let `L` be a finite-dimensional real subspace of `Herm(K)` containing
`I` and `H`, and put

\[
 \mathcal S_H=\operatorname{span}_{\mathbb R}\{I,H\}.              \tag{3}
\]

Assume **local centralizer rigidity**:

\[
 \boxed{
 \mathcal L\cap\{A:[H,A]=0\}=\mathcal S_H.}                       \tag{4}
\]

Assume also the minimal **two-gap irrationality** condition

\[
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_j-E_1:2\le j\le D\}\ge2.                                  \tag{5a}
\]

The completed-time applications below use the stronger maximal-projective condition

\[
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_j-E_1:2\le j\le D\}=D-1.                                    \tag{5}
\]

Write

\[
 U_H(t)=e^{-itH},\qquad
 W_H=\max_jE_j-\min_jE_j>0.                                       \tag{6}
\]

The phase spectrum of `U_H(t)` is simple when

\[
 t(E_j-E_k)\notin2\pi\mathbb Z\qquad(j\ne k).                     \tag{7}
\]

For fixed simple `H`, the exceptional times in `(7)` form a countable set.

## 2. Exact local logarithms: full rigidity off collisions, subwinding rigidity at all times

### Theorem A -- projective local-logarithm rigidity

Assume `(4)` and `(5a)`, and let `t` satisfy `(7)`.  If `K_0 in L` is Hermitian and

\[
 e^{-iK_0}=e^{i\phi}U_H(t)                                       \tag{8}
\]

for some real `phi`, then there is `m in Z` such that

\[
 \boxed{
 K_0=tH+(2\pi m-\phi)I.}                                         \tag{9}
\]

In particular,

\[
 \boxed{
 \max\operatorname{spec}K_0-\min\operatorname{spec}K_0
 =|t|W_H.}                                                        \tag{10}
\]

Thus no alternative time-independent generator in the same local shell can implement the endpoint
with smaller spectral action.  The only local exact logarithm is physical time, modulo scalar
phase.

### Proof

Every operator commutes with its exponential, so `(8)` gives

\[
 [K_0,U_H(t)]=0.                                                   \tag{11}
\]

Condition `(7)` makes the eigenspaces of `U_H(t)` the one-dimensional eigenspaces `P_j` of `H`.
Hence `[K_0,H]=0`.  Local centralizer rigidity `(4)` gives

\[
 K_0=aH+bI                                                        \tag{12}
\]

for real `a,b`.  Equation `(8)` now says that for integers `m_j`,

\[
 (a-t)E_j+b+\phi=2\pi m_j.                                       \tag{13}
\]

Subtract the equation for `j=1`:

\[
 (a-t)(E_j-E_1)=2\pi(m_j-m_1).                                  \tag{14}
\]

If `a!=t`, every nonzero anchored gap is an integer multiple of the same real number
`2pi/(a-t)`.  Any two anchored gaps then have rational ratio, contradicting `(5a)` because
`D>=3`.  Therefore `a=t`.  Equation `(13)` makes all `m_j` equal and gives
`b=2pi m-phi`.  Scalar shifts do not change spectral diameter, proving `(10)`. `square`

### Theorem A.1 -- collision-complete subwinding dichotomy

Assume `(4)` and `(5a)`, with no condition on the phase multiplicities of `U_H(t)`.  If `K_0 in L`
is Hermitian and satisfies `(8)`, then

\[
 \boxed{
 K_0=tH+(2\pi m-\phi)I\text{ for some }m\in\mathbb Z
 \quad\text{or}\quad
 \operatorname{diam}(\operatorname{spec}K_0)\ge2\pi.}
\]

Equivalently, every exact local logarithm whose spectrum fits strictly inside one phase window is
the physical elapsed-time logarithm, modulo scalar phase.  In particular,

\[
 |t|W_H\ge2\pi
 \quad\Longrightarrow\quad
 \text{no exact local logarithm of }e^{i\phi}U_H(t)
 \text{ has spectral diameter }<2\pi.
\]

### Proof

Suppose `diam(spec K_0)<2pi` and put `V=e^(-iK_0)=e^(i phi)U_H(t)`.  The operator `K_0`
commutes with `V`.  On each eigenspace of `V`, all eigenvalues of the Hermitian restriction of
`K_0` have the same exponential.  Any two such eigenvalues differ by an integer multiple of
`2pi`; the strict diameter bound forces that multiple to be zero.  Hence `K_0` is scalar on every
eigenspace of `V`.

The Hamiltonian `H` commutes with `V` and therefore preserves those eigenspaces.  Scalarity of
`K_0` on each one gives `[K_0,H]=0`, even when `V` has phase collisions.  Rigidity `(4)` now gives
`K_0=aH+bI`.  Equations `(13)--(14)` and two-gap irrationality `(5a)` force `a=t` and
`b=2pi m-phi`, exactly as in Theorem A.  The physical logarithm has diameter `|t|W_H`, proving
both alternatives and the consequence. `square`

At a phase collision a nonphysical logarithm may indeed mix energy eigenspaces and fail to commute
with `H`; Theorem A.1 proves that any such local exception must spend at least one complete
spectral winding.  Thus phase collisions no longer leave a loophole for bounded-action local
compression.

The threshold is sharp.  At `t=0`, choose any `H` satisfying `(5a)`, a rank-one projector `P`
which does not commute with `H`, and
`L=span_R{I,H,2pi P}`.  Then `(4)` holds, while

\[
 e^{-i2\pi P}=I=U_H(0),
 \qquad \operatorname{diam}(\operatorname{spec}(2\pi P))=2\pi.
\]

Thus `<2pi` in Theorem A.1 cannot be replaced by `<=2pi` under the stated hypotheses.

## 3. Bounded phase folding forces nonlocality

Choose the half-open phase representative

\[
 \operatorname{wr}(x)\in(-\pi,\pi],
 \qquad x-\operatorname{wr}(x)\in2\pi\mathbb Z.                  \tag{15}
\]

Define the canonical folded Hermitian generator and its integer branch ledger by

\[
 F_H(t)=\sum_j\operatorname{wr}(tE_j)P_j,
 \qquad
 N_H(t)=\sum_j {tE_j-\operatorname{wr}(tE_j)\over2\pi}P_j.       \tag{16}
\]

Then

\[
 F_H(t)=tH-2\pi N_H(t),\qquad
 e^{-iF_H(t)}=U_H(t),\qquad
 \operatorname{spec}F_H(t)\subset(-\pi,\pi].                    \tag{17}
\]

### Theorem B -- phase-folding locality fracture

Assume `(4)` and `(5a)`.  If `F_H(t) in L`, then

\[
 \boxed{F_H(t)=tH+2\pi mI}                                      \tag{18}
\]

for some integer `m`.  Consequently,

\[
 \boxed{
 |t|W_H\ge2\pi\quad\Longrightarrow\quad F_H(t)\notin\mathcal L.} \tag{19}
\]

Equivalently: after one full winding across the spectral diameter, bounded phase folding and
two-locality cannot coexist.

### Proof

The operator `F_H(t)` is a spectral function of `H`, so it commutes with `H` even when
`U_H(t)` has phase collisions.  If it lies in `L`, `(4)` gives

\[
 F_H(t)=aH+bI.                                                    \tag{20}
\]

Exponentiating `(20)` and comparing with `(17)` gives `(13)` with `phi=0`.  The same
two-gap argument as in Theorem A gives `a=t` and `b=2pi m`, proving `(18)`.

Because the spectrum is a finite subset of the half-open interval `(-pi,pi]`, the left side of
`(18)` has spectral diameter strictly smaller than `2pi`.  The right side has diameter
`|t|W_H`.  Thus `|t|W_H>=2pi` is impossible if `F_H(t)` is local. `square`

The theorem does not say that the endpoint unitary ceases to be generated by a local Hamiltonian:
the unwrapped logarithm `tH` remains local.  It says that **compressing the generator into one
bounded phase window forces it out of the local shell**.

### Theorem C -- quantitative fracture from the tangent condition number

If `L=S_H`, every distance-to-`L` conclusion below is trivial.  Otherwise let

\[
 \gamma_H=inf\{\|[H,A]\|_{\rm HS}:
 A\in\mathcal L\cap\mathcal S_H^\perp,\ \|A\|_{\rm HS}=1\}>0. \tag{21}
\]

For every Hermitian `F` commuting with `H`,

\[
 \boxed{
 \operatorname{dist}_{\rm HS}(F,\mathcal L)
 \ge {\gamma_H\over\gamma_H+W_H}
      \operatorname{dist}_{\rm HS}(F,\mathcal S_H).}            \tag{22}
\]

For the folded generator,

\[
 \boxed{
 \operatorname{dist}_{\rm HS}(F_H(t),\mathcal L)
 \ge {2\pi\gamma_H\over\gamma_H+W_H}
      \operatorname{dist}_{\rm HS}(N_H(t),\mathcal S_H).}       \tag{23}
\]

The right side is positive whenever the integer branch ledger is not affine in the spectrum.  Under
`(5a)`, every nonconstant branch ledger is non-affine.

### Proof

Fix `K in L`.  Since `F` commutes with `H`,

\[
 [H,K]=[H,K-F].                                                   \tag{24}
\]

Let `c=(max_j E_j+min_j E_j)/2`.  Then
`||H-cI||op=W_H/2` and `[H,X]=[H-cI,X]`.  The tangent estimate from `(21)` and the elementary
Hilbert--Schmidt commutator bound give

\[
 \begin{aligned}
 \operatorname{dist}_{\rm HS}(K,\mathcal S_H)
 &\le {\|[H,K]\|_{\rm HS}\over\gamma_H}\\
 &\le {W_H\over\gamma_H}\|K-F\|_{\rm HS}.
 \end{aligned}                                                    \tag{25}
\]

Therefore

\[
 \operatorname{dist}_{\rm HS}(F,\mathcal S_H)
 \le\|F-K\|_{\rm HS}
   +\operatorname{dist}_{\rm HS}(K,\mathcal S_H)
 \le\left(1+{W_H\over\gamma_H}\right)
       \|F-K\|_{\rm HS}.                                        \tag{26}
\]

Infimize over `K in L` to obtain `(22)`.  Since `tH in S_H`, equation `(17)` gives

\[
 \operatorname{dist}_{\rm HS}(F_H(t),\mathcal S_H)
 =2\pi\operatorname{dist}_{\rm HS}(N_H(t),\mathcal S_H),         \tag{27}
\]

proving `(23)`.  If an integer ledger belongs to `S_H`, its entries have the form
`aE_j+b`; comparing integer differences and using two rationally independent gaps forces `a=0`,
so the ledger is constant. `square`

No dimension-uniform lower bound on the last distance follows from rational independence alone.
Near-affine integer ledgers are a Diophantine obstruction, not a missing estimate in `(23)`.

### Theorem C.1 -- collision-complete approximate subwinding rigidity

Put

\[
 \sigma_H=\operatorname{dist}_{\rm HS}(H,\mathbb RI).
\]

Assume `(4)` and `L!=S_H`, let `0<eta<2pi`, and let `K_0 in L` be Hermitian with

\[
 \operatorname{diam}(\operatorname{spec}K_0)\le2\pi-\eta.
\]

If

\[
 \|e^{-iK_0}-e^{i\phi}U_H(t)\|_{\rm op}\le\varepsilon,
\]

then, without any phase-simplicity condition,

\[
 \boxed{
 \operatorname{dist}_{\rm HS}(K_0,\mathcal S_H)
 \le {\sigma_H\over\gamma_H}
       {2\pi-\eta\over\sin(\eta/2)}\,\varepsilon.}
\]

The constant diverges only when the candidate logarithm approaches a complete winding, exactly
where Theorem A.1 permits collision-induced nonphysical branches.

### Proof

Diagonalize `K_0` with eigenvalues `kappa_a`.  For every pair `a,b`, put
`d=|kappa_a-kappa_b|<=2pi-eta`.  Monotonicity, after continuous extension at zero, of

\[
 d\longmapsto {d\over2\sin(d/2)}
\]

on `[0,2pi)` gives

\[
 |\kappa_a-\kappa_b|
 \le {2\pi-\eta\over2\sin(\eta/2)}
      |e^{-i\kappa_a}-e^{-i\kappa_b}|.
\]

Comparing matrix entries of the two commutators in this eigenbasis yields

\[
 \|[H,K_0]\|_{\rm HS}
 \le {2\pi-\eta\over2\sin(\eta/2)}
      \|[H,e^{-iK_0}]\|_{\rm HS}.
\]

Set `E=e^(-iK_0)-e^(i phi)U_H(t)`.  Since `H` commutes with `U_H(t)`, for every scalar `c`,

\[
 \|[H,e^{-iK_0}]\|_{\rm HS}
 =\|[H-cI,E]\|_{\rm HS}
 \le2\|H-cI\|_{\rm HS}\|E\|_{\rm op}.
\]

Infimizing over `c` gives the factor `2 sigma_H epsilon`.  Finally decompose `K_0` into its
`S_H` and `S_H^perp` components inside `L` and apply the definition `(21)` of `gamma_H`.
Multiplying the three bounds proves the claim. `square`

### Corollary C.2 -- approximate local subwinding exclusion at every long time

Assume `(4)`, `(5a)`, and `L!=S_H`.  For `0<eta<2pi` define

\[
 C_{H,\eta}={\sigma_H\over\gamma_H}
 {2\pi-\eta\over\sin(\eta/2)}
\]

and the **projective affine-alias gap**

\[
 \chi_{H,t,\eta}
 =\inf_{\substack{a\in\mathbb R\\|a|W_H\le2\pi-\eta/2}}
   \inf_{\beta\in\mathbb R}
   \|e^{-i(aH+\beta I)}-U_H(t)\|_{\rm op}.
\]

If `|t|W_H>=2pi`, then

\[
 \boxed{\chi_{H,t,\eta}>0.}
\]

Moreover, no Hermitian `K_0 in L` with

\[
 \operatorname{diam}(\operatorname{spec}K_0)\le2\pi-\eta
\]

can satisfy

\[
 \|e^{-iK_0}-e^{i\phi}U_H(t)\|_{\rm op}\le\varepsilon
\]

whenever

\[
 \boxed{
 \varepsilon<
 \min\left\{{\eta\over4C_{H,\eta}},
 {\chi_{H,t,\eta}\over1+C_{H,\eta}}\right\}.}
\]

Thus approximate tubes do not reopen the collision loophole.  The remaining quantitative issue is
an ensemble-uniform lower tail for the two-dimensional affine-alias gap and the static tangent gap,
not a minimum many-body level spacing.

### Proof

The variables `a` and `beta mod 2pi` range over a compact set, so the infimum defining `chi` is
attained.  If it were zero, equality of the two unitaries would give

\[
 (a-t)(E_j-E_1)\in2\pi\mathbb Z\qquad(2\le j\le D).
\]

Condition `(5a)` forces `a=t`, while the defining range of `a` and `|t|W_H>=2pi` make that
impossible.  Hence `chi>0`.

Now suppose such a `K_0` exists.  Theorem C.1 gives an `A=aH+bI in S_H` with

\[
 \|K_0-A\|_{\rm HS}\le C_{H,\eta}\varepsilon.
\]

The first bound on `epsilon` makes this at most `eta/4`.  Weyl's spectral-diameter inequality then
gives

\[
 |a|W_H=\operatorname{diam}(\operatorname{spec}A)
 \le\operatorname{diam}(\operatorname{spec}K_0)
    +2\|K_0-A\|_{\rm op}
 \le2\pi-\eta/2.
\]

The Hermitian exponential is operator-Lipschitz with unit constant along a line segment, so,
after absorbing `phi` into the scalar `b`,

\[
 \chi_{H,t,\eta}
 \le\|e^{-iA}-e^{i\phi}U_H(t)\|_{\rm op}
 \le(1+C_{H,\eta})\varepsilon.
\]

The second bound on `epsilon` contradicts this inequality. `square`

## 4. Approximate local logarithms remain near the physical direction

Define the finite-time local commutator gap

\[
 \alpha_H(t)=inf\{\|[U_H(t),A]\|_{\rm HS}:
 A\in\mathcal L\cap\mathcal S_H^\perp,\ \|A\|_{\rm HS}=1\}.    \tag{28}
\]

Under `(4)` and phase simplicity `(7)`, `alpha_H(t)>0`.

### Theorem D -- approximate local-logarithm direction law

Let `(4)` and `(7)` hold.  If `K_0 in L` is Hermitian and

\[
 \|e^{-iK_0}-e^{i\phi}U_H(t)\|_{\rm op}\le\varepsilon,           \tag{29}
\]

then

\[
 \boxed{
 \operatorname{dist}_{\rm HS}(K_0,\mathcal S_H)
 \le {2\varepsilon\over\alpha_H(t)}
      \operatorname{dist}_{\rm HS}(K_0,\mathbb RI).}             \tag{30}
\]

Thus any norm-controlled approximate logarithm in the local shell is forced toward the physical
time line.  A useful many-body conclusion requires a lower tail for `alpha_H(t)` and a norm
normalization for `K_0`; the theorem does not hide either input.

### Proof

Write `K_0=K_parallel+A` with `K_parallel in S_H` and
`A in L intersect S_H^perp`.  Since `U_H(t)` commutes with `S_H`,

\[
 [U_H(t),K_0]=[U_H(t),A].                                      \tag{31}
\]

Put `V=e^{-iK_0}`.  Since `[V,K_0]=0`, equation `(29)` gives, for every real `c`,

\[
 \begin{aligned}
 \alpha_H(t)\|A\|_{\rm HS}
 &\le\|[U_H(t),A]\|_{\rm HS}\\
 &=\|[U_H(t)-e^{-i\phi}V,K_0]\|_{\rm HS}\\
 &=\|[U_H(t)-e^{-i\phi}V,K_0-cI]\|_{\rm HS}\\
 &\le2\varepsilon\|K_0-cI\|_{\rm HS}.
 \end{aligned}                                                   \tag{32}
\]

Since `||A||` is the distance to `S_H`, infimizing over `c` gives `(30)`. `square`

The 2026 long-time Hamiltonian-learning theorem of Cedillo Vayson de Pradenne--Cotler--Huang
proves inverse-polynomial lower bounds of the form `(28)` with high probability for broad random
local ensembles and sampled long times.  That external theorem strongly overlaps the
**approximate conserved-direction** interpretation of `(30)`.  It does not state Theorems A--C
(including the collision-complete subwinding dichotomy) or
the address filtration below.  No novelty is assigned here to generic local identifiability alone.

## 5. Tangent rigidity does not control finite holonomy

Let `P_H:Herm(K)->C_H` be Hilbert--Schmidt projection onto the full spectral centralizer

\[
 \mathcal C_H=\{A:[H,A]=0\}.                                    \tag{33}
\]

### Proposition E -- exact second-order vertical curvature

For Hermitian `A,B`, the second-order centralizer generator of `(1)` is

\[
 \boxed{\Omega_H(A,B)=P_H(-i[A,B]).}                            \tag{34}
\]

In the energy eigenbasis,

\[
 \langle e_j,\Omega_H(A,B)e_j\rangle
 =-i\sum_k(A_{jk}B_{kj}-B_{jk}A_{kj}).                          \tag{35}
\]

There are horizontal controls with `P_H(A)=P_H(B)=0` but
`Omega_H(A,B)!=0`.  In fact, with unrestricted horizontal matrix controls, the values `(34)` span
the entire traceless centralizer.

### Proof

Set `X=-iA`, `Y=-iB`.  Multiplying the four norm-convergent exponential Taylor expansions through
order two gives

\[
 e^{\varepsilon X}e^{\varepsilon Y}
 e^{-\varepsilon X}e^{-\varepsilon Y}
 =I+\varepsilon^2[X,Y]+O(\varepsilon^3)
 =I-\varepsilon^2[A,B]+O(\varepsilon^3).                        \tag{36}
\]

The Hermitian effective generator is `-i[A,B]`, and projecting it gives `(34)` and `(35)`.

For `j>1`, let

\[
 X_{1j}=|1\rangle\langle j|+|j\rangle\langle1|,
 \qquad
 Y_{1j}=-i|1\rangle\langle j|+i|j\rangle\langle1|.             \tag{37}
\]

Both have zero diagonal, while `-i[X_(1j),Y_(1j)]` is a nonzero scalar multiple of
`P_1-P_j`.  These differences span the traceless diagonal matrices. `square`

This kills any proposed theorem saying that vertical endpoint phase is bounded by the integral of
instantaneous vertical projection.  Curvature creates vertical motion from a completely horizontal
loop.  The mechanism is standard in holonomic control and is recorded here as a no-go, not as a
novelty claim.

## 6. The finite Lie-word address filtration

Let `m=dim_R L`.  Let `Lie_k(L)` be the span of all Hermitian nested commutator words with exactly
`k` leaves in `L`; factors of `i` are inserted so every evaluated word is Hermitian.  Define the
order-`p` spectral address space

\[
 \mathcal A_p(H,\mathcal L)
 =q_H P_H\left(\sum_{k=1}^p\operatorname{Lie}_k(\mathcal L)\right)
 \subset\mathcal C_H/\mathbb RI,                               \tag{38}
\]

where `q_H` is the quotient by scalar operators.

This definition is external to circuit complexity.  It records which projective spectral phases
can occur in a Magnus/Baker--Campbell--Hausdorff logarithm through commutator order `p`.
Because `P_H` is applied after forming Lie words, it is an over-approximation to realizable
vertical holonomy.  It becomes a necessary endpoint address space when the transverse logarithmic
jet cancels through the retained order; it is not itself a controllability theorem.

### Theorem F -- universal finite-order address-capacity bound

For every `H,L,p`,

\[
 \boxed{
 \dim\mathcal A_p(H,\mathcal L)
 \le\sum_{k=1}^p m^k.}                                          \tag{39}
\]

Every order-`p` Magnus or BCH logarithm assembled from controls in `L` has its centralizer
component in `A_p(H,L)` through that order.

### Proof

The homogeneous degree-`k` part of the free Lie algebra on the vector space `L` is a quotient of
the tensor power `L^(tensor k)`.  Its dimension is therefore at most `m^k`.  Evaluation as matrix
commutators, summation over `k<=p`, orthogonal projection `P_H`, and the scalar quotient cannot
increase dimension, proving `(39)`.

The Magnus and BCH expansions are universal Lie series: every homogeneous term of degree `k` is a
linear combination of evaluated `k`-leaf Lie words.  Projecting the truncation through order `p`
therefore lands in `(38)`. `square`

The theorem is only an **order** obstruction.  A fixed finite gate word has an infinite BCH series,
and a large excursion need not be controlled by its low-order truncation.  Equation `(39)` is not
a circuit-depth lower bound.

## 7. Most completed phases escape every fixed finite-action address order

Identify the projective centralizer with `R^(D-1)` by anchored diagonal differences:

\[
 q_H\!\left(\sum_j a_jP_j\right)
 =(a_2-a_1,\ldots,a_D-a_1).                                    \tag{40}
\]

Let `pi_d:R^d->T^d` be reduction modulo `2pi Z^d`.  Define the canonical projective folded phase

\[
 \Theta_H(t)
 =\bigl(\operatorname{wr}(t(E_2-E_1)),\ldots,
        \operatorname{wr}(t(E_D-E_1))\bigr)
 \in(-\pi,\pi]^{D-1}.                                           \tag{41}
\]

It is the bounded anchored logarithm of the projective endpoint.

A raw linear address space is not enough.  Because it contains the physical direction `H`, its
image modulo `2pi` can be dense in the whole phase torus even when it is one-dimensional.  This is
the same irrational winding responsible for recurrence.  Action must therefore be retained.

For `B<infinity`, define the order-`p`, action-`B` address set

\[
 \operatorname{Addr}_{p,B}(H,\mathcal L)
 =\pi_d\bigl(S_p\cap\overline B_{\mathbb R^d}(0,B)\bigr)
 \subset\mathbb T^d.                                               \tag{42}
\]

This is the set of projective spectral phases having an order-`p` centralizer representative of
Euclidean spectral action at most `B`.  It is compact.  The unwrapped physical representative
`tH` belongs to the first-order space but exits every fixed action ball as `|t|` grows.

### Theorem G -- finite-action completed-time addressability law

Assume maximal projective rank `(5)`, put `d=D-1`, and identify
`A_p(H,L)` with its linear image `S_p subset R^d` under `(40)`.  Put
`k_p=dim S_p`.  If

\[
 k_p<d,                                                            \tag{43}
\]

then for every finite `B`,

\[
\boxed{
 \operatorname{dens}\{t:\pi_d(\Theta_H(t))
   \in\operatorname{Addr}_{p,B}(H,\mathcal L)\}=0.}              \tag{44}
\]

More quantitatively, equip the flat torus with its quotient Euclidean metric.  For
`0<epsilon<=pi/2`,

\[
\boxed{
 \limsup_{T\to\infty}{1\over2T}
 \operatorname{Leb}\{t\in[-T,T]:
   \operatorname{dist}_{\mathbb T^d}
   (\pi_d(\Theta_H(t)),\operatorname{Addr}_{p,B})
   \le\varepsilon\}
 \le
 \left(1+{2B\over\varepsilon}\right)^{k_p}
 {v_d(2\varepsilon)^d\over(2\pi)^d},}                            \tag{45}
\]

where `v_d` is the volume of the Euclidean unit `d`-ball.  The right side may always be truncated
at one.  Thus exact finite-action addressability has zero completed-time density, while its robust
tube has an explicit entropy--codimension bound.

### Proof

Condition `(5)` says that the frequency vector

\[
 (E_2-E_1,\ldots,E_D-E_1)                                      \tag{46}
\]

has no nonzero integer annihilator.  Kronecker--Weyl therefore makes its continuous linear flow
uniquely ergodic on the projective torus `T^d`.  The half-open cell in `(41)` is a fundamental
domain.

The Euclidean `k_p`-ball `S_p intersect closedBall(0,B)` has an `epsilon`-net of size at most

\[
 \left(1+{2B\over\varepsilon}\right)^{k_p}.                       \tag{47}
\]

The quotient map `pi_d` is one-Lipschitz, so the same points form an `epsilon`-net of
`Addr_(p,B)`.  Its closed `epsilon`-tube is therefore covered by the same number of flat-torus
balls of radius `2epsilon`.  Since `2epsilon<=pi`, each such ball has normalized Haar volume at
most

\[
 {v_d(2\varepsilon)^d\over(2\pi)^d}.                              \tag{48}
\]

This proves the Haar-volume bound in `(45)`.  The set is compact.  Unique ergodicity and the
closed-set half of Portmanteau therefore give the time-frequency upper bound `(45)`.

Because `k_p<d`, the compact Lipschitz image `Addr_(p,B)` has zero `d`-dimensional Haar measure.
Applying the same closed-set bound directly to it proves `(44)`. `square`

### Corollary H -- ordinary path-local chains have a growing address-order barrier

For the traceless one-site plus nearest-neighbour two-site qubit shell,

\[
 m=3n+9(n-1)=12n-9,
 \qquad d=2^n-1.                                                 \tag{49}
\]

For every `p` satisfying

\[
 \sum_{k=1}^p(12n-9)^k<2^n-1,                                   \tag{50}
\]

almost every completed time lies outside every fixed finite-action order-`p` address set, with the
explicit robust bound `(45)`.  Consequently an address filtration capable even of spanning the
whole projective phase vector space must have

\[
 p=\Omega(n/\log n).                                              \tag{51}
\]

Conditions `(4)` and `(5)` hold simultaneously on a full-measure subset of the ordinary path
shell: the first parent supplies generic maximal projective rank, and the second parent supplies
centralizer rigidity off explicit determinant loci.

Equation `(51)` is not an exponential circuit lower bound.  It proves that no fixed-order,
finite-action perturbative holonomy model can be the missing universal shortcut mechanism as
system size grows.

## 8. Full-scale circuit hardness with an identifiable local parent

The locality--action law composes exactly with the completed-time Choi plateau already proved in
`../3-formalized/universal-static-choi-complexity-plateau.md`.

Fix `0<delta<1/2`, a finite inverse-closed local gate alphabet acting on the doubled Choi register,
with at most `M>=2` labelled choices per step, and define

\[
 \eta_\delta=1-\sqrt{1-4\delta^2},\qquad
 B_D(\delta)=De^{D/2}
 \left({\pi\eta_\delta\over2}\right)^{(D-1)/2}.                  \tag{52}
\]

Let `Phi_H(t)` be the normalized Choi state of `U_H(t)` in the doubled system, and let
`C_delta` be its trace-distance circuit complexity for this alphabet.

### Theorem I -- hard folded phase / visible local-parent coexistence

For almost every ordinary open-chain Hamiltonian in the shell of the tangent-rigidity parent,
and every integer `s>=0`,

\[
 \boxed{
 \liminf_{T\to\infty}{1\over2T}\operatorname{Leb}
 \left\{\begin{array}{l|l}
 t\in[-T,T]&
 C_\delta(\Phi_H(t))>s,\\
 &U_H(t)\text{ has simple phase spectrum},\\
 &|t|W_H\ge2\pi
 \end{array}\right\}
 \ge1-M^{s+1}B_D(\delta).}                                      \tag{53}
\]

At every time counted on the left,

\[
 \boxed{
 \begin{aligned}
 \mathcal L\cap\{A:[U_H(t),A]=0\}&=\operatorname{span}\{I,H\},\\
 K_0\in\mathcal L,\ e^{-iK_0}=e^{i\phi}U_H(t)
 &\Longrightarrow K_0=tH+(2\pi m-\phi)I,\\
 F_H(t)&\notin\mathcal L.
 \end{aligned}}                                                  \tag{54}
\]

Thus a full-scale circuit-hard phase can retain an exactly identifiable local parent even though
its bounded canonical generator is necessarily nonlocal.

### Proof

The two generic parent theorems have conull good sets in the same finite-dimensional path-local
coefficient shell: maximal projective rank `(5)` and local centralizer rigidity `(4)`.  Their
intersection is conull.

For every retained `H`, the completed-time Choi plateau gives

\[
 \limsup_{T\to\infty}{1\over2T}
 \operatorname{Leb}\{t\in[-T,T]:C_\delta(\Phi_H(t))\le s\}
 \le M^{s+1}B_D(\delta).                                        \tag{55}
\]

The phase-collision set `(7)` is countable, and the interval
`|t|W_H<2pi` is bounded.  Removing both changes no asymptotic density.  Complementing `(55)`
therefore proves `(53)`.

At a phase-simple time, any local observable commuting with `U_H(t)` also commutes with `H`; `(4)`
gives the first line of `(54)`.  Theorem A gives the second line, and Theorem B plus
`|t|W_H>=2pi` gives the third. `square`

For any fixed `delta` with the plateau exponent positive, choosing
`s=Theta(D/log M)` below the explicit entropy threshold makes the right side of `(53)`
`1-exp(-Omega(D))`.  This is a completed-time full-scale plateau theorem.  It gives no first hard
time and no linear ramp.

## 9. Conjecturing and falsification ledger

### C0 -- tangent rigidity implies finite centralizer undistortion

**Verdict:** `[FALSIFIED]` by Proposition E.  Horizontal commutator loops create vertical phase at
second order.  This is the same obstruction exploited by holonomic quantum computation.

### C1 -- a bounded effective logarithm can remain two-local after many windings

**Verdict:** `[FALSIFIED GENERICALLY AND CLASSIFIED]` by Theorems A--C.  Locality and bounded
phase action separate at `|t|W_H>=2pi`.  Away from phase collisions every exact local logarithm
keeps diameter `|t|W_H`; at collisions every nonphysical local exception has diameter at least
`2pi`.  The folded logarithm is quantitatively separated from the local shell by its non-affine
branch ledger.

### C2 -- unrestricted finite holonomy is controlled by the local tangent line

**Verdict:** `[FALSIFIED]`.  Full horizontal matrix controls generate every traceless centralizer
direction through curvature, even though their first-order vertical projection vanishes.

### C3 -- raw address dimension controls phase coverage modulo `2pi`

**Verdict:** `[FALSIFIED]`.  A one-dimensional line of irrational slope has dense image in a
higher-dimensional torus.  In particular, the physical line `tH` already winds densely when the
spectrum has maximal projective rank.  Dimension controls phase coverage only after action is
bounded.

### C4 -- fixed commutator order at finite action can address a generic many-body phase

**Verdict:** `[FALSIFIED IN COMPLETED TIME]` by Theorems F--G.  At fixed local-shell dimension
`m=poly(n)`, the order-`p` address space has dimension at most `sum_(k<=p)m^k`; before
`p=Omega(n/log n)`, every finite-action piece occupies zero measure in the `2^n-1` dimensional
projective phase torus and obeys the robust tube bound `(45)`.

### C5 -- phase collisions reopen arbitrarily cheap local folding

**Verdict:** `[FALSIFIED BELOW A SHARP THRESHOLD]` by Theorem A.1.  A Hermitian logarithm with
spectral diameter below `2pi` is scalar on every eigenspace of its exponential, even when that
exponential is degenerate.  Local-centralizer rigidity and only two irrational gaps then force the
physical logarithm.  Theorem C.1 and Corollary C.2 preserve this conclusion for approximate tubes
with a fixed branch margin.  The `2pi` threshold is sharp by the rank-one projector example.

The unresolved probabilistic problem is a dimension-useful lower tail for `gamma_H` and the
projective affine-alias gap `chi_(H,t,eta)` on the ordinary local shell.  Pointwise positivity is
now proved; no uniform Diophantine margin is claimed.

### Strongest positive survivor

The finite-holonomy problem is not a scalar bandwidth problem.  It is a **spectral addressability
problem**:

> Long evolution creates a bounded but nonlocal folded branch ledger.  A shortcut must synthesize
> that ledger by transverse local-control holonomy.  Tangent rigidity removes alternative local
> clocks; action-truncated Lie-word address sets measure how rapidly transverse control can address
> new spectral phase directions without merely hiding elapsed time in an unbounded generator.

This is the first noncircular invariant in this route that simultaneously distinguishes

1. unwrapped physical time (`tH` remains local but grows in action);
2. phase folding (`F_H(t)` remains bounded but becomes nonlocal);
3. finite transverse holonomy (graded, action-truncated address sets `Addr_(p,B)`);
4. plateau phases (almost every completed phase escapes every fixed finite-action order); and
5. recurrence (the folded projective phase returns near the scalar origin, collapsing the required
   address).

It does not yet compare address order with arbitrary fixed-error circuit depth.

## 10. Relation to the Brown--Susskind frontier

The theorem removes two possible fake closures.

1. **Static fast forwarding by another local generator is absent generically.**  Theorem A says
   every exact local logarithm is physical time plus scalar away from phase collisions.  Theorem
   A.1 closes the collision loophole below one full winding, and Theorem B excludes the canonical
   folded logarithm at and beyond that winding.  Folding away elapsed time cannot be done inside
   the same local shell with subwinding spectral action.
2. **Tangent uniqueness is not enough.**  Proposition E identifies finite transverse holonomy as
   the only remaining exact local-control bypass.  Theorems F--G prove that its bounded-order,
   finite-action spectral address capacity is far below the many-body phase capacity.

The exact remaining theorem is stronger and narrower than the previous phrase “bound finite
holonomy”:

> Prove a fixed-error, nonperturbative undistortion theorem converting local circuit length into
> spectral address capacity for the folded branch ledger, uniformly over all circuit architectures
> and after one common recurrence excision.

Such a theorem would compose with the existing phase-bandwidth extraction and completed-time
plateau laws.  The present card does not supply that conversion and therefore does not prove the
Brown ramp.

## 11. Hostile audit

1. **No arbitrary-circuit lower bound.**  A finite word can leave the centralizer by a large amount,
   and its logarithm contains all BCH orders.  The order barrier `(51)` is not a gate-count bound.
2. **Phase collisions retain only a large-action loophole.**  Theorem A classifies every local
   logarithm off the countable collision set.  Theorem A.1 is collision-complete for spectral
   diameter below `2pi`; it does not classify possible nonphysical local logarithms of diameter at
   least `2pi`.  Theorem C.1 is the corresponding approximate statement only with a fixed margin
   `eta>0`; its constant must diverge as that margin closes.
3. **No uniform Diophantine margin.**  Maximal projective rank gives exact independence and
   equidistribution, not a finite-time rate or a uniform lower bound in `(23)`.
4. **Completed time is not prescribed Brown time.**  Theorem G is a long-time occupation law.  It
   does not prove that one specified time lies outside `Addr_(p,B)`.  The physical line `tH` enters
   `Addr_(1,B)` whenever `B` is allowed to grow to its unwrapped action, so the comparison must keep
   a shortcut action budget strictly below physical elapsed action.
5. **Projection is only a necessary perturbative address test.**  `P_H` of a truncated logarithm
   need not exponentiate independently of its transverse component.  The address space is an
   over-approximation for vertical jets, not a claim that every element is realizable or that every
   finite word is controlled by one truncation.
6. **No false novelty from holonomy.**  Group-commutator curvature, BCH/Magnus Lie words, and
   holonomic quantum control are established mathematics.  Proposition E is a killing mechanism,
   not claimed new science.
7. **Unbounded action defeats dimension.**  The full modular image of a proper linear address
   space may be dense.  Every use of Theorem G must retain the finite action budget `B`; dropping it
   re-admits physical time `tH` and makes the claim false.
8. **Hamiltonian learning collision.**  Long-time local-generator identifiability and an
   inverse-polynomial dynamical commutator gap are now in external literature.  The candidate new
   contribution is the exact locality--bounded-action fracture plus the completed-time graded
   spectral-address law, not uniqueness of a local conserved direction.
9. **Finite dimension.**  No thermodynamic limit, QFT, gravity, or black-hole geometry follows from
   these theorems.
10. **Control model.**  `A_p` controls perturbative Lie order.  Universality of a gate alphabet can
   make the full generated Lie algebra all of `su(D)`; `(39)` only delays, not forbids, full
   addressability.
11. **Novelty remains provisional.**  Uniqueness of a matrix logarithm inside a `2pi` branch
   strip and inverse divided-difference bounds for the exponential on a shorter arc are standard
   matrix analysis.  Targeted searches found those facts, Floquet branch-cut topology, Hamiltonian
   aliasing, holonomic control, local-conserved-observable learning, and symmetry-locality
   restrictions, but no theorem combining branch-strip uniqueness with local-centralizer rigidity
   and maximal projective rank to obtain the collision-complete dichotomy, nor the larger package
   `(9)`, `(19)`, `(23)`, and `(44)--(51)`.  Citation-graph and expert audit remain required before
   any novelty promotion.
12. **Lean deferred.**  Corpus refactoring is active.  No Lean source or process was touched.  These
   statements cannot enter a final claim set before exact formalization and axiom audit.

## 12. External boundary

- Tanimura's isoholonomic solution and Pachos--Zanardi holonomic quantum computation show that loop
  curvature can synthesize fibre unitaries.  They kill a tangent-only finite-holonomy argument.
- Cedillo Vayson de Pradenne--Cotler--Huang, *Learning Hamiltonians at Long Times*,
  `arXiv:2606.05690`, proves high-probability inverse-polynomial separation of the Hamiltonian from
  other local approximately conserved observables at sampled long times.
- Marvian, *Restrictions on realizable unitary operations imposed by symmetry and locality*,
  `arXiv:2003.05524`, studies which symmetry-preserving unitaries local symmetric controls can
  realize; sufficiently long general local evolution need not retain a simple finite-time locality
  restriction.
- Floquet effective-Hamiltonian literature treats matrix-logarithm branch cuts and anomalous
  locality/topology.  It does not, in the targeted audit, give the maximal-projective
  local-logarithm classification or the address-density law above.
- Principal-matrix-logarithm theory supplies the standard uniqueness of a logarithm whose spectrum
  lies in one branch strip, and elementary divided differences control the inverse exponential on
  a strictly shorter arc.  Theorems A.1 and C.1 use only those spectral mechanisms as input; their
  local-centralizer, tangent-gap, and projective-rank consequences are the candidate new
  composition.

## Gates

- [x] tangent-only finite-holonomy conjecture killed by explicit curvature loop
- [x] strongest positive locality--action survivor extracted
- [x] complete proofs of phase-simple exact, collision-complete exact/approximate subwinding,
  folded, quantitative, and finite-time approximate local-logarithm laws
- [x] finite Lie-word address filtration defined without circuit-complexity circularity
- [x] all-order dimension bound and completed-time escape theorem proved
- [x] ordinary path-shell corollary proved from existing parents
- [x] initial primary-source collision audit
- [ ] specialist priority audit of the combined locality--action/address theorem
- [ ] Lean formalization after shared refactor stabilizes
- [ ] nonperturbative circuit-length-to-address-capacity theorem

## Exact next move

For a fixed finite two-qubit gate alphabet, define a nonperturbative address profile from the
centralizer extraction `Z_H(W)` of every word endpoint, not from a BCH truncation.  Prove that one
gate changes a robust multiscale address functional by at most `poly(n)` while the folded ledger of
`U_H(t)` grows through `Omega(t/poly(n))` scales before plateau and collapses only on the common
recurrence set.  A successful functional must survive arbitrary transverse excursions, gate-word
architecture union, and fixed operator-norm error; otherwise it is only another perturbative
holonomy proxy.

## Lean progress -- the arithmetic core of Theorem A and Theorem A.1

`formal/GaloisForLFunctions/HTGeometry/LocalLogarithmRigidity.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| `(14)`: if `r` pushes every anchored gap into `2πℤ`, all gaps lie on one rational line | `span_le_of_commensurable` |
| **`(5a)` forces the physical slope**: two-gap irrationality makes `a = t` | `eq_zero_of_two_dim_span` |
| `(13)` with the physical slope: all winding integers coincide | `winding_const` |
| **`(10)`**: `diam spec(tH + cI) = \|t\| W_H`, so a scalar shift is invisible | `diam_affine` |
| its four affine ingredients | `sup'_affine_of_nonneg`, `inf'_affine_of_nonneg`, `sup'_affine_of_nonpos`, `inf'_affine_of_nonpos` |
| **the strict-diameter step of Theorem A.1**: same exponential and separation `< 2π` force equality | `eq_of_exp_eq_of_abs_sub_lt` |

`eq_zero_of_two_dim_span` is the exact content of the card's "if `a ≠ t`, every nonzero anchored gap
is an integer multiple of the same real number, so any two have rational ratio, contradicting `(5a)`":
the commensurability puts the whole gap family inside the rational line `ℚ·(2π/r)`, whose rational
dimension is at most one, so a family of rational dimension at least two forces `r = 0`.

`eq_of_exp_eq_of_abs_sub_lt` is the collision step: on an eigenspace of `V` the Hermitian
restriction of `K₀` has eigenvalues with equal exponentials, so they differ by a multiple of `2π`,
and a strict diameter below `2π` makes the multiple zero -- hence `K₀` is scalar there.

### The operator layer of Theorem A is closed too

| Card item | Declaration |
|---|---|
| two phases with the same exponential differ by `2πℤ` | `exists_int_of_expI_eq` |
| **`(7)` makes the orbit phases distinct** | `orbitPhase_injective` |
| **`(11) ⟹ [K₀,H] = 0`**: commuting with a resolved orbit kills the off-diagonal entries, hence commutes with `H` | `commutes_diagonal_of_commutes_orbit` |
| **`(13)`**: diagonalizing `(8)` gives the winding equations | `exists_int_winding` |
| **Theorem A, `(9)`**: `a = t` and `b = 2πm - φ` | `localLogarithm_eq_physical` |

The off-diagonal vanishing reuses the corpus commutant description
(`mem_commutantSubmodule_diagonal` in `HistogramCentralizerDimension`) rather than reproving it.
`localLogarithm_eq_physical` is the full arithmetic of Theorem A: `(13)` anchored at `j₁` gives
`(14)`, two-gap irrationality gives `a = t` through `eq_zero_of_two_dim_span`, and the residual
equation gives `b = 2πm - φ`.  With `diam_affine` this is `(9)` and `(10)`.

### Theorem A at the matrix level

| Card item | Declaration |
|---|---|
| the exponential of a diagonal matrix is the diagonal of the scalar exponentials | `exp_diagonal_entries` |
| **`(12)` in the eigenbasis**: an element of the centralizer line is the diagonal of `a Eⱼ + b` | `centralizerLine_diagonal` |
| **Theorem A as a matrix statement**: `(8)` in the eigenbasis forces `a = t` and `b = 2πm - φ` | `localLogarithm_eq_physical_matrix` |

Theorem A is therefore complete at the matrix level: `commutes_diagonal_of_commutes_orbit` supplies
`[K₀, H] = 0` from `(11)` and `(7)`; rigidity `(4)` -- a hypothesis of the card, not a claim --
supplies `(12)`, which `centralizerLine_diagonal` puts in diagonal form; and
`localLogarithm_eq_physical_matrix` closes `(9)`, with `diam_affine` giving `(10)`.

### Theorem A.1: the collision case

| Card item | Declaration |
|---|---|
| a spectrum of diameter below `2π` separates no two values by `2π` | `abs_sub_lt_of_diam_lt` |
| **scalarity on the phase fibres**: below diameter `2π`, equal exponentials force equal eigenvalues | `eigenvalue_eq_of_exp_eq_of_diam_lt` |
| **`[K₀,H] = 0` even at a phase collision** | `commutes_of_scalar_on_fiber` |

This is the card's collision argument verbatim.  In the eigenbasis of `K₀`, the exponential `V` is
the diagonal of `e^{-iκⱼ}`; `H` commuting with `V` kills every entry across distinct phases
(the corpus commutant description again), and `eigenvalue_eq_of_exp_eq_of_diam_lt` makes `κ` constant
across equal phases, so `[K₀, H] = 0` entry by entry regardless of collisions.  Feeding that into
`localLogarithm_eq_physical_matrix` gives the first alternative of Theorem A.1, and its negation is
the second.

### Section 3: the folded generator and its branch ledger

`formal/GaloisForLFunctions/HTGeometry/FoldedPhaseGenerator.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| the symmetric gap lands in `[-π, π)` | `phaseGap_zero_mem` |
| **`(15)`: the half-open representative `wr(x) ∈ (-π, π]`** | `phaseWrap`, `phaseWrap_mem` |
| **`(15)`: `x - wr(x) ∈ 2πℤ`, with the branch integer explicit** | `branchIndex`, `sub_phaseWrap_eq` |
| folding does not change the exponential | `exp_phaseWrap` |
| **`(16)`: the folded generator `F_H(t)` and the branch ledger `N_H(t)`** | `foldedGenerator`, `branchLedger` |
| **`(17)`: `F(t) = tH - 2π N(t)`** | `foldedGenerator_eq` |
| **`(17)`: `e^{-iF(t)} = U_H(t)`** | `exp_foldedGenerator` |
| **`(17)`: `spec F(t) ⊂ (-π, π]`** | `foldedGenerator_spec` |

The branch integer is explicit -- `branchIndex x = -round(-x/2π)` -- so nothing here rests on choice.
The window is half-open on the right, which is why the wrap is the negation of the symmetric gap:
`phaseGap` lands in `[-π, π)` because mathlib's `round` breaks ties upward.

### Theorem B: the locality fracture

Same module.

| Card item | Declaration |
|---|---|
| a spectrum inside the half-open window has diameter strictly below `2π` | `diam_lt_of_mem_window` |
| **the folded spectrum has diameter strictly below `2π`** | `foldedSpectrum_diam_lt` |
| **`(19)`**: if the folded generator is `tH + 2πm`, then `\|t\|W_H < 2π` | `abs_mul_width_lt_two_pi_of_physical` |

`(18)` is Theorem A applied to the folded generator: `F_H(t)` is diagonal, so it commutes with `H`;
rigidity `(4)` gives `F = aH + bI`; `exp_foldedGenerator` is exactly `(8)` at `φ = 0`; and
`localLogarithm_eq_physical_matrix` returns `a = t` and `b = 2πm`.
`abs_mul_width_lt_two_pi_of_physical` is then `(19)` in contrapositive form: the folded window forces
diameter `< 2π`, while `diam_affine` says a physical folded generator has diameter exactly `\|t\|W_H`,
so `\|t\|W_H ≥ 2π` is impossible -- after one full winding, bounded phase folding and two-locality
cannot coexist.

Note the strictness: values in `(-π, π]` differ by strictly less than `2π`, so the card's threshold
`\|t\|W_H ≥ 2π` is exactly the right one and needs no separate boundary argument.

### Theorem C: the quantitative fracture

`formal/GaloisForLFunctions/HTGeometry/DiagonalCommutatorWidth.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| the commutator against a diagonal is the entrywise product by the energy differences | `commutator_diagonal_apply` |
| **the Hilbert--Schmidt commutator bound of `(25)`**: `‖[H,X]‖²_HS ≤ W_H² ‖X‖²_HS` | `hsSqRe_commutator_diagonal_le` |
| every energy difference is bounded by the spectral width | `abs_sub_le_width` |
| **`(26)`, the triangle step**, which infimizes to `(22)` | `infDist_le_of_tangent` |

The commutator bound is proved exactly, entry by entry, so it needs neither operator-norm theory nor
the card's centring at `c = (max E + min E)/2`, and the constant is the width `W_H` itself rather
than `2‖H - cI‖`.  `infDist_le_of_tangent` is `(26)`: given `dist(K, S_H) ≤ (W_H/γ_H)‖K - F‖`, one
triangle inequality yields `dist(F, S_H) ≤ (1 + W_H/γ_H)‖F - K‖`, and taking the infimum over
`K ∈ L` is `(22)`.

### Theorem C completed: the tangent gap and the distance identity

Same module.

| Card item | Declaration |
|---|---|
| **`(21)` homogenized**: a gap on the unit sphere is a gap everywhere, so `γ_H‖A‖ ≤ ‖[H,A]‖` for every `A` | `gap_mul_norm_le` |
| distance to a subspace is translation invariant | `infDist_add_mem`, `infDist_add_mem_submodule` |
| distance to a subspace is absolutely homogeneous | `infDist_smul_submodule` |
| **`(27)`**: `dist(p - cN, S) = \|c\| dist(N, S)` for `p ∈ S`, hence `dist(F_H(t),S_H) = 2π dist(N_H(t),S_H)` | `infDist_folded` |

`gap_mul_norm_le` is the step that turns the unit-sphere definition `(21)` into the estimate
`dist(K,S_H) ≤ ‖[H,K]‖/γ_H` of `(25)`: on the orthogonal complement the distance *is* the norm, and
the commutator is homogeneous, so a gap on the sphere scales to every vector.  `infDist_folded`
applied with `p = tH ∈ S_H` and `c = 2π` is `(27)` exactly, because `(17)` writes
`F_H(t) = tH - 2π N_H(t)`.

### Theorem C.1: the subwinding chord comparison

`formal/GaloisForLFunctions/HTGeometry/SubwindingChordComparison.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| the exact chord `\|e^{-ix} - e^{-iy}\| = 2\|sin((x-y)/2)\|` | `norm_expI_sub_eq` |
| **the secant comparison** behind the monotonicity of `d ↦ d/(2 sin(d/2))` | `mul_sin_le_of_le_sub` |
| **Theorem C.1's eigenvalue comparison**: `\|κ_a - κ_b\| ≤ ((2π-η)/(2 sin(η/2))) \|e^{-iκ_a} - e^{-iκ_b}\|` | `abs_sub_le_chord` |

The card proves this by monotonicity of `d ↦ d/(2 sin(d/2))` on `[0,2π)`; the formal proof instead
uses the secant bound for the concave sine on `[0, π - η/2]` together with `sin(π - η/2) = sin(η/2)`,
which needs no derivative computation and gives the same constant.  The secant bound itself is the
corpus lemma `QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le`, reused rather than reproved.

### Theorem C.1: the commutator step

Same module.

| Card item | Declaration |
|---|---|
| the commutator against a diagonal, in the order `X D - D X` | `commutator_diagonal_apply'` |
| **the entrywise commutator comparison**: an entrywise bound between two diagonal families transfers to their commutator energies | `hsSqRe_commutator_comparison` |
| **left multiplication is bounded by the operator norm**: `‖E A‖²_HS ≤ ‖E‖²_op ‖A‖²_HS` | `hsSqRe_mul_left_le` |

Instantiating `hsSqRe_commutator_comparison` with `d j = κⱼ`, `e j = e^{-iκⱼ}` and the constant of
`abs_sub_le_chord` gives the card's
`‖[H,K₀]‖_HS ≤ ((2π-η)/(2 sin(η/2))) ‖[H, e^{-iK₀}]‖_HS` -- the comparison is entrywise, exactly as
the card describes, because both commutators against a diagonal are entrywise multipliers.
`hsSqRe_mul_left_le` is the ideal property in the form the last step needs, proved column by column
from the vector bound with no operator-norm theory.

### The operator-norm commutator bound: `(32)` of Theorem D and the last step of C.1

`formal/GaloisForLFunctions/HTGeometry/CommutatorOperatorBound.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| `‖A - B‖²_HS ≤ 2‖A‖²_HS + 2‖B‖²_HS` | `hsSqRe_sub_le` |
| Hilbert--Schmidt energy is conjugate-transpose invariant | `hsSqRe_conjTranspose` |
| right multiplication is bounded by the adjoint's operator norm | `hsSqRe_mul_right_le` |
| **the commutator bound** `‖[E,A]‖²_HS ≤ (2c)²‖A‖²_HS` for `‖E‖_op ≤ c` | `hsSqRe_commutator_le_of_opBound` |
| **`(31)`/`(32)`**: a commutator ignores scalars and commuting terms in either slot | `commutator_sub_smul_one`, `commutator_add_commuting`, `commutator_sub_commuting` |

These are the two remaining mechanisms of both Theorem C.1 and Theorem D.  In C.1 they give
`‖[H - cI, E]‖_HS ≤ 2‖H - cI‖_HS ε`; in D they give
`‖[U_H(t) - e^{-iφ}V, K₀ - cI]‖_HS ≤ 2ε‖K₀ - cI‖_HS`, which with `gap_mul_norm_le` applied to
`(28)` is `(30)`.  The commutator rewrites `(31)` -- dropping `K_parallel` because it commutes with
`U_H(t)`, dropping `e^{-iφ}V` because it commutes with `K₀`, and dropping `cI` because scalars
commute with everything -- are `commutator_add_commuting`, `commutator_sub_commuting` and
`commutator_sub_smul_one`.

The factor `2` comes out of `hsSqRe_sub_le` rather than a Minkowski inequality for the
Hilbert--Schmidt norm, which the corpus does not carry; the constant is the same.

### The assembled estimates of C.1 and D

Same module.

| Card item | Declaration |
|---|---|
| **Theorem D, `(30)`** in squared form: gap + rewrite + approximation force the transverse part below `(2ε/α)` times the distance to the scalars | `transverse_le_of_gap_and_approx` |
| **Theorem C.1's estimate**: tangent gap + chord comparison + approximation give the card's constant | `subwinding_transverse_le` |

Both are stated with the Hilbert--Schmidt energies rather than the norms, which is the same
inequality squared and avoids a square root at every step.  Each hypothesis is discharged by an
earlier lemma of this card's stack: the gap by `gap_mul_norm_le` applied to `(21)` or `(28)`, the
rewrite by `commutator_add_commuting`/`commutator_sub_commuting`/`commutator_sub_smul_one`, the chord
comparison by `hsSqRe_commutator_comparison` with `abs_sub_le_chord`, and the approximation by the
operator-norm hypothesis `(29)`.

### Theorem F: the address capacity bound

`formal/GaloisForLFunctions/HTGeometry/AddressCapacityBound.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| a finite supremum of subspaces has dimension at most the sum of the dimensions | `finrank_biSup_le` |
| **`(39)`**: the image of the first `p` layers under any linear map has dimension at most the sum of the layer bounds | `finrank_map_biSup_le` |
| its geometric form `∑_{k<p} m^{k+1}` | `finrank_map_biSup_le_geom` |

This is the whole of Theorem F once each layer's bound `dim Lie_k(L) ≤ m^k` is supplied: the two
steps the card names -- "summation over `k ≤ p`" and "orthogonal projection `P_H` and the scalar
quotient cannot increase dimension" -- are `finrank_biSup_le` and `Submodule.finrank_map_le`, and
`P_H` followed by `q_H` is a single linear map.

### The layer bound

Same module.

| Card item | Declaration |
|---|---|
| the span of a finite family has dimension at most the size of the family | `finrank_span_range_le` |
| **`dim Lie_k(L) ≤ m^k`** once the layer is spanned by the words indexed by `k`-tuples of basis labels | `finrank_span_le_pow` |

`finrank_span_le_pow` is stated for a family indexed by `Fin k → Fin m`, whose cardinality is `m^k`,
so it is the layer bound for any spanning family of that shape.  Feeding it into
`finrank_map_biSup_le_geom` gives `(39)` outright.

### The left-normed layers

`formal/GaloisForLFunctions/HTGeometry/LeftNormedBracketLayer.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| the span of brackets of two subspaces | `bracketSpan` |
| **bilinearity moves the span outside the bracket**: brackets of spans are spanned by brackets of generators | `bracketSpan_span_range` |
| the left-normed word on a generating family, and the degree-`k` layer | `leftNormed`, `bracketLayer` |
| **`dim Lie_k ≤ m^k` with an explicit spanning family** | `finrank_bracketLayer_le` |
| the zeroth layer is the span of the generators | `bracketLayer_zero` |

This replaces the card's "the homogeneous degree-`k` part of the free Lie algebra is a quotient of
`L^{⊗k}`" by a construction that needs no tensor power at all: the left-normed words on `m`
generators are indexed by `Fin (k+1) → Fin m`, so the layer they span has dimension at most
`m^{k+1}` by `finrank_span_range_le`, with no appeal to a free-Lie-algebra grading that mathlib does
not carry.

### The Jacobi reduction: Theorem F is closed

Same module.

| Card item | Declaration |
|---|---|
| bracketing a generator into a layer lands in the next layer | `bracketSpan_zero_le` |
| the left-normed word of a cons | `leftNormed_cons` |
| **the Jacobi reduction**: `⟦Lie_a, Lie_b⟧ ⊆ Lie_{a+b}`, so every bracket shape reduces to left-normed words | `bracketSpan_bracketLayer_le` |

`bracketSpan_bracketLayer_le` is proved by induction on the first degree using the Leibniz form of
Jacobi, `B x (B A Y) = B (B x A) Y + B A (B x Y)`: the left-normed word of degree `a+1` is
`B x A`, and rewriting `B (B x A) Y = B x (B A Y) - B A (B x Y)` places both terms in the layer of
degree `a+b+2` by the inductive hypothesis at `b` and at `b+1`.

**Theorem F is therefore complete.**  Every bracket word with `k` leaves lies in the left-normed
layer of degree `k` by `bracketSpan_bracketLayer_le`, that layer has dimension at most `m^k` by
`finrank_bracketLayer_le`, and `finrank_map_biSup_le_geom` sums the layers and applies `P_H` and the
scalar quotient without increasing dimension.  The card's tensor-power argument is replaced
throughout by bilinearity and Jacobi, which mathlib does supply.

### Proposition E: vertical curvature from horizontal controls

`formal/GaloisForLFunctions/HTGeometry/VerticalCurvature.lean` (new, umbrella-wired, axiom-clean).

| Card item | Declaration |
|---|---|
| matrix-unit products, matching and mismatched inner index | `single_mul_single_same`, `single_mul_single_ne` |
| **the witnesses `(37)`** `X = \|p⟩⟨q\| + \|q⟩⟨p\|`, `Y = -i\|p⟩⟨q\| + i\|q⟩⟨p\|` | `curvX`, `curvY` |
| **both are horizontal**: every diagonal entry vanishes | `curvX_diag`, `curvY_diag` |
| **`-i[X,Y] = 2(P_p - P_q)`** | `curv_commutator` |
| hence the curvature is nonzero | `curv_commutator_ne_zero` |

This is the card's no-go: `P_H(X) = P_H(Y) = 0` because the diagonals vanish, yet the second-order
generator `-i[X,Y]` is a nonzero multiple of `P_p - P_q`.  A completely horizontal loop therefore
creates vertical motion, so no bound on endpoint vertical phase by the integral of instantaneous
vertical projection can hold.

**Proposition E is complete**: `diagonal_eq_sum_anchored` is the card's closing claim that the
curvature values span the traceless centralizer.  Every traceless diagonal `∑ aⱼPⱼ` is
`∑_{j≠p} (-aⱼ)(P_p - P_j)`, the coefficient identity being exactly `∑ aⱼ = 0`.  Since
`curv_commutator` realizes each `P_p - P_j` as `-i[X,Y]/2` with `X, Y` horizontal, the curvature
values of unrestricted horizontal controls do span the whole traceless centralizer.

### Theorem G: the entropy factor of `(45)`

`formal/GaloisForLFunctions/HTGeometry/EuclideanPackingBound.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| Euclidean ball volume in dimension `k`, and its constant | `euclideanBallConst`, `volume_ball_eq`, `euclideanBallConst_ne_zero`, `euclideanBallConst_ne_top` |
| **the entropy factor `(1 + 2B/ε)^{k_p}` of `(45)`**: an `ε`-separated subset of a ball of radius `B` in `k` dimensions has at most that many points | `card_le_of_separated` |

The proof is the volumetric packing argument: the `ε/2`-balls around an `ε`-separated set are
disjoint and lie inside the ball of radius `B + ε/2`, and Euclidean ball volume is the `k`-th power
of the radius times a constant, which cancels.  The constant is exactly the card's, because the
enlarged radius is `B + ε/2` rather than `B + ε`.

### The codimension hypothesis of `(43)`

Same module.

| Card item | Declaration |
|---|---|
| **`(43)` in measure-theoretic form**: a subspace of deficient dimension is Lebesgue-null | `volume_submodule_eq_zero` |
| hence the action-bounded address set, sitting inside it, is null | `volume_subset_submodule_eq_zero` |

`k_p < d` is exactly the hypothesis that makes `S_p` a proper subspace, and mathlib's
`Measure.addHaar_submodule` then gives measure zero.  This is the input Kronecker--Weyl consumes:
the time-average of the indicator of a null closed set is zero.

### Theorem G's equidistribution input is already in the corpus

The corpus already carries the full multidimensional Kronecker--Weyl machinery, so nothing here
needs building:

| Card item | Existing declaration |
|---|---|
| **Weyl's criterion on `𝕋^d`**: a velocity vector pairing nontrivially with every nonzero integer vector makes the time average of every continuous function converge to its torus mean | `RHTower.deningerWeyl` (`RHTower/Deninger/DeningerWeylCriterion.lean`) |
| a character with nonzero frequency has vanishing flow mean | `RHTower.deningerFlowAverage_mFourier_tendsto` (`RHTower/Deninger/DeningerTorusFlow.lean`) |
| Kronecker density from a trivial annihilator | `RHTower.deningerKroneckerFlow_dense` (`RHTower/Deninger/DeningerKroneckerDense.lean`) |
| **symmetric-window unique ergodicity** of a rationally independent phase flow | `hasHaarTimeAverage_of_continuous` (`HTGeometry/InfiniteTorusEquidistribution.lean`) |
| its one-sided form | `hasHaarForwardAverage_of_continuous` (`HTGeometry/InfiniteTorusForwardDensity.lean`) |
| the symmetric character average and its exact `sinc` value | `symmetricPhaseAverage`, `symmetricPhaseAverage_eq_sinc` (`HTGeometry/SymmetricTimeAverageCharacterLaw.lean`) |
| its limit at a nonzero detuning | `symmetricPhaseAverage_tendsto_resonanceIndicator` (`HTGeometry/ReplicaCollisionExtremality.lean`) |

Condition `(5)` is exactly the hypothesis of `deningerWeyl`, and `flowAverage` in
`InfiniteTorusEquidistribution` is exactly the symmetric average `(2T)⁻¹∫_{-T}^{T}` that `(45)`
uses.

### Theorem G is already closed by the corpus

The whole density layer of Theorem G exists in the corpus; nothing needed building.

| Card item | Existing declaration |
|---|---|
| **`(44)`/`(45)`**: for a rationally independent frequency packet and any **closed** target, the completed-time upper density is at most the target's Haar measure | `rationallyIndependent_closedTarget_limsup_le_volume` (`HTGeometry/FiniteSpectralRecurrenceFrequencyLaw.lean`) |
| the uniformly-sampled clock law and its weak convergence | `finiteTorusPhaseProbabilityMeasure` (`HTGeometry/FiniteTorusPhaseEnsembleLaw.lean`), `finiteTorusPhaseProbabilityMeasure_tendsto_haar`, `finiteTorusPhaseProbabilityMeasure_tendsto_orbitClosureHaar` (`HTGeometry/CompletedObserverTimeTorus.lean`) |
| the fundamental box projects to the torus measure preservingly, so box-null sets are torus-null | `measurePreserving_torusProj` (`HTGeometry/CompletedTimeCaptureDensity.lean`) |
| a worked instance of the same density argument | `limsup_finiteTorusPhaseProbabilityMeasure_capture_le` (`HTGeometry/CompletedTimeCaptureDensity.lean`) |

`(44)` is `rationallyIndependent_closedTarget_limsup_le_volume` with `volume A = 0`, the nullity
coming from `volume_submodule_eq_zero` transported through `measurePreserving_torusProj`; `(45)` is
the same theorem with `volume A` bounded by the entropy factor `card_le_of_separated` times the
ball volume.

**Theorem G is therefore complete**, and with it every numbered result of the card.

### Correction to this ledger

Two modules I added for Theorem G -- a symmetric character average and a portmanteau-for-flows
wrapper -- duplicated `symmetricPhaseAverage` (`HTGeometry/SymmetricTimeAverageCharacterLaw.lean`)
and `rationallyIndependent_closedTarget_limsup_le_volume` respectively.  Both have been deleted and
unwired.  The corpus equidistribution stack (Deninger--Weyl, infinite-torus unique ergodicity,
completed-observer-time equidistribution, closed-target density) is complete and should be searched
before any further work in this area.

## Lean certificate

Every declaration below is in `GaloisForLFunctions.HTGeometry` (except where marked corpus-existing)
and depends only on `propext`, `Classical.choice`, `Quot.sound`.  Audited 23 declarations, all clean.

| Card item | Declaration | Module |
|---|---|---|
| `(11)` ⟹ `[K₀,H] = 0` under `(7)` | `orbitPhase_injective`, `commutes_diagonal_of_commutes_orbit` | `LocalLogarithmRigidity` |
| `(12)` in the eigenbasis | `centralizerLine_diagonal` | `LocalLogarithmRigidity` |
| `(13)` the winding equations | `exists_int_winding` | `LocalLogarithmRigidity` |
| `(14)` + `(5a)` ⟹ physical slope | `span_le_of_commensurable`, `eq_zero_of_two_dim_span`, `winding_const` | `LocalLogarithmRigidity` |
| **Theorem A, `(9)`** | `localLogarithm_eq_physical`, `localLogarithm_eq_physical_matrix` | `LocalLogarithmRigidity` |
| **`(10)`** | `diam_affine` (+ the four affine sup/inf lemmas) | `LocalLogarithmRigidity` |
| **Theorem A.1** | `eq_of_exp_eq_of_abs_sub_lt`, `abs_sub_lt_of_diam_lt`, `eigenvalue_eq_of_exp_eq_of_diam_lt`, `commutes_of_scalar_on_fiber` | `LocalLogarithmRigidity` |
| `(15)` half-open representative and branch integer | `phaseWrap`, `phaseWrap_mem`, `branchIndex`, `sub_phaseWrap_eq` | `FoldedPhaseGenerator` |
| `(16)`, `(17)` folded generator and ledger | `foldedGenerator`, `branchLedger`, `foldedGenerator_eq`, `exp_foldedGenerator`, `foldedGenerator_spec` | `FoldedPhaseGenerator` |
| **Theorem B, `(18)`/`(19)`** | `diam_lt_of_mem_window`, `foldedSpectrum_diam_lt`, `abs_mul_width_lt_two_pi_of_physical` | `FoldedPhaseGenerator` |
| `(21)` homogenized; `(25)` commutator bound | `gap_mul_norm_le`, `commutator_diagonal_apply`, `hsSqRe_commutator_diagonal_le`, `abs_sub_le_width` | `DiagonalCommutatorWidth` |
| `(26)` ⟹ `(22)`; `(27)` ⟹ `(23)` | `infDist_le_of_tangent`, `infDist_add_mem`, `infDist_smul_submodule`, `infDist_folded` | `DiagonalCommutatorWidth` |
| **Theorem C.1** chord comparison | `norm_expI_sub_eq`, `mul_sin_le_of_le_sub`, `abs_sub_le_chord` | `SubwindingChordComparison` |
| **Theorem C.1** commutator step | `commutator_diagonal_apply'`, `hsSqRe_commutator_comparison`, `hsSqRe_mul_left_le` | `SubwindingChordComparison` |
| `(32)` commutator identities and operator bound | `hsSqRe_sub_le`, `hsSqRe_conjTranspose`, `hsSqRe_mul_right_le`, `hsSqRe_commutator_le_of_opBound`, `commutator_sub_smul_one`, `commutator_add_commuting`, `commutator_sub_commuting` | `CommutatorOperatorBound` |
| **Theorem D, `(30)`**; **Theorem C.1 assembled** | `transverse_le_of_gap_and_approx`, `subwinding_transverse_le` | `CommutatorOperatorBound` |
| **`(35)`** commutator diagonal | `commutator_diag_apply` | `VerticalCurvature` |
| **Proposition E, `(37)`** | `curvX`, `curvY`, `curvX_diag`, `curvY_diag`, `curv_commutator`, `curv_commutator_ne_zero` | `VerticalCurvature` |
| **Proposition E** spanning claim | `diagonal_eq_sum_anchored` | `VerticalCurvature` |
| `(38)` layers; **Theorem F, `(39)`** | `finrank_biSup_le`, `finrank_map_biSup_le`, `finrank_map_biSup_le_geom`, `finrank_span_range_le`, `finrank_span_le_pow` | `AddressCapacityBound` |
| `dim Lie_k ≤ m^k` with explicit spanning family, and the Jacobi reduction | `bracketSpan`, `bracketSpan_span_range`, `leftNormed`, `bracketLayer`, `finrank_bracketLayer_le`, `bracketSpan_zero_le`, `bracketSpan_bracketLayer_le` | `LeftNormedBracketLayer` |
| **`(45)`** entropy factor; **`(43)`** codimension | `card_le_of_separated`, `volume_submodule_eq_zero`, `volume_subset_submodule_eq_zero` | `EuclideanPackingBound` |
| **Theorem G, `(44)`/`(45)`** density | `rationallyIndependent_closedTarget_limsup_le_volume` | corpus, `FiniteSpectralRecurrenceFrequencyLaw` |
| the clock law and its weak convergence | `finiteTorusPhaseProbabilityMeasure`, `finiteTorusPhaseProbabilityMeasure_tendsto_haar` | corpus, `FiniteTorusPhaseEnsembleLaw`, `CompletedObserverTimeTorus` |
| box-null ⟹ torus-null | `measurePreserving_torusProj` | corpus, `CompletedTimeCaptureDensity` |

### Deviations from the paper proof

- `(15)`'s branch integer is explicit (`-round(-x/2π)`), so nothing rests on choice.  The wrap is the
  negation of the symmetric gap because mathlib's `round` breaks ties upward.
- `(25)` is proved entrywise, so it needs no operator-norm theory and no centring at
  `c = (max E + min E)/2`; the constant is the width `W_H` itself rather than `2‖H - cI‖`.
- Theorem C.1's monotonicity of `d ↦ d/(2 sin(d/2))` is replaced by the secant bound for the concave
  sine on `[0, π - η/2]`, giving the same constant with no derivative computation.
- The factor `2` in `(32)` comes from `‖A-B‖² ≤ 2‖A‖² + 2‖B‖²` rather than a Minkowski inequality for
  the Hilbert--Schmidt norm, which the corpus does not carry.
- Theorem F's "the degree-`k` part is a quotient of `L^{⊗k}`" is replaced by the left-normed layers:
  words indexed by `Fin (k+1) → Fin m` span the layer by the Jacobi reduction, so the dimension bound
  is a cardinality count and no tensor power is needed.
- `(19)`'s threshold is exact: values in `(-π, π]` differ by strictly less than `2π`, so
  `|t|W_H ≥ 2π` is impossible with no separate boundary argument.
