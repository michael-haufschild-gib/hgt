# Spectral phase-folding locality and addressability law

- **ID:** `spectral-phase-folding-locality-addressability-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / finite-holonomy correction / spectral-addressability law
- **Parents:** `centralizer-phase-bandwidth-shortcut-extraction-law.md`,
  `path-local-centralizer-tangent-rigidity-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY PROVISIONAL] [LEAN DEFERRED]`
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
