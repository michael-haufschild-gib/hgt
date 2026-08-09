# Marked half-character duality, soldering, and cofinal diagonal-inverse obstruction

- **ID:** `clg-marked-half-character-duality-cofinal-diagonal-obstruction`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / CROSS-CORPUS CONSTITUTIVE LAW / COFINAL DIAGONAL NO-GO
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [HURWITZ/STOKES REALIZATIONS]`
  `[COMPACT-RECURRENCE ACTION CALIBRATION]`
  `[MARKED ROOT TORSOR] [CANONICAL DIAGONAL INVERSE FAILS COFINALLY] [NOT RH]`
  `[LEAN-FORMALIZED] [AXIOM-AUDITED] [UMBRELLA-BUILT]`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.MarkedHalfCharacterDualityLaw`,
  `GaloisForLFunctions.HTGeometry.MarkedHalfCharacterCompactActionLaw`,
  `GaloisForLFunctions.RHTower.MarkedHalfCharacterCofinalDiagonalInverseLaw`
- **Statement:** A marked half-character `u` with coarse holonomy `z=u^2` has exact even-curvature,
  odd-soldering, duality, and energy shadows. It realizes both Hurwitz branch increments and the
  arithmetic Gamma/paracyclic defect; its placewise reciprocal fails to define a morphism on the
  fixed all-prime `ell^1` quotient.

## Goal

Construct one coordinate-free local law with exact realizations in a non-RH hypertranscendental
family and the live arithmetic Stokes/Bockstein chart. Determine which data are intrinsic, which
require marking, and what unconditional new restriction this places on the missing source
comparison.

## 1. Strict Čech cocycles are not unframed Morita invariants

Let `U` be the unit groupoid on one point and `P` the pair groupoid on two points. They are Morita
equivalent. Use normalized constant coefficients `A=Z` and the chosen nonzero element `1 in A`.

\[
 Z^1(N\mathcal U;A)=0.
\tag{1}
\]

On `P`, take zero-cochain `theta(0)=0`, `theta(1)=1`. Its coboundary is the nonzero cocycle

\[
 (d\theta)(0\to1)=1,
 \qquad
 (d\theta)(1\to0)=-1.
\tag{2}
\]

Both first cohomology groups vanish. Hence strict `Z^1` changes under Morita-equivalent
presentations, while passing to `H^1` erases the exact symbol.

### Consequence 1.1

The strict-cocycle functor itself does not factor through unmarked Morita localization. In
particular, a construction that is required to reproduce the nonzero pair-groupoid cocycle cannot
be obtained solely from the unmarked Morita class. This does not rule out every transformation
into `Z^1`; constant or zero transformations remain possible.

Thus a source-sensitive transformation required to reproduce this strict representative,

\[
 \Theta\longrightarrow Z^1(N(q);E)
\]

cannot be canonically transported using only the unframed Morita class. Exact Hurwitz increments
and Gamma Bocksteins therefore require a marked atlas/local primitive or comparable descent
enhancement, not only the coarse quotient stack or its `H^1`.

## 2. Marked augmentation cocycle

Let `G` be a groupoid, `E` a linear left representation over a fixed commutative ring, and
`theta_x in E_x` a marked zero-cochain.
Define

\[
 \nabla_\theta(g)=\rho(g)\theta_{s(g)}-\theta_{t(g)}.
\tag{3}
\]

For composable `h:x->y`, `g:y->z`,

\[
 \boxed{
 \nabla_\theta(gh)=\rho(g)\nabla_\theta(h)+\nabla_\theta(g).}
\tag{4}
\]

Thus `nabla_theta` is a normalized twisted one-cocycle. Its sign is the negative of the
constant-coefficient coboundary convention used in `(2)`. Formula `(3)` is functor-natural under
equivalences carrying both `E` and `theta`, but not under unmarked Morita equivalence. Scaling or
reversing `theta` scales or reverses the cocycle, so source normalization is load-bearing.

#### Proof

Expand the right side:

\[
 \rho(g)(\rho(h)\theta_x-\theta_y)+(\rho(g)\theta_y-\theta_z)
 =\rho(gh)\theta_x-\theta_z.
\]

This is `(4)`. QED.

## 3. Duality-root Cartan theorem

Let `u in C^times`, put `z=u^2`, and define

\[
 S(u)=u-u^{-1},
 \qquad
 C(u)=u+u^{-1},
 \qquad
 \kappa(z)=z-1.
\tag{5}
\]

Let duality `J` send `u` to `u^{-1}` and `z` to `z^{-1}`.

### Theorem 3.1

One has the exact identities

\[
 \boxed{\kappa=uS},
\tag{6}
\]

\[
 \boxed{\kappa+zJ(\kappa)=0},
\tag{7}
\]

\[
 \boxed{-\kappa J(\kappa)=S^2},
\tag{8}
\]

and

\[
 \boxed{z-z^{-1}=CS=(1+z^{-1})\kappa}.
\tag{9}
\]

Equation `(6)` is the local soldering relation between even curvature and odd half-character.
Equation `(7)` is its duality-weighted Bianchi identity. Equation `(8)` is the reflection-paired
energy law; for positive real `u`, it is nonnegative and loses the orientation of `S`.

**Real-form boundary.** On the split real form `u=e^x in R_(>0)`, equation `(8)` is
`S^2=4sinh^2(x)>=0`, but the positive square root `u=sqrt(z)` globally trivializes the root cover.
On the compact recurrence form `u=e^(i theta)`, the root cover has winding holonomy, while
`S^2=-4sin^2(theta)<=0`; positive energy is instead `S^dagger S=|S|^2` and requires a chosen
dagger/polarization. Arithmetic positivity and compact root holonomy are different real-form
shadows, not simultaneous consequences of the Laurent identity.

#### Proof

Direct multiplication gives

\[
 u(u-u^{-1})=u^2-1=z-1,
\]

\[
 (z-1)+z(z^{-1}-1)=0,
\]

and

\[
 -(z-1)(z^{-1}-1)=z+z^{-1}-2=(u-u^{-1})^2.
\]

Finally `(u+u^{-1})(u-u^{-1})=u^2-u^{-2}` and
`(1+z^{-1})(z-1)=z-z^{-1}`. QED.

For the one-loop representation `rho(m)=z^m` and marked vector `theta`, the cocycle

\[
 \tau_{u,\theta}(m)=(z^m-1)\theta
\tag{10}
\]

obeys `tau(m+n)=tau(m)+z^m tau(n)` by `(4)`.

## 4. Root-torsor obstruction

The square map

\[
 r:\mathbb G_m\longrightarrow\mathbb G_m,
 \qquad u\longmapsto u^2
\tag{11}
\]

has no global continuous or algebraic section.

### Proof

Topologically, a section would induce an integer `n` on
`pi_1(C^times)=Z` satisfying `2n=1`, impossible. Algebraically, every unit of
`C[z,z^{-1}]` is `c z^n`; a unit squaring to `z` would again require `2n=1`. QED.

Under deck transformation `u -> -u`,

\[
 \kappa\longmapsto \kappa,
 \qquad
 S\longmapsto-S,
 \qquad
 C\longmapsto-C.
\tag{12}
\]

Thus `kappa` is an even coarse-holonomy shadow, while `S` and `C` live in the sign line associated
with the `mu_2` root torsor. The unrooted identity `(9)` compares scalar symbols, but an oriented
polarity or square-root action carrier genuinely requires the marked half-character.

## 5. Hurwitz realization

For a branch point `-n`, exponent `s_j`, and ladder index `k`, set

\[
 z_j=q_j=e^{-2\pi i s_j},
 \qquad
 u_j=e^{-\pi i s_j},
 \qquad
 \theta_{jkn}=c_{j,n}(a+n)^{-s_j-k}.
\tag{13}
\]

The actual branch deformation is

\[
 \boxed{
 F^{\mathcal T_nc}_{j,k}-F^c_{j,k}
 =(q_j-1)c_{j,n}(a+n)^{-s_j-k}
 =\kappa(z_j)\theta_{jkn}.}
\tag{14}
\]

Thus the Hurwitz branch increment is precisely the marked augmentation cocycle. The exponent
`s_j`, not coarse monodromy `q_j` alone, supplies the half-lift: shifting `s_j -> s_j+1` fixes
`q_j` and flips `u_j`.

Equation `(14)` does not imply Hurwitz hypertranscendence. The independent branch-history,
deletion-spanning, and Vandermonde theorem remains necessary.

## 6. Arithmetic Stokes/Bockstein realization

Let `s=rho` be a nontrivial Xi divisor point of multiplicity `r_rho`, put
`c_rho=Xi_C^(r_rho)(rho) != 0`, and assume the critical-strip parameter
`t=2 Re(rho)-1` lies in `(-1,1)`.

Use the corpus convention

\[
 t=2\operatorname{Re}\rho-1,
 \qquad
 z_p=p^t=\delta_p(\rho),
 \qquad
 u_p=p^{t/2},
\tag{15}
\]

and

\[
 d(p)=\frac p{(p+1)^2},
 \qquad F_t(p)=d(p)p^t.
\tag{16}
\]

The cofinal Gamma Bockstein coefficient is

\[
\begin{aligned}
 b_t(p)
 &=F_{-t}(p)-F_t(p)\\
 &=d(p)(z_p^{-1}-z_p)\\
 &=-d(p)C(u_p)S(u_p)\\
 &=-d(p)(1+z_p^{-1})\kappa(z_p).
\end{aligned}
\tag{17}
\]

The physical paracyclic residue is

\[
 \operatorname{Res}(D_{p,s}x)
 =(z_p-1)c_\rho\varepsilon(x)
 =\kappa(z_p)c_\rho\varepsilon(x).
\tag{18}
\]

Combining `(17)` and `(18)` gives the exact comparison

\[
 \boxed{
 b_t(p)c_\rho\varepsilon(x)
 =-d(p)(1+p^{-t})\operatorname{Res}(D_{p,\rho}x).}
\tag{19}
\]

Hence the Gamma Bockstein is not an independent cancelling current. It is a duality-weighted copy
of the same paracyclic curvature. At each finite prime the coefficient in `(19)` is nonzero.

For physical rank `M>0`, replacing `z` by `z^M` gives

\[
 \boxed{
 -\kappa(z^M)\kappa(z^{-M})
 =(u^M-u^{-M})^2
 =4\sinh^2\!\left(M(\operatorname{Re}\rho-\tfrac12)\log p\right),}
\tag{20}
\]

the exact unweighted numerator of the Stokes--Mertens local energy. Multiplication by `1/p` gives
the corpus summand. On the arithmetic positive-real form this is specifically the
reflection/coorientation quotient `t mapsto -t`, not loss of an unavailable positive square root.

## 7. Cofinal diagonal-inverse obstruction

Treat the following as an algebraic quotient; no Hausdorff quotient topology is asserted. Let

\[
 \mathcal S=\mathbb C^{\mathcal P},
 \qquad
 \mathcal I=\ell^1(\mathcal P),
\tag{21}
\]

and, for `|t|<1`, define

\[
 r_t(p)=d(p)(1+p^{-t}).
\tag{22}
\]

### Theorem 7.1

1. `r_t in ell^infinity(P)` and `r_t(p)->0`;
2. `r_t^(-1) notin ell^infinity(P)`;
3. diagonal multiplication `M_(r_t)` preserves `I` and descends to `S/I`;
4. `M_(r_t^(-1))` does not preserve `I` and does not descend to `S/I`.

Consequently the all-prime comparison

\[
 \boxed{[b_t]=-M_{r_t}[\kappa_t]}
\tag{23}
\]

is a legitimate quotient morphism, but its canonical placewise inverse is not a quotient
morphism.

#### Proof

One has `d(p) asymp p^(-1)`. If `t>=0`, then `r_t(p)=O(p^(-1))`. If `-1<t<0`, then
`r_t(p)=O(p^(-1-t))`. Hence `r_t` is bounded and tends to zero, so its reciprocal is unbounded.
A diagonal multiplier preserves every `ell^1` sequence exactly when its coefficients are bounded.
For the converse, choose primes `p_n` with `|m(p_n)|>=2^n` and set
`a(p_n)=m(p_n)^(-1)`, zero elsewhere. Then `a in ell^1` but `ma` has infinitely many unit
coordinates. Apply this to `m=r_t^(-1)`.

The induced quotient map is also noninjective. Choose distinct primes `p_n` with
`r_t(p_n)<=2^(-n)` and let `x(p_n)=1`, with all other coordinates zero. Then `x notin ell^1`, while
`r_t x in ell^1`. Hence `[x]!=0` but `M_(r_t)[x]=0`. On the other hand the induced map is
surjective because coordinatewise division by the nonzero sequence `r_t` is defined on all of
`S`. QED.

This is unconditional live-route leverage:

> Finite-place Bockstein--dagger equivalence loses its canonical diagonal inverse and becomes
> noninjective on the fixed all-prime algebraic quotient.

This does **not** prove categorical nonsplitting: the surjective linear map admits noncanonical
algebraic right splittings. It rules out an invertible quotient comparison implementing the forced
coefficient relation `(19)` by the canonical bounded placewise-diagonal multiplier on this fixed
algebraic quotient. A canonical inverse would need a different domain/topology or genuinely
non-diagonal source structure.

## 8. Relation-kernel interpretation

For the free history `Z ->> C_2`, kernel `2Z`, assume `tau` and `T` are invertible,
`tau^2=1`, `T^2=z id_V`, the scalar action is faithful, and the landing `L:S->V` is nonzero. Let
`Z` act on `Hom(S,V)` by

\[
 m\cdot L=T^mL\tau^{-m}.
\tag{24}
\]

Then

\[
 \nabla_L(1)\tau=TL-L\tau,
 \qquad
 \nabla_L(2)=T^2L-L\tau^2=(z-1)L.
\tag{25}
\]

Thus the dagger defect is an honest cocycle upstairs on free history and relation curvature after
quotienting by `2Z`. The coefficient action and coboundary descend to the ordinary `C_2` nerve when
`z=1`. Conversely, vanishing on the kernel relation gives `(z-1)L=0`, hence `z=1` under the stated
faithfulness and nonzero-landing hypotheses. In the literal physical landing this is the
RH-bearing condition. An ordinary downstairs Čech cocycle therefore cannot be the missing
intermediate construction.

## 9. Compact recurrence and lifted-action theorem

Let `T>0`, `n in Z`, and

\[
 z_n(t)=e^{2\pi i nt/T},\qquad u_n(t)=e^{\pi i nt/T},\qquad u_n^2=z_n.
\tag{26}
\]

Then

\[
 z_n(T)=z_n(0)=1,\qquad u_n(T)=(-1)^n u_n(0).
\tag{27}
\]

Thus the root sheet is winding parity and is recoverable from the full coarse path, though not
from its endpoint. Moreover

\[
 S(u_n)^2=-4\sin^2(\pi nt/T),\qquad
 S(u_n)^\dagger S(u_n)=4\sin^2(\pi nt/T),
\tag{28}
\]

and, for every `n!=0`,

\[
 \int_0^T |S(u_n)|^2dt=2T.
\tag{29}
\]

Hence this integrated positive energy determines neither winding magnitude nor parity. Define the
lifted logarithmic action

\[
 \mathcal A[u]=\int_0^T\left|\frac{\dot u}{u}\right|^2dt.
\tag{30}
\]

For every absolutely continuous `U(1)` loop `z` of winding `n` and every square-root lift `u`,

\[
 \boxed{\mathcal A[u]\ge \frac{\pi^2n^2}{T},}
\tag{31}
\]

with equality exactly for a constant-speed circular lift. Indeed path lifting gives
`integral_0^T dot(u)/u dt=pi i n`, and Cauchy--Schwarz proves `(31)`. In the framed two-level GHZ
fibre, using kinetic-action convention `A_FS=(1/2) integral g_FS(dot z,dot z)dt`, the minimum is

\[
 \mathcal A_{\mathrm{FS}}^{\min}(n;T)=\frac{\pi^2n^2}{2T}.
\tag{32}
\]

This is an exact recurrence chart: boundary/end-state observation closes, the root remembers only
parity, and a separately defined proper action retains full integer history. It is not a wormhole
theorem. A minimal operator model retaining the missing integer is the quantum rotor
`ell^2(Z)` with `N|k>=k|k>`, `V|k>=|k+1>`, `Gamma=e^(i pi N)`, and `H=N^2`; then
`V^*NV=N+1` and `Gamma V Gamma=-V`. Identifying these operators with horizon charge or wormhole
length requires a source-derived intertwiner and reconstruction theorem.

## 10. Hostile audit

1. **Unframed Morita-natural `Z^1`:** false by the pair-groupoid counterexample.
2. **Canonical logarithm or half-root from coarse holonomy:** false by the root-torsor theorem.
3. **Marked augmentation cocycle:** exact but depends on source-normalized marking.
4. **Duality-root Cartan factorization:** exact field type; `u=2` satisfies every identity off the
   unit locus, so it does not select `u=1`.
5. **Gamma Bockstein cancels physical dagger defect:** false; `(19)` makes it a nonzero scalar copy
   at every finite prime.
6. **Finite-place inverse globalizes:** false by Theorem 7.1.
7. **Hurwitz monodromy alone implies HT:** false; independent history realization is required.
8. **RH:** not proved. A source construction forcing a valid comparison to kill the retained
   physical class remains open and RH-bearing.

## 11. Field consequences and predictions

1. A CLG transgression carrying exact local symbols must be natural for **marked** equivalences,
   not unframed Morita equivalence.
2. Complex/Hurwitz holonomy has a `mu_2` half-character line. Arithmetic positive-real energy
   instead forgets reflection/coorientation `t mapsto -t`; identifying these requires an extra
   dagger/polarization theorem.
3. A closed coarse loop `z` of winding `n` lifts to `u(T)=(-1)^n u(0)`. This is finite `mu_2`
   holonomy, not unbounded open history. The full coarse path determines parity from winding;
   endpoint-only observation does not. Unbounded executed history requires the integer deck class
   and a separate coercive action.
4. A physical horizon interpretation must derive a root/sign edge line, its full integer
   deck-history refinement, a dagger selecting positive energy, and an independently defined
   length/action operator. Root parity or boundary positivity alone cannot identify wormhole
   length or interior time orientation.
5. The forced all-prime coefficient relation cannot be implemented as an invertible comparison by
   its canonical bounded diagonal multiplier on the fixed algebraic `ell^1` quotient. A canonical
   inverse needs different domain/topology or non-diagonal structure.

## 12. Literature boundary

- Morita-invariant groupoid cohomology does not canonically retain strict cocycle representatives:
  Tang--Villatoro, <https://arxiv.org/abs/2509.07285>.
- Crossed-module transgression is established parent theory:
  Cai, <https://arxiv.org/abs/2001.10233>.

The algebraic identities are elementary. The paper is a `[BRIDGE]`: its delta is the marked
strict-representative lesson, exact Hurwitz/Gamma coefficient dictionary, and noninjective
all-prime diagonal comparison. It is not a source transgression. No priority claim is required for
the field programme.

## Formalization gates

- [x] Morita/strict-cocycle no-go
- [x] marked augmentation law
- [x] root-torsor and duality identities
- [x] Hurwitz realization
- [x] arithmetic Gamma/paracyclic realization
- [x] all-prime canonical diagonal-inverse obstruction and noninjectivity theorem
- [x] hostile countermodels
- [x] exact Lean formalization of every proved assertion and hostile countermodel
- [x] direct per-file elaboration
- [x] targeted module builds and both umbrella builds
- [x] exhaustive theorem axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] forbidden-declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`

## Separate future source-realization program

The following are design targets, not proved claims of this card and not prerequisites for its
formalization:

- literal source construction of a singular or non-diagonal comparison;
- physical horizon/root-charge/integer-history realization.

## Lean audit

The three modules formalize the elementary Laurent-unit identities, categorical marked/unmarked
boundary, finite Hurwitz and arithmetic coefficient equations, compact-action rigidity, rotor-core
relations, and the exact prime-indexed `ell^1` multiplier theorem. Direct elaboration and targeted
builds pass. Both `HTGeometry` and `RHTower` umbrella builds pass. Exhaustive `#print axioms` output
for every theorem contains only standard foundations: `propext`, `Classical.choice`, and
`Quot.sound`. Repository-wide formal lint's forbidden-declaration scan passes; its reachability
phase remains blocked by unrelated pre-existing modules absent from umbrellas, recorded in the
campaign tracker.

## Log

- 2026-08-09 — proved after unframed Čech transgression failed Morita invariance and the
  half-character/root torsor exposed a shared Hurwitz--Stokes constitutive law.
- 2026-08-09 — every proved theorem and hostile boundary formalized unconditionally; direct,
  targeted, umbrella, forbidden-declaration, and exhaustive axiom audits passed; promoted to Stage 3.
