# Mixed-state coherence-graph recurrence-dimension law

- **ID:** `mixed-state-coherence-graph-recurrence-dimension-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM CANDIDATE / MIXED-STATE QUANTUM RECURRENCE /
  OBSERVER-DEPENDENT TIME DIMENSION
- **Source:** failure-driven extension of the projective weighted recurrence--rate-distortion law;
  Kotowski--Oszmaniec 2026 mixed-state and observable open problem; spectral-support and
  quantum-walk periodicity literature
- **Statement:** Quantum recurrence has two independent ranks.  The graphic rank of nonzero
  energy coherence is the observable phase capacity; the rational rank of the energy gaps on that
  graph is the dynamical clock rank.  Generic Hamiltonians saturate capacity, while symmetries and
  free-particle structure collapse the explored rank.  Neither entropy nor spectra alone determine
  either invariant.

## 2026-07-28 proved core and paper pivot

The paper now combines two dependency-closed results.

1. **Exact pure-state minimax law already present in the enlarged corpus.** For every finite
   spectral probability vector and every fidelity defect, the logarithm of the least deadline
   that works uniformly over all eigenphase packets lies within explicit errors linear in support
   size of a pivot-optimized reverse-water-filling entropy. The physical Floquet statement is
   `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich` in
   `RHTower/ProjectiveWeightedFloquetRecurrence.lean`. The exact separation from hard effective
   support is `operationalBinary_supportAndWaterEntropySeparation`.
2. **New mixed-state/observer extension proved in this cycle.** For every finite Hamiltonian,
   finite matrix-observer family and nonnegative observer weighting, total squared
   Hilbert--Schmidt displacement is exactly one coherence-weighted graph energy; exact return is
   componentwise phase locking; phase capacity is `vertices-components`; and at every integer
   resolution `Q` a positive recurrence occurs no later than
   `(Q+1)^(vertices-components)` with an explicit quadratic error. The modules are
   `RHTower/FiniteQuantumObserverCoherenceLaw.lean` and
   `RHTower/FiniteQuantumObserverGraphRecurrenceBound.lean`.
3. **Infinite boundary proved exactly.** For arbitrary pure-point spectral index types and
   arbitrary observer families, the displacement/phase-energy identity holds. Under nonnegative
   weights and summability, zero total displacement is equivalent to phase locking on every
   positively observed nonzero block. This is
   `RHTower/PurePointQuantumObserverCoherenceLaw.lean`. No universal continuous-spectrum
   recurrence claim is made.

All load-bearing declarations were axiom-audited on 2026-07-28 and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The manuscript centre is therefore no longer the graph rank
alone. It is the joined law:

```text
pure-state worst-spectrum recurrence information
  = pivot water entropy + explicit universal extensive error;

mixed-state and observable recurrence capacity
  = visible sectors - coherence components.
```

## 2026-07-28 Nature-facing synthesis

The superseded specialist manuscript in
`docs/drafts/pipeline/4-publication-ready/projective-quantum-recurrence-rate-distortion/`
was rewritten as **“An information law for quantum recurrence.”** The new
package contains:

1. a 2,584-word main Article with the two-sided projective water law as the
   headline result;
2. the exact finite observer-union phase-energy, graph-capacity, and
   graph-rank deadline theorems;
3. the arbitrary summable pure-point identity and zero law as the honest
   infinite boundary;
4. the equal-spectrum, equal-speed, equal-QFI qutrit separation;
5. an explicit multiqubit/observable-family experimental discriminator;
6. supplementary paper proofs, internal claim trace, current novelty audit,
   cover letter, and popular summary.

The manuscript and supplement do not mention formal verification and do not
count it toward novelty. Nature Portfolio's current policy was applied:
language models were removed from the author list, human accountability was
made explicit, and substantive generative-AI use was declared. Cosmology,
black holes, inflation, the Riemann zeta function, and an origin-of-time claim
were excluded because no proved bridge supports them.

Fresh literature audit through 2026-07-28 added Gupta--Short, *Physical Review
A* 114, 012208 (2026), which already proves simultaneous finite-system
recurrence including mixed states. This kills the broad novelty claim “mixed
states recur,” but does not collide with weight-adaptive water filling or the
observer-union graph rank. The closest frontier remains
Kotowski--Oszmaniec, accepted *Physical Review Letters* (23 June 2026), whose
conclusion explicitly identifies mixed-state and expectation-value bounds as
open and whose hard effective support does not contain the water law.

## Goal

Answer the quantitative mixed-state recurrence problem by identifying the exact finite-dimensional
carrier visible to unitary time evolution.  For a density operator `rho` and Hamiltonian spectral
projectors `(P_v)`, take as vertices all active sectors `v` with `P_v rho P_v!=0`, and put an edge
`{u,v}` between distinct energy sectors exactly when

```text
P_u rho P_v != 0.                                          (1)
```

For a positive density operator, an inactive diagonal block forces its whole block row and column
to vanish, so no coherence is lost.  Isolated active vertices retain stationary population and
matter under tensor products, although each contributes zero to single-system rank.  Let `G_rho`
be this basis-independent energy-coherence graph, let `c(G_rho)` be its number of connected
components, and set

```text
r_cap(rho,H)=|V(G_rho)|-c(G_rho).                          (2)
```

Choose any spanning forest and let `beta_f=E_child-E_parent` on its edges.  All other coherent
energy gaps are integer signed sums of these forest gaps, so the following ranks do not depend on
the forest:

```text
s_cont=dim_Q span_Q{beta_f},
s_disc=dim_Q span_Q{2pi,beta_f}-1.                         (3)
```

Here `0<=s_cont,s_disc<=r_cap`.  The phase capacity is `r_cap`; the physical continuous orbit
closure is an `s_cont`-torus and the identity component of the stroboscopic orbit closure is an
`s_disc`-torus.  Every fixed system has recurrence upper exponents

```text
stroboscopic exponent <=s_disc,
continuous-time exponent <=max(s_cont-1,0),                (3a)
```

and these exponents are equalities for almost every Hamiltonian within the corresponding rank
stratum.  Equivalently, generic energy gaps saturate `s_cont=s_disc=r_cap`.  Exceptional
Diophantine spectra may recur faster; no rank-only statement can exclude that.

The subtraction from `|V|` removes one unobservable phase on every coherence component.  The
continuous subtraction removes the one physical flow parameter.  A diagonal state has capacity
zero and is stationary.  A connected coherent state on `d` distinct generic energies has capacity
`d-1` and continuous recurrence exponent `d-2`.

## Universal observer extension

The state theorem is one instance of an operator theorem.  Let `(A_j)_(j in J)` be any finite
family of self-adjoint operators, with positive observation weights `lambda_j`, and define the
joint Heisenberg-return distance

```text
D_A(t)^2=sum_j lambda_j
  ||exp(itH)A_j exp(-itH)-A_j||_HS^2.                       (3a0)
```

Give `{u,v}` weight

```text
a_uv=2 sum_j lambda_j ||P_u A_j P_v||_HS^2.                 (3a1)
```

The same block orthogonality gives exactly

```text
D_A(t)^2=sum_(u<v) a_uv
  |exp(-itE_u)-exp(-itE_v)|^2.                              (3a2)
```

Consequently every theorem below applies unchanged to every collection of mixed states,
observables, or both.  The graph is the union of their nonzero energy-block graphs.  Adding a
probe can raise recurrence dimension only when one of its blocks joins two previously disconnected
components.  Thus the observable clock rank is

```text
r(A,H)=number of visible energy sectors
       -number of observationally disconnected components. (3a3)
```

The extension also holds for a countable family whenever
`sum_j lambda_j||A_j||_HS^2<infinity`; then the aggregate edge weights are summable.  Operator
recurrence implies simultaneous recurrence of all expectation values uniformly over input states,
because

```text
|Tr(sigma(A_j(t)-A_j))|
 <=||A_j(t)-A_j||_infinity
 <=||A_j(t)-A_j||_HS.                                      (3a4)
```

This supplies a deterministic, mixed-state and uniform-observable answer to the open extensions
identified by Kotowski--Oszmaniec (2026).  It does not claim a sharp exponent for one scalar
expectation value, where cancellations can accelerate return.

## Isospectral blindness theorem candidate

Fix a nondegenerate `d`-level Hamiltonian spectrum and a full-rank density spectrum with distinct
eigenvalues.  Keep both spectra fixed.  By changing only the relative eigenbasis of the Hamiltonian
and density operator, every graphic rank

```text
0,1,...,d-1                                                   (3a)
```

occurs.  For rank `r`, leave `d-r-1` density eigenvectors aligned with energy eigenvectors and
apply a generic unitary inside the remaining `(r+1)`-dimensional block.  Every off-diagonal entry
inside that block is nonzero off a finite union of proper real-analytic zero sets, so its coherence
graph is one complete component on `r+1` vertices plus isolated vertices and has graphic rank `r`.

Therefore no function of any combination of

```text
Hamiltonian spectrum,
density-operator spectrum,
von Neumann entropy,
all Renyi entropies,
purity,
matrix rank,
Hilbert-space dimension                                      (3b)
```

can determine recurrence dimension.  Those quantities are identical across the constructed
family.  The missing datum is relational: eigenvector coherence between the two spectral
decompositions.  This is the candidate headline result:

```text
spectra do not determine quantum time.                        (3c)
```

## Equal-speed isospectral separation theorem candidate

The stationary-versus-moving comparison is too easy to dismiss.  The stronger construction fixes
the initial speed as well.

Let `d>=2`, let `H=diag(E_0,...,E_(d-1))` with `E_0=0` and all `E_k!=0`, and choose
`0<b<1/d`.  Put `c=1-db` and, for `1<=r<=d-1`, define

```text
p_0^(r)(delta)=1-r delta,
p_k^(r)(delta)=delta       (1<=k<=r),
|psi_(r,delta)>=sum_(k=0)^r sqrt(p_k^(r)(delta)) |k>,
rho_(r,delta)=b I+c |psi_(r,delta)><psi_(r,delta)|.          (3d)
```

Every `rho_(r,delta)` is full rank with the same complete density spectrum

```text
{1-(d-1)b,b,...,b}.                                          (3e)
```

Its coherence graph is the complete graph on `{0,...,r}` plus isolated vertices, so its graphic
rank is `r`.  Its squared Hilbert--Schmidt speed is

```text
v_2(r,delta)^2
 =||[H,rho_(r,delta)]||_HS^2
 =2c^2 Var_(p^(r)(delta))(E)
 =2c^2[delta sum_(k=1)^r E_k^2
       -delta^2(sum_(k=1)^r E_k)^2].                         (3f)
```

Writing `a=1-(d-1)b` for the nondegenerate density eigenvalue, the unitary-family quantum Fisher
information is

```text
F_Q(rho_(r,delta),H)
 =4c^2/(a+b) Var_(p^(r)(delta))(E).                          (3f1)
```

Thus equal variance fixes both Hilbert--Schmidt speed and optimal local time-estimation precision.

For each `r`, the bracket in `(3f)` is strictly increasing from zero on a sufficiently short
common interval `(0,delta_*)`.  Choose

```text
0<s<min_r Var_(p^(r)(delta_*))(E).                            (3g)
```

The intermediate-value theorem gives one `delta_r` for every `r` with the same variance `s`.
Thus the `d-1` states `rho_(r,delta_r)` have the same Hamiltonian, complete state spectrum, every
unitarily invariant entropy, purity, rank, the same nonzero initial speed, and the same quantum
Fisher information for estimating elapsed time, while their graphic ranks are exactly

```text
1,2,...,d-1.                                                  (3h)
```

For a Hamiltonian in the full-measure set where every nested support has its generic
continuous-time recurrence exponent, the exponents are exactly

```text
0,1,...,d-2.                                                  (3i)
```

Consequently neither static spectral data nor the leading escape-time law determines even the
power of precision governing long-time return.  This is the nontrivial headline form:

```text
clocks with identical local precision can return arbitrarily different powers later. (3j)
```

### Explicit qutrit separation

The smallest nontrivial instance needs no almost-everywhere qualifier.  Fix

```text
H=diag(0,1,sqrt(2)).                                        (3j1)
```

No intermediate-value choice is needed.  Set

```text
delta=sqrt(2)-1,
p^(1)=(1-delta,delta,0),
p^(2)=(1-2delta,delta,delta).                              (3j1a)
```

Both are probability vectors because `0<delta<1/2`, and direct use of `sqrt(2)^2=2` gives

```text
Var_(p^(1))(0,1,sqrt(2))
 =delta-delta^2
 =3delta-(3+2sqrt(2))delta^2
 =Var_(p^(2))(0,1,sqrt(2)).                                (3j1b)
```

For the concrete choice `b=1/6`, `c=1/2`, the states

```text
rho_j=(1/6)I+(1/2)|psi_j><psi_j|,
|psi_j>=sum_k sqrt(p_k^(j))|k>                             (3j1c)
```

are full rank and have the same complete spectrum `{2/3,1/6,1/6}`, the same nonzero
Hilbert--Schmidt speed, and the same elapsed-time quantum Fisher information.

The `r=1` state uses only energies `0,1` and returns exactly with period `2pi`.  For the `r=2`
state, a return within `epsilon` forces

```text
dist(t,2pi Z)<=C epsilon,
dist(sqrt(2)t,2pi Z)<=C epsilon.                            (3j2)
```

Writing `t=2pi q+O(epsilon)` gives

```text
dist(q sqrt(2),Z)<=C' epsilon.                              (3j3)
```

For a nearest integer `p`, when the left side is below a fixed constant,

```text
1<=|2q^2-p^2|
  =|q sqrt(2)-p||q sqrt(2)+p|
  <=C''q |q sqrt(2)-p|.                                    (3j4)
```

Hence every return has `q>=c/epsilon`.  Ordinary one-dimensional Dirichlet approximation gives a
matching `q<=C/epsilon`.  Therefore

```text
tau_(r=1)(epsilon)=Theta(1),
tau_(r=2)(epsilon)=Theta(1/epsilon).                        (3j5)
```

This is an explicit, three-level, same-Hamiltonian, same-spectrum, same-speed falsifiable
separation of long-time recurrence.

There is an even cleaner stroboscopic form at the common interrogation times `t_n=2pi n`.
The first state returns exactly at every positive tick.  The second has trace distance

```text
D_2(n)
 =(1/2)sqrt(delta(1-delta))
   |exp(2pi i n sqrt(2))-1|.                               (3j6)
```

The elementary inequalities

```text
4 dist(n sqrt(2),Z) <= |exp(2pi i n sqrt(2))-1|,
dist(n sqrt(2),Z) >= 1/(4n)                                (3j7)
```

give `D_2(n)>=sqrt(delta(1-delta))/(8n)`.  One-dimensional Dirichlet approximation gives, for
every positive integer `Q`, some `1<=n<=Q` with

```text
D_2(n)<=pi sqrt(delta(1-delta))/Q.                          (3j8)
```

Thus the linear inverse-resolution law is both lower and upper, with explicit constants, on one
fixed experimentally natural sampling schedule.  Appending any number of stationary energy
levels embeds the identical pair into every Hilbert-space dimension `d>=3` without changing its
spectrum equality, QFI equality, or return laws.

## Many-body composition law candidate

Let `(H_A,rho_A)` and `(H_B,rho_B)` be independent systems.  Restrict to active energy sectors,
meaning sectors with nonzero diagonal density block.  Assume the sum energies `E_u+F_alpha` are
all distinct.  This collision-free condition holds outside a finite union of hyperplanes in the
pair of spectra.

For

```text
H_AB=H_A tensor I+I tensor H_B,
rho_AB=rho_A tensor rho_B,
```

the energy block between `(u,alpha)` and `(v,beta)` is

```text
(P_u rho_A P_v) tensor (Q_alpha rho_B Q_beta).              (3k)
```

It is nonzero exactly when both factors are nonzero.  Positivity of a density operator makes every
active diagonal block nonzero.  Hence the reflexive coherence relation is the direct product of
the two reflexive relations, equivalently the simple coherence graph is the strong graph product

```text
G_AB=G_A strong_product G_B.                                (3l)
```

If `n_A,n_B` are active vertex counts and `c_A,c_B` component counts, strong-product components
are exactly products of components.  Therefore

```text
n_AB=n_A n_B,
c_AB=c_A c_B,
r_AB=n_A n_B-c_A c_B.                                      (3m)
```

For connected coherence graphs this becomes

```text
r_cap,AB=(r_cap,A+1)(r_cap,B+1)-1.                          (3n)
```

This multiplication is a phase-capacity law, not by itself a physical-time exponent.  Let
`W_A,W_B` be the rational vector spaces spanned by the coherent energy gaps of the two factors.
Product energy differences are sums of factor differences, hence

```text
s_cont,AB=dim_Q(W_A+W_B)
         =s_cont,A+s_cont,B-dim_Q(W_A intersect W_B).       (3o)
```

Thus independent observable phase capacity compounds multiplicatively, while dynamically explored
clock rank grows only additively when the factor gap spaces are rationally independent.  Repeated
identical spectra share the same gap space and may add no new arithmetic rank at all.  This exact
capacity--exploration separation explains why a many-body state can occupy exponentially many
energy sectors while free or symmetric dynamics recur on a far lower-dimensional torus.
Energy-sum collisions require an additional spectral-sector quotient and are excluded from
`(3m)`--`(3o)` by the explicitly testable collision-free hypothesis.

## Exact phase model

Let `V` be finite and let `a_{uv}>0` on the edges of a simple graph `G=(V,E)`.  For
`z in T^V`, define

```text
Phi_a(z)=sum_{{u,v} in E} a_{uv}|z_u-z_v|^2.               (4)
```

Its zero set consists exactly of phase vectors constant on each connected component.  If
`r=|V|-c(G)`, a rooted spanning forest gives `r` independent edge-difference coordinates and a
Haar-preserving isomorphism

```text
T^V ~= T^c x T^r.                                          (5)
```

## Master coherence-volume law

Let `X_a` be the phase torus modulo the zero-distance subgroup of `(4)`, equipped with the
translation-invariant metric

```text
d_a(x,y)=sqrt(Phi_a(x/y)).
```

Use open recurrence balls and write

```text
mu_a(epsilon)=Haar_Xa{d_a(x,1)<epsilon},
H_a(epsilon)=-log mu_a(epsilon).                            (5a)
```

For the least deadline `T_a(epsilon)` such that every `x in X_a` has some
`1<=n<=T_a(epsilon)` with `d_a(x^n,1)<=epsilon`, the exact universal sandwich is

```text
H_a(epsilon)
 <=log T_a(epsilon)
 <=H_a(epsilon/4).                                         (5b)
```

Thus recurrence entropy is the negative logarithm of coherence-return volume, up to one fixed
change of resolution and with no additive finite-size slack.

This theorem does not require finite dimension.  It holds on every compact metrizable abelian
group with a translation-invariant metric.  For a countable coherence graph with
`sum_e a_e<infinity`, `(4)` converges uniformly on the product torus, its quotient is compact, and
every positive-radius ball has positive Haar measure.  Thus `(5b)` gives a finite deadline at every
finite resolution for every finite or countably infinite summable coherence network.

## Physical orbit-closure law

The full quotient `X_a` is observable phase capacity.  A fixed Hamiltonian need not explore all of
it.  Define

```text
K_cont=closure_Xa{[exp(-itE)]:t in R},
K_disc=closure_Xa{[exp(-inE)]:n in Z}.                      (5c)
```

In forest-edge coordinates the continuous frequency vector is `beta=(beta_f)`.  Character
duality for tori gives

```text
dim K_cont=dim_Q span_Q{beta_f}=s_cont,
dim identityComponent(K_disc)
 =dim_Q span_Q{2pi,beta_f}-1=s_disc.                        (5d)
```

Restrict `d_a` to either orbit closure and use its normalized Haar measure.  On the connected
continuous closure, the small-return volume has

```text
mu_(a,H)^cont(epsilon)
 =C_(a,H) epsilon^s_cont(1+o(1)),                           (5e)
```

where `C_(a,H)>0` is the ellipsoid volume of the graph Laplacian restricted to the primitive
subtorus lattice.  When `s_cont=r_cap`, this reduces to the spanning-tree constant below.  The
stroboscopic closure has the analogous power `s_disc`, multiplied near the identity by the
reciprocal of its finite component count.

Thus two measurements distinguish the invariants:

```text
independent energy-sector phase sampling  ->slope r_cap,
sampling the actual long-time orbit       ->slope s_cont.  (5f)
```

The deficit `r_cap-s_cont` is the number of observable relative-phase directions frozen by exact
energy-gap arithmetic.  It vanishes for generic spectra and can be extensive for free, symmetric,
or tensor-product Hamiltonians.

When the physical orbit is dense in `K_cont`, Weyl equidistribution gives, for every
`epsilon>0`,

```text
lim_(T->infinity) (1/T) measure{0<=t<=T:D_A(t)<epsilon}
 =mu_(a,H)^cont(epsilon).                                  (5g)
```

The target boundary has Haar measure zero because it is a nonconstant real-analytic level set on
the orbit torus.  Thus the arithmetic slope in `(5f)` is an actual long-time return-frequency law,
not only a geometric surrogate.

The finite graph-rank and spanning-tree laws below are the high-resolution evaluation of the
universal carrier `(5a)`.  Weak edges enter continuously through `mu_a`; support topology is only
the terminal small-resolution limit.  This closes the finite-precision discontinuity objection.

Consequently the small target has Haar volume comparable to `epsilon^r`:

```text
C_-(G,a) epsilon^r
 <= Haar{z:Phi_a(z)<=epsilon^2}
 <= C_+(G,a) epsilon^r                                    (6)
```

for all sufficiently small positive `epsilon`.  Constants are explicit products of spanning-forest
edge weights and graph path lengths; no randomness or computation is required.

The sharper local law is expected to be

```text
lim_(epsilon->0) epsilon^(-r)
  Haar{z:Phi_a(z)<=epsilon^2}
 =vol(B_r)/((2 pi)^r sqrt(tau_a(G))),                         (6a)
```

where `tau_a(G)` is the product, over connected components, of their weighted spanning-tree sums.
In rooted forest coordinates the quadratic tangent of `Phi_a` is the reduced weighted graph
Laplacian.  Ellipsoid volume and the weighted matrix-tree theorem give `(6a)`.  This supplies an
exact probability law, not only an exponent: near-return rarity is set by the total weight of
spanning coherence trees.

### Stroboscopic theorem candidate

For `omega in R^V`, put

```text
tau_a^disc(epsilon;omega)
 =min{n>=1:Phi_a((exp(i n omega_v))_v)<=epsilon^2}.         (7)
```

Then:

1. for every `omega`,
   `tau_a^disc(epsilon;omega)=O_(G,a,omega)(epsilon^(-s_disc(omega)))`;
2. for Haar-almost every `omega`,

   ```text
   lim_(epsilon->0)
     log tau_a^disc(epsilon;omega)/log(1/epsilon)=r;        (8)
   ```

3. for the minimax deadline `T_a^disc=sup_omega tau_a^disc`,

   ```text
   lim_(epsilon->0)
     log T_a^disc(epsilon)/log(1/epsilon)=r.                (9)
   ```

Almost every `omega` has `s_disc=r`, so `(8)` is the saturated case of item 1.  Exceptional
Diophantine spectra may recur faster.  The upper bounds are rational-basis compression followed by
spanning-forest Dirichlet approximation.  The lower minimax bound is Haar avoidance using `(6)`.
The almost-everywhere lower bound is the first Borel--Cantelli lemma.  The stronger
finite-resolution statement is `(5b)`.

### Continuous-time theorem candidate

For an edge-frequency gradient `alpha_e=E_u-E_v`, define first recurrence after first exit from the
`epsilon` target.  For every fixed nonstationary flow, the exponent is at most `s_cont-1`.  For
Lebesgue-almost every assignment of vertex energies, `s_cont=r`; for the worst energy assignment
after fixing one nonzero energy scale,

```text
lim_(epsilon->0)
  log tau_a^cont(epsilon;E)/log(1/epsilon)=r-1             (10)
```

when `r>=1`; for `r=1` the orbit is periodic and the exponent is zero.  A chosen spanning-tree edge
serves as the exact phase clock, leaving `r-1` simultaneous ratios.  The lower bound uses the same
forest coordinates: a continuous hit forces the clock edge close to an integer time, reducing the
problem to avoidance by a translation on `T^(r-1)`.

Equation `(10)` is not yet banked.  The definition must keep the exit interval and the normalization
of the energy scale explicit before promotion.

### Escape--recurrence equality

For a nonstationary finite state, the Hilbert--Schmidt speed is

```text
v_2=||[H,rho]||_HS
```

and the first exit time satisfies

```text
t_exit(epsilon)=(epsilon/v_2)(1+o(1)).                    (10a)
```

Combining `(5e)`, `(6a)`, `(8)`--`(10)`, and `(10a)` gives the candidate two-rank capstone

```text
r_cap
=lim_(epsilon->0) H_a(epsilon)/log(1/epsilon)
=lim_(epsilon->0) log T_a^disc(epsilon)/log(1/epsilon),

s_cont
=lim_(epsilon->0) H_(a,H)^cont(epsilon)/log(1/epsilon)
=lim_(epsilon->0)
   log(t_rec(epsilon)/t_exit(epsilon))/log(1/epsilon),     (10b)
```

where the last equality holds for almost every generator of each orbit-closure rank and for the
normalized minimax continuous problem on that rank stratum.  For every fixed Hamiltonian the
corresponding upper exponent is at most `s_cont`; exceptional Diophantine arithmetic can only
accelerate return.

Thus the two integers separate capacity from exploration:

```text
r_cap
=dimension of observable relative-phase space
=codimension of the independent-phase return target,

s_cont
=dimension of the Hamiltonian orbit closure
=generic number of powers of precision separating escape from return.  (10c)
```

For pure states the graph is complete and `r_cap=d-1`, recovering the projective capacity behind
current pure-state bounds.  Structured Hamiltonians can have `s_cont<<d-1`.  For mixed states
`r_cap` can be any value from zero to `d-1`, even at fixed spectrum and initial speed.

## Quantum identity

For a finite-dimensional Hamiltonian

```text
H=sum_v E_v P_v,      rho_t=exp(-itH) rho exp(itH),         (11)
```

orthogonality of distinct spectral blocks gives the exact identity

```text
||rho_t-rho||_HS^2
 =sum_(u<v) 2||P_u rho P_v||_HS^2
              |exp(-itE_u)-exp(-itE_v)|^2.                (12)
```

Thus `(4)` is not an analogy or inserted model: it is exactly mixed-state unitary evolution in
Hilbert--Schmidt distance with

```text
a_{uv}=2||P_u rho P_v||_HS^2.                              (13)
```

On a fixed finite Hilbert space, Hilbert--Schmidt and trace distance differ only by
dimension-dependent constants.  Hence they have the same high-resolution recurrence exponent.
The graph uses spectral projectors and is invariant under basis changes inside degenerate energy
eigenspaces.

## Infinite pure-point extension

For a countable pure-point Hamiltonian and trace-class state, the block weights in `(12)` are
summable.  At every positive resolution, a finite set of coherence blocks captures all but an
arbitrarily small squared-distance tail.  Applying the finite theorem to this truncation proves
recurrence at every finite observational resolution.  The relevant dimension becomes a
resolution-dependent finite forest rank.  No claim is made for continuous spectral measure.

This extension is a closure requirement, not the novelty apex: qualitative mixed-state recurrence
for discrete infinite spectra already exists in Gimeno--Sotoca 2017.

## Antagonist attacks

### Known parents and collisions

1. Gimeno--Sotoca 2017 already proves finite- and countably-discrete mixed-state upper bounds.  Its
   ambient-energy count can overcount stationary diagonal states; it does not identify the
   coherence-support graphic rank.
2. Godsil--Zhang 2022 already defines the basis-independent support graph through
   `P_u rho P_v != 0`.  The graph definition is not novel.
3. Kotowski--Oszmaniec 2026 proves pure-state deterministic and random recurrence bounds and
   explicitly leaves mixed states and observables open.  For a pure state its support graph is
   complete, so `(2)` reduces to the known projective dimension `d-1`.
4. Campos Venuti 2015 uses rational independence to replace pure-state time averages by full-torus
   phase averages.  It does not separate observable phase capacity from a lower-dimensional
   arithmetic orbit, handle mixed-state graph components, or give first-return exponents.
5. Lostaglio--Korzekwa--Jennings--Rudolph 2015 decompose energy coherence into time-translation
   modes.  That resource-theory decomposition does not identify recurrence rank, return volume,
   or the bridge-plus-rational-independence transition.
6. Torus orbit--stabilizer dimension, rational rank, simultaneous Diophantine approximation,
   ellipsoid volume, and the matrix-tree theorem are classical.  Novelty can only be their exact
   quantum identification as a two-rank law, the equal-speed isospectral no-go, the mixed-state
   and observer extensions, and the operational capacity-versus-exploration test.

### Immediate falsifiers

1. a source proving the same mixed-state recurrence exponent `|V|-c(G_rho)`;
2. a counterexample where the Hilbert--Schmidt identity `(12)` has a nonzero block outside the
   graph or a graph edge invisible to the norm;
3. failure of the forest coordinate map to be Haar preserving;
4. an energy assignment with continuous-time exponent larger than `s_cont-1`;
5. a metric conversion that changes the exponent in finite dimension;
6. an infinite pure-point state whose block tail is not uniformly negligible in time.

### Significance falsifiers

1. result remains only a standard orbit-dimension calculation with no prediction beyond the 2017
   bound;
2. graph components cannot be manipulated or inferred in any physical platform;
3. black-hole, QFT, or cosmological language requires an unproved spectral/random-matrix premise;
4. no experimentally measurable recurrence or finite-resolution crossover differs from support
   cardinality;
5. paper answers only a mathematical subproblem and cannot meet Nature's exceptional-importance
   and interdisciplinary-interest gates.

### Hostile Nature editorial review after two-rank correction

1. **Originality — provisional pass.**  Support graphs, rationally independent energies, torus
   recurrence, QFI, and matrix-tree asymptotics are parents.  Searches found no source combining
   them into the capacity/exploration ranks, equal-spectrum/equal-QFI separation, observer-union
   law, and operational two-slope test.
2. **Arresting and unexpected — pass.**  Full-rank clocks can share Hamiltonian, complete state
   spectrum, every spectral entropy, purity, initial speed, and optimal local time precision while
   their global first-return laws have different powers.  The qutrit witness makes this literal,
   not asymptotic rhetoric.
3. **Outstanding importance — borderline.**  The theorem answers the mixed-state and uniform
   observable extension left open by the 2026 pure-state state of the art and invalidates
   entropy-only microscopic recurrence laws.  A hostile editor can still call it a classical
   torus calculation unless the local-versus-global clock law and many-body capacity/exploration
   split lead the paper.
4. **Interdisciplinary interest — provisional pass.**  Quantum information, metrology,
   thermodynamics, graph theory, Diophantine dynamics, recurrence experiments, and conditional
   quantum-gravity consequences meet.  Black-hole language must remain a carefully delimited
   consequence, never evidence.
5. **Immediate and far-reaching implications — borderline.**  The qutrit protocol is executable
   on current hardware and avoids astronomical waiting through phase-volume sampling.  No new
   experimental data are present.  A theory-only Nature submission must make the no-go theorem,
   exact test, and resolution of free-versus-generic many-body scaling independently compelling.
6. **Nonspecialist readability — achievable.**  Lead with “equally precise clocks can have
   different reset laws”; defer graph Laplacians, Haar volume, and rational rank.

Current honest verdict: **not publication-ready yet, but no longer intrinsically too narrow.**
Remaining rejection grounds are incomplete proof/formal audit, absence of a finished manuscript
and claim trace, and failure to demonstrate that the two-rank law changes a live physical
conclusion rather than only its notation.

## Physical consequence gate

Potential exact consequence:

```text
dephasing deletes coherence edges;
only deletion of a graph bridge can lower phase capacity;
it lowers dynamical clock rank iff its gap is rationally independent
of the surviving coherent gaps.                                        (14)
```

Deleting any non-bridge coherence changes weights but neither rank: its energy gap is the signed
sum along an alternate surviving path.  Deleting a bridge increases the number of components by
one and lowers `r_cap` by exactly one.  It lowers `s_cont` by one exactly when that bridge gap is
outside the rational span of all surviving gaps.  Dually, a new observable clock direction turns
on only when a coherence both joins two graph components and carries a rationally new gap.  This
topology--arithmetic AND law is the exact transition rule.

The isospectral theorem makes the physics claim sharper.  Entropy-only Poincare-time estimates are
not universal quantum laws: even complete Hamiltonian and state spectra leave the recurrence
dimension undetermined across its full allowed range.  Any black-hole or cosmological recurrence
estimate based only on state counting or entropy therefore requires an additional coherence and
spectral-arithmetic premise.  The paper must distinguish this unconditional insufficiency theorem
from a prediction for any particular black hole.

The exact no-go can be stated without gravity.  For every `d>=3`, one may fix a `d`-level
Hamiltonian and a microcanonical state-count entropy `S_shell=log d`, then choose full-rank states
with the same density spectrum, all spectral entropies, purity, local speed, and time-estimation
QFI but continuous return exponents `0,...,d-2`.  Therefore no function of

```text
S_shell, spectrum(H), spectrum(rho), purity, or local QFI
```

determines microscopic recurrence time.  At saturated clock rank `s_cont=d-1`,

```text
log(t_rec/t_exit)
 ~(d-1)log(1/epsilon)
 =(exp(S_shell)-1)log(1/epsilon),                           (14e)
```

which is the double-exponential-in-entropy regime discussed in quantum-complexity and black-hole
work.  The same shell data also permit periodic return.  The theorem therefore identifies the
missing premises behind the competing recurrence scales: coherence capacity, arithmetic clock
rank, target resolution, and Diophantine type.

For finite precision, arbitrarily weak edges cannot cause an abrupt observable jump; their weight
must set a crossover scale.  A publication-level theorem therefore needs a weighted finite-scale
law, not only the support exponent.  Candidate carrier: a graph-Laplacian water entropy or
spanning-forest rate--distortion functional that reduces to `(2)` at high resolution.

Black-hole language is permitted only as a conditional corollary.  A thermal state is diagonal and
stationary in its own Hamiltonian basis.  Information-bearing off-diagonal blocks create the
coherence graph.  No theorem here proves that a real black hole has a finite discrete spectrum,
generic energy gaps, or a connected radiation coherence graph.

The law is experimentally accessible without waiting for an astronomical first return.  Apply
independently sampled diagonal phase gates

```text
U_theta=sum_v exp(i theta_v)P_v
```

and measure the two-copy overlap `Tr(rho U_theta rho U_theta*)`.  Since purity is unchanged,

```text
||U_theta rho U_theta*-rho||_HS^2
 =2Tr(rho^2)-2Tr(rho U_theta rho U_theta*).                  (14a)
```

The fraction of phase samples within distance `epsilon` is exactly `mu_a(epsilon)` and therefore
has the falsifiable small-resolution law

```text
Pr{return within epsilon}
 ~vol(B_r) epsilon^r /[(2pi)^r sqrt(tau_a(G))].              (14b)
```

The log--log slope reads out graphic rank; the intercept reads out weighted spanning-tree
complexity.  This converts an astronomical waiting-time claim into a random-phase overlap
experiment using already-demonstrated two-copy/SWAP or randomized-overlap measurements.
Sampling actual evolution times instead of independent phases gives slope `s_cont`; the difference
between the two measured slopes directly counts arithmetic clock constraints.

The explicit qutrit experiment uses

```text
|psi_1>=sqrt(1-delta_1)|0>+sqrt(delta_1)|1>,
|psi_2>=sqrt(1-2delta_2)|0>
        +sqrt(delta_2)|1>+sqrt(delta_2)|2>,
rho_j=bI+(1-3b)|psi_j><psi_j|,                              (14c)
```

with `delta_1,delta_2` tuned to the common variance in `(3g)`.  A standard depolarizing channel
prepares the common spectrum, and diagonal qutrit phase gates implement `(3j1)`.  Before any
long-time scan, tomography or overlap measurements verify identical spectra, purity, and QFI.
The pre-registered predictions are:

```text
independent-phase near-return slopes: 1 versus 2,
physical first-return exponents:      0 versus 1.           (14d)
```

Native trapped-ion and superconducting-qutrit platforms already demonstrate arbitrary phase
control and density-matrix reconstruction; the required operations are not beyond current
hardware.

## Approach

1. prove exact block identity `(12)` and metric equivalence;
2. prove the forest quotient and small-target law `(6)`;
3. prove discrete minimax and almost-everywhere exponent `(8)`--`(9)`;
4. close continuous exit/return theorem `(10)` with explicit scale;
5. derive bridge-deletion classification `(14)`;
6. seek and prove a finite-resolution weighted graph functional;
7. prove the equal-speed isospectral separation `(3d)`--`(3j)`;
8. derive and audit the random-phase overlap experiment `(14a)`--`(14b)`;
9. re-run exact-object literature audit;
10. only then formalize the dependency-closed theorem in Lean.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack plan, exact falsifiers
- [ ] source audit excludes existing coherence-graph recurrence exponent
- [ ] complete finite stroboscopic proof
- [ ] complete continuous exit/return proof
- [ ] complete infinite pure-point truncation proof
- [ ] finite-resolution weighted graph law or honest proof that none survives
- [ ] equal-speed isospectral separation proof
- [ ] operational random-phase overlap law
- [ ] physical consequence survives hostile review without speculative cosmology
- [ ] 1 → 2 fully-proven: complete dependency-closed paper proof
- [ ] 2 → 3 formalized: exact Lean theorem surface, foreground builds, axiom audit
- [ ] 3 → 4 publication-ready: manuscript, claim trace, Nature editorial audit

## Log

- 2026-07-28 — created after rejecting literal zeta-zero particle/antiparticle and Casimir
  interpretations and after locating the June 2026 pure-state recurrence collision.
- 2026-07-28 — identified existing parents: Gimeno--Sotoca mixed-state upper bounds,
  Godsil--Zhang support graph, Kotowski--Oszmaniec pure-state tight bounds.

## Dependency-closed paper proof draft

### Master compact-group recurrence proof

Let `(X,d)` be a compact metrizable abelian group with translation-invariant metric, normalized
Haar measure `m`, and `b(epsilon)=m(B(1,epsilon))`.  A maximal
`epsilon/2`-separated subset is finite and its `epsilon/2`-balls cover `X`.  Its
`epsilon/4`-balls are disjoint, so its cardinality is at most `1/b(epsilon/4)`.
Consequently `X` has a cover by at most `1/b(epsilon/4)` balls of radius `epsilon/2`.

For any `x in X`, place the points

```text
1,x,x^2,...,x^M
```

into such a cover.  If `M` is at least the covering cardinality, two points lie in the same ball.
Translation invariance and the triangle inequality give

```text
d(x^(j-i),1)<=epsilon,       1<=j-i<=M.                    (14a)
```

This proves the upper half of `(5b)`.

For the lower half, `x |-> x^n` preserves normalized Haar measure on a torus and, more generally,
on every compact connected abelian group.  In the coherence application `X_a` is a quotient of a
product torus and is connected.  Hence

```text
m{exists 1<=n<=N:d(x^n,1)<=epsilon}
 <=N b(epsilon).                                           (14b)
```

If `N b(epsilon)<1`, some `x` avoids the target through time `N`.  Take
`N=ceil(1/b(epsilon))-1`.  Then `N b(epsilon)<1`, so the least universal deadline is at least
`N+1=ceil(1/b(epsilon))>=1/b(epsilon)`.  This proves the lower half of `(5b)` without additive
slack.

For countably many edges with `sum_e a_e<infinity`, the series `(4)` converges uniformly because
each chord square is at most four.  It therefore defines a continuous translation-invariant
pseudometric on the compact product torus.  Quotienting by its closed zero subgroup gives a compact
metrizable abelian group.  Every positive-radius ball is a nonempty open set and has positive Haar
measure.  The preceding argument applies without truncation and proves a finite minimax deadline
at every positive resolution.

### Orbit-closure ranks and restricted volume

In forest coordinates let `beta in R^r`.  Characters of `T^r` are indexed by `k in Z^r`.
A character is trivial on the continuous orbit exactly when `k dot beta=0`.  Therefore the
annihilator of `K_cont` is

```text
L_cont={k in Z^r:k dot beta=0}.                             (14c)
```

The dimension of a subtorus is `r-rank_Z(L_cont)`.  Elementary rational linear algebra identifies
this with `dim_Q span_Q{beta_f}`.  For the cyclic orbit, a character is trivial exactly when
`k dot beta in 2pi Z`.  Homogenizing this relation by adjoining `2pi` gives

```text
dim identityComponent(K_disc)
 =dim_Q span_Q{2pi,beta_f}-1.                              (14d)
```

These prove `(5d)` and forest-independence, since every coherent gap is an integer signed sum of
forest gaps and every forest gap is itself coherent.

Let `K` be the connected orbit subtorus of dimension `s`.  Choose a primitive integer torus
embedding `M:T^s ->T^r` with image `K`.  In local angular coordinates the restricted phase energy
is

```text
Phi_a(exp(iM y))
 =y^T(M^T L_red M)y+O(||y||^4).                            (14e)
```

The middle matrix is positive definite because the quotient metric has no nontrivial zero
direction.  Ellipsoid scaling with normalized torus Haar measure proves `(5e)` with

```text
C_(a,H)=vol(B_s)/[(2pi)^s sqrt(det(M^T L_red M))].          (14f)
```

For a disconnected cyclic closure, sufficiently small identity balls meet only its identity
component, so normalized Haar measure contributes the reciprocal of the finite component count.

A translation flow with dense image in a compact torus is uniquely ergodic.  Weyl's character
criterion proves this directly: every nontrivial character has time average

```text
(1/T) integral_0^T exp(i lambda t)dt ->0,
```

and trigonometric polynomials are uniformly dense in the continuous functions.  The restricted
phase energy is a nonconstant real-analytic function when `s>0`; each of its level sets has Haar
measure zero.  Approximation of the target indicator from above and below by continuous functions
therefore proves `(5g)`.

### Rational-basis recurrence compression

For stroboscopic time put `alpha_f=beta_f/(2pi)` and
`s=s_disc`.  Choose a rational basis

```text
1,theta_1,...,theta_s
```

of `span_Q{1,alpha_f}` and clear all denominators in the expansions of the finitely many
`alpha_f` by one positive integer `D`.  Simultaneous Dirichlet approximation of the `s` numbers
`theta_j` supplies `1<=q<=Q^s` for which every `q theta_j` is within `1/Q` of an integer.
At `n=Dq`, every forest phase is within `C_(beta)/Q` of an integer multiple of `2pi`.  The forest
path bound then yields

```text
tau_a^disc(epsilon;beta)
 <=C_(a,beta)epsilon^(-s_disc).                            (14g)
```

When `s_disc=0`, clearing denominators gives an exact finite period.

For continuous time let `s=s_cont>=1`, choose a rational basis
`gamma_0,...,gamma_(s-1)` of the gap span with `gamma_0!=0`, and clear the rational coefficients
of every `beta_f/gamma_0`.  Approximate the `s-1` ratios `gamma_j/gamma_0`; at

```text
t=2pi Dq/|gamma_0|,       1<=q<=Q^(s-1),                  (14h)
```

all forest phases are `O(1/Q)`.  Hence every fixed nonstationary flow obeys

```text
tau_a^cont(epsilon;beta)
 <=C_(a,beta)epsilon^(-(s_cont-1)).                        (14i)
```

For `s_cont=1`, `(14h)` is an exact period.  These are the universal upper halves of `(3a)`.

### A. Forest phase coordinates

Choose one root in every component of `G` and a spanning forest `F`.  Orient every forest edge
away from its root.  The map

```text
(z_v)_(v in V)
  |-> ((z_root)_(roots), (z_child/z_parent)_(edges in F))   (15)
```

is an automorphism of compact abelian tori.  Its inverse multiplies edge ratios along the unique
root-to-vertex forest paths.  Both maps are given by integer monomials, so `(15)` preserves
normalized Haar measure.  There are exactly

```text
|F|=|V|-c(G)=r                                             (16)
```

edge-ratio coordinates.

Put `ell_e` for the number of forest edges in the path joining the endpoints of `e in E` and

```text
K_F=sum_(e in E) a_e ell_e^2.                              (17)
```

If every forest-edge chord is at most `delta`, the chord metric and the forest path give

```text
|z_u-z_v|<=ell_{uv} delta
```

for every graph edge.  Hence `Phi_a(z)<=K_F delta^2`.

Conversely, `Phi_a(z)<=epsilon^2` implies

```text
|z_child-z_parent|<=epsilon/sqrt(a_f)                      (18)
```

on every `f in F`.  For `0<=delta<=2`, normalized circle Haar measure satisfies

```text
delta/pi
 <=Haar_T{|z-1|<=delta}
 <=delta/2.                                                (19)
```

Indeed the exact measure is `(2/pi)arcsin(delta/2)`, and
`x<=arcsin x<=(pi/2)x` on `[0,1]`.  Equations `(15)`--`(19)` prove, for sufficiently small
`epsilon`,

```text
(epsilon/(pi sqrt(K_F)))^r
 <=mu_a(epsilon)
 <=epsilon^r/(2^r product_(f in F)sqrt(a_f)),              (20)
```

where `mu_a(epsilon)=Haar{Phi_a<=epsilon^2}`.  This proves `(6)` with explicit constants.

### B. Exact spanning-tree small-target constant

Use `(15)` to discard the root phases and write the remaining angular coordinates as
`x in (-pi,pi]^r`.  The zero of the quotient target is unique.  At that zero,

```text
Phi_a(exp(ix))=x^T L_red x+O(||x||^4),                     (21)
```

where `L_red` is the block-diagonal reduced weighted graph Laplacian obtained by deleting one root
row and column per component.  It is positive definite.  Scaling `x=epsilon y`, using `(21)` to
sandwich the sublevel set between quadratic ellipsoids with factors tending to one, and applying
ordinary ellipsoid volume gives

```text
lim_(epsilon->0) epsilon^(-r) mu_a(epsilon)
 =vol(B_r)/((2pi)^r sqrt(det L_red)).                       (22)
```

The weighted matrix-tree theorem says that each component block determinant is its weighted
spanning-tree sum.  Therefore `det L_red=tau_a(G)` and `(22)` is exactly `(6a)`.

### C. Discrete recurrence upper bound

For `omega in R^V`, apply `(15)` to its forest-edge differences `beta_f`.  Partition every circle
into `Q` arcs.  Among the `Q^r+1` points

```text
(n beta_f mod 2pi)_(f in F),       0<=n<=Q^r,
```

two occupy the same product cell.  Their difference supplies `1<=n<=Q^r` for which every
forest-edge chord is at most `2pi/Q`.  By `(17)`,

```text
Phi_a(exp(in omega))<=K_F(2pi/Q)^2.                        (23)
```

Taking `Q=ceil(2pi sqrt(K_F)/epsilon)` proves

```text
tau_a^disc(epsilon;omega)
 <=ceil(2pi sqrt(K_F)/epsilon)^r                           (24)
```

for every `omega`.

### D. Discrete minimax and almost-everywhere lower bounds

For every positive integer `n`, coordinatewise multiplication by `n` preserves torus Haar
measure.  Hence

```text
Haar{exists 1<=n<=N:Phi_a(exp(in omega))<=epsilon^2}
 <=N mu_a(epsilon).                                       (25)
```

The upper half of `(20)` permits `N` to be a fixed positive multiple of `epsilon^(-r)` while the
right side remains below one.  Some `omega` therefore avoids recurrence through `N`, proving the
minimax lower bound and `(9)`.

For `gamma>0`, set `epsilon_n=n^(-1/r-gamma)`.  Equations `(20)` and Haar invariance give

```text
sum_n Haar{Phi_a(exp(in omega))<=epsilon_n^2}
 <=C sum_n n^(-1-r gamma)<infinity.                        (26)
```

The first Borel--Cantelli lemma implies that almost every `omega` belongs to only finitely many
events in `(26)`.  If `n=tau_a^disc(epsilon;omega)` is large, this forces

```text
n>epsilon^(-r/(1+r gamma)).
```

Intersecting over positive rational `gamma` and combining with `(24)` proves `(8)`.  For `r=0`,
`Phi_a` vanishes identically and all three exponents are zero.

### E. Continuous-time upper bound

Assume `r>=1`.  Write the forest-edge energy gaps as

```text
beta_f=E_child-E_parent.
```

Every forest edge joins distinct spectral sectors, so every `beta_f` is nonzero.  Choose
`f_0 in F`.  Simultaneous Dirichlet approximation applied to the `r-1` ratios
`beta_f/beta_(f_0)` gives, for every `Q>=1`, an integer

```text
1<=q<=Q^(r-1)
```

such that at

```text
t=2pi q/|beta_(f_0)|                                      (27)
```

the `f_0` phase is exact and every other forest-edge phase has chord at most `2pi/Q`.  Therefore

```text
Phi_a(exp(-itE))<=K_F(2pi/Q)^2,                            (28)
```

and every fixed nonstationary flow has a recurrence witness

```text
t<=C_(E,G,a) epsilon^(-(r-1)).                             (29)
```

For small `epsilon`, `(27)` lies after the initial exit because the exit time tends to zero while
`(27)` is bounded below by a positive energy-scale constant.  When `r=1`, `(27)` is an exact
period, so the exponent is zero.

### F. Continuous minimax and almost-everywhere lower bounds

Fix a forest clock edge `f_0`, normalize its gap to `2pi`, and assign the other forest gaps

```text
beta_f=2pi omega_f,       omega_f in [0,1].                (30)
```

Root energies plus forest gaps determine vertex energies uniquely.  Common offsets on the
components can be chosen so that all spectral values are distinct; coincident values form only a
finite union of null hyperplanes.

If `Phi_a(exp(-itE))<=epsilon^2`, the clock-edge term and `(19)` imply

```text
dist(t,Z)<=epsilon/(4sqrt(a_(f_0)))                        (31)
```

for sufficiently small `epsilon`.  Write `t=n+s` with `n in Z` and `|s|` bounded by `(31)`.
For every other forest edge, the triangle inequality gives

```text
|exp(2pi i n omega_f)-1|
 <=epsilon/sqrt(a_f)+2pi|s|
 <=C_f epsilon.                                           (32)
```

Thus a continuous return near integer `n` forces the `(r-1)`-torus point
`(n omega_f)_(f!=f_0)` into a product target of Haar measure at most
`C epsilon^(r-1)`.

The squared distance has expansion

```text
Phi_a(exp(-itE))
 =t^2 sum_e a_e(E_u-E_v)^2+O(t^4),                         (33)
```

with a positive quadratic coefficient.  Hence for each such flow there is a fixed `t_0>0` such
that, once the small initial target is exited, no return occurs before `t_0`.  For returns after
`t_0`, `(31)` has `n>=1` when `epsilon` is small.  Haar avoidance over the first `N` integers in
`(32)` now gives an assignment `omega` with

```text
tau_a^cont(epsilon;E)>=c_(G,a)epsilon^(-(r-1)).             (34)
```

Together with `(29)`, this proves the continuous minimax exponent `r-1` under the fixed clock-gap
normalization.

For the almost-everywhere statement, use the targets

```text
epsilon_n=n^(-1/(r-1)-gamma)
```

in `(32)`.  Their measures are summable.  Borel--Cantelli and `(29)` give the exponent `r-1` for
almost every forest-gap ratio.  The linear change from roots plus forest gaps to vertex energies,
followed by Fubini over the nonzero clock gap, transfers this to Lebesgue-almost every energy
vector.  The cases `r=0` and `r=1` are respectively stationary and periodic.

### G. Exact quantum reduction and metric stability

The spectral blocks `P_u rho P_v` are pairwise orthogonal in Hilbert--Schmidt inner product.
Expanding `(11)` and pairing the `(u,v)` and `(v,u)` terms proves `(12)` with positive edge
weights `(13)`.  In ambient Hilbert dimension `D`,

```text
||X||_HS<=||X||_1<=sqrt(D)||X||_HS.                        (35)
```

Targets in the two norms therefore contain one another after multiplying `epsilon` by fixed
constants.  Equations `(24)`--`(34)` show that these constants disappear after division by
`log(1/epsilon)`.  The Hilbert--Schmidt and trace-distance recurrence exponents coincide.

The graph is basis-independent inside degenerate energy sectors because `(1)` uses spectral
projectors and the Hilbert--Schmidt norm of the whole block.

For a positive density operator, `P_v rho P_v=0` implies the full `v` block row and column vanish:

```text
Tr(P_v rho P_v)=||sqrt(rho)P_v||_HS^2=0
```

forces `sqrt(rho)P_v=0`, hence `rho P_v=P_v rho=0`.  Thus the active-vertex convention loses no
coherence and retains isolated stationary populations needed by tensor products.

### H. Full isospectral range

Fix distinct positive density eigenvalues `lambda_1,...,lambda_d` summing to one.  For a desired
`0<=r<=d-1`, conjugate the first `r+1` eigenvectors by a unitary `U` and leave the rest fixed.
For each pair `i!=j` in the block, the real-analytic function

```text
U |-> (U diag(lambda_1,...,lambda_(r+1)) U*)_(ij)          (36)
```

is not identically zero: a nontrivial two-coordinate rotation already makes that entry nonzero.
Its zero set has empty interior.  A finite union of these zero sets cannot cover the unitary
group, so some `U` makes every block off-diagonal entry nonzero.  The support graph is a complete
component on `r+1` vertices and isolated vertices, with graphic rank `r`.

There are only finitely many ranks and blocks.  Intersecting the corresponding full-measure sets
from the discrete and continuous almost-everywhere theorems gives one fixed nondegenerate
Hamiltonian spectrum for which all these isospectral density operators realize their asserted
recurrence exponents.  This proves the spectral-blindness statement without changing either
spectrum.

### H.1 Equal-speed isospectral separation

Fix `E_0=0` and nonzero `E_1,...,E_(d-1)`.  For `1<=r<=d-1`, set

```text
A_r=sum_(k=1)^r E_k^2,     B_r=sum_(k=1)^r E_k,
V_r(delta)=delta A_r-delta^2 B_r^2.                         (36a)
```

Since `A_r>0`, there is a common

```text
0<delta_*<min_r{1/r,A_r/(2B_r^2)}                            (36b)
```

with the second entry omitted when `B_r=0`.  Hence `V_r'(delta)>0` on
`[0,delta_*]` for every `r`.  Choose `0<s<min_r V_r(delta_*)`.  Continuity and strict
monotonicity give a unique `delta_r in (0,delta_*)` with `V_r(delta_r)=s`.

For the probabilities and states in `(3d)`, direct calculation gives

```text
<H>=delta B_r,
<H^2>=delta A_r,
Var(H)=V_r(delta).                                          (36c)
```

Let `pi=|psi><psi|`.  The commutator identity

```text
||[H,pi]||_HS^2=2(<H^2>-<H>^2)                              (36d)
```

follows by expanding the four trace terms in
`Tr([H,pi]*[H,pi])` and using `pi^2=pi`.  Since the identity part commutes with `H`,

```text
||[H,bI+c pi]||_HS^2=2c^2 Var_psi(H).                       (36e)
```

The entire return trajectory, not only its tangent, is a scaled pure-projector trajectory:

```text
rho_t-rho=c(pi_t-pi),
(1/2)||rho_t-rho||_1
 =c sqrt(1-|<psi|exp(-itH)|psi>|^2).                        (36e1)
```

The last equality follows by diagonalizing `pi_t-pi` on the two-dimensional span of the two unit
vectors; its nonzero eigenvalues are the opposite pair
`+-sqrt(1-|<psi_t|psi>|^2)`.

In an eigenbasis of `rho`, the symmetric-logarithmic-derivative formula for unitary parameter
estimation is

```text
F_Q(rho,H)
 =2 sum_(m,n:lambda_m+lambda_n>0)
   (lambda_m-lambda_n)^2/(lambda_m+lambda_n)|H_mn|^2.       (36e2)
```

Only matrix elements between `psi` (eigenvalue `a`) and its orthogonal complement (eigenvalue `b`)
contribute.  The two orderings contribute equally, and

```text
sum_(j orthogonal psi)|<psi|H|j>|^2=Var_psi(H),
```

which proves `(3f1)`.

Thus all `rho_(r,delta_r)` have the same speed `sqrt(2)c sqrt(s)`.  They also have the same
eigenvalues because `pi` has eigenvalues `1,0,...,0`.  Every amplitude in the first `r+1`
energy sectors is positive, so every off-diagonal block there is nonzero and the graph is
`K_(r+1)` plus isolated vertices.

For each `r`, the exceptional Hamiltonian spectra for which the continuous exponent differs from
`r-1` have Lebesgue measure zero by Section F.  Their finite union is null.  Choose one Hamiltonian
outside it and with nonzero energy values.  The same Hamiltonian then gives exponents
`0,1,...,d-2` to the equal-speed isospectral family.  This proves `(3d)`--`(3j)`.

For the explicit qutrit `(3j1)`, the common-variance construction applies because

```text
V_1(delta)=delta-delta^2,
V_2(delta)=3delta-(3+2sqrt(2))delta^2
```

are both strictly increasing near zero.  A small return bounds the two forest-edge chords; the
circle chord--angle comparison gives `(3j2)`.  Rounding the first phase gives `(3j3)`.
If `|q sqrt(2)-p|<1`, then `|p|<2q` for positive `q`, so `(3j4)` gives an explicit lower bound
`|q sqrt(2)-p|>=1/((sqrt(2)+2)q)`.  Dirichlet's theorem supplies the matching upper bound.
The fixed exact period of the two-energy state lies after its small initial exit.  This proves
`(3j5)` in both Hilbert--Schmidt and trace distance by `(36e1)`.

### H.2 Operational random-phase law

Let `U_theta=sum_v exp(i theta_v)P_v`.  Unitary invariance of purity and trace cyclicity give

```text
||U_theta rho U_theta*-rho||_HS^2
 =Tr((U_theta rho U_theta*-rho)^2)
 =2Tr(rho^2)-2Tr(rho U_theta rho U_theta*).                  (36f)
```

The block calculation in Section G identifies the left side with `Phi_a(exp(i theta))`.
Uniform independent phases push forward to Haar measure on the quotient phase torus.  Therefore
the observed fraction of samples whose two-copy overlap exceeds
`Tr(rho^2)-epsilon^2/2` is exactly `mu_a(epsilon)`.  Section B yields `(14b)`.

For the rank-one spike family `(3d)`, the complete-graph edge weights are

```text
a_ij=2c^2 p_i p_j.
```

The weighted Prüfer-code identity for a complete graph,

```text
sum_T product_{{i,j} in T}(x_i x_j)
 =(sum_i x_i)^(m-2) product_i x_i,                          (36g)
```

with `m=r+1` and `x_i=sqrt(2)c p_i`, gives the explicit tree invariant

```text
tau_a(K_(r+1))=(2c^2)^r product_(i=0)^r p_i.                (36h)
```

Hence both the power and prefactor of the random-phase near-return probability are fixed before
the experiment.

### H.3 Observer union and tensor-product composition

For a finite self-adjoint family, the `(u,v)` energy blocks of
`exp(itH)A_j exp(-itH)-A_j` are Hilbert--Schmidt orthogonal over ordered pairs `(u,v)`.  Summing
their squared norms over `j`, then pairing `(u,v)` with `(v,u)`, proves `(3a1)`--`(3a2)`.
For a countable family, Tonelli's theorem and

```text
sum_(u,v)||P_u A_j P_v||_HS^2=||A_j||_HS^2
```

give summable aggregate edge weights under the stated hypothesis.  Section "Master compact-group
recurrence proof" then applies.  Adding operators adds nonnegative weights, so the support graph
is the union graph.  A new edge changes `|V|-c` precisely when it joins two components; a finite
batch changes the rank by the rank increase of the corresponding graphic matroid.

For product density operators, `(3k)` follows from the tensor-product spectral projectors.
A tensor product of finite matrices is zero exactly when at least one factor is zero.  On every
active sector positivity gives `P_u rho_A P_u!=0` and
`Q_alpha rho_B Q_alpha!=0`.  Thus two distinct product vertices are adjacent exactly when, in
each coordinate, the entries are equal or adjacent.  This is `(3l)`.

A path in a strong product projects to paths inside components of both factors, so a product
component is contained in a pair of factor components.  Conversely, interleave paths in the two
factor components, holding the other coordinate fixed; reflexive adjacency makes this a
strong-product path.  Product components are therefore exactly the `c_A c_B` Cartesian products
of factor components.  Counting vertices proves `(3m)` and `(3n)`.

Every product energy gap has form `(E_u-E_v)+(F_alpha-F_beta)`, while both factor gaps occur by
holding the other active coordinate fixed.  The rational span of product gaps is therefore exactly
`W_A+W_B`.  The vector-space dimension formula proves `(3o)`.  Iteration gives multiplicative
phase capacity but the dimension of the sum of factor gap spaces for dynamical clock rank.

### I. Infinite pure-point closure

Let `H` have countably many pure-point spectral projectors and let `rho` be trace class.  For finite
partial spectral sums `P_N` increasing strongly to the identity,

```text
rho_N=P_N rho P_N,
||rho-rho_N||_1 ->0.                                      (37)
```

Because `P_N` commutes with `H`, the approximation is uniform in time:

```text
||rho_t-(rho_N)_t||_1=||rho-rho_N||_1.                     (38)
```

The finite spectral-sector evolution of `rho_N` recurs by the forest Dirichlet argument.
The triangle inequality with `(37)`--`(38)` then proves trace-distance recurrence of `rho` at
every positive finite resolution.  This establishes the infinite pure-point extension while
making no statement about continuous spectral measure.

### J. Topological edge classification

Removing a non-bridge edge leaves the component count unchanged, so
`r_cap=|V|-c(G)` is unchanged.  Its energy gap is the signed sum of gaps along an alternate path,
so removing it also leaves the rational gap span and `s_cont` unchanged.

Removing a bridge increases `c(G)` by one and lowers `r_cap` by one.  The surviving gap span either
contains the removed numerical gap or has codimension one in the old span.  Hence `s_cont` falls by
one exactly in the latter case.  Adding an edge between two components performs the inverse
topological operation and raises dynamical rank exactly when its gap is rationally new.  This
proves the topology--arithmetic AND law `(14)`.

At fixed nonzero resolution a weak edge changes constants and only crosses to the new capacity
power below its weight scale; no discontinuous finite-precision claim follows from support alone.
