# Proof dossier: Galois microlocal coarea law

Status: in progress; internal research record, not manuscript text.

## 1. Exact finite source

Fix a positive integer `N` and write `w^N=z`. A finite Puiseux spectrum on this cover is a finite
`mu_N`-stable set `A` of pairwise distinct polynomials

`q_a(w)=sum_{k=1}^K c_(a,k) w^k`.

For `a != b`, define

`k(a,b)=max{k : c_(a,k) != c_(b,k)}` and `h(a,b)=k(a,b)/N`,

and put `h(a,a)=0`. The cyclic action is required to satisfy
`q_(g a)(w)=q_a(g w)`; therefore it preserves `h`. Let `I=A/mu_N` be the orbit set and let
`r_i=|A_i|`.

For two orbits define the mixed irregularity

`s_ij = sum_(a in A_i) sum_(b in A_j) h(a,b)`.

It is integral. Decompose `A_i x A_j` into cyclic orbits. If an ordered pair has orbit length `L`,
its difference polynomial is fixed by rotation through `2 pi L/N`; hence its leading exponent `k`
is divisible by `N/L`. That orbit contributes `Lk`, divisible by `N`. Summing and dividing by `N`
proves integrality. Equivalently `s_ij` is the irregularity of the descended exponential Hom local
system.

Define the core diagram by

`B_ij=s_ij-r_i r_j` for `i != j`,

`B_ii=s_ii-r_i^2+1`.

Thus, without separate loop and edge interfaces,

`1+B_ij/(r_i r_j)=s_ij/(r_i r_j)` for `i != j`,

`1+(B_ii-1)/r_i^2=s_ii/r_i^2`.

These are exactly the normalized Hom-irregularity contacts.

## 2. Dendrogram lemma

For all `a,b,c`,

`h(a,b) <= max(h(a,c),h(c,b))`.

Proof. For every exponent strictly above the maximum on the right, coefficients of `q_a,q_c` and
`q_c,q_b` agree, hence coefficients of `q_a,q_b` agree. Symmetry and the same inequality under
permutation imply that the largest of the three contacts occurs at least twice.

For `t>0`, set

`a ~_t b iff a=b or h(a,b)<t`.

The preceding inequality proves transitivity. The partitions `Pi_t=A/~_t` coarsen as `t`
increases. Since `A` is finite, only finitely many partitions occur. Their inclusion poset is a
canonical rooted dendrogram; leaves are singleton branches and the meet height of `a,b` is
`h(a,b)`. This constructs the rooted object from coefficients.

## 3. Finite coarea identity

Choose `H>max_(a,b) h(a,b)`. For a charge `y:A->R`, and a block `C in Pi_t`, write
`y(C)=sum_(a in C)y_a`. Define

`E_H(y)=integral_[0,H] sum_(C in Pi_t) y(C)^2 dt`.

The integrand is a finite step function. Expanding squares and using
`1_{a~_t b}=1_{h(a,b)<t}` gives

`E_H(y)=sum_(a,b) (H-h(a,b)) y_a y_b`

`       =H(sum_a y_a)^2-sum_(a,b)h(a,b)y_a y_b`.                 (C)

This is an identity of finite sums: if `0=t_0<...<t_s=H` contains every contact value, the
integral means

`sum_(nu=0)^(s-1) (t_(nu+1)-t_nu) sum_(C in Pi_t) y(C)^2`

for any `t in (t_nu,t_(nu+1)]`. Every coefficient is positive. Singleton blocks near zero imply
`E_H(y)>0` for `y != 0`.

Equation (C) is the source law. Rooted cuts, Rees level scaling, electrical energy, and corona
reduction are presentations of this one filtered partition energy.

## 4. Orbit descent and Cartan polarization

For `x:I->R`, lift `y_a=x_i` on `A_i` and set physical rank

`M=sum_i r_i x_i=sum_a y_a`.

Then

`sum_(i,j)s_ij x_i x_j=sum_(a,b)h(a,b)y_a y_b`.                 (D)

Let `C=2 Id-B` and `Q(x)=x^T C x`. Direct substitution of the unified definition of `B`, including
its diagonal correction, gives

`Q(x)=sum_i x_i^2+M^2-sum_(i,j)s_ij x_i x_j`.                  (E)

Combining (C)--(E),

`Q(x)=sum_i x_i^2+E_H(y)-(H-1)M^2`.                            (W)

The first two terms define a positive definite form. Therefore `Q` is positive on `M=0`, its
negative index is at most one, and every zero or negative direction has nonzero physical rank.
Changing `H` adds the same `(H'-H)M^2` to `E_H` and the defect, so (W) is root-height independent.

This proof includes twisted orbits, loops, and negative diagram multiplicities. No realization
certificate is used.

## 5. Genuine microsupport and characteristic cycles

For `a,b in A`, let `p_ab=q_b-q_a`, with leading degree `k_ab=N h(a,b)`. On the boundary circle of
the `w`-cover, the ordered exponential Hom has formal phase

`phi_ab(theta)=Re(c_ab exp(i k_ab theta))`,

where `c_ab` is the leading coefficient. Define its zero-time exponential sheaf

`S_ab = k_{ {theta : phi_ab(theta)>=0} }`.

If `a!=b`, `phi_ab` has exactly `2 k_ab` simple zeros. These are the dominance walls of the two
exponentials. The sheaf is locally constant off them. At each wall its singular support contains
exactly one oriented conormal ray and its microstalk has rank one. Its characteristic cycle is the
signed sum of those rays, each with coefficient one. Exactly `k_ab` walls have the orientation that
enters a decay sector for `exp(q_b-q_a)`; equivalently, those oriented walls are in canonical
bijection with the `k_ab` maximal-decay Stokes directions for the ordered root `a->b`. Hence

`k_ab = sum_(directed Stokes conormals d) dim mu_d(S_ab)`.       (M)

After tensoring by `Hom(V_a,V_b)`, every coefficient is `dim(V_a)dim(V_b)`. Summing (M) over
Galois orbits and dividing by cover degree gives

`s_ij = (1/N) sum_(a in A_i,b in A_j,d decaying) dim mu_d(S_ab)`.

Thus characteristic-cycle coefficients are integers; rational contact is produced only by
finite-cover normalization. This resolves the former type error.

The equality of singular support is local: for a closed half-interval sheaf on an oriented
one-manifold, sections are constant on the interval and zero outside, so the microlocal Morse cone
is one-dimensional in the outward conormal direction and zero in the opposite direction. Pullback
by a local coordinate in which a simple zero is `u=0` reduces every point to this model.

## 6. Stokes deformation complex and dimension formula

Let `Gdim`, `z`, `h_a`, `s_a`, and `k_a` denote respectively the dimensions of `G`, its centre,
the formal centralizer, the directed Stokes-root microstalk sum, and the prescribed conjugacy
class.  The tangent of the unreduced factor product has dimension

`A=2g Gdim + sum_a(Gdim+h_a+s_a+k_a)`.

Effective moment constraints and effective gauge directions each have dimension

`R=Gdim-z+sum_a h_a`.

At a smooth stable point, write `d_mu:C^A -> C^R` for the surjective moment derivative and
`d_act:C^R -> C^A` for the injective effective gauge derivative. Infinitesimal moment invariance
is `d_mu d_act=0`. The reduced tangent is therefore not an imported dimension formula but the
actual quotient

`T = ker(d_mu)/im(d_act)`.

Rank-nullity gives `dim T=A-2R`, hence

`dim T=2z+(2g-2+m)Gdim+sum_a(s_a+k_a-h_a)`.                 (QH)

The complete three-term deformation complex is

`C^z + C^R --d0--> C^A --d1--> C^R + C^z`,

where `d0` kills the central summand and equals `d_act` on the effective gauge summand, while
`d1(v)=(d_mu(v),0)`. Injectivity and surjectivity give

`dim H^0=z`, `H^1=T`, `dim H^2=z`,

and therefore

`chi Def_St=(2-2g-m)Gdim+sum_a(h_a-s_a-k_a)`.                (EP)

Thus (QH) is derived from the cellular deformation complex. The Stokes-root term `s_a` is the
integer Galois-normalized directed microstalk mass proved in Section 5, not a graph input.

## 7. Rees and corona closure

For every threshold-class cut `e`, set

`z_e(y)=sqrt(ell_e) sum_a y_a 1_e(a)`.

Then the associated-graded map is `y |-> (z_e(y))_e` and

`sum_e z_e(y)^2=E_H(y)`.

A multi-Rees parameter `lambda_e` gives

`E_lambda(y)=sum_e lambda_e z_e(y)^2`.

Unit specialization recovers `E_H`; setting selected `lambda_e` to zero deletes precisely those
graded channels. For all nonnegative parameters the local part remains nonnegative, and the
global term `-(H-1)M^2` is parameter-independent. This proves preservation of the single rank
channel under every Rees specialization.

For boundary coordinates `x`, hidden corona coordinates `y`, and a positive definite hidden block
`D`, write the full energy matrix as

`[[A,B],[B^*,D]]`.

Completing the square gives the exact identity

`E(x,y)=<y+D^{-1}B^*x,D(y+D^{-1}B^*x)>`
`        + <x,(A-BD^{-1}B^*)x>`.                              (SC)

Thus the effective boundary form is exactly the Schur complement, the unique minimizing extension
is `y=-D^{-1}B^*x`, and the hidden residual is the relative vanishing-cycle coordinate with its
positive `D`-metric. Exact minimization composes. Since an exact effective energy is unique,
successive positive corona eliminations are independent of order.

## 8. Novelty boundary

Known ingredients: irregularity as local index; Stokes-direction root counts; irregular
Riemann--Hilbert; ultrametric/fission trees; characteristic-cycle index formula; Schur complements.

Candidate new theorem is their dependency-closed polarization (W) together with (M) and global
self-dual deformation complex: full mixed Euler pairing, not scalar rigidity index, is a positive
microlocal coarea energy plus one boundary-rank line. Falsifier: any published source containing
this exact mixed pairing or any valid twisted Puiseux spectrum whose form has two negative
directions.

## 9. Cellular Stokes category and exact vanishing cycles

The local category is not an analogy. Let `C` be the walking cospan with two arrows
`L -> W <- R`, and set

`Sh_St(C)=Fun(C,Vect_Q)`.

An exponential germ of fiber `V` is the cospan whose wall stalk is `V`, whose two arc stalks are
complementary choices `V` and `0`, and whose incidence maps are respectively the identity and zero
inclusions. For a side `s`, define

`mu_s(F)=F(W)/im(F(s)->F(W))`.

Naturality of a cospan morphism preserves the incidence image, so `mu_s` is a functor, not only a
dimension assignment. The canonical quotient map supplies the exact and right-surjective sequence

`F(s) -> F(W) -> mu_s(F) -> 0`.                                  (VC)

For the exponential germ, one of `mu_L,mu_R` has dimension `dim V` and the other has dimension
zero. Thus microsupport, characteristic-cycle coefficient, and vanishing-cycle rank are three
descriptions of the same categorical quotient in this finite model.

For degree `k>0`, let `C_k` be the cyclic incidence quiver with `2k` wall vertices, `2k` arc
vertices, and two arrows from every arc to its endpoints. No two nonidentity arrows compose, hence
its path category is exactly the entrance-path category of the cellular boundary stratification;
there are no unrecorded higher paths or relations. The global cellular Stokes category is

`Sh_St(S^1;k)=Fun(Path(C_k),Vect_Q)`,

an abelian category. The alternating exponential object has wall dimension `d`, active-arc
dimension `d`, inactive-arc dimension zero, and inclusion incidence maps. Its incidence-quiver
Euler form is

`sum_w d_w^2 + sum_a d_a^2 - sum_(a->w) d_a d_w = k d^2`.        (CE)

This is the categorical source of one positive local channel. Equation (VC) identifies its
integer generators with directed vanishing cycles; finite-cover regrouping gives (M), threshold
coarea gives (W), and the reduction complex gives (EP). The chain

`coefficient difference -> wall -> quotient microstalk -> integer orbit irregularity`
`-> threshold cut -> positive Euler channel`

is therefore dependency-closed at the finite cellular level.

## 10. Nearest-ancestor audit: Hiroe's scalar spectral-curve theorem

Hiroe proves, for irreducible connections whose local HTL forms are multiplicity-free or regular
semisimple and whose spectral curve satisfies additional smoothness assumptions, that the scalar
rigidity index of the endomorphism connection equals the Euler characteristic of the normalized
irregular spectral curve. Locally, his Milnor formula contains
`Irr(End(M))` together with branch and intersection corrections.

This is a genuine ancestor and forbids presenting “irregularity equals an Euler characteristic” as
new. It does not contain the theorem under audit here for four independent reasons:

1. it is scalar and diagonal (`End(M)`), whereas (W) is the polarization on arbitrary independent
   multiplicity vectors and is determined by every mixed `Irr Hom(I,J)`;
2. it assumes a restricted spectral-curve regime, whereas the finite Puiseux-orbit construction
   covers ramified cyclic orbits, loops, and negative diagram multiplicities;
3. it identifies no threshold dendrogram, positive cut channels, capacity wall, or exact
   one-negative-line inertia statement;
4. it supplies no cellular microstalk persistence, Rees-channel law, or corona Schur functoriality.

Accordingly the only defensible novelty target is the **polarized Stokes--microlocal Witt/coarea
law**, not the existence of a scalar irregular Euler index. Any paper version must cite Hiroe next
to the first statement of the new law and state this distinction explicitly.
