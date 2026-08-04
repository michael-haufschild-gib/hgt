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

It is integral: before division by `N`, the sum is invariant under the free cyclic rotation of
ordered pairs, and stabilizer-orbit decomposition gives divisibility by `N`. Equivalently `s_ij`
is the irregularity of the descended exponential Hom local system.

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

If `a!=b`, `phi_ab` has exactly `2 k_ab` simple zeros. The sheaf is locally constant off those
zeros. At each zero its singular support contains exactly one oriented conormal ray and its
microstalk has rank one. Its characteristic cycle is the signed sum of those rays, each with
coefficient one. The `k_ab` conormals on which `exp(q_b-q_a)` is maximally decaying are the Stokes
directions for the ordered root `a->b`; hence

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

Let `L` be a stable Stokes local system on the real oriented blow-up `X~`. Its adjoint deformation
complex is the cellular complex of `ad L` on the interior, with boundary conditions given by the
formal centralizer and, at each singular direction, the directed microstalk root space in (M).
Denote it `Def_St(L)`.

Required theorem, not yet closed:

1. `H^0 Def_St(L)` is the infinitesimal stabilizer.
2. The tangent space to fixed-formal-type Stokes representations modulo gauge is `H^1 Def_St(L)`.
3. Trace pairing and antipodal pairing of roots give a chain-level perfect pairing
   `Def_St(L) ~= Def_St(L)^vee[-2]`.
4. Its cellular Euler characteristic is obtained by cells, so for `G=GL_M`

   `chi Def_St(L)=(2-2g-m)M^2 + sum_a(h_a-s_a-k_a)`,

   where `h_a` is formal-centralizer dimension, `s_a` is the directed microlocal sum above, and
   `k_a` is the conjugacy-class dimension.
5. Stability gives `dim H^0=dim H^2=1`; hence

   `dim H^1=2+(2g-2+m)M^2+sum_a(s_a+k_a-h_a)`.

This derives Boalch's dimension polynomial from the deformation sheaf. Until the chain complex,
pairing, and tangent identification are proved explicitly, global theorem remains open.

## 7. Rees and corona requirements

Required theorem, not yet closed:

- A Rees deformation rescales intervals between successive partitions `Pi_t`. Specialization to
  zero contracts selected intervals. Associated graded is the direct sum of relative block-charge
  channels; (C) shows its quadratic energy is the sum of their positive squared norms.
- For a subtree/corona block with no external singular support except attachment stratum, relative
  cellular cohomology is contractible. Eliminating its cochains by the contraction data produces
  the Schur complement of the positive energy matrix. The attachment microstalk is the relative
  vanishing cycle; its metric is the Dirichlet-to-Neumann effective conductance.

These statements must be proved at chain level, including order-independence of successive
eliminations and preservation of the one-dimensional rank channel.

## 8. Novelty boundary

Known ingredients: irregularity as local index; Stokes-direction root counts; irregular
Riemann--Hilbert; ultrametric/fission trees; characteristic-cycle index formula; Schur complements.

Candidate new theorem is their dependency-closed polarization (W) together with (M) and global
self-dual deformation complex: full mixed Euler pairing, not scalar rigidity index, is a positive
microlocal coarea energy plus one boundary-rank line. Falsifier: any published source containing
this exact mixed pairing or any valid twisted Puiseux spectrum whose form has two negative
directions.
