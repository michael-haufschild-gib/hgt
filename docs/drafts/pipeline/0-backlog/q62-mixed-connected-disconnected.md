# Q6.2 — Mixed Connected/Disconnected Bottcher Independence

- **ID:** q62-mixed-connected-disconnected
- **Stage:** 0-backlog
- **Type:** THEOREM CANDIDATE / PROVED HERE
- **Source:** Nguyen arXiv:1310.2329 Question 6.2; extends the connected and both-disconnected Q6.2 cards
- **Statement:** If `a in M \ {0,-2}` and `b notin M`, then the inverse Bottcher coordinates
  `phi_a(z)` and `phi_b(z)` are algebraically independent over `C(z)`, hence over `Qbar(a,b,z)`.

## Anti-Theatre Gate

No computation is useful for this claim. The possible failure is not numerical. It is whether the
monodromy loop for the disconnected coordinate is reachable from the common infinity germ while
the connected coordinate stays single-valued. The proof must therefore supply a continuation-domain
topology statement, not a finite Laurent or sampling test.

## Proof

Let `f_c(z)=z^2+c`, let `K_c` be the filled Julia set, `J_c=partial K_c`, and let `G_c` be the
escape-rate Green function. For `a in M`, `K_a` is connected and `phi_a` is single-valued on
`Omega_a=C\K_a`. For `b notin M`, `K_b=J_b` is a Cantor compactum and `phi_b` is single-valued
only on the outer Bottcher domain `Delta_b={G_b>G_b(0)}`, but it has multivalued analytic
continuation on `Omega_b=C\K_b`.

Assume for contradiction that

`P(z, phi_a(z), phi_b(z))=0`

for a nonzero polynomial `P in C[z,Y,W]`, on the common germ near infinity.

If `P` has degree zero in `W`, then `phi_a` is algebraic over `C(z)`, contradicting
Becker--Bergweiler/Fernandes for nonexceptional connected parameter `a`. Hence take `d=deg_W P>0`.

### Step 1: `K_b` is not contained in `K_a`

Suppose `K_b subset K_a`. Both filled Julia sets have logarithmic capacity `1`, so their equilibrium
energy is the same. The equilibrium measure of `K_b` is then also an energy minimizer among probability
measures on `K_a`; by uniqueness of the equilibrium measure, `mu_b=mu_a`.

For polynomials, the potential-theoretic equilibrium measure of the filled Julia set is Brolin's
canonical/maximal-entropy measure and has support `J_c`. Since `b notin M`, `J_b=K_b` is a Cantor set.
Since `a in M`, `J_a` is connected. Equality of measures would force equality of supports:

`K_b = supp(mu_b) = supp(mu_a) = J_a`,

which is impossible because a Cantor set is totally disconnected and `J_a` is connected. Thus
`K_b notsubset K_a`.

Choose `z0 in K_b \ K_a`. Then `G_a(z0)>0`.

### Step 2: reachable disconnected branch points

The branch points of the multivalued inverse Bottcher coordinate `phi_b` are the preimages
`f_b^{-n}(0)`. They accumulate on `K_b=J_b`. Since `G_a(z0)>0` and `Omega_a` is open, all sufficiently
nearby branch points of `phi_b` lie in `Omega_a cap Omega_b`.

The branch point also has to lie in the same continuation component as the infinity germ. This is the
topology gate: inside the domain `Omega_a`, the relatively closed set `K_b cap Omega_a` is zero-dimensional.
A relatively closed zero-dimensional subset of a plane domain does not disconnect it. Therefore

`Omega_a cap Omega_b = Omega_a \ K_b`

is path-connected. After deleting the countable discrete branch loci of `phi_b`, paths from infinity to a
punctured neighborhood of the chosen branch point still exist by small perturbation.

Choose a branch point

`p in f_b^{-n}(0) cap Omega_a`

with `2^n>d`, reached by such a path, and choose a small loop around `p` avoiding branch points of the
continued functions except `p`.

### Step 3: monodromy degree contradiction

Analytically continue the relation along the path to a basepoint near `p`. The connected-coordinate
`phi_a` has no monodromy on `Omega_a`. A loop around `p in f_b^{-n}(0)` multiplies the continued branch
of `phi_b` by `exp(2*pi*i/2^n)`. Therefore, at the same basepoint,

`P(z, phi_a(z), exp(2*pi*i*k/2^n) phi_b(z))=0`

for `k=0,...,2^n-1`. Since `phi_b(z) != 0` on `Omega_b`, these are `2^n>d` distinct roots in the
`W`-variable of the degree-`d` polynomial `P(z,phi_a(z),W)`. Hence all `W`-coefficients vanish after
substitution `Y=phi_a(z)`.

Those coefficient identities make `phi_a` algebraic over `C(z)` unless all coefficients are zero
identically. Becker--Bergweiler/Fernandes exclude algebraicity of `phi_a`, so every coefficient is
identically zero and `P=0`, contradiction.

Therefore `phi_a` and `phi_b` are algebraically independent over `C(z)`.

## Dependencies to Audit

- Becker--Bergweiler/Fernandes: nonexceptional rational Bottcher/Schroeder functions are not algebraic
  and in fact hypertranscendental.
- Equilibrium uniqueness for nonpolar compact plane sets.
- Polynomial equilibrium measure equals Brolin/maximal-entropy measure and has support `J_c`.
- `b notin M` implies `K_b=J_b` is Cantor; `a in M` implies `J_a` is connected.
- Topology gate: a relatively closed zero-dimensional subset of a plane domain does not disconnect it.
- Standard Bottcher monodromy: a loop around `f_b^{-n}(0)` multiplies the inverse Bottcher branch by a
  `2^n`-th root of unity.

## Relation to Existing Cards

- `q62-bottcher-independence-natural-boundary.md` proves the connected/connected case.
- `q62-both-disconnected.md` now proves the disconnected/disconnected case, pending team acceptance of the
  same zero-dimensional continuation-component gate.
- This card closes the missing mixed connected/disconnected case by using monodromy on the disconnected
  coordinate and single-valuedness of the connected coordinate.

## Grade

If the topology gate is accepted, this completes the `n=2` inverse-Bottcher Q6.2 theorem across all parameter
placements:

`c1 != c2`, `c_i notin {0,-2}` implies `phi_c1` and `phi_c2` are algebraically independent over `C(z)`.

Significance: high for Nguyen Q6.2 / inverse-Bottcher independence. It is still cross-method complex dynamics
and algebraic continuation, not a native archimedean-prime weld apex.

## 2026-06-24 topology-gate source closure

The relative path-connectedness claim in Step 2 is source-backed by the classical Mazurkiewicz theorem. A convenient modern reference is Krupski--Valov, `Mazurkiewicz manifolds and homogeneity`, arXiv:0901.1329: the introduction recalls that Mazurkiewicz proved regions, i.e. open connected subsets of Euclidean spaces and topological manifolds, cannot be cut by subsets of codimension at least two; their Theorem 4 strengthens this to suitable `F_sigma` subsets.

Apply this with the planar region `Omega_a`. The removed set is `(K_b cap Omega_a)` plus the countable branch loci to be avoided. This is an `F_sigma` subset of covering dimension `0`: `K_b` is a Cantor compactum and the branch loci are countable isolated point sets with accumulation only on the removed Cantor/boundary. Since planar codimension is at least two, Mazurkiewicz gives a continuum, hence a path after standard local connectedness refinement in the complement, connecting the infinity germ to the chosen punctured branch neighborhood.

Thus the mixed-case monodromy loop is genuinely reachable. The proof no longer depends on a visual crossing assumption.

### Path refinement for analytic continuation

Mazurkiewicz supplies a continuum in the complement rather than explicitly naming a path. This is enough for analytic continuation. Given small closed disks around the infinity-germ basepoint and a punctured neighborhood of the selected branch point, apply the no-cut theorem inside `Omega_a` to obtain a continuum in the complement meeting both disks. Since that continuum is compact and lies in an open plane domain, it has a finite connected cover by disks with closures still in the domain. A chain through overlapping disks gives a polygonal path in the continuation domain. Therefore the standard path-based analytic continuation and monodromy argument applies.

## 2026-06-24 monodromy audit — proof not promoted

This card is **not promoted** as written. The Step 3 sentence

`a loop around p in f_b^{-n}(0) multiplies phi_b by exp(2*pi*i/2^n)`

fails the local-model check for the direct/inverse-Bottcher convention used in these notes, where
`phi_c(f_c(z))=phi_c(z)^2`. Near a basin precritical point `p`, after enough iteration one writes a local
branch as a root of a nonzero analytic function. A sufficiently small loop around `p` therefore need not wind
around `0` in the Böttcher coordinate and need not produce the claimed root-of-unity monodromy.

The plausible replacement is not a small loop around `p`, but a loop in the basin around a depth-`n` Cantor
or puzzle component of `K_b`. In the external-coordinate/log-Böttcher picture such a loop should have dyadic
period `2*pi*i/2^n`, giving multiplier `exp(2*pi*i/2^n)`. That is a different lemma and must be proved or
sourced before the mixed disconnected proof can be banked.

Current status: **OPEN at monodromy gate**. The capacity/topology reachability work remains useful, but the
degree contradiction is not established until the dyadic component-loop monodromy lemma is written with the
correct domain and path.

## 2026-06-24 repair candidate — harmonic-measure period loop

A plausible repair of the monodromy gate is the following component-loop lemma.

**Lemma candidate.** Let `c notin M`, let `phi_c` be the Böttcher coordinate germ with
`phi_c(f_c(z))=phi_c(z)^2`, and let `C_w` be a depth-`n` symbolic cylinder in the Cantor Julia set
`K_c`. If `gamma` is a loop in `Omega_c=C\K_c` enclosing `C_w` and no other depth-`n` cylinder, then analytic
continuation of `phi_c` along `gamma` multiplies the branch by `exp(2*pi*i/2^n)`.

Reason: locally write `log phi_c = G_c + iG_c^*`. The period of `d(log phi_c)` around a loop enclosing a
clopen piece `C_w` of the boundary is `2*pi*i` times harmonic measure at infinity of `C_w`. For a quadratic in
the shift locus, harmonic measure equals Brolin's maximal-entropy measure on `K_c`, and the depth-`n` symbolic
cylinders have mass `2^-n`. Hence the period is `2*pi*i/2^n`, giving the multiplier above.

If this lemma is accepted, the mixed proof should be rewritten as follows. Choose `z0 in K_b\K_a` and a disk
`D subset Omega_a` around `z0`. Because `K_b` is Cantor, for arbitrarily large `n` there is a depth-`n`
cylinder `C_w subset K_b cap D`. A loop around `C_w` lies in `Omega_a cap Omega_b`, is reachable from the
infinity germ by the zero-dimensional non-cutting gate, leaves `phi_a` single-valued, and multiplies `phi_b`
by a primitive `2^n`-th root. Taking `2^n > deg_W P` restores the degree contradiction.

Status: **candidate repair, pending audit of the period/harmonic-measure lemma and path placement.**

## 2026-06-24 period lemma proved — mixed proof repaired pending team audit

The repair candidate above is valid after replacing the informal branch-point language by the complex-potential period calculation.

### Component-loop period lemma

Let `c notin M`, `K_c=J_c` be the Cantor Julia set, `Omega_c=C\K_c`, and let `mu_c` be the equilibrium measure of `K_c`. Let `C_w` be a depth-`n` symbolic cylinder in `K_c`, using the conjugacy of `f_c|K_c` with the full one-sided two-shift.

There is a closed curve, or finite product of closed curves based at the same point, in `Omega_c` whose winding number is `1` on `C_w` and `0` on `K_c\C_w`. This is a standard planar separation fact for a clopen subset of a zero-dimensional compactum: take a finite neighborhood of `C_w` with closure disjoint from `K_c\C_w`, and use its oriented boundary.

On `Omega_c`, the normalized Böttcher germ satisfies

`log phi_c(z) = int log(z-zeta) dmu_c(zeta)`

up to the branch chosen near infinity. Equivalently,

`d log phi_c = int dz/(z-zeta) dmu_c(zeta)`.

Therefore the period around the separating curve `gamma` is

`int_gamma d log phi_c = int_K (int_gamma dz/(z-zeta)) dmu_c(zeta)
 = 2*pi*i int_K Ind(gamma,zeta) dmu_c(zeta)
 = 2*pi*i mu_c(C_w)`.

For `c notin M`, the map is in the quadratic shift locus. De Marco's shift-locus theorem records that `f_c|K_c` is conjugate to the one-sided two-shift. The Brolin-Lyubich/equilibrium measure is the harmonic measure of the basin of infinity and is the measure of maximal entropy; under the full two-shift coding it is the fair Bernoulli measure. Hence every depth-`n` cylinder has mass `2^-n`.

Thus continuation around `gamma` changes the logarithm by `2*pi*i/2^n`, and changes the Böttcher coordinate by

`phi_c -> exp(2*pi*i/2^n) phi_c`.

This proves the needed dyadic monodromy. The earlier small-loop-around-`f^{-n}(0)` statement remains invalid; the monodromy comes from a loop around a clopen Julia cylinder.

### Repaired mixed proof

In the mixed case, Step 1 gave `z0 in K_b\K_a`, hence a disk `D subset Omega_a` around `z0`. Since `K_b` is a Cantor repeller and symbolic cylinders shrink to points, choose, for arbitrarily large `n`, a depth-`n` cylinder `C_w subset K_b cap D`. By planar separation, choose the component-loop `gamma` inside `D\K_b subset Omega_a cap Omega_b`.

The zero-dimensional non-cutting gate connects the infinity germ to a basepoint of `gamma` inside `Omega_a cap Omega_b`; no precritical local branch point is needed. Along `gamma`, the connected-coordinate `phi_a` is single-valued on `Omega_a`, while the period lemma gives

`phi_b -> exp(2*pi*i/2^n) phi_b`.

Taking `2^n > deg_W P`, the same degree contradiction from Step 3 is now valid with `C_w` in place of the precritical point `p`.

Current status: **proof repaired as a theorem candidate; pending independent team audit/source-newness vote before moving to `2-fully-proven`.**

### Source-newness note after period repair

Narrow source search for Nguyen Q6.2 / inverse-Böttcher algebraic independence still surfaces Nguyen's question itself and adjacent value/small-orbit literature, not a theorem proving this function-field relation for distinct quadratic parameters.

Relevant support, not a source-kill: Harry Schmidt, `Polynomial dynamics and local analysis of small and grand orbits`, Compositio Mathematica 159 (2023), §6 studies monodromy for disconnected Julia sets and proves that continuations of the inverse Böttcher uniformization have high-order root-of-unity monodromy. This independently confirms that the disconnected case is controlled by monodromy, but Schmidt's statements concern relations on one polynomial's small/grand-orbit uniformization, not the relation `P(z,phi_a(z),phi_b(z))=0` between two parameter fibers.

Thus the repair is source-supported and still appears source-new for Nguyen Q6.2 n=2, pending team audit.

## 2026-06-24 local-vs-topological monodromy correction

Further correction: for the direct Böttcher coordinate convention used in these cards,

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)/z -> 1`,

escaping precritical points in `Omega_c` should not be treated as the load-bearing local branch points of `phi_c`. Locally near such a point, a branch can be represented as a root of a nonzero analytic function, so the branch is locally analytic after a choice of root. The relevant multivaluedness is period/topology-based: `d log phi_c` is a single-valued holomorphic differential on `Omega_c` whose periods around removed Julia-set pieces are nonzero.

Thus the maintained proof is the component-loop proof only. Any earlier sentence saying that a small loop around `f_c^{-n}(0)` gives the required monodromy is retired, except as source-history of the failed attempt.

## 2026-06-24 superseded by aggregate theorem

This backlog card is retained as a development log. Its early branch-point/small-loop proof attempt is retired.
The maintained mixed-case proof is now part of
`../2-fully-proven/q62-bottcher-independence-n2-all-parameters.md`, using the exact Cantor-cylinder period
monodromy theorem `../2-fully-proven/bottcher-exact-pruefer-monodromy.md` and the one-coordinate monodromy
obstruction `../2-fully-proven/unbounded-one-coordinate-monodromy-obstruction.md`.

Current status of the mixed case: **proved as a subcase of the aggregate theorem**.
