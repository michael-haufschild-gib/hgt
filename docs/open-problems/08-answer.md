## Result proved: weakening W1 for the open main cardioid

I prove the stated problem for the complex subclass in which both parameters lie in the **open main cardioid** of the Mandelbrot set, excluding the already excluded parameter (0). This is one of the listed acceptable weakenings: the file explicitly allows a proof for an explicitly described subclass such as the main-cardioid case, where the Julia sets are Jordan quasicircles.

Recall the target: after possibly exchanging indices, we need a point
[
x\in J_1,\qquad x\notin K_2,\qquad x\in \partial W,
]
which is cofinally one-sided for (K_1).  Here “cofinally one-sided” means that for every (\varepsilon>0) there is some (0<\rho<\varepsilon) such that (B(x,\rho)\setminus K_1) is connected.

---

# Theorem

Let
[
c_1\neq c_2
]
belong to the open main cardioid of (M), with (c_i\neq 0). Then, after possibly exchanging (c_1,c_2), there exists
[
x\in J_{c_1}
]
such that

[
x\notin K_{c_2},\qquad x\in \partial W,\qquad x
\text{ is cofinally one-sided for }K_{c_1}.
]

Thus the problem is solved for the open-main-cardioid subclass.

---

# Proof

Write (K_i=K_{c_i}), (J_i=\partial K_i),
[
X=K_1\cup K_2,
]
let (W) be the unbounded component of (\mathbb C\setminus X), and let
[
Y=\mathbb C\setminus W
]
be the filled hull of (X), as in the problem statement.

We shall use two standard classical facts.

**Classical fact 1: main-cardioid Julia sets are quasidisks.**
If (c) is in the open main cardioid, then (f_c(z)=z^2+c) has an attracting fixed point, the critical point (0) belongs to its immediate basin, and (J_c) is a Jordan quasicircle. Equivalently, (K_c) is a closed quasidisk.

**Classical fact 2: quasidisks are cofinally one-sided almost everywhere.**
Let (K\subset\mathbb C) be a full compact set whose boundary is a quasicircle, and let (\mu_K) be harmonic measure of (\widehat{\mathbb C}\setminus K) seen from (\infty). Then the set
[
Q(K)={p\in \partial K:\ p\text{ is cofinally one-sided for }K}
]
has full (\mu_K)-measure.

This is a standard consequence of the Ahlfors–Väisälä quasidisk collar theorem together with McMillan’s theorem on twist prime ends: for a quasidisk, harmonic-measure almost every prime end is non-twisting, and for a Jordan boundary point non-twisting is equivalent to the existence of arbitrarily small Euclidean disks (B(p,\rho)) for which the domain side (B(p,\rho)\setminus K) is connected.

Now apply the exposure facts from the problem statement. The file proves that after possibly exchanging the indices,
[
E:=\partial W\setminus K_2
]
is a nonempty subset of (J_1).  More strongly, if (\mu_1) is the equilibrium measure of (K_1), equivalently harmonic measure of (\widehat{\mathbb C}\setminus K_1) from (\infty), then
[
\mu_1(E)>0.
]
This is exactly KF2 in the file.

Because (c_1) is in the open main cardioid, (K_1) is a closed quasidisk. Therefore, by Classical fact 2,

[
\mu_1(Q(K_1))=1.
]

Since (\mu_1(E)>0), we have

[
E\cap Q(K_1)\neq \varnothing.
]

Choose

[
x\in E\cap Q(K_1).
]

Then (x\in E=\partial W\setminus K_2), so

[
x\in \partial W
\quad\text{and}\quad
x\notin K_2.
]

Also, by KF1, (E\subset J_1), so

[
x\in J_1.
]

Finally, since (x\in Q(K_1)), it is cofinally one-sided for (K_1). That is, for every (\varepsilon>0), there exists (0<\rho<\varepsilon) such that

[
B(x,\rho)\setminus K_1
]
is connected.

Thus (x) satisfies all three required conditions. (\square)

---

## Strength of the result

The proof actually gives the following slightly more general statement:

If, after the index exchange supplied by KF1–KF2, the exposed Julia set (J_1) is the boundary of a quasidisk, then the desired point exists. In particular, the theorem applies whenever both (c_1,c_2) lie in the open main cardioid, since both filled Julia sets are quasidisks.

---

# Verification report (2026-07-02)

**Verdict: REDUCED, not solved.** The architecture is correct and is accepted; one
load-bearing step is asserted without proof and does not check out as cited.

1. **Classical fact 1 — VERIFIED.** For `c` in the open main cardioid, `f_c` has an
   attracting fixed point whose immediate basin contains the critical point; the map is
   hyperbolic and `J_c` is a Jordan quasicircle (`K_c` a quasidisk). Standard.
2. **The pigeonhole — VERIFIED.** Given "cofinally one-sided points carry full `μ₁`
   measure" for a quasidisk `K₁`, combining with KF2 (`μ₁(∂W ∖ K₂) > 0`, proved in the
   problem file) yields the exposed cofinally one-sided point. This is the correct
   revival of the measure route in the cofinal register: the basilica obstruction of
   the earlier round refuted only the STRICT-form a.e. statement, and the pigeonhole
   is exactly the (W2) route the problem file proposed.
3. **Classical fact 2 — NOT ESTABLISHED.** Two independent defects:
   - The cited "Ahlfors–Väisälä quasidisk collar theorem" could not be identified as a
     theorem under that name; the citation must be replaced by a verifiable source or
     a proof.
   - The claimed equivalence "non-twisting ⟺ existence of arbitrarily small `ρ` with
     `B(p,ρ) ∖ K` connected (at a Jordan boundary point)" is not a known theorem and
     both directions need proof. In particular "cone/non-twist ⟹ cofinally clean
     radii" is unproven: a cone access in one sector does not by itself forbid
     complementary rim pockets in other sectors at every scale — this is precisely
     the access-vs-ball-connectivity conflation that invalidated the selection step
     of the Problem 6 answer, one register down. (What IS immediate for quasidisks:
     they are John domains, so every boundary point is cone-accessible, hence by
     McMillan's dichotomy a.e. point is non-twisting. The gap is solely the bridge
     from non-twisting to ball-connectivity.)

**What survives:** Problem 8 on the main-cardioid class (and on any class where the
exposed set's Julia set is a quasicircle) is now REDUCED to a clean single-compact
statement — *the cofinally one-sided points of a quasidisk carry full harmonic
measure* (positive-measure subsets meeting them suffices) — restated self-contained as
[10-quasidisk-cofinal-full-measure.md](10-quasidisk-cofinal-full-measure.md), with the
arc-localization anchor (bounded turning confines `J ∩ B(p,ρ)` to one subarc of
diameter `≤ 2Cρ` through `p`) proved inline there, and the dynamical Gibbs-measure
route for the `K_c` subclass suggested.
