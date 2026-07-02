I prove a slightly stronger statement: **under the stated hypotheses, no exceptional pairs occur, and in fact either index can be used.** That is, for each (i\neq j) there is a one-sided point
[
x\in J_{c_i}\setminus K_{c_j}
\quad\text{with}\quad
x\in \partial W .
]
This is stronger than the requested “possibly after exchanging the indices” conclusion. The requested target is exactly the point described in the file: (x\in J_{c_1}), (x\notin K_{c_2}), and (x\in\partial W).

## Standard theorem used

I use the following classical form of the Fatou–Lindelöf–Zdunik/Zakeri biaccessibility theorem.

**Theorem.** Let (c\in M\setminus{-2}), and let (\mu_c) be the equilibrium, equivalently harmonic, measure of (K_c) seen from infinity. Then the set of one-sided points of (J_c) has full (\mu_c)-measure.

Here “one-sided” is in the local sense of the problem: for all sufficiently small (\rho>0),
[
B(p,\rho)\setminus K_c
]
is connected. The Chebyshev case (c=-2), where (K_c=[-2,2]), is exactly the excluded case in which typical points have two exterior sides. The disk case (c=0) is harmless for this theorem, but it is also excluded in the problem statement.

A standard proof is: Fatou’s theorem gives radial landing of external rays for harmonic-measure-a.e. boundary point; the Lindelöf access theorem identifies distinct local accesses with distinct landing external rays; and Zdunik’s theorem says that, for a polynomial with connected Julia set, the set of biaccessible boundary points has harmonic measure zero unless the polynomial is Chebyshev. For (z^2+c), the Chebyshev parameter is (c=-2).

The problem statement permits standard results from polynomial dynamics, plane topology, and potential theory to be used.

---

## Proof

Write
[
K_i=K_{c_i},\qquad J_i=J_{c_i},\qquad G_i=G_{c_i},\qquad \mu_i=\mu_{c_i}
]
for (i=1,2). Each (K_i) is compact, full, connected, has logarithmic capacity (1), and has continuous Green function (G_i) vanishing exactly on (K_i).  Also (K_1\neq K_2), because distinct parameters have distinct filled Julia sets.

Let
[
X=K_1\cup K_2,
]
and let (W) be the unbounded component of (\mathbb C\setminus X), as in the statement.  Put
[
Y=\mathbb C\setminus W.
]
Thus (Y) is the filled-in hull of (X): it is (X) together with all holes of (X). Its outer boundary is (\partial W).

### 1. The outer hull has capacity strictly larger than (1)

First observe that neither (K_1\subset K_2) nor (K_2\subset K_1) can hold. Indeed, suppose for example that (K_2\subsetneq K_1). Choose (a\in K_1\setminus K_2). Since (K_2) is closed, there is a small disk (D) about (a) with (\overline D\cap K_2=\varnothing). The set (K_1\cap \overline D) has positive logarithmic capacity: if (a\in \operatorname{int}K_1), this is immediate from the presence of a small disk; if (a\in J_1), it follows because (\mu_1) has full support on (J_1).

Now use a standard strict monotonicity argument for logarithmic capacity. Let (E) be a compact set of capacity (1), let (A\subset \mathbb C\setminus E) be compact of positive capacity, and assume (G_E>0) on (A). Let (\mu_E) be the equilibrium measure of (E), and choose a probability measure (\sigma) of finite logarithmic energy supported on (A). With the convention
[
I(\nu)=\iint \log \frac1{|z-w|},d\nu(z)d\nu(w),
]
we have (I(\mu_E)=0), because (\operatorname{cap}(E)=1), and
[
I(\mu_E,\sigma)=\int U^{\mu_E},d\sigma
======================================

-\int G_E,d\sigma
<0 .
]
Therefore, for small (t>0),
[
I\bigl((1-t)\mu_E+t\sigma\bigr)
===============================

(1-t)^2 I(\mu_E)
+2t(1-t)I(\mu_E,\sigma)
+t^2I(\sigma)
<0.
]
Hence the Robin constant of (E\cup A) is negative, so
[
\operatorname{cap}(E\cup A)>1.
]

Applying this with (E=K_2) and (A\subset K_1\setminus K_2) gives
[
\operatorname{cap}(K_1)>1,
]
contradicting (\operatorname{cap}(K_1)=1). Thus (K_2\not\subset K_1), and symmetrically (K_1\not\subset K_2).

In particular, (K_2\setminus K_1) contains a compact subset of positive capacity lying in (\mathbb C\setminus K_1). Applying the same strict monotonicity argument with (E=K_1) gives
[
\operatorname{cap}(K_1\cup K_2)>1.
]
Since (Y\supset K_1\cup K_2), monotonicity of capacity gives
[
R:=\operatorname{cap}(Y)>1.
]

### 2. The exposed part of each Julia set has positive harmonic measure

Let (\mu_Y) be the equilibrium measure of (Y). Since (Y) is the filled hull of (X), (\mu_Y) is the harmonic measure of (W) seen from infinity, and it is supported on (\partial W).

For (i=1,2), the standard energy identity gives
[
\int G_i,d\mu_Y=\log \operatorname{cap}(Y)=\log R.
]
Indeed, since (\operatorname{cap}(K_i)=1), the Green function satisfies
[
G_i=-U^{\mu_i},
]
where (\mu_i) is the equilibrium measure of (K_i). By Fubini,
[
\int G_i,d\mu_Y
===============

# -\iint \log\frac1{|z-w|},d\mu_i(w)d\mu_Y(z)

-\int U^{\mu_Y}(w),d\mu_i(w).
]
Because (\mu_i) is supported on (K_i\subset Y), and (U^{\mu_Y}=-\log R) quasi-everywhere on (Y), this equals (\log R).

Now take (i=2). Since (R>1),
[
\int G_2,d\mu_Y=\log R>0.
]
But (G_2=0) exactly on (K_2), while (G_2>0) on (\mathbb C\setminus K_2). Also (\mu_Y) is supported on (\partial W\subset K_1\cup K_2). Hence
[
\mu_Y(\partial W\setminus K_2)>0.
]
Set
[
E_1:=\partial W\setminus K_2.
]
Then (E_1\subset K_1). Moreover (E_1\subset J_1), because no point of (\operatorname{int}K_1) can lie on (\partial W). Thus
[
E_1\subset J_1\setminus K_2
]
and
[
\mu_Y(E_1)>0.
]

Now compare harmonic measures in the nested domains
[
W\subset \Omega_1:=\mathbb C\setminus K_1.
]
The set (E_1) is a common boundary portion of (W) and (\Omega_1). By domain monotonicity of harmonic measure,
[
\omega_W(\infty,E_1)\le \omega_{\Omega_1}(\infty,E_1).
]
But
[
\omega_W(\infty,\cdot)=\mu_Y,
\qquad
\omega_{\Omega_1}(\infty,\cdot)=\mu_1.
]
Therefore
[
\mu_1(E_1)\ge \mu_Y(E_1)>0.
]

So the exposed set
[
E_1=\partial W\setminus K_2\subset J_1\setminus K_2
]
has positive equilibrium measure for (K_1).

### 3. Choose a one-sided point in the exposed set

By the one-sided full-measure theorem quoted above,
[
\mu_1({\text{one-sided points of }J_1})=1.
]
Since (\mu_1(E_1)>0), the intersection
[
E_1\cap {\text{one-sided points of }J_1}
]
is nonempty.

Choose
[
x\in E_1
]
that is one-sided for (K_1). Then, by definition of (E_1),
[
x\in \partial W,
\qquad
x\notin K_2,
\qquad
x\in J_1.
]
Thus (x) is exactly the desired one-sided boundary point visible from infinity.

The same argument with the indices reversed gives a one-sided point of (J_2\setminus K_1) on (\partial W). Hence no exceptional pairs occur under the stated assumptions (c_1\neq c_2\in M\setminus{0,-2}).

---

# Verification report (2026-07-02)

## Verdict

**Steps 1–2 are correct and are new, load-bearing progress: the exposed set
`E₁ = ∂W ∖ K₂ ⊆ J₁ ∖ K₂` carries positive equilibrium measure, `μ₁(E₁) ≥ μ_Y(E₁) > 0`, and
simultaneously for both orderings.**  This settles the caution in weakening (W2)
measure-theoretically: `∂W ∖ K₂` is not merely nonempty, it is μ-large.

**Step 3 has a gap and the strict Problem statement remains open.**  The quoted
"one-sided full measure theorem" is stronger than what the cited literature provides.

## Audit of steps 1–2 (verified)

1. *Strict capacity monotonicity* — correct.  For compact `E` of capacity 1 and compact
   `A ⊆ ℂ ∖ E` of positive capacity with `G_E > 0` on `A`, the mixture
   `(1−t)μ_E + tσ` has negative energy for small `t` because the cross term
   `I(μ_E, σ) = −∫ G_E dσ < 0` dominates; hence `cap(E ∪ A) > 1`.  Applied twice this
   gives `K₂ ⊄ K₁`, `K₁ ⊄ K₂` (using `cap(K_i) = 1` and that distinct parameters have
   distinct filled Julia sets), then `R := cap(Y) ≥ cap(K₁ ∪ K₂) > 1`.  The positive-capacity
   input (`K₁ ∩ D̄` for `a ∈ J₁`) is sound: `supp μ₁ = J₁` (Brolin), and a restriction of a
   finite-energy measure has finite energy.
2. *Energy identity* — correct.  `G_i = −U^{μ_i}` off a polar set (capacity 1, Robin
   constant 0), `U^{μ_Y} = −log R` q.e. on `Y ⊇ K_i`, and `μ_i` charges no polar set
   (finite energy), so Fubini gives `∫ G_i dμ_Y = log R > 0`.  Since `G₂ = 0` exactly on
   `K₂` and `μ_Y` is carried by `∂W ⊆ K₁ ∪ K₂`, positivity forces `μ_Y(∂W ∖ K₂) > 0`.
   `∂W ∖ K₂ ⊆ J₁` is sound (interior points of `K₁` cannot lie on `∂W`).
3. *Domain monotonicity* — correct.  `E₁` is relatively open in `∂W` (complement of the
   closed `K₂`), hence Borel; `W ⊆ Ω₁ = ℂ ∖ K₁` share the boundary portion `E₁ ⊆ ∂W ∩ J₁`,
   and `ω_W(∞,·) ≤ ω_{Ω₁}(∞,·)` on common boundary portions by the maximum principle.
   Hence `μ₁(E₁) ≥ μ_Y(E₁) > 0`.

## The gap in step 3

Fatou (radial landing a.e.), Lindelöf (accesses ↔ landing rays), and Zdunik/Zakeri/Smirnov
(biaccessible points have zero harmonic measure unless Chebyshev) together give:

> for `c ∉ {0, −2}`, μ_c-a.e. point of `J_c` is the landing point of **exactly one** external
> ray — equivalently, has **exactly one access** from `ℂ ∖ K_c`.

The Problem's definition of one-sided is strictly stronger: `B(p,ρ) ∖ K_c` **connected for
every** small `ρ`.  Uniaccessibility does not imply it.  A comb (a full compact set: a base
segment with teeth accumulating on a limit tooth) has its limit endpoint uniaccessible while
every small ball around it is sliced into infinitely many components by the neighboring
teeth: **accumulation without access**.  Access-counting is blind to strands of `K₁` (or, in
the pair setting, to holes of `K₁ ∪ K₂`) that accumulate at a point at all scales without
contributing an access there.  Nothing in the cited biaccessibility literature excludes this
configuration at μ-a.e. point, and its exclusion is exactly the open content of the Problem.
So the selection "μ₁(E₁) > 0 ∧ one-sided μ₁-a.e. ⟹ a one-sided point in E₁" rests on an
unproven premise.  The Problem as stated (and its consumer, the strict hole-free-ball
certificate) remains open.

**Sharpened residual question (new, and of independent interest):** for `c ∈ M ∖ {0,−2}`, is
μ_c-a.e. point of `J_c` one-sided in the strict ball sense?  Equivalently: can strands of a
quadratic Julia set accumulate, at positive harmonic measure many of its points, at all
scales, without access?  A comb shows general full compacta allow it; self-similarity of
`J_c` and the Makarov–Zdunik twist-point theory are the natural tools against it.

## What the verified part already buys (the measure route)

The application consuming this Problem was re-examined against the verified steps 1–2, with
two consequences (recorded here so the answer file is self-contained about its own impact):

1. **The formal rigidity interface was strengthened (Lean, done).**  The engine that turns a
   Böttcher relation into a smooth Julia piece now carries two extra certified clauses: the
   piece is a full Julia-ball piece `S = J₁ ∩ closedBall(z₁, ρ₂)`, and **no constant unit root**:
   no `ζ` with `|ζ| = 1` kills the fibre polynomial identically on `ℂ ∖ K₂` (proved from
   irreducibility of the minimal relation, transcendence of `φ_{c₂}`, and `‖φ_{c₁}‖ > 1` on
   the escape region).  Without these clauses the rigidity endgame was refutable by
   artificial instantiations (a singleton piece, or a constant unit branch) and could never
   have been proven.
2. **A measure-quantified variant of the endgame is the designated consumer of THIS answer**
   `[CONJECTURE — route, citations to be pinned]`: from `μ₁(E₁) > 0`, pick
   `x ∈ E₁ ∩ supp μ_Y` and take the piece `F := supp μ_Y ∩ closedBall(x, δ)` with
   `δ < dist(x, K₂)`.  Every point of `supp μ_Y ⊆ ∂W` is a limit of escaping points, so the
   relation propagates to all of `F` (no hole-free ball needed); `μ_Y` is non-atomic (finite
   energy), so `F` is uncountable and every relatively open piece of `F` has positive
   `μ_Y`-, hence `μ₁`-measure.  The measure pigeonhole then puts a positive-`μ₁` subset of
   `J₁` inside the modulus-one locus of one analytic root branch — a rectifiable set.  By
   Bishop–Jones (positive harmonic measure on a rectifiable curve forces a positive-measure
   set of cone points) against Przytycki–Urbański–Zdunik / Makarov–Zdunik (for
   `c ∉ {0,−2}`, μ_c-a.e. point is a twist point), this is impossible.  The two bracketed
   citations are load-bearing and must be verified before this route is promoted; if they
   hold, steps 1–2 of this answer discharge the both-connected case without the strict
   one-sided selection ever being needed.
