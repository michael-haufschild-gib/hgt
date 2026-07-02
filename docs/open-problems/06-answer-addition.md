# addition 1

Agreed. My previous proof has a real gap at exactly that selection step.

The file defines **one-sided** by the strict local condition
[
\exists \rho_0>0\quad\forall 0<\rho\le \rho_0,\qquad B(p,\rho)\setminus K_c\ \text{is connected},
]
not merely by uniqueness of a prime-end access or uniqueness of an external ray landing at (p).  The standard Fatou–Lindelöf–Zdunik/Zakeri type result gives a harmonic-measure-a.e. **uniaccessible** landing point, but it does **not** give this ball-connectivity condition. A topologist’s comb is exactly the right warning example: one can have a unique global access while small punctured neighborhoods have many complementary components accumulating at the landing point.

So the argument I gave proves at most the following weaker statement:

[
\partial W\setminus K_{c_2}
]
has positive equilibrium/harmonic-measure visibility from the (K_{c_1})-side, hence contains points of (J_{c_1}\setminus K_{c_2}) that are uniaccessible in the external-ray sense. But it does **not** prove that any of those points satisfy the file’s strict one-sided condition. The requested conclusion is stronger: the point must be one-sided in the ball-connectivity sense and lie on (\partial W).

The exact invalid inference was:

[
\mu_{c_1}(E)>0
\quad+\quad
\text{“one-sided a.e.”}
\quad\Longrightarrow\quad
E\text{ contains a strict one-sided point}.
]

The true known input is only something like:

[
\mu_{c_1}(E)>0
\quad+\quad
\text{“uniaccessible a.e.”}
\quad\Longrightarrow\quad
E\text{ contains a uniaccessible point}.
]

That does not meet the problem’s definition. The file itself only grants density of strict one-sided points via the (\beta)-fixed point and its suitable pullbacks, not full measure of strict one-sided points.  And density is explicitly insufficient because (\partial W\setminus K_{c_2}) need not be relatively open in (J_{c_1}).

A corrected version of the partial result is:

**Proposition actually proved by the potential-theoretic part.**
For (c_1\neq c_2\in M\setminus{0,-2}), after possibly exchanging indices, the exposed set
[
E_1:=\partial W\setminus K_{c_2}
]
is a nonempty subset of (J_{c_1}\setminus K_{c_2}), and in fact it has positive (K_{c_1})-equilibrium measure. Consequently it contains external-ray-uniaccessible points of (J_{c_1}), but this does not imply strict one-sidedness.

To complete the problem by the harmonic-measure route, one would need an additional statement of the form:

[
\text{Every positive } \mu_c\text{-measure subset of }J_c
\text{ contains a strict one-sided point,}
]

or at least that particular exposed sets (\partial W\setminus K_{c_2}) cannot avoid all strict one-sided beta-preimage points. That is precisely the missing nontrivial step; it is not supplied by the standard a.e. accessibility theorem.

So yes: the previous proof should be retracted as a solution to the stated problem. It proves a natural “visible uniaccessible point” weakening, not the required “visible strict one-sided point” statement.

# addition 2
You are right to ask for exactly that missing lemma. But I should not pretend to have a proof of it:

[
\boxed{\text{Every positive }\mu_c\text{-measure subset of }J_c\text{ contains a strict one-sided point}}
]

is not a consequence of the standard Fatou–Lindelöf–Zdunik accessibility theorem. It is essentially the **full-measure strict one-sidedness theorem** that my earlier proof incorrectly assumed. The file’s definition is the strict ball-connectivity condition, not uniaccessibility by a ray.

What I can give rigorously is the precise reduction and the exact point at which a genuinely new theorem is required.

---

## 1. The requested measure lemma is equivalent to full measure of strict one-sided points

Fix (c\in M\setminus{0,-2}). Let

[
S_c={p\in J_c:\ p\text{ is strict one-sided in the ball-connectivity sense}}.
]

Then the proposed statement

[
\tag{P}
\text{every positive }\mu_c\text{-measure subset of }J_c\text{ contains a point of }S_c
]

is equivalent to

[
\tag{Q}
\mu_c(J_c\setminus S_c)=0.
]

Indeed, if ((Q)) holds and (E\subset J_c) has (\mu_c(E)>0), then (E\not\subset J_c\setminus S_c), so (E\cap S_c\neq\varnothing).

Conversely, if ((P)) holds but (\mu_c(J_c\setminus S_c)>0), then the positive-measure set

[
E=J_c\setminus S_c
]

contains no strict one-sided point, contradicting ((P)). Hence ((P)\iff(Q)).

So the requested replacement lemma is exactly:

[
\boxed{\mu_c(S_c)=1.}
]

That is strictly stronger than the known density statement in the file, which only says that the (\beta)-fixed point and its suitable iterated preimages are strict one-sided and dense in (J_c).  Density alone is explicitly identified as insufficient for the exposed set (\partial W\setminus K_{c_2}).

---

## 2. Why the beta-preimage alternative is also not forced by measure

Let

[
B_c={ \text{iterated }f_c\text{-preimages of the }\beta\text{-fixed point along noncritical branches}}.
]

The file records that these points are strict one-sided and dense in (J_c).  But (B_c) is countable: at level (n), there are at most (2^n) preimages, so

[
B_c=\bigcup_{n\ge 0} f_c^{-n}(\beta)
]

is countable.

The equilibrium measure (\mu_c) has no atoms. Therefore

[
\mu_c(B_c)=0.
]

Consequently, measure positivity alone can never imply that a set contains a beta-preimage. The full-measure set

[
J_c\setminus B_c
]

has (\mu_c)-measure (1) and contains no beta-preimage at all.

So the proposed alternative

[
\partial W\setminus K_{c_2}
\quad\text{cannot avoid all strict beta-preimage points}
]

cannot follow merely from positive (\mu_c)-measure of (\partial W\setminus K_{c_2}). It would require a special geometric or dynamical property of that exposed set, not just a harmonic-measure argument.

A sufficient but unavailable condition would be:

[
\partial W\setminus K_{c_2}
\text{ contains a relatively open subset of }J_{c_1}.
]

Then density of (B_{c_1}) in (J_{c_1}) would immediately give a beta-preimage in (\partial W\setminus K_{c_2}). But the file specifically warns that (\partial W\setminus K_{c_2}) need not be relatively open in (J_{c_1}).

---

## 3. The conditional theorem that would complete the original problem

Here is the rigorous reduction.

### Conditional theorem

Assume that for every (c\in M\setminus{0,-2}),

[
\mu_c(S_c)=1.
]

Then the problem in the file has a solution for every pair

[
c_1\neq c_2\in M\setminus{0,-2}.
]

In fact, after choosing the index as in Known Fact 4, there exists

[
x\in J_{c_1}\setminus K_{c_2}
]

such that

[
x\in \partial W
]

and (x) is strict one-sided for (K_{c_1}). This is exactly the requested conclusion.

### Proof

Write

[
K_i=K_{c_i},\qquad J_i=J_{c_i},\qquad \mu_i=\mu_{c_i}.
]

Let

[
X=K_1\cup K_2,
]

and let (W) be the unbounded component of (\mathbb C\setminus X), as in the file.  Let

[
Y=\mathbb C\setminus W
]

be the filled hull of (X). Thus (Y) is compact and full, and

[
\partial Y=\partial W.
]

By Known Fact 4, after possibly exchanging the indices,

[
E:=\partial W\setminus K_2
]

is a nonempty subset of (J_1).

The potential-theoretic argument from my previous response gives more: (E) has positive (\mu_1)-measure. I spell out the key point.

Since distinct parameters have distinct filled Julia sets, (K_1\neq K_2).  Both have logarithmic capacity (1).  If (K_1\cup K_2) had filled hull of capacity (1), then strict monotonicity of capacity would force (K_1=K_2), contradiction. Hence

[
R:=\operatorname{cap}(Y)>1.
]

Let (\nu) be the equilibrium measure of (Y), equivalently harmonic measure of (W) seen from infinity. Since (K_2\subset Y), and (\operatorname{cap}(K_2)=1), the usual Green-potential identity gives

[
\int G_{c_2},d\nu=\log R>0.
]

But (G_{c_2}=0) exactly on (K_2), while (G_{c_2}>0) on (\mathbb C\setminus K_2). Therefore

[
\nu(\partial W\setminus K_2)>0.
]

Since (E=\partial W\setminus K_2) lies on the common boundary portion of the nested domains

[
W\subset \mathbb C\setminus K_1,
]

domain monotonicity of harmonic measure gives

[
\mu_1(E)\ge \nu(E)>0.
]

Now apply the assumed full-measure strict one-sidedness theorem:

[
\mu_1(S_{c_1})=1.
]

Since (\mu_1(E)>0),

[
E\cap S_{c_1}\neq\varnothing.
]

Choose

[
x\in E\cap S_{c_1}.
]

Then

[
x\in E=\partial W\setminus K_2,
]

so

[
x\in \partial W,\qquad x\notin K_2.
]

Also (E\subset J_1), so

[
x\in J_1.
]

Finally, (x\in S_{c_1}), so (x) is strict one-sided for (K_1). This proves the desired conclusion.

---

## 4. What remains genuinely missing

The missing theorem is not

[
\text{uniaccessible a.e.}
]

It must be

[
\boxed{\text{strict ball-connectivity one-sided a.e.}}
]

or a special substitute saying that the particular exposed set

[
\partial W\setminus K_{c_2}
]

must meet (S_{c_1}), or even just the countable dense beta-preimage subset (B_{c_1}).

The first substitute is exactly the full-measure theorem above. The second substitute is not implied by positive measure, because (B_{c_1}) is countable and measure zero. Therefore a valid proof must add a new geometric argument controlling the special outer-boundary set (\partial W\setminus K_{c_2}), not just invoke harmonic measure or density.

---

# Audit of the additions (2026-07-02)

Verdict: **both additions verified; retraction accepted; the conditional theorem is
correct and is the right re-cut.** Detail:

1. **Addition 1 (retraction).** Agrees exactly with the independent audit already
   recorded in the verification report of `06-answer.md`: the invalid inference was
   `μ₁(E) > 0` + "one-sided a.e." ⟹ `E` meets a strict one-sided point, where the
   literature supplies only *uniaccessible* a.e.; the comb separates the notions.
   Accepted.

2. **Addition 2 §1 (equivalence (P) ⟺ (Q)).** Correct, with one footnote: as stated it
   uses measurability of `S_c`; the clean formulation is via a Borel hull
   (`J_c ∖ S_c` contained in a Borel null set), which is how Problem 7 states it.

3. **Addition 2 §2 (β-preimage no-go).** Correct and load-bearing: `B_c` is countable
   (≤ 2ⁿ preimages at level `n`) and `μ_c` is non-atomic (Brolin measure, positive
   entropy), so `μ_c(B_c) = 0` — measure positivity can never force meeting the dense
   one-sided set we actually possess. This permanently closes every "density +
   positive measure" shortcut, including for the special set `∂W ∖ K_{c₂}`.

4. **Addition 2 §3 (conditional theorem).** The potential-theoretic recap matches the
   verified argument of the report, except one loose line: "strict monotonicity of
   capacity would force K₁ = K₂" is not a valid principle as stated (capacity is not
   strictly monotone — polar additions change nothing). The verified repair, already in
   the report, is the energy identity: if `cap(Y) = 1` then `∫G_i dν = log 1 = 0` for
   both `i`, so `supp ν ⊆ K₁ ∩ K₂`, hence `∂Y ⊆ K_i` and fullness gives `Y = K₁ = K₂`,
   contradiction. With that substitution the conditional theorem stands: **`μ_c(S_c)=1`
   for all `c ∈ M ∖ {0,−2}` ⟹ Problem 6 in full.** The pigeonhole and domain
   monotonicity steps are correct as written.

5. **Addition 2 §4 (what remains).** Correct framing. Two additions of our own:
   (i) the required statement is genuinely non-generic — it is FALSE for `c = −2`
   (`K = [−2,2]`: interior segment points are two-sided, `S_{−2} = {±2}`, so
   `μ_{−2}(S_{−2}) = 0`), so any proof must use non-smoothness of `J_c`, matching
   Zdunik's smooth/singular dichotomy; (ii) since no Jordan arc separates the plane, a
   single spiraling (twist-point) access does not by itself break ball-connectivity —
   a refutation needs positive measure of *comb-type* points, a proof must exclude
   them a.e.

**Consequences applied.** The residual is restated self-contained as
`07-full-measure-one-sided.md` (full form, special-set form (W1), subclass form (W2),
refutation form (W3)); the README table carries the new row. Suggested attack route 2
of the problem file `06-onesided-exposed-on-outer-boundary.md` asserted the missing
statement as a known fact — that seeded the original error — and has been corrected in
place, with a status banner added. On the Lean side nothing changes shape:
`ExposedOneSided c₁ c₂` (OneSidedCertificate.lean) remains the named analytic input
consumed by `q62_phiMero_bothconnected_of_op6`, and the internal measure-quantified
engine variant (support-piece rigidity consuming `μ₁(∂W∖K₂) > 0` directly) remains the
route that bypasses Problem 7 entirely.
