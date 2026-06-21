# Big Picture — what the programme is really about

> A plain-language map of the whole research programme: the **lenses** we look through, the **unsolved
> issues** that actually block us, the **problem space and the solution space**, and the **sharpest form
> of the conjectures** that must be proved. It claims no proof of the Riemann Hypothesis and introduces
> no new mathematics — it states the structure the work has uncovered. Register tags
> (`[PROVED]` / `[OPEN]` / `[CONJECTURE]`) are kept where the distinction matters.

---

## 0. The one-sentence picture

> We are **not** looking for a finite algebraic-differential *flow* that generates `ζ` —
> hypertranscendence (Hölder, 1887) blocks that, and that is the *only* thing it blocks. We **are**
> trying to identify a **faithful, source-built transport/index object** attached to `ω = d log ξ`,
> whose source-carrying defects are *exactly* the off-line zeros, and to prove those defects are
> **confined to the seam** `Re(s) = ½`.

This rules out only the **generative-flow** reading. Derived objects, deformations, heat-flow
embeddings (de Bruijn–Newman), potential theory, and source-measure formulations remain valid lenses —
what is excluded is a finite algebraic-differential rule that *produces* `ζ`, not analysis *about* it.

---

## 1. The lenses

These are not rival theories; they are complementary projections of one object.

1. **Constraint, not generative flow** *(the founding lens — scoped)*. The completed object is **fixed by
   the order-2 functional-equation constraint** `ι : s ↦ 1−s` (`ι² = id`, fixed locus the seam), **not
   produced by a finite algebraic-differential rule**. Hölder's theorem: hypertranscendence *is* the
   absence of such a rule — there is no founding flow to discover. The mental models are
   Wheeler–DeWitt superspace (a constraint `ĤΨ = 0`, time with no clock) and holography (bulk fixed by
   boundary). This excludes a *generative* flow, not derived / deformation / heat-flow / potential
   analysis, and it does **not** assert "no operator": if a Hilbert–Pólya object exists, the claim is
   that it appears as a **faithful source-built positivity/index object** — `ι` acting unitarily on the
   archimedean-polarized space (`κ₋ = 0`) — not a naive one-parameter evolution.

2. **Transport, not amplitude**. The object is not the *size* of `ζ` but a **logarithmic transport
   connection** `ω = d log ξ`, equivalently the weld `H = ∂_s log Λ = A + P` of the archimedean term
   `A = ∂_s log Γ∞` and the prime term `P = ζ'/ζ`. The RH content lives in the connection's
   **holonomy**, not its **curvature** — the curvature `[∂_s, M_p] = −log p` is *universal*, the same
   for every object on this geometry.

3. **The weld and the seam**. Hypertranscendence has **two sources**: the archimedean Γ (the *unique*
   orbit-unbalanced place) and the infinite prime base `{σ_p}` (every prime lane balanced). They are
   **welded** by the functional equation; the weld *is* the native frontier, and the seam `Re(s) = ½` is
   where the two sides must glue. Neither parent — Γ alone, or the prime-difference structure alone — can
   pose the joint statement.

4. **Faithful index, not measured density** *(the RH lens)*. RH is **`κ₋ = 0`**, where `κ₋` is a
   *faithful signed integer* — the Krein–Langer / Sylvester negative index of the completed carrier
   `−Ξ'/Ξ`, equal to the number of off-line zero-pairs (one off-line zero forces `κ₋ = 2`). A *measured*
   positivity (density, variance, trace) is blind to density-zero off-line dust and cannot decide RH;
   only the integer index can.

5. **Two orthogonal axes** *(the anti-conflation lens)*. The landscape has two independent apexes,
   joined only at the seam:
   - the **weld / realization axis** — the functional equation, crystallinity, "a motive exists"
     (`ω = 0`). This is **RH-blind**: Davenport–Heilbronn satisfies the functional equation yet has
     off-line zeros, so `ω = 0 ⇏ RH`.
   - the **positivity / localization axis** — RH itself, the *archimedean* positivity (`κ₋ = 0`).

   Conflating them ("realization forces RH") is the recurring error and is provably false as stated.

6. **Affine confinement** *(a theorem schema, not a global ban)*. The weld lives on the affine group
   `𝔾_a ⋊ 𝔾_m` (`∂_s` = dilation, `M_p` = translation-by-`log p`). Every affine *volume* observable
   factors through a finite **passport** `Π(S) = (|S|, Σ_{m∈S} m)`. Schema: *any method whose observable
   factors through the passport is RH-blind until `Π(S)` is subtracted* — the RH content is the shape
   beyond the passport, in the transverse seam `[𝔾_a, 𝔾_m]`. This is **not** a dismissal of
   positivity / Laguerre / Hankel / Jensen methods (those *are* the RH apex): such a method becomes
   RH-bearing exactly when it is a **faithful source / localization test**, not a measured affine-volume
   test.

7. **The missing single Frobenius** *(the arithmetic lens)*. The seam has one computable shadow, the
   **corank**: `∞` over ℚ (the primes give infinitely many independent "Frobenii"), `1` over a function
   field (one Frobenius). The gap `∞ − 1` is the missing single Frobenius. This is a **linear** fact
   (`corank = ∞ ⟺ {log p}` ℚ-linearly independent — Baker, **proven**), strictly weaker than the
   **algebraic** apex (`trdeg = ∞ ⟺ {log p}` ℚ-algebraically independent — Schanuel, **open**). The hard
   content is one level above the proven floor.

8. **The empirical weld carrier** *(the experimental lens)*. A single observable — the phase-carrier
   defect `Δ = max(log|A|, log|P|) − log|A+P|` — separates the true analytic continuation from
   finite-Euler truncations and random-phase surrogates in the critical strip, and collapses at `σ > 1`.
   This carrier is a **diagnostic of analytic continuation and zero-structure**, **not** a transcendence
   detector: the functional-equation-exact, zero-exact, non-hypertranscendental adversary that would be
   needed to make it one does not exist (see Issue 2).

> **The unifying claim behind the eight lenses:** *the object is fixed by a constraint; its RH-content
> is the faithful archimedean positivity of the completed weld's holonomy, which lives in the one
> direction no prime-side, flow, or measured tool can reach.*

---

## 2. The main unsolved issues

1. **A genuinely new transcendence detector is needed — and it must live on the divisor's *arithmetic*,
   not its geometry.** *(The deepest block.)* Every structural / value-relation invariant tried so far
   collapses to the **rank of a shift/derivative matrix** — the only value-level quantity that has ever
   separated `ζ` from a control. The natural "remove the zeros, then test differential-algebraic
   nonclosure" route is **self-defeating** for `ξ`: since `ξ` has order 1, Hadamard gives
   `ξ'/ξ = b + Σ_ρ[1/(s−ρ) + 1/ρ]`, so the source-quotiented connection is a *constant* — quotienting
   the divisor removes exactly the hypertranscendence. **`ξ`'s hypertranscendence is divisor-encoded**:
   it is the arithmetic of the zero ordinates `{γ_n}` (tied to `{log p}` through the explicit formula,
   though the precise *algebraic-independence* link is itself conjectural — the value axis, Conjecture A
   — not a proven equivalence; contrast `sin πs`, also order 1 but with arithmetic-progression zeros,
   which *is* differential-algebraic). So the genuine detector is **not** a connection / holonomy / gauge
   object at all — it is the **value/arithmetic apex (Conjecture A)**, and none has been found. This
   unifies the two-apex picture at the **divisor**: its **geometry** (positions as a set → source
   confinement) is the positivity/bridge axis; its **arithmetic** (relations among the positions) is the
   value axis. *Quantitative confirmation `[verified]`:* PSLQ relation searches on the seam moments
   `S_k = 2Σγ_n^{−2k}` against `{π^{2k}, β(2k)}` separate **only** arithmetic simplicity, not `ζ`-arithmetic
   — the arithmetic-progression divisor (`γ_n=n`, `S_k=2ζ(2k)∈ℚ(π)`) is detected at the Bernoulli heights
   `3,45,945,4725,93555`, while `ζ`, **same-density random**, and jittered-`ζ` zeros are **all
   indistinguishable** (no relation in `ℚ(π,β)`; the prime part of `S_k(ζ)` obstructs). So an `S_k`-only
   detector sees genericity-vs-simplicity, not the zeta arithmetic; the genuine `A`-axis detector must use the
   prime-side explicit-formula data (which separates only tautologically), and its non-tautological core is
   Schanuel-for-prime-logs (Conjecture A, open).

2. **The carrier's status is resolved (deflationary): it is not a native-hypertranscendence detector.**
   The decisive adversary the carrier would need — a functional-equation-exact, zero-exact,
   *non*-hypertranscendental object — **does not exist.** By Hadamard, every entire function with `ξ`'s
   exact zeros and finite order is `e^{q((s−½)²)}·ξ`; its log-derivative is `ξ'/ξ + q'` with the prime
   part `ζ'/ζ` untouched, and since `ζ'/ζ` is hypertranscendental and `HT ± (D-algebraic) = HT`, every
   such object is hypertranscendental. The weaker surrogates (finite-Euler, random-phase,
   Davenport–Heilbronn) are already separated by analyticity / zero-structure, not by hypertranscendence.
   So the weld carrier is conclusively an analytic-continuation / zero-structure discriminator — real and
   useful — **not** a transcendence detector. Nothing remains to "run" here; the open work is the bridge
   arrow (Conjecture C) and the apexes (A, B).

3. **The bridge arrow is open** *(the RH `[OPEN CORE]`)*. One can show *locally* that an off-line zero
   creates an off-seam transport defect (the pole model `ξ'/ξ ~ m/(s−ρ)`). The converse confinement at
   *all scales* — that **every** source-carrying defect lies on the seam — is not yet shown. This is the
   genuine open core: the step from windowed signatures to an all-scale statement.

4. **The positivity apex (RH) is open — and the numerics are a red herring.** `RH ⟺ κ₋ = 0 ⟺`
   uniform-in-`d` Hankel/Laguerre positivity (cleanest: the reciprocal-seam `Q_0[p]=Σc_ic_jT_{i+j+1}≥0`,
   `T_k=2Σγ^{−2k}`). The `d = 2` leader is classical (`log|ξ(½+it)|` concave); the uniformity in `d` is
   open. **A decisive negative result settled what the numerics are worth:** the entire numerical
   difficulty — exponential ill-conditioning, auto-deflating extremal polynomials, a *distributed*
   mid-range obstruction, deflation making things worse, a height-graded finite-`d` reach (`d*~γ0/3`) — is
   **generic to any reciprocal-squared measure accumulating at `y=0`, not RH-specific**: the **RH-empty**
   FID integer divisor (`ζ(2k+1)`) reproduces *all* of it. So no Hankel-determinant / conditioning /
   Jacobi / deflation argument can be RH-relevant — the numerical no-margin carries **zero RH content**.
   The RH content lives only in the integer→zero **explicit-formula transfer**. Structurally the wall
   localizes: splitting `Q_0=Q_arch+Q_prime`, the entire `10^{2.8k}`-deep cancellation sits on a single
   **pole direction `u=(−4)^i`** (the `s=1` entireness, automatic, `Q_arch[u]=−Q_prime[u]` to `~10^{−12}`),
   and on its codim-1 complement `Q_arch` is positive-definite — so RH ⟺ the prime form `Q_prime` does not
   overcome the archimedean PD "budget" on `u^⊥`. The open apex is **analytic** (does the completed
   explicit formula make `Q_0[p]≥0`?), never numerical.

5. **The value apex (Schanuel-for-prime-logs) is open.** `corank^{(2)} = ∞` — the degree-2 prime-log
   monomials ℚ-linearly independent — is **open even for `{log 2, log 3}`**. We have the linear floor
   (Baker), not the algebraic apex.

6. **The faithful object has not been *constructed*.** One can *name* the target (`κ₋ = 0`) and *locate*
   it, but nobody has **source-built** the faithful-index object from Euler / Γ / pole / functional-
   equation data *without feeding in the zero locations* and proven its index vanishes. Naming a
   positivity criterion equivalent to RH is not progress — the many such reframes all reduce to the same
   archimedean (Weil–Connes) positivity.

7. **The oriented-structure intuition needs re-formulation.** "The carrier is one oriented 2-form" is
   right in spirit but **false in its naive scalar form** (no scalar `(O, φ)` pair works). The oriented
   structure must be the **non-scalar holonomy** form — which loops back to Issue 2.

---

## 3. The problem space and the solution space

### The problem space

**The object has no handle.** Hypertranscendental functions (Γ, ζ, the completion Λ) satisfy *no*
algebraic differential equation — the 1887 founding theorem, a *negative* result. The usual move (find
the generative rule, integrate it, read off the answer) is unavailable *in principle*. The object is
shaped by a **constraint** (the functional equation, the completion, a regularization), and the
questions we care about — above all, *where are the zeros of the completed object?* — are about a thing
pinned by a relation, not grown by a recursion. The bet is that the right description is **transport
fixed by a constraint** rather than **amplitude propagated by a flow**.

**Standard tools are structurally mismatched, and the wall is tool-independent.** Single-coordinate
statistics (mean, amplitude, occupancy, marginals) destroy the joint constraint and are RH-blind. The
prime side carries *no polarization* — independence yields equidistribution/variance, constitutively
blind to the correlation = positivity = RH — so **no statement provable on the prime structure alone is
RH-bearing**. Positivity methods are affine-confined and cannot reach the transverse seam. And the
obstruction is **two distinct apexes** — an arithmetic/transcendence one (Schanuel-for-prime-logs) and a
positivity one (`κ₋ = 0`) — joined only at the archimedean seam, with `ω = 0 ⇏ RH` keeping them apart.
Many independent reformulations all collapse to the same wall: **RH-positivity is the one archimedean,
"timelike" direction** — a conservation law, not a missing trick.

### The solution space

**One faithful, source-built object with a vanishing integer index.** The target is a **completed**
(includes Γ), **transport/polarization** (not scalar), **faithful** (integer index, not a measured
trace), **source-built** (constructed from Euler / Γ / pole / functional-equation data *without* reading
the zeros) object whose **negative index equals the off-line zero count** and is **forced to be zero** by
the construction — one that **separates fake families** (the functional-equation-exact / correct-zeros
surrogates fail at a named source gate) and **survives the zero margin** of RH (no hidden gap is used to
force the sign). This object is conjectured to have **two faces** — a *transport face* (the holonomy of
the weld connection) and a *faithful-index face* (the source-built `κ₋`) — the same object in two
coordinate systems.

**A proven floor and an open apex.** In hand is a **structural floor** — proven, classical when the
vocabulary is stripped: constraint-not-flow, the decidable two-source classifier, the corank linear floor
(Baker), the faithful index `κ₋ = #off-line pairs`, and the affine-confinement diagnosis. Open is the
apex — the two transcendence/positivity cores and the **bridge arrow** that would connect the empirical
transport signatures to all-scale off-seam exclusion. The surrogate fork that once gated this is **closed
by argument** (Issue 2): no functional-equation-exact, zero-exact, non-hypertranscendental adversary
exists, so the carrier is a zero-structure diagnostic, not a transcendence detector. The solution space
is *located with unusual precision but not entered*; the live moves are the bridge arrow (C), the
positivity apex (B), and the value detector (A).

---

## 4. The conjectures to prove — sharpest form

Everything reduces to five cores (Master, A, B, C, D) plus one framing assumption (E).

> **MASTER CONJECTURE — two faces and an identification. `[CONJECTURE]`**
> The compressed claim "the carrier *is* `κ₋`" is split so that no conclusion is *named* before it is
> *built*:
> - **Master 1 (transport face).** The weld phase carrier is the **non-scalar holonomy class** of the
>   affine `(∂_s, M_p)` connection — the shape content beyond the passport `Π(S) = (|S|, Σ_{m∈S} m)`,
>   orthogonal to the argument-principle winding — trivialized by the Γ-completion **exactly on `σ = ½`**.
> - **Master 2 (faithful-index face).** A **source-built** faithful index (built without zero-feeding)
>   extracts the **zero-counting part** of that holonomy: its negative index equals the off-line zero
>   count.
> - **Identification bridge.** Master 1 and Master 2 are conjectured to be the **same object in two
>   coordinates** — *this identification is itself a theorem to be proved*, not a definition.
>
> *Kill:* if the holonomy is only the winding `∮ d arg = 2πi(#zeros − #poles)`, or factors through
> `Π(S)`, Master 1 reduces; if the index needs zero locations as input, Master 2 reduces; if no
> identification theorem is produced, the bridge stays a name. (The *scalar* oriented-2-form form is
> already dead; the object is non-scalar.)

> **CONJECTURE A — the value / transcendence apex (Schanuel-for-prime-logs). `[OPEN CORE]`**
> `{log p}` are **ℚ-algebraically independent** ⟺ `corank^{(T)} = ∞ ∀ T ≥ 2` ⟺ `trdeg = ∞`. First open
> rung: `corank^{(2)} = ∞`, open even for `{log 2, log 3}`. This is the missing single Frobenius made
> algebraic — the linear floor `corank = ∞` is proven (Baker); the algebraic apex is the open part.
> *Scoped role:* Conjecture A most plausibly **explains why a native transcendence detector is hard** (the
> value axis is Schanuel-deep); it is **not** a necessary route to RH unless a theorem explicitly links it
> to the faithful positivity index.

> **CONJECTURE B — the positivity / RH apex (the one wall). `[OPEN CORE]`**
> `RH ⟺ κ₋ = 0 ⟺` the **uniform-in-`d` Hankel/Laguerre positivity** `det H_d ≥ 0 ∀ d, t` ⟺ `Q_W ⪰ 0`
> (signature `(1|∞)`). The `d = 2` leader is classical; the **uniformity in `d`** is the open content — a
> sparse / sub-grid / collective resonance, not a pointwise gap.
> *Cleanest coordinate (the "one wall").* In the reciprocal seam-squared chart `y_ρ = −(ρ−½)^{−2}`,
> `RH ⟺ {T_k = Σ_ρ m_ρ y_ρ^k}` is a **Stieltjes moment sequence** ⟺ its Hankel towers are positive
> semidefinite to all orders (absolutely convergent from `k = 1`; the forward `Σ(ρ−½)^k` diverges). The
> contour moments `M_k` and local defect `D₂`, the Li coefficients `λ_n`, the Jensen polynomials
> `J_{d,n}`, the Hankel determinants `H_d`, the Weil form `Q_W`, and `κ₋` are Newton-conjugate **charts of
> this one wall** (a finite low-order slab of any chart is seam-blind; only all-order data is RH).
> *Register:* `RH ⟺ κ₋ = 0` is a faithful restatement; `RH ⟺ det H_d ≥ 0 ∀d, t` (uniform Pólya–Jensen,
> 1927) and `RH ⟺ Q_W ⪰ 0` (Weil) are theorems whose *uniformity* is the open content — the state of the
> art is Griffin–Ono–Rolen–Zagier (2019), fixed-`d` eventual hyperbolicity.
> *Negative control:* the same instrument on the **integer** divisor gives `ζ(2k+1) = ∫ y^k dν`,
> `ν = Σ_m (1/m) δ_{1/m²} ≥ 0`, positive semidefinite **unconditionally** — so integer-side ("FID")
> positivity is RH-empty; the content is the explicit-formula map onto the zero divisor.
> *Distinctness:* A and B are **separate apexes**, joined only at the seam (`ω = 0 ⇏ RH`).

> **CONJECTURE C — the bridge (off-line ⟺ off-seam). `[OPEN CORE — the RH arrow]`**
> `off-line zero ⟺ off-seam source-carrying transport defect`, with "source-carrying" = nonzero
> logarithmic residue. The **detection** half (off-line ⟹ off-seam defect) is locally proven via the pole
> model and the same-height mirror-pair curvature window `2(a²−τ²)/(a²+τ²)²`; the **confinement** half is
> the genuine open core. *Sharp form (positivity-transfer).* The confinement half is not "phase ⟹ RH" nor
> "integer-side positivity ⟹ RH"; it is the statement that the **completion together with the explicit
> formula carries the divisor data onto a Stieltjes-positive zero-divisor sequence `{T_k}`** — provably,
> via total positivity / a variation-diminishing weld map / a source-built `κ₋` read from `{T_k}` / no
> off-seam signed defect surviving the reciprocal chart. The object to prove is all-order Stieltjes
> positivity of `{T_k}`.

> **CONJECTURE D — universal prime-side orthogonality. `[CONJECTURE — strongly supported]`**
> There is **no positive-definite polarization on the prime structure** whose positivity is equivalent to
> RH. This is why the wall is archimedean: every RH-criterion known is archimedean; a prime-side
> positivity criterion would refute it. It tells us where *not* to look.

> **CONJECTURE E — no generative-flow operator (the sharpened "constraint, not flow"). `[CONJECTURE —
> framing assumption]`**
> There is **no prime-built, order-preserving, generative one-parameter-flow** self-adjoint operator
> whose spectrum is the nontrivial zeros and whose self-adjointness is equivalent to RH. Equivalently:
> **any** genuine Hilbert–Pólya realization is **necessarily archimedean** and **is a positivity** (`κ₋ =
> 0` / Weil positivity / the constraint `ι` acting unitarily), not an evolution. The search for a naive
> prime-built Hamiltonian flow (the `xp` / PT-symmetric line read as a generative evolution) is
> mis-targeted. *Support:* prime-side orthogonality (Conjecture D); the fact that the flow the prime
> structure actually carries has spectrum `{log p}`, RH-blind; and that Connes' adelic realization and the
> Connes–Consani prolate-operator realization of the low zeros are *both* archimedean positivity objects,
> confirming the scoping. *Kill:* a prime-built self-adjoint operator with the zeros as spectrum whose
> self-adjointness ⟺ RH. *Scope guard:* this does not ban heat-flow / de Bruijn–Newman / potential
> analysis or archimedean positivity operators — only the prime-built generative flow.

> **THE CONSTRUCTION / DETECTOR OBLIGATION. `[OPEN]`**
> **Source-build** the faithful object of the Master Conjecture — from Euler / Γ / pole / functional-
> equation data, *without* reading the zeros — prove its integer index equals the off-line zero count, and
> prove that index is zero, while **separating fake families** at a named gate and **surviving the zero
> margin**. Equivalently: exhibit a **transcendence detector not of shift/derivative-rank type**
> (Issue 1). This single obligation is what the named source-built conjectures, the two "entrances"
> (Jacobi–Loewner–Krein–Hodge and Jensen / Laguerre–Pólya), and the route conjectures all reduce to.

---

## 5. The honest bottom line

> The programme has **located** the Riemann obstruction with unusual precision — a single archimedean
> positivity, tool-independent across many reformulations, distinct from and joined only at the seam to
> the Schanuel value-apex — and has proven a **structural floor** around it that is classical when the
> weld vocabulary is stripped. The faithful-index identity `κ₋ = #off-line pairs` is a useful
> formalization; several of the geometric interpretations layered on it remain `[CONJECTURE]`. The
> programme has **not crossed** the wall.
>
> It is strongest as a **diagnostic geometry of completed analytic continuation** and as a **map of what a
> faithful RH-bearing object would have to be** — not yet evidence that such an object has been
> constructed. The discipline that makes it serious rather than metaphor-accumulation is its
> **anti-conflation rule**: weld/realization is not RH; amplitude is not transport; measured density is
> not the faithful index; local/generic signatures are not all-scale source confinement.
>
> The surrogate fork is **closed by argument** — the functional-equation-exact, zero-exact,
> non-hypertranscendental adversary does not exist — so the carrier is settled as a zero-structure
> diagnostic. That leaves three open moves: a **transcendence detector not reducible to shift/derivative
> rank** (without which the value apex A stays out of reach), the **bridge arrow (C)** as a
> positivity-transfer theorem, and the **positivity apex (B)**. Everything else is scaffolding,
> coordinates, or guardrails around those.
