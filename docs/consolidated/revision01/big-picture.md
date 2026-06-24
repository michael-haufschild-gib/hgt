# Big Picture — what the programme is really about

> A plain-language map of the whole research programme: the **lenses** we look through, the **unsolved
> issues** that actually block us, the **problem space and the solution space**, and the **current form
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

> **The target, now narrowed (post-2026-06-22 computation battery).** That faithful object is no longer a vague
> "two-faced carrier." Its RH-bearing face is constrained to a **rank-one boundary-Weyl sign problem**: the
> completed explicit formula must produce either a bounded self-adjoint
> `K = M_triv^{−1/2}(−R^P)M_triv^{−1/2} ⪯ I` with `‖K‖=1`, `1 ∈ σ_ess(K)`, or the correct closed
> semibounded form replacing that operator, built **without zero-feeding**. The finite matrices `K_d` are
> congruence-normalized witnesses, not the construction of `K`. If the completion exists, RH is equivalent to
> `λ_min(I−K_d) > 0 ∀d`. Its content then collapses to a **scalar** condition at **one exterior point** — the
> first trivial zero `y=−0.16` controlling
> the deep hard edge `y=0⁺` (an inverse exterior Christoffel function) — with the de Branges/Krein boundary at
> the **seam centre `s=½`**. In the current finite-section chart, the completed form splits as `H^0_d = H^-_d + 0.16·v_{−0.16}v_{−0.16}^T`
> with `inertia(H^-_d)=(d,1)`, so RH `⟺` the **scalar Weyl gap** `s_d = 0.16·margin_d > 0 ∀d` (the first
> trivial-zero atom stays just above the rank-one Weyl threshold at every degree). The proof is a **sign-exact
> boundary-monotonicity theorem** at `y=−0.16`, never an estimate. This is the **Rank-one Γ-boundary Weyl Bridge**:
> *Γ supplies the exact boundary atom (the j=1 trivial zero), the primes create exactly one bulk defect, RH says
> the Γ atom repairs it at every degree*; the new reduction is `Q_0[p]≥0 ∀p ⟺ s_d>0 ∀d`. The **fundamental
> fake-family separator is the integer `κ₋`**, with `s_d=0` its rank-one shadow: DH (a real off-line zero) keeps
> `κ₋=1` and crosses `s_d=0` at d=62 (height-limited), but a global sign-fake jumps to `κ₋=2` with `s_d>0` (comp81) —
> so watch the index `κ₋`, not the scalar `s_d`.

> **Current naming (Krein–Langer rank-one signed moment problem, gpt/43 synthesizing the de-Branges battery).**
> The finite anatomy is one clean object: `H^-_d = M_d(σ)` is the moment matrix of the **signed** measure
> `σ = ν' − a_*δ_{y_*}`, where `ν'=Σ_ρ 2y_ρδ_{y_ρ}` is the shifted reciprocal zero-divisor measure; `ν'`
> is a positive `R_+` measure exactly on the RH side, so that positivity is not input. The bridge is the Krein
> transition `σ∈Π₁ ──(+a_*δ_{y_*})──▶ ν'∈Π₀`: the Cauchy transform
> `m_σ∈N₁` (one negative square, verified κ=1) becomes PSD after the canonical Γ atom is restored. The apex, as a
> reproducing-kernel statement, is the **Uvarov one-point boundary-removal positivity** `K_{ν'}(y_*,y_*)>0 ∀d` — the
> same `s_d>0`. The Hankel tail `μ_E` is now read as the **seam shadow of `σ`** (anatomy, `γ_1`-dominated, *not* the
> gate). Three divisors must not be conflated: the **RH divisor** `{y_ρ}`, the **Γ-boundary divisor** `0.16δ_{−0.16}`,
> and the **Krein signed divisor** `σ` (the proof divisor, in `Π₁`).

---

## 1. The lenses

These are not rival theories; they are complementary projections of one object.

1. **Constraint, not generative flow** *(the founding lens — scoped)*. The completed object is **fixed by
   the order-2 functional-equation constraint** `ι : s ↦ 1−s` (`ι² = id`, `Fix(ι)={1/2}`;
   the seam is `Fix(ι∘conj)`), **not
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
   content is one level above the proven floor. *(The geometric carrier of this lens — the `𝔽₁` object,
   `Spec ℤ ×_{𝔽₁} Spec ℤ`, Connes–Consani / Borger / Deninger — is consolidated in `11-f1-the-target-object.md`.)*

8. **No target, only byproduct** *(the anti-mirror lens — the enforcement of lens 1)*. **RH cannot be
   reached by aiming at RH.** Every object provably equivalent to RH — `κ₋=0`, `Q_0≥0`, Weil/Li positivity,
   Pólya–Jensen, the prolate Sonin compression — is *the same wall under a new name*; the equivalences are
   **horizontal** (cheap, content-preserving: proof12 turns one into another in a single line), so motion
   among them is motion without progress — a **hall of mirrors** — and is exactly the *deduction* the
   immutable rules forbid (and that a century of renamings has failed at). The difficulty is **invariant**
   under every RH-equivalence; leverage can only come from **outside the class** — a *non*-RH-equivalent
   constraint (the hypertranscendence/value home, the `𝔽₁`/geometric realization, a transcendence-independence
   fact) that leaves **no room** for off-line zeros, so RH is **forced as a residue** ("it cannot be
   otherwise"), never proved as a goal. **Warrant:** the *only* RH-type statement ever proved — RH over `𝔽_q`
   (Deligne, Weil II) — was a **byproduct** of Grothendieck building étale cohomology *for its own sake*; RH
   fell out of that structure's positivity (hard Lefschetz), which existed independently of wanting RH.
   **Operational rule:** before adopting any target, test it for RH-reduction; if it reduces, it is a mirror —
   *step back to a provable, non-equivalent point* (hypertranscendence, Baker, the weld category `𝓜⁺`) *and
   turn orthogonal*. Treating RH as a target to **prove** is treating it as a flow-endpoint to **reach** —
   which lens 1 already forbids. **The project's hunch, restored to its charter:** we do not try to prove RH;
   we build the constraint-structure of hypertranscendence, and *if* it forces the divisor onto the line, the
   RH proof is a byproduct — never the wall, never the goal.

> **The unifying claim behind the eight lenses:** *the object is fixed by a constraint; its RH-content
> is the faithful archimedean positivity of the completed weld's holonomy — but that positivity is a
> mirror of RH, not a lever on it (lens 8), so the work is to build the **non-equivalent** constraint from
> which the divisor's location, hence RH, falls out as a residue.*

### 1′. The logical form of a constraint-proof (what "constraint, not flow" means in logic)

"Constraint, not flow" is a *logical type*, not a slogan, and it is **not** a deduction `a ⟹ b`:

- **Why not a syllogism.** Modus ponens needs a *generative premise* to propagate forward; hypertranscendence
  (Hölder) is the theorem that *no generative premise exists* — there is nothing to flow from. And "constraint"
  is **not** `¬(a ⟹ b)`: that is `a ∧ ¬b`, a counterexample — the empty/wrong type.
- **The actual form: `∃!` from rigidity** (predicate logic, not propositional). A constraint is a *definite
  description* — "*the* `x` with `C(x)`" — whose force is a **degrees-of-freedom / conservation** argument:
  an off-line zero is one *extra free parameter*; the completed object is **parameter-free** (its freedoms
  are fully spent by FE + Euler product + finite order); a parameter-free object cannot absorb an extra
  parameter ⟹ no off-line zero — *for lack of room, not by prohibition*. The conclusion is **read off a
  unique fixed point**, never derived from a premise.
- **Mirror vs non-mirror, stated logically (= lens 8).** The doomed direction *quantifies over zeros*
  ("knock out every off-line configuration" — case-elimination, which *is* RH; `κ₋=0` is this). The live
  direction *never quantifies over zeros at all* — it over-determines the **ambient object** from non-zero
  data until uniqueness is structural, and zero-locations fall out downstream. **The dividing line is
  whether your quantifier ranges over zeros (mirror) or over the object (constraint).**
- **"Decoherence" is exact: pointer-basis selection.** For a constraint operator `T`, the allowed objects are
  `Fix(T)/ker(T)`; if `T` is rigid enough that this is one-dimensional, the object "manifests in one way."
  Off-line zeros are the states that *don't commute with* `T` (the Euler-product/multiplicative constraint),
  suppressed by incompatibility, not by a law naming them. RH = the pointer basis of the multiplicative constraint.
- **The one rigorous instance of this exact logic: Deligne (Weil II).** RH over `𝔽_q` was *not* proved by
  eliminating bad Frobenius eigenvalues; it was proved by **purity** — the cohomology is pure of weight `i`
  (hard Lefschetz + Poincaré duality pin a closed weight grading), and purity *forces* `|α|=q^{i/2}`: a
  deviant eigenvalue is the extra degree of freedom a rigid grading cannot hold. Same shape as Wheeler–DeWitt
  (`ĤΨ=0`, state = kernel of a constraint) and holography (boundary rigidly fixes bulk).
- **Forward (the non-mirror task).** Build a **weight/purity rigidity structure** on the seam object — the
  missing `𝔽₁`-Frobenius grading (lens 7) — whose rigidity makes off-line zeros a *dimensionally excluded*
  degree of freedom, constructed from non-zero data. RH is then a residue of purity, never a target.

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

**Update (post-2026-06-22 battery): the positivity face is localized, not completed.** What was a
"vague two-faced carrier" has, on the positivity/`κ₋` side, narrowed to a **rank-one boundary-Weyl
operator/form obligation** whose RH content is a **scalar** sign condition at the first trivial zero
`y=−0.16` (§0, Conjecture B). The finite sections and Uvarov identities identify the coordinate; they do
not construct the completed source object. The *transport-face holonomy* and its *identification* with
this object (Master Conjecture) remain `[CONJECTURE]`. So the open apex (B) is now "**source-build the
rank-one boundary object without zero-feeding, prove its domain/completion theorem, and prove its
sign**," not "find some equivalent positivity."

---

## 4. The conjectures to prove — current form

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
> The all-order seam-log jet is not a softer source input: for `Xi(w)=Phi(w^2)`, the full coefficient
> sequence of `log(Phi(z)/Phi(0))` determines `Xi` up to scalar, hence determines the reciprocal zero
> divisor. It becomes a legitimate source coordinate only after Euler / Gamma / FE data produce it
> independently; receiving it as data is already receiving a function-complete chart.
> The same warning survives any all-order triangular/invertible recoding of that jet — continued-fraction,
> Jacobi, cumulant, Hankel-ratio, or Pade-style coordinates are lenses, not source constraints, when the
> full coordinate string reconstructs the germ or shifted tower.
> *Register:* `RH ⟺ κ₋ = 0` is a faithful restatement; `RH ⟺ det H_d ≥ 0 ∀d, t` (uniform Pólya–Jensen,
> 1927) and `RH ⟺ Q_W ⪰ 0` (Weil) are theorems whose *uniformity* is the open content — the state of the
> art is Griffin–Ono–Rolen–Zagier (2019), fixed-`d` eventual hyperbolicity.
> *Negative control:* the same instrument on the **integer** divisor gives `ζ(2k+1) = ∫ y^k dν`,
> `ν = Σ_m (1/m) δ_{1/m²} ≥ 0`, positive semidefinite **unconditionally** — so integer-side ("FID")
> positivity is RH-empty; the content is the explicit-formula map onto the zero divisor.
> *Distinctness:* A and B are **separate apexes**, joined only at the seam (`ω = 0 ⇏ RH`).
> *Purified form (gpt/38, post-2026-06-22 battery):* the apex is now a **specific operator/form
> obligation** — the completed explicit formula must produce a **noncompact self-adjoint contraction**
> `K = M_triv^{−1/2}(−R^P)M_triv^{−1/2}` with `K ⪯ I`, `‖K‖=1`, `1∈σ_ess(K)`, finite sections `K_d=P_d K P_d^*`,
> or a closed semibounded form with the same Loewner content, built **without zero-feeding**. Only after this
> source object exists does RH become `λ_min(I−K_d)>0 ∀d`. Every finite-`d`/conditioning/margin/correlation
> observable is **demoted** (prime-blind, generic) — only the **all-order sign** is RH-bearing, so the proof must
> be **boundary monotonicity / Weyl positivity**, never a spectral-gap estimate. The cross-scale smoking gun: the
> **first trivial zero `y=−0.16` controls the entire deep hard edge `0⁺`** via an inverse exterior Christoffel
> function; the natural operator coordinate is the protector shift `x=y+0.16` (where `R^P` is near-Jacobi), and
> the de Branges/Krein boundary sits at the **seam centre `s=½` (`y=∞`)**.

> **CONJECTURE C — the bridge (off-line ⟺ off-seam). `[OPEN CORE — the RH arrow]`**
> `off-line zero ⟺ off-seam source-carrying transport defect`, with "source-carrying" = nonzero
> logarithmic residue. The **detection** half (off-line ⟹ off-seam defect) is locally proven via the pole
> model and the same-height mirror-pair curvature window `2(a²−τ²)/(a²+τ²)²`; the **confinement** half is
> the genuine open core. *Current form (positivity-transfer).* The confinement half is not "phase ⟹ RH" nor
> "integer-side positivity ⟹ RH"; it is the statement that the **completion together with the explicit
> formula carries the divisor data onto a Stieltjes-positive zero-divisor sequence `{T_k}`** — provably,
> via total positivity / a variation-diminishing weld map / a source-built `κ₋` read from `{T_k}` / no
> off-seam signed defect surviving the reciprocal chart. The object to prove is all-order Stieltjes
> positivity of `{T_k}`.
> This transfer is not termwise in Euler frequencies: a single positive FE-even source germ
> `B(cosh(lambda w)-1)` contributes `T_k=B(-1)^(k+1)lambda^(2k)/(2k-1)!`, giving a negative first
> shifted Hankel determinant. The source proof must use completed interaction, not isolated
> positive-frequency summation.
> *Current finite shadow (gpt/37):* `Q_0 = M_triv + R^P` with `M_triv` the explicit positive trivial-zero
> square; RH ⟺ the **one-sided Loewner domination** `−R^P ⪯ M_triv` (`λ_max(K_d) ≤ 1 ∀d`,
> `K_d = M_triv^{−1/2}(−R^P)M_triv^{−1/2}`). The proof object is a source-built **Loewner inequality `I−K_d⪰0` at
> zero margin** on a **three-stratum reciprocal divisor** (pole `y=−4` + trivial chain + nontrivial divisor),
> *not* a slack estimate. The first real **source-gate** test: do genuine Dirichlet-`L` pass `K_d⪯I` while
> Davenport–Heilbronn fails (`λ_max>1`)?
> *Answered (2026-06-22 battery):* the bridge structure reproduces for **every** genuine completed `L` (the
> mechanism is Euler-product-general; exponent is protector/parity-set, not universal), but the **real
> Davenport–Heilbronn off-line zero is NOT detected through d=55** (`Im(y)≈10^{−6}` at the hard edge) and
> jittered-ζ matches ζ to 4–5 digits — so finite `K_d⪯I` is **height-limited, not a finite-`d` source
> gate**; the discriminator is the same **all-order** wall. RH lives only in the sign.

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

## 5. Where we stand — and what we refuse to chase

> **Where we stand.** The Riemann obstruction is **located with unusual precision** and, after the
> 2026-06-22 computation battery, **purified**: every finite-`d`, conditioning, margin, correlation,
> density, and rate observable is provably RH-blind, leaving exactly one RH-bearing quantity — the
> **all-order sign** of the shifted reciprocal form. We have **not crossed** the wall; we have made it
> small, named, and one-dimensional.
>
> **What blocks us, in one line.** Build the **source-built rank-one boundary-Weyl object** from Γ / pole /
> functional-equation / explicit-formula data *without reading the zeros*: either a bounded noncompact
> contraction `K ⪯ I` (`‖K‖=1`) or the correct closed semibounded form, then prove its scalar boundary
> sign stays positive at all orders.
>
> **What we solved — beyond just checking SOTA.** Not theorems toward RH, but a hard structural map nobody
> had, and several decisive *no-go*s that SOTA had not drawn:
> - the wall is **archimedean and one-dimensional** — tool-independent across the Li / Jensen / Hankel /
>   Weil / `κ₋` charts (all the same object);
> - the RH content in this chart is **the sign of a rank-one boundary-Weyl object** — finite operator face,
>   moment face, and scalar Weyl face all read a **scalar condition at the single point `y=−0.16`** (the
>   first trivial zero), whose finite-section threshold is the bridge margin;
> - the no-margin **rate is a clean archimedean law, now derived** (not fitted):
>   `α_d(y_*) ≈ 4 + [4(1−ln2)+2ln|y_*|]/L̄_d` (`L̄_d=(1/d)Σ ln γ_j`) from exterior-Christoffel asymptotics —
>   base 4 (reciprocal-square) + hard-edge Vandermonde correction + Γ-boundary normalization; the empirical
>   `≈4.31+½ln|y_*|` is its `L̄_d≈4` finite-window specialization (the slope `½=2/L̄_d` drifts down with `d`, so
>   no universal slope) — *not* the zeros, *not* the primes;
> - the numerics are **certified prime-blind**: ζ and jittered-ζ (correlations destroyed) are
>   indistinguishable to 4–5 digits — every conditioning / margin / GUE observable carries zero RH content;
> - the tested approximations do not preserve the sign — band *and* low-rank truncations both flip it
>   (dropping a 0.8% tail sends the margin `+10^{−40}→−10^{16}`), so the theorem must be **sign-exact**.
>
> Each is a leap past the SOTA reflex of producing one more RH-equivalent positivity criterion: we instead
> **measured which directions carry the content and which are decoration**, and threw the decoration out.
>
> **The hunch (our leap of faith).** We bet the proof is a **source-built rank-one boundary-Weyl
> monotonicity theorem**: construct the bulk `H0_minus` (inertia `(d,1)`) and the single boundary atom
> `(y=−0.16, mass (2.5)^{−2})` from source data without zero-feeding, in the protector coordinate
> `x=y+0.16` (where the operator is near-Jacobi), regularized through a de Branges/Krein boundary at the
> **seam centre `s=½`**, and prove the scalar Weyl function nonnegative at all orders while keeping the
> exact sign-carrying tail. We may be wrong — this is a bet, not a theorem — but it is where we place it.
>
> **What we refuse to chase** (a discipline, not a dismissal of the mathematics — these are where we judge
> the SOTA *mis-aimed for this one archimedean sign*, and we spend no time on them):
> - a **prime-built generative flow / Hamiltonian** whose self-adjointness is RH (the `xp` / PT-symmetric
>   line read as an evolution) — Conjecture E;
> - any **prime-side positivity** criterion — the prime structure carries no polarization (Conjecture D);
> - **finite-`d` positivity sweeps** (Pólya–Jensen / Griffin–Ono–Rolen–Zagier eventual hyperbolicity) as
>   anything but *calibration* — they are height-limited and miss off-line zeros exactly like any finite
>   detector (the real Davenport–Heilbronn counterexample passes the `K_d` test through `d=55`);
> - **correlation / GUE / pair-statistics** arguments — certified RH-blind here (ζ ≡ jittered-ζ);
> - **low-rank / numerical / conditioning / deflation** arguments — the sign lives in the exponential tail
>   they discard;
> - **raw Weil test functions** — inadmissible at the seam centre; the route needs a singular boundary
>   extension, not a classical test space.
>
> **What stays genuinely open.** The seam finite-part construction supplies strong source-domain structure
> (canonical, regulator-/window-/gauge-fixed; `E=μ_E` identified), but the live theorem is still the
> **Krein–Langer rank-one positivity plus completion problem**: source-build `σ=ν'−a_*δ_{y_*}∈Π₁` as a
> closed boundary object, then prove the canonical Γ-atom repair crosses to `Π₀` — equivalently the
> **source-built scalar Weyl positivity** `s_d = a_*+1/m_d = 1/K_{ν'}(y_*) > 0 ∀d` (Uvarov form:
> `K_{ν'}(y_*,y_*)>0`). The canonical-`ξ` gauge-extraction lemma and the Christoffel/Uvarov identity give
> coordinates; the `N₁` carrier theorem gives anatomy, subject to its seam-boundary hypothesis. They do not
> prove the closed source object or the repair sign. Orthogonally, on the value axis, the
> Schanuel-for-prime-logs apex (A). Everything else — the tail `μ_E`, Jacobi near-banding, regulator
> invariance, even the `N₁` anatomy — is scaffolding around the **sign of one scalar** (`N₁` alone is not
> enough: Davenport–Heilbronn shares it and fails when `s_d` crosses 0).
>
> **SOTA reality-check (§10, 2026-06-22 literature sweep).** Almost the entire construction is classical apparatus
> reassembled in the seam coordinate: the moments `T_k` are **Voros secondary-zeta values** (Voros 2010); `s_d` is the
> inverse **Christoffel function = Hankel-determinant ratio** (Szegő); the Uvarov boundary-removal kernel (proof11) is
> **Uvarov 1969**; the `N₁→N₀` rank-one transition (proof10) is **Derkach–Hassi–de Snoo, JFA 188 (2002)**; the
> boundary-Weyl positivity overlaps **Suzuki (arXiv:1204.1827)**; and `Q_0≥0⟺RH` sits in the Weil/Li moment-positivity
> family. So proof10/proof11/comp80 are *re-derivations* (cite, claim no novelty). Of the two cells the sweep did
> **not** find verbatim: (i) the *exterior* hard-edge Christoffel asymptotic `s_d~∏γ_j^{−α}` (comp49/proof4) is now
> **closed** — it is the *non-regular* regime of Stahl–Totik theory, a derivable special case with **no RH content**
> (the rate is generic hard-edge geometry; the RH content is the sign `s_d>0`); and (ii) a *positivity-framed*
> Euler-product-vs-DH separator — which is exactly the open apex `s_d>0`, one open RH-bearing cell. Heed the
> **Conrey–Li (arXiv:math/9812166)** no-go: de Branges positivity fails for ξ.
