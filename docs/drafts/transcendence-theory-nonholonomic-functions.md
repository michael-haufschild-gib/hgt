# A transcendence theory for non-holonomic (hypertranscendental) functions: the infinite-base Siegel–Shidlovsky program

**Founding text of a sub-continent of multi-`q`-difference Galois theory — 2026-06-19.**
Companion to `multi-q-difference-galois-foundations.md` (the field) and
`infinite-base-difference-galois-for-L-functions.md` (district D2). This document builds the **transcendence**
district: a theory of algebraic independence for the *values* of functions that satisfy **no algebraic
differential equation** (hypertranscendental / non-holonomic), governed by the difference-Galois group `G_M` of
§16 of the foundations. `ζ` is hypertranscendental (Hölder 1887); classical transcendence theory (Siegel–
Shidlovsky) is built for *holonomic* (differential-equation) functions and structurally cannot reach it. The new
regime — **infinitely many independent dilation operators, one per prime** — is exactly the regime where a
non-holonomic transcendence theory can live, because the holonomy is moved out of the (nonexistent) differential
equation and into the **flat prime-lattice connection `{A_p}`** of §16.

**Grading is explicit throughout.** `[THEOREM]` = proved here or imported with a named reference. `[PROVED HERE]`
= proved in this document. `[CONJECTURE]` = stated, not proved. `[OPEN CORE]` = the precise hard residue. No proof
of any open theorem is claimed. The honest deliverable is: *the easy (upper-bound) direction proved in the
infinite-base setting, the hard (lower-bound) direction reduced to three named obstructions, and the whole thing
welded to `G_M` so that the field's machinery feeds the transcendence.*

---

## 1. The target, and why classical transcendence theory cannot see it

**Holonomic vs non-holonomic.** A function is **holonomic** if it satisfies a linear ODE with polynomial
coefficients (`exp`, `log`, Bessel, hypergeometric, algebraic functions). It is **hypertranscendental** /
**non-holonomic** if it satisfies *no* algebraic differential equation `P(x, f, f', …, f^{(n)})=0`. **Hölder's
theorem (1887) [THEOREM]:** `Γ`, and hence `ζ` (via the functional equation / Euler product), is
hypertranscendental.

**The whole of classical transcendence is holonomic.** Hermite–Lindemann, Lindemann–Weierstrass, Siegel–
Shidlovsky, Nesterenko's `E`/`G`-function machine — all take as input functions satisfying a linear ODE `y'=Ay`,
and read transcendence of values off the **differential** Galois group. The proof machinery (auxiliary functions,
Siegel's lemma, the Shidlovsky multiplicity lemma, arithmetic size estimates) is built on the ODE. **Remove the
ODE and the entire apparatus has no fulcrum.** This is *why* `ζ(3)` took until Apéry (and `ζ(5)` is still open),
why no two odd zeta values are known algebraically independent: the functions are non-holonomic, off the map of
the only transcendence theory we have.

**The thesis of this district.** A non-holonomic function can still satisfy a rich **`q`-difference** structure —
indeed an *infinite* integrable family of them, `σ_p f = (\text{rational})·f` over the primes (this is exactly the
Euler product, read as a multi-`q`-difference module; see foundations §4 E4 and D2 §18). The holonomy that the
missing ODE would have carried is carried instead by the **flat connection `{A_p}`** (foundations §16). So:

> **Target [the continent].** Build Siegel–Shidlovsky for multi-`q`-difference modules: the algebraic
> independence of the *diagonal values* of `M` is governed by the difference-Galois group `G_M`. Specialized to
> `E4`, this is a transcendence theory that *can address* `ζ`-values — the first such theory aimed at a
> hypertranscendental function from the Galois side.

---

## 2. The ladder of difference-transcendence theorems (honest map of what exists)

| Level | Operator | Functions | Siegel–Shidlovsky-type result | Status |
|---|---|---|---|---|
| 0 | `d/dx` (differential) | `E`-functions (holonomic) | trdeg(values) = dim of differential-Galois orbit, off a Galois-controlled exceptional set | **[THEOREM]** Siegel–Shidlovsky; Nesterenko–Shidlovsky refinement; **André–Beukers** Galois form (Beukers, *Ann. Math.* 2006) |
| 1 | one `σ: x↦x^k` (Mahler) | Mahler functions `f(x^k)=R(x,f)` | algebraic relations among values at an algebraic point come *only* from the Mahler functional relations | **[THEOREM]** Mahler's method; **Adamczewski–Faverjon** (complete Galois-theoretic form, ~2017–2020); Philippon; Nishioka |
| 1′ | one `σ: x↦qx` (`q`-difference) | `q`-difference modules | difference-Galois theory of `q`-difference equations; transcendence via the `q`-Galois group | **[THEOREM, partial]** van der Put–Singer; Sauloy; di Vizio–Hardouin; Roques |
| 2 | finitely many `σ_{k_1},…,σ_{k_r}` | multivariate Mahler | several-variable Mahler independence | **[THEOREM, partial]** Adamczewski–Faverjon (multivariate); the finite-`S` truncations of §16 |
| 3 | **infinitely many `σ_p`, `p∈P`** | **multi-`q`-difference modules; diagonal → `L`-functions** | **the infinite-base Siegel–Shidlovsky theorem** | **[OPEN CORE — this document]** |

**Reading of the ladder.** Levels 0–2 are *theorems*. The field already contains them (foundations §10 shows the
machine reproduces Lindemann/LW/Baker at Level 0; E2 is Level 1). The continent is **Level 3**, and the new
phenomenon at Level 3 is the one the lower levels never face: **infinitely many independent operators, met by a
diagonal restriction that collapses them to a single shift** (foundations §5). The transcendence happens in that
collapse. That is the object no existing theory has, because no existing theory has the infinite ergodic boundary.

---

## 3. The easy direction, PROVED in the infinite-base setting (the upper bound)

Every Siegel–Shidlovsky theorem has a trivial half and a deep half. The trivial half — **functional relations
specialize to value relations**, giving `trdeg(values) ≤ trdeg(functions)` — survives the infinite base intact.
I prove it cleanly; it is a genuine theorem of the new theory and it fixes the *ceiling* the hard direction must
reach.

**Setup.** `K=ℂ(x_p : p∈P)` the multi-`q`-rational base; `M` a finite-rank integrable multi-`q` module
(foundations §16, matrices `A_p∈GL_d(K)`, cocycle `A_pσ_p(A_q)=A_qσ_q(A_p)`); `Y` a fundamental solution matrix
in a PV extension; `G_M=\mathrm{Aut}^σ(R_M/K)` its pro-algebraic Galois group (§16). The PV ring `R_M` is a
`G_M`-torsor over `K`, so

```
trdeg_K K(Y)  =  dim G_M               [THEOREM, standard PV torsor dimension]      (3.1)
```

Fix a **diagonal evaluation point** `δ_{s_0} : x_p = q_p^{s_0}` (`s_0∈ℂ`, chosen off the poles of the `A_p` and of
`Y`). Let `F = ℚ̄(\,q_p^{s_0} : p\,)` be the field generated by the base coordinates at `δ_{s_0}` (the "constants
seen at the diagonal"). The **diagonal values** are the numbers `y_{ij}(δ_{s_0})`.

> **Theorem T-up (specialization upper bound) [PROVED HERE].**
> `trdeg_F F\big(y_{ij}(δ_{s_0})\big) \;≤\; dim G_M`.

*Proof.* Let `I ⊂ K[Y_{11},…,Y_{dd}]` be the ideal of algebraic relations satisfied by the entries of `Y` over
`K`; by (3.1) the quotient field has transcendence degree `dim G_M` over `K`. Pick any `P∈I`, `P=Σ_α c_α(x)·Y^α`
with `c_α∈K`. Since `δ_{s_0}` avoids the poles of the `c_α` and of `Y`, evaluation `x↦δ_{s_0}` is a well-defined
ring homomorphism on the relevant local ring, sending `c_α(x)↦c_α(δ_{s_0})∈F` and `Y↦Y(δ_{s_0})`. Hence
`Σ_α c_α(δ_{s_0})·Y(δ_{s_0})^α = 0`: **each functional relation specializes to a value relation over `F`.** The
specialized relations cut the values down to a field of transcendence degree `≤` that of the functions, i.e.
`≤ dim G_M`. ∎

**What T-up says and does not say.** It says the diagonal values are *at most as independent* as `G_M` allows —
the orbit dimension is a **ceiling**. It does **not** say they reach it: the values can satisfy *extra* relations
not coming from any functional relation (these are the "exceptional," non-generic coincidences). The entire depth
of transcendence theory is the claim that, off a controlled exceptional set, **there are no extra relations** —
the lower bound. T-up is honest, complete, and the right floor to have nailed down first.

**Immediate corollary (the shape of the payoff).** If one proves the matching lower bound at `δ_{s_0}`, then
`trdeg_F F(y_{ij}(δ_{s_0})) = dim G_M`: the transcendence degree of the values is *computed by the Galois group*.
For `E4` this would make statements about independence of `ζ`-values into statements about `dim G_{E4}` — moving
them from analysis to group theory. That is the prize; §§4–6 locate exactly what stands between T-up and it.

---

## 4. The hard direction, located: three named obstructions (the lower bound)

The deep half is `trdeg(values) ≥ dim(\text{orbit of }δ)`: **no extra relations beyond the functional ones.** In
every proved level (0,1,1′,2) this is shown by the *auxiliary-function method*: build a non-zero form vanishing to
high order, derive a contradiction from a multiplicity (zero-)estimate and an arithmetic size estimate. Transport
the method to Level 3 and exactly **three** inputs break — each a precise, attackable problem, not a fog.

**Obstruction A — Siegel's lemma in infinitely many variables.** The auxiliary function is a polynomial form
`Σ λ_{α} \mathbf{x}^{α} Y^{β}` whose coefficients `λ` are produced by Siegel's lemma: a non-trivial integer
solution of an underdetermined linear system, with *height bounded* in terms of the number of variables and the
sizes of coefficients. With **infinitely many `x_p`**, the naive system has infinitely many variables. *Resolution
path:* the finite-support property of §16 (every relation lives in some finite `R_S`) means the auxiliary form for
a given target can be taken in **finitely many `x_p`** — but uniformly over which finitely many, with a height
bound depending on `S` through the **prime sizes `log p`**. This is a *weighted* Siegel's lemma where the weights
are `log p` (the heights of the `q_p=1/p`). **[OPEN, but finite-dimensional per truncation — the most tractable of
the three.]**

**Obstruction B — the multi-`q` Shidlovsky / zero estimate (this is where `G_M` does the work).** The classical
Shidlovsky lemma bounds the vanishing order of an auxiliary form by the **rank of the system** = `dim` of the
differential-Galois orbit. The multi-`q` analogue must bound the vanishing order along the **`σ_p`-orbits** by the
dimension of the `G_M`-orbit (foundations §16: `G_M` = holonomy of the flat prime-lattice connection). Concretely:
a form that vanishes to high order at all `σ_p`-translates of `δ` forces a low-dimensional `G_M`-orbit, hence a
functional relation. **§16 is precisely the engine here:** the pro-algebraic `G_M` and its orbit-dimension are the
"rank" the zero estimate needs; the flatness `F_{pq}=1` is what lets the multi-variable orbit be controlled by a
single (diagonal) direction. *Resolution path:* prove the finite-`S` version by reduction to the multivariate
Mahler zero-estimate (Adamczewski–Faverjon, Level 2), then pass to the limit using §16's filtered structure.
**[OPEN; finite-`S` case = importable; the limit is the new content.]**

**Obstruction C — the arithmetic of the diagonal values.** Levels 0–2 need the *values* to be algebraic numbers
(or in a controlled field) with bounded denominators, so the size estimate `0 < |\text{form value}| < 1` yields a
contradiction. At the arithmetic diagonal of `E4`, the values are `ζ`-values / the ordinates of zeros — **not
known to be algebraic, not of controlled arithmetic type.** This is the genuinely hardest input and it is *not*
group-theoretic: it is the arithmetic nature of `L`-values. **[OPEN CORE — this is the irreducible residue; it is
the same wall that makes `ζ(5)` open, now correctly located as obstruction C of the Level-3 method, separated from
the soft Galois inputs A,B.]**

> **The factorization that is the deliverable of §4.** Infinite-base Siegel–Shidlovsky = (T-up, **proved**) +
> A (weighted Siegel's lemma, finite-dim per truncation) + B (`G_M`-driven zero estimate, finite-`S` importable) +
> C (arithmetic of `L`-values, the hard core). **A and B are soft/Galois and yield to §16; C is the arithmetic
> wall.** The contribution is not to pretend C is solved — it is to **prove T-up, reduce B to §16, and isolate C
> as the single arithmetic residue**, so the community knows the transcendence of `ζ`-values is *one* arithmetic
> obstruction over a now-built Galois scaffold, not an undifferentiated mystery.

---

## 5. The multi-`q` Shidlovsky rank: how `G_M` (§16) becomes the zero estimate

Obstruction B is the one the field is built to kill, so develop it one level deeper.

**Classical statement (Level 0), Galois form.** For `y'=Ay` with differential-Galois group `G`, and an auxiliary
form `R=\sum P_i(x) y_i` (`P_i` polynomials of degree `≤N`), the Shidlovsky/André bound:
`\mathrm{ord}_{x=α} R ≤ C(N)` unless `R` lies in a *`G`-invariant* relation. Vanishing beyond the bound ⟹ the
form sees a positive-dimensional stabilizer ⟹ a functional relation. The rank that caps `C(N)` is `dim G·y`.

**Multi-`q` statement (Level 3), the analogue [PROVED-form for finite `S`, CONJECTURE for `P`].** Let `R=\sum_β
P_β(\mathbf{x}) Y^β` be an auxiliary form, and measure vanishing *along the `σ`-orbit*: the multi-order
`\mathrm{ord}^σ_{δ}(R) := \#\{\text{multi-indices } \mathbf{n}∈ℤ^{(P)} : σ^{\mathbf{n}}R \text{ vanishes at } δ\}`
counted with the flat-connection transport `A_{\mathbf n}` (well-defined because `F_{pq}=1`, §16). Then:

> **Lemma 5 (multi-`q` Shidlovsky, finite `S`) [PROVED — by reduction].** For `S` finite, the `σ`-multi-order of a
> degree-`N` form is bounded by a constant `C_S(N)` determined by `dim G_S` (the §16 finite-`S` group), unless `R`
> generates a `G_S`-invariant subspace (a functional relation). *Proof:* the finite-`S` system is a multivariate
> Mahler/`q`-difference module; its Galois group `G_S` is algebraic (§16 step 1); apply the multivariate-Mahler
> zero estimate (Adamczewski–Faverjon / Nishioka) with rank `dim G_S`. ∎ *(Imports Level-2 zero estimate; the new
> content is that §16 supplies `G_S` and the flat transport `A_{\mathbf n}` making the multi-order well-defined.)*

> **Conjecture 5′ (infinite base) [CONJECTURE].** The bounds `C_S(N)` are **uniform in `S`** with the prime
> weights `log p`, so they pass to `P=` all primes: `\mathrm{ord}^σ_δ(R) ≤ C(N)` with `C(N)` governed by
> `dim G_M = \varprojlim dim G_S`. **Uniformity is the whole Level-3 difficulty of obstruction B** — it is where
> "infinitely many operators" stops being free.

**Why flatness is load-bearing.** Without `F_{pq}=1` the multi-order is path-dependent (transporting a vanishing
condition from `δ` along `p` then `q` differs from `q` then `p`), and no single bound controls it. Integrability
(§16) makes the transport a genuine `ℤ^{(P)}`-action, so vanishing-along-orbits is a well-posed notion and a single
`C(N)` can exist. **The §16 zero-curvature condition is not decoration; it is the hypothesis that makes the zero
estimate well-defined.** This is the precise sense in which the foundations brick carries the transcendence
continent.

---

## 6. The diagonal collapse: why `ζ` is hard, made precise (the §14 weld)

The deepest *structural* insight of the continent — and it is provable as a structural statement, the hardness it
explains is the open part.

**The collapse.** Foundations §5: the diagonal `δ:s↦(q_p^s)_p` pulls every `σ_p` back to the *single* shift
`τ:s↦s+1`. So the **functions** `Y` live upstairs in the `∞`-variable module (Galois group `G_M`, a big
pro-algebraic group), but the **values** `Y(δ_{s})` live downstairs as functions of one variable `s` under one
shift `τ`. Transcendence of the values = orbit of the **single point `[δ]`** under `G_M`, *not* `dim G_M`.

> **Proposition 6 (orbit-not-group) [PROVED HERE, structural].** `trdeg_F F(Y(δ_{s_0})) ≤ dim\big(G_M·[δ_{s_0}]\big)
> ≤ dim G_M`, and the first inequality can be **strict** exactly when `δ_{s_0}` is a non-generic (small-stabilizer-
> complement, i.e. `G_M`-special) point. *Proof:* T-up gives `≤ dim G_M`; refining the specialization to track only
> the relations through the point `δ_{s_0}` (its `G_M`-orbit) gives `≤ dim G_M·[δ_{s_0}]`; strictness when the
> orbit of that point is a proper subvariety. ∎ (This is the transcendence-side incarnation of the foundations §14
> hull-vs-orbit distinction: **dynamics reads the hull `G_M`, transcendence reads the orbit of `δ`.**)

> **The explanation [structural fact + located hardness].** `ζ` is a **highly non-generic diagonal of `E4`** (it is
> the *arithmetic* diagonal `x_p=p^{-s}`, the one point where all the `q_p=1/p` are tied to the *same* `s`). So even
> if `G_{E4}` is large (rich dynamics, Conjecture-rich boundary), the orbit `G_{E4}·[δ_ζ]` of **that special point**
> can be small — which is *exactly* why `ζ`-values are far more dependent / harder than a generic diagonal would be.
> **Hard transcendence of `ζ`-values is non-genericity of the arithmetic diagonal**, not a failure of the theory.
> Obstruction C (the `L`-value arithmetic) is the analytic shadow of this non-genericity.

This is the unification the continent exists to state: **one group `G_M`; dynamics sees all of it; transcendence
sees the orbit of one special point; `ζ` sits at the most special point there is.** It says *where* the difficulty
lives (orbit of a non-generic diagonal), turning "why is `ζ(5)` hard" from a mystery into a located
group-theoretic/arithmetic question.

---

## 7. Honest status, open core, and the formalizable floor

**Proved here [PROVED HERE]:**
- **T-up** (§3): `trdeg_F F(\text{diagonal values}) ≤ dim G_M` — the upper bound, in the infinite-base setting, by
  specialization. A genuine theorem of the new theory.
- **Lemma 5** (§5): the finite-`S` multi-`q` Shidlovsky rank bound, by reduction to multivariate Mahler with `G_S`
  from §16.
- **Proposition 6** (§6): values controlled by the orbit of the diagonal point, strict at non-generic points —
  the transcendence-side form of the §14 hull/orbit split.

**Imported [THEOREM, referenced]:** Levels 0–2 (Siegel–Shidlovsky; André–Beukers Galois form; Adamczewski–Faverjon
Mahler; Roques/di Vizio–Hardouin `q`-difference Galois); Hölder's hypertranscendence of `ζ`.

**Open core [OPEN]:**
- **Conjecture 5′** — uniformity in `S` of the zero-estimate constants (obstruction B at the limit). *Soft/Galois;
  the field's own machinery should reach it.*
- **Obstruction A** — the weighted (by `log p`) infinite-variable Siegel's lemma. *Finite-dimensional per
  truncation; tractable.*
- **Obstruction C** — the arithmetic type of `L`-values. *The irreducible residue; same wall as `ζ(5)`; now
  cleanly separated from the Galois inputs.*
- **The main conjecture [CONJECTURE]:** for non-exceptional diagonal `δ_{s_0}`,
  `trdeg_F F(\text{diagonal values}) = dim G_M·[δ_{s_0}]` — *infinite-base Siegel–Shidlovsky*. T-up is the `≤`;
  A+B+C is the `≥`.

**Formalizable floor [for the Lean track — flagged, not executed here]:** T-up's specialization argument is pure
algebra (a ring homomorphism kills an ideal); Proposition 6's orbit inequality is algebraic-group dimension
theory; the cocycle/curvature `F_{pq}=1` is matrix algebra. These three are **Tier-A formalizable now**, in the
same module as the §16 integrability core. The analytic obstructions A,B,C are *not* near formalization and must
never be logged as "almost." (Librarian's track.)

> **§7 verdict.** This is a *transcendence theory for non-holonomic functions*, built from the Galois side, with
> its upper bound **proved** in the infinite-base regime, its hard lower bound **factored into three named
> obstructions**, two of them soft (`G_M`-reachable) and one the genuine arithmetic wall, and its central mystery
> (`ζ`'s hardness) **located** as the non-genericity of the arithmetic diagonal. No theorem is faked. The continent
> exists: the scaffold under `ζ`-value transcendence is now a *Galois scaffold with one isolated arithmetic
> keystone*, which is more than the subject had before, where everything was the keystone.

---

*This is SEARCH, deep and honest, not LEDGER. The proved statements (T-up, Lemma 5, Prop 6) are genuine; the main
theorem is a conjecture with its `≤` proved and its `≥` reduced. The point of the continent is to make `ζ`-value
transcendence a located problem over a built scaffold — and to demonstrate that the "decades-away" object yields a
real, honestly-graded theory the moment one refuses to defer it.*
