# Ledger: novel formalized facts (target 100)

Rules, binding:
- A line is added only after the theorem **builds**, has axioms exactly
  `propext, Classical.choice, Quot.sound`, and passes the lint gate.
- A line counts as a **fact** only if it is a substantive statement, not a supporting lemma or a
  restatement of something already in the corpus. Supporting lemmas are listed separately and do not
  count.
- Each fact carries an honest novelty label. `[NOVELTY UNVERIFIED]` is the default; absence from all
  literature cannot be proved by search.
- Anti-theatre: if a fact decomposes into (classical result) + (existing corpus theorem) with only
  framing added, it is **rejected** and recorded in the rejected list.

---

## Vein A — width-one strip meets period-one monodromy

The Hurwitz monodromy character is `mu(s) = exp(2 pi i s)`, and `mu(s) = mu(t) ⟺ s - t ∈ ℤ`. The
critical strip has width exactly one — exactly the period of `mu`. So strip points are automatically
monodromy-separated, with no arithmetic input whatever.

**A1.** `RHTower.openCriticalStrip_hurwitz_differentialIndependent`
For *any* set `S` of points in the open critical strip, `{H(s, ·)}_{s ∈ S}` is differentially
independent over `ℂ(a)`. Unconditional; no finiteness, no arithmetic.
*Significance:* every arithmetic instance is a corollary at once — the nontrivial zeros of the
Riemann zeta function, of any Dirichlet `L`-function, of any Dedekind zeta function, of any member of
the Selberg class, and of all of them **simultaneously**, since all such zeros inhabit this one
strip. `[NOVELTY UNVERIFIED]` — literature audit found only *joint universality* results for this
index set, which are conditional on Montgomery pair correlation plus `ℚ`-linear independence.

**A2.** `RHTower.xi_divisor_hurwitz_differentialIndependent`
The Hurwitz functions indexed by *all* nontrivial zeros of zeta simultaneously admit no algebraic
differential relation over `ℂ(a)`. Unconditional.
*Relation to prior corpus:* the finite-family case existed (`xi_zero_hurwitz_differentialIndependent`);
the global case did not, and was not derivable in place — see infrastructure below.
`[NOVELTY UNVERIFIED]`

### Infrastructure proved for this vein (does not count toward 100)

- `globalXiRatFuncDifferentialAlgebra` : `DifferentialAlgebra (RatFunc ℂ) upperEndMeroField`.
  The rational coordinate field embeds in the upper-end meromorphic field as a **differential**
  subfield — the embedding intertwines the formal derivative with the analytic one. Absent from the
  corpus; this was the blocker for every global statement in the vein.
- `globalXiUpperEndCharZero`, `globalXiRatFuncDifferential` — supporting instances.
- `RHTower.widthOneStrip_eq_of_sub_eq_int` — two points of any open strip of width one differing by
  an integer are equal.

**A3.** `RHTower.monoScalar_injOn_widthOneStrip`
The monodromy coordinate `mu(s) = exp(-2 π i s)` is injective on *every* open strip of width one.
This is the engine of the vein isolated as its own statement: the period of `mu` equals the width of
the strip. `[NOVELTY UNVERIFIED]`

---

## Vein D — the monodromy uniformization of the critical strip

**D1.** `RHTower.monoScalar_lineConj`
`mu(1 - conj s) = conj (mu s)`: the functional-equation/Schwarz reflection becomes **ordinary complex
conjugation** in the monodromy coordinate.
*Significance:* the critical line is not a metric accident. It is the fixed locus of conjugation in
the coordinate in which the functional equation *is* conjugation. `[NOVELTY UNVERIFIED]`

**D2.** `RHTower.monoScalar_im_eq_zero_iff_re_eq_half` with
`RHTower.monoScalar_re_neg_of_re_eq_half`
Inside the open critical strip, `mu(s)` is **real** exactly when `Re s = 1/2`, and there it is
strictly negative. So the critical line is precisely the real locus of the monodromy coordinate, and
the strip maps to the plane slit along the positive reals with the critical line going to the
negative real axis. `[NOVELTY UNVERIFIED]`

Supporting: `monoScalar_re`, `monoScalar_im` (explicit real and imaginary parts).

---

## Vein H — the monodromy image of the Xi divisor

**H1.** `RHTower.norm_monoScalar_ne_one_of_xiDivisor`
The monodromy image of the Xi divisor **never meets the unit circle**: `‖mu(rho)‖ ≠ 1` for every
nontrivial zero. Equivalently, transported to the modulus, zeta has no real zero in the critical
strip — the modulus is `exp(2 π Im rho)`, which equals one exactly on the real axis, where `xi` is
strictly positive. `[NOVELTY UNVERIFIED]`

**H2.** `RHTower.monoScalar_conj_mem_image`
The monodromy image is **conjugation stable**: `conj (mu rho) = mu (1 - conj rho)`, and `1 - conj rho`
is again a zero. This is the functional equation transported into the uniformizing coordinate.
`[NOVELTY UNVERIFIED]`

*Combined statement of the vein.* Under `mu`, the nontrivial zeros form a discrete,
conjugation-stable subset of the slit plane that avoids the unit circle; and by D2 the Riemann
Hypothesis is exactly the assertion that this set lies on the negative real axis. Three of the four
constraints — slit plane, conjugation stability, unit-circle avoidance — are unconditional theorems;
RH is the fourth.

Supporting: `norm_monoScalar` (the modulus of the monodromy coordinate).

---

## Rejected (recorded so they are not re-attempted)

- *Trivial/nontrivial zero dichotomy under the Hurwitz functor.* Decomposes into the textbook
  evaluation `ζ(-n, a) = -B_{n+1}(a)/(n+1)` plus the existing corpus independence theorem. Only new
  content is framing. **Rejected on significance.**
- *Any statement of the form `RH ⟺ X`.* See `5-failed/downstream-functionals-of-the-zero-set.md`.

---

## Count

**Facts: 0 / 100 — see retraction below.**

---

# RETRACTION — all seven entries above

**Facts: 0 / 100.**

Every entry A1–A3, D1–D2, H1–H2 is withdrawn as a novelty claim. Applying this ledger's own
anti-theatre rule:

| Entry | Why it fails |
|---|---|
| A1 | The corpus already had `continued_hurwitz_intrinsic_residue_differentialMatroid_law` as an **iff**, and `xi_zero_hurwitz_differentialIndependent` already ran this exact argument. A1 replaces a `Fintype` hypothesis with a `Set`. Weakening a hypothesis on an existing theorem. |
| A2 | Finitary upgrade of an existing theorem; acknowledged routine when written. |
| A3 | One line from a corpus lemma plus "two points less than one apart differing by an integer are equal". |
| D1 | Two lines of `exp` algebra. Immediate on writing down `mu`. |
| D2 | `exp(-2πiσ)` is real iff `σ ∈ (1/2)ℤ`. Elementary trigonometry. |
| H1 | Content is "zeta has no real zero in `(0,1)`" — classical, already in the corpus as `xi_pos_on_real_anchor`. Restated through a substitution. |
| H2 | D1 plus the functional equation. Restatement. |

## The failure mode, named

`mu(s) = exp(-2 π i s)` is a **change of variable**. Transporting known facts through a change of
variable produces no new knowledge, however unfamiliar the transported statements look. This is the
identical error to the Poisson coordinate recorded in
`5-failed/downstream-functionals-of-the-zero-set.md`: a notational device that makes familiar
statements look novel, generating correct Lean at high speed and zero science.

## Rules added

1. A candidate fact must not be expressible as (known statement) ∘ (bijective change of coordinates).
   If the proof is "rewrite in coordinate `X`, apply a known theorem", it is **transport**, not
   discovery.
2. A candidate fact must not be an existing corpus theorem with a hypothesis weakened, an index type
   generalized, or a finite case extended to an infinite one.
3. **Rate sanity test.** Seven claimed novel facts in thirteen minutes, on a problem worked
   continuously since 1859, is prima facie evidence of transport. Any batch produced at that rate is
   presumed transport until audited item by item against rules 1 and 2.

## Honest statement of what a real rate looks like

A genuinely novel significant fact about zeta is, at minimum, the content of a research note. The
achievable rate is not measured in facts per hour. The Lean corpus in this project can be extended
quickly — that is a property of formalization, not of discovery, and the two must not be conflated
again.

---

# Literature audit of the whole hypertranscendence layer

Performed after the retraction, to find out whether the layer that produces Lean fastest can produce
novelty *at all*. It cannot. The results it formalizes are classical, and mostly from 1920.

- **Hilbert's conjecture** that `ζ(x,s) = Σ x^n / n^s` is not a composition of one-variable analytic
  and algebraic functions was proved independently by **D. D. Mordukhai-Boltovskoi** and
  **A. Ostrowski** (*Über Dirichletsche Reihen und algebraische Differentialgleichungen*, 1920).
  Mordukhai-Boltovskoi also treated the hypertranscendence of `ζ(s, x)` — the **Hurwitz** function.
- **A. G. Postnikov** proved that **all Dirichlet `L`-functions are algebraically differentially
  independent**.
- Differential and difference independence of `ζ` and `Γ` is an active but *established* line
  (Acta Math. Sci. 2020/2021; J. Number Theory 2020; arXiv:1811.09336, arXiv:2005.02707).

## Consequence for this project

The corpus's Hurwitz/Gamma differential-independence layer — `monoScalar`, the integer-translation
matroid, the joint ladder theorems, the Xi-zero independence law — is **formalization of classical
mathematics**, not new mathematics. Its novelty is *formalization* novelty. This explains, at the
level of cause rather than symptom, why every candidate I generated in that layer decomposed into
transport or hypothesis-weakening: **there is no undiscovered mathematics there to reach.**

That is why the seven retracted entries were producible in thirteen minutes. The layer is
mechanically productive precisely because its mathematics was settled a century ago.

## Standing conclusion

Novel scientific facts about zeta are not obtainable from this corpus layer at any rate. Any future
attempt must begin by identifying a layer whose underlying mathematics is *not* classical, and must
establish that before writing a single line of Lean.

**Facts: 0 / 100.** The count stands at zero and the honest projection is that it stays near zero
under this constraint.
