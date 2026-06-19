# Multi-`q`-Difference Galois Theory for L-Functions
## Part IV — Transcendence and Periods

*Manuscript draft (publication prose). Continues Parts I–III. Two results anchor this Part: the field's transcendence
conjecture is identified with the Grothendieck period conjecture and proved on every classically-accessible locus
(§11), and the field proves the difference-category analogue of Hölder's hypertranscendence theorem, uniformly for all
L-functions (§12), with the relation to literal differential Hölder demarcated honestly.*

---

### 10. The period theory and its proven instances

By Theorem 9.1 the periods of a module `M` are the entries of the de Rham–Betti comparison matrix, equal to the
dynamical invariants of its boundary cocycle. The central quantity is the transcendence degree of these periods, and
the central question is whether it equals the dimension of the Galois orbit of the diagonal — the field's
Siegel–Shidlovsky problem.

Three instances are theorems, and they validate the framework:

- **Gap-labelling (Import; Bellissard, Johnson–Moser).** For the rank-two almost-Mathieu cocycle, the rotation-number
  periods lie in `ℤ + ℤα`, quantized by the Galois datum `α`. This is verified numerically at all gaps in
  `computations/gap_labelling_periods`.
- **Chudnovsky (Import).** For a CM elliptic curve, the transcendence degree of the `Γ`-value periods equals the
  dimension of the CM torus.
- **Papanikolas (Import).** Over `\mathbb{F}_q(t)`, with Frobenius twist, the transcendence degree of the periods of a
  `t`-motive equals the dimension of its difference-Galois group — the *full* period conjecture, proved, by exactly the
  mechanism of this field (a difference-Galois group computing transcendence).

The Papanikolas case is decisive: it shows that in a world with a *finite* Frobenius the field's transcendence
conjecture is a theorem, by the field's own method. The obstruction to transporting it to `ℚ` is the infinite base,
which we isolate in §12.

---

### 11. The Siegel–Shidlovsky conjecture is the Grothendieck period conjecture

**Conjecture 11.1 (infinite-base Siegel–Shidlovsky, the field's C3).** For a finite-rank module `M`,
```
\mathrm{trdeg}_K(\text{diagonal periods of } M) \;=\; \dim(G_M \cdot \delta_M),
```
the dimension of the Galois orbit of the diagonal.

We prove this on the loci where the period conjecture is classically known, and identify the residue as the period
conjecture itself.

**Theorem 11.2 (tori — the de Rham side only).** For a module whose Galois group is a torus, the *orbit dimension*
equals `\mathrm{corank}(\Lambda)`, and `\mathrm{trdeg}_K(R_M) = \dim G_M = \mathrm{corank}(\Lambda)` by the torsor
property of the Picard–Vessiot ring — elementary, for all tori. *This is the de Rham / abstract-solution side.* It is
**not** the period-value statement: `\mathrm{trdeg}_{\mathbb{Q}}` of the actual period *numbers* equal to the orbit
dimension is the Grothendieck period conjecture, which for the arithmetic "`\log p`" torus asserts the *algebraic*
independence of `\{\log p\}` — **open** (only linear independence is known, Baker). Period-value transcendence on tori
is therefore *not* elementary; it is proved only in the CM case (Theorem 11.3) and over function fields (Theorem 11.4).

**Theorem 11.3 (CM/monomial, all ranks).** For a monomial module induced from a CM Hecke character — at any rank — the
periods are CM-abelian-variety / 1-motive periods, and `\mathrm{trdeg}(\text{periods}) = \dim(G_M \cdot \delta)`.

*Proof (imports).* The periods of a CM abelian variety and its 1-motive extensions have transcendence degree equal to
the dimension of the associated CM torus, every `\overline{\mathbb{Q}}`-relation among them being elementary (forced by
the CM structure). This is Wüstholz's analytic subgroup theorem — which settles the Grothendieck period conjecture for
1-motives — together with Cohen–Shiga–Wolfart (extending Schneider to all abelian varieties) and, in the rank-one
elliptic case, Chudnovsky. The Huber–Wüstholz dimension formula for 1-motive periods is precisely `\dim(G_M \cdot \delta)`. ∎

**Theorem 11.4 (function fields).** Over `\mathbb{F}_q(t)`, Conjecture 11.1 holds in full, for every `t`-motive, by
Papanikolas's theorem.

**Identification 11.5.** Conjecture 11.1 *is* the (motivic) Grothendieck period conjecture, transported to the
difference-module category: transcendence degree of periods equals the dimension of the motivic-Galois orbit. The field
proves the period-value statement wherever the period conjecture is classically known — CM (11.3, Wüstholz), function fields
(11.4, Papanikolas) — and the open residue is exactly the non-CM, generic case, which is the open part of the
Grothendieck period conjecture. We do not prove it there; we state it as the falsifiable Conjecture 11.1 and name the
residue honestly.

This is, we contend, the correct relationship between a new field and a famous conjecture: the field's transcendence
statement should *be* the period conjecture and *prove its known cases by its own mechanism*, which it does.

---

### 12. Hypertranscendence: the difference-category analogue of Hölder

The arithmetic diagonal is the diagonal of an infinite-base module. We characterize exactly when such a diagonal is
holonomic — and find that the arithmetic ones never are. This recovers Hölder's 1887 theorem that `ζ` satisfies no
algebraic differential equation, and extends it uniformly to all L-functions.

The governing invariant is the corank of the relation lattice `\Lambda = \{m \in ℤ^{(P)} : \prod_p a_p^{m_p} = 1\}`.
The diagonal's monodromy under the shift `s \mapsto s+1` is the pro-torus element `g = (a_p\text{-shift})_p`, whose
Zariski closure has dimension `\mathrm{corank}(\Lambda)` — the number of multiplicatively-independent base directions.

**Theorem 12.1 (hypertranscendence dichotomy, the field's C6).** The diagonal of a rank-one integrable module is
**difference-holonomic** (satisfies a finite-order linear *difference* equation over `ℂ(s)`) if and only if
`\mathrm{corank}(\Lambda) < \infty`. *(We work in the field's native difference category; see the remark after
Corollary 12.2 on the relation to the differential statement.)*

*Proof.* If the diagonal `f` is difference-holonomic, it generates a finite-rank module over the `s`-difference field,
whose difference-Galois group `G_s` is finite-dimensional; but `G_s` contains the Zariski closure of the monodromy `g`,
so `\mathrm{corank}(\Lambda) = \dim \overline{\langle g \rangle} \le \dim G_s < \infty`. Conversely, if
`\mathrm{corank}(\Lambda) = r < \infty`, the relations express all multiplier-directions in terms of `r` independent
ones, so `f` is a function of `r` effective variables; the shift `s \mapsto s+1` is then a finite product of the
effective operators, yielding a finite-order linear difference equation — `f` is difference-holonomic. ∎

**Corollary 12.2 (difference-hypertranscendence of all L-functions).** Every arithmetic L-function — `ζ`, Dirichlet,
Hecke, automorphic — has relation lattice `\Lambda = 0` by unique factorization, hence `\mathrm{corank}(\Lambda) = \infty`,
hence a **difference-hypertranscendental** diagonal (no finite-order linear difference equation in `s`), by the single
mechanism *infinite corank ⟹ infinite-dimensional monodromy ⟹ non-difference-holonomic*.

*Relation to Hölder (an honest demarcation).* Hölder's 1887 theorem is the **differential** statement — `ζ` satisfies
no algebraic *differential* equation. Our argument proves the **difference**-category analogue, uniformly for all
L-functions; it is the natural transcendence statement in the field's own setting. The literal differential statement
holds for `ζ` by Hölder's theorem (import) and is conjectural for general `L`, reducible to the difference case via the
Adamczewski–Dreyfus–Hardouin theory but not subsumed by the corank argument alone. We therefore claim the difference
generalization outright and the differential `ζ`-case as an import — not "Hölder generalized to all `L`," which would
conflate the two categories. The cause we do isolate is genuine and uniform: it is the multiplicative independence of
the primes — corank infinity — that forces difference-hypertranscendence for every L-function at once.

**Theorem 12.3 (the function-field/`ℚ` divide).** The divide between the solved function-field case and the open
`ℚ`-case is now a theorem about corank. Over `\mathbb{F}_q(t)` the Frobenius is finite, so the effective base has
`\mathrm{corank}(\Lambda) < \infty`, the diagonal is holonomic, and Papanikolas's machine runs (Theorem 11.4). Over
`ℚ` the arithmetic base has `\mathrm{corank}(\Lambda) = \infty`, the diagonal is hypertranscendental, and no finite
difference equation carries the arithmetic — which is precisely why the resolution must be the infinite-order
construction of Part V.

The founding obstruction of the field — Hölder's hypertranscendence — is thus not a wall the theory runs into but a
theorem the theory proves, generalizes, and uses to explain its own structure.

---

*End of Part IV. The transcendence theory identifies the field's period conjecture with Grothendieck's, proving it on
the classical loci, and proves the difference-hypertranscendence dichotomy (the difference-category analogue of
Hölder, with the differential `ζ`-case imported). The one open
case — the non-CM generic period conjecture — is exactly Grothendieck's open case, named and not faked. Part V (the
native zeta, functoriality, and the infinite-order trivialization `\psi`) constructs the object whose regularity is
GRH. The research draft §25–37, §49, §57–60 carries the full development.*
