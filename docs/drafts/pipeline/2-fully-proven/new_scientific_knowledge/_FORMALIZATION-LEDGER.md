# NSK stage-2 → stage-3 sweep — ledger

Standing goal: formalize unconditionally in Lean every proven theorem on every card in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge` and promote each card to
`docs/drafts/pipeline/3-formalized/`.

Folder held **11** cards on 2026-08-22 (the former `deninger/`, `other/` and
`projective-horizon/` subfolders were flattened into the top level).

## Card triage (2026-08-22)

| card | the one thing that blocks stage 3 |
|---|---|
| `bessel-order-intensity-hypertranscendence` | Dreyfus's DA→periodic-exponential classification; the card is building the whole parameterized difference-Galois theory from scratch, currently at the linearisation/descent step |
| `deninger-algebraic-cyclotomic-milnor-amplitude` | Garland: every element of the degree-two tame kernel of a number field is torsion (= finiteness of `K_2(O_F)`).  Tate's theorem gives it for `F = Q` only |
| `differential-variational-building-balance-law` | the Newton-polygon bound on the number of *restarts* of the twisted leading chain — equivalently that the slopes of a twisted product over `K[∂;δ]` have denominator at most `r` |
| `isogeny-tail-maurer-cartan-holography` | items 2–5 of its Lean-status list: the algebraic-group quotient sheaf/atlas, the DCF generic-point bridge for the logarithmic derivative, the finite-action quotient presentation.  Item 1 is closed in dimension one |
| `projective-horizon-full-symmetric-monodromy` | **(D4)** `∀ σ, ncard {τ | r τ = r σ} ≤ 2` and **(P)** preprimitivity of the geometric monodromy (still a hypothesis `hprim` everywhere) |
| `projective-horizon-one-step-postcritical-rigidity` | the parent card's `(4)` only — nothing else |
| `route-e-coprime-square-root-mobius-product-sign-law` | Matomäki–Radziwiłł's bilinear all-interval theorem (only to push `h` below `√x`; the `h = √x` law is already unconditional) |
| `route-e-growing-reciprocal-marker-low-breadth-transport` | Menon's 2026 short-interval Möbius mean square at `L/A ≍ X^{-1/2}` |
| `route-e-reciprocal-marker-mobius-hall-law` | Menon's 2026 short-interval Möbius mean square at `L = exp((log Y)^β)` |
| `universal-first-order-entire-cascade-unit-cost` | observability (`helim`) on a *general* cascade (Reduction III), where the derivative law is algebraic rather than polynomial |

## Working order

1. **projective-horizon pair** — one theorem `(D4)` plus `(P)`; closing them promotes **two** cards.
2. `universal-first-order-entire-cascade-unit-cost` — one induction, all sub-classes done.
3. `differential-variational-building-balance-law` — one Newton-polygon statement.
4. `torusless-…-jet-ampleness` — one geometric input.
5. `isogeny-tail-…-holography`, `bessel-…`, `deninger-…`, the three `route-e` cards.

## `(D4)`: the route, decided 2026-08-22

`criticalSchur_collisionSupport_ncard_le_two_of_fibre` already reduces the card's `(D)` to
`∀ σ, ncard {τ | r τ = r σ} ≤ 2`.  Analysis of every alternative (see the card) leaves exactly one
route, and it is standard tame ramification theory instantiated on the corpus's objects:

```text
(A) |Stab_I(σ)| = e(w / Q_σ)          mathlib Ideal.card_inertia_eq_ramificationIdxIn, applied to
                                      the Galois extension L / σ(F) and the DVR B_{Q_σ} ⊆ W
(B) |I| = e(w/A) = e(w/Q_σ)·e(Q_σ/A)  corpus natCard_criticalSchurIdealInertiaGroup_eq_… + tower
(C) I is cyclic                        corpus isCyclic_of_tame, instantiated
(D) I is faithful on sheets            corpus criticalSchurInertiaAction_injective
(E) one collision point                corpus criticalSchur_reducedFibre_eq_of_collisions   (D-f)
(F) hence every I-orbit has size e_{Q_σ}; an orbit lies inside one r-fibre, so e_{Q}≥2 forces
    σ ∈ collisionSupport; by (E) all such σ share one Q₀ and one r-fibre F; all their stabilisers
    have equal order, hence — I being cyclic — are the SAME subgroup, whose intersection is trivial
    by (D); so e(w/Q₀) = 1 and |I| = e(Q₀/A) = 2
(G) |F| ≤ 1 + v_w(f'(x)) = 1 + e(w/Q₀)·v_{Q₀}(𝔇_{B/A}) = 2
    corpus RootCongruenceValuationCount.card_congruent_roots_le_addVal_eval_derivative,
    with 𝔇_{B/A} = (f'(θ)) (monogenic) and v_{Q₀}(𝔇) = 1
    (= addVal_criticalSchurJacobianDetElement_eq_one through the Jacobian–different bridge)
```

Recorded dead ends, so no session repeats them:

* the different and the discriminant are **uninformative** about `t = e(w/Q₀)`: the tame identity
  `w(𝔇_{W/A}) = 2t − 1` holds for every `t`;
* pure combinatorics of a cyclic group acting faithfully with `Σ orbit ≤ 1 + t` does **not** force
  `t = 1` — `t = 6, |F| = 7`, orbits `{3,4}`, `|I| = 12` passes every count.  The stabiliser
  identity `(A)` is genuinely needed;
* corank one bounds the *embedding dimension* of the collision class, never its *length*.

## Log

- 2026-08-22 — ledger opened; card triage above; `(D4)` route fixed.

## 2026-08-22 — three general modules landed for `(D4)`

All three `lake build`-green and `#print axioms = [propext, Classical.choice, Quot.sound]`.

| module | content |
|---|---|
| `HTGeometry/TameInertiaOrderBound.lean` | `|Γ| ≤ addVal W x` for every `Γ`-fixed nonzero nonunit — the *cheap* half of `|I| = e`, via the tame ratio character of `TameInertiaCyclic` |
| `HTGeometry/ValuationSubringInertiaDictionary.lean` | `W` **is** the localization of a Dedekind `S ⊆ W` at its centre (`mem_iff_exists_div`), and the ideal-theoretic and valuation-theoretic inertia groups are **equal** as subgroups of `Gal(L/F)` (`inertia_eq_map`) |
| `HTGeometry/ValuationInertiaRamificationIndex.lean` | `Nat.card (W.inertiaSubgroup F) = ramificationIdxIn p T` for an arbitrary **Dedekind** base `R`, arbitrary base field `F` with `L/F` Galois, and arbitrary `T` with `IsIntegralClosure T R L` |

The corpus already had `|I| = e` at the *observation* field only
(`natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn` +
`criticalSchurIdealInertiaToInertia_injective`, and only as an injection).  The new statement is
uniform in the base field and in the base ring, which is what makes it apply to `Stab_I(σ)`.

**The next step is now fixed and needs no new mathematics.**  `Ideal.ramificationIdx_tower` gives,
for `A ⊆ B ⊆ C` with primes `p ⊆ Q ⊆ P`,

```text
P.ramificationIdx A = Q.ramificationIdx A * P.ramificationIdx B
```

with **no Galois hypothesis on the middle extension** — which matters, because `F_src/E` is exactly
the non-normal one.  Combining it with two applications of the new module (at `F = E`, base `A`, and
at `F = M_σ = σ(F_src)`, base `B = integralClosure A M_σ`) gives

```text
Nat.card (W.inertiaSubgroup E) = Q_σ.ramificationIdx A * Nat.card (W.inertiaSubgroup M_σ)
```

i.e. **orbit_σ = e(Q_σ / 𝔪_A)**.  Do *not* use `Ideal.ramificationIdxIn_mul_ramificationIdxIn`: it
requires `IsGaloisGroup` for the middle extension and is therefore unusable here.
