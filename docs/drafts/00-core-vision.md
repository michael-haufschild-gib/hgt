# The Vision — why this field exists

> "Γ satisfies no algebraic differential equation. The Riemann ξ and ζ inherit it, through
> the completion `Λ = Γ·ζ` and the functional equation: they are hypertranscendental, evading every algebraic differential equation." — Hölder, 1887.

> "The object is fixed by a constraint, not propagated by a flow." - Claude, 2026

---
## 0. There is no founding principle
  "Having a founding principle" — a generative rule from which everything follows by deduction — is "satisfying an algebraic differential equation." And hypertranscendence is precisely the absence of one. The request is self-defeating: a function with a generative founding principle is, by definition, not hypertranscendental.

  So Hölder 1887 isn't a missing founding principle — it is the founding theorem, and it's
  negative: it certifies that no generative rule exists. The math of hypertranscendental functions cannot be a theory of generative rules; it can only be a theory of obstructions (why no rule exists) and relations among values (transcendence theory). That's exactly what difference-Galois Siegel–Shidlovsky + DSS are.


## 1. The reason — two sources of hypertranscendence

The objects we most want to understand — `ζ`, the arithmetic `L`, and their completion `Λ` — obey no clean
differential rule of change, so the differential toolbox (differential Galois theory, the `E`/`G`-function
formalism, the period ring, Siegel–Shidlovsky) cannot reach their values or zeros. But the hardness has
**two distinct sources**, and the field exists to hold **both**:

- **Source A — the archimedean factor `Γ`.** One operator with a **polynomial** multiplier:
  `Γ(z+1) = z·Γ(z)`. In the *differential* direction this is maximally wild (Hölder 1887); in the
  *difference* (rescaling) direction it is **tame** — a single first-order recurrence. *This is the
  standing proof that replacing differentiation by rescaling works:* the rescaling tames exactly what the
  differential toolbox cannot.
- **Source B — the infinite prime base.** Infinitely many operators with **constant** multipliers,
  `σ_p : x_p ↦ p^{-1}x_p`, one per prime (`x_p = p^{-s}`). Here the rescaling thesis is a *conjecture*, not
  a theorem: the Euler product needs *all* the dilations at once, and unique factorization keeps the lanes
  independent — the "free flow."

The completed `Λ = Γ·ζ` carries **both** sources, welded by the functional equation `Λ(s) = Λ(1−s)`. No
existing theory holds the two together: differential Galois theory sees only Source A (as Hölder); a
single-base Mahler / difference theory sees only one lane of Source B. **The field is the category in which
the archimedean differential generator and the infinite prime difference base coexist and interact.**

## 2. The idea — rescaling, on both places

Mahler widened the differential rule into a *single* rescaling and reached transcendence facts the
differential toolbox could not. The field widens it twice over, and keeps both:

- across the **primes**: the simultaneous action of one dilation `σ_p` per prime —
  **multi-`q`-difference Galois theory** (Source B);
- across the **archimedean place**: the scaling generator `∂_s = −Σ_p (log p) θ_p` (the `s`-flow, whose
  `ζ`-regularized determinant is `Γ`) — the differential lane (Source A), held **as a generator inside the
  field, not as an obstruction outside it**.

Together they form one category `𝓜⁺` of `(σ_p, ∂_s)`-modules with difference Galois group `G_L⁺`. The
natural object is the **completed `Λ`**; the functional equation is the weld; the place at infinity is
**inside** the field.

## 3. What we are aiming for

Two questions that look separate from the classical side now look like two axes on one shared object:
- **where** the zeros sit (the Riemann Hypothesis);
- **what kind** of numbers the zeros are — whether they are genuinely independent (the transcendence
  question).

The aim is a theory in which RH is a feature of the geometry rather than an external wall, while the
transcendence/hypertranscendence axis remains wider than RH. The current weak unification is: one shared
archimedean locus, two distinct rigidities — FE-polarization positivity for RH and value-independence for
DSS. The single object on which both live and the precise form of the two-axis unification are developed
in `door/bucket-A1-A2-unification-the-carrier.md`, `door/bucket-the-seam-archimedean-obstruction.md`, and
`door/bucket-archimedean-generator.md`.

## 4. Where the new content is — the weld

Source A alone is classical (Hölder = differential Galois of the one archimedean place). Source B alone
has, so far, come back **BRIDGE**: stripped of the multi-`q` vocabulary the prime difference structure
**decouples prime-by-prime**, and a parent reproves it (the Door-2 verdict on the difference-Hölder G1 and
the corank dichotomy G3). So the genuinely native content is **neither source in isolation but their
interaction** — the **archimedean–prime weld**: the functional equation coupling the polynomial-multiplier
`Γ` to the constant-multiplier primes. That weld is the seam, and earning one irreducible theorem there is
the keystone (C5).

## 5. What counts as progress

The deliverable is the theory: each road laid on this ground — a native object made precise, a difficulty
located exactly, a gatekeeper turned into a theorem — is progress whether or not RH itself falls. RH is the
hoped consequence, not the only measure. The gatekeeper conjectures and their current status are in
`door/00-status.md`.
</content>
