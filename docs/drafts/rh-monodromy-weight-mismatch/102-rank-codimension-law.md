# 102 — The rank–codimension law (finite case, PROVED): the value-orbit dimension is the prime-exponent rank

**Register: SEARCH** (§§1–2 are a self-contained proof at promotion grade; §3 attack-as-false;
§4 the (XLD) connection and honest boundary; §5 the Lean brick). This is the general finite form
of doc 10 §7.3's miniature (`the "rank–codimension law"`, there proved only for two frequencies).
It is the constraint-side static skeleton under the (XLD) relay dynamics (doc 76/77) and the exact
steering-codimension of the blind cone (doc 10 §§2–5). Companion: `LogIndependence.lean` (the
independence/rank-0 face already banked), doc 09 (principal wall), doc 10 (blind cone).

## 1. The object

Fix a finite set `S = {n₁,…,n_d} ⊂ ℤ_{≥2}` of distinct integers. The **value-orbit map** is

>  Φ : ℝ → 𝕋^d,  Φ(t) = (n_j^{−it})_j = (e^{−i t·log n_j})_j,   𝕋 = ℝ/2πℤ,

the trajectory the ζ-truncation's `j`-th term's phase traces at a fixed real height as the height
varies (equivalently, the Dirichlet monomials' joint phase). Its frequency vector is
`ω = (log n₁,…,log n_d) ∈ ℝ^d`. The orbit `Φ(ℝ)` is a one-parameter subgroup of the torus; the
question doc 10 §7.3 left open in general is the **dimension of its closure** — the number of
independent directions the value orbit actually fills.

Two arithmetic gadgets attached to `S`:
- the **multiplicative relation module** `R := { k ∈ ℤ^d : ∏_j n_j^{k_j} = 1 }` (a subgroup of ℤ^d);
- the **prime-exponent matrix** `E ∈ ℤ^{P×d}`, `E_{p,j} = v_p(n_j)`, `P` = primes dividing some `n_j`.

## 2. The theorem [PROVED HERE]

> **Rank–codimension law (finite).** `closure(Φ(ℝ))` is a subtorus of `𝕋^d` of dimension
> `d − rank_ℤ(R) = rank_ℤ(E)`. Equivalently, the value orbit fills exactly as many dimensions as
> there are multiplicatively independent elements of `S`; each independent multiplicative relation
> `∏ n_j^{k_j}=1` removes exactly one dimension.

*Proof.* `Φ` is a continuous group homomorphism `ℝ → 𝕋^d`, so `Φ(ℝ)` is a connected subgroup and
`H := closure(Φ(ℝ))` is a **closed connected** subgroup of `𝕋^d`, i.e. a subtorus. By Pontryagin
duality closed subgroups of `𝕋^d` correspond to their annihilators in the character group
`ℤ^d = Hom(𝕋^d, 𝕋)`, and `H = (H^⊥)^⊥` with

>  H^⊥ = { k ∈ ℤ^d : the character x ↦ ⟨k,x⟩ is trivial on H }
>       = { k ∈ ℤ^d : ⟨k, Φ(t)⟩ = 0 in 𝕋 for all t }
>       = { k ∈ ℤ^d : t·⟨k,ω⟩ ∈ 2πℤ for all t∈ℝ }
>       = { k ∈ ℤ^d : ⟨k,ω⟩ = 0 }                                   (all-`t` forces the frequency to vanish)
>       = { k ∈ ℤ^d : Σ_j k_j log n_j = 0 }
>       = { k ∈ ℤ^d : ∏_j n_j^{k_j} = 1 }  = R.

(The step `⟨k,ω⟩=0`: if `c:=⟨k,ω⟩≠0` then `tc` ranges over all of ℝ as `t` does and cannot lie in
the discrete `2πℤ` for every `t`.) Hence `H^⊥ = R`, and `dim H = d − rank_ℤ(H^⊥) = d − rank_ℤ(R)`.

Finally `rank_ℤ(R) = d − rank_ℤ(E)`: by unique factorization `∏_j n_j^{k_j}=1 ⟺ ∀p, Σ_j k_j v_p(n_j)=0
⟺ E k = 0`, so `R = ker_ℤ(E)` and rank-nullity over ℚ gives `rank(R) = d − rank(E)`. Therefore
`dim H = rank_ℤ(E)`. ∎

Sanity locks (recovering doc 10 §7.3's miniature and §5's witness):
- `S={2,4}`: `E=[1 2]` (prime 2), `rank(E)=1` ⟹ `dim=1`. The orbit lies on the curve `(z,z²)`,
  `z=2^{−it}` — one real dimension, the single relation `4=2²`. ✓
- `S={2,3}`: `E=I₂`, `rank=2` ⟹ `dim=2`, full torus (Kronecker + ℚ-independence of `log2,log3`). ✓
- Doc 10 §5 Hurwitz `q=3` relation `(2/3)(8/3)=(4/3)²`: the same law in shifted-rational
  frequencies — the relation drops one dimension, collapsing steering onto the principal line.

## 3. Attack-as-false, and why this is not universality

- *Is `closure` really the whole subtorus `R^⊥`, not a dense-with-holes set?* Closure of a subgroup
  is a subgroup; a closed connected subgroup of `𝕋^d` is a subtorus, and Pontryagin duality is an
  order-reversing bijection on closed subgroups, forcing `H=(H^⊥)^⊥` exactly. No gaps. Solid.
- *Does it need Baker/transcendence?* No — only ℚ-linear relations among `{log n_j}`, and those are
  governed entirely by unique factorization (`Σ k_j log n_j=0 ⟺ ∏ n_j^{k_j}=1`), an elementary
  equivalence. This is why the rank-0 face is already elementary in `LogIndependence.lean`. The law
  needs no deep transcendence; it needs only FTA. (Contrast: algebraic *independence* of the values
  would be Baker territory; the orbit *dimension* is not.)
- *Why is this progress past the principal wall, not more universality?* Joint universality is a
  **density-in-a-region** statement and is **jet-blind** (doc 10 §7.1) and **blind on the ζ-line**
  (doc 10 Thm B). The rank–codimension law is a **exact-dimension** statement: it says precisely
  which subtorus the orbit fills, as an equality driven by the arithmetic, for every `S` including
  relation-bearing ones where universality says nothing. It is the sharp form of "steering
  codimension = relation rank" that doc 10 §§2–5 needed and only had as a 2-frequency miniature.

## 4. The (XLD) connection and the honest boundary

The (XLD) discriminator (doc 77 §3) is **not** phase equidistribution (ζ and D–H share it) but
whether a **coefficient conspiracy restores the walk** — i.e. whether a multiplicative relation
pins the value configuration onto a lower-dimensional set that *contains* the sustaining (off-line)
configuration. The rank–codimension law is exactly the geometry of that pinning:

- **ζ, prime-frequency basis:** the multiplicatively independent generators `{p}` have relation
  module `R=0`, so the value orbit is **full-dimensional** — no lower-dim set to pin a relay onto.
  This is the constraint form of ζ's relay **sub-criticality**: there is no algebraic subtorus the
  walk can be trapped on.
- **A genuine off-line zero** is precisely an imposed **relation among the values** (`Σ c_n n^{−ρ}=0`)
  — a drop in effective orbit dimension along the sustaining direction, the **super-critical** pin.

So (XLD)-proper = (this static rank–codimension skeleton) **+** the **jet-direction refinement**
(doc 10 §7.1): the value-orbit being full-dimensional is universality (blind); the *new* content is
that the **direction of approach** (`arg f′`, the sign of the depth increment) to a near-zero is
constrained by the same relation module. **Honest boundary — three things stay open:**
(i) the **infinite-frequency** rank–codimension law (all integers `n`, the genuine Dirichlet series;
doc 10 §7.3's actual open question — does the relation-module rank deficit still equal the lost
steering codimension when `d→∞`?); (ii) the **jet-direction** upgrade (does full orbit dimension +
a relation-free frequency set force the *increment sign* to be null-distributed?); (iii) whether
(i)+(ii) close the (EXC-ℓ)/(CHAIN-geo) rate `RelayLedger.lean` waits on. This card settles the
finite static half only; it does not by itself discriminate ζ from D–H (both are relation-free in
the truncation) — that is (ii).

## 5. What opens / the Lean brick

1. **Formalize the finite rank–codimension law** — the missing mathlib piece is the `n`-torus
   Kronecker closure (`closure of a one-parameter subgroup of 𝕋^d = R^⊥`); mathlib has only the
   1-dim `AddCircle.denseRange_zsmul_iff`. Build order: (a) the annihilator computation
   `H^⊥ = R` (elementary, above); (b) `R = ker E` via `Nat.factorization` (partly in
   `LogIndependence.lean`); (c) `dim = rank E`. The rank-0 subcase (dense orbit) can reuse the
   tree's `trig_time_average` (continuous Weyl) rather than a fresh Kronecker.
2. **The rank-1 containment** as the first verified step past the `{2,4}` miniature: for ANY single
   relation `∏ n_j^{k_j}=1`, the orbit lies in the codimension-1 subtorus `{x : ⟨k,x⟩=0}` — a clean
   `Φ(t)` computation, no closure theorem needed, generalizing doc 10 §7.3's witness to arbitrary
   `S` and `k`.
3. **The infinite-frequency law** (open): the rank deficit vs steering codimension as `d→∞`, the
   genuine-Dirichlet-series question — the object doc 10 §7.3 actually named.
4. **The jet-direction refinement** (open): pair the full-dimensional orbit with an `arg f′`
   coordinate; this is the (XLD)/§7.1 crux universality cannot see.
