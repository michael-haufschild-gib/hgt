# Prime-valuation fusion-completion lower bound

- **ID:** `prime-valuation-fusion-completion-lower-bound`
- **Stage:** 3-formalized
- **Type:** GENERAL HT MASTER THEOREM / UNIVERSAL COMPLETION LAW
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY PROVISIONAL: HIGH]`
- **Parents:**
  `../../3-formalized/new_scientific_knowledge/prime-residue-valuation-interaction-superselection-law.md`,
  `../../3-formalized/new_scientific_knowledge/prime-residue-analytic-source-creation-tower.md`

## One-sentence law

For a tail-complete finite prime source, every differential field that contains the complete
depth-zero carrier layer and is closed under prime-valuation fusion must contain arbitrarily
large jointly differentially independent carrier rectangles; the exact forced rank through
depth `d-1` is

```text
d * product_i |A_i|.
```

Thus finite source multiplication forces unbounded differential rank in every fusion-complete
analytic realization.

## Setup

Let `I` be finite, let every `A_i` be a finite pointed set with distinguished point `1`, and put

```text
A = product_i A_i.
```

Let `y : primes -> A` be tail-complete: every value of `A` occurs on every cofinite prime tail.
For `z in A`, let `b_z` be the anchored tensor basis function

```text
b_z(x) = product_i [z_i = 1 or x_i = z_i].
```

Write `V_r(b_z)` for the prime-power column supported at `p^(r+1)` with coefficient
`b_z(y(p))`, and let `F_(r,z)` be its faithful upper-end meromorphic Dirichlet germ.

Prime-valuation fusion is the external graded operation

```text
V_e(f) star V_r(g) = V_(e+r+1)(f*g).
```

It is bilinear, symmetric and associative, and the rotated logarithmic derivation satisfies its
Leibniz law.

For an intermediate differential field `L` of the upper-end meromorphic field, say that `L` is
**carrier-fusion complete** when, for disjoint anchored supports,

```text
F_(e,z) in L and F_(r,w) in L
  => F_(e+r+1, z union w) in L.
```

This is a membership closure condition on the exact carrier selected by coefficient fusion.  It
does not pretend that `star` is ordinary multiplication of meromorphic germs.

## Master theorem: fusion completion forces unbounded differential rank

Assume that `L` contains the complete depth-zero layer:

```text
F_(0,z) in L for every z in A.
```

If `L` is carrier-fusion complete, then:

1. `F_(r,z) in L` for every valuation depth `r` and every `z in A`;
2. for every `d`, the rectangle

   ```text
   {F_(r,z) : 0 <= r < d, z in A}
   ```

   is jointly differentially independent over `C`;
3. its exact cardinality is

   ```text
   d * product_i |A_i|.
   ```

Consequently no finite number bounds the size of a differentially independent carrier packet
contained in a fusion-complete realization.

### Proof

Let `1_A` be the all-identity state.  Its anchored observable is the constant function `1`, so

```text
b_z * b_(1_A) = b_z
```

and the supports of `z` and `1_A` are disjoint.  The exact fusion law gives

```text
V_r(b_z) star V_0(1) = V_(r+1)(b_z).
```

The depth-zero hypothesis supplies `F_(0,1_A)`.  Induct on `r`.  If the complete depth-`r`
layer lies in `L`, carrier-fusion completeness applied statewise to the preceding identity puts
the complete depth-`r+1` layer in `L`.  Hence every layer lies in `L`.

Tail completeness makes the anchored coefficient family tail-independent.  The prime-power
Dirichlet packet theorem then gives joint differential independence of every finite
depth-by-state rectangle.  The index set is

```text
Fin d times product_i A_i,
```

whose cardinality is `d * product_i |A_i|`.  This proves all three clauses.  Notice that the
proof uses only fusion by the neutral source observable.  Closure under the full fusion law is
stronger than necessary.

## Sharp canonical tower

Let

```text
K_n = C< F_(r,z) : 0 <= r <= n, z in A >_diff.
```

The complete next layer is differentially independent over `K_n`, with exact relative rank
`product_i |A_i|`, and

```text
K_n proper-subfield K_(n+1).
```

Moreover both `F_(n,z)` and `F_(0,1_A)` belong to `K_n`, while their exact coefficient fusion is
`F_(n+1,z)`, which does not belong to `K_n`.  Thus the universal completion lower bound is sharp
at every finite frontier: the canonical tower acquires precisely one complete state multiplet
per step.

## Actual-prime corollary

For pairwise-coprime positive moduli `q_i`, take

```text
A_i = (Z/q_i Z)^x,
y(p) = (p mod q_i)_i,
```

assigning the identity at the finitely many nonunit primes.  Chinese remaindering and Dirichlet
recurrence make this profile tail-complete.  Hence every carrier-fusion complete field containing
the depth-zero residue layer contains, for every `d`, a jointly differentially independent
packet of exact size

```text
d * product_i phi(q_i).
```

The canonical frontier rank is exactly `product_i phi(q_i)`.

## New characteristic law

The coefficient algebra is finite-dimensional and its unit is neutral:

```text
f * 1 = f.
```

After valuation lifting, the same neutral multiplication becomes a depth-raising creation law:

```text
V_r(f) star V_0(1) = V_(r+1)(f).
```

Every created analytic layer is relatively hypertranscendental over the complete earlier field.
The scientifically characteristic statement is therefore positive:

> **Neutral-source creation law.** Any analytic realization that internalizes the exact
> prime-valuation fusion of a tail-complete finite source must carry unbounded differential
> transcendence rank.  Finite source algebra can be fusion-complete only through an infinite HT
> completion.

This is stronger than nonclosure of one chosen field.  It is a lower bound on every possible
fusion-complete carrier field.

## Novelty and anti-theatre audit

No novelty is claimed for finite tensor bases, Dirichlet recurrence, prime-power dilation,
Hadamard multiplication, or the fact that some classes of differentially algebraic series fail
Hadamard closure.  The candidate new contribution is the universal quantified coupling:

```text
actual recurring prime source
  + exact differential graded fusion
  + fusion-complete arbitrary ambient field
  => all valuation layers are forced
  => arbitrarily large differential-independent packets are forced
  => exact linear rank law d * product_i |A_i|.
```

The hostile reductions are:

1. **Hadamard nonclosure:** known nonclosure gives examples of escaped products, not a rank-exact
   lower bound for every completion.
2. **Finite-dimensional source algebra:** this strengthens rather than explains away the result;
   the forced analytic rank is unbounded although the source state space is finite.
3. **Independence repackaging:** rectangular independence alone does not quantify over arbitrary
   fusion-complete fields.  The induction from neutral-source closure is the new universal step.
4. **Physics rhetoric:** deleting the words `creation`, `state`, and `multiplet` leaves the exact
   field-membership and differential-independence theorem unchanged.
5. **Zeta rhetoric:** the empty-support carrier is a prime-zeta valuation layer, but no statement
   about zeta zeros or RH is used.

The law survives these attacks.  External priority remains provisional pending specialist
review.

## RH pressure test

The theorem does not prove RH.  It gives a necessary positive condition on finite-Euler proof
architectures: any construction that tries to internalize the exact prime-power fusion law must
introduce an infinite HT completion.  A finite differential-rational Euler field cannot be that
completion.  Functional-equation reflection, the archimedean factor, positivity, or a genuinely
infinite limiting operation must supply additional structure if such a route is to select zeta
zeros.

## Formalization target

Create one connector module proving:

- the neutral-source creation capstone over the arithmetic carrier field;
- the analytic neutral-source creation capstone;
- carrier-fusion completeness implies containment of every layer;
- the universal unbounded-rank completion theorem;
- the actual-prime totient specialization.

The connector is implemented in
`formal/GaloisForLFunctions/HTGeometry/PrimeValuationFusionCompletionLaw.lean` and imported by the
HTGeometry umbrella.  No new foundational theorem was required; the analytic independence,
fusion, tail-completeness, and actual-prime ingredients were reused from the formal corpus.

## Gates

- [x] dependency-closed paper proof
- [x] internal corpus collision audit
- [x] known-Hadamard-nonclosure boundary separated
- [x] exact connector formalization
- [x] one targeted cached verification
- [x] axiom audit
- [x] standalone Stage 4 paper

## Verification record

- Exact connector target:
  `lake build GaloisForLFunctions.HTGeometry.PrimeValuationFusionCompletionLaw` — passed.
- Direct touched-file check:
  `lake env lean GaloisForLFunctions/HTGeometry/PrimeValuationFusionCompletionLaw.lean` — passed.
- Axiom audit of the vacuum-creation, all-layer containment, canonical-minimality,
  universal-rank, and actual-prime capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- No full or umbrella build was run.  The exact analytic parent target was built only to restore
  missing cached dependency objects required by the new leaf.
- Publication artifact:
  `docs/drafts/pipeline/4-publication-ready/finite-fusion-infinite-hypertranscendence/main.tex`
  and `main.pdf`.
