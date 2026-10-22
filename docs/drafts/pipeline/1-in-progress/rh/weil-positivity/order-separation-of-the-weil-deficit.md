# Order separation of the Weil deficit

- **ID:** `order-separation-of-the-weil-deficit`
- **Stage:** 1-in-progress
- **Type:** CORPUS-WIDE STRUCTURAL READING + `[CONJECTURE]` + `[PREDICTION]`
- **Scientific status:** `[SYNTHESIS OF PROVED CARDS]` `[CONJECTURE]` `[NO RH CLAIM]`
- **Read, not assumed:** `2-fully-proven/meta/synthesis-finite-continuation-infinite-boundary.md`;
  the 59 `2-fully-proven/new_scientific_knowledge/suzuki-*.md` cards;
  `1-in-progress/harmonic-invisibility-and-the-one-over-delta-law.md` §§103–104;
  `3-formalized/novel-facts-ledger.md`; `docs/handover/connes.md`;
  `1-in-progress/rh-sota-literature-lean-wall-2026.md`.

---

## 1. What the corpus actually proves, in two pillars

### Pillar A — hypertranscendence / infinite boundary

The corpus's own synthesis memo states the unifying principle verbatim:

> Finite algebraic structure wants finite continuation control. The objects here carry infinite
> boundary data. The mismatch forces independence or hypertranscendence.

Its four proof templates are crossing + algebraic IFT, one-coordinate high monodromy, singular-row
descent with tail independence, and bounded companion-system continuation. The decisive point,
which the memo itself isolates as **Gap 2**, is:

> exact monodromy is a **pairwise** independence tool, not merely a single-function transcendence
> tool.

That is: Pillar A only started producing theorems once it stopped using *first-order* invariants
(transcendence of one function) and moved to *second-order* ones (the exact period group of a loop
that moves **one** coordinate while fixing another; rational independence of a **family** of tails).
Where it succeeds it succeeds by computing an **exact** invariant — the Prüfer group `2 pi i Z[1/2]`
via equilibrium measure, exact capacity, exact fractional-polylog pole towers — never by an estimate.

### Pillar B — the positivity budget (Suzuki / CCM / Hedenmalm)

Weil positivity in Suzuki's screw-function realization is a contest between a **continuous
archimedean channel** `A_a` and an **atomic prime wall**

```text
W = sum_n w_n delta_(tau_n),   w_n = 2 Lambda(n)/n,   tau_n = 2 log n.
```

Every proved card in this pillar is an *exact conservation, tax, lock, or no-go* about moving the
wall's mass into the continuum:

| Proved card | What it says |
|---|---|
| `suzuki-bicausal-displacement-overlap-conservation` | displacement and overlap are exactly conserved |
| `suzuki-bicausal-no-free-splice-classification` | splicing "neither weakens nor strengthens the RH-bearing inequality" |
| `suzuki-krein-schur-holonomy-tax` | completion of the negative channel carries an **exact** two-channel tax |
| `suzuki-mangoldt-apex-lock-rigidity` | each atom sits at the **unique** maximizer of its channel, hence on a Lebesgue-**null** superlevel; no positive-volume dominating cell can pay it |
| `suzuki-mangoldt-macroscopic/uniform-dyadic-block-surplus` | exact tilted-tent antitonicity and exact dyadic block brackets |
| `suzuki-coherent-response-gain-no-go`, `suzuki-negative-shift-defect-escape`, `suzuki-critical-apex-vacuum-capacity-no-go` | the corresponding gains do not exist |
| `suzuki-aperture-dressed-wall-light-completion` | the raw wall has divergent energy, `sum_n Lambda(n)/sqrt n = infinity` |

Read together: **the deficit is invariant under the entire source-side transport groupoid the
corpus has built.** Ten independent theorems, one invariance.

### The two pillars are one principle with the roles exchanged

- Pillar A: a **finite algebraic relation** cannot absorb a depth-indexed infinite tower of
  independent levels (cylinder depth `n`, singularity index `n`).
- Pillar B: a **finite positive transport** cannot pay a depth-indexed infinite tower of atoms
  (`tau_n = 2 log n`, mass `2 Lambda(n)/n`).

Both are *finite control against depth-indexed level structure*. The corpus has solved this shape
before — but only after moving from first order to second order.

---

## 2. The resource neither pillar has used

Inspect the inputs of every proved law in Pillar B. They use exactly:

- `Lambda >= 0`;
- `Lambda(n) <= log n`;
- `supp Lambda = ` prime powers;
- Bertrand and Mertens (`sum_(d<=X) Lambda(d)/d <= log X`, imported from Ramaré–Zuniga Alterman).

That is the **size and support** of `Lambda`, nothing else. No proved card in the pillar uses a
*correlation* of `Lambda`.

Pillar A is the mirror image: it uses the **independence** of `{log p}` as a frequency system
(dissociativity, unique factorization) but never the joint distribution of the masses.

And the corpus reached the same conclusion independently, from the third direction, in
`harmonic-invisibility-and-the-one-over-delta-law.md` §104.3, where after exhausting the analytic
lane it asks *"What is a second, independent, non-self-dual arithmetic input?"* and names as its
first candidate:

> the `Lambda`-values' multiplicative **independence** across primes rather than their positivity.

Three independent lanes, one missing resource. That is the corpus speaking.

---

## 3. The conjecture the picture forces

> **[CONJECTURE — Order separation of the Weil deficit.]**
> The sign of the Weil deficit in the Suzuki/CCM realization is not determined by any **first-order**
> functional of the prime wall — any functional of the masses `w_n` and their positions `tau_n`
> alone, i.e. of the size and support of `Lambda`. Precisely: for every first-order source law
> (transport, splice, cell, completion, dressing, surplus, tax, lock) there exist two positive
> atomic walls with identical first-order data whose deficits have opposite sign. The sign is
> decided at **second order**, by the wall's autocorrelation at multiplicative lags
>
> ```text
> (W * W~)(2 log(a/b)) = sum_d w_(ad) w_(bd),   gcd(a,b)=1,
> ```
>
> that is, by the correlations of `Lambda` — not by its size, support, or positivity.

**Why the picture forces it.** A quantity conserved by *every* mass-rearranging operation cannot be
a nontrivial function of mass placement alone. Pillar B has proved that conservation ten times over.
Pillar A already made exactly this move — from first-order transcendence to second-order pairwise
monodromy — and only then produced theorems (memo, Gap 2). Pillar B has not made it.

**What is structurally new.** The corpus's conservation laws have been read as *obstacles* — each
card records a no-go and sharpens an open core. This conjecture reads them as **data**: they are
not ten separate walls but one measurement, and what they measure is that the deficit lives one
order up. The negative results become a positive structural theorem about where the deficit is.

**How it could fail.** Exhibit a single first-order source law whose value decides the sign — i.e.
two walls with equal `(w_n, tau_n)` data forced to have the same deficit sign against every
admissible archimedean channel. That would refute the conjecture outright and re-open the entire
first-order programme.

**What its truth would open.** The RH-bearing positivity would have to be a positivity of a
**correlation kernel in the multiplicative-lag variable** `a/b`, not a pointwise domination in the
additive lag variable `t`. The corpus owns a large Toeplitz/Hankel/Gram apparatus (`CompleteHankelCone`,
Krein/Schur, Gram gates, Weil polarization) — and every deployment of it so far has been in the
**additive** lag variable. The prediction is that the same apparatus applied to the multiplicative
lag is where the sign lives.

**What its falsity would teach.** If a first-order law does decide the sign, then the ten
conservation theorems are accidental rather than structural, and the correct reading is that the
corpus has simply not yet found the right transport — which would make the transport programme
live again and identify precisely which conservation law is the removable one.

---

## 4. `[PREDICTION]` — a test that costs nothing

The conjecture predicts a property of the corpus's own failed-route folder: **every retired route in
this lane should be first-order.** Spot check:

- `5-failed/suzuki-pointwise-turning-seam-cell-transport.md` — a transport. First-order.
- `5-failed/suzuki-continuum-two-flank-surplus-pays-bicausal-seam.md` — a surplus comparison.
  First-order.

Both first-order, both retired. A retired route in this lane that is genuinely second-order would be
evidence against.

---

## 5. The first object to construct

```text
C(a,b) := sum_d w_(ad) w_(bd) = 4 sum_d Lambda(ad) Lambda(bd) / (ad · bd),   gcd(a,b) = 1.
```

`C` is the prime wall's autocorrelation read at multiplicative lag `a/b`. It is a positive-definite
kernel on the coprime pairs by construction, and it is *not* a function of `(w_n)` through any
rearrangement-invariant functional — moving mass between atoms changes `C` even when it preserves
every first-order statistic. The conjecture says the Weil deficit is a functional of `C`.

Immediate targets, in order:

1. Prove that the Suzuki deficit is expressible through `C` and the archimedean autocorrelation
   alone — i.e. that the pairing factors through second order. This is the load-bearing step and is
   where the conjecture is won or lost.
2. Identify which conservation laws of Pillar B are the statement "the first-order part of the
   pairing vanishes identically". If they all are, the ten theorems collapse to one.
3. Only then ask what positivity of `C` against the archimedean autocorrelation means
   arithmetically — that is where `Lambda`-correlations, and hence a genuinely second, non-self-dual
   arithmetic input, enter for the first time in this corpus.

## Gates

- [x] Corpus-wide reading verified against named proved cards, not inferred
- [x] Missing resource identified independently from three lanes
- [x] Conjecture stated with falsification and with a zero-cost prediction
- [ ] Step 1: factor the Suzuki pairing through second order
- [ ] Step 2: re-derive the conservation laws as the vanishing of the first-order part
- [ ] External novelty audit of the second-order positivity statement before any claim

## Log

- 2026-07-25 — Card opened after retracting `local-cyclotomic-detection-of-the-euler-product` on the
  external novelty gate. Reading built from what the corpus proves, not from a retired card's
  forward-pointer.

---

## 6. Step 1 executed: the block sample mass is a Fejér-smoothed `psi`-fluctuation

The corpus states the successor frontier itself, in the hostile audit of
`suzuki-mangoldt-apex-lock-rigidity`:

> Per-atom pointwise seam transport is retired. Exact successor is `SUZUKI-APEX-BLOCK-TRANSPORT`:
> construct source-canonical disjoint blocks containing apex and flank atoms and prove aggregate
> sample mass is paid by aggregate completed-kernel mass. **Any valid proof must expose a
> nonnegative block surplus; it cannot decompose into independently dominated atomic cells.**

"Cannot decompose into independently dominated atomic cells" is the order-separation conjecture of
§3 stated from inside the lane. So the corpus and this card agree on the direction. What follows
computes the sample side of that block, using only quantities the corpus has already fixed.

From `suzuki-mangoldt-uniform-dyadic-block-surplus`, verbatim:

```text
A_n(m) = sqrt(m) · max(0, log 2 - |log(m/n)|),      w_m = 2 Lambda(m)/m.
```

Hence the **aggregate block sample mass** at `n` is

```text
S(n) := sum_m w_m A_n(m)
      = 2 sum_m Lambda(m) m^(-1/2) T(log(m/n)),     T(t) = (log 2 - |t|)_+.
```

Put `f(t) = e^(-t/2) T(t)`, supported on `(-log 2, log 2)`. Substituting `m = n e^t`,

```text
S(n) = 2 n^(-1/2) sum_m Lambda(m) f(log(m/n)) = 2 n^(-1/2) ∫ f(log(u/n)) dpsi(u).
```

The explicit formula for the smoothed `psi` gives, with `C = ∫ e^(w/2) T(w) dw > 0` and
`hat f(rho) = ∫ T(w) e^(i gamma w) dw = 2(1 - cos(gamma log 2))/gamma^2` at `rho = 1/2 + i gamma`,

```text
S(n) = 2C sqrt(n) - 2 sum_rho n^(rho - 1/2) hat f(rho) + O(n^(-1/2)).      (*)
```

`[PROVED HERE — classical mechanism]` Three readings of `(*)`:

1. **The main term matches the channel exactly.** `S(n) ~ 2C sqrt n`, and the channel amplitude is
   `sqrt m`. So the block is asymptotically *exactly* balanced at leading order — which is why every
   first-order surplus law in the lane is an equality up to `O(1)` and why ten independent
   conservation theorems appeared. The corpus's conservation laws are the leading term of `(*)`.
2. **The fluctuation is the divisor.** The correction is `-2 sum_rho n^(beta - 1/2) e^(i gamma log n)
   hat f(rho)`. The tent's transform decays like `gamma^(-2)`, so against the zero density
   `~ log gamma` the sum converges absolutely; under RH every `n^(beta-1/2) = 1` and the fluctuation
   is `O(1)`. A single zero with `beta > 1/2` contributes `n^(beta-1/2)`, which is unbounded.
3. **Therefore the normalized block mass `S(n)/sqrt n` converges (indeed, is bounded) if and only if
   RH holds.**

### 6.1 Consequence for the lane `[DIAGNOSIS]`

`SUZUKI-APEX-BLOCK-TRANSPORT` asks for the aggregate block sample mass to be paid. By `(*)` the
sample side alone is `2C sqrt n` plus a fluctuation whose boundedness **is** RH. So the named open
core is **not a sub-problem of RH; on its sample side it is RH.** No further source-side block
construction can advance it: the object the construction must control is the Fejér-smoothed
`psi(x)/sqrt x` fluctuation, i.e. the divisor itself.

This does not retire the Suzuki lane — the kernel side is a genuine and separate object — but it
does retire the expectation that block aggregation is an intermediate step. It is the destination.

### 6.2 Honest novelty verdict on §6

`[REDISCOVERED — classical]`. Equation `(*)` is the explicit formula applied to a compactly
supported tent; any analytic number theorist produces it directly. Its value here is entirely
**corpus-diagnostic**: it identifies the lane's named successor frontier with RH and thereby
redirects the effort of a 59-card cluster. It is *not* frontier-moving mathematics and must not be
counted as such.

### 6.3 What survives as genuinely open, and where the second order actually lives

What `(*)` shows is that the *first-order* (mass) content of the block is exactly the main term, and
the divisor sits entirely in the fluctuation. That is the order separation of §3, now visible in a
formula rather than inferred from ten no-gos. The second-order object of §5,

```text
C(a,b) = sum_d w_(ad) w_(bd),    gcd(a,b) = 1,
```

is not visible in `(*)` at all: `(*)` is linear in the wall. So the correct next step is **not** to
smooth harder but to form the pairing that is quadratic in the wall — the Weil form itself read in
the multiplicative-lag variable — and ask whether its first-order part is the `2C sqrt n` main term.
If it is, then every conservation law in the lane is the vanishing of a first-order remainder, and
the sign question is `C(a,b)` against the archimedean autocorrelation.

---

## 7. Step 2: the pairing formed correctly, and a transport dichotomy `[PROVED HERE]`

§6 left the question: is the Weil form quadratic in the wall? It is not, and getting this right
changes the verdict on the whole lane.

### 7.1 The correct pairing

For `phi` supported in `[-D, D]` put the autocorrelation

```text
A_phi(t) = ∫ phi(u) conj(phi(u - t)) du,     supp A_phi ⊂ [-2D, 2D].
```

The explicit formula makes the prime part of the Weil form

```text
P(phi) = 2 <W, A_phi>,     W = sum_n (Lambda(n)/sqrt n) delta_(log n).
```

So `P` is **linear in the wall and quadratic in the test function**, and the wall is tested only
against the cone of autocorrelations. The multiplicative-lag variable of §5 is already present, but
not as `C(a,b)`: it is the **Toeplitz argument** `u - v = log(m/n)` of the kernel `W(u-v)`. The §5
object `C(a,b) = sum_d w_(ad) w_(bd)` is quadratic in the wall and therefore **does not occur in the
Weil form at all.** That part of §3 is withdrawn.

### 7.2 Separation

> **Lemma.** Fix `D > 0` and `psi ∈ L^2[-D,D]`, `psi ≠ 0`. For distinct reals `t_1, …, t_N` the
> translates `u ↦ psi(u - t_k)` are linearly independent in `L^2`.
>
> *Proof.* A vanishing combination gives `hat psi(xi) · sum_k c_k e^(-i t_k xi) = 0` a.e. Since
> `psi ≠ 0`, `hat psi` is a nonzero entire function of exponential type, so its zero set is discrete
> and `sum_k c_k e^(-i t_k xi) = 0` on a set of positive measure; that sum is entire, hence
> identically zero, and distinct exponentials are linearly independent. So every `c_k = 0`. ∎

> **Theorem (transport dichotomy).** Let `W, W'` be locally finite measures on `(-2D, 2D)`.
>
> (a) If `<W, A_phi> = <W', A_phi>` for every `phi ∈ L^2[-D,D]`, then `W = W'` on `(-2D, 2D)`.
>
> (b) If `<W, A_phi> <= <W', A_phi>` for every such `phi`, then `W' - W` is a nonnegative-definite
> distribution on `(-2D, 2D)` — i.e. its Fourier transform is a nonnegative measure there.
>
> *Proof.* (a) Polarization turns the hypothesis into `<W - W', A_(phi,psi)> = 0` for all `phi, psi`,
> where `A_(phi,psi)(t) = <phi, T_t psi>`. By the Lemma the translates `T_t psi` span a set rich
> enough that `A_(phi,psi)` exhausts a sup-norm-dense subspace of `C_0((-2D,2D))`; hence `W - W' = 0`
> there. (b) is Bochner applied to `W' - W`. ∎

### 7.3 What this settles about the lane

**Every source-side transport is either the identity or a relocation.**

- A transport that *conserves* the deficit conserves the pairing against the whole autocorrelation
  cone, and by (a) it does not move the wall. It is a **rewriting of the same object**. This is
  exactly what the corpus's own cards say of themselves — `no-free-splice` records that its residual
  "is the original continuous-minus-atomic quadrature deficit"; `displacement-overlap conservation`
  is the set identity `L ∪ R = U`, `L ∩ R = O`. The theorem says this had to be so.
- A transport that *dominates* — replacing `W` by a friendlier `W'` with `<W,A_phi> <= <W',A_phi>` —
  is by (b) required to make `W' - W` nonnegative-definite, which is a positivity problem of exactly
  the same type as the one being solved. **The difficulty is relocated, never reduced.**

So the transport programme is closed as a matter of structure, not of ingenuity: there is no third
option. `SUZUKI-APEX-BLOCK-TRANSPORT` inherits this — §6 already showed its sample side is RH, and
§7 shows no transport can stand between them.

### 7.4 Correction to §3

The conjecture of §3 is **withdrawn in its stated form.** Its object `C(a,b)` is quadratic in the
wall and the Weil form is linear in the wall, so `C` cannot decide the sign. What survives, and is
now proved rather than conjectured, is the operative half:

> **[PROVED]** No source-side rearrangement of the prime wall changes the Weil deficit, and no
> source-side domination reduces the difficulty. The ten conservation theorems of the lane are one
> theorem — the separation lemma — seen ten times.

The correct location of the remaining freedom is therefore **not** the wall and **not** any transport
of it. It is the **test cone**: the only structure the Weil form has beyond the wall is which
positive-definite functions are realisable as `A_phi` with `supp phi ⊂ [-D,D]`. That is a
Beurling–Selberg/Krein extremal geometry, and it is the only place in this realization where a new
idea can enter.

### 7.5 Novelty verdict on §7

`[REDISCOVERED — classical ingredients]` (linear independence of translates; Bochner). Against the
external literature this moves nothing. Its force is internal and it is a **theorem, not a
heuristic**: it closes a 59-card direction with a proof and names the single surviving degree of
freedom. Recorded as diagnosis, not as new scientific knowledge.

---

## 8. The surviving degree of freedom, probed

§7.4 leaves exactly one place where a new idea can enter this realization: the **test cone**. By
Krein's factorization the cone is exactly

```text
G_D = { g : supp g ⊂ [-2D, 2D],  hat g >= 0 },
```

and Weil positivity is `<W_arch, g> >= <W_prime, g>` for every `g ∈ G_D`, every `D`.

### 8.1 A hard constraint on the cone `[PROVED HERE — classical mechanism]`

> For every continuous positive-definite `g` with `g(0) = 1` and `supp g ⊂ [-2D, 2D]`, and every
> `0 < t <= 2D`,
>
> ```text
> Re g(t) <= 1 - (t / (2D + t))^2.
> ```
>
> *Proof.* Bochner gives `g(t) = ∫ e^(i t xi) d nu`, `nu >= 0`, `nu(R) = 1`. From
> `1 - cos(k θ) <= k^2 (1 - cos θ)` one gets `1 - Re g(kt) <= k^2 (1 - Re g(t))`. Choose
> `k = ⌊2D/t⌋ + 1`, so `kt > 2D` and `g(kt) = 0`, hence `1 <= k^2 (1 - Re g(t))`. ∎

Read at `t = log p`: a normalized compactly supported test can never be near-flat at a log-prime,
and the deficiency is governed by the **multiplicative depth** `k ≈ 2D/log p` — the same depth
parameter that indexes both pillars. This is the depth-indexed level structure of §1 appearing on
the *test* side rather than the wall side.

### 8.2 Why it does not close the gap, and what that means

Applying the bound termwise gives only

```text
<W_prime, g> <= 2 sum_(n <= e^(2D)) Lambda(n) n^(-1/2) [1 - (log n/(2D + log n))^2],
```

which is still of size `e^D`, while `<W_arch, g>` is of size `D`. The inequality therefore cannot be
won pointwise: it needs the **cancellation** in `sum_n Lambda(n) n^(-1/2) Re g(log n)`, which is the
smoothed `-Re(zeta'/zeta)(1/2 + i·)` — the explicit formula, again.

`[NOVELTY VERDICT]` The inequality of §8.1 is Bochner plus the classical `1 - cos(k θ)` estimate;
against the July-2026 literature it is `[REDISCOVERED]`. The surrounding area — extremal
compactly-supported test functions against the explicit formula — is itself heavily worked
(Beurling–Selberg/Vaaler; Carneiro–Littmann–Milinovich; Chirre). Nothing here moves that frontier.

---

## 9. Closing assessment of this line

What was delivered, with honest labels:

| Result | Status vs. July-2026 literature | Value |
|---|---|---|
| §6: block sample mass `= 2C√n − 2Σ_ρ n^(ρ-1/2) hat f(rho) + O(n^(-1/2))`; `SUZUKI-APEX-BLOCK-TRANSPORT` is RH on its sample side | `[REDISCOVERED]` — explicit formula on a tent | closes a named frontier as a destination, not a step |
| §7: transport dichotomy — conserving transports are the identity; dominating transports relocate the same positivity problem | `[REDISCOVERED]` — separation + Bochner | closes the transport programme with a proof; explains ten conservation theorems as one lemma |
| §8: compact-support PD deficiency bound at multiplicative depth | `[REDISCOVERED]` | sharp, but pointwise, so it cannot beat the exponential wall |
| §3 conjecture (`C(a,b)` second-order object) | **withdrawn by §7.1** — the Weil form is linear in the wall | — |

**No frontier-moving mathematics was produced on this line.** The reason is structural and worth
recording: Pillar A is declared classical by the corpus's own `novel-facts-ledger` retraction;
Pillar B's transport half is closed by §7 and its aggregate half is RH by §6; and the one surviving
degree of freedom, the test cone, is exactly the region the extremal-function literature occupies.

### 9.1 The one mechanism §6–§8 do **not** close

Everything above concerns **positivity**: an inequality to be won. Suzuki's lane also contains an
object of a different logical shape — the **characteristic functions of self-adjoint extensions**.
Per the corpus's SOTA ledger, `SuzukiFiniteApertureHermiteBiehler` and
`SuzukiGroundEdgeCayleyUniversality` establish that the deficiency-`(1,1)` family produces entire
`W(a, theta; z)` with **only real zeros, unconditionally**, together with a Hermite–Biehler/Livšic
normal-family package; and the two proved no-gos isolate the scale window in which a Xi-bearing
schedule could live.

There reality of the zeros is *free* and the open problem is a **convergence and identification**
problem — does some admissible schedule's Livšic limit equal the global Xi carrier — not a
positivity problem. §7's dichotomy says nothing about it, because no measure transport occurs.
That is the only part of this corpus where the logical shape of the difficulty differs from
"win an inequality", and it is therefore the correct next target.

## Log (cont.)

- 2026-07-25 — §7 proved; §3 withdrawn by it. §6 and §8 recorded with `[REDISCOVERED]` verdicts.
  Line closed with an explicit no-frontier-movement finding and the Livšic identification named as
  the one surviving mechanism of different logical shape.

---

## 10. The Conrey–Li check on the Livšic target, run

**Question.** `[LITERATURE]` Conrey–Li, *A note on some positivity conditions related to zeta- and
L-functions*, IMRN 2000 (arXiv:math/9812166), show that de Branges's positivity conditions — which
would imply GRH — are **not satisfied** by the structure functions of the reproducing-kernel Hilbert
spaces associated with `zeta`. Since Suzuki's carriers are de Branges structure functions, does that
obstruction transfer?

**Answer: no.** The two constructions fail in opposite directions.

- Conrey–Li's mechanism is that *proposed* structure functions attached to `zeta` **fail** the
  required positivity.
- Suzuki's structure functions **satisfy** it unconditionally. From Suzuki's Theorem 1.5 (for every
  extension angle, `W(a,theta;z) = A_(a,lambda)(z) + e^(i theta) E_(a,lambda)(z)` is entire with only
  real zeros) plus `A(i)=0`, the corpus's all-angle lemma gives `|A| < |E|` on `Im z > 0`; parity and
  reality of the screw kernel give `A = E^#`, so

  ```text
  |E^#(z)| < |E(z)|,   Im z > 0,
  ```

  is the Hermite–Biehler inequality itself, and `Theta_(a,lambda) = E^#/E` is a meromorphic inner
  function with the **aperture- and shift-free** bound `|Theta(z)| <= |(z-i)/(z+i)|`.

So the positivity Conrey–Li showed fails for de Branges's candidates is *automatic* for Suzuki's.
The Livšic route is not closed by Conrey–Li. `[CHECK COMPLETE]`

### 10.1 Where the difficulty actually sits, localized

Positivity being free, the whole problem is the limit. Read through **Clark measures**: for a
meromorphic inner `Theta` and `|alpha| = 1`, `sigma_alpha` is carried by `{Theta = alpha}` with
masses `2/|Theta'|`, and locally uniform convergence of `Theta_a` on `Im z > 0` is exactly weak-*
convergence of `sigma_alpha`. The corpus's `suzuki-donoghue-defect-spectral-measure-law` identifies
these with the extension spectral measures. The possible limits then split three ways:

| limit | Clark measure | corpus status |
|---|---|---|
| `Theta = (z-i)/(z+i)` (universal Cayley) | one atom | proved to occur (ground-edge leakage `-> 0`) |
| `Theta = 0` (free carrier) | absolutely continuous | proved to occur (far-negative shifts) |
| `Xi`-bearing | purely atomic, density `~ log|x| / 2 pi` | the open wall |

**A blind invariant, removed.** At aperture `a` the function `E_(a,lambda)` has exponential type `a`,
so its level sets have density `a/pi` and Clark weights `~ 1/a`: mass per unit length `~ 1/pi`,
**independent of the aperture**. For the `Xi` target the density is `log|x|/2 pi` and the weights are
`2/|Theta'| ~ 2/log|x|`: mass per unit length again `~ 1/pi`. So **mean spectral density is the same
for the whole finite-aperture family, for the free limit, and for the target.** Density cannot
detect degeneration, and no schedule can be certified or excluded by a density estimate.

What separates the three rows is only the **type** of the limiting measure — one atom, absolutely
continuous, or atomic-with-growing-density. So the identification problem is a problem about
*atomicity and spacing fluctuation* of a weak-* limit of purely atomic measures of fixed mean
density, not about any size or density estimate. The corpus's "dimensionless leakage"
`tau ||sinh||^2 / (Delta |<phi_0, cosh>|^2)` is precisely the parameter that decides collapse to the
one-atom row; the free row is the opposite collapse.

### 10.2 Verdict

`[REDISCOVERED — classical mechanism]` (Clark measures, de Branges/Krein). Nothing here moves the
July-2026 frontier. Its value: (i) it clears the Conrey–Li obstruction from the Livšic target with a
reason rather than a hope, and (ii) it removes density from the list of usable invariants, leaving
weak-* atomicity as the single live question in that lane.

---

## 11. The atomicity question, worked — an attempted no-go and its self-refutation

### 11.1 The attempt

The Clark atom at a level point `x_k` has mass `2/vartheta_a'(x_k)`, where `vartheta_a` is the phase
of `Theta_(a,lambda)`. A purely atomic weak-* limit needs a subfamily of level points on which
`vartheta_a'` stays **bounded**, of density `~ log|x|/2pi`, while the full level set has density
`a/pi`. So the phase derivative must be strongly bimodal.

The attempted no-go: if `E_(a,lambda)` has exponential type `a` with the type attained in the
Nevanlinna sense, then `Theta_(a,lambda) = E^#/E` carries the singular inner factor `e^(2 i a z)`,
whence

```text
|Theta_(a,lambda)(x + i y)| <= e^(-2 a y),
```

so `Theta_(a,lambda) -> 0` locally uniformly on `Im z > 0` for **every** shift schedule, every
aperture-cofinal limit is the free carrier, and no `Xi`-bearing limit exists in the family.

### 11.2 Why it is false `[SELF-REFUTED]`

The bound `|Theta(iy)| <= e^(-2 a y)` requires `E` to be *one-sided* exponential, as for the model
`E(z) = e^(-i a z)`, where `|E(iy)| = e^(a y)` grows while `|E^#(iy)| = e^(-a y)` decays. Suzuki's
`E_(a,lambda)(z) = (z+i) ∫_(-a)^a v_-(x) e^(i z x) dx` is a **Paley–Wiener** function: a compactly
supported transform grows like `e^(a|y|)` in *both* half-planes. Hence

```text
|E(iy)| ~ e^(a y),   |E^#(iy)| = |E(-iy)| ~ e^(a y),
```

and `|Theta_(a,lambda)(iy)|` tends to a finite nonzero constant. **The mean type of
`Theta_(a,lambda)` is `0`, not `2a`.** The attempted bound is wrong and the no-go collapses.

### 11.3 Positive residue `[PROVED HERE]`

The refutation leaves a correct structural fact that sharpens the corpus's picture:

> For every aperture `a` and admissible shift `lambda`, the Livšic quotient `Theta_(a,lambda)` has
> **zero mean type**, hence **no singular inner factor**: it is a pure Blaschke product over the
> zeros of `E_(a,lambda)` in the lower half-plane.

Consequences:

1. The proved free-carrier degeneration (`Theta -> 0` for far-negative shifts) is **not** a
   singular-factor phenomenon. It cannot be diagnosed or prevented by any type or growth estimate,
   because the type is identically zero across the whole family.
2. Degeneration is therefore entirely a statement about the **depths** `eta_k = -Im w_k` of the
   zeros of `E_(a,lambda)`. The Blaschke sum `sum_k eta_k/(1 + xi_k^2)` converges by construction;
   `Theta_a -> 0` locally uniformly is exactly divergence of that sum along the schedule, and
   collapse to the one-atom Cayley map is its degeneration to a single term.
3. The atomicity of the limit is controlled by the same data: `vartheta_a'(x) = 2 sum_k eta_k /
   |x - w_k|^2`, so the Clark atom masses are `2/vartheta_a'`, and a `Xi`-bearing limit requires the
   zero depths to be arranged so that `vartheta_a'` is bounded on a set of density `log|x|/2pi` and
   large elsewhere.

So the single live quantity in this lane is the **depth profile of the zeros of the finite-aperture
carrier** — not its type, not its density, not its mass. Together with §10's removal of density,
this leaves exactly one unconditional object to compute from the screw operator.

### 11.4 Verdict

`[NO NEW KNOWLEDGE]` on the attempt: the candidate no-go was false and I refuted it myself. The
residue in §11.3 is correct and useful but its mechanism (Krein's factorization of Hermite–Biehler
functions; Paley–Wiener two-sided growth) is classical — `[REDISCOVERED]` against July 2026. Value
is again localization: two invariants (type, density) are now provably blind, and the depth profile
is named as the sole remaining one.

---

## 12. The depth profile computed structurally: `A_a` is a frame operator, and the apex lock is Nyquist matching

### 12.1 What the screw operator is

Suzuki's `A_a` on `L^2(-a,a)` is the convolution operator with kernel `k = -g''`, whose symbol is the
Riemann–Weil distribution. Under RH that distribution is `Omega = 2 pi sum_rho delta_(gamma_rho)`, so

```text
<A_a v, v> = sum_rho |hat v(gamma_rho)|^2,     hat v(xi) = ∫_(-a)^a v(x) e^(i xi x) dx.
```

That is, `A_a = S_a^* S_a` with `S_a v = (hat v(gamma_rho))_rho`: **the truncated Weil operator is the
frame operator of the zeta-zero exponential system `{e^(i gamma_rho x)}` on `(-a,a)`.** Positivity is
then automatic — a Gram operator. Off the critical line the corresponding pairing is
`hat v(rho) · conj(hat v(1 - bar rho))`, hyperbolic rather than Gram; so RH is exactly the statement
that this pairing *is* a Gram form. `[PROVED HERE — classical mechanism]`

### 12.2 The apex lock is a Nyquist condition

The zero density is `(1/2 pi) log(gamma/2 pi)`; the Nyquist (Beurling) density for `(-a,a)` is
`a/pi`. These are equal exactly when

```text
gamma = 2 pi e^(2a),     equivalently    a = (1/2) log(gamma/2 pi).
```

So aperture `a` critically resolves zeros up to height `e^(2a)`. The corpus's apex lock

```text
a_n = (1/2) log(2n),    tau_n = 2 log n,
```

is **precisely this matching**, with `n <-> gamma/2pi`. It is the Riemann–Siegel relation
`n ≈ sqrt(t/2pi)` read on the aperture axis. That is why `tau_n` is the unique maximizer of `A_n`
(`suzuki-mangoldt-apex-lock-rigidity`): the atom at `2 log n` is exactly at the critical frequency of
its own aperture. The "exact source lock" the corpus identified as the scientific content of that
card is a Nyquist resonance, not an accident of the tent geometry.

### 12.3 Consequence for the depth profile — the sole remaining invariant

§10 and §11 reduced the lane to the depth profile `eta_k` of the carrier's zeros. In the frame
reading, `eta_k` measures the redundancy of the exponential system at frequency `xi_k`:

| regime | Beurling density vs. `a/pi` | frame status | limit |
|---|---|---|---|
| overcritical | `>` | frame, redundant | `Theta -> 0`, free carrier, AC Clark measure |
| undercritical | `<` | Riesz sequence, deficient | Cayley collapse, one-atom Clark measure |
| **critical** | `=` | neither generically | the `Xi`-bearing window |

So the corpus's unnamed "intermediate window" — the schedule that must avoid both proved
degenerations — **is the critical-density regime of the zeta-zero exponential system.** By Landau's
necessary density conditions a frame forces density `>=` Nyquist and a Riesz sequence forces `<=`
Nyquist; at exactly critical density the system is generically neither, and completeness/frame
properties there are decided by fine arithmetic of the frequency set, not by any density or size
estimate. That is consistent with, and explains, §10's and §11's findings that density and type are
both blind.

### 12.4 Verdict

`[REDISCOVERED — classical mechanism]` (Beurling–Landau density; Paley–Wiener frame theory;
Riemann–Siegel). Against July 2026 this moves nothing. Its value is a third localization: the lane's
open window is not an estimate to be sharpened but a **critical-density problem for the exponential
system of the zeta zeros**, which is a known-delicate regime and explains why every size, density,
and type invariant in the corpus has come out blind.
