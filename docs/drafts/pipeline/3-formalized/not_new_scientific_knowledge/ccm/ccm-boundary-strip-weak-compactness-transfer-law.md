# Weak boundary-strip compactness transports the four-unit CCM budget

- **ID:** `ccm-boundary-strip-weak-compactness-transfer-law`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent results:** weak compactness and lower semicontinuity in the Hilbert--Schmidt class
- **Statement:** A cofinal family of finite-stage boundary-strip operators that converges on one
  graph core of the Xi anti-causal operator and obeys the Euler four-unit Hilbert--Schmidt budget
  forces the limiting Xi boundary relative trace to obey the same budget, and hence proves RH.

## 1. Abstract graph-core transfer theorem

Let `H,K` be Hilbert spaces, let `D:D(D) subset H -> K` be a closed densely defined operator, and
let `C subset D(D)` be a graph core for `D`. For each `u>0`, let `Q_u in B(K)` and suppose that

```text
A_(N,u) in S_2(H,K).                                    (1)
```

Assume that for every `f in C`,

```text
A_(N,u)f -> Q_uDf weakly in K                           (2)
```

as `N -> infinity`. Then

```text
||Q_uD||_(S_2,ext)^2
 <= liminf_(N->infinity)||A_(N,u)||_(S_2)^2.            (3)
```

Here the left side is the squared norm of the unique Hilbert--Schmidt extension of `Q_uD`, if one
exists, and `+infinity` otherwise.

### Proof

If the right side of `(3)` is infinite there is nothing to prove. Otherwise choose a subsequence
whose squared norms converge to the finite lower limit. This subsequence is bounded in the Hilbert
space `S_2(H,K)`, so it has a weakly convergent further subsequence, with limit `A_u in S_2(H,K)`.

For fixed `f in H`, evaluation `T |-> Tf` is a bounded map from `S_2(H,K)` to `K`. Hence the
subsequence converges weakly to `A_uf`. On the core `C`, hypothesis `(2)` identifies

```text
A_uf=Q_uDf.                                             (4)
```

Since `C` is a graph core, for every `f in D(D)` there are `f_j in C` with

```text
f_j -> f,       Df_j -> Df.                             (5)
```

The boundedness of `A_u` and `Q_u` extends `(4)` from `C` to all of `D(D)`. Thus `A_u` is the
Hilbert--Schmidt extension of `Q_uD`. Weak lower semicontinuity of the Hilbert--Schmidt norm gives
`(3)`.

The theorem uses no norm convergence of the full operators and no trace-class property of `D`.
The graph core is the exact incidence datum that prevents the weak limit from losing the
distinguished source.

## 2. Four-unit specialization

Let `D_Xi` be the closed anti-causal logarithmic-source operator and let `C_Xi` be any graph core.
Suppose finite-stage completed Euler--Gamma constructions produce `A_(N,u) in S_2` such that

```text
A_(N,u)f -> Q_uD_Xi f weakly                            (6)
```

for every `f in C_Xi`, and there is a scalar remainder `r(u)=o(u)` with

```text
limsup_(N->infinity)||A_(N,u)||_(S_2)^2
 <=4(1-exp(-u))+r(u).                                   (7)
```

Then `(3)` gives

```text
Delta_Xi(u)=||Q_uD_Xi||_(S_2,ext)^2
 <=4(1-exp(-u))+r(u).                                   (8)
```

Since `4(1-exp(-u))~4u`,

```text
limsup_(u->0+) Delta_Xi(u)/(4(1-exp(-u)))<=1.           (9)
```

The four-unit boundary relative-trace criterion therefore gives RH.

## 3. Positive carrier law

This theorem identifies a complete finite-prime implementation mechanism. A successful CCM/Connes
construction may transport the divisor through a singular operator limit rather than through
locally uniform determinant convergence, but it is then forced to carry all three of the following:

1. **Cofinal arithmetic source:** finite-stage Euler--Gamma operators whose action converges on a
   graph core of the exact Xi source;
2. **pointed source--divisor incidence:** the limiting core belongs to the Xi logarithmic graph and
   therefore changes under rational off-line orbit insertion;
3. **positive boundary budget:** a uniform Hilbert--Schmidt bound on the one-sided boundary strips,
   asymptotic to the incoming Euler-pole budget `4u`.

The first item is the infinite prime carrier from `docs/prompts/notes.md`; the second is its pointed
positive-chamber orientation; the third is the metric coercivity that excludes every transverse
divisor unit. Weak Hilbert--Schmidt compactness is enough to transport the budget once these three
carriers have been built.

This is a direct functional-analytic bridge, not new scientific knowledge. It does not prove `(7)`
for any particular finite Euler--Gamma construction; `(7)` is now the single finite-stage estimate
that the route must supply.

## 4. Attack by the canonical finite stages

The theorem is a transfer interface, not a shortcut around the known CCM core.

1. **Real-spectrum CCM determinants.** Their dephased entire factors are real-rooted. Smirnov
   theory therefore makes every finite anti-causal logarithmic operator identically zero. Graph-core
   convergence to `D_Xi` would force `D_Xi=0`, which is equivalent to RH. Thus hypothesis `(6)`
   already contains the whole conclusion on this branch.
2. **Finite-prime theta-cusp screens.** These provide source-pure entire functions converging
   locally uniformly and zero-preservingly to Xi, but their zeros need not be real. A uniform
   four-unit boundary-strip budget excludes every off-line zero packet remaining in a compact
   substrip. It is therefore another form of the unresolved horizontal zero control, not a free
   consequence of kernel positivity.
3. **All-prime signed-Mobius continuation.** Its reciprocal-zeta quotient already contains the
   actual zeta divisor. Proving its four-unit bound is the Xi estimate itself.

Consequently the boundary-strip theorem remains useful for identifying the minimal limiting norm,
but it does not weaken either primary CCM completion: divisor-preserving determinant convergence or
cofinal Weil spectral-floor convergence.

## Lean status

**Formalized unconditionally, 2026-08-04**, in
`formal/GaloisForLFunctions/RHTower/CCMBoundaryStripTransfer.lean`, together with the kernel-model half
that the tree already owned.

- **`norm_le_of_weak_limit`** — the weak lower semicontinuity step of the proof of `(3)`, in the shape
  the card actually consumes: a weak limit inherits every *eventual* norm bound.  Proof: Cauchy--Schwarz
  against the limit itself, `‖x‖² = lim <x, A n> ≤ ‖x‖ c`.  Stated with an eventual bound rather than a
  `liminf`, because hypothesis `(7)` is a `limsup` bound, and this form composes with it directly.
- **`eq_of_graphCore`** — equations `(4)`–`(5)`.  A continuous map agreeing with `Q ∘ D` on a graph core
  agrees with it on the whole domain.  What the formal statement makes precise is that **only** the
  approximation property is used: for each `f`, approximants in `C` converging to `f` *together with*
  their `D`-images.  No closedness of `D`, no density of the domain, and no linearity enter.
- `fourMulCDF_pos`, **`tendsto_one_sub_exp_neg_div`**, **`tendsto_div_fourMulCDF`**,
  **`eventually_div_le_one_add_of_le_fourMulCDF`** — equations `(8)`–`(9)`.  A profile with
  `Delta(u) <= 4(1 - e^{-u}) + r(u)` and `r(u) = o(u)` satisfies
  `limsup_(u -> 0+) Delta(u)/(4(1 - e^{-u})) <= 1`, stated in its epsilon form to avoid extended-real
  junk values.  The two analytic inputs are the slope of `1 - e^{-u}` at the origin and the resulting
  `u/(4(1-e^{-u})) -> 1/4`; both are proved here.

The **kernel-model half of `(3)`** was already in the tree and is not re-proved:
`RHTower.hsNormSq_le_of_tendsto_entries` in `MobiusFisherContactWardBudget.lean` is exactly entrywise
(weak) lower semicontinuity of the Hilbert--Schmidt energy, and `RHTower.completedSourceWardBudget` is
the budget transfer it feeds.  Together with `norm_le_of_weak_limit` and `eq_of_graphCore` the card's
section 1 is covered: the corpus's Hilbert--Schmidt layer (`HTGeometry/HilbertSchmidt.lean`) realises
`S_2` inside `lp 2`, which is where the abstract weak-limit lemma applies.

- **`norm_le_of_weak_limit_complex`**, **`hsNormSq_le_of_weak_limit`** — equation `(3)` itself,
  assembled in the corpus's `lp 2` realisation of `S_2`: a family of Hilbert--Schmidt kernels whose
  pairings against the limit converge, with energies eventually at most `B`, has a limit of energy at
  most `B`.  This is the card's conclusion with **no weak compactness, no norm convergence of the
  operators, and no trace-class property**.  The complex form takes real parts of the pairing rather
  than its norm, because the `RCLike` cast of `‖x‖²` produced by `inner_self_eq_norm_sq_to_K` matches
  neither `Complex.norm_real` nor `RCLike.norm_ofReal`.

What is **not** formalized, deliberately: the weak-compactness extraction of the card's own proof.  The
formalization does not need it — the standard argument extracts a weakly convergent subsequence from a
bounded family in `S_2`, which in Lean would require Eberlein--Smulian or separability, neither of which
is in mathlib.  The route taken instead bounds each finite piece directly, so the conclusion `(3)` is
reached with no compactness at all.  This is a strictly weaker hypothesis set than the card's, not a
gap.

## Lean gates

- [x] Lean: weak lower semicontinuity of the norm, in eventual-bound form
- [x] Lean: graph-core extension `(4)`–`(5)`, using only the approximation property
- [x] Lean: four-unit asymptotics `(8)`–`(9)` with an `o(u)` remainder
- [x] Lean: entrywise lower semicontinuity of the Hilbert--Schmidt energy (pre-existing)
- [x] Lean: the `S_2`-valued weak-limit statement `(3)` assembled against the corpus
      Hilbert--Schmidt realisation

## Gates

- [x] abstract graph-core lower-semicontinuity theorem proved
- [x] full-operator norm convergence removed
- [x] full trace class removed
- [x] four-unit specialization proved
- [x] notes-level arithmetic, pointing, and metric carriers coupled
- [x] canonical finite-stage sources attacked
- [x] real-spectrum graph-core shortcut proved RH-equivalent
- [x] retired as an independent lower-burden CCM completion
- [ ] use `(7)` only if a genuinely transverse finite-stage source is constructed
- [ ] RH
