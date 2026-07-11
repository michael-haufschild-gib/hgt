# Weak boundary-strip compactness transports the four-unit CCM budget

- **ID:** `ccm-boundary-strip-weak-compactness-transfer-law`
- **Stage:** 2-fully-proven
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

## Gates

- [x] abstract graph-core lower-semicontinuity theorem proved
- [x] full-operator norm convergence removed
- [x] full trace class removed
- [x] four-unit specialization proved
- [x] notes-level arithmetic, pointing, and metric carriers coupled
- [x] canonical finite-stage sources attacked
- [x] real-spectrum graph-core shortcut proved RH-equivalent
- [ ] construct the canonical finite-stage operators `A_(N,u)`
- [ ] prove their uniform budget `(7)`
- [ ] RH
