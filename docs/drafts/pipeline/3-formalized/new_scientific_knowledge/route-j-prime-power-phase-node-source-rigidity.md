# Route J: prime-power phase-node source rigidity

**Status:** `[PAPER+LEAN-PROVED CLASSIFICATION]`
`[CANDIDATE SOURCE-SPECIFIC NEW KNOWLEDGE]` `[NOT RH]`

**Parent:** `../../1-in-progress/route-j-principal-relative-julia-current.md`, `J-SF6`.

**Claim boundary.** This result closes phase-node singularity for every uncensored
multi-prime prime-power source, including the literal Suzuki/von-Mangoldt far-hinge source. It does
not close one-prime towers, arbitrary singular measures, singular boundary distributions,
reflection-breaking carriers, or relation-valued channels.

## 1. Hard question

The exact four-atom Route-J escape uses full-turn times

```text
T, 2T, 3T, 4T
```

and therefore makes every sine row vanish atomwise. This mechanism is not automatically available
to an arithmetic source. The prime--Gamma and Suzuki wall sources have delays

```text
log(p^(e+1)) = (e+1) log p,
```

with nonzero weight at every prime power. Can one nonzero carrier place all these delays on its
sine-node lattice?

## 2. Two-prime obstruction

Let `u != 0`, let `p != q` be primes, and let `a,b` be positive integers. Suppose

```text
sin(u a log p)=0,
sin(u b log q)=0.                                      (1)
```

There are integers `m,n` with

```text
m pi = u a log p,
n pi = u b log q.                                      (2)
```

Cross-multiplication gives

```text
u (a n log p - b m log q)=0.                           (3)
```

Since `u != 0`,

```text
(a n) log p + (-b m) log q=0.                          (4)
```

Unique factorization makes `log p,log q` integer-linearly independent, so

```text
a n=0,   b m=0.
```

Positivity of `a,b` gives `m=n=0`. Equation (2) then gives
`u a log p=0`, contradicting `u != 0`, `a>0`, and `log p>0`.

Hence:

> At a nonzero carrier, prime-power delays from two distinct prime bases cannot both be phase
> nodes.

No zero location, Xi multiplicity, asymptotic estimate, or RH premise enters this proof.

## 3. Exact rank-one classification

For a real multiplier

```text
A : (prime, depth) -> R
```

define its active prime-base set

```text
P(A)={p : exists e, A(p,e) != 0}.
```

Call `A` a phase-node multiplier at `u` if every active atom satisfies

```text
sin(u log(p^(e+1)))=0.                                 (5)
```

Applying the two-prime obstruction to any two elements of `P(A)` proves

```text
P(A) is subsingleton.                                  (6)
```

Equivalently, a phase-node multiplier must censor at least one of every pair of atoms whose prime
bases differ. This is the sharp arithmetic boundary: all depths on one prime ray have commensurate
delays and are not excluded.

## 4. Literal Suzuki/von-Mangoldt source

The updated source architecture supplies the far-hinge weight

```text
w(p,e)=Lambda(p^(e+1))/sqrt(p^(e+1))
      =log(p)/sqrt(p^(e+1)) > 0.                       (7)
```

Thus every prime-power atom is active. In particular the depth-zero atoms at primes `2` and `3`
are both active. Equation (6) is impossible. Therefore, for every `u != 0`,

```text
w is not a phase-node multiplier at u.                 (8)
```

This closes the phase-node escape for the literal uncensored Suzuki/von-Mangoldt far-hinge source.
Any phase-node singular repair of that source must first destroy source faithfulness by projecting
onto at most one prime tower.

## 5. Hostile/theatre audit

- The proof uses no Xi zero and no target multiplicity.
- The carrier `u` is arbitrary and only assumed nonzero.
- Coefficients are not fitted to `u`; the multiplier classification quantifies over every
  coefficient function.
- The source corollary uses the already proved literal weight (7), not a proxy with chosen support.
- The result does not promote the one-prime survivor to a construction.
- It does not claim arbitrary phase-node singular measures are impossible.

## 6. Novelty audit

The ingredients are classical:

- integer-linear independence of logarithms of distinct primes is unique factorization;
- sine zeros are integer multiples of `pi`;
- prime-power delays in Euler/Weil sources are standard.

Connes--Consani's semilocal framework treats finite sets of places and its source/operator
realization, while Connes--Consani--Moscovici analyze the single-prime
`S={p,infinity}` moment problem. See:

- A. Connes and C. Consani,
  [*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771);
- A. Connes, C. Consani, and H. Moscovici,
  [*On q-series and the moment problem associated to local factors*](https://arxiv.org/abs/2403.01247).

Targeted searches found no theorem identifying the exact Route-J phase-node boundary (6), nor its
application (8) to the uncensored Suzuki/von-Mangoldt far-hinge source. Candidate novelty is
restricted to this source-specific rank-one classification and its consequence for the Route-J
singular escape. No novelty is claimed for prime-log independence itself.

## 7. Lean certificate

Formalization:

```text
formal/GaloisForLFunctions/RHTower/
  XiCTaylorSignedPrimePhaseNodeSourceNoGo.lean
```

Principal declarations:

```text
routeJ_scaledPrimeLog_phaseNodes_incompatible
routeJ_primePowerLog_phaseNodes_incompatible
routeJ_primePowerPhaseNode_primeSupport_subsingleton
routeJ_primePowerPhaseNodeMultiplier_activePrimeSet_subsingleton
routeJ_primePowerPhaseNodeMultiplier_censors_distinctPrime
routeJSuzukiFarHingeSourceWeight_pos
routeJ_suzukiFarHingeSource_not_all_phaseNodes
```

Validation:

```text
lake env lean \
  GaloisForLFunctions/RHTower/XiCTaylorSignedPrimePhaseNodeSourceNoGo.lean

lake build \
  GaloisForLFunctions.RHTower.XiCTaylorSignedPrimePhaseNodeSourceNoGo
```

Both passed. Batched `#print axioms` reports only:

```text
propext
Classical.choice
Quot.sound
```

The module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## 8. Surviving frontier

Phase-node singularity is now split exactly:

```text
uncensored source with at least two prime bases: impossible;
arbitrary phase-node multiplier with at least two active prime bases: impossible;
one-prime prime-power tower: still live.
```

Route J remains open. Remaining work includes the one-prime tower, singular non-atomic/boundary
sources, variable regular four-change profiles, broken reflection, relation-valued carriers, and
the `J-SF5` singular semilocal Hardy compression.
