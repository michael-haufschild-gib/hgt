# Quenched Krylov--circuit incidence front law

- **ID:** `quenched-krylov-circuit-incidence-front-law`
- **Stage:** 1 -- in progress
- **Type:** bold conjecture / sole finite-onset core
- **Parent:** `../2-fully-proven/radial-krylov-projected-complete-incidence-law.md`
- **Replaces:** `scale-matched-signed-action-packet-law.md`
- **Status:** `[CONJECTURE] [EXACT OBJECT] [OPEN LOCAL-HAMILTONIAN CORE] [NO LEAN DURING REFACTOR]`
- **Date:** 2026-08-08

## Public sentence

**Conjecture:** static quantum complexity grows when the moving Krylov history becomes transverse
to every history producible by a shorter circuit; replica order measures the advancing causal
front, not an individual spectral gap.

## Exact object

Use the unit fixed-strength nearest-neighbour Pauli coefficient shell on `n` qubits, with
`D=2^n`, a finite local gate dictionary of branching number `M_n`, and one efficiently preparable
stabilizer seed `chi`.  For the sampled time-independent Hamiltonian `H`, define

```text
K_K(H,chi) = span { chi,H chi,...,H^K chi },
P_K = Proj_(K_K(H,chi)),
phi_K(t) = P_K exp(-itH) chi.
```

Let `Z_s(chi)` be the distinct occupied depth-at-most-`s` circuit endpoint image after the fixed
anchor/return residualization already proved in the corpus.  At replica order `r`, put

```text
S_(K,r,s) = span { (P_K z)^(tensor r) : z in Z_s(chi) },

Q_(K,r,s)(H,chi,t)
 = ||Proj_(S_(K,r,s)) phi_K(t)^(tensor r)||^2.               (1)
```

This is duplication-invariant, retains the actual projected occupied endpoint image, and is
defined before any target selector.  The parent theorem proves that the original complete shortcut
incidence action is at most `(1)` plus

```text
2 r (B_n |t|)^(K+1)/(K+1)!,                                (2)
```

where `B_n` is the deterministic shell operator-norm ceiling.

## Frozen conjecture

There exist constants and a subextensive microscopic cutoff `r_*(n)=o(D)`,

```text
C_0>0,   0<c_r<1,   0<c_t<exp(-(1+delta)),
gamma>0,   delta>0,   beta>0,
```

and target-independent return sets `R_(n,t)` such that the following holds.  For

```text
r_*(n) <= r <= c_r D,
C_0 r/B_n <= |t| <= c_t D/B_n,
K+1 = ceil(exp(1+delta) B_n |t|),
s+1 = floor(beta r/log M_n),                                (3)
```

whenever this interval is nonempty, the static one-draw ensemble satisfies

```text
Pr{R_(n,t)}
 + integral_(R_(n,t)^c) Q_(K,r,s)(H,chi,t) dmu_n(H,chi)
 <= o_n(1) + exp(-gamma r),                                 (4)
```

where `gamma` is large enough that the exact capture threshold factor from the parent theorem is
absorbed.  No disorder is refreshed between times, targets, replicas, or circuit words.

Equation `(4)`, not a minimum-gap law or signed total-variation contraction, is the remaining
finite-onset assertion needed to turn the already proved plateau capacity, duration, recurrence,
and permanent locality witness into Brown--Susskind growth--plateau--recurrence for one ordinary
static local ensemble.

## Consequence if proved

The parent complete-incidence law and `(2)--(4)` would give

```text
C_epsilon(exp(-itH)chi)
 >= Omega(min{B_n |t|,D}/log M_n)                           (5)
```

with high pair probability outside the one paid return filtration, until the existing
near-maximal plateau theorem takes over.  Existing locality/simulation bounds supply the matching
polynomially normalized upper cone, and existing recurrence theorems supply later low-complexity
returns for the same fixed pair.

## Conjecturing and falsification ledger

### C0 -- individual spectral-action anti-concentration

**Failed.** Observer-dimensional crowding forces exponentially small nonzero balanced gradients at
`r=Theta(D)`, and absolute small-gradient coefficient mass exceeds the capture scale.

### C1 -- raw observer-Jacobian pseudodeterminant

**Failed.** Reporter duplication changes the determinant while leaving the physical tube fixed.
Frame normalization repairs invariance but cannot encode occupied target incidence.

### C2 -- full signed packet contraction

**Refined.** Before a quotient norm is specified this can be circular.  The parent theorem closes
all packet mass outside the causal Krylov carrier with one factorial error and no target union.

### C3 -- targetwise Krylov carrier load

**True but insufficient.** A targetwise sum pays circuit entropy.  Projection before the replica
lift yields `(1)`, which absorbs the complete occupied image once.

### C4 -- projected Hilbert rank controls `(1)`

**False.** A single target parallel to `phi_K(t)` gives rank one and action nearly one.

### C5 -- Gaussian radius randomizes the projected target geometry

**False by exact rigidity.** For `H(cx)=cH(x)`, the Krylov flag and projected occupied image are
unchanged and `(1)` at `(cx,t)` equals `(1)` at `(x,ct)`.  Gaussian radial disorder is only a
positive time mixture of fixed-shell actions.

### C6 -- quenched Krylov--circuit angle decay

**Survives.** It is precisely `(4)`.  It cannot be weakened to rank, worst gap, one target, one
replica, completed-time equidistribution, or fresh-random circuit theory.

## Falsifiers

The conjecture dies if any of the following has nonvanishing ensemble mass along a cofinal system
sequence:

1. after the prescribed return removal, `Q_(K,r,s)>=exp(-o(r))` at a time satisfying `(3)`;
2. a shallow occupied circuit image tracks the random Krylov orbit through a positive fraction of
   the proposed front window;
3. a conserved projected endpoint sector survives residualization and forces order-one action;
4. the best valid `K` needed to make `(2)` negligible reaches the full cyclic dimension strictly
   before a linear-depth lower bound can be extracted;
5. the completed near-maximal plateau can be preceded by an arbitrarily long carrier-incidence
   delay on a positive-measure pair set.

## Exact next mathematical move

Disintegrate `(4)` on the fixed coefficient sphere, condition on the random Krylov flag, and bound
the spectrum of the compressed occupied-image covariance

```text
Proj_(S_(K,r,s))
  E[ |phi_K(t)^(tensor r)><phi_K(t)^(tensor r)|
     | K_K(H,chi) ]
Proj_(S_(K,r,s)).                                           (6)
```

Required estimate is an upper bound on its trace against the **actual** projected endpoint image,
uniform through growing `K,r`.  Operator norm over the whole carrier is too strong and generally
one; Hilbert--Schmidt normalization alone is too weak.  Candidate mechanism must use local Pauli
word geometry to show that shallow-circuit Veronese directions occupy exponentially little of the
conditional orbit covariance.

## Hostile audit

- `(4)` is unproved and may be false.  No Brown growth claim is authorized.
- The causal projection theorem is a real reduction but not decay: it can enlarge the incidence
  action when distinct targets collapse inside the carrier.
- `K=Theta(B_n t)` approaches the full cyclic dimension near saturation.  Constants in `(3)` must
  leave a nonempty regime; this cannot be hidden asymptotically.
- Completed-time phase orthogonality and static spectral ramps do not imply `(6)`.
- A Nature-level manuscript remains impossible until `(4)` is proved, externally prioritized, and
  combined with the already proved plateau/recurrence/locality components without presenting a
  collage.

## Pipeline

- [ ] Stage 1 -> 2: prove or falsify `(4)`
- [ ] Stage 2 -> 3: frozen; no Lean work during corpus refactor
- [ ] Stage 3 -> 4: external priority and hostile journal audit
