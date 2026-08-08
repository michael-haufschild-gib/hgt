# Quenched Krylov--circuit incidence front law

- **ID:** `quenched-krylov-circuit-incidence-front-law`
- **Stage:** 1 -- in progress
- **Type:** bold conjecture / sole finite-onset core
- **Parents:** `../2-fully-proven/radial-krylov-projected-complete-incidence-law.md`,
  `../2-fully-proven/bures-incidence-minimax-coarea-law.md`
- **Replaces:** `scale-matched-signed-action-packet-law.md`
- **Status:** `[CONJECTURE] [EXACT OBJECT] [OPEN LOCAL-HAMILTONIAN CORE] [NO LEAN DURING REFACTOR]`
- **Date:** 2026-08-08

## Public sentence

**Conjecture:** static quantum complexity grows when the moving Krylov history becomes transverse
to every history producible by a shorter circuit; replica order measures the advancing causal
front, not an individual spectral gap.

## 2026-08-08 frontier advance -- Bures incidence replaces full-span load

The full projected-span action `(1)` is sufficient but no longer the minimal open invariant.  The
paper-proved Bures incidence minimax law shows that the complete circuit union is controlled by the
maximum quantum fidelity between quenched replica covariance and the convex hull of actual
occupied target rays.  This source-aware quantity is never larger than the occupied-span trace and
can be arbitrarily smaller.

The ordinary ensemble must be disintegrated honestly: condition on the seed `chi`, so
`Z_s(chi)` is fixed, but retain Hamiltonian randomness in the covariance.  Conditioning on the
entire random Krylov flag is not assumed useful; in identifiable families the flag can reveal the
coefficient direction and leave almost no conditional randomness.

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

For the sharper ensemble object, with `psi_(H,chi)(t)=exp(-itH)chi`, define

```text
C_(r,t,R)^chi
 = E_H[1_(R^c)(H,chi)
       |psi_(H,chi)(t)^(tensor r)>
       <psi_(H,chi)(t)^(tensor r)|],

K_(r,s)^chi
 = closed convex hull
   {|z^(tensor r)><z^(tensor r)| : z in Z_s(chi)},

B_(r,t,s,R)
 = E_chi max {F(C_(r,t,R)^chi,M)^2 : M in K_(r,s)^chi}.
```

Equivalently, for every occupied-target probability design `lambda`, define

```text
(K_(r,t,R,lambda)^chi c)(H)
 = 1_(R^c)(H,chi)
   sum_(z in Z_s(chi)) sqrt(lambda_z) c_z
     <exp(-itH)chi,z>^r.
```

Then

```text
B_(r,t,s,R)
 = E_chi sup_lambda ||K_(r,t,R,lambda)^chi||_(Schatten 1)^2. (2b)
```

This is the exact incidence-normalized coarea operator: `H`-fibres remain distinct source rows,
occupied endpoints form target columns, and replica order acts on the physical overlap kernel
before the nuclear norm.

Here `F(C,M)=Tr sqrt(C^(1/2) M C^(1/2))` is root fidelity for positive,
possibly unnormalized operators.  The complete shortcut probability is unconditionally at most

```text
Pr(R) + a^(-r) B_(r,t,s,R)                               (2a)
```

at squared-fidelity threshold `a`.

## Frozen conjecture

There exist constants and a subextensive microscopic cutoff `r_*(n)=o(D)`,

```text
C_0>0,   0<c_r<1,   0<c_t<1,
gamma>0,   beta>0,
```

and target-independent return sets `R_(n,t)` such that the following holds.  For

```text
r_*(n) <= r <= c_r D,
C_0 r/B_n <= |t| <= c_t D/B_n,
s+1 = floor(beta r/log M_n),                                (3)
```

whenever this interval is nonempty, the static one-draw ensemble satisfies

```text
Pr{R_(n,t)} + a^(-r) B_(r,t,s,R_(n,t))
 <= o_n(1) + exp(-gamma r).                                 (4')
```

Here `gamma` is the post-threshold exponent; `a^(-r)` is displayed rather than hidden.  No disorder
is refreshed between times, targets, replicas, or circuit words.

The former sufficient conjecture was the stronger full-span estimate

```text
Pr{R_(n,t)}
 + integral_(R_(n,t)^c) Q_(K,r,s)(H,chi,t) dmu_n(H,chi)
 <= o_n(1) + exp(-gamma r),                                 (4)
```

with `K+1=ceil(exp(1+delta)B_n|t|)`.  Fidelity Cauchy--Schwarz shows that `(4)`
implies `(4')`, but it may be arbitrarily stronger.

Equation `(4')`, not full-span decay `(4)`, a minimum-gap law, or signed total-variation
contraction, is the remaining finite-onset assertion needed to turn the already proved plateau
capacity, duration, recurrence, and permanent locality witness into Brown--Susskind
growth--plateau--recurrence for one ordinary static local ensemble.

## Consequence if proved

The Bures complete-incidence law and `(4')` would give

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

**Survives but is stronger than necessary.**  Full-span decay `(4)` would close the problem, but it
forgets covariance orientation inside that span.

### C7 -- source-aware Bures incidence

**Paper-proved exact reduction; local decay open.**  The complete target union is bounded by
`(2a)`, and the Bures quantity is exactly the best positive ellipsoidal reporter.  It cannot be
weakened to rank, worst gap, one target, one replica, completed-time equidistribution, or
fresh-random circuit theory.

## Falsifiers

The conjecture dies if any of the following has nonvanishing ensemble mass along a cofinal system
sequence:

1. after the prescribed return removal, `a^(-r)B_(r,t,s,R)>=exp(-o(r))` at a time satisfying `(3)`;
2. a convex mixture of shallow occupied replica rays has Bures fidelity `exp(-o(r))` with the
   quenched orbit covariance through a positive fraction of the proposed front window;
3. a conserved projected endpoint sector survives residualization and forces order-one action;
4. the best valid `K` needed to make `(2)` negligible reaches the full cyclic dimension strictly
   before a linear-depth lower bound can be extracted;
5. the completed near-maximal plateau can be preceded by an arbitrarily long carrier-incidence
   delay on a positive-measure pair set.

## Exact next mathematical move

Do not condition on the full random Krylov flag without proving that useful randomness remains.
Disintegrate only by the efficient seed and prove `(4')`.  Equivalently, construct a positive
reporter `A_chi>0` such that

```text
Tr(C_(r,t,R)^chi A_chi)
  sup_(z in Z_s(chi))
    <z^(tensor r),A_chi^(-1)z^(tensor r)>
 <= exp(-gamma r)                                           (6)
```

after the one paid exceptional/return sector and averaging over `chi`.  By the Bures minimax
identity, optimizing `(6)` is exactly `(4')`; choosing a reporter is a proof strategy, not a new
hypothesis.  Candidate mechanism must use local Pauli word geometry to separate quenched orbit
covariance from the **convex body of actual shallow-circuit rays**.  Operator norm over the whole
carrier is too strong and generally one; Hilbert--Schmidt normalization and occupied rank are too
weak.

In operator language, exact task is uniform growing-replica nuclear-norm contraction in `(2b)`.
The identity `||K||_1^2<=rank(K)||K||_2^2` explains the dimension loss in every fixed-target
Hilbert--Schmidt attack, while operator norm discards source-sheet multiplicity.  Any successful
cavity, transfer, or Pauli-word argument must control the singular-value profile, not only its
largest value or squared mass.

An equivalent sufficient route is now exact.  Construct one seed-dependent physical observer
channel or POVM for which the classical outcome law of `C_(r,t,R)^chi` has exponentially small
Hellinger affinity with every outcome distribution in the convex hull of `Z_s(chi)`.  Fidelity data
processing then proves `(6)` in the full replica carrier.  This is where oriented Krylov/history or
local Pauli-word observables may enter; they must separate convex mixtures, not merely individual
targets.

Equivalently, choose a Hermitian reporter `W_(r,chi)` and prove an opposite-tilt product bound for
`A=exp(W_(r,chi))`.  Additive one-copy reporters reduce `(6)` to one positive source exponential
moment times one worst occupied-target inverse moment, both raised through replica order.  Energy
and seed-return tilts are already falsified; the live candidate must resolve oriented history or
Pauli-word growth and may need genuine collective replica structure.

## Hostile audit

- `(4')` is unproved and may be false.  No Brown growth claim is authorized.
- The causal projection theorem is a real reduction but not decay: it can enlarge the incidence
  action when distinct targets collapse inside the carrier.
- The Bures theorem is an exact, strictly sharper universal reduction, not local-Hamiltonian
  anti-concentration.  Its maximum can equal one when source covariance enters the shallow-target
  convex hull.
- `K=Theta(B_n t)` approaches the full cyclic dimension near saturation.  Constants in `(3)` must
  leave a nonempty regime; this cannot be hidden asymptotically.
- Completed-time phase orthogonality and static spectral ramps do not imply `(6)`.
- A Nature-level manuscript remains impossible until `(4')` is proved, externally prioritized, and
  combined with the already proved plateau/recurrence/locality components without presenting a
  collage.

## Pipeline

- [ ] Stage 1 -> 2: prove or falsify `(4')`
- [ ] Stage 2 -> 3: frozen; no Lean work during corpus refactor
- [ ] Stage 3 -> 4: external priority and hostile journal audit
