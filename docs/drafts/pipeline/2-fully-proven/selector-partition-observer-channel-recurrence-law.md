# Selector-partition observer-channel recurrence law

- **ID:** `selector-partition-observer-channel-recurrence-law`
- **Stage:** 2 -- fully proven on paper
- **Type:** exact adaptive-history theorem / failed-frontier replacement
- **Parent:** `centralizer-centered-shortcut-history-recurrence-energy-law.md`
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean promotion:**
  `../3-formalized/selector-partition-observer-channel-recurrence-law.md`
- **Failed route:**
  `../5-failed/scalar-centralizer-recurrence-energy-as-brown-onset-provider.md`
- **Date:** 2026-08-14

## Public sentence

Quantum recurrence measures reuse of an observational channel; complexity growth can instead spend
its history on producing new channels, whose unavoidable diagonal cost no amount of dephasing can
erase.

## Setup

Let `J` be a finite time-sample type, `C` a finite observer-channel type, and `F` a real Hilbert
space.  Let

```text
r_j in F                         dynamical memory at sample j,
q_c in F                         preparation memory of channel c,
sigma : J -> C                   adaptive selected channel,
w_j >= 0                         sample weight.
```

For each channel define its masked weight, total load, and memory:

```text
m_c(j) = w_j if sigma(j)=c, else 0,
W_c    = sum_j m_c(j),
V_c    = sum_j m_c(j) r_j.
```

Define selector-load and selector-recurrence energies

```text
L_sigma = sum_c W_c^2,
R_sigma = sum_c ||V_c||^2.
```

## Theorem A -- selector-partition observer--spectral law

Assign every channel its own nonnegative margin `eta_c`.  Assume

```text
eta_(sigma j) <= <r_j,q_(sigma j)>       for every j.
```

Then

```text
boxed:
sum_c eta_c^2 W_c^2
 <= sum_c ||q_c||^2 ||V_c||^2.                            (SP1)
```

No collision sign condition against unselected targets is needed.  Target adaptation is retained
exactly by the partition rather than erased by a uniform target average.

If `eta<=eta_c` and `||q_c||^2<=B` for every occupied channel, `(SP1)` gives the uniform corollary

```text
eta^2 L_sigma <= B R_sigma.                               (SP1u)
```

### Proof

Fix `c`.  Nonnegative weights and the selected-channel alignment give termwise

```text
eta_c m_c(j) <= m_c(j) <r_j,q_c>.
```

Summing and using linearity yields

```text
eta_c W_c <= <V_c,q_c>.
```

Both sides are nonnegative.  Squaring and applying Hilbert-space Cauchy--Schwarz gives

```text
eta_c^2 W_c^2
 <= <V_c,q_c>^2
 <= ||V_c||^2 ||q_c||^2.
```

Summing over `c` proves `(SP1)`.  The two uniform bounds prove `(SP1u)`.

## Theorem B -- exact selector-filtered stationary kernel

Let `U(t)` be a real unitary flow and let `r_j=U(t_j)z`.  Then

```text
R_sigma
 = sum_(i,j) 1_{sigma(i)=sigma(j)} w_i w_j
     <z,U(t_j-t_i)z>.                                      (SP2)
```

### Proof

Expand every `||V_c||^2` bilinearly.  A pair `(i,j)` occurs in the `c`-summand exactly when
`sigma(i)=c=sigma(j)`, hence exactly when the two selected channels agree.  Unitarity and the group
law give

```text
<U(t_i)z,U(t_j)z>=<z,U(t_j-t_i)z>.
```

This proves `(SP2)`.

## Theorem C -- recurrence/channel-production dichotomy

Two extreme selector partitions are exact.

1. If `sigma` is constant, every pair survives and

   ```text
   R_sigma = ||sum_j w_j U(t_j)z||^2,
   ```

   the scalar recurrence energy of the parent theorem.

2. If `sigma` is injective, only diagonal pairs survive and

   ```text
   boxed: R_sigma = ||z||^2 sum_j w_j^2.                  (SP3)
   ```

   It is independent of all time differences and spectral phases.

Thus temporal recurrence controls repeated use of a channel.  A history selecting a fresh channel
at every sample has no off-diagonal recurrence obligation at all; it pays the exact diagonal
channel-production energy `(SP3)`.

## Theorem D -- target-specific two-memory capstone

Take nested orthogonal projections `Pi<=P`, a unitary flow fixing `range P`, and seed `x`.  For
every target `y_c` with `Pi y_c=Pi x`, put

```text
z   = x-Px,
q_c = y_c-Pi x,
B_c = <Pi x,Pi x> + <(P-Pi)x,q_c>.
```

Assign every target its own nonnegative completed margin `eta_c`.  Suppose sample `j` selects
`sigma(j)` and

```text
<U(t_j)x,y_(sigma j)> >= B_(sigma j)+eta_(sigma j).
```

The exact two-memory collision decomposition gives

```text
<U(t_j)z,q_(sigma j)> >= eta_(sigma j).
```

Applying `(SP1)--(SP2)` proves

```text
boxed:
sum_c eta_c^2 (sum_(j:sigma(j)=c) w_j)^2
 <= sum_c ||q_c||^2
      sum_(i,j:sigma(i)=c=sigma(j)) w_i w_j
        <x-Px,U(t_j-t_i)(x-Px)>.                         (SP4)
```

Unlike the averaged parent law, `(SP4)` has no inverse-total-dictionary attenuation, no
nonnegative-overlap premise for unselected targets, and no target frame-energy surrogate.  It pays
the actual selected-channel occupancy partition.

## Sharpness

The saturation mechanism does not require orthogonality. Take `J=C`, select `sigma(c)=c`, put
`q_c=r_c`, and choose the channel margin `eta_c=||r_c||^2`. Each occupied channel is a singleton,
so for arbitrary vectors and arbitrary weights

```text
eta_c^2 W_c^2 = ||q_c||^2 ||V_c||^2
```

term by term. Thus `(SP1)` is exactly saturated by fresh self-target channels before any spectral
or cross-channel geometry enters.

Let `J=C`, take an orthonormal family `e_c`, put `r_c=q_c=e_c`, choose `sigma(c)=c`, and use unit
weights.  Then `eta_c=1`, `W_c=1`, `V_c=e_c`, and both sides of `(SP1)` equal `|C|`.  Hence the
diagonal channel-production term and coefficient one are sharp.

The same example saturates the parent scalar law after uniform averaging:

```text
q_bar=|C|^(-1)sum_c e_c,
||q_bar||^2=|C|^(-1),
||sum_c e_c||^2=|C|,
<sum_c e_c,q_bar>^2=1.
```

Therefore neither better source dephasing nor a sharper universal Hilbert inequality can turn the
scalar recurrence law into a first-onset theorem.

## Hostile audit

- **Signed weights:** `(SP1)` needs nonnegative weights.  `(SP2)` is an identity for arbitrary real
  weights.  No signed-threshold claim is made.
- **Empty channels:** contribute zero to both sides.
- **Refinement monotonicity:** not claimed.  Splitting a channel removes signed cross terms and can
  raise or lower recurrence energy.  Only the two extreme identities are asserted.
- **Fresh channels:** `(SP3)` is not a decay theorem; it proves why dephasing cannot address them.
- **Brown onset:** the theorem does not prove ordinary static-H channel production.  It changes the
  exact open core from a false scalar-energy ceiling to selector-resolved incidence/channel
  production after return and carrier removal.
- **Physics:** no black-hole interior identification follows from Hilbert geometry alone.
- **Novelty:** direct sums, Gram matrices, Cauchy--Schwarz, cross-Gram operators, and participation
  ratios are classical.  Application priority of `(SP4)` is unverified.

## External and corpus boundary

- Brown and Susskind conjecture linear growth, a long plateau, and recurrence for chaotic quantum
  dynamics; this theorem proves none of those ensemble-specific rates.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones prove saturation and recurrence for random circuits
  and stochastic local Hamiltonian dynamics, not one ordinary static Hamiltonian.
- Frame-potential and cross-Gram literature already studies Hilbert incidence operators.
- Local phase-twisted replica-action and return-excised coarea laws already establish that labels
  must survive until after positive moments.  `(SP1)--(SP4)` apply that lesson to the later
  centralizer-recurrence history law and expose its exact scale obstruction.

## Exact frontier consequence

The scalar quenched recurrence-energy bound named as the sole remaining source obligation is
retired.  Correct unresolved statement must prove, for one ordinary static local Hamiltonian,
either:

1. direct selector-resolved cross-incidence anti-concentration strong enough for the complete
   circuit union; or
2. growth of the number of occupied observer-resolution channels faster than shallow-circuit
   capacity, while same-channel recurrence remains controlled.

This is a stricter and structurally different target than source dephasing.

The deterministic bridge between the two alternatives is now proved in
`observer-channel-recurrence-production-dichotomy-law.md`: total shortcut mass satisfies
`eta^2 W^2 <= B M_sigma R_sigma`. Consequently the remaining ensemble theorem is precisely a
uniform strict recurrence-budget estimate over every canonical resolution-separated selector with
bounded shallow-circuit capacity—not scalar dephasing of the unlabelled source.

## Promotion gates

- [x] scalar-source conjecture killed by singleton and orthogonal saturation
- [x] diagonal-subtraction repair killed
- [x] strongest positive survivor identified
- [x] dependency-closed proof of `(SP1)--(SP4)`
- [x] hostile audit
- [x] exact Lean theorem
- [x] umbrella wiring and axiom audit
