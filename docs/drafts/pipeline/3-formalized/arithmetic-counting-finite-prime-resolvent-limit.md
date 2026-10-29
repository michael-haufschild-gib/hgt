# Finite-prime conductor mass determines the full actual resolvent

- **ID:** ACP-FINITE-PRIME-RESOLVENT-LIMIT
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** arithmetic-counting-finite-prime-secular-gap.md
- **Sources:** arithmetic-counting-finite-prime-spectral-mass; arithmetic-counting-finite-prime-spectral-coordinates; arithmetic-counting-parity-resolvent-limit in stage three
- **Statement:** For every finite prime set F and 0<s<2 log 2, the whole actual finite resolvent converges to c_F^2 times its normalized arithmetic secular series. The series is strictly increasing on that interval.

## Exact objects

Let c_F be the positive product harmonic density, b_F the Möbius transform,
`w_F(m)=b_F(m)^2/phi(m)`, and `a_F(m)=c_F b_F(m)/sqrt(phi(m))`.
Let E_m be the conductor adjunction energy and `D_m=E_m-gamma`.
The normalized secular function is

`Phi_F(s)=-1/s+sum_(m>=2) w_F(m)/(D_m-s)`.

At horizon N let e_i be the actual orthonormal prime eigenbasis, E_(i,N)
its energy, and v_(F,N) the unit harmonic sign constraint. The finite reading is

`R_(F,N)(s)=sum_i <v_(F,N),e_i>^2/(E_(i,N)-gamma-s)`.

The theorem asserts `R_(F,N+1)(s)->c_F^2 Phi_F(s)`, for every fixed finite
prime set and fixed s in (0,2 log 2). All eigenlines enter the finite reading.

## Closed proof

### 1. Summability and normalization

The conductor mass theorem gives `sum_(m>=0) a_F(m)^2=1`, with a_F(0)=0
and a_F(1)=c_F. Since `a_F(m)^2=c_F^2 w_F(m)` and c_F>0, the nonnegative
weights w_F are summable. Every m>=2 has `D_m>=2 log 2`. Thus for fixed
0<s<2 log 2,

`0<=w_F(m)/(D_m-s)<=w_F(m)/(2 log 2-s)`.

Comparison proves summability of the entire positive-conductor tail.
Multiplication by c_F^2 and separation of the ground term give

`sum_(m>=1) a_F(m)^2/(D_m-s)=c_F^2 Phi_F(s)`.

This is a HasSum identity; no conditionally convergent rearrangement is used.
The empty prime set is included: only the ground conductor carries mass.

### 2. Actual finite packets

For each positive conductor m=k+1, the coordinate theorem provides an actual
index sequence i_(k,N) at horizons N+1. Its energy above gamma tends to
D_(k+1), and its squared constraint coordinate tends to a_F(k+1)^2.
The adjunction energies of distinct positive conductors are distinct.
For k!=l, the square of the difference of the two selected energies therefore
has a strictly positive limit. Their indices are different eventually.
Intersecting these events for a finite packet makes the whole packet injective.
No monotone ordering of energies by integer conductor is required.

### 3. All omitted lines have a positive denominator

Put `eta=(2 log 2-s)/2`. The actual bounded-spectrum count at
`gamma+s+eta` is one eventually. The selected ground energy tends to gamma,
so its index is in that sublevel eventually. Every other actual index then
has energy at least `gamma+s+eta`. Consequently all omitted reciprocal
denominators are at least eta>0, independently of the chosen packet.

Parseval gives unit total squared constraint mass at each positive horizon.
For the packet of conductors 1 through K+1 let L_(K,N) be its reciprocal
sum and M_(K,N) its squared coordinate mass. Exact finite summation gives

`L_(K,N)<=R_(F,N+1)(s)<=L_(K,N)+(1-M_(K,N))/eta`

once the packet indices are distinct and the ground is included. Each fixed
packet sum and mass converge to their counted arithmetic values. As K grows,
the packet mass tends to one and the packet reciprocal sum tends to the full
HasSum value in step 1. The already proved packet-limit theorem therefore
squeezes the complete actual reading to c_F^2 Phi_F(s). The eventual horizon
may depend on K; the proof does not require a uniform packet horizon.

### 4. Strict monotonicity

For 0<s<t<2 log 2, every positive denominator remains positive and
`w_F(m)/(D_m-s)<=w_F(m)/(D_m-t)`. Summability permits termwise comparison
of the two tails. The ground term satisfies `-1/s<-1/t`. Adding this strict
inequality proves `Phi_F(s)<Phi_F(t)`, even when the tail is identically zero.

## Reuse and integrity

The generic packet theorem is the already proved private lemma
`tendsto_reciprocal_mass_of_packets` in
`TheParityTowerDeterminesTheFiniteResolvent.lean`. Its hypotheses are all
explicitly discharged above by the actual finite spectrum and counted mass.
The formalization reuses it through the documented
`Batteries.Tactic.OpenPrivate` command, whose installed source and existing
olean were inspected. This command only opens the proved constant locally;
it adds no premise or kernel shortcut and avoids copying the packet proof.
The invocation and all four endpoints passed Lean. No hardcoded
mangled name is used, and the old module's existing olean is not rebuilt.

This contribution is full finite resolvent convergence for arbitrary finite
prime sets. It does not by itself assert the joint greatest gap, root location,
prime-exhaustion rate or complete Weil positivity.

## Formalization

Canonical source: `formal/GaloisForLFunctions/ArithmeticCountingPositivity/FinitePrimeCountsDetermineTheFullResolvent.lean`.

- `summable_finiteFlipSecularTail`
- `hasSum_finiteFlipSecularSeries`
- `tendsto_finiteFlipFiniteResolvent`
- `finiteFlipSecular_strictMonoOn`

Scratch 11788 and canonical check 25395 both exited zero without diagnostics.
All four transitive audits use only `propext`, `Classical.choice`, and
`Quot.sound`. Exact commands, source hash and output are in the adjacent
`-audit.txt`. The umbrella is wired but was not compiled.

- [x] Dependency-complete paper proof.
- [x] Four Lean endpoints and transitive axiom audit.
- [x] Canonical source audit, wiring, durable evidence and cleanup.
