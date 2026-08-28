# SC holomorphic prime-log zero condensation

- **ID:** SC-HPLZC
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** read-only `rh-current-frontier-map.md` · route SC `LAND COMP`; corpus theorems `preDivisorRiggedPrimeNeutralPacketDeterminant_eq`, `tendsto_log_nthPrimePoint_atTop`, and `shrinking_periodic_zero_limit_vertical`
- **Statement:** After arbitrary packet-growing cancellation of the central SC wall zero, the coefficient-faithful holomorphic packet still has a first nonzero Bockstein zero `πi/log p_m → 0`; no regularizer finite at those moving points can produce entire approximants converging locally uniformly to normalized centered Xi.

## Goal
Close the surviving packet-growing scalar-regularization branch of the SC Xi-landing problem.  The
claim must identify what a viable landing is forced to change: primewise determinant factorization,
not a numerical constant or rate.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems `RHTower.not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicPacket_scalarFactor` and `RHTower.preDivisorRiggedPrimeHolomorphicPacket_clock`; exact leaf builds green, scoped axiom audits PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Origin and corpus baseline

The SC source corpus already proves the exact real neutral-packet determinant

`(1-(m+2)) · ∏ primeGammaCofinalBocksteinCoefficient(t,p_i)`.

The same corpus proves that the final packet prime tends to infinity on the logarithmic scale and
that locally uniform limits transport zero clocks, including clocks whose periods shrink to zero.
No searched declaration connects these facts to the coefficient-faithful holomorphic SC packet or
classifies scalar Xi landings by their forced prime-log singularities.

## Conjecture loop

1. **C1 — one moving zero is enough.**  Complexify each signed Bockstein by
   `a_p (exp(-z log p) - exp(z log p))`; the point `πi/log p` is a zero and tends to zero along
   packet-final primes.  Expected conclusion: normalized Xi would vanish at zero.
2. **C2 — full-clock strengthening fails after central cancellation.**  Every integral multiple
   of `2πi/log p` is a raw packet zero, but a packet-growing central pole is precisely allowed to
   cancel the `k=0` member.  Therefore the corpus full-clock transfer theorem cannot be applied to
   the surviving branch.  Pivot to the first nonzero member, which central cancellation cannot
   remove.
3. **C3 — survivor.**  Any viable coefficient-faithful SC landing must either introduce
   packet-dependent meromorphic poles at the selected moving nonzero prime-log zeros (and, for
   full divisor cancellation, their complete clocks) or break the
   primewise determinant product through genuine cross-prime/operator coupling.  A finite-valued
   scalar gauge at the moving points cannot work.

## Attack

Define the entire coefficient-faithful complex Bockstein and its finite packet product.  Prove its
restriction to the real transverse coordinate is the existing signed Gamma-Bockstein product.
Choose the final prime in each packet and prove the first nonzero clock-zero law, nonvanishing and
convergence of its period to zero.  For arbitrary entire regularized approximants agreeing with a
scalar multiple of the raw packet away from zero, finiteness of that scalar at the moving point
preserves the zero.  Local uniform convergence evaluated along the moving points forces normalized
Xi to vanish at the origin, contradicting its value `1` there.

## Paper proof `[PROVED HERE]`

For an ordinary prime `p`, put `L_p = log p` and let `a_p` be its source-selected occupancy
Fisher density.  Define

`B_p(z) = a_p (exp(-L_p z) - exp(L_p z))`.

This is entire.  On the real axis, `exp(L_p t)=p^t`, so `B_p(t)` is exactly the corpus signed
Gamma-Bockstein coefficient.  Hence

`D_m(z) = (1-(m+2)) ∏_{j < m+2} B_{p_j}(z)`

is the coefficient-faithful entire complexification of the exact neutral SC packet determinant.

Take the final packet prime `q_m=p_{m+1}`, put `τ_m=π/log q_m`, and `z_m=iτ_m`.  Ordinary primes
are at least two, hence `log q_m>0`, so `τ_m>0` and `z_m≠0`.  Since

`(log q_m) z_m = iπ`,

Euler's identity gives `exp(-(log q_m)z_m)=exp((log q_m)z_m)=-1`.  Thus `B_{q_m}(z_m)=0` and the
corresponding factor in the finite product gives `D_m(z_m)=0`.  More generally the same argument
gives the exact Bockstein zero clock `D_m(i kπ/log q_m)=0` for every integer `k`.

The corpus theorem `tendsto_log_nthPrimePoint_atTop`, composed with the shift `m↦m+1`, gives
`log q_m→+∞`.  Division of the constant `π` by this positive divergent sequence gives `τ_m→0`,
hence `z_m→0`.

Now let `F_m` be any entire regularized packet and `G_m` any complex-valued scalar profile such
that `F_m(z)=G_m(z)D_m(z)` for every `z≠0`.  Because `z_m≠0`, the factorization holds at `z_m`;
because `G_m(z_m)` is a finite complex value, `F_m(z_m)=0`.  If `F_m` converged locally uniformly
to a continuous function `F`, compact-uniform convergence composed with `z_m→0` would give
`F_m(z_m)→F(0)`.  The left side is identically zero, so `F(0)=0`.  For
`F(z)=XiC(z)/XiC(0)`, however, the unconditional corpus theorem `XiC_zero_ne` gives `F(0)=1`.
Contradiction.

No RH statement, zero-location assumption, asymptotic estimate, or numerical optimization enters
the proof.  All dependencies are unconditional and already present in the corpus.

## Strongest positive survivor

The obstruction classifies the divisor change a viable SC landing must perform.  Growing central
pole order alone cannot work: at packet size `m`, a scalar route must also be meromorphically
singular at `πi/log p_{m+1}` (and conjugate point) or destroy the primewise product factorization by
cross-prime/operator coupling.  Since these noncentral points converge to the wall origin, the
required pole set condenses there.  This is the exact new representation burden exposed by the
no-go.

## Literature audit (as of 2026-08-28)

- [Connes--Consani, *The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368) identify the
  local-factor lattice `2πi ℤ/log p` and use it to obstruct a Hardy
  inner-function route; this establishes that prime-log lattices themselves are not new.  The
  signed SC Bockstein has the finer zero lattice `πi ℤ/log p` because it is a reflected-minus-
  forward character.
- [Britz--Carey--Gesztesy--Nichols--Sukochev--Zanin](https://arxiv.org/abs/2007.12834) prove
  regularized Fredholm product formulas whose anomaly is an exponential trace correction.
- [Hartmann--Lesch](https://arxiv.org/abs/2106.02444) show regularized Fredholm determinants retain
  their spectral zero divisor, while zeta/Fredholm comparisons differ by an exponential
  polynomial.
- No located primary source states the SC packet-growing shrinking-clock obstruction or its forced
  cross-prime-coupling alternative.  **Novelty status:** `[NOVELTY UNVERIFIED]`.

## Door passport

- **Unconditional source:** exact SC packet determinant and ordinary-prime enumeration.
- **No RH leakage:** target input is only `XiC 0 ≠ 0` and continuity/differentiability already
  proved unconditionally in the corpus.
- **Hard burden removed if proved:** all central-pole-only scalar packet-growing holomorphic
  regularizations, and more generally every scalar regularization finite at the selected moving
  prime-log zeros of the primewise SC determinant.
- **Remaining burden:** construct a divisor-changing cross-prime/operator landing, or a rigorously
  meromorphic renormalization with the forced condensing pole clocks and show its cancellations do
  not re-encode Xi zeros.

## Log
- 2026-08-28 — created directly in Stage 1 after mandatory corpus search and primary-literature
  comparison; frontier map left read-only.
- 2026-08-28 — full-clock conjecture rejected under central-pole cancellation; pivoted to moving
  noncentral zero.  Dependency-closed paper proof completed and promoted to Stage 2.
- 2026-08-28 — formalized in
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicPrimeLogZeroCondensation.lean` and
  wired into `GaloisForLFunctions.RHTower`.  Source check and exact leaf build passed.  Exact
  realification, zero-condensation survivor, and scalar-factor no-go each audit to only
  `[propext, Classical.choice, Quot.sound]`.  Global lint sees the module as reachable and reports
  only unrelated concurrently unwired modules.  Frontier map remained read-only.
- 2026-08-28 — completed paper proof's full integer-clock clause in
  `formal/GaloisForLFunctions/RHTower/SourceHorizontalHolomorphicPrimeLogFullClock.lean`:
  `preDivisorHolomorphicPrimeBockstein_clock` proves every `kπi/log p` zero,
  `preDivisorHolomorphicPrimeClockPoint_one_terminal` identifies selected zero with `k=1`, and
  `preDivisorRiggedPrimeHolomorphicPacket_clock` transports complete clock to each packet.  Module
  wired into `GaloisForLFunctions.RHTower`; direct check and targeted leaf build passed.  One
  batched audit of these three new theorems returned only
  `[propext, Classical.choice, Quot.sound]`.
