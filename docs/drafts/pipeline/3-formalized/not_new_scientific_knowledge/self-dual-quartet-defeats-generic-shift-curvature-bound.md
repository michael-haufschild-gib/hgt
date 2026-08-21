# A self-dual quartet defeats every generic shifted-curvature bound

- **ID:** `self-dual-quartet-defeats-generic-shift-curvature-bound`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** COUNTEREXAMPLE THEOREM (paper),
  `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `shifted-euler-quotient-twisted-cocycle-flatness.md`;
  `infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** Functional equation, Schwarz symmetry, critical-strip geometry, boundary
  unimodularity, the exact full-shift cocycle, and Toeplitz contractivity do not imply any uniform
  bound on the infinitesimal leakage-curvature corner.  A degree-four self-dual polynomial family
  satisfies all these generic structures while its corner energy is arbitrarily large.

## Counterexample family

Fix

```text
0<a<1/2,       gamma>0,
```

and put `z=s-1/2`.  Define

```text
F_(a,gamma)(s)
 =((z-a)^2+gamma^2)((z+a)^2+gamma^2).                    (1)
```

Its zeros are

```text
1/2+a+i gamma,   1/2+a-i gamma,
1/2-a+i gamma,   1/2-a-i gamma.                         (2)
```

All lie in `0<Re s<1`.

## Theorem A: all generic completed-source symmetries hold

The polynomial `(1)` satisfies

```text
F_(a,gamma)(1-s)=F_(a,gamma)(s),
F_(a,gamma)(conjugate s)=conjugate(F_(a,gamma)(s)).       (3)
```

For real `omega>0`, define

```text
R_omega(s)=F_(a,gamma)(s-omega)/F_(a,gamma)(s+omega).
```

On the critical boundary `Re s=1/2`,

```text
|R_omega(s)|=1                                           (4)
```

away from its finitely many zeros and poles.  It also obeys the exact full-shift cocycle

```text
R_(omega+eta)(s)=R_omega(s-eta)R_eta(s+omega).            (5)
```

Consequently boundary multiplication is unitary and its causal Toeplitz compression is a
contraction for every `omega`.

### Proof

The polynomial in `z` is even and has real coefficients, proving `(3)`.  If `Re s=1/2`, then

```text
s-omega=1-conjugate(s+omega).
```

Use both identities in `(3)` to get

```text
F(s-omega)=conjugate(F(s+omega)),
```

which proves `(4)`.  Equation `(5)` is the telescoping quotient identity.  A unimodular boundary
multiplier is unitary on `L^2`; compression by an orthogonal projection is contractive.

## Theorem B: the curvature corner is unbounded

The right-half divisor consists of the two simple zeros at ordinates `gamma` and `-gamma`, both at
displacement `a`.  Its normalized anti-causal profile is

```text
ell_(a,gamma)(t)
 =2exp(-(a+i gamma)t)+2exp(-(a-i gamma)t)
 =4exp(-at)cos(gamma t).                                (6)
```

Therefore the Toeplitz-curvature corner is

```text
C_(a,gamma)(0,0)
 =integral_0^infinity |ell_(a,gamma)(t)|^2 dt
 =4/a+4a/(a^2+gamma^2).                                 (7)
```

In particular,

```text
C_(a,gamma)(0,0)>8,
lim_(a->0+) C_(a,gamma)(0,0)=infinity.                   (8)
```

### Proof

Equation `(6)` is the universal first-order residue profile with multiplicity one.  Using

```text
cos^2(gamma t)=(1+cos(2gamma t))/2
```

gives

```text
16 integral_0^infinity exp(-2at)cos^2(gamma t)dt
 =8(1/(2a)+(2a)/((2a)^2+(2gamma)^2)),
```

which is `(7)`.  Since `a<1/2`, its first term is greater than `8`, proving `(8)`.

## Route C consequence

No theorem using only the following generic data can prove the required corner bound `<=4`:

1. entire or Cartwright-type finite-order completion;
2. `F(1-s)=F(s)` and Schwarz symmetry;
3. all nontrivial zeros lying in the open critical strip;
4. unimodularity of the centered shifted quotient;
5. the exact full-shift cocycle; or
6. contractivity and positivity of the associated Toeplitz Schur defect.

The family `(1)` satisfies all six and violates the bound by an arbitrarily large amount.  Any live
Route C proof must therefore use a property absent from `(1)`: the exact infinite Euler product,
the explicit gamma/theta completion, and a quantitative law coupling them at the compressed
boundary.  Generic self-dual entire-function or operator theory is fully excluded as the source of
the bound.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The counterexample is an elementary symmetric polynomial quartet,
and the energy is a two-exponential integral.  It is decisive route control but not a new theorem
in entire-function or operator theory.

## Gates

- [x] 0 -> 1: generic compressed-cocycle premise and smallest falsifier isolated.
- [x] 1 -> 2: symmetries, strip geometry, unimodularity, cocycle, contractivity, and unbounded
  curvature proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; a polynomial wrapper would not address the open
  Euler--Gamma boundary estimate.
- [ ] 3 -> 4: no scientific-novelty claim.

## Lean formalization (2026-08-21) — COMPLETE

Both theorems are now unconditional Lean theorems in

`formal/GaloisForLFunctions/RHTower/SelfDualQuartetShiftCurvature.lean`

(namespace `RHTower`; every declaration audited to `propext`, `Classical.choice`, `Quot.sound`).
The energy half is *not* a re-encoded constant: it goes through the corpus off-line Cauchy stack, so
the number `4/a + 4a/(a²+γ²)` is the genuine `∫_{t>0} ‖ℓ_{a,γ}(t)‖² dt`.

**Definitions.**  `selfDualQuartetPoly a γ z = ((z-a)²+γ²)((z+a)²+γ²)`,
`selfDualQuartet a γ s = selfDualQuartetPoly a γ (s - 1/2)` — equation `(1)`;
`selfDualShiftRatio a γ ω s = F(s-ω)/F(s+ω)`.

**Theorem A.**
- `selfDualQuartet_functional_equation` — `F(1-s) = F(s)`, first half of `(3)`.
- `selfDualQuartet_schwarz` — `F(conj s) = conj (F s)`, second half of `(3)`.
- `selfDualQuartetPoly_factor`, `selfDualQuartet_eq_zero_iff` — the exact zero set `(2)`:
  `1/2 ± a ± iγ` and nothing else.
- `selfDualQuartet_zero_mem_strip` — for `0 < a < 1/2` every zero has `0 < Re s < 1`.
- `selfDualQuartet_shift_conj`, `norm_selfDualQuartet_shift`,
  `norm_selfDualShiftRatio_eq_one` — boundary unimodularity `(4)`, via the identity
  `F(s-ω) = conj (F(s+ω))` on `Re s = 1/2`.
- `norm_mul_selfDualShiftRatio` — boundary multiplication is a pointwise isometry, hence unitary on
  `L²` of the critical line, so every compression of it is a contraction.
- `selfDualShiftRatio_cocycle` — the exact full-shift cocycle `(5)`
  (with the one honest side condition `F(s+ω-η) ≠ 0`, which is where the quotient is defined).

**Theorem B.**  Instantiating the corpus off-line divisor data at
`selfDualQuartetOffsets a = (a, a)`, `selfDualQuartetOrdinates γ = (γ, -γ)`,
`selfDualQuartetMultiplicities = (1, 1)`:
- `selfDualQuartetProfile_eq` — the profile is exactly `(6)`:
  `ℓ_{a,γ}(t) = 4 e^{-at} cos(γ t)`.
- `selfDualQuartetCornerEnergy_eq` — `(7)`: the corner equals `4/a + 4a/(a²+γ²)`.
- `integral_norm_sq_selfDualQuartetProfile` — the same number is
  `∫_{t ∈ (0,∞)} ‖ℓ_{a,γ}(t)‖² dt`, through
  `RHTower.integral_norm_sq_finiteOfflineProfile`.
- `selfDualQuartetCornerEnergy_gt_eight` — `(8)` first half: `> 8` whenever `0 < a < 1/2`.
- `tendsto_selfDualQuartetCornerEnergy_atTop` — `(8)` second half: the corner tends to `+∞` as
  `a → 0⁺`, so the six generic data admit no uniform corner bound.

Wired into `GaloisForLFunctions.RHTower`.

## Gates

- [x] 2 -> 3: Theorems A and B formalized unconditionally in Lean (no polynomial re-encoding: the
  energy is the genuine `L²(0,∞)` integral of the residue profile).
