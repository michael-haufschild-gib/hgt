# 105 — No mod-2^k shadow of Landau positivity survives the wall [ROUTE KILLED]

Formal home: `formal/GaloisForLFunctions/RHTower/LandauShadowNoGo.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`).

Answers the open core named in doc 104 §6 / approach doc §4.1 (Arc B2): **does the finite
Landau positivity carry a mod-`2^k` shadow that survives pole subtraction across the wall
`Re s = 1`?** The answer is **no**, and the obstruction is structural, not a matter of effort.
This terminalizes Arc B2 as a dead sub-route; it does not close the program, which never
depended on this sub-route (§4).

## 1. What the shadow would have to be

Landau / Euler positivity is `Λ(n) ≥ 0`: `log ζ = Σ Λ(n)/log n · n^{−s}` and
`−ζ'/ζ = Σ Λ(n) n^{−s}` have nonnegative **real** coefficients (`MertensFirst`,
`vonMangoldt_nonneg`; doc 104 §4). A "mod-`2^k` shadow surviving the wall" would be a
`ℤ/2^k`-valued invariant, derived from that positivity, well-defined into the strip
`1/2 < Re s < 1`, constraining the off-line multiplicities `m(ρ) mod 2^k`.

## 2. The kill: positivity's axis is the real axis, blind to the zeros [PROVED HERE]

A real-coefficient structure is symmetric under complex conjugation `s ↦ s̄`, whose fixed set is
the **real axis**. Its only natural discrete invariant is the mod-`2` count of the zero divisor
across that axis. That invariant is vacuous:

- `conj_equivariant_parity`: for any conjugation-symmetric configuration, the mod-`2` total
  multiplicity equals the multiplicity **on the real axis** (`{im = 0}`). Off-axis points pair
  `ρ ↔ ρ̄` and cancel mod `2`.
- `conj_shadow_trivial_of_offaxis`: a configuration all of whose points are off the real axis has
  **even** total multiplicity — mod-`2` shadow `= 1`.
- `xi_conj_shadow_blind`, `xi_conj_order_sum_even`: applied to ξ (reality pairing `xi_orderAt_conj`
  gives the matched multiplicities), any conjugation-closed set of off-real-axis points has
  `2 ∣ Σ ord_ρ ξ`. Every nontrivial zero has `im ≠ 0`, so the conjugation shadow detects **none**
  of them — on-line or off.

Positivity is symmetric about the real axis, orthogonal to the critical line where the zeros sit;
its shadow cannot see them.

## 3. The contrast that makes it decisive [PROVED HERE]

The **same** off-axis configuration read across the **critical line** `Re s = 1/2` — the fixed
set of the FE involution `s ↦ 1 − s̄` — has mod-`2` shadow equal to its on-critical-line count
(`landau_conj_shadow_vs_fe_line_shadow`): conjugation reading trivial, line reading the nonvacuous
Hardy invariant. The useful axis is the FE's, not positivity's — and the FE line shadow is a
real-function-on-a-curve phenomenon that goes silent off the line (ξ is not real on any natural
off-line curve). Neither constraint alone yields an off-line mod-`2^k` detector:

- **positivity** gives inequalities (zero-free half-planes), never congruences. A single
  positivity `P ≥ 0` forbids a zero; it cannot force an existing zero to have even order — order
  parity is a **sign change**, not an inequality, and sign changes need the real function on the
  critical line (the FE axis).
- **the FE** gives the right axis but only the line reading.

Detecting parity = detecting sign changes = the FE/critical-line side. Landau positivity has no
parity content to reduce; its entire output is the zero-free inequality bounded at the wall.

## 4. Why pole subtraction cannot help — the mantra does the work

"Survives pole subtraction across the wall" asks positivity's reach to cross `Re s = 1`. Every
mechanism that carries positivity past the wall is a **flow**, which this lane refuses:

- analytic continuation of the positive representation across `Re s = 1` — a flow (propagating the
  function across a boundary); pole subtraction destroys the sign-definiteness that was the whole
  content (`−ζ'/ζ + 1/(s−1)` is no longer a nonnegative-coefficient series).
- the de la Vallée Poussin zero-free region `σ > 1 − c/log|t|` — obtained from a `|t| → ∞`
  asymptotic of the log-derivative bound; a height flow ([[height-is-flow-not-constraint]]), and
  a zero-**free** region carries no parity anyway.
- the Bohr / Kronecker `T^∞` lift with its a.s.-nonvanishing random Euler product on `σ > 1/2` —
  the vertical translation flow in disguise (approach doc §4.3), refused wholesale.

At a **pinned** configuration (no flow), positivity reaches exactly `Re s ≥ 1`
(`xi_ne_zero_of_one_le_re`, the classical wall) and its shadow there is the conjugation one of §2
— trivial. The crossing IS the flow; remove the flow and there is nothing to reduce mod `2^k`.

For `k ≥ 2` nothing improves: conjugation pairing makes the count `2·(Σ over pair
representatives)`, an even multiple carrying only the **aggregate**; `RH_{2^k}` is a **per-zero**
divisibility, and no count-based invariant (conjugation or line) isolates a single zero — that is
the Gate-4 aggregate-vs-localized wall (doc 121) restated on the positivity side.

## 5. What this opens

Arc B2 (mod-`2^k` shadow of Landau positivity) is dead: positivity and the FE are **separately**
blind to off-line multiplicity parity, and their shadows meet only through a flow. This does not
touch the program's actual mechanism, which was never single-constraint positivity but the q62
transposition — an off-line zero killed by a **weight mismatch** under a group action of
**unbounded order**, not by any positivity inequality (approach doc §2.2, §2.4). The two
constraints being separately blind is precisely why the weld — where `∂_s` (FE axis) and `{σ_p}`
(real axis) *interact* — is the native frontier: the detector must be **joint**, reading the
divisor across one axis while the positivity constrains the other, in a single carrier (the
`q62_mixed` shape). The next object to construct is that joint reading at one pinned annulus: the
positivity of the `{σ_p}` side (doc 104, real ≥ 1 on the real axis) coupled to the FE-axis divisor
parity (docs 122–124) on the same configuration — two axes, one constraint, no flow between them.
