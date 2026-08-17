# Three barriers to certifying an off-line Beurling zero with regular integers

- **ID:** `BEURLING-ZERO-CERTIFICATION-BARRIERS-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / NO-GO CLUSTER
- **Parent:** `../1-in-progress/thin-random-deletion-beurling-alpha-beta.md` §9
- **RH used:** no · **Computation used:** no
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN CERTIFIED] [NOT RH]`

## Question answered

Can a *self-similar / Cantor-type* discrete multiplicative system certify `α > 1/2` while keeping
`β < 1/2`?  It was the last regime not covered by the placement-variance wall or the
ℤ-perturbation wall.

**Answer: no**, for two independent elementary reasons, and the second reason generalises into a
barrier that covers *every* perturbative construction over *any* base.

## 1. Lattice barrier — self-similar systems have no power saving at all

**Theorem.**  Let all generalized integers of a system be powers of a fixed `q > 1` (equivalently:
all log-primes lie in `(log q)ℤ`).  Then for every density `a > 0` and every `n`, some
`x ∈ [q^n, q^{n+1})` satisfies

```
|N(x) − a x|  ≥  (a(q−1)/(4q))·x.
```

Hence `N(x) − ax ≠ o(x)`: **β = 1**.  No power saving is available at any exponent.

*Proof.*  `N` is constant on `[q^n, q^{n+1})` — there are no generalized integers strictly between
consecutive lattice points — while `a x` increases by `a q^n (q−1)` across it.  Probing at
`x₁ = q^n` and the midpoint `x₂` gives `a(x₂−x₁) ≤ |N(x₁)−ax₁| + |N(x₂)−ax₂|`, so one probe carries
at least half; converting `q^n ≥ x/q` gives the stated proportion. ∎

Lean: `lattice_no_power_saving`.

**Why this settles the self-similar route.**  A multiplicative self-similarity is exactly a lattice
of log-primes, and lattices are excluded above.  The two escapes both fail as well:
*finitely generated* systems (log-primes in `ℤ log q₁ + … + ℤ log q_k`) have
`N(x) ≍ (log x)^k / (k! ∏ log q_i)`, not linear density; and genuinely *fractal* log-prime sets have
`π_P` of sub-exponential growth in the logarithmic variable, again incompatible with `N(x) ∼ a x`.
Self-similarity and linear density are mutually exclusive.

## 2. Modification barrier — a modification cannot create a zero

**Theorem.**  Let `(q_i)` be generalized primes with `q_i > 1` and `∑ q_i^{-σ} < ∞`, `σ > 0`.  Then
for every `s` with `Re s ≥ σ`,

```
∏_i (1 − q_i^{-s})  ≠  0.
```

*Proof.*  `‖q_i^{-s}‖ = q_i^{-Re s} ≤ q_i^{-σ}`, so the family is absolutely summable and
`∑ log(1 − q_i^{-s})` converges; the product is therefore `exp` of that sum, hence nonzero.  Each
factor is nonzero separately because `q_i^{-Re s} < 1` for `Re s > 0`. ∎

Lean: `tprod_one_sub_ne_zero`, `modification_factor_ne_zero`.

**Consequence.**  Inserting, deleting or rescaling a family of generalized primes of reciprocal
abscissa `γ` multiplies the zeta function by `Φ^{±1}` with `Φ` analytic and **zero-free** on
`Re s > max(γ,0)`.  Therefore

> **the modified system and its base have exactly the same zeros in `Re s > max(γ, 0)`.**

Combined with the barrier of the parent card (`β ≥ γ` for such a modification): if the modified
system has `β < 1/2` then `γ ≤ β < 1/2`, so **every zero with `Re s > 1/2` is inherited from the
base**.  An off-line zero is never manufactured; it is only ever passed along.

## 3. The resulting picture

| route | wall |
|---|---|
| random placement from scratch | `β ≥ 1/2` (variance abscissa `1/2`) |
| perturbation of any base | `β ≥ γ`, and *no new zeros* in `Re s > γ` (§2) |
| self-similar / lattice | `β = 1`; fractal or finitely generated ⟹ no linear density (§1) |

The only certified-`β<1/2` bases available are `ℤ` (`β = 0`) and number-field ideal systems
(`β = 1 − 2/(d+1)`, Landau; `β = 1/3` for quadratic fields).  Their off-line zeros are exactly the
failure of RH, resp. ERH.  So every perturbative route to an unconditional `[α,β]`-system with
`β < 1/2` and `α > 1/2` is equivalent to disproving RH or ERH, and the two non-perturbative routes
are barred outright.

## 4. Status of the surviving conjecture

**[CONJECTURE — unconditional square-root uncertainty]**  Every `[α,β]`-system with `α > 1/2`
satisfies `β ≥ 1/2`; equivalently `β < 1/2 ⟹ α = 1/2`.

Strictly stronger than Hilberdink's `max{α,β} ≥ 1/2`.  **Verdict this cycle: `SURVIVES PRELIMINARY
ATTACK`** — the falsifying side has now been attacked in all three regimes and each is barred.  The
conjecture remains RH-hard in the proving direction (applied to `ℤ`, where `β = 0`, it yields RH),
so only construction is attackable, and no unbarred construction regime is currently known.

**What would falsify it.**  A from-scratch discrete system, not a lattice and not a
bounded-discrepancy discretisation of a continuous model, whose zeta zero at `Re s > 1/2` is
certified by a mechanism other than an exact Laplace-transform evaluation.  No such mechanism is
known; identifying one is the reframed open problem.

## 5. Lean

| result | theorem | module |
|---|---|---|
| lattice systems admit no power saving | `lattice_no_power_saving` | `RHTower/BeurlingLatticeAndModificationBarriers` |
| absolutely convergent `∏(1−z_i)` is nonzero | `tprod_one_sub_ne_zero` | same |
| **a modification cannot create a zero** | `modification_factor_ne_zero` | same |

Built, wired into `GaloisForLFunctions.RHTower`, axioms `[propext, Classical.choice, Quot.sound]`.

## 6. Novelty (bounded audit)

Both statements are elementary and any specialist would accept them on sight; the contribution is
their role as a *classification of the construction space*, and in particular the observation that a
modification is zero-free — which converts "build an off-line zero" into "inherit one", and thereby
explains why every unconditional `β < 1/2` construction in the literature (Broucke–Debruyne–Révész,
`arXiv:2309.01567`) is stated under RH.  The lattice statement is folklore in the Beurling
community; it is recorded here because it is what excludes the self-similar regime.
