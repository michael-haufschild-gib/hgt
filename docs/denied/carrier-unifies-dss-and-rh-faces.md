# The carrier `m_ξ` as the single object whose two coordinate systems are DSS and RH

**Theorist, 2026-06-19.** Status: SEARCH note with ledgered finite anchors. No proof of RH or apex
DSS is claimed. The **finite** anchors (Bricks 0 and 1) are `[LEDGER-PROVEN]`; everything infinite is
`[CONJECTURE]`/`[OPEN CORE]`. Companion: `dss-multiplicity-estimate-spectral-genericity.md`,
`period-comparison-primes-zeros-the-planet.md`, `formalization-roadmap-finite-to-apex.md`.

## 0. The two faces are two coordinate systems on one analytic germ

The field's Object-X is the **secular-moment sequence** `P_k = Σ_ρ ρ_z^{-k}`, power sums over the
zeros of `Ξ(z) = ξ(½+iz)`. The standing slogan is "two faces of one point": the **RH face** (Li
positivity / Herglotz) and the **DSS face** (algebraic genericity). This note pins what the "one
point" *is*: the carrier germ, and makes the slogan a precise statement.

**Observation (the germ).** The carrier `m_ξ(z) = −Ξ'/Ξ(z) = Σ_ρ 1/(ρ_z − z)` has Taylor expansion at
`z = 0`
```
   m_ξ(z) = Σ_{k≥0} P_{k+1} z^k ,      P_m = Σ_ρ ρ_z^{-m},
```
because `1/(ρ−z) = Σ_k z^k/ρ^{k+1}`. So **`{P_k}` are literally the Taylor coefficients of the
carrier at 0**, and `m_ξ` is the single analytic germ carrying both faces:

| Face | Coordinate on the germ `m_ξ` | Statement | This-session status |
|---|---|---|---|
| **RH** | global analytic type | `m_ξ` Herglotz ⟺ `κ₋ = 0` ⟺ no `ℂ⁺`-poles ⟺ RH | finite version PROVEN (§Brick 0) |
| **DSS** | jet at `0` (Taylor coefficients) | `{P_k}` algebraically independent over `ℚ` | OPEN (famous) |

RH reads the germ's **monodromy/positivity type**; DSS reads its **infinite jet at a point**. They
are independent readings of the *same* function — which is exactly why neither implies the other and
why the field needs both wings.

## 1. Brick 0 (the finite RH face) — `[LEDGER-PROVEN, this session]`

For a finite carrier with `k` off-line conjugate pairs `m(z) = Σ_{i<k}[1/(t_i−z)+1/(t̄_i−z)]`
(`Im t_i > 0`), the Pick form has **negative inertia exactly `k`**
(`GaloisForLFunctions.multiPair_carrier_exact_neg_inertia`, axiom-clean, unconditional). The proof is
the explicit Krein–Langer factorization `2·Pick = Σ(e_i+a_i)(e_i+a_i)* − Σ(e_i−a_i)(e_i−a_i)*` plus
Cauchy non-degeneracy of the `2k` pole-vectors. So at finite level the **RH face is fully understood
and quantitative**: each off-line zero contributes exactly one negative square; `κ₋ = #off-line zeros`.

The slogan "RH ⟺ κ₋ = 0" is the `k = 0` case in the limit — see Brick 2.

## 2. Brick 1 (the finite DSS face) — `[LEDGER-PROVEN, finite]`

The DSS face at finite level: for a finite spectrum `{ρ_1,…,ρ_n}`, the moments `P_1,…,P_n` and the
elementary symmetric functions `e_1,…,e_n` are related by **Newton's identities**, a polynomial change
of coordinates over `ℚ` that is a *bijection* (triangular, leading coefficient `±1`). Hence
```
   trdeg_ℚ ℚ(P_1,…,P_n) = trdeg_ℚ ℚ(e_1,…,e_n) = trdeg_ℚ ℚ(ρ_1,…,ρ_n).
```
`[LEDGER-PROVEN, finite]` The elementary-symmetric coordinate form is formalized as
`GaloisForLFunctions.spectrum_esymm_algIndep`: the `e_1,…,e_n` coordinates of `n` indeterminate
spectral points are algebraically independent over `ℚ`. The moment-to-`e` map
(`MomentReconstruction.secular_moment_newton` gives the recursion) is the finite Newton bridge from
power sums to symmetric coordinates; this is the finite shadow of the apex DSS, while the infinite
moment/jet statement remains open. **This closes the clean finite DSS brick alongside Brick 0**, making
both finite readings of the carrier germ ledgered.

## 3. Brick 2 (the infinite passage) — `[OPEN CORE, decades — staged]`

The two finite faces (Bricks 0, 1) are joined to the apex by the **same** `k → ∞` regularization:
- **RH face:** `κ₋(m_ξ) = lim_k #{off-line zeros in window} = 0 ⟺ RH`. The finite `κ₋ = k`
  (Brick 0) is exact; the infinite carrier `m_ξ` requires the completed-`ξ` Hadamard product (a
  not-finite, regularized sum), the Krein–Langer `N_κ` class for the limit, and the Nevanlinna/Pick
  characterization at infinite nodes (mathlib gap). `[infra]`
- **DSS face:** the infinite jet `{P_k}` — the Taylor coefficients of the *same* `m_ξ` — algebraically
  independent. Via the proven formula `P_k = 1 − (−1)ᵏζ(k)/2ᵏ − a_{k−1}` with `a_j` the
  Stieltjes-constant closed forms (this project's discovery), DSS reduces to the joint algebraic
  independence of `{π} ∪ {ζ(odd)} ∪ {Stieltjes γₙ}` — open mathematics (Apéry–Rivoal–Zudilin +
  Stieltjes transcendence). `[OPEN]`

**The unification's payoff (conjectural).** Because both faces live on one germ, a *single*
rigidity statement would feed both: any quantitative bound forcing the carrier germ to be
"transcendentally generic at 0" (DSS) is, by analytic continuation of the same germ, a constraint on
its global pole structure (RH). The field's bet (`[CONJECTURE]`): the **multiplicity estimate** on
`G_L` (the `MultiplicityEstimate` determinant criterion, already ledgered) is the common ingredient —
ingredient (2) of a Nesterenko algebraic-independence argument on the jet **and** the rank input to
the inertia count on the type. Brick 0 shows the inertia side is now exact and unconditional; the
remaining content is the Nesterenko arithmetic lower bound (the missing Liouville substitute), which
is the same explicit-formula rigidity in both readings.

## 4. A falsifiable finite test — `[NUMERIC, runnable]`

The unification predicts: for a finite spectrum, the moment-Jacobian (Newton) is unimodular, so
moments and spectrum have equal `ℚ`-transcendence degree — testable by checking the Newton change-of-
basis determinant is `±1` for random `n` (trivially true by triangularity, a sanity anchor), and, more
interestingly, that **no spurious low-height `ℚ`-relation** appears among `{P_2,…,P_8}` of the *actual*
`ξ`-zeros beyond those forced by the `ζ`-value/Stieltjes formula — already checked (PSLQ, dps=220,
height `1e12`, `computations/dss_secular_moments_pslq/`): none. The finite RH face (Brick 0) is exact;
the elementary-symmetric finite DSS face (Brick 1) is ledgered; the infinite passage (Brick 2) is the
staged apex.

**House status.** Brick 0 `[LEDGER-PROVEN]` (the exact finite inertia, this session). Brick 1
`[LEDGER-PROVEN]` (finite elementary-symmetric algebraic genericity). Brick 2 `[OPEN CORE]` (infinite
`m_ξ` = infra; DSS = open mathematics). The open core is unchanged in difficulty — but it is now
precisely *one germ, two readings*, with both finite layers closed.

---

## UPDATE (2026-06-19) — Brick 1 is now `[LEDGER-PROVEN]`

The finite DSS face is no longer conjectural: `GaloisForLFunctions.spectrum_esymm_algIndep` (axiom-clean)
proves the elementary symmetric coordinates `e_1,…,e_n` of `n` indeterminate spectral points are
algebraically independent over `ℚ` (full transcendence degree `n`), via mathlib's fundamental theorem
of symmetric polynomials (`esymmAlgHom_injective`). By Newton's identities (char 0) this is equivalent
to algebraic independence of the finite power-sum moments `P_1,…,P_n`.

**Both finite faces of the carrier germ are now ledgered, axiom-clean:**
- Brick 0 (finite RH face): `multiPair_carrier_exact_neg_inertia` — `κ₋ = #off-line zeros`, exact, unconditional.
- Brick 1 (finite DSS face): `spectrum_esymm_algIndep` — symmetric coordinates algebraically independent.

So the unification is anchored on *both* sides at the finite level: one carrier germ, two readings, each
read's finite layer now a theorem. The open core (Brick 2) is the single infinite passage — `m_ξ` (infra)
for RH, and the infinite jet `{P_k}` = `{π,ζodd,Stieltjes}` independence (open) for DSS.
