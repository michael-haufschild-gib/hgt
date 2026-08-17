# Thin random deletion from ℤ: unconditional [α,β]-systems with β < 1/2

- **ID:** `THIN-DELETION-ALPHA-BETA-001`
- **Stage:** 1-in-progress
- **Type:** CONSTRUCTION PROGRAMME with one `[OPEN CORE]`
- **Parent:** `../3-formalized/regular-beurling-integers-do-not-constrain-the-zeros.md` §6
- **RH used:** no (a case split *on* RH is used, which is not the same thing)
- **Status:** `[PRIOR ART VERIFIED] [STRATEGY NEW] [OPEN CORE OPEN]`

## 0. Prior-art finding — the previous target was rediscovery

The card's earlier conjecture asked for a *discrete* Beurling system with regular integers and an
off-line zeta zero.  Verified against the source (Broucke–Debruyne–Révész, *Some examples of
well-behaved Beurling number systems*, `arXiv:2309.01567v2`, 26 Jun 2024 — full text read):

* Their systems **are discrete**: `P = (p_j)`, `1 < p₁ ≤ p₂ ≤ …`, `p_j → ∞`.
* An **[α,β]-system** (Hilberdink) is one with `ψ_P(x) = x + O_ε(x^{α+ε})` and
  `N_P(x) = ax + O_ε(x^{β+ε})` for every `ε > 0` **and for no `ε < 0`** — so `α`, `β` are the
  *optimal* exponents, `α = limsup log|ψ_P(x)−x|/log x`, `β = limsup log|N_P(x)−ax|/log x`.
* **Hilberdink's uncertainty principle:** every `[α,β]`-system has `max{α,β} ≥ 1/2`.
* **Their Theorem 1.1:** for every `α ∈ [0,1)` and `β ∈ [1/2,1)` an `[α,β]`-system exists.
* Assuming RH they also build families with `β < 1/2`; **unconditionally `β < 1/2` is open.**

Taking `α ∈ (1/2,1)`, `β = 1/2` in their Theorem 1.1 already gives a discrete system with
RH-quality integer regularity `N(x) = ax + O(x^{1/2+ε})` whose primes are *not* RH-quality.  So the
firewall at the square-root scale is **already published**, and the earlier conjecture at `β = 1/2`
is `REDISCOVERED`.  Recorded, not repackaged.

The live problem is exactly the one BDR leave open:

> **Construct, unconditionally, an `[α,β]`-system with `β < 1/2`** (necessarily `α ≥ 1/2` by
> Hilberdink).  For the firewall we want the strict form `α > 1/2`.

## 1. Why the known method stops at `1/2`

Every unconditional construction in this literature (Diamond–Montgomery–Vorhauer; Zhang;
Broucke–Vindas; BDR) *places* generalized primes at random real points approximating a continuous
prime measure.  The integer count then inherits a square-root error from a randomisation carried out
over a set of size `≍ x` (the integers below `x`), which pins `β ≥ 1/2`.  Precisely: if
`π_P = π_c + R` with `R` the placement discrepancy, then `log(ζ_P/ζ_c)(s) = ∫x^{-s}dR(x)`, whose
variance is `∫x^{-2σ}dπ_c(x)` — convergent exactly for `σ > 1/2`.  **The `1/2` is the abscissa of the
variance, not an artefact of the estimates.**

## 2. The new idea: randomise a *thin deletion from ℤ*, not a placement

Do not place new primes.  **Delete** a thin random subset of the rational primes and keep ℤ's own
rigidity (`N_ℤ(x) = ⌊x⌋`, error `O(1)`) as the scaffold.

Fix `ρ₀ ∈ (1/2, 1)`.  Let `B` be a random set of rational primes, `p ∈ B` independently with
probability `q_p ≍ p^{ρ₀−1}`, and put `P := {p prime : p ∉ B}`.  Write `𝒟` for the set of squarefree
products of elements of `B`, and `D(x) = #{d ∈ 𝒟 : d ≤ x}`.

Then a.s. `π_B(x) ≍ x^{ρ₀}/log x`, hence `∑_{p∈B} 1/p < ∞`, and:

**(a) `ζ_P(s) = ζ(s)·∏_{p∈B}(1 − p^{-s})`,** so `log ζ_P − log ζ` is a Dirichlet series with
one-signed coefficients and abscissa `ρ₀`; by Landau `s = ρ₀` is a singularity and the product tends
to `0` as `s ↓ ρ₀`.  The system's zeta is not analytic-and-zero-free past `1/2`.

**(b) `α > 1/2`, unconditionally, by a case split on RH.**
`ψ_P(x) = ψ(x) − θ_B(x)` with `θ_B(x) ≍ x^{ρ₀}` deterministic and one-signed.
*If RH holds*, `ψ(x) − x = O(x^{1/2+ε})`, so `ψ_P(x) − x ≍ −x^{ρ₀}` and `α = ρ₀ > 1/2`.
*If RH fails*, `ζ` has a zero with `Re ρ = Θ > 1/2` and `ψ(x) − x = Ω(x^{Θ−ε})`; the two terms have
different growth exponents unless `Θ = ρ₀`, and choosing `ρ₀` outside the (at most one-point)
coincidence gives `α ≥ max(ρ₀, Θ) > 1/2`.
Either way `α > 1/2` **without knowing which case holds** — the construction never needs RH, only the
dichotomy.

**(c) `N_P` is a sieve count, and the randomisation set is thin.**
`N_P(x) = #{n ≤ x : p | n ⟹ p ∉ B} = ∑_{d ∈ 𝒟, d ≤ x} μ(d)⌊x/d⌋`, so **exactly**

```
N_P(x) = c_B·x  −  x·∑_{d ∈ 𝒟, d > x} μ(d)/d  −  ∑_{d ∈ 𝒟, d ≤ x} μ(d){x/d},
c_B = ∏_{p∈B}(1 − 1/p) > 0.
```

The trivial bound on either error term is `D(x) ≍ x^{ρ₀+o(1)}`, giving `β = ρ₀ > 1/2` — no gain.
But both terms are **signed sums over the thin set `𝒟`, of size `x^{ρ₀}`, not over all `x` integers**.
Square-root cancellation over `𝒟` therefore yields `x^{ρ₀/2+ε}`, and

```
ρ₀ ∈ (1/2, 1)  ⟹  ρ₀/2 ∈ (1/4, 1/2)  <  1/2.
```

**This is the whole point: moving the randomisation from a set of size `x` to a set of size `x^{ρ₀}`
moves the square-root barrier from `x^{1/2}` to `x^{ρ₀/2}`, which is below `1/2` for every admissible
`ρ₀`.**  ℤ supplies the rest of the integer regularity for free.

## 3. `[OPEN CORE]`

Prove, almost surely and uniformly in `x`, the two square-root bounds

```
(i)   ∑_{d ∈ 𝒟, d ≤ x} μ(d){x/d}  =  O_ε( x^{ρ₀/2 + ε} ),
(ii)  x · ∑_{d ∈ 𝒟, d > x} μ(d)/d =  O_ε( x^{ρ₀/2 + ε} ).
```

Both are second-moment computations over the independent inclusions `1_{p ∈ B}`, with
`P(d ∈ 𝒟) = ∏_{p|d} q_p`; the diagonal contributes `∑_d P(d∈𝒟)/d²`-type quantities of the right
size, and the off-diagonal must be shown to cancel.  The union bound over `x` is the standard
DMV/BDV chaining step (`x` ranges over a `1 + x^{-1}`-net, `N_P` monotone).

Optimality of these two bounds would give `β = ρ₀/2` and hence, with (b), an **unconditional
`[α, ρ₀/2]`-system with `α ≥ ρ₀ > 1/2 > ρ₀/2 = β`** — BDR's open problem, solved.

## 4. What each outcome teaches

* **`[OPEN CORE]` provable** ⟹ unconditional `[α,β]`-systems with `β < 1/2` exist; combined with the
  two firewall cards, **no regularity of the generalized-integer counting function — continuous or
  discrete, at any power scale — implies RH**.  The firewall is then complete and final, and the
  arithmetic input of any RH proof is isolated to the exact identity `N(x) = ⌊x⌋`.
* **`[OPEN CORE]` false**, i.e. the cancellation provably fails for every admissible `B` ⟹ a **new
  uncertainty principle strictly stronger than Hilberdink's** in this regime: deleting enough primes
  to spoil `α` costs `β ≥ 1/2` regardless.  That would make discreteness the load-bearing arithmetic
  hypothesis and would be the more interesting outcome.

Both outcomes are firewall results; neither proves or disproves RH.  Note the asymmetry that makes
this safe: the *negative* form ("`β < 1/2` forces no off-line zeros") applied to ℤ, where `β = 0`,
would prove RH — so only the *construction* direction is attackable, and that is the direction taken.

## 5. Formalisation targets (deterministic parts, independent of the open core)

1. The exact sieve identity of §2(c) — pure combinatorics, no probability.
2. `ζ_P(s) = ζ(s)∏_{p∈B}(1−p^{-s})` for a set `B` with `∑_{p∈B}1/p < ∞`.
3. `c_B = ∏_{p∈B}(1−1/p) > 0` under `∑_{p∈B}1/p < ∞`.
4. The RH case-split of §2(b) as a clean disjunction: `α > 1/2` follows from
   `(RH ∨ ¬RH)` with no other input.

## 6. Log

- Prior art verified by reading `arXiv:2309.01567v2` in full: the `β = 1/2` firewall is theirs.
- Strategy shift recorded: randomise *deletions from ℤ*, not *placements of reals*.  The gain is the
  exponent `ρ₀/2` in place of `1/2`, because the second moment is taken over `𝒟` (size `x^{ρ₀}`)
  rather than over the integers (size `x`).

---

# VERDICT ON THE OPEN CORE: `FALSE` — and the failure is a theorem

The cancellation asked for in §3 is irrelevant: the construction fails for an elementary reason that
no amount of cancellation repairs, and the reason generalises into a no-go for the whole class.

## 7. What kills it

`N_P(x)` counts `B`-free integers `≤ x`, so it is blind to every deleted prime `p > x`.  The density
constant `c_B = ∏_{p∈B}(1−1/p)` is not.  Hence, with `c_{B∩[1,x]} = c_B·∏_{p∈B,p>x}(1−1/p)^{-1}`,

```
N_P(x) − c_B x  =  c_B·x·∑_{p ∈ B, p > x} 1/p  +  E(x),
```

and with `π_B(t) ≍ t^γ` the first term is `≍ x^{γ}` — smooth, positive, of the same order as the
trivial bound on `E(x)`.  No choice of density constant absorbs it: `N_P(x) − ax = o(x)` forces
`a = c_B`.  So `β = γ`, not `γ/2`.  **The randomisation never enters.**

## 8. The barrier theorem (proved, and it explains the literature)

Let `B` be a set of rational primes with `π_B(t) ≍ t^γ`, `0 < γ < 1`, and `P` the rational primes
with `B` deleted.  Then `ζ_P(s) = ζ(s)Φ(s)`, `Φ(s) = ∏_{p∈B}(1−p^{-s})`, and:

1. `Φ` is analytic and non-vanishing on `Re s > γ`, so `ζ_P = ζΦ` there by continuation from
   `Re s > 1`.
2. `−log Φ(σ) ≥ g(σ) := ∑_{p∈B}p^{-σ}`, and partial summation with `π_B(t) ≍ t^γ` gives
   `g(σ) ≍ 1/(σ−γ)` as `σ ↓ γ`.  Hence `0 < Φ(σ) ≤ exp(−c/(σ−γ))`.
3. Suppose `N_P(x) = ax + O(x^{β+ε})` with `β < γ`.  Then `ζ_P(s) = s∫N_P(x)x^{-s-1}dx` is analytic
   on `Re s > β` apart from the simple pole at `1`, hence analytic at the real point `γ`.  Since
   `ζ(γ) ≠ 0` for `γ ∈ (0,1)` (`ζ < 0` there), `ζ_P` vanishes at `γ` to some finite order `m`,
   forcing `Φ(σ) ≥ K(σ−γ)^m` near `γ`.
4. Steps 2 and 3 are incompatible: no positive function is both `≤ exp(−c/t)` and `≥ K t^m`.
   **Formalized:** `no_finite_order_zero_absorbs_exponential_deficit`.

Hence **β ≥ γ**.  The same argument with the sign of `log Φ` reversed covers *insertions* of
generalized primes and *scalings* `p ↦ μp` of a set of counting exponent `γ`: in every case the
modification series has one-signed coefficients with abscissa `γ`, and `Φ` acquires an essential
singularity at the real point `γ`.

**Corollary (the dichotomy).**  `ψ_P(x) − x = (ψ(x) − x) ∓ θ_Δ(x)` with `θ_Δ(x) ≍ x^{γ}`.  If
`β < 1/2` then `γ ≤ β < 1/2`, so under RH `ψ_P(x) − x = O(x^{1/2+ε})`, giving `α ≤ 1/2`, and
Hilberdink forces `α = 1/2` exactly.  Contrapositive:

> **A ℤ-perturbation system with `β < 1/2` and `α > 1/2` exists if and only if RH is false.**

The entire perturbation route is therefore *conditionally circular*.  This is why
Broucke–Debruyne–Révész's `β < 1/2` families are stated under RH: the conditionality is forced, not
an artefact of their method.

## 9. Relentless interrogation — what survives

The barrier bites only on systems built *from* ℤ, or from any system already known zero-free past
`1/2`.  Two independent walls now stand at `1/2`:

| route | wall | mechanism |
|---|---|---|
| from-scratch random placement | `β ≥ 1/2` | variance `∫x^{-2σ}dπ_c` has abscissa `1/2` |
| ℤ-perturbation | `α > 1/2 ⟺ ¬RH` | essential singularity of `Φ` at the real point `γ` |

Neither wall is Hilberdink's.  Note too that quadratic-field ideals give `β = 1/3` unconditionally
(Landau), so `β < 1/2` alone is *not* the difficulty — **certifying `α > 1/2` is**, and every known
certification route runs through one of the two walls.

**[REFRAMED OPEN PROBLEM]** Exhibit a discrete multiplicative system, built from scratch and not by
perturbing a known-zero-free system, whose integers are better-than-square-root regular and whose
zeta *provably* has a zero with `Re s > 1/2`.

**[CONJECTURE — unconditional square-root uncertainty]** Every `[α,β]`-system with `α > 1/2`
satisfies `β ≥ 1/2`; equivalently `β < 1/2 ⟹ α = 1/2`.  Strictly stronger than Hilberdink,
consistent with both walls, and **RH-hard**: applied to `ℤ` (`β = 0`) it yields RH.  Only the
construction direction is attackable, and §8 shows the two natural constructions are barred.

## 10. Lean

| result | theorem | module |
|---|---|---|
| exponential deficit beats every power near `0` | `exp_neg_div_lt_pow` | `RHTower/ThinDeletionEssentialSingularity` |
| **no finite-order zero absorbs an exponential deficit** | `no_finite_order_zero_absorbs_exponential_deficit` | same |
| one-prime split of the deletion sieve | `freeCount_insert` | `RHTower/ThinDeletionSieveIdentity` |
| the deletion sieve identity | `freeCount_eq_sum` | same |

All build, wired into `GaloisForLFunctions.RHTower`, axioms `[propext, Classical.choice, Quot.sound]`.
