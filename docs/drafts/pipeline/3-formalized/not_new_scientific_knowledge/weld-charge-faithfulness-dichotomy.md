# Which weld charges see the prime lattice — a target-torsion dichotomy gated by the transcendence of e

- **ID:** weld-charge-faithfulness-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Settles question C2/Q2-E: *does the deck charge preserve or collapse the prime-lattice independence of the weld classes?*
- **Statement:** Reading the rank-`∞`, `ℤ`-independent prime weld lattice `{[weld_{log p}]}` through a charge `H²(WeldGroup; ℝ) →+ M` is governed **entirely by the target `M`**, along a sharp trichotomy: (i) into any **bounded-exponent (finite)** target the whole lattice **collapses to `0`** — a divisible source has no nonzero bounded-exponent character; (ii) into the **torsion-free** `H²(·; ℝ)` faithfulness is total (unique factorization only); (iii) into the **compact, divisible, torsion** circle `ℝ/ℤ` faithfulness **returns**, but now requires a genuinely new input — the **transcendence of `e`**. The dividing line is *bounded exponent*, not torsion.

## Goal
Locates exactly what a torsion-valued weld charge can and cannot read off the prime lattice, and pins the arithmetic content of each regime. The flux grading (real conversion constant `θ = log base`, domain of `weldClassHom : ℝ ↪ H²`) is a *divisible, flow-like* datum; a deck charge `wCharge n : ℤ → ℤ/n` is a *torsion, constraint-like* datum. The theorem is that a discrete constraint of bounded exponent cannot see a divisible flow — "constraint, not flow" at the level of coefficient rings — and that the obstruction dissolves once the target is allowed *unbounded exponent* (bounded exponent is sufficient for guaranteed collapse; the circle `ℝ/ℤ`, itself divisible and torsion but of unbounded exponent, already recovers faithfulness — so torsion is not what causes the collapse), at which point the *arithmetic of the weld meets the transcendence of e*. No carrier is constructed anywhere; every result forces a homomorphism to be zero (rigidity) or proves an independence.

## What is proved

**A. The finite-target collapse** (`formal/GaloisForLFunctions/RHTower/WeldChargeFaithfulness.lean`).
- `real_addHom_eq_zero_of_nsmul` — a divisible source has no nonzero bounded-exponent character: if `n • y = 0` for all `y ∈ M` (`n ≠ 0`), every `φ : ℝ →+ M` is identically zero (`x = n·(x/n)`, `φ x = n • φ(x/n) = 0`).
- `real_addHom_zmod_eq_zero`, `weldClass_charge_invisible`, `prime_flux_charge_collapse` — every `ZMod n`-valued charge annihilates every weld class, collapsing the whole finitely-supported prime lattice to the single point `0`.
- `weldClass_finite_charge_invisible` — the same for **every** finite abelian target (bounded exponent `Fintype.card M • y = 0`), not merely `ZMod n`. This is *not* the modular-quotient barrier of `DeciderBarrier`; it is a coefficient-ring phenomenon (divisible source, torsion target).

**B. The torsion-free faithful contrast** (same file).
- `primeFluxHom : (Nat.Primes →₀ ℤ) →+ H²(WeldGroup; ℝ)`, `primeFluxHom_injective` — into the torsion-free target the identical prime lattice is fully faithful, repackaging `primes_weld_class_indep`. The independence is entirely present, only invisible to bounded-exponent charges.

**C. The order channel is faithful** (same file).
- `eq_zero_of_forall_two_pow_dvd` (Archimedean: an integer divisible by every `2^k` is `0`), `wCharge_two_pow_profile_injective` — the `2`-adic deck-charge profile `idx ↦ (wCharge(2^k) idx)_k` is injective, the profinite embedding `ℤ ↪ ℤ₂`. So the collapse is confined to the transcendental flux channel; the integer order grading loses nothing.

**D. The transcendence input, built from scratch** (`formal/GaloisForLFunctions/RHTower/ExpNatIrrational.lean`).
Mathlib proves `π` irrational but has **no** irrationality of `e^n`; this is built here by the Hermite integral method.
- `hermiteP`, `hermiteTerm`, `hermiteF` — the base polynomial `f = Xᵐ(A-X)ᵐ ∈ ℤ[X]` and its signed antiderivative `F = Σ_{j≤2m}(-1)ʲDʲf`; `hermiteF_add_derivative` proves the telescoping identity `F + F' = f` (via `D·termⱼ = -termⱼ₊₁`, the top term dying past degree `2m`).
- `factorial_dvd_hermiteF_eval_zero`, `factorial_dvd_hermiteF_eval_A` — `m! ∣ F(0)` and `m! ∣ F(A)` (below degree `m` the coefficient vanishes; at or above, `j!` already contains `m!`), the integrality of the endpoint values; the `A`-endpoint via the reflection `f(A-X)=f(X)` (`taylor_hermiteP_coeff_eq_zero`).
- `hasDerivAt_hermite` (`d/dx(eˣF) = eˣf`), `hermiteBigI_eq` (FTC), `hermiteBigI_pos`, `hermiteBigI_le` (`0 < Iₘ ≤ eᴬA²ᵐ⁺¹`).
- `exp_nat_irrational : 1 ≤ A → Irrational (e^A)` and `exp_int_irrational : k ≠ 0 → Irrational (e^k)`: `q·Iₘ ∈ ℤ` while `0 < q·Iₘ ≤ q·eᴬA²ᵐ⁺¹/m! → 0`, an impossible integer in `(0,1)` for large `m`.

**E. The circle recovers faithfulness — the transcendence-gated leg** (`formal/GaloisForLFunctions/RHTower/WeldCircleFaithfulness.lean`).
- `exp_primeLog_comb_eq_rat` — `exp(Σ_p z_p log p) = ∏_p p^{z_p}`, a positive rational cast to `ℝ` (`exp` sum → product, `exp(z log p) = p^z`).
- `primeLog_indep_mod_one` — **`{log p} ∪ {1}` is `ℤ`-linearly independent**: a relation `Σ z_p log p = k ∈ ℤ` exponentiates to `e^k = ∏ p^{z_p} ∈ ℚ`, impossible for `k ≠ 0` by `exp_int_irrational`; then `k = 0` reduces to `primeLog_linearIndependent` (unique factorization).
- `primeCircleHom`, `primeCircleHom_injective` — the circle-valued prime charge `c ↦ [Σ_p c(p) log p] mod 1` is injective. The compact, torsion, divisible target `ℝ/ℤ` reads the entire rank-`∞` prime lattice, in sharp contrast to the total collapse under any bounded-exponent charge.

## Why the trichotomy holds
`ℝ` is divisible; a bounded-exponent target kills every character out of it, so a charge of finite exponent literally cannot resolve any two prime combinations — the rank-`∞` independence is real-cohomology data off every such charge's radar (A). Remove the exponent bound and faithfulness is available: for the torsion-free `H²(·;ℝ)` it costs only unique factorization (B); for the compact circle `ℝ/ℤ`, which *is* divisible and torsion yet carries nonzero characters, faithfulness is equivalent to `{log p} ∪ {1}` independence and therefore demands transcendence — a relation would make `e^k` rational (E). The order channel meanwhile stays faithful on `ℤ` via the profinite `ℤ ↪ ℤ₂` (C), locating the collapse precisely in the transcendental flux channel. The obstruction is a coefficient-ring divisibility fact, structurally distinct from both the modular-quotient barrier (`DeciderBarrier`) and the divisor-blindness no-gos (`deck-charge-invariant`).

## Novelty / significance
Novel: the faithfulness of a weld charge on the prime lattice is not a property of the modulus's coarseness but of the target's **bounded exponent**, and the compact-circle leg forces a bridge into transcendence — `e^n` irrationality, a result **mathlib does not have**, built here from the Hermite integral. This exhibits the seam of the branch concretely: the *arithmetic* weld (prime multiplicative independence) and the *transcendental* frontier (`e`) are the two independent inputs the circle-faithfulness needs, neither reducible to the other. "Constraint, not flow": every theorem is a rigidity (a hom forced to zero) or an independence; no carrier is constructed. Not a difference-Galois statement and not derivable from the known corpus by a competent search — the coefficient-ring dichotomy and its transcendence gate are the new content.

## Lean
`RHTower.{real_addHom_eq_zero_of_nsmul, real_addHom_zmod_eq_zero, weldClass_charge_invisible, prime_flux_charge_collapse, weldClass_finite_charge_invisible, primeFluxHom, primeFluxHom_injective, eq_zero_of_forall_two_pow_dvd, wCharge_two_pow_profile_injective}` in `WeldChargeFaithfulness.lean`; `RHTower.{hermiteP, hermiteF, hermiteF_add_derivative, factorial_dvd_hermiteF_eval_zero, factorial_dvd_hermiteF_eval_A, hasDerivAt_hermite, hermiteBigI_eq, hermiteBigI_pos, hermiteBigI_le, exp_nat_irrational, exp_int_irrational}` in `ExpNatIrrational.lean`; `RHTower.{exp_primeLog_comb_eq_rat, primeLog_indep_mod_one, primeLogHom, primeCircleHom, primeCircleHom_injective}` in `WeldCircleFaithfulness.lean`. All three imported in the `RHTower` umbrella. Axiom-clean (`propext, Classical.choice, Quot.sound` only) for `exp_nat_irrational`, `exp_int_irrational`, `primeCircleHom_injective`, `primeLog_indep_mod_one`, and the charge-collapse/faithfulness theorems; lint pass.

## Open continuations
- **Which non-torsion targets are faithful in general?** The circle `ℝ/ℤ` is faithful iff `{log p}` are `ℤ`-independent mod `ℤ`; a general period lattice `Λ ⊂ ℝ` is faithful iff `{log p}` are independent mod `Λ`. Characterizing the faithful `Λ` is a transcendence-of-log-primes-mod-`Λ` question — the circle is the first nontrivial case; the next is a rank-`2` lattice `⟨1, τ⟩` and asks independence of `{log p, 1, τ}`, open for generic `τ`.
- **Simultaneous circle charge = a Kronecker equidistribution object.** The map `c ↦ ([Σ c(p)log p mod 1])` extends to the infinite-torus character `p ↦ (log p mod 1)`; its density/equidistribution is the multiplicative analogue of the prime-log lattice and a natural next construct.
- **The `e`-tower.** `exp_int_irrational` is the base case `k↦e^k`; the transcendence of `e` itself (not in mathlib) would upgrade every "`k=0`" step to a full `ℚ`-independence of `{log p}∪{1, e-powers}` — a strictly larger weld lattice with `e` adjoined as a non-arithmetic rate.

## Log
- 2026-07-08 — created in 3-formalized. C2/Q2-E settled as a target-torsion trichotomy: finite→collapse, torsion-free→faithful, circle→faithful-via-transcendence. `e^n` and `e^k` irrationality built from scratch (Hermite integral; mathlib gap), then consumed to prove `{log p}∪{1}` independence and circle-charge injectivity. Three modules, umbrella green, axiom-clean, lint pass.
