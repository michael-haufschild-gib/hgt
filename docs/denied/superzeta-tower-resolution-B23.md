# Resolution of B23 (the superzeta transcendence tower): the tower does NOT recurse

**Theorist, 2026-06-19.** Charter cell **B23** (the wildest conjectures, `hypertranscendental_galois_program.md`)
proposes a *transcendence tower* `ζ → 𝒵 → 𝒵₂ → …`: the Voros superzeta `𝒵(w) = Σ_ρ ρ^{-w}` (whose
integer values are the secular moments `P_k`) is itself a hypertranscendental generating function with
its *own* zeros, to which the whole field recurses; "does the tower have a fixed point / `q→1` limit
that is *the* prime?" Resolved here, using the field's own First Theorem. Falsify-and-log, first-class.
Air-marked.

---

## The verdict: the tower breaks at level 2  [argued, uses the field's First Theorem]

> **The superzeta has no Euler product, so by the field's First Theorem it is a "fake" — its zeros
> are NOT a spectrum the field's machinery acts on. The tower does not recurse.**

**Why.** The field's First Theorem (`EulerProduct.lean`, `isMultiplicative_iff_bohr_factorization`):
a generating function lies in the field's domain — carries the two-faces structure on a spectrum the
difference-Galois `G_L` acts on — **iff** it has an Euler product, i.e. its Dirichlet coefficients are
multiplicative over a *prime base with unique factorization*. The superzeta `𝒵(w) = Σ_ρ ρ^{-w}` is a
generalized Dirichlet series whose **frequency set is the zeros `{ρ}`**, and:

1. **The zeros carry no multiplicative structure.** `{ρ}` is not closed under multiplication, has no
   unique factorization, no "prime sub-basis". So `𝒵` has **no Euler product** — there is no
   `𝒵(w) = ∏_? 𝒵_?(w)` over a prime base. (By contrast `ζ`'s frequencies are `{log n}`, supported on
   the `ℚ`-LI prime base `{log p}` — the field's foundation, `linearIndependent_log_primes`.)
2. **By the First Theorem, `𝒵` is reducible / "fake."** A generating function with no Euler product is
   not a single irreducible infinite-base difference module (foundations §9). Its zeros are therefore
   not constrained to a symmetry locus by any `G_L`-action — there is no Face A / Face B law on them.
   The field's machinery is **anchored to the primes** (the multiplicative base); `𝒵` is built from the
   *additive/spectral* side (the zeros), the wrong side of the seam.

So the recursion `ζ → 𝒵` already exits the field at the first step: `𝒵` is the kind of object the
field's firewall *excludes*, not a new instance of the field.

## The category error in "the fixed point is the prime"  [resolved]

B23's wild hope — a `q→1` fixed point of the tower that "is the prime" — inverts the field's actual
structure. The field's whole content (the seam, `infinite-base-…-L-functions.md`) is that **primes
(multiplicative, `𝕋^∞`, free) and zeros (the spectrum, additively/archimedean-structured) sit on
opposite sides of the `[𝔾_a, 𝔾_m]` seam**, and the difficulty is precisely that they do not convert
into each other (no Euler product for the zeros; no spectrum for the primes alone). The tower asks the
zeros to *become* a prime base; the seam is exactly the obstruction to that. So:

> B23's tower is a **category error across the seam**: it would require the spectral (zero) side to
> acquire the multiplicative (prime) structure, which is the one thing the field says it lacks. The
> "fixed point = the prime" is the seam collapsing — equivalent to the whole problem dissolving, not a
> new object. Logged as **falsified** (in its literal form), with the precise reason: no Euler product
> on the zeros.

## What survives (the salvage)  [conjecture, narrowed]

Not all of B23 is dead. Two narrowed, non-category-error remnants:

- **The superzeta as a `(value, no-spectrum)` object.** `𝒵` belongs in the *value* corners of the 2×2
  (charter Part VIII), not the spectral one: its special **values** `𝒵(2m) = P_{2m}` are periods (the
  secular moments, §8–11 of `dss-multiplicity-estimate-spectral-genericity.md`), governed by classical
  transcendence (`{π, ζ(odd), Stieltjes γ_n}`), **not** by a second `G_L`. So the "tower" is really a
  *descent into the value-side period theory*, where it already lives — no new spectral level.
- **Voros's actual superzeta zeros** (if any in the continuation) are a legitimate point set, but —
  lacking an Euler product — they are a "fake family" by the field's classification, expected to be
  *unconstrained* (no RH-type localization). A concrete test (referee): if `𝒵`'s continuation has
  zeros off any symmetry line, that **confirms** the no-Euler-product ⟹ no-Face-A prediction.

**House status.** B23 (transcendence tower) **resolved**: the tower does not recurse — `𝒵` has no
Euler product, so by the field's First Theorem it is excluded from the field's spectral domain; "fixed
point = the prime" is a seam-collapse category error. Salvage: `𝒵` lives in the *value/period* corner
(its values are the secular-moment periods `{π,ζ(odd),Stieltjes}`), not a second spectral level. This
is the field **adjudicating its own wild conjecture by its own First Theorem** — a sign of internal
coherence. Prediction (testable): Voros superzeta zeros, lacking an Euler product, are off-line / fake.

---

## Content check, a ledger witness, and a wild expansion (Critic, 2026-06-19)

### 1. Correctness check  [verdict sound; one sharpening]

The verdict — `𝒵(w) = Σ_ρ ρ^{-w}` has no Euler product, so by the First Theorem it
is excluded from the field's spectral domain; "fixed point = the prime" is a
seam-collapse category error — is **correct as stated**. One sharpening for rigor:
the phrase "its frequency set is the zeros `{ρ}`" (§The verdict, point 1) should
read **the frequencies are `{log ρ}`** (a generalized Dirichlet series
`Σ_ρ e^{-w log ρ}`); the load-bearing fact is unchanged and in fact *strengthened*
— `{log ρ}` is not supported on any `ℚ`-LI multiplicative base (contrast
`{log p}`, `linearIndependent_log_primes`), and `{ρ}` is not multiplicatively
closed, so no Euler product either way. Verdict stands.

### 2. Ledger witness — the superzeta is an additive resolvent trace  [PROVED HERE]

The structural core of the verdict is now **machine-checked**
(`formal/GaloisForLFunctions/RHTower/SuperzetaResolvent.lean`, axiom-clean, full tree
green, audit PASS). For a finite multiset of reciprocal-zeros `r_i = ρ_i⁻¹`:

- `geom_eq_inv`: each `Σ_m r_iᵐ Xᵐ = (1 − r_iX)⁻¹` (the per-zero **resolvent**).
- `superzeta_eq_sum_resolvent`: the superzeta generating function is the **sum**
  `Σ_i (1 − r_iX)⁻¹` — additive over the zeros, a **trace**, structurally **not**
  a product. Contrast `EHKoszulDuality.coeff_localFactor_series`, whose generating
  object is the **product** `∏(1 − αx)` over a multiplicative base.
- `superzeta_coeff_eq_powerSum`: its `k`-th coefficient is `Σ_i r_iᵏ = 𝒵(k) = P_k`.

So the `Σ` (spectral/additive) vs `∏` (prime/multiplicative) split is now a Lean
theorem: the superzeta sits on the additive side of the `[𝔾_a, 𝔾_m]` seam, hence
carries no Euler product. This is the ledger-grade half of the B23 verdict (the
finite witness); the infinite analytic continuation and the no-second-`G_L` claim
stay in the draft.

### 3. Wild conjecture — the tower DOES recurse, but motivically, not spectrally  [SPEC, expands reach]

B23 killed the *spectral* recursion (`ζ → 𝒵 → 𝒵₂` as difference-Galois objects).
But the salvage (§What survives) places `𝒵`'s values `𝒵(2m) = P_{2m}` in the
**period** corner. Conjecture: **the tower recurses there** — not as a tower of
`L`-functions, but as a tower of **motives / periods**:

> **Conjecture B23′ (the motivic period tower) [SPEC].** The `ℚ`-algebra
> `𝒫_𝒵 = ℚ⟨P_k : k ≥ 2⟩` generated by the superzeta values (secular moments) is a
> **period algebra** carrying a **motivic Galois action** (Kontsevich–Zagier /
> mixed-Tate type), and *that* action — not a second difference-Galois `G_L` — is
> the next level of the tower. The "fixed point" is not the prime but the
> **pro-unipotent radical of the motivic Galois group** of `𝒫_𝒵`. The two towers
> are the two sides of the seam: the **multiplicative/spectral** tower
> (difference-Galois `G_L`) is *dead at level 2* (B23, no Euler product on the
> zeros); the **additive/period** tower (motivic-Galois) is *alive* and is where
> the recursion actually lives. **Their non-interaction is the seam itself**:
> `[𝔾_a, 𝔾_m] ≠ 0` is exactly "the spectral tower cannot become the period tower."

*Why this is the right kind of wild.* It is **falsifiable** (the `P_k` either are
or are not motivic periods with the predicted Galois structure — Voros's explicit
formulae for `𝒵(2m)` in `{π, ζ(odd), Stieltjes γ_n}` are the data), it is
**non-circular** (it reads the *values*, source-pure periods, not the zeros it
would constrain), it **respects the seam** (places the recursion on the additive
side, where B23's own First-Theorem obstruction does not bite), and it routes B23
into **Nesterenko / motivic-Galois** territory — the genuine transcendence engine
the field's height-vacuum wall was pointing at. It expands B23 from a *negative*
result (the spectral tower is dead) to a *positive* program (find the motivic
tower).

**House status (updated).** B23 verdict re-confirmed and content-checked (one
wording sharpening, `{ρ}` → `{log ρ}`). Its structural core is now **ledger-proven**
(`SuperzetaResolvent.lean`: superzeta = additive resolvent trace ≠ multiplicative
Euler product). New **wild expansion B23′**: the tower recurses on the
*motivic/period* side, not the spectral side — the two towers' non-interaction is
the seam. Spectral tower dead at level 2 (proved-direction); motivic period tower
open (conjecture, the new positive program).
