# Critical prime negativity on linear scale windows

- **ID:** critical-prime-linear-windows-20261022
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Programme:** `srt-apt-biscale-250-contributions-2026-10-22.md`, Q3.
- **Count:** zero until paper, novelty, Lean and significance audits pass.

## Exact target

There exist constants `δ > 0` and `N₀` such that, for every integer `N ≥ N₀`, every
finite set of native indices `S` with `N ≤ m+1 ≤ (1+δ)N` for `m ∈ S`, and every
real coefficient vector `b`, the actual critical prime energy satisfies

`criticalPrimeEnergy S b ≤ -(2/(7000 π⁴)) Σ_{m∈S} b_m²`.

The dimension may grow linearly with `N`. No archimedean contribution enters this
inequality. The stronger approximation target is: for every `η > 0`, there exist
`δ > 0,N₀` such that the same windows satisfy

`|criticalPrimeEnergy S b - factorialCriticalTranslatedPrimeLimit S b|
 ≤ η Σ_{m∈S} b_m²`.

The limit depends on differences of native indices, so the comparison uses `S`
itself as the offset pattern. No reindexing of the actual finite source is needed.

## Why this is a substantive candidate

`eventually_factorialCriticalTranslatedPrimeEnergy_le` fixes `S` before translating
it. Its proof bounds entry errors by a tolerance depending on `S.card`; it does
not furnish a growing-width regime. The complete-form window positivity theorem
uses archimedean logarithmic growth and controls the prime term by absolute value.
The target instead retains the arithmetic sign on spaces of unbounded dimension.
It is not an all-scale positivity theorem and makes no RH claim.

## Proof architecture

Write `E=Σ b_m²`, `w_k=dyadicHarmonicWeight k`, and
`H_k(v)=Σ b_m[cos(2πk λ_{m+1}v)-cos(2πk(m+1)v)]`.
Use critical measure `dμ=1_{v>1}v⁻²dv`. The actual physical correlation is
`C_S(r)=(4/π⁴)Σ_{k,l}w_k w_l ∫H_k(v)H_l(rv)dμ`.

1. **Uniform harmonic tails.** The collar/endpoint decomposition of `v⁻²`,
   support-independent Schur bounds, and jump-kernel Montgomery–Vaughan bound give
   `|∫H_k H_l(r·)dμ| ≤ U E` for every `k,l,r≥1`, with
   `U=windowCollarUniform+windowEndpointUniform`. Consequently the double harmonic
   tail is bounded by `U E` times the corresponding tail of `|w_k w_l|`, uniformly
   in the support. The same bound passes to each limiting harmonic correlation.

2. **Uniform prime tails.** For windows with `δ≤1`,
   `abs_criticalWindowCorrelation_le` with `L=2` gives
   `|C_S(r)|≤D r⁻¹ᐟ² E`. Hence the prime tail is bounded by
   `D E Σ_{r>R} Λ(r)r⁻³ᐟ²`, independently of dimension. The limiting correlation
   inherits this estimate by translating each fixed pattern into a dyadic window
   and taking its already-proved limit. This proves uniform tails on both sides.

3. **Affine comparison in a fixed harmonic head.** Replace `λ_m` by `m+1/12`.
   Disjoint frequency intervals give the existing exact error estimate
   `∫|H_k-H_k^aff|²dμ≤π²k Σ e_{m+1}b_m²≤π²k E/(140N)`.
   Integer dilation satisfies `H_l(rv)=H_{lr}(v)`, for both actual and affine
   clocks, so the same estimate applies with harmonic index `lr`. Step 1 at
   `r=1` gives `∫H_k²dμ≤UE`.
   Cauchy–Schwarz and `‖H_k^aff‖₂≤‖H_k‖₂+‖H_k-H_k^aff‖₂` therefore control the
   difference of each actual/affine head correlation by `B_{k,l,r}N⁻¹ᐟ²E`.
   This is an operator estimate, with no `S.card` loss.

4. **Affine head resonance.** Product-to-sum writes each affine entry using
   `F(f)=∫_{v>1}v⁻²cos(2πfv)dv`. The existing collar/endpoint bounds imply
   `|F(f)|≤D₀/|f|` for `|f|≥1`. If `k≠rl`, all difference frequencies are at
   least `N/2` when `δ≤1/(8K(R+1))` and `N≥K(R+1)`; all sum frequencies are
   at least `N`. If `k=rl`, the slow difference part is exactly the known
   pattern harmonic mass `J_k(S,b)`; only the fast sum part remains.
   Each residual entry is `O_{K,R}(1/N)`. Summing coefficients costs
   `(Σ|b_m|)²≤S.card E≤(δN+1)E`, so the head error is
   `O_{K,R}(δ+1/N)E`.

5. **Order of choices.** Choose `R` for the prime tails, then `K` for the finitely
   many harmonic tails, then `δ` for the finite-head error, then `N₀` for the
   affine and endpoint errors. This proves the approximation target. Combine it
   with the existing limit bound `P∞≤-4E/(7000π⁴)` at
   `η=2/(7000π⁴)` to obtain the sign theorem.

## Quantitative paper estimate

The following estimate makes the order of choices precise. All constants below
are already defined by convergent series or finite physical integrals in the corpus.
Set

- `U = windowCollarUniform + windowEndpointUniform`;
- `D₀ = criticalCollarCurvature + criticalEndpointCurvature + 1/(2π)`;
- `D = (4/π⁴) criticalWindowConstant √2`, `D∞ = 28/π⁴`;
- `a = π²/140`, `W = 7/4`;
- `L_R = Σ_{2≤r≤R} Λ(r)/r`;
- `τ_K = Σ_{(k,l)∉{1,…,K}²} |w_k w_l|` (zero indices contribute zero).

For integers `R≥2,K≥1,N≥max(2,K(R+1))`, take
`0≤δ≤min(1,1/(4K(R+1)))`. If every `m∈S` satisfies
`N≤m+1≤(1+δ)N`, then

```
|P(S,b) - P∞(S,b)|
 ≤ E · [ (D+D∞) Σ_{r>R} Λ(r)/r^(3/2)
       + (4/π⁴)(U+4)L_R τ_K
       + (4/π⁴)W² L_R ·
           (2√(U a K R/N) + a K R/N + 6D₀(δ+1/N)) ].
```

### Normalizations and proof

**Prime representation.** The source change of variables contributes one factor
`r⁻¹ᐟ²`, in addition to the explicit prime weight `Λ(r)r⁻¹ᐟ²`.
Thus `P=Σ_{r≥2}Λ(r)C_S(r)/r`, with no missing square root. The Bernoulli
expansion of each phase has coefficient `-2/π²`, so its quadratic correlation
has coefficient `4/π⁴`. Existing absolute series admission justifies these
identities for each individual finite family before any uniform estimate is used.

**Both prime tails.** The actual window estimate gives
`|C_S(r)|≤D E/√r`. For the limit, `0≤J_m≤4E` for `m≥1` and
`|w_{rl}|≤1/r²` for `r,l≥1`. Since `Σ_l |w_l|≤7/4`,

`|C∞_S(r)|≤(4/π⁴)(4E)(7/4)/r² = D∞ E/r² ≤ D∞ E/√r`.

Multiply by `Λ(r)/r` and sum for `r>R`. The majorant converges by the
corpus von Mangoldt Dirichlet-series theorem at exponent `3/2`.

**Both harmonic tails.** For fixed `2≤r≤R`, the actual integrated harmonic
pair has absolute value at most `UE`; its limiting value is either zero or
`J_k`, of absolute value at most `4E`. The discarded double series therefore
costs `(4/π⁴)(U+4)τ_K E`. Summing its nonnegative prime weights gives the second
term in the displayed estimate. Absolute summability of `w` proves `τ_K→0`.

**Actual-to-affine head.** Put `p=k`, `q=rl`, so `p,q≤KR` inside the head.
Write `H_p=A_p+d_p` and `H_q=A_q+d_q`. In critical measure,
`∫H_p²,∫H_q²≤UE`, while
`∫d_p²≤apE/N`, `∫d_q²≤aqE/N`. The identity

`H_pH_q-A_pA_q = d_pH_q + H_pd_q - d_pd_q`

and three Cauchy–Schwarz inequalities bound the integrated difference by
`[√(Uap/N)+√(Uaq/N)+a√(pq)/N]E`, at most
`[2√(UaKR/N)+aKR/N]E`. This proves the estimate for arbitrary signed coefficient
vectors, including growing supports. No pointwise coefficient-sum estimate is
used in this comparison.

**Affine head-to-limit.** On branches `σ,τ∈{0,1/12}`, product-to-sum uses
frequencies

`f₋=p(m+1+σ)-q(n+1+τ)`, `f₊=p(m+1+σ)+q(n+1+τ)`.

If `p≠q`, integrality gives `|p-q|≥1`, hence

`|f₋|≥N-(p+q)δN-(p+q)/12≥N/2`, and `f₊≥2N`.

Here `p+q≤K(R+1)`, so the displayed restrictions on `δ,N` imply the two
inequalities. The collar, jump and remainder decomposition gives
`|F(f)|≤D₀/|f|` for `|f|≥1`. Each branch pair costs at most
`(2D₀/N+D₀/N)/2`; four branch pairs cost at most `6D₀/N`.

If `p=q`, retain all difference-frequency terms exactly. Their signed sum is

`F(p(m-n)) - [F(p(m-n+1/12))+F(p(m-n-1/12))]/2`.

It equals the integral of
`v⁻² cos(2πp(m-n)v)(1-cos(2πpv/12))`. Summing `b_m b_n` and using the exact
pairwise expansion of `factorialCriticalPatternDensity` gives precisely `J_p`.
Only the four sum-frequency terms remain; their bound `2D₀/N` is covered by
`6D₀/N`. This also checks the factor in the resonant mass.

In either case, summing the entry errors costs
`(6D₀/N)(Σ|b_m|)²≤(6D₀/N)card(S)E`.
The integer points `m+1` are one-separated in an interval of length `δN`, so
`card(S)≤δN+1`. This proves the remaining `6D₀(δ+1/N)E` term. Finally the
finite harmonic head has total absolute weight at most `W²`, yielding the
third term in the estimate.

**Uniform approximation and sign.** Given `η>0`, first make the prime-tail
term smaller than `η/4` by choosing `R`. Next choose `K` so the harmonic-tail
term is smaller than `η/4`. Choose positive `δ` obeying the frequency-gap
restriction and making its contribution smaller than `η/4`. Then choose `N₀`
so the remaining inverse-scale terms are smaller than `η/4`, and so all scale
restrictions hold. All choices precede `S,b`. For `E=0`, all coefficients on
`S` vanish, so both forms are zero; no normalization or division by zero is
needed. The existing limit gap proves the target at `η=2/(7000π⁴)`.

This closes the analytic paper argument. Remaining work: audit its exact Lean
implementation and repeat the corpus novelty check on the final statement.

## Dependency audit

Verified source:

- `FactorialCriticalPrimeFiniteScaleNegativity.lean`: existing fixed-pattern result.
- `FactorialCriticalTranslatedHarmonicLimit.lean`: exact resonant harmonic limit.
- `FactorialCriticalTranslatedCorrelationLimit.lean`: complete harmonic limit.
- `FactorialCriticalTranslatedPrimeLimit.lean`: complete prime limit.
- `CriticalPrimeChannelScaleWindows.lean`: uniform harmonic bounds (currently
  private component lemmas) and public window correlation estimate.
- `FactorialAffineFrequencyIntervals.lean`: exact whole-line error energy and
  critical half-line estimate.
- `FactorialCriticalAffineComparison.lean`: complete profile comparison, available
  if useful; no need to control affine infinite tails separately.

Still to make explicit in Lean: full-weight harmonic bound, affine-head comparison,
finite-head matrix estimate, and uniform two-tail assembly. Paper argument requires
checking every normalization and the cardinality inequality before promotion.

## Novelty audit

Corpus searches include `critical prime matrix uniform growing support negative
finite scale`, `critical correlation quantitative convergence rate translated
pattern`, `growing window finite scale prime negative affine`, and `uniform operator
convergence factorial translated`. No matching growing-window sign theorem found
in inspected hits. Source-only index; semantic coverage incomplete.

User directs corpus-only research. Continue novelty checks through the research
search tool and exact Lean sources; do not use the web.

## Continuation

`RHTower/FactorialCriticalAffineFrequencies.lean` now checks with the required
foreground leaf command (exit 0). It proves the unequal-harmonic `N/2` gap,
the `2N` sum-frequency gap, `card(S) ≤ δN+1`, and the resulting coefficient
absolute-sum-square estimate. The module is wired into `RHTower.lean`; it is a
supporting phase of this single contribution, not an independently counted result.

Renewed corpus searches for affine frequency windows, exact resonance identities,
and growing-dimension critical prime negativity completed without search errors.
The relevant established results remain fixed-pattern prime negativity, uniform
absolute window bounds, and affine resonance classification. No matching
growing-window sign theorem appeared in inspected hits. Compiler applicability
is still checked from source and by Lean, not inferred from search metadata.

Drafts exist in `RHTower/FactorialCriticalWindowHarmonicBounds.lean` and
`RHTower/FactorialCriticalWindowAffineEnergy.lean`. They are not audited or wired.
The first audit stopped at a stale transitive import of
`GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam`; its source
now lives under `RHTower/ThetaCusp/`. The current
`ThetaCusp/ThetaCuspFullReflectionEighthHankelSeam.lean` checks successfully, but
its copied binary retains the old import. Plain `lean <file>` emits no replacement
binary. The root `AGENTS.md` now explicitly reiterates no `-o`/`-i` and no
permission stop for missing imports; the earlier exception request is withdrawn.
Continue exact named-module checks with the prescribed command. Do not emit
replacement binaries through another mechanism to bypass that restriction.

`RHTower/FactorialCriticalWindowAffineHead.lean` contains the next draft: affine
product-to-sum, exact slow resonant mass, inverse-scale matrix entry bounds, and
the relative-window coefficient-square bound. This draft has not passed Lean.
The remaining full theorem requires harmonic and prime series assembly.
Keep helper results grouped as one contribution; they do not count individually.
