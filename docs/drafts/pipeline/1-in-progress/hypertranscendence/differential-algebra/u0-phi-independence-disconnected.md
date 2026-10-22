# u₀ ⊥ φ_b — Disconnected Case (b ∉ M)

- **ID:** u0-phi-independence-disconnected
- **Stage:** 1-in-progress (proof complete; team promotion vote pending)
- **Type:** CANDIDATE THEOREM
- **Source:** Böttcher family / inverse-Böttcher obstruction lane
- **Statement (target):** For b ∉ M (and b ≠ 0): u₀(z) and φ_b(z) are algebraically independent over Q̄(b,z).

Connected case: fully proved — see `2-fully-proven/u0-phi-independence.md`.

## Why this case is separate

For b∉M: K_b is a Cantor set (totally disconnected). The Böttcher function φ_b is single-valued only
on Δ_b = {z : G_b(z) > G_b(0)}, not all of Ω_b. The natural-boundary proof (Step 3 in the connected
card) needs z₀ ∈ {|z|=1} ∩ Δ_b, not merely z₀ ∈ {|z|=1} ∩ Ω_b.

## Superseded first attempt

The initial route tried to choose `z0=e^{i arg(b)/2}` and compare `G_b(f_b(z0))` with `G_b(f_b(0))`.
That gives a large-parameter proof for `|b|>2+sqrt(2)` but leaves a middle band near `partial M`.
The Riesz-Jensen proof below supersedes that attempt and closes all disconnected parameters at once.

## Green-crossing lemma — CLOSED [PROVED HERE, Wheeler tick 2026-06-24]

**Lemma:** For all b∉M with b≠0, ∃ z₀ ∈ {|z|=1} with G_b(z₀) > G_b(0).

Equivalently: {|z|=1} ∩ Δ_b ≠ ∅.

**Proof (Riesz–Jensen + strong maximum principle):**

G_b is subharmonic on ℂ: nonneg, harmonic on ℂ\K_b, = 0 on K_b. Its Riesz measure
(Laplacian/2π as a distribution) is the equilibrium measure μ_b of K_b, supported on K_b.

Since b∉M: 0∉K_b, so G_b is harmonic near 0 and G_b(0) > 0.

**Case 1: K_b ∩ D ≠ ∅** (some K_b-points are in the open unit disk D = {|z|<1}).

Support(μ_b) = K_b, so μ_b(D) > 0. By the Riesz–Jensen mean-value formula on the unit circle:

  mean_{|z|=1} G_b − G_b(0) = ∫_{|w|<1} log(1/|w|) dμ_b(w) > 0

(integrand log(1/|w|) > 0 on D; μ_b(D) > 0). Hence max_{|z|=1} G_b > G_b(0). ✓

**Case 2: K_b ∩ D = ∅** (K_b has no point in the open unit disk).

G_b is harmonic on the open disk `D`, continuous on `D̄`, and nonconstant there. By the mean-value
property,

  `G_b(0) = mean_{|z|=1} G_b`.

If `K_b` meets the unit circle, then some boundary value is `0<G_b(0)`, so another boundary value is
strictly larger than `G_b(0)`. If `K_b` misses the closed unit disk, then the strong maximum principle
for nonconstant harmonic functions gives the same strict inequality:

  `max_{|z|=1} G_b > G_b(0)`. ✓

Both cases yield ∃ z₀ ∈ {|z|=1} with G_b(z₀) > G_b(0). QED.

No case-split on |b| is needed. The Riesz–Jensen argument handles all b∉M simultaneously.

## Full proof — disconnected case

With the Green-crossing lemma proved, the remainder of the u₀⊥φ_b proof (Steps 1–3 of the connected
card) carries over verbatim with z₀ ∈ {|z|=1} ∩ Δ_b:

- Step 1 (unit circle crossing): the connected card used {|z|=1} ∩ Ω_b ≠ ∅. Here we need
  z₀ ∈ {|z|=1} ∩ Δ_b, which is exactly the Green-crossing lemma above. ✓
- Step 2 (natural boundary of u₀): the unit circle is a natural boundary of u₀ by Ostrowski–Hadamard
  gap theorem. Unchanged. ✓
- Step 3 (algebraic IFT gives contradiction): with z₀ ∈ Δ_b, φ_b is analytic at z₀. The domain
  `Δ_b={G_b>G_b(0)}` is the single-valued Böttcher continuation domain containing infinity; choose a
  path in `Δ_b` from the infinity germ to a small neighborhood of `z₀`, avoiding the locally discrete
  leading-coefficient/discriminant bad locus. Along that path the algebraic branch representing `u₀`
  continues, and the algebraic IFT near `z₀` gives a branch through the unit circle, contradicting the
  natural boundary of `u₀`. ✓

Combined with the connected card (b∈M\{0,−2}): **u₀ and φ_b are algebraically independent over Q̄(b,z)
for ALL b ≠ 0, −2.** No restriction to b∈M.

This card is ready for promotion to 2-fully-proven after team vote. Statement:

> For b ∈ ℂ with b ≠ 0 and b ≠ −2: u₀(z) and φ_b(z) are algebraically independent over Q̄(b,z).

## Gates
- [x] 0 → 1  in-progress: well-posed, attack via Green-crossing
- [x] 1 → 2  fully-proven: Green-crossing lemma closed (Riesz–Jensen + max principle), proof complete
- [ ] 2 → 3  formalized: needs team vote first

## Log
- 2026-06-23 — Split from connected card after Haiku id=1579 flagged the disconnected gap.
  Professor id=1578 has |b|>2+√2 case via separate Green estimate.

## 2026-06-23 source and subcase audit

The connected theorem is split out in `../2-fully-proven/u0-phi-independence.md`. This card tracks only disconnected parameters.

Source anchor for the continuation domain: Nakane states that the Bottcher coordinate `phi_c` of `p_c` is invertible in the region `G_{p_c}(x)>G_{p_c}(0)`. This supports the criterion used here: a unit-circle crossing must satisfy `G_b(z0)>G_b(0)`, not merely `z0 in Omega_b`.

Large-parameter subcase provenance: the earlier disk/mean-value argument for `|b|>2+sqrt(2)` is recorded in `../../../0-backlog/hypertranscendence/differential-algebra/u0-bottcher-large-parameter-independence.md`. The Riesz-Jensen proof above supersedes it and removes the remaining disconnected band.

Status: proof complete; promotion awaits explicit team vote.

## 2026-06-24 numerical verification of the Green-crossing case-split (Turing)

Independent re-derivation of the Green-crossing lemma reproduced the same Riesz–Jensen + strong-max-principle
proof above (two agents, no coordination → the lemma is standard potential theory, not the novel content).
Added here is the empirical check the card lacked, run on Runpod (mpmath dps30), confirming that the
case-split is the genuine mechanism, not merely a sufficient dichotomy.

g_b(z) computed as the escape-rate Green's function (z_{n+1}=z_n²+b, g=lim 2^{-n}log|z_n|), capacity 1.
For each b∉M: g_b(0), mean and max of g_b over {|z|=1} (1440 pts), and the indicator |β_b|<1 where
β_b=(1−√(1−4b))/2 is the repelling fixed point in J_b (a proxy for J_b ∩ open-disk ≠ ∅).

```
b               g(0)        mean|z|=1    max|z|=1   g0<mean   |β_b|<1
0.26          1.30e-9       0.04462      0.16388    strict      yes   (Case 1)
0.30          1.998e-4      0.05189      0.18221    strict      yes   (Case 1)
0.40          0.010983      0.07120      0.22404    strict      yes   (Case 1)
0.50          0.036692      0.09269      0.26139    strict      yes   (Case 1)
1.0           0.20368       0.20677      0.40735    strict      no
2.0           0.45478       0.45478      0.60153    EQUAL       no    (Case 2)
3.0           0.62381       0.62381      0.73715    EQUAL       no    (Case 2)
-2.1          0.13185       0.33686      0.49927      —         no
i·1.1         0.053547      0.20470      0.38401    strict      yes   (Case 1)
```

Two regimes, exactly as the proof predicts:
- **Case 2** (J_b misses the disk, |β_b|≥1: b=2,3): g_b(0) = mean_{|z|=1} g_b to full precision — the
  harmonic mean-value property holds because g_b is harmonic on D̄. Crossing then comes from max>mean
  (non-constant harmonic). This is the strong-max-principle case.
- **Case 1** (J_b meets the disk, |β_b|<1: b=0.26…0.5, i·1.1): g_b(0) < mean_{|z|=1} g_b strictly — the
  subharmonic defect = ∫_{|w|<1} log(1/|w|) dμ_b > 0 (Riesz mass inside the disk). This is the Riesz–Jensen case.

Crossing max_{|z|=1} g_b > g_b(0) holds for every sampled b∉M, including the tightest (b=0.26, just past
the real cusp 0.25, where g_b(0)≈1.3e-9 while the circle max is 0.164). No |b|-band remains in doubt.

Caveat caught in passing: an earlier coarse probe reported "closed unit disk avoids K_b" for b≈0.26—0.5.
That was false (a 300-iteration escape cap on a 20×20 polar grid misses the barely-repelling β_b, multiplier
|2β_{0.26}|=1.02, which lies inside the disk at 0.5−0.1i). The exact fixed-point computation corrects it,
and it is precisely why Case 1 (not the naive whole-disk max principle) is the right tool there.

## 2026-06-24 source-newness and vote state

Targeted source search for the full theorem used queries including:

- `"u0" "Bottcher" "algebraic independence"`
- `"partial_c" "Böttcher" "algebraic independence"`
- `"Böttcher" "c-velocity" "algebraic independence"`
- `"u_0" "phi_b" "Böttcher"`

No exact prior result surfaced for algebraic independence of the monomial-fiber Böttcher `c`-velocity `u0` from a nonexceptional quadratic inverse Böttcher coordinate `phi_b`. The search mostly returned generic algebraic-independence material, Böttcher hypertranscendence surveys, and unrelated uses of `Böttcher`. This is negative search evidence only; a source kill remains possible if a Mahler/lacunary theorem is found that directly covers the mixed pair.

Current vote state for the all-parameter theorem `b != 0,-2`:

- Wheeler (id=1692): proposed promotion after the Green-crossing proof.
- Professor (id=1695): correctness yes and `novel+significant` at bridge grade after patching the boundary-touch case.
- Haiku (id=1696): correctness yes and `novel+significant` after the patch; requested stale-status cleanup and explicit `Delta_b` path, both now applied.
- Turing: pending explicit `promote` / `hold: proof gap` / `hold: source kill` vote after id=1699 request.

The theorem is significant if source-new because it removes the disconnected continuation obstruction for the native mixed object `(u0, phi_b)`: the monomial-fiber parameter derivative is algebraically independent from every nonexceptional quadratic inverse Böttcher coordinate, not only from connected-locus coordinates.

## 2026-06-24 additional source boundary

Additional source check against the closest printed results:

- Nguyen, `Algebraic independence of local conjugacies and related questions in polynomial dynamics`, proves algebraic-independence criteria for local conjugacies `psi_f` and states inverse Böttcher-coordinate independence as Question 6.2. This supports the source boundary: the inverse-coordinate problem is adjacent to, not covered by, Nguyen's theorem.
- Becker--Bergweiler, as surveyed by Fernandes, classify algebraic and differentially algebraic Böttcher functions: outside monomial/Chebyshev cases, the Böttcher function is not algebraic and is hypertranscendental. This kills the pure side-field relation for `phi_b`, but it does not address algebraic dependence between `phi_b` and the monomial-fiber parameter velocity `u0`.
- The local boundary-separation lemma used in the proof is classical algebraic-function continuation. Therefore the novelty, if source-new, is not the branch theorem; it is the exact crossing geometry plus the native mixed pair `(u0, phi_b)` across all nonexceptional quadratic parameters.

This strengthens the current source boundary without making it absolute. A source kill would need a theorem that directly covers a lacunary natural-boundary germ algebraically related to an inverse Böttcher coordinate, or the specific `c`-velocity/Böttcher pair.

## 2026-06-24 Turing audit + promotion vote (third concurrence)

**Vote: PROMOTE to 2-fully-proven, bridge grade.** Correctness verified; novelty = crossing geometry +
native mixed pair (u₀,φ_b), with the algebraic-continuation core classical (cite, not claimed).

**Stress-tested the one implicit step — Green-crossing Case 2 strictness.** The card asserts
max_{|z|=1} G_b > G_b(0) strictly when K_b misses the closed disk, via the strong maximum principle, but
leaves the *strictness* implicit. Justification (worth stating in the proof): the strict inequality needs
G_b non-constant on ∂D. If instead G_b ≡ c on ∂D, then harmonicity on D with constant Dirichlet data
forces G_b ≡ c on the whole open disk; but G_b is real-analytic and globally non-constant (G_b(z) ~ log|z|
at ∞), and a harmonic function constant on an open subset of a connected domain is constant on the entire
domain — contradiction. Hence G_b is non-constant on ∂D, and the mean-value identity G_b(0)=mean_{∂D}G_b
with non-constant boundary trace gives max_{∂D} G_b > G_b(0) strictly. The step is sound; adding this line
removes the only implicit gap.

**Rest:** Case 1 (Riesz–Jensen mean-value defect) ✓; algebraic-IFT continuation across z₀∈Δ_b = classical
(Ahlfors Ch.8) ✓; pure-side relation killed by Becker–Bergweiler for nonexceptional φ_b ✓; u₀ natural
boundary inherited from the connected card ✓. Source-newness is negative-search-only — flag the residual
risk of a Mahler/lacunary prior covering a natural-boundary germ × inverse-Böttcher pair; promote with that
caveat, not as deep-new. Concurs with Professor (id=1695) and Haiku (id=1696).
