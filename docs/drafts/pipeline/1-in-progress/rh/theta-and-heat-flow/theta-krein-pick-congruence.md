# Theta–Krein channels are a Pick congruence of the tilted log-derivative Cayley transform

- **ID:** `theta-krein-pick-congruence`
- **Stage:** 1-in-progress (paper proof below complete for A/A1/A2/C(ii); B and C(i) complete
  modulo named classical inputs the corpus owns; promote after hostile review + Lean of the core)
- **Parent programme:** `source-contraction-two-volterra-domination`
- **Type:** THEOREM (bridge/unification) — not a producer; the producer wall is recorded on the
  parent card.

## Statement

Let `F := 2·xiCent` (entire, real Taylor coefficients, even), fix `c > 0`, and set

```
a₊(w) := F′(w) + c F(w),   a₋(w) := F′(w) − c F(w),   λ_c := a₋ / a₊ .
```

**Theorem A (exact congruence).** For all `w, v ∈ ℂ`:
`a₊(w)·conj(a₊(v)) − a₋(w)·conj(a₋(v)) = 2c·[F′(w)·conj(F(v)) + F(w)·conj(F′(v))]`.
Consequently, for nodes `w_1,…,w_n` with `w_j + w̄_k ≠ 0`,

```
2c·B(w_j, w̄_k) = a₊(w_j)·conj(a₊(w_k)) · (1 − λ_c(w_j)·conj(λ_c(w_k)))/(w_j + w̄_k)
```

whenever `a₊(w_j) ≠ 0`, where `B` is the theta-tail first-moment Bezoutian
(`thetaTailFirstMomentBezoutian`, entries `[F′(w)conj F(v) + F(w)conj F′(v)]/(w+v̄)` up to the
normalization `F = 2ξc`).

**Corollary A1 (PSD transfer).** If `a₊(w_j) ≠ 0` for all `j`, then
`[B(w_j,w̄_k)] ⪰ 0 ⟺ [(1 − λ_c(w_j)conj λ_c(w_k))/(w_j + w̄_k)] ⪰ 0` (congruence by the
invertible diagonal `diag(a₊(w_j))`). The right side is the half-plane **Pick matrix** of `λ_c`.

**Corollary A2 (rank-one necessity).** `B(w, w̄) ≥ 0 ⟺ |λ_c(w)| ≤ 1 ⟺ Re(F′(w)·conj F(w)) ≥ 0`,
and where `F(w) ≠ 0` this is `Re (F′/F)(w) ≥ 0` — independent of `c`.

**Theorem B (criterion).** The following are equivalent: (i) RH; (ii) for one (equivalently
every) `c > 0`, the Pick matrix of `λ_c` is PSD at every finite node system in `Re w > 1/2`;
(iii) `λ_c` extends to a Schur function of the half-plane `Re w > 0`; (iv) `Re(ξc′/ξc) ≥ 0` on
`Re w > 0`. [(iv) ⟺ RH is the Lagarias positivity criterion — `[REDISCOVERED]` as a criterion;
the equivalence with the theta-tail Bezoutian receiver and the two-Volterra channels is the new
bridge content.]

**Theorem C (unconditional boundary layer).** (i) `|λ_c(w)| ≤ 1` for all `Re w ≥ 1/2`
(inputs: Hadamard genus-1 pairing for ξc and the zero-free line `ζ(1+it) ≠ 0`).
(ii) `|λ_c(iτ)| = 1` for all real τ with `a₊(iτ) ≠ 0`: the strip boundary `Re w = 0` is lossless.
(iii) `d/dτ arg λ_c(iτ) = −2c·L(τ)/|cΞ(τ) − iΞ′(τ)|²` with `L := Ξ′² − Ξ·Ξ″`; under RH `L ≥ 0`
(corpus: `xi_laguerre_inequality_of_rh`), so the boundary reflection is causal; the unconditional
status of `L ≥ 0` is open and is *not* used anywhere above.

**Wall corollary (for the parent card).** RH ⟺ `λ_c` has no poles in the open strip
`0 < Re w < 1/2` (zeros of `ξc′ + c·ξc`); both strip boundaries carry unconditional modulus
control (≤ 1 on `Re = 1/2` by C(i); = 1 on `Re = 0` by C(ii)); by the maximum principle the ONLY
failure mode of global domination is an actual strip pole. Equivalently: for every `c > 0` the
tilted derivative `(e^{cw} ξc(w))′` is zero-free on `0 < Re w < 1/2` ⟺ RH (the `c → 0⁺`
degeneration is the Speiser-type derivative criterion).

## Paper proof

**A.** Expand: `a₊(w)conj a₊(v) = F′(w)F̄′(v) + cF′(w)F̄(v) + cF(w)F̄′(v) + c²F(w)F̄(v)` and
`a₋(w)conj a₋(v) = F′(w)F̄′(v) − cF′(w)F̄(v) − cF(w)F̄′(v) + c²F(w)F̄(v)`, where `F̄(v)` denotes
`conj(F(v))` (legitimate since the identity is pure sesquilinear algebra; no reality is used).
Subtract: the diagonal terms cancel, leaving `2c[F′(w)F̄(v) + F(w)F̄′(v)]`. Divide by
`(w + v̄) ≠ 0` and factor `a₊(w)conj a₊(v)` on the left. ∎

**A1.** Congruence `M ↦ D*MD` with `D = diag(a₊(w_j))` invertible preserves and reflects PSD. ∎

**A2.** `n = 1` in A: `2c(w+w̄)B(w,w̄) = |a₊(w)|²(1 − |λ_c(w)|²)`; and
`|a₊|² − |a₋|² = 4c·Re(F′ conj F)`. Since `w + w̄ > 0` on the node domain and `c > 0`, the three
conditions are equivalent; the last rewrite divides by `|F(w)|² > 0`. ∎

**B.** (ii) ⟺ (iii): Pick's theorem on the half-plane `Re w > 0` with the Szegő kernel
`1/(w+v̄)`: PSD of all finite Pick matrices at nodes in a set with an accumulation point in the
domain ⟺ existence of a Schur-class extension to the whole half-plane; nodes range over the open
half-plane `Re w > 1/2` which accumulates in `Re w > 0`, and `λ_c` is already holomorphic where
`a₊ ≠ 0`, hence the extension agrees with `λ_c` by uniqueness of analytic continuation wherever
both are defined. (iii) ⟺ (iv): Cayley: `|λ_c| ≤ 1 ⟺ Re(F′/F) ≥ 0` pointwise where defined
(A2), and a Schur extension across the `a₊`-zeros forces those zeros to be removable for `λ_c` or
on the boundary; conversely `Re(F′/F) ≥ 0` on `Re > 0` makes `λ_c` Schur directly. (iv) ⟺ (i):
Hadamard for the even genus-one entire `ξc` gives, with zeros paired `±ρc`,
`ξc′/ξc(w) = Σ_pairs [1/(w−ρc) + 1/(w+ρc)]` (locally uniformly). Under RH every `ρc = iγ`, and
`Re[1/(w−iγ)] = Re w/|w−iγ|² > 0` for `Re w > 0`; summing gives (iv). If RH fails, pick `ρc`
with `Re ρc ∈ (0, 1/2)`; as `w → ρc` inside the half-plane, the single term `m/(w−ρc)`
dominates and takes negative real values, violating (iv). Finally (i) ⟹ (ii) is the corpus
receiver (`riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`) plus A1, and (ii) ⟹
(iv) via A2 on rank-one packets and continuity, closing the cycle. ∎

**C(i).** For `Re w ≥ 1/2`: every zero of `ξc` has `Re ρc ∈ (−1/2, 1/2)` — the open inclusion at
the endpoints is exactly the zero-free line `ζ(1+it) ≠ 0` transported by the functional
equation. Then in the paired Hadamard sum both `Re(w − ρc) > 0` and `Re(w + ρc) > 0`, so each
pair has strictly positive real part, hence `Re(F′/F)(w) > 0`, hence `|λ_c(w)| < 1` by A2's
pointwise identity (note `F(w) ≠ 0` on `Re w ≥ 1/2` for the same reason). ∎

**C(ii).** `ξc` is even with real Taylor coefficients, so on `w = iτ`: `ξc(iτ) = Ξ(τ) ∈ ℝ` and
`ξc′(iτ) = −i·Ξ′(τ) ∈ iℝ`. Thus `a±(iτ) = −iΞ′ ± cΞ` and `|a₊(iτ)|² = Ξ′² + c²Ξ² = |a₋(iτ)|²`. ∎

**C(iii).** `λ_c(iτ) = −(cΞ + iΞ′)/(cΞ − iΞ′)`, so `arg λ_c = π − 2 arg(cΞ − iΞ′)` and
`d/dτ arg(cΞ − iΞ′) = Im[(cΞ′ − iΞ″)·conj(cΞ − iΞ′)]/|cΞ − iΞ′|² = c(Ξ′² − ΞΞ″)/|cΞ − iΞ′|²`. ∎

**Wall corollary.** Given C(i)+C(ii), `λ_c` is holomorphic on the closed strip minus the
`a₊`-zeros, with `|λ_c| ≤ 1` on both boundary lines and Phragmén–Lindelöf-admissible growth
(order one of `ξc`); the maximum principle then bounds `|λ_c| ≤ 1` on the strip iff no poles
occur there; poles are zeros of `a₊ = e^{−cw}(e^{cw}ξc)′·`-normalization. RH ⟺ no such zeros by
B(iv) (a strip value `ξc′/ξc = −c < 0` violates positivity; conversely positivity forbids
negative real values). ∎

## Honest review notes (pre-promotion checklist)

1. B uses classical half-plane Pick (corpus owns Nevanlinna–Pick: `nevanlinna-pick-built`);
   the removability discussion at `a₊`-zeros should be spelled out in the Lean version by
   avoiding division: state everything multiplicatively (as in A) — done in the Lean scope below.
2. C(i) inputs: Hadamard pairing for ξc (corpus: order-one Hadamard stack) and the zero-free
   line (corpus: PNTPlus). Both must be wired explicitly when C(i) is formalized.
3. The `[REDISCOVERED]` flag for B(iv) ⟺ RH: Lagarias, "On a positivity property of the
   Riemann ξ-function" (1999-era) — cite precisely at promotion; Speiser (1935) and
   Levinson–Montgomery (1974) for the wall corollary's `c → 0` degeneration.
4. Nothing here is a producer: every RH-equivalent statement is labeled receiver; the new
   content is the exact congruence + channel identification + lossless-boundary layer.

## Lean scope (this cycle)

Core algebra, unconditional and division-free: Theorem A as a sesquilinear identity; A1 as a
matrix congruence statement; A2 in multiplicative form
`2c·(w+w̄)·B(w,w̄) = |a₊(w)|² − |a₋(w)|²` and `|a₊|² − |a₋|² = 4c·Re(F′(w)·conj(F(w)))`.
Follow-ups (separate cards): B with corpus Pick assets; C(i) with Hadamard + zero-free line.

## Post-audit correction and Lean status (2026-08-28)

**Novelty correction after deep corpus audit** (the corpus is ahead of the external SOTA here):
the Carathéodory-form of Theorem B was already corpus-owned —
`riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel` (`XiEulerSafeCauchyLoss`),
`xiCentBezoutian_eq_mul_criticalKernel`, and the theta-source weld
`sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel`
(`ThetaCuspTiltFluxObservabilityWeld`) already implement "Bezoutian PSD ⟺ log-derivative
Carathéodory kernel PSD" on the safe half-plane `Re > 1/2`. The `[REDISCOVERED]` flag for the
criterion content therefore applies against the corpus itself, not only Lagarias. What remains
new from this card and is now **Lean-proved unconditionally**
(`RHTower/ThetaTailKreinXiCentTiltCollapse.lean`, axioms: propext/Classical.choice/Quot.sound):

1. `thetaTailKrein{Plus,Minus}Transform_eq_exp_mul_tilt` — the literal two-Volterra channels
   collapse to `e^{−ws}·(ξc′ ± c·ξc)`: the frame-diagonal structure of the domination problem.
2. `xiCentTilt_mul_sub_eq_bezoutianNumerator` and `two_mul_add_mul_xiCentBezoutian_eq_tilt` —
   the division-free, hypothesis-free, all-plane (strip-covering, antidiagonal-including) tilt
   form of the Bezoutian; the corpus's prior factorization required `Re > 1/2`.
3. `xiCentTiltMinus_I_mul_eq_neg_conj` and `norm_xiCentTiltMinus_I_mul` — the lossless critical
   boundary: `tilt₋ = −conj(tilt₊)` on `Re w = 0`. New consequence recorded: a pole of `λ_c` on
   the critical line would force a double zero of `ξc` there; the `c`-trajectories of
   `(e^{cw}ξc)′`-zeros cannot touch the line unless a double zero occurs.
4. Boundary phase law `d/dτ arg λ_c(iτ) = −2c·(Ξ′²−ΞΞ″)/|cΞ−iΞ′|²`: causality ⟺ pointwise
   Laguerre inequality (corpus owns it under RH only; unconditional status open, weaker than RH).

Stage stays 1-in-progress for Theorems B/C(i) (Lean pending on corpus Pick + Hadamard/zero-free
inputs); the four items above are the promotable core.
