# SC cofinal scalar-unitization dichotomy

- **ID:** SC-CSUD-1
- **Stage:** 2-fully-proven (awaiting move after Lean formalization)
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` route SC; map is read-only
- **Statement:** Every real scalar rescaling of the coefficient-faithful holomorphic SC reservoir that asymptotically restores centered-Xi parity must collapse its normalized central second jet; hence no such scalar spectral-shift family converges compact-open to `XiC / XiC 0`.

## Goal

Close the full scalar spectral-shift/unitization escape class left after the fixed identity-unitization, multiplicative parity, additive parity, scalar-factor, and matrix-equivalence no-gos.  This is source-pure: the family is built only from the actual prime Gamma-Bockstein columns and the universal shared reservoir.  A proof would force any surviving SC route to use genuinely nonscalar additive coupling, a singular moving clock, or a nondeterminantal operator invariant.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact family

For `a : ℕ → ℝ`, let

`Uₘᵃ(z) = det(I + aₘ Rₘ diag(B_{p_i}(z)))`,

where `Rₘ = I - 𝟙𝟙ᵀ`, `i : Fin (m+3)`, and `B_p` is the corpus entire signed prime Gamma-Bockstein.  Since `B_p(0)=0`, every `Uₘᵃ(0)=1` without a target-derived normalizer.

## Conjecture loop

### C1 — cubic parity-rate law

If `Uₘᵃ(1) - Uₘᵃ(-1) → 0`, then `(m+3) |aₘ| → 0`.

Attack: expand the determinant over principal compounds.  At `z=1`, all Bockstein coordinates are `-w_p` with `w_p ≥ 1/3`.  Every odd compound has the same sign.  The complete cubic layer gives

`Uₘᵃ(1) - Uₘᵃ(-1) ≥ 4 * choose(m+3,3) * (aₘ/3)^3`.

For `aₘ > 0` all odd layers are nonnegative; for `aₘ < 0` they are all nonpositive.  Hence the same lower bound holds for the absolute defect with `|aₘ|`.  Thus parity convergence kills every real dimension-scaled scalar coupling.

### C2 — central-jet collapse

If `(m+3) |aₘ| → 0`, then `(Uₘᵃ)''(0) → 0`.

Attack: the singleton compound vanishes because its reservoir coefficient is zero; `B_p(0)=B_p''(0)=0`; only the exterior-square layer survives:

`(Uₘᵃ)''(0) = -2 aₘ² ∑_{i<j} B'_{p_i}(0) B'_{p_j}(0)`.

The neutral prime-log jets tend to zero, so their finite Cesàro means tend to zero.  Combined with `(m+3)aₘ → 0`, the quadratic jet vanishes.

### C3 — compact-open exclusion

Compact-open convergence `Uₘᵃ → XiC / XiC 0` implies C1 because centered Xi is even.  Holomorphic derivative convergence plus C2 then forces the normalized Xi second derivative at zero to vanish, contradicting the corpus identity that it is the negative normalized strictly positive theta second moment.

## Hostile falsification plan

1. Check whether existing variable scalar normalization theorem already contains this family.  Current corpus search found only arbitrary multiplicative scalar factors of the ununitized determinant and fixed/unit parity repairs, not cofinal scalar shifts.
2. Test signed or complex `aₘ`.  Real sign changes do not escape because every odd layer changes sign together.  A genuinely complex phase-changing scale remains a survivor and must be audited separately, not silently claimed dead.
3. Test matrix-valued shifts.  They lie outside the claim and remain the intended SC survivor.
4. Verify cubic count and second-jet formula symbolically, without numerical experiments.

## Paper proof

`[PROVED HERE]` Put `n=m+3` and write `B_i(z)=B_{p_i}(z)`.  At `z=1`, corpus identities give `B_i(1)=-w_i`, where `1/3 ≤ w_i < 1`.  Principal-minor expansion of `I+a_m R_m diag(B_i(z))` gives

`Uₘᵃ(z)=∑_{S⊆Fin n}(1-|S|) a_m^|S| ∏_{i∈S}B_i(z)`.

Subtracting the value at `-z` retains only odd `|S|`.  The `|S|=1` coefficient is zero.  At `z=1`, all remaining odd summands have one sign: positive if `a_m>0`, negative if `a_m<0`.  Therefore

`|Uₘᵃ(1)-Uₘᵃ(-1)| ≥ 4 choose(n,3)(|a_m|/3)^3`.

Since `choose(m+3,3)=(m+3)(m+2)(m+1)/6 ≥ (m+1)^3/6`, parity-defect convergence implies `|a_m|(m+1)→0`, hence `|a_m|(m+3)→0`.

Now set `q_i=2 primeActivationOccupancyFisherDensity(p_i) log p_i`.  The Bockstein is odd, `B_i(0)=B_i''(0)=0`, and `B_i'(0)=-q_i`.  Differentiating the principal-compound expansion twice at zero leaves only the exterior-square layer:

`(Uₘᵃ)''(0)=-2a_m²∑_{i<j}q_iq_j`.

Moreover `q_i→0`: corpus gives Fisher density at most `1/p_i`, and `(log p_i)/p_i→0`.  Cesàro therefore gives `n⁻¹∑_{i<n}q_i→0`.  Consequently

`|(Uₘᵃ)''(0)| ≤ (|a_m|∑_{i<n}q_i)^2 = ((n|a_m|)(n⁻¹∑_{i<n}q_i))² →0`.

If `Uₘᵃ` converged compact-open to `XiC/XiC(0)`, centered-Xi evenness would give parity-defect convergence, hence the collapse above.  Cauchy derivative convergence would force the target's second derivative at zero to vanish.  But the corpus identity

`(XiC/XiC(0))''(0) = -thetaCuspNormalizedEvenMoment(1)`

has strictly positive moment on the right.  Contradiction.  All dependencies are unconditional and pre-divisor until the final target comparison.

## Novelty audit

- **Internal corpus:** no declaration found for scaled/cofinal SC unitization, cubic parity-rate rigidity, or its central-jet consequence.  Nearby results cover fixed `aₘ=1`, parity product/projection, scalar multiplication after determinant, and left/right matrix equivalence.
- **External literature through 2026-08-28:** rank-one matrix-pencil perturbation literature classifies Kronecker/spectral structure, but search found no prime Gamma-Bockstein cofinal parity-rate theorem or RH-facing central-jet collapse.
- **Provisional status:** `[PROVED HERE] [INTERNALLY NOVEL] [EXTERNALLY UNVERIFIED BEYOND TARGETED PRIMARY-SOURCE SEARCH]`.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** real scalar shift parity forces `dimension × |scale| → 0`; the same rate annihilates the only surviving central quadratic compound.
- **Strongest positive survivor:** complex phase-changing scalar shifts and genuinely matrix-valued/singular shifts are not covered.  They must control odd compounds by cross-degree phase cancellation rather than positive scalar damping.
- **New insight:** SC scalar unitization has a cubic-parity/quadratic-curvature incompatibility, not merely the fixed-scale polarity failure already in corpus.
- **Status:** dependency-closed paper proof; Lean formalization next.

## Log

- 2026-08-28 — created directly in Stage 1 after corpus and primary-literature audit; frontier map left unchanged.
- 2026-08-28 — C1 strengthened from nonnegative to arbitrary real scales; C1–C3 proved on paper with no open dependency.
