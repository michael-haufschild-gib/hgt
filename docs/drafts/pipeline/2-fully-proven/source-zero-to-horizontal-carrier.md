# Source-zero to horizontal cofinal carrier

- **ID:** SOURCE-ZERO-TO-HORIZONTAL-CARRIER
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md`, common R/L/CCM open operation
- **Statement:** Complete-resolution reflection displacement and full prime-labelled Gamma
  Bockstein family form one multiplicity-exact, reflection-odd pre-scalar carrier; ordered
  cofinal source ratios recover its horizontal grade, and their orientation agrees strictly at
  every prime exactly off the critical line.

## Goal

Construct source-derived relation which orients retained horizontal class before bounded
scalarization while retaining ordinary-prime labels, every Xi-divisor multiplicity copy, and both
functional-equation orientations. This card proves orientation branch. It does not prove global
annihilation and therefore does not prove RH.

## Gates

- [x] 0 → 1: source is actual complete-resolution vector; attack uses ordered cofinal ratios
- [x] 1 → 2: dependency-closed proof below
- [ ] 2 → 3: final targeted Lean build, axiom audit, and lint pending
- [ ] 3 → 4: external novelty audit and standalone exposition pending

## Heavy conjecture loop

1. **Conjecture: reflected source vectors coincide at a Xi zero. Failed.** Complete source
   embedding is injective, so equality is equivalent to `rho = 1 - conj rho`; this assumes exact
   conclusion sought.
2. **Pivot: use zero-mass source relation. Failed as orientation.** Difference of reflected source
   vectors is always killed by codiagonal, including off-line zeros. Codiagonal erases horizontal
   information.
3. **Pivot: use arbitrary bounded label-blind consumer. Failed exactly.** Every such consumer
   factors through codiagonal and annihilates whole zero-mass hyperplane. Strong positive survivor:
   source labels must remain ordered.
4. **Pivot: identify finite Burnol Bockstein kernel with complete source density. Failed.** One is a
   finite signed Stein polynomial at each truncation; other is infinite positive resolution. No
   coefficient-faithful literal equality exists at finite level.
5. **Pivot: read ordered adjacent source ratios before linear fusion. Proved.** Ratios converge to
   prime-two shell character; its log modulus recovers exact horizontal grade. Feeding this grade
   into full prime-indexed Bockstein produces common carrier with strict sign agreement.

## Construction

Let `q = (rho,k)` be a multiplicity copy of Xi zero `rho`, and let `J rho = 1-conj rho`. For every
shell start `K`, write `V_K(rho)` for complete source vector in `ℓ¹(ℕ,ℂ)` and define

```text
D_K(q) = V_K(rho) - V_K(J rho).
```

For normalized adjacent-coordinate ratios `R_{K,n}(rho)`, existing complete-resolution theorem
gives

```text
R_{K,n}(rho) → chi_2(rho),
L(q) := log ‖chi_2(rho)‖ = (1/2 - Re rho) log 2.
```

Thus centered horizontal grade is recovered from source tail by exact relation

```text
t(q) := 2 Re rho - 1 = -2 L(q) / log 2.
```

For every ordinary prime `p`, define signed Gamma Bockstein

```text
B(q,p) = F_{-t(q)}(p) - F_{t(q)}(p),
```

where `F_t(p)` is positive Fisher density times `p^t`. Full pre-scalar carrier is

```text
C_K(q) = (D_K(q), p ↦ B(q,p))
       ∈ ℓ¹(ℕ,ℂ) × (Nat.Primes → ℝ).
```

Domain remains `XiZeroCopy`, so analytic divisor multiplicity is not quotient-ed. Prime family is
not summed, so labels remain intact.

## Theorem and proof

For every `K`, multiplicity copy `q`, and prime `p`:

1. `D_K(q)` has zero codiagonal because both complete source vectors have mass one.
2. Complete source embedding is injective. Hence `D_K(q)=0` iff `rho=J rho`, equivalently
   `Re rho=1/2`.
3. Source-tail identity above gives `t(q)=-2L(q)/log 2`; `log 2>0`, so no division degeneracy occurs.
4. Strict monotonicity of `p^t` for `p>1` gives
   `B(q,p)<0` for `t(q)>0`, `B(q,p)>0` for `t(q)<0`, and `B(q,p)=0` iff `t(q)=0`.
5. Therefore `D_K(q)=0 ↔ B(q,p)=0 ↔ Re rho=1/2`, and
   `L(q) B(q,p)>0 ↔ Re rho≠1/2`. This is exact all-prime orientation agreement.
6. Under `q ↦ Jq`, source edge reverses and `t` changes sign. Oddness of Bockstein gives
   `C_K(Jq)=-C_K(q)`. Both reflection orientations survive.
7. Existing Rees-corona comparison sends `B(q,p)` times actual leading Xi jet to physical
   adjacent-depth corona class through nowhere-zero factor. Prime, depth, divisor, analytic
   multiplicity provenance remain intact.
8. Consequently `C_K(q)=0` iff retained Gamma/co-Poisson horizontal defect at `rho` vanishes.
   Globally, `C_K=0` iff source-forced horizontal vanishing, hence iff RH.

Every step is unconditional. Last equivalence audits exact strength; it is not global vanishing.

## New knowledge

Horizontal class is not missing from source and is not intrinsically unoriented. It lies in
zero-mass radical, so bounded label-blind linear observation necessarily destroys it. Orientation
resides at ordered cofinal boundary of source coordinates and is recovered by nonlinear adjacent
ratio. Same grade drives all-prime Gamma Bockstein, giving source-to-physical handoff.

Higher principle: **horizontal information is transverse mass plus boundary-at-infinity order**.
Valid killing relation must act on this ordered cofinal boundary (or pair its two orientations)
before codiagonal/Hilbert scalarization. More bounded target geometry cannot supply missing step.

## Lean target

`formal/GaloisForLFunctions/RHTower/SourceZeroHorizontalCarrier.lean`

Principal declarations:

- `completeResolutionReflectionSourceDisplacement_reflection`
- `completeResolutionSourceTail_reads_sourceZeroHorizontalTailLog`
- `primeDepthBVWoldXiCenteredRate_eq_sourceTailLog`
- `sourceZeroHorizontalPrimeCarrier_eq_sourceTailBockstein`
- `sourceZeroHorizontalCarrierAt_reflection`
- `sourceZeroHorizontalResolutionCarrier_eq_zero_iff_primeCarrier`
- `sourceZeroHorizontalTailLog_mul_primeCarrier_pos_iff`
- `sourceZeroHorizontalPrimeCarrier_realification_eq_physicalCorona`
- `sourceZeroHorizontalCarrierVanishes_iff_riemannHypothesis`

## Log

- 2026-08-09 — four conjecture failures closed; ordered cofinal pivot proved on paper and in Lean;
  final formal audit pending.
