# CLG/TTF effective compensated odd tail

RH remains unproved; goal stays active. This continues `mem:rh_frontier/clg_ttf_explicit_compact_odd_compensation_2026_09_07`.

## Exact result
For q = π exp(2x), first atom φ, complete native odd determinant H, leading minor Δ > 0, and G = 3Φ² + 2xΦΦ′:
- On q ≥ 30, for every 0 ≤ C ≤ 3e9, (H+CΔG)/(φ⁶q⁹) ≥ 2e10 > 0.
- x ≥ 6/5 implies q ≥ 30.
- Canonical K* ∈ (1e9,3e9) is positive on [0,137/2000] ∪ [6/5,∞).
- Corrected weighted odd determinant is positive for every a>0 on r≥12/5 (prior compact r≤137/1000).
- Fixed gap (137/2000,6/5), global mixed rank six, and all-order hierarchy remain unproved.

## Source estimates
ε = exp(-3(q-π))/399.
On q≥m+n+6: |CoolingJet n m| ≤ (8q)^n (3q)^m ε.
On q≥n+3: |φ^(n)| ≤ 3(4q)^n φ.
On q≥n+6, x>0: |Φ^(n)-φ^(n)| ≤ 3(12q)^n ε φ.
Reflected error /φ² ≤ 18(16q)^n ε+9(24q)^n ε² ≤27(24q)^n ε.
On q≥30: q⁵ε≤1e-30, and |A_k-B_k|≤1e-10 for every k≤5, with A_k=(-1)^k j_(2k)/(φ²q^k).
Exact first-atom rational profiles at u=1/q have common denominator (4-6u)².
First-atom odd determinant ≥5e10. Both tuples bounded by 2e8; generic determinant Lipschitz estimate 18 M² δ gives error≤72e6.
Hence H/(φ⁶q⁹)≥49e9, 0<Δ/(φ⁴q⁴)≤1e5.
Sharp first slope |φ′|≤2qφ; full Φ≤2φ and |Φ′|≤3qφ. Since 6x≤q, G/(φ²q⁵)≥-2/30³.
These imply the compensated reserve.

## Modules
11 new modules, 60 public declarations, 1291 source lines, largest203.
HTGeometry: FirstAtomOddTailAlgebra (ROOT namespace HTGeometry), HankelThreePerturbation.
RHTower: ThetaCuspEffectiveLikelihoodCooling, ThetaCuspEffectiveFirstAtomJets, ThetaCuspEffectiveSourceApproximation, ThetaCuspEffectiveReflectionApproximation, ThetaCuspEffectiveTailScale, ThetaCuspEffectiveFirstAtomProfiles, ThetaCuspEffectiveOddDeterminant, ThetaCuspEffectiveCompensationSource, ThetaCuspEffectiveCompensatedTail.
All passed targeted foreground lake env lean scratch checks, one process at a time; identical sources copied to production, needed oleans retained; imports wired exactly once. No umbrella/full build. Formal lint passed.
Only four NEW capstones audited: reflected single-scale error, effective normalized compensated lower bound, canonical positivity outside gap, weighted effective tail. All only propext/Classical.choice/Quot.sound. Do not re-audit these or old corpus in next turn.

## Current docs
Stage3: docs/drafts/pipeline/3-formalized/clg-ttf-effective-compensated-odd-tail.md.
Stage1 target: docs/drafts/pipeline/1-in-progress/clg-ttf-center-integration-compensation.md.
Current frontier CLG segment, TCD status, universal whole-integration-domain rule, and compact proof cross-reference updated.
No commits. Owned /tmp/clg_effective_stage and eight scratch/probe/generator/audit files were removed; no owned Lean/Lake process remains. Many unrelated tasks edit shared tree; preserve their changes.

## Lean details
Use formal cwd. Import baseline for RHTower needs -M8192.
abs_sub_le has three arguments: |a-c|≤|a-b|+|b-c|.
Use inv_le_iff_one_le_mul₀, not inv_le_iff₀.
le_div_iff₀ for lower bound on a quotient; div_le_iff₀ for upper.
For linarith on 1/q^n versus 2/q^n, simp only [div_eq_mul_inv] first.
field_simp often closes completely; subsequent ring can be no-op.
pow_lt_pow_left₀ final arg exponent≠0, not 0<exponent.
No source computations supply Lean premises; all numeric coefficients are verified symbolic identities/order arguments.
