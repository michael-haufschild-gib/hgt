# Arithmetic reconstruction and nonzero remainder refinement

- **ID:** EDQ-REMAINDER-RECONSTRUCTION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [BRIDGE]; no RH implication
- **Source:** [frozen tests, complete paper proofs, and novelty scope](../1-in-progress/euler-deletion-remainder-mobius-inversion.md)

## Exact statements

For `sigma=Re(s)>0`, `s!=1`, define

`R_s(n)=sum_(k=1..n)k^(-s)-zeta(s)-n^(1-s)/(1-s)-n^(-s)/2`,

`W_p=p^(1-s) sum_(n>=1)n^(-s) conjugate(R_s(pn))`.

For every positive integer `m`, the absolutely convergent arithmetic inverse is

`sum_(p>=1)mu(p) W_(mp)/(mp)=m^(-s) conjugate(R_s(m))`.

In particular,

`sum_(p>=1)mu(p) W_p/p=1/2-conjugate(zeta(s))-1/(1-conjugate(s))`.

At a zeta zero this value has norm strictly greater than `1/2`. Therefore

`sum_(p>=1)|W_p/p|>1/2` and `exists p>=1, W_p!=0`.

The actual uniform bound is

`|W_m| <= [|s(s+1)|/(sigma+1)] [sum_(n>=1)n^(-2 sigma-1)] m^(-2 sigma)`.

Consequently `W_m->0`. If also `sigma<=1`, then for each integer `p>1` some positive integer `q` satisfies

`W_(pq)-W_p-p^(2-2 sigma) W_q+p^(2-2 sigma) W_1 != 0`.

This last theorem concerns the literal remainder expression. Interpretation as a component of the earlier infinite mixed decomposition uses that decomposition's domain `1/2<=sigma<1`.

## Lean certificate

Namespace: `RHTower.DeletionMixedRefinement`.

| Claim | Module | Declaration |
|---|---|---|
| Absolutely admitted multiples inversion | `EulerDeletionRemainderMobiusInversion` | `moebius_multiples_inversion` |
| Product-index absolute majorant | same | `summable_norm_weightedPowerRemainder_pair` |
| Reconstruction at every cutoff | same | `infiniteRemainder_moebius_inversion` |
| Outer absolute convergence | same | `summable_norm_infiniteRemainder_div` |
| Explicit reconstructed value | same | `moebius_infiniteRemainder_eq` |
| Zero specialization and strict norm bound | same | `norm_moebius_infiniteRemainder_gt_half_at_zero` |
| Strictly positive absolute mass | same | `remainder_mass_gt_half_at_zero` |
| Uniform modulus bound and decay | `EulerDeletionRemainderRefinementObstruction` | `norm_infiniteRemainder_le`, `tendsto_infiniteRemainder` |
| Decay plus noncontracting refinement forces zero | same | `eq_zero_of_decaying_refinement` |
| Some refinement remains nonzero at every zero | same | `exists_remainder_refinement_ne_zero_at_zero` |

The generic inversion lemma states its absolute-convergence requirement explicitly; the actual arithmetic application proves that requirement. The generic dilation lemma states decay and refinement hypotheses explicitly; the actual obstruction proves decay and the multiplier bound. No missing mathematical input is assumed in these arithmetic conclusions.

## Scope

The positive survivor is exact reconstruction of every ordinary cutoff error, together with quantitative mass and decay. The proposed all-zero annihilation is incompatible with these pointwise zero consequences. No numerical experiment or computational proof certificate is used.

This does not prove that a strict-right contradiction strategy is impossible. An independent arithmetic theorem forcing the displayed refinement to vanish at a hypothetical strict-right zero would contradict the checked nonvanishing theorem. That source theorem remains missing. Nor does this construct an exhaustive classification of zeros or imply that grouping primes partitions the zeros. Generic inversion is already present in the corpus; no literature-wide novelty is claimed.

## Verification

The combined scratch proof and both published sources passed `lake env lean`. Each new leaf passed its serialized final `LEAN_NUM_THREADS=1 lake build --old <module>` audit. Both are wired into `GaloisForLFunctions.RHTower`; no full or umbrella build was run.

A scratch `#print axioms` audit of all 18 public declarations (17 theorems and one definition) reports only `propext`, `Classical.choice`, and `Quot.sound`. The corpus index was regenerated and retrieves the new reconstruction theorem. No owned Lean process remained after the checks.

Global `scripts/formal_tools.py lint --check-generated` failed on unrelated shared-tree modules missing their area-umbrella imports: `RHTower.ChronologicalFermiRepair`, `RHTower.ChronologicalLambertRepair`, `RHTower.ChronologicalRepairCoefficientBoundary`, `HTGeometry.DigammaMittagLeffler`, and `HTGeometry.PerronRationalKernels`. Existing large-file warnings were also reported. Both reconstruction leaves are reachable; the unrelated modules were not edited. Global lint success is not claimed.
