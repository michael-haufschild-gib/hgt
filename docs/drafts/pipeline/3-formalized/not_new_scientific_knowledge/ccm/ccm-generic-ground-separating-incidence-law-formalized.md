# Generic ground separating incidence — formalized closure

- **ID:** `ccm-generic-ground-separating-incidence-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-generic-ground-separating-incidence-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.HTGeometry.SeparatingGramLocus` — the abstract separating-locus theory in an
  arbitrary complex inner-product space. Reusable, so it lives in `HTGeometry`.
- `GaloisForLFunctions.RHTower.CCMGenericGroundSeparatingIncidence` — the compressed-shift
  construction of a separating vector and the prime-power label injectivity.

Standing on `RHTower/CCMCompressedShiftIndependence` (the compressed shifts) and the corpus theorem
`GaloisForLFunctions.linearIndependent_log_primes`.

Umbrellas: `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| `(1)`–`(3)` | `gramMatrix`, `separatingGramDet`, `separatingLocus`, `det_gramMatrix_ne_zero_iff` | the separating condition and its Gram determinant characterisation, in any complex inner-product space |
| orthogonality shortcut | `det_gramMatrix_ne_zero_of_orthogonal` | pairwise orthogonal nonzero images are separating |
| openness | `isOpen_separatingLocus`, `continuous_separatingGramDet` | `(3)` is open |
| `(4)` | `gramLinePoly`, `gramLinePoly_eval`, `natDegree_gramLinePoly_le`, `coeff_det_gramLinePoly`, `eval_det_gramLinePoly` | along `x + t x₀` the Gram determinant is the evaluation of a polynomial of degree at most `2(k+1)` whose top coefficient is exactly `Δ_A(x₀)` |
| density | `dense_separatingLocus` | one separating vector makes the locus dense |
| `(19)`–`(20)` | `isClosed_compl_separatingLocus`, `interior_compl_separatingLocus_eq_empty` | the seam is closed with empty interior |
| `(11)`, `(13)` | `linearIndependent_proj_iff` | the projection criterion of section 3 |
| `(18b)`–`(18d)` | `eventually_det_gramMatrix_ne_zero` | Galerkin preservation: separation survives every family of approximations converging to a separating configuration |
| disjoint supports | `integral_conj_mul_eq_zero_of_disjoint`, `linearIndependent_of_disjoint_support` | the mechanism used in section 2 |
| `(7)` | `separatingBump`, `separatingBump_eq_zero_of_notMem`, `separatingBump_zero` | the test vector |
| support law | `compressedShift_separatingBump_eq_zero`, `compressedShift_separatingBump_apply` | `T_(A,h)x₀` is carried in `[h, h+ε]` and is nonzero at the label |
| `(8)` | `separatingChannels`, `channelWindow`, `separatingChannels_eq_zero_of_notMem`, `channelWindow_unique`, `linearIndependent_separatingChannels` | the bump together with its compressed shifts is linearly independent whenever the labels are separated by more than the bump width and bounded away from the origin |
| `(10f)` | `primePowerLabel_inj` | `m log p = ℓ log q` with `m, ℓ ≥ 1` forces `p = q` and `m = ℓ`, from rational independence of the prime logarithms — the unique-factorization step making the prime and prime-ray labels distinct |

## Axioms

`#print axioms` on all 26 declarations of the two modules returns exactly
`[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

- The Kato response formula `(16)`, which is the content of
  `ccm-prime-source-ground-incidence-response.md`.
- Injectivity of the compact-support Mellin transform, used in `(18)`.
- The simple-isolated-ground-state hypotheses of section 4, and the card's own open gate: excluding
  the seam for the true source-selected ground state.

## Verification performed

- `lake env lean` on both modules: no errors, no warnings.
- `lake build` of each: success.
- `#print axioms` on every theorem: clean.
- Umbrella imports added for both modules.
