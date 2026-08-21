# ULF-DFPM-4 — Lean certification record

**Card:** `global-regular-inertia-calkin-faithfulness-and-split-formation-conservation-law.md`
**Status:** every theorem of the card is Lean-certified, unconditional and axiom-clean.

## Card result → Lean declaration

| Card | Statement | Lean |
|---|---|---|
| (GRC.1)–(GRC.2) | the depth blocks and their Hilbert sum | `GlobalIndex`, `LpTwo GlobalIndex` |
| (GRC.3) | the block-diagonal charge unitary | `globalShift`, `globalInertiaUnitary`, `globalInertiaCLM`, `globalInertiaDefect` |
| (GRC.4) | `q ↦ U_q` is a group homomorphism | `globalInertiaCLM_comp`, `globalInertiaCLM_zero` |
| (GRC.6)–(GRC.7) | the essential norm of a nonzero charge is two | `globalShift_chains`, `two_le_norm_globalInertiaDefect_sub`, `norm_globalInertiaDefect_le_two` |
| (GRC.5) | the exact Calkin metric on charges | `isGLB_essDist_globalInertiaCLM`, `isGLB_essDist_globalInertiaCLM_self`, `isGLB_essDistSet` |
| Thm 3.1, faithfulness | `ρ_ess` is injective | `globalInertiaCLM_eq_of_isCompactOperator_sub` |
| Thm 3.1 (1)–(5) | zero charge ⟺ zero defect ⟺ compact ⟺ Schatten ⟺ determinant class | `globalInertia_tfae` (via `isCompactOperator_globalInertiaDefect_iff`, `globalInertiaDefect_eq_zero_iff`, `MemSchattenClass.isCompactOperator`, `memSchattenClass_of_hasRankLE`) |
| Cor 3.2, (GRC.8) | compact repair cannot erase charge | `two_le_norm_globalInertiaCLM_sub_sub`, `two_le_essDist_of_ne` |
| (GRC.9) | the two-component packet | `globalInertiaPacket` |
| Thm 4.1, reconstruction | the packet determines `(μ, q)` | `globalInertiaPacket_reconstructs` |
| (GRC.10)–(GRC.11) | the signature is reproduced on formed packets | `globalInertiaSignature`, `globalInertiaSignature_formed` |
| Thm 4.1, conservation | the recovery lift preserves both entries | `globalInertiaSignature_lift_invariant` |
| §5 | reflection neutrality is not selection | `not_isCompactOperator_globalInertiaDefect` |
| Cor 6.1 (1)–(4) | global compact-formation selection, abstract form | `globalInertiaSelection_tfae` |
| Cor 6.1, Euler shell | each condition is equivalent to RH | `riemannHypothesis_tfae_globalInertia` |
| Cor 6.1, faithfulness | the local mark determines the local order | `localFormationCharge_eq_of_isCompactOperator_sub`, `two_le_norm_globalInertiaDefect_sub_of_zetaZero` |

## Modules

| Module | Public declarations |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/GlobalRegularInertiaCalkin.lean` | 25 |
| `formal/GaloisForLFunctions/HTGeometry/GlobalRegularInertiaFusion.lean` | 8 |
| `formal/GaloisForLFunctions/RHTower/GlobalInertiaDivisorSelection.lean` | 3 |

All wired into `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Proof notes

The card proves (GRC.7) by choosing infinitely many odd primes `p ∤ h`, working in the block of
depth `2^{v₂(|h|)+1} p`, extracting exact `(−1)`-eigenvectors and testing against a weakly null
sequence.  The Lean proof reuses the charge-free engine
`HTGeometry.LpReindexCompactDichotomy.two_le_norm_lpReindexDefect_sub`, whose only input is that the
shift admits arbitrarily many pairwise disjoint injective chains of arbitrary length.  Those exist
in the depth-`(m+1)|q| + k + 2` block by the elementary bound `|a − b|·|q| ≤ (m+1)|q| < depth`, so
no valuation, no prime selection and no subsequence extraction is needed; the approximating vectors
have defect norm `√((4m+2)/(m+1)) → 2` and the compact correction is handled by a finite
totally-bounded net.

The Calkin-algebra quotient itself is not constructed: the class of `U_q` is represented by the
operator, and `‖π(U_q) − π(U_{q'})‖` by `IsGLB` of the set of distances to compact operators.  This
is equivalent and avoids importing a quotient C*-algebra.

The charge difference is reduced to a single defect by the factorization
`U_q − U_{q'} = U_{q'} ∘ (U_{q−q'} − I)` together with `‖A ∘ S‖ = ‖S‖` for an isometry `A`
(`norm_comp_isometry`), so the two-separation argument is run only once.

## Verification

* `lake env lean` on all three modules: 0 errors, 0 warnings.
* `#print axioms` over the 36 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, and no added hypotheses.

## Not claimed

The source admission statement of §6 — that the literal pre-zero source forms its complete
root-inertia symmetry in the compactly restricted (or determinant-class) global formation group —
is the card's declared open gate.  Corollary 6.1 is an equivalence, not an RH proof.  Fock
implementability is explicitly outside the card's scope and is not formalized.
