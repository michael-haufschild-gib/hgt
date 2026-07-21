# Suzuki opposite-shift parity exchange and harmonic zero-fibre recovery

- **ID:** `suzuki-opposite-shift-parity-harmonic-recovery`
- **Stage:** 3-formalized
- **Type:** SOURCE-SEMANTICS CORRECTION / EXACT FRONTIER REDUCTION
- **Scientific status:** `[FORMALIZED] [FULLY PROVEN ON PAPER] [SOURCE-SPECIFIC] [NOVELTY AUDITED] [NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Corollary 1.6 and Sections 7--8.
- **Lean module:**
  `GaloisForLFunctions.RHTower.SuzukiOppositeShiftParityHarmonicRecovery`

## Actual frontier before this card

Suzuki proves that every finite-aperture characteristic function has only real zeros. His RH
corollary still requires identification, after a common entire gauge and a cofinal aperture
limit, with the zero-shift meromorphic reciprocal-logarithmic target

```text
R_0(z)=z^2 XiC(z)/XiC'(z).
```

The corpus has reduced that limit problem to common-gauge parity-pair normality, exact finite
Neumann/exterior continuation, and off-real holomorphy of the corrected exterior channel. It does
not prove any of those producer statements. In particular, Suzuki says that `lambda=0` is the
case motivating his limit formula; he does not identify an arbitrary auxiliary form shift with
the canonical Donoghue carrier.

## Falsification target

The previous handover proposed that a finite cluster at arbitrary

```text
R_eta(z)=z^2 XiC(z)/(XiC'(z)-eta XiC(z))
```

could be reconstructed from the canonical Donoghue anchor after applying an Euler defect. This
conflates two different objects: Suzuki's one-phase characteristic target and the ratio of two
parity phases defining the anchored Donoghue function. It also predicts an odd canonical carrier
for a target which is not odd when `eta != 0`.

## Strongest positive survivor

Centered Xi is even and its derivative is odd. Therefore reflection should exchange, rather than
preserve, opposite shift fibres:

```text
D_eta(-z)=-D_(-eta)(z),
R_eta(-z)=-R_(-eta)(z).                                  (P1)
```

Consequences proved:

1. `R_eta` is an odd meromorphic function if and only if `eta=0`.
2. At every nonzero point away from the Xi divisor, reciprocal coordinates have exact midpoint
   law

   ```text
   z^2/R_eta(z)+z^2/R_(-eta)(z)=2 z^2/R_0(z).            (P2)
   ```

3. Away from poles, the harmonic cross identity

   ```text
   (R_eta+R_(-eta))R_0=2 R_eta R_(-eta)                  (P3)
   ```

   recovers the distinguished zero fibre exactly from a paired nonzero cluster.

Thus `(P1)` kills arbitrary one-fibre parity reconstruction, while `(P2)`--`(P3)` replace the
false route by a source-compatible paired-shift route that does not require `eta -> 0`.

## Scientific-method tests

- **T1 source test:** verify Suzuki's displayed conjectural target is `lambda=0`, and finite
  `lambda<lambda_a` is an auxiliary Hilbert-space shift.
- **T2 corpus test:** verify canonical Donoghue carrier is odd and anchored, but `R_eta` is only a
  one-phase target; search for any existing opposite-shift law.
- **T3 algebra test:** derive `(P1)` directly from `XiC(-z)=XiC(z)` and
  `XiC'(-z)=-XiC'(z)`.
- **T4 rigidity test:** combine `(P1)` with the already formalized reciprocal translation law at
  one unconditional nonzero Xi-regular point to force `eta=0` from oddness.
- **T5 pole test:** state `(P2)` without denominator hypotheses using totalized reciprocal
  coordinates, but require explicit denominator nonvanishing for pointwise `(P3)`.
- **T6 novelty test:** search repository and current primary literature for this Suzuki-specific
  parity exchange and harmonic recovery.
- **T7 formal test:** prove the dependency-closed identities in Lean, inspect axioms, run formal
  lint, then build only the exact module.

## Open core after a successful test

This result does not prove RH. It makes the remaining producer statement honest:

> Construct a common-gauge opposite-shift pair from Suzuki's finite-aperture source and prove its
> corrected exterior continuation converges strongly enough that harmonic fusion commutes with the
> cofinal meromorphic limit. The fused target is then forced to be `R_0`, the target occurring in
> Suzuki's RH corollary.

**Later source correction.** Actual `+eta` and `-eta` finite-aperture constructions use different
resolvents and need not share `W`, `I`, or an entire gauge. The common-channel theorem below
remains a valid special case, not source identification. Its source-compatible replacement is the
distinct-channel cross-sewn product in
`suzuki-opposite-shift-cross-sewn-exterior-product`, which removes all three commonness premises.

## Paper proof

Write

```text
X=XiC(z),   Y=XiC'(z),   N=z^2 X,
D_eta=Y-eta X,           R_eta=N/D_eta,
G_eta=R_eta^(-1)=D_eta/N.                               (P4)
```

Centered functional-equation parity gives `XiC(-z)=XiC(z)` and
`XiC'(-z)=-XiC'(z)`. Hence

```text
D_eta(-z)=-Y-eta X=-(Y+eta X)=-D_(-eta)(z).
```

Since `(-z)^2=z^2`, division by the reflected denominator proves `(P1)`.

If `R_eta` is odd, `(P1)` gives `R_eta(z)=R_(-eta)(z)`. At any nonzero Xi-regular point, the
already-proved reciprocal translation law gives

```text
z^2/R_(-eta)(z)-z^2/R_eta(z)=2 eta.                     (P5)
```

The left side vanishes, so `eta=0`. For the converse, `(P1)` at `eta=0` is exactly oddness.
The Lean proof takes `z=i`; the corpus's unconditional centered zero-free slab proves
`XiC(i)!=0`, so no RH assumption is hidden in the witness.

Apply reciprocal translation once from `eta` to `0` and once from `-eta` to `0`:

```text
z^2/R_0-z^2/R_eta= eta,
z^2/R_0-z^2/R_(-eta)=-eta.
```

Adding proves `(P2)`. At points where all three denominators are nonzero, substitute `(P4)` and
clear denominators. Both sides of `(P3)` become

```text
2 N^2/(Y^2-eta^2 X^2),
```

which proves harmonic recovery.

For the exterior multiplier, addition occurs before any cancellation:

```text
G_eta+G_(-eta)
 =(D_eta+D_(-eta))/N
 =2Y/N
 =2G_0.                                                   (P6)
```

If `E_eta=G_eta W-I` uses one common characteristic factor `W` and finite-interval part `I`, then

```text
E_eta+E_(-eta)=2E_0.                                     (P7)
```

Thus symmetric opposite-shift projection is exactly the zero-shift exterior channel carrying all
Xi poles. Off `z=0` and the Xi divisor, subtraction instead gives

```text
z^2(G_(-eta)-G_eta)=2eta,
z^2(E_(-eta)-E_eta)=2eta W.                              (P8)
```

The antisymmetric channel is Xi-free and also cancels `I`. Equations `(P6)`--`(P8)` are stronger
than target harmonic recovery for the actual corrected exterior frontier: the RH-bearing and
shift-gauge channels split exactly.

Combining `(P7)` with the corpus's exterior pole-tomography equivalence gives the paired capstone:
for one common all-real Suzuki characteristic member and one common entire interval part,

```text
RH
 <=> E_eta+E_(-eta) is analytic at every nonreal point.  (P9)
```

Thus opposite finite shifts are not merely another representation. Their symmetric exterior
channel is an exact RH criterion after source identification, with no `eta -> 0` premise.

## Hostile audit outcome

- [x] **Object-type check:** Suzuki's `W(a,theta;z)` is one entire characteristic member. The
      canonical Donoghue function is a ratio of two parity members. They are not interchangeable.
- [x] **Source normalization check:** Corollary 1.6 displays only the zero-shift target and states
      that the argument is formulated with `lambda=0` in mind. Finite `lambda<lambda_a` is an
      auxiliary form shift whose control may matter; Suzuki does not claim an arbitrary shifted
      Donoghue identification.
- [x] **Parity falsification:** `R_eta(-z)=-R_(-eta)(z)`, so any nonzero fibre fails oddness. The
      previous anchored one-fibre reconstruction claim is false.
- [x] **Anchor scope:** Euler-defect injectivity remains valid for two anchored Donoghue carriers.
      It cannot by itself convert a one-phase target into that carrier.
- [x] **Pole conventions:** `(P2)` uses totalized reciprocal coordinates and needs only `z!=0`,
      `XiC(z)!=0`. Pointwise harmonic cross identity `(P3)` explicitly excludes its three poles.
- [x] **No accidental pole cancellation:** symmetric multiplier projection preserves the complete
      zero-shift Xi pole channel; antisymmetric projection is asserted only off the Xi divisor in
      pointwise Lean form.
- [x] **No RH or computation:** parity, zero-free witness, and all algebraic identities are already
      unconditional in the corpus.

## Novelty audit

- Repository search found the affine pencil, reciprocal translation, exterior multiplier, and
  parity-normalized Donoghue oddness separately, but no opposite-shift reflection, unique-odd
  classifier, harmonic zero-fibre recovery, or symmetric/antisymmetric exterior projection.
- Suzuki arXiv:2606.09096v1 states the zero-shift conjectural limit and auxiliary-shift setup but
  none of `(P1)`--`(P8)`.
- Current exact-phrase and concept searches found general reciprocal-logarithmic and harmonic-mean
  material, but no Suzuki/Xi opposite-shift decomposition.
- Even/odd algebra and harmonic means are standard ingredients. Novelty claim is limited to their
  source-specific synthesis, the falsification of arbitrary one-fibre parity reconstruction, and
  the exact exterior-channel projection.

## Lean status

Formalized declarations:

```text
suzukiShiftedXiDenominator_neg
suzukiShiftedXiTarget_neg
suzukiShiftedXiTarget_odd_iff
suzukiShiftedXiTarget_not_odd
suzukiShiftedXiTarget_opposite_reciprocal_midpoint
suzukiShiftedXiTarget_opposite_harmonic_cross
suzukiShiftedXiMultiplier_opposite_average
suzukiExteriorRemainder_opposite_average
suzukiShiftedXiMultiplier_opposite_difference
suzukiExteriorRemainder_opposite_difference
riemannHypothesis_iff_suzukiExteriorRemainder_opposite_average_analytic_offReal
```

Direct Lean checks of the new module, SOTA ledger, and RHTower umbrella pass. Formal lint passes.
Exact module build passes (`8993/8993`). Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for every new declaration.
