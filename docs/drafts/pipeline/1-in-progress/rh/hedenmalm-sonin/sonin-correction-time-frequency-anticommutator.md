# Sonin projection correction as a time-frequency anticommutator

- **ID:** `sonin-correction-time-frequency-anticommutator`
- **Stage:** 1-in-progress
- **Type:** AUDIO/OPERATOR VALUE RELATION / FORMAL BRIDGE
- **Scientific status:** `[BRIDGE] [CORPUS-USEFUL] [NOT AN RH PROOF]`
- **Physics/audio source:** A. Israel and A. Mayeli, *On the Eigenvalue Distribution of
  Spatio-Spectral Limiting Operators in Higher Dimensions*, arXiv:2301.09616 (limiting operators
  as alternating products of spatial and frequency projections); S. Walters, *Anticommutator
  Norm Formula for Projection Operators*, arXiv:1604.00699.
- **Lean target:** `formal/GaloisForLFunctions/RHTower/SoninTimeBandIdeal.lean`

## Claim

Let `P,R` be the physical and Fourier forbidden projections, `Q` the orthogonal projection onto
their common kernel, and

```text
C = Q - (1-P-R)
```

the existing exact Sonin projection correction.  Then

```text
C^2 + C = PR + RP.
```

## Paper proof

The common-kernel definition gives

```text
P^2=P, R^2=R, Q^2=Q,
PQ=QP=RQ=QR=0.
```

Expanding `(Q-1+P+R)^2+(Q-1+P+R)` and applying precisely those seven relations leaves
`PR+RP`.

## Corpus value

1. Gives the projection correction an exact polynomial normal form, rather than only membership
   in the time-band ideal and Hilbert--Schmidt norm estimates.
2. Connects the correction directly to the anticommutator of the two projections whose
   alternating product is the prolate/time-frequency limiting operator.
3. Supplies an exact replacement rule for later relative-Gram and semilocal-trace manipulations
   involving `centralSoninProjectionCorrection`.
4. The anticommutator identity alone does not control the dilation factors.  The later
   two-projection Pythagorean law reduced the Hilbert--Schmidt energy constant from `80` to `16`;
   the zero-mode-subtracted partition in
   `sonin-zero-mode-subtracted-supersymmetric-partition.md` additionally proves the actual
   correction is a contraction and gives the operator-norm residual bound `≤ 4`.

## Lean surface

- `centralSoninProjectionCorrection_sq_add_self_eq_anticommutator`

## Verification boundary

The proof is exact projection algebra and uses no numerical evidence.  Under the current
no-computation instruction the Lean source has been manually reviewed but not built, linted, or
axiom-audited.  Promotion to stage 3 requires one later targeted file check.

## Gates

- [x] primary time-frequency/operator sources identified
- [x] exact relation proved on paper
- [x] direct existing correction object identified
- [x] Lean source added and manually reviewed
- [ ] targeted Lean verification when computation is permitted
