# CCM first-clock prime-entry slope tomography

- **ID:** `ccm-first-clock-prime-entry-slope-tomography`
- **Stage:** `3-formalized/needs-audit`
- **Type:** SOURCE TOMOGRAPHY / POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW BRIDGE] [NO RH CLAIM]`
- **Parent:** `ccm-first-clock-direct-positive-factorization-attack`

## Corpus-wide reason for this target

Whole-HT audit eliminates generic positivity as producer of literal first-clock sign:

- positive prime-log Herglotz carriers cannot be transported to critical weight by any finite
  positive exponential/rational correction;
- raw prime delays are not Herglotz;
- common-aperture operator-Pick mixing preserving Gamma-sewn marginals is impossible;
- critical-Mellin Pick indices grow cofinally;
- finite jets, unpointed hypertranscendence, and divisor-only data do not select orientation; and
- multiplicative positive regularization deletes subleading arithmetic, while source-retaining
  subtraction does not inherit positivity.

The surviving HT mechanism is not positivity but **crease tomography**: hard source apertures retain
arithmetic in one-sided slope defects. Apply it to the literal moving first clock itself.

## Frozen conjecture FCES-1

For `k > 1`, define the active first-clock atom

```text
A_k(L)=criticalMellinAtomWeight(k) * sin((2*pi/L)*log k).
```

At its entry aperture `L=log k`:

```text
A_k(log k)=0,
A_k'(log k)=-2*pi*criticalMellinAtomWeight(k)/log k.
```

Consequently

```text
criticalMellinAtomWeight(k)
  =-(log k)/(2*pi) * A_k'(log k).
```

If `k=p^e`, with `p` prime and `e>=1`, then

```text
A_(p^e)'(log(p^e))=-2*pi/(e*sqrt(p^e)).
```

If `k` is not a prime power, the slope is zero. After restoring the hard entry indicator
`1_(log k <= L)`, the left derivative is zero and the right derivative is the displayed active
slope. Every other atom in a finite hard-entered packet is smooth there, so the packet admits an
exact decomposition into smooth background plus the unique source-marked kink. Extension to the
complete published source additionally needs the Gamma--polar term identified and proved smooth in
the same normalization; that stronger statement is not claimed here.

## Resolution

FCES-1 survives in its dependency-closed finite-packet form. Chain rule gives the displayed slope.
The hard entry indicator is identically zero to the left and equals the active atom to the right;
the atom vanishes at entry, so it is continuous with left slope zero and displayed right slope.
Injectivity of `log` on positive reals isolates `k` from every `j != k`. Hence, in any finite packet
supported on integers greater than one, deleting `k` leaves a function differentiable at `log k`.
The whole packet is exactly that smooth background plus the unique kink atom.

Prime-power specialization cancels the logarithmic mark:

```text
w(p^e) = p^(-e/2)/e,
slope(p^e) = -2*pi*p^(-e/2)/e < 0.
```

Normalization by `-log(k)/(2*pi)` recovers the exact critical-Mellin/von-Mangoldt atom weight.

Formal module and capstones:

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimeEntrySlopeTomography.lean
ccmFirstClockPrimeEntrySlope_recovers_weight
ccmFirstClockPrimeEntrySlope_primePower_neg
ccmFirstClockEnteredPrimePacket_entry_smoothDecomposition
```

## Significance and exact RH frontier

This does not orient the first-clock source and does not prove RH. It gives a source-native inverse:
the one-variable first-clock curve is arithmetically complete, not a lossy RH criterion. Every prime
power inserts a negative slope quantum, while all compensation required for an eventual lower floor
must occur in continuous inter-entry drift plus accumulated old-atom motion. Thus a valid producer
cannot smooth, radially collapse, or finitely regularize away the crease current.

## Falsifiers

1. Chain-rule coefficient differs from `-2*pi*w/log k`.
2. Prime-power simplification leaves a factor `log p` or misses exponent `e`.
3. A different atom enters at same logarithmic aperture.
4. Gamma--polar term has a matching nonsmooth contribution.
5. Exact theorem already occurs in corpus or primary literature.

## Novelty boundary

Jumps of Chebyshev's `psi` at prime powers and recovery of `Lambda(k)` are classical. Corpus audit
found an important analogue in `SuzukiPrimeTangentTomography.lean`: high-clock Suzuki tangent data
also reconstruct prime source weights. It does not state this moving-first-clock entry law or its
finite-packet smooth-background decomposition. Targeted primary-source search found no exact
moving-frequency statement. Classification is therefore conservative: `[CORPUS-NEW BRIDGE]`, not
an external novelty claim. Elementary chain rule and generic kink calculus are not claimed new.

## Gates

- [x] whole-corpus mechanism audit
- [x] exact conjecture frozen before proof
- [x] targeted corpus collision search
- [x] targeted primary-literature search
- [x] dependency-closed paper proof
- [x] hostile audit narrowed overstrong full-source claim to exact finite-packet theorem
- [x] unconditional Lean theorem
- [x] RHTower umbrella wiring and direct Lean check
- [x] final module build and axiom audit
- [x] lint: no forbidden declaration; only unrelated pre-existing HTGeometry umbrella gaps

## Formal audit

- Direct check: `lake env lean GaloisForLFunctions/RHTower/CCM/CCMFirstClockPrimeEntrySlopeTomography.lean`
- Final build: `9262/9262`, successful.
- Axioms for four capstones: exactly `[propext, Classical.choice, Quot.sound]`.
- Formal lint: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` issue in new module. Global lint
  remains nonzero on nine unrelated HTGeometry modules already unreachable from its umbrella.

## New producer constraint

This theorem does not create a lower floor. It sharpens what any producer must explain. Literal
first-clock source has a negative atomic crease invariant carrying the entire prime-power source,
while compensation capable of producing eventual boundedness must live in smooth inter-entry drift
(old-atom motion plus Gamma--polar contribution). Any HT mechanism seeing only a smoothed or
radially collapsed observable has discarded an arithmetic-complete invariant before the sign
problem begins.
