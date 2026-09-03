# Prime--Hodge Toeplitz-horizon finite-capacity selector

- **ID:** ULF-PHTH-002
- **Stage:** 1-in-progress
- **Parent:** ULF-PHSTH-001
- **Status:** exact two-edge RH successor; neither edge asserted

## 1. Higher-law target

RH should not be selected by comparing unrelated source and divisor energies. Literal integer and
Poisson formation should force the completed theta object to have the same local open-history
displacement as the pre-divisor prime-mixed defect `T`. The difference between any two such
completions is then a Toeplitz horizon. An off-line copy should be exactly a nonzero positive
observer symbol in that horizon. Finite Euler capacity forbids every such symbol because its open
history repeats mass indefinitely.

In one line:

```text
same local defect + positive finite source capacity + open lift of off-line observer => RH.
```

## 2. Checked corpus facts

Searches were run before formulating the successor.

- `PrimeHodgeHistoryIntegralNuclearDefect` and
  `PrimeHodgeHistoryIntegralNuclearHomotopyDefect` prove `T` is pre-divisor, prime-mixed,
  Schatten-one, and integral.
- `PrimeHodgeHistoryFirstExitTransgression` proves curvature/first exit gives exactly that `T`, not
  only its trace.
- ULF-PHSG-001 proves `G=diag(m_n)` and `Phi=diag(w_n)` are forced by the marked Stein system.
- ULF-PHSTH-001 proves `T=G_A-U*G_AU`, classifies every same-defect completion as `G_A+R` with
  Toeplitz `R`, and proves positive finite trace forces `R=0`.
- `EulerStokesApertureCapacity`/ULF-ESAC-001 gives a literal positive prime/depth trace-class
  carrier with trace below `115/108`, plus its singular sixth boundary.
- `DirectSubunitEscapeCapacityFusion` proves source ownership and the current primewise relative
  completion, but its escape energy and source budget remain on different objects.
- `XiWardCubicTranslationEnergySeparator` and
  `XiWardCubicReflectionLoewnerCodiagonalIncidence` give at least one fixed escape quantum for each
  strict-right copy.
- `HedenmalmThetaSignedPolarizationEscape` rules out a fixed theta-metric vanishing correction.
- `RoutePCubicHardyMixedJetLanding` already contains the Cauchy-to-cubic mixed-jet landing; it is
  not the missing law.

## 3. Exact surviving RH chain

Let `mathcal U=U tensor I` and let `T_cap` be the prime-mixed history defect built from the literal
Euler capacity carrier. Construct a pre-divisor anomaly-subtracted completion `X` such that:

```text
(A) X>=0 and Tr X<infinity;
(B) X-mathcal U*Xmathcal U=T_cap;                                     (PHTH.1)
(C) every strict-right copy q supplies p_q>=0, p_q!=0, with
    I tensor p_q <= X-G_cap.                                          (PHTH.2)
```

Then ULF-PHSTH-001 gives `X=G_cap` from `(A)--(B)`, while `(C)` gives
`0<I tensor p_q<=0`, impossible. Hence there is no strict-right zero. Functional-equation symmetry
excludes strict-left zeros; all nontrivial zeros lie on the critical line.

The constant `115/108` is no longer used to amplify a small inequality. Its role is to certify a
finite source-owned trace budget for `X`. Any unconditional finite trace bound would suffice.

## 4. Successor conjecture

**PHTH conjecture.** Literal integer formation and Poisson self-duality canonically produce `X`
and maps `q |-> p_q` satisfying `(PHTH.1)--(PHTH.2)` before a divisor is supplied to the
construction.

This conjecture is intentionally not an object-existence placeholder. It asks for two mechanisms:

1. **same-boundary descent:** Poisson completion commutes with one open-history displacement after
   subtraction of the already proved universal metric anomaly, preserving unsquared Euler
   coefficients;
2. **observer opening:** horizontal grade of a strict-right copy is the positive grade-zero symbol
   whose canonical shift-harmonic lift is `I tensor p_q`.

## 5. Immediate research tests

1. Express ULF-EHGM-001's relative Mellin anomaly on the same history carrier and compute its
   displacement, not its trace.
2. Test whether ULF-ESAC-001's singular sixth boundary intertwines with `U` after the history lift;
   failure at one matrix coefficient kills `(PHTH.1)` for that carrier.
3. Extract the strict-right grade-zero compression from the existing Loewner/cubic landing and
   test positivity before any zero sum or Gram squaring.
4. Verify coefficient fidelity: each prime-power coefficient must remain unsquared through
   same-boundary descent.

## 6. Falsifiers and locks

- `PHTH-F1`: the displacement identity is available only after inserting `q` or its divisor.
- `PHTH-F2`: completion and capacity live on carriers with no source-forced intertwiner preserving
  full operator displacement.
- `PHTH-F3`: anomaly subtraction makes `X` indefinite, so PHSTH-E cannot apply.
- `PHTH-F4`: strict-right landing produces energy but no nonzero positive grade-zero observer.
- `PHTH-F5`: observer lift is not shift harmonic.
- `PHTH-F6`: only scalar traces agree; operator-valued boundaries differ.
- `PHTH-F7`: unsquared Euler coefficients are lost.

Any of `F1--F7` retires this selector. Scalar trace matching, a fitted shared ghost, a
divisor-dependent correction, or another Cauchy jet does not count as progress.

## 7. Lean gate

Do not formalize the conjecture as assumptions. Formalize ULF-PHSTH-001 first, closed and
unconditional, after paper audit. Formalize this card only after `(PHTH.1)` or `(PHTH.2)` has a
dependency-closed paper proof.
