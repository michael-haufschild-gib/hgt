# Vinogradov–Korobov bound for the completed Suzuki residual

- **ID:** suzuki-residual-vinogradov-korobov
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Π49.
- **Statement:** For the literal completed Abel source `A_N`, some `C > 0` gives
  `|A_N| ≤ C√N exp(−κ Q(N)/54)` eventually, where
  `Q(N)=(log N)^(3/5)(log log N)^(−5/3)` and `κ=1/(12·10⁸)`.

## Derivation

**[PROVED HERE]**

Set `q(h)=e^(−h)(ψ(e^h)−e^h)`. The corpus gives a global bound `|q|≤M`
and the VK bound `|q(h)|≤B exp(−κQ(e^h)/24)` for sufficiently large `h`.
The exact completed resolvent satisfies

`e^(−h/2)R(h)=∫₀^∞ e^(−3t/2)q(h−t)dt`.

Write `S=κQ(e^h)/54`. For sufficiently large `h`, `S≤h/2`.
If `0≤t≤h/2`, the power-scale comparison gives
`Q(e^(h−t))≥(4/9)Q(e^h)`, so the integrand's absolute value is at most
`B e^(−S)e^(−t/2)`. If `t>h/2`, use the global bound and `S≤t`
to obtain `M e^(−S)e^(−t/2)`. Integration gives
`|R(h)|≤2(B+M)e^(h/2−S)`.

At `h=log N`, the completed outgoing charge is `R(h)/2`.
The literal completed Abel source differs from this by the uniformly bounded
polar and archimedean corrections. Since `e^(h/2−S)≥1` eventually, those
corrections are absorbed in the same bound.

The prime outgoing charge `P_N` satisfies `P_N/√N→1/3`, hence
`P_N≥√N/6` eventually. The exact energy ratio is `(A_N/P_N)²`, so

`0≤E_completed(N)/E_core(N)≤36C² exp(−κQ(N)/27)`.

Thus the canonical signed correction leaves at most this fraction of the
original energy. The argument retains the literal completed source throughout.

## Novelty and boundary

Existing source results give `A_N=o(√N)` and exponent laws involving the
unknown zero abscissa. This estimate supplies a VK rate for the signed
residual itself. Uniform boundedness of `A_N` remains open.

## Verification

- [x] Exact source and dependency-closed paper argument identified.
- [x] Lean formalization and direct-file axiom audit.

Module: `ArithmeticCompensationTheory/SuzukiResidualVinogradovKorobov.lean`.

- `exists_abs_criticalResolvent_le_vinogradovKorobov`: real-aperture resolvent bound.
- `exists_abs_suzukiCompletedAbelSource_le_vinogradovKorobov`: literal Abel-source bound.
- `exists_suzukiCompletedEnergy_ratio_le_vinogradovKorobov`: completed/core energy ratio.

Direct audit: `lake --old env lean GaloisForLFunctions/ArithmeticCompensationTheory/SuzukiResidualVinogradovKorobov.lean`
passed. All three declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
Wired into `ArithmeticCompensationTheory.lean`; no umbrella build.
