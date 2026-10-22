# BM second-harmonic unsquared-source orientation rigidity

- **ID:** HB-BM-USOR
- **Stage:** 3-formalized
- **Type:** RIGIDITY + NO-GO + EXACT RECEIVER
- **Parent:** HB
- **Statement:** `[LEAN-PROVED] [NEW] [RIGIDITY]` Literal unsquared angular--Einstein source amplitude obeys unique reflected BM cancellation orientation iff Xi point is on critical wall. Its off-wall obstruction is an explicit quartic whose Xi roots are all wall-confined.

## Goal

Test strongest literal source candidate left after Hermitian no-go: retain full complex phase of
angular--Einstein second-harmonic amplitude and compare its reflected coefficient against unique
BM current-cancellation ratio.

## Gates

- [x] 0 → 1 in-progress: unsquared-source conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: exact quartic reduction, root confinement, compatibility classification
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

For seed one, let `A(q)` be literal unsquared polarized source amplitude and
`r_n(q)=-λ_n(q)/λ_n(Jq)`. Then

`A(Jq)=A(q)r_n(q) ↔ Re(q)=1/2`.

Corpus identities give

`λ_n(q)=4n+2+q`, `C(q)=q²(q+2)/8`, `C(Jq)=C(1-q)`.

Off wall, common nonzero angular factor cancels and compatibility cross-multiplies to

`P_n(q)=u²+(56n+46)u+(40n+25)=0`, `u=(2q-1)²`.

Every Xi zero of `P_n` lies on critical wall. Consequently literal unsquared-source reflected
current vanishes exactly on wall; universal vanishing is equivalent to RH.

## Complete paper proof

Exact normalized Mellin identity collapses Gamma/Beta carrier to `a h²`, yielding cubic carrier
polynomial. Functional-equation reflection is `q↦1-q`; exact BM exponent is affine. Clearing its
nonzero reflected denominator and centering at `t=2q-1` gives displayed even quartic in `u=t²`.

Suppose a polynomial root is off wall. Xi height makes `Im t≠0`; off-wall placement makes
`Re t≠0`; hence `Im u=2 Re(t) Im(t)≠0`. Imaginary part of quadratic gives
`2 Re(u)+(56n+46)=0`. Substitution into real part forces
`40n+25 ≥ (56n+46)²/4`, contradicting positivity of
`(56n+46)²-4(40n+25)=3136n²+4992n+2016`.

On critical wall, reflection-invariant angular mixing vanishes on both fibres, so compatibility is
automatic. Off wall, polynomial confinement contradicts assumed placement.

## Hostile review and novelty verdict

- This is stronger than Hermitian no-go: it retains literal unsquared source phase.
- Quartic is not inserted ad hoc; it is exact eliminant of corpus carrier and BM exponent laws.
- It still does not derive full augmented Peierls pairing. It proves literal angular--Einstein source
  amplitude lacks needed response/left-functional phase.
- Primary-source searches on nonlinear harmonics, second-order Teukolsky sources, and conserved QNM
  currents found no analogous quartic reflection-orientation rigidity theorem.

Verdict: centered quartic algebra `[REDISCOVERED]`; coefficient-faithful BM/Xi source-orientation
rigidity `[NEW] [RIGIDITY]`, external priority provisional.

Primary audit: Papadopoulos, arXiv:gr-qc/0104024; Birmingham--Mokhtari,
arXiv:hep-th/0609028; Green et al., arXiv:2210.15935; Spiers--Pound--Moxon,
arXiv:2305.19332; Mitman et al., arXiv:2208.07380.

## No-go closure

- **Exact killing mechanism:** literal carrier reflection ratio solves only wall-confined quartic;
  it cannot equal forced BM cancellation ratio at any off-wall Xi divisor.
- **Strongest positive survivor:** explicit quartic `P_n` and theorem that all its Xi roots lie on
  critical wall.
- **New insight:** remaining producer phase cannot come from angular mixing, normalized Mellin
  carrier, or their norm square. It must enter through global retarded-minus-advanced response,
  augmented boundary pairing, or left-QNM functional.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSecondHarmonicUnsquaredSourceOrientationRigidity.lean`
- Exact exponent coordinate:
  `d4BMXiPlusPlusComplementaryExponent_eq_xi`
- Quartic obstruction and confinement:
  `d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial`,
  `d4BMXiSecondHarmonicUnsquaredSourceOrientationPolynomial_eq_zero_implies`
- Compatibility classification:
  `d4BMXiSecondHarmonicUnsquaredSourceOrientationCompatible_iff`
- Reflected-current classifier and global endpoint:
  `d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff`,
  `forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh`
- Direct `lake env lean` passed.
- Targeted module build passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from exact carrier polynomial, reflection, and exponent laws in corpus.
- 2026-08-27 — quartic confinement and unsquared-source orientation classification proved in Lean.
