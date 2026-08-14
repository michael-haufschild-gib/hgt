# Route U Kelvin--Mellin critical heat phase

- **ID:** `route-u-kelvin-mellin-critical-heat-phase`
- **Stage:** 3-formalized
- **Type:** CONJECTURE ATTACK + EXACT PHASE CLASSIFICATION
- **Parent:** `route-u-kelvin-cross-source-current`
- **Status:** `[PAPER-PROVED] [HOSTILE AUDIT PASSED] [LEAN CLOSED] [AXIOM AUDITED] [NOVELTY: CORPUS BRIDGE]`

## Conjecture--failure--pivot loop

### U-HEAT-ORIENTATION -- Kelvin cross defect has one sign for all heat times

Conjecture: after exact inversion pairing, Gaussian damping orients every cross orbit in same
direction and supplies missing sign.

**Verdict:** `[FALSIFIED]`.  Write `d` for common reciprocal degree, use inner log-radius
`x=a exp(-u)` with `u>0`, and temporarily take source weight `w=1`.  Exact Kelvin defect is

```text
D_(a,d,t)(u)
 = 1 - exp(2*(2d+1)*u - 2*t*a^2*sinh(2u)).               (M.1)
```

It changes sign at unique positive time

```text
t_*(a,d,u)=((2d+1)*u)/(a^2*sinh(2u)).                    (M.2)
```

Precisely

```text
D<0 iff t<t_*,   D=0 iff t=t_*,   D>0 iff t_*<t.         (M.3)
```

Thus heat damping does not provide scale-uniform orientation.  Sign flips at a forced
degree/mass-dependent parabolic phase.

### U-MELLIN-ODD -- expose canonical anti-invariant cross state

Replacement conjecture: remove Kelvin cocycle before asking for sign.  Define

```text
K(x)=(a/x)^(2d) F_0(x),
```

where `F_0` is zero-heat cross polynomial density.  Then

```text
K(a^2/x)=-K(x).                                          (M.4)
```

Equivalently, `H(u)=K(a exp u)` is exactly odd:

```text
H(-u)=-H(u).                                              (M.5)
```

**Verdict:** `[PAPER-PROVED] [LEAN SCRATCH CLOSED]`.

## Dependency-closed proof

Previous Kelvin theorem gives

```text
F_0(a^2/x)=-(a^2/x^2)^(2d)F_0(x).
```

Multiplying left side by `(a/(a^2/x))^(2d)=(x/a)^(2d)` proves `(M.4)` because
`(x/a)*(a^2/x^2)=a/x`.  Substitution `x=a exp u` gives `(M.5)`.

For `x=a exp(-u)`, inversion ratio is `a^2/x^2=exp(2u)` and squared-radius gap is

```text
(a^2/x)^2-x^2=a^2(exp(2u)-exp(-2u))=2a^2 sinh(2u).
```

Substitution in prior arbitrary-weight Kelvin factorization with `w=1` proves `(M.1)`.  Since
`a>0,u>0`, denominator in `(M.2)` is positive.  `Real.exp(s)<1`, `=1`, or `>1` exactly when
`s<0`, `=0`, or `>0`; division by positive `a^2 sinh(2u)` proves `(M.3)`.

## Higher principle

Hard-edge cross polarization is a Mellin-odd state with a heat-driven modular-defect phase
transition.  Earlier sign obstruction is not accidental oscillation: it is failure to first divide
out Kelvin cocycle.  Canonical normalization exposes exact oddness.  Degree and mass enter pure-heat
defect only through critical phase; completed Gamma and prime weights remain outside this theorem.

## Hostile audit

- Threshold classifies **modular weight defect**, not sign of full paired current.  Full current is
  `F_t(x) D_(a,d,t)(u)` and cross density `F_t` can have either sign.
- Physical specialization uses `w=1`.  It does not replace literal Gamma-rate source, polar term, or
  prime Fourier cross term.
- No monotonicity in log-radius, no integrated positivity, and no RH consequence are claimed.
- Algebra closes from previous Kelvin theorem plus positive-domain identities only; no analytic or
  spectral hypothesis is hidden.
- Internal declaration search found no existing theorem with this Kelvin-normalized prime--Gamma
  landing or exact orbit-dependent critical time.  Generic Mellin oddification is treated as
  rediscovered; corpus-specific landing is only claimed as bridge knowledge.

## Significance and next wall

Generic Kelvin/Mellin oddification is `[REDISCOVERED]`; exact common-degree prime--Gamma landing and
critical time `(M.2)` are a corpus-specific `[BRIDGE]`.  This kills every heat-uniform cross-sign
strategy.  Next target must integrate over heat with actual capital weight while retaining Gamma
rate, polar residue, and prime Fourier cross source.  Candidate invariant is signed distribution
of heat mass relative to `t_*`, not pointwise cross energy.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaKelvinMellinCriticalPhase.lean`

- canonical Kelvin-normalized cross density and anti-invariance `(M.4)`;
- exact log-radius oddness `(M.5)`;
- critical heat time positivity `(M.2)`;
- heat defect formula `(M.1)` and sign trichotomy `(M.3)`;
- exact specialization of physical paired current at `x=a exp(-u)`;
- premise-free existence of positive heat times on both orientations for every `a>0,u>0,d`.

## Gates

- [x] `U-HEAT-ORIENTATION` falsified by exact threshold
- [x] `U-MELLIN-ODD` dependency-closed paper proof
- [x] Hostile Lean feedback audit
- [x] Exact Lean formalization and axiom audit

## Formalization audit

- Source: `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaKelvinMellinCriticalPhase.lean`
- Source length: 182 lines.
- Scratch and checked-in source both pass `lake env lean <file>`.
- Exact module `.olean` built directly: 437840 bytes.  No full or umbrella build run.
- Module wired into `formal/GaloisForLFunctions/RHTower.lean`.
- Key theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Targeted scan: no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `#eval`, or `#reduce`.
