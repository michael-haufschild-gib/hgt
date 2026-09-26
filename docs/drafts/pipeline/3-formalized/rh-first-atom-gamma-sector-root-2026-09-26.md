# First theta atom: strict Gamma sector in the spectral strip

- **ID:** RH-FIRST-ATOM-GAMMA-SECTOR-ROOT-20260926
- **Owner:** root
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/rh-full-source-sign-root-2026-09-26.md, S6–S7
- **Scope:** a special-function inequality needed to audit one attempted negative packet; not RH.

## Exact theorem

For every complex z with `abs(Im z)<1/2`,

`Re [(z^2+1/4)^2 * Gamma(1/4+i*z/2) * Gamma(1/4-i*z/2)] > 0`.

The same holds after division by `4*sqrt(pi)`. The normalized expression
is `RHTower.thetaCuspAtomGammaPair`; the theorems are
`RHTower.thetaCuspAtomGammaCore_re_pos` and
`RHTower.thetaCuspAtomGammaPair_re_pos` in
`formal/GaloisForLFunctions/RHTower/ThetaCuspAtomGammaSector.lean`.
No assumption on the zeta zeros occurs.

## Dependency-closed proof

Evenness and complex conjugation reduce to z=b+ic, b,c>=0, c<1/2.
Set `a_n=2*n+1/2`, `f(t)=atan(b/t)`, and
`delta_n=f(a_n-c)-f(a_n+c)`.
Both linear factors of
`q_n=(a_n-c+i*b)*(a_n+c-i*b)=z^2+a_n^2`
have positive real part. Their arguments give `arg(q_n)=delta_n>=0`.

For n>=1, `a_n+c<=a_(n+1)-c`. Since f decreases on positive t,

`0<=sum_(n=1..N) delta_n<=f(a_1-c)-f(a_(N+1)-c)`.

Consequently the quotient `q_0/product_(n=1..N) q_n` has argument
between `-M` and `M`, where `M=f(a_0-c)<pi/2`. No branch change occurs:
the denominator argument and the quotient argument are both kept inside
their principal ranges by the displayed bounds.

Put `s_plus=1/4-c/2+i*b/2`, `s_minus=1/4+c/2-i*b/2`.
Euler's Gamma sequence gives the exact finite identity, for N>0,

`q_0^2*GammaSeq(s_plus,N)*GammaSeq(s_minus,N)`
` = N^(1/2)*(N!)^2*4^(N+1) * q_0/product_(n=1..N) q_n`.

The scalar is positive. Thus each finite expression H_N satisfies
`norm(H_N)*cos(M)<=Re(H_N)`. GammaSeq convergence passes this closed
inequality to the limit. That limit is nonzero: q_0 and both Gamma factors
are nonzero, the latter because their arguments have positive real part.
Since cos(M)>0, its real part is strictly positive. Division by the
positive real normalization preserves the conclusion.

## Whole-route consequence and remaining obligation

The paper first-atom transform A satisfies
`A(z)*A(-z)=thetaCuspAtomGammaPair(z)`.
The formal theorem above verifies the explicit Gamma expression, not that
transform identity or the noncompact Weil admission. Once that admission
is proved, the full-line single Mobius packet has positive spectral
contributions even from hypothetical off-line zeros. It therefore cannot
be the desired negative witness.

Finite-tail packets and mixed translates retain an unresolved sign.
No negative full-source packet, unrestricted source positivity, or RH
conclusion has been obtained. The parent route remains in progress.

## Verification

- Scratch proof passes at default proof limits; no numerical experiment.
- Named leaf build passes; leaf wired once in `RHTower.lean`.
- All three public declarations pass the final axiom audit: only
  `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint` exits 0. Existing large-file warnings
  concern other leaves; the new leaf produces no warning.
- Logs: `/tmp/rh-s7-gamma-sector-build.log`,
  `/tmp/rh-s7-final-axioms.log`, `/tmp/rh-s7-lint.log`.
- No literature-priority claim. Corpus deep search supplied no applicable
  existing sector theorem; retrieved candidates were checked for scope.
