# TG C9.11q — full native prime–polar signed energy

- **Stage:** 3-formalized
- **Route:** TG, joint prime–Gamma relative admission
- **Status:** final leaf audit and all fourteen public axiom queries pass
- **Open parent:** ../1-in-progress/tg-principal-polar-operator-cancellation.md

## Hard question and result

After exact response recovery, can the two opposite dilation directions
conceal an unbounded signed prime–polar source energy? On every actual
time-band Taylor output, their cross term is nonnegative and factors through
one explicit moment. This is now proved for the complete native finite
prime–polar operator, including its continuum integral on full physical L2.

No arithmetic tail bound, cofinal nuclear admission, Gamma completion, Hardy
cubic compatibility, strict sub-unit law or RH proof follows yet.

## Source and paper proof

Write `f_n=soninCutoffMonomial a n`, `lambda=n+1/2`, `U_u=D_exp(u)`.
The corpus's exact ordered overlap gives the full covariance

`<U_u f_n,U_v f_n>=‖f_n‖² exp(-lambda |u-v|)`.

Let mu be a positive measure supported almost everywhere on nonnegative
logarithmic scales, and w any integrable complex weight. Define

`V_+=∫ w(u) U_u f_n dmu(u)`, `V_-=∫ w(u) U_(-u) f_n dmu(u)`,

`m_n=∫ w(u) exp(-lambda u) dmu(u)`.

Strong continuity and the unitary norm bound prove integrability of both
vector integrands. Passing inner products through these Bochner integrals
retains the original complex signs. Simultaneous reflection leaves the
same-direction kernel unchanged, so `‖V_-‖²=‖V_+‖²`. For u,v>=0 the mixed
kernel factors as `‖f_n‖² exp(-lambda u) exp(-lambda v)`. Hence

`<V_+,V_->=‖f_n‖² |m_n|²`,

`‖V_++V_-‖²=2‖V_+‖²+2‖f_n‖² |m_n|²`.

This is equality for the signed source, not an estimate after taking
absolute values of its prime and polar coefficients.

## Literal arithmetic specialization

For every finite prime set P, positive lower logarithmic endpoint b and
arbitrary upper endpoint R, the bounded operators are

`K_± = Σ_(p in P) p^(-1/2) D_(p^(±1))`

`      − ∫_[b,R] (2 cosh(u/2)/u) D_exp(±u) du`.

The interval is a set interval, empty if R<b. The continuum operator is
constructed from its strong vector integral: linearity and a finite L1 norm
bound are proved. It acts on full SoninL2. Its application to f_n is exactly
the finite prime sum minus this same polar integral.

To apply the complex signed-energy theorem without introducing an admission
premise, use the positive measure consisting of the prime Dirac measures
plus restricted Lebesgue measure on `[b,R]`. At each prime log point, set
the weight to its inverse square root; almost everywhere for the continuum,
set it to the negative native polar density. Finite prime support has zero
Lebesgue measure. This representation preserves both original contributions,
and its integrability and positive-logarithm support are proved.

Thus the native operator satisfies

`‖(K_++K_-)f_n‖²=2‖K_+f_n‖²+2‖f_n‖² |m_n(P,b,R)|²`,

where the literal moment is

`m_n(P,b,R)=Σ_(p in P) p^(-1/2) exp(-(n+1/2) log p)`

`             − ∫_[b,R] (2 cosh(u/2)/u) exp(-(n+1/2)u) du`.

Finite prime intervals and matching positive logarithmic endpoints specialize
this to synchronized cutoff increments. Neither direction may be discarded.

## Lean and verification

Leaf: `formal/GaloisForLFunctions/RHTower/SoninPrimePolarSignedEnergy.lean`.
Thirteen public declarations cover the logarithmic covariance, general
complex signed energy, native source and moment, bounded full operator and
its exact energy theorem. The source is wired into `RHTower.lean`.

Final foreground check, 2026-10-02, exit 0 with empty diagnostics:

```
lake --old env lean GaloisForLFunctions/RHTower/SoninPrimePolarSignedEnergy.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninPrimePolarSignedEnergy.olean
```

No full/umbrella build, heartbeat override, numerical experiment, new axiom
or proof hole. Formal lint reports twelve unrelated unwired leaves and no
finding in this module. Public axiom queries are in the separate scratch
file `/tmp/tg-c911q-energy-axioms.lean`.
That foreground `lake --old env lean` audit also exited 0. All thirteen
declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
The index command completed successfully and all thirteen public declarations
appear in `formal/LEAN_API.md`. Owned scratch sources and fragments were
removed; final audit logs and the axiom-query scratch file are retained.

## C9.11r–s follow-up audit

The additional `soninPrimePolarSourceOperator_apply` theorem exposes the
literal formula on every full physical vector. The updated leaf passed its
foreground audit. All fourteen public declarations passed the separate
32-query audit across the four affected leaves in
`/tmp/tg-c911r-axioms.lean`, using only the standard three foundations.
All fourteen are present in the refreshed generated index. Global lint still
reports twelve unrelated unwired leaves and no finding in this module.

## Remaining hard proof

The exact arithmetic cumulative-error formula in the active parent card is
still paper-only. Its positive tail energy must actually tend to zero.
The all-degree resolvent/parity transfer and physical time-band nuclear
control are now proved in P3 `tg-prime-polar-ground-nuclear-transfer`.
Fourier-channel/full-response transport, actual arithmetic decay, Gamma
completion, Hardy compatibility and the strict sub-unit law remain open.
