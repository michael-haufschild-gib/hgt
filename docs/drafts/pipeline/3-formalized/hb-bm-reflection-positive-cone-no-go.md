# BM reflected positive-cone no-go

- **ID:** HB-BM-RPC
- **Stage:** 3-formalized
- **Type:** NO-GO + POSITIVE SURVIVOR
- **Source:** `HB-BM3-PPC` functional-equation-odd source-covariance burden
- **Statement:** `[LEAN-PROVED] [NEW] [NO-GO] [POSITIVE SURVIVOR]` On every reflected Xi fibre pair, canonical regular/complementary BM currents admit no nontrivial cancellation by nonnegative real source weights.

## Goal

Test whether Hermitian norm-square source weights can supply functional-equation-odd cancellation
for carrier-normalized HB Peierls incidence. Classify exact surviving source geometry when they
cannot.

This does not prove RH and does not construct augmented retarded/advanced Einstein incidence.

## Gates

- [x] 0 → 1 in-progress: conjecture frozen from corpus open-half-plane momentum and exact current
- [x] 1 → 2 fully-proven: dependency-closed convex-separation proof and hostile audit
- [x] 2 → 3 formalized: exact Lean theorem, targeted build, umbrella wiring, axiom audit
- [ ] 3 → 4 publication-ready: external priority review beyond corpus-specific specialization

## Exact frozen claim

For `q : XiZeroCopy`, let

`lambda(q)=4n+3+2i chi(q)` and `J(q)=-lambda(q)`

be the exact BM complementary exponent and unit-radius regular/complementary current. Corpus
half-strip control gives `0 < Im chi(q) < 1/2`, hence

`Re lambda(q)=4n+3-2 Im chi(q)>0`.

The same holds for `reflect(q)`. Therefore for `a,b : NNReal`,

`a J(q)+b J(reflect(q))=0  iff  a=0 and b=0`.

No premise remains after Xi specialization.

## Complete paper proof

Exact exponent formula gives `Re lambda(q)=4n+3-2 Im chi(q)`. Since `n≥0` and
`Im chi(q)<1/2`, this is strictly positive; applying the same premise-free corpus theorem to the
reflected Xi copy proves the second strict inequality. Exact radial-current evaluation at
`z=1/2` gives `J=-lambda` for both fibres. If their nonnegative weighted sum vanishes, its real
part says

`a Re lambda(q)+b Re lambda(reflect(q))=0`.

Each summand is nonnegative and each coefficient multiplying a nonzero weight is strictly
positive, so both weights vanish. Converse is immediate.

## Hostile review and priority verdict

- Weights are literal `NNReal`; no hidden strict-positivity premise is used.
- Result is stronger than failure of equal-weight cancellation: entire positive cone intersects
  cancellation hyperplane only at its vertex.
- It concerns canonical BM regular/complementary currents, not full augmented Peierls currents.
- Positive-cone separation is elementary convex geometry. Exact BM/Xi reflection specialization
  and its source-incidence consequence were not found in corpus or audited HB/Peierls literature.

Verdict: `[NEW] [NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`; external priority
provisional. Significance is exact removal of a whole physical-source ansatz class.

## No-go closure

- **Killed route:** Hermitian/norm-square/nonnegative reflected source weighting cannot create a
  nonzero FE-odd BM seam.
- **Strongest positive survivor:** both reflected canonical currents lie in one open complex
  half-plane, giving strict positive-cone separation.
- **New insight:** viable Peierls incidence must acquire genuinely complex or sign-indefinite
  orientation before Xi specialization. Carrier magnitude alone cannot supply it.
- **Remaining core:** derive augmented time-oriented retarded/advanced incidence and prove its
  source coefficients carry such orientation from action/support/corner data, then establish the
  exact FE-odd covariance needed by the existing wall receiver.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSecondHarmonicReflectionPositiveConeNoGo.lean`
- Right-half-plane theorem:
  `d4BMXiPlusPlusComplementaryFrobeniusExponent_re_pos`
- Rigidity theorem:
  `d4BMXiReflectionPositiveConeRegularComplementaryCurrent_eq_zero_iff`
- Direct `lake env lean` check passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicReflectionPositiveConeNoGo`
  passed (`11879/11879`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Formal lint remains blocked by unrelated concurrently added sieve modules not yet wired into
  umbrella; theorem module itself passes direct and targeted checks.

## Log

- 2026-08-27 — corpus search exposed open-half-plane exponent control plus exact `J=-lambda` law.
- 2026-08-27 — positive-weight cancellation conjecture disproved; sharp cone-rigidity survivor
  paper-proved and Lean-formalized.
