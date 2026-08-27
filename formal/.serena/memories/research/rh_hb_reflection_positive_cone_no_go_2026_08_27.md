# HB reflected positive-cone no-go (2026-08-27)

Module `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicReflectionPositiveConeNoGo.lean` proves premise-free on each Xi reflection pair:

- `Re(d4BMPlusPlusComplementaryFrobeniusExponent n chi(q)) > 0`.
- For `a b : NNReal`, the nonnegative weighted sum of exact unit-radius regular/complementary currents at `q` and `xiZeroCopyReflectEquiv q` vanishes iff `a=b=0`.

Mathematical consequence: Hermitian norm-square/probability/nonnegative source weighting cannot produce a nonzero FE-odd HB seam. Actual augmented time-oriented Peierls incidence must generate complex or sign-indefinite orientation before Xi specialization.

Verification: direct `lake env lean` passed; targeted build passed 11879/11879; axiom audit only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired. Card: `docs/drafts/pipeline/3-formalized/hb-bm-reflection-positive-cone-no-go.md`. Active HB and frontier ledgers appended. Formal lint remains blocked by unrelated concurrent unwired sieve modules.