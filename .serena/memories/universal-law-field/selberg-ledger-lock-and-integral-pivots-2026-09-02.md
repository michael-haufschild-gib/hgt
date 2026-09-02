# 2026-09-02 Selberg ledger lock and higher-mechanism audit

- Lean certificate exists at `formal/GaloisForLFunctions/RHTower/SelbergLedgerCeiling.lean`, wired in `RHTower.lean`.
- Verified with `lake env lean GaloisForLFunctions/RHTower/SelbergLedgerCeiling.lean` and targeted `lake build GaloisForLFunctions.RHTower.SelbergLedgerCeiling`.
- Independent `#print axioms` for seven ceiling theorems plus `petersson_formula_levelOne`: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint` currently fails only on unrelated unwired modules in shared worktree; target module is wired.
- Added GL2 trace-formula hard lock to `docs/drafts/pipeline/1-in-progress/rh-research-status.md`; updated ULF `STATUS.md` through F373/CANNOT-177/FAIL-69.
- GL2 conclusion: Petersson zero-blind; Kuznetsov sees only zero-free-line `|ζ(1+2ir)|⁻²`; Selberg positive ledger Class II, width `1-β₀ < 1/((4/29)|Z|-2)`; automorphic created positivity retired.
- Higher-mechanism failures:
  - faithful wall-torsion module: impossible over universal monodromy ring; after divisor pullback RH-equivalent.
  - ordinary K0/Morita or Big-Witt rapidity quantization: grade-blind or assumes exact missing integral lift. Existing locks: `PrimeIrrationalRotationKZeroRH`, `FrankensteinBigWittIntegralBidirectionalGammaDescent`, `SourceHorizontalGammaSixRelativeReflectionFraming`.
- Next mechanism must derive discrete/integral structure from a source operation that retains oriented boost; completion/Morita equivalence alone cannot.
