Exact arithmetic reduction formalized in `formal/GaloisForLFunctions/RHTower/XiSquarefreePoleUnitRootReduction.lean`, wired into `RHTower.lean`.

Definitions/results:
- `xiSquarefreePoleComplement(s) = (s/2 * Gamma_R(s)) * zeta(2s)`.
- Complement analytic and nowhere zero on `rightHalf`.
- Exact factorization `xi = xiSquarefreePoleComplement * squarefreeMobiusCriticalPoleUnit` on `rightHalf`, where pole unit is `zetaResidueUnit(s)/zeta(2s)`.
- Pole unit analytic on `rightHalf`.
- `analyticOrderAt poleUnit s = analyticOrderAt xi s` for every `s in rightHalf`.
- Complement has unconditional analytic square root by simply connectedness.
- Therefore Xi admits right-half analytic sqrt iff pole unit does.
- `RHLadder 1` iff pole unit admits right-half analytic sqrt.

Interpretation: exact target is single-valued analytic sqrt of pole-cleared squarefree arithmetic carrier. Naive `exp(primeZeta/2)` is circular: prime-zeta continuation has logarithmic branch points at zeta zeros, and its half-exponential monodromy is exactly multiplicity parity.

Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.XiSquarefreePoleUnitRootReduction` passed; axiom audit for all public theorems only `propext`, `Classical.choice`, `Quot.sound`. Formal lint still fails only due pre-existing unrelated unreachable modules. Exact g remains open.