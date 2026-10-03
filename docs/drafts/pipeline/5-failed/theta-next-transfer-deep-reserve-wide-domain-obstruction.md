# Deep pair-relative reserve: artificial boundary obstruction

- **ID:** TH-next-deep-reserve-domain
- **Stage:** 5-failed (overextended lemma only; route TH remains active)
- **Type:** FALSIFIED, with formalized positive survivor
- **Statement:** The proposed inequality `F_q(bare_d) > Cnext(q) bareMoment(q,d,9)/64` fails on the enlarged domain `q >= 3/2, d >= 8`.

## Exact obstruction
Lean proves the reverse strict inequality at `q=3/2, d=8` in `bareDeepPairRelativeTransfer_artificial_boundary`. The constant shifted coefficient is exactly
`-398543776414562021241793998349132018000172201025/134217728`.
This falsifies the enlarged-domain estimate, not RH or route TH.

## Strongest positive survivor
The same factor 64 works throughout the actual domain `q >= pi-3/2, d >= 8`.
The degree-zero reserve is bounded below by `c0+c1*y` for `y>=0`, where
`c1=8843962935035803044052618947439114695870880636785/16777216`.
This lower bound is positive for `y>=pi-3`; every other gap coefficient is already positive for `y>=0`. Summing the exact finite polynomial proves the bare-atom reserve. Positive atom scaling and the exact convergent atom decomposition yield
`Cnext(q)*D9(q)/64 < F_q(D)`.
The actual coordinate `q(x)=pi*(exp x)^2-3/2` meets this domain for every `x>=0`.

## New insight
The artificial boundary lies below the actual modular source ray. It cannot be used as the universal base point for this lower reserve. The full deep-tail reserve survives unchanged on the source ray; no constant tuning or truncation is needed. A separate exact convolution estimate gives `F_q(D*D) <= 512*Cnext(q)*D0(q)*D9(q)`.

## Proof and Lean status
Dependency-closed symbolic paper proof: affine lower bound, positive gap expansion, positive scaling, convergent summation. Formalized in `ThetaCuspCurvatureDefectGrowthDeepNextReservePolynomial.lean` and `ThetaCuspCurvatureDefectGrowthDeepNextReserve.lean`.
Key endpoints: `deepAtomNextMonomialReserve_zero_affine`, `deepAtomNextMonomialReserve_pos`, `bareDeepPairRelativeTransfer_artificial_boundary`, `source_deepTailPairRelativeTransfer_lower`, `deepPairPairRelativeTransfer_upper`.
Both leaf audits used `lake --old env lean` and exited 0. Scratch axiom audit lists only `propext`, `Classical.choice`, `Quot.sound`. Both leaves wired; no umbrella build.

The complete signed source transfer, C5 compensation, and positivity at every degree remain open.
