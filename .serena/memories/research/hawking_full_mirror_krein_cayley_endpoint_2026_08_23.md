# Hawking full-mirror Krein--Cayley endpoint (2026-08-23)

## Result
Added `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorKreinCayleyEndpoint.lean` and wired it into `formal/GaloisForLFunctions/RHTower.lean`.

Ordinary sectorwise SU(2) Cayley/full Davies--Fulling mirror equality remains falsified by the existing even second coupling jet. Correct full-amplitude completion is the SU(1,1) Krein--Cayley chart of the actual bosonic Bogoliubov block.

For exact pair amplitude beta and positive CCR gain g=sqrt(1+|beta|^2), define chi=beta/(g+1). Lean proves:
- normSq chi = (g-1)/(g+1) < 1;
- g=(1+normSq chi)/(1-normSq chi);
- beta=2 chi/(1-normSq chi);
- chi is unique among open-disk coordinates reproducing actual gain and pair coefficient;
- Krein--Cayley outputs equal literal full-mirror Bogoliubov outputs;
- signed-Hermitian preservation and exact signed-adjoint inverse;
- coordinate nonzero iff full nonlinear Davies--Fulling amplitude nonzero;
- one arbitrarily weak common coupling mixes any countable tilted family unconditionally;
- standard van-Hove disk rate tends to one quarter of existing Bogoliubov pair-rate limit;
- RH iff every noncentral tilted sector has positive Krein--Cayley standard-clock limit rate.

Interpretation: full dynamics does select a canonical Cayley completion, but only in bosonic Krein signature. This resolves completion provenance without proving RH. Finite-coupling all-sector mixing is unconditional. Remaining RH-bearing producer is theta-specific first-order transversality/no delayed onset on common lambda^-2 clock.

## Verification
- Direct target check passed:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingFullMirrorKreinCayleyEndpoint.lean`.
- Targeted module build passed.
- Axiom audits for uniqueness, signed-form preservation, inverse, common mixing, van-Hove limit, and RH equivalence use only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint reports only unrelated umbrella reachability errors; new module is reachable and has no forbidden declaration.
- `docs/reports/endpoints.md` updated from 1771 to 1772 endpoints and includes route summary/catalogue row.
- No git commands used.

## External provenance
Primary arXiv directions audited: Bruneau--Derezinski math-ph/0511069 (bosonic Bogoliubov/symplectic dynamics), Cariolaro--Pierobon 1704.02008 (complex symplectic Gaussian transformations), Butera 2306.03813 (moving-mirror open-system/FDT), Gough math-ph/0511046 (quantum Stratonovich/Wong--Zakai Cayley boundary, relevant contrast).