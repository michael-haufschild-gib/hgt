# Genuine two-sheet completed-Xi contact-seven wall (2026-08-25)

Formalized first inhabited genuinely equivariant cyclic landing chamber.

Files:
- `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetContactSeven.lean`
- `docs/drafts/pipeline/3-formalized/route-p-cubic-genuine-two-sheet-contact-seven.md`
- import added to `formal/GaloisForLFunctions/RHTower.lean`

Result:
- For `f : EquivariantFinitePuiseuxFamily 2 K 2` whose monodromy exchanges sheets 0 and 1, every sphere/one-puncture/unit-Rees completed-Xi cubic landing for the corresponding one-orbit datum forces `7 ≤ contactNumerator(0,1)`.
- Abstract threshold gives only `k≥6`. Genuine order-two equivariance excludes `k=6`: at the attained highest-difference coefficient, `(root⁻¹)^6=1`, so the swap would make the two coefficients equal.
- Constructed explicit canonical primitive-square-root family supported at exponent `7/2`, proved monodromy swaps sheets, contact numerator exactly 7, and landing fibre nonempty (`10<14`). Hence genuine wall `7/2` is sharp.

Important hostile-audit lesson: rejected naive `N=1` multibranch witness because unramified continuation fixes branches and cannot justify one genuine orbit.

Validation:
- direct targeted module elaboration passed;
- `/tmp` axiom audit of exactly six public declarations returned `[propext, Classical.choice, Quot.sound]` for all;
- no umbrella build, global lint, or full build;
- scratch files and temporary two-branch dependency `.olean` removed.

Scope: genuine cyclic formal Puiseux data plus abstract microlocal charge; no global meromorphic connection and no fixed arithmetic source-to-charge map. Frontier map remained read-only; dirty status belongs to concurrent work.

Builds on `mem:research/irregular_stokes_global_single_orbit_contact_phase_diagram_2026_08_25`.