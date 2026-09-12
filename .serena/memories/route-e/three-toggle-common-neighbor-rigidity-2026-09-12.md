# Route E three-toggle common-neighbor rigidity (2026-09-12)

Added `formal/GaloisForLFunctions/RHTower/RouteEThreeToggleCommonNeighborRigidity.lean` and wired it into `RHTower.lean`.

Closed finite laws:
- `routeEThreeToggleAdjacent S T := card (S △ T) = 3`.
- `routeE_threeToggle_reverses_moebius`: every distance-three edge reverses Möbius sign on prime supports.
- `routeE_threeToggle_common_neighbor_exact_overlap`: if `T` is distance three from `S,U`, then `card(S△U)=2*card((S△T)∩(S△U))`.
- separation cases exactly `0,2,4,6`.
- at separation six, common neighbors are precisely `S △ A` for 3-subsets `A` of `S△U`, with exact cardinality `Nat.choose 6 3`.

Scientific consequence: source pairs farther than six never collide; distance-six collision is ambient-dimension independent. Any unbounded common-neighbor obstruction lies in distance-two/four clusters. This does not prove Hall. Next hard target is multiplicative-threshold coefficient-one arbitrary-family expansion controlling those clusters and top-shell row loss, with physical interval/seam compatibility.

Docs: `docs/drafts/pipeline/3-formalized/route-e-three-toggle-common-neighbor-rigidity.md`; Route E frontier updated; `MUST-348` added to universal law field.

Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.RouteEThreeToggleCommonNeighborRigidity` passed (8658/8658); `scripts/formal_tools.py lint` passed; capstones depend only on `propext`, `Classical.choice`, `Quot.sound`; no forbidden tokens. No umbrella build. Broad Sep 2026 arXiv analogies: 2609.11606 positive scattering, 2609.08012 tight-tree shadow, 2609.10975 signed switching; none supplies multiplicative-threshold Hall.