Closed axiom-free nonarchimedean local Brauer isomorphism and immediate RH-route obstruction.

Key theorem: `nonarchimedeanLocalBrauerGroupAddEquivRatModInt` in `formal/GaloisForLFunctions/HTGeometry/ABHN/NonarchimedeanLocalBrauerInvariant.lean`, giving `BrauerGroup F ≃+ RatModInt` for complete locally compact ultrametric nontrivially normed fields.

Proof chain: unramified root-lift embeddings under degree divisibility; nested cyclic Brauer subgroups; explicit factorial slices `S_n ≃ ZMod ((n+1)!)`; `⨆ n, S_n = ⊤`; unit adjustment normalizes adjacent cyclic coordinates; generic successor-to-all-level compatibility; directed-union gluing; source exhaustion gives injectivity and target torsion exhaustion gives surjectivity.

New modules: `CyclicSubgroupCompatibleCoordinates.lean`, `NonarchimedeanLocalBrauerCompatibleCoordinates.lean`, `NonarchimedeanLocalBrauerInvariant.lean`; earlier supporting modules are wired into `HTGeometry.lean`.

Unconditional Connes/Tate consequence in `formal/GaloisForLFunctions/RHTower/CCMRationalAdelicLocalBrauerObstruction.lean`: every additive `BrauerGroup(Q_p) →+ C` map is zero and cannot equal the nonzero Tate local zeta or Connes local Weil term for `Re(s)>0`. This kills direct additive ABHN→analytic-local-term landing; future RH use must be nonlinear (finite torsion character/twist/pairing) or use global reciprocity structure.

Targeted source checks and leaf builds passed. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py lint` still fails only on unrelated pre-existing unreachable modules. No umbrella builds. Scratch files cleaned; no owned Lean processes remain.