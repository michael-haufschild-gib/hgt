# CHMD: reflection symmetry of the arithmetic Doob graph; the odd sector detects RH

- **ID:** chmd-odd-sector-criterion-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** CHMD route; continuation of chmd-spectral-riemann-criterion-2026-10-16; corpus input: `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`, the Doob graph construction (`archBase`, `archWeight`, `primeMeasure`, `left`, `right`)
- **Statement:** (1) the edge reflection `σ(t,x) = (t, −x−t)` is measure preserving for the edge measure and `x ↦ −x` for the theta–cosh mass; (2) composition gives isometric involutions `J` of `L²(μ)` and of the completed graph, compatible with the source projection, and the arithmetic resolvent commutes with `J`; (3) for every closed `R`-invariant subspace `V`: `E ≥ 0` on graph vectors with source in `V` ⟺ `R ≤ ½` on `V` ⟺ no eigenvector of `R` in `V` above `½`; (4) `RH ⟺ ⟪Rw,w⟫ ≤ ½‖w‖² for all odd w ⟺ no odd eigenvector of R above ½`; `¬RH ⟺ ∃ odd bound state`; eigenvectors split into even and odd eigenvectors; every primitive bound state forces an odd one.
- **Status:** STATUS MUST-1555. Two leaves (`CHMDReflectionSymmetry`, `CHMDOddSectorCriterion`; 62 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audits clean; `lake build --old` green; wired; index refreshed; global lint clean of proof debt (remaining errors are other agents' unwired `CHMDMass*` modules).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `measurePreserving_edgeReflect_edge`, `resolvent_reflectMass`, `half_bound_on_of_no_eigenvector`, `riemannHypothesis_iff_no_odd_bound_state`, `exists_odd_bound_state_of_primitive_bound_state`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
The spectral Riemann criterion (MUST-1552) lives on the primitive hyperplane, which still contains
the pole directions (`tanh` mode) and the full even sector. The symmetry `x ↦ −x` of the Doob
graph had never been formalized, so no parity reduction was available. Now: the resolvent commutes
with reflection, the odd sector is a closed invariant subspace on which the Weil pole terms are
irrelevant, and the corpus odd criterion lifts to the operator level: RH is exactly the absence of
odd bound states above the essential threshold. The failure of RH is therefore always visible in the
odd sector, halving the problem and removing the polar directions from the picture.

## Paper proof
*Measures.* `w(σ(t,x)) = ω(t)Θ(−x−t)Θ(−x) = w(t,x)` and `Λ(n)n^{−1/2}Θ(−x−log n)Θ(−x) = `prime weight
at `x`; `σ` preserves `(volume|_{(0,∞)}) × volume` (skew product with the fiberwise maps
`x ↦ −x−t`, each Lebesgue-preserving) and maps each prime fiber `{t = log n}` to itself by
`x ↦ −x − log n`. A measure-preserving map fixing a density preserves the weighted measure, so
`σ` preserves `archMeasure`, each `primeMeasure n`, hence their sum.

*Graph reflection.* `J(f, e) = (f∘(−·), −e∘σ)`; the compatibility `e = f(left) − f(right)` a.e.
transports along `σ` using `left∘σ = −right`, `right∘σ = −left`. `J` is an isometric involution
(`‖Jp‖² = ‖f∘(−·)‖² + ‖e∘σ‖²`), `S∘J = J_μ∘S`, and `⟪Jp, q⟫ = ⟪p, Jq⟫`. Riesz uniqueness gives
`Riesz(J_μ w) = J(Riesz w)`, hence `R(J_μ w) = J_μ(R w)`.

*Invariant subspaces.* For closed `R`-invariant `V`, the arguments of MUST-1552 go through verbatim
with "primitive" replaced by "source in `V`": `Riesz w` has source `Rw ∈ V` for `w ∈ V`; weak limits
of sequences in `V` stay in `V = Vᗮᗮ`.

*Odd sector.* `V = ker(J+1)` is closed and `R`-invariant. Under RH the corpus criterion gives
`E ≥ 0` on odd compact tests; the odd projection `Φ(q) = ½(q − Jq)` is continuous, maps a compact
test `compactLift v` to `compactLift(½(v − v(−·)))` (odd, `C²`, compact), and fixes every
odd-source graph vector (`Jp = −p` by source injectivity), so `E ≥ 0` on all odd-source vectors by
density. Conversely `E ≥ 0` on odd compact tests is the corpus criterion. The dictionary then gives
`RH ⟺ R ≤ ½ on V ⟺ no odd eigenvector above ½`.

## Lean modules (namespace `RHTower.CHMDPolar`)
1. `RHTower/CHMDReflectionSymmetry.lean` — `measurePreserving_withDensity_of_invariant`,
   `measurePreserving_neg_volume`, `measurePreserving_neg_sub_volume`, `measurePreserving_neg_mass`,
   `edgeReflect` (+ `left_edgeReflect`, `right_edgeReflect`, involution), `measurePreserving_edgeReflect_archBase`,
   `archWeight_edgeReflect`, `measurePreserving_edgeReflect_arch`, `primeWeight_reflect`,
   `measurePreserving_primeReflect`, `map_edgeReflect_primeMeasure`, `measurePreserving_edgeReflect_edge`,
   `reflectMass`, `reflectEdge`, coeFn lemmas, `reflectMass_reflectMass`, `inner_reflectMass`,
   `reflect_mem_graph`, `reflectGraph`, `reflectGraph_fst/snd`, `reflectGraph_reflectGraph`,
   `reflectGraph_add/smul`, `norm_reflectGraph`, `reflectGraphₗᵢ`, `inner_reflectGraph`,
   `continuous_reflectGraph`, `rieszLift_reflectMass`, `resolvent_reflectMass`, `reflectGraph_compactLift`.
2. `RHTower/CHMDOddSectorCriterion.lean` — `ResolventInvariant`, `half_bound_on_of_energy`,
   `energy_nonneg_on_of_half_bound`, `eq_zero_of_eigenvector_of_half_bound`,
   `exists_eigenvector_mem_of_approx_eigen_above_half`, `half_bound_on_of_no_eigenvector`, `oddOp`,
   `oddSector`, `mem_oddSector`, `isClosed_oddSector`, `resolventInvariant_oddSector`,
   `reflectMass_compactLift_fst`, `compactLift_fst_mem_oddSector`, `oddPart_compactLift`,
   `reflectGraph_eq_neg_of_odd`, `sourceEnergy_compactLift_nonneg_of_rh_odd`, `sourceEnergy_nonneg_of_rh_odd`,
   `riemannHypothesis_of_odd_energy`, `riemannHypothesis_iff_odd_half_bound`,
   `riemannHypothesis_iff_no_odd_bound_state`, `not_riemannHypothesis_iff_exists_odd_bound_state`,
   `oddPart_eigenvector`, `evenPart_eigenvector`, `exists_odd_bound_state_of_primitive_bound_state`.

## Big picture
- The CHMD spectral dictionary now has its symmetry: the arithmetic resolvent is reflection
  symmetric, bound states have definite parity, and the odd ones already decide RH. The polar
  directions (`1`, `tanh`) play no role in the odd criterion.
- Combined laws: odd bound states above `1/2` are finitely degenerate, locally finite (MUST-1551),
  and at most `2·#(off-line zeros)` (MUST-1553, applied to odd orthonormal families, which are
  primitive).

## Next conjectures
1. The even primitive sector also detects RH (needs an even-sector Dirichlet–Poincaré criterion in
   the corpus, or a parity argument on the corpus's zero-side expansion).
2. Odd-sector Birman–Schwinger count with the sharp constant: odd defect functionals pair zeros
   `ρ ↔ ρ̄`, which should cut the factor `2`.
3. Explicit odd bound states from a deep zero (`IsolatedDeepZeroWeilDetection` uses odd tests
   `sinh(δu)(a²−u²)₊^{5/2}` — the natural odd trial function for the Rayleigh quotient of `R`).
