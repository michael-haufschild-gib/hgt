# Ritt's implication for every rational map: the c-family route

- **Stage:** 3-formalized (route closed; every target card promoted)
- **Serves:** 04 cards `exact-rational-rg-generation-dichotomy` (general `(1) ⇒ (4)`),
  `gadc-tree-population-rg-clock-hypertranscendence`, `noisy-binary-tree-channel-rg-clock-hypertranscendence`.
- **Why a new route:** Di Vizio–Fernandes (arXiv 2102.08268, §4, proof of `1 ⇒ 2`) conclude
  `τ^{(n)} ∈ K_n` and call it a contradiction with minimality; it is not (Airy).  The corpus log-tower
  descent returns affine obstructions whose inhomogeneities are not tracked (`TowerObstruction` is
  vacuous).  The route below replaces the obstruction bookkeeping by one symmetry.

## Setting
`L ⊇ K = ℂ(t)`, `σ` extends `ψ = (· ∘ R)`, `d ∘ σ = ρ·σ ∘ d`, `ρ = R'`, σ-fixed elements of `L` lie in
`K`, ψ-fixed elements of `K` are constants (deg R ≥ 2).  `στ = qτ`.  `v = dτ/τ` (`σv = ρ⁻¹v`),
`u = dv/v` (`σu = ρ⁻¹u + b₀`, `b₀ = −dρ/ρ²`).  `u` = affine connection of the coordinate `log τ`;
`u + c·v` = connection of `τ^c`; these are exactly the σ-invariant connections in `L`.

## Step 1 (the c-family lemma)
Collapse `u_n = F(u_0..u_{n−1})`, `F ∈ K[X]`, `u_0..u_{n−1}` alg. independent.  For a formal constant
`c`, `E(c) = (u+cv)_n − F(jets of u+cv)` satisfies `σE(c) = ρ^{−(n+1)}E(c)` (tower relations hold for
every invariant connection).  Coefficientwise `E_m v^{−(n+1)}` is σ-fixed ⇒ `E_m = κ_m v^{n+1}`.
Jets of `cv` are `c·v·B_j(u)` (complete Bell: `B_0=1`, `B_{j+1} = D B_j + X_0 B_j`).  So with
`s = cv`: `F + s B_n − F(X + sB(X)) = Σ_m κ_m v^{n+1−m} s^m` (coefficients `P_m(u) = κ_m v^{n+1−m}`).

**Case A (v transcendental over K⟨u⟩):** `F(X+sB) = F + sB_n − κ s^{n+1}` in `K[X][s]`.  `T_s` is
weight-preserving (`w(s)=1`), and a polynomial constant along all lines `X + sB(X)` has zero gradient
(directions `B(Z(s))`, `Z(s)+sB(Z(s)) = X`, have triangular s-coefficients with diagonal `(−1)^k k!`).
Hence `F = F_{n+1} + γ`, `γ ∈ K`.  `F_{n+1} ≠ 0` ⇒ ψ-fixed coefficients (top layer) ⇒ residual with a
constant: n ≥ 2 refuted by the Lie argument (b_n enters only at ν^{n+1}); n = 1: `u' = u²/2 + γ`,
i.e. `S(log τ) = γ ∈ K`; n = 0: `u ∈ K`.
**Case B (v algebraic over K⟨u⟩):** `v^M = Q(u)`, Q polynomial (coprime-denominator argument), and the
same c-trick gives `Q(X+sB) = Q + λ s^M` ⇒ `Q = Q_M + q_0`; top weight ≠ M ⇒ `v^I ∈ K` (Ritt).  M ≤ 2
by rescaled-family Lie argument; M = 1: `u − a = c v`, `a ∈ K` invariant connection; M = 2:
`S(u) = γ + c v²`, `γ ∈ K`.

## Step 2 (global: poles along the backward orbit of the fixed point)
Invariant connection residues: `(r_z+1) = e_z (r_{R z}+1)`; pole orders ≥ 2 propagate backward;
invariant projective connection exponents: `μ_z = e_z μ_{R z}` (double-pole coefficient `(1−μ²)/2`).
The fixed point has infinite backward orbit (R'(0) ≠ 0, deg ≥ 2).  Consequences: A0/A1 impossible;
B: residues rational, simple poles ⇒ `E = v τ^{−c}` has `E^N ∈ K` ⇒ Ritt form `(τ')^N = E^N τ^{N(1+c)}`.
(B with M = 2 still needs its endgame.)

## Global part, refined (orbifold theory on P^1, all algebraic)
Outcome of Step 1 (both cases) is one of: (i) `v^I ∈ K` (Ritt), (ii) some `u_c = u + c v ∈ K`
(invariant affine connection; residue `c − 1` at the fixed point), (iii) some `S(u_c) ∈ K` (invariant
projective connection; exponent `μ = c` at the fixed point, `c² = 2κ`).
Local theory needed at every point of P^1 (∞ via conjugation by `1/x` and functoriality
`(P∘Q)^* = Q^* P^*`): for connections `res_z(P^*a) = e·res_w(a) + e − 1`, pole order ≥ 2 propagates;
for projective connections `c_z = e² c_w + (1 − e²)/2` (`μ_z = e μ_w`), order ≥ 3 propagates.
(ii): residues rational, simple poles ⇒ `N a = g'/g`, `N c ∈ ℤ` ⇒ `τ'^N = C g τ^{N(1−c)}`.
Finite backward orbit ⇒ `R` permutes it with `e = d` (no Riemann–Hurwitz needed) ⇒ exponent 0.
(iii): orbifold covering `μ_z = e_z μ_{R z}`, Riemann–Hurwitz `Σ(1 − μ_p) = 2`, the connection
`a = Σ (μ_p − 1)/(x − p)` is invariant, `γ − (a' − a²/2)` is an invariant quadratic differential
with ≤ simple poles, killed by the fixed-point multiplier (`λ = R'(0)^2` or `R'(0)`), so `γ` comes
from `a` and `u_c − a = c' v` ⇒ case (ii).

## Status
- [x] Lean: `TriangularLineFieldInvariants` (constancy along unitriangular lines),
  `ConnectionBellPolynomials` (jets `v^{(k)} = v·B_k(u)`, unitriangular, weight `k`),
  `RittConnectionShiftSymmetry` (`exists_shift_defect`, `lineSubst_collapse`,
  `coeff_eq_zero_of_lineSubst_collapse`), `RittLogTowerQuasiInvariantResidual`
  (`false_of_scaleInvariant_collapse_const`, `le_one_of_collapse_of_independent_eigen`: Case A ⇒ n ≤ 1).
- [x] Step 1 complete (2026-09-29): `RittJetDenominator` (reduced fractions, eigen-denominator
  `B(u) = k v^W`), `RittLogSeedTranscendentalEigen` (additive rigidity over `K(jets, v)`, algebraic
  elements of a simple transcendental extension, `le_one_of_transcendental_eigen`),
  `RittEigenPowerRigidity` (minpoly/scaleRoots: `v^D ∈ E`; some `v^M` polynomial in the jets),
  `RittEigenPowerLineIdentity` (σ-fixed coefficients of a polynomial in `c`: `Q(x+sB) = Q + κ s^M`
  or Ritt), `RittEigenPowerNormalForm` (weights; `M ≥ 3` impossible via rescaled family +
  unitriangular `z^{k+1}∂`; `M = 1`, `M = 2` forms), `RittLogSeedNormalForm`
  (**`RittFrame.normalForm_of_differentiallyAlgebraic`**: DA `u` ⇒ `v^M ∈ K` ∨ `u + c v ∈ K` ∨
  `du − u²/2 = γ + κ v²`; axioms `[propext, Classical.choice, Quot.sound]`).  All wired in
  `HTGeometry.lean` after `RittLogTowerScaleInvariantRigidity`.
- [x] Phase 2 (2026-09-29): `RationalPolarCalculus` (values, residues, double-pole coefficients,
  pullback laws `s ↦ e·s`, `c ↦ e²c + (1−e²)/2`, pole propagation), `RationalConnectionCharts`
  (functoriality `(P∘Q)^* = Q^*P^*`, inversion chart, order at ∞ = deg den − deg num).
- [x] Phase 3 (2026-09-29): `RationalSphereDynamics` (points `Option K`, charts, `ptImage`, `locRep`,
  `locDeg`; fibre sums `Σ_{R p = w} e_p = deg R`; surjectivity; unique preimage ⇒ `e = d`; finite
  backward-invariant sets are permuted and periodic; chart transport of connections),
  `RationalSimplePoleForms` (partial fractions + residue theorem for forms with simple poles),
  `RationalInvariantConnections` (**`ratCocycle_of_invariant_connection`**: invariant affine connection
  ⇒ simple poles, rational residues ⇒ `N a = g'/g`, `g = κ g(R) R'^N`, `κ λ^{m+N} = 1`),
  `RationalInvariantProjectiveConnections` (**`exists_schConn_of_invariant_projective`**: invariant
  projective connection = `a' − a²/2` with `a` invariant; orbifold exponents `μ ∈ ℚ≥0`,
  `μ_p = e_p μ_{Rp}`, ε-argument via residue theorem + fibre over ∞, quadratic-differential
  rigidity at a fixed point with multiplier not a root of unity).  Axioms clean.
- [x] Frame bridge (2026-09-29): `RittRationalLinearizerCocycle` — `deg ≥ 2 ⇒ R'' ≠ 0, S(R) ≠ 0`;
  `RittFrame.IsRational`; **`ratTransport_of_linearizer`**: DA linearizer in a rational frame ⇒
  `A(R)·R'^N = β·A` (`N ≥ 1`, `β ≠ 0`, `A ≠ 0`), which `treeRG_no_cocycle_interior` refutes.
- [x] Phase 4b: `MeromorphicGermField`, `RittMeromorphicGermFrame` (frame on germs along `𝓝[≠] 0`,
  `fixed` from λ not a root of unity), `RittLinearizerRittForm`, `RittPoincareRittForm` (card 14),
  `RittTreeChannelLinearizer`, `RittTreeChannelClock` (cards 12/13, regimes I and III).
- [x] Parabolic regime: the frame of formal Laurent series (`ParabolicLaurentFrame`), the formal flow
  (`ParabolicFormalFlow`), Boshernitzan–Rubel coherence (`AbelIterateCoherence`,
  `AbelIterateJetRelation`), assembly (`ParabolicAbelHypertranscendence`); card forms in
  `TreeChannelClockRegimes`.  Cards 12, 13 promoted (2026-09-29).
