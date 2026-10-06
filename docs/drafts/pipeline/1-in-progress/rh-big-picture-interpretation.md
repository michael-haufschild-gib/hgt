# RH: the big picture of what the corpus has proven, and what it implies

- **ID:** rh-big-picture-interpretation
- **Stage:** 1-in-progress (living synthesis; read at the start of every RH cycle)
- **Sources:** STATUS.md (474 MUST / 221 CANNOT), rh-current-frontier-map.md (16 routes, 23 candidates),
  rh-killed-routes.md (27 retired routes, 101 class kills, 477 scoped mechanisms),
  cross-route-producer-synthesis.md (positivity sources P1–P10), krein-producer-loops.md (L1–L405),
  terminal-classification-two-doors (ULF-TERM-001), f1-object-forced-shape (ULF-F1-003),
  rh-goal-loop-opus-2026-09-29.md (483 cycles).

## 1. What is proven, by kind
1. **Equivalences (receivers).** Every route ends at the same statement. Examples:
   - RH ⟺ restricted Weil positivity `μ₀(a) ≥ 0` at every aperture (Bombieri–Yoshida) [L];
   - ⟺ `Λ ∈` Weil cone, which splits into existence (PBAP) and uniqueness (U);
   - ⟺ Krein–Langer index of the pole-free form `= 1` at every aperture (L366);
   - ⟺ finite-order slice signs; ⟺ Báez-Duarte `d_N → 0`; ⟺ `newmanConstant = 0`; and many more.
   - HF's Hodge index, RW's aperture positivity and TG's integrality index are **one integer**:
     `index(H_W|_B) = 1 + N_off(B)`, the number of off-line pairs resolved at aperture `B` (L366).
2. **Unconditional zero information** (all near `σ = 1`, or on average):
   - VK zero-free region `riemannZeta_ne_zero_vinogradovKorobov` [L];
   - 67.25% simple critical zeros and 83.62% distinct (Zeta23);
   - off-line moment `≤ 0.067V`; horizontal isolation; local zero counts;
   - Hardy's theorem; zero-free window `|t| ≤ 10.26`; Newman constant `< 1/8`.
3. **Unconditional positivity, small or soft only:**
   - `μ₀(½log 2) ≥ 1/10`, and `≥ 1/20` past the prime 2 [L];
   - PBAP on the nonnegative cone (L349, paper);
   - Weil-cone rigidity: Λ extreme and exposed, every regular perturbation fails (exact-primes gate) [L].
4. **The approximation side, complete** (MUST-787–793) [L]. At every aperture:
   - real-rooted ground states exist;
   - the ground level is `{P·G_a : deg P < d}` over one real-rooted generator, with multiplicity
     `1 +` (number of form-domain derivatives), and `d ≥ 2` only at parity crossings;
   - `W_a − μ_a` dominates a positive quadrature at the zeros of `G_a`.

## 2. The no-go structure (proved obstructions)
- **Gates** (frontier map): sharp endpoints · exact primes · rigidity not estimate · orientation (two-torsion,
  reflection-odd) · individual zeros · exponent not constant · cofinal source law · Mellin-diagonal blind ·
  holomorphic readers unquantized.
- **Walls** (core catalogue): √X-precision one-sided prime sums (wall 1, the terminus of every lane),
  |ζ|²-vs-log|ζ|, clustering, axis outside the zero set, no F₁ Frobenius, probability-cone, statistical, infinitesimal
  admixture, temperedness, oscillation–transport.
- **Terminal classification** (ULF-TERM-001): every producer shape is one of four theorem-closed kinds.
  These are fixed functionals; convergence in the strip; symmetries `s ↔ σ(s)`; two-factor presentations of ξ.

## 3. Interpretation
1. **RH is the vanishing of one integer, cofinally.** `N_off(B) = 0` for every `B` (L366). All analytic receivers are
   readings of this integer at some smoothing scale.
2. **There is no slack anywhere.**
   - `μ_a ≤ exp(−e^{2a})` (MUST-478) and `λ₂(Q₀) ≤ exp(−ce^{2a})` (L62);
   - `σ_prod ≥ ½` with equality only at Λ (L346–L347);
   - de Bruijn–Newman `Λ ≥ 0`.
   - RH sits exactly on the boundary of every deformation family. A proof must be an exact or extremal mechanism,
     never an estimate with margin.
3. **The only certificate is the zero set itself.**
   - The producer is Λ, unique among regular deviations, and its positive spectral measure is the zero measure.
   - Local zero-free certificates exist at every finite scale but cannot glue: a global producer must be singular
     at the zeros of an Euler product (L386).
   - Hence every unconditional producer route needs near-RH input (L398).
4. **Partial results do not interpolate.**
   - Zero-free regions improve the floor exponent by `o(1)` only (row 480); only a strip moves it.
   - Densities and averages are blind to individual zeros.
   - The RH step is a jump of `½` in an exponent, with no intermediate statements in the Weil/lag lanes.
5. **Consequence:** statistical or averaged tools cannot prove RH: pair correlation (Montgomery), moments, large
   sieve, Szegő asymptotics, mollifiers below θ>1, Bakry–Émery integrated curvature. They read the integer only
   through averages. The approximation side (CCM) is closed in Lean and moves RH only through the sign of `μ_a`.

## 4. What a proof must therefore be
- An exact, global, orientation-sensitive mechanism forcing the integer `N_off(B)` to vanish at every `B`, with input
  beyond Markov positivity and the PNT main term (Beurling systems share those and have off-line zeros: row 475).
- Known templates for "an integer forced to vanish by structure", each with its corpus status:
  - (a) Hodge index from geometry. HF, door 1: the missing surface. The arithmetic "easy half" is not free (row 468).
  - (b) Spectral realization by a self-adjoint operator. Its faithfulness is RH verbatim (CANNOT-462,
    `DeningerResolventCoreIsRiemannHypothesis`).
  - (c) An exact trace equal to the index, with an a-priori sub-unit bound. This is TG and door 2, and MUST-127
    requires it. The bound `B_base < 1` is explicit, but the source-side identity must hold at √X precision
    (CANNOT-461).
  - (d) Rigidity: existence plus uniqueness of producers (PBAP + U). The two decisive tests are computational.
- The forced shape of the missing object (ULF-F1-003):
  - infinite rank, with the scaling flow as Frobenius;
  - integrality on the Dirichlet-ring coefficients, never on eigenvalues;
  - no finite integral lattice carrying three Frobenii [L];
  - the single open datum is a geometrically produced Hodge positivity.

## 5. Working rule
- Choose each target from §4. Name which template (a)–(d) it advances, which forced-shape constraint it respects,
  and which gate it passes. Do not start from a borrowed tool.

## Log
- 2026-10-06 — created at user direction ("always start with the big picture, and interpretation of all we know and
  have proven in our lean corpus").
- 2026-10-06 (loop 484–486, first computations under the lifted ban).
  - U, the uniqueness of the producer, has a dual certificate, C-PIN: a prime-blind `ν = Ξ²ĥ` with `ĥ > 0`. By Gordan duality, C-PIN is infeasible exactly when a positive-off-Z crystalline separator exists. Separators are Dirichlet series with spectrum in `log ℕ_{≥2}`, holomorphic on `σ > ½`, with `Re ≥ 0` on the line off Z; the U-violators are among them.
  - Finite-level C-PIN is feasible with healthy margins once `ĥ` resolves the zero spacing (M ≤ 240). The corpus "Kronecker wall" was a resolution artifact, so the dual route to U is open.
  - The prime-blind LP has no universal extremal (cross-gaps 2.5e-6 to 1e-2), so there is no closed-form route to PBAP.
  - Atomic-on-Z producers are already closed in the corpus (`WeilConeCriticalZeroCarriedRigidity`).
- 2026-10-06 (row 488, MUST-794): external audit against the 2026 CCM literature (Connes arXiv 2602.04022; Connes–van Suijlekom CMP 2026; Silva Zenodo 2026). Their structural hypothesis, even-simplicity, is now discharged in Lean: even-sector generators are cross-rooted, and Ξ ≠ 0 on iℝ. The approximation template's single open step is the convergence (localization) of explicit even generators to Ξ.
- 2026-10-06 (row 496, MUST-796): the CCM receiver of MUST-795 was vacuous for polar ground states.
  - Cross-rooted zeros add positively to `Σz⁻⁴`, and the forced polar zeros `±i/2` exceed Ξ's budget by a factor of about 4·10⁵.
  - The corrected open input is `G_a/(z²+¼) → cΞ` on the strip (Lean receiver). Numerics at a ≤ 0.8 show it holds, with z²-deficit ≈ e^{−2a}/(4π²): the zero-density gap above `T* = 2πe^{2a}`, i.e. the same Nyquist law as μ_a.
  - Picture unchanged: approximation side closed except one convergence statement, which is RH-strength.
  - Methodological lesson: positivity of power sums on the cross detects vacuous receivers.
- 2026-10-06 (row 497, MUST-797): Connes's QW_λ has a real-rooted ground state at every λ, and a simple one is real-rooted, of either parity, with no hypothesis. The approximation template is now closed in Lean for both the polar and the unconstrained form, except the single convergence statement.
- 2026-10-06 (rows 496–508): the CCM approximation template has ONE analytic open core, the boundary (edge) mass of the restricted-Weil ground state at `x = ±a`.
  - Arithmetic-blind (proved): real roots [L], quadrature, multiplicity, monotone zero flow.
  - Equivalent faces of the edge decay: convergence, localization, zero domination, gap non-penetration, parity-simplicity (Connes's step 1 is RH-sensitive: planted off-line zeros force even/odd crossings with half-period π/(2t₀)).
  - Exact parity transfer: `Q(sign·f) = Q(f) ∓ 4H(f₊)`, H the Hankel form of the Weil kernel. The archimedean Hankel part is a negative Laplace kernel (favors even), the pole part is rank-2 positive and measures edge mass (favors odd).
