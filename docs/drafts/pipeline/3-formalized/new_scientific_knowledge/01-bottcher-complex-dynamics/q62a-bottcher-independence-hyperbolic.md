# Q6.2(a) — Hyperbolic Böttcher Independence

- **ID:** q62a-bottcher-independence-hyperbolic
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Nguyen arXiv:1310.2329 Question 6.2 / inverse-Böttcher lane
- **Statement:** If `c1 != c2` are hyperbolic parameters in the Mandelbrot set and `c1,c2 notin {0,-2}`, then the inverse Böttcher coordinates `phi_c1(z)` and `phi_c2(z)` are algebraically independent over `Qbar(c1,c2,z)`.

Disconnected parameters are out of scope here. The broader connected statement is tracked in
`docs/drafts/pipeline/1-in-progress/q62-bottcher-independence-natural-boundary.md`.

## Goal

This proves a concrete stratum of Nguyen Question 6.2 for inverse Böttcher coordinates. Nguyen proves
algebraic-independence results for the local conjugacies `psi_f(u(t))`; Section 6.3 explicitly separates
the inverse Böttcher coordinate `phi_f=psi_f^{-1}` and asks for necessary and sufficient conditions for
algebraic independence of the `phi_i`.

## Proof

Let `K_i` be the filled Julia set of `f_i(z)=z^2+c_i`, `J_i=partial K_i`, and `Omega_i=C \ K_i`.
For hyperbolic `c_i in M`, `K_i` is connected and the Böttcher coordinate `phi_i` extends
single-valuedly through all of `Omega_i`.

**Step 1: crossing.** We prove `J_1 cap Omega_2` is nonempty. Suppose `J_1 subset K_2`. Since `K_2` is
full, this implies `K_1 subset K_2`. Both are connected full compacta of logarithmic capacity `1`
because the polynomials are monic.

If `K_1 subsetneq K_2`, choose `p in K_2 \ K_1`. Let `g_1` be the Green function of `C \ K_1` with pole
at infinity. Since `K_1` is full and regular, `g_1>0` outside `K_1`. A compact continuum in `K_2`
joining `p` to `K_1` has a nondegenerate compact subcontinuum `E` on which `g_1 >= delta > 0`. Choose
a finite-energy probability measure `nu` on `E`, and mix it with the equilibrium measure `mu_1` of
`K_1`: `mu_t=(1-t)mu_1+t nu`. Since `U^{mu_1}=V_1-g_1` off `K_1`,

`I(mu_t)=V_1-2t(1-t) int_E g_1 dnu+t^2(I(nu)-V_1)<V_1`

for small `t>0`, so `cap(K_2)>cap(K_1)`, contradiction. Hence `K_1=K_2`. Equal filled Julia sets in
the quadratic family force `c1=c2` (Atela-Hu / coefficient at infinity), contradiction. Thus
`J_1 cap Omega_2 != empty`.

**Step 2: no analytic continuation across `J_1`.** Suppose `phi_1` analytically continued to a
neighborhood `D` of a point of `J_1`; call the branch `Phi`. Since `G_1=log|phi_1|` on `Omega_1` and
`G_1=0` on `J_1`, the set `J_1 cap D` lies in `{|Phi|=1}`. Avoiding isolated zeros of `Phi'`, a
relatively open subset of `J_1` lies in a smooth real-analytic curve. By Eremenko-van Strien
arXiv:0810.2260, a relatively open subset of a Julia set contained in a smooth curve forces the whole
Julia set into a circle. For connected quadratics this gives exactly the exceptional cases `c=0` or
`c=-2`, contrary to hypothesis. Therefore `phi_1` has no analytic continuation across any point of `J_1`.

For the hyperbolic stratum this step can also be routed through standard expansion/arc propagation, but
the Eremenko-van Strien relative-open statement is the sharper citation used here.

**Step 3: algebraic relation gives forbidden continuation.** Suppose

`P(z,phi_1(z),phi_2(z))=0`

with nonzero `P in Qbar(c1,c2)[z,Y,Z]`. If `P` does not involve `Y=phi_1`, then `phi_2` is algebraic
over `Qbar(c1,c2,z)`, contradicting Becker-Bergweiler for nonexceptional `c2`.

Otherwise choose a monic irreducible relation of minimal degree in `Y` over
`Qbar(c1,c2)(z,W)`, where `W` represents `phi_2`. Let `D(z,W)` be a common denominator of its
coefficients and `Delta(z,W)` its discriminant. After substituting `W=phi_2(z)`, the zeros of
`D(z,phi_2(z))` and the numerator of `Delta(z,phi_2(z))` form a locally discrete bad set in `Omega_2`;
if either vanished identically, it would give algebraicity of `phi_2` over `C(z)`.

Choose `z0 in J_1 cap Omega_2` outside this bad set. The algebraic implicit function theorem gives
analytic branches solving the relation near `z0`. On a component of `Omega_1` accumulating at `z0`,
`phi_1` equals one branch by the identity principle, so that branch analytically continues `phi_1`
through `z0`. This contradicts Step 2. Therefore no algebraic relation exists.

## Source Boundary

- Nguyen arXiv:1310.2329 proves the local-conjugacy (`psi`) results and poses inverse Böttcher
  coordinate independence as Question 6.2.
- Becker-Bergweiler / Fernandes cover single-function algebraicity and hypertranscendence, not the
  two-function inverse-coordinate relation.
- Eremenko-van Strien arXiv:0810.2260 supplies the smooth-piece rigidity used in Step 2.
- Atela-Hu supplies same-filled-Julia-set rigidity for the quadratic family.
- Pritsker records capacity `1` for monic polynomial Julia sets.

No source found in the audit proves this inverse-Böttcher function-field relation by the
natural-boundary / capacity-crossing / algebraic-IFT bridge.

## Novelty / Significance Vote

Consensus grade: `novel+significant` as a **cross-corpus theorem**, not a deep-new-mathematics claim.

- Professor: `novel+significant` for the connected theorem; hence yes for the hyperbolic stratum.
- Haiku (id=1630): `novel+significant`; source-newness audit survives current evidence.
- Turing (id=1631, id=1637): `novel+significant` at cross-corpus grade; later calibrated to the locally connected/hyperbolic common stratum when Wheeler objected.
- Wheeler (id=1641): correctness accepted for the hyperbolic stratum; novelty/significance `YES` at cross-corpus bridge grade.

Theatre test passed only at this calibrated level. The result answers a named open inverse-Böttcher
question on a large stratum using a bridge not found in the searched corpus. It is not claimed as deep
novelty because the proof uses classical potential theory, algebraic IFT, and complex-dynamical rigidity.

## Gates

- [x] 0 -> 1 in-progress: well-posed; target is Nguyen Q6.2 inverse-Böttcher independence.
- [x] 1 -> 2 fully-proven: complete paper proof for hyperbolic connected parameters; four-agent vote recorded.
- [x] 2 -> 3 formalized: `Bottcher.noRelation_phiMero_of_mem_mandelbrot` (2026-09-29).
- [ ] 3 -> 4 publication-ready: standalone paper with full citations and formal proof plan.

## Log

- 2026-06-24 - Created after shared chat consensus. The broader connected case remains in progress; this card records the common theorem all agents explicitly accepted as novel and significant.

## Lean formalization (stage 3, 2026-09-29)

Unconditional; axioms `[propext, Classical.choice, Quot.sound]`.  The hyperbolic stratum is a special
case of the connected theorem, which is proved for every `c₁ ≠ c₂ ∈ M ∖ {0,−2}` with no hyperbolicity
assumption: `Bottcher.noRelation_phiMero_of_mem_mandelbrot` (`Q62BothConnectedIndependence`).

| Card step | Lean |
|---|---|
| Theorem (independence over `ℂ(z) ⊇ Q̄(c₁,c₂,z)`) | `noRelation_phiMero_of_mem_mandelbrot` |
| Step 1 crossing `J_{c₁} ∩ Ω_{c₂} ≠ ∅`; `K_{c₁} = K_{c₂} ⟹ c₁ = c₂` | `exists_frontier_filledJulia_not_mem_of_mem_mandelbrot`, `not_filledJulia_subset_of_mem_mandelbrot` (`FilledJuliaNoContainment`, maximum principle, no capacity); `c_eq_of_filledJulia_eq'` |
| Step 2: no analytic continuation of `φ_{c₁}` across `J_{c₁}` | `hnb_of_mem_mandelbrot_connected`; one-access-region form `false_of_continuation_on_open_approach` |
| Step 3: relation forces a forbidden continuation (including `P` free of `φ_{c₁}`: transcendence of `φ_{c₂}`) | `hno_of_connected_of_mem_filledJulia_not_mem`, `phiMero_transcendental_of_mem_mandelbrot` |

The card's Step 3 "on a component of `Ω₁` accumulating at `z₀`" is made rigorous exactly by the
one-access-region natural boundary: the relation only needs to hold on one open access region,
which the common far-field component supplies.
