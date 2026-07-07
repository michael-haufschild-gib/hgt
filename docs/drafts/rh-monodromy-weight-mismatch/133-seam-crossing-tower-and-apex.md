# 133 — The length-sensitive seam crossing tower: unconditional core + the apex, both formal

Formal home: `formal/GaloisForLFunctions/RHTower/SeamCrossingTower.lean` (all endpoints axiom-clean
`[propext, Classical.choice, Quot.sound]`; full `MainTheorems` gate green). This is the convergence
point: the seam construction's **unconditional** finite-prime content is now Lean, and the
**critical-line apex** is formalized exactly as what it is — logically equivalent to RH.

## 1. Unconditional: the crossing tower (Theorems 1, 3, 5, in Lean)

The `r`-step seam crossing `B_{p,r} = (1−Q_p)S_p^r Q_p` sends the shell `e_n` to `e_{n−r}` for
`1 ≤ n ≤ r`, else `0` — it crosses exactly `r` shells. Formalized (at the level of its matrix / HS
combinatorics, which is the load-bearing content):

- **Crossing-energy law** (`crossHS_inner`, from `crossSupport_card` + `crossSupport_orthogonal`):
  `⟨B_{p,r}, B_{p,s}⟩_HS = r·δ_{r,s}`. The `r`-crossing occupies exactly `r` unit matrix positions
  `{(n−r,n) : 1 ≤ n ≤ r}`; distinct-length crossings are orthogonal. So `‖B_{p,r}‖²_HS = r`.
- **Euler factor = exp of the reproducing kernel** (`expKernel_eq_eulerFactor`):
  `exp(Σ_r (p^{−s})^r / r) = (1 − p^{−s})⁻¹`. The prime-power weight `1/r` is the **reciprocal of the
  `r`-shell crossing energy** — not inserted by formal power-series algebra, but forced by the
  Hilbert–Schmidt geometry of `§1`.
- **Finite-prime Weil energy is positive** (`finite_weil_energy_nonneg`):
  `Σ_{(p,r)} r·‖h(p,r)‖² ≥ 0` — each crossing contributes its own nonnegative energy `r`. The finite
  half of the Weil form realized as a manifest HS norm.

This is genuinely new-flavored structural content (crossing length ↦ Hilbert-space energy ↦ Euler
weight) and it is unconditional. It is also, by design, entirely on the `Re s > 1` side: the crossing
kernel `Σ_p Σ_r p^{−rs}/r` converges to `log ∏_p(1−p^{−s})⁻¹` for `Re s > 1` only.

## 2. The apex, formalized exactly — it is RH [PROVED HERE]

The program completes the crossing tower to a self-dual seam Hilbert space with a scaling generator
`Θ_Δ` skew-adjoint-after-shift, whose spectrum (via a determinant identity) is the ξ-zeros — forcing
them onto the line. Its endpoint is: *every strip ξ-zero has the self-adjoint spectral form
`ρ = 1/2 + iλ`, `λ ∈ ℝ`.* Formalized:

- **`rh_of_seam_spectral`** — that endpoint **implies** RH (a strip zero of the form `1/2 + iλ` has
  `Re = 1/2`; combined with `xi_ne_zero_of_one_le_re` and `rh_iff_xi_ne_zero_right`, this is RH).
- **`seam_spectral_iff_rh`** — that endpoint is **equivalent** to RH.

The second is the decisive "let Lean speak" statement. The remaining ingredient of the program — the
self-adjoint spectral identification of the zeros (equivalently: Weil positivity of the completed seam
norm, `‖B_h^rec‖²_Δ = Σ_ρ m_ρ ĥ(ρ)ĥ(1−ρ̄)`) — is **not a bridge lemma derivable from the crossing
tower**. Discharging it *is* proving RH. The crossing tower (`§1`) gives the Euler/energy side on
`Re s > 1`; the spectral identification lives at the zeros in the strip; connecting them across the
wall `Re s = 1` is the whole problem (the carrier-support disjointness of doc 127, restated on the
seam).

## 3. The exact frontier

- **Proved, unconditional:** `B_{p,r}` crossing-energy law `‖B_{p,r}‖²_HS = r`; Euler factor
  `(1−p^{−s})⁻¹ = exp K_p(p^{−s},1)`; the Euler product on `Re s > 1` as the boundary seam kernel;
  finite-prime Weil energy `≥ 0`.
- **Still conjectural (the apex):** the reciprocity-completed positive quotient `H¹_Δ` with the
  Weil-norm identity `W_Δ(h) = ‖B_h^rec‖²_Δ`, built *without* circularity — i.e. without inserting the
  answer. `seam_spectral_iff_rh` shows this apex is RH-equivalent: it cannot be assembled from the
  unconditional `Re s > 1` ingredients, because the object it must produce (zeros on the line, or
  equivalently the positive middle cohomology) is the theorem itself.

The seam picture is a genuine and clean **repackaging of the Euler side as crossing energy**, and it
sharpens the apex to one precise demand: construct the reciprocity-completed positive `H¹_Δ` from the
crossing operators and the self-dual archimedean seam, and prove its norm equals the spectral divisor
sum. Until that positive quotient is built non-circularly, the critical-line conclusion is exactly the
part `seam_spectral_iff_rh` isolates — and that part is RH, not a bridge lemma.

## 4. Two structural constraints on the apex (§5 and §10, formalized)

`SeamKreinStructure.lean` formalizes two unconditional constraints the seam-positivity apex must obey,
both axiom-clean:

- **§5 — no internal reciprocity on the one-particle prime space** (`seam_no_bounded_reciprocity_carrier`,
  `prime_reflection_diagonal_unbounded`). `A(s) = ⊕_p p^{−s}C_p` is bounded for `Re s > 1`, but its
  reflection `A(1−s) = ⊕_p p^{s−1}C_p` has **unbounded** diagonal `p^{s−1} → ∞` (proved: for real
  `s > 1`, `{p^{s−1}}` exceeds every bound over the primes). A bounded conjugation preserves
  boundedness, so no bounded `J` gives `J A(s) J⁻¹ = A(1−s)`. The prime determinant cannot self-continue
  internally; it must be embedded in a larger self-dual seam. (Strengthens the `no_oneParticle_FE_involution`
  trace argument — boundedness, not just spectrum.)

- **§10 — the reciprocity graph is Lagrangian, so the apex cannot be a naive positive quotient**
  (`isotropic_eq_zero`, `signedForm_graph_isotropic`, `graph_lagrangian`). On a positive Hilbert space an
  isotropic vector is `0` (`isotropic_eq_zero`), so a reciprocity relation cannot be isotropic in a direct
  positive norm — the naive positive-quotient apex is impossible. The correct ambient object is a **signed
  Green (Krein) form** `[(x₊,x₋),(y₊,y₋)] = ⟪x₊,y₊⟫ − ⟪x₋,y₋⟫`, on which the doubled reciprocity graph
  `{(x, U x)}` (`U` unitary) is **Lagrangian**: `graph_lagrangian` proves `(a,b) ⟂ graph ↔ b = U a`, i.e.
  `R^⊥ = R`. A full doubled reciprocity graph therefore has **zero quotient** — nonzero middle cohomology,
  where the zeros would live, can arise only from **domain/closure/boundary defects** of the actual seam
  complex, never from the reciprocity algebra alone. This is a genuine constraint on the shape of the apex.

Net: the apex is now pinned to a precise structural form — a positive quotient of a **signed Krein
reciprocity form** extracted via analytic **domain defects** (not a naive positive Hilbert quotient), with
the spectral/skew-adjoint carrier of the divisor as the final unproved statement (`rh_of_seam_spectral`,
§12: skew-adjoint `Θ_Δ − 1/2` ⟹ zeros on the line ⟹ RH).

## 5. Step 3 — the seam-flux cochain (Λ(p^r) = log p from scale flux, formalized)

`SeamFluxCochain.lean` gives the von Mangoldt weight an intrinsic seam origin, independent of the `1/r`
crossing-energy origin. All axiom-clean, gate green.

- **The scale-flux commutator** (`commutator_X_Spow`): with the shift `S_p e_n = e_{n−1}` (`Sshift`) and
  the logarithmic position `X_p e_n = n·(log p)·e_n` (`Xpos`), formalized as linear maps on `ℤ → ℂ`,
  `[X_p, S_p^r] = −r·(log p)·S_p^r`. So the seam derivation `∇_p = −[X_p,·]` has eigenvalue `r·log p` on
  the `r`-crossing (`seam_derivation_eigenvalue`). The scale-flux of an `r`-crossing is `r·log p`.
- **Von Mangoldt = flux/length** (`vonMangoldt_eq_flux_over_length`): for a prime power `p^r` (`r ≥ 1`),
  mathlib's real `vonMangoldt (p^r) = (r·log p)/r` — the scale-flux eigenvalue `r·log p` renormalized by
  the crossing-length eigenvalue `r` (`SeamCrossingTower.crossSupport_card`, `‖B_{p,r}‖²_HS = r`). The
  arithmetic weight is renormalized scale flux, not an inserted constant.
- **The flux energy** (`flux_energy_nonneg`): `Σ_{(p,r)} (log p)·‖h‖² ≥ 0`, the arithmetic-mass form,
  distinct from the crossing-length form `finite_weil_energy_nonneg` (`Σ r·‖h‖²`).

Net: the two fundamental arithmetic coefficients now have independent, intrinsic seam origins — `1/r`
from reproducing-kernel duality (crossing energy), `Λ(p^r) = log p` from logarithmic scale flux. The
finite arithmetic cochain `Ω_fin(s) = N⁻¹ A e^{−sA} ds` has `Tr Ω_fin = Σ_{p,r} Λ(p^r) p^{−rs} ds`
(the finite `−∂_s log ζ`) built only from `B_{p,r}`, `X_p`, `N`, `A = −ad X_p` — no `ζ` imported. The
apex is unchanged (§2–§4): completing `Ω_fin` to a reciprocity-invariant, Krein-positive divisor cochain
whose norm is the spectral divisor sum — the RH-equivalent step `seam_spectral_iff_rh`.

## 6. The completed flux cochain is `−ξ'/ξ`; Theorem A/B (SeamFluxCompletion.lean)

The reviewer's completed flux cochain `Ω_Δ = Ω_fin + Ω_∞ + Ω_∂` is, in the project's existing carrier,
`−logDeriv ξ`, because `ξ = archFactor · ζ` (`ZetaCarrier.xi_eq_archFactor_mul_zeta`) with
`archFactor s = s(s−1)/2 · Gammaℝ s` — the boundary seams `s(s−1)` times the archimedean Gaussian seam
`Gammaℝ`, times the finite Euler side `ζ`. The archimedean flux is the already-formalized
`ArchimedeanGamma.gammaRealLogConnection = −½log π + ½ψ(s/2)`. Formalized (gate green, axiom-clean):

- **`logDeriv_xi_reciprocity`** / **`seamFluxCochain_reciprocity`**: `Ω_Δ(1−s) = −Ω_Δ(s)`, the
  chain-level reciprocity — proved **from the existing `xi_one_sub`** (the completed FE), not postulated.
- **`boundary_flux_reciprocity`**: the boundary pair `1/s + 1/(s−1)` is anti-invariant under `s↦1−s`.
- **`seamFluxCochain_carrier`**: `ξ = archFactor · ζ` (existing).
- **Theorem A** (cochain divisor = ξ-divisor): the cochain is `−logDeriv ξ`, carrier `ξ` entire, so its
  divisor is `analyticOrderAt ξ` — the classical nontrivial zeros. Captured by the `seamFluxCochain`
  definition + carrier.
- **Theorem B** (`seam_determinant_divisor_of_const_mul`, conditional): if the seam superdeterminant is
  `C·ξ` (`C ≠ 0`), then `analyticOrderAt (C·ξ) ρ = analyticOrderAt ξ ρ` at every point. The whole content
  is the hypothesis `D_Δ = C·ξ`, which the **resolvent-flux identity** `Str_ren((s−Θ_Δ)⁻¹) = ξ'/ξ`
  delivers by integration. Positivity + reciprocity do **not** force it — adjoining a reciprocal spectral
  pair `{½±iτ}` preserves both while multiplying the determinant by `(s−½−iτ)(s−½+iτ)`. Only the
  resolvent-flux identity pins `D_Δ = C·ξ`.
- **`seam_H1_seminorm_nonneg`**: `H_Δ^1` positivity (quotient seminorm of a positive space `≥ 0`).

**Frontier, now formal on both sides.** Proved: `Ω_Δ = −d log ξ` (cochain divisor = ξ-divisor);
reciprocity from `xi_one_sub`; `H_Δ^1 ≥ 0`; `D_Δ = C·ξ ⟹ div D_Δ = div ξ`. The single open identity is
`Str_ren((s−Θ_Δ)⁻¹) = ξ'/ξ` — the resolvent-flux bridge between the positive `H_Δ^1` operator and the
cochain. The integration step `logDeriv D = ξ'/ξ ⟹ D = C·ξ` that would reduce Theorem B's hypothesis
to the raw resolvent identity is a Wronskian-proportionality theorem for entire functions handling
ξ's zeros — a standard but non-trivial analytic input, not yet in mathlib or the project.
