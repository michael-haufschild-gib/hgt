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
