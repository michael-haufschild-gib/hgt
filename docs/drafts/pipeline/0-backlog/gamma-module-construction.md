# The Γ-module M_∞ — the archimedean Euler factor as a rank-1 polynomial-multiplier difference module

- **ID:** gamma-module-construction
- **Stage:** 0-backlog
- **Type:** CONJECTURE / CONSTRUCTION (foundational — the first Source-A native object)
- **Priority:** FOUNDATIONAL
- **Source:** the Hölder-recentering (Source A = Γ; `../../00-foundations-native-objects-and-gatekeepers.md` N1⁺);
  the polynomial-multiplier observation #90 §64 (`Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`); builds on
  `completed-base-archimedean-coordinate.md`; feeds `completed-connection-category.md` and the completed `Λ`;
  00-status row #27 (`ω`/Kurokawa)
- **Statement (to shape).** Construct the **archimedean Euler factor** `π^{-s/2}Γ(s/2)` as a concrete
  **rank-1 object `M_∞`** in the completed category: a difference module with the **polynomial** (non-constant)
  multiplier of the `Γ`-recurrence
  > `Γ_ℝ(s) := π^{-s/2}Γ(s/2)`, `Γ_ℝ(s+2) = (s/2π)·Γ_ℝ(s)` — multiplier `a(s) = s/2π`, the **unique
  > non-constant polynomial multiplier** among the places (#90 §64),
  together with its `∂_s`-connection (`∂_s log Γ_ℝ = −½log π + ½ψ(s/2)`, the digamma). Then `M_∞` is the
  Source-A native object; `M_Λ = M_∞ ⊗ M_ζ` has the completed `Λ` as its diagonal section.

  **One sentence:** `Γ` is *difference*-simple — one operator, polynomial multiplier — so it has a clean
  rank-1 module; that module is the archimedean factor brought inside the field as an object, not a wall.

## Why this is the right first Source-A object
The whole reorientation rests on Source A being **constructible** (not just an obstruction). The
polynomial-multiplier recurrence makes `Γ_ℝ` a genuine difference module — the archimedean analogue of the
prime factor `(1−x_p)^{-1}` (which is the rank-1 module for `σ_p` with **constant** multiplier). The
contrast `constant (1/p)` vs `polynomial (s/2π)` is exactly the Source-B/Source-A multiplier dichotomy
(`multiplier-dichotomy-theorem.md`), so `M_∞` is the worked example that makes the dichotomy concrete.

## Concrete first steps
1. **The recurrence module.** Realize `M_∞` as `R⁺·e` with `σ_∞ e = a(s)e`, `a(s)=s/2π` (the shift `s↦s+2`),
   or in the `∂_s`-picture the rank-1 connection `∇_s e = (−½log π + ½ψ(s/2))e`. Pin which shift (`s↦s+1`
   half-integer vs `s↦s+2`) and normalize.
2. **`ζ`-regularized determinant.** Verify the corpus claim `Γ = ζ-reg det(∂_s|M_∞)` (Kurokawa absolute
   zeta, #90) — i.e. `M_∞` is the object whose regularized determinant **is** the Γ-factor (the link to `ω`
   and RH, `gamma-regularized-det-omega` material, now owned by the seam/G5 cards).
3. **The tensor `M_Λ = M_∞ ⊗ M_ζ`.** Confirm its diagonal section is the completed `Λ(s)=π^{-s/2}Γ(s/2)ζ(s)`
   and that the FE acts on it (feeds `completed-connection-category` FE=flatness).
4. **Numerically pre-certify** (mpmath): `Γ_ℝ(s+2)/Γ_ℝ(s) = s/2π`, `∂_s log Γ_ℝ = −½logπ+½ψ(s/2)`, on a
   grid — before any Lean (archive in `computations/`).

## Door passport
- **Door-2:** `M_∞` **alone** is differential Galois / Hölder (Source A = a border) — BRIDGE by itself, as
  expected. Its value is being a constructed *object* the weld can use; native content is `M_∞ ⊗ M_ζ` under
  the joint structure (the cross-term card).
- **Door-5:** over `F_q` there is no `Γ` — `M_∞` is absent; the completed module degenerates to `M_ζ` alone.

## Gates
- [ ] 0 → 1  in-progress: `M_∞` defined (recurrence + `∂_s`-connection, normalization fixed); `Γ=ζ-reg det`
  link stated; `M_Λ=M_∞⊗M_ζ` with diagonal `Λ` posed; numerics planned; Door passport
- [ ] 1 → 2  fully-proven: `M_∞` constructed as a rank-1 `(σ_∞,∂_s)`-module; the recurrence/connection
  verified; `M_Λ`'s diagonal `=Λ`; `F_q` degeneration
- [ ] 2 → 3  formalized: Lean — the recurrence multiplier `a(s)=s/2π` and the rank-1 module fragment; reuse
  `functionField_localFactor_FE`/`BoundaryModulus` ledger anchors where applicable
- [ ] 3 → 4  publication-ready: "the archimedean Euler factor as a polynomial-multiplier difference module"

## Cross-references
- `completed-base-archimedean-coordinate.md` — the base `R⁺` this lives over (dependency).
- `multiplier-dichotomy-theorem.md` — `M_∞` is the polynomial-multiplier worked example.
- `completed-connection-category.md`, `archimedean-prime-cross-term.md` — consume `M_∞`/`M_Λ`.
- `../../door/bucket-the-seam-archimedean-obstruction.md`, `compute-omega-h2-gl.md` — own the `Γ=ζ-reg det`/`ω` face.

## Log
- 2026-06-19 — created in 0-backlog as the first **Source-A native object**: the Γ-factor `π^{-s/2}Γ(s/2)`
  as a rank-1 polynomial-multiplier difference module `M_∞` (recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, #90 §64),
  with `M_Λ=M_∞⊗M_ζ`. First step = fix the recurrence/connection normalization and numerically pre-certify.
</content>
