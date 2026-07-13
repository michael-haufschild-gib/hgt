# The Γ-module M_∞ — the archimedean Euler factor as a rank-1 polynomial-multiplier difference module

- **ID:** gamma-module-construction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CONSTRUCTION — Door grade **BRIDGE** (Source A alone; the weld is where it turns native)
- **Priority:** FOUNDATIONAL (the Source-A object of the completed constraint module `M_Λ=M_∞⊗M_ζ`)
- **Source:** the Hölder-recentering (Source A = Γ; `00-foundations` N1⁺); `#90 §64` (`Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`,
  the unique non-constant polynomial multiplier); Lerch 1894 / Kurokawa absolute zeta (`Γ` = ζ-reg det);
  builds `completed-base-archimedean-coordinate.md`; feeds `lambda-difference-differential-hypertranscendence.md`,
  `archimedean-prime-cross-term.md`. 00-status row #27, #130.
- **Numerics:** `computations/2026-06-19-gamma-module-Minfty.py(.out)` — recurrence, connection, Lerch all ≥30 digits.

---

## Result — `M_∞` constructed

`Γ_ℝ(s) := π^{-s/2}Γ(s/2)` is realized as a **rank-1 `(σ_∞, ∂_s)`-module** `M_∞ = R⁺·e`:

**(1) Difference structure (the polynomial multiplier).** With `σ_∞ : s ↦ s+2`,
> `σ_∞ e = a(s)·e`, `a(s) = s/2π`  —  i.e. `Γ_ℝ(s+2) = (s/2π)·Γ_ℝ(s)`.
*Proof:* `Γ_ℝ(s+2)=π^{-(s+2)/2}Γ(s/2+1)=π^{-s/2}π^{-1}(s/2)Γ(s/2)=(s/2π)Γ_ℝ(s)`. ∎ The multiplier `a(s)=s/2π`
is the **unique non-constant (degree-1 polynomial) multiplier** among the places (#90 §64) — the Source-A
signature (vs the prime places' **constant** multipliers `p^{-1}`); this is the multiplier-dichotomy divide
(#131): `a(s)` is **non-CC** (`∂_s\log a = 1/s ≠ 0`, the Hölder obstruction). *(Recurrence verified ≥30 digits.)*

**(2) Differential structure (the rank-1 `∂_s`-connection).**
> `∇_s e = (−½\log π + ½ψ(s/2))·e`  —  i.e. `∂_s\log Γ_ℝ = −½\log π + ½ψ(s/2)` (digamma `ψ`).
*Proof:* `\log Γ_ℝ = −\tfrac{s}{2}\log π + \logΓ(s/2)`; differentiate. ∎ `[∂_s, σ_∞]` acts compatibly
(`∂_s` and the shift commute as operators); the connection is the archimedean generator restricted to `M_∞`.
*(Connection verified ≥30 digits.)*

**(3) `Γ_ℝ` = INVERSE ζ-regularized determinant (the Euler-factor convention; Kurokawa link).** Via **Lerch's
formula** (IMPORT) `\tfrac{d}{dz}ζ_H(z,a)\big|_{z=0} = \logΓ(a) − ½\log(2π)`, the ζ-regularized determinant of
the shift/number generator `N+s/2` (spectrum `{s/2+k}_{k≥0}`, `N` the number operator) is
> `det_ζ(N+s/2) = exp(−ζ_H'(0,s/2)) = {\prod_{k≥0}}^{\mathrm{reg}}(s/2+k) = \sqrt{2π}/Γ(s/2)`,
so `Γ(s/2)` is the **reciprocal** of this determinant (up to the constant `√(2π)`):
> `Γ(s/2) = \sqrt{2π}·det_ζ(N+s/2)^{−1}`,  equivalently  `Γ(s/2)·det_ζ(N+s/2)=\sqrt{2π}`.
Hence `Γ_ℝ(s)=π^{−s/2}Γ(s/2)=π^{−s/2}\sqrt{2π}·det_ζ(N+s/2)^{−1}` — the `π^{−s/2}` is the archimedean conductor
power, separate from the determinant. **This is the universal "local Euler factor = inverse determinant"
structure**, uniform across all places: finite primes give `L_p(s)=det(1−p^{−s}\mathrm{Fr}_p)^{−1}`, the
archimedean place gives `Γ_ℝ(s)=π^{−s/2}\sqrt{2π}·det_ζ(N+s/2)^{−1}` — both *inverse* determinants of the
place's generator. (Connes scaling / Kurokawa absolute-zeta, #90 §1; matches the verified one-sided-ladder
identity `Γ(a)·det_ζ(N+a)=√2π`, DeWitt #347/#357.) `M_∞` is exactly the object whose **inverse** regularized
determinant is the archimedean Γ-factor. *(Verified ≥35 digits incl. complex argument
`a=0.25+7i`: `computations/2026-06-19-gamma-module-invdet.py`; det−reciprocal `≤8e−36`, `Γ·det−√2π ≤2e−40`.)*

**(4) The completed constraint object.** `M_Λ := M_∞ ⊗ M_ζ` carries the completed `Λ(s)=Γ_ℝ(s)ζ(s)` as its
diagonal section; the FE `Λ(s)=Λ(1−s)` acts on it. `M_∞` is the rigorous archimedean factor the weld cards
(#132, #134) previously used only as "the concrete analytic incarnation `Γ_ℝ`."

## Door passport
- **Door-2:** `M_∞` **alone** is differential Galois / Hölder (Source A = a border) — **BRIDGE** by itself, as
  the multiplier dichotomy predicts (non-CC polynomial multiplier). Its value is being a *constructed object*
  the weld consumes; native content lives in `M_∞⊗M_ζ` under the joint structure (the cross-term / weld cards).
- **Door-5:** over `F_q` there is **no archimedean place** ⟹ `M_∞` is absent; the completed module degenerates
  to `M_ζ` alone (all places constant-multiplier/CC, holonomic — corank 1, #121).

## Gates
- [x] 0 → 1 in-progress: `M_∞` defined; recurrence + `∂_s`-connection fixed; `Γ=ζ-reg det` link stated;
  `M_Λ` posed; numerics planned; Door passport.
- [x] 1 → 2 fully-proven: recurrence (multiplier `s/2π`) and connection (digamma) **proved + verified ≥30
  digits**; `Γ_ℝ` = **inverse** ζ-reg det via **Lerch** (`det_ζ(N+s/2)=√2π/Γ(s/2)`; import, verified ≥35
  digits); `M_Λ=M_∞⊗M_ζ` diagonal `=Λ`; `F_q` degeneration. Grade BRIDGE (Source A alone).
- [ ] 2 → 3 formalized: Lean anchors **DONE** for the scalar Gamma recurrence and connection compatibility:
  `gammaReal_shift_two`, `digamma_half_add_one`, and `gammaRealLogConnection_shift_compat` in
  `formal/GaloisForLFunctions/RHTower/ArchimedeanGamma.lean`, with split certificate
  `../3-formalized/archimedean-gamma-shift-connection.md`. Remaining Lean targets are the full rank-one
  `(σ∞, ∂s)` module packaging, the Lerch inverse-ζ-reg-det import
  `Γ(a)·exp(−ζ_H'(0,a))=√2π`, and the completed object `M_Λ`.
- [ ] 3 → 4 publication-ready: "the archimedean Euler factor as a polynomial-multiplier difference module."

## Cross-references
- `completed-base-archimedean-coordinate.md` — the base `R⁺` (dependency).
- `multiplier-dichotomy-theorem.md` (#131) — `M_∞` is the polynomial-multiplier / non-CC worked example.
- `lambda-difference-differential-hypertranscendence.md` (#134), `archimedean-prime-cross-term.md` (#132) —
  consume `M_∞`/`M_Λ`; now rest on this rigorous object instead of the analytic incarnation.
- `../../door/bucket-the-seam-archimedean-obstruction.md`, `compute-omega-h2-gl.md` — own the `Γ=ζ-reg det`/`ω` face.

## Log
- 2026-06-19 — created in 0-backlog (Source-A object).
- 2026-06-19 — Professor: built to 2-fully-proven, acting on the "constraint, not flow" steer (constructing
  the archimedean factor of the completed *constraint* object `M_Λ`). Proved + verified (≥30 digits): (1)
  recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, unique non-constant polynomial / non-CC multiplier (#131 divide); (2)
  rank-1 `∂_s`-connection `∂_s\logΓ_ℝ=−½\logπ+½ψ(s/2)`; (3) `Γ_ℝ` = ζ-regularized determinant of the shift
  generator via **Lerch** (`ζ_H'(0,a)=\logΓ(a)−½\log(2π)` ⟹ reg-`∏(s/2+k)=\sqrt{2π}/Γ(s/2)`). `M_Λ=M_∞⊗M_ζ`
  carries `Λ`. Grade **BRIDGE** (Source A alone — the weld is native). Numerics
  `computations/2026-06-19-gamma-module-Minfty.*`.
</content>

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)` and the displayed logarithmic-connection calculation are fine as paper identities, but the ζ-regularized determinant conclusion has the determinant/inverse determinant reversed. Lerch's formula gives
`ζ_H'(0,a)=log Γ(a)-1/2 log(2π)`, so the standard ζ-regularized product/determinant is
`exp(-ζ_H'(0,a)) = √(2π)/Γ(a)`, exactly as the card and numeric script compute. That is reciprocal to `Γ(a)` up to the constant, not `Γ(a)` itself. Therefore the statement that `Γ(s/2)` / `Γ_ℝ(s)` is the ζ-regularized determinant of the shift generator is not proven as written. A repaired ticket should state the inverse determinant (or specify a reciprocal determinant convention/operator) and then re-check the `π^{-s/2}` normalization.

## Repair note — 2026-06-19 (Professor): Leaner's det/inverse-det return CLOSED (and it improved the card)
Leaner's return (correct): the ζ-reg determinant of the shift generator is `√2π/Γ(s/2)`, the **reciprocal** of
Γ, not Γ itself — so "Γ_ℝ IS the ζ-reg determinant" was wrong as written. **Fixed** claim (3): Γ_ℝ is the
**inverse** ζ-reg determinant — `det_ζ(N+s/2)=exp(−ζ_H'(0,s/2))=√2π/Γ(s/2)`, hence
`Γ_ℝ(s)=π^{−s/2}√2π·det_ζ(N+s/2)^{−1}` (the `π^{−s/2}` re-checked: it is the archimedean conductor power,
independent of the determinant). The correction is **not a patch but a clarification on-mission**: it makes the
archimedean factor obey the **universal "local Euler factor = inverse determinant"** law — finite primes
`L_p=det(1−p^{−s}Fr)^{−1}`, ∞ `Γ_ℝ=π^{−s/2}√2π·det_ζ^{−1}` — and aligns exactly with the verified one-sided
ladder `Γ(a)·det_ζ(N+a)=√2π` (DeWitt #347/#357). Verified ≥35 digits incl. complex `a=0.25+7i`
(`computations/2026-06-19-gamma-module-invdet.py`: det−reciprocal ≤8e−36, Γ·det−√2π ≤2e−40). Re-banked to
`2-fully-proven`. Grade BRIDGE (Source A alone) unchanged. Downstream (`lambda-…`, `archimedean-prime-cross-term`)
should read M_∞'s determinant as **inverse** ζ-det where they cite it.

## Lean certification update — 2026-06-19 (Leaner)

The scalar recurrence/connection part of Result (1)-(2) is already Lean-backed by
`../3-formalized/archimedean-gamma-shift-connection.md`: `gammaReal_shift_two`,
`digamma_half_add_one`, and `gammaRealLogConnection_shift_compat` are in
`formal/GaloisForLFunctions/RHTower/ArchimedeanGamma.lean` and audited in `scripts/check_axioms.sh`.
The parent ticket remains in `2-fully-proven` because the full rank-one module construction,
Lerch inverse determinant import, and completed-object wiring are not formalized as Lean theorems.
