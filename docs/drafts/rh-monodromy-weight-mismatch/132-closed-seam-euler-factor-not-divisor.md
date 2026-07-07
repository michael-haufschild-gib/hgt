# 132 — Closing the cross-boundary seam: it recovers the Euler factor, not the divisor [PROVED HERE]

Formal home: `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean` §7 (all endpoints axiom-clean;
full `MainTheorems` gate green). Evaluates a proposed one-prime→global "Weil-cohomology" realization
(the `Δ_p ↦ C_p = Δ_p*Δ_p ↦ det ↦ divisor` pipeline) and locates precisely what it achieves and where
it still crosses the wall.

## 1. What the proposal fixes — correctly

Doc 131 §6 proved the open cross-boundary cochain is **traceless** (`crossBoundary_trace_zero`), so it
has no determinant of its own. The proposal's key correct move: **close the seam**. For the shell model
of `ℚ_p` the crossing is the rank-one partial isometry `Δ_p = |e_{p,0}⟩⟨e_{p,1}|`, and its closure

`C_p := Δ_p^* Δ_p = |e_{p,1}⟩⟨e_{p,1}|`

is a rank-one **projection** (`Tr C_p = 1`). Formalized concretely (`§7`): the open corner
`crossWitness = crossBoundary … = !![0,0;1,0]` is traceless (`crossWitness_trace_zero`), while its
closure `closedSeam = crossWitnessᵀ·crossWitness = !![1,0;0,0]` is a rank-one idempotent
(`closedSeam_idempotent`, `closedSeam_trace_one`). This genuinely resolves the tracelessness
obstruction: a closed seam carries a trace and a determinant. **Credited.**

## 2. The Euler factor is recovered — but it is zero-free [PROVED HERE]

`det(1 − λ·C_p) = 1 − λ` for the rank-one projection (`det_one_sub_smul_closedSeam`). With `λ = p^(−s)`
this is the local Euler factor `1 − p^(−s)`, so `det(1 − p^(−s)C_p)⁻¹ = (1 − p^(−s))⁻¹`, and the product
`∏_p` gives `∏_p(1 − p^(−s))⁻¹` on `Re s > 1`. This is correct and it is not the previous
reverse-engineered `Π`: no free `m`, no free `c_ρ`.

But the formalized determinant `1 − λ` **vanishes only at `λ = 1`** — the closed seam produces the
**zero-free** Euler factor. This is the same fact as doc 127 (`eulerPartial_zeroSet_eq_empty`): the
finite/local prime side has no zeros. Closing the seam recovers the **prime side**, not the divisor.

## 3. The decisive gap: the determinant lives only on `Re s > 1` — the wall, again

The pipeline defines `Z_fin(s) = det(1 − ⊕_p p^(−s)C_p)⁻¹` only where `⊕_p p^(−s)C_p` is trace-class,
i.e. `Σ_p p^(−Re s) < ∞`, i.e. **`Re s > 1`**. There, `Z_ξ = ξ` has **no zeros**, so `m_ρ = ord_ρ Z_ξ = 0`
for every `ρ` in the domain of definition: **on its own domain the construction detects no zeros.**

Every nontrivial zero is in the strip `0 < Re ρ < 1`, **outside** where the Fredholm determinant
converges. Step 5 of the proposal (`m_ρ := Res_{s=ρ} L_ξ`) silently evaluates `Z_ξ` at a strip `ρ` —
which requires the **analytic continuation** of the determinant across `Re s = 1`. The Fredholm
determinant does **not** supply it (the operator is not trace-class past the wall), and that
continuation *is* the classical continuation of `ζ`: the flow the mantra forbids (rule 7), i.e.
importing `ζ`. So the "produced" multiplicity `m_ρ` is produced only by reading the **already-continued**
`ξ` — it presupposes `ξ`'s divisor.

Three inserted-by-hand ingredients confirm the location:
- the weight `p^(−s)` in `det(1 − p^(−s)C_p)` — `C_p` contributes only "rank one"; the holomorphic
  `p^(−s)` is inserted (and `Δ_{p,s}^*Δ_{p,s} = |p^(−s)|²C_p` gives `|p|^(−2Re s)`, real, *not* the
  holomorphic `p^(−s)`);
- the archimedean factor `½s(s−1)π^(−s/2)Γ(s/2)` — inserted as "the fixed completion," so `Z_ξ := ξ`
  by definition;
- hence "the divisor of `Z_ξ`" = "the divisor of `ξ`" tautologically; reading it needs the continuation.

## 4. Verdict

The proposal is a real conceptual advance over the reverse-engineered `Π`: it correctly closes the
open seam (`Δ ↦ Δ*Δ`, the trace-bearing projection), correctly recovers the local Euler factor as a
determinant, and gives a canonical (parameter-free) germ-Fitting localization `m_ρ Y^{m_ρ−1}` — *given*
the divisor. But it does not produce the divisor. It rebuilds `Z_fin = ζ`'s Euler product on `Re s > 1`,
inserts the Γ-completion to define `Z_ξ = ξ`, and then reads `ξ`'s zeros — which requires continuing the
determinant across `Re s = 1`, exactly the wall of carrier-support disjointness (doc 127): the prime
determinant lives on `Re s > 1`, the divisor lives in the strip, and the only bridge is the
continuation of `ζ` — the flow. The smuggling moved from "reverse-engineered `Π`" (previous attempt) to
"silent analytic continuation of the Fredholm determinant past its convergence wall."

## 5. What would actually be required (the apex, unchanged in location, sharper in form)

For this to produce the divisor without importing `ζ`, the determinant would need an **intrinsic
continuation across `Re s = 1` that is not `ζ`'s classical continuation** — i.e. the functional equation
and the strip values would have to **emerge from the operator/seam structure**, not be inserted as the
Γ-factor. That intrinsic continuation of the closed-seam determinant is exactly the missing Weil
cohomology / Connes–Consani trace-formula content. The closed-seam move is the right first step —
it makes the crossing trace-class — and it sharpens the apex to a single, precisely located demand:
**continue `det(1 − ⊕_p p^(−s)C_p)⁻¹` past the trace-class wall by the seam's own symmetry.** That is
where the next genuine construction must act; every step up to the wall is now formal, and the wall is
the same one four independent lane results (docs 105, 106, 127, 131) have located.
