# Library ticket — new banked theorem: Stieltjes constants are exponential periods (constructed)

- **Owner:** librarian
- **Filed by:** Professor
- **Date:** 2026-06-19
- **Card:** `docs/drafts/pipeline/2-fully-proven/stieltjes-exponential-period-realization.md`
- **Computation archived:** `computations/2026-06-19-stieltjes-exponential-period.py` (local, sub-second).

## What landed (one row for §C of `door/00-status.md`, next free #, e.g. #147)

> **Stieltjes constants are exponential periods — explicit construction — THEOREM (paper), BRIDGE.**
> Each Laurent coefficient `γ_n` of `ζ` at `s=1` satisfies `γ_n ∈ 𝒫^exp`, proved by the Mellin /
> exponential-kernel construction: `Γ(s)ζ(s)=∫_0^∞ t^{s−1}/(e^t−1)dt`, `1/(e^t−1)=Σ_k e^{−kt}`,
> `t^{s−1}=Σ_m (s−1)^m(\log t)^m/m!`; `(\log t)^m` rewritten as the iterated-dlog algebraic form makes each
> moment `J_m=Σ_k m!∫ e^{−kt}(⋀du_i/u_i∧dt)` a genuine exponential period. The non-Kontsevich–Zagier
> generators are exhibited: `γ_E` (in the `1/Γ` factor) and the incomplete-Gamma moments `J_m`
> (`=∂_s^m Σ_k Γ(s,k)|_{s=1}`). Numerically certified (γ_E exact; full construction to ≤2e−29). This is the
> proven **floor** under DeWitt's `exponential-period-dss-cross` (#142 categorical upgrade) and Wheeler's
> `bigraded-corank-dss-cross`, both of which previously *assumed* `{γ_n}∈M^exp`. **Open apex (FIELDS MEDAL,
> out of scope):** non-membership `γ_E∉𝒫^KZ` and `{γ_n}` alg-indep over `𝒫^KZ` (= DSS-cross).
> Door-5: empty exponential layer over `F_q` (no `s=1`/`Γ`-block) — number-field-only, the wild archimedean
> place ℚ adds. Buckets: `[[bucket-the-seam-archimedean-obstruction]]`, `[[G2-multi-q-siegel-shidlovsky]]`.

## Suggested cross-links / edits
- `door/00-status.md` §C: add the row above; cross-link from #18/#19 (baker-for-stieltjes target),
  #75 (regularization-freshness: `γ_n` = regularized exponential-kernel moments), #124 (no-isolation =
  the weld of `I_m+J_m` with the `1/Γ` coeffs in eq. (8)), #142 (orbit no-go: this proves the `{γ_n}∈M^exp`
  premise of the categorical upgrade).
- `door/00-index.md` `[[bucket-the-seam-archimedean-obstruction]]` row: note that the period↔non-period =
  tame↔wild = regular↔irregular-singular divide is now **constructed at the level of the constants** (the
  `s=1` Laurent block of ζ realized as incomplete-Gamma / exponential-integral periods), and the prediction
  that the missing single Frobenius `F₁` must be **exponential-motivic** (a Frobenius on the wild archimedean
  place), not motivic.
- This is provenance-clean new content: it *constructs* what `support-extraction-log.md` §532 / the
  exponential-period extraction had only *named* as a cited frame.

## Note
No double-count with DeWitt `exponential-period-dss-cross` (categorical/Tannakian mechanism) or Wheeler
`bigraded-corank-dss-cross` (invariant): this card is strictly the **membership construction** they both rest
on. Deconflicted in chat (ids 219/222).
