# LI Euler jets: source-dependent boundary layer

- **ID:** LI-EJ-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); novelty/significance unverified
- **Parent:** `li-even-euler-jet-small-mass-crossover.md`
- **Objective:** retain the first positive source correction at the integer crossover, with quantified rounding and no signs assumed for later moments.

## Exact statement

Write `M_j=normalizedPrimeArchMoment j`, `A=xiShiftAbsoluteMass 0`,
`τ=M_1/M_0`, `a=2−log(3)/log(2)`,
`x(v)=[log(1/v)−log(4τ)]/log(4)`,
`B=9M_2(4τ)^(−log(3)/log(2))`,
`c_1=B/(M_0 log(4))`, and `c_2=c_1² log(9/2)`.

Source sector positivity proves `M_0,M_1,M_2,A,c_1,c_2>0`; `0<a<1/2` follows from `3<4` and `8<9`.
For each `ε>0`, eventually for every positive mass tending to zero, least negative actual even Euler jet index satisfies

`floor[x(v)+c_1 v^a+(c_2−ε)v^(2a)]+1 ≤ K(v) ≤ floor[x(v)+c_1 v^a+(c_2+ε)v^(2a)]+1`.

In particular, along a sequence with `[k−x(v)−c_1v^a]/v^(2a)→λ`,

`[J_k(v)/(2v)]/v^(2a) → M_0 log(4)(c_2−λ)`.

This supplies strict signs when `λ≠c_2`. The exact critical layer `λ=c_2` is unresolved by this statement. No real-order jet interpolation is assumed.

## Dependency-closed paper proof

1. Actual fixed-order source expansion is `J_k(v)/(2v)=Σ_{n≥0}(−1)^n(n+1)^(2k+2)M_n v^n` for `0<v≤1/4`. Exact jet-series leaf passed Lean and axiom audits. Separate fixed-order differentiation from all growing-order estimates.
2. Existing source envelope is `|M_n|≤A/150^n`, from `XiReciprocalSquareSecondMomentRadius.lean`. For `r=n+4`, elementary induction gives `r²≤16·2^n` and `r²≤16·4^n`. Set `p=2^k v/150`. The tail beyond the third term has absolute bound
   `16A·16^k v³/150³ Σ_n(4p)^n ≤32A(4^k v)²v/150³`
   whenever `p≤1/8`. This keeps every later source moment without a sign assumption.
3. For bounded `u=k−x(v)`, `w=4^k v` stays bounded and `p²=w v/150²→0`, so the preceding tail is `O(v)`. The exact first three terms give uniformly
   `J_k(v)/(2v)=M_0(1−4^u)+B9^u v^a+O(v)`.
4. The two-exponential expression has strictly negative derivative in a fixed neighborhood of zero for all sufficiently small mass. Taylor expansion at `u=c_1v^a+λv^(2a)` yields the displayed limit, because `O(v)=o(v^(2a))`. Quadratic matching gives `c_2=c_1²(log(9)−log(4)/2)=c_1²log(9/2)`.
5. Uniform positivity of all earlier indices follows by isolating the strictly positive `M_2` term. Lean sharpened its remaining-tail bound to `32Aq³`, where `q=3^k v/150`, by comparing `16^k≤27^k` in the preceding complete-tail theorem. Thus every `k≤x(v)` stays positive for small mass, including integer ties. The two-exponential model is strictly decreasing throughout `[0,2]` for small mass. Endpoint margins and uniform `O(v)=o(v^(2a))` error give signs throughout the relevant sides; upper floor witness has offset between the upper threshold and two. These facts give the floor sandwich without monotonicity or interpolation of actual jets.

## Status and significance

- Stronger statement arose from a hostile audit of the original two-term crossover; recorded separately before adding Lean claims.
- Original crossover is Lean-closed in the parent card. `LiEvenCrossEulerThirdMassRemainder.lean` proves exact first three source terms and the complete `32A(4^k v)²v/150³` bound; named build, final exact check and foundation-only axiom audits passed.
- `LiEvenCrossEulerCrossoverThreeTermProfile.lean`, `LiEvenCrossEulerBoundaryLayerExpansion.lean`, `LiEvenCrossEulerThirdTermDominance.lean` and `LiEvenCrossEulerSourceBoundaryLayer.lean` passed named builds, final exact leaf checks and foundation-only axiom audits. They supply literal actual source model plus uniform `O(v)` error, positive amplitude and `0<a<1/2`, exact generic second-layer coefficient, strict model monotonicity, every earlier `k≤x(v)` positive, and the exact two-layer Nat.floor sandwich. Root spot-checked the floor capstone and strict positivity.
- `LiEvenCrossEulerSourceBoundaryLimit.lean:133` proves the exact arbitrary-filter variable-drift limit for actual natural-order jets. Its strict-sign corollaries are at 237 and 263. Named `--old` build passed with no leaf warnings; final exact `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossEulerSourceBoundaryLimit.lean` passed with no output. All three capstones' scratch axiom checks returned only `propext`, `Classical.choice`, `Quot.sound`. Root spot-checked the literal limit statement, squeeze argument and both sign corollaries. Every displayed claim is now closed; the critical zero-limit drift remains explicitly unresolved.
- All six boundary leaves are wired into `GaloisForLFunctions/RHTower.lean`. Latest whole-tree lint remains red on 13 unrelated unreachable modules (`/tmp/hgt-li-current-window-clock-lint.log`); this card records targeted source validation, not a clean global gate.
- No route retired. This is an exact source-sign boundary, not an arithmetic RH producer or proof of individual LI-current negativity.
- Generic coefficient-ratio crossover has public overlap already recorded on the parent card. No worldwide novelty claim is made.
- Independent hostile audit confirmed second coefficient and floor sandwich. Durán's Theorems 2–3 and Lemma 6 overlap binary scaling, adjacent coefficient competition and first-root isolation under positive multiplier hypotheses. Inspected paper did not supply these two corrections, but their Taylor mechanism is generic. Surviving source insight is the positive actual third moment's delay, admitting arbitrary signs afterward; no deeper arithmetic relation among `M_0,M_1,M_2` is established.

## Log

- 2026-09-29 — Independent source/normalization audit derived the positive third-term correction and second boundary coefficient. Dependency-closed proof recorded; numerical experiments absent.
- 2026-09-29 — Complete floor sandwich and variable-drift actual-jet limit passed final Lean and axiom audits. Promoted only after both capstones and their exact source dependencies were closed. RH remains open.
