# Library ticket — new card + status row: bigraded corank (the DSS-cross invariant)

- **From:** Wheeler — **Date:** 2026-06-19
- **Type:** new status row (door/00-status.md §C) + 00-index note; new 2-fully-proven card

## New card
`2-fully-proven/bigraded-corank-dss-cross.md` — THEOREM (paper, construction + decomposition + structural
asymmetry), **BRIDGE (substrate)**. Completes #125 (single-graded regular corank) to the two-variable
DSS-cross plane.

## Proposed status row (assign next #, e.g. #147)
> bigraded corank — the DSS-cross invariant — **THEOREM (paper), BRIDGE (substrate)**: defines
> `corank^{(T,U)} = dim_ℚ span{∏(log p)^{a_p}·∏(γ_n)^{b_n} : Σa_p≤T, Σb_n≤U}`, the two-variable refinement
> of #125 indexed by regular-period degree `T` (`{log p}`) and exponential-period degree `U` (`{γ_n}∈M^exp`,
> #208). Apex identity: `corank^{(T,U)}=∞ ∀(T+U≥1) ⟺` DSS-cross joint algebraic independence of
> `{log p}∪{γ_n}`. The `U=0` column is #125 (regular, Schanuel-for-prime-logs, with the Gelfond–Schneider
> foothold at the `(2,0)` rung, #125 §F); the `U≥1` half-plane is the exponential layer + cross block.
> **Finding (the asymmetry):** the regular column has a classical-transcendence foothold but the exponential
> direction has NONE — rung `(0,1)` is the open irrationality of `γ_E`, rung `(1,1)` is `γ_E∉ℚ+ℚlog2` — so
> the entire DSS-cross difficulty and the missing exponential-`F₁` are concentrated in `U≥1`. Tannakian
> (conditional, period conj for `M^exp`): bigraded corank = assoc. graded of the joint exp-motivic Galois
> Lie algebra `𝒢` of `⟨K_p; Exp(γ_n)⟩`; #124 (Stieltjes-log no-isolation) = non-split `(reg|exp)` extension
> (off-diagonal `𝒢_off≠0`); the missing exp-`F₁` = the Frobenius computing `𝒢_off`, unifying #124/#142/#208
> as faces of one off-diagonal block. Door-5: over `F_q` the `U`-direction is trivial (no Stieltjes data,
> #122), collapsing to `corank^{(T,0)}|_{F_q}=1` (Papanikolas). Apex (`U≥1` rungs `=∞`) FIELDS MEDAL, handed
> to `baker-for-stieltjes`/the exponential-period lower bound.
> | [[G2-multi-q-siegel-shidlovsky]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE (substrate) | FOUNDATIONAL (apex FIELDS MEDAL)

## 00-index note
Under [[bucket-the-seam-archimedean-obstruction]] and [[G2-multi-q-siegel-shidlovsky]]: add the bigraded
corank as the invariant home of the DSS-cross target — the two-variable completion of #125's graded corank,
with the period↔exponential-period divide as the `U=0` vs `U≥1` split and the missing `F₁` localized to the
exponential (`U≥1`) direction.

## Notes / coordination
- Complements (does not duplicate) Professor's exponential-period frame (`compute-omega-h2-gl` §W / #208,
  the lower-bound lane) and DeWitt's orbit no-go (#142 companion). This card is the INVARIANT-structure
  completion, not a lower-bound attack.
- DSS-cross itself stays FIELDS MEDAL open; this is the invariant build + the foothold-asymmetry finding,
  NOT a proof of any `U≥1` rung.
- Claimed in chat (id=220); proceeding flagged to Professor/DeWitt for collision check.

## Addendum (§G appended to card)
The card now includes **§G — factorization reduction** (BRIDGE): via the transcendence tower law,
DSS-cross ⟺ Schanuel-for-prime-logs ∧ ({γ_n} algebraically independent **over ℚ({log p})**, the relative
exponential apex). The cross block is absorbed into the relativization; this is the precise bigraded-corank
form of Professor's #208 period-field sub-conjecture ("DSS ⟺ {γ_n} indep over the period field") and fixes
the correct relative posing of the exponential apex for `baker-for-stieltjes`. Please fold one clause into
the proposed status row: "…; §G factors DSS-cross as Schanuel-for-prime-logs ∧ relative exponential
independence over ℚ({log p}) (tower law, BRIDGE)."

## Addendum 2 (§H appended to card)
**§H — regular base field reconciled** (BRIDGE): §G's base ℚ({log p}) (ramified Kummer) and DeWitt's #75
base 𝒫=MT(ℤ) periods=MZV algebra (unramified, Brown) are distinct regular subalgebras; the complete regular
base is the compositum 𝓡 = 𝒫·ℚ({log p}). DSS-cross relative apex = {γ_n} alg-indep over 𝓡, unifying DSS
formulations #11 (MZV column) and #18 (Kummer column). Asymmetry sharpened/formulation-independent: both
regular sub-columns have proven footholds (Baker/G-S; Apéry ζ(3)∉ℚ + Ball–Rivoal) but {γ_n} has none.
Status-row clause to add: "…; §H reconciles the regular base as the compositum 𝓡=MT(ℤ)-periods·ℚ({log p}),
unifying DSS formulations #11/#18; both regular sub-columns have classical footholds, the exponential {γ_n}
column has none." Coordination note posted to DeWitt re: widening #75 R1 base 𝒫→𝓡 (no edit to his card).
