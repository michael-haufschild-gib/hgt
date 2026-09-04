# Theta C5 completed compensation: the direct gate `M(1) > 0`

- **ID:** CLG-TTF-C5-completed-compensation-direct-gate
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET (finite special-function inequality, no RH content of its own)
- **Source:** `theta-c5-likelihood-homotopy-curvature.md` (numerical survival 2026-09-04), corpus
  `ThetaCuspFixedActionC5LikelihoodLiftReduction`, `ThetaCuspFixedActionC5Jacobian*`,
  `ThetaCuspReflectedActionVelocityBalance`

## Exact claim

```text
[TARGET]  0 < t < u,  6 ≤ π e^{2u}   ⟹   0 < c5CompletedCompensationMargin u t.
```

By `thetaCuspReflectedActionC5FixedActionJacobian_pos_iff_completedCompensation` this is strict
direct-J orientation `0 < thetaCuspReflectedActionC5FixedActionJacobian u t` on the structural
tail, i.e. the compact-seam burden of CLG/TTF.  It is the right endpoint `M(1)` of the likelihood
homotopy (`thetaCuspC5LikelihoodHomotopyCompensation_one`); `M(0) > 0` is the corpus theorem
`c5SingleAtomCompensationMargin_pos_of_sameHalfLine`.

## Structure (derived 2026-09-04, verified numerically to 45 digits)

Write `Φ(u,t) = thetaCuspCompletedReflectedCumulantAction u t` (`= thetaCuspReflectedLogAction` on
`t < u`), the completed reflected action of the full theta-cusp source
`ℓ(x) = log Σ_{n≥1} n²(n²A(x) − 3/2) e^{−n²A(x)}`, `A(x) = π e^{2x}`:
`Φ = 2ℓ(u) − ℓ(u+t) − ℓ(u−t)`.  The seven completed jets are `Φ_t, Φ_tt, Φ_ttt, Φ_u, Φ_ut, Φ_utt`
and `Φ` itself, and

```text
H := Φ_t·(tΦ_ut) − (Φ_t + tΦ_tt)·Φ_u            (completed centre numerator)
P := Φ_t·(tΦ_ut + t²Φ_utt) − (Φ_t + 3tΦ_tt + t²Φ_ttt)·Φ_u
W := 14 + 10·tΦ_t + 8·tΦ_t/(e^Φ − 1)             (Bose weight)
M(1) = 5P − W·H.
```

Two identities (pure calculus, once the jets are derivatives):

```text
(I1)  P = H + t·∂_t H.
(I2)  H = t² Φ_t² · K,   K := ∂_t ( Φ_u / (t Φ_t) ).
```

Hence, with `w := 1 + tΦ_tt/Φ_t` (the corpus's `thetaCuspReflectedActionVelocitySlope`) and
`κ := −K`,

```text
M(1) = t² Φ_t² · [ 5t·K' + (5 + 10w − W)·K ],
M(1) > 0  ⟺  W > 5 + 10w + 5·t·(log κ)'     (given Φ_t > 0, K < 0).
```

Both sides tend to `30` as `t → 0` (`w → 2`, `t(log κ)' → 1`), so the sign is decided by the
next order: `W − 30 = 10v + 8v/r − 16` with `v = tΦ_t`, `r = e^Φ − 1` (`≈ 12Φ`), against
`10(w − 2) + 5(t(log κ)' − 1)`.  Numerically the ratio `(W − 30)/(10(w−2) + 5(t(logκ)'−1))` is
`≥ 40` throughout the tail (`330` at `u = 1.2, t = 0.05`; `44` at `(0.5, 0.2)`; `67` at
`(0.4, 0.39)`).  This is the margin a proof has to realise; it is far larger than the `0.19`
relative margin of the homotopy endpoint itself, because the prefactor `t²Φ_t²K` carries all
the small-`t` cancellation.

## Proof plan

1. `[LEAN]` (I1) and (I2) as algebraic identities of the literal jets, and the factorisation
   `M(1) = t²Φ_t²[5tK' + (5 + 10w − W)K]`.
2. `[LEAN/CORPUS]` `Φ_t > 0`, `K < 0` (equivalently `H < 0`) on the tail — check corpus sign
   theorems for the completed jets (`thetaCuspReflectedLogJetOne`, centre numerator).
3. Lower bound `W − 30 ≥ 4Φ` (from `v ≥ 2Φ − O(t⁴)` and `e^Φ − 1 ≤ Φe^Φ`).
4. Upper bounds `w − 2 ≤ c_w·Φ`, `t(log κ)' − 1 ≤ c_κ·Φ` with `10c_w + 5c_κ < 4`, from the
   Riccati/monotonicity theory of `ℓ', ℓ'', ℓ'''` in the corpus, split into `t ≤ t₀` (Taylor with
   remainders) and `t ≥ t₀` (crude growth bounds against `W − 30 ≥ 12·2Az`).
5. Assemble; wire; record.

## Log

- 2026-09-04 — Card opened after the numerical survival of the homotopy core.  Structure (I1),
  (I2) and the first-order criterion found and verified at 45 digits
  (`2-fully-proven/computations/clg-ttf-c5-homotopy-numerical-test/clg_structure.py`).
