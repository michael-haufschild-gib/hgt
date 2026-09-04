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

## Kernel representations (2026-09-04, verified numerically to 8 digits)

Write `c(x) = thetaCuspLogCurvature x = −ℓ''(x)` (positive, even, `c'' > 0` on `[0, 6]` numerically),
and for fixed `u` let `e(s) = (c(u+s) + c(u−s))/2`, `o(s) = (c(u+s) − c(u−s))/2` (even/odd parts),
`E(t) = ∫₀ᵗ e`, `O(t) = ∫₀ᵗ o`.  Then `Φ_t = 2E`, `Φ_u = 2O`, `Φ_tt = 2e`, `Φ_ut = 2o`, and

```text
H = 4 [ t e(t) ∫₀ᵗ (t−r) r o''(r) dr  −  (∫₀ᵗ s e'(s) ds)(∫₀ᵗ s o'(s) ds) ]   =: 4 (T₁ − T₂),
G = tḢ − 5H = 4 [ O·Δ_e − E·Δ_o ],
      Δ_e = ∫₀ᵗ r (e'(r) − r e''(r)) dr = O(t⁵),   Δ_o = 5t·o(t) − 8O − t²o'(t) = O(t⁶).
```

Both are exact and bilinear in `(e, o)`; the `t³`-cancellation of `H` and the `t⁵`-cancellation of
`G` are built into the kernels.  For the pure exponential model `c = 4A e^{2s}`:
`H = −16A² z (sinh 2t − 2t)`, `G/4 = A²(16t²S − 16tz² − 56tz + 20Sz)`, `T₂/T₁ = 1 + 1/(4t(t−1))`
for large `t`.

Numerical margins on the tail: `T₂/T₁ ∈ [1.10, 7.7]` (so `H < 0`, but the relative margin decays
like `1/(4t²)` at large `t`, where the right endpoint `x = u + t` dominates and the model is exact
to `O(e^{−4(u+t)})`); the assembly hypothesis `5|G| ≤ 6Φ(−H)` holds with ratio `≤ 1/6`.

## Order data of the completed curvature (numerical, `[0, 6]`)

`c' > 0`, `c'' > 0` and the projective energy `c'c'' − c·c''' > 0` hold on `(0, 6]`, but `c''' > 0`
**fails** for `x ≲ 0.3` (`c'''(0.2)/(32A) = −0.62`).  Hence the corpus far-tail chain
(`exists_c5CompletedVelocityCenterNumerator_neg_farTail`, private lemmas needing all four order
facts on `[x₀, ∞)`) cannot be pushed to `x₀ = 0` as it stands; the corner `u − t ≲ 0.3` needs the
kernel representation directly (there the margin `T₂/T₁ ≈ 7` is largest).  Near `x = 0` the
deviation from the exponential model is large (`c(0)/4A(0) = 1.49`, `J₂(0) ≈ 0.84`), so the
likelihood corrections are `O(1)` on `[0, 0.32]` and exponentially small beyond `A ≥ 6`.

## Reduction of the three hypotheses to sign facts about `c` (2026-09-04, evening)

Notation as above; `x₋ = u − t ≥ 0`, `x₊ = u + t`; `c, c', c''` evaluated at `x±`.

**(b) `v ≥ 2Φ`** ⟸ `c'' ≥ 0` on `[0, ∞)`.  Proof: `v − 2Φ = 2(tE − 2∫₀ᵗE)`, and `E(s)/s` is
nondecreasing when `e` is nondecreasing on `[0, t]`, i.e. `e'(s) = (c'(u+s) − c'(u−s))/2 ≥ 0`, i.e.
`c'` nondecreasing on `[x₋, x₊]`.

**(a) `H < 0`** ⟸ two monotone-l'Hospital descents of `ρ = O/(tE)` (`N = O, D = tE`; then
`N₂ = o, D₂ = E + te`) reduce strict decrease of `ρ` to strict decrease of
`r₃ = o'/(2e + te')`, i.e. to the two-point inequality

```text
(∗)  (c''₊ − c''₋)[2(c₊ + c₋) + t(c'₊ − c'₋)]  <  (c'₊ + c'₋)[3(c'₊ − c'₋) + t(c''₊ + c''₋)],
```

verified numerically on the tail with `LHS/RHS ∈ [0.13, 0.88]` (`→ 1 − 1/(2t)` at large `t`).
Expanding, `RHS − LHS = Q(x₋, x₊) + 2t(c'₊c''₋ + c''₊c'₋)` with
`Q(y, x) = 3(c'(x)² − c'(y)²) − 2(c''(x) − c''(y))(c(x) + c(y))`, `Q(y, y) = 0`, and
`∂ₓQ ≥ 4(c'c'' − c c''')` where `c''' ≥ 0`, `∂ₓQ ≥ 4c'c''` where `c''' < 0`.  Hence

```text
(a) ⟸ (R1) c > 0, (R2) c' ≥ 0, (R3) c'' ≥ 0 on [0, ∞), (R4) c'c'' − c c''' ≥ 0 wherever c''' ≥ 0.
```

`(R1)` is `thetaCuspLogCurvature_pos`; `(R4)` is the corpus's projective energy
`thetaCuspCompletedCurvatureProjectiveEnergy`, proved only cofinally so far; numerically
`E(x) > 0` on `(0, 6]` and `E(0) = 0` with `E'(0) = c''(0)² − c(0)c⁗(0) > 0` by a 12 % margin.
The model (`c = 4Ae^{2x}`) gives `RHS − LHS = 128A²(sinh 2t cosh 2t + 2t)`.

**(c) `5|G| ≤ 6Φ(−H)`.**  With `w' = te/E`, `M := o'·tE − O·(2e + te')` (the second transport
numerator), `t(log κ)' = 4tM/H − 2 − 2w'`, so `(c)` follows from

```text
10(w − 2) ≤ 1.6Φ      [⟸ e' ≥ 0, c''/c ≤ q_max, c(u) ≥ 4A(u) ≥ 24; numerically (w−2)/Φ ≤ 0.061]
4t|M| ≤ (3 + 2w' + 0.88Φ)|H|   [numerically 4tM/H − 3 − 2w' = t(log κ)' − 1 ≤ 0.0042Φ; slack ≈ 200×].
```

The second inequality is the only remaining item without a local reduction; in the descent
language `4t|M|/|H| = [tD₂'/D₂]·[(ρ − r₃)/(ρ − r₂)]` with `ρ ≥ r₂ ≥ r₃`, all three tending to
`1` as `t → 0`.

## Lean plan (ordered)

1. `ThetaCuspC5CompletedGateReduction` (written; compiling): identities, Bose floor, assembly.
2. Structural layer: `(b)` from `(R3)`; `(a)` from `(R1)–(R4)` via the two descents and `Q ≥ 0`
   (the corpus's private `completed_strictAntiOn_div_of_strictAnti_derivRatio` in
   `ThetaCuspCompletedVelocityCenterFarTail` is the descent lemma; re-prove publicly).
3. Sign facts `(R2)`, `(R3)`, `(R4)` on the whole half-line: first-atom rational part explicit,
   likelihood jets `J₂ … J₅` bounded by the moment machinery (`twelve_mul_thetaCuspLikelihoodMean…`,
   `…TailProbability_lt_thirtyFive_mul_exp_neg_three_scale`); `(R4)` near `x = 0` is the delicate one.
4. `(c)`: the `w − 2` bound, then `4t|M| ≤ (3 + 2w' + 0.88Φ)|H|`.
