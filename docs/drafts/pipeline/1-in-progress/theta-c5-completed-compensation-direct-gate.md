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

## Sign facts: first-atom part versus likelihood jets (numerical, 2026-09-04)

`c = c₁ − J₂` with `c₁ = 4A + 6A/(A − 3/2)²` (first atom) and `J_k = LP^{(k)}` the likelihood jets:

| x | c₁' | J₃ | c₁'' | J₄ | J₄/c₁'' | c₁''' | J₅ |
|---|---|---|---|---|---|---|---|
| 0.0 | −14.42 | −14.42 | 371.8 | 228.8 | 0.62 | −3378 | −3378 |
| 0.1 | 11.45 | −2.62 | 184.9 | 48.6 | 0.26 | −928 | −810 |
| 0.2 | 26.74 | −0.33 | 132.1 | 7.62 | 0.058 | −250 | −158 |
| 0.3 | 39.21 | −0.025 | 121.5 | 0.73 | 0.006 | 4.8 | −19.3 |
| 0.5 | 65.37 | −2e−5 | 147.2 | 8e−4 | 5e−6 | 225 | −0.03 |

* `(R2)` `c' = c₁' − J₃ ≥ c₁' > 0` for `x ≥ 0.1` (since `J₃ < 0`); on `(0, 0.1)` the likelihood
  term carries the sign (`c'(0) = 0`, `c''(0) = 143`).
* `(R3)` `c'' = c₁'' − J₄ > 0` with margin `≥ 38 %` (worst at `x = 0`); needs upper bounds on `J₄`
  of size `≈ 230` at `A = π`, `≈ 50` at `A ≥ 3.8`, `≈ 8` at `A ≥ 4.7`; the corpus's uniform
  `J₄ < 2432` is too weak, its scale-indexed families are the right tool.
* `(R4)` is needed only where `c''' ≥ 0`, i.e. `x ≳ 0.28`; there `c''' = c₁''' − J₅ ≥ c₁''' > 0`
  (`J₅ < 0`) and `E = c'c'' − c c''' ≫ 0`.  On `(0, 0.28)` we have `c''' < 0` (`c⁗(0) < 0`), so
  `E > 0` holds automatically; the earlier worry about a 12 % margin at `x = 0` was a sign error.
* All three are robust two-level-system statements: at `A = π` the `n = 3` atom is `10⁷` times
  smaller than the `n = 2` atom, so closed forms with the `n = 2` atom plus a remainder bound suffice.

## Lean status

* `C5FixedActionDescentLemmas` (Mathlib-only): strict monotone l'Hospital (`deriv_cross_lt…`,
  `strictAntiOn_ratio…`), `twoPointCurvatureGain_nonneg`, chord bound — compiled, wired.
* `ThetaCuspC5CompletedGateReduction`: excess form, Bose floor, assembly — written, awaiting the
  dependency build.
* `ThetaCuspC5CompletedGateSigns`: `(b)` from `(R3)`, `(a)` from `(R1)–(R4)` — written, awaiting
  the dependency build.

## Regime I (`A(u − t) ≥ 6`): explicit plan for the sign facts (2026-09-04, pod `clg_moments.py`)

Corpus decompositions on `x > 0`: `c' = BW₃ − J₃`, `c'' = BW₄ − J₄`, `c''' = BW₅ − J₅` with
`BW_k = thetaCuspBornWittenLog{Third,Fourth,Fifth}Derivative 1 x` (explicit rational functions of
`B = A − 3/2`: `BW₃ = 2A(4 − 6/B² − 18/B³)`, `BW₄ = 2A(8 + 12/B² + 108/B³ + 162/B⁴)`) and
`J_k = thetaCuspLikelihoodSourceLogPartitionJet_k` (via `iteratedDeriv_{three,four,five}_…_eq_full_jets`
and `…_eq_higherLikelihoodLogJet…`).

Normalized moments `NM_k = M_k/Z` of the higher likelihood state, for `A ∈ [6, 26]` (and monotone in
`A`): `NM_k ≤ C_k e^{−3A}` with `C = (20.0, 60.9, 185.7, 567.8, 1740.7, 5354.1)` for `k = 0…5`; these
are the `n = 2` closed forms at `A = 6`, `16·3^k + 18 Σ_{j≤k} k!/j!·3^j/B^{k−j+1}`; the `n ≥ 3` atoms
contribute a relative `5·10⁻¹³`.  Cumulants: `|κ₃| ≤ NM₃(1 + 3NM₀ + 2NM₀²)` etc. by the corpus
`thetaCuspHigherLikelihoodSpectralMoment_mul_le_tailMass_mul`.  Hence
`|J₃| ≤ 5300·A³e^{−3A}`, `J₄ ≤ 2·10⁴·A⁴e^{−3A}`, `|J₅| ≤ 1.2·10⁵·A⁵e^{−3A}` (numerically `3813`,
`1.9·10⁴`, `9·10⁴`), against `BW₃ ≥ 8A − 6`, `BW₄ ≥ 16A`, `BW₅(A=6) ≈ 42`, `E₁(A=6) ≈ 4055`.
All four sign facts then hold on `[0.3235, ∞)` with margins `≥ 10⁴`.

The corner regime `A(u − t) < 6` (i.e. `t > u − 0.3235`) needs `J₄ < BW₄` on `[0, 0.32]` with
`J₄(0) = 229` vs `BW₄(0) = 372`; this is a chamber-wise two-level-system computation
(`J₄` decreasing from `229` to `0.7`, `BW₄` from `372` to `121`), to be done after regime I.

## 2026-09-04 (late): structural layer and regime I are Lean theorems; the gate is one growth bound

**Exact criterion (new form).**  Since `M(1) = (W − 30)(−H) + 5G` and `G = tḢ − 5H`,
`M(1) = (W − 5)(−H) + 5tḢ`, so with `H < 0`

```text
M(1) > 0   ⟺   t·∂ₜ log(−H) < (W − 5)/5,      (W − 5)/5 ≥ 5 + 2.4Φ  (Padé floor, from v ≥ 2Φ).
```

Hence the whole gate is `H < 0` plus the growth bound `t·∂ₜ log(−H) ≤ 5 + 2.4Φ` (equivalently
`5|G| ≤ 6Φ(−H)`).  Pod scan (`clg_cmargin.py`, 80 points, `x₀ ∈ [0, 2]`, `t ∈ [0.02, 3]`): the
excess `t∂ₜlog(−H) − 5` is at most `5.2 %` of `2.4Φ` (tightest at `x₀ ≈ 0.32`, `t = 0.02`, ratio
`1/19`), and at most `0.1 %` for `t ≥ 1`.  Pure-exponential model (`ℓ₀ = −A`): `H ∝ A²·h(t)`,
`h = sinh²(2t)(t sech²t − tanh t)`, `t h'/h − 5 ≈ (16/15)t²` versus `2.4Φ ≈ 9.6A t²`.

**Lean (all compiled, wired after `C5FixedActionDescentLemmas`, `lake build` clean):**

| module | content |
|---|---|
| `ThetaCuspC5CompletedGateReduction` | excess form, Padé floor `(x−2)eˣ + x + 2 ≥ 0`, `12Φ ≤ W − 30`, assembly `c5CompletedCompensationMargin_pos_of_bounds (H<0) (2Φ≤v) (5|G| ≤ 6Φ(−H))` |
| `ThetaCuspC5CompletedGateSigns` | even/odd curvature data, `two_mul_action_le_velocity_of_jetTwo_nonneg` (`(b)` from `c'' ≥ 0` on `[u−t, ∞)`), `local_ratio_deriv_neg` (two-point inequality `(∗)` from `Q ≥ 0` + `2s(j₊j₂₋ + j₂₊j₋) > 0`), `centerNumerator_neg_of_curvatureSigns` (`H < 0` from `(R2)–(R4)` on `[x₀, ∞)`, `x₀ ≤ u − t`, via the two monotone-l'Hospital descents and `H = 4(o·tE − O(E + te))`) |
| `ThetaCuspC5RegimeOneCurvatureSigns` | sharp support comparison `M_m(B) ≤ 3^m e^{−3δ} M₀(B − δ)` for `δ ≥ m/3`; `NM_m ≤ 3^m ε(x)`, `ε = e^{−3(A−π)}/399`; cumulant majorants `9ε, 28ε, 82ε, 244ε`; jet majorants `|J₂| ≤ 38A²ε, |J₃| ≤ 261A³ε, |J₄| ≤ 1800A⁴ε, |J₅| ≤ 12900A⁵ε`; decompositions `c⁽ᵏ⁾ = BW_{k+2} − J_{k+2}`; identity `BW₂BW₅ − BW₃BW₄ = −(2q+3)²(1296q⁴ + 4536q³ + 4536q² + 2916q + 2916)/q⁷`; `(R2)`, `(R3)`, `(R4)` for `A ≥ 6` (chambers `[6,7]`, `[7,10]`, `[10,∞)` with `|D| ≥ 1835, 583, 5184/A` against `err ≤ 58100A⁶ε ≤ 1328, 167, 1.8/A`) |
| `ThetaCuspC5RegimeOneGate` | `centerNumerator_neg_of_regimeOne`, `two_mul_action_le_velocity_of_regimeOne` (unconditional for `A(u−t) ≥ 6`), and `c5CompletedCompensationMargin_pos_of_regimeOne (hG : 5|G| ≤ 6Φ(−H))` |

**Open (exact).**  (i) the growth bound `5|G| ≤ 6Φ(−H)` on `0 < t < u`; (ii) the corner regime
`A(u − t) ∈ [π, 6)` for `(R2)–(R4)`: there `J₄(0) = 229` vs `BW₄(0) = 372`, so the two-atom explicit
model `ℓ₂ = −A + log(A − 3/2 + (16A − 6)e^{−3A})` (n ≥ 3 remainder `≤ 10⁻⁷` relative at `A = π`,
decaying like `e^{−8A}`) must be handled chamber-wise; note `c` is even (`thetaCuspLogCurvature_neg`),
so `c'(0) = c'''(0) = 0` and `(R4)` is vacuous on `(0, 0.28)` where `c''' < 0`.

**Structure of (i) found today.**  `N := H/4 = E·Λ − O·Y` with `Λ = ∫₀ᵗ (t−r) r o''(r) dr`,
`Y = ∫₀ᵗ s e'(s) ds` (both `O(t⁴)`, `O(t³)`), `N ≈ (t⁵/12)(c c''' − 2c'c'')`.  Writing
`D = OY − EΛ > 0`, `t D'/D = a + (a − b)·EΛ/D` with `a = to/O + t²e'/Y`, `b = te/E + tΛ'/Λ` (each
`5 + O(t²)`), and `EΛ/D → c c'''/(2c'c'' − c c''') ≤ 1` exactly by `(R4)`.  The natural sufficient
condition is a family of log-derivative bounds `|g'(s)/g(s)| ≤ κ s` for the four averaged
integrands (`κ ≈ 4/3, 4/3, c''/c ≤ 8, c⁽⁵⁾/(5c''') ≈ 0.8` in the pure model) with total budget
`≈ 10` against `2.4c ≥ 58`; the difference structure needs `EΛ ≤ K·D` globally (weighted descent).

## 2026-09-04 (night): frozen-jet growth bound in Lean; regime-I plan fixed

**Lean (compiled, wired, axioms clean):** `C5FrozenJetTaylorBounds` (monotone comparison lemma
`|h'| ≤ K s^k ⇒ |h| ≤ K s^{k+1}/(k+1)`, frozen-jet expansions of a `C⁴` chain),
`C5FrozenJetGrowthBound` (even/odd data, closed-form auxiliaries `K₁ = t²o₁ − 5to + 8O`,
`K₂ = 3te − 3E − t²e₁`, `Λ = to − 2O`, `Y = te − E`; identities `tM − 5N = E·K₁ + O·K₂`,
`N = EΛ − OY`; component bounds `|K₁| ≤ (2/45)S₅t⁶`, `|K₂| ≤ (2/15)S₄t⁵`,
`|Λ − c₃t⁴/12| ≤ S₅t⁶/180`, `|Y − c₂t³/3| ≤ S₄t⁵/30`, `|E − c₀t − c₂t³/6| ≤ S₄t⁵/120`,
`|O − c₁t²/2 − c₃t⁴/24| ≤ S₅t⁶/720`), `ThetaCuspC5FrozenJetGate` (`H = 4N`, time jet `= 4M`,
`G = 4(tM − 5N)`, `|Φ − c₀t² − c₂t⁴/12| ≤ S₄t⁶/360`, strict assembly
`5|G| < 12Φ(−H) ⇒ M(1) > 0`, and `growthBound_of_frozenJets`: the growth bound follows from one
explicit numeric inequality `hkey` in `c₀…c₃, S₄, S₅, t`).  Truncated polynomial parts of `tM`
and `5N` cancel exactly, so no interval integrals are needed.

**Numerics (pod `clg_frozen.py`, true theta jets):** with the improved `K_N = c₀S₅/180 + c₁S₄/60`
the bound certifies `t ≤ 0.5` in regime I and `t ≤ 0.3` in the corner (margins 3–13×);
with crude jet ranges the discharge loses the `A = 6` correlations (`clg_hkey.py`), so the
discharge must use the exact Born–Witten jets at `u` and endpoint sup bounds.

**Regime-I plan (all `t`):**
* `t ≤ 0.3`: `growthBound_of_frozenJets` with jets `c_k(u) = BW_{k+2}(q) ∓ |J_{k+2}|` and
  `S₄ ≤ max ends of 2A(32 + 90.2(4.5/q)²)`, `S₅ ≤ max ends of 2A(64 + 780(4.5/q)³)` (+ `J₆, J₇`),
  chambers in `q(u)`.
* `t ≥ 0.3`: perturbation from the corpus single-atom gate.  The corpus proves
  `M(0) = c5SingleAtomCompensationMargin A t > 0` via
  `base = (2A + λ/r)(4A + d/r)·shape(t) + correction`, `shape(t) = z((25+72z)e − t(140+328z)) + 20t²e`
  (`z = cosh 2t − 1`, `e = 2 sinh 2t`, `shape ~ t⁷`), `correction > 0`, `M(0) > base`; so
  `M(0) ≥ 2A(4A − 6)·shape(t)`.  The homotopy data splits every jet as single-atom + likelihood
  (`a + da`, …); for `A(u−t) ≥ 6` the `d`-jets are `≤ 10⁻³` relative (`|J₂| ≤ 38A²ε` etc.), and
  a naive bound `|M(1) − M(0)| ≤ Σ|∂M||d-jet|` (no cancellation needed for `t ≥ 0.3`) is
  `≈ 30` against `M(0) ≥ 150` at `A(u−t) = 6, t = 0.3`, improving with `t` and `A`.
  This also bypasses `H < 0` and `v ≥ 2Φ` for `t ≥ 0.3`.

**Corner (`A(u−t) < 6`) remains:** the first-atom jets are far from the true ones at `x ≈ 0`
(`J₃(0) = −14.4 = c₁'(0)`), so the perturbation must be from a two-atom model, for which no corpus
gate theorem exists; `c` even gives `c'(0) = c'''(0) = 0`.

## 2026-09-05: regime I for `t ≥ 1/4` reduced to one explicit numeric inequality (Lean)

`ThetaCuspC5RegimeOnePerturbation` (compiled, wired, axioms clean):
* §1 public certificate series: `c5HyperbolicGaussianBaseShape t = 2·cert(2t)`,
  `cert x = Σ_n term_n(x)` with `term_{k+1} = (54·9^{k+1} − (160+82(k+1))4^{k+1} + 20(k+1)² + 268(k+1) + 194)·x^{2k+3}/(2k+3)!`,
  all `≥ 0`, hence `shape(t) ≥ (6656/9)t⁷ + (615872/945)t⁹ + (50560/189)t¹¹`.
* §2 correction jets in regime I: `|da| ≤ 12A₋ε₋`, `|db|,|dm| ≤ 76A₋²ε₋`, `|dc|,|dn| ≤ 522A₋³ε₋`,
  `|ds| ≤ 24A₋ε₋`, `|dq| ≤ 4ε₋` (`|J₁| ≤ 6Aε`, `0 ≤ LP ≤ ε`, monotone transport `A^kε` from `u−t`).
* §3 single-atom jets for `A ≥ 6`: `λ ≤ 6/A`, `|d| ≤ 18/A`, `1/2 < r ≤ 1`, hence
  `|a| ≤ (2A + 12/A)z'`, `|b| ≤ 4(12/A)²z(z+2) + 4(2A+12/A)(z+1)`, `|c| ≤ z'(8(12/A)³z(z+2) + 12(12/A)²(z+1) + 4(2A+12/A))`,
  `|s| ≤ 4Az + 36z/A`, `|m| ≤ (4A + 72/A)z'`, `|n| ≤ 4(1728/A²·z(z+2) + (4A+72/A)(z+1))`, `slope ≥ 2A`, `L ≥ 4A − 36/A`.
* §4 generic homotopy differences: `vS(1) − vS(0) = vS₁(0) + vS₂/2`, same for `vC`;
  `M(1) − M(0) = 5ΔvS − ΔW·vC(1) − W(0)·ΔvC`; Bose reciprocal for `q ≥ 2`, `|dq| ≤ 1`:
  `ρ(0) ≤ 2e^{−q}`, `ρ(1) ≤ 6e^{−q}`, `|ρ(1) − ρ(0)| ≤ 24|dq|e^{−q}`; the total bound
  `compensationDiffBound` (explicit polynomial in the thirteen bounds and `e^{−q}`).
* §5 `M(0) ≥ 2A(4A − 36/A)·(series bound)` from the corpus factorisation.
* §6a `c5CompletedCompensationMargin_pos_of_regimeOne_key`: for `1/4 ≤ t ≤ u`, `A(u−t) ≥ 6`,
  `compensationDiffBound(…) < 2A(4A − 36/A)·poly(t)` ⟹ `M(1) > 0`.  No `H < 0` needed.

Pod (`clg_beta3.py`): the key inequality holds with ratio `20` at `t = 1/4` (`A(u−t) = 6`), `46` at
`0.3`, `≥ 300` for `t ≥ 0.5`, up to `t ≈ 6` with the polynomial shape bound; beyond that the
exponential form `shape ≥ 32 sinh 2t cosh² 2t` (`t ≥ 5/4`) is needed.  Remaining for regime I:
the numeric discharge of the key (chambers in `t` after absorbing `A(u−t) ≥ 6` by the decay
`A^kε(A)` for `k ≤ 18`), and the small-`t` frozen-jet discharge for `t ≤ 0.3`.

## 2026-09-05 (verdict on the downstream chain) — work on this gate paused

**Question settled by corpus search only:** is "direct-J in all regimes + rank-four/Ptolemy ⇒ Weil
positivity" a theorem, or is the general-packet step RH-equivalent?

**Answer: the general-packet step is RH-equivalent; the implication is not a theorem.**

- What direct-J + rank-four gives (once the compact sign is closed in all regimes): nonnegativity
  of every fibre odd wall (`thetaCuspReflectedSourceOddParityWall_nonneg_of_dividedDrop_logConvex`),
  transported to the physical mixture (`thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres`),
  hence positive semidefiniteness of the center-mixed Toeplitz kernel on the **equispaced four-node
  packet** `{0,t,2t,3t}` for every aperture `a ∈ (0,1/2)` and `t > 0`
  (`thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_ptolemy`).  Separated packets of any size
  are already unconditional (`thetaTailFirstMomentKernel_separatedPacket_quadraticForm_nonneg`,
  `posSemidef_thetaTailFirstMomentBezoutian_separatedRealPacket`).
- What Weil positivity is in this receiver: `thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`
  (Fourier nonnegativity of the center-mixed autocorrelation tangent for all `a`, all `b`), and
  `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian` /
  `riemannHypothesis_iff_posSemidef_thetaTailKreinDifference` (PSD on **every finite node system**,
  every aperture).  Both are `↔ RiemannHypothesis`.
- No corpus theorem reduces the universal packet quantifier to bounded size or to equispaced nodes.
  The corpus records the opposite direction of evidence: rank five does not follow from the shape
  properties that give rank four (explicit indefinite five-node compression, frontier map "W2C"
  paragraph); the three-point problem needed its own compact-core theorem
  (`exists_thetaCuspCenterMixedThreePointMatrix_compactCore_iff`); and on the Xi side even fixed
  rank two over all packet pairs is `↔ RH`
  (`riemannHypothesis_iff_forall_xiSeparatedPacketWeilGram_two_det_nonnegative`), i.e. the RH
  content sits in the quantifier over all packets, not in the rank.
- Hence "extend rank four to clustered/general packets and exclude cofinal escape" (frontier map,
  CLG/TTF) is the universal criterion minus the proven separated stratum, which is RH itself.
  The direct-J gate is a receiver-side local input: closing it in every regime would add the
  equispaced four-node stratum of an RH-equivalent universal positivity and nothing beyond it.

**State of the gate itself at pause (all Lean, unconditional, wired, built, axioms clean):**
- `c5CompletedCompensationMargin_pos_of_regimeOne_quarter`: `1/4 ≤ t ≤ u`, `A(u−t) ≥ 6` ⇒ gate.
- Small `t` in regime I: theory complete, assembly not done.  Modules
  `ThetaCuspC5SharpTailMeasures` (second atom + deep tail, closed-form second-atom moments `j ≤ 7`,
  support-8 tail bound), `ThetaCuspC5SharpTailJets` (`|J_k − e^{−3A}G_k(A)| ≤ K_k A^k ε² + L_k A^k e^{−8(A−π)}/399`,
  `k = 2..7`, `|h_k|` antitone on `[6,∞)`), `C5FrozenJetSharpKernel` (`|K₁| ≤ S₅t⁶/90`, `|K₂| ≤ S₄t⁵/15`),
  `ThetaCuspC5FrozenJetGateSharp`, `ThetaCuspC5SharpWindowBounds` (uniform errors, `c⁽⁴⁾ = BW₆ − J₆`,
  `c⁽⁵⁾ = BW₇ − J₇`, window majorants, two-sided centre chambers, `sharpKey_of_bounds`).
  Remaining: 17 chamber certificates (`A(u) ∈ [6,16.5]`, Case I `[6,9]` with `t ≤ (A₂−6)/12` and
  window `[6, A₂²/6]`; Case II `[9,16.5]` with `t ≤ 1/4`, window `[max(6,0.6A₁), min(1.65A₂, A₂²/6)]`)
  plus a linear-bound tail for `A(u) ≥ 16.5`, using BW₇ monotone in `q` (via
  `thetaCuspBornWittenLogEighthDerivative_pos`) for the `S₅` lower end.  Chamber list verified on the
  pod against the exact Lean-side expressions (`clg_chambers_v2.py`).
- Corner regime `A(u−t) ∈ [π,6)`: not started.
