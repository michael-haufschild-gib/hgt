# Step 39: effective Turán detection window [LEAN-PROVED]

Frontier item (b) of the resolvent-Turán arc, part I (quantitative descent opening).

Module `formal/GaloisForLFunctions/RHTower/XiResolventEffectiveTuranDetection.lean`, wired into
`RHTower.lean` after `XiResolventPartialLineSupply`. All five theorems audit to
`[propext, Classical.choice, Quot.sound]`; olean-built; module compiles warning-free.

## Theorems (namespace RHTower)

- `even_minor_truncation_le_of_offline_level`: setup = weight `Wf` conj-symmetric, `‖Wf‖ ≤ BW`,
  vanishing above level `ℓ`; `ρ₂ < ℓ` bounds sub-level moduli; `S ≥ Σ'‖u‖`; `g > 0` lower-bounds
  `‖V²−1‖` on non-resonant level pairs; witness `qh` at level, off-line, `Wf qh ≠ 0`. If the even
  weighted minors are `≥ 0` for all `n < N` then
  `N ≤ (2S²BW²/g + BW²S²/(ℓ²−ρ₂²)) / ((u qh).im² · normSq (Wf qh))`.
- `exists_neg_even_minor_of_offline_level`: past the window some even minor with `n < N` has
  negative real part.
- `level_criticalLine_of_even_minors_window`: finite jet certificate — minors nonnegative on
  `n < N` clean the level of every copy whose defect places its window below `N`.
- `xiWeightedResolventMoment_one`: weight-1 = raw moments bridge.
- `exists_neg_even_plain_minor_of_offline_top`: at the top level (all moduli ≤ ℓ), finitely many
  PLAIN even minors `R_{2n}R_{2n+2} − R_{2n+1}²` detect an off-line zero; window
  `(2S²/g + S²/(ℓ²−ρ₂²))/Im(u_qh)²`.

## Mechanism and significance

Machine's master estimate (`XiResolventEvenTuranMachine`) consumes minors only at `n < N`;
re-quantify and bound its three constants: level count ≤ S/ℓ, per-pair CP2 term ≤ 8ℓ²BW²/g,
complement pair mass P₀ ≤ S². Window is POLYNOMIAL in configuration data — classical Turán
power-sum detection constants decay exponentially in N. Numerically pre-certified on 200 random
two-scale configs before formalization.

## Lean traps

- linarith cannot match division atoms across scalar multiples (`8*X/g` vs `2*X/g`) in large
  contexts: name them first, `obtain ⟨A, hA⟩ : ∃ A : ℝ, A = S^2*BW^2/g := ⟨_, rfl⟩`, rewrite the
  bounds to `8*A`, then linarith is linear.
- `push_neg` is deprecated on this toolchain (deprecation warning fails the formal gate); use
  `simp only [not_exists, not_and, not_lt]`.
- Cloning a machine with `set`-variables: hypotheses freshly written in raw
  (`xiResolventPoint X q`) form bridge to `u q` forms by `exact`/`show` (defeq via zeta);
  `field_simp` may close a goal fully — drop trailing `ring`.

## Next (part II)

Effective descent iteration: compose the per-level window with the killing-polynomial weights
(`P(u)²`, `P = ∏(X−r)` over higher real atoms, cf. `XiResolventSpectralDescent`) to certify
partial RH down to scale δ from finitely many polynomial-weighted minors. Data side closes via
the two-scale supply bridge (`XiResolventPartialLineSupply`). Also open: window optimality
(step-38 masking config as lower-bound testbed). Card: xic-order-one-growth-organ.md steps 37-39.
