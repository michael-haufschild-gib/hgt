# Constant-vector JAS tests detect a maximal off-line zero on every dyadic shell

## Statement

Setting: the level-one constant-vector JAS test `JasConstProductPositiveOn P σ` on the primes of a
dyadic shell `P = (N, 2N]`.

**Theorem** (`eventually_not_jasConstProductPositiveOn_shell_of_maximal_offLine`). Suppose an
off-line zero has the largest distance `δ` from the critical line, and `δ < σ < 1 + δ`. Then for every
sufficiently large `N` the test on `(N, 2N]` is negative for some `z ∈ ℂ`.

**Capstones.**

- `RH ⟺ ZAL ∧ ∃ᶠ N, JasConstProductPositiveOn (primes in (N, 2N]) 1`.
- The same holds with "no off-line chain" in place of ZAL.

This is T216 of `5-failed/jas-sparse-dyadic-scale-detector.md`, now complete for exact ties.

## Proof

1. **Shell main term.** For `z = α − it` with `0 < α < 1`:
   - `M_z(2N) = λ_N 2^{1−α} e^{it log 2} M_z(N)`, where `λ_N = log N/log 2N`;
   - so `‖Σ_{N<p≤2N} p^{−z}‖ = f(t) E_α(N) + o(E_α(N))`, with
     `f(t) = |2^{1−α}e^{it log 2} − 1|/|1−α+it|`.
2. **Tie group.**
   - `f > 0`, since `|2^{1−α}e^{iθ} − 1| ≥ 2^{1−α} − 1`, and `f(t)|t| ≤ 3`.
   - Only finitely many zeros at distance `δ` have `f ≥ f(γ₀)/2`.
   - The maximum `f_max` is attained on a finite nonempty group `G`. Every other zero at distance `δ`
     has `f ≤ f₂`, with `f_max/2 ≤ f₂ < f_max`.
   - The zeros closer to the line have shell sums `o(E_α(N))`.
3. **Order of constants.** None depends on the tail set `F`:
   - `c = ¼ − δ²`;
   - `ε = (f_max − f₂)/4` and `ρ₂ = (f₂ + ε)/(f_max − ε) < 1`;
   - `W = Σ_ρ |1/(ρ(1−ρ))|` and `w_min = min_G |w|`;
   - `L` with `2We^{4−L} ≤ c w_min/4`, `R₀ = 1 + 2L/(1−ρ₂)²`, the ladder top `R* = R_{2|G|}`, and
     `Λ₀ = 2(R*+4)C₂/c₁`.

   Only then choose `F ⊇ G` with a light tail.
4. **Multi-point anti-alignment** (`exists_multi_antiAligned`).
   - Points: `t = (q, b)` for `q ∈ F` and `b ∈ {u, ū}`. Each has `ζ_t = W_big(q)/S` or `/S̄`, where
     `S` is the largest big sum on `G` at the current `N`.
   - Ladder: `R_{k+1} = R_k + 1 + 2L/τ(R_k)²`, with `τ(R) = c/(8(R+4))`. The bands
     `[τ(R_k)², 2L/R_k)` of `‖ζ−1‖²` are disjoint.
   - Pigeonhole over the `2|G|` points of the tie group gives an empty band.
   - At that rung, near points satisfy `e^{Yζ} ≈ −e^R`, so they are anti-aligned with every `w` of
     positive real part. Far points are `e^{−L}` smaller.
   - The points of `F∖G` have `‖ζ‖ ≤ ρ₂`, so they are far at every rung.
5. **Uniform angle.** `Re(1/(ρ(1−ρ))) ≥ (¼ − δ²)|1/(ρ(1−ρ))|` when `|Re ρ − ½| ≤ δ < ½`. Hence
   `Re w ≥ c|w|` on all zeros.
6. **Kernel errors** (`exists_jasConstKernel_type_eq`). With `u = jasTypeAmp`, the kernel of type `b`
   is `exp(Y_b ζ + e)`, where `‖e‖ ≤ ‖Y‖‖z₀‖² + ‖z₀‖Σp^{−σ} + Σ‖x_p‖² ≤ c/8` for large `N`.

## Reading

- Fixed-ratio windows suffice for the sparse AAL receiver. No window-edge growth or progression
  structure is needed.
- Exact ties among top-distance zeros are no obstruction. The phase freedom of one complex amplitude
  anti-aligns any finite tie group at once.
- The ZAL/no-chain input stays necessary (CANNOT-518): super-high off-line clusters can dominate any
  single-scale test.
- So on the AAL side the JAS receiver is now sharp at its sparsest natural form. The remaining content
  of RH on this route is ZAL (large height) or chain exclusion.

## Lean

Modules:

- `RHTower/JointAncestryConstantVectorDyadicShells` (677 lines): ladder, anti-alignment, big/small
  sums, typed kernels, and the one-window core `exists_jasConstPairTerm_tsum_neg`.
- `RHTower/JointAncestryConstantVectorDyadicShellDetection` (790 lines): uniform angle, shell main
  term, tie group, the one-shell lemma, the eventual theorem, and the capstones.

Standard axioms. Wired after `JointAncestryConstantVectorEveryScale`.

Reusable pieces:

- `exists_multi_antiAligned`: a finite tie group, the far set, and a ladder;
- `exists_top_group`: attained maximum with a gap, for any decaying weight on a set of zeros;
- `quarter_sub_sq_mul_norm_le_re_one_div`;
- `eventually_abs_norm_shell_sub_le`;
- `jasMainScale_two_mul`, `jasMainTerm_two_mul`;
- `exists_exp_budget`.

## Amplitude refinement (MUST-1420)

The detector also bounds its amplitude: the negative vector has `|z| ≤ C log N·N^{−δ}` (module
`RHTower/JointAncestryShellAmplitudeAbscissaDuality`). This gives the amplitude–abscissa duality:

- Without a chain, zeros in `|Re ρ − ½| ≤ β` ⟺ for every `ε`, positivity at `|z| ≤ N^{−(β+ε)}` holds
  on infinitely many shells.
- RH ⟺ ¬chain (or ZAL) ∧ small-disc shell positivity for every `ε`.
- The unconditional perturbative producer reaches `N^{−½−ε}`.

## Power-sum form (MUST-1421)

`RH ⟺ ZAL (or ¬chain) ∧ ∀ε > 0, ∃ᶠ N, ∀k ≥ 1: |Σ_ρ W_ρ(N)^k/(ρ(1−ρ))| ≤ N^{εk}`. The proof applies
Turán directly to the tie group, with no anti-alignment, so the criterion is exact (module
`RHTower/JointAncestryShellPowerSumCriterion`).

## Prime-side form (MUST-1423)

Let `A_k(N) = Σ_{p₁,…,p_k ∈ (N,2N]} (p₁⋯p_k)^{−3/2}𝓔(p₁⋯p_k)`. Here
`𝓔(X) = (X − ψ(X)) + X(Σ_{n≤X}Λ(n)/n − log X + γ) − log 2π + Σ_j X^{−2j}/(2j(2j+1))` is the prime
side of the genus-kernel explicit formula.

- Identity: `A_k(N) = Σ_ρ U_ρ(N)^k/(ρ(1−ρ))` with `U_ρ(N) = Σ_{N<p≤2N} p^{ρ−3/2}`.
- Criterion: `RH ⟺ ZAL (or ¬chain) ∧ ∀ε ∃ᶠN ∀k ≥ 1, |A_k(N)| ≤ N^{εk}`.
- Proof. Under RH every `|U_ρ| ≤ Σ 1/p ≤ 1`. Conversely, run Turán on the right half `Re ρ ≥ ½` of
  the top tie group. Its mirror images have `|U| ≤ 1`, which is below the Turán ratio at large `N`.
- Reading. The trivial bound is `N^{k/2}`. So on the prime side the sparse producer target is
  square-root cancellation of the explicit-formula error over k-fold products of shell primes,
  uniformly in `k`.

Module `RHTower/JointAncestryShellArithmeticCriterion` (556 lines). Standard axioms.

## Loud-set form (MUST-1426)

**Absorbed Turán bound.** If finitely many zeros, and at least one, have `|B(ρ)| > L`, then some
`k > M₀` gives `|Σ_ρ B(ρ)^k/(ρ(1−ρ))| ≥ 2W L^k` with `W = Σ|1/(ρ(1−ρ))|`. The quiet zeros decay
like `(L/Z)^M`, and this absorbs Turán's polynomial loss, the minimal weight and the angle constant.

**Criterion.** `RH ⟺ JasShellLoudFinite ∧ ∀ε ∃ᶠN ∀k ≥ 1, |A_k(N)| ≤ N^{εk}`.

- `JasShellLoudFinite` means that for every `ε > 0` and every large `N`, only finitely many zeros have
  `|Σ_{N<p≤2N} p^{ρ−3/2}| > N^ε`.
- ZAL implies loud-set finiteness, and no maximal zero is needed.

**Reading (CANNOT-526).** The remaining large-height content is exactly the infinitude of loud
sets.

- A low off-line zero can be hidden only by infinitely many phase-aligned high zeros. They must
  surround its shell value with a positive measure whose holomorphic moments mimic a negative atom,
  and such measures exist.
- Far zeros (`β > ¾`) are self-coherent through the conjugate mirror term `c N^{2β−3/2}/log N`, but
  clusters break this.

Module `RHTower/JointAncestryShellLoudSetCriterion` (349 lines). Standard axioms.

## Concavity of the level-one prime side (MUST-1428)

Let `J(t) = ψ(t)/t + log t − γ − 1 − Σ_{n≤t}Λ(n)/n` and `E = ψ − t`. Then `J` is continuous,
`J' = −E/t²` off the integers, and `𝓔(X) = −X J(X) + c(X)` exactly.

Abel summation with ψ and M frozen between integers gives

`Σ_{n≤X} Λ(n)J(n)/√n = H(X) − H(1) + ∫_1^X (J/√t + J²/(8√t) + E²/(t²√t))`, with `H = EJ/√t − √tJ²/4`.

So the prime-weighted explicit-formula sum is `−(H(X) − H(1) + ∫J/√t + Q(X))`, where `Q ≥ 0` is the
mean square. Its diagonal is the one-signed far-zero signal of CANNOT-526(b).

Module `RHTower/PrimeSamplingMeanSquareIdentity` (399 lines). Standard axioms.

## Unconditional producer (MUST-1429)

For some `κ > 0` and every large `N`, constant-vector positivity holds on `(N, 2N]` at all
amplitudes `|z| ≤ κ log N/√N`, with no half-plane bound.

- The uniform angle comes from the ordinate gap: `Re(1/(s(1−s))) ≥ η²/(η²+η+1)|1/(s(1−s))|`.
- The shell sums are bounded by `Σ p^{−1/2} ≤ C√N/log N`.
- The producer sits at the trivial strip, and the producer gap to `N^{−ε}` is exactly a zero-free
  strip.

Module `RHTower/JointAncestryUnconditionalShellProducer` (176 lines). Standard axioms.

## Radius law (MUST-1430)

Under a maximal off-line zero at distance `δ*`, the shell positivity radius is `a(N) = N^{−δ*+o(1)}`:
the tests are positive below `N^{−(δ*+ε)}` and negative below `N^{−(δ*−ε)}`. They are unconditionally
positive below `κ log N/√N`. Under RH, `a(N) = ∞`.

## Damped shells: no large-height input (MUST-1432)

Let `V_ρ(N) = U_ρ(N)/(ρ+1)²` and `D_k(N) = Σ_ρ V_ρ^k/(ρ(1−ρ))`. Then
`RH ⟺ ∀ε ∃ᶠN ∀k ≥ 1, |D_k(N)| ≤ N^{εk}`, with no ZAL, attainment or loud-set hypothesis.

- The damping makes every loud set finite: `|V| > L` forces `(Im ρ)² < S(N)/L`.
- The absorbed Turán bound then detects any zero right of the line.

Arithmetic side: `D_k(N)` is a k-fold shell average of the order-2k Riesz mean of `𝓔̃`.

## Arithmetic damped criterion (MUST-1434)

With `𝓡_m(X) = (1/m!)∫_0^∞ 𝓔̃(Xe^{−t})t^m e^{−t}dt`:

`RH ⟺ ∀ε ∃ᶠN ∀k ≥ 1, |Σ_{p₁…p_k ∈ (N,2N]} (∏p_i)^{−3/2} 𝓡_{2k−1}(∏p_i)| ≤ N^{εk}`.

This is purely arithmetic, with no large-height hypothesis. Module
`RHTower/JointAncestryDampedShellArithmetic` (360 lines).

## Damped shell Weil positivity (MUST-1435)

`F_N(z) = Σ_ρ e^{z V_ρ(N) + z̄ V_{1−ρ}(N)}/(ρ(1−ρ))` is the Weil form of `ĝ_z(s) = e^{zV_s(N)}/s`.

`RH ⟺ ∃ᶠN ∀z, Re F_N(z) ≥ 0 ⟺ ∀N ∀z, Re F_N(z) ≥ 0`.

- `zV_ρ + z̄V_{1−ρ} = Re(z a_ρ) + i Im(z b_ρ)`, where `a = V + conj V*` and `b = V − conj V*`.
- `min(|V_ρ|, |V_{1−ρ}|) ≤ 1`, so `b_ρ ≠ 0` once `|a_ρ| > 2`.
- Take the top direction `ā*/M`, tilt it by a generic `1 + is` and scale it. Every top phase is then
  nonzero and less than 1 in absolute value.
- The real symmetrisation of the power sum on `z = nω` is a dominant unit pencil with
  positive-real-part fibres, so it is uniformly negative arbitrarily late.

Module `RHTower/JointAncestryDampedShellPositivity` (544 lines). Standard axioms.

## Prime-blindness (CANNOT-538, paper)

The proof of MUST-1435 is multiplier-agnostic. The prime-free
`m_N(s) = κN^{s−1/2}(2^{s−1/2}−1)/((s−½)(s+1)²)` gives an RH-equivalent shell Weil family with no
primes in it. At an off-line zero the shell sum is, to leading order, the PNT main term (the pole
shadow). Sampling at prime products therefore adds no producer leverage over smooth Riesz means.

## Exponential Weil-form dichotomy and the pole shadow (MUST-1441)

`RHTower/ExponentialWeilFormDichotomy` proves the MUST-1435 mechanism for any detecting family
`A_N, B_N`. The family must be bounded, have `min(|A|,|B|) ≤ 1`, have finite loud sets, be conjugate
under RH, and be loud off RH. Its prime-free instance `m_N(s) = N^{s−½}/(s+1)²` is RH-complete, so
the shell criterion is the pole shadow plus decorative prime sampling. MUST-1435 is now an instance.

## Cayley single-family criterion (MUST-1443)

`RH ⟺ ∀z ∈ ℂ: Re Σ_ρ exp(z(1−1/ρ) + z̄(1−1/(1−ρ)))/(ρ(1−ρ)) ≥ 0`, with one family and no side
condition. With `r = |1 − 1/ρ|`, the modulus part has norm `r + 1/r` and the phase part vanishes iff
`r = 1`. The new `exists_re_expWeilForm_neg_of_threshold` handles the on-line level `|a| = 2`.
Module `RHTower/CayleyExponentialWeilCriterion` (270 lines).
