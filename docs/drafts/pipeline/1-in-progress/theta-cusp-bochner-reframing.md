# Card: the center-mixed all-node wall is one Fourier sign, not a ladder

Status: Stage 1 (reframing + numerical determination). Topic: RH / Xi.

## What the corpus has

`thetaCuspCenterMixedThreePointMatrix a x y = !![d,p,r; p,d,q; r,q,d]` with
`d = D_a(0), p = D_a(x), q = D_a(y), r = D_a(x+y)`, where

    D_a(t) = ∫_{0}^{∞} r · sinh(a r) · Φ(r/2 + t) · Φ(r/2 − t) dr,     0 < a < 1/2,

and `Φ = thetaCuspFullSource` is **twice the classical Riemann Ξ-kernel**
`Φ(x) = Σ_{n≥1} (4π²n⁴e^{9x/2} − 6πn²e^{5x/2}) exp(−πn²e^{2x})` (verified even, numerically).

Proved unconditionally in the corpus: 2-node PSD, and 3-node PSD for **all** admissible `(a,x,y)`
(`thetaCuspCenterMixedThreePointMatrices_posSemidef`). All-node PSD is recorded as the RH wall.

## [OBSERVATION] The wall is a Bochner condition

The three-point matrix has entries `D_a(t_i − t_j)` at nodes `0, x, x+y`. So the matrix family is
**translation-invariant**, and

    (all-node PSD, every node configuration)  ⟺  D_a is a positive-definite function on ℝ
                                              ⟺  D̂_a ≥ 0    (Bochner).

This replaces an infinite ladder of determinant inequalities by the sign of a single function. It also
makes the standard sufficient criteria available (Pólya convexity, Askey, complete monotonicity,
Kuttner–Golubov) — none of which was in play in the node-by-node framing.

Note `D_a` is **not** an autocorrelation: the weight `r·sinh(ar)` couples the two arguments through
`u+v`, which is precisely what stops `D̂ = |Φ̂|² ≥ 0` from being automatic.

## [NUMERICS] D̂_a > 0, and D_a changes sign

At `a = 1/4` (mp.dps = 40, Simpson on `[0,3]`, N = 240; `Φ` summed to machine-zero):

- `D_a(0) = 7.8826×10⁻³`; `D_a` decays doubly exponentially and turns **negative** near `t ≈ 1.7`
  (`D_a(2.0) ≈ −2.8×10⁻¹¹³`). So `D_a` is not a nonnegative kernel — positive-definiteness is genuine,
  not a triviality.
- `D̂_a(s) > 0` for every sampled `s ∈ [0,60]`: `2.86×10⁻³` at `s=0`, decreasing smoothly and
  monotonically to `3.35×10⁻¹⁶` at `s=60`, **no sign change and no oscillation**.

So the wall is consistent with RH and worth attacking, not refuting.

## [MECHANISM] why `0 < a < 1/2`

With `u = r/2+t`, `v = r/2−t` (so `r = u+v`), `sinh(a r) = ½(e^{au}e^{av} − e^{−au}e^{−av})`, hence

    D_a(t) = ½ ∫_{u+v>0} (u+v) [ Φ_a(u)Φ_a(v) − Φ_{−a}(u)Φ_{−a}(v) ] ,   Φ_{±a}(x) = e^{±ax}Φ(x),

and `Φ̂_{±a}(ξ) = Ξ(ξ ∓ ia)`. Therefore `D̂_a` is a **bilinear form in `Ξ` shifted off the critical
line by `±ia`**, and admissibility `a < 1/2` is exactly the requirement that the shift stay inside the
critical strip. Naive Fubini is illegitimate here: `∫_0^∞ r sinh(ar)e^{-irσ}dr` diverges, and the
formal evaluation `2iaσ/(σ²+a²)²` is odd, which would force `D̂ ≡ 0` — contradicted by the numerics.
The convergence comes from `Φ`'s doubly-exponential decay, so the contour must be shifted rather than
the integrals exchanged. **That contour shift is where the zeros enter.**

## [OPEN CORE]

Establish `D̂_a(s) ≥ 0` for all real `s` and one admissible `a`, unconditionally — equivalently exhibit
the shifted bilinear form as manifestly nonnegative. Sub-questions:
1. Exact closed form for `D̂_a` as a contour integral in `Ξ(ξ±ia)`.
2. Does `D_a` satisfy a Pólya-type criterion? (Corpus has **log-concavity**, which does *not* give
   convexity, so Pólya does not apply directly — determine convexity of `D_a` on `[0,∞)` numerically.)
3. Is `D̂_a` completely monotone in `s²`? The sampled decay is smooth and monotone.

---

## [PAPER-PROVED + NUMERICALLY CERTIFIED] The closed form

**Theorem.** Let `Φ` be the Riemann Ξ-kernel (even, `Ξ(ζ) = ∫Φ(x)e^{iζx}dx`), and for `0 < a < 1/2`
let `D_a(t) = ∫_0^∞ r·sinh(ar)·Φ(r/2+t)·Φ(r/2−t) dr`. Then for every real `s`, with `ζ = s/2 + ia`:

        D̂_a(s)  =  −Im[ Ξ'(ζ) · conj(Ξ(ζ)) ]  =  ½ ∂/∂a |Ξ(s/2 + ia)|² .

*Proof.* The integrand is **even in `r`** (Φ even), so the half-line integral is half the full line;
`r = 2w` gives `D_a(t) = 2∫_ℝ w·sinh(2aw)·Φ(w+t)Φ(w−t)dw`. Substituting `u = w+t`, `v = w−t`
(`dw dt = ½ du dv`) and expanding `sinh(a(u+v)) = ½(e^{au}e^{av} − e^{−au}e^{−av})`, the double
integral **factorises**:

        D̂_a(s) = ¼ Σ_{±} ∓ [ (∫u f_±)(∫g_±) + (∫f_±)(∫v g_±) ],
        f_±(u) = Φ(u)e^{±au}e^{−isu/2},   g_±(v) = Φ(v)e^{±av}e^{+isv/2}.

Because `Φ` decays **doubly exponentially**, `e^{±ax}Φ(x)` is integrable for *every* real `a`, so
`∫f_+ = Ξ(s/2+ia)`, `∫g_+ = Ξ(s/2−ia)`, and `∫u f_+ = ∂_a Ξ(−s/2−ia) = iΞ'(s/2+ia)` (Ξ even ⟹
`Ξ'(−z) = −Ξ'(z)`). The `−a` term equals minus the `+a` term, doubling it. This gives
`D̂_a(s) = (i/2)[Ξ'(ζ)Ξ(ζ̄) − Ξ(ζ)Ξ'(ζ̄)]`; since Ξ has real Taylor coefficients, `Ξ(ζ̄) = conj Ξ(ζ)`,
so the bracket is `W − conj W = 2i·Im W` with `W = Ξ'(ζ)conj(Ξ(ζ))`. The second form follows from
`∂_a log|Ξ(z+ia)| = −Im(Ξ'/Ξ)(z+ia)`. ∎

**TRAP (recorded so it is not re-walked).** Applying Fubini to the `r`-integral *alone* is illegitimate:
`∫_0^∞ r sinh(ar)e^{−irσ}dr` diverges, and its formal value `2iaσ/(σ²+a²)²` is **odd**, which paired
against the even factor `Ξ(σ+s/2)Ξ(σ−s/2)` would force `D̂_a ≡ 0` — contradicted by the numerics.
Convergence comes from `Φ`, so one must factorise *after* the `(u,v)` substitution, never split the
`r`-integral off by itself.

**Numerical certification** (mp.dps = 30, `a = 1/4`): the three quantities — direct cosine transform of
`D_a`, `−Im[Ξ'conj Ξ]`, and `½∂_a|Ξ|²` — agree to **10 significant digits** at
`s = 0,1,2,4,6,8,10,14`, e.g. `s=0: 0.002862926847` and `s=14: 0.0003612677341` for all three.
(Trap caught during certification: `Φ(x)` for `x ≲ −4` needs `n` up to `~e^{|x|}` series terms;
truncating at `n<60` silently produces garbage. Evaluate `Φ` at `|x|` — Φ is even.)

## [CONSEQUENCE] Three of the ledger's faces are ONE face

Equivalent, for each `a ∈ (0,1/2)`:
1. every center-mixed matrix (all node counts) is positive semidefinite — i.e. `D_a` is a
   positive-definite function (Bochner);
2. `Im (Ξ'/Ξ) ≤ 0` on the line `Im ζ = a`;
3. `a ↦ |Ξ(z + ia)|` is non-decreasing, for every real `z`.

Quantifying over `a ∈ (0,1/2)` and invoking the corpus's certified chain, each is equivalent to RH.
So the theta-cusp positivity route is **not an independent route**: it is the `Im logDeriv Ξ ≤ 0`
face and the `|Ξ| monotone in height` face, in Fourier coordinates.

## [ACTIONABLE] The node ladder has no top

`n`-node PSD for every `n` is equivalent to a single Fourier-sign condition, and each finite `n` is a
strictly weaker shadow of it; no finite rung implies the next. The programme of climbing
2-node → 3-node → 4-node → … is therefore structurally incapable of reaching RH, however many rungs
are proved. Each rung remains a genuine unconditional theorem about Ξ, but the route should not be
labelled "approaching the wall". The Hermite–Biehler mechanism is explicit here: if all zeros `ρ` of Ξ
are real then `Im(Ξ'/Ξ)(z+ia) = −Σ_ρ a/|z+ia−ρ|² < 0`, so `D̂_a > 0`; a single off-line zero reverses
the sign near it.

## [LEAN-PROVED] Formal bridge layer

`HTGeometry/VerticalModulusDerivative.lean` (axiom-clean: propext/Classical.choice/Quot.sound;
umbrella-wired; build green):

- `hasDerivAt_normSq_vertical_general (f x a) (hf : DifferentiableAt ℂ f (x+ia))` :
  `HasDerivAt (fun t => normSq (f (x+it))) (-2 * (deriv f (x+ia) * conj (f (x+ia))).im) a`.
  **Strictly stronger than the corpus's `RHTower.hasDerivAt_normSq_vertical`**, which needs
  `XiC z ≠ 0` because it routes through `logDeriv`. The `-2 Im (f' conj f)` form is defined
  *at the zeros too*, where it vanishes — and the zeros are exactly where the criterion is sharp.
- `neg_two_im_deriv_mul_conj_eq` : off the divisor the two forms agree
  (`-2 Im (f' conj f) = -2 normSq(f) · Im (logDeriv f)`), via `Complex.inv_def`.
- `monotoneOn_normSq_vertical_of_neg_im_nonneg` : the sign condition `0 ≤ -Im(f' conj f)` on a
  convex set forces `MonotoneOn` of `t ↦ normSq (f (x+it))` — the zero-tolerant form of the
  "modulus non-decreasing in height" face.

This is the right-hand half of the main identity, formalized for an arbitrary analytic `f`.

**Still paper-only (multi-session analytic build):** the Fourier half
`D̂_a(s) = -Im[Ξ'(ζ) conj Ξ(ζ)]`. It needs (i) the Fourier pair `Ξ(ζ) = ∫Φ(x)e^{iζx}dx` at
*complex* `ζ` (the corpus has real-axis pieces in `ThetaCuspFourierXi.lean`, not the complex-argument
pair), (ii) Fubini on `ℝ²` after the `(u,v)` substitution, (iii) differentiation under the integral
for `∫uΦ(u)e^{au}e^{-isu/2}du = ∂_a Ξ`. All three exist in mathlib; the work is the integrability
side conditions, which are easy in principle because `Φ` decays doubly exponentially.
