You’re right. The (c=0) and (c=-2) cases are the two explicit smooth models, so they do not count as a fractal partial solution.

I should not pretend the previous answer solved the intended problem. From the file, the requested result is for real
[
c\in[-2,1/4)
]
with
[
\phi_c(t)=|\gamma_c(t)-\beta|,
]
and the allowed deliverable is a proof for the full range or for a genuinely described subrange.    The file also explicitly says that the strong “all small (\rho)” version is false numerically, so the real issue is proving existence of clean levels cofinally often, not monotonicity of (\phi_c).

I do **not** currently have a rigorous fractal-(c) proof that I can honestly stand behind. The natural next target would be a hyperbolic real subrange, for example the attracting-fixed-point interval
[
-3/4<c<1/4,\qquad c\ne0,
]
where (J_c) is a quasicircle and is fractal for non-exceptional (c). But proving the desired clean-level statement there still requires controlling the log-periodic side-well structure near the repelling fixed point (\beta). The file’s suggested route is exactly the missing hard step: one needs a uniform well-bottom/barrier comparison or a one-window clean-level proof with distortion control.

What I can give as a valid replacement is the following **reduced theorem**, which is useful but conditional:

Let (c) be a real hyperbolic parameter with locally connected (J_c). Suppose that, in a Koenigs linearizing coordinate (L_c) at (\beta), the function
[
r_c(t)=|L_c(\gamma_c(t))|
]
has one clean level in a fundamental dyadic window, with a positive multiplicative gap separating the central component from every side well in that window. Then the original Euclidean function
[
\phi_c(t)=|\gamma_c(t)-\beta|
]
has arbitrarily small connected sublevel sets.

The proof is standard: (L_c(f_c(z))=\lambda L_c(z)), so
[
r_c(2t)=\lambda r_c(t)
]
exactly near (0). A clean level in one fundamental window therefore reproduces at scales (\lambda^{-n}). Since
[
L_c^{-1}(w)=\beta+w+O(w^2),
]
Euclidean distance and linearizing-coordinate distance differ by a factor (1+O(|w|)). Thus a clean level with a fixed multiplicative gap remains clean after sufficiently many pullbacks. This proves cofinally many connected Euclidean sublevels.

But that conditional hypothesis is essentially where the real fractal difficulty sits. It is not a completed fractal-(c) solution unless we prove the one-window clean level for a concrete non-smooth parameter, such as (c=-1), or for a genuine interval of parameters.

So the honest correction is: my previous answer solved only the two excluded smooth models and does **not** satisfy your “fractal (c) only” requirement.

---

# Verification report (2026-07-02)

**Note on filing:** this addition responds to Problem 11 (the landing-distance
sublevel problem), not Problem 12 — it retracts the smooth-cases answer as a fractal
solution and supplies a new conditional reduction for Problem 11.

**Verdict: the retraction is accepted; the reduced theorem is VERIFIED and is a real
improvement — it makes the scale-propagation EXACT.**

1. In the Koenigs coordinate `L_c` at `β` (`L_c(f_c(z)) = λ L_c(z)`, `λ = 2β`), the
   profile `r_c(t) = |L_c(γ_c(t))|` satisfies `r_c(2t) = λ r_c(t)` exactly near
   `t = 0` — removing the asymptotic factor `|γ_c(t) + β| = λ + o(1)` of the
   Euclidean identity. Correct.
2. The transfer back to `φ_c(t) = |γ_c(t) − β|` via `L_c⁻¹(w) = β + w + O(w²)` is
   where care is needed, and the "positive multiplicative gap" hypothesis is exactly
   what makes it sound: a clean level WITHOUT a range-gap would not survive the
   `O(r²)` coordinate discrepancy (micro-oscillations of `φ` across the level are
   possible even when `r` is clean at a single level), but a clean BAND of levels of
   fixed multiplicative width `(1 ± g)` dominates the discrepancy `1 + O(λ^{-n})` for
   large `n`, and the Euclidean sublevels are then intervals. Verified.
3. Two glue points, both fine: (i) a window-edge condition (`σ(1+g)` below the
   infimum of `r_c` on the outer half of the window) makes the propagation argument
   self-contained down all scales; (ii) outside the window, `γ_c(t) ≠ β` for
   `t ≠ 0` (only the angle `0` lands at `β`) bounds `φ_c` below, so sufficiently
   small levels see nothing outside the window.

**Consequence.** Problem 11 is now reduced, in exact parallel with Problem 12's
reduction, to a FINITE one-window statement: exhibit one clean level with a
multiplicative range-gap in one fundamental dyadic window of `r_c`, for one real
fractal `c`. Restated self-contained (with the window-edge condition and the
assumable black-box chain) as `14-koenigs-window-clean-level.md`, following the
series' convention that answered problem files stay frozen. The external round-trip
set is now the sibling pair 13 (main-cardioid, planar crossing window) and 14 (real
slice, 1D Koenigs window) — both finite, both open to certified computer-assisted
proof.
