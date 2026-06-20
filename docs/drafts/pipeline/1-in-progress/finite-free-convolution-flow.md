
## Log (cont.)
- 2026-06-20 (novelty-loop R21) — **Numerical confirmation of single-orbit no-margin + one structural seed.**
  Runpod, Ξ Jensen polynomials `J_d(X;t)` along the translation orbit (the proven RH-equivalent object), scale-
  invariant min root-gap vs the Hermite (GORZ t=0) archimedean control:

  | d | xi-margin sup_t | Hermite baseline | ratio |
  |---|---|---|---|
  | 4 | 5.06e-4 | 0.318 | 1.6e-3 |
  | 6 | 1.02e-5 | 0.186 | 5.5e-5 |
  | 8 | 2.35e-5 | 0.130 | 1.8e-4 |

  Orbit relative margin runs **10³–10⁴× below the archimedean baseline** (d=4,6,8), hyperbolic throughout,
  tightest approaches in the low-zero band `t≈9–26` (d=8 at `14.08≈γ₁`). Ratio NOT cleanly monotone (sampling-
  limited) ⟹ **no scaling law claimed.** Quantifies how RH-blind the GORZ center is; corroborates Wheeler #94
  (no-margin real) with a fair archimedean control.
  - **Structural seed (rigorous):** `J_d(0;t)=Ξ(t)`, so a Jensen root is **pinned to the origin at every zero-
    height** (verified: `|root|=1.77e-8` at `t=γ₁`; `0.164` at `t=12`). The t-orbit threads its Jensen roots
    through the origin at each `γ_n`; the center is one generic point. This is the concrete mechanism behind
    "GORZ is t=0-only / RH lives in the t-orbit." **Provable next target:** does the pinned-root mechanism force
    a lower bound on the avoided-crossing margin at zero-heights (numerics → theorem)?
  - Honest grade: confirmatory (novelty ~20, significance ~28, proof ~55); under-performed a pure-reasoning round
    — logged as a method lesson (confirmatory numerics on mapped structure cap low).
- 2026-06-20 (novelty-loop R22) — **Lemma (origin-crossing velocity), PROVEN + verified.** For Ξ (real entire,
  simple zeros), the degree-`d` Jensen polynomial `J_d(X;t)=Σ_j C(d,j)Ξ⁽ʲ⁾(t)/j! Xʲ` has a root pinned to the
  origin exactly at each zero `γ_n`, crossing transversally with **universal velocity `dX₁/dt|_{γ_n}=−1/d`**
  (proof: `J_d(0;t)=Ξ(t)`, `∂_XJ_d(0;t)=dΞ'(t)`, IFT). **Verified runpod** to ≤3.4e-10 (d=4,6,8,10 → −1/d).
  Two consequences: (i) `−1/d` is independent of `n`, of `γ_n`, of `Ξ'(γ_n)` ⟹ the origin-crossing is purely
  combinatorial, **arithmetic-free**; (ii) the crossing is real & transversal ⟹ **RH-violation (real pair →
  complex pair, `λ_min(S_d)=−1`) is EXCLUDED from the origin-crossing and can only occur at BULK avoided-
  crossings.** Rigorous localization confirming the card's edge/bulk-localization (displacement side) by proof.
  Trims the search space for `sup_t λ_min(S_d(t))≥−1`: the danger is bulk, never the pinned origin root.
