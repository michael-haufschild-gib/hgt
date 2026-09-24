# Mean-zero twists annihilate the main term of the smoothed divisor sum

- **ID:** estermann-mean-zero
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Statement:** `‖∑_{a ∈ (ZMod q)ˣ} w(a) ∑_N d(N) e(aN/q) e^{-Nx}‖ ≤ C_w x^{-1/2}` whenever
  `∑_a w(a) = 0`.

## Goal

The Estermann analytic layer gives, for every modulus `q` and every unit `a` mod `q`,

```text
∑_N d(N) e(aN/q) e^{-Nx} = (γ − log x − 2 log q)/(qx) + O_q(x^{-1/2}).
```

The point exploited here is that the main term is **independent of `a`**.  That is not an accident:
it comes from the character-sum collapse `∑_{c mod q} expZeta(c/q, s) = q^{1−s} ζ(s)`, which makes
`D(s, a/q) = q^{1−2s} ζ(s)² + q^{−s} R_a(s)` with an `a`-independent double pole.  So the main term
lies in the kernel of every mean-zero weight on the units.

## What is proved

`formal/GaloisForLFunctions/RHTower/EstermannMeanZeroTwist.lean`, all axiom-clean:

* `estermannSmoothedSum q a x = ∑' N, d(N) e(aN/q) e^{-Nx}`, `estermannSmoothedMain q x` the
  twist-independent main term;
* `estermannSmoothedSum_sub_main` — the difference is exactly the critical-line integral;
* `exists_bound_norm_estermannSmoothedSum_sub_main` — that difference is `O_q(x^{-1/2})`;
* `exists_bound_norm_estermann_meanZero` — for `∑_a w(a) = 0`, the weighted twist is
  `O_w(x^{-1/2})` with no main term;
* `exists_bound_norm_estermann_character` — the non-principal Dirichlet character case.

## Next

Character orthogonality converts this into divisor sums over arithmetic progressions, but the
inverse transform needs **all** residues `a` mod `q`, not only the units.  The reduction is the gcd
one: with `d = gcd(a, q)`, `q' = q/d`, `a' = a/d`, one has `e(aN/q) = e(a'N/q')`, hence
`estermannSmoothedSum q a x = estermannSmoothedSum q' a' x`, and the main term becomes
`(γ − log x − 2 log q')/(q' x)` — now genuinely `a`-dependent through `d`.  Averaging with
`e(−ab/q)` then produces a Ramanujan-sum main term `∑_{d ∣ q} c_{q/d}(b) · main(q/d)`.  That is the
next module, and it is the twisted-divisor input the ledger's Barban–Vehov / BCHB off-diagonal item
asks for.

## Log
- 2026-09-24 — built, wired, axiom-clean.
