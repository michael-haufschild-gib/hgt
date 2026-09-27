# Mean-zero twists annihilate the main term of the smoothed divisor sum

- **ID:** estermann-mean-zero
- **Stage:** 3-formalized
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

## Additive orthogonality and the prime-modulus progression (2026-09-24)

`formal/GaloisForLFunctions/RHTower/EstermannProgressionOrthogonality.lean` (axiom-clean):

* `summable_estermannSmoothedTerm` — absolute convergence of the smoothed twisted terms, from
  `d(N) ≤ N + 1` against the geometric factor `e^{-Nx}`;
* `sum_twist_eq_progression` — the exact bridge, for **every** modulus,

```text
∑_{a mod q} e(−ab/q) ∑_N d(N) e(aN/q) e^{-Nx} = q · ∑_{N ≡ b (q)} d(N) e^{-Nx}.
```

`formal/GaloisForLFunctions/RHTower/EstermannPrimeProgression.lean` (axiom-clean):

* `exists_bound_norm_estermann_weighted` — the weighted form that keeps the main term: for an
  arbitrary weight on the units, `∑_a w(a) S_a = (∑_a w(a)) · main_q + O_w(x^{-1/2})`.  The
  mean-zero theorem is the case `∑_a w(a) = 0`;
* `estermannSmoothedSum_zero` — the untwisted sum is the zero twist;
* `sum_zmod_eq_add_sum_units` — for a prime modulus the residue sum is the zero term plus the unit
  sum;
* **`exists_bound_norm_estermann_prime_progression`** — for prime `q` and `b ≢ 0 (mod q)`,

```text
q ∑_{N ≡ b (q)} d(N) e^{-Nx}
  = ∑_N d(N) e^{-Nx} − (γ − log x − 2 log q)/(qx) + O_q(x^{-1/2}).
```

The subtracted term is the twist-independent main term weighted by the Ramanujan sum
`c_q(b) = ∑_{a ≠ 0} e(−ab/q) = −1`.

## Reading

The whole `b`-dependence of the progression sum, to this accuracy, is the single Ramanujan factor.
Everything beyond it lives in the `O(x^{-1/2})` critical-line integral, which is where the
arithmetic of `d(n)` in progressions actually sits.  This is the twisted-divisor input the ledger's
Barban–Vehov / BCHB off-diagonal entry asks for; the general (non-prime) modulus needs the gcd
reduction `e(aN/q) = e(a'N/q')`, giving the full Ramanujan main term `∑_{d ∣ q} c_{q/d}(b)·main(q/d)`.

## The scaled-twist reduction (2026-09-24)

`formal/GaloisForLFunctions/RHTower/EstermannScaledTwist.lean` (axiom-clean):

* `stdAddChar_scale` — `e((d j)/(d q')) = e(j/q')`: the standard additive character is invariant
  under simultaneously scaling argument and modulus;
* `estermannCoeff_scale`, `estermannSmoothedSum_scale` —
  `estermannSmoothedSum q (d·m) x = estermannSmoothedSum (q/d) m x` whenever `q = d q'`.

Writing `d = gcd(a, q)` this sends an arbitrary residue twist to a **unit** twist of the reduced
modulus `q/d`, which is exactly the hypothesis `estermann_smoothed_sum` requires.  The arithmetic
consequence is that the main term carried by a scaled twist is `(γ − log x − 2 log q')/(q' x)`,
belonging to the reduced modulus — this is the `a`-dependence that upgrades the single Ramanujan
factor of the prime case to the full expansion `∑_{d ∣ q} c_{q/d}(b) · main(q/d)`.

## The general modulus (2026-09-24)

`formal/GaloisForLFunctions/RHTower/EstermannGeneralProgression.lean` (axiom-clean):

* `exists_reducedMain` — **every** residue twist has an `O(x^{-1/2})` expansion, not only the units:
  with `d = gcd(a, q)`, `Nat.coprime_div_gcd_div_gcd` makes `a/d` coprime to `q' = q/d`, so the
  scaled-twist reduction lands on a unit twist of the divisor modulus `q'`, where
  `estermann_smoothed_sum` applies.  The main term carried is `(γ − log x − 2 log q')/(q' x)`.
* `exists_bound_norm_estermann_general_progression` — averaging against `e(−ab/q)`, of modulus one,

```text
q ∑_{N ≡ b (q)} d(N) e^{-Nx} = ∑_{a mod q} e(−ab/q) · main(q_a) + O_q(x^{-1/2})
```

for an arbitrary modulus, `q_a = q/gcd(a,q)`.

The remaining step is purely finite and combinatorial: grouping the residues by their gcd turns
`∑_a e(−ab/q) main(q_a)` into `∑_{d ∣ q} c_{q/d}(b) · main(q/d)` with Ramanujan sums.  No analysis
is left in it.

## The Ramanujan main term (2026-09-27)

`formal/GaloisForLFunctions/RHTower/EstermannRamanujanMainTerm.lean` (axiom-clean) carries out the
grouping step.

* `estermannRamanujanSum d b = ∑_{0 ≤ m < d, gcd(m,d)=1} e(mb/d)`, the Ramanujan sum `c_d(b)`;
* `sum_filter_reducedModulus_eq`: the residues `0 ≤ n < q` with `q/gcd(n,q) = d` are exactly
  `(q/d)·m` with `m` a reduced residue mod `d`;
* `sum_stdAddChar_mul_reducedModulus`: for every weight `g` on the moduli,
  `∑_{a mod q} e(−ab/q) g(q/gcd(a,q)) = ∑_{d ∣ q} c_d(−b) g(d)`;
* `estermannRamanujanSum_neg`: `c_d(−b) = c_d(b)`, from the involution `m ↦ d − m` on the reduced
  residues and `e(b) = 1`;
* **`norm_progression_sub_ramanujanMain_le`**: for every modulus `q`, residue `b` and `x > 0`,

```text
‖q ∑_{N ≡ b (q)} d(N) e^{-Nx} − ∑_{d ∣ q} c_d(b) (γ − log x − 2 log d)/(dx)‖ ≤ C q^{5/2} x^{-1/2},
```

  with `C = estermannSmoothedErrorConstant` absolute; `norm_progression_sub_ramanujanMain_le'` is
  the same expansion in the card's indexing `∑_{d ∣ q} c_{q/d}(b) main(q/d)`.

Direct check, single-module build (`lake build --old`), and axiom audit pass: the new theorems and
every declaration listed above audit to exactly `[propext, Classical.choice, Quot.sound]`
(`sum_zmod_eq_add_sum_units` is a private helper of the prime-progression module).  Wired into
`RHTower` without an umbrella build.

## Gates
- [x] 1 → 2: complete paper proof
- [x] 2 → 3: every proved statement formalized, unconditional, axiom-clean

- 2026-09-27 — Ramanujan grouping formalized; card moved to 3-formalized.
