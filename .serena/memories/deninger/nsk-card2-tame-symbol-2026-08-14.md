# Card 2: the tame symbol on `K_2^M` is built (2026-08-14)

`formal/GaloisForLFunctions/HTGeometry/MilnorKTameSymbol.lean` — compiles clean, axioms
`propext, Classical.choice, Quot.sound`, wired into `HTGeometry.lean`.

`TameData K k` bundles a valuation `Kˣ →* Multiplicative ℤ`, the residue hom `val.ker →* kˣ`,
`res_neg_one`, and the three `1 - a` clauses (`oneSub_of_pos`, `oneSub_of_zero`, `oneSub_of_neg`).
Derived: `v`, `v_mul`, `v_zpow`, `mem_ker_iff`, `v_neg_one`, `symbolUnit`, `symbolUnit_mem`,
`tame`, `res_zpow`, `neg_one_mem_ker`, `tame_mul_left`, `tame_mul_right`,
**`tame_steinberg`** (four-way case analysis; the negative case closes because `v(a)²+v(a)` is
even), `tame_eq_one_of_mem_ker`, `tameOnSymbol`, `tamePre`, `tamePre_rel`,
**`tameHom : MilnorKDeg K 2 →+ Additive kˣ`**, `tameHom_symbol`.

Not yet done: the instantiation of `TameData` for a number field from
`IsDedekindDomain.HeightOneSpectrum` (valuation `v.valuation K`, residue field `R ⧸ v.asIdeal`),
and the finiteness-of-support statement (a fixed pair is a unit pair at all but finitely many
primes, so `tame_eq_one_of_mem_ker` applies).  Those two would give: for every `{a,b}` of a number
field there is `n ≠ 0` with `n{a,b}` in the tame kernel.

RESIDUAL DEEP INPUT (unchanged): the tame kernel of a number field is torsion — Garland's
finiteness, equivalently Borel's `rank K_2(O_K) = 0`.  Literature check (July 2026): no elementary
proof is known; Tate's Euclidean argument covers `ℚ` only; Bass–Tate's `K_n^M ≅ (ℤ/2)^{r_1}` for
`n ≥ 3` does not descend to `n = 2`; Moore's theorem reduces to the wild kernel but its finiteness
is again Tate/Garland.  `ℚ̄` gives no shortcut (Suslin: `K_2` of an algebraically closed field is
uniquely divisible, generally nonzero).
