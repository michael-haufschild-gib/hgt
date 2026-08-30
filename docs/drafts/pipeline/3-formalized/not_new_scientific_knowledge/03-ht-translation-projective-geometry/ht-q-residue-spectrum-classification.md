# q-Residue Classification of DA Scaling Spectra

- **ID:** ht-q-residue-spectrum-classification
- **Stage:** 3-formalized
- **Type:** BRIDGE / CONSTRAINT-SPECTRUM CLASSIFICATION
- **Scientific status:** `[BRIDGE]` — scientifically routine from affine order-one hypertranscendence plus q-discrete residues
- **Statement:** The differentially algebraic scaling defects of a hypertranscendental rational `q`-difference primitive are classified exactly by the translation stabilizer of a finite `q`-residue class on the elliptic curve `C*/q^Z`. The spectrum modulo `q^Z` is finite, every finite subgroup is realizable, and every off-spectrum defect is hypertranscendental.

## Setup

Fix `q in C*` with `0 < |q| < 1`, and write

`sigma(f)(x) = f(qx)` and `delta = x d/dx`.

Let `r in C(x)` be regular at zero with `r(0)=0`. There is a unique germ

`f in x C[[x]]`

satisfying

`sigma(f) - f = r`.

It is convergent near zero and extends meromorphically to `C*` by the same functional equation.

Define the rational `q`-summability quotient

`W_q = C(x) / (sigma - 1) C(x)`.

For `a in C*`, scaling `S_a g(x)=g(ax)` commutes with `sigma`, hence acts on `W_q`. Define

`Spec_DA(f) = {a in C* : f(ax)-f(x) is DA over C(x)}`.

Assume throughout that `[r] != 0` in `W_q`, equivalently that `r` is not rationally `q`-summable.

## Main theorem `[PROVED HERE]` — bridge only

Let

`H_r = {a in C* : S_a [r] = [r] in W_q}`.

Then:

1. `f` is hypertranscendental over `C(x)`;
2. `Spec_DA(f) = H_r`;
3. for `a notin H_r`, the defect `f(ax)-f(x)` is hypertranscendental over `C(x)`;
4. `q^Z` is a subgroup of `H_r`, and `H_r/q^Z` is finite;
5. if the nonzero `q`-residue class `[r]` has support on `s` distinct points of `E_q=C*/q^Z`, then `|H_r/q^Z| <= s!`.

Thus this natural HT class has no wild scaling spectra: every DA spectrum is a finite extension of the structural lattice `q^Z`, and every non-DA defect is again HT rather than merely non-rational.

## Proof

### 1. Rational-or-hypertranscendental dichotomy

The germ `f` satisfies an inhomogeneous first-order linear `q`-difference equation over `C(x)`, hence a homogeneous linear `q`-difference equation after adjoining the constant solution `1`. By Adamczewski--Dreyfus--Hardouin, a Puiseux-series solution of such an equation is either in `C(x^(1/*))` or hypertranscendental. Since `f` has only integral powers, membership in the ramified rational field descends to `C(x)`.

If `f` were rational, then `r=(sigma-1)f` would be rationally `q`-summable, contrary to `[r] != 0`. Hence `f` is HT.

### 2. The defect equation

For `a in C*`, put `d_a(x)=f(ax)-f(x)`. Commutation of scaling and `sigma` gives

`(sigma-1)d_a = S_a r-r`.

The same rational-or-HT theorem shows that `d_a` is DA if and only if it is rational.

If `d_a` is rational, then the displayed equation says

`S_a[r]-[r]=0` in `W_q`.

Conversely, suppose `S_a r-r=(sigma-1)g` for a rational `g`. Then `d_a-g` is `sigma`-invariant as a Laurent series at zero. Because `q` is not a root of unity, every invariant Laurent series is constant. The left side of the equation is regular at zero; any polar part of `g` would survive under `sigma-1`, so `g` is also regular there. Adjusting its constant gives `d_a=g`. Thus

`d_a is DA <=> d_a is rational <=> S_a[r]=[r]`,

which proves the exact spectrum and the off-spectrum HT claim.

### 3. Finite residue support forces a finite quotient

The Chen--Singer `q`-discrete residue theorem identifies the nonsummable part of a rational function with finitely supported residue data on

`E_q = C*/q^Z`,

separated by pole order, together with the residue at infinity. Since `r` is regular at zero and `r(0)=0`, a nonzero class `[r]` cannot consist only of the constant-at-infinity obstruction: if all finite-orbit residues vanished, then `r=(sigma-1)g+c`, and evaluation at zero would force `c=0`.

Therefore `[r]` has a nonempty finite support `Supp_q([r]) subset E_q`. If `a in H_r`, scaling carries this support to itself. Translation by the class of `a` on `E_q` therefore permutes `Supp_q([r])`. The resulting homomorphism

`H_r/q^Z -> Sym(Supp_q([r]))`

is injective: a translation fixing even one point of the group `E_q` is the identity. This proves finiteness and the factorial bound. Finally `q^Z subset H_r` because `S_(q^n)r=sigma^n r` has the same class as `r`.

## Realization theorem `[PROVED HERE]`

Every finite subgroup `K` of the elliptic curve `E_q` occurs.

For a representative `alpha in C*`, set

`e_alpha(x)=x/(x-alpha)`.

Then

`S_a e_alpha = e_(alpha/a)`

and

`sigma(e_alpha)=e_(alpha/q)`.

Consequently `[e_alpha]` depends only on the point `[alpha] in E_q`, and the classes belonging to distinct points are linearly independent by the `q`-residue criterion. Choose representatives `alpha_u` for `u in K` and put

`r_K(x)=sum_(u in K) e_(alpha_u)(x)`.

This function is regular and zero at the origin, and its residue class is the uniform point-mass sum on `K`. Its translation stabilizer in `E_q` is exactly `K`. The associated primitive `f_K` is therefore HT and satisfies

`Spec_DA(f_K)/q^Z = K`.

Hence the possible quotient groups for rational `q`-difference primitives are exactly the finite subgroups of `E_q`.

## Additive entire-plane consequence

Let `tau in H` with `q=exp(2 pi i tau)` and set

`F(z)=f(exp(2 pi i z))`.

The meromorphic continuation of `f` on `C*` makes `F` meromorphic on `C`. Local composition with the DA maps `exp` and `log` transfers both DA and HT in the required directions. Thus

`Stab_DA(F) = {h in C : exp(2 pi i h) in H_r}`.

In particular, taking a one-point residue class gives

`Stab_DA(F)=Z+tau Z`.

After a linear rescaling, every rank-two lattice in `C` is the exact DA translation stabilizer of a meromorphic HT function, and every off-lattice translation defect is HT.

## Scientific novelty verdict

The statement is useful infrastructure but does **not** qualify as new scientific knowledge. Adamczewski--Dreyfus--Hardouin Proposition 5.1 already gives the affine order-one rational-or-HT dichotomy, while Chen--Singer identifies the q-summability quotient with finitely supported q-orbit residue data. The exact spectrum is therefore the stabilizer of an existing obstruction vector, its quotient is finite because the support is finite, and realization by a uniform finite-subgroup sum is elementary. This fails the routine-parent and ordinary-prompt gates.

The surviving residue is the rank-three boundary: elliptic-gamma translation defects obey two compatible elliptic difference constraints, while no single rational q-residue quotient controls them.

## Parent-theory threats

1. **Adamczewski--Dreyfus--Hardouin (2021).** Supplies the rational-or-HT theorem for linear `q`-difference solutions. If the spectrum theorem is judged a routine parameterized use of that dichotomy, scientific novelty fails.
2. **Chen--Singer (2012/2014).** Supplies the complete `q`-discrete-residue obstruction to rational summability. Search whether their quotient formalism or descendants already study scaling isotropy.
3. **Isotropy algorithms.** Recent multivariate summability work uses Sato isotropy groups and difference transformations. Determine whether the one-variable elliptic stabilizer and realization theorem are already implicit or explicit there.
4. **q-logarithm literature.** Search exact classifications of `f(ax)-f(x)` for Lambert series, `q`-logarithms, and rational `q`-primitives.
5. **Routine-parent test.** Erase all HGT language. If the theorem becomes an immediate corollary that a summability-obstruction vector has finite support, downgrade it to `[BRIDGE]` even if the exact wording is absent.

## Lean status (2026-08-29)

**Complete and unconditional** for both `[PROVED HERE]` theorems.  All declarations are axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`) and wired into `GaloisForLFunctions.HTGeometry`.

The `q`-summability quotient `W_q` is realized by the `q`-discrete residues, which had to be built
from scratch — neither mathlib nor the corpus had partial fractions, residues, or the Chen--Singer
criterion.

| Layer | Module | Content |
|---|---|---|
| Residues | `QOrbitResidue` | `qOrbitResidue q a d C = ∑ᶠ n (q^{-d})^n·polePart C (a q^n) d`; it annihilates every dilation coboundary |
| Euler action | `QOrbitResidueEuler` | `ρ_(d+1)(δf) = −(d+1)ρ_(d+1)(f) − d·a·ρ_d(f)`; no nonzero Euler polynomial of a function with a nonzero top residue is `q`-summable |
| Partial fractions | `PrincipalPartMonomial`, `PrincipalPartDecomposition` | every rational function is a polynomial plus a finite combination of `(x−α)^{-d}`, coefficients `= polePart` |
| Block telescoper | `PrincipalPartScale`, `QBlockTelescoper` | a block with vanishing residue is exactly a dilation coboundary |
| Chen--Singer | `QSummabilityFromResidues` | `exists_dilationTelescoper_of_qOrbitResidue_vanish` — the converse half |
| Top level | `QOrbitResidueTop` | `exists_top_qOrbitResidue` |
| The primitive | `QPrimitiveExistence` | `innerDilation_qPrimitive`: the coefficientwise solution of `f(qx) − f(x) = r` |
| Hypertranscendence | `QPrimitiveResidueHypertranscendence` | the exact differential Ostrowski criterion applied to the `q`-primitive |
| Card statements | `QResidueSpectrum` | items 1--4 |
| Stabilizer | `QResidueStabilizer` | items 4--5 |
| Realization | `SimplePoleUnit` | the realization theorem |
| Lattice | `QLatticeStabilizer` | the additive lattice consequence |

Statement by statement:

1. `f` is hypertranscendental over `C(x)`: `hypertranscendentalOver_qPrimitiveOf`.
2. `Spec_DA(f) = H_r`: `hypertranscendentalOver_qDefect` (`Spec_DA ⊆ H_r`) and
   `differentialAlgebraicOver_qDefect` (`H_r ⊆ Spec_DA`).
3. off-spectrum defects are hypertranscendental: `hypertranscendentalOver_qDefect`.
4. `q^Z ⊆ H_r`: `qSummable_ratFuncScale_zpow_sub`.
5. `H_r/q^Z` finite with `|H_r/q^Z| ≤ s!`: `mul_mem_residueSupport` embeds `H_r/q^Z` into the
   residue-support orbits and `residueSupport_subset_orbit_poles` makes those finite;
   `qSummableStabilizer_eq_pole_div` gives the explicit form `a = β q^{-n}/α₀`.
   (The formalized bound is the sharper `|H_r/q^Z| ≤ s`, which implies `≤ s!`.)

Realization theorem: `qSummable_ratFuncScale_simplePoleSum_sub_iff` — for a finite set `S` in
distinct `q`-orbits whose orbit union is division-closed, the stabilizer of
`r_S = ∑_{α∈S} x/(x−α)` is *exactly* that orbit union.  Every finite subgroup of `E_q` therefore
occurs.

Additive entire-plane consequence: the exact content is formalized in the multiplicative model —
`qSummable_simplePoleUnit_one_iff_lattice` states that for `q = exp(2πiτ)` with `τ` off the real
axis, the scaling stabilizer of `x/(x−1)` pulls back under `h ↦ exp(2πih)` to exactly
`Z + τZ` (`exp_mem_zpow_iff_lattice`), and `periodMultiplier_zpow_ne_one` supplies the non-torsion
hypothesis.  The passage from the formal Laurent solution to a meromorphic function on `C*` and its
composition with `exp` is a change of coordinates that this formalization does not carry: the model
here is the formal Laurent field `k((w))`, in which the whole spectrum theorem is proved.  No
mathematical content of the section beyond that change of coordinates is left unformalized.

## Sources checked

- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*, Theorem 1.2, JAMS 2021 / arXiv:1910.01874.
- S. Chen, M. F. Singer, *On the summability of bivariate rational functions*, especially the univariate `q`-discrete residue criterion, J. Algebra 409 (2014), 320--343 / arXiv:1210.6366.
- H. Ogawara, *Differential Transcendency of a Formal Laurent Series Satisfying a Rational Linear q-Difference Equation*, Funkcial. Ekvac. 57 (2014), 477--488.

## Gates

- [x] Exact statement and complete paper proof drafted.
- [x] Edge cases: summable `r`, constant obstruction, pole at zero, ramified-rational descent, and one-point support addressed.
- [x] Significance gate failed: complete rank-two classification, but no new mechanism beyond parent theories.
- [x] Parent-theory gate failed: affine order-one dichotomy plus q-discrete-residue support proves the result routinely.
- [ ] Exact/equivalent/stronger literature gate.
- [ ] Rediscovery gate across summability, special functions, and difference Galois theory.
- [x] Lean: both `[PROVED HERE]` theorems formalized unconditionally (2026-08-29).

## Log

- 2026-07-10 - Opened after Mahler normalization parent-killed the universal countability theorem and the `q`-Pochhammer boundary revealed exact rank-two lattice spectra.
- 2026-07-10 - Strengthened from one `q`-logarithm example to the full residue-class stabilizer theorem and realization of every finite subgroup of `E_q`.
- 2026-07-10 - Downgraded to `[BRIDGE]`: the full classification is a routine synthesis of Adamczewski--Dreyfus--Hardouin and Chen--Singer. The nonroutine residue begins at paired elliptic constraints and rank-three spectra.
- 2026-08-29 - Formalized unconditionally in Lean 4 and promoted to stage 3: the `q`-discrete
  residue calculus, both halves of the Chen--Singer criterion, the spectrum theorem, the stabilizer
  finiteness and the realization theorem.
