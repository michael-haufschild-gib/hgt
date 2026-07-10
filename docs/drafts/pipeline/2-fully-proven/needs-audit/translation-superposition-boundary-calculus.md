# Translation-Superposition Boundary Calculus

- **ID:** translation-superposition-boundary-calculus
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / REALIZATION THEOREM
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` — contingent on the independently audited elliptic-gamma defect theorem
- **Statement:** Once a hypertranscendental function has an atomic coset matroid of translation defects, every finite linear superposition of its translates has an exact DA spectrum and defect matroid computed by a boundary operator in the group algebra. Applied to the elliptic-gamma logarithmic derivative, this classifies all spectra of finite translate superpositions and realizes every finite-index overgroup of its rank-three structural group.

## Atomic defect functions

Let `f` be meromorphic on `C`, let `H` be an additive subgroup of `C`, and put

`G=C/H`, `pi:C -> G`.

Say that `f` has the **`H`-atomic defect property** if, for every finite list `a_1,...,a_n`,

`dtrdeg_(C(z)) C(z)<Delta_(a_1)f,...,Delta_(a_n)f>_delta`

is the number of distinct nonzero classes among `pi(a_1),...,pi(a_n)`.

Equivalently, the defects from distinct nonzero `H`-cosets are differentially algebraically independent, zero-coset defects are DA, and defects in the same coset differ by a DA function.

The elliptic-gamma logarithmic derivative `Psi` in `elliptic-gamma-rank-three-da-spectrum` has this property for

`H=Z+Z tau+Z sigma`

when `1,tau,sigma` are `Q`-linearly independent.

## Finite translate superpositions

Let `C[G]` denote the finite-support group algebra, with basis elements `[g]`. For

`D=sum_j c_j[g_j] in C[G]`,

choose lifts `a_j in C` of `g_j` and define

`f_D(z)=sum_j c_j f(z+a_j)`.

Changing a lift changes `f_D` by a DA function, so its DA translation spectrum and all finite-defect differential transcendence degrees depend only on `D`.

For `q in G`, write `t_qD` for translation of the group-algebra support by `q`, and define

`Stab_G(D)={q in G : t_qD=D}`.

## Main theorem `[PROVED HERE]`

Assume that `f` has the `H`-atomic defect property.

### Exact boundary-rank formula

For every `D in C[G]` and arbitrary shifts `h_1,...,h_n in C`,

`dtrdeg_(C(z)) C(z)<Delta_(h_1)f_D,...,Delta_(h_n)f_D>_delta`

equals

`dim_C span{(t_(pi(h_i))-1)D : 1 <= i <= n}`.

The vectors on the right lie in the augmentation ideal of `C[G]`. Thus every finite-defect dependence question for `f_D` is finite-dimensional linear algebra on the translated boundary of `D`.

### Exact spectrum and hypertranscendence

If `D ne 0`, then

`Spec_DA(f_D)=pi^(-1)(Stab_G(D))`.

The stabilizer of a nonzero finite-support group-algebra element is finite. Consequently every nonzero `f_D` is hypertranscendental and its DA spectrum is a finite-index additive overgroup of `H`.

If `D=0`, then `f_D` is DA and its spectrum is all of `C`.

### Complete realization theorem

Conversely, every finite subgroup `Q` of `G` occurs. Set

`D_Q=sum_(q in Q)[q]`.

Then `Stab_G(D_Q)=Q`, so the hypertranscendental function `f_(D_Q)` has exact spectrum

`pi^(-1)(Q)`.

Therefore the exact DA translation spectra of non-DA finite translate superpositions of `f` are precisely the additive groups `H'` satisfying

`H subset H' subset C`, `H'/H` finite.

### Multiplicative companion for logarithmic derivatives

Suppose `f=delta log F` for a nonzero meromorphic function `F`, and let `D` have finite integer coefficients. Define

`F_D(z)=product_j F(z+a_j)^(c_j)`.

Then `delta log F_D=f_D`. If `D ne 0`, the function `F_D` is hypertranscendental. Moreover

`F_D(z+h)/F_D(z) is DA iff pi(h) in Stab_G(D)`,

and for arbitrary `h_1,...,h_n`, the differential transcendence degree of the corresponding quotient family is

`dim_C span{(t_(pi(h_i))-1)D : 1 <= i <= n}`.

Indeed, the logarithmic derivative of the `h`-quotient is `Delta_h f_D`. A nonzero meromorphic function and its logarithmic derivative are differential algebraic over each other's differential fields: one direction is logarithmic differentiation, and the other is the first-order equation `delta Y=(delta log Y)Y`. Thus the additive boundary theorem transfers exactly to the multiplicative family.

## Proof

### 1. Defects linearize the augmentation ideal

Put `d_a=Delta_a f`. If `a-b in H`, then

`d_a-d_b=Delta_(a-b)f(z+b)`

is DA. Hence, modulo a differential-algebraic extension of `C(z)`, the class of `d_a` depends only on `pi(a)`, and the zero class gives zero.

Let `I(G)` be the augmentation ideal of `C[G]`. Dropping the coefficient at `[0]` identifies `I(G)` linearly with the finite-support vector space on `G\{0}`, because the missing coefficient is the negative sum of all the others. Under this identification,

`[g]-[0] mapsto d_a`, `pi(a)=g`,

up to DA terms.

The atomic defect property says that the finitely many coordinate functions corresponding to distinct nonzero `g` are differentially algebraically independent. Therefore, for any finite vectors `v_1,...,v_n in I(G)`, the associated linear combinations `ell(v_i)` satisfy

`dtrdeg ell(v_1),...,ell(v_n)=dim_C span{v_1,...,v_n}`.

Indeed, after adjoining the finitely many DA correction terms, choose a basis of the vector span and extend its coefficient matrix to an invertible linear change of the independent defect coordinates. Differential-algebraic base extension and invertible constant linear changes preserve differential transcendence degree.

### 2. A superposition defect is a group-algebra boundary

For `q=pi(h)`,

`Delta_h f_D=sum_j c_j(f(z+a_j+h)-f(z+a_j))`

`=sum_j c_j(d_(a_j+h)-d_(a_j))`.

Under the identification in Step 1 this is exactly the vector

`(t_q-1)D in I(G)`.

Applying the last formula of Step 1 to all `h_i` proves the boundary-rank theorem.

### 3. Spectrum equals stabilizer

The boundary-rank formula for one shift is zero exactly when

`(t_(pi(h))-1)D=0`.

This is equivalent to `pi(h) in Stab_G(D)`, proving the exact spectrum formula.

If `D ne 0`, its support is a nonempty finite set. Its translation stabilizer acts faithfully on that support: a translation fixing one support point is zero. Thus `Stab_G(D)` injects into a finite symmetric group and is finite.

Since `G=C/H` is infinite, some translation lies outside that finite stabilizer. The corresponding defect of `f_D` is not DA. Were `f_D` itself DA, all its translation defects would be DA. Hence `f_D` is hypertranscendental.

If `D=0`, the coefficients of the chosen lifts sum to zero separately in every `H`-coset. Replacing all translates within one coset by a fixed representative leaves only DA differences, so `f_D` is DA.

### 4. Realization

For a finite subgroup `Q`, translation by every element of `Q` fixes `D_Q`. Conversely, if `t_gD_Q=D_Q`, then its support obeys `g+Q=Q`, hence `g in Q`. Thus `Stab_G(D_Q)=Q`.

For any finite-index overgroup `H'` of `H`, take `Q=H'/H`. The construction gives exact spectrum `H'`. This proves both directions of the classification.

## Elliptic-gamma consequence `[NEW IF THE PARENT THEOREM SURVIVES AUDIT]`

Let

`Psi(z)=delta log Gamma(z;tau,sigma)`,

with `1,tau,sigma` `Q`-linearly independent and `H=Z+Z tau+Z sigma`. For any finite weighted translate divisor

`D=sum_j c_j[a_j+H]`,

the function

`Psi_D(z)=sum_j c_j Psi(z+a_j)`

has the exact boundary-rank formula above. In particular:

1. `Psi_D` is DA exactly when `D=0`;
2. every nonzero `Psi_D` is hypertranscendental;
3. its exact DA translation spectrum is the inverse image in `C` of the finite stabilizer of `D`;
4. every finite-index overgroup of `Z+Z tau+Z sigma` is realized as the exact spectrum of an explicit finite superposition of elliptic-gamma logarithmic derivatives;
5. its complete finite-defect matroid is the linear matroid represented by the boundary vectors `(t_q-1)D`.

For an integer-weighted divisor define the explicit elliptic-gamma product

`Gamma_D(z)=product_j Gamma(z+a_j;tau,sigma)^(c_j)`.

Every nonzero `Gamma_D` is hypertranscendental. Its shift-quotient DA spectrum is exactly `pi^(-1)(Stab_G(D))`, and every finite family of its shift quotients has differential transcendence degree equal to the boundary-vector rank. Taking `D_Q=sum_(q in Q)[q]` realizes every finite-index overgroup of `H` by an explicit hypertranscendental elliptic-gamma product, not merely by a logarithmic derivative.

This goes beyond a spectrum calculation for one named function: it constructs and completely classifies a closure class under finite translation superposition, including all its possible spectra and dependence geometries.

### Exact consistency check from the classical multiplication formula

Let

`Q_n=(1/n)H/H`, `D_n=sum_(q in Q_n)[q]`.

Felder--Varchenko's first multiplication formula is

`Gamma(nz;tau,sigma)=product_(0<=k_1,k_2,k_3<n) Gamma(z+(k_1+k_2 tau+k_3 sigma)/n;tau,sigma)`.

Logarithmic differentiation gives

`n Psi(nz)=Psi_(D_n)(z)`.

The boundary theorem predicts

`Spec_DA(Psi_(D_n))=pi^(-1)(Q_n)=(1/n)H`.

Independently, scaling the parent spectrum gives

`Delta_h(n Psi(nz)) is DA iff Delta_(nh)Psi is DA iff nh in H`,

which is the same group `(1/n)H`. Thus a classical identity checks the stabilizer theorem exactly on the full torsion-orbit divisor. The multiplication formula supplies this one highly symmetric divisor; it does not classify arbitrary weighted divisors, arbitrary finite subgroups, or finite-family boundary ranks.

## Novelty and significance audit

### Routine ingredients

- finite-support group algebra;
- augmentation ideals and stabilizers;
- invariance of differential transcendence degree under DA base extension and invertible constant linear changes.

### Nonroutine scientific input

- the `H`-atomic defect theorem for the elliptic-gamma logarithmic derivative;
- the observation that finite translate superposition closes exactly onto the boundary representation of `C/H`;
- the resulting classification and realization of all possible exact DA spectra in that closure class.

Classical elliptic-gamma multiplication formulas give particular identities among products at changed arguments or changed nomes. The first multiplication formula yields the full torsion-orbit consistency check above, but does not state even its DA spectrum, much less a stabilizer classification or boundary-rank formula. Searches through 2026 for differential-algebraic translation spectra, hypertranscendence of finite translate combinations, and elliptic-gamma shift dependence found no equivalent theorem.

The general group-algebra implication is elementary once an atomic defect theorem is known, but its significance is the exact closure and realization result for a concrete new HT family. It is not promoted independently of the elliptic-gamma parent: failure of that parent demotes this card automatically.

## Boundaries

1. The theorem concerns finite, not infinite, translate superpositions.
2. It classifies additive translation differences of `f_D`; it does not by itself classify algebraic relations involving the un-differenced functions `f_D` for several different divisors.
3. If the parent function has defect relations finer than a partition matroid, the correct construction uses their actual relation module instead of `I(G)`.
4. For elliptic gamma, every finite subgroup of `C/H` is contained in `(1/N)H/H` for some `N`; the realized spectra are finite extensions of the dense rank-three group, not arbitrary additive subgroups of `C`.

## Lean route

The group-algebra part is formally accessible, but formalizing it before the analytic atomic-defect theorem would certify only a conditional linear-algebra shell. That would be formalization theatre. No Lean edit is warranted until the elliptic analytic and parameterized-Galois parent exists in the formal tree.

## Gates

- [x] Exact theorem stated.
- [x] Boundary-rank proof completed.
- [x] Exact spectrum classification completed.
- [x] Every finite-index overgroup realized explicitly.
- [x] Multiplicative elliptic-gamma products and all their shift quotients classified.
- [x] Non-collapse gate: distinct weighted divisors have genuinely different stabilizers and boundary matroids.
- [x] Preliminary exact/equivalent/stronger literature search completed.
- [ ] Independent audit of the elliptic-gamma atomic-defect theorem.
- [ ] Independent audit of the literature boundary.

## Log

- 2026-07-10 - Opened only after the one-pole quasi-elliptic abstraction collapsed back to elliptic gamma.
- 2026-07-10 - Identified the augmentation ideal as the exact linear receptacle for finite superposition defects.
- 2026-07-10 - Proved the boundary-rank formula, spectrum-stabilizer classification, hypertranscendence of every nonzero superposition, and realization of every finite-index overgroup.
- 2026-07-10 - Checked the full torsion-orbit case against Felder--Varchenko's multiplication formula; both routes give the exact spectrum `(1/n)H`.
- 2026-07-10 - Transferred the boundary calculus to integer-weighted products of elliptic gamma functions, including exact quotient spectra and finite-family quotient matroids.
