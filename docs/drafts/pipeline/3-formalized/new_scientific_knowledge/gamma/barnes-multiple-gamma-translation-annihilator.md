# Barnes Multiple Gamma Translation Annihilator

- **ID:** `barnes-multiple-gamma-translation-annihilator`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM (paper) / DIFFERENTIAL CHARACTERISTIC BOUNDARY / RECONSTRUCTION
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOVELTY PROVISIONAL PASS]`
  `[SIGNIFICANCE PASS AS A FOUNDATIONAL PAPER THEOREM] [INDEPENDENT AUDIT OPEN]`
  Nishizawa and Ogawara are direct parent threats but do not state the rationally-independent full
  differential-translation annihilator, boundary-cylinder, or rank-two reconstruction theorem.
- **Statement:** For Barnes' multiple gamma function with rationally independent periods, the
  complete constant-coefficient **differential-translation** annihilator of its logarithmic
  derivative modulo differentially algebraic functions is the principal squarefree ideal generated
  by the product of all parameter differences.  The resulting HT/DA orbit module is the reduced
  translation boundary `prod_j(T_j-1)=0` crossed with a free differential prolongation direction.

## Setup

Let `N >= 1`, and let nonzero complex numbers

`omega=(omega_1,...,omega_N)`

lie in a common open half-plane and be linearly independent over `Q`. Let

`Gamma_N(z|omega)`

be the zeta-regularized Barnes multiple gamma function in the Shintani normalization, and put

`Psi_N(z|omega)=d/dz log Gamma_N(z|omega)`.

For `j=1,...,N`, let `T_j` act by translation through `omega_j`, and put

`x_j=T_j-1`.

Write

`R_N=C[T_1^(+-1),...,T_N^(+-1)]`.

Barnes' ladder relation is

`Gamma_N(z+omega_j|omega)=Gamma_N(z|omega)/Gamma_(N-1)(z|omega^(j))`,

where `omega^(j)` is obtained by deleting `omega_j` and `Gamma_0(z)=1/z`. Consequently

`x_j Psi_N=-Psi_(N-1)(z|omega^(j))`,

and `Psi_0(z)=-1/z`.

Changing between standard Barnes normalizations only multiplies `Gamma_N` by an exponential of a polynomial in `z`. It therefore adds a polynomial to `Psi_N` and does not change any annihilator modulo DA functions.

## Atomic scaled-digamma theorem `[PROVED HERE]`

Fix `omega != 0` and write `phi(z)=Psi_1(z|omega)`. Let

`h_1,...,h_m`

be pairwise distinct modulo `omega Z`. Then

`phi(z+h_1),...,phi(z+h_m)`

are differentially algebraically independent over the field of `omega`-periodic meromorphic functions with `z` adjoined. In particular, every nonzero constant-coefficient finite linear combination of these translates is hypertranscendental over `C(z)`.

### Proof

The order-one ladder equation gives

`phi(z+omega)-phi(z)=1/z`.

After the change of variable `z=omega u`, the functions

`y_i(u)=phi(omega u+h_i)`

satisfy

`y_i(u+1)-y_i(u)=1/(omega u+h_i)`.

Hardouin--Singer, Corollary 3.2, says that these meromorphic functions are differentially dependent over the field of `1`-periodic meromorphic functions with `u` adjoined if and only if there are constant-coefficient differential operators `L_i in C[d/du]`, not all zero, and `g in C(u)` such that

`sum_i L_i(1/(omega u+h_i))=g(u+1)-g(u)`.

For a rational function `r`, rational summability `r=g(u+1)-g(u)` forces every discrete residue to vanish: for every coset in `C/Z` and every pole order, the sum of the corresponding principal-part coefficients over that coset is zero. This follows directly by telescoping the finitely many principal parts of `g` along each integer orbit.

Choose an index `i` for which `L_i` is nonzero, and let `d_i` be its highest derivative order. At the pole class

`-h_i/omega + Z`,

the left side has a pole of order `d_i+1` with nonzero coefficient. No other summand contributes on this orbit, because the `h_i` are distinct modulo `omega Z`. The corresponding discrete residue is therefore nonzero, contradicting rational summability. Hence no telescoper exists, and Hardouin--Singer gives differential algebraic independence. The final assertion follows because a DA nonzero linear combination would itself give a nonzero differential polynomial relation among the independent translates.

## Exact annihilator theorem `[PROVED HERE]`

Define

`Ann_DA(Psi_N)={P in R_N : P Psi_N is DA over C(z)}`.

Then

`Ann_DA(Psi_N)=(x_1 x_2 ... x_N)`.

Thus there are no hidden finite constant-coefficient cancellations beyond the full mixed Barnes ladder relation.

### Forward inclusion

Iterating the ladder relation in all `N` distinct directions gives

`x_1 x_2 ... x_N Psi_N=(-1)^N Psi_0=(-1)^(N+1)/z`.

Every Laurent translate of this rational function is rational. Hence every multiple of `x_1...x_N` belongs to `Ann_DA(Psi_N)`.

### Reverse inclusion

Suppose `P Psi_N` is DA and that `x_1...x_N` does not divide `P`. Since the `x_j` are pairwise nonassociate prime elements of `R_N`, choose `j` such that `x_j` does not divide `P`. Evaluation at `T_j=1` gives a nonzero Laurent polynomial

`Q=P|_(T_j=1) in C[T_k^(+-1):k != j]`.

Write

`P=Q+x_j S`.

Apply the complementary difference operator

`D_j=product_(k != j) x_k`

to `P Psi_N`. Translation preserves differential algebraicity, so

`P D_j Psi_N`

is DA. The ladder relations give

`D_j Psi_N=(-1)^(N-1) Psi_1(z|omega_j)`.

Put `phi_j=Psi_1(z|omega_j)`. Then `P phi_j` is DA. Since

`x_j phi_j=1/z`,

the function `x_j S phi_j` is rational. It follows from `P=Q+x_jS` that `Q phi_j` is DA.

Expand

`Q=sum_n c_n product_(k != j) T_k^(n_k)`.

Its terms translate `phi_j` through

`h_n=sum_(k != j) n_k omega_k`.

Distinct exponent vectors give distinct classes modulo `omega_j Z`: an equality of two such classes would be a nontrivial integer relation among `omega_1,...,omega_N`. The atomic scaled-digamma theorem therefore makes the nonzero combination `Q phi_j` hypertranscendental, a contradiction. Hence every annihilator is divisible by `x_1...x_N`.

## Full differential-translation annihilator `[PROVED HERE]`

Let `delta=d/dz`, commuting with every `T_j`, and enlarge the operator ring to

`D_N=C[delta,T_1^(+-1),...,T_N^(+-1)]=R_N[delta]`.

Define

`Ann_DA^diff(Psi_N)={P in D_N : P Psi_N is DA over C(z)}`.

Then the translation theorem remains exact after adjoining **all constant-coefficient
differential operators**:

`Ann_DA^diff(Psi_N)=(x_1 x_2 ... x_N)D_N`.             `(A)`

This is stronger than scalar extension of the preceding theorem.  In general, knowing that no
pure translation combination is DA does not exclude a DA combination of derivatives of distinct
translates.

### Proof of `(A)`

The forward inclusion follows from the full mixed Barnes ladder: `x_1...x_N Psi_N` is rational,
and every constant-coefficient derivative and structural translate of a rational function is DA.

For the reverse inclusion, suppose `P Psi_N` is DA and the squarefree product does not divide
`P in D_N`.  The elements `x_j` remain pairwise nonassociate primes after adjoining `delta`, so
choose `j` with `x_j` not dividing `P`.  Evaluation at `T_j=1` gives a nonzero

`Q=P|_(T_j=1) in C[delta,T_k^(+-1):k != j]`

and `P=Q+x_jS`.  Apply `D_j=prod_(k != j)x_k`.  All operators commute, and

`D_j Psi_N=(-1)^(N-1)phi_j`,  where `phi_j=Psi_1(z|omega_j)`.

Hence `P phi_j` is DA.  Since `x_j phi_j=1/z`, the term `x_jS phi_j=S(1/z)` is DA, so `Q phi_j`
is DA.

Collect the finitely many monomials in the remaining translations.  Rational independence of the
periods gives distinct classes `h mod omega_j Z`, and

`Q phi_j=sum_h L_h(delta) phi_j(z+h)`

with `L_h in C[delta]`, not all zero.  The atomic scaled-digamma theorem says that these translates
are differentially algebraically independent.  A nonzero constant-coefficient differential-linear
form in differentially independent elements is differentially transcendental: if `L_h` has maximal
order `d` with leading coefficient `a != 0`, then the `r`-th derivative of the form has the new
leading jet `a phi_h^(d+r)`, giving a triangular injective substitution

`K{Z} -> K{phi_h : h}`,  `Z |-> sum_h L_h(delta)phi_h`.

Thus `Q phi_j` cannot be DA, a contradiction.  This proves `(A)`.

## Differential boundary cylinder `[PROVED HERE]`

The cyclic differential-translation module generated by `Psi_N` modulo DA functions is therefore

`M_N ~= D_N/(x_1...x_N) ~= (R_N/(x_1...x_N))[delta]`.   `(B)`

Since `x_1...x_N` is squarefree, its translation-character support is the reduced thin boundary

`V(x_1...x_N)=union_j V(T_j-1)`.

Equation `(B)` says that this boundary carries a free, unbounded differential prolongation.  For
`N=1` it specializes to

`M_1 ~= C[delta]`,

the unit-shift Gamma atom with all polygamma orders.  This is the first nontriptic theorem realizing
the proposed structural law

```text
infinite differential-algebraic capacity
concentrated on a reduced thin constraint boundary.
```

The word "capacity" here is exact: it is polynomial degree in `delta`, not physical time and not
the cardinality of the zero divisor.  The thin boundary is forced by the complete source
annihilator, while differential algebraic independence prevents the prolongation direction from
collapsing modulo DA.

## Full source-face descent `[PROVED HERE]`

The squarefree boundary also has an exact all-face reconstruction law.  For each nonempty subset
`S` of `{1,...,N}`, set

`F_S=D_N/(x_j : j in S)`

and form the augmented alternating restriction complex

```text
0 -> M_N -> direct_sum_(|S|=1) F_S -> direct_sum_(|S|=2) F_S -> ...
     -> F_{1,...,N} -> 0.                                  (C)
```

Here `M_N` is the Barnes module in `(B)`.  Complex `(C)` is exact.

To prove this, put `u_j=T_j-1`.  The Laurent operator ring is the localization of
`C[delta,u_1,...,u_N]` obtained by inverting the `1+u_j`, so it suffices by flatness to prove
exactness before localization.  Decompose every term by the monomial basis
`delta^m u_1^(a_1)...u_N^(a_N)`.  For a fixed monomial, let `Z={j:a_j=0}`.  The monomial is absent
when `Z` is empty; otherwise its surviving summands in `(C)` are exactly the augmented simplicial
cochain complex of the full simplex on the nonempty vertex set `Z`, which is exact.  Taking the
direct sum over all monomials proves `(C)`.

Therefore compatible differential data on the individual Barnes source faces glue to a unique
global HT/DA orbit class.  There is no higher **singular kinematic** interaction cohomology in this
family, even though every face carries unbounded differential capacity.  This separates two axes
which a unified HT theory must not conflate:

```text
hypertranscendental capacity  !=  descent obstruction height.   (D)
```

For Barnes, the singular descent axis is exact.  The next theorem computes the remaining regular
normalization inertia and shows that it collapses after rank two once the singular marker and one
pointing are retained.

## Exact derived face fracture `[PROVED HERE; LEAN CORE FORMALIZED]`

The face restriction has a stronger derived form.  Fix `j`, put

`p_j=product_(k != j)x_k`,

and regard `M_N=D_N/(p_j x_j)`.  Multiplication by the two factors gives an exact two-periodic
matrix factorization

```text
... -> M_N --p_j-> M_N --x_j-> M_N --p_j-> M_N --x_j-> M_N -> ... .  (C+)
```

For every nonempty set `S` of source faces, put `B_S=D_N/(x_j:j in S)`.  The length-one free
resolution of `M_N` restricts to the zero-differential complex `[B_S -> B_S]`, hence

```text
Tor_i^(D_N)(M_N,B_S)=B_S for i=0,1,
Tor_i^(D_N)(M_N,B_S)=0   for i>=2.                            (C++)
```

Thus relation death and capacity birth are the same free face module in adjacent degrees.  The
number of deleted source directions does not increase the derived amplitude.  This gives a sharp
nonperiodic no-go to any universal law equating face codimension, cohomological obstruction depth,
and HT capacity.  The positive replacement is the canonical two-periodic conservation pair
`(B_S[-1],B_S)`, while the unbounded HT capacity remains the independent `delta`-prolongation.

The complete statement, proof, novelty boundary, and next transverse divisor-to-winding target are
recorded in `barnes-differential-source-face-matrix-factorization.md`.

## Rank-two regular-inertia collapse `[PROVED HERE]`

The remaining inertia can also be computed.  Fix the lower Barnes source faces and let `F,G` be
two nonzero global meromorphic solutions of the same top-level source equations.  Their ratio

`p=G/F`

is fixed by every structural translation.  Suppose `N>=2`, the periods are rationally independent,
`F` and `G` have the same full principal-part marker after `dlog`, and they agree at one common
regular nonzero pointing.

Then `F=G`.

Indeed, equality of the logarithmic principal parts says that `p'/p` is entire.  Therefore `p` has
neither zeros nor poles.  Choose two rationally independent periods.

1. If their ratio is real, it is irrational.  Their integer span has nonzero periods tending to
   zero, so meromorphic period rigidity already makes `p` constant.
2. If their ratio is nonreal, they span a lattice.  The entire function `p` is bounded by reduction
   to a compact fundamental parallelogram, hence is constant by Liouville.

The pointing forces that constant to be one.  Equivalently, on this Barnes stratum,

```text
K^S intersect ker(full singular principal parts) intersect ker(pointing) = {1}.   (E)
```

Thus the common-kernel gate is actually discharged.  Rank one and rank at least two are separated
by a sharp reconstruction transition:

```text
one source period:
  full singular localization + pointing still leaves nontrivial regular periodic units;

two Q-independent source periods:
  full singular localization + one pointing reconstructs the top meromorphic solution.  (F)
```

Bare rank-two source plus pointing is still insufficient in the lattice case, because nonconstant
elliptic meromorphic gauges exist.  The singular marker is essential: it removes their divisors,
after which compact-period rigidity removes the regular remainder.

Combining `(A)`, `(C)`, and `(E)` gives a complete source-effectively normalized Barnes theorem:
the differential characteristic boundary is exact, its face descent is acyclic, and its residual
regular gauge is killed by one calibration.  This is the strongest positive result produced by the
Gamma reconstruction no-go.

### Formalization of the reverse-inclusion criterion

The algebraic backbone of the reverse inclusion — that `P` lies in the principal annihilator ideal
`(x_1 ... x_N)` iff every pairwise-coprime ladder operator `x_j = T_j - 1` divides `P`, so that
`x_1...x_N` failing to divide `P` yields a distinguished index `j` with `x_j` not dividing `P` — is
formalized axiom-clean in `GaloisForLFunctions.CoprimeProductAnnihilator`:

```text
mem_span_prod_iff_forall_dvd_of_pairwise_isRelPrime :
  P in Ideal.span {prod_j f j}  <->  forall j, f j | P
```

for any finite family `f` of pairwise `IsRelPrime` elements of a commutative ring (via mathlib's
`prod_dvd_of_isRelPrime`). Instantiated at `f j = T_j - 1` in the Laurent ring `R_N` this is exactly
the ideal-membership step of the reverse inclusion; the ring-specific input is the pairwise
coprimality of the `T_j - 1`, and the analytic input is the hypertranscendence making `Q phi_j`
non-DA.

The same module now also carries the **mixed-difference threshold** in its algebraic form:

```text
prod_dvd_prod_pow_iff_forall_one_le :
  (prod_j f j) | (prod_j f j ^ a j)  <->  forall j, 1 <= a j
```

for pairwise `IsRelPrime` **non-unit** factors.  This is exactly the statement that
`x_1^{a_1} ... x_N^{a_N} Psi_N` is DA iff every `a_j` is positive: repetition inside a proper subset
of the structural directions never reaches the annihilator, while one use of every direction
already does, whatever the further repetition.  The non-unit hypothesis is what the ladder
operators supply.  `#print axioms` clean.

### Formalization of the differential boundary consequences

`GaloisForLFunctions.HTGeometry.DifferentialOrbitMarkerLocalization` formalizes the algebraic
noncompression forced by the free `delta` direction:

```text
polynomialJetReporter_eq_zero_iff;
finiteJetMarker_eq_zero_iff_pointwise_X_pow_dvd;
exists_finiteJetMarker_ne_zero_of_ne_zero;
finiteJetMarker_blind_fullMarker_aperiodic;
divisorShadow_eq_zero_iff_exists_differentialMarkerShift;
analyticOnNhd_constant_of_period_one_tau;
analyticOnNhd_eq_one_of_period_one_tau_of_pointed.
```

Thus every fixed differential depth has an explicit nonzero invisible atom, every individual
finite marker is detected at some depth, and the ordinary divisor shadow has kernel exactly the
positive differential tail.  Lean also proves that the regular entire gauge on an oriented
rank-two period lattice is scalar and that one pointing kills it.  The general normalized
simplex-block contraction underlying the all-face proof is already formalized by
`standardSimplexNormalizedCoproduct_exactAt_succ`.

The **descent half of `(C)` is now concrete Lean** rather than abstract blocks.
`GaloisForLFunctions.HTGeometry.MonomialFaceIdeal` works in the ring
`MvPolynomial sigma R` -- with `R = C[delta]` and `sigma = {1..N}` this is exactly the operator ring
of `(C)` before localization, which is the reduction the paper proof performs -- and proves:

```text
mem_faceIdeal_iff       : P in (X_j : j in S)  <->  every monomial of P uses some direction of S;
iInf_faceIdeal_singleton: (intersection_j (X_j)) = (prod_j X_j);
iInf_faceIdeal_pair     : (intersection_j (X_n, X_j)) = (X_n) + (prod_j X_j);
exists_glue             : pairwise-compatible atomic data have a global lift.
```

The first is the monomial description of every face ideal.  The second is exactness at `M_N`, that
is uniqueness of the global boundary class.  The third is the distributivity of the face lattice
along a vertex, and it is exactly what powers the fourth: `exists_glue` is exactness at the atomic
term, that is existence.  Together they are

```text
0 -> A/(prod_j X_j) -> direct_sum_j A/(X_j) -> direct_sum_{j,k} A/(X_j,X_k)
```

exact, which is the stated consequence of `(C)`: compatible differential data on the individual
Barnes source faces glue to a unique global HT/DA orbit class.  `#print axioms` clean.

The **higher degrees of `(C)` are now Lean too**, in the same concrete model.
`GaloisForLFunctions.HTGeometry.MonomialFaceComplexExactness` gives the complex an explicit cochain
form: a degree-`c` cochain sends every `c`-element direction set `S` to a polynomial none of whose
monomials uses a direction of `S`, that is a representative of a class of `A/(X_j : j in S)`, and
`faceCoboundary` is the signed face sum followed by deletion of the monomials that meet the new
direction.

```text
faceCoboundary_faceCoboundary      : the differential squares to zero;
faceComplex_augmentation_kernel    : a degree-zero cocycle lies in (prod_j X_j) -- exactness at M_N;
faceComplex_exact                  : every cocycle of degree c+1 is a coboundary of degree c.
```

The proof is the paper argument made literal.  `coeff_faceCoboundary` shows that taking the
coefficient of a fixed monomial turns the differential into the reduced simplicial coboundary on
the vertex set `unusedDirections d` of directions that monomial does not use; that vertex set is
nonempty whenever the coefficient is nonzero, so the corpus cone contraction
`simplicialCoboundary_simplicialCone_of_subset` applies to each block, and the finitely many block
primitives reassemble into a polynomial primitive with the same avoidance property.  Complex `(C)`
is therefore exact in every degree, unconditionally, with no analytic input.  `#print axioms` clean.

### The algebraic steps of `(A)` are Lean

Three of the four steps of the reverse inclusion of `(A)` are formalized, leaving only the analytic
input.

1. **Choice of a missing ladder factor.**  `mem_span_prod_iff_forall_dvd_of_pairwise_isRelPrime`
   above: if the squarefree product does not divide `P`, some `x_j` does not.
2. **Face splitting `P = Q + x_j S`.**  `GaloisForLFunctions.FaceIdeal.sub_faceTruncate_mem_faceIdeal`
   proves `P - P|_{x_j = 0} in (x_j)`, with `faceTruncate` the restriction that deletes the
   monomials using the deleted direction.  Uniform in the face, so it covers the whole
   `D_j = prod_{k != j} x_k` step at once.
3. **Triangular differential freeness.**  The step "a nonzero constant-coefficient
   differential-linear form in differentially independent elements is differentially transcendental"
   is `hypertranscendentalOver_differentialOperatorRow_of_ne_zero`
   (`GaloisForLFunctions.HTGeometry.DifferentialOperatorRowHypertranscendence`), proved by the
   operator-row independence criterion rather than by an ad hoc jet induction; its degree-zero
   specialization `hypertranscendentalOver_linearCombination_of_ne_zero` is the pure-translation
   case used in the scalar annihilator theorem.  Axiom-clean.
4. **Atomic differential independence of the scaled-digamma translates.**  This is the remaining
   analytic input (Hardouin--Singer plus discrete residues) and is not in Lean.

So `(A)` reduces in Lean to constructing the Barnes source itself and proving its ladder relation
and atomic independence.

### First brick of the Barnes analytic construction

`GaloisForLFunctions.HTGeometry.ConePeriodSummability` supplies the convergence foundation that
every construction of the Barnes source needs.  For a frame in a common open half-plane,
`mul_sum_le_norm_conePeriod` proves that the cone value `|sum_i n_i omega_i|` is at least a fixed
positive multiple of the total degree, and `summable_conePeriod_inv_pow` proves

```text
sum_{n in N^N, n != 0} |sum_i n_i omega_i|^{-(N+1)} < infinity,
```

the critical exponent: the `N`-fold subtraction of the expansion of `1/(z+w)` in powers of `1/w`
leaves a term of size `|z|^N/|w|^{N+1}`, so this is exactly the summability that makes the
regularized Barnes series converge, and equally the summability that makes the genus-`N`
Weierstrass product for `1/Gamma_N` converge.  The proof compares with a finite product of
`p`-series at `p = 1 + 1/N` through `prod_succ_le_pow`, using the corpus lemma
`summable_fintype_pi_product_of_nonneg`.  `#print axioms` clean.

### Second brick: the Weierstrass factor of arbitrary genus

`GaloisForLFunctions.HTGeometry.WeierstrassGenusFactor` builds the other half of the convergence
input.  For every genus `p` it defines the truncated logarithm and the elementary factor

```text
E_p(w) = (1 - w) exp(w + w^2/2 + ... + w^p/p),
```

and proves the collapsed derivative

```text
hasDerivAt_weierstrassFactor : E_p'(w) = -w^p exp(w + ... + w^p/p),
```

which is the geometric telescoping `(1-w)(1 + w + ... + w^{p-1}) = 1 - w^p` and nothing else.  Since
`E_p(0) = 1`, the mean-value inequality on the segment then gives the defining genus estimate

```text
norm_weierstrassFactor_sub_one_le :
  |w| <= 1/2  ->  |E_p(w) - 1| <= exp(B_p) |w|^{p+1},
```

with `B_p = weierstrassLogBound p` an explicit symbolic constant.  Mathlib has only the genus-one
case (through the reciprocal-Gamma product); arbitrary genus is corpus-new.

The two bricks meet in `norm_weierstrassFactor_conePeriod_sub_one_le`: outside the finitely many
small cone values, the factor at `-z/w_n` deviates from one by at most a constant times
`|w_n|^{-(N+1)}`, which `summable_conePeriod_inv_pow` sums.  That is exactly the local majorant
that makes the genus-`N` Weierstrass product over the period cone converge, hence makes
`1/Gamma_N` entire and puts `Psi_N` in the meromorphic differential field.  `#print axioms` clean.

### Third brick: the cone product is entire

`GaloisForLFunctions.HTGeometry.BarnesConeProduct` assembles the two bricks into the actual
Weierstrass product over the period cone,

```text
barnesConeProduct omega z = prod_{n in N^N} E_N(-z / w_n),
```

the zero exponent vector contributing trivially.  `finite_conePeriod_lt` proves that only finitely
many exponent vectors have small cone value — the linear growth of the cone bounds the total degree,
and the exponent vectors of bounded total degree form a finite box.  So on any compact set the
argument of all but finitely many factors is inside the half-disc, where the genus estimate applies,
and the resulting majorant is the summable weight of the first brick.  Hence

```text
hasProdLocallyUniformlyOn_barnesConeFactor : the product converges locally uniformly on C;
differentiable_barnesConeProduct           : its limit is entire.
```

This is the analytic object the annihilator theorem needs: an entire function whose zero set is the
shifted cone, so that the Barnes source is a ratio of entire functions and lands in the meromorphic
differential field.  `#print axioms` clean.

### Fourth brick: the Barnes source lives in the meromorphic differential field

`GaloisForLFunctions.HTGeometry.BarnesSourceMero` places the object in the corpus's own field.
Every elementary factor is one at the origin, so `barnesConeProduct_zero_arg` gives value one there
and `barnesConeProduct_ne_zero` makes the product a nonzero entire function.  Hence

```text
barnesConeAnalytic       : the product as an element of the global analytic germ domain;
barnesConeAnalytic_ne_zero, barnesConeMero_ne_zero;
barnesSourceLogDerivMero : its logarithmic derivative in the meromorphic differential field.
```

`barnesSourceLogDerivMero` is the Barnes source `Psi_N` up to the linear factor and the
normalization exponential.  Both of those are differentially algebraic, so by the normalization
remark in the Setup they are invisible to every annihilator statement taken modulo the
differentially algebraic sector — which is the only way this card's theorems use the source.
`#print axioms` clean.

### Fifth brick: the rational atom of one factor, and the ladder reindexing

`GaloisForLFunctions.HTGeometry.BarnesConeLogDeriv` computes the atom the ladder is built from.
The collapsed derivative of the elementary factor makes the exponential correction cancel between
numerator and denominator, leaving a single rational term:

```text
logDeriv_barnesConeFactor : logDeriv (z |-> E_N(-z/w_n)) (z) = (-z/w_n)^N / (w_n + z),
```

valid whenever the exponent vector is nonzero and `z` is not the corresponding pole; the
nonvanishing `conePeriod_ne_zero` of a nonzero cone value comes from the linear growth of the cone.
So the Barnes source is, term by term, the classical regularized digamma series
`sum_n (-1)^N z^N / (w_n^N (w_n + z))`.

The combinatorics of the ladder is also isolated:

```text
conePeriod_add_single             : w_{n + e_j} = w_n + omega_j;
conePeriod_eq_sum_erase_of_eq_zero: on the slice n_j = 0 the cone value is the deleted-frame one.
```

These are exactly the two reindexings the ladder proof performs — the shift `n -> n + e_j` is a
bijection onto `{n : n_j >= 1}`, and what it leaves over is the cone of the frame with `omega_j`
deleted.  `#print axioms` clean.

### Sixth brick: the source is the convergent atom series

`GaloisForLFunctions.HTGeometry.BarnesSourceSeries` sums the atoms.  Everything rests on one
principle, `summable_of_conePeriod_majorant`: a nonnegative weight dominated by the inverse
`(N+1)`-st cone power **outside a finite set** is summable, the exceptional set being finite by
`finite_conePeriod_lt`.  Applied twice it gives

```text
barnesConeProduct_ne_zero_of_notMem_poles : off the poles w_n + z = 0 the product is nonzero;
summable_logDeriv_barnesConeFactor        : the atoms are summable at every point;
logDeriv_barnesConeProduct_eq_tsum        : logDeriv (barnesConeProduct omega) z
                                              = sum_n (-z/w_n)^N / (w_n + z).
```

The last one is the identification the card's proof works with: the constructed source **is** the
classical regularized digamma series of the Barnes hierarchy, as a convergent sum, not merely
factorwise.  `#print axioms` clean.

### Seventh brick: the atoms and the ladder shift

`GaloisForLFunctions.HTGeometry.BarnesLadderAtoms` names the atom and isolates the ladder mechanism.
`barnesAtom` is the rational term, `logDeriv_barnesConeProduct_eq_tsum_barnesAtom` restates the
source as `sum_n barnesAtom omega n z`, and the ladder shift is exact at the level of one atom:

```text
barnesAtom_shift_sub :
  barnesAtom omega n (z + omega_j) - barnesAtom omega (n + e_j) z
    = (numerator difference) / (w_{n+e_j} + z),
```

because `conePeriod_shift_denom` makes the two denominators literally the same.  The reindexing is a
bijection, `addSingleEquiv : (N^ind) ≃ {n // 1 ≤ n_j}`, and `conePeriod_of_not_one_le` identifies
the complementary slice with the deleted-frame cone — the lower step of the hierarchy.

So the ladder is now reduced to summing the displayed atomwise identity over the bijection and
splitting off the complementary slice.  `#print axioms` clean.

### Eighth brick: the ladder decomposition

`GaloisForLFunctions.HTGeometry.BarnesLadderDecomposition` sums the atomwise shift over the
bijection.  `summable_barnesAtom` gives convergence of the atom series at every point,
`summable_barnesAtom_add_single` transports it along the injection `n -> n + e_j`, and
`tsum_barnesAtom_split` splits the series along the slice `1 <= n_j` using the reindexing
bijection.  Together:

```text
barnesSource_ladder_decomposition :
  Psi(z + omega_j) - Psi(z)
    = sum_n (A_n(z + omega_j) - A_{n+e_j}(z))  -  sum_{n_j = 0} A_n(z).
```

Both series converge — the first as a difference of two convergent ones, the second as a subseries
— so this is an identity of genuine sums, not a formal rearrangement.  The second term is the atom
series of the deleted-frame cone, that is the lower step of the hierarchy; the first is the
correction the normalization absorbs.  This is the exact shape in which the card's proof uses the
ladder.  `#print axioms` clean.

### Ninth brick: the genus mismatch is a monomial

The slice left over by the ladder is the cone of the deleted frame, but its atoms carry the genus of
the ambient frame — one higher than the lower step of the hierarchy uses.
`GaloisForLFunctions.HTGeometry.BarnesGenusShift` prices that mismatch exactly.

`barnesAtomPow_succ_sub` raises the genus of one atom:

```text
A^{p+1}_n(z) - A^p_n(z) = -(-z/w_n)^p / w_n,
```

the pole cancelling because `(-z/w) - 1 = -(z+w)/w`.  Those corrections are summable at the critical
genus (`summable_barnesGenusCorrection`), so `tsum_barnesAtomPow_succ` shifts the genus of the whole
series, and `tsum_barnesGenusCorrection_eq` evaluates the correction:

```text
sum_n (genus correction) = (-1)^N z^N * coneZeta omega,
```

a **constant times `z^N`**.  The genus mismatch between the ladder slice and the lower source is
therefore a monomial, hence differentially algebraic, hence invisible modulo the DA sector — which
is precisely the normalization remark of the Setup, now proved rather than assumed for the
constructed object.  `#print axioms` clean.

### Tenth brick: the ladder slice is the lower source

`GaloisForLFunctions.HTGeometry.BarnesSliceReindex` identifies what the ladder leaves over.
Restriction is a bijection `sliceEquiv` from the vanishing slice onto the cone of the deleted frame,
`conePeriod_sliceEquiv` matches the cone values, `sliceEquiv_eq_zero_iff` matches the zero exponent
vector, and `card_subtype_ne_succ` records that the deleted frame has one direction fewer — so the
slice carries the ambient genus, one above the deleted frame's own.  Hence

```text
tsum_barnesAtom_slice :
  sum_{n_j = 0} A_n(z) = sum_g A^{N}_g(z)   over the deleted-frame cone,
```

and combining with the genus pricing of the previous brick,

```text
tsum_barnesAtom_slice_eq_lower :
  sum_{n_j = 0} A_n(z)
    = (lower source of the deleted frame) - (-1)^{N-1} z^{N-1} coneZeta(deleted frame).
```

So the ladder slice **is** the lower step of the Barnes hierarchy, up to a monomial.  Combined with
the ladder decomposition this is the constructed-object form of the classical ladder
`x_j Psi_N = -Psi_{N-1}(z | omega^{(j)})` modulo the differentially algebraic sector.
`#print axioms` clean.

### Eleventh brick: the correction is polynomial in the common denominator

`GaloisForLFunctions.HTGeometry.BarnesLadderGenusOne` explains why the ladder correction is tame.
Writing `D = w_{n+e_j} + z` for the common denominator produced by `conePeriod_shift_denom`, both
numerators of the correction are polynomials in `D` with constant term one:

```text
neg_div_eq_one_sub_denom       : -(z + omega_j)/w_n      = 1 - D/w_n,
neg_div_shift_eq_one_sub_denom : -z/w_{n+e_j}            = 1 - D/w_{n+e_j}.
```

So their difference is divisible by `D`, and the correction — that difference over `D` — is a
polynomial in `D` rather than a term with a pole.  At genus one the polynomial is the constant

```text
barnesAtom_shift_sub_card_one :
  A_n(z + omega_j) - A_{n+e_j}(z) = 1/w_{n+e_j} - 1/w_n,
```

with no `z` at all (`barnesAtom_shift_sub_card_one_const`).  The genus-one ladder correction is
therefore a telescoping difference of inverse cone values, which is the structural reason the
order-one source has a rational shift difference.  `#print axioms` clean.

### Twelfth brick: the correction factors at every genus

`GaloisForLFunctions.HTGeometry.BarnesLadderGeneralGenus` removes the genus restriction.
`barnesNumerator_sub` says the difference of the two numerators is the common denominator times the
telescoping factor,

```text
u - v = D (1/w_{n+e_j} - 1/w_n),
```

and factoring the difference of `N`-th powers through `geom_sum_2_mul` cancels `D` outright:

```text
barnesAtom_shift_sub_eq_geom :
  A_n(z + omega_j) - A_{n+e_j}(z)
    = (1/w_{n+e_j} - 1/w_n) * sum_{k<N} u^k v^{N-1-k}.
```

So at **every** genus the ladder correction is the genus-one telescoping factor multiplied by a
polynomial in the two numerators, and in particular it has no pole.  The genus-one case is the
special case where the polynomial factor is the empty product one.  `#print axioms` clean.

### Thirteenth brick: the order-one ladder, complete

`GaloisForLFunctions.HTGeometry.BarnesLadderOrderOne` closes the bottom step of the hierarchy for
the constructed source.  With a single structural direction the slice on which the exponent vanishes
is the zero vector alone, whose atom is zero, so `tsum_barnesAtom_slice_card_one` kills the slice
series.  The correction series then splits off its zero term, which is the explicit rational atom at
the unit exponent, and every remaining term is the argument-free telescoping difference of the
previous brick.  Hence

```text
barnesSource_shift_sub_card_one :
  Psi(z + omega_j) - Psi(z)
    = -A_{e_j}(z) + sum_{n != 0} (1/w_{n+e_j} - 1/w_n),
```

an explicit rational function of the argument plus a constant.  **The order-one ladder of the
constructed source is rational, hence differentially algebraic** — the bottom of the Barnes ladder,
proved rather than assumed.  `#print axioms` clean.

### Fourteenth brick: the ladder coefficients converge

Expanding the factored correction in powers of the argument produces, for each split `k` of the
genus, a constant obtained by summing one coefficient over the cone.
`GaloisForLFunctions.HTGeometry.BarnesLadderCoefficients` proves those constants exist.

`conePeriod_inv_sub_inv` puts the telescoping factor in closed form,

```text
1/w_{n+e_j} - 1/w_n = -omega_j / (w_n w_{n+e_j}),
```

so the coefficient at split `k` is `omega_j` over a product of `N+1` cone values.  Both cone values
are at least `delta` times the total degree, and `norm_conePeriod_le` bounds the ambient one above
by `(sum_i |omega_i|)` times the same total degree, so

```text
norm_barnesLadderCoefficient_le :
  |c_{n,k}| <= |omega_j| ((sum_i |omega_i|)/delta)^{N+1} |w_n|^{-(N+1)},
```

the critical exponent.  Hence `summable_barnesLadderCoefficient`: every coefficient family is
summable, so the expansion of the correction series in powers of the argument has well-defined
constant coefficients.  `#print axioms` clean.

### Fifteenth brick: the correction is a polynomial at every genus

`GaloisForLFunctions.HTGeometry.BarnesLadderPolynomial` completes the ladder correction.
`barnesLadderTerm_eq` separates the argument from the cone in each term of the factored correction,

```text
t_n u_n^k v_n^{N-1-k} = ((-1)^{N-1} (z + omega_j)^k z^{N-1-k}) * c_{n,k},
```

with `c_{n,k}` the ladder coefficient, carrying no `z` at all.  Since the `k`-sum is finite and each
coefficient family is summable, the cone sum passes inside, giving

```text
tsum_barnesLadderCorrection_eq :
  sum_n (A_n(z + omega_j) - A_{n+e_j}(z))
    = -A_{e_j}(z)
      + sum_{k<N} ((-1)^{N-1} (z + omega_j)^k z^{N-1-k}) * (sum_n c_{n,k}).
```

The first term is the explicit rational atom at the unit exponent; the rest is a **polynomial in the
argument with constant coefficients**.  So the ladder correction is differentially algebraic at every
genus, not only at genus one.  `#print axioms` clean.

Combined with `barnesSource_ladder_decomposition` and `tsum_barnesAtom_slice_eq_lower`, the classical
Barnes ladder `x_j Psi_N = -Psi_{N-1}(z | omega^{(j)})` now holds for the constructed source modulo
the differentially algebraic sector, at every order.

### Sixteenth brick: the discrete-residue obstruction

The atomic theorem's contradiction is the statement that a rationally summable rational function has
vanishing discrete residues — proved on paper "by telescoping the finitely many principal parts of
`g` along each integer orbit".  That telescoping is combinatorial, and
`GaloisForLFunctions.HTGeometry.TelescopingJumpObstruction` proves it.

Along one integer orbit the poles of `g` form a finite set of integers, and the poles of
`g(u+1) - g(u)` are exactly its **jumps**: the places where the membership indicator changes, since
at an extreme pole one of the two terms is regular and cannot cancel the other.  Then

```text
exists_two_jumps        : a nonempty finite set of integers has two distinct jumps —
                          after its maximum and before its minimum;
eq_empty_of_single_jump : if the indicator is constant across every step but one, the set is empty.
```

So a telescoped difference never has exactly one pole on an orbit: a rational function whose poles on
some orbit reduce to a single class is not rationally summable.  That is the obstruction the atomic
scaled-digamma theorem invokes at the pole class `-h_i/omega + Z`.

The same module carries the statement at the level of **pole orders**, which is the form the
argument actually needs, since the atomic theorem's contradiction is about a pole of order `d_i + 1`
rather than mere membership:

```text
exists_two_order_jumps            : a finitely supported order function on an orbit has two
                                    distinct steps where it changes value;
eq_zero_of_single_order_jump      : one exceptional step forces the order to vanish identically;
eq_zero_of_jump_poles_subsingleton: if every order jump forces a pole of the difference and the
                                    difference has at most one pole on the orbit, there are no
                                    poles at all.
```

The last one is the interface the analytic step plugs into: it isolates exactly what the
discrete-residue argument contributes, leaving only the no-cancellation fact at an extreme pole as
analytic input.  `#print axioms` clean.

### Seventeenth brick: the obstruction for an actual rational function

`GaloisForLFunctions.HTGeometry.RationalPoleOrder` instantiates the obstruction on genuine rational
functions.  `poleOrder g c` is the multiplicity of `c` as a root of the reduced denominator, so
`poleOrder_pos_iff` makes it positive exactly at the poles, and
`finite_support_poleOrder_orbit` shows the orbit order function `orbitPoleOrder g c` is finitely
supported: a nonzero polynomial has finitely many roots and the orbit map is injective.  Feeding
that into the interface gives

```text
poleOrder_orbit_eq_zero_of_subsingleton :
  if every order jump of g along the orbit forces a pole of the telescoped difference, and the
  difference has at most one pole on the orbit, then g has no pole on the orbit at all,
not_isRoot_denom_orbit_of_subsingleton  : the same conclusion stated at the denominator.
```

So for an honest rational function the discrete-residue obstruction is now a theorem, modulo the
single analytic fact that an extreme pole survives the telescoping.

### Eighteenth brick: the extreme pole survives

That last fact is now proved too, and it needs no valuation theory.  `RegularAt g c` says `g` can be
written with a denominator not vanishing at `c`, and `regularAt_iff_poleOrder_eq_zero` identifies it
with vanishing pole order through `RatFunc.denom_dvd`.  Regularity is closed under the ring
operations — `RegularAt.add`, `RegularAt.neg`, `RegularAt.sub` — because a common denominator works,
so the regular functions at a point form a local subring.  Hence

```text
poleOrder_sub_eq_zero : regular minus regular is regular,
poleOrder_sub_ne_zero : if a has a pole at c and b does not, then b - a has a pole at c.
```

The second is the survival statement: a regular difference would exhibit `a = b - (b - a)` as
regular.  At the top of a pole orbit `g(u+1)` is regular while `g(u)` is not, so the telescoped
difference has a pole there — and symmetrically below the bottom.  `#print axioms` clean.

### Nineteenth brick: shifting the variable moves the orbit

The telescoped difference compares `g` with `g(X+1)`, so the obstruction needs the shift to move
pole orbits by one step.  `GaloisForLFunctions.HTGeometry.PolynomialShift` supplies it:
`polyShift a` is the algebra automorphism substituting `X + a`, with inverse the substitution of
`X - a`, and `polyShift_sub_C` sends the linear factor at `c + a` to the linear factor at `c`.
Transporting divisibility by powers of linear factors along the automorphism gives

```text
rootMultiplicity_polyShift :
  rootMultiplicity c (p(X + a)) = rootMultiplicity (c + a) p.
```

So the pole orbit of the shifted function is the shifted pole orbit, which is exactly the
reindexing the telescoping performs.  `#print axioms` clean.

### Twentieth brick: the discrete-residue theorem, assembled

`GaloisForLFunctions.HTGeometry.RationalNonSummability` puts the pieces together.
`finite_orbit_poles` makes the pole set of `g` on an orbit finite;
`not_regularAt_sub_of_not_regularAt` and its mirror say that a pole minus a regular term is a pole
in either order; and `exists_two_jumps` supplies two jumps of the finite pole set.  At each jump one
of the two terms of the telescoped difference is regular and the other is not, so the difference has
a pole there.  Therefore

```text
regularAt_orbit_of_telescoped_pole_subsingleton :
  if gs is regular exactly one step along from g, and gs - g has at most one pole on the orbit
  c + Z, then g is regular at every point of that orbit.
```

This is the discrete-residue obstruction as a theorem about honest rational functions: a telescoped
difference never has exactly one pole on an orbit.  The shift enters only through its effect on pole
position, so it appears as the hypothesis on `gs`, which the variable shift of the previous brick
supplies.  `#print axioms` clean.

### Twenty-first brick: the operator produces a pole of the predicted order

The atomic theorem's contradiction needs not only that the left side has a pole in the class, but
that its order is `d_i + 1` with nonzero coefficient — that is, that the pole is *exactly* as deep
as the operator is long.  `poleOrder_powerDenominator` supplies the algebra:

```text
numerator not vanishing at c  ->  poleOrder (P / (X - c)^m) c = m.
```

The proof cross-multiplies against the reduced presentation and compares root multiplicities, using
coprimality of numerator and denominator to kill the numerator's multiplicity.  Applied to
`L(delta) (1/(omega u + h))`, whose denominator is a pure power of the linear factor of order
`deg L + 1`, it gives exactly the order the discrete-residue argument needs.  `#print axioms` clean.

### Twenty-second brick: the obstruction in applied form

`not_telescoped_of_unique_orbit_pole` states the obstruction the way the atomic theorem invokes it:

```text
a rational function with exactly one pole on an integer orbit is not a telescoped difference.
```

Given a hypothetical telescoper `r = gs - g`, the single pole makes the pole set of `gs - g` on that
orbit a subsingleton, the previous theorem forces `g` regular on the whole orbit, hence `gs` regular
at the pole as well, hence `gs - g` regular there — contradicting the pole.  This is exactly the
step "the corresponding discrete residue is therefore nonzero, contradicting rational summability"
of the atomic proof, with the pole class `-h_i/omega + Z` supplied by the distinctness of the shifts
and the pole depth supplied by the previous brick.  `#print axioms` clean.

Only the special-function identification `(A)` remains a paper theorem; it is not inserted into
Lean as an analytic axiom.

`GaloisForLFunctions.HTGeometry.NormalCrossingFaceMatrixFactorization` formalizes the local
derived-fracture algebra over every commutative domain:

```text
range_normalCrossingLeftFactor_eq_ker_rightFactor;
range_normalCrossingRightFactor_eq_ker_leftFactor;
normalCrossingFactorization_twoPeriodicExact.
```

Applied after the paper-proved identification `(A)`, these are exactly the two kernel/image laws
in `(C+)`.  No Barnes analytic assertion is inserted as a Lean axiom.

## Mixed-difference threshold `[PROVED HERE]`

For nonnegative integers `a_1,...,a_N`, not all zero,

`x_1^(a_1) ... x_N^(a_N) Psi_N`

is DA if and only if every `a_j` is positive. Repetition in any proper subset of the structural directions never destroys hypertranscendence; using every distinct direction once is sufficient, regardless of further repetition.

The radical and prime decomposition are

`(x_1...x_N)=intersection_(j=1)^N (x_j)`.

Thus the DA constraint variety in the structural translation torus is the reduced union of the `N` coordinate hypertori `T_j=1`.

## Classification of every finite translate product `[PROVED HERE]`

Let

`P=sum_(n in Z^N) c_n T^n in Z[T_1^(+-1),...,T_N^(+-1)]`

have finite support, and define

`F_P(z)=product_(n in Z^N) Gamma_N(z+n dot omega|omega)^(c_n)`.

Then

`F_P is DA over C(z) iff P in (x_1...x_N)`.

Indeed,

`F_P'/F_P=P Psi_N`.

If `F_P` is DA, then its logarithmic derivative is DA. Conversely, if `P Psi_N` is DA, then `F_P` satisfies the first-order differential equation

`Y'=(P Psi_N)Y`

over a differential-algebraic extension of `C(z)`; transitivity of differential algebraicity makes `F_P` DA over `C(z)`. The exact annihilator theorem completes the classification.

For example, the elementary full-cube quotient encoded by `x_1...x_N` is DA, but this theorem classifies arbitrary finite supports and coefficients, not only cubes produced visibly by the ladder recurrence.

## Consequences `[PROVED HERE]`

1. Every `Gamma_N(z|omega)` is hypertranscendental: take `P=1`.
2. Every proper-subset mixed difference of `Psi_N` remains hypertranscendental, even with arbitrary repeated differences.
3. Every finite integer product of translates outside the principal constraint ideal is hypertranscendental.
4. The structural translation module generated by `Psi_N` modulo DA functions is the cyclic module

   `R_N/(x_1...x_N)`.

5. Its reduced support is the union of coordinate hypertori, so the Barnes hierarchy has a codimension-one constraint geometry, in contrast with the higher-codimension skeleton ideal obtained for the multiple elliptic gamma hierarchy.
6. The full differential-translation module is `(R_N/(x_1...x_N))[delta]`, its all-face complex
   is exact, and for `N>=2` its full singular marker plus one pointing reconstructs the top
   meromorphic source solution.
7. Every nonempty source face has derived restriction concentrated in exactly two adjacent
   degrees, both equal to the free boundary module; deeper faces do not create higher Tor.

## Degenerate and boundary cases

1. **Dependent periods.** Rational independence is essential to the proof. If the periods have an integer relation, distinct exponent vectors can induce the same translate modulo `omega_j Z`, and extra group-ring cancellations can occur.
2. **Equal-period Vigneras hierarchy.** The theorem does not cover the diagonal specialization `omega_1=...=omega_N`. Nishizawa and Ogawara already prove strong hypertranscendence and algebraic-independence results there.
3. **Arbitrary complex shifts.** The theorem computes the annihilator in the Laurent group ring of the structural period lattice. It does not classify operators using shifts outside that lattice.
4. **Nonconstant coefficients.** Coefficients depending on `z` are outside the theorem.
5. **Normalization.** Polynomial-exponential normalization factors are DA and hence invisible modulo the DA field.

## Scientific-novelty audit

### Established parents

- Barnes' multiple gamma ladder equations are classical.
- Nishizawa (2001) proves nonexistence of algebraic differential equations for Barnes multiple gamma functions and explicitly notes differential relations among several such functions in the equal-period case.
- Hardouin--Singer (2008), Corollary 3.2, supplies the exact differential-dependence criterion for meromorphic indefinite sums used in the atomic theorem.
- Standard rational summability theory supplies the discrete-residue obstruction.
- Ogawara (2017), Corollary 4.2, proves algebraic independence of the equal-step Vigneras hierarchy
  together with all derivatives of Euler Gamma.  This is a direct parent for the differential-
  independence mechanism, but it does not treat rationally independent Barnes periods or compute
  a differential-translation annihilator ideal.
- Perez-Marco (2021) gives source-and-growth uniqueness theorems for higher Gamma functions.  These
  control normalization gauge, not the DA-relative differential-translation module.

### Exact residue not yet located

The search so far has not located a source computing

`Ann_DA^diff(Psi_N)=(product_j(T_j-1))`

inside the full ring `C[delta,T_1^(+-1),...,T_N^(+-1)]` for rationally independent Barnes periods,
proving persistence under arbitrary differential order and arbitrary repetition in a proper subset
of translation directions, or identifying the HT/DA orbit module with the differential cylinder
over the squarefree characteristic boundary.

### Why external promotion remains provisional

The mathematical proof is complete, but two gates remain open.

1. **Literature gate.** Nishizawa's proceedings chapter is not openly available in full. Google Books snippets show that its special differential relation concerns equal periods, which is disjoint from the rationally independent setting, but a full-text audit is still required.
2. **Routine-parent gate.** Once the exact annihilator question is posed, the proof is a short
   synthesis of the Barnes ladder, Hardouin--Singer telescoping, triangular differential freeness,
   and elementary commutative algebra.  The exact module is structurally significant for the HT
   theory, but independent expert judgment is still needed on whether it warrants a standalone
   paper rather than forming one main theorem in a broader paper on HT characteristic boundaries.

The targeted audit therefore gives a provisional novelty pass for the conjunction, not a priority
certificate.  It may be described internally as candidate new scientific knowledge, but external
publication claims still require the unavailable Nishizawa proceedings text and independent
specialist review.

## Primary sources checked

- E. W. Barnes, *On the theory of the multiple gamma function*, Transactions of the Cambridge Philosophical Society 19 (1904), 374--425.
- M. Nishizawa, *Generalized Holder's Theorem for Multiple Gamma Function*, Physics and Combinatorics 2000 (2001), 220--232, DOI `10.1142/9789812810007_0010`.
- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*, Mathematische Annalen 342 (2008), 333--377.
- R. Perez-Marco, *On the definition of higher Gamma functions* (2021), especially Section 6 and the Barnes ladder equation.
- H. Ogawara, *On criteria for algebraic independence of collections of functions satisfying algebraic difference relations*, Opuscula Mathematica 37 (2017), 457--472.

## Gates

- [x] Exact statement isolated from the already-known hypertranscendence theorem.
- [x] Atomic scaled-digamma differential-independence theorem proved.
- [x] Exact structural translation-annihilator ideal proved.
- [x] Exact full differential-translation annihilator ideal proved.
- [x] Differential boundary-cylinder interpretation proved.
- [x] Full Barnes source-face complex proved exact.
- [x] Exact two-periodic source-face matrix factorization and all-face Tor law proved.
- [x] Rank-two regular-inertia collapse and pointed reconstruction proved.
- [x] Classification transferred to every finite integer translate product.
- [x] Degenerate equal-period and dependent-period cases separated.
- [x] Ogawara equal-step differential-independence parent separated from the rationally-independent
      Barnes statement.
- [x] Mixed-difference threshold formalized in its algebraic form.
- [x] Descent half of the all-face complex `(C)` formalized concretely: monomial description of the
      face ideals, atomic intersection, vertex distributivity, and the gluing theorem.
- [x] Higher-degree exactness of `(C)` in the same concrete monomial model, together with
      `delta^2 = 0` and exactness at the augmentation.
- [x] Algebraic steps 1--3 of the reverse inclusion of `(A)` formalized (missing ladder factor,
      face splitting, triangular differential freeness).
- [x] Cone summability at the critical exponent formalized, the convergence foundation of the
      Barnes source construction.
- [x] Genus-`p` Weierstrass elementary factor, its collapsed derivative and its half-disc estimate,
      together with the cone majorant that couples it to the summability brick.
- [x] Local uniform convergence of the genus-`N` cone product and entirety of its limit.
- [x] Barnes source object in Lean: the cone product is a nonzero entire germ, hence a nonzero
      element of the global meromorphic field, and its logarithmic derivative is the source.
- [x] The rational atom of one cone factor, and the two cone reindexings the ladder is assembled
      from.
- [x] The source expressed as the convergent atom series, with nonvanishing of the product off the
      poles.
- [x] The atom of the source named, the atomwise ladder shift proved, and the reindexing bijection
      and complementary slice constructed.
- [x] The ladder decomposition: the shift difference of the source equals the correction series
      over the cone minus the atom series of the deleted-frame slice, both convergent.
- [x] The genus mismatch between the ladder slice and the lower source priced exactly: a constant
      times `z^N`, hence a polynomial.
- [x] The slice-to-deleted-frame reindexing, so the ladder slice is the lower source up to a
      monomial.
- [x] The ladder correction shown polynomial in the common denominator, and constant at genus one.
- [x] The ladder correction factored at every genus as the telescoping factor times a polynomial in
      the numerators, hence pole-free.
- [x] The order-one ladder complete: the shift difference of the order-one source is an explicit
      rational function plus a constant.
- [x] The coefficient families of the higher-genus correction proved summable at the critical
      exponent.
- [x] The ladder correction assembled as an explicit rational atom plus a polynomial, at every
      genus, so the ladder holds modulo the DA sector at every order.
- [x] The discrete-residue obstruction: a telescoped difference has no single-pole orbit, at the
      level of both membership and pole orders, with the interface form for the analytic step.
- [x] The obstruction instantiated on genuine rational functions through the denominator
      multiplicity, with finiteness of the orbit order function.
- [x] Survival of an extreme pole under telescoping, from the local subring of regular functions.
- [x] The variable shift as an algebra automorphism moving root multiplicities along the orbit.
- [x] The discrete-residue theorem assembled: a telescoped difference of rational functions never
      has exactly one pole on an integer orbit.
- [x] The exact pole order of a reduced power-denominator fraction, giving the depth an operator of
      order `d` produces at a simple pole.
- [x] The obstruction in applied form: a single orbit pole blocks rational summability outright.
- [x] Theorem `(A)` formalized end to end on the Barnes source: `Ann_DA^diff(Psi_N) = (x_1...x_N)D_N`.
- [x] The structural annihilator `Ann_DA(Psi_N) = (x_1...x_N)` formalized on the Barnes source.
- [x] The difference-Galois criterion for indefinite sums, in the only direction the theorem needs,
      proved from scratch: no Hardouin--Singer citation is required.
- [x] The atomic differential independence of the scaled-digamma translates, unconditionally.
- [ ] Full-text audit of Nishizawa's 2001 Barnes paper.
- [ ] Equivalent/stronger-result audit across difference Galois theory and Barnes product identities.
- [ ] Routine-parent and significance verdict from independent experts.
- [ ] Scientific novelty promotion, if and only if all remaining gates pass.

## Log

- 2026-07-10 — Opened after the universal spectrum and rational `q`-residue directions were parent-killed as routine bridges.
- 2026-07-10 — Isolated the exact annihilator, rather than hypertranscendence of `Gamma_N`, as the only possible new residue.
- 2026-07-10 — Proved atomic differential independence of distinct scaled-digamma translation orbits using Hardouin--Singer Corollary 3.2 and discrete pole-orbit residues.
- 2026-07-10 — Closed the converse annihilator proof and transferred it to all finite integer translate products.
- 2026-07-10 — Kept status at `[NOVELTY UNVERIFIED]` because the direct 2001 parent is only partially accessible and the routine-parent gate remains live.
- 2026-07-17 — Extended the exact annihilator from pure translations to the full constant-coefficient differential-translation ring.
- 2026-07-17 — Identified the resulting module as a free differential cylinder over the reduced squarefree source boundary and proved its augmented all-face complex exact.
- 2026-07-17 — Proved the rank-two reconstruction transition: full logarithmic principal parts plus one pointing kill the common Barnes gauge, while rank-one Gamma retains regular periodic inertia.
- 2026-07-17 — Targeted Ogawara and Perez-Marco checks found the differential-independence and normalization parents but not the combined annihilator, descent, and reconstruction theorem; novelty remains provisional pending independent audit.
- 2026-08-03 — Formalized the mixed-difference threshold algebraically, and the descent half of the
  all-face complex concretely in the monomial model: face-ideal monomial description, atomic
  intersection, vertex distributivity of the face lattice, and the gluing theorem.  Axiom-clean.
- 2026-08-03 — Closed complex `(C)` in Lean in every degree: explicit cochain model, `delta^2 = 0`,
  exactness at the augmentation, and exactness in every positive degree by the monomial-blockwise
  cone contraction.  The only remaining paper step is the special-function identification `(A)`.
- 2026-08-03 — Audited `(A)` step by step: the triangular-freeness step turned out to be already
  Lean in `DifferentialOperatorRowHypertranscendence`, the face splitting is now Lean, and the
  cone summability at the critical exponent — the convergence foundation of the Barnes source
  itself — is now Lean.  What is left of `(A)` is the source object and its ladder.
- 2026-08-03 — Built the genus-`p` Weierstrass elementary factor with its collapsed derivative and
  half-disc estimate (mathlib has only genus one), and coupled it to the cone summability by the
  majorant `|E_N(-z/w_n) - 1| <= C |w_n|^{-(N+1)}`.  The convergence input of the Barnes product is
  now complete; what remains is the product itself and the ladder.
- 2026-08-03 — Built the cone product and proved it entire: only finitely many exponent vectors have
  small cone value, so on every compact set the genus estimate and the cone summability give a
  uniform majorant.  The Barnes analytic object now exists in Lean; what remains is its zero set,
  the ladder relation, and the atomic independence.
- 2026-08-03 — Placed the constructed object in the corpus's meromorphic differential field: the
  cone product is one at the origin, hence a nonzero entire germ, and `barnesSourceLogDerivMero` is
  its logarithmic derivative.  The Barnes source is now a genuine element of the differential field
  the annihilator theorem is stated in; the ladder relation is next.
- 2026-08-03 — Computed the rational atom of one cone factor: the exponential correction cancels
  and the collapsed derivative leaves `(-z/w_n)^N/(w_n+z)`, so the source is the classical
  regularized digamma series term by term.  Isolated the two cone reindexings the ladder needs.
- 2026-08-03 — Summed the atoms: one majorant principle (dominated off a finite set by the inverse
  cone powers) gives both nonvanishing of the product off the poles and summability of the atoms,
  hence `logDeriv (barnesConeProduct) = sum_n (-z/w_n)^N/(w_n+z)`.  The constructed source is now
  identified with the classical regularized digamma series as a convergent sum.
- 2026-08-03 — Named the atom, restated the source as the atom series, and proved the atomwise
  ladder shift: the shifted argument and the shifted exponent vector share a denominator, so the
  ladder difference is the numerator difference over it.  Built the reindexing bijection and
  identified the complementary slice with the deleted-frame cone.
- 2026-08-03 — Summed the atomwise shift over the bijection: `barnesSource_ladder_decomposition`
  gives the shift difference of the source as the correction series minus the deleted-frame slice
  series, both genuinely convergent.  The ladder is now an identity of sums in Lean.
- 2026-08-03 — Priced the genus mismatch: raising the genus of an atom costs a pole-free term, the
  corrections are summable at the critical genus, and their sum is `(-1)^N z^N` times a cone zeta
  value — a monomial.  The Setup's normalization remark is now proved for the constructed source.
- 2026-08-03 — Identified the ladder slice: restriction is a bijection onto the deleted-frame cone
  matching cone values and the zero vector, and the genus drops by exactly one, so the slice is the
  lower source minus a monomial.  The classical ladder now holds for the constructed object modulo
  the DA sector, except for the remaining correction series.
- 2026-08-03 — Showed the ladder correction is polynomial in the common denominator: both numerators
  are `1 - D/w`, so their difference is divisible by `D`.  At genus one the quotient is the constant
  `1/w_{n+e_j} - 1/w_n`, a telescoping difference with no argument dependence at all.
- 2026-08-03 — Removed the genus restriction: the numerator difference is the denominator times the
  telescoping factor, so factoring the difference of `N`-th powers cancels the denominator and the
  correction is the telescoping factor times a polynomial in the numerators, at every genus.
- 2026-08-03 — Completed the order-one ladder: at one direction the slice series vanishes and the
  correction series splits into the explicit rational atom at the unit exponent plus an
  argument-free constant, so the order-one shift difference is rational.
- 2026-08-03 — Proved the higher-genus ladder coefficients summable: the telescoping factor in
  closed form makes each coefficient `omega_j` over `N+1` cone values, and the two-sided cone bounds
  put it at the critical exponent.
- 2026-08-03 — Assembled the correction: separating the argument from the cone in each term and
  passing the cone sum inside the finite genus sum gives the correction as the unit-exponent atom
  plus a polynomial with constant coefficients.  The ladder now holds modulo DA at every order; the
  only remaining input of `(A)` is the atomic differential independence.
- 2026-08-03 — Proved the discrete-residue obstruction combinatorially: a nonempty finite set of
  integers has two jumps, so a telescoped difference never has exactly one pole on an orbit.  This
  is the contradiction step of the atomic scaled-digamma theorem.
- 2026-08-03 — Lifted the obstruction from membership to pole orders and exposed the interface form:
  once the no-cancellation fact at an extreme pole is supplied, a difference with at most one pole
  on an orbit forces the pole order to vanish identically.
- 2026-08-03 — Instantiated the obstruction on rational functions: pole order as denominator
  multiplicity, finiteness of the orbit order function, and the resulting no-single-pole-orbit
  theorem.  The only analytic input left in the discrete-residue step is survival of an extreme
  pole under telescoping.
- 2026-08-03 — Proved that survival with no valuation theory: regular functions at a point form a
  local subring, so a regular difference would make the polar term regular.  The discrete-residue
  step of the atomic theorem is now complete; what remains is the Hardouin--Singer criterion.
- 2026-08-03 — Built the variable shift as an algebra automorphism and proved it moves root
  multiplicities along the orbit, which is the reindexing the telescoped difference performs.
- 2026-08-03 — Assembled the discrete-residue theorem for rational functions: finite orbit pole set,
  two jumps, and pole-minus-regular-is-pole give that a telescoped difference never has exactly one
  pole on an orbit.  The rational-summability obstruction of the atomic theorem is now Lean.
- 2026-08-03 — Added the exact pole order of a reduced power-denominator fraction, which is the
  depth a constant-coefficient operator of order `d` produces at a simple pole.  Every algebraic
  ingredient of the atomic theorem is now Lean; the remaining input is Hardouin--Singer itself.
- 2026-08-03 — Stated the obstruction in applied form: a rational function with exactly one pole on
  an integer orbit is not a telescoped difference.  This is the contradiction the atomic proof
  reaches once Hardouin--Singer supplies the telescoper.
- 2026-08-03 — Removed the Hardouin--Singer dependence entirely.  The direction the theorem needs is
  elementary: coefficient shift plus variable translation acts on the top of the degree filtration by
  `sigma` alone, so normalising a leading coefficient makes the relation ideal descend to a
  `Phi`-invariant element, partial derivatives linearise it, and an affine-linear invariant *is* a
  telescoper.  Proved in Lean over an arbitrary `sigma`-`delta`-field and for an arbitrary shift.
- 2026-08-03 — Identified the Barnes annihilator with the top squarefree Veronese ideal, making the
  Barnes source a normal-crossing source and closing the second-realization gate of the fat-point
  card.
- 2026-08-03 — Split off the structural (translation-only) annihilator as an explicit theorem, by
  descending divisibility along the retraction that evaluates the differential variable at zero.
- 2026-08-03 — **`(A)` is proved in Lean for the Barnes source itself**: for rationally independent
  periods in a half-plane, `P Psi_N` is differentially algebraic over `C(z)` exactly when the full
  ladder product divides `P`.  No analytic or difference-Galois input is assumed anywhere in the
  chain.
- 2026-08-03 — The descent induction is Lean: the ladder product over all directions but `j` reaches
  the single-direction source modulo DA, with the accumulated sign.  At `S = univ` this is the ladder
  hypothesis of `(A)`.
- 2026-08-03 — Found and removed the sign obstruction: the descent produces `(-1)^N phi`, so `(A)`
  now takes its ladder hypothesis with a nonzero constant multiple, divided out by the constant
  pass-through laws of the operator action.
- 2026-08-03 — Added the operator half of the descent: the ladder product peels one direction, and
  the empty product acts trivially.  Both halves of the induction are now in matching form.
- 2026-08-03 — Restated the ladder step between subframes indexed by a finite set and by that set
  with one element erased — the exact inductive step for the descent to a single direction.
- 2026-08-03 — Proved the Barnes source invariant under reindexing the frame, the lemma that keeps
  the nested subtypes of repeated deletion from drifting apart during the iteration.
- 2026-08-03 — Removed the `hfull` hypothesis from `(A)`: the full ladder product lands in the DA
  sector automatically, by one application of the ring action to the ladder hypothesis.
- 2026-08-03 — Lifted the multi-period ladder into the field: one ladder step of the Barnes source is
  differentially algebraic, i.e. `x_j Psi_N = -Psi_(N-1)` modulo DA.  Only the two iterations remain.
- 2026-08-03 — Proved the multi-period ladder defect equal to one explicit rational function off the
  poles, composing the ladder decomposition, the correction series, the slice identification and the
  single-step atom.  With the previous brick this makes the defect differentially algebraic.
- 2026-08-03 — Made rational ladder corrections free: an element with a rational punctured
  representative is that rational function, hence differentially algebraic.  The multi-period ladder
  now needs only the explicit `p/q` and the pointwise identity off the poles.
- 2026-08-03 — Attached the atomic theorem to the genuine Barnes source: its corrected order-one
  translates are differentially independent over `C(z)`, and a nonzero operator avoiding the ladder
  direction is hypertranscendental on it.
- 2026-08-03 — Ran the lift: the order-one Barnes ladder is now an identity in the meromorphic
  field, and after absorbing its constant by a shift coboundary the corrected source satisfies the
  normalized ladder equation `sigma_omega phi - phi = 1/(z + omega_j)` — the hypothesis `hφ` of `(A)`.
- 2026-08-03 — Completed the ingredients of the germ lift: punctured-thinness of the cone poles, the
  rational representative, and the representatives of the Barnes source and its translate.  All that
  is left of `(A)` is running these on the corpus's pointwise ladder identities.
- 2026-08-03 — Built the keystone of the germ lift: a punctured-local representative determines the
  field element, plus the representatives of the two pieces a ladder identity is made of (the
  logarithmic derivative of an entire germ, and a translate).  Only the local finiteness of the
  Barnes pole set is still to be fed in.
- 2026-08-03 — Put the ladder defect in its natural normalization `1/(z + b)` throughout the chain,
  which is the shape the corpus's Barnes source produces; recorded the three-step route for lifting
  the pointwise Barnes ladder into the meromorphic field, the only remaining step of `(A)`.
- 2026-08-03 — Assembled `(A)` in Lean as an exact iff for any laddered source: the operator ring
  action (including multiplicativity), the splitting at `T_j = 1` with its avoidance property, and a
  divisibility criterion that needs no primality.  Only the instantiation of the two ladder
  hypotheses at the Barnes source remains.
- 2026-08-03 — Built the reverse-inclusion engine of `(A)`: the operator row on ladder translates, the
  monomial shift dictionary from rational independence of the periods, and the action of
  `C[delta, T_1, ..., T_N]` with its two laws (DA sector preserved; a nonzero operator avoiding one
  direction is HT on that direction's ladder solution).  Recorded the five remaining bookkeeping
  steps that would state `(A)` as a single Lean theorem.
- 2026-08-03 — Closed the last Lean gate of `(A)`: dilation of the coordinate transfers the corpus's
  unit-shift orbit-residue theorem to the shift `omega`, and the atomic scaled-digamma theorem is now
  unconditional Lean in the global meromorphic differential field, in the exact form the card uses
  (translates of a solution of the order-one Barnes ladder).

### Twenty-third brick: the difference-Galois criterion is elementary

The paper proof of the atomic theorem cites Hardouin--Singer, Corollary 3.2, for the implication

```text
the indefinite sums are differentially dependent  ==>  a constant-coefficient telescoper exists.
```

That citation is **not needed**.  The implication is elementary, and the Lean development proves it
in full generality.  Let `K` be a field with a ring endomorphism `sigma`, let `R` be a family in `K`,
and let

`Phi(P) = P^sigma(X + R)`

act on `K[X_i : i]`.  If `y_i` lie in a `sigma`-`delta`-extension of `K` with `sigma(y_i) - y_i = r_i`
in `K`, then the jets satisfy `sigma(delta^k y_i) = delta^k y_i + delta^k r_i`, so applying `sigma`
to a polynomial relation among the jets is exactly applying `Phi` to the relating polynomial: the
ideal `J` of relations is `Phi`-stable, and it contains no nonzero constant because `K` embeds in the
extension.

Three facts then force a telescoper.

1. *Descent.*  Normalising one top-degree coefficient of `P` to `1` makes it cancel in
   `Phi(P) - P`, because `Phi` acts on the top-degree coefficients by `sigma` alone.  Hence either
   `Phi(P) = P` or the pair `(total degree, number of top-degree monomials)` drops lexicographically.
   The descent terminates, and only at a nonzero `Phi`-invariant element of `J`.
2. *Linearisation.*  `Phi` commutes with every partial derivative, and in characteristic zero some
   partial derivative lowers the total degree by exactly one.  A `Phi`-invariant element of positive
   degree therefore produces a `Phi`-invariant polynomial of degree exactly one.
3. *Reading off.*  An affine-linear `b + sum_i a_i X_i` satisfies
   `Phi(b + sum a_i X_i) = (sigma b + sum sigma(a_i) R_i) + sum sigma(a_i) X_i`, so invariance says
   exactly `sigma(a_i) = a_i` and `sum_i a_i R_i = sigma g - g` with `g = -b`.

Lean: `shiftTranslate`, `coeff_shiftTranslate_of_le`, `totalDegree_shiftTranslate_le`,
`exists_ne_zero_shiftTranslate_eq_self`, `pderiv_shiftTranslate`, `exists_pderiv_totalDegree_eq`,
`exists_totalDegree_eq_one_shiftTranslate_eq_self`, `shiftTranslate_affineLinearPoly`,
`exists_affineLinearPoly_repr`, `exists_telescoper_of_mem_ideal`, and the differential form
`exists_telescoper_of_not_differentialIndependent`.  All `#print axioms` clean.

This is strictly stronger than what the card used: the criterion holds over an arbitrary
`sigma`-`delta`-field, for an arbitrary shift, with no Picard--Vessiot theory.

### Twenty-fourth brick: dilating the coordinate transfers the orbit-residue theorem

Composition with `X -> omega X` is an automorphism of `C(X)` for `omega != 0` and conjugates the
translation by `omega` into the unit translation,

`(r(X + omega))(omega X) = r(omega X + omega) = (r(omega X))(X + 1)`,

fixes the constants, and scales the jet increments of a simple pole:

`((-1)^j j! / (X + b)^(j+1))(omega X) = omega^(-(j+1)) (-1)^j j! / (X + b/omega)^(j+1)`.

Hence the unit-shift orbit-residue theorem transfers to every nonzero shift: for `b_i` pairwise
incongruent modulo `omega Z`, no nonzero constant charge matrix on the increment jets is an
`omega`-shift coboundary; and a rational function fixed by a nonzero translation is constant, which
is what identifies the `sigma`-invariant coefficients of the telescoper as complex numbers.

Lean: `ratScaleBy`, `ratScaleBy_ratShiftBy`, `ratShiftBy_fixed_eq_const`,
`ratScaleBy_familyIncrement`, `ratShiftBy_sub_familyIncrement_combination`.  `#print axioms` clean.

### Twenty-fifth brick: the atomic scaled-digamma theorem

Combining the two previous bricks in the global meromorphic differential field closes the atomic
step of `(A)`:

```text
if sigma_omega(y_i) - y_i = 1/(X + b_i) with the b_i pairwise incongruent mod omega Z,
then y_1, ..., y_r are differentially independent over C(X).
```

A differential relation would give constants, not all zero, and a rational `g` with
`sum_(i,j) a_(i,j) d^j/dX^j (1/(X + b_i)) = g(X + omega) - g(X)`, which the dilated orbit-residue
theorem forbids.  Specialised to the translates of one solution of the order-one Barnes ladder
`sigma_omega phi - phi = 1/X` — that is, to `phi = Psi_1(.|omega)` — this is exactly the atomic
scaled-digamma theorem of the card: for shifts pairwise distinct modulo `omega Z`, the translates
`phi(z + h)` are differentially algebraically independent over `C(z)`.

Lean: `differentialIndependent_of_shiftDefect_simplePole`, `differentialIndependent_ladderTranslate`.
`#print axioms` clean.

### Twenty-sixth brick: the reverse-inclusion step of `(A)`, in operator form

Three further layers turn the atomic theorem into the exact step the reverse inclusion of `(A)`
performs.

*The operator row.*  Restricting the coefficient field of the atomic theorem to the constants keeps
the translates differentially independent, and a nonzero row of constant-coefficient differential
operators on a differentially independent family is hypertranscendental over the constants.  Since
differential algebraicity over the coordinate field descends to the constants, the form is
hypertranscendental over the coordinate field as well:

```text
hypertranscendentalOver_ladderTranslateOperatorRow(_fintype) :
  L != 0  ==>  sum_i L_i(delta) phi(z + h_i)  is HT over C(z).
```

*The monomial shift dictionary.*  For rationally independent periods, two distinct exponent vectors
avoiding the direction `j` translate through shifts in different classes modulo `omega_j Z`; an
equality of classes is a nontrivial integral relation among the periods
(`monomialShift_incongruent`).

*The operator ring in action.*  `diffTranslateApply` applies an element of
`C[delta, T_1, ..., T_N]` -- a finitely supported family of differential operators indexed by
translation exponent vectors -- to a meromorphic element.  Two laws:

```text
differentialAlgebraicOver_diffTranslateApply :
  y DA  ==>  P y DA                                   (the forward inclusion engine)

hypertranscendentalOver_diffTranslateApply_of_avoid :
  P != 0, no monomial of P uses T_j, sigma_(omega_j) phi - phi = 1/z
     ==>  P phi is HT over C(z)                       (the reverse inclusion engine)
```

The second is exactly the card's step "`Q phi_j` cannot be DA", with the finitely many monomials of
`Q` collected and the distinctness of their shift classes supplied by the dictionary.  `#print axioms`
clean.

### What remains to state `(A)` as one Lean theorem

Every *ingredient* of `(A)` is now Lean.  Assembling the single statement
`Ann_DA^diff(Psi_N) = (x_1...x_N) D_N` needs only bookkeeping in the operator ring, in this order.

1. **The operator action is a ring action.**  `diffTranslateApply` is additive in the operator and
   satisfies `(P Q) y = P (Q y)`; the inputs are all present -- `differentialOperatorApply_mul`,
   `differentialOperatorApply_add`, `addTranslationMeroEquiv_differentialOperatorApply`,
   `addTranslationMeroEquiv_add`, and additivity of `monomialShift`.  The model is
   `D_N = MvPolynomial (Fin N) (Polynomial C)` with the variables acting as the translations `T_j`,
   which is literally the type `(Fin N ->0 N) ->0 Polynomial C` the action is defined on.
2. **The splitting at `T_j = 1`.**  `P - P|_{T_j = 1}` lies in `(T_j - 1)`, monomial by monomial from
   `(T_j - 1) | T_j^m - 1`.  In the translation variables `P|_{T_j = 1}` literally omits `T_j`, which
   is exactly the avoidance hypothesis of `hypertranscendentalOver_diffTranslateApply_of_avoid`.
3. **The divisibility criterion.**  `prod_j (T_j - 1) | P  <->  forall j, (T_j - 1) | P`, from the
   already formalized `mem_span_prod_iff_forall_dvd_of_pairwise_isRelPrime` once the `T_j - 1` are
   pairwise relatively prime -- equivalently, after the automorphism `T_j -> T_j + 1`, once the
   variables are, which follows from their primality.
4. **The ladder reduction.**  `D_j Psi_N = +- Psi_1(z|omega_j)` modulo the DA sector, by iterating the
   Barnes ladder decomposition already proved for the source; and `x_1...x_N Psi_N` is rational, the
   forward inclusion.
5. **Assembly.**  Forward from `differentialAlgebraicOver_diffTranslateApply`; reverse from 1--4 plus
   `hypertranscendentalOver_diffTranslateApply_of_avoid`.

No further analytic input is needed: after this session the analytic content of `(A)` is complete and
what is left is the operator-ring algebra above.

### Twenty-seventh brick: `(A)` assembled

The operator ring, the splitting and the divisibility criterion are now Lean, and with them the
statement `(A)` itself.

*The ring action.*  `diffTranslateApply` is additive in the operator and in the argument, the unit
acts as the identity, and

```text
diffTranslateApply_mul : (P Q) y = P (Q y),
```

proved by reduction to monomials: translations commute with every constant-coefficient differential
operator and compose additively, so the translation monomials multiply exactly as the operators do.
The model is `D_N = MvPolynomial (Fin N) C[delta]`.

*The splitting.*  For any two algebra homomorphisms out of a polynomial ring, the difference of the
values lies in the ideal generated by the differences on the variables
(`sub_mem_span_range_sub_of_algHom`).  Applied to the identity and to the substitution `T_j -> 1` this
gives `P - P|_{T_j=1} in (T_j - 1)`, and `vars` shows `P|_{T_j=1}` does not involve `T_j` at all --
exactly the avoidance hypothesis of the reverse-inclusion engine.

*The divisibility criterion, without primality.*  Over a domain,

```text
(forall j in S, P|_{T_j = 1} = 0)  ==>  prod_{j in S} (T_j - 1) | P,
```

by induction on `S`: after factoring out one `T_i - 1`, the substitution in another direction fixes
that factor, and cancelling it in a domain propagates the vanishing to the cofactor.  The card's plan
called for pairwise coprimality of the ladder operators; it is not needed.  Contrapositively, a
missing divisibility hands over both the distinguished direction `j` and the nonzero restriction
`Q = P|_{T_j=1}` at once.

*The theorem.*  For rationally independent periods and a source `Psi` with the ladder property --
`D_j Psi = phi_j` modulo the DA sector, where `phi_j` solves `phi(z+omega_j) - phi(z) = 1/z`, and the
full product `prod_j (T_j - 1) Psi` already DA -- every constant-coefficient differential-translation
operator satisfies

```text
differentialAlgebraicOver_diffTranslateApply_iff_fullLadder_dvd :
  P Psi is DA   <->   prod_j (T_j - 1) | P.
```

That is `(A)`: `Ann_DA^diff(Psi_N) = (x_1 ... x_N) D_N`.  Forward by the ring action on an already DA
element; reverse by the splitting, the ladder reduction, the rationality of `(T_j - 1) phi_j = 1/z`,
and the hypertranscendence of the nonzero restriction.  `#print axioms` clean.

What remains is to instantiate the two ladder hypotheses at the corpus's Barnes source, which is the
iterated ladder decomposition already proved for it.

### Twenty-eighth brick: the ladder defect in its natural normalization

The whole chain -- atomic independence, operator row, monomial sum, operator action, and `(A)` --
now carries the ladder defect in the shape

```text
sigma_(omega_j) phi - phi = 1/(z + b),
```

with an arbitrary pole location `b`, instead of the normalized `1/z`.  This is what the corpus's
Barnes source actually produces: its order-one ladder gives the defect `-1/(z + omega_j)` plus a
constant, and a constant is a shift coboundary (`w = (c/omega) z`), so replacing `Psi_1` by
`-Psi_1 + w` puts the defect in exactly the above shape with `b = omega_j`.  The generalization is
free: the translates of `phi` then have defects `1/(z + b + h_i)`, and the incongruence condition on
the `h_i` is unchanged.

### The one remaining step: lifting the Barnes ladder into the field

`(A)` is now a Lean theorem for every source with the ladder property.  Instantiating it at the
corpus's Barnes source `barnesSourceLogDerivMero` needs the pointwise ladder identities -- already
proved as identities of functions off the poles -- to be lifted to identities in the meromorphic
field.  The route is fixed by what the corpus already owns:

1. **Uniqueness of a punctured representative.**  If two field elements are represented by the same
   function on a punctured neighbourhood of every point, they are equal: cross-multiplying gives two
   entire functions agreeing off a discrete set, hence agreeing, by the identity theorem the corpus
   already uses for `isDomain_analyticSubring`.  The representation predicate
   `HasPuncturedMeromorphicRep` and its closure properties are built; only the uniqueness direction
   is missing.
2. **Representatives of the pieces.**  `Psi = logDeriv` of an entire germ has the punctured
   representative `P'/P`; translation of a representative is the translated representative; the
   rational atom and the lower source are represented by themselves.
3. **The discreteness of the pole set**, which makes "for all `z` off the poles" into "eventually on
   every punctured neighbourhood" -- the local finiteness `finite_conePeriod_lt` already proved for
   the cone.

With those, `barnesSource_ladder_decomposition` and `barnesSource_shift_sub_card_one` become the two
hypotheses `hladder` and `hφ` of `(A)`, and the exact annihilator theorem holds for the Barnes source
itself.

### Twenty-ninth brick: the germ lift, keystone and pieces

Two of the three steps of the lift are now Lean.

*Uniqueness of a punctured representative.*

```text
eq_of_hasPuncturedMeromorphicRep :
  x, y represented by the same function on a punctured neighbourhood of every point  ==>  x = y.
```

Cross-multiplying the two entire presentations gives an entire `f k - h g`.  At a point where the
first denominator is nonzero the second is nonzero on a punctured neighbourhood -- a nonzero entire
function has isolated zeros -- so `f k - h g` vanishes there, hence vanishes on a full neighbourhood
(a nonzero analytic germ cannot vanish on a punctured neighbourhood), hence identically by the
identity theorem on the connected plane.  Equality of the cross products is equality of the
fractions.  This is the missing direction the corpus's `HasPuncturedMeromorphicRep` layer did not
have.

*Representatives of the pieces.*

```text
hasPuncturedMeromorphicRep_logDeriv : logDeriv of an entire germ is represented by f'/f;
HasPuncturedMeromorphicRep.translate : a translate is represented by the translated function.
```

The first is the compatibility of the field derivation with differentiation of analytic germs; the
second is that translation of the field is precomposition on germs, together with the fact that the
translation carries the punctured neighbourhood of a point to that of its translate.  `#print axioms`
clean.

What remains of the lift is the third step: the Barnes pole set `{-conePeriod omega n : n != 0}` is
locally finite (`finite_conePeriod_lt` already gives this), so "for every `z` off the poles" upgrades
to "eventually on the punctured neighbourhood of every point", which is the hypothesis the two
theorems above consume.  With that, `barnesSource_shift_sub_card_one` and
`barnesSource_ladder_decomposition` become identities in the field, and they are exactly the
hypotheses `hφ` and `hladder` of `(A)`.

### Thirtieth brick: the lift is assembled except for the identity itself

The third step of the germ lift is now Lean too, together with the representatives the Barnes ladder
needs.

*The cone poles are punctured-thin.*  Only finitely many cone periods lie in a bounded region, so the
pole set meets a unit ball in a finite set, and a finite set is avoided on the punctured neighbourhood
of every point:

```text
eventually_nhdsNE_conePeriod_add_ne_zero :
  for every z0, eventually on the punctured neighbourhood of z0, no nonzero cone period cancels the
  argument;
eventuallyEq_nhdsNE_of_forall_off_conePoles :
  hence a pointwise identity valid off the poles holds eventually on every punctured neighbourhood.
```

*The representatives.*

```text
hasPuncturedMeromorphicRep_ratfuncToMero          : a rational function, by num/denom;
hasPuncturedMeromorphicRep_barnesSourceLogDerivMero : the Barnes source, by logDeriv of the cone
                                                      product;
hasPuncturedMeromorphicRep_addTranslation_...      : its translate, by the translated logDeriv.
```

All `#print axioms` clean.  Every ingredient of the lift is now present: uniqueness, the
representatives of source, translate and rational function, and the punctured-thinness that converts
"off the poles" into "eventually".  What remains is to run them on
`barnesSource_shift_sub_card_one` -- whose right-hand side is, after expanding the order-one atom,
`1/omega_j - 1/(z + omega_j)` plus a constant tsum -- to obtain the field identity

```text
sigma_(omega_j) Psi - Psi = algebraMap (c - 1/(X + omega_j)),
```

and then to absorb the constant `c` by the shift coboundary `w = (c/omega_j) z`, giving the exact
hypothesis `hφ` of `(A)` with `b = omega_j`; the multi-period `hladder` follows by iterating the
ladder decomposition the same way.

### Thirty-first brick: the order-one Barnes ladder, in the field

The lift now runs.  Both sides of the pointwise order-one ladder are represented on the punctured
neighbourhood of every point -- the left by the translated logarithmic derivative, the right by the
logarithmic derivative plus an explicit rational function -- the poles are punctured-thin, and a
punctured representative determines the element.  Hence, in the meromorphic differential field,

```text
addTranslationMeroEquiv_barnesSourceLogDerivMero_card_one :
  sigma_(omega_j) Psi_1 = Psi_1 + ((1/omega_j + K) - 1/(z + omega_j)),
```

with `K` the constant the ladder produces (the convergent sum of inverse cone-period differences).
The order-one atom, expanded at `card = 1`, is exactly `-z/(omega_j (omega_j + z))`, whose negative is
`1/omega_j - 1/(z + omega_j)`; that is where the constant comes from.

Absorbing the constant by the shift coboundary `w = ((1/omega_j + K)/omega_j) z` and negating gives

```text
addTranslationMeroEquiv_barnesLadderSolutionOne :
  sigma_(omega_j) phi = phi + 1/(z + omega_j),      phi = -Psi_1 + w,
```

which is exactly the hypothesis `hφ` of `(A)` with `b = omega_j` -- the reason the defect shape was
generalized from `1/z` to `1/(z + b)` two bricks ago.  `#print axioms` clean.

The remaining work on `(A)` is now purely the multi-period ladder: iterating
`barnesSource_ladder_decomposition` through the same lift to produce `hladder`, and the full product
statement `hfull`.

### Thirty-second brick: the atomic theorem, on the Barnes source itself

With the order-one ladder normalized in the field, the atomic theorem applies to the genuine Barnes
source rather than to an abstract laddered element:

```text
differentialIndependent_barnesLadderTranslate :
  translates of the corrected order-one Barnes source through shifts pairwise distinct modulo
  omega_j Z are differentially algebraically independent over C(z);

hypertranscendentalOver_diffTranslateApply_barnesLadderSolutionOne :
  a nonzero constant-coefficient differential-translation operator avoiding the direction j is
  hypertranscendental on it.
```

The two instance blocks the corpus uses for the global meromorphic field -- the punctured-
representation one and the relative-gauge one -- have identical definitions, so the field ladder
proved in the first transfers verbatim into the second.  `#print axioms` clean.

This closes the atomic step of the card at the level of the actual Barnes object.  What is left of
`(A)` is the multi-period ladder: lifting `barnesSource_ladder_decomposition` the same way -- its
right-hand side is the rational correction (already proved rational plus polynomial) minus the
deleted-frame lower source (already proved to be the slice) -- and iterating it to reach `hladder`
and `hfull`.

### Thirty-third brick: rational corrections are discharged automatically

The multi-period ladder differs from the order-one one only in that its correction is a longer
rational expression.  Two lemmas make such a correction cost nothing.

```text
eq_ratfuncToMero_of_hasPuncturedMeromorphicRep_ratio :
  an element represented by p/q on every punctured neighbourhood IS the coordinate-field element p/q;
differentialAlgebraicOver_of_hasPuncturedMeromorphicRep_ratio :
  hence it is differentially algebraic over the coordinate field.
```

So to discharge a ladder correction it is enough to exhibit polynomials `p, q` and check the
pointwise identity off the poles -- no further analysis.  For the multi-period ladder the corpus
already supplies the two pieces of that identity: the correction series is an explicit rational atom
plus a polynomial (fifteenth brick), and the slice series is the deleted-frame lower source minus a
monomial (tenth brick).  Assembling them into one `p/q` and running the lift is what remains for
`hladder` and `hfull`.

### Thirty-fourth brick: the multi-period ladder defect is one rational function

The three pieces the corpus owned separately are now one identity.  Off the poles of both the full
cone and the deleted cone,

```text
barnesSource_ladder_ratio :
  Psi_omega(z + omega_j) - Psi_omega(z) + Psi_(omega^(j))(z)  =  p(z) / (z + omega_j),
```

with `p` the explicit polynomial

```text
p = (correction polynomial) * (X + omega_j) - ((-1)/omega_j)^N X^N,
```

whose correction polynomial collects the ladder coefficient sums and the deleted-frame cone zeta.
The proof composes the ladder decomposition, the correction series (fifteenth brick: an explicit atom
plus a polynomial), the slice identification (tenth brick: the deleted-frame lower source minus a
monomial), and the atom expansion at the single step `Pi.single j 1`, whose cone period is
`omega_j`.  The only non-polynomial contribution is that atom, and it carries the linear denominator.

`#print axioms` clean.  Combined with the thirty-third brick this says: the multi-period ladder
defect, as an element of the meromorphic field, is a rational function, hence differentially
algebraic — which is `hladder` for one step.  Iterating over the remaining directions and taking the
full product gives `hladder` and `hfull` of `(A)` for the Barnes source.

### Thirty-fifth brick: one ladder step, in the field, modulo DA

The lift now runs on the multi-period ladder:

```text
differentialAlgebraicOver_barnesSource_ladder_step :
  sigma_(omega_j) Psi_omega - Psi_omega + Psi_(omega^(j))   is DA over C(z).
```

All three terms have punctured representatives -- the translated source, the source, and the
deleted-frame source -- their combination is the ratio of polynomials of the previous brick, and a
rational punctured representative makes an element differentially algebraic.  Representatives are
now closed under subtraction as well as addition.

This is exactly the card's ladder relation `x_j Psi_N = -Psi_(N-1)` modulo the differentially
algebraic sector, for the Barnes source itself.  `#print axioms` clean.

Iterating it over the directions `k != j` reduces `D_j Psi_N` to the order-one source modulo DA --
where the thirty-first and thirty-second bricks take over -- and the same iteration over all
directions gives `hfull`.  Those two iterations are all that separate the Barnes source from the
statement `(A)` proved in the twenty-seventh brick.

### Thirty-sixth brick: `(A)` needs only the ladder hypothesis

The forward inclusion of `(A)` no longer assumes that the full product lands in the differentially
algebraic sector: that follows from the single ladder hypothesis.  Writing
`prod_j (T_j - 1) = (T_1 - 1) D_1` and applying the ring action,

```text
prod_j (T_j - 1) Psi = sigma_(omega_1)(D_1 Psi) - D_1 Psi,
```

and `D_1 Psi = phi_1 + R` with `R` differentially algebraic, so the right-hand side is
`(sigma phi_1 - phi_1) + (sigma R - R)` -- a rational function plus a difference of differentially
algebraic elements, since translation preserves the sector.

So `(A)` now reads: for rationally independent periods, at least one direction, and a source whose
complementary ladder products reach solutions of the order-one ladder equation modulo DA,

```text
P Psi is DA   <->   prod_j (T_j - 1) | P.
```

`#print axioms` clean.  The only remaining input for the Barnes source is the iteration of the
thirty-fifth brick down to the order-one source.

### Thirty-seventh brick: the source does not see the labelling of the frame

Reindexing the periods along a bijection of index types permutes the cone, and the cone product is a
product over the whole cone, so nothing changes:

```text
conePeriod_comp_equiv, barnesConeFactor_comp_equiv,
barnesConeProduct_comp_equiv, barnesConeAnalytic_comp_equiv,
barnesSourceLogDerivMero_comp_equiv :
  Psi_(omega o e) = Psi_omega  for every equivalence e of index types.
```

The genus exponent is `Fintype.card`, which the bijection preserves, and the exponent vectors
reindex along the induced bijection of the cone.  `#print axioms` clean.

This is the enabling lemma for the iteration: deleting directions one at a time produces nested
subtypes `{i // i != j}`, `{i' // i' != j'}`, ..., and the reindexing invariance identifies each with
a single-level subtype of the original index, so the ladder step of the thirty-fifth brick can be
applied repeatedly without the types drifting apart.

### Thirty-eighth brick: the ladder step between subframes

The ladder step is now stated between the frames carried by a finite set of directions and by that
set with one element erased:

```text
differentialAlgebraicOver_subframe_ladder_step :
  sigma_(omega_k) Psi_S - Psi_S + Psi_(S.erase k)   is DA over C(z),
```

for every direction `k` of a set `S` with at least two directions.  The nested subtype produced by
the one-point deletion is identified with the single-level subtype of the erased set by an explicit
equivalence, and reindexing invariance carries the source across it; a congruence lemma removes the
dependence on the chosen positivity proof.

This is exactly the shape an induction on the number of directions consumes: from `S` down to a
single direction, deleting one at a time, each step paying only a differentially algebraic
correction.  `#print axioms` clean.

### Thirty-ninth brick: peeling one direction off a ladder product

The operator half of the descent:

```text
ladderProd S = prod_(k in S) (T_k - 1);

diffTranslateApply_ladderProd_erase :
  (ladderProd S) y = (ladderProd (S.erase i)) (sigma_(omega_i) y - y)     for i in S;

diffTranslateApply_ladderProd_empty :
  (ladderProd empty) y = y.
```

The product factors through any one of its directions and the action is a ring action, so applying
the product is applying that direction's defect first and the rest afterwards.  The full and
complementary ladder products of `(A)` are the instances `S = univ` and `S = univ.erase j`, on the
nose.  `#print axioms` clean.

With the thirty-eighth brick — the analytic half, `sigma_(omega_k) Psi_S - Psi_S + Psi_(S.erase k)`
differentially algebraic — the two halves of the induction on the number of directions are now both
in place, in matching form.

### Fortieth brick: `(A)` tolerates the sign the descent produces

Iterating the ladder step down to one direction produces `D_j Psi = (-1)^(N-1) Psi_{j}` modulo DA,
and the order-one ladder solution of the thirty-first brick is `phi = -Psi_1 + w`, so the element the
descent hands to `(A)` is `(-1)^N phi`, whose defect is `(-1)^N / (z + omega_j)` -- a simple pole with
residue `+-1`, not `1`.

Rather than generalize the whole atomic chain to arbitrary residues, `(A)` now takes the ladder
hypothesis with a nonzero constant multiple:

```text
hladder j : D_j Psi - c_j phi_j   is DA,     c_j != 0.
```

The reverse inclusion divides it out — constants pass through the operator action
(`diffTranslateApply_algebraMap_complex_mul`, from the corresponding statements for jets and for a
single differential operator) and through the differentially algebraic sector — and the forward
direction multiplies the rational defect by `c_j`.  Nothing else changes.  `#print axioms` clean.

The remaining step is the induction itself, whose two halves are the thirty-eighth and thirty-ninth
bricks, and whose sign is now accepted by `(A)`.

### Forty-first brick: the descent to a single direction

The induction runs.  For every finite set `S` of directions containing `j`,

```text
differentialAlgebraicOver_ladderProd_descent :
  (prod_(k in S.erase j) (T_k - 1)) Psi_S  -  (-1)^(|S|-1) Psi_{j}   is DA over C(z).
```

Base case: one direction, where the product is empty and the two sources coincide.  Step: peel a
direction `k != j` off the product (thirty-ninth brick), replace the defect `sigma_(omega_k) Psi_S -
Psi_S` by `-Psi_(S.erase k)` at the cost of a differentially algebraic term (thirty-eighth brick),
push the remaining product through -- it preserves the sector and is additive, and negation passes
through it -- and apply the inductive hypothesis to `S.erase k`, whose sign is the negative of the
one required, exactly cancelling the peeled factor.

`#print axioms` clean.  At `S = univ` this is the ladder hypothesis of `(A)`, with the constant
`(-1)^(N-1)` that the fortieth brick made the theorem accept.

### Forty-second brick: `(A)` for the Barnes source

The chain closes.

```text
differentialAlgebraicOver_diffTranslateApply_barnesSource_iff :
  for periods in a common half-plane with no nontrivial integral relation,
  P Psi_N is DA over C(z)   <->   prod_j (T_j - 1) | P.
```

This is theorem `(A)` of the card, unconditional, on the genuine Barnes multiple-gamma logarithmic
derivative -- no longer on an abstract laddered source.

The instantiation: the full frame is the subframe carried by all directions (reindexing invariance);
the descent gives `D_j Psi_N = (-1)^(N-1) Psi_{j}` modulo DA; the single-direction source, negated
and corrected by the linear term `w`, is the ladder solution `phi_j` with defect `1/(z + omega_j)`,
so `Psi_{j} = w - phi_j` and the descent reads `D_j Psi_N = (-1)^N phi_j` modulo DA -- the leftover
`(-1)^(N-1) w` is rational, hence absorbed.  The constant `(-1)^N` is the one the theorem was
generalized to accept.  `#print axioms` clean.

Every ingredient of `(A)` -- the source, its ladder, the atomic independence, the operator ring, the
splitting, the divisibility criterion, the descent -- is now Lean, with no analytic or
difference-Galois input assumed.

### Forty-third brick: the structural annihilator, for translations alone

The degree-zero part of `(A)` is now separate and explicit.  A pure translation operator is a
differential-translation operator with constant coefficients, and evaluating the differential
variable at zero retracts that embedding, so divisibility descends:

```text
fullLadder_dvd_constEmbed_iff :
  prod_j (T_j - 1) | (Q with constant coefficients)   <->   prod_j (T_j - 1) | Q  in C[T_1,...,T_N];

differentialAlgebraicOver_transApply_barnesSource_iff :
  Q Psi_N is DA over C(z)   <->   prod_j (T_j - 1) | Q.
```

The descent needs no degree argument: applying `map (eval 0)` to a factorization
`Q^const = prod_j (T_j - 1) * T` returns the factorization of `Q` itself, because the retraction
fixes the ladder product.  `#print axioms` clean.

This is the card's exact structural annihilator theorem `Ann_DA(Psi_N) = (x_1 ... x_N)` on the Barnes
source, and it is the form the fat-point card's normal-crossing interface consumes: for `r = N` the
squarefree Veronese ideal is generated by the single squarefree monomial of degree `N`, so the
annihilator set of the Barnes source is that ideal after the variable change `X_j -> T_j - 1`.

### Forty-fourth brick: the Barnes source is a normal-crossing source

The structural annihilator, read in the ladder variables `x_j = T_j - 1`, is the principal ideal
generated by the product of all the variables; and for `N` variables the squarefree Veronese ideal of
order `N` is that same principal ideal, since the only squarefree monomial of degree `N` is the full
product.  Hence

```text
barnesAnnihilator_eq_veroneseIdeal :
  {Q | Q Psi_N is DA}  =  veroneseIdeal C (Fin N) N     (in the ladder variables);

isNormalCrossingSource_barnesSource :
  IsNormalCrossingSource (Barnes annihilator) N.
```

`#print axioms` clean.  This closes the "Barnes/multiple-sine second realization" gate of the
physical-characteristic fat-point card: the physical package theorem there transports source height,
arc-contact order, powered period-incidence level and the polarizing half-density to the Barnes
source verbatim, and it is a genuinely independent realization -- the first was the multiplicative
translate products, this one is the cone product of Weierstrass factors.

## Stage-3 Lean certificate

Theorem `(A)` holds unconditionally on the genuine Barnes multiple-gamma logarithmic derivative:

```text
differentialAlgebraicOver_diffTranslateApply_barnesSource_iff   -- (A): P Psi_N DA <-> prod_j (T_j - 1) | P
differentialAlgebraicOver_transApply_barnesSource_iff           -- the structural (translation-only) annihilator
barnesAnnihilator_eq_veroneseIdeal                              -- the annihilator is the squarefree Veronese ideal
isNormalCrossingSource_barnesSource                             -- the Barnes source is a normal-crossing source
```

Every declaration named above was resolved against the built Lean tree and `#print axioms`
reported only `propext`, `Classical.choice`, `Quot.sound`.  `scripts/formal_tools.py lint`
reports no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the tree.
