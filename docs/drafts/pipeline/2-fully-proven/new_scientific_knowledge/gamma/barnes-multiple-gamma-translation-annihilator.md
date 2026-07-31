# Barnes Multiple Gamma Translation Annihilator

- **ID:** `barnes-multiple-gamma-translation-annihilator`
- **Stage:** 2-fully-proven / needs independent audit
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
`standardSimplexNormalizedCoproduct_exactAt_succ`.  The special-function identification `(A)` and
the assembly of those blocks into the concrete localized Barnes complex remain paper theorems;
neither is inserted into Lean as an analytic axiom.

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
