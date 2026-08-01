# Arithmetic endpoints and relative middle reduction

- **ID:** `deninger-arithmetic-endpoint-relative-middle-reduction`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) · LEAN 4 THEOREM
- **Label:** `DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION`
- **Parent:** `deninger-true-to-approximate-derived-coefficient`
- **Statement:** the rational Milnor--Arakelov core supplies exactly
  Deninger's degrees zero and two; every nontrivial middle class lies
  in the canonical relative analytic cone.
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerEndpointRelativeMiddleReduction` (clauses 1 and 3),
  `GaloisForLFunctions.RHTower.DeningerRationalPrimeFactorization` (clause 2)

## Algebraic endpoint complex

For a number field \(K\), put
\[
 P_K=(K^\times/\mu_K)\otimes_{\mathbb Z}\mathbb R
\]
and let
\[
 D_K=\operatorname{Div}_{\mathrm{Ar}}(K)_{\mathbb R}
\]
be the real Arakelov divisor space, with principal-divisor map
\(\operatorname{pr}:P_K\to D_K\).  Define
\[
 C_{\mathrm{end}}(K)
 =
 \mathbb R[0]\oplus
 \left[
   P_K\xrightarrow{\operatorname{pr}}D_K
 \right]_{[1,2]}.                                                   \tag{1}
\]

`DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT` proves the exact sequence
\[
 0\longrightarrow P_K
 \xrightarrow{\operatorname{pr}}D_K
 \xrightarrow{\deg}\mathbb R(-1)
 \longrightarrow0.                                                 \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION]`

1. The cohomology of `(1)` is
   \[
   H^i(C_{\mathrm{end}}(K))
   =
   \begin{cases}
     \mathbb R,&i=0,\\
     0,&i=1,\\
     \mathbb R(-1),&i=2,\\
     0,&\text{otherwise}.
   \end{cases}                                                       \tag{3}
   \]
2. For \(K=\mathbb Q\), `(1)` is the real realization of the
   rational Milnor generic/finite localization core:
   degree one is
   \((\mathbb Q^\times/\{\pm1\})\otimes\mathbb R\), and its finite
   residue coordinates are the valuations
   \(\operatorname{ord}_p\); the real coordinate is forced by product
   formula.
3. Let \(C_{\mathrm{Den}}\) be any three-term arithmetic cohomology
   complex and suppose there is a flow-equivariant map
   \[
     \iota:C_{\mathrm{end}}(K)\longrightarrow C_{\mathrm{Den}}       \tag{4}
   \]
   inducing the prescribed isomorphisms on \(H^0\) and \(H^2\).
   For
   \[
     C_{\mathrm{mid}}
       :=\operatorname{Cone}(\iota),                                \tag{5}
   \]
   one has
   \[
     H^i(C_{\mathrm{mid}})
     =
     \begin{cases}
       H^1(C_{\mathrm{Den}}),&i=1,\\
       0,&i\ne1.
     \end{cases}                                                     \tag{6}
   \]
   Thus the spectral middle cohomology is canonically a relative
   analytic defect after removing the algebraic endpoints.

## Proof

Equation `(2)` says that the degree-one differential of `(1)` is
injective and has cokernel \(\mathbb R(-1)\).  The direct degree-zero
summand has zero differential.  This proves `(3)`.

For \(K=\mathbb Q\), unique factorization identifies
\[
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \cong\bigoplus_p\mathbb R[p].
\]
Its coordinates are precisely the Milnor \(K_1\) residues.  The
archimedean component and degree map are the product-formula completion
in `(2)`, proving clause 2.

Apply the long exact cohomology sequence to the triangle
\[
 C_{\mathrm{end}}
 \xrightarrow{\iota}C_{\mathrm{Den}}
 \longrightarrow C_{\mathrm{mid}}
 \longrightarrow C_{\mathrm{end}}[1].
\]
The endpoint maps are isomorphisms, both complexes vanish outside
degrees \(0,1,2\), and `\(H^1(C_{\mathrm{end}})=0\)`.  Exactness gives
`(6)`.

## Structural consequence

The theory has a forced two-layer form:
\[
 \boxed{
 C_{\mathrm{Den}}
 \text{ is an extension of }
 C_{\mathrm{end}}
 \text{ by }H^1_{\mathrm{Den}}[-1].
 }
\]
Milnor/Steinberg and Arakelov data determine the endpoints.  They
cannot by themselves create the nontrivial zero spectrum.  The latter
must be constructed as the relative smooth/leafwise part of
\(\mathscr E_{\mathrm{Den}}\).  Coarse/stack and Frobenius-coherence
defects may map into this relative object but are not its definition.

## Formalized statement

All declarations live in the `RHTower` namespace, in
`GaloisForLFunctions/RHTower/DeningerEndpointRelativeMiddleReduction.lean`.

**Clause 1, equation `(3)`.**  The two-term part of `(1)` sits in degrees one and two, so its
cohomology there is the kernel and the cokernel of the principal-divisor map:

- `deningerEndpointH1_eq_bot` : `ker pr = ⊥`, i.e. `H¹ = 0`, from injectivity of `pr` in `(2)`;
- `deningerEndpointH2Equiv` : `(D ⧸ range pr) ≃ₗ[ℝ] ℝ`, i.e. `H² = ℝ(-1)`, from exactness of
  `(2)` together with surjectivity of `deg`;
- `deningerEndpointH2Equiv_mk` : the class of a divisor is its Arakelov degree.

`H⁰ = ℝ` is the degree-zero summand `ℝ[0]` of `(1)`, whose differentials are zero by
construction, so it needs no separate proof.

**Clause 3, equation `(6)`.**  `DeningerConeLES φ ψ δ` is the long exact cohomology sequence of
the cone triangle, with `A` the cohomology of `C_end`, `B` that of `C_Den` and `M` that of the
cone.  Under the card's hypotheses — `H¹(C_end) = 0`, `φ⁰` and `φ²` bijective, and both `A` and
`B` vanishing outside degrees `0, 1, 2` —

- `deningerRelativeMiddleEquiv` : `B 1 ≃ₗ[ℝ] M 1`, the degree-one half of `(6)`;
- `deningerRelativeMiddle_eq_zero` and `deningerRelativeMiddle_subsingleton` : `M i = 0` for
  every `i ≠ 1`, the vanishing half of `(6)`.

The supporting steps are separate lemmas: `deningerCone_eq_zero_of_surjective`,
`deningerCone_eq_zero_of_injective`, `deningerCone_eq_zero_of_neighbours`,
`deningerCone_middle_injective`, `deningerCone_middle_surjective`.  Note the degree `-1` case is
not covered by the naive "both neighbours vanish" argument and needs injectivity of `φ⁰`; the
Lean proof does that case separately.

**Clause 2, the rational case.**  `deningerRatExp q : ℕ →₀ ℤ` is the prime-exponent vector of a
rational number, built from the factorizations of numerator and denominator.  In
`GaloisForLFunctions/RHTower/DeningerRationalPrimeFactorization.lean`:

- `deningerRatExp_apply_of_prime` : at a prime the coordinate *is* the residue,
  `deningerRatExp q p = ord_p q = padicValRat p q`;
- `deningerRatExp_apply_of_not_prime`, `deningerRatExp_support_prime` : the vector is supported
  on primes;
- `deningerRatExp_mul`, `deningerRatExp_inv`, `deningerRatExp_pow`, `deningerRatExp_zpow`,
  `deningerRatExp_prod` : additivity on nonzero rationals;
- `deningerRatExp_neg`, `deningerRatExp_abs` : the vector does not see the sign, so it factors
  through `ℚ^× / {±1}`;
- `deningerRatExp_eq_zero_iff`, `deningerRatExp_injOn_pos` : injectivity on positives, from
  unique factorization (`Nat.factorization_inj` plus coprimality of numerator and denominator);
- `deningerRatExp_surjective_on_primes` : every prime-supported vector is realized, by the
  explicit product `∏ p ^ f p`;
- `deningerRatExp_existsUnique` : the two together — the positive rationals are free abelian on
  the primes with coordinates `ord_p`, which is exactly the unique-factorization identification
  the card's clause 2 invokes;
- `deningerRatExpTensorReal` : `(ℕ →₀ ℤ) ⊗[ℤ] ℝ ≃ₗ (ℕ →₀ ℝ)`, the passage from the free abelian
  group to the real coordinate space `⨁_p ℝ`.

### What is formalized and what is not

Formalized unconditionally: clauses 1, 2 and 3.

The long exact sequence of the cone triangle is a hypothesis on the given data, exactly as in the
card's own proof, which applies it as a standard fact rather than proving it.  Mathlib does have
the machinery to construct it (`homologyFunctor` on the homotopy category is `IsHomological`);
that construction is not carried out here.

### Verification

- Direct commands:
  `lake env lean GaloisForLFunctions/RHTower/DeningerEndpointRelativeMiddleReduction.lean` and
  `lake env lean GaloisForLFunctions/RHTower/DeningerRationalPrimeFactorization.lean`
- Result: passed with no errors and no warnings.
- Scratch `#print axioms` on all 12 + 18 declarations of the two modules: only the Lean/mathlib
  standard `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Both imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] endpoint complex constructed
- [x] endpoint cohomology computed
- [x] relative middle isolation proved
- [x] Lean formalization of the abstract relative reduction
  (`deningerRelativeMiddleEquiv`, `deningerRelativeMiddle_eq_zero`)
- [x] Lean formalization of the endpoint cohomology `(3)`
- [x] Lean formalization of clause 2: the free abelian structure of `ℚ^×/{±1}` on the primes
  (`deningerRatExp_existsUnique`)
- [ ] construct the sheaf-level endpoint map `(4)`
- [ ] identify `(5)` with reduced arithmetic leafwise cohomology
- [ ] construct positive Hodge form and source trace on `(5)`

## References

- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`
- `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`
- `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`
- Christopher Deninger, *Some analogies between number theory and
  dynamical systems on foliated spaces*:
  https://emis.de/ft/10155

## Log

- 2026-07-26 — Isolated the unique canonical location of Deninger's
  spectral \(H^1\) after constructing the rational generic coefficient
  and real endpoint.
- 2026-08-01 — Formalized clauses 1 and 3 unconditionally in Lean 4.  Clause 2 needs the free
  abelian structure of the positive rationals on the primes, which mathlib does not have.
- 2026-08-01 — Built the missing infrastructure and formalized clause 2: the positive rationals
  are free abelian on the primes with coordinates `ord_p`.  All three clauses are now
  unconditional in Lean 4.
