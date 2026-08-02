# Arithmetic pro-log Kummer divisor resolution

- **ID:** `deninger-arithmetic-pro-log-kummer-divisor-resolution`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Statement:** filtered finite divisorial log structures on
  \(\operatorname{Spec}\mathbb Z\) give the canonical
  generic-to-prime Kummer residue sheaf, and Deninger's generalized
  prime divisors realize its pullback to the rational-Witt space.

## Goal

Construct prime normal orientations without assuming that Deninger's
generalized function \([p]\) is an ordinary analytic function.  The
arithmetic curve already carries the required Cartier data.  Its
filtered divisorial log structure supplies the Kummer boundary, while
Deninger's generalized-divisor theorem identifies the boundary's
support on the rational-Witt character space.

## Finite log stages

Let
\[
 S=\operatorname{Spec}\mathbb Z
\]
and let \(P\) be a finite set of rational primes.  Put
\[
 D_P=\sum_{p\in P}V(p),\qquad
 j_P:S\setminus D_P\hookrightarrow S.
\]
Each \(V(p)\) is an effective Cartier divisor because \(p\) is a
non-zero-divisor in \(\mathbb Z\).  For \(p\ne q\),
\[
 V(p)\cap V(q)=V((p,q))=\varnothing,                              \tag{1}
\]
so \(D_P\) is a disjoint strict-normal-crossings divisor.

Give \(S\) the divisorial log structure
\[
 \mathscr M_P
 =
 \mathscr O_S\cap
 j_{P,*}\mathscr O_{S\setminus D_P}^{\times}
 \subset j_{P,*}\mathscr K_S^\times.                             \tag{2}
\]
Write
\(\overline{\mathscr M}_P
  =\mathscr M_P/\mathscr O_S^\times\).

## Theorem

`[PROVED HERE] [DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION]`

### 1. Finite characteristic monoid

There is a canonical isomorphism
\[
 \overline{\mathscr M}_P
 \cong
 \bigoplus_{p\in P}i_{p,*}\mathbb N,                              \tag{3}
\]
and after groupification a canonical short exact sequence
\[
 0\longrightarrow\mathscr O_S^\times
 \longrightarrow\mathscr M_P^{\mathrm{gp}}
 \xrightarrow{(\operatorname{ord}_p)_{p\in P}}
 \bigoplus_{p\in P}i_{p,*}\mathbb Z
 \longrightarrow0.                                               \tag{4}
\]

### 2. Cofinite opens and the pro-log limit

For
\[
 U_N=\operatorname{Spec}\mathbb Z[1/N],\qquad
 S_N=\{p:p\mid N\},
\]
let \(P\) range over finite subsets of primes not in \(S_N\).  Then
filtered colimit of global sections of `(4)` is the exact divisor
sequence
\[
 0\longrightarrow
 \mathbb Z[1/N]^\times
 \longrightarrow
 \mathbb Q^\times
 \xrightarrow{(\operatorname{ord}_p)_{p\nmid N}}
 \bigoplus_{p\nmid N}\mathbb Z[p]
 \longrightarrow0.                                               \tag{5}
\]
Modulo \(\{\pm1\}\), `(5)` is canonically the coordinate sequence
\[
 0\longrightarrow
 \bigoplus_{p\mid N}\mathbb Z[p]
 \longrightarrow
 \bigoplus_p\mathbb Z[p]
 \longrightarrow
 \bigoplus_{p\nmid N}\mathbb Z[p]
 \longrightarrow0.                                               \tag{6}
\]
Tensoring with \(\mathbb R\) gives the algebraic row in
`DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`.

### 3. Pullback to Deninger's space

Let
\[
 a:X_{\mathrm{Den}}\longrightarrow S
\]
be Deninger's arithmetic projection.  Inverse image of abelian
sheaves is exact, so `(4)` pulls back to
\[
 0\longrightarrow a^{-1}\mathscr O_S^\times
 \longrightarrow a^{-1}\mathscr M_P^{\mathrm{gp}}
 \longrightarrow
 \bigoplus_{p\in P}a^{-1}i_{p,*}\mathbb Z
 \longrightarrow0.                                               \tag{7}
\]
Moreover
\[
 a^{-1}i_{p,*}\mathbb Z
 \cong
 \iota_{p,*}\underline{\mathbb Z}_{a^{-1}V(p)},                   \tag{8}
\]
where \(\iota_p:a^{-1}V(p)\hookrightarrow X_{\mathrm{Den}}\).
The supports in `(8)` are pairwise disjoint.

Deninger's generalized-function map satisfies
\[
 \operatorname{div}[\beta]
 =
 \operatorname{pr}^{-1}(\operatorname{div}\beta).                 \tag{9}
\]
For \(\beta=p\), `(9)` identifies the generalized divisor of
\([p]\), as a set, with the support of the \(p\)-summand of `(7)`.
Thus `(7)` is the canonical generalized-log Cartier/Kummer refinement
of the same prime packets.  Its multiplicity-one generator comes from
the Cartier divisor \(V(p)\) on the arithmetic base, not from a
multiplicity assertion in Deninger's Proposition 11.7.  It does not
assert that \([p]\) is an ordinary analytic section.

### 4. Rational powers and Tate normalization

After Kummer groupification,
\[
 \mathscr M_{P,\mathbb Q}^{\mathrm{gp}}
 =
 \mathscr M_P^{\mathrm{gp}}\otimes_{\mathbb Z}\mathbb Q,
\]
the rational-power correspondence acts on the characteristic group by
\[
 F_q^*(\operatorname{ord}_p)
 =
 q\,\operatorname{ord}_p.                                       \tag{10}
\]
Deninger's identity \(F_q^*[\beta]=[\beta]^q\) gives the same
scaling on generalized divisors.  Tensoring the residue target with
the Tate line \(\mathbb R(1)\), on which \(q\) acts by \(q^{-1}\),
makes the Kummer boundary invariant:
\[
 q^{-1}\cdot q\,\operatorname{ord}_p
 =
 \operatorname{ord}_p.                                          \tag{11}
\]

## Proof

At the generic point and at every closed point \(V(r)\) with
\(r\notin P\), `(2)` is the trivial log structure.  At \(V(p)\) with
\(p\in P\), the local ring is the discrete valuation ring
\(\mathbb Z_{(p)}\), and every element of `(2)` has a unique
decomposition
\[
 u p^n,\qquad
 u\in\mathbb Z_{(p)}^\times,\quad n\in\mathbb N.                  \tag{12}
\]
Hence the characteristic stalk is \(\mathbb N\) at \(p\) and zero at
every other point.  Disjointness `(1)` proves `(3)`.  Groupifying
`(12)` gives \(\mathbb Z\), with quotient map
\(\operatorname{ord}_p\).  Exactness can be checked on stalks, proving
`(4)`.

On \(U_N\), a rational number lies in the groupification of a finite
stage precisely when its valuations vanish outside
\(S_N\cup P\).  Taking the filtered union over finite
\(P\subseteq\{p:p\nmid N\}\) gives every nonzero rational number.
The kernel of the surviving-prime valuation map is
\[
 \mathbb Z[1/N]^\times
 =
 \left\{
  \pm\prod_{p\mid N}p^{n_p}:n_p\in\mathbb Z
 \right\}.                                                       \tag{13}
\]
Unique factorization makes the valuation map surjective and proves
`(5)`--`(6)`.

For a continuous map, inverse image of sheaves of abelian groups is
left adjoint to direct image and is left exact; hence it is exact.
This proves `(7)`.  Stalks of inverse image identify the last term
with extension by zero from \(a^{-1}V(p)\), proving `(8)`.
Deninger's Proposition 11.7 is exactly the set equality `(9)`, so its
specialization to \(p\) identifies the support in `(7)`.  The
multiplicity-one generator was already fixed by
\(\operatorname{ord}_p(p)=1\) on the arithmetic base.  Finally
exponentiation multiplies valuations, which proves `(10)`; `(11)` is
the definition of the Tate normalization.

## Consequence

Finite-prime normal orientations and their direct-sum Kummer residues
are no longer an open part of the arithmetic-cohomology construction.
The remaining geometric gate is a comparison between the
Tate--Milnor analytic coefficient on Deninger's coarse suspension and
the pulled-back pro-log Cousin resolution `(7)`.

Equivalently, the missing statement is not “\([p]\) is an analytic
Cartier function.”  It is:
\[
 \boxed{\text{the source analytic coefficient satisfies purity for
 the canonical pulled-back generalized log divisor.}}
\]

## Hostile audit

- The infinite union of closed primes is not installed as one
  finite-type divisor.  All constructions occur at finite \(P\), then
  pass through a filtered colimit.
- A global chart \(\mathbb N^P\to\mathbb Z\), \(e_p\mapsto p\), does
  not create fake prime intersections: `(1)` and the stalk
  calculation show characteristic rank at most one.
- Equation `(9)` gives support and valuation multiplicity, not an
  ordinary analytic local equation.
- Pullback exactness gives the log divisor sequence, not acyclicity of
  Deninger's coarse invariant sheaf.
- No group-action bar complex, quotient-stack cohomology, zeta zero,
  RH premise, or numerical computation occurs.

## Gates

- [x] 0 → 1 in-progress: finite-stage pro-log statement isolated
- [x] 1 → 2 fully-proven: stalk, colimit, pullback, and power proof
- [x] finite-support valuation resolution encoded in Lean
- [x] Tate-normalized power compatibility encoded in Lean
- [ ] 2 → 3 formalized: blocked only by the log-geometric layer, which
  mathlib cannot yet express (see Lean status)
- [ ] 3 → 4 publication-ready: integrate with source analytic purity

## References

- Kazuya Kato, *Logarithmic structures of Fontaine--Illusie*:
  https://www.math.brown.edu/dabramov/LOGGEOM/Kato-log.pdf
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Proposition 11.7 and §§11--12:
  https://arxiv.org/abs/1807.06400
- Stacks Project, normal crossings divisors:
  https://stacks.math.columbia.edu/tag/0BSF

## Log

- 2026-07-27 — replaced unsupported ordinary analytic Cartier
  conjecture for \([p]\) by finite divisorial log stages and their
  exact generalized-prime Kummer resolution.
- 2026-08-02 — §4 formalized unconditionally in
  `DeningerTateNormalizedPowerCompatibility.lean`: integral power
  compatibility of divisors, the rational power correspondence with the
  proof that it really is exponentiation, equation `(10)`, equation
  `(11)`, and the rigidity theorem that weight `-1` is the only twist
  producing invariance.  Both named sub-items of the `2 → 3` gate are
  now encoded; only the log-geometric layer remains.

## Lean status

### The arithmetic content landed

`formal/GaloisForLFunctions/RHTower/DeningerRationalDivisorSequence.lean`, on top of the `S`-unit
machinery in `DeningerSUnitEndpointPage.lean` and the finite-support lemma in
`DeningerRestrictedPrimeSheaf.lean`.  Axiom audit for all 11 declarations:
`propext, Classical.choice, Quot.sound`.

- `deningerValuationSupport_finite`, `deningerDivisor`, `deningerDivisor_apply` — the divisor of a
  rational unit as a finitely supported family of integers, which is what makes `(4)`--`(5)` land
  in a direct sum.
- `deningerDivisor_mul` — taking divisors is additive, i.e. the groupified characteristic map of
  `(4)` is a homomorphism.
- `deningerDivisor_eq_zero_iff` — **the kernel is trivial on positives**: a positive rational whose
  valuations all vanish is `1`.  Modulo `{±1}` this is the exactness of `(5)` at `ℚ^×`.
- `deningerDivisorProduct`, `deningerDivisor_divisorProduct`, `deningerDivisorProduct_pos`,
  `deningerDivisor_surjective` — **unique factorization in divisor form**: every finitely supported
  family is the divisor of the corresponding product of prime powers, so the valuation map of `(5)`
  is onto and the positive rationals are the free abelian group on the primes.  This is the
  content the card derives `(5)`--`(6)` from, and the multiplicity-one normalization
  `ord_p(p) = 1` is `deningerPadicValRat_primeUnit`.
- `deningerDivisor_vanishing_off_iff`, `deningerDivisor_surjective_off` — **the cofinite sequence
  `(5)`--`(6)`**: a positive unit is an `S`-unit exactly when its divisor is supported in `S`, so
  the kernel of the surviving-prime valuations is `ℤ[1/N]^×/{±1}`, and every family supported off
  `S` is realized.
- The identification of the `S`-units with the free abelian group on `S`, which is `(6)` in
  coordinates, is `deningerSUnitsEquiv` in `DeningerSUnitEndpointPage.lean`.

### Rational powers and the Tate normalization landed

`formal/GaloisForLFunctions/RHTower/DeningerTateNormalizedPowerCompatibility.lean` encodes §4,
equations `(10)`--`(11)`.  Axiom audit for all 23 declarations:
`propext, Classical.choice, Quot.sound`.

- `deningerDivisor_one`, `deningerDivisor_inv`, `deningerDivisor_pow`, `deningerDivisor_zpow` —
  **exponentiation multiplies divisors**, `div(u^n) = n · div(u)` for every integer `n`.  This is
  the characteristic-group form of Deninger's `F_q^*[β] = [β]^q`.
- `DeningerRationalCharacter`, `deningerRationalDivisor`, `deningerOrd` — the Kummer
  groupification `M_P^{gp} ⊗ ℚ` in prime coordinates, the Kummer map into it, and the residue
  functional `ord_p`.  `deningerOrd_rationalDivisor_primeUnit` is the multiplicity-one
  normalization `ord_p(p) = 1` in that language.
- `deningerRationalPower`, `deningerRationalPower_mul`, `deningerRationalPower_one` — the
  rational power correspondence `F_q` as an action on the characteristic group, and
  `deningerRationalPower_zpow_kummer` proves this scaling *is* exponentiation: on an integral
  exponent it carries the Kummer class of `u` to that of `u^n`, so the action is not an arbitrary
  normalization.
- `deningerOrd_rationalPower`, `deningerOrd_comp_rationalPower` — **equation `(10)`**:
  `F_q^*(ord_p) = q · ord_p`.
- `deningerTateLineAction`, `deningerTateLineAction_mul`, `deningerTateResidue`,
  `deningerTateResidue_invariant` — **equation `(11)`**: the Tate line is the line on which `F_q`
  acts by `q^{-1}`, and the residue valued in the Tate-twisted target is invariant under the whole
  correspondence.
- `deningerTateWeight_unique` — **weight rigidity**: a scalar twist `χ` of the residue target makes
  the Kummer boundary invariant for every nonzero exponent *exactly when* `χ(q) = q^{-1}`.  So the
  Tate normalization is forced, not chosen; multiplicity one at the prime supplies the test vector.

### What cannot be stated in Lean, and why

The log-geometric layer: log structures on `Spec ℤ` and their characteristic monoids `(2)`--`(3)`,
sheaf inverse image and the pullback `(7)`--`(8)` along Deninger's projection, and Proposition 11.7
of Deninger's paper used for `(9)`.  mathlib has no logarithmic geometry and no inverse-image
functor for abelian sheaves along a map of arbitrary spaces in usable form.  What is formalized is
the arithmetic core those steps are built on — the divisor sequence and its cofinite splitting —
so the card stays at stage 2.
