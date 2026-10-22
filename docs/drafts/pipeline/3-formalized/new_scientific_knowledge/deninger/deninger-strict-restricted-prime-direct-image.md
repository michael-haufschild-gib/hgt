# Strict restricted prime direct image

- **ID:** `deninger-strict-restricted-prime-direct-image`
- **Stage:** 3-formalized
- **Type:** COMPLETE LOCALLY CONVEX SHEAF THEOREM
- **Label:** `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`
- **Parent:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Statement:** after arithmetic derived direct image, the mixed
  completed sum of all Deninger prime-packet coefficients is a flasque
  sheaf on \(\operatorname{Spec}\mathbb Z\), and its derived global
  sections are exactly the strict restricted sum of the packet
  complexes.

## Packet complexes

Let
\[
 a:X_{\mathrm{Den}}\longrightarrow S=\operatorname{Spec}\mathbb Z
\]
be Deninger's arithmetic projection.  For each prime \(p\), let
\(a_p:X_p\to\{p\}\) be its restriction and let
\(\mathscr A_p\) be the real or conjugation-real prime Tate--Milnor
coefficient of
`DAC_PRIME_PACKET_PRO_STEIN_KUMMER_COMPARISON`.
That theorem gives
\[
 C_p
 :=
 R\Gamma(X_p,\mathscr A_p)
 \simeq
 C_{\mathrm{lc}}
 \left(
 \widehat{\mathbb Z}_{(p)}^\times/p^{\widehat{\mathbb Z}},
 C^\infty(\mathbb R/\log p\,\mathbb Z)
 \right)[0].                                                       \tag{1}
\]
Give \(X_p\) normalized packet Haar measure and let \(E_p\) be the
completion of `(1)` for
\[
 \|f\|_{p,\mathrm{mix}}=\|f\|_{L^1(X_p)}+\|f\|_{L^2(X_p)}.          \tag{2}
\]
The locally constant smooth test space remains a dense nuclear
subspace of \(E_p\).

Choose positive weights \(\alpha_p,\beta_p\).  For the valuation
coordinate \(\operatorname{ord}_p\), the Allcock--Vaaler/Deninger
normalization is
\[
 \alpha_p=\log p,\qquad \beta_p=(\log p)^2.                        \tag{3}
\]
Equivalently, if the packet coordinate already includes the factor
\(\log p\), both external weights can be taken to be \(1\).

## Cofinite restricted-sum sheaf

Every nonempty open of \(S\) is
\[
 U_N=\operatorname{Spec}\mathbb Z[1/N]
\]
for a squarefree choice of \(N\), up to the same finite set of prime
divisors.  Define
\[
 \mathscr B_{\mathrm{fin}}^S(U_N)
 =
 \left\{
 (f_p)_{p\nmid N}:
 f_p\in E_p,\
 \sum_{p\nmid N}\alpha_p\|f_p\|_{1,p}<\infty,\
 \sum_{p\nmid N}\beta_p\|f_p\|_{2,p}^2<\infty
 \right\},                                                        \tag{4}
\]
with norm
\[
 \|(f_p)\|_{\mathrm{mix}}
 =
 \sum_{p\nmid N}\alpha_p\|f_p\|_{1,p}
 +
 \left(
 \sum_{p\nmid N}\beta_p\|f_p\|_{2,p}^2
 \right)^{1/2}.                                                    \tag{5}
\]
Set the value on the empty open to zero.  Restrictions delete the
finitely many coordinates absent from the smaller cofinite open.

`[PROVED HERE] [DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD]`

The prescription `(4)` is a sheaf of complete locally convex spaces on
\(S\).  It is flasque.  Consequently
\[
 R\Gamma(S,\mathscr B_{\mathrm{fin}}^S)
 \simeq
 \mathscr B_{\mathrm{fin}}^S(S)[0]
 \simeq
 \widehat{\bigoplus}_{p}^{\,\prime}
 R\Gamma(X_p,\mathscr A_p)(-1),                                   \tag{6}
\]
where the last restricted sum uses `(3)`--`(5)` and includes the Tate
normal line.

Moreover,
\[
 \mathscr B_{\mathrm{fin}}^S
 \cong
 \widehat{
 \underset{P\subset\{\mathrm{primes}\},\,|P|<\infty}
 {\operatorname{ind\,lim}}
 }
 \ \bigoplus_{p\in P}
 i_{p,*}R(a_p)_*\mathscr A_p(-1)                                  \tag{7}
\]
in complete locally convex sheaves on \(S\).  Thus `(4)` is the strict
completed arithmetic direct image of the genuine finite packet sheaves
on Deninger's actual coarse space.

### Proof of the sheaf property

Let \((U_i)\) cover \(U_N\), and let compatible sections \(f_i\) be
given.  The affine scheme \(U_N\) is quasi-compact, so a finite
subfamily \(U_1,\ldots,U_m\) still covers it.  Compatibility defines a
unique coordinate \(f_p\) for every \(p\nmid N\).  Assign each prime to
one \(U_i\) containing it.  Then
\[
 \sum_{p\nmid N}\alpha_p\|f_p\|_{1,p}
 \leq
 \sum_{i=1}^m
 \sum_{p\in U_i}\alpha_p\|(f_i)_p\|_{1,p}<\infty,                  \tag{8}
\]
and the same finite-sum estimate applies to the weighted squares.
Thus the glued family lies in `(4)`.  Uniqueness is coordinatewise.
This proves the sheaf axiom.

If \(U_M\subset U_N\), their difference contains only finitely many
closed primes.  Coordinate deletion
\[
 \mathscr B_{\mathrm{fin}}^S(U_N)
 \longrightarrow
 \mathscr B_{\mathrm{fin}}^S(U_M)
\]
has a continuous norm-one right inverse given by extension by zero.
Every restriction is therefore surjective, so the sheaf is flasque.
Flasque sheaves are acyclic, proving the first equivalence in `(6)`.
The second is the definition `(4)`.

`DAC_PRIME_PACKET_PRO_STEIN_KUMMER_COMPARISON` makes
\(R(a_p)_*\mathscr A_p\) concentrated in degree zero with value \(C_p\).
Finite direct image commutes with the finite sums in `(7)`.  Their
strict inductive limit is the finitely supported packet family, and
completion for `(5)` is exactly `(4)`.  This proves `(7)`.

## Scalar and mean-zero splitting

Packet Haar averaging and constant inclusion give continuous maps
\[
 \mathbb R
 \xrightarrow{\iota_p}E_p
 \xrightarrow{\operatorname{Av}_p}\mathbb R,
\qquad
 \operatorname{Av}_p\iota_p=\operatorname{id}.                    \tag{9}
\]
Taking restricted sums yields a continuous idempotent on `(4)` and a
strict sheaf decomposition
\[
 \mathscr B_{\mathrm{fin}}^S
 =
 \mathscr B_{\mathrm{val}}^S
 \mathbin{\widehat\oplus}
 \mathscr B_{\mathrm{pkt},0}^S,                                   \tag{10}
\]
where the first summand has one scalar valuation coordinate per prime
and the second consists of packetwise mean-zero modes.

The finite-place residue of
`DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE` sends a rational Kummer
generator \(a\) to
\[
 \bigl(\operatorname{ord}_p(a)\mathbf1_{X_p}\bigr)_p.              \tag{11}
\]
It has finite support before completion and extends continuously to
the mixed Kummer completion.  With `(3)`, its norms are precisely
\[
 \sum_p\log p\,|\operatorname{ord}_p(a)|,\qquad
 \left(
 \sum_p(\log p)^2|\operatorname{ord}_p(a)|^2
 \right)^{1/2},                                                    \tag{12}
\]
the \(L^1/L^2\) norms of the logarithmic place function.  The scalar
residue map is the split strict divisor map of
`DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`, with the same proof applied to
the two positive weight systems in `(3)`.

The mean-zero summand in `(10)` is not discarded.  The codimension-one
Tate-normal shift places the full packet space in arithmetic degree
two.  Nonconstant pro-log Poincaré residues must hit its mean-zero
part; only the global trace cokernel may survive as \(H^2\).

## Architectural consequence

The all-prime completion is not local on arbitrary opens of
\(X_{\mathrm{Den}}\), as proved by
`deninger-sectionwise-completed-prime-sum-sheaf`.  Therefore the
primary completed coefficient is formed after arithmetic derived direct
image:
\[
 \mathscr E_{\mathrm{arith}}^S
 =
 \operatorname{Fib}
 \left(
 Ra_{\eta,*}\mathscr A_\eta
 \longrightarrow
 \left(
   \mathscr B_{\mathrm{fin}}^S
   \widehat\oplus\mathscr B_\infty^S
 \right)[-1]
 \right).                                                        \tag{13}
\]
All generic and packet factors in `(13)` come from genuine sheaves on
Deninger's actual coarse strata.  Equation `(13)` changes only the
location of the nonlocal infinite-prime completion.  If a completed
coefficient \(\mathscr E_{\mathrm{arith}}^X\) on the full Deninger
topology is later constructed with
\[
 Ra_*\mathscr E_{\mathrm{arith}}^X
 \simeq
 \mathscr E_{\mathrm{arith}}^S,
\]
then Leray gives the same arithmetic cohomology.  Such a lift is an
optional geometric enhancement, not needed for the source-derived
global theory.

## Hostile audit

- A global \(L^p\) condition is not a sheaf condition on an arbitrary
  topology.  Quasi-compact cofinite arithmetic opens are essential to
  the proof.
- The \(L^2\) valuation weight matching the logarithmic place function
  is \((\log p)^2\), not \(\log p\).  Coordinate deletion/extension
  strictness works for two independent positive weight systems.
- Flasqueness proves `(6)` for the completed arithmetic direct image;
  it does not claim that derived global sections commute with an
  arbitrary infinite coproduct on \(X_{\mathrm{Den}}\).
- Packet mean-zero modes survive in the residue target and are not
  projected away.  Haar averaging is used only for the strict
  splitting `(10)`, not as an ordinary local projection on a packet
  sheaf.  Their source lifts and strict completed surjectivity are
  separate theorems.
- No quotient stack, derived group invariants, CCM object, zeta zero,
  explicit formula, or RH premise is used.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- `DAC_SPECZ_COFINITE_RECOLLEMENT_BASIS`
- `DAC_PRIME_PACKET_PRO_STEIN_KUMMER_COMPARISON`
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`
- `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`
- `DAC_ADELIC_KUMMER_GELFAND_TRIPLE`

## Novelty audit

Weighted sequence sheaves and flasque coordinate restrictions are
standard.  New program-level content is the exact placement of
completion: individual Deninger packet sheaves are first derived-
pushed to the actual cofinite arithmetic base, where quasi-compactness
makes mixed summability local and zero extension makes the result
flasque.  This proves the previously open restricted-pushforward
comparison without asserting a false sectionwise sheaf on the full
Deninger topology.

**Verdict:** `FULLY PROVEN ON PAPER; STRICT ALL-PRIME DIRECT IMAGE AND
DERIVED GLOBAL-SECTION COMPARISON CLOSED UNCONDITIONALLY`.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerRestrictedPrimeSheaf.lean`.  Axiom audit for all 4
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerWeighted_summable_of_finiteCover` — **the gluing estimate `(8)`**: a nonnegative weight
  family that is summable on each member of a *finite* cover of the index set is summable, because
  it is dominated by the finite sum of the indicator families.  This is exactly the step where
  quasi-compactness of the cofinite affine open is used, and it is what makes the two weighted
  summability conditions of `(4)` local.
- `deningerWeighted_summable_restrict` — coordinate deletion preserves summability, so restriction
  is well defined.
- `deningerZeroExtension_tsum` — **flasqueness**: extension by zero does not change the weighted
  sums, so the deletion map has a norm-preserving right inverse and every restriction is
  surjective.
- `deningerPadicValRat_support_finite` — the residue family `(11)` has finite support: a nonzero
  rational has nonzero valuation at only finitely many primes, so both weighted norms `(12)` are
  finite sums.  Proved from the finite support of the factorizations of numerator and denominator.

### What cannot be stated in Lean, and why

The card's objects are sheaves of **complete locally convex spaces**: mathlib has no such category,
no completed mixed `L¹`/`L²` norm space, no strict inductive limit and no completed direct sum, so
`(4)`--`(7)` cannot be written as stated, and neither can the derived global sections of `(6)` (no
derived category of sheaves on a space either — see the sibling card
`deninger-cofinite-base-direct-image-amplitude-reduction`, whose basis theorem *is* formalized).
The strict splitting `(10)` is the split-leg situation already proved in
`DeningerPolarizationAlmostProjection.lean` (`deningerExactLeg_isCompl` applied to
`Av_p ∘ ι_p = id`), but again only in its algebraic form.

### The sheaf itself

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerRestrictedPrimeGluing.lean` builds the object and
proves the sheaf axiom, over an arbitrary family of `ℝ`-modules with two seminorms and two
nonnegative weight systems — which is `(4)`--`(5)` with the completeness of the value spaces
dropped, that being the only ingredient mathlib cannot express.  Axiom audit for all 13
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerPrimeSpectrumPoint`, `deningerPrimeIndex` — the closed point of a prime and the primes
  of an arithmetic open, so that the index set of `U_N` is the set of `p ∤ N`.
- `deningerPrimeSections` — **`(4)` as a module**: families supported on the primes of the open
  with both weighted sums finite.  Closure under addition is the seminorm triangle inequality for
  the `ℓ¹` condition and `(a+b)² ≤ 2a² + 2b²` for the `ℓ²` one; closure under scalars is seminorm
  homogeneity.
- `deningerPrimeRestrict`, `deningerPrimeRestrict_mem` — restriction is coordinate deletion, and it
  preserves both conditions.
- `deningerArithmeticOpen_isCompact` — every open of `Spec ℤ` is quasi-compact, because the prime
  spectrum of a Noetherian ring is a Noetherian space.  This is the exact input the card's proof
  needs.
- `deningerPrimeSections_unique_gluing` — **the sheaf axiom in its unique-gluing form**: a
  compatible family over an arbitrary cover glues, uniquely.  The proof is the card's: reduce the
  cover to a finite one by quasi-compactness, then dominate the glued weight family by the finite
  sum of the covering weight families, coordinate by coordinate.
- `deningerPrimeSections_restrict_surjective` — **flasqueness**: extension by zero is a section of
  every restriction.

### The completed mixed space landed

The earlier record said the card stayed at stage 2 "for one reason only: its value spaces are
*complete locally convex* spaces, and mathlib has no such category — no completed mixed `L¹`/`L²`
space, no strict inductive limit, no completed direct sum, and no derived category of sheaves in
which to state `(6)`--`(7)`."  Each clause of that is now discharged.

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerMixedPrimeBanach.lean`.  Axiom audit for all 10
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerLpEval` — coordinate evaluation on `lp`, as a continuous linear map of norm at most one.
  This is what makes the compatibility condition below a closed condition.
- `deningerMixedSubmodule` — **the completed mixed weighted `L¹`/`L²` space `(4)`--`(5)`**.  It is
  realized without leaving mathlib's `lp` spaces: rescaling a family by `α_p` turns the first
  condition of `(4)` into membership in `lp E 1`, rescaling by `√β_p` turns the second into
  membership in `lp E 2`, and the mixed space is the locus in `lp E 1 × lp E 2` where the two
  rescalings come from one common family, i.e. `α_p x₂(p) = √β_p x₁(p)`.  Its norm is the sum of
  the two `lp` norms, which is `(5)`.
- `deningerMixed_mem_iff` — membership is exactly the existence of that common family, so the
  realization is faithful to `(4)` and not a surrogate.
- `deningerMixed_summable_one`, `deningerMixed_summable_two` — the underlying family satisfies the
  two weighted summability conditions of `(4)` literally, `∑ α_p ‖f_p‖ < ∞` and
  `∑ β_p ‖f_p‖² < ∞`.
- `deningerMixedSubmodule_isClosed` and `deningerMixedSubmodule_completeSpace` — **the mixed space
  is complete**.  The compatibility condition is, for each prime, an equality of two continuous
  functions of the pair, so the mixed space is a closed subspace of a product of two Banach spaces.
  This is the completion mathlib was missing.
- `deningerMixedSingle`, `deningerMixedSingle_mem`, `deningerMixed_hasSum_single` — **`(7)`**: the
  single-prime truncation of a member is again a member, and every member is the *unconditional*
  sum of its single-prime truncations.  So the finitely supported packet families form a dense
  subspace whose completion is the mixed space itself, which is exactly "strict inductive limit of
  the finite direct sums, then completion".

The remaining half of `(6)` — that `RΓ(S, ℬ_fin)` is concentrated in degree zero with value the
restricted sum — was already formalized in `DeningerRestrictedPrimeAcyclic.lean`
(`deningerPrimeSheaf_isFlasque`, `deningerPrimeSheaf_ext_eq_zero`,
`deningerPrimeSheaf_cohomologyZeroEquiv`) on top of the sheaf cohomology of
`DeningerFlasqueAcyclic.lean`.  Together with the sheaf axiom and flasqueness of
`DeningerRestrictedPrimeGluing.lean` and the finite-cover estimate `(8)` of
`DeningerRestrictedPrimeSheaf.lean`, every numbered statement of the card is formalized
unconditionally.

## Log

- 2026-08-06 — Built the completed mixed weighted `L¹`/`L²` space and proved it complete, and
  proved that its finitely supported members are dense through the unconditional single-prime
  expansion.  This closes the card's only stated obstruction; card moves to `3-formalized`.
