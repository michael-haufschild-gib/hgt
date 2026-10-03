# Self-adjoint Dyson word reversal, twisted reflection realization, and joint-selection no-go

- **ID:** ULF-CRSM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ULF-SRSM-1 + ULF-CRSM-1
- **Statement:** The self-adjoint Dyson source already generates an exact schedule-reversing
  anti-involution: every word coefficient is sent to the adjoint coefficient of the reversed word.
  Functional-equation relabelling composes with it to a twisted anti-involution, and both fixed
  loci carry the reflection fusion law. However the full source exponential is fixed by both
  reversals, so their joint fixed tangent contains the nonzero generator; these two symmetries
  cannot select neutrality.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [SOURCE-GENERATED]
  [WORD REVERSAL] [FIRST CRSM REALIZATION] [EXACT FUSION]
  [JOINT-SELECTION COUNTERMODEL] [NOT RH] [LEAN-PROVED: (DSR.1)–(DSR.22), certificate below]`

## 1. Setup

Let \(H\) be a finite-dimensional complex Hilbert space, let \(A\) be a finite alphabet, and let

\[
 L=L^*,
 \qquad
 K_a=K_a^*\quad(a\in A).
 \tag{DSR.1}
\]

Let \(A^*\) be the free monoid of words and let \(\operatorname{rev}\) reverse word order. Work in
the Banach algebra

\[
 \mathfrak B=\operatorname{End}(H)\widehat\otimes\ell^1(A^*)
 \tag{DSR.2}
\]

with concatenation product. Put

\[
 B=L\otimes\delta_\varnothing
   +\sum_{a\in A}K_a\otimes\delta_a,
 \qquad
 F_t=e^{-tB}=\sum_{w\in A^*}U_w(t)\otimes\delta_w.
 \tag{DSR.3}
\]

These \(U_w\) are exactly the Dyson coefficients from ULF-SRSM-1.

Define the conjugate-linear word adjoint by

\[
 (T\otimes\delta_w)^*=T^*\otimes\delta_{\operatorname{rev}(w)}.
 \tag{DSR.4}
\]

It extends continuously to \(\mathfrak B\).

## 2. Exact source-native word reversal

### Theorem 2.1 -- Dyson adjoint reversal

The map `(DSR.4)` is an isometric conjugate-linear anti-involution:

\[
 (XY)^*=Y^*X^*,
 \qquad
 (X^*)^*=X.
 \tag{DSR.5}
\]

The source generator and its exponential are fixed:

\[
 B^*=B,
 \qquad
 F_t^*=F_t.
 \tag{DSR.6}
\]

Consequently every word response obeys the exact schedule-reversal law

\[
 \boxed{U_w(t)^*=U_{\operatorname{rev}(w)}(t).}
 \tag{DSR.7}
\]

### Proof

On elementary tensors,

\[
 \begin{aligned}
 ((T\otimes\delta_u)(R\otimes\delta_v))^*
 &=(TR)^*\otimes\delta_{\operatorname{rev}(uv)}\\
 &=R^*T^*\otimes\delta_{\operatorname{rev}(v)\operatorname{rev}(u)},
 \end{aligned}
\]

which is `(DSR.5)`. Word reversal preserves the \(\ell^1\)-norm and operator adjoint preserves
the operator norm, so the map extends continuously.

Every letter is fixed by word reversal, and `(DSR.1)` therefore gives \(B^*=B\). Since adjoint is
continuous and reverses each power without changing it,

\[
 (e^{-tB})^*=e^{-tB^*}=e^{-tB}.
\]

Comparing the coefficient of \(w\) on both sides gives `(DSR.7)`. QED.

This closes the schedule-reversal operation that letterwise functional covariance could not
provide. No path-signature or commutativity assumption is used.

## 3. Functional relabelling and the twisted anti-involution

Assume now that \(J\) is a unitary involution and \(\sigma:A\to A\) is an involutive permutation
such that

\[
 JLJ^*=L,
 \qquad
 JK_aJ^*=K_{\sigma(a)}.
 \tag{DSR.8}
\]

Extend \(\sigma\) letterwise to words. Define the algebra automorphism

\[
 \mathcal C(T\otimes\delta_w)
 =JTJ^*\otimes\delta_{\sigma(w)}.
 \tag{DSR.9}
\]

and the anti-involution

\[
 \rho=\mathcal C\circ *.
 \tag{DSR.10}
\]

### Theorem 3.1 -- twisted functional-equation reversal

The maps \(\mathcal C\) and `*` commute, \(\mathcal C^2=\rho^2=\operatorname{id}\), and

\[
 \mathcal C(B)=B,
 \qquad
 \rho(B)=B,
 \qquad
 \mathcal C(F_t)=F_t,
 \qquad
 \rho(F_t)=F_t.
 \tag{DSR.11}
\]

On response coefficients,

\[
 \boxed{J U_w(t)J^*=U_{\sigma(w)}(t),}
 \tag{DSR.12}
\]

\[
 \boxed{J U_w(t)^*J^*
       =U_{\sigma(\operatorname{rev}(w))}(t).}
 \tag{DSR.13}
\]

Thus the source supplies two distinct operations:

- order-preserving functional covariance \(\mathcal C\);
- order-reversing twisted adjoint \(\rho\).

### Proof

Conjugation by \(J\) commutes with operator adjoint, while an involutive letter permutation
commutes with word reversal. Hence \(\mathcal C*=*\mathcal C\) and the involution claims follow.
Equation `(DSR.8)` and reindexing the finite letter sum give \(\mathcal C(B)=B\). Combine with
\(B^*=B\) to obtain all of `(DSR.11)`. Coefficient comparison gives `(DSR.12)` and
`(DSR.13)`. QED.

## 4. Reflection-space realization without a Hopf hypothesis

Let \(\mathfrak B^\times\) be the unit group. For either anti-involution
\(\alpha\in\{*,\rho\}\), put

\[
 Q_\alpha=\{X\in\mathfrak B^\times:\alpha(X)=X\}.
 \tag{DSR.14}
\]

### Theorem 4.1 -- fixed Dyson units carry native reflection fusion

For \(X,Y\in Q_\alpha\),

\[
 X\triangleright Y=XY^{-1}X
 \tag{DSR.15}
\]

lies in \(Q_\alpha\), and the reflection identities

\[
 X\triangleright X=X,
 \qquad
 X\triangleright(X\triangleright Y)=Y,
 \tag{DSR.16}
\]

\[
 X\triangleright(Y\triangleright Z)
 =(X\triangleright Y)\triangleright(X\triangleright Z)
 \tag{DSR.17}
\]

hold. Ordinary formation satisfies

\[
 \alpha(XY)=YX,
 \qquad
 XY\in Q_\alpha\Longleftrightarrow XY=YX.
 \tag{DSR.18}
\]

In particular every \(F_t\) belongs to both \(Q_*\) and \(Q_\rho\).

### Proof

Every algebra anti-involution restricts to a group anti-involution on units. The proof of
ULF-CRSM-1, Theorem 2.1, applies verbatim. Membership of \(F_t\) follows from `(DSR.11)`. QED.

This is a literal realization of Constitutive Reflection-Space Mechanics on the already-derived
source response algebra. It does not require the operator coefficients to be group-like in a tensor
Hopf algebra.

## 5. Filtered logarithm and first fusion escape

The degree-zero term of \(F_t\) is \(S_t=e^{-tL}\), not the identity. Since \(S_t\) is invertible,
define the interaction-normalized response

\[
 Z_t=(S_t^{-1}\otimes\delta_\varnothing)F_t.
 \tag{DSR.19}
\]

Then \(Z_t\in1+\mathfrak B_{\ge1}\), so its word-filtration logarithm converges. This normalization
does not automatically preserve `*`, because \(S_t^{-1}\) need not commute with every response
coefficient. The correct fixed unit for Theorem 4.1 is therefore the unnormalized \(F_t\), unless a
separate interaction-picture anti-involution is constructed.

For any two fixed units \(X=e^A\), \(Y=e^C\) in a complete filtered subalgebra where logarithms are
defined, their ordinary product leaves the fixed locus first through

\[
 \frac12[A,C]
 \tag{DSR.20}
\]

modulo filtration degree three. This is ULF-CRSM-1, Theorem 6.1. Applied to two different
self-adjoint source generators, it predicts the first order-sensitive formed response directly
from their commutator.

## 6. Exact joint-selection no-go

The two source-native anti-involutions do not yet select the identity.

### Theorem 6.1 -- current adjoint and functional reversal share a nonzero fixed generator

If \(B\ne0\), then

\[
 B^*=B,
 \qquad
 \rho(B)=B,
 \tag{DSR.21}
\]

and for every \(t\ne0\),

\[
 F_t=e^{-tB}\ne1
 \tag{DSR.22}
\]

while \(F_t\) is fixed by both anti-involutions. Thus the common fixed tangent of `*` and \(\rho\)
contains the entire source line \(\mathbb RB\), and the two-reversal joint Gramian has nontrivial
kernel on the source response algebra.

### Proof

Equation `(DSR.21)` is `(DSR.6)` and `(DSR.11)`. In a finite-dimensional coefficient algebra,
\(e^{-tB}=1\) for all sufficiently small nonzero real \(t\) would force \(B=0\) by differentiation
at zero. More directly, the degree-zero coefficient is \(e^{-tL}\ne I\) when \(L>0\) and \(t\ne0\).
Fixedness is `(DSR.11)`. QED.

### Corollary 6.2

Functional covariance plus Hilbert adjoint supplies the missing reflection-space *kinematics* but
not neutral selection. Any successful source family must include an additional reversal whose
defect is nonzero on the physical transverse log-response, or must quotient out the common base
generator and prove joint properness on the resulting transverse module.

## 7. Recovery remains information-neutral

Forming a probability packet with a common recovery kernel after applying `(DSR.12)` or
`(DSR.13)` preserves KL and Jeffreys divergence exactly by
`HTGeometry.ConstitutiveFunctionalEquationPacketLift`. Therefore recovery neither destroys the
reflection-space structure nor removes the common fixed generator from Theorem 6.1.

## 8. What was proved and what remains open

### Closed

1. exact source-native reversal of every ordered Dyson word;
2. exact composition with functional relabelling;
3. first literal reflection-space response realization;
4. exact ordinary-formation commutativity boundary;
5. constructive no-go for selection from the current two reversals.

### Open

1. construct the correct interaction-picture anti-involution with constant term one;
2. identify the physical transverse response quotient rather than the nonzero base generator;
3. find a source-native reversal independent on that quotient;
4. prove its joint Gramian is bounded below cofinally;
5. reconstruct neutral arithmetic displacement from neutral complete response.

## 9. Hostile scope

1. The theorem is finite-dimensional in the operator coefficient. Banach-algebra extension needs
   admitted bounded generators and norm convergence.
2. `*` is Hilbert adjoint generated by the source setup, not automatically an arithmetic
   involution before a Hilbert realization exists.
3. The unnormalized exponential has nontrivial degree zero. Calling it a Chen group-like signature
   would be false without interaction normalization and a coproduct theorem.
4. Two fixed source exponentials can commute, in which case ordinary fusion shows no commutator.
5. Fixedness of the base evolution is a counterexample to selection, not an RH statement.
6. Common recovery is sufficient transport only; it does not create a third reversal.

## 10. Consequence for the new field

The exact higher mechanism now has a literal first realization and a literal failure:

\[
 \boxed{
 \text{source adjoint generates schedule reversal}
 \quad\text{but}\quad
 \text{functional covariance and adjoint share a live fixed direction}.}
 \tag{DSR.23}
\]

The next construction is no longer “find a source-native nullhomology.” It is:

> form the transverse complete response modulo the common base evolution, construct an additional
> source anti-involution on that same quotient, and prove the resulting joint reversal Gramian is
> proper.

This target is algebraically typed, independently falsifiable, and cannot be repaired by common
recovery or endpoint positivity.

## Gates

- [x] word-adjoint anti-involution proved;
- [x] coefficient schedule reversal proved;
- [x] functional relabelling composition proved;
- [x] reflection-space realization proved;
- [x] joint-selection countermodel proved;
- [ ] interaction-picture fixed anti-involution;
- [ ] transverse quotient and third source reversal;
- [ ] cofinal joint properness;
- [x] Lean formalization after hostile research audit.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all clean under `lake env lean`, built as modules, axiom audit `[propext, Classical.choice, Quot.sound]` only):
new `GaloisForLFunctions.HTGeometry.{WordConvolutionBanachAlgebra, SelfAdjointDysonWordReversal,
PositiveInvolutionIsIdentity}`.  `WordL1 A E` is the Banach algebra `ℓ¹(A*; E) = E ⊗̂ ℓ¹(A*)` with concatenation
product (built here: ring axioms, `‖XY‖ ≤ ‖X‖‖Y‖`, normed algebra, completeness, word adjoint, relabelling
automorphisms, constant term, length filtration).  `H` is any complex Hilbert space (finite dimension not needed),
`A` a finite alphabet.  The word coefficients `U_w(t)` are defined by the expansion (DSR.3); their identification
with the recursive Duhamel family (SR.20) is ULF-SRSM-1 Theorem 4.1, formalized with that card.

| Claim | Lean declaration |
|-|-|
| (DSR.1) self-adjoint source | `SelfAdjointDysonSource` |
| (DSR.2) `𝔅 = End(H) ⊗̂ ℓ¹(A*)` Banach algebra with concatenation product | `WordL1`, `wordSplits`, `mem_wordSplits`, `wordConv`, `wordConv_assoc`, `WordL1.mul_apply`, `WordL1.norm_mul_le'`, `WordL1.norm_eq_tsum`, `WordL1.single`, `WordL1.single_mul_single`, `WordL1.single_nil_one`, `WordL1.hasSum_single` |
| (DSR.3) `B = L ⊗ δ_∅ + Σ K_a ⊗ δ_a`, `F_t = e^{-tB} = Σ_w U_w(t) ⊗ δ_w` | `SelfAdjointDysonSource.generator`, `SelfAdjointDysonSource.response`, `SelfAdjointDysonSource.coeff`, `SelfAdjointDysonSource.hasSum_response`, `SelfAdjointDysonSource.generator_apply_nil`, `SelfAdjointDysonSource.generator_apply_singleton` |
| (DSR.4) word adjoint, `(T ⊗ δ_w)^* = T^* ⊗ δ_{rev w}`, continuous on `𝔅` | `WordL1.star_apply`, `WordL1.star_single`, `WordL1.norm_star'` |
| Theorem 2.1 (DSR.5) isometric conjugate-linear anti-involution | `WordL1.star_mul'`, `SelfAdjointDysonSource.wordAdjoint_laws` |
| (DSR.6) `B^* = B`, `F_t^* = F_t` | `SelfAdjointDysonSource.star_generator`, `SelfAdjointDysonSource.star_response` |
| (DSR.7) `U_w(t)^* = U_{rev w}(t)` | `SelfAdjointDysonSource.star_coeff` |
| (DSR.8)–(DSR.10) relabelling data, `𝒞`, `ρ = 𝒞 ∘ *` | `SelfAdjointDysonSource.FunctionalRelabelling`, `unitaryConj`, `norm_unitaryConj`, `unitaryConj_star`, `unitaryConj_unitaryConj`, `WordL1.relabel`, `WordL1.relabel_single`, `SelfAdjointDysonSource.FunctionalRelabelling.covariance`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal` |
| Theorem 3.1 `𝒞* = *𝒞`, `𝒞² = ρ² = id`, `ρ` anti-automorphism | `SelfAdjointDysonSource.FunctionalRelabelling.covariance_star`, `SelfAdjointDysonSource.FunctionalRelabelling.covariance_covariance`, `SelfAdjointDysonSource.FunctionalRelabelling.covariance_involutive`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal_twistedReversal`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal_mul` |
| (DSR.11) `𝒞B = ρB = B`, `𝒞F_t = ρF_t = F_t` | `SelfAdjointDysonSource.FunctionalRelabelling.covariance_generator`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal_generator`, `SelfAdjointDysonSource.FunctionalRelabelling.covariance_response`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal_response` |
| (DSR.12) `JU_wJ* = U_{σw}` | `SelfAdjointDysonSource.FunctionalRelabelling.conj_coeff` |
| (DSR.13) `JU_w^*J* = U_{σ(rev w)}` | `SelfAdjointDysonSource.FunctionalRelabelling.conj_star_coeff` |
| Theorem 4.1 (DSR.14)–(DSR.17) fixed units closed under `X ▷ Y = XY⁻¹X`; reflection identities | `reflectionFusion`, `reflectionFusion_self`, `reflectionFusion_reflectionFusion`, `reflectionFusion_left_distrib`, `antiInvolution_reflectionFusion`, `SelfAdjointDysonSource.star_reflectionFusion`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal_reflectionFusion` |
| (DSR.18) `α(XY) = YX`; `XY` fixed ⟺ `XY = YX`; `F_t ∈ Q_* ∩ Q_ρ` | `antiInvolution_mul_of_fixed`, `antiInvolution_mul_fixed_iff`, `SelfAdjointDysonSource.star_mul_fixed_iff`, `SelfAdjointDysonSource.FunctionalRelabelling.twistedReversal_mul_fixed_iff`, `SelfAdjointDysonSource.FunctionalRelabelling.response_mem_fixedUnits` |
| §5 (DSR.19) constant term `e^{-tL}`; `Z_t ∈ 1 + 𝔅_{≥1}`; filtered logarithm converges coefficientwise; `Z_t^* = Z_t` ⟺ `[S_t⁻¹ ⊗ δ_∅, F_t] = 0` | `WordL1.constantTerm`, `WordL1.continuous_constantTerm`, `SelfAdjointDysonSource.constantTerm_response`, `SelfAdjointDysonSource.normalizedResponse`, `SelfAdjointDysonSource.constantTerm_normalizedResponse`, `SelfAdjointDysonSource.normalizedResponse_sub_one_mem`, `SelfAdjointDysonSource.pow_normalizedResponse_sub_one_apply`, `SelfAdjointDysonSource.star_normalizedResponse_iff`, `WordL1.filtration`, `WordL1.mul_mem_filtration`, `WordL1.pow_mem_filtration`, `WordL1.isClosed_filtration` |
| (DSR.20) fixed `e^A, e^C`: `XY - α(XY) ≡ [A,C]` and anti-fixed truncated log `≡ ½[A,C]` mod `𝔅_{≥3}` | `WordL1.exp_sub_sum_mem_filtration`, `exp_sub_one_sub_mem_filtration_two`, `fixed_mul_escape`, `truncatedLog`, `truncatedLog_antiFixed` |
| Theorem 6.1 (DSR.21) common fixed line `ℝB` of `*` and `ρ` | `SelfAdjointDysonSource.FunctionalRelabelling.fixed_sourceLine` |
| Theorem 6.1 (DSR.22) `B ≠ 0 ⇒ F_t ≠ 1` for all real `t ≠ 0` | `SelfAdjointDysonSource.response_ne_one`, `eq_zero_of_exp_smul_eq_one`, `isPositive_exp_smul`, `eq_one_of_isPositive_of_mul_self_eq_one` |
| §7 common recovery preserves KL / Jeffreys | corpus `GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift`: `klDiv_splitFormation`, `formationLiftKernel_klDiv_isometry` |

## Log

- 2026-08-14 -- extracted from the self-adjoint hypotheses already present in ULF-SRSM-1.
- 2026-08-14 -- joint fixed generator killed the claim that adjoint plus functional covariance
  already selects neutrality.
- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
