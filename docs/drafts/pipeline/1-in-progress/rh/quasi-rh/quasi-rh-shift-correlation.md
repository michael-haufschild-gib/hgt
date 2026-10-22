# Additive shifts of the sextic character block

- **ID:** quasi-rh-shift-correlation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE, with a closed algebraic exceptional-set classification
- **Source:** [Fixed-strip task](quasi-rh-fixed-strip-improvement.md)
- **Statement:** Keep the fourth-moment character correlations produced by additive shifts, and separate their exact power degeneracies before completion.

## Arithmetic target

The common-ideal-one specialization of the cached detector's `GramJoint.jointExtension` contains a sextic character in each lattice variable. A pointwise cube-root-conductor block bound would require a scalar bound of shape `N^(1/2) q^(1/6+ε)`. The existing windowed `RHTower.Sieve.weyl_vdc` supplies the shift inequality, but its correlations still require arithmetic estimates. Complete character orthogonality alone does not provide this conductor saving.

For a finite field K and a multiplicative character χ with χ⁶=1, the shifted fourth-moment integrand is

`χ(x−a) χ(x−b) conjugate(χ(x−c) χ(x−d)) = χ(P(x))`,

where `P(X)=(X−a)(X−b)(X−c)^5(X−d)^5`. The equality includes the zeros of the factors: all exponents are positive and multiplicative characters vanish at zero.

## Closed paper proof: exact power degeneracies

More generally, let s,t be multisets of elements of any field, each of cardinality less than m, with m>0. Write `A_s=∏_{a∈s}(X−a)` and `P=A_s A_t^(m−1)`. Then P is an m-th power if and only if s=t.

If `P=Q^m`, the root multiplicity at u is

`count_s(u)+(m−1)count_t(u)=m count_roots(Q)(u)`.

Adding `count_t(u)` and reducing modulo m shows that the two counts are congruent. Both lie in `[0,m)`, so they are equal. This holds at every u, proving s=t. Conversely s=t gives `P=A_s^m`. The argument uses polynomial roots with multiplicity, not equality of the functions induced on a finite field; small field size does not invalidate it.

For m=6 and two shifts on either side, the exact exceptional condition is

`(a=c and b=d) or (a=d and b=c)`.

For a finite shift set S of cardinality H, there are exactly `2H²−H` exceptional ordered quadruples. The two matching graphs each have H² elements, and their intersection is the H tuples `(a,a,a,a)`. Thus the count retains collisions instead of assuming four distinct shifts. The same algebraic classification applies to cubic order at this moment; quadratic order needs a different classification because two repeated roots can already be a square.

## Closed paper proof: cross-ratio reduction

For a finite field K, put

`Cχ(a,b,c,d)=Σ_x χ((x−a)(x−b)/((x−c)(x−d)))`,
`Hχ(λ)=Σ_t χ(t(t−1)/(t−λ))`.

Assume `a≠b`, `a≠d`, `b≠d`, `c≠d`. Set `A=(b−d)/(b−a)`, `B=A(d−a)`, `λ=A(c−a)/(c−d)` and `k=(b−a)/(c−d)`. The permutation `t=A+B/(x−d)` of K has inverse `x=d+B/(t−A)`; the field's total inverse maps zero to zero, so `x=d` corresponds to `t=A`. For `x≠c,d`, direct factorization gives

`(x−a)(x−b)/((x−c)(x−d)) = k t(t−1)/(t−λ)`.

At `x=c` both character arguments vanish. At `x=d` the left argument vanishes and the right equals one. Summation therefore gives the exact identity

`Cχ(a,b,c,d)+1 = χ(k) Hχ(λ)`.

No distinctness between c and a or b is needed. The identity applies to every multiplicative character, not just order six. It retains the exceptional point at infinity; omitting its correction changes the sum. This is a complete-field identity and does not itself control a short interval or an Eisenstein shell.

For a nonprincipal character, the translation Gram kernel is

`Σ_λ conjugate(χ(u−λ)) χ(v−λ) = q·1[u=v]−1`.

Consequently, for `A(t)=χ(t(t−1))`,

`Σ_λ |Hχ(λ)|² = q Σ_t |A(t)|² − |Σ_t A(t)|² ≤ q(q−2)`.

The Gram identity follows by a fractional-linear permutation when u≠v and by counting the q−1 nonzero arguments when u=v. The inequality keeps the nonnegative Jacobi-sum term; it needs no unproved Weil bound. This offers complete-parameter average cancellation. A short-parameter application still needs a source-specific distribution or completion argument.

For fixed distinct a,b,d, the cross-ratio map permutes K and `|χ(k)|=1` for c≠d. Thus

`Σ_{c≠d} |Cχ(a,b,c,d)+1|² ≤ q(q−2)`.

This estimates the literal complete four-shift correlations, including c=a and c=b. It is not a pointwise bound for every c.

## Conjecture: extend the short-shift fourth-moment range

For a prime p and a character of exact order six, let S be an interval of B distinct residues. The concrete target is

`(CM4)  Σ_{x mod p} |Σ_{h∈S} χ(x−h)|⁴ ≪ε p^(1+ε) B²`, uniformly for `1≤B≤p^(1/3)`.

The exact fourth-moment expansion is `Σ_{a,b,c,d∈S} Cχ(a,b,c,d)`. The power classification isolates `2B²−B` diagonal tuples, each of absolute size at most p. The new burden is the signed aggregate of the remaining correlations. At `B=p^(1/3)`, bounding each of the B⁴ terms separately by square-root conductor size would cost `p^(11/6)`; CM4 asks for `p^(5/3+ε)`. The aggregate therefore needs a further `p^(1/6)` saving. The complete-parameter mean-square theorem above does not supply it for this structured shift set.

Why this is the right exponent to investigate: a Burgess-style amplification with A multiplicative shifts, B additive shifts and `AB≈N` has the Hölder numerator

`(AN)^(3/4) (p B²)^(1/4)`

if the literal multiplicity second moment is `Oε(AN p^ε)` and CM4 holds. Division by AB gives `N^(1/2) p^(1/4) B^(−1/4)`. The choice `B=p^(1/3)` gives the required `N^(1/2) p^(1/6)`; `B=p^(1/4)` gives only `p^(3/16)`. This is an exponent calculation, not a closed amplification proof: shift errors, multiplicity bounds and the interval constraints remain to be supplied. The critical range `p^(1/3)≤N≤p^(2/3)` is compatible with `AN≈N²/B≤p`.

The first pilot is a rational prime residue field. An application to the detector additionally needs Eisenstein lattice windows, composite conductors, fixed ray factors and the exceptional-frequency subtraction. For three quarters, the reflected-source loss remains an independent obligation. No CM4 assertion is introduced as an axiom or as a proved Lean estimate.

**Formalized scope obstruction.** CM4 cannot be extended to arbitrary shift sets over square fields using cardinality alone. Take K of size `r²`, with `r≡5 mod 6`, and its subfield F of size r. An order-six character of K is trivial on F×. For `S⊂F`, `|S|=B`, the packet is B on F\S and B−1 on S. Hence the fourth moment is at least `(r−B)B⁴+B(B−1)⁴`. At `B≈r^(2/3)`, this exceeds `|K| B²` by a power `|K|^(1/6)`, contradicting the proposed subpower-loss bound for any fixed `ε<1/6`. The surviving target must use the geometry of intervals over prime fields or balanced Eisenstein windows. The [cardinality-only variant](../../../5-failed/quasi-rh-cardinality-only-cm4.md) is retired; CM4 as stated over prime intervals remains open.

The construction needs no floor or numerical experiment. Set `r=5^(6n+3)`, `q=r²=5^(12n+6)`, and `B=5^(4n+2)`. Then `B³=q`, `r/B=5^(2n+1)≥5`, and the lower bound is at least `4·5^(22n+10)=4·5^(2n)·qB²`. Both the field and an order-six character exist for every n, because `6|(q−1)`. The character's restriction to F is trivial directly from norm surjectivity: every nonzero a in F is the norm of a nonzero y in K, its image is `y^(r+1)`, and `6|(r+1)`. `RHTower.QuasiRHShiftCorrelation.exists_sextic_subfield_moment_obstruction` in `QuasiRHSubfieldMoment.lean` formalizes the full existential family without an assumed character or set. The exact subfield contribution and its nonnegative complementary contribution supply the positive survivor.

## Closed paper proof: the subfield projection

The obstruction exposes a useful exact identity. Let K/F have degree two, `|F|=r`, and let χ be nonprincipal and trivial on F×. Then

`Σ_{a∈F} χ(x−a) = r·1[x∈F]−1`.

For x in F this counts r−1 nonzero arguments. For x outside F, `(a,b)↦bx−a` is a bijection from F² to K: equality with different b would put x in F, and the two finite sets have the same cardinality. The b=0 row contributes r−1. Every b≠0 row equals the desired sum by division by b and χ(b)=1. Since the complete nonprincipal character sum is zero, the desired row is −1.

Scaling by u≠0 gives `Σ_{a∈F}χ(x−ua)=χ(u)(r·1[x/u∈F]−1)`. For an arbitrary shift set S, summing its packet over the affine line `x−uF` therefore gives

`Σ_{a∈F} Σ_{h∈S}χ(x−ua−h) = χ(u)(r·|S∩(x−uF)|−|S|)`.

Thus affine-line occupancy is an exact visible component of the character packet, not merely a qualitative obstruction. Any extension of CM4 to the inert Eisenstein residue fields must account for concentration on every F-line. A concrete surviving pilot is a box `S=I+ωJ` over `F_p²`, with ω an Eisenstein basis element, comparable side lengths and `|S|≤p^(2/3)`. Such a box has at most `max(|I|,|J|)` points on any affine F_p-line. This removes the exhibited one-line concentration at the level of geometry; it does not prove the desired fourth-moment cancellation. The remaining signed cross-ratio aggregate still needs an estimate.

The precise box conjecture is `Σ_{x∈K}|Σ_{h∈S}χ(x−h)|⁴≪_{ε,C₀}q^(1+ε)B²`, where `p≡5 mod 6`, `q=p²`, χ has exact order six, I and J are residue intervals, `C₀⁻¹≤|I|/|J|≤C₀`, and `B=|I||J|≤q^(1/3)`. The aspect-ratio bound is part of the conjecture. The affine-line identities are formalized; neither this box moment estimate nor its transport to the detector is proved.

## Remaining analytic obligations

- Obtain a complete-sum estimate for the non-power sextic polynomials over the actual residue fields. The inspected native Stepanov theorem covers quadratic characters over square-cardinality fields; it is not this estimate.
- Retain the explicit exceptional count in the additive-shift fourth moment, including the coprimality masks at composite moduli.
- Transport the resulting estimate to the actual Eisenstein shell and fixed ray-class weights, with uniform conductor and smoothing costs.
- Check the final exponent before counting it toward `5/6`. An ordinary Burgess saving is weaker than the proposed Weyl-strength block estimate. `3/4` additionally requires changing the actual reflected-source bound.

## Calibration test

`Detector/CalibrationCancellation.calibration_coefficient_cancel` and `SourceCoefficient.sourceHighCoefficient_eq_bare` remove the auxiliary calibration from the normalized coefficient on its supported frequencies. The positive invariant is the explicit `bareSourceCoefficient`; varying calibration phases alone cannot be counted as cancellation in this coefficient. This does not rule out changing the excluded prime set, the detector weights, or bounding a genuinely mixed physical expression, whose support and normalization would need separate proofs.

## Gates

- [x] Dependency-closed paper proof of the power classification and exact exceptional count.
- [x] Formalize the classification, count, and character integrand identity.
- [x] Formalize the complete correlation normalization, exact mean-square identity, and literal fourth-moment expansion.
- [x] Formalize the subfield lower bound and its order-six character realization; retain the window-geometry restriction.
- [x] Formalize the exact affine-line character average and packet occupancy identity.
- [ ] Prove CM4, or a source-weighted alternative with the same conductor saving.
- [ ] Supply a source-applicable nonexceptional correlation estimate.
- [ ] Derive either requested zero strip from unconditional arithmetic estimates.

`QuasiRHShiftCorrelation.lean` contains six exported theorems. `QuasiRHCharacterCorrelation.lean` contains eleven, including the complete four-shift average and the signed fourth-moment expansion. Both leaves pass focused `lake --old env lean` checks without warnings and are wired into `RHTower`. All 17 theorem audits, and the fractional-linear equivalence audit, use only `propext`, `Classical.choice`, and `Quot.sound`.

`QuasiRHSubfieldMoment.lean` adds seven exported theorems, including the exact subfield contribution and the existential order-six family. `QuasiRHSubfieldProjection.lean` adds three exact line-average and occupancy identities. Both leaves pass focused checks without warnings and are wired into `RHTower`; all ten exported theorem audits use the same standard axioms.

These are supporting arithmetic results, not a proof of either strip or a claim of external novelty.
