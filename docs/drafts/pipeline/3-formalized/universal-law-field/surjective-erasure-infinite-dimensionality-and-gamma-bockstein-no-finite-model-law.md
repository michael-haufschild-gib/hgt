# Surjective erasure, infinite dimensionality, and Gamma-Bockstein no-finite-model law

- **ID:** ULF-REG-SEID-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified) / LIVE-OBSTRUCTION CONSEQUENCE
- **Source:** Realization End Geometry plus fixed-corona Gamma response lifetime
- **Statement:** A surjective linear endomorphism that kills a nonzero law class forces an infinite-dimensional carrier; therefore the fixed-corona Gamma-Bockstein death transition has no faithful finite-dimensional linear realization.
- **Status:** [LEAN-CERTIFIED] [DEPENDENCY-CLOSED] [LIVE BOCKSTEIN LEVERAGE]
  [NO PROJECT AXIOMS] [NOT RH]

## 1. General theorem — surjective erasure forces infinity

Let \(K\) be a field, \(V\) a \(K\)-vector space, and \(T:V\to V\) a surjective linear map. If
there is \(x\ne0\) with \(Tx=0\), then

\[
\boxed{\dim_KV=\infty.}
\tag{SE.1}
\]

### Proof

If \(V\) were finite-dimensional, rank-nullity for the endomorphism \(T\) would make surjectivity
equivalent to injectivity. But \(Tx=T0\) with \(x\ne0\), contradicting injectivity. QED.

The conclusion is not merely that the kernel is nontrivial. It says a one-sided response can be
surjective and information-erasing only because the carrier has an infinite direction reservoir.

## 2. Semigroup consequence

Let \((T_s)_{s\ge0}\) be a semigroup of surjective linear endomorphisms of one carrier \(V\). If a
nonzero class \(x\) has a finite death time,

\[
T_sx=0
\quad\text{for some }s,
\tag{SE.2}
\]

then \(V\) is infinite-dimensional. Consequently no finite-dimensional semigroup of surjective
endomorphisms can have a nontrivial increasing death-kernel filtration.

## 3. Literal fixed-corona application

Let

\[
Q=\mathbb C^{\mathcal P}/\ell^1(\mathcal P)
\tag{SE.3}
\]

be the fixed prime corona and let \(\overline G_s:Q\to Q\) be the source Gamma response

\[
(G_sx)_p=p^{-2s}x_p.
\tag{SE.4}
\]

The Lean-certified response theorem proves:

1. every \(\overline G_s\) is surjective;
2. for every \(t\ne0\), the Bockstein class \([\beta_t]\) is nonzero through the critical time
   \(s=|t|/2\);
3. \(\overline G_s[\beta_t]=0\) exactly when \(s>|t|/2\).

Choose any \(t\ne0\) and \(s>|t|/2\). The class \([\beta_t]\ne0\) lies in
\(\ker\overline G_s\), while \(\overline G_s\) is surjective. Theorem 1 gives

\[
\boxed{\neg\operatorname{FiniteDimensional}_{\mathbb C}(Q).}
\tag{SE.5}
\]

More importantly, any linear realization preserving both surjectivity and the nonzero-to-zero
Bockstein transition must also be infinite-dimensional.

## 4. Field consequence

Realization End Geometry predicted that a genuine finite/global law event must expose
nonproperness, nonclosed admission, or infinite branching. Equation (SE.5) locates that event in the
live fixed-corona obstruction: the response is one-sided surjective rather than invertible, and its
kernel can grow only in an infinite-dimensional carrier.

This rules out, unconditionally:

- every finite matrix model of the full Gamma death semigroup;
- every finite-dimensional exactification that retains surjectivity and the physical Bockstein
  lifetime;
- every locally finite realization tower claiming to model class death without an additional
  infinite/nonproper boundary.

Finite matrices may still model fixed apertures. They cannot preserve the global death transition.

## 5. Why this matters for the source-normal dagger landing

The open source theorem asks for a source-normal comparison whose physical image is the dagger
Bockstein class. This result does not construct that comparison. It proves a hard design constraint:
if the comparison intertwines the surjective Gamma response and preserves the observed finite
lifetime, its target cannot be finite-dimensional or locally finite in the relevant exact sense.

Therefore searches for a source-normal landing inside finite cyclic quotients, finite matrices, or a
uniformly finite extension category cannot work. The landing must retain an infinite prime/coframe
reservoir or cross a nonclosed/singular admission boundary.

## 6. Sharp boundaries

1. Dropping surjectivity kills the theorem: projection \(K^2\to K^2\),
   \((x,y)\mapsto(x,0)\), erases a nonzero class in finite dimension.
2. Replacing endomorphism by a surjection \(V\to W\) with \(\dim W<\dim V\) also permits a finite
   kernel. Same-carrier dynamics is load-bearing.
3. Infinite dimension is necessary, not sufficient, for nontrivial death.
4. The result does not prove chain-level source coframe conservation or RH.

## 7. Lean certificate

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveSurjectiveErasure`.

Closed declarations:

- `constitutiveSurjectiveErasure_not_finiteDimensional`;
- `constitutiveGammaCorona_not_finiteDimensional_of_bockstein_death`;
- `constitutiveGammaCorona_not_finiteDimensional`.

All three declarations are closed. Targeted source check and final module build passed. `#print
axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. No project axiom, computation
proof, or unproved source premise occurs.

## Log

- 2026-08-09 — general surjective-erasure theorem and literal Gamma-Bockstein application proved on
  paper; finite-dimensional landing mechanisms ruled out.
- 2026-08-09 — all three declarations closed in Lean; targeted final build passed; promoted to
  Stage 3.
