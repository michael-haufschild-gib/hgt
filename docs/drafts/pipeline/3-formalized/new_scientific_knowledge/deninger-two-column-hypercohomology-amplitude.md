# Two-column arithmetic hypercohomology amplitude

- **ID:** `deninger-two-column-hypercohomology-amplitude`
- **Stage:** 2-fully-proven
- **Type:** FORMAL SOURCE LEMMA
- **Label:** `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`
- **Parent:** `deninger-arithmetic-rost-schmid-signature-resolution`

## Statement

Let \(X\) be a site and let \(\mathscr A\) be a connective derived sheaf.  Assume:

1. \(\mathcal H^q(\mathscr A)=0\) for \(q\notin\{0,1,2\}\);
2. for \(q=0,1\), there is an exact resolution
   \[
   0\longrightarrow\mathcal H^q(\mathscr A)
   \longrightarrow\mathscr G^{0,q}
   \xrightarrow{\partial_q}\mathscr G^{1,q}
   \longrightarrow0,                                                  \tag{1}
   \]
   and every \(\mathscr G^{p,q}\) is acyclic for global sections;
3. \(\mathcal H^2(\mathscr A)=i_{\infty,*}\mathbb R(-1)\) for a closed
   zero-dimensional boundary \(i_\infty:X_\infty\hookrightarrow X\), and this
   sheaf is acyclic for global sections.

Then \(R\Gamma(X,\mathscr A)\) has cohomological amplitude \([0,2]\).  More
precisely, after choosing a Cartan--Eilenberg representative of the extension
data of \(\mathscr A\), it is represented by the total complex
\[
 L^0=\Gamma\mathscr G^{0,0},                                          \tag{2}
\]
\[
 L^1=\Gamma\mathscr G^{1,0}\oplus\Gamma\mathscr G^{0,1},              \tag{3}
\]
\[
 L^2=\Gamma\mathscr G^{1,1}\oplus\Gamma i_{\infty,*}\mathbb R(-1),    \tag{4}
\]
with no other terms.  In a strict bicomplex model without a nonzero
Postnikov \(k\)-invariant, the differentials are
\[
 d^0(a)=(\partial_0a,\delta^0a),                                      \tag{5}
\]
\[
 d^1(c,b)=\delta^1c-\partial_1b,                                      \tag{6}
\]
where \(\delta\) is the internal coefficient differential.  A nonzero
archimedean \(k\)-invariant adds its boundary component to `(6)` but creates
no fourth term.

Consequently a local coefficient of amplitude \([0,1]\), a length-one
Rost--Schmid resolution, and one zero-dimensional degree-two orientation
sheaf produce the required arithmetic degrees \(0,1,2\).

## Derived-descent form

The form used after `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` does not require
two-term homotopy sheaves.  Let \(G^{0,\bullet}\) and
\(G^{1,\bullet}\) be derived-section complexes of amplitude \([0,1]\), let
\(\partial:G^{0,\bullet}\to G^{1,\bullet}\) be a cochain map, and let
\(S[-2]\) be one orientation summand.  If
\[
 R\Gamma(X,\mathscr A)
 \simeq
 \operatorname{Tot}\!\left(
 G^{0,\bullet}\xrightarrow{\partial}G^{1,\bullet};S[-2]
 \right),                                                            \tag{7}
\]
then \(R\Gamma(X,\mathscr A)\) has amplitude \([0,2]\).  Choosing two-term
representatives gives
\[
 G^{0,0}\longrightarrow
 G^{1,0}\oplus G^{0,1}\longrightarrow
 G^{1,1}\oplus S.                                                     \tag{8}
\]
This is the same total-degree argument as `(2)`--`(4)`.  It applies to a
two-level arithmetic localization or hypercover model for derived sections,
even when \(\mathscr A\) itself has additional stalk Tor.

## Proof

Resolve the two nonzero sheaves
\(\mathcal H^0(\mathscr A)\) and \(\mathcal H^1(\mathscr A)\) by `(1)`.
The degree-two boundary sheaf is already global-section acyclic.  The
resulting Cartan--Eilenberg object has nonzero bidegrees
\[
 (p,q)=(0,0),(1,0),(0,1),(1,1),(0,2).
\]
All its entries are acyclic for \(\Gamma\), so applying global sections and
totalizing computes \(R\Gamma(X,\mathscr A)\).  Total degree is \(p+q\).
The listed bidegrees therefore give exactly `(2)`--`(4)` and no term of
degree greater than two.  The standard signed total differential gives
`(5)`--`(6)` and squares to zero because the horizontal and vertical
differentials commute.  Postnikov extension maps remain inside the same
three total degrees.  This proves the amplitude claim.

Equivalently, the hypercohomology spectral sequence
\[
 E_2^{p,q}=H^p(X,\mathcal H^q(\mathscr A))
 \Longrightarrow\mathbb H^{p+q}(X,\mathscr A)
\]
has nonzero entries only at
\((0,0),(1,0),(0,1),(1,1),(0,2)\), so it has no abutment outside
\([0,2]\).

## What this does not prove

- It does not construct the resolutions `(1)` on Deninger's rational-Witt
  flow space.
- In the derived-descent form it does not prove the comparison `(7)`.
- It does not prove their exactness or global-section acyclicity.
- It does not compute \(H^1\) or prove that it is infinite-dimensional.
- It does not identify \(H^2\) with the orientation line after taking the
  quotient by \(d^1\); that follows from trace duality, not amplitude alone.
- It does not use the transverse flow as a differential.  Any flow must act
  by commuting endomorphisms of `(2)`--`(4)`.

## Novelty audit

The double-complex argument is standard.  Its new role here is to isolate the
minimal source theorem required by Deninger's arithmetic curve: two
Rost--Schmid derived-section columns for geometric Milnor degrees \(0,1\),
plus one archimedean orientation in degree \(2\).  This replaces the
unsupported claims that local amplitude alone bounds global
hypercohomology or that chartwise amplitude is stalkwise amplitude.

The algebraic totalization, including a nonzero signature boundary and the
two reciprocity identities forcing \(d^1d^0=0\), is implemented
unconditionally in
`DeningerArithmeticTwoColumnSignatureTotalization.lean`, and is now verified:
the module compiles and builds, and every declaration audits to
`propext, Classical.choice, Quot.sound`.

**Verdict:** `FULLY PROVEN ON PAPER`.

## Lean status

### The totalization is verified

`formal/GaloisForLFunctions/RHTower/DeningerArithmeticTwoColumnSignatureTotalization.lean`,
building on the three-term complex framework of
`DeningerArithmeticThreeTermCohomology.lean`.  Axiom audit: `propext, Quot.sound` for the
totalization itself, `propext, Classical.choice, Quot.sound` for the flow and cup constructions.

- `deningerTwoColumnSignatureD0`, `deningerTwoColumnSignatureD1` (with their `_apply` lemmas) —
  **`(5)`–`(6)`**: `d⁰(a) = (∂₀a, δ⁰a)` and `d¹(c,b) = δ¹c - ∂₁b` together with the archimedean
  signature boundary.
- `deningerTwoColumnSignatureD1_comp_D0` — **`d¹d⁰ = 0`**, forced by exactly the two reciprocity
  identities: commutation of the residue square and vanishing of the total signature boundary on
  degree zero.
- `deningerTwoColumnSignatureComplex` — **`(2)`–`(4)`**: the total complex
  `L⁰ = Γ𝒢^{0,0}`, `L¹ = Γ𝒢^{1,0} ⊕ Γ𝒢^{0,1}`, `L² = Γ𝒢^{1,1} ⊕ Γ i_∞ℝ(-1)`, as a three-term
  complex — the amplitude claim, since the listed bidegrees `(0,0),(1,0),(0,1),(1,1),(0,2)` are
  exactly the terms of total degree at most two and there is no fourth term.  This is also the
  derived-descent shape `(8)`.
- `deningerTwoColumnSignatureComplexKInvariant` — **a nonzero archimedean `k`-invariant creates no
  fourth term**: adding any further component to the signature boundary changes only the
  reciprocity identity, not the three total degrees.
- `deningerTwoColumnSignatureFlow` — the transverse flow acts by commuting endomorphisms of
  `(2)`–`(4)`, as the card's scope requires; it is not a differential.
- `deningerTwoColumnPair02`, `deningerTwoColumnPair11`, `deningerTwoColumnCupPairing` — the
  chain-level cup pairing assembled from the endpoint and middle traces.

### Exact scope of the formalization

Formalized: the total complex, its differentials, `d¹d⁰ = 0`, the absence of a fourth term, the
flow action, and the cup pairing — that is, the card's own computation, which its novelty audit
already identifies as the Lean content.

Not formalized, and not formalizable in mathlib today: the reduction of `RΓ(X,𝒜)` to that total
complex, i.e. the Cartan--Eilenberg resolution and the statement that `Γ`-acyclic entries compute
derived global sections.  mathlib has no sheaf cohomology on a site, so this step cannot even be
stated there; it is the standard homological-algebra input the card quotes, and the card's own
"what this does not prove" list already places the construction of the resolutions `(1)` and the
comparison `(7)` outside the theorem.
