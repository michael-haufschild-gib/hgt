# CLG/TTF native rank-six boundary

- **Stage:** 5-failed — only the proposed all-order positivity of individual reflected theta fibres.
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR.
- **RH chain:** Literal theta source → all signed center-mixed jet Hankel sections nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Scope:** The center-mixed hierarchy remains live and equivalent to RH. Its all-order positivity is unproved. The individual-fibre extension is false.

## Exact obstruction

Let `r_n(x)` be the literal derivative at `t=0` of `Φ(x+t)Φ(x−t)`, with `Φ` the complete theta source. Its next signed odd block is

```
[-r₂   r₄  -r₆]
[ r₄  -r₆   r₈]
[-r₆   r₈  -r₁₀].
```

At the self-dual seam, write `f_n=Φ⁽ⁿ⁾(0)`. Odd `f_n` vanish, so the five independent entries are

`a=-2f₀f₂`, `b=2f₀f₄+6f₂²`, `c=-2f₀f₆-30f₂f₄`,

`d=2f₀f₈+56f₂f₆+70f₄²`, `e=-2f₀f₁₀-90f₂f₈-420f₄f₆`.

The determinant is `D=ace-ad²-b²e+2bcd-c³`. The exact modular ODE eliminates the mass derivatives through order twelve and gives `D=M⁶ P(R²)`, where `M` is the positive self-dual theta mass and `P` is the explicit degree-fifteen rational polynomial in `PolynomialODEJetOddRankThreeClosure`. The source bounds give `191/10<R²<20`.

Set `y=R²-191/10`, so `0≤y≤1`. The negative polynomial has an exact decomposition into a positive constant, nonnegative positive-coefficient powers `y,…,y⁹`, and positive-coefficient terms `1-y¹⁰,…,1-y¹⁵`. This proves `P(R²)<0` by symbolic polynomial identities and inequalities. Every jet step is separately sealed as a proved auxiliary lemma; no numerical oracle or computed sign certificate enters the proof.

The public source-positive chart identifies every literal source jet at the seam with its normalized four-state formal ODE jet. Exact chart pullbacks and the first-order source equations provide this all-order identity. Thus the negative polynomial is the determinant of the literal source block. Continuity extends negativity to a nontrivial open center interval.

## Strongest positive survivor: sharp uniform rank boundary and Schur split

Every positive center has a strictly positive five-dimensional native jet block. The even rank-three block uses the proved global eighth-order curvature; the odd rank-two block uses the proved global second–sixth curvature. Near the seam the next odd rank-three block is not positive semidefinite. Therefore five is the sharp uniform leading rank for this individual-fibre method.

More precisely, put `Δ=ac-b²>0` and

`Q(x,y,z)=ax²+2bxy+c(y²+2xz)+2dyz+ez²`.

The exact division-free identity is

`aΔQ = Δ(ax+by+cz)² + [Δy+(ad-bc)z]² + aDz²`.

The plane `z=0` remains strictly positive. The triangular change

`x ↦ x+(bd-c²)z/Δ`, `y ↦ y+(bc-ad)z/Δ`

gives exactly `Q(x,y,0)+(D/Δ)z²`. It is invertible by reversing the shifts, so this isolates one scalar channel. The cofactor vector `(bd-c²,bc-ad,Δ)` has energy `ΔD`; it supplies the explicit negative witness when `D<0`. For arbitrary coordinates the sharp lower bound is `Q≥(D/Δ)z²`.

This is a dependency-closed paper proof and a Lean-formalized survivor, not only a negative test. Center integration must retain the square terms and compare their contribution with the signed Schur remainder. Individual negative fibres do not imply a negative integrated determinant; the exact global correction below yields a positive integrated rank-six section.

## Positive integrated survivor

The exact integral-preserving correction now closes the next mixed odd block. With `G=3Φ²+2xΦΦ′`, `ThetaCuspGlobalOddCompensation` proves `H+CΔG>0` for every nonnegative center and every `10⁹≤C≤3·10⁹`. The coefficient selected from the literal seam lies in this interval. The correction is a proved integrable derivative with zero half-line integral, so it leaves the actual mixed tenth entry unchanged. Consequently `thetaCuspCenterMixed_oddHankelThree_pos` is strictly positive for every critical aperture, without a source-sign premise.

This is a dependency-closed paper proof and Lean-formalized positive survivor. The proof retains the complete infinite source and controls the middle determinant by exact two-atom reserves and certified errors. See [the full global comparison and audit](../3-formalized/clg-ttf-global-odd-compensation.md). The [full six-dimensional matrix and arbitrary six-point cluster assembly](../3-formalized/clg-ttf-sixth-rank-and-successor-source.md) are proved. The rank-seven successor source sign and all-order positivity remain open.

## Lean status

- `RankThreeHankelSchurBoundary`: exact square identity, cofactor witness, positive plane, sharp minimum bound, triangular split.
- `PolynomialODEJetOddRankThreeClosure`: exact twelfth-jet elimination, analytic ODE closure, strict degree-fifteen polynomial sign.
- `ThetaCuspModularSeamSourceJets`: all-order literal-source/formal-jet identity and exact odd determinant specialization.
- `ThetaCuspNativeSixthRankBoundary`: literal reflected derivatives and continuity; global positive five-dimensional block; negative seam determinant; open negative chamber; explicit non-PSD witness; source-specialized Schur split.
- Main capstone: `RHTower.exists_thetaCuspNativeTranslationJet_rankFiveBoundary`. The literal translation-jet matrices have entries `(-1)^j r_(i+j)`; the signed odd block is proved to be a diagonal congruence of the rank-six principal block. Reflection symmetry supplies every zero odd entry.
- Positive decomposition: `RHTower.thetaCuspNativeOddHankelThree_schur_split`.

## Verification

- All four modules pass scratch and direct production `lake env lean` checks; final production checks have no warnings.
- Only needed oleans generated. All four modules are imported once by their umbrellas; no umbrella, full, or cascading build was run.
- New rank-boundary, source Schur-split, and sharp-minimum capstones report only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint passes. Existing large-file warnings are unrelated to these four modules.
- All 37 new public declaration names have no outside-module declaration conflicts. `git diff --check` passes; the corpus index retrieves the final capstone.
- Owned scratch files removed and foreground Lean processes completed. No pre-existing theorem was axiom-audited again.

## Native even rank-four boundary and its calibrated positive survivor

`ThetaCuspEvenCompensationCoefficient` also proves that the complete-source even four-by-four determinant is strictly negative at zero. The strict even head remains invertible, and its exact new Schur coordinate is negative. This does not change the sharp uniform native leading-rank-five boundary or imply failure of an integrated sign.

The positive survivor is a rationally calibrated family of exact integral-preserving corrections. The canonical even coefficient satisfies `10^12<C_*<3·10^12`; every coefficient in the closed band gives strict positivity on common near-zero and cofinal regions, with all weighted entries integrated exactly. Its dependency-closed paper proof and eight Lean modules are [formalized and audited](../3-formalized/clg-ttf-even-compensation-rational-band.md). The intervening compact comparison remains open, as do the actual rank-seven sign and all-order hierarchy. This boundary does not retire the integrated route.
