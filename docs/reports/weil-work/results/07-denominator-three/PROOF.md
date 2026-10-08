# Proof ledger

## Assigned target

For every λ : ℕ → ℝ, full Weil positivity and third-integral interval masses imply λ(n)=Λ(n) for n≥2. **OPEN CORE:** classify the normalized degree-three data listed in the working card with all zeros of the completion on the critical line. No paper proof is claimed.

## Multiplicity audit

At a zero ρ of ζ of multiplicity m, let r=ordρ(G). The meromorphic quotient G/ζ³ has order r−3m, and pole order max(3m−r,0). Thus failure of the bound pole order ≤2m means r<m. For m>1 this permits 0<r<m. Consequently the pole-filtration argument alone does not establish an entirely omitted zeta zero.

## Local pencil candidate: REDISCOVERED / incomplete multiplicity audit

Corpus L273/L301/L387 already use rosette splitting and divisibility to obstruct perturbative twins. This is not selected as a new result. The multiple-zero issue above remains a correction to the wording of older notes, not a refutation of their underlying converse mechanism.

## Central exclusion: dependency-closed paper proof

**Statement.** There is a fixed δ>0 such that every full-positive λ with third-integral interval masses has μλ((-δ,δ])=0. In particular its corresponding degree-three completion is nonzero at 1/2 and has positive functional-equation sign. No RH, Euler product, coefficient sign, regular-deviation, or finite-type assumption is added.

Let r=1/100 and w=1/6. Let φ be the convolution of the corpus nonnegative smooth probability bump supported on [-r,r] with two uniform probability densities on [-w,w]. This is the corpus `WeilDeletion.phi r hr w 1`. It is C², nonnegative, has integral 1, and is supported in [-103/300,103/300]. Its autocorrelation is supported in [-103/150,103/150], strictly inside (-log 2,log 2). Thus every integer term of its Weil form vanishes, for every λ.

Put K(t)=|φ̂(t)|², using the corpus paper Fourier normalization. The exact spectral representation and explicit formula give

    ∫ K dμλ = Re Wζ(φ,φ).

This uses full positivity only to obtain μλ and the finite nonnegative integral; the zeta zero side does not use RH. For a centered complex zeta zero z=γ+i(1/2−β), |Im z|<1/2. The corpus Fourier estimate gives

    |φ̂(z)| ≤ exp(r|Im z|) [cosh(w Im z)/(w|z|)]²
             ≤ 36 exp(103/600)/|z|².

Here cosh(x)≤exp(|x|). The same bound holds at conjugate z. Consequently

    Re[φ̂(z) conjugate(φ̂(conjugate z))]
       ≤ 1296 exp(103/300)/|z|⁴ < 2592/|z|⁴.

The exponential inequality follows from 103/300<log 2. All zero multiplicities are retained. The existing unconditional source-moment theorem states

    Σ_q |z_q|⁻⁴ < (42/41)(17/200000).

It is `xiShiftAbsoluteMass_one_lt_secondMomentBudget`; its definition is precisely this absolute fourth reciprocal sum. Absolute convergence justifies taking real parts and the termwise majorant. Therefore

    ∫ K dμλ ≤ 2592 Σ_q |z_q|⁻⁴
              < 2592(42/41)(17/200000) < 1/4.

Since K(0)=1, this already proves μλ({0})<1/4 for every full-positive λ. Continuity gives a fixed δ>0 with K(t)≥3/4 whenever |t|≤δ. Hence

    (3/4) μλ((-δ,δ]) ≤ ∫ K dμλ <1/4,

so 3 μλ((-δ,δ])<1. The left side is a natural number under the exact third-counting assumption, hence zero. By the proved zero-measure correspondence, a central zero of a degree-three completion would contribute at least 1/3 to this interval, contradiction. Evaluating the negative functional equation at s=1/2 would force that central zero. Thus only the positive sign survives. ∎

**Status:** paper proof complete and both new Lean modules compile. The quantized central-gap conclusion excludes a proper subclass only. The positive-sign degree-three classification remains open. The numerical threshold also gives the same central-atom contradiction for positive integer denominators at most four; only the assigned denominator-three consequence is formalized here.

**Attack / novelty verdict:** SURVIVES PRELIMINARY ATTACK as an exact exclusion for the full non-Euler class; novelty label **BRIDGE / UNESTABLISHED**. Parent method is classical explicit-formula testing (Miller 2002; Omar 2014). Bllaca, “On Properties of Certain Special Zeros of Functions in the Selberg Class” (2016 online; 2018 volume), explicitly studies central multiplicity and first positive zeros under GRH in a subclass of the extended Selberg class. This is close prior work beyond automorphic classes. Its publisher abstract was checked, but the full article was unavailable; no claim of scientific novelty or disjointness from that theorem is justified. The corpus contribution is the exact formally checked bridge from its unconditional reciprocal-zero bound to the complete Weil datum.

## Multiplicity deficit in every nontrivial degree-three datum

Exact target for the next loop: under the complete degree-three correspondence, either λ(n)=Λ(n) for every n≥2, or there is a nontrivial zeta zero ρ with ordρ(E)<ordρ(ξ). No simplicity, RH for ζ, or Euler-product hypothesis may be added. This is a formalization candidate for the corrected L223 boundary, not a claim of new scientific novelty.

Proposed proof: if E contains ξ's full zero divisor, then ζ satisfies RH because all E-zeros lie on the line. Divide E by 2ξ, canceling all removable singularities. On Re(s)>1 the corresponding Dirichlet series is G/ζ (Möbius convolution), with degree-two gamma factor and logarithmic weights (3λ−Λ)/2. Degree-two counting rigidity then gives (3λ−Λ)/2=Λ. The obligations are global holomorphic division, growth of the quotient with zeros, and exact Dirichlet/logarithmic-derivative transport. The located `FiniteOrderEnvelope.of_entire_quotient` and `OrderOneEnvelope.of_entire_quotient` require a zero-free quotient and do NOT pay the growth obligation here.

Successful paper route: subtract one zeta counting measure from three times the producer measure. Divisor containment makes the difference positive; half of that difference is half-integral. The detailed proof below identifies its full Weil functional with (3λ−Λ)/2 and applies half-integer rigidity. This avoids unproved quotient-growth assumptions. **Status: paper proof complete; spectral subtraction and multiplicity transport Lean-checked and axiom-audited.**

Further correction: L224's finite-pole argument, even when all growth hypotheses are paid, yields infinitely many zeta zeros with ordρ(G)<2 ordρ(ζ). It does not show that those zeros are simple. A stronger “infinitely many deficits below ordρ(ζ)” statement might follow from a finite-pole degree-two converse theorem; Raghunathan's 2010 abstract confirms the general subject, but the exact theorem was unavailable and is not imported as an assumption.

## Spectral subtraction: paper proof before Lean

Let a,b be full-positive coefficient systems. Suppose b has integer interval counting, a has third-integral interval counting, and μ_b≤3μ_a. Put c=(3a−b)/2. For every compact C² test f, affine dependence of the explicit formula on coefficients gives
3 W_a(f,f)=W_b(f,f)+2 W_c(f,f).
Spectral representation and μ_b≤3μ_a imply W_b(f,f)≤3W_a(f,f), hence W_c(f,f)≥0. Thus c is full-positive, derived rather than assumed.

For any full-positive a,b,c satisfying 3a=b+2c, their canonical measures satisfy 3μ_a=μ_b+2μ_c. Proof: for each compact mollifier f_j, its three finite Bochner measures have characteristic functions satisfying the same affine identity, because translates of f_j⋆f̃_j remain compact tests. Uniqueness of characteristic functions identifies 3ν_a=ν_b+2ν_c. The corpus's weighted-measure identity and mollifier-shell uniqueness then give the unweighted measure identity. No subtraction of infinite measures is used.

On any bounded interval, write 3μ_a(I)=m and μ_b(I)=n, both natural. The identity gives 2μ_c(I)=m−n, with m≥n; therefore c has half-integer counting. Integer rigidity gives b=Λ, and half-integer rigidity gives c=Λ. Hence a=(b+2c)/3=Λ. This proves the spectral-domination exclusion with all its stated inputs paid. It is a bridge to existing counting rigidity, not a claim of new converse-theorem novelty.

To obtain the divisor-deficit theorem under the complete degree-three datum alone, negate all deficits. Every ξ zero then remains an E zero, so RH for ζ follows from the datum's critical-zero condition. The ξ atom formula and integer counting identify μ_Λ. At each ordinate, divisor domination gives μ_Λ{t}≤3μ_a{t}; μ_Λ is purely atomic, so this implies measure domination. Apply the preceding exclusion. The affine-measure lemma and exact atom-order/integer-counting transport are Lean-checked. The mathematical argument introduces no new growth or simplicity hypothesis.

For the exact atom identity, write F(z)=E(z+2). Each zero copy contributes mass 1/3 at Im(z+2). Because every E-zero has real part 1/2, all copies with ordinate t have the same point z=1/2+it−2. This fiber is finite by local finiteness of the analytic divisor and has cardinality ord(F,z)=ord(E,1/2+it). Thus 3μ_a{t}=ord(E,1/2+it), with multiplicities retained. For μ_Λ, a bounded interval meets only finitely many critical zero ordinates, so its mass is a finite sum of natural multiplicities. These arguments also cover empty fibers and empty intervals.

## Next attack after multiplicity transport

Conjecture: if the complete degree-three datum is nontrivial, its deficit set {ρ : ξ(ρ)=0 and ordρ(E)<ordρ(ξ)} is infinite. A finite deficit set would make G/ζ a degree-two Dirichlet series with finitely many extra poles. This is stronger than the corrected L224 degree-one threshold ordρ(G)<2 ordρ(ζ), and still does not assert simple or omitted zeros.

Attack status: **OPEN**. The located degree-two rigidity requires positivity (or a holomorphic completion), so it cannot simply be applied to a signed finite-atom remainder. Finite pole Maass converse results are a literature lead, not a paid lemma. The corpus's `eq_vonMangoldt_of_deficitCount` controls deficit against the full zeta mass μ_ζ, whereas this question concerns the lower threshold μ_ζ/3; it does not fill this gap. Deep search of finite negative index/finite pole terms found no directly applicable verified receiver. No absence claim or new Lean theorem is asserted for this next conjecture.

**Source-application failure, 2026-10-07.** Neururer–Oliver's introduction explicitly distinguishes Raghunathan's polar converse (Euler-product input) from their result (twisted functional equations). Their Theorem 1.2 also excludes spectral parameter zero. Hochfilzer–Oliver's Theorem 3.1 treats parameter zero, but requires a family of twisted functional equations and coefficient growth O(n^σ) with σ<1. None of these extra inputs has been derived for G/ζ from our exact datum. Therefore these sources do not prove the next conjecture. This is a failed import of a theorem, not a disproof of infinite deficits.

**Positive survivor of this failed extension.** The all-points domination result remains valid: the remainder's positivity is proved directly from canonical measure order, and finite Bochner-measure uniqueness pays its exact normalization. Finite exceptions are a specific residual obstruction, not something hidden inside a growth assumption.

**Next alternative to test.** The weaker infinite-deficit statement ordρ(E)<2 ordρ(ξ) at infinitely many ξ-zeros corresponds to finitely many poles of the degree-one quotient G/ζ². The finite-pole Hamburger theorem is a primary-source lead with a finite-growth obligation; no matching complete corpus receiver has yet been verified. Existing Hamburger theta-defect and radial-residue lemmas may provide the needed proof rather than importing an Euler product. This remains a conjecture/transport task, not a Lean result.

Concrete corpus route for that alternative: `coeff_eq_of_critical_line_even_sublinear_defect` in `HamburgerStabilityCriticalLine.lean` takes a holomorphic remainder on 1/2≤Re(s)≤3/2 with quadratic vertical decay and a measurable polynomially bounded boundary defect g satisfying δ∫|g(t)|e^(−δ|t|)dt→0. Finite polar principal parts might be removed using shifted Gamma terms; their reflected discrepancy divided by Γℝ should then decay at infinity. Outstanding work: exact cancellation for arbitrary pole orders, continuation across poles on the boundary, quotient growth/strip decay, and Gamma-ratio derivative estimates. The inspected `norm_Gamma_div_le` and `norm_Gamma_vertical_le` give uniform bounds for positive real abscissas at a common ordinate; they do not themselves establish arbitrary complex-shift decay or differentiated estimates. No premise is silently discharged by those bounds.

## Conjecture audit: arithmetic size versus spectral integrality

Given the exact internal and external frontier, what would a Fields Medal-winning mathematician conjecture? The missing mechanism must distinguish the real-rooted, quantized spectrum inside the large functional-equation class. Improving an already available coefficient-size estimate does not supply that mechanism.

The proposal that `Σ_{n≤X} λ(n)^2/n` has subpolynomial growth is **REDISCOVERED**. `WeilMeanSquare.exists_sum_sq_Ioc_le_of_weilPositiveFull` gives a dyadic log-square bound, and dyadic summation gives `O((1+log X)^3)`. WP03 already records this consequence. Booker's Definition 1.3(A1) additionally asks for pointwise rapid logarithmic decay of `λ(n)/sqrt(n)`; the square-prefix estimate alone does not establish it. Definition 1.3(A3) requires all but finitely many spectral masses integral. Applying its degree-one classification to a third-integral spectrum before proving that requirement would be circular.

The sampling-coefficient proposal is **BRIDGE**. Keeping the square-summable representing coefficients β in `HalfLineSamplingRelations.exists_sampling_relation` gives `γ_j=β_j sqrt(w_j)` with `w_j≪p_{j+1}+1`. The degree-three chart has `p∼n^(1/3)` and the coefficient transport multiplies by another chart factor. Thus the intended stronger abundance statement is `Σ |e(n)|²/n<∞`; Cauchy–Schwarz would give `Σ |e(n)|/n^σ<∞` for σ>1. This remains an unformalized refinement of the existing sampling construction, and is not a complete WP07 datum. In particular no critical-zero conclusion follows. It is not selected as the next core attack.

### Competing exact successor conjectures

For a complete datum `(λ,g,E)`, define

    D₁(T) = Σ_{ξ(ρ)=0, |Im ρ|≤T} max(ordρ(ξ) − ordρ(E), 0).

The sum is over distinct ξ zeros, with multiplicities in the summand. It is finite at every finite T because ξ zeros lie in the critical strip and form a locally finite divisor. No RH or simplicity assumption is made; off-line ξ zeros automatically contribute their full multiplicity because E has only critical-line zeros.

**C-positive:** every nontrivial complete degree-three datum satisfies `liminf_{T→∞} D₁(T)/T > 0`.

**C-thin:** there exists a nontrivial complete degree-three datum with `liminf_{T→∞} D₁(T)/T = 0`.

These are incompatible. C-positive strengthens the infinite-deficit conjecture and makes the obstruction quantitative. C-thin would refute WP07 itself, so constructing it requires every original datum condition, not merely a toy divisor. Neither is asserted proved. **SURVIVES PRELIMINARY ATTACK**, with novelty unestablished: inspected source results use a different deficit, total divisor variation, an Euler product, or twisted functional equations.

**[OPEN CORE]** Prove rigidity when D₁ has finite total mass, retaining the signed degree-two remainder and its cubic parent. The already formalized argument covers D₁ identically zero only. Discarding finitely many negative atoms does not preserve Weil positivity. The known bound for `deficitCount` concerns deficits against the full zeta measure, equivalent here to the larger threshold `3 ord(ξ)`, so it cannot be substituted for D₁. After the finite case, seek a quantitative remainder estimate strong enough to handle a sublinear subsequence; no such estimate is assumed.

## Finite-pole boundary attack: exact bridge and open transport

Given the exact internal and external frontier, what would a Fields Medal-winning mathematician conjecture? A nontrivial complete cubic datum cannot have only finitely many deficits below `ord(ξ)`. Its degree-two quotient should force an impossible finite boundary defect. The competing possibility is a nontrivial cubic datum whose degree-two quotient has finitely many extra poles; that would refute this conjecture and WP07. Neither possibility is assumed.

The following elementary bridge has a dependency-closed paper proof. Let `q : (0,∞) → ℂ` satisfy

    q(x) = q(x+1) + q(x/(x+1))/(x+1),
    q(x) = −q(1/x)/x,
    q(x) → 0 as x → ∞.

Suppose `|q(t)−q(1)| ≤ C |t−1|` for `1/2 ≤ t ≤ 1`, with `C ≥ 0`. Inversion at 1 gives `q(1)=0`. For `x≥1`, put `t=x/(x+1)`. Then `1/2≤t≤1`, and

    |q(x)−q(x+1)| ≤ C/(x+1)²
                         ≤ C(1/x − 1/(x+1)).

Summing the triangle inequality for `x,x+1,…,x+N−1` gives

    |q(x)−q(x+N)| ≤ C(1/x − 1/(x+N)).

Let `N→∞`. This proves `|q(x)|≤C/x` for `x≥1`. Inversion then gives `|q(x)|≤C` for `0<x≤1`. No Euler product, spectral sign, numerical calculation, or coefficient estimate enters this bridge. An even 1-periodic boundary function `f` gives both algebraic identities for `q(x)=f(x)−f(1/x)/x`: periodicity cancels the terms at `1/(x+1)` and `x/(x+1)`; inversion cancels directly. Distributional boundary values require a separate transport proof.

**Novelty attack: REDISCOVERED / BRIDGE.** Lewis–Zagier, *Period Functions for Maass Wave Forms I*, Chapter III §§3–4, prove substantially stronger period-function asymptotics and bootstrapping. The elementary estimate above is selected only as a small exact receiver for the finite-pole argument, not as new mathematics or WP07 closure.

**Transport obligations, still OPEN.** For `Q=G/ζ`, finitely many deficits give finitely many poles `ρ` with `0<Re ρ<1`, retaining arbitrary pole orders. One must prove: (i) the pole-cleared quotient has sufficient growth for Mellin inversion and contour transport; (ii) after the usual poles at 0 and 1 are removed, the Maass inversion defect is the sum of the homogeneous eigenfunction extensions of its axial polar terms; (iii) its leading `sqrt(y) log(y)` boundary coefficient is an even-periodic coboundary represented by a finite sum `Σ x^(−ρ) Pρ(log x)`; (iv) the map from principal parts to the top logarithmic coefficients is injective. The exact scalar factor `−2/Cρ` and its nonvanishing are now checked for the constructed base mode at x=1; arbitrary logarithmic orders and actual quotient transport remain open. The finite boundary-packet receiver below already converts boundedness near zero into vanishing of every polynomial coefficient, allowing equal real parts and oscillatory cancellation. Remaining obligations are proof work, not added hypotheses on the cubic target.

### Finite-mode elimination: dependency-closed paper proof

The cancellation issue has an elementary solution that retains every logarithmic order. First, suppose distinct complex numbers `z_i` satisfy `|z_i|>1` and the sequence `Σ P_i(m) z_i^m`, `m≥1`, is bounded. Induct on `Σ weight(P_i)`, where the zero polynomial has weight zero and a nonzero polynomial has weight `degree+1`. Choose a nonzero `P_a` and apply the shift `F(m+1)−z_a F(m)`. Boundedness is preserved, while the coefficient polynomial becomes

    Q_i(X) = z_i P_i(X+1) − z_a P_i(X).

At `i=a` the weight strictly drops; at every other node it is unchanged, since the leading coefficient is multiplied by `z_i−z_a`. Induction gives every `Q_i=0`. Hence `P_i=0` for `i≠a`. For `i=a`, the identity `Q_a=0` gives `P_a(m+1)=P_a(m)`, so the values at positive integers equal a constant `c`. Boundedness of `c z_a^m` forces `c=0`, because `|z_a|>1`. Infinitely many polynomial roots then force `P_a=0`. This completes the induction. It does not compare real parts, discard oscillatory terms, or assume simple poles.

Consequently, a finite exponential polynomial `Σ exp(ρ_i t) P_i(t)` with distinct exponents of positive real part cannot be bounded for `t≥0` unless every `P_i` vanishes. Choose `h>0` small enough that all imaginary parts of `hρ_i` lie strictly between `−π` and `π`. Then the nodes `exp(hρ_i)` are distinct and have modulus greater than 1. Apply the discrete result to `P_i(hX)` and the sampled times `hm`; substitution by nonzero `h` is injective on polynomials. Sampling here is an exact proof specialization, not a numerical experiment.

For `q(x)=Σ exp(−ρ_i log x) P_i(log x)` with `Re ρ_i>0`, every term tends to zero as `x→∞`: set `t=log x` and use polynomial growth versus exponential decay. The function is continuously differentiable on `(0,∞)`. If it satisfies both period identities above, the telescoping result makes it bounded for `0<x≤1`. Substitution `x=exp(−t)` gives the bounded exponential polynomial `Σ exp(ρ_i t) P_i(−t)`. Therefore every `P_i=0`. This is the positive survivor of the failed conjecture that a nonzero finite interior-pole boundary packet could satisfy the modular relations. It is a proved paper-level BRIDGE, not a proof that a cubic quotient has this packet representation.

The interior identity is also exact before boundary transport: for any 1-periodic `u` on the upper half-plane and `V(z)=u(z)−u(−1/z)`,

    V(z)=V(z+1)+V(z/(z+1)),   V(−1/z)=−V(z).

Indeed `z/(z+1)=1−1/(z+1)` and `−1/(z/(z+1))=−1−1/z`; translation invariance cancels the middle terms. This avoids assuming automorphy of the original Maass function. Passing this identity to a leading logarithmic boundary coefficient still requires the uniform local boundary expansion from the polar modes.

### Concrete next transport construction

For `0<Re ρ<1`, use the absolutely convergent integral

    Uρ(x+iy) = sqrt(y) ∫_{ℝ} |t|^(−ρ) / sqrt((x−t)²+y²) dt,   y>0,
    Cρ = Γ((1−ρ)/2) Γ(ρ/2) / Γ(1/2).

The value assigned to the integrand at `t=0` is immaterial. Substitution `t=yu` and then `v=u²` gives exactly `Uρ(iy)=Cρ y^(1/2−ρ)`. Absolute convergence uses `Re ρ<1` at zero and `Re ρ>0` at infinity. The Poisson kernel satisfies the quarter-eigenvalue equation; dominated differentiation transfers it to `Uρ`. The integral is even in x and analytic along horizontal lines. Hence the corpus's axis unique-continuation receiver should identify the finite polar defect with a linear combination of `Uρ/Cρ` and its parameter derivatives, once the axial Mellin-residue identity is proved.

For fixed `x≠0`, the near-`t=x` integral gives

    Uρ(x+iy)/(sqrt(y) log y) → −2 |x|^(−ρ)  as y→0+.

The intended proof splits a small symmetric neighborhood of x from its complement, subtracts the smooth value `|x|^(−ρ)` in that neighborhood, and bounds the remaining integrals. It must establish convergence locally uniformly in x away from zero and in ρ in compact subsets of the strip, including parameter derivatives. The normalized top boundary coefficient is therefore `−2/Cρ`, nonzero in the strip. Differentiating in ρ produces all logarithmic pole orders with an invertible triangular top coefficient. This supplies a concrete construction for obligations (ii)–(iv), without treating a hypergeometric asymptotic or distributional boundary map as an assumption. These estimates and their Lean transport remain OPEN.

Growth entry point: `FiniteOrderEnvelope.of_entire_quotient` requires a zero-free quotient and is still inapplicable. `PoissonJensenUpperBound.log_norm_le_proximity_of_entire` allows zeros but adds their count; its counted variant asks for an outer bound on the quotient and cannot simply be applied circularly. A possible replacement is to normalize the finite zero factors as disk Blaschke factors, whose boundary modulus is one and interior modulus at most one, then reuse the zero-free Poisson bound. This would give the needed general entire-quotient finite-order lemma from the already available quotient-proximity inequality. No such replacement is asserted implemented.

The boundary estimate has the following explicit paper argument. Fix compact sets of x-values away from zero and ρ-values inside the open strip. For each fixed derivative order j put `Fρ,j(t)=(-log|t|)^j |t|^(−ρ)`. Choose a common `η>0` so `|t−x|≤η` stays away from zero. On that interval `Fρ,j` has a uniform Lipschitz constant L, and

    ∫_{|t−x|≤η} |Fρ,j(t)−Fρ,j(x)|/sqrt((t−x)²+y²) dt ≤ 2Lη.

The constant part integrates exactly to `2 Fρ,j(x) [log(η+sqrt(η²+y²))−log y]`. The complementary integral is uniformly bounded: near zero use `|t|^(−b)(1+|log|t||)^j` with `b<1`; at infinity use `|t|^(−1−a)(1+log|t|)^j` with `a>0`; the intervening compact region is separated from x by η. Thus the remainder after adding `2Fρ,j(x) log y` is uniformly `O(1)`, and division by `log y` proves the required locally uniform limit for every parameter derivative. The same bounds justify parameter differentiation under the integral.

For horizontal analyticity, allow complex x with `|Im x|<y/2`. The real part of `(x−t)²+y²` is positive, so the principal square-root kernel is holomorphic and uniformly dominated on smaller compact sets. All spatial derivatives remain integrable at zero and infinity, giving smoothness and transfer of the directly verified quarter equation. Evenness follows by `t↦−t`. Together with the beta substitution and Gamma nonvanishing, this gives a dependency-closed paper construction of the homogeneous polar modes. Spatial regularity and the quarter equation remain to be formalized; the integral, normalization, evenness and fixed-parameter boundary coefficient are checked in the continuation below.

More precisely define `Vρ,j=(-1)^j ∂ρ^j(Uρ/Cρ)`. Its axis value is `y^(1/2−ρ)(log y)^j`. Its leading logarithmic boundary coefficient is `(-1)^j ∂ρ^j(-2 x^(−ρ)/Cρ)` for x>0. At logarithmic degree j the coefficient is exactly `−2/Cρ`, with only lower-degree terms added. Hence the map on each finite polynomial packet is triangular and injective. For an even, smooth quarter-eigenfunction inversion defect with a finite polar axis expansion, subtract these modes and apply the exact corpus theorem `MaassAxisContinuation.eq_zero_of_axis` (smoothness, quarter equation, evenness, zero axis, horizontal real analyticity). The resulting finite boundary packet satisfies the two modular identities by locally uniform boundary convergence; the finite-packet receiver kills every coefficient. This proves the **paper-level finite-axis-defect rigidity bridge**. The actual quotient's finite-pole Mellin-axis expansion and growth remain unpaid, so the infinite-deficit conjecture is still OPEN.

### Constructed polar integral and a shorter boundary proof

`WeilWorkHigherDenominatorPoissonMode.lean` now constructs the exact integral above. The square substitution reuses `HTGeometry.integral_halfLine_beta`; Gamma nonvanishing proves the resulting integral is nonzero and, by the Bochner convention, integrable. Reflection gives full-axis integrability. At any upper point z, the elementary inequality

    |i−t| ≤ (1+|i−z|/Im z) |z−t|

dominates the new integrand by the already integrable axis kernel. No unknown convergence hypothesis is assumed. Positive dilation, horizontal evenness, the exact axis value, its nonvanishing, and unit-axis normalization are proved. The quarter equation, smoothness, horizontal analyticity, parameter derivatives, and boundary limits are not yet asserted in Lean.

For the next boundary proof, dilation reduces positive x to x=1. Split at `|t−1|≤1/2`. On the complement,

    |i−t| ≤ |1−t|+|i−1| ≤ (1+2|i−1|)|1−t|.

Thus the complementary kernel is dominated, uniformly in y>0, by a fixed multiple of the integrable axis kernel. This avoids separate zero/infinity estimates for each fixed ρ. On the central interval the smooth weight `t^(−ρ)` is Lipschitz; subtracting its value 1 leaves a uniformly bounded integral, because `|t−1|/sqrt((t−1)²+y²)≤1`. The constant part is exactly

    2 arsinh(1/(2y)) = 2 log(1/2+sqrt(1/4+y²))−2 log y.

Consequently the integral plus `2 log y` stays bounded as y→0+. This bounded remainder and the normalized limit at x=1 are now checked in `WeilWorkHigherDenominatorPoissonBoundary.lean`. Dilation gives the paper route to moving x and local uniformity away from zero; its formal transport is still pending. For uniformity in ρ and parameter derivatives, retain the compact-strip envelopes already proved on paper above; fixed-parameter convergence alone does not supply them. No WP07 hypothesis has changed.

**Arbitrary-order refinement.** Parameter differentiation is not essential. For a polynomial P define directly

    Uρ,P(z)=sqrt(Im z) ∫ |t|^(−ρ) P(log|t|)/|z−t| dt.

All logarithmic moments converge: choose ε>0 with `0<Re ρ−ε<Re ρ+ε<1`; for each k, `|log u|^k≤C(u^ε+u^(−ε))` on u>0, using exponential domination at both ends and compactness in between. The two shifted axis kernels therefore dominate each moment. Spatial differentiation and the quarter equation use the same bounds as for P=1. The local subtraction argument gives boundary coefficient `−2x^(−ρ)P(log x)`.

On the axis, substitution t=yu gives `Uρ,P(iy)=y^(1/2−ρ)(AρP)(log y)`, where `AρP(X)=∫ |u|^(−ρ)P(X+log|u|)/sqrt(1+u²) du`. Finite expansion shows Aρ preserves polynomial degree and multiplies its leading coefficient by the already checked nonzero Cρ. On polynomials of degree at most n it is triangular with diagonal Cρ, hence invertible. This realizes every polar-axis polynomial without differentiating Gamma or assuming holomorphic parameter transport. It is a simpler dependency-closed paper route to arbitrary pole orders; its logarithmic integrability and polynomial operator are now formalized below; spatial regularity remains open in Lean. Fixed-parameter boundary convergence must still be extended to the moving spatial arguments in the modular identities.

For the spatial equation write `R=(x−t)²+y²` and `K=sqrt(y)/sqrt(R)`. Direct differentiation gives

    Kxx = −sqrt(y) R^(−3/2) + 3sqrt(y)(x−t)² R^(−5/2),
    Kyy = −K/(4y²) − 2sqrt(y) R^(−3/2) + 3y^(5/2) R^(−5/2).

Thus `y²(Kxx+Kyy)+K/4=0` exactly. On a compact upper-half-plane set, y has a positive lower bound, `|x−t|/sqrt(R)≤1`, and every spatial derivative of K is bounded by a constant times `1/sqrt(1+t²)`. The already described logarithmic moment bounds permit differentiation of every order under the integral. For horizontal complex extension with `|Im x|<y/2`, `Re R≥(Re x−t)²+3y²/4>0`; the principal square-root branch and its derivatives have the same compact majorants. This supplies smoothness, the quarter equation, and horizontal analyticity at paper level for every polynomial weight, with explicit domination independent of t. These are concrete remaining Lean proofs, not assumptions on a producer.

### Exact all-order axis operator

Write `Mρ,j=∫(log|t|)^j |t|^(−ρ)/sqrt(1+t²) dt`. The two-exponent bound above proves absolute convergence for every natural j, with no maximum order. On u≥1 and j>0, take δ=ε/j and raise `log u≤u^δ/δ` to the jth power; this gives `|log u|^j≤δ^(−j)u^ε`. On 0<u≤1 apply the same inequality to u⁻¹. The case j=0 uses `1≤max(u^ε,u^(−ε))`. This proves the required global envelope directly.

Define `Bρ,n(X)=Σ_{j=0}^n binom(n,j)Mρ,j X^(n−j)` and extend `X^n↦Bρ,n` complex-linearly to Aρ. Every Bρ,n has degree at most n and coefficient at n equal to `Mρ,0=Cρ≠0`. Hence Aρ preserves every nonzero polynomial's degree and multiplies its leading coefficient by Cρ. It is injective. For surjectivity, subtract from a target Q of degree n the image of `(leadingCoeff Q/Cρ)X^n`; the remainder is zero or has strictly smaller degree. Constants are reached by division by Cρ; induction on n reaches every Q. This supplies an exact finite-degree proof of invertibility, including degree zero.

For y>0, substitute t=yu in the convergent polynomial-weight integral. The logarithm becomes `log y+log|u|`, the kernel contributes `y^(−ρ−1)`, and the measure contributes y. Expand the finite polynomial using the binomial theorem and integrate each term, justified by the all-order moment bounds. This gives exactly `Uρ,P(iy)=y^(1/2−ρ)(AρP)(log y)`. Therefore every prescribed polar-axis polynomial is realized by one of these actual convergent modes, with no inverse-transform or regularity assumption added. The quarter equation and spatial boundary transport still require their separate Lean proofs.


**Lean checkpoint (2026-10-07).** `WeilWorkHigherDenominatorLogMoments` and `WeilWorkHigherDenominatorAxisPolynomial` now prove the full preceding moment/axis construction. All fourteen public theorems passed final direct checks and standard-axiom audits. `exists_polynomialPolarMode_axis` realizes every Q at every positive y using one actual polynomial weight P. The inverse uses the verified polynomial-sequence basis theorem, whose finite-degree induction is the triangular argument above. No parameter differentiation, simple-pole restriction, or unknown convergence premise enters. This pays the all-order axis construction only; WP07 remains open.

### General quotient growth without zero-freeness

The main conjecture stays infinite deficits for every nontrivial cubic datum; the finite-deficit alternative is still the OPEN CORE. The following classical bridge pays a specific analytic input and is not scientific novelty.

Let F,G,H be entire, F and G not identically zero, and G=HF. Suppose F and G have finite-order envelopes. Then H has a finite-order envelope, with no restriction on its zero divisor. The corpus's `proximity_quotient_le` already proves `m(R,H)≤m(R,G)+m(R,F)+K`; its maximum-modulus step previously required H to be zero-free.

Here is the missing general step with a dependency-closed proof. Fix a circle of radius R>0, center c, on which an entire nontrivial f does not vanish. The checked finite-zero factorization gives `f(z)=g(z)∏(z−a)^m(a)`, with g analytic and zero-free on the closed disk. Every factor with positive multiplicity lies in its interior: a boundary factor would force f(a)=0, contrary to the chosen circle. Replace each linear factor by `B_a(z)=(R²−conj(a−c)(z−c))/R` and define `h(z)=g(z)∏B_a(z)^m(a)`. Zero multiplicities contribute 1. The checked `innerLogKernel_ne_zero` shows every positive-multiplicity corrected factor is nonzero on the closed disk. The corrected h is analytic and zero-free there.

For `|z−c|≤R`, `|z−a|≤|B_a(z)|`. Normalize a and z by R and apply the checked disk Blaschke inequality, or expand the exact identity

`|B_a(z)|²−|z−a|² = ((R²−|a−c|²)(R²−|z−c|²))/R² ≥ 0`.

On the boundary, equality holds by `norm_innerLogKernel_sphere`. Therefore `|f(w)|≤|h(w)|` inside, and their boundary norms coincide. Apply the checked zero-free Poisson estimate to h and replace its boundary proximity with that of f. For `|w−c|≤r<R`, this proves `|f(w)|≤exp(((R+r)/(R−r)) m_c(R,f))`, even if f(w)=0. This proof adds no zero-count or minimum-modulus assumption and retains all multiplicities.

For H, take a zero-free boundary radius `2(1+|w|)≤R≤2(1+|w|)+1`, available from the checked cofinal-good-radius lemma. The Poisson factor is at most 3. Finite-order bounds `|F(z)|≤exp(CF(1+|z|)^dF)` and similarly for G bound their proximities by `CF(1+R)^dF` and `CG(1+R)^dG`. Since `1+R≤4(1+|w|)`, `d=max(dF,dG)` and `C=3(CG 4^dG+CF 4^dF+|K|)` give `|H(w)|≤exp(C(1+|w|)^d)`. H is nontrivial because G is. All hypotheses come from the factorization and the two known envelopes. This establishes the bridge on paper; its application to the cubic quotient still needs the finite-pole clearing factor and exact analytic normal form.

### Endpoint audit for the eventual Mellin transport

The checked finite-packet receiver requires strictly positive real exponents. It must not be applied to endpoint terms at exponent zero. There is an exact survivor: `q(x)=c(1−1/x)` satisfies odd weight-one inversion and the three-term identity for x>0. This already follows from `weightOneDefect_inv` and `weightOneDefect_three_term` applied to the constant periodic even function. Thus extending the receiver to all nonnegative exponents with a zero conclusion would be false. The finite-pole Mellin transport must separate the endpoint correction before applying the interior-pole receiver.

For the degree-two quotient `Q=G/ζ`, with the repository convention `ξ(s)=s(s−1)Γℝ(s)ζ(s)/2`, its completion is `Γℝ(s)^2 Q(s)=(E(s)/ξ(s))/(2(s(s−1))²)`. Thus even after clearing all interior deficit poles, the endpoint factors need attention. A paper-level candidate is a finite-packet classification modulo `c(1−1/x)`, retaining every interior logarithmic order. The quarter-eigenfunction constant term `sqrt(y)(a log y+b)` must be included in the actual inversion-defect construction. This is an explicit transport obligation, not an asserted Lean theorem or an added assumption on the cubic datum.


**Growth Lean checkpoint (2026-10-07).** The preceding majorant, Poisson bound, and general finite-order quotient descent are now proved by `WeilWorkHigherDenominatorQuotientGrowth.lean`, with final direct compilation and all three standard-axiom audits complete. The actual finite-deficit quotient still needs its explicit pole-clearing polynomial and analytic factorization; growth is no longer blocked by an unjustified zero-free assumption. The endpoint audit remains a required part of the subsequent Mellin transport.

### Finite-deficit pole clearing: exact normal form

The competing conjectures remain infinite deficits for every nontrivial complete cubic datum versus a nontrivial datum with finite deficit support. Verdict: SURVIVES PRELIMINARY ATTACK; neither is proved. The next lemma is a classical BRIDGE, not a new classification theorem. Current primary check: Kaczorowski–Perelli, *Multiple standard twists of L-functions*, arXiv:2603.13885v1, starts with extended Selberg-class functions whose only possible pole is at 1. It does not remove the interior poles of our quotient. The corpus deep search was partial (reranking deadline and incomplete judge response); exact source reads, not a search-absence claim, establish the dependencies below.

Here is a dependency-closed proof before Lean. Let E be the entire completion of a cubic datum, with E(1) nonzero. Put `d(z)=max(ord_z ξ−ord_z E,0)` and `S={z:d(z)>0}`. The identity theorem and the nonzero values at 1 make both orders finite everywhere. If S is finite, set

    P(X)=∏_{ρ∈S}(X−ρ)^d(ρ).

P is monic, has degree `Σ_{ρ∈S}d(ρ)`, and has analytic order exactly d(z) at every z. Indeed the factor indexed by z, when present, has that order; every other factor is nonzero at z and has order zero. Since ξ(1)=1/2, d(1)=0 and P(1) is nonzero. The product P·E consequently has order `d(z)+ord_z E≥ord_z ξ` everywhere. The checked entire-division theorem gives an entire H with `P(z)E(z)=H(z)ξ(z)` at every z, including all zeros. In particular H(1) is nonzero. There is no unproved removability or zero-free-quotient assumption.

The checked order-one envelopes for E and ξ imply finite-order envelopes: `log(2+r)≤1+r` for r≥0 gives `C(1+r)log(2+r)≤C(1+r)^2`. Polynomials have a checked finite-order envelope, and products preserve it. Apply the newly checked general entire-quotient growth theorem to ξ, P·E, H. Thus H has finite order. This yields an unconditional alternative on the original datum: either its deficit support is infinite or it has this exact finite polynomial normal form. Finiteness is a case of the conclusion, not a new hypothesis closing WP07. Critical-line location, functional-equation sign, endpoint cancellation and all logarithmic orders remain unchanged. The normal form alone does not exclude the finite branch; its actual Mellin transport remains the OPEN CORE.

**Pole-clearing Lean checkpoint (2026-10-07).** `WeilWorkHigherDenominatorPoleClearing.lean` proves the finite polynomial's monicity, exact degree and exact analytic orders, the canonical deficit specialization, the entire finite-order normal form, and `degreeThree_infiniteDeficits_or_poleCleared`. Final direct compilation and all seven public axiom audits pass; the import is wired. This pays the actual finite-pole clearing and growth specialization. It does not prove the infinite-deficit conclusion.

### Next attack: actual finite-pole Mellin transport

The endpoint correction can be made explicit, so the transport should now be attacked as one connected proof, not as an abstract period-function assumption. The following assembly is a paper target; its remaining analytic steps are not yet Lean theorems for our datum.

Write F=G/ζ and `Λ₂=Γℝ²F=E/(2s²(s−1)²ξ)`. The original complete datum supplies the positive functional-equation sign by the checked central exclusion. Hence `Λ₂(1−s)=Λ₂(s)`. Dirichlet convolution of g with Möbius supplies F's absolutely convergent Dirichlet series on Re(s)>1; no Euler product for G is needed. The canonical clearing polynomial gives an entire finite-order H=P·E/ξ.

**Strip growth.** On Re(s)=2 the identity is `H=2P s²(s−1)² Γℝ²G/ζ`. The checked `CompletionGrowth.norm_LSeries_le_of_two_le` bounds G, `RHTower.norm_zeta_inv_le_of_two_le_re` bounds 1/ζ by 4, and `IntegerMassRigidity.exists_bound_Gammaℝ_two` gives exponential Gamma decay. Every polynomial weight times H is bounded on that line. On Re(s)=−1 use the functional equations of E and ξ; the reflected P is still a polynomial, so the same bound holds. Finite-order Phragmén–Lindelöf then bounds every polynomial weight times H throughout [−1,2]. The corpus's `CompletionGrowth.isBigO_strip_of_finiteOrder` supplies the strip admissibility condition after converting the checked finite-order envelope to its stated convention. Outside a fixed horizontal band all factors of P have modulus at least one. Division by P and by the endpoint polynomial therefore gives arbitrary polynomial vertical decay of Λ₂ away from its finite poles. This proves the needed contour bounds on paper without assuming them of the datum. Exact formal input/output types still need to be joined.

**Contour and endpoints.** Let Θ(y)=Σ f(n)K₀(2πny); its Mellin transform is Λ₂/4 by `MaassThetaMellin.hasMellin_kTheta`. Move the inverse line from 2 to −1 using `FinitePoleVerticalContourShift.verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq`, which retains arbitrary pole orders. Write the Laurent terms at 1 as `a/(s−1)²+b/(s−1)`; symmetry gives `a/s²−b/s` at 0. The endpoint residue contribution to Θ(y)−y⁻¹Θ(1/y) is

    1/4 [(b−a log y)/y − (b+a log y)].

Thus the periodic even quarter-eigenfunction

    u(x+iy)=sqrt(y) Σ f(n)K₀(2πny)cos(2πnx)
              + sqrt(y)(b+a log y)/4

has an inversion defect V=u−u∘S whose axis is exactly a finite sum `sqrt(y)y^(−ρ)Qρ(log y)` over the interior poles, with no leftover endpoint packet. All such ρ satisfy 0<Re ρ<1: they are zeros of ξ, and the checked zero-free half-plane and reflection argument in `RiemannXiZerosInfinite.exists_riemannZeta_zero_mem_openStrip` applies to each zero. At a pole of order d, Qρ has degree d−1 and nonzero leading coefficient, proportional to the highest Laurent coefficient divided by (d−1)!.

**Transport and contradiction.** The checked invertible axis operator realizes each Qρ by an actual polynomial-weight Poisson mode. Once those modes' spatial smoothness, horizontal analyticity and quarter equation are formalized, `MaassAxisContinuation.eq_zero_of_axis` identifies their sum with V. The already-paper-proved locally uniform boundary estimate gives a finite boundary packet with exponents ρ and an invertible map on every logarithmic polynomial. Passing V's exact inversion and three-term identities to that boundary matches the checked `finitePoleBoundary_eq_zero_of_period` hypotheses exactly. It forces every polynomial to vanish, contradicting the nonzero leading Laurent coefficient of any interior pole. This would exclude nonempty finite deficit support; empty support is already handled by the checked multiplicity-domination rigidity theorem.

Remaining audit points are concrete: coefficient convolution and normalization, finite-order-envelope conversion and actual strip bounds, full arbitrary-order Laurent residue expansion, and the Poisson modes' regularity plus moving-point boundary limits. None may be replaced by an additional hypothesis in the final theorem. The complete infinite-deficit theorem and WP07 remain OPEN until this assembly has been audited and formalized. Classification of the ingredients remains BRIDGE / REDISCOVERED; novelty of the exact assembled consequence is UNESTABLISHED.

### Polynomially weighted strip bound: dependency-closed proof

Exact next bridge: for any cubic datum, any polynomial P and entire finite-order H satisfying P·E=H·ξ, every polynomial Q satisfies `sup_{−1≤Re s≤2}|Q(s)H(s)|<∞`. The finite-deficit capstone already produces P and H, so no boundary estimate is an extra premise. The infinite-deficit conjecture still survives preliminary attack against its finite-deficit competitor; this strip theorem is BRIDGE / REDISCOVERED, not that conjecture's conclusion.

For the growth convention conversion, suppose `|H(z)|≤exp(C(1+|z|)^d)`. Set A=max(1,C·2^d) and B=C(1+A)^d. When r≥A, `C(1+r)^d≤C2^dr^d≤r^(d+1)`; when r≤A it is at most B. Thus always `|H(z)|≤exp(B)exp(|z|^(d+1))`, exactly the input of the checked finite-order strip Phragmén–Lindelöf theorem. Polynomial multiplication preserves the original finite-order envelope.

For a polynomial R, choose M,d with `|R(s)|≤M(1+|s|)^d`. On s=2+it, `1+|s|≤|t|+4`. The checked Gamma bound is `|Γℝ(2+it)|≤Cγ(|t|+4)^N exp(−π|t|/4)`. The existing factorial inequality bounds `x^m exp(−πx/4)` by `(4/π)^m m!` for all x≥0. Apply it with x=|t|+4 and m=d+N, using the extra constant exp(π). This proves a uniform bound for R·Γℝ, for every R. Applying the same result to R=1 also bounds the second Gamma factor.

On Re(s)=2, exact cancellation of the nonzero factors in ξ gives `H=2P s²(s−1)²Γℝ²G/ζ`. Absorb all polynomial factors into R, use the preceding Gamma bounds, the absolutely convergent Dirichlet-series bound for G, and the checked bound |1/ζ|≤4. This bounds H on the entire right edge. For the left edge, write E(1−s)=εE(s), |ε|=1. The reflected H obeys the same factorization with polynomial `εP(1−s)` and the original E, so the right-edge argument bounds H on Re(s)=−1. No reflection equation for P or H is assumed. The strip Phragmén–Lindelöf theorem bounds H by the maximum of the two edge constants. Finally apply exactly that proof to QH and QP to obtain every polynomial weight. All steps are independent of zero multiplicities, critical-line location and the sign ε. The original cubic datum's stronger assumptions are retained for the subsequent rigidity argument.

**Normalization audit and tail proof.** In Lean the literal pointwise ratio E/ξ takes value zero at a shared zero, even when the removable analytic value is nonzero. It therefore cannot be used as the analytic continuation in contour transport. Define the degree-two completed continuation by `L₂(s)=H(s)/(2P(s)s²(s−1)²)` using the entire H from pole clearing. Outside the finite zeros of P and the endpoints this is analytic and agrees with the meromorphic ratio in the paper notation. Equality with Γℝ²G/ζ on the right half-plane uses nonvanishing of the canonical P there, which follows from its exact deficit orders and ξ's zero-free half-plane; retain that obligation explicitly.

For any nonzero P, the corpus's `RHTower.exists_radius_norm_polynomial_ge` gives c>0 and R with |P(s)|≥c for |s|≥R. Set T=max(1,R). If |Im s|≥T, both |s| and |s−1| are at least one, so the denominator of L₂ has modulus at least 2c. For each natural N the strip theorem with Q=X^N gives `|s|^N|H(s)|≤B_N`. Also `1+|Im s|≤2|s|` at these heights. Consequently

    |L₂(s)| ≤ [2^N B_N/(2c)] / (1+|Im s|)^N

uniformly on −1≤Re(s)≤2 and |Im(s)|≥T. The same T works for every N. This proves the exact rapid-tail bridge on paper from the actual data; no numerical estimate, zero-free quotient hypothesis, or pre-assumed contour bound enters.

**Strip and continuation Lean checkpoint (2026-10-07).** `WeilWorkHigherDenominatorStripBounds.lean` now proves the polynomially weighted strip bounds from the exact factorization and cubic datum. `WeilWorkHigherDenominatorStripDecay.lean` constructs the pole-cleared degree-two completion, proves it meromorphic everywhere and analytic off the clearing roots/endpoints, derives its equality with `Γℝ²G/ζ` on Re(s)≥2 without assuming P nonvanishing there, and proves every tail decay order with one common height threshold. Both final direct checks pass without diagnostics; all eleven public theorems have only standard axioms. Both imports are wired. The original-datum alternative `degreeThree_infiniteDeficits_or_rapidCompletion` carries these bounds as conclusions, not hypotheses. The next step is the actual Mellin contour identity, including the reflected line and arbitrary Laurent orders; spatial Poisson regularity and boundary transport remain open.

### Actual quotient Mellin and finite-pole contour bridge

The next exact bridge has a dependency-closed paper proof. Put `f=g⋆μ`, with the ordinary Dirichlet convolution and the integer Möbius function mapped to ℂ. Both factors converge absolutely for every Re(s)>1, so convolution converges there. The checked identity `ζ(s)L(μ,s)=1`, together with ζ(s)≠0 in this half-plane, gives `L(f,s)=G(s)/ζ(s)`. Also f(1)=g(1), so normalization is preserved. The real weighted summability required by the checked K₀ Mellin theorem follows directly from this absolute convergence. Therefore the actual theta function of f has Mellin transform `Γℝ(s)²G(s)/(4ζ(s))`. On Re(s)≥2 this is the actual pole-cleared completion divided by four, by the preceding normalization theorem. No new coefficient estimate or Euler product is assumed.

For the contour bridge, let P,H be the exact normal form already supplied by the original datum. Choose the finite set Z consisting of the distinct roots of P together with 0 and 1. All these points lie strictly between Re=−1 and Re=2: P's exact orders imply that a root is a zero of ξ; ξ has no zeros on Re≥2, and its reflection equation excludes Re≤−1. Thus the completed representative is analytic on both boundary lines and everywhere in the closed strip outside Z, and meromorphic at every point of Z.

Fix x>0. Multiplication by the entire function x^(−s) preserves these properties. Along a boundary line σ, its norm is x^(−σ). The actual rapid-tail bound with N=2 gives an integrable tail majorant. On the bounded middle interval the function is continuous, so `(1+t²)` times its norm has a finite maximum. Combining this compact bound and the tail bound yields a global multiple of `(1+t²)⁻¹`, proving both vertical integrals absolutely convergent. On a horizontal side of height ±T, the factor x^(−Re s) is at most x+x^(−2). For sufficiently large T the integral norm is at most `3(x+x^(−2))C/(1+T)²`, hence tends to zero. Applying the checked arbitrary-order finite-pole contour theorem gives the difference of the right and left vertical integrals as `2π Σρ∈Z Resρ[x^(−s)L₂(s)]`. This retains the full Laurent residue, with no simple-pole restriction and no new contour premise.

This bridge does not yet identify the reflected vertical integral, expand endpoint residues, or prove spatial Poisson regularity. Those remain exact obligations for the infinite-deficit conjecture. Classification: classical BRIDGE / REDISCOVERED; WP07 remains OPEN.

**Reflected line and actual theta defect.** The same proof works with either functional-equation sign ε. For Re(s)≥2, ξ(s), P(s), ξ(1−s), and P(1−s) are nonzero. Cancel the exact normal forms at s and 1−s and use E(1−s)=εE(s), ξ(1−s)=ξ(s), and `(1−s)²((1−s)−1)²=s²(s−1)²`. This proves `L₂(1−s)=εL₂(s)` on the boundary pair, without asserting a pointwise formula at poles or removable zeros. The checked inverse-dual Mellin identity says that `x^(−1)Θ(1/x)` has transform `MΘ(1−s)`. Consequently the left-line Mellin preimage of L₂/4 is `εx^(−1)Θ(1/x)`; this uses reflection at 1−s and does not assume ε²=1 separately. Both preimages are continuous for x>0 by theta continuity and reciprocal continuity. Mellin inversion on each boundary line is justified by the integrability already proved. Subtracting the two inversion formulas and using the finite-pole contour identity gives exactly

    Θ(x) − ε x^(−1) Θ(1/x) = (1/4) Σρ∈Z Resρ[x^(−s)L₂(s)]  (x>0).

The factor 1/4 is the K₀ Mellin normalization; the 2π from contour transport cancels Mellin inversion's 1/(2π). This proves the actual finite-residue theta defect on paper for the original datum's finite-deficit branch. It still leaves the endpoint/interior Laurent polynomial decomposition and the spatial Poisson transport unpaid.

**Actual-theta Lean checkpoint (2026-10-07).** All steps in the preceding quotient/Mellin/contour/reflection argument are now checked by `WeilWorkHigherDenominator{QuotientMellin,FinitePoleMellin,ThetaDefect}.lean`. The capstone `degreeThree_infiniteDeficits_or_thetaDefect` needs only the original cubic datum and E(1)≠0. The finite branch supplies the exact coefficient sequence and residue identity, without assuming finite support, vertical estimates, Mellin inversion or a simple-pole restriction as new producer premises. Final direct checks pass without diagnostics; sixteen public theorem audits, including the newly exposed existing right-zero-free lemma, use only standard axioms. The endpoint/interior Laurent-polynomial expansion and spatial Poisson transport remain separate, unproved Lean obligations; WP07 remains OPEN.

### All-order residue polynomials and removable germs

The infinite-deficit conjecture survives preliminary attack against its finite-support competitor; the next statement is a classical BRIDGE, not a new conjecture. The corpus already supplies arbitrary Laurent coefficients, analytic clearing shifts, principal-part splitting, and invariance under punctured-germ equality. Current primary Maass contour formulas likewise retain residues, but do not discharge our missing spatial transport.

Here is the dependency-closed proof before Lean. Let F be meromorphic at ρ, and choose k≥1 with `G(t)=t^k F(ρ+t)` analytic at zero, using the checked existence of arbitrarily large clearing exponents. Define the explicit polynomial

    Q_{F,ρ,k}(X)=Σ_{j=0}^{k−1} [(-1)^j a_{−1−j}/j!] X^j,
    a_ℓ=laurentCoeff F ρ ℓ.

For x>0, `x^(−(ρ+t))=x^(−ρ) exp(−(log x)t)`. The k-clearing shift of `s↦x^(−s)F(s)` is therefore the product of that entire exponential and G. Its residue is the Taylor coefficient of degree k−1 at zero. The ordinary Leibniz formula and `binom(n,j)j!(n−j)!=n!` give the product rule for normalized Taylor coefficients. The exponential's jth Taylor coefficient is `x^(−ρ)(−log x)^j/j!`. The checked shift theorem identifies the complementary coefficient of G with `a_{−1−j}`. Summing and factoring proves exactly

    Resρ[x^(−s)F(s)] = x^(−ρ) Q_{F,ρ,k}(log x).

No maximum pole order and no simplicity hypothesis enters. The coefficient of X^j, j<k, is exactly `(-1)^j a_{−1−j}/j!`; all higher coefficients are zero. Since these scalar factors are nonzero, Q=0 iff all k negative Laurent coefficients vanish. The principal-part splitting then yields an analytic g at ρ with F(s)=g(s) off ρ in a neighborhood. Conversely an analytic punctured germ has every negative Laurent coefficient zero, so Q=0. Equivalently, by the checked meromorphic-order criterion, `Q=0 ↔ 0≤meromorphicOrderAt F ρ`. This is injectivity on the polar part, not a false assertion about F's arbitrarily assigned value at ρ. Thus a pole yields a nonzero polynomial. Increasing the admissible clearing exponent only adds zero coefficients below the possible principal part; the represented residue function and removable-germ criterion are unchanged.

For later application the strict pole strip is also elementary. If ξ(ρ)=0, then ρ≠1. If Reρ≥1, the checked identity `2ξ=ρ(ρ−1)Γℝζ`, Gamma nonvanishing for positive real part and zeta nonvanishing on Re≥1 contradict ξ(ρ)=0. Thus Reρ<1. Apply the same argument to 1−ρ using ξ's reflection equation to get Reρ>0. Exact deficit orders force every root of P to be a ξ zero: if ξ(ρ)≠0, its order and hence its deficit are zero, so P has order zero and cannot vanish. Therefore every interior clearing root lies in 0<Reρ<1, independently of RH. The endpoints 0,1 are treated separately.

This does not yet prove endpoint cancellation or the spatial Poisson transport. Those remain the OPEN CORE after this bridge; the assigned WP07 implication is not claimed.

**Actual deficit poles are nonremovable.** Let P,H be the exact normal form, with E and H entire and nonzero at 1. Their analytic orders are finite everywhere by the identity theorem, as are ξ's. At a root ρ of P, exact orders give `d=ordρ(P)=max(ordρξ−ordρE,0)>0`. Taking orders in P·E=H·ξ gives `d+ordρE=ordρH+ordρξ`. Since d>0, its definition yields `d+ordρE=ordρξ`, hence ordρH=0 and H(ρ)≠0. The strict strip excludes ρ=0,1. Thus `A(s)=H(s)/(2s²(s−1)²)` is analytic and nonzero at ρ. Since L₂=A/P, its meromorphic order is exactly −d<0. The residue polynomial of every actual clearing root is therefore nonzero by the preceding injectivity theorem. This identifies the exact missing multiplicity with the pole order; no cancellation of a genuine deficit is silently allowed.

Consequently the checked theta identity can be written with one polynomial Qρ at every possible pole, chosen by the meromorphic residue theorem above. Each interior root has 0<Reρ<1 and Qρ≠0. The original cubic datum gives infinite deficits OR this actual nonzero interior polynomial packet, with endpoint terms still included explicitly. This is a further exact bridge; it does not yet prove the modular boundary identities for that packet.

### Endpoint cancellation in the existing Maass normalization

This dependency-closed paper proof was written before implementation; its Lean checkpoint follows below. Near each endpoint P is nonzero, since its roots lie in the strict strip. Put A=H/(2P), analytic near 0 and 1. The exact factorization gives A=E/(2ξ) there; ξ(0)=ξ(1)=1/2 ensures local cancellation is legitimate. The original functional equation therefore gives `A(s)=εA(1−s)` near 0. Applying it twice and using E(1)≠0 also gives ε²=1.

Set `B₁(s)=A(s)/s²`, analytic near 1, and `a=B₁(1)`, `b=B₁′(1)`. Then L₂(s)=B₁(s)/(s−1)² near 1. At 0 put `B₀(s)=A(s)/(s−1)²=εB₁(1−s)`, so B₀(0)=εa and B₀′(0)=−εb. For an analytic B at c, the double-pole germ B(s)/(s−c)² has clearing shift of exponent three equal to `t B(c+t)`, including at t=0. The Laurent/Taylor shift theorem gives coefficients B′(c), B(c),0 at indices −1,−2,−3. The residue polynomial is therefore `B′(c)−B(c)X`, with no approximation. Applying the already proved Mellin residue formula gives

    R₁(x)=x⁻¹(b−a log x),   R₀(x)=−ε(b+a log x).

The finite pole set is the disjoint union of the clearing roots and {0,1}. Split its residue sum and substitute these expressions. With the repository's actual definition `RHTower.MaassBesselSeries.maassFun f α β = 4*cosSeries f + constTerm α β`, choose `U=maassFun f (εa) (εb)`. Its axis value is `4sqrt(x)Θ(x)+εsqrt(x)(b+a log x)`. Using ε²=1 and `log(1/x)=−log x`, the endpoint contributions cancel exactly in `U(ix)−εU(i/x)`, leaving

    U(ix)−εU(i/x)=Σρ∈roots(P) x^(1/2−ρ) Qρ(log x).

This normalization removes the extraneous factor 1/4 from the mode matching. For the complete WP07 datum ε=1 is already proved, so the standard inversion-defect period identities apply. Absolute convergence of f gives PolyGrowth f by the checked `MaassConverseLevelOne.polyGrowth_of_summable`; U's regularity and quarter equation are existing corpus results. What remains is endpoint formalization plus the polynomial Poisson modes' spatial regularity/analyticity, quarter equation and moving-point boundary transport, not an unproved regularity premise on U.

For the endpoint implementation, use the equivalent numerator `B₁(s)=E(s)/(2ξ(s)s²)`. The exact factorization and nonvanishing of P and ξ near 0,1 identify L₂ with `E(s)/(2ξ(s)s²(s−1)²)` as a neighborhood germ, even at the assigned endpoint values. At 1 this is B₁(s)/(s−1)². At 0 it is `εB₁(1−s)/s²`: apply the original functional equation at 1−s, so E(s)=εE(1−s), and ξ(1−s)=ξ(s). This avoids any supplementary sign premise. The reflected numerator is analytic at 0, with value εa and derivative −εb. Its two endpoint residues are exactly the expressions above. Derivative and Laurent-germ congruence suffice; no global pointwise quotient assertion at common zeros is made.

**Logarithmic-packet Lean checkpoint.** The all-order residue polynomial, removable-germ criterion, strict interior strip, exact deficit pole order and original-datum polynomial packet are now checked in ResiduePolynomial, InteriorPoles and LogPolynomialDefect. Fourteen public theorem audits use standard axioms only. Endpoint formulas and cancellation below are the next implementation scope, not yet part of that checkpoint.

**Endpoint/Maass Lean checkpoint (2026-10-07).** EndpointResidues and MaassDefect now check the endpoint numerator germs, double-pole formulas and their exact cancellation in U. `degreeThree_infiniteDeficits_or_maassDefect` has only the original cubic datum and E(1)≠0 as premises; its finite branch supplies the actual interior axis packet with nonzero polynomials. Both final direct checks pass without diagnostics; eight public theorem audits have only standard axioms. Both imports wired. This supersedes the endpoint obligation at the earlier checkpoint. The spatial proof below remains unformalized; WP07 remains OPEN.

### Next spatial proof obligations, with uniform boundary parameters

The following is a paper plan for the remaining analytic bridge, not a Lean checkpoint or a claim of scientific novelty. It is derived from the actual `polynomialPolarMode` integral already in the corpus. Write `W(t)=|t|^(−ρ)P(log|t|)` and `q=(x−t)²+y²`. Its kernel is `sqrt(y) q^(−1/2) W(t)`. All logarithmic moments are already integrable for 0<Reρ<1.

For local differentiation, restrict (x,y) to a compact rectangle with y≥δ>0 and |x|≤M. The existing kernel majorant is uniform there: q^(−1/2)≤C(M,δ)(1+t²)^(−1/2). Every spatial derivative of q^(−1/2) is a finite sum of a polynomial in x−t,y divided by a half-integral power of q. The inequalities |x−t|≤sqrt(q), |y|≤sqrt(q), and q≥δ² give an order-dependent constant times q^(−1/2). Derivatives of sqrt(y) are bounded on this rectangle. Thus each derivative is bounded by a constant times the already integrable `|W(t)|/sqrt(1+t²)`. Dominated continuity and differentiation, iterated in the spatial variables, give smoothness. At order two, if D=q^(−1/2), then Dxx+Dyy=q^(−3/2), Dy=−y q^(−3/2), and

    Δ(sqrt(y)D) = sqrt(y)(Dxx+Dyy) + y^(−1/2)Dy − (1/4)y^(−3/2)D
                 = −sqrt(y)D/(4y²).

The differentiated integral is therefore a quarter eigenfunction. An explicit recurrence pays the higher-order bound: with X=x−t, Y=y and q=X²+Y², write an order-n derivative as `P_n(X,Y)q^(−n−1/2)`. Start P₀=1. Differentiation in X replaces P by `q ∂X P−(2n+1)XP`; differentiation in Y replaces it by `q ∂Y P−(2n+1)YP`. Each polynomial is homogeneous of degree n. Hence its absolute value is bounded by its finite coefficient norm times q^(n/2), giving `C_n δ^(−n)q^(−1/2)` uniformly on the rectangle. Leibniz with sqrt(y) gives the stated integrable bounds for every mixed derivative.

For horizontal analyticity at fixed y>0, extend x to w∈ℂ with |Im w|<y/2 and use `((w−t)²+y²)^(−1/2)` on the principal branch. Its argument has real part `(Re w−t)²+y²−(Im w)²>0`; the same compact-strip majorant bounds the function and its complex derivative. The checked complex version of differentiation under the integral then gives a holomorphic extension, hence horizontal real analyticity. All branch, measurability and derivative-majorant conditions must be supplied in Lean before using axis continuation.

For the moving boundary, fix x₀>0 and choose η>0 so every interval [x−η,x+η] for x near x₀ stays away from zero. W is uniformly Lipschitz there. Subtract `W(x) 1_{|t−x|≤η}` from the numerator. On the local interval the remainder is bounded by L|t−x|/sqrt((t−x)²+y²)≤L, uniformly in x,y. Outside it, the denominator is separated from zero; near t=0 and at infinity the integrable logarithmic-moment bounds give a common majorant independent of x near x₀. Consequently

    integral W(t)/sqrt((t−x)²+y²) dt = 2W(x) arsinh(η/y) + O(1)

uniformly as x→x₀ and y→0+. Dividing by log y yields −2W(x₀), without imposing a relation between the rates of x and y. Under a modular map with cx₀+d≠0, its imaginary part is y/|cz+d|²; log of this differs from log y by a bounded term, and the square-root factor has the corresponding continuous limit. These are precisely the moving-point limits required by the finite-boundary receiver. Extending the old fixed-point limit alone would leave this obligation unpaid.

### Compact parameter proof of spatial smoothness

This alternative pays smoothness without constructing each kernel derivative polynomial separately. It is classical BRIDGE / REDISCOVERED: the projective Poisson model in Bruggeman–Lewis–Zagier, §2.3 and equation (2.30), is a stronger parent framework. It does not itself settle the exact untwisted cubic-data conjecture.

First prove the following weighted compact-parameter integration lemma. Let U,V be open subsets of the real plane, K⊆V compact, γ:ℝ→K continuous, w:ℝ→ℝ integrable, and F:U×V→G be Cⁿ, where G is any real Banach space. Then `J(x)=∫ w(t)•F(x,γ(t))dt` is Cⁿ on U. For each x₀∈U choose a closed ball B about x₀ contained in U. Continuity on B×K supplies a uniform bound C for F, hence C|w| dominates the integrand locally. Each fiber in t is continuous before multiplication by measurable w, and each fiber in x is continuous; dominated convergence gives continuity of J. When F is C¹, its derivative in x is the first-coordinate restriction of its total Fréchet derivative. This restriction is continuous on B×K and bounded by C₁. The derivative of the weighted integrand is w(t) times that restriction, bounded by C₁|w(t)|. The checked dominated Fréchet differentiation theorem gives J′ as its integral. The restriction map is Cⁿ when F is Cⁿ⁺¹, because differentiation lowers regularity by one and composition with the fixed coordinate inclusion is continuous linear. Induct on n, applying the same statement to the Banach space of continuous linear maps, then use the finite-order characterization of C∞. Every integrability and uniform-bound hypothesis follows from w∈L¹ and compactness; no finiteness assumption on Lebesgue measure of ℝ enters.

Apply this lemma to `γ(t)=(I−t)/‖I−t‖`. The denominator is positive since Im(I−t)=1; γ is continuous and has norm one. Let `K(z,c)=1/‖z*c.im+c.re‖`, for Im z>0 and c≠0. The denominator cannot vanish: its imaginary part would force c.im=0, then its real part forces c.re=0. Its squared norm is a positive real polynomial in the real coordinates of z,c, so K is jointly C∞ as the negative-half power of that polynomial. The closed unit circle is compact and excludes zero, so the weighted integration lemma applies to every real integrable weight.

For the actual polynomial mode put `W₀(t)=P(log|t|) polarKernel(ρ,I,t)`, already integrable by LogMoments. Since `‖I−t‖=sqrt(1+t²)`, direct cancellation gives

    P(log|t|) polarKernel(ρ,z,t) = W₀(t) * K(z,γ(t)).

Both real and imaginary parts of W₀ are integrable. Apply the real-weight lemma to each, and combine their integrals into the complex integral. Multiplication by sqrt(Im z), smooth on the upper half-plane, proves the actual `polynomialPolarMode` is C∞ there. This argument works for arbitrary polynomial degree and the same exact strip 0<Reρ<1. Reflection still follows by t↦−t, since the polynomial logarithmic weight is even. The quarter equation, horizontal analyticity and moving boundary remain separate obligations; smoothness alone is not axis continuation.

### Spatial smoothness verification checkpoint

The compact-parameter proof above is now formalized in
`WeilWorkHigherDenominatorWeightedIntegral.lean` and
`WeilWorkHigherDenominatorPoissonSmooth.lean`. Both final direct Lean checks
pass, and all eleven public theorem audits use only standard axioms.
In particular `contDiffOn_polynomialPolarMode` and
`polynomialPolarMode_reflect` pay smoothness and evenness in the actual
axis-uniqueness receiver. Quarter PDE, horizontal analyticity and the moving
boundary limit are not yet Lean conclusions. These remaining premises must be
proved before invoking spatial identification or finite-boundary rigidity.

### Quarter equation through inversion and compact parameter integration

The following dependency-closed bridge proof precedes its Lean implementation.
Let U be the upper half-plane, V the punctured parameter plane, and define
A(z,c)=sqrt(Im z)/norm(z*c.im+c.re), complex-valued by inclusion.
The preceding smoothness proof and smoothness of sqrt(Im z) give joint C∞ on U×V.
For a fixed c, put a=c.im and b=c.re. If a=0, then b≠0 and
A(z,c)=|b|⁻¹ sqrt(Im z). This is a constant multiple of the already checked
Maass constant term with parameters (0,1), hence satisfies the quarter equation.
If a≠0, write r=b/a and S(z)=−1/z. The norm identity
norm(z*a+b)=|a| norm(z+r), and Im S(z+r)=Im z/norm(z+r)², give
A(z,c)=|a|⁻¹ sqrt(Im S(z+r)). The existing Maass inversion theorem
preserves the quarter equation and C∞ regularity. Translation by real r
preserves the imaginary coordinate and has complex derivative 1; the checked
holomorphic Laplacian chain rule therefore preserves the quarter equation.
Thus every c∈V gives an actual quarter eigenfunction, including the compactification endpoints.

For completeness, commute the differential operator with weighted integration.
For a joint C∞ family F on U×V and v∈ℂ, define F_v(z,c)=D_zF(z,c)[v].
The first-coordinate restriction of the Fréchet derivative and evaluation at v
are continuous linear operations, so F_v is jointly C∞. On any closed spatial
ball contained in U times compact K⊆V, F, F_v and F_vv are bounded. A fixed
integrable real weight w makes all three weighted fibers integrable. The already
proved dominated derivative formula and the continuous-linear evaluation/integral
identity give D_v ∫wF=∫wF_v. Applying the same result to F_v gives
D_v² ∫wF=∫wF_vv; equality on U suffices for this second differentiation because
U is open. Linear combination for v=1,I and the spatially fixed quarter weight
gives quarterDefect(∫wF)(z)=∫w(t) quarterDefect(F(·,γ(t)))(z)dt.
Every measurability and domination premise follows from continuity and the
compact-bound argument, rather than being added to the final mode theorem.

Apply this to F=A, γ(t)=(I−t)/norm(I−t), K the unit circle, and separately to
the real and imaginary parts of W₀(t)=P(log|t|)polarKernel(ρ,I,t).
LogMoments proves both weights integrable for 0<Reρ<1. Kernel factorization
and pulling the constant sqrt(Im z) through the integral identify the resulting
sum with the actual polynomialPolarMode. The quarter operator is linear and
commutes with constant complex multiplication, so that actual mode has zero
quarter defect for every polynomial order. No hypothesis on a differential
equation, derivative bound, Euler product or coefficient growth is added.
Horizontal analyticity and moving-boundary limits remain separate open steps.

### Horizontal analyticity by the same compact parameter mechanism

This is a dependency-closed paper proof for the next analytic bridge; no Lean
analyticity claim is made here. Fix y>0, put D={w∈ℂ: |Im w|<y/2}, and retain
V=ℂ\{0}. For c∈V write a=Im c, b=Re c and
q(w,c)=(wa+b)²+(ya)². Its real part is
(Re w·a+b)²+(y²−(Im w)²)a². If a=0, b≠0 makes it positive;
if a≠0, the second summand is positive. Thus q lies in the right half-plane
on D×V. The principal function H(w,c)=q(w,c)^(−1/2) is jointly continuous,
and holomorphic in w with jointly continuous derivative
H₁(w,c)=−a(wa+b)q(w,c)^(−3/2).
The derivative formula follows by the polynomial chain rule and the principal
complex-power derivative on the slit plane; its branch condition follows from
Re q>0. All constants are exact, with the same fixed spectral eigenvalue 1/4.

For any continuous joint F,F₁ on D×V with HasDerivAt(F(·,c),F₁(w,c),w),
continuous γ into compact K⊆V and real integrable weight u, the integral
J(w)=∫u(t)F(w,γ(t))dt has complex derivative ∫u(t)F₁(w,γ(t))dt.
Indeed a closed ball about each w₀ contained in D times K bounds F₁ by C;
C|u| is integrable. Continuity supplies measurable fibers, while the same
compact argument for F gives integrability at w₀. The pointwise derivative
is u times F₁. These discharge every premise of the complex dominated
integral derivative theorem. It follows that J is holomorphic on D.

Apply this to H and separately to Re W₀, Im W₀, where the existing logarithmic
moment theorem makes W₀(t)=P(log|t|)polarKernel(ρ,I,t) integrable.
The function sqrt(y)(J_ReW₀(w)+i J_ImW₀(w)) is holomorphic on D. At real
w=x, q(x,c) is exactly the positive projective denominator of x+iy;
the real-power/complex-power identity therefore identifies H(x,c) with
projectivePoissonKernel(x+iy,c). The checked kernel factorization identifies
the holomorphic function's real restriction with polynomialPolarMode(ρ,P)(x+iy).
A holomorphic function is complex analytic on its open domain, and restriction
of scalars followed by the real inclusion gives real analyticity at every
x∈ℝ. Thus the actual mode is horizontally real analytic without an added
regularity or growth premise. This completes the paper proof of that separate
receiver obligation. Moving-boundary limits remain to be formalized afterward.

The pointwise projective-kernel equation also holds at c=0: the defined inverse
norm is zero, so the entire kernel is the zero function. This adds no analytic
claim at the excluded parameter; joint smoothness is used only on c≠0. It is a
trivial extension of the same bridge, not a new rigidity conjecture.

### Quarter-equation Lean checkpoint

WeightedQuarter formalizes first and second directional differentiation through
the actual compact-parameter integral and commutation of quarterDefect.
PoissonQuarter formalizes real translation, full projective-kernel smoothness,
the inversion identification, and `quarterDefect_polynomialPolarMode` for every
polynomial and 0<Reρ<1. All final direct checks pass without diagnostics.
Nine new public theorems and two exposed existing helpers have only standard
axioms. This pays the PDE obligation above. Horizontal analyticity remains a
paper proof awaiting Lean; moving-boundary transport remains separate.

### Spatial identification of the actual finite packet

This dependency-closed proof precedes the corresponding Lean assembly. Suppose
an actual Maass function U from polynomial-growth coefficients has axis defect
U(iy)−εU(i/y)=Σρ∈Z y^(1/2−ρ)Qρ(log y), with finite Z and 0<Reρ<1.
For each ρ∈Z choose Rρ=(polarAxisEquivρ)⁻¹Qρ, and set Rρ=0 off Z.
Invertibility gives Rρ≠0 whenever Qρ≠0, and the already checked axis theorem
gives polynomialPolarMode(ρ,Rρ)(iy)=y^(1/2−ρ)Qρ(log y).
Let B be the finite sum of these actual modes, and A(z)=U(z)−εU(−1/z).
Existing Maass theorems give U and its inverted composition C∞, quarter PDE,
horizontal analyticity and horizontal evenness. The inversion commutes with
z↦−conj z. The now proved mode regularity, quarter equation and reflection,
together with the horizontal-analyticity argument above, give the same four
properties for each mode. Finite sums preserve smoothness and analyticity;
linearity of the quarter operator proves its equation for B. The reflection
identity is termwise. Consequently V=A−B is C∞, even, horizontally analytic,
and satisfies the quarter equation. Its imaginary-axis values vanish exactly.
The existing `MaassAxisContinuation.eq_zero_of_axis` gives V=0 throughout the
upper half-plane, proving A=B there.

Apply this to the finite branch of `degreeThree_infiniteDeficits_or_maassDefect`.
Its actual quotient coefficients have absolute Dirichlet convergence beyond 1,
so the checked weighted-summability-to-polynomial-growth theorem supplies the
only coefficient bound used in the Maass regularity facts. All axis polynomials
are nonzero in that branch, hence all Rρ are nonzero. The resulting original-data
dichotomy is infinite deficit support OR the exact all-point Poisson defect,
with the same P,H,ε normal form and no new regularity, differential-equation,
mode-realization or growth premise. This is spatial transport, not pole removal:
moving-boundary limits are still required to obtain the two finite-boundary
period identities and the desired contradiction. The infinite-deficit branch
and full WP07 remain open.

### Spatial-identification Lean checkpoint

PoissonAnalytic and SpatialDefect pass their final direct Lean checks without
diagnostics. Together with the complex weighted-derivative extension, all seven
new public theorems have only `[propext, Classical.choice, Quot.sound]` in their
axiom audits. Both new imports are wired. The original-datum capstone assumes
only ZetaPowerDatum 3 g E and E(1)≠0, and retains every nonzero residue polynomial.
The horizontal-analyticity and spatial-identification obligations above are now
paid in Lean. The following moving-boundary proof remains to be formalized.

### Moving-boundary reduction by positive dilation

The next exact bridge is the following unrestricted path limit. Fix 0<Reρ<1,
P∈ℂ[X], and x₀>0. As x→x₀ and y→0 through y>0,

    polynomialPolarMode(ρ,P)(x+iy)/(sqrt(y) log(y))
      → −2 x₀^(−ρ) P(log x₀).

No relation between the rates of x and y is required. The already proved
`integral_polynomial_polarKernel_dilate` gives a shorter dependency-closed
proof than a new uniform local estimate in two variables.

First fix x=1. Put W(t)=P(log|t|)|t|^(−ρ), so W(1)=P(0). On [1/2,3/2]
this weight is continuously differentiable; bounded derivative and the mean
value inequality give |W(t)−W(1)|≤L|t−1|. Subtract W(1) times the existing
local cutoff kernel. Its local remainder is bounded by L, since the kernel
denominator is at least |t−1|. Off this interval, the existing boundary tail
comparison bounds the weighted kernel by
(1+2|i−1|)|P(log|t|) polarKernel(ρ,i,t)|, integrable by LogMoments.
Thus the remainder integral is bounded independently of 0<y≤1. The exact
cutoff integral is −2log y plus a bounded continuous function of y∈[0,1].
Division by log y therefore gives the fixed-point limit −2P(0), for every P.

Now put h=y/x, eventually positive and tending to zero. Positive dilation
rewrites the original integral as x^(−ρ) times the integral at 1+ih with
weight P(log x+log|t|). For P(X)=Σₙ aₙXⁿ, expand this translated weight
as ΣₙΣⱼ≤ₙ aₙ binom(n,j)(log x)^(n−j)(log|t|)^j. Each fixed monomial
integral divided by log h tends to −2 if j=0, and to 0 if j>0, by the
fixed-point result. The coefficient functions converge by x→x₀>0.
The finite sum consequently tends to −2P(log x₀). Finally,
log h/log y=1−log x/log y→1, and x^(−ρ)→x₀^(−ρ). Cancelling the
positive sqrt(y) in the actual mode gives the stated limit. Every integral
used in the finite expansion is absolutely convergent by LogMoments.

This pays arbitrary approach paths to positive boundary points once formalized.
Reflection supplies negative points. Under a real Möbius map away from its
denominator zero, the new height is y/|cz+d|²; continuity and the same logarithm
ratio yield the expected weight-one factor. These later algebraic transports
must still be assembled with the actual defect identities. This section makes
no Lean claim for the moving-boundary limit and no full-rigidity claim.

For reuse of the already checked scalar boundary theorem, the fixed-point proof
can equivalently set Q=P−P(0). Its actual weight vanishes at t=1, so the same
local Lipschitz and tail bounds give a uniformly bounded integral for Q alone.
The identity F_P=P(0)F_1+F_Q then gives the full logarithmic remainder bound and
limit. On positive t the weight Q(log t)t^(−ρ) equals the one-term finite
boundary packet already proved C¹ in FiniteBoundary; no new differentiability
assumption is needed. This refinement changes neither the limit nor its scope.

### Height rescaling and the two boundary period identities

The following continuation is proved on paper before its Lean implementation.
Let d→d₀>0 while y→0+, and x→x₀>0. Apply the moving integral limit at
height y/d and multiply by log(y/d)/log y→1. The mode's remaining prefactor
is sqrt(y/d)/sqrt y=1/sqrt d. Consequently its normalization by sqrt(y)log y
has limit −2 x₀^(−ρ)P(log x₀)/sqrt d₀. All denominators are eventually
nonzero by positivity and convergence; no approach-rate hypothesis is used.

For the actual finite packet B(z)=Σρ Uρ,Rρ(z), define
q(x)=−2Σρ x^(−ρ)Rρ(log x), x>0. At z=x+iy the normalized packet tends
to q(x). At z+1 it tends to q(x+1). Write z/(z+1)=1−1/(z+1).
Its real part tends to x/(x+1)>0 and its height is y/|z+1|², so the
rescaling result gives q(x/(x+1))/(x+1). The original Maass function is
1-periodic; its already proved three-term defect identity therefore gives
q(x)=q(x+1)+q(x/(x+1))/(x+1), by taking finite-sum limits.

For inversion S(z)=−1/z, reflection of each mode gives
B(S(z))=B(1/conj z). The latter point has real part x/|z|²→1/x and
height y/|z|², so its normalized limit is q(1/x)/x. The exact inversion
defect identity A(S(z))=−A(z) gives q(x)=−q(1/x)/x. This step uses
B=A=U−U∘S, hence FE sign +1. In the complete cubic correspondence that
sign is already proved by CentralExclusion; it is not assumed for arbitrary
bare cubic data. Every transformed point remains in the upper half-plane.

Thus q is exactly finitePoleBoundary with coefficient polynomials −2Rρ.
The exponents are distinct (a finite set) and have positive real part. The
checked finite-boundary receiver yields −2Rρ=0 for every exponent, hence
Rρ=0. In the original finite-deficit branch each Rρ is nonzero, so there
can be no clearing root. Every positive deficit would make P vanish at its
point (its analytic order is that positive deficit), contradicting the absence
of roots. Hence every deficit is zero and ξ's divisor is contained in E's.
The existing Multiplicity theorem gives λ=Λ for the complete datum.
This would prove the finite-deficit alternative, not eliminate the remaining
infinite-deficit branch or solve full WP07.

### Finite-deficit Lean checkpoint

PolynomialBoundary, MovingBoundary, BoundaryTransport, BoundaryPeriod and
FiniteDeficit pass final direct `lake --old env lean -o ... <module>` checks
without diagnostics. The complete theorem is
`degreeThree_eq_vonMangoldt_or_infiniteDeficits`: precisely the original cubic
correspondence implies `(λ=Λ ∧ RH) ∨ Infinite(xiDeficitSupport E)`.
Thus the finite-deficit competitor is FALSE; the infinite-deficit conjecture
is PROVED for every nontrivial complete datum. The strongest positive survivor
of finite-packet elimination is this all-data dichotomy, now formalized.
Its axiom and lint audit are recorded in EVIDENCE.md. Full WP07 remains OPEN.

### Density continuation: exact conjecture and threshold audit

C2 retains every hypothesis of `degreeThree_eq_vonMangoldt_or_infiniteDeficits`.
For a datum with some n≥2 satisfying λ(n)≠Λ(n), define

`D₁(T) = Σ_{ξ(ρ)=0, |Im ρ|≤T} max(ordρ(ξ)−ordρ(E),0)`.

The sum is over distinct points, with the displayed multiplicity weight. Local
finiteness and the strict zero strip make every finite-height sum finite. C2
asserts that there is c>0 such that, for every R>0, some T>R has D₁(T)≥cT.
The incompatible competitor is D₁(T)=o(T). Neither is proved. Verdict:
SURVIVES PRELIMINARY ATTACK. No literature novelty is established by search
failure. If C2 is true, finite-deficit rigidity extends to all sublinear
one-divisor repairs. A complete counterexample to C2 would also refute WP07;
an arbitrary meromorphic model is not such a counterexample.

The finite-packet proof does not justify an infinite residue sum or its boundary
limit. A sublinear divisor suggests an even canonical clearing product of zero
exponential type, but this requires complex zero locations and arbitrary
multiplicities. `MovingEvenCanonicalProduct` instead starts from positive real
nodes. Even a successful clearing construction does not by itself give the
period defect a continuous, C¹, or real-analytic boundary value. The current
Bohr coefficient receiver assumes absolute summability. Lewis–Zagier's
bootstrapping theorem assumes real analyticity; the already checked C¹ period
bound must not be substituted for it. These are separate obligations.

There is a useful exact change of representation, but not yet a density proof.
Put B(s)=s(s−1)Γ_R(s), C(s)=B′(s)/B(s), and
F_a(s)=E′(s)/E(s)−a ξ′(s)/ξ(s). For real a and Re(s)>1, the original
completion and logarithmic-derivative identities give

`F_a(s) = (3−a) C(s) − 3 L_λ(s) + a L_Λ(s)`.

The constant normalization of ξ disappears on logarithmic differentiation.
At any point ρ the meromorphic residue is
`ordρ(E)−a ordρ(ξ)`: factor each nonzero analytic germ into a power of
s−ρ times a nonvanishing analytic germ, and differentiate logarithmically.
The corpus already proves this local integer-residue mechanism in
`HTGeometry/LogarithmicResidueQuantization.lean`; it is classical, not a new
theorem claimed here.

At a=1, the negative residue mass is exactly D₁, with no residue-amplitude or
pole-order assumption. However, the right-hand expression retains 2C(s).
At a=3, the archimedean term vanishes, but the negative residue mass is
max(3 ordρ(ξ)−ordρ(E),0), the wrong threshold. Thus the existing generic
Weil-deficit counting theorem cannot be imported by a scalar rescaling.
This obstruction is to that proposed inference, not to C2 itself.

[OPEN CORE] Derive a quantitative constraint on the negative integer residues
of F₁ from the exact degree-two quotient structure, while retaining its two
archimedean copies. A contour or period argument must control its infinite
limit from the original datum. Neither small pole count, a zero-type clearing
factor, nor the local residue formula supplies that constraint alone. Next
proof attempt should work directly with finite spectral windows and this
normalization; no additional positivity or regularity premise is permitted.
Phase 5 is incomplete, so no Lean formalization of C2 has been started.


## Exact logarithmic-residue bridge (2026-10-07)

**Classification: BRIDGE / REDISCOVERED.** This does not prove C2 or WP07.
Before implementation, the complete local argument is as follows. For any entire
E with E(1) nonzero, neither E nor xi is identically zero. Hence their analytic
orders at every rho are finite natural numbers e and m. Local factorization gives
E(s)=(s-rho)^e U(s) and xi(s)=(s-rho)^m V(s), with U,V analytic and nonzero at rho.
Consequently

    (s-rho) * (E'/E - xi'/xi)(s) -> e-m

on the punctured neighborhood. This is an actual analytic limit, independent of
any totalized value assigned at rho. Its negative integer part is exactly
max(m-e,0)=xiDeficit E rho. It is negative exactly on xiDeficitSupport E.
Summing this equality over any finite window preserves the exact deficit weight.
The checked finite-deficit capstone therefore gives, under precisely the complete
cubic correspondence, lambda=Lambda and RH OR infinitely many negative integer
residues of this logarithmic difference. No finite-order bound, location condition,
or simplicity assumption on xi zeros is added to the local argument.

On Re(s)>1, the existing logarithmic-derivative identity yields
E'/E=3*weilFunction(lambda). The xi identity yields xi'/xi=C-L_Lambda, where
C=zetaArchimedeanDatum+1/(s-1). Thus the same actual function is

    2*C - 3*L_lambda + L_Lambda.

This makes the degree-two archimedean term and the one-xi threshold explicit in
one checked representation. It is not a mean-negative-residue density estimate.
The general finite-rank/index proposal remains a classical consequence requiring
an additional interpolation argument; it is not being presented as a new theorem.

The affine-pencil and analytic-parameter proposals considered this cycle are
REDISCOVERED (L273/L301/L387/L394). In addition, exclusion of analytic paths does
not prove topological isolation in the infinite-dimensional space. L394's isolated-
component conclusion is not used without a separate compactness or local-structure
argument. C2 remains the next actual open claim; replacing it with more known
local perturbation exclusions would not move the research frontier.


### Next density attack: preserve the exact residue while tracking symmetry

There is an algebraic distinction worth retaining. Subtracting *three xi logarithmic
derivatives* removes C but changes the deficit threshold. Subtracting *2C itself*
from the one-xi logarithmic difference does not change residues in 0<Re(s)<1,
because C is analytic there. In the latter representation,

    A(s) = 2C(s) - (E'/E - xi'/xi)(s)
         = 3 L_lambda(s) - L_Lambda(s)  (Re(s)>1),

positive residues at deficit points are exactly xiDeficit. What this operation
loses is homogeneous reflection: writing F=E'/E-xi'/xi, the positive functional
equations give F(1-s)=-F(s), whereas

    A(s)+A(1-s)=2(C(s)+C(1-s))

away from singularities. Thus merely passing to a pure Dirichlet series has not
removed the archimedean obstruction from the global problem. A density proof
must pay this inhomogeneous reflection term. These are algebraic paper observations,
not a new checked density theorem. The next cycle must attack that estimate rather
than repeat local residues, finite poles, analytic pencils, or broad SOTA inventory.


**LogResidue Lean checkpoint.** The six public theorems in
`WeilWorkHigherDenominatorLogResidue.lean` pass direct foreground compilation and
standard-axiom audits. The printed capstone type has exactly the original complete
correspondence assumptions. Complex deficit points and all multiplicities remain
present. The additional arithmetic-subtraction/reflection discussion above is a
paper observation, not a claimed C2 proof. Scientific frontier unchanged.


## Infinite boundary receiver: exact next proof target (2026-10-07)

C2 remains SURVIVES PRELIMINARY ATTACK, not proved. The current cycle did not
move the scientific classification frontier. The following distinguishes the
objects needed for a new proof attempt; none is an added premise of WP07.

### Two representations cannot be interchanged

The linear Maass/Poisson period equation applies to the degree-two quotient
`Q=L_g/zeta`, with completion proportional to `E/xi`. Its principal parts have
amplitudes as well as orders. In contrast, `F=E'/E-xi'/xi` has the exact integer
residues already checked in LogResidue. Logarithmic differentiation does not
commute with the linear Mellin/Poisson transform, nor with addition in the
three-term equation. No period equation for F follows from the one for Q.

Subtracting `2C` produces a Dirichlet series, but only on its original right
half-plane of absolute convergence. Its almost periodicity there does not give
recurrence of a pole in the critical strip. The meromorphic almost-periodic
theory assumes recurrence on the whole strip under consideration. That is a
missing hypothesis here. L126's existing envelope pays a different spectral
threshold, below three xi divisors, and cannot pay the one-xi threshold by
renaming the signed measure.

Likewise, ordinary pole counting and Beurling–Malliavin density are different
inputs. Exterior BM density controls completeness of exponentials; interior
BM density controls a finite measure's spectral-gap problem. Neither theorem
automatically gives the compact annihilator or the actual spectral-gap measure
needed here. No density theorem was obtained from this literature check.
These are rejected inferences, not a retirement of C2 or WP07.

### Define the boundary object from arithmetic coefficients

Use the verified definitions, with positive functional-equation sign already
derived from the complete correspondence:

    q(n) = degreeTwoQuotientCoeff g n,
    a = degreeTwoEndpointNumerator E 1,
    b = deriv (degreeTwoEndpointNumerator E) 1,
    u = MaassBesselSeries.maassFun q a b,
    U(z) = u(z)-u(-1/z).

For a smooth compactly supported test function phi on R, define the periodic,
even distribution B by

    B[phi] = a integral(phi)
             - 4 sum_{n>=1} q(n) integral(cos(2*pi*n*x) phi(x) dx).

This definition requires no convergence of a residue expansion. The checked
`degreeTwoQuotientCoeff_weighted_summable` gives
`M2=sum_{n>=1}|q(n)|/n^2<infinity`. Two integrations by parts give

    |B[phi]| <= |a| ||phi||_L1 + (M2/pi^2) ||phi''||_L1.

Thus the displayed series defines a distribution of order at most two.
Translation by one and reflection preserve it, directly term by term. This is
a classical paper construction, not a new Lean or scientific-novelty claim.

For phi supported in (0,infinity), set

    (S_test phi)(t) = t^(-1) phi(1/t),
    beta[phi] = B[phi]-B[S_test phi].

The test function remains smooth with compact support in (0,infinity), so beta
is well-defined. The Jacobian is included: this is precisely the distributional
version of `B(x)-x^(-1)B(1/x)`. Keeping the constant a is essential; dropping it
would reintroduce the endpoint survivor `c(1-1/x)` eliminated in the finite
argument. The constant b contributes no leading logarithmic boundary term.

The intended trace identity, not yet proved in this project, is

    U(x+i*y)/(sqrt(y)*log(y)) --> beta in D'((0,infinity)), y --> 0+.

For fixed Fourier mode this follows from the small-argument K0 limit. A proof
for the actual series must justify passage against each test function and the
moving inversion argument; pointwise mode limits do not justify that passage.
The distributional modular relations should then follow by dualizing the
existing algebraic period identities. Classical boundary-form theory supports
this construction, but does not supply the sparsity-to-regularity implication.

### Exact regularity target and incompatible competitor

Retain every original correspondence hypothesis. Under the counterhypothesis
`D1(T)=o(T)`, conjecture that the above beta is represented by a C1 function
`h:(0,infinity)->C` with `h(x)->0` as `x->infinity`.

The incompatible competitor is a complete cubic datum with sublinear D1 for
which this beta remains singular, or every C1 representative fails that decay.
An arbitrary sparse-frequency distribution does not provide such a datum.
This is a BRIDGE conjecture toward C2, not a separately claimed scientific
advance. C2 remains the selected classification conjecture.

If the bridge holds, the already proved weight-one period bounds give
boundedness at zero and `O(1/x)` decay at infinity. The next transport obligation
is to identify the cutoff/one-sided Mellin transforms of beta with the actual
quotient's interior principal parts and use this boundary control to exclude
them. Do not say that an unrestricted bilateral Mellin transform of a polar
mode has its pole at that exponent: `x^(-rho)` has no bilateral convergence
strip, and the continuations of its two half-integrals cancel. Cutoffs and their
domains must be explicit in the infinite argument.

[OPEN CORE] Prove the C1-and-decay conclusion from sublinear D1 for the actual
boundary distribution, while retaining complex deficit points, arbitrary
multiplicities and clustered poles. First pay the distributional trace and
cutoff-Mellin identification, without assuming an absolutely convergent pole
sum. Phase 5 for this receiver and for C2 is incomplete; no new Lean module or
resource-limit change is justified yet. Next cycle should work on these exact
identities, not repeat broad literature inventories.

### Paper proof of the weak logarithmic trace

The trace is a classical BRIDGE. C2 and its regularity conclusion remain open.
Here is the dependency-closed analytic argument for the trace, before Lean work.
Write `K_j(r)=integral_0^infinity cosh(t)^j exp(-r cosh(t)) dt` as in the
existing BesselKZeroMoments module.

For r>0, the primitive `-exp(-r sinh(t))/r` has nonnegative derivative
`J_r(t)=cosh(t)exp(-r sinh(t))`, tends to zero at infinity, and has value -1/r
at zero. Hence J_r is integrable and its integral is 1/r. For t>=0,
`sinh(t)<=cosh(t)<=sinh(t)+1`, so

    exp(-r) J_r(t) <= cosh(t) exp(-r cosh(t)) <= J_r(t).

Integration gives `exp(-r)<=r K_1(r)<=1`. Consequently

    H(r)=K_0(r)+log(r),  H'(r)=(1-r K_1(r))/r,
    0<=H'(r)<=1,

where the last bound uses `exp(-r)>=1-r`. Thus H is monotone and 1-Lipschitz
on the positive half-line. In particular H is bounded on (0,1], and
`K_0(c*y)/log(y)->-1` for every fixed c>0. Monotonicity of K0 gives a bound
`K_0(c*n*y)/|log(y)|<=C_c` simultaneously for all n>=1 and all sufficiently
small y. No asymptotic assertion uniform in n is being assumed.

For the moving inversion term two derivatives of its amplitude are needed.
The existing moment ODE gives `r^2 K_2(r)=r^2 K_0(r)+r K_1(r)`. For r<=1,
`K_0(r)<=K_1(r)` makes the right side at most two. For r>=1, the existing
exponential estimate `K_0(r)<=exp(-(r-1)) K_0(1)` makes `r^2 K_0(r)` bounded.
Therefore both `r K_1(r)` and `r^2 K_2(r)` are bounded on (0,infinity).

Let phi be smooth and supported in a fixed [d,M] with 0<d<M. Set
`psi_y(x)=x/(x^2+y^2)` and `c_y(x)=2*pi/(x^2+y^2)`. For sufficiently small y,
psi_y' stays away from zero on this interval; all derivatives needed below,
including the reciprocals of psi_y', are uniformly bounded. The nth Fourier
term of the normalized inverted trace paired with phi is

    integral phi(x)/(sqrt(x^2+y^2)*log(y))
             K_0(n*y*c_y(x)) cos(2*pi*n*psi_y(x)) dx.

Twice integrate by parts using
`d(exp(2*pi*i*n*psi_y))/dx=2*pi*i*n*psi_y' exp(2*pi*i*n*psi_y)`.
There are no boundary terms because phi has compact support. The amplitude
and its first two derivatives are uniformly bounded: its K0 term uses the
uniform logarithmic bound; its differentiated K0 terms use the bounded
quantities `r K_1(r)` and `r^2 K_2(r)`, together with bounded `r'/r` and
`r''/r`. Thus the integral has absolute value at most `C_phi/n^2`, uniformly
in small y. The same bound for the uninverted term follows by ordinary
Fourier integration by parts. The original-data sum `sum |q(n)|/n^2` now
dominates both series of pairings.

For each fixed n, the K0 limit and compact support give the two limits
`-integral cos(2*pi*n*x)phi(x) dx` and
`-integral x^(-1)cos(2*pi*n/x)phi(x) dx`. Dominated convergence over n is
therefore valid. The constant terms tend to a and a/x respectively; the b
terms and the extra `log(x^2+y^2)/log(y)` term vanish uniformly on the support.
After the substitution t=1/x, the inverted limit is B[S_test phi]. Including
the factor four in maassFun proves the exact proposed trace beta, for every
test phi. The sum/integral interchanges at positive y follow from the existing
exponential strip bounds, also valid on the compact image under inversion.

This proof provides distributional convergence, not continuity of beta and
not convergence of any termwise Mellin residue expansion. Its constants may
depend on the test function's support and derivatives. It gives no new
assumption on g, E or lambda. Lean work starts with the global K-moment and
logarithmic bounds; the moving-phase weak trace and cutoff Mellin identities
remain separately visible formal obligations.

### Sharper remaining regularity receiver

The corpus already proves `weightOne_period_tail_bound` and `weightOne_period_origin_bound` from the three-term identity, inversion identity, decay at infinity, and the local estimate `norm(h(t)) <= C*(1-t)` for `1/2 <= t <= 1`. Their exact source in `WeilWorkHigherDenominatorPeriodDefect.lean:93–158` was checked. Consequently the earlier global C1 target is stronger than the receiver needs.

The narrower conjecture retains every original correspondence hypothesis and D1(T)=o(T): beta has a continuous representative h, tending to zero at infinity, with that local linear-vanishing bound for some C>=0. Its distributional identities then become pointwise identities by continuity. The existing receiver gives boundedness at zero and O(1/x) decay at infinity, sufficient for a bilateral Mellin convergence strip (0,1); identifying this transform with the actual quotient obstruction remains a separate obligation. The incompatible competitor is an actual complete cubic datum with sublinear deficits for which this representation or local bound fails. Neither competitor has been established.

The horizontal trace proved this cycle does not use D1 at all. Attempting to upgrade its dominated-convergence estimate to boundary regularity fails at the test norm: original coefficient summability pays two integrations by parts against smooth tests, not a uniform bound on boundary values or local linear vanishing. This rejects that inference, not C2. The substantive next step must extract cancellation from the actual datum and the sparse deficit hypothesis. No generic sparse-frequency example is being substituted for a complete datum.

Formal status: BesselBoundary, FourierBoundary and WeakTrace now certify the full horizontal testwise limit, including actual sum/integral interchange. The paper's moving-inversion limit is not yet formalized. No continuous-linear distribution object, moving-inversion theorem, cutoff-Mellin identification, sparsity implication or full WP07 solution is claimed by those three modules.

### Variable-phase identity used for moving inversion

Fix real a<=b, L!=0, a C1 real phase psi on [a,b], and a continuous nonvanishing speed v=psi'. Let A0,A1,A2 be complex amplitudes such that the derivatives of A0/v and A1/v are A1 and A2 respectively on the closed interval. Assume these derivatives are integrable and A0,A1 vanish at both endpoints. All quotients use the real speed embedded in C. The primitive P(x)=(iL)^(-1) exp(iL psi(x)) has derivative v(x)exp(iL psi(x)). Integration by parts gives I(A0)=-(iL)^(-1) I(A1) and I(A1)=-(iL)^(-1) I(A2), with every boundary term zero. Thus I(A0)=(iL)^(-2) I(A2), and its norm is at most |L|^(-2) integral_a^b norm(A2). No spectral or residue-series assertion is used.

For a twice differentiable amplitude A and twice differentiable nonzero speed v, the explicit chain is A1=A'/v-A*v'/v^2 and A2=A''/v^2-3*A'*v'/v^3-A*v''/v^3+3*A*(v')^2/v^4. Both identities follow by the quotient/product rule; all real quantities are embedded into C. Uniform bounds for A,A',A'',v',v'' and a positive lower bound for |v| yield a uniform bound on A2. In the actual inversion problem these are to be derived from the already checked Bessel moment bounds and rational phase, not assumed in the cubic-data theorem. This generic identity is a classical BRIDGE.

### Relative-scale derivatives of the normalized Bessel kernel

Fix positive k,y,c(x), write r=k*y*c(x), and assume log(y)<=-1. For F(x)=K0(r)/log(y), the chain rule gives F'=-k*y*c'(x)*K1(r)/log(y) and F''=((k*y*c'(x))^2*K2(r)-k*y*c''(x)*K1(r))/log(y). Put ell=c'/c and eta=c''/c. The exact same expressions become F'=-ell*(r*K1(r))/log(y) and F''=(ell^2*(r^2*K2(r))-eta*(r*K1(r)))/log(y).

Since |log(y)|>=1, 0<=r*K1(r)<=1, and 0<=r^2*K2(r)<=B2:=2+2*exp(1)*K0(1), it follows that |F'|<=|ell| and |F''|<=ell^2*B2+|eta|. The zeroth derivative is bounded uniformly whenever r>=c_min*y and c_min*y<=1, by the already checked K0/log estimate. For inversion c(x)=2*pi/(x^2+y^2), relative derivatives are smooth uniformly bounded functions on any fixed positive compact x-interval for all sufficiently small y. Multiplying F by the smooth compact amplitude phi(x)/sqrt(x^2+y^2) therefore gives the uniform first-two-derivative bounds needed by the variable-phase identity. These are derived estimates, not extra correspondence premises.

### Actual inversion geometry

For x>0 put d=x^2+y^2, psi=x/d, v=(y^2-x^2)/d^2, c=2*pi/d, and w=d^(-1/2). Differentiation in x gives v'=2*x*(x^2-3*y^2)/d^3, v''=-6*(x^4-6*x^2*y^2+y^4)/d^4, c'=-4*pi*x/d^2, c''=4*pi*(3*x^2-y^2)/d^3, w'=-x*d^(-3/2), and w''=-d^(-3/2)+3*x^2*d^(-5/2). These follow directly from the quotient and real-power derivative rules, whose denominators are nonzero because d>0.

Fix 0<a<=b. On K=[a,b]x[0,a/2], x>y>=0, hence v<0 and c>0. Every displayed jet, 1/v, c'/c, c''/c, and 1/c is continuous on K. Compactness therefore bounds all their norms by a common finite constant; increasing it to at least one also yields a uniform positive lower bound for c. This includes y=0 in the geometry only, not in the Bessel/logarithm expressions. Combining these actual bounds with the relative-scale estimates pays the geometric inputs of the moving-trace domination argument.

The explicit amplitude chain also has a useful pointwise norm bound: if the norms of A,A',A'' are at most M>=0 and the norms of 1/v,v',v'' are at most G>=0, then norm(A2)<=M*(G^2+4*G^4+3*G^6). Bound the four displayed quotient terms respectively by M*G^2, 3*M*G^4, M*G^4 and 3*M*G^6, then use the triangle inequality. This avoids any hidden frequency dependence in the final integration-by-parts constant.

For the fixed-mode limit with a moving scale, let c(y)->c0>0. Eventually c0/2<c(y)<2*c0. Monotonicity of K0 sandwiches K0(c(y)*y)/log(y), with inequalities reversed since log(y)<0, between the normalized kernels at fixed scales c0/2 and 2*c0. Both tend to -1. For the actual inversion at x>0, c(y)=k*2*pi/(x^2+y^2) has positive limit and w(y)->1/x. Hence the normalized weighted kernel tends to -1/x, and multiplying by the continuous cosine phase gives -cos(2*pi*k/x)/x. This is the exact fixed-mode limit used after, not instead of, proving a frequency-uniform integrable majorant.


### Compact test amplitude and uniform jet budget

Write H=phi*w, H1=phi'*w+phi*w', H2=phi''*w+2*phi'*w'+phi*w''. For the normalized kernel F, define A=H*F, A1=H1*F+H*F1 and A2=H2*F+2*H1*F1+H*F2. The product rule gives A'=A1 and A1'=A2. Smoothness of phi and positivity of the actual Bessel argument make all three functions continuous on the positive interval. If the first three test jets have norm at most D, the weight jets at most G, and the kernel jets at most B, then the triangle inequality gives norms H<=DG, H1<=2DG, H2<=4DG and A<=DGB, A1<=3DGB, A2<=9DGB. Thus 9DGB is a common amplitude-jet bound. (The mixed second-derivative coefficient is essential.)

Compactness bounds the test jets; the actual geometry budget bounds the weight and relative-scale jets. Increase G to be positive and set c0=1/G. The bound 1/c<=G gives c>=c0. For 0<y<=G and log(y)<=-1, the zeroth normalized kernel is at most B0=K0(1)+|log(c0)|+1; its first derivative is at most G and its second at most G^2*B2+G. The nonnegative sum B=B0+2G+G^2*B2 dominates all three. These bounds hold simultaneously for every k>=1 and every x in the compact interval. Compact support inside its interior forces both phi and phi' to vanish at both endpoints, so A and A1 vanish there. The phase-divided chain from the preceding proof therefore has zero endpoint terms and a uniform bound, paying every premise of the double integration-by-parts identity.


### Scope audit of the sublinear-deficit implication

The moving Fourier majorant is derived without D1. It therefore cannot by itself establish that D1=o(T) produces a continuous boundary representative or local linear vanishing. The negative integers in E'/E-xi'/xi locate deficits exactly, but quotient residues in E/xi are different amplitudes; bounds for the former do not bound the latter. Also, the signed remainder retains degree two: the general three-xi deficit receiver does not apply to the one-xi divisor.

A tempting sparse-clearing argument would form a canonical product over the deficit divisor and use sublinear counting to seek a zero-exponential-type multiplier. Even granting that growth conclusion, multiplying by such a function does not preserve the required ordinary Dirichlet series or the polynomial vertical bounds of a finite-order boundary distribution. Neither preservation assertion has been proved from the actual cubic datum. Thus this is an unpaid inference, not a reduction of C2 to the finite-pole theorem and not a retired route. The precise remaining target is still the continuous representative with the local linear bound and infinity decay, derived from the original datum plus D1=o(T), followed by actual cutoff-Mellin identification. A generic sparse sequence is not a counterexample to that exact statement.


The current corpus also exposes two distinct sublinear receivers. `RHTower.zeta_mass_sublinear_rigidity_of_truncated` (ZetaMassSublinearRigidity.lean, source lines 795 onward) assumes an exact one-Gamma atomic identity and sublinear weighted mass `sum |c_j|*|zeta(1/2+i*t_j)|`, with t_j>=1 and quadratic weighted summability. `RHTower.HamburgerStability.coeff_eq_of_critical_line_even_sublinear_defect` assumes a one-Gamma critical-line defect with polynomial pointwise bound, strip continuity/holomorphy/decay, and sublinear Abel L1 mass. Their source types were inspected. D1 counts missing multiplicities at xi zeros; neither the zeta-weighted mass of E's extra zeros nor the needed one-Gamma defect estimate follows from that count in the present argument. The quotient retains two Gamma factors, and critical-line placement of E zeros does not place every xi pole on that line. These receivers are therefore possible targets with explicit unpaid premises, not current applications or new theorems. The full-data C2/continuous-representative conjecture survives this attack.


### Actual inverted spatial pairing and constant term

Fix 0<a<=b, y>0 and a continuous test phi on [a,b]. Put z_y(x)=-1/(x+iy), d=x^2+y^2. Then Re(z_y)=-x/d and Im(z_y)=y/d. For a<=x<=b, d lies between a^2 and b^2+y^2, so the inverted height lies in the fixed positive strip [y/(b^2+y^2),y/a^2]. The existing polynomial-coefficient Bessel-series estimate supplies a summable sequence u_n bounding every actual mode on this strip. Consequently the integrals of |phi times mode_n| are bounded by u_n times the finite integral of |phi|, and sum/integral interchange is justified on the whole interval.

For each mode, (y/d)^(1/2)=y^(1/2)*d^(-1/2), and cosine is even. Dividing its tested integral by y^(1/2)*log(y) therefore gives exactly q(n+1) times inversionCosinePairing(phi,a,b,n+1,y). The full normalized inverted cosine-series integral is the sum already handled by InversionFourier. This proves actual spatial identification without an extra series-convergence premise.

The normalized constant term is exactly

    phi(x)*w_y(x)*(A + (B - A*log(d))/log(y)),  w_y=d^(-1/2).

On [a,b]x[0,1], w_y and log(d) are continuous and bounded, because d>=a^2>0. Both tested integrals H(y)=integral phi*w_y and J(y)=integral phi*w_y*log(d) therefore converge at y=0 by compact dominated convergence. In particular H(0)=integral phi/x; J has a finite limit. Since 1/log(y)->0 from positive y, A*H(y)+(B*H(y)-A*J(y))/log(y) tends to A*H(0). This retains the B term and the inversion logarithm before taking the limit. Adding four times the actual cosine-series limit proves the normalized inverted Maass spatial limit against phi. No deficit-density, boundary-continuity, or residue-series premise enters.

Finally the positive reciprocal substitution t=1/x gives integral phi(x)/x times cos(2*pi*k/x) over [a,b] equal to integral phi(1/t)/t times cos(2*pi*k*t) over [1/b,1/a]. Its Jacobian is t^-2, and the weight 1/x becomes t. A smooth phi supported strictly inside the positive interval gives a smooth compact transformed test Sphi(t)=phi(1/t)/t: it vanishes near zero and outside the reciprocal interval, while inversion is smooth away from zero. Thus the inverted boundary pairing is the existing B[Sphi]. This substitution and support assertion remain explicit Lean obligations until their checks finish.


### Sparse-boundary audit after spatial identification

The complete second search returned periodic spectrum rigidity with an entire function and a one-sided exponential expansion, and Bohr-spectrum periodicity with a global almost-periodicity premise. Neither hypothesis is supplied for the meromorphic E/xi quotient by D1(T)=o(T). The inspected WeilWorkDeficitProjection/ZeroTransport source controls the projection of all xi-zero copies and proves a fixed-frequency error divided by T tends to zero. That is a different deficit variable from missing multiplicity below one xi divisor. Even an analogous normalized estimate for D1 would erase a sublinear defect; it would not identify the unnormalized boundary distribution or produce local regularity. No application is claimed.

Miller–Schmid, Distributions and Analytic Continuation of Dirichlet Series, Proposition 5.37 and Theorem 4.8 (https://arxiv.org/pdf/math/0403030), require entire continuation with moderate growth on vertical strips for their infinite-order vanishing and Mellin inversion conclusion. The present quotient may have infinitely many poles. The original cubic data must still pay the cutoff-Mellin identification and a regularity/vanishing estimate; replacing that obligation by the cited entire-function theorem would be circular. C2 versus a complete sublinear-deficit counterdatum therefore remains SURVIVES PRELIMINARY ATTACK.


### C3: harmonic-deficit divergence (new open intermediate target)

Under exactly the complete cubic correspondence, conjecture that either lambda=Lambda (and RH), or the nonnegative family

    xiDeficit(E,rho) / (1 + |Im(rho)|),  rho in xiDeficitSupport(E),

is not summable. Competing conjecture: a nontrivial complete datum with summable reciprocal-height deficit mass exists. This strengthens the checked infinite-support alternative and is weaker than C2 positive upper linear density. The stronger sparsity assumption in its contrapositive is chosen to expose a possible absolutely convergent pole-clearing product; such a product by itself does not preserve an ordinary Dirichlet series, polynomial vertical growth, or the period identities. Those remain proof obligations. No paper proof or new Lean theorem of C3 exists at this checkpoint. Verdict: SURVIVES PRELIMINARY ATTACK; novelty UNESTABLISHED.

The deep reciprocal-height search was partial (reranking unfinished), and every returned candidate/source statement was screened. The inspected halfPoleWeight is the arithmetic comparison 1/(n-1)^2, not a xi-pole-height family. The inspected inverse deficit energy is a rational function of clipped shared spectral mass, not reciprocal height. The sharp reciprocal-sum theorem bounds producer Mobius coefficients, not E/xi principal parts. No retrieved result establishes C3 or refutes its complete-data competitor. Generated ingredient sets combining these unrelated reciprocals are inapplicable. Exact-string web searches did not locate a usable primary theorem; that is not an absence or novelty claim.

Next research cycle: construct the cutoff-Mellin identity for the actual endpoint-corrected distribution B - S*B without presuming an infinite residue expansion; then test C3 via the nonlinear period relation, retaining every pole order and all original data. Do not infer continuous boundary regularity from sparse pole locations alone. Keep C2 and the full assigned implication as the ultimate targets.

## Cutoff-Mellin receiver through a continuous primitive (2026-10-08)

This is a classical BRIDGE, not a proof of C2, C3, or scientific novelty. The comparison with Miller--Schmid's distributional Mellin theory is explicit; the advantage here is an absolutely convergent overlap derived from the original coefficients, without an infinite residue expansion. All statements in this section are paper proofs until their exact Lean audits are recorded.

Fix the original cubic datum and put q(n)=degreeTwoQuotientCoeff(g,n), n>=1. The already checked weighted coefficient theorem gives sum |q(n)| n^(-sigma)<infinity for every real sigma>1. Define

    F(x) = pi^(-2) sum_{n>=1} q(n)n^(-2) cos(2*pi*n*x),
    f(x) = F(x)-F(0).

Absolute uniform convergence proves continuity, boundedness, evenness and period one of F. For every smooth compact test phi, integration by parts twice in each cosine term gives

    integral F phi'' = -4 sum q(n) integral phi(x) cos(2*pi*n*x) dx.

The interchange is dominated by sum |q(n)|/n^2 times the integral of |phi''|. Consequently B[phi]=A integral phi+integral F phi'' is exactly the checked fourierBoundaryPairing, with no new distribution hypothesis. The constant F(0) may be subtracted in that formula because integral phi''=0.

### Absolute weighted integrability and exact Mellin overlap

For 0<alpha<2, let C(alpha)=integral_0^infinity (1-cos u)u^(-1-alpha)du. It is finite and positive: near zero use 0<=1-cos u<=u^2/2; at infinity use 1-cos u<=2. Positive dilation gives integral (1-cos(bx))x^(-1-alpha)dx=C(alpha)b^alpha for b>0. These facts are already in ConnesLevyKernelScaling and ConnesFractionalSymbolGrowth.

For 1<sigma<2, Tonelli and alpha=2-sigma give

    integral_0^infinity |f(x)| x^(sigma-3) dx
      <= pi^(-2) C(2-sigma)(2*pi)^(2-sigma)
         sum_{n>=1} |q(n)| n^(-sigma) < infinity.                 (P1)

In fact the same computation proves summability of the integrals of the absolute values of every weighted summand; it therefore pays complex sum/integral interchange. This is stronger than merely taking a pointwise limit at zero. For complex s with 1<Re(s)<2, put

    M(s)=(s-1)(s-2) integral_0^infinity f(x)x^(s-3)dx.

The scalar integral used here is

    integral_0^infinity (cos x-1)x^(s-3)dx
      = -pi/[2 Gamma(3-s) sin(pi*s/2)].                           (P2)

For completeness, set alpha=2-s, so 0<Re(alpha)<1. Insert the Euler--Laplace integral
x^(-1-alpha)=Gamma(1+alpha)^(-1) integral_0^infinity t^alpha exp(-tx)dt. Absolute Fubini is justified by integrating the absolute value: with r=Re(alpha), the nonnegative double integral is Gamma(1+r)C(r)<infinity, using the just proved convergence of C(r). The elementary Laplace cosine integral gives integral (1-cos x)exp(-tx)dx=1/[t(1+t^2)]. Substitute v=t^2; the remaining integral is one half of Euler's beta integral B(alpha/2,1-alpha/2), equal to pi/[2 sin(pi*alpha/2)]. Gamma(1+alpha) is nonzero in this half-plane. Since sin(pi*alpha/2)=sin(pi*s/2), this proves (P2) without a conditionally convergent cosine transform.

Dilation and (P1) now yield

    M(s) = -4(2*pi)^(-s) Gamma(s) cos(pi*s/2) Q(s)
         = -2 Gamma_R(s)/Gamma_R(1-s) Q(s)
         = -E(s)/[xi(s)s^2(s-1)^2 Gamma_R(s)Gamma_R(1-s)],         (P3)

where Q(s)=L(g,s)/zeta(s). The first equality uses Gamma recurrence and reflection in (P2); the second uses duplication and reflection; the third uses the exact original quotient-completion identity. At shared zeros the last expression denotes its meromorphic germ. On 0<Re(s)<1, the multiplier of E/xi in (P3) is analytic and nowhere zero. Thus its poles there are exactly deficits below one copy of xi, with their full orders retained.

### Smooth cutoffs and endpoint terms

Choose a smooth real cutoff chi on [0,infinity), equal to one on a neighborhood of zero and zero beyond a finite positive number. A sharp cut at an integer is inadmissible because B can be singular there. For 1<Re(s)<2 define

    N_chi(s)=A integral chi(x)x^(s-1)dx
             +integral f(x)[chi(x)x^(s-1)]''dx.

Its second integral is absolutely convergent by (P1). It is the limit of B tested against chi(x)x^(s-1) with a smooth lower cutoff at epsilon. To check the cutoff-derivative errors choose 1<sigma'<Re(s); on [epsilon,2epsilon] each derivative error is bounded by a fixed constant times epsilon^(Re(s)-sigma') times the (P1) integrable density |f(x)|x^(sigma'-3). All these errors tend to zero. The constant term tends by ordinary dominated convergence.

For any smooth tail cutoff psi, zero near zero and one beyond a finite number, define on Re(s)<2, s!=0,

    T_psi(s)=-(A/s) integral psi'(x)x^s dx
             +integral F(x)[psi(x)x^(s-1)]''dx.

The derivative of psi has compact support away from zero. The second integral converges because F is bounded and its tail weight is O(x^(Re(s)-3)); logarithmic derivatives in s are dominated on every compact subset of Re(s)<2. Thus T_psi is holomorphic there except a possible simple pole at s=0. For Re(s)<0 this equals the limit of the actual tested distribution with a smooth upper cutoff at R: the constant term is the ordinary integral, and all derivative-cutoff errors are O(R^(Re(s)-2)). It is therefore a genuine continuation of the tail distribution, not an assigned meromorphic answer.

For psi=1-chi, the A terms of N_chi+T_psi cancel by one integration by parts. Replacing F by f in the tail integral makes no change, since the integral of [psi x^(s-1)]'' is zero for Re(s)<2. The differentiated cutoff terms cancel exactly, proving

    N_chi(s)+T_(1-chi)(s)=M(s),  1<Re(s)<2.                       (P4)

Write Sphi(t)=phi(1/t)/t, the already checked reciprocal smooth test, and beta[phi]=B[phi]-B[Sphi] on (0,infinity). Under reciprocal substitution the lower-cutoff test for the second term is the upper-cutoff tail test chi(1/t)t^(-s). Since Re(1-s)<0 in the overlap, the genuine-tail result proves

    beta_chi(s)=M(s)-T_(1-chi)(s)-T_(chi composed with inv)(1-s).   (P5)

No higher periodic primitives or entire continuation of the tails are needed: both tail transforms in (P5) are holomorphic throughout 0<Re(s)<2 except possible endpoint poles at s=1 (and the boundary s=0).

### Local receiver, retaining the endpoint survivor

Suppose beta has a representative h on (0,a) and there exists c in C such that r(x)=h(x)-c/x satisfies

    integral_0^a |r(x)| x^(sigma-1)dx < infinity for every sigma>0. (P6)

Choose chi supported in this interval. The cutoff Mellin transform of r is holomorphic on Re(s)>0: on a compact substrip, powers of |log x| are absorbed by choosing a smaller positive sigma in (P6). The c/x term has a continuation with its only possible pole at s=1, obtained by integration by parts against chi'. Therefore beta_chi is holomorphic on 0<Re(s)<2 away from s=1. Equation (P5), initially on 1<Re(s)<2, analytically continues the meromorphic expression (P3) with no interior-strip pole. Every xi deficit vanishes. The already checked full-datum divisor-containment theorem then gives lambda=Lambda and RH.

In particular local boundedness of beta suffices (c=0), and the receiver also allows the exact endpoint survivor c(1-1/x). Only local regularity at zero is required; no global C1 representative, decay at infinity, finite pole set, residue-amplitude bound, or expansion over infinitely many residues is assumed in the receiver proof. Its original-data contrapositive is: a nontrivial datum forces failure of (P6) for every local representative and every endpoint coefficient c. This is an exact research target, not a derivation of (P6) from D1 sparsity. The first OPEN CORE for C2/C3 remains that derivation or an alternative argument exploiting the complete cubic parent.

### Current implementation boundary

First formalize F, the exact distributional second-primitive identity, and (P1) from original data. Next formalize (P2)--(P5) and the local receiver. The preceding paper proof is dependency-closed using Euler--Laplace, beta, Gamma reflection/duplication, complex dominated differentiation, and the already checked exact quotient/divisor theorems. Formal library availability is separate from paper validity. None of (P1)--(P6) is a new premise to be added to the original cubic-data definition. C2/C3 remain SURVIVES PRELIMINARY ATTACK; this receiver is BRIDGE / REDISCOVERED.

### Harmonic multiplier attack and next exact conjecture

The harmonic-deficit condition suggests clearing the sparse pole divisor with an entire multiplier and controlling its growth by a compactly supported smoothing factor. Bhowmik--Sen, arXiv:1606.02125, Theorem 1.1(a), states a classical existence criterion for compact smooth functions with a prescribed nondecreasing Fourier-decay weight whose logarithmic integral is finite. It supplies no ordinary-Dirichlet-series or modular-period preservation statement. No multiplier theorem is applied here, and no pole-product estimate is claimed as proved.

The unpaid step has a concrete geometric form: multiplication in the Mellin variable corresponds to averaging spatial dilations. Each frequency n then becomes nt as the dilation parameter t ranges through the smoothing support. The original exact integer-frequency periodicity and its three-term relation do not follow for that averaged object. Taking supports ever closer to one does not produce an approximate identity for free: a multiplier vanishing at a fixed deficit pole cannot converge there to the constant multiplier one. Thus the proposed reduction to the finite-pole theorem has no justified limit argument. This does not refute C3 or retire all multiplier approaches.

The next exact competing statements are now C4 and its negation. Here B uses q=degreeTwoQuotientCoeff g and the actual endpoint A=degreeTwoEndpointNumerator E 1. C4: under the complete original cubic correspondence and summable reciprocal-height one-xi deficits, there exist a>0, c in C and a measurable r on (0,a), with integral |r(x)|x^(sigma-1) finite for every sigma>0, such that for every smooth test supported compactly in (0,a),

    B[phi]-B[Sphi] = integral_0^a (c/x+r(x))*phi(x)dx.

The competitor is a complete nontrivial harmonic-thin datum whose actual defect has no such representation. C4 is an analytic mechanism for C3, not a new assumption to add to the cubic datum or a proved novelty claim. Its first OPEN CORE is this exact testwise identity with the weighted L1 estimates; sparse pole locations alone do not pay it. The cutoff receiver above explains why proving it would eliminate the harmonic-thin branch. Verdict: SURVIVES PRELIMINARY ATTACK; novelty UNESTABLISHED. The corpus's retrieved reciprocal-square zero sums, smooth-test Fourier decay, and arithmetic Ingham-density results do not establish this representation.

Formal checkpoint: BoundaryPrimitive and PrimitiveMellin now prove the continuous bounded second primitive, its exact distributional pairing, the absolute weighted overlap (P1), and its exact factorization as Q(s)*cosineDifferenceMellin(s)/pi^2. Both direct module checks and all eleven exported axiom audits pass. Gamma evaluation (P2), cutoff identity (P5), and the local receiver remain paper-only. C2, C3, C4 and full WP07 remain OPEN.

### Scalar evaluation on its natural complex strip

The (P2) proof in fact works for every complex alpha with 0<Re(alpha)<2. This is the natural absolute-convergence strip, already consistent with the cosine kernel bounds and the classical fractional-Laplacian normalization (Pagnini--Runfola, arXiv:2305.04251, equation (1.5)); it is not a stronger new classification conjecture. Set

    J(alpha)=integral_0^infinity (1-cos x)x^(-1-alpha)dx,
    H_alpha(t,x)=t^alpha exp(-t*x)(1-cos x).

Every slice in t is absolutely integrable by the scaled Euler integral at 1+alpha. Its integrated norm is Gamma(1+Re(alpha)) times (1-cos x)x^(-1-Re(alpha)), an integrable Connes kernel. Joint measurability follows from continuity on the positive quadrant. Hence H_alpha is product-integrable and Fubini applies with no formal iterated-integral shortcut. Integrating t first gives Gamma(1+alpha)J(alpha). Integrating x first gives integral t^(alpha-1)/(1+t^2), because the exact exponential-minus-cosine Laplace transform is 1/[t(1+t^2)]. All reordering and power identities use t,x>0.

The square substitution, equivalently Mellin scaling by t^2, gives this last integral as one half of integral v^(alpha/2-1)/(1+v). The checked half-line beta kernel and Gamma reflection give pi/[2 sin(pi*alpha/2)]. Since Gamma(1+alpha) is nonzero on this strip, division yields J(alpha)=pi/[2 Gamma(1+alpha)sin(pi*alpha/2)]. This proves the desired complex formula with all convergence obligations, not merely its real specialization. Put alpha=2-s and dilate by 2*pi to evaluate the exact cosineDifferenceMellin used by the current original-data capstone. The actual quotient formula is still restricted to 1<Re(s)<2 by its given Dirichlet convergence.

This proof is dependency-closed on paper. C4's sparse-deficit-to-regularity step remains the OPEN CORE; no scalar integral identity implies it. Formalization must prove product integrability and retain the actual kernel normalization.

The scalar factor for the actual normalized primitive is

\[
 A(s)=-\frac{(2\pi)^{2-s}}{2\pi\,\Gamma(3-s)\sin(\pi(2-s)/2)}.
\]

It is nonzero throughout `0 < Re(s) < 2`: the positive-real base power never
vanishes, `Re(3-s)>1` makes Gamma finite and nonzero, and with
`w=(2-s)/2` both `Re(w)` and `Re(1-w)` are positive. Euler reflection then
forces `sin(pi*w) != 0`. Thus this scalar evaluation introduces no hidden
zeros capable of cancelling the actual quotient's poles in the interior
critical strip. This is a classical normalization fact, not the missing
C4 local-regularity assertion. The actual absolute Mellin identity remains
restricted to `1 < Re(s) < 2`, where its coefficient summability is proved.

The same factor is holomorphic on that strip: the constant positive-base power
is entire; Gamma is holomorphic at `3-s` with positive real part; the sine is
entire; and the denominator is nowhere zero by the preceding argument.

### A weaker local receiver: a power exponent above one half

This is a paper receiver, not a derivation from sparse deficits and not a claim
of scientific novelty. It refines the checked C1 telescoping argument in
`WeilWorkHigherDenominatorPeriodDefect.lean`.

Let a locally integrable representative `q` of the actual defect after
subtracting `c(1-1/x)` satisfy the weight-one three-term and odd-inversion
identities pointwise, tend to zero at infinity, and obey

`|q(t)| <= C (1-t)^delta` for `1/2 <= t <= 1`,

where `C >= 0` and `0 < delta <= 1`. For `x >= 1`, the three-term identity gives

`|q(x)-q(x+1)| <= C (x+1)^(-1-delta)`.

Telescoping to `x+N`, letting `N` tend to infinity, and comparing the decreasing
power series with its integral gives

`|q(x)| <= (C/delta) x^(-delta)`.

Odd inversion therefore gives

`|q(x)| <= (C/delta) x^(delta-1)` for `0 < x <= 1`.

Every origin Mellin integral is consequently absolutely convergent and
holomorphic on `Re(s) > 1-delta`. Holomorphy follows on compact substrips by
choosing a strictly smaller real exponent and absorbing every logarithmic
factor into the resulting power margin. The previously recorded cutoff-tail
identity, applied to this actual representative, continues the normalized
primitive transform there, up to the retained endpoint term. Its factor
relative to `E/xi` is holomorphic and nonzero in `0 < Re(s) < 1`: the factor
proved above is nonzero, the polynomial factors have only endpoint zeros,
and Gamma_R(s) is finite and nonzero for positive real part.

If `delta > 1/2`, this removes every deficit pole with `Re(s) >= 1/2`.
Reflection of both E and xi removes the remaining poles. Thus the existing
original-data multiplicity receiver yields lambda=vonMangoldt and RH. At
`delta=1/2` this argument only removes poles strictly right of the line;
reflection and the original critical-line condition on E would force RH,
but this argument does not remove central multiplicity deficits. This is
an integrability threshold for this proof, not a sharpness theorem about
realizable complete data. The receiver is not yet formalized.

### Smooth upper Mellin tails: dependency-closed implementation proof

Let F be the bounded continuous primitive already proved from the original
cubic datum. Choose a smooth complex-valued cutoff psi, zero on x<a for some
a>0 and one on x>b. Continuity bounds psi on [a,b]; its plateaus bound it
globally. Every positive derivative vanishes off [a,b], hence is bounded
and has compact support away from zero. In particular, F psi is continuous,
bounded and zero near zero; F psi' and F psi'' are continuous and zero near
both endpoints of (0,infinity).

For any continuous bounded h vanishing near zero, Mellin(h,z) converges and
is holomorphic for Re(z)<0: its tail is bounded by a constant times
x^(Re(z)-1), and its origin part vanishes. If h also vanishes near infinity,
its Mellin transform is entire. On compact parameter sets one chooses strict
power margins at both ends; logarithmic derivatives are absorbed by these
margins. These are exactly the hypotheses of Mathlib's Mellin big-O theorem.

Define the upper tail by its actual convergent second-primitive integral

T_psi(s) = -(A/s) integral_0^infinity psi'(x) x^s dx
           + integral_0^infinity F(x) (psi(x) x^(s-1))'' dx.

For x>0 the ordinary real second derivative equals

psi''(x) x^(s-1) + 2(s-1) psi'(x) x^(s-2)
                  + (s-1)(s-2) psi(x) x^(s-3).

Each summand is absolutely integrable for Re(s)<2, by the preceding bounds.
Thus the integral is exactly

-(A/s) Mellin(psi',s+1)
 + Mellin(F psi'',s)
 + 2(s-1) Mellin(F psi',s-1)
 + (s-1)(s-2) Mellin(F psi,s-2).

The first three Mellin factors are entire; the fourth is holomorphic on
Re(s)<2. Consequently T_psi is holomorphic there away from s=0.
No divisor count, pole-amplitude bound or boundary regularity is used.
The explicit psi(x)=smoothTransition(x-1) pays all cutoff hypotheses and
the original datum pays every hypothesis on F. The formal capstone must
identify this expansion with the displayed derivative integral, rather than
merely assign an analytic function the name 'tail'. The cutoff/inversion
identity P5 and the actual distributional upper-cutoff limit remain separate
obligations until checked. This is a classical analytic bridge, not C5.

Receiver dependency refinement: the scalar A(s) of PrimitiveGamma is already
analytic and nonzero on 0<Re(s)<2. Once P5 identifies the actual cutoff
defect with the regularized primitive transform, local regularity can be
transported to the quotient using (s-1)(s-2)A(s), which is nonzero throughout
the interior critical strip. Completion then transfers removability to the
E-versus-xi multiplicity comparison. A second closed-form Gamma_R evaluation
of the boundary transform is not needed for this receiver. The exact
completion identity and analytic continuation still require formal checking;
no new scalar normalization or multiplicity theorem is claimed here.

### Cutoff overlap and actual truncations: implementation proof

The C5 almost-positive subtraction attack does not close. The corpus's
half-integer receiver requires a positive atomic representation on the
critical line; a summable negative divisor does not supply it, and off-line
xi zeros cannot be converted into real measure atoms by assuming RH.
Booker's multiplicity-one condition bounds the total absolute spectral
mass by o(T), not only its negative part. The degree-two remainder still
has an uncontrolled positive part. C5 remains SURVIVES PRELIMINARY ATTACK.
No regularity hypothesis is added to an original-data theorem.

Fix any already defined smooth upper cutoff psi. For Re(s)>0,
chi=1-psi is bounded, vanishes at infinity, and

  integral chi(x)x^(s-1) dx = (1/s) integral psi'(x)x^s dx.

Indeed, (chi x^s)'=-psi' x^s+s chi x^(s-1); both summands are
integrable. The antiderivative vanishes at infinity by the cutoff and
at zero because Re(s)>0. The fundamental theorem on (0,infinity) gives
the equality, including its sign.

For Re(s)<2, the integral of (psi x^(s-1))'' is zero. Its first
derivative vanishes near zero. At infinity it is (s-1)x^(s-2),
which tends to zero. Absolute convergence follows from the checked
second-derivative tail theorem with F=1. Thus adding a constant to F
does not change the second-derivative tail integral.

For the actual f=F-F(0), differentiating
chi x^(s-1)+psi x^(s-1)=x^(s-1) twice on x>0 gives

  f (chi x^(s-1))'' = (s-1)(s-2)f x^(s-3) - f (psi x^(s-1))''.

Both right-hand terms are absolutely integrable on 1<Re(s)<2,
by P1 and the checked bounded-tail theorem. This pays the lower
integral and, together with the preceding scalar endpoint identities,
proves P4 with the actual primitive and its full quotient multiplier.

For P5 use smooth lower truncations eta_R(x)=psi(R*x), R>0, R->infinity.
For each fixed positive x the positive derivatives eventually vanish
and eta_R(x) eventually equals one. For j=0,1,2,

  |x^j eta_R^(j)(x)| <= C_j

uniformly in R,x>0. For j>0 this is the compact-support bound for
|(R*x)^j psi^(j)(R*x)|; j=0 uses boundedness of psi. Each shrinking
transition error in the second derivative is therefore bounded by a
fixed multiple of |f(x)|x^(Re(s)-3). P1 at the same Re(s), without
a stronger exponent, gives dominated convergence. The constant term
uses integrability of chi x^(s-1). These truncations are actual smooth
compact tests, supported away from zero.

Their reciprocal tests are exactly chi(1/t) psi(R/t) t^(-s). Extend
chi(1/t) by zero on t<=0 when using a globally smooth cutoff. On
positive t it vanishes near zero and equals one near infinity. Its
upper truncation psi(R/t) has uniformly bounded logarithmic jets and
converges pointwise with its first two derivatives to one. For Re(s)>1,
the constant part is integrable at infinity; boundedness of F controls
the second-derivative part by a multiple of t^(-Re(s)-2), with a fixed
origin buffer. Dominated convergence identifies the actual reciprocal
pairing limit with the checked tail at 1-s. Subtracting these two
actual pairing limits and P4 proves P5. No infinite residue expansion
or local representative is used. Every claimed equality here is on
its stated convergence strip; continuation beyond it is a later step.


### All-order cutoff survivor and remaining assembly

The same envelope argument holds for every derivative order n, not only 0,1,2. For n>0, psi^(n) vanishes outside a compact transition interval, so x^n psi^(n)(x) is bounded; for n=0 use boundedness of psi. The chain rule gives x^n D^n[psi(Rx)] = (Rx)^n psi^(n)(Rx). For each x>0, psi(Ry) is identically one on a neighborhood of x once R is sufficiently large. Thus its zeroth jet is eventually one and every positive jet eventually zero. Multiplication by any absolutely integrable G gives the common majorant C_n |G| and dominated convergence. This is dependency-closed ordinary cutoff analysis and REDISCOVERED / BRIDGE, not scientific novelty. The exact all-order statement is now checked in CutoffJets.

P4 is checked for the original datum in CutoffOverlap. The actual lower product-rule assembly is now checked in CutoffHead, and the reciprocal upper-test limit in CutoffReciprocity. CutoffDefect combines them into the full P5 compact-test identity on 1<Re(s)<2. These are limits of actual compact-test pairings, not an assignment of head and tail transforms. Analytic continuation beyond that strip, a local representative, and C5 remain separate obligations.


### Actual lower compact-test limit: dependency-closed assembly

Write chi=1−psi, eta_R(x)=psi(Rx), f=F−F(0), w(x)=chi(x)x^(s−1), and a=(s−1). Assume only the proved bounds on the actual continuous bounded primitive, its Mellin integrability on 1<Re(s)<2, and ordinary smooth cutoff geometry. Set

G0=f*w'',
G1=2[-f*psi'*x^(s−2)+(s−1)chi*f*x^(s−3)],
G2=chi*f*x^(s−3).

G0 is integrable by checked P4. G2 is the full primitive Mellin integrand minus its upper cutoff part; both are integrable by P1 and the bounded-tail theorem. The first summand of G1 has compactly supported psi' away from zero, and the second is a scalar multiple of G2. Thus all three weights are absolutely integrable on the positive half-line. The ordinary product rule and x*x^(s−3)=x^(s−2), x²*x^(s−3)=x^(s−1) give exactly

f*(w eta_R)'' = G0*eta_R + G1*(x eta_R') + G2*(x² eta_R'').

The checked all-order jet integral theorem gives limits integral G0, 0, 0, respectively. The constant term follows from the same theorem with n=0 and G=w, which is integrable for Re(s)>0. For R>0, w eta_R is smooth on the entire line, supported in a compact positive interval: eta_R gives an origin buffer, and chi an upper buffer. Its second derivative has integral zero, by the fundamental theorem of calculus applied to its compactly supported first derivative (equivalently the already checked zero-frequency cosine derivative identity). Hence F can be replaced by f in the exact Fourier-boundary pairing. All full-line integrals equal their positive-half-line versions because the tests and their derivatives vanish near the nonpositive half-line. Therefore the actual FourierBoundaryPairing on these compact tests tends to primitiveMellinHead(F,A,psi,s). This proves the lower-test part of P5 without assigning it by definition; the reciprocal-test part remains separate.


### C6: a thin-pole converse without zero confinement (OPEN)

Given the exact internal and external frontier, test a genuinely stronger source-class conjecture. For every g:N->C and E:C->C satisfying ZetaPowerDatum 3 g E, g(1)=1 and E(1)!=0, suppose the family xiDeficit(E,rho)/(1+|Im rho|), indexed by xiDeficitSupport(E), is summable. Then conjecture LSeries g s = riemannZeta(s)^3 for every Re(s)>1. Do not assume critical-line confinement of E's zeros, real lambda, a logarithmic-derivative identity, Euler product, multiplicativity, or coefficient signs. The exact competing statement is a normalized datum of this larger class with the indicated summable deficit and a different Dirichlet series.

This strengthens C3's analytic content and is not being substituted for the assigned target. Truth would show the analytic Dirichlet/functional-equation structure already excludes thin defects; falsity would identify a reason to use the complete correspondence's currently unused zero-confinement or real-logarithmic-derivative hypotheses. The original-data implication then remains to be checked through the existing correspondence, rather than assumed. First OPEN CORE: proving the actual modular defect has enough local regularity, or constructing a nontrivial thin-pole datum in this larger class. The cutoff identity does not prove this regularity. C6 is a conjecture only, with no paper proof or Lean claim; its novelty is UNESTABLISHED. Search and applicability audit follows in EVIDENCE.md.

### Reciprocal-cutoff assembly — paper obligations before repository Lean

Let ψ be a smooth tail cutoff and put ψ∨(x)=1−ψ(1/x) for x>0,
and ψ∨(x)=0 otherwise. If ψ=1 above b, choose B>max(b,0).
Then ψ∨ vanishes for x<1/B. If ψ=0 below a>0, ψ∨=1 above 1/a.
These buffers and ordinary inversion on x>0 prove ψ∨ is again a smooth tail cutoff.

For n≥0 put K_n(R,x)=(R/x)^n ψ^(n)(R/x). Every K_n is uniformly
bounded, because the logarithmic jets u^n ψ^(n)(u) are bounded. For fixed
x>0, K_0 tends to 1 and K_n tends to 0 for n>0; in fact the values are
eventually constant. Dominated convergence applies against every integrable
G on (0,∞), independently of any pole hypothesis.

For η_R(x)=ψ(R/x), xη'_R=−K_1 and x²η''_R=K_2+2K_1.
Write a=1−s, χ=ψ∨ and w=χ x^(a−1). For positive x the actual reciprocal
head test is wη_R. Its primitive integrand is exactly

    F(wη_R)'' = (Fw'')K_0 + 2(Fw/x²−Fw'/x)K_1 + (Fw/x²)K_2.

For bounded continuous F and Re(a)<0 all three weights are integrable:
cutoff derivatives have compact support away from zero, while each remaining
term is a bounded function times χ x^(a−3). The scalar weight w is also
integrable. The limit is therefore A∫w+∫Fw''. Integration by parts in
χ x^a (zero at both endpoints) gives ∫w=−a⁻¹∫χ' x^a, so this is exactly
primitiveMellinTail(F,A,χ,a). Smoothness, compact support and the origin
buffer of each reciprocal test follow from the previously proved reciprocal
transport. The actual primitive pairing may use F rather than F−F(0), since
the compact test's second derivative has integral zero.

These identities prove the reciprocal half of P5 on paper. Each advertised
formal conclusion remains limited to the exact modules that pass Lean.
No regularity conclusion for the infinite-pole defect follows yet.

### C6 preliminary applicability verdict

Deep search `degree two meromorphic converse harmonically summable poles finite
order Dirichlet gamma functional equation` returned existing finite-pole
clearing/contour machinery and unrelated meromorphic-order results. The
proposed gap-of-divisor-coefficients transfer presupposes the ζ² coefficient
system; it cannot identify our unknown quotient. The proposed pole-order
ingredient chain supplies local orders but not global thin-pole rigidity.
Neururer–Oliver Theorem 1.1 (arXiv:1809.06586, version 4) requires twisted
functional equations, a polynomial clearing the untwisted poles, stronger
coefficient growth, and ν≠0. The present quotient has ν=0 and none of the
first two inputs. Burnol's Hamburger extension also uses finitely many poles
and a one-gamma functional equation. No source checked here resolves C6.
Verdict: SURVIVES PRELIMINARY ATTACK; novelty UNESTABLISHED. This is not an
absence theorem or a proof. No WP07 route is retired.

Reciprocal implementation simplification: for R>0, x>0 and χ=ψ∨,
ψ(R/x)=1−χ(x/R). Thus the actual reciprocal test equals
χ(x)(1−χ(x/R))x^(−s). Use ordinary dilation by R⁻¹, followed by the
origin buffer, instead of differentiating inversion twice. Its logarithmic
jets are uniformly bounded by the already checked dilation bound; every jet
of χ(x/R), including order zero, eventually vanishes at each positive x.
This proves the same dominated limits with fewer chain-rule obligations.

### Pressure test for a direct distributional replacement of C5

The corpus already proves both weight-one identities for the coboundary of
any even one-periodic function. Taking f(x)=cos(2πx) gives
q(x)=cos(2πx)−x⁻¹cos(2π/x). It is smooth at every positive x and vanishes
linearly at x=1, yet is not zero: along positive integers n it tends to 1,
while along n+1/2 it tends to −1. Thus the two identities and local regularity
at 1 alone cannot replace the global decay/analytic restrictions. This is
an elementary instance of the existing coboundary construction, not new
scientific knowledge or a counterdatum to C5/C6. No full cubic datum has
been supplied by this example. Any direct sparse-spectrum proof must retain
and use the global degree-two analytic structure, rather than infer rigidity
from the modular algebra alone.

### Post-P5 audit and C7: pointwise coefficient decay

This scientific cycle is STALLED. C6 has neither a proof nor a full counterdatum.
The attempted primitive-packet mean-square argument is REDISCOVERED: the exact
stronger result is already `WeilMeanSquare.exists_sum_sq_div_le_of_primitive`
in `WeilPrimitiveSetMeanSquare.lean`. For every primitive S contained in [2,N],
it gives sum_S lambda(n)^2/n <= (log N+C0)^2. Dyadic summation gives
sum_(2<=n<=X) lambda(n)^2/n = O((1+log X)^3). This already supplies Booker's
square-prefix condition for f(n)=3 lambda(n)/sqrt(n), for the original positive
source. EVIDENCE.md and WP03 had already recorded this deduction. It is not
new knowledge and must not be proposed again as a research theorem.

The pointwise part of Booker's A1 remains distinct. New conjecture C7:
for every complete datum of the assigned correspondence (ZetaPowerDatum 3 g E,
g(1)=1, E(1)!=0, all E zeros on Re=1/2, real lambda absolutely summable with
weight n^(-sigma) for every sigma>1, and
LSeries g' = -3 LSeries(lamC lambda) LSeries g on Re>1), one has

    for every integer K>=1 there exists C_K>=0 such that, for every n>=2,
    |3 lambda(n)/sqrt(n)| * (log n)^K <= C_K.

Here `LSeries g'` means the derivative in the complex argument of LSeries g,
not the Dirichlet series of a differentiated coefficient function. No Euler
product, coefficient signs, harmonic-thin divisor, or additional regularity
is assumed. The exact competitor is a complete datum in this same class and
an integer K>=1 for which the displayed sequence is unbounded. C7 is weaker
than the assigned rigidity conclusion, and is a separate test of how the
zero confinement and real logarithmic derivative can help; C6 omits them.
Verdict: SURVIVES PRELIMINARY ATTACK; novelty UNESTABLISHED. No paper proof or
Lean theorem is claimed.

The first attack must go beyond extracted logarithmic Toeplitz ceilings.
WP03 already has an unconditional sparse prime-supported witness satisfying
every such ceiling and a log-squared square-prefix bound. Its construction
has lambda(p_j)/sqrt(p_j)=((j+1)/(j+2))*log p_j, with p_j strictly increasing.
Thus even these all-cutoff bounds allow pointwise spikes growing like log p_j.
The exact source and capstone `exists_sharp_prime_supported_toeplitz_weight`
in `WeilWorkSingularArithmeticToeplitzSharpness.lean` were inspected. This is
a countermodel only to the relaxation, not to full Weil positivity or C7.
Do not rebuild this example or infer a full datum from it.

C7 would pay only the missing pointwise coefficient condition. It would not
turn infinitely many harmonic-thin negative spectral weights into Booker's
finite-negative condition, nor remove the two archimedean copies in E/xi.
C2--C6 and WP07 remain OPEN. The next cycle should attack C7 directly through
the full cubic completion, while retaining C6 as the analytic alternative;
another general finite-pole or mean-square survey is not progress.

### C7 growth and quantization attack — 2026-10-08

Verdict: **STALLED**. C7 still SURVIVES PRELIMINARY ATTACK; no new proof,
counterdatum, or scientific-novelty claim. The paper-proof gate has not passed,
so no Lean implementation follows from this cycle.

The actual `exists_producerZeta_subpolynomial_of_weilPositiveFull` statement
was inspected. It already supplies upper and lower subpolynomial vertical
growth on every fixed half-plane Re(s)>=1/2+delta, for every full-positive
producer. The proof passes through a logarithmic continuation bounded by
C(log(|t|+3))^theta with theta<1. No coefficient extraction argument giving
C7's rapid logarithmic decay has been established. In contrast,
`exists_re_producerLogZeta_le_littlewood` explicitly assumes
|lambda(n)|<=kappa log n; importing that theorem does not derive its premise.
Neither observation proves that C7 is false or independent of the full datum.

Later source correction: `WeilWorkSettledPhaseLittlewood` now supplies
`exists_re_producerLogZeta_le_littlewood_full` from full positivity alone.
The coefficient hypothesis belongs to the older theorem, not every
Littlewood bound in the current corpus. Its source was directly Lean-checked
in the intermediate-multiplicity cycle below. C7's coefficient-extraction
step remains unproved even with this stronger growth theorem.

The proposed integer-spectrum shortcut also fails as a theorem import.
Favorov's entire-function result requires entire almost periodic functions
of exponential growth and a linear bound for the total variation of the
logarithmic Fourier coefficients. The quoted Meyer theorem requires finitely
many possible atom weights and linear Fourier total variation. Integer
multiplicities alone supply neither condition. The original completion's
archimedean contribution cannot be discarded to manufacture a pure-point
Fourier quasicrystal. The recent unbounded-density unit-mass example has an
additional delta-double-prime Fourier term, unrelated spectrum and different
counting growth; it is not a cubic counterdatum. Exact sources are in EVIDENCE.

Central nonvanishing and positive functional-equation sign are REDISCOVERED:
they are already our checked CentralExclusion result above. The sparse-Mellin,
Fabry-gap and nonlinear-change-of-variable direction also repeats recorded
queries; no admissible spectral synthesis or regularity implication was found.
These observations close neither C7 nor C3 and do not retire either route.

Next concrete target returns to C3 with its exact competitor: a nontrivial
complete cubic datum whose one-xi deficits have finite harmonic sum. Use the
already checked `xiRelativeLogDeriv_residue` and
`xiLogResidue_negativePart`: negative logarithmic residues are precisely the
integer deficit weights. This avoids confusing those weights with the
uncontrolled Laurent amplitudes of E/xi. **[OPEN CORE]** turn harmonic control
of this negative logarithmic divisor, together with the exact right-half-plane
identity retaining TWO archimedean copies, into elimination of the divisor.
No such implication is currently proved. A coefficient-size theorem, a local
regularity assumption, or another generic converse survey is not a substitute.

### C3 negative-divisor audit and its actual first primitive — 2026-10-08

Verdict for C3: **SURVIVES PRELIMINARY ATTACK**; this cycle is **STALLED**
scientifically. The logarithmic residue formula retains two archimedean
copies. The singular-deficit envelope compares mu_lambda with mu_xi, whereas
this problem compares 3 mu_lambda with ONE mu_xi. Arithmetic summable-deficit
rigidity concerns coefficients indexed by integers, not these zero heights.
Neither theorem supplies the missing estimate.

The following elementary paper calculation isolates exactly what harmonic
summability does provide. It is **BRIDGE / REDISCOVERED**, not C3 or a new
scientific theorem. Sum over distinct xi zeros rho, put
d_rho=max(ord_rho(xi)-ord_rho(E),0), t_rho=Im(rho), and
gamma_rho=(rho-1/2)/i. In the hypothetical harmonic-thin branch,
S=sum d_rho/(1+|t_rho|)<infinity. Define

    J(x) = sum_rho d_rho * (exp(i gamma_rho x)-1)/(i gamma_rho),

with the summand's continuous value x when gamma_rho=0. The zero set is
locally finite and |Im(gamma_rho)|<1/2. For |x|<=L and |t_rho|>=1,
the absolute value of the summand is at most
2*(exp(L/2)+1)*d_rho/(1+|t_rho|). The remaining finitely many terms are
continuous. The Weierstrass test therefore gives a continuous J on the real
line with J(0)=0 and locally uniform convergence of its defining series.
More precisely, for T>=1 its omitted |t_rho|>T tail is uniformly bounded on
[-L,L] by 2*(exp(L/2)+1) times the corresponding tail of S.

For a smooth compactly supported test phi, termwise integration against phi'
is legitimate by that same majorant. Integration by parts in each term gives

    -integral J(x) phi'(x) dx
      = sum_rho d_rho * integral exp(i gamma_rho x) phi(x) dx.

The series on the right converges absolutely: its term equals minus the
integral of the primitive summand against phi', whose absolute integrals
have a summable bound. Thus J is a distributional first primitive of the
negative logarithmic divisor's exponential sum. Pointwise differentiation
of the series is neither asserted nor used.

This calculation provides continuity, with no proved Lipschitz or positive
Holder exponent. J is not the second arithmetic Fourier primitive of Q,
nor the actual period defect of E/xi. Passing from the logarithmic divisor
to that linear quotient remains nonlinear and unpaid. In particular the
calculation cannot be inserted into the existing cutoff-Mellin receiver.

Vedana's September 2026 strip classification represents signed measures
using a difference of generalized Nevanlinna functions. Membership in that
difference does not assert finite negative index of the resulting function.
Burnol's extended Hamburger theorem still assumes finitely many poles.
Neither theorem turns the above weighted tail bound into finite support.
No route is retired, no full counterdatum is supplied, and no new Lean
module is justified by a completed proof of C3. **[OPEN CORE]** exploit the
full cubic arithmetic identity to eliminate a nonempty harmonic-thin
negative divisor; the continuous primitive alone does not do this.

### Arithmetic splitting and deformation re-audit — 2026-10-08

Scientific verdict: **STALLED / NO PROGRESS**. C3 and its complete-data
counterexample alternative remain open. No proof of C3 passes the paper gate.

The explicit formula controls the signed divisor of E/xi. It does not give
the same Fourier identity separately for its positive and negative parts.
Subtracting one xi leaves two archimedean copies; subtracting three would
change the deficit being counted. The positive-measure gap theorems inspected
in this cycle therefore have no admissible input yet. No claim that such an
input cannot be constructed is made.

An attempted polynomial/analytic deformation conjecture repeats
L273/L301/L387/L394 in
`docs/drafts/pipeline/1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`.
The previous warning at this file's local-deformation audit remains valid:
analytic-path exclusion does not establish isolation in the whole
infinite-dimensional space. A finite-dimensional compactness repair would
still exclude only a proper subclass. Do not present that repair as a new
global classification or spend the next cycle formalizing it as frontier
progress.

For precision, the proposed repair's local calculation was as follows. If
f_n=f_0+epsilon_n h_n, h_n tends locally uniformly to h, and the M zeros
alpha_(j,n) near an M-fold zero of f_0 are real, the argument-principle
moments p_(l,n)=sum_j alpha_(j,n)^l satisfy p_(2,n)=O(epsilon_n).
Consequently |p_(l,n)|<=p_(2,n)^(l/2)=o(epsilon_n) for l>=3. The linearized
contour integral then forces h/f_0 to have pole order at most two there.
At a zero of xi of multiplicity m, f_0=(2xi)^3 has M=3m, giving
ord(h)>=3m-2>=m. This is the existing divisibility mechanism. Turning
arbitrary approaching data into a nonzero limiting h needs compactness of
their normalized directions; it is available in a fixed finite-dimensional
space, not established for the full class. No new theorem is claimed here.

The degree-two receiver does not introduce a critical-zero premise:
`MaassZetaSquaredConverse.coeff_eq_divisorCount_of_functional_equation`
uses entireness, its functional equation, Dirichlet summability, normalization,
and a strip bound. The checked quotient-growth and polynomial-strip results
are relevant to a divisible tangent. They do not make a nondivisible actual
E/xi entire, nor supply the missing normalized-direction compactness.

The asymmetric-zero literature inspected here does not remove these gaps.
Its equal-degree or arithmetic-independence hypotheses cannot be applied
to xi versus the unrestricted cubic completion. Comparing xi^3 instead
again changes the threshold from one copy to three. Infinite-order
pole-clearing remains unpaid as well: an Euler-differential multiplier
does not automatically preserve the period-one translation law.

Next entry point: retain C3 versus a nontrivial complete datum with finite
one-xi harmonic deficit. Work on a concrete estimate for the full signed
arithmetic identity before requesting another generic gap, deformation,
or finite-pole survey. No added coefficient, regularity, residue-amplitude,
Euler-product, RH, or compactness premise may enter the capstone.

### Positive tail annihilators and their arithmetic obstruction — 2026-10-08

C3 remains **OPEN**. The following is a classical analytic bridge, not a
new scientific rigidity theorem. It repairs one specific limitation of the
earlier multiplier attempt: a filter that kills only an escaping tail can
converge to one on compact sets. The claim that its output is still an
ordinary-Dirichlet datum is **FALSE**. General multiplier/stability approaches
are not retired, and no new original-data capstone is claimed.

Work in C3's hypothetical branch. For each distinct xi zero rho write
delta_rho=Re(rho)-1/2, t_rho=Im(rho), and d_rho=xiDeficit(E,rho).
Fix T>=1 and keep only |t_rho|>T with d_rho>0. Put

    a_rho = pi/|t_rho|,
    c_rho = cosh(a_rho*delta_rho),
    nu_rho = c_rho/(1+c_rho) delta_0
             + 1/(2*(1+c_rho)) (delta_(a_rho)+delta_(-a_rho)).

Here delta_x on the right denotes a Dirac measure. Every nu_rho is a
symmetric probability measure. Its bilateral Laplace transform is

    k_rho(z) = (c_rho+cosh(a_rho*z))/(1+c_rho).

Since a_rho*t_rho is pi or -pi, k_rho(delta_rho+i*t_rho)=0.
Evenness and real coefficients also give the reflected zeros. Repeat the
factor d_rho times; no simplicity assumption is needed. A critical-line
zero actually gives a double zero of the factor, which is harmless.

Define

    R_T = pi * sum_(|t_rho|>T) d_rho/|t_rho|.

The harmonic assumption makes R_T finite and tending to zero: for |t|>=1,
1/|t|<=2/(1+|t|). The distinct zero set is countable and locally finite.
On the countable product of the three-point probability spaces, the sum of
the coordinate values converges uniformly, because their absolute values
sum to at most R_T. Its law nu_T is thus a symmetric probability measure
supported on [-R_T,R_T]. This constructs the infinite convolution directly;
no infinite residue expansion or quotient-residue bound enters.

Let K_T(z)=integral exp(z*u) dnu_T(u). Compact support proves entireness by
dominated differentiation on each compact z-set. Uniform convergence of
the coordinate sums and boundedness of the integrands on compact z-sets
give the product formula K_T=product k_rho^d_rho. Separating any one factor
as a convolution proves the required zero order without division by an
infinite product. Also K_T(0)=1, so K_T is not identically zero.

The first moment is zero. Independence and uniform bounded convergence give

    v_T = integral u^2 dnu_T(u)
        = sum_(|t_rho|>T) d_rho*a_rho^2/(1+c_rho)
        <= (pi^2/2) sum_(|t_rho|>T) d_rho/t_rho^2
        <= pi*R_T/(2*T).

The integral Taylor remainder for exp(z*u), with its linear term integrating
to zero, therefore yields

    |K_T(z)| <= exp(R_T*|Re(z)|),
    |K_T(z)-1| <= (|z|^2/2)*exp(R_T*|Re(z)|)*v_T.

In particular K_T tends locally uniformly to one, and is uniformly bounded
on each fixed vertical strip. Multiplying E(s)/xi(s) by K_T(s-1/2) cancels
every tail deficit pole with its multiplicity. Only the finitely many head
poles remain. The multiplier is even about 1/2, so it preserves the plus
functional equation. It has finite exponential type. These statements do
not identify the product as an ordinary Dirichlet series or make its
associated spatial function periodic.

That missing arithmetic assertion fails directly. Suppose the tail is
nonempty. Then v_T>0, so nu_T is not delta_0. Symmetry gives some b>0 and
p>0 with nu_T([b,R_T])=p. For real r>=0, positivity gives

    K_T(r) >= p*exp(b*r).

For the normalized original datum, Q(s)=L_g(s)/zeta(s) tends to one as real
s tends to infinity. Thus |K_T(s-1/2)*Q(s)| tends to infinity. In contrast,
every ordinary Dirichlet series absolutely convergent in a right half-plane
tends to its finite first coefficient along this ray, by dominated
convergence. Consequently the filtered quotient has no such representation.
The same proof classifies all symmetric compactly supported probability
filters that can preserve this representation for a function tending to
one: only delta_0 can do so. This is a classical source-preservation
obstruction, not a counterdatum to C3.

Spatially, A_T u(z)=integral u(exp(t)*z) dnu_T(t) tends to u on compact
subsets of the upper half-plane for continuous u. Symmetry makes A_T commute
with S:z->-1/z. Dilation averaging also commutes with the hyperbolic
Laplacian when the smooth integral is justified. It does not commute with
translation by one. For a fixed compact set and a C2 function u, Taylor's
formula in t and the zero first moment bound A_T u-u by a constant times
v_T; the constant uses second dilation derivatives on the enlarged compact
set. This controls interior compact sets, not the y->0 boundary limit or
the real-s->infinity Dirichlet normalization. Neither limit can be exchanged
with T->infinity on the strength of this estimate.

The exact next **[OPEN CORE]** is a stability estimate for the actual
filtered inversion defects, in a topology strong enough for the boundary
receiver, derived from the complete original datum and harmonic sparsity.
Compact convergence of the multipliers and a distributional translation
error alone do not provide it. Keep the competitor explicit: a nontrivial
complete cubic datum with finite one-xi harmonic deficit, not an arbitrary
nonperiodic filtered function. No classification of cubic data follows
from the bridge above; scientific novelty is not claimed.

The source-preservation obstruction has a shorter dependency-closed proof
suited to formalization. For any symmetric compactly supported probability
measure nu put m=integral |t| dnu(t). Positivity and the zero-integral
criterion give m=0 iff nu=delta_0. The elementary inequality

    |y| <= exp(y)+exp(-y)

and symmetry give x*m <= 2*K(x) for x>=0. Thus every nonidentity filter
has K(x)->+infinity. If L_f(x)=K(x-a)*L_g(x) eventually and g(1) is nonzero,
the quotient L_f(x)/L_g(x) instead tends to f(1)/g(1), a contradiction.
Conversely delta_0 preserves every such source. This proves the exact iff,
including arbitrary real shifts and eventual equality rather than a
full-half-plane identity. For the actual cubic quotient, the existing
Möbius-convolution theorem supplies absolute convergence and first
coefficient one from the original datum. No new arithmetic hypothesis is
introduced. The formal module is
`WeilWorkHigherDenominatorPositiveFilter.lean`; direct foreground Lean audit
passed, with all eight public theorems depending only on propext,
Classical.choice and Quot.sound. The tail infinite convolution and variance
bound remain paper-only. The exact source-preservation shortcut is closed;
the broader filtered-boundary stability route is not retired.

### Euler support and the exact one-divisor threshold — 2026-10-08

Scientific verdict: **NO PROGRESS**. No new rigidity proof or complete
counterdatum was obtained. The signed logarithmic identity still has two
archimedean copies; no Jordan part separately inherits that identity.

C8 is the following falsifiable intermediate assertion, always for the
complete original cubic correspondence: lambda(n)=0 for every n>=2 which
is not a prime power. Its competitor is a complete datum with a nonzero
such coefficient. This would derive prime-power support, rather than add
an Euler-product premise, but would not alone prove WP07. The conceptual
route is **REDISCOVERED**: Kaczorowski--Kulas explicitly ask whether RH or
a suitable zero-density estimate forces an Euler product, and solve the
degree-one case. Their abstract does not establish the cubic specialization.
The other inspected results retain periodic coefficients, Euler products,
orthogonality or twisted functional equations not supplied here. Thus C8
remains open; no scientific novelty is claimed.

For distinct primes p,q, ordinary Dirichlet coefficient comparison in
the already given identity L_g'=-3 L_lambda L_g gives

    3 lambda(pq) / log(pq) = g(pq) - g(p)g(q).

Indeed the p and q equations give 3 lambda(p)=g(p)log p and
3 lambda(q)=g(q)log q; substituting them in the pq equation proves
the formula. The coefficient at one is zero by that same identity and
g(1)=1. Absolute convergence in a sufficiently far right half-plane
justifies the products and coefficient uniqueness. Thus the first mixed
test is g(6)=g(2)g(3). This is elementary bookkeeping, not a new theorem
about a complete datum; none of the inspected identities forces that
equality. No Lean module is justified for this observation alone.

The more direct target concerns the **threshold**, not just integrality.
Write m_rho=ord_rho(xi), k_rho=ord_rho(E) and

    D1(T) = sum_(xi(rho)=0, 0<Im rho<=T) (m_rho-k_rho)_+.

All sums here are over distinct divisor points; multiplicities are in m,k.
The exact atom theorem `three_mul_boundaryMeasure_singleton` says that
the full-Weil boundary atom at a critical point has mass k_rho/3. Hence
the previously proved `deficitCount`, denoted Dnorm here, is

    Dnorm(T) = sum_(xi(rho)=0, 0<Im rho<=T) (3m_rho-k_rho)_+ / 3.

At off-critical xi zeros k_rho=0 by the original zero-confinement condition,
so this formula also agrees with the off-critical copy weight. It does
not assume RH for xi or simplicity of its zeros. The definitions checked
are `atomShare`, `deficitWeight`, `ordinateWindowWeight`, `deficitCount`
in DeficitEnvelope/DeficitCounting, not a newly invented deficit receiver.

For all nonnegative integers m,k, case splitting at k=m and k=3m gives

    (3m-k)_+ = 3(m-k)_+ + min(2k,(3m-k)_+).

Consequently, on each finite ordinate window,

    Dnorm(T) = D1(T) + J(T)/3,
    J(T) = sum_(xi(rho)=0, 0<Im rho<=T) min(2k_rho,(3m_rho-k_rho)_+).

In particular k=m or k=2m contributes zero to D1 but positive mass to J.
Off-critical points contribute zero to J. This identity is a classical
algebraic diagnosis, with no scientific novelty or new Lean claim.

The existing exact coefficient receiver proves, eventually for every
epsilon>0 and each n>=2,

    |lambda(n)-Lambda(n)|/(4*pi*sqrt(n))
      <= Dnorm(T)/T + epsilon
       = D1(T)/T + J(T)/(3T) + epsilon.

Thus its transfer to D1 has not been proved. Harmonic summability of the
one-xi deficits implies D1(T)/T->0 by splitting a finite head and reciprocal-
height tail. It gives no estimate on J by this argument. In particular the
existing receiver does not close C3 merely because the E multiplicities
are integers. Dropping J would discard exactly the shared intermediate
multiplicities which need to be controlled.

C9 is a concrete stronger candidate motivated by this receiver: for every
complete original cubic datum and each n>=2,

    |lambda(n)-Lambda(n)|/(4*pi*sqrt(n))
      <= limsup_(T->infinity) D1(T)/T,

where the right side may be positive infinity. Its exact competitor is a
complete datum and index n violating this bound. C9 would imply C2 and C3;
it would still leave the positive-density branch of full WP07 open. This
is **SURVIVES PRELIMINARY ATTACK / novelty UNESTABLISHED**, not a theorem.
No new assumption is added to the cubic datum. The stronger uniform bound
has not been inferred from the weaker qualitative C2 assertion.

Next **[OPEN CORE]**: derive an estimate for the actual intermediate
multiplicity mass J under the harmonic-thin branch, or find a direct signed
character estimate avoiding J. For example J(T)=o(T) in that branch,
together with the checked receiver, would prove C3. That estimate is itself
unproved, not a hypothesis to insert into a formal capstone. A bound on
arbitrary integer arrays, a generic common-zero survey, or another finite-
pole converse theorem does not discharge it. The full arithmetic source,
functional equation and zero confinement must enter the next argument.

### Nonlinear multiplicity audit and C10 — 2026-10-08

Scientific verdict: **NO PROGRESS**. C9 remains open. Integer multiplicities
were used in an attempted quadratic detector, rather than merely restated
as a proposed source of rigidity. Put

    F = E'/E, X = xi'/xi, A = zetaArchimedeanDatum + 1/(s-1),
    Q = F(3X-F).

On Re(s)>1 the exact original identities give

    Q = 9(A-L_lambda)(L_lambda-L_Lambda).

At a shared zero rho, with z=s-rho, write the actual meromorphic germs as

    F = k/z + a + O(z), X = m/z + b + O(z).

Direct multiplication gives

    Q = k(3m-k)/z^2 + (3kb+3ma-2ka)/z + O(1).

The double-pole coefficient is positive for 0<k<3m, so it detects the
intermediate multiplicities missing from D1. But it is negative at k>3m
and at zeros of E not shared with xi (where m=0). Moreover, integrating
Q against an analytic test retains the simple-pole term with the regular
parts a,b. Neither those regular parts nor the positive part of the double-
pole coefficients is bounded by the signed arithmetic identity. Thus this
calculation proves no estimate for J. This is elementary germ algebra,
not a new scientific theorem or a no-go for every nonlinear method.

The existing Wiener identity in `WeilFullConePNTErrorWiener` already
identifies the squared atomic energy of a smoothed full-positive measure.
`WeilPaperDeficitInverseEnergy` compares another exact energy with Dnorm,
but supplies no decay bound and does not change its threshold. Neither is
a J estimate. The attempted replacement by known pair-correlation
theorems also fails at the premise level: the inspected Rudnick--Sarnak
Theorems 1.1--1.2 require cuspidal automorphic input and restricted Fourier
support; the original cubic datum supplies neither automorphy nor an Euler
product. Their second-moment arithmetic input is not implicit here.

An adjacent phase argument was also checked. The current corpus proves
the stronger Littlewood bound

    Re producerLogZeta(sigma+it) <= C log|t|/log log|t|,
    1/2<sigma<=2, |t| sufficiently large,

from full positivity alone. `WeilWorkSettledPhaseLittlewood.lean` passed
the final direct `lake --old env lean` check; its named theorem's scratch
axiom audit reports exactly propext, Classical.choice, Quot.sound. No new
coefficient bound was assumed. The corresponding canonical trace envelope
was read in `WeilWorkSettledPhaseCanonicalDisorder`; it was not rebuilt.
This corrects the earlier applicability restriction, but does not imply C7.

The actual radial remainder currently has, for every fixed nu in (0,1],
an upper bound of the form K_nu epsilon^(1-nu) exp(-c epsilon |b|).
The layer-cake proof combines this with C(t)=O(t^alpha), alpha<1, and
chooses nu<(1-alpha). Replacing that power condition by a bare reciprocal-
height summability assertion would not pay this estimate: even if an
associated Laplace mass is o(1/epsilon), the remaining epsilon^(-nu)
factor need not vanish. Constants K_nu are not uniform as nu->0 in the
stated theorem. More importantly, this residual phase mass is a different
measure from the one-xi deficits. No transfer between them was proved.

#### C10: no intermediate shared multiplicity (OPEN)

Given the exact internal and external frontier, the next structural
conjecture is: for every datum satisfying **all** the original complete
cubic correspondence conditions, and every xi zero rho,

    ord_rho(E)=0 OR 3*ord_rho(xi)<=ord_rho(E).

Equivalently, no shared zero has 0<k<3m. Its exact competitor is a complete
cubic datum and a shared zero with multiplicity in that interval. No RH
for xi, simple-zero hypothesis, Euler product, coefficient signs or extra
growth condition is inserted. C10 would force J(T)=0 on every window and
therefore Dnorm(T)=D1(T), proving C9 through the existing coefficient
receiver. It would not rule out infinitely many entirely omitted xi zeros,
so full WP07 would still require another step.

Verdict: **SURVIVES PRELIMINARY ATTACK**, scientific novelty **UNESTABLISHED**.
The finite-deficit theorem does not decide it: that theorem requires global
divisor coverage up to finitely many points. Local analytic germs allow
every intermediate k and cannot prove C10. Products of shifted zeta factors
change the Gamma factors; local polynomials and meromorphic inner examples
lack the full ordinary Dirichlet/completion conditions. None is a complete
counterdatum. The inspected Artin quotient theorem proves infinitely many
unshared zeros under different global inputs, not this pointwise law.

The source-pairing approach has an exact local limitation. At a critical
xi zero rho, put z=s-rho and write zeta(s)=c z^m+O(z^(m+1)) and
zeta(1-s)=d z^m+O(z^(m+1)), c*d nonzero. Since the actual continuation is
Phi=F/3, the source pairing from `WeilWorkSingularArithmeticCanonicalGaussian`
has expansion

    sourceZetaPairing(s) = c*d*(m-k/3)*z^(2m-1) + O(z^(2m)).

This follows by substituting Phi=k/(3z)+O(1) in its definition
((A-Phi)zeta+zeta')zeta(1-s). The factor A is regular at rho. Thus this
pairing is analytic at a shared zero even when 0<k<3m; pole cancellation
alone cannot exclude such multiplicities. Its Gaussian spectral integral
weights atoms by |zeta(1/2+it)|^2 and hence assigns zero to every shared
atom. Dividing out the chosen zero could reveal its mass, but no arithmetic
sign or bound for such a modified test was proved. This is an applicability
diagnosis, not a refutation of C10.

Next **[OPEN CORE]**: prove or refute the pointwise law using a test or
global arithmetic identity that actually detects a shared atom. Retain the
regular-part terms of any nonlinear logarithmic expression. No paper proof
of C9/C10 has closed; no conjectural Lean module is created. Do not relabel
the displayed elementary expansions as a scientific advance.

### Shared-atom test audit — 2026-10-08

Scientific verdict: **NO PROGRESS**. C10 is still **OPEN**, with novelty
unestablished. The proposed divided probe repairs atom detection but does
not supply an order comparison between the two quadratic forms.

Fix a shared critical zero rho=1/2+i gamma, with orders m>0 for xi and
k>0 for E. In the spectral coordinate z, put A(z)=xi(1/2+iz) and
B(z)=E(1/2+iz). The quotient

    F(z) = A(z) B(z) / (z-gamma)^(m+k)

has an entire removable extension. Its value at gamma is nonzero, and it
vanishes at every other zero of either A or B. Normalize by F(gamma).
This elementary construction retains all multiplicities. The canonical
divisor sum of the normalized test against its reflected conjugate is m:
all terms except rho vanish, even if other xi zeros are off the line.
The corresponding E spectral sum, scaled by 1/3, is k/3. Both sums have
finite support on their respective divisors, so these evaluations require
no exchange of infinite sums and no RH assumption for xi.

These are statements about spectral evaluations, not yet about the test
class of the complete arithmetic explicit formula. Multiplication by a
Gaussian centered at gamma retains the two evaluations and is a possible
analytic regularization. The needed contour and arithmetic convergence
must still be proved before applying that formula to this noncompact
test. More fundamentally, even granting that extension, separate
nonnegativity of the two diagonal forms gives m>=0 and k/3>=0. It gives
no sign for their difference k/3-m. At the level of one-dimensional
Hermitian forms, c*|v|^2 is positive for every c>0, including c=1/3 and
c=2/3. This is a diagnostic of the positivity inference, not a complete
cubic counterdatum and not a refutation of C10.

The existing corpus already contains multiplicity-exact entire divided
tests in GaussHodgeWeilEntireDetection and XiHedenmalmMultiplicityChain.
XiWeilPolarization computes their spectral weights; its RH-dependent
norm theorem cannot add RH to the present assumptions. Suzuki's
Hilbert-space description likewise has simple operator eigenvalues even
at multiple xi zeros. Operator rank therefore supplies no missing lower
bound for the weight. No rank-based proof of C10 is retained.

The local-operator pole-clearing fallback also remains unpaid. The
previous notes already distinguish preservation of local support from
preservation of the period-one arithmetic law. Allowing an infinite-order
operator or a hyperfunction target does not establish that law. The
harmonic negative-divisor primitive was already constructed above; it is
not the actual boundary of E/xi and cannot be reused as if it were. None
of these observations retires the broad harmonic-deficit route.

Next **[OPEN CORE]** remains a direct arithmetic bound for the actual
shared-multiplicity mass J(T) in Dnorm=D1+J/3, or a complete-data
counterexample. C9 is the less restrictive target: it does not require
C10's pointwise saturation. Any new argument must retain the arithmetic
term that compares the two forms. Adding positivity of their difference
would insert the missing conclusion as a premise. No dependency-closed
paper proof has emerged, so no Lean theorem is added in this cycle.

### Arithmetic comparison, packets, and the half-degree test — 2026-10-08

**NO NEW SCIENTIFIC THEOREM.** The coefficient-density proof in
WeilWorkDeficitCoefficient loses the sign when passing to the common
spectral measure. Its threshold is necessarily 3 ord(xi), not ord(xi).
Replacing the source by three times its measure destroys the zero-frequency
mass cancellation. This audit supplies no estimate for J(T) and leaves C9
and C10 open.

The cubic phase takes three values off its jumps. This does not make it
constant, continuous, or settled. Grouping fractional atoms into packets
of total mass one also repeats existing work: WeilWorkSettledPhasePackets
already computes the exact two-atom packet cost as chord(q)*|b-a| and bounds
finite families. WeilWorkSettledPhaseCanonicalDisorder already gives a
near-linear lower bound for actual integrated phase disorder in every
nonrigid full source. An infinite packet decomposition and a source-derived
width bound remain unpaid. No new packet receiver is needed.

Two competing candidates were then examined: C9's direct shared-mass
estimate and parity of the cubic divisor. For the latter, let O_E(T) count
distinct zeros rho of E with 0<Im(rho)<=T and odd analytic order. Local
finiteness makes this a finite integer. All data and assumptions are exactly
those in the assigned cubic correspondence.

**C11 [OPEN, parent mechanism REDISCOVERED]:** O_E(T) is unbounded.
Booker's Corollary 1.8 proves the GL(3) analogue by halving an L-datum.
His A1 pointwise requirement is still C7 here, so the corollary cannot be
invoked directly. However, failure of A1 has not been shown to block the
analytic proof itself. The following dependency audit is worth retaining.

Put b(n)=3 lambda(n)/(2 log n) for n>=2, b(0)=b(1)=0, and
F(s)=exp(sum b(n)n^(-s)). The corpus Dirichlet exponential construction
gives F=sum a(n)n^(-s), absolutely convergent for Re(s)>1, with a(1)=1.
The original logarithmic-derivative identity and normalization give
F(s)^2=LSeries(g)(s) there: the derivative of their ratio is zero and its
limit on the positive real axis is one. Hence

    |F(sigma)| = |E(sigma)|^(1/2) /
      |sigma*(sigma-1)*Gamma_R(sigma)|^(3/2),   sigma>1.

Since E(1)!=0 and Gamma_R(1)=1, this tends to infinity as sigma decreases
to one. Thus the absolute-convergence abscissa sigma1* of a is exactly one.
Indeed, convergence at any real r<1 would dominate and bound F(sigma) for
1<sigma<=2, a contradiction. Also |a(n)|<=C_epsilon*n^(1+epsilon) follows
from the absolute sum at 1+epsilon. Neither statement uses C7 or an Euler
product. These are paper-level elementary consequences, not new formal
theorems or a proof of C11.

There is a useful correction to the proposed coefficient obstacle in the
half-degree argument. At d=3/2, its kappa=1/(d-1) is two. The local error
from replacing the nearest-integer phase has size
|a(n)|/sqrt(n) * O(x^(-2+epsilon)), with n comparable to x. The elementary
bound above makes this O(x^(-3/2+2 epsilon)), exactly the required error
when sigma1*=1. A separate square-root coefficient bound is therefore
unnecessary at this particular step. This does not establish the preceding
contour transformation or its stationary-phase expansion.

If those transformations are proved for the actual square-root branch,
the intended closure is concrete: the localized identity first gives
a(n)=O_epsilon(n^epsilon); Cauchy--Schwarz then makes the square-coefficient
abscissa sigma2* equal to one. Its dyadic square mass forces an oscillatory
second moment at least X^(-1-epsilon) along arbitrarily large X, whereas
the transformed expression gives O(X^(-3/2+epsilon)). These incompatible
exponents describe the receiver, not a theorem whose analytic premises
have been discharged. In particular, branches at s=0 and s=1 have order
-3/2 and must be retained. One cannot call the square root globally
meromorphic. Under finite odd-zero support its high upper half-plane is
holomorphic, but the cut domain, reflection phase, strip bounds, and both
transform estimates still need a complete proof. C11 is not marked proved.

**C12 [OPEN, novelty UNESTABLISHED]:** every complete cubic datum satisfies

    exists c>0, for every R>0 there exists T>=R with O_E(T)>=c*T.

The exact competitor is a complete datum with O_E(T)/T tending to zero.
C12 would turn an eventual-integrality obstruction into a quantitative
obstruction to sparse nonintegral branch orders. It is stronger than C11;
neither claim is the assigned rigidity theorem, nor does parity alone
control D1 or J. The finite-cut parent argument does not settle C12.

First **[OPEN CORE]**: derive the contour defect for infinitely many actual
square-root branch points, then estimate its contribution to the localized
second moment using O_E(T)=o(T) and the original cubic data. Counting branch
points alone is not an estimate for the cut integrals: their lengths and
the actual boundary amplitude must be controlled. The full-source
Littlewood bound is available, but no such control has been deduced from it.
This is the next concrete test; failure must return to C9's shared-mass
comparison, not be hidden by adding a boundary regularity premise.

The first localization attack on C12 does not close. At degree 3/2 the
dual phase uses n^2, so adjacent arithmetic indices at height T are
separated on the scale sqrt(T). Sublinear branch count alone only forces
unbounded branch-free gaps, not gaps on that larger scale. A counting
model with gaps comparable to log(T) diagnoses this failed inference;
it is not a complete cubic counterdatum. Any successful local-window
argument must account for this arithmetic resolution, or replace the
single-gap step with an aggregate estimate. No quantitative zero theorem
is inferred from the finite-cut argument.

### Actual half-degree cut and a different spectral test — 2026-10-08

**Scientific status: no new rigidity theorem.** The following cut calculation
is a classical contour bridge. It identifies the missing estimate in C12;
it neither disproves C12 nor supplies a new premise for the original datum.

Use the original complete cubic data throughout. The checked central
exclusion and real-type/functional-equation results give E(1/2)>0 and even
reflection. Positivity on the real axis follows by continuation from s>1:
there the normalized logarithmic-derivative identity makes L_g positive,
and E has no real zero. Let H_R be the analytic square root of E on
Re(s)>1/2, positive on the real axis. For t>0 off the zeros put

    N(t) = sum_{0<gamma<t} ord_{1/2+i gamma}(E).

Following the argument from the right at each critical zero gives

    H_R(1/2+it) = i^N(t) * |E(1/2+it)|^(1/2).

Indeed a zero of order k contributes an argument increase k*pi as a
right-hand path crosses its ordinate. Between zeros the real boundary
value of E has constant sign; the chosen continuous argument fixes the
multiple of 2*pi, not just that sign. For epsilon in {1,-1}, reflect by
H_L(s)=epsilon*conj(H_R(1-conj(s))). The exact jump is

    H_R(t)-H_L(t) = (1-epsilon*(-1)^N(t))*H_R(t).

Thus the jump occupies whole parity-mismatch intervals. Its modulus there
is 2*sqrt(|E|); it is not an atomic measure at the odd zeros. Both boundary
branches vanish at a zero of order k at rate O(|s-rho|^(k/2)).

For the actual half Dirichlet series F above, set Lambda_R=Gamma_R^(3/2)*F.
On the upper critical line the right-hand argument of s(s-1) is pi, so

    Lambda_R(1/2+it) = i*H_R(1/2+it)/(t^2+1/4)^(3/2).

Consequently, for Lambda_L(s)=omega*conj(Lambda_R(1-conj(s))), omega=+/-1,
the matching condition is (-1)^(N(t)+1)=omega. The extra minus sign from
the endpoint factor cannot be dropped. The endpoint branches at 0 and 1
are avoided by working at positive heights a<b.

Take vertical sides sigma>1 and 1-sigma, and a holomorphic multiplier K
on the finite rectangle between heights a,b, neither an ordinate of a
zero. Apply Cauchy's theorem separately on the two half-rectangles and
let their inner boundaries approach the critical line. With both vertical
integrals directed upward, and the horizontal outer paths directed
counterclockwise, their sum gives

    I_right-I_left + I_bottom+I_top
      = integral_(1/2+ia)^(1/2+ib) (Lambda_R-Lambda_L)*K ds.

Indentations at zeros contribute zero in the limit by the local vanishing
estimate. After division by 2*pi*i, the right side is
(1/(2*pi))*integral_a^b (Lambda_R(t)-Lambda_L(t))*K(1/2+it) dt.
This is a finite-height identity; no infinite contour or discarded
horizontal limit is being asserted.

For Booker's complementary Gamma factor at degree 3/2,

    G(s)=(pi/2)^((1/2-s)/4)*Gamma(s/4+3/4),

take K(s)=G(s+4k)*(-iz)^(-s), k>=0, z=-x+iy with x in a fixed compact
subset of (0,infinity) and y>0. Stirling gives the powers t^(-3/8) and
t^(k+3/8) from Gamma_R(s)^(3/2) and G(s+4k), respectively. The available
full-source Littlewood bound for F supplies at most t^eta. Their
exponential factors combine to exp(-(pi-arg z)*t). Therefore the absolute
cut estimate obtainable this way is only

    |cut_k(z)| <= C_eta,k * integral_a^infinity
        1_mismatch(t)*t^(k+eta)*exp(-delta_z*t) dt
      <= C'_eta,k*delta_z^(-k-1-eta),
    delta_z=pi-arg z comparable to y.

The last estimate has no saving over the trivial Fourier-series growth.
O_E(T)=o(T) counts switches of the indicator, not its occupied length or
the weighted source amplitude. Even-order zeros can also change the sign
of the root without switching this indicator, so integrating only the
known Gamma phase by parts does not remove the source derivative cost.
Under finitely many odd zeros one can choose omega so the mismatch set
is bounded. That familiar finite-cut fact does not extend to the needed
infinite-cut estimate. **C12 remains OPEN.**

### C13: sparse extra support, with exact unproved injectivity — 2026-10-08

Given the exact internal and external frontier, what would a Fields
Medal-winning mathematician conjecture? The corpus already forces
rigidity when the entire source measure is carried by critical xi zeros,
regardless of their masses. Test a density version of that support law,
instead of assuming an order relation between the two spectral forms.

Let S_E be the set of positive ordinates gamma such that E(1/2+i gamma)=0
but xi(1/2+i gamma)!=0, and let X_E(T)=#(S_E intersect (0,T]). Count
distinct extra ordinates, without analytic multiplicities.

**C13 [OPEN; SURVIVES PRELIMINARY ATTACK; novelty UNESTABLISHED]:** for
every original complete cubic datum, either lambda=Lambda or

    exists c>0, for every R>0 there exists T>=R with X_E(T)>=c*T.

The incompatible competitor retains every original hypothesis and has
lambda!=Lambda but X_E(T)/T -> 0. An arbitrary signed weight sequence is
not such a competitor. C13 would require a nonrigid source to introduce
linearly many distinct new spectral locations; existing Dnorm bounds
also count changes of mass at shared locations. No implication from C13
to the full assigned rigidity is claimed. No relation to C9's shared-mass
term J has been proved.

Here is the precise paper reduction under the competitor's sublinear
count. It does not multiply the source Dirichlet series. Local finiteness
and X_E(T)=o(T) give the even canonical product

    P(z)=product_(gamma in S_E) (1-z^2/gamma^2),   P(0)=1.

It converges locally uniformly since sum gamma^(-2)<infinity. Writing
N_S(t)=X_E(t), for r=|z| integration by parts gives

    log|P(z)| <= integral_0^infinity
        2*r^2*N_S(t)/(t*(t^2+r^2)) dt.

For every eta>0, choose A with N_S(t)<=eta*t for t>=A. The finite initial
part is O_A(log(1+r)); the tail is at most pi*eta*r. Hence, for every
eta>0, |P(z)|<=C_eta*exp(eta*|z|). No harmonic summability or positive
minimal separation is needed here. P is even and real on the real axis.

Use the corpus Fourier convention and normalize Xi so that Phi-hat=Xi.
Define K_P as the inverse Fourier transform of Xi(t)*P(t). On each fixed
horizontal strip, Xi has a polynomial factor times exp(-pi*|Re z|/4).
The bound just proved makes Xi*P and all polynomial multiples integrable
on each horizontal line. Contour shifting therefore gives, for every
A>0 and integer j>=0,

    |K_P^(j)(u)| <= C_A,j*exp(-A*|u|).

In particular K_P is real, even, smooth, and admissible by truncation.
Its transform vanishes on every source atom (use Xi at shared zeros and
P at extra zeros), and on every xi zero, including any off the critical
line. Smooth cutoffs converge with their derivatives in every required
exponentially weighted norm. Two integrations by parts give uniform
weighted transform error on the closed zero strip. The source's finite
reciprocal-square moment and the corresponding xi zero sum then let the
two spectral pairings pass to the limit. The arithmetic side converges
by sum |lambda(n)-Lambda(n)|/n^2<infinity and the displayed decay.

Thus the explicit formula and polarization give, for every real smooth
compact H, T_(lambda-Lambda)(K_P,H)=0. Test-function duality gives exactly

    sum_(n>=2) (lambda(n)-Lambda(n))/sqrt(n) *
       [K_P(u-log n)+K_P(u+log n)] = 0,   every real u.

These analytic facts are a classical BRIDGE, not a proof of C13 or a
novelty claim. The first **[OPEN CORE]** is injectivity of this modified
kernel transform for the actual weights and this minimal-type product.
The existing RiemannKernelTransformInjectivity proof uses the specific
identity Phi=Psi''-Psi/4, an odd theta relation, Hamburger, and divisor
inversion. It proves the case P=1; it cannot be called on K_P. Applying
an infinite-order differential operator to a periodic distribution also
requires a defined operator and an injectivity theorem; locality or a
formal symbol does not supply either one.

The already checked zeta-mass receiver is different: it needs sublinear
sum ord(E)*|zeta(1/2+i gamma)| on the extra support. Distinct unweighted
X_E=o(T) supplies neither the amplitudes nor the multiplicities. Li's
global zero/pole bound counts multiplicity differences, including shared
zeros, so it likewise does not settle C13. Fourier interpolation formulas
with sqrt(n) frequencies do not become an ordinary n-frequency Hamburger
receiver without a separate proof.

The next attack is the precise injectivity statement above. A failed
unrestricted multiplier extension must not be mistaken for a complete
cubic counterexample or for failure of the minimal-type case.

Here is an exact pressure test of that distinction. Put l=log(3) and
C_a(u)=sum_(j in Z) Phi(u+j*a). All these sums converge locally uniformly.
Define w(3^k)=sqrt(3^k)*(1-3*1_(2 divides k)+2*1_(4 divides k)) for k>=1,
and w(n)=0 otherwise. Then w(3)!=0, w(1)=0, and sum |w(n)|/n^sigma is
finite for every sigma>1/2. Direct grouping gives

    G_w = C_l-3*C_(2l)+2*C_(4l).

This function is 4l-periodic with mean zero: its mean is proportional to
1/l-3/(2l)+2/(4l)=0. Let q be the normalized indicator of [-2l,2l]. Its
Fourier transform is P_+(t)=sin(2l*t)/(2l*t), with value one at zero.
The kernel K_+=q*Phi therefore has transform Xi*P_+, and absolute
convergence permits convolution through the defining weight sum. Hence

    G_(w,K_+) = q*G_w = 0,   but w!=0.

Thus injectivity for arbitrary even real finite-exponential-type
multipliers, even normalized at zero, is **FALSE**. This is elementary
periodization, classified BRIDGE / REDISCOVERED rather than new science.
The example has positive type 2l and a linear zero lattice; it does not
attack C13's minimal-type product. Nor is lambda=Lambda+w a full positive
source: the existing prime-power lacunary rigidity theorem excludes it.
The surviving question is exactly the minimal-type case with the original
source structure. Its positive classification has no paper proof yet;
no WP07 route is retired and no new Lean theorem is claimed.
