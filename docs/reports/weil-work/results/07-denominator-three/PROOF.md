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
