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

**Transport obligations, still OPEN.** For `Q=G/ζ`, finitely many deficits give finitely many poles `ρ` with `0<Re ρ<1`, retaining arbitrary pole orders. One must prove: (i) the pole-cleared quotient has sufficient growth for Mellin inversion and contour transport; (ii) after the usual poles at 0 and 1 are removed, the Maass inversion defect is the sum of the homogeneous eigenfunction extensions of its axial polar terms; (iii) its leading `sqrt(y) log(y)` boundary coefficient is an even-periodic coboundary represented by a finite sum `Σ x^(−ρ) Pρ(log x)`; (iv) the map from principal parts to the top logarithmic coefficients is injective. The proposed scalar factor is proportional to `Γ(1/2)/(Γ(ρ/2) Γ((1−ρ)/2))`, nonzero in the open strip, but its precise normalization and transport have not been proved here. Finally, boundedness near zero of that finite sum must be converted to vanishing of every polynomial coefficient without assuming distinct real parts or noncancellation of oscillations. These are proof obligations, not added hypotheses on the cubic target.

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

For horizontal analyticity, allow complex x with `|Im x|<y/2`. The real part of `(x−t)²+y²` is positive, so the principal square-root kernel is holomorphic and uniformly dominated on smaller compact sets. All spatial derivatives remain integrable at zero and infinity, giving smoothness and transfer of the directly verified quarter equation. Evenness follows by `t↦−t`. Together with the beta substitution and Gamma nonvanishing, this gives a dependency-closed paper construction of the homogeneous polar modes. Its formalization is still pending.

More precisely define `Vρ,j=(-1)^j ∂ρ^j(Uρ/Cρ)`. Its axis value is `y^(1/2−ρ)(log y)^j`. Its leading logarithmic boundary coefficient is `(-1)^j ∂ρ^j(-2 x^(−ρ)/Cρ)` for x>0. At logarithmic degree j the coefficient is exactly `−2/Cρ`, with only lower-degree terms added. Hence the map on each finite polynomial packet is triangular and injective. For an even, smooth quarter-eigenfunction inversion defect with a finite polar axis expansion, subtract these modes and apply the exact corpus theorem `MaassAxisContinuation.eq_zero_of_axis` (smoothness, quarter equation, evenness, zero axis, horizontal real analyticity). The resulting finite boundary packet satisfies the two modular identities by locally uniform boundary convergence; the finite-packet receiver kills every coefficient. This proves the **paper-level finite-axis-defect rigidity bridge**. The actual quotient's finite-pole Mellin-axis expansion and growth remain unpaid, so the infinite-deficit conjecture is still OPEN.
