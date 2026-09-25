# Three research routes toward a formal proof or falsification of RH

Basis: only `docs/reports/endpoints.md` (snapshot 2026-09-25), `docs/reports/xi.md` (snapshot 2026-09-26) and `docs/reports/STATUS.md`, read in full on 2026-09-26. Identifiers (F…, MUST-…, CANNOT-…, FAIL-…, endpoint families F0…, `xi §…`) point into those three files. No other source was used; every judgement below is a reading of that ledger.

Status tags follow the ledger: [L] Lean-checked, [P] paper proof, [C] claimed or numerical.

## 1. Selection tests

The ledger holds about 1,400 Lean-level RH equivalences, almost all receivers, and no producer for any of them (xi §0.3, §4.A, §10). A route was kept only if it can pass every test below. Each test is a consequence recorded in the ledger, not a preference.

| Test | Content | Source |
|-|-|-|
| A. No slack | Λ=0 exactly and free-orbit counts are integers. The decisive step must be an exact identity plus a bound strictly below one integer quantum, uniform in height. Height-dependent bounds of any strength give nothing. | xi §0.3, §9.1; CANNOT-411, CANNOT-437 |
| B. Single-prime deformation | An argument whose hypotheses survive a change of one Euler factor proves a false statement (ζ(s)²(1−2^{θ−s}), quartet gauges, the modified source with negative grade-two log coefficient). A route must name the step where exact Λ(n) is used. | xi §7.3, §8.10, §8.12; MUST-389, MUST-357–MUST-373 |
| C. Orientation | The deciding datum is reflection-odd (grade 2Re ρ−1, a two-torsion class). Reflection-even readers (norms, energies, signatures, Gram determinants, positivity) take equal values on a zero and its partner. Covariance cannot create orientation. | CANNOT-399, CANNOT-227, MUST-03 |
| D. Boundary map, not cohomology | RH is the vanishing of one coboundary, N(1_{Re<½}) = 1_{Re≠½}; localized and equivariant invariants (Tate, Smith, index, inertia, spectral flow) compute only the fixed part. | CANNOT-405, CANNOT-407, CANNOT-435, MUST-436 |
| E. Scale | A displacement δ→0 is visible only to degree-zero functionals (sup, total variation, count, H^{1/2}); pointwise averages have degree one. | xi §8.3; MUST-433, MUST-440 |
| F. Pre-divisor | The law must be proved on source data before specializing at zeros. Imposing admissibility (compactness, positivity, properness, bounded work) at zero fibres is an RH-equivalent endpoint. | MUST-01, MUST-13, MUST-29 |
| G. Singular limit | No finite datum suffices: finite jets, moments, apertures, prime sets and windows all admit off-line extensions. The proof must pass through a singular or cofinal limit. | xi §7, §8, §9.1; CANNOT-02, MUST-06, MUST-27 |
| H. Brief | Not positivity alone, rigidity alone or compactness alone; not cohomology; as far as possible from classical routes. | user brief |

## 2. The three routes, ranked

1. **Sub-quantum chiral loss through the Gaussian Euler–continuum passage.** The winding of strict-right rectangles is an exact integer, and a pre-divisor sub-unit budget B_base<1 already exists. The claim is that the H^{1/2} degree lost in the singular passage into the strip stays below one quantum.
2. **Beyond-all-orders winding of the theta renewal loop, read at the natural boundary of the source.** Nonreal zeros are the solutions of K=−1 for an exact renewal feedback, whose information lies beyond all orders. The claim is that the exponentially small remainder is fixed by the source's boundary function Q(r)=Σe^{−iπn²r}/n² and its prime-2 self-similarity.
3. **Exact ordinate coincidence.** RH is ordinate injectivity. The collision charge has a full quantum of margin (<2) and a two-prime arithmetic form. The claim is that exact coincidence, unlike closeness, is detected without the one-log loss.

Why this order: Route 1 is the most refined target in the ledger that has not been refuted. It is the only one where both the integer and a sub-unit pre-divisor number are already in hand. Two independent lanes (divisor-side bubbles and source-side boundary phases) point to the same carrier. Route 2 has an exact equivalence and a precise named requirement (xi §9.5). Its new identity has not been attempted, but it sits closest to a classical object (Riemann's theta integral). Route 3 has the largest margin (a full quantum) but the least developed arithmetic side. It may also collapse onto an existing receiver (see its risks).

None of the three is close to finished. The ledger records no producer for any receiver. The proposals target the places where its constraints leave the most room.

## 3. Route 1 — Sub-quantum chiral loss through the Gaussian Euler–continuum passage

### 3.1 Statement to prove

Let D be a pre-divisor admissible strict-right rectangle (inside ½<Re s<1, with ξ≠0 on ∂D). Let u_{D,x}=Φ_x/|Φ_x| on ∂D be the boundary phase of the zero-free Gaussian Euler–continuum family, and let u_D be the Xi boundary phase. Write κ₋(D) for the negative-chirality Hankel energy lost as x→0. The claim is κ₋(D) < 1 for every such D.

Consequence: along weakly convergent zero-winding phases wind(u_D) = κ₋ − κ₊ (F448 [P]). wind(u_{D,x}) = 0 because Φ_x is zero-free, and wind(u_D) is the enclosed multiplicity, so it is ≥ 0. Hence 0 ≤ wind(u_D) ≤ κ₋ < 1, and wind(u_D) = 0 for every D. There is no zero with ½<Re ρ<1, and RH follows by the functional equation.

### 3.2 Ledger evidence

- **The integer exists before any divisor and is exact.** T_D is positive nuclear, Tr T_D = |wind u_D| = enclosed Xi multiplicity, and RH ⟺ T_D=0 for all D (F438–F440). Cubic degree is the first ordinary nuclear trace that is both reflection-odd and integral (F452–F454).
- **Degree changes only in quanta.** Every bounded W^{1/2,2}(S¹;S¹) degree loss is a finite list of escaping Möbius profiles, each costing the sharp quantum 4π²; diffuse excess energy cannot carry a winding jump. Bounding κ₋ alone suffices and is strictly weaker than uniform H¹ properness (F442, F444, F447, F448, MUST-134, MUST-135).
- **A zero-free source family with literal coefficients exists.** L_x(s)=Σ_{n≥2}(Λ(n)/log n)e^{−πxn²}n^{−s}, E_x=exp L_x, with the continuum counterterm M_x(s)=∫_1^∞e^{−πxu²}u^{−s}du, A_x'=M_x, A_x(2)=0, and Φ_x=½sπ^{−s/2}Γ(s/2)exp(L_x+A_x). Φ_x is zero-free on Re s>0, and Φ_x→ξ on Re s>1. On every contour in Re s>1 the phases converge in C¹ with both chiral losses 0, so the defect is created only at the singular passage into the strip (F446, F449–F451, MUST-136, MUST-137).
- **A sub-unit pre-divisor budget exists.** B_base = (1/4)Σ_{n≥2}Λ(n)/(n log³n) = (1/8)∫_0^∞t²[−ζ'/ζ(1+t)]dt < 1. It is the third inverse moment of the safe prime-log semigroup, the Mellin form of the Gaussian atomic-minus-continuum anomaly, and the bulk action ∫_0^∞(d/dc)Tr C_def(c)dc of the prime-mixed Burnol aperture damping (F455–F458).
- **Two independent lanes land on the same carrier.**
  - Divisor side: off-line zeros are critical-exponent bubbles of the Gagliardo H^{1/2} energy, with seminorm π/4 independent of δ (MUST-442). The angular energy jumps by exactly one unit at an off-line zero (MUST-420).
  - Source side: boundary phases lose degree only through quantized Möbius bubbles (MUST-134).
- **Why this avoids the recurring one-log loss.**
  - The ledger's most persistent wall is that H^{1/2} misses L^∞ by one log (MUST-440). CANNOT-437 then requires an absolute constant in sup U < 2, which no known method delivers.
  - This route never asks for L^∞ control. It replaces "U<2 uniformly in height" by "negative-chirality H^{1/2} loss below one quantum". That statement is degree-zero, height-free (B_base is one number) and pays no log.

### 3.3 Why it passes the tests

- **A.** An exact integer plus a sub-unit number, with no height dependence.
- **B.** Exact Λ enters in two places: the positive reduction E_reduced ≥ 0 in E_Euler = E_reduced + Tr T_D (MUST-141, MUST-143), and the matrix-complete cross-prime entries. A one-prime deformation must break one of these; step 6 below checks this.
- **C.** Orientation comes from pairing the singular completion metric with the reflection-odd source current T_src (F490–F492, MUST-149). Only κ₋ needs a bound and κ₊ is free: the argument is one-sided, as the orientation test demands.
- **D.** The winding on ∂D is a value of the boundary map (MUST-436), not a cohomology class. Cyclic or mapping-cone language appears only as bookkeeping; the decisive step is an analytic inequality.
- **E.** H^{1/2} is degree zero (MUST-440).
- **F.** Φ_x, B_base and the syntheses A_E, A_0 are all built before any divisor.
- **G.** x→0 is a singular, ordered limit. The Blaschke-kernel example shows the loss tends to 1 if |a|→1 first and to 0 if τ→0 first (F447, F448).
- **H.** The argument combines four things: an integer (degree), an energy budget, a positivity (E_reduced ≥ 0) and a singular limit. None of them works alone (FAIL-81–FAIL-93 record each failing separately). It uses no Weil-form positivity, operator spectrum or heat flow.

### 3.4 Program

Each step is a theorem with a stop test.

1. **Boundary class.** Show u_{D,x} ∈ H^{1/2}(∂D;S¹) with finite seam cost C_Θ for each x>0, and wind(u_{D,x}) = 0. Target: [L].
2. **Weak convergence through the passage.** Prove u_{D,x} ⇀ u_D weakly in H^{1/2}(∂D) along a source-fixed schedule x→0. This is the one analytic input the chiral decomposition still needs.
   - *Stop test:* if the seam cost diverges diffusely rather than by quantized bubbles, the decomposition does not apply. The argument must then move to the relative defect T_{(D,x)} = (R_{D,0} − R_{D,x})³, whose trace is independent of x (F471–F473).
3. **Chiral decomposition in Lean.** wind(u) = κ₋ − κ₊ (currently [P], F448).
4. **Bulk-to-boundary inequality (the core).** Use the two-parameter formation: aperture damping c and Gaussian heat x, whose mixed connection curvature is the polar–Gamma term (MUST-142, F466, F467). Prove κ₋(D) ≤ ∫_0^∞(d/dc)Tr C_def(c)dc = B_base by a matrix-complete cubic transgression (MUST-138, MUST-144) that:
   - keeps every cross-prime Burnol entry;
   - subtracts the continuum before taking norms, using the cubic aperture gauge (1−e^{−2cλ})^{3/2}, since order q≥3 is minimal (F474–F476);
   - keeps atomic/continuum provenance as a measure-class datum: pure point on {log n} against absolutely continuous, with the zero-distance/infinite-action defect of A_E relative to Ran A_0 (F477–F486, MUST-145–MUST-148).

   Shortcuts the ledger already excludes:
   - global Wold/Gamma domination (CANNOT-211);
   - orthogonal range quotients and output-space Schur shorting (CANNOT-224–CANNOT-226);
   - covariance-only formulas (CANNOT-227);
   - homotopy invariance of equal windings (CANNOT-222);
   - choosing a member of the same-defect fibre (CANNOT-269, CANNOT-271);
   - Green–Stokes positivity channels, which exceed the budget (CANNOT-272).
5. **Close.** κ₋ < 1 ⇒ wind(u_D) = 0 for all D ⇒ RH.
6. **Deformation audit (test B).** Rebuild Φ_x with Λ changed at one prime: the modified source Q(s)=2^s+57/20+2·2^{−s} of xi §7.3, or ζ(s)²(1−2^{θ−s}). Identify which step of 4 fails for the deformed family. Until that step is named, step 4 is not trusted.

### 3.5 Falsification arm

- Under ¬RH, some admissible strict-right D has wind ≥ 1. There the identity E_Euler = E_reduced + Tr T_D forces E_reduced ≤ B_base − 1 < 0.
- So a failure of positive reduction is concentrated on rectangles around off-line zeros; it cannot be diffuse. At finite x the negative-chirality energy density is computable from literal prime data, and its build-up toward one quantum localizes candidate rectangles.
- A falsification is then a certified argument-principle winding on an explicit ∂D (interval arithmetic on ξ), in the shape of the finite local certificates of xi §4.B and endpoint F0190. By xi §3.1 [C], such a rectangle lies above ordinate 3·10¹², so this arm serves as a localizer, not as a search program.

### 3.6 Main risks

- **Budget order.** The raw positive cubic Euler/Wold mismatch is not sub-unit: its prime-two atom is (95/16)(log 2)³ > 1, and identity-scale landing overshoots by a factor >2000. Only the cubic-gauged B_base is below 1. If the transgression lands on the raw mismatch, the route fails (F441, CANNOT-211).
- **Orientation.** An even invariant cannot produce the odd charge (F487–F489). Step 4 must pair metric and odd current inside one identity.
- **The passage.** The ledger states convergence Φ_x→ξ only on Re s>1 (xi §1.2). If step 2 fails, the relative cubic defect carries no scalar budget without a matrix-complete action map (CANNOT-222).
- **Nearby failed sub-mechanisms** (FAIL-81–FAIL-93): Beta/Jacobi diffusion, generic dilation, fixed-scale clocks, scalar outer completion, finite monitored unitaries, continuous multiplicative completion. Step 4 must not reduce to any of them.

## 4. Route 2 — Beyond-all-orders winding of the theta renewal loop, read at the natural boundary

### 4.1 Statement to prove

The renewal form of the theta source (a=¼, c=θ(1)) gives:

- Ξ(2iλ) = (a+λ)D(λ) + (a−λ)D(−λ);
- the cosh factorization Ξ(2iλ) = 2ac·e^{−C(λ)}cosh(η+S)/cosh η, whose prefactor is zero-free on |Re λ|<¼;
- a feedback K with RH ⟺ K(λ) ≠ −1 on 0<|Re λ|<¼, equivalently no nonreal solution of η(λ)+S(λ) = iπ/2 (xi §1.4, §2.1, §4.A.2, §10.2 [P]).

The claim has two parts:

(i) 1+K on the strip has an exact representation whose exponentially small part is determined by the boundary values of the source on its natural boundary |Im x| = π/4. There the Gaussian atoms become unimodular phases, the cusp amplitudes are quadratic Gauss sums, and the boundary potential is Q(r) = Σ_{n≥1}e^{−iπn²r}/n².

(ii) The number of solutions of K = −1 off the imaginary axis is a winding number of a loop generated by that boundary data. It vanishes because of the exact self-similarity Q(r+1) + Q(r) = ½Q(4r).

### 4.2 Ledger evidence

- **Exact reformulation.** Positive real zeros are the crossings of phase level π/2 of an exact renewal phase built from a source-defined probability law (increment ν(t) = 2πΣn²e^{(5/4)t−πn²e^t} > 0, mass q < 1/6). Nonreal zeros are the nonreal solutions of K = −1 (xi §2.1, §4.A.2).
- **All finite-order information is empty.** Every inverse-power endpoint coefficient of the phase gap vanishes. The seam phase satisfies θ₁(y) − π/2 = O(e^{−κy}/y) with infinitely many sign changes, against −a(1−r)/y for r<1, so Ξ sits at critical coupling r=1 of the loop. The feedback 1+K decays like e^{−κ|y|}.
- **The ledger names the requirement.** "Control the renewal loop's beyond-all-orders complex winding; one-port positivity cannot decide it" (xi §9.5). Sources: xi §2.1 seam phase, §2.5; STATUS first route-independent CANNOT.
- **Positivity is provably useless here, so the route cannot collapse into positivity alone.** The Pick-defect kernel of K has infinite positive and negative index. Residues of 1/(1+K) grow super-polynomially. No passive or completely monotone model exists (xi §2.5, §8.18, §8.23).
- **Where the beyond-all-orders information must live.**
  - Ξ decays at rates set by the source strip: |ξ(½−a+it)| ≤ C_δe^{−δ|t|} for δ<π/4 (xi §2.3), and Xi(2z) = O(e^{−κ|Re z|}) for κ<π/2 on inner strips (STATUS first CANNOT).
  - The source is holomorphic exactly on |Im x|<π/4. That line is a natural boundary: the source is unbounded on a dense set there, with rational-cusp amplitudes given by quadratic Gauss sums, |G_{p,q}| = √q (xi §2.1 [L]+[P]).
  - At Im x = π/4 the factor e^{−πn²e^{2x}} becomes the unimodular e^{−iπn²y} with y = e^{2Re x}, so the boundary data are derivatives of the quadratic-phase potential Q. Q is continuous, 2-periodic and of mean zero, with Q(1) = −π²/12 (xi §2.1, card theta-rational-cusp-boundary-law).
- **The ledger's own escape clauses point here.** Dark divisor packets rule out every finite family of inequalities that is continuous and strict at the theta source k. The only exits it names are a boundary equality, a nonuniform or singular observation, or an exact arithmetic membership law (CANNOT-386, CANNOT-389). It also requires acting at the exact tail scale e^{−πe^{2|x|}}, where capacity exponent b=2 is sharp (MUST-391, xi §9.5). The natural boundary is that tail scale continued to its singular edge.
- **The self-similarity is a prime-2 relation.**
  - Q(r+1) + Q(r) = 2Σ_{n even}e^{−iπn²r}/n² = ½Q(4r).
  - Scaling e^{2x} by 4 is the source translation x ↦ x + log 2.
  - The theta translation gauges a·k(x+log p) + b·k(x−log p) have positive, completely monotone fluxes but transform (ap^w + bp^{−w})ξ(½+w), with off-line zeros (xi §7.3). They replace the boundary potential by aQ(p²r) + bQ(r/p²), which breaks the relation. That is where test B can be met.

### 4.3 Why it passes the tests

- **A.** A winding count at the single level K = −1 is exact and integer-valued.
- **B.** The decisive step must use Q(r+1) + Q(r) = ½Q(4r), which translation gauges and renewal surgery violate.
- **C.** The count of solutions in 0<Re λ<¼ versus −¼<Re λ<0 is oriented. The Lévy form K(z) − K(−z) = −izΞ(z) is reflection-odd (xi §1.4).
- **D.** A winding over a region boundary is a boundary-map value, not a cohomology class.
- **E.** An exact count is scale-free.
- **F.** Everything is built from the source k and Q, with no zeros used.
- **G.** Information beyond all orders requires a singular limit at the natural boundary.
- **H.** The route combines continuation to a natural boundary, arithmetic (Gauss sums, the prime-2 self-similarity) and topology (winding). The only positivity is that of the fixed renewal law. It uses Riemann's theta integral, which is classical, but none of the classical mechanisms on it: Pólya-kernel positivity, total positivity, Laguerre–Pólya membership and heat flow are all excluded in the ledger (xi §7.3, §8.19, §8.23; TP₅ fails, xi §2.25).

### 4.4 Program

1. **Renewal objects in Lean.** Formalize D, K, η, S and the cosh factorization from the source (currently [P]).
2. **Continuation identity (the new theorem).** Continue the renewal integrals in the source variable up to |Im x| = π/4. Write 1+K on 0<|Re λ|<¼ as an explicit elementary part plus a boundary integral against Q and its cusp expansion.
   - *Stop test:* the source itself has complex zeros inside the strip ([C], e.g. near 0.6388i, xi §2.25), so log k is not holomorphic there. The identity must use k linearly, or account for those zeros by source-determined terms. If they enter as uncontrolled contributions, the route stops.
3. **Winding count.** Express the number of solutions of K = −1 with |Im λ| ≤ Y, minus the critical-line count, as the winding of the loop generated by the boundary data.
   - Show that the loop is invariant under the map induced by r ↦ 4r, up to terms that vanish beyond all orders.
   - Evaluate it at the fixed point of that map.
4. **Level specificity.** The argument must separate the level K = −1 from other levels, because Ξ(z) = L with L<0 has infinitely many nonreal solutions (xi §2.5 [P]). An argument that would equally give real solutions for Ξ = L is wrong.
5. **No homotopy in the coupling.** There is no zero-free homotopy X_r = 2ac(1−r) + rΞ(2z) (xi §8.18), so the argument must work directly at r = 1.
6. **Deformation audit.** Two deformed sources must each violate a named step:
   - the translation gauges a·k(x+log p) + b·k(x−log p);
   - the renewal surgery P_T, which has exact seam jets, renewal mass, reflection, positive density and positive finite prime deletions, yet X_T(T+ib) = 0 (xi §7.3).

### 4.5 Falsification arm

- The boundary representation is explicit in Q and in the Gauss-sum cusp amplitudes.
- A nonzero winding at finite depth of the r ↦ 4r map localizes a nonreal solution of K = −1 to an explicit window.
- Interval arithmetic can certify such a solution, which gives an off-line zero of Ξ at z = 2iλ. The height bound of xi §3.1 [C] applies.

### 4.6 Main risks

- **The real-line phase does not suffice.** The ledger records that the phase crosses π/2 infinitely often with ∫|θ'| = O(e^{−κY}), so no real-line winding or total-variation budget decides (xi §8.18). The route targets the complex winding in the strip; if that count reduces to the real phase, it fails.
- **Complex zeros of k inside the strip** obstruct naive continuation of log-type renewal quantities (step 2 stop test).
- **Renewal structure alone is insufficient** (renewal surgery). The proof must rest on the modular self-similarity; the renewal factorization only presents the data.
- **Closest to classical of the three,** because the starting object is Riemann's theta integral.

## 5. Route 3 — Exact ordinate coincidence: the collision quantum with a two-prime arithmetic realization

### 5.1 Statement to prove

RH ⟺ the collision charge K(T) = Σ_{|Im ρ|≤T} ord_ρ·(H(Im ρ) − ord_ρ) satisfies K(T) < 2 for all T. Here H(t) is the total multiplicity on the slice Im s = t, and K is even-valued [L] (xi §4.A.16).

The claim: the source-side form holds. The two-prime Cesàro excess built from the χ₂, χ₃ carriers is eventually < 2 ([L] ⟺ RH; endpoint family F0237). The proof would be an exact identity between the thin-slice pair current of ξ and that arithmetic excess, followed by a bound that is uniform in height.

### 5.2 Ledger evidence

- **RH is ordinate injectivity.**
  - Each slice Im s = t is finite and stable under the reflection. Its fixed part has at most one point. A zero alone on its slice is critical [L].
  - Slice count = [ξ(½+it) = 0] + 2·(number of free orbits).
  - RH ⟺ distinct zeros have distinct ordinates (xi §3.2, §4.A.16; MUST-401, MUST-403, MUST-404).
- **This target has never been attempted.** The ledger separates excluding a small displacement (resolution), where every method stops one log short, from excluding an exact coincidence of two ordinates. The latter is a scale-insensitive transversality condition "never attempted" (CANNOT-402).
- **The integer is analytic and needs no zero enumeration.** The collision charge is the cutoff-independent thin-slice limit of the pair Poincaré–Lelong current of ξ [L] (xi §4.A.28). Thin-strip contours are invariant under every finite exponential Euler gauge [L] (xi §8.16).
- **The margin is a full quantum.** Unlike the slack-free endpoints (Λ=0), any bound strictly below 2 suffices. F0237 lists several such sub-quantum source forms:
  - two-prime Cesàro excess < 2;
  - prime Cayley information loss < 2 (xi §4.A.21);
  - Ward–Green Cayley reflection energy < 32;
  - exterior packet energy below 4(96/145)².
- **Two prime clocks separate ordinates; one does not.** γ ↦ (2^{2iγ}, 3^{2iγ}) is injective, while one clock aliases ordinates modulo 2π/log p [L] (xi §2.6). Pointwise, β = ½ ⟺ p^{ρ−½} + p^{½−ρ} is real for p = 2 and p = 3 [P] (xi §4.A.14).
- **Discrete means detect exact coincidence at every scale.**
  - A Cesàro mean over the two-prime lattice {k log 2 + l log 3} of e^{i(γ−γ')(k log 2 + l log 3)} is 1 if γ = γ' and 0 otherwise. The alternative, (γ−γ')log 2 and (γ−γ')log 3 both in 2πℤ, is impossible for γ ≠ γ'.
  - So an exact coincidence is weighed fully whatever the displacement δ, while distinct ordinates, however close, average out.
  - Absolutely continuous clocks erase every nonzero prime-log character (F190), so the detector must be discrete, as this one is.
- **The problem is local.** The far field costs one log, and it enters only as a normalization (MUST-457). The pair field is bounded by one-sided fields at the two zeros (MUST-446, MUST-447). Everything reduces to the at most 40 log(180|t|) zeros within distance 1 of the slice [L] (xi §3.3).

### 5.3 Why it passes the tests

- **A.** An integer count with quantum 2 and margin 2 minus the bound. It must be uniform in height; CANNOT-437 is the stop test.
- **B.** The arithmetic excess must use the full prime sum, with 2 and 3 serving only as clock frequencies. A bound that depends on finitely many primes cannot work: finite prime data are divisor-invisible [L] (xi §2.6), and a one-prime deformation plants a collision (xi §7.2, MUST-389).
- **C.** The collision is the free orbit itself. The prime seam C_p(ρ) = log p·(p^{−ρ̄} − p^{−(1−ρ)}), with |C_p|²p/(4log²p) = sinh²((β−½)log p) (xi §4.A.29), reads it. The identity must keep the signed seam before any squaring (CANNOT-161).
- **D.** The count is fibred over height: it is the fibre of the boundary map (MUST-436), with no localization.
- **E.** Counts are degree zero.
- **F.** The pair current and the arithmetic excess are both pre-divisor.
- **G.** The thin-slice limit and the Cesàro limit are both cofinal.
- **H.** The route combines integrality, arithmetic clocks and local analysis. It is not pair correlation: bandwidth-≤1 pair statistics cannot see exact same-ordinate pairs or multiplicities (CANNOT-334, xi §8.4).

### 5.4 Program

1. **Decisive first check (cheap).** From the Lean definition behind the two-prime Cesàro carrier, determine the excess's unconditional growth over a height window. If it is of the order of the Cauchy-weighted local density, C·log T, the route stops (CANNOT-437; xi §2.21, LocalCountBound).
2. **Two-variable explicit formula.**
   - Express the thin-slice pair current (pairs at equal ordinate, real shift h ∈ (0,1)) through prime sums on the lattice log 2·ℤ + log 3·ℤ, plus archimedean and near-field terms.
   - The lag function is already decided on this lattice [L]: RH ⟺ Φ(k log p + l log q) is bounded above (xi §4.A.3).
3. **Near field at an absolute constant.**
   - This is where every earlier attempt stopped (CANNOT-437).
   - The claim to establish: in the Cesàro limit only exact same-ordinate pairs survive. The ~log T near zeros at distinct ordinates then contribute 0 rather than O(log T), and the log never appears.
   - Inputs: MUST-446, MUST-447 and MUST-457.
4. **Close.** An excess below 2 gives K < 2 and hence RH.
5. **Deformation audit.** Both deformations must violate a named step:
   - the quartet gauge P·ξ, which keeps FE, order one and hypertranscendence (xi §7.1);
   - ζ(s)²(1−2^{θ−s}) with a complex planted zero (MUST-389).

### 5.5 Falsification arm

- A collision is a pair of zeros at one ordinate, so the arm is to certify, at a candidate ordinate, a nonzero Euler-shift Pick energy below −2δ.
- The cleanest finite certificate in the ledger is the Euler-shift prime Pick witness: ¬RH ⟺ there exist a rational shift ω, Gaussian-rational nodes, a finite prime set and a rational δ whose finite-S Pick energy is at most −2δ within δ of the exact value [L] (endpoints F0257; xi §4.A.12, §4.A.25).
- The collision picture says where to place the nodes: at the candidate ordinate, with ω below the displacement (the Hardy leakage switches on exactly for 0 < ω < a; xi §4.A.18, §4.A.25).
- The height bound of xi §3.1 [C] applies.

### 5.6 Main risks

- **Collapse onto an existing receiver.** On lattice lags the arithmetic side is the Chebyshev remainder at x = 2^k3^l. Its Cesàro mean square may reduce to Cramér's mean-square criterion. The mean-square, positive-part, Herglotz and Hardy forms of the lag criterion are one receiver (MUST-269), and no known tool reaches the one-sided √X lag scale (CANNOT-326). If step 2 lands there, the route stops.
- **Growth of the excess.** If the unconditional excess grows like log T, step 1 stops the route.
- **Neighbouring collision routes already closed:**
  - HC bounded-diagonal reception (F0102);
  - the HC filtered Gamma-six landing (F0228);
  - Chen–Gupta–Li packets, whose envelope is ≥ 288 (xi §8.6);
  - window enlargement: blocks larger than a pair are strictly harder to collapse (CANNOT-453).
- **Adjacency to the shifted-Euler (Suzuki) family.** The collision-by-real-shift picture is close to that de Branges-type family, which the ledger treats as a receiver (F0202, F0197).

## 6. Routes considered and set aside

| Route family | Reason from the ledger |
|-|-|
| Weil / explicit-formula positivity (restricted Weil, lag function, Gaussian and rectangular tests, Suzuki screw) | Positivity alone; the ledger calls these receivers; no known tool reaches the one-sided √X lag scale; exact prime weights are load-bearing, so no lossy input can work (xi §4.A.6–§4.A.8, §8.11–§8.12; CANNOT-326, MUST-232–MUST-256). Classical. |
| Regularity of the first-contact Weil minimizer (under ¬RH the ground energy vanishes at a unique aperture with a rough completion-boundary kernel) | A smoothness bootstrap would run on a symbol that grows only logarithmically; prime entry is log-soft; this hits the same one-log deficit (xi §2.15, §4.A.7; MUST-440; STATUS "Sonin strictness + aperture continuity is the live edge"). Close to the Connes–Consani line. |
| Hilbert–Pólya, self-adjoint and determinant realizations | Arbitrary real spectra have self-adjoint realizations; ordinates carry no displacement; trace-ideal and symmetrizer walls (CANNOT-08; xi §7.6, §8.24, §9.3). |
| de Bruijn–Newman, Calogero pair dynamics | No direction proves RH; no localized monotone observable exists for any pair kernel (CANNOT-455, CANNOT-456; xi §8.19). |
| Li / Keiper, Laguerre–Pólya, Jensen, Hankel and moment towers | Finite data never suffice; degree-uniformity is required; Jensen content lies at d≳n (xi §8.13–§8.15; CANNOT-321, CANNOT-322). |
| Mollifiers, Levinson, the off-line first moment (L) | Slope consumers cannot prove RH; the gate constant has an exponential floor (CANNOT-371, CANNOT-372; xi §8.17). |
| Cohomological, equivariant, K-theoretic and index routes | Localized invariants see only fixed points; RH is a coboundary (CANNOT-405, CANNOT-407, CANNOT-435); brief rule. |
| Integral descent: F₁ / Frobenius, common lattices, two-superghost and dyadic relative-reflection frames | Each integral frame is an external landing hypothesis; physical evaluation is real-valued; total multiplicity destroys the one-prime selector (F270–F280, F314, CANNOT-160). Rigidity alone; F₁ / Deligne is classical-adjacent. |
| Completion index, arithmetic Levinson exact sequence | Every Xi mode adds a matched kernel–cokernel pair, so the vacuum index cancels (F180, CANNOT-100). |
| Transverse equilibrium identity | There is no variational derivation (ξ is differentially transcendental), and the non-attained case remains (CANNOT-415, MUST-419). |
| Hermite–Biehler, trace-form signature | Already held in stronger form; the gap is strictness (MUST-438, MUST-439). Classical. |
| Two-sided bounded factorization, properness, compact route atlases | Compactness alone; countable compact atlases miss a residual set; normal stationary correspondences fail (F309, FAIL-38, CANNOT-108). |

## 7. Order of work

Cheap decisive checks come first. Every item names the previously unproved statement it would establish (MUST-40).

1. **Route 3, step 1.** Determine the unconditional growth of the two-prime Cesàro excess. If it is of order log T, Route 3 is retired and its falsification arm is kept as a certificate template.
2. **Route 1, steps 1, 3 and 6.** Put the boundary class and the chiral decomposition wind = κ₋ − κ₊ into Lean. Do the deformation audit on paper. This settles whether the core inequality is well posed and where exact Λ enters.
3. **Route 2, step 2.** Prove the continuation identity for 1+K up to the natural boundary on paper, including the stop test for complex zeros of the source.
4. **Route 1, steps 2 and 4.** Prove weak H^{1/2} convergence through the singular passage, then the bulk-to-boundary inequality κ₋(D) ≤ B_base < 1.

The new statement each route must establish:

| Route | Statement |
|-|-|
| 1 | κ₋(D) ≤ B_base for every admissible strict-right rectangle D, from literal Euler and continuum formation. |
| 2 | An exact boundary representation of 1+K through Q, and a count of the solutions of K = −1 that is specific to that level. |
| 3 | An exact identity between the thin-slice pair current and the two-prime excess, and a bound on the excess strictly below 2, uniform in height. |

Each of these is new relative to the ledger. Each would close RH only together with its deformation audit (test B).
