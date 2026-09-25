## Sub-quantum chiral loss through the Gaussian Euler–continuum passage
The winding of strict-right rectangles is an exact integer, and a pre-divisor sub-unit budget B_base<1 already exists. The claim is that the H^{1/2} degree lost in the singular passage into the strip stays below one quantum.

### Statement to prove

Let D be a pre-divisor admissible strict-right rectangle (inside ½<Re s<1, with ξ≠0 on ∂D). Let u_{D,x}=Φ_x/|Φ_x| on ∂D be the boundary phase of the zero-free Gaussian Euler–continuum family, and let u_D be the Xi boundary phase. Write κ₋(D) for the negative-chirality Hankel energy lost as x→0. The claim is κ₋(D) < 1 for every such D.

Consequence: along weakly convergent zero-winding phases wind(u_D) = κ₋ − κ₊ (F448 [P]). wind(u_{D,x}) = 0 because Φ_x is zero-free, and wind(u_D) is the enclosed multiplicity, so it is ≥ 0. Hence 0 ≤ wind(u_D) ≤ κ₋ < 1, and wind(u_D) = 0 for every D. There is no zero with ½<Re ρ<1, and RH follows by the functional equation.

### Ledger evidence

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

### Program

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

### Falsification arm

- Under ¬RH, some admissible strict-right D has wind ≥ 1. There the identity E_Euler = E_reduced + Tr T_D forces E_reduced ≤ B_base − 1 < 0.
- So a failure of positive reduction is concentrated on rectangles around off-line zeros; it cannot be diffuse. At finite x the negative-chirality energy density is computable from literal prime data, and its build-up toward one quantum localizes candidate rectangles.
- A falsification is then a certified argument-principle winding on an explicit ∂D (interval arithmetic on ξ), in the shape of the finite local certificates of xi §4.B and endpoint F0190. By xi §3.1 [C], such a rectangle lies above ordinate 3·10¹², so this arm serves as a localizer, not as a search program.

### Main risks

- **Budget order.** The raw positive cubic Euler/Wold mismatch is not sub-unit: its prime-two atom is (95/16)(log 2)³ > 1, and identity-scale landing overshoots by a factor >2000. Only the cubic-gauged B_base is below 1. If the transgression lands on the raw mismatch, the route fails (F441, CANNOT-211).
- **Orientation.** An even invariant cannot produce the odd charge (F487–F489). Step 4 must pair metric and odd current inside one identity.
- **The passage.** The ledger states convergence Φ_x→ξ only on Re s>1 (xi §1.2). If step 2 fails, the relative cubic defect carries no scalar budget without a matrix-complete action map (CANNOT-222).
- **Nearby failed sub-mechanisms** (FAIL-81–FAIL-93): Beta/Jacobi diffusion, generic dilation, fixed-scale clocks, scalar outer completion, finite monitored unitaries, continuous multiplicative completion. Step 4 must not reduce to any of them.