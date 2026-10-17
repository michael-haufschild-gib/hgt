# CHMD + HF + EWU Three-Option Synthesis: Odd-Profile Collar/Chain Bridge, Clamped First-Cell Resolvent Bound, and Polar Blind Spectral Gap

- **ID:** chmd-hf-ewu-three-options-2026-10-17
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/notes.md · docs/reports/rh-current-frontier-map.md
- **Statement:** Unconditional Lean 4 formalization of the three structural advances in `docs/notes.md`: (1) `CHMD` secondary odd-$m_a$ Doob collar absorption, prime-chain variance bridge, and reflected collar compensation; (2) `HF` clamped / $S(F)$-free rational-resolvent first-cell quadrature bound and tail-cell ($n \ge 3$) variance localization; (3) `EWU` doubly polar-constrained smooth even prime-blind kinetic spectral gap ($S > 27 L$) and clamped resolvent balance.

## Goal
Advance the three coupled bottlenecks identified in `docs/notes.md` toward a formal Lean 4 proof of the Riemann Hypothesis:
1. **Option 1 (`CHMD` Secondary Odd-$m_a$ Doob + Divisor-Chain Factorization):** Connect the odd ground profile factorization $f(x) = m_a(x) w(x) = \Theta(x) (\Psi_a(x) w(x))$ ($w$ even) in `CHMDOddHarmonicIdentityAndPolarDoobAbsorption.lean` to the complete divisor-chain variance factorization in `CHMDPrimeChainSourceFactorization.lean` and `CHMDReflectedPrimeSingularPart.lean`, proving the archimedean collar absorption integral, the exact algebraic identity between the $\Theta$-Doob collar killing density and the $m_a$-Doob pure Dirichlet collar jump, and convex gauge interpolation between the positive divisor-chain variances and the positive $+2\int_0^\infty m_a\sinh(x/2)w^2\,dx$ pole potential.
2. **Option 2 (`HF` Clamped High-Frequency $I_2(r)$ + Uncertainty Gap / Euler–Maclaurin Audit):** Replace the unbounded $r=0$ Taylor parabola $I_2(r) \ge -(7/480) r^2$ at high frequencies by exploiting the exact $(1/4+r^2)$ identity in `MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP.lean` to derive an $S(F)$-free rational-resolvent lower bound and a clamped two-regime bound $-\min((7/480)r^2, C_\infty) \le I_2(r)$, and prove that under the exact Euler–Maclaurin conservation law on the primitive prime-blind cone (`coshHalfMoment = 0`, `logVector = 0`), high-frequency kinetic oscillation is forced out of the $n=2$ cell into the tail cells $n \ge 3$.
3. **Option 3 (`EWU` + Clamped `HF` / Doubly Polar-Constrained Even Blind Spectral Gap):** Bridge `EWU` (`SmoothEvenPolarTestFn` in `EvenSectorExactMomentRealization.lean` / `EvenSectorBlindMinimumSmallAperturePositivity.lean`) with the `HF` Euler–Maclaurin conservation hierarchy by proving that every smooth even polar test satisfies BOTH `coshHalfMoment = 0` and `sinhHalfMoment = 0` (`weilPoleTerm = 0`), yielding the exact pole-free conservation law `rightCellQuadratureDefect + bochnerResolventEnergy = 0`, the unconditional 27-ratio kinetic spectral gap $S(f) > 27 L(f)$ on every nonzero prime-blind smooth even polar test, and the clamped $S(f)$-free first-cell resolvent balance.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems compiled with `lake build --old` and `lake env lean`, `scripts/formal_tools.py lint` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
1. **Module 1 (`formal/GaloisForLFunctions/RHTower/CHMDOddProfileArchAbsorptionAndPrimeChainBridge.lean`):**
   - Prove the full-line to half-line archimedean collar-absorption integral theorem for $f = m_a w$ ($w$ even).
   - Relate `oddProfileTest a w` to `phiDoobTest (oddPolarFunction a * w)` and plug $v = \Psi_a w$ (which is odd when $w$ is even) into `doob_source_eq_chain_variances_sub_cosh` and `reflected_compensation_hasSum_chains`.
   - Establish the exact pointwise and integral comparison between the $\Theta$-Doob collar and the $m_a$-Doob pure Dirichlet difference collar, short-support / reflection-symmetric collar vanishing, and the $\theta \in [0,1]$ convex gauge interpolation combining nonnegative divisor-chain variances with the positive $m_a\sinh(x/2)$ potential.
2. **Module 2 (`formal/GaloisForLFunctions/RHTower/MarkovClampedFirstCellAndTailVarianceLocalizationPBAP.lean`):**
   - Divide `neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq` by $1/4+r^2 > 0$ to prove an explicit rational-resolvent lower bound on $I_2(r)$ depending only on $1$ and $1/(1/4+r^2)$ (zero $r^2$ growth!) and the clamped bound $-\min((7/480)r^2, C_\infty) \le I_2(r)$.
   - Integrate against $\|F(r)\|^2 / (2\pi)$ to obtain an $S(F)$-free lower bound on the first-cell quadrature integral in terms of $\|F\|_2^2$ and `bochnerResolventEnergy`, plus a two-regime clamped spectral bound.
   - Combine with the exact Euler–Maclaurin conservation law on `coshHalfMoment = 0` and `logVector = 0` to prove **Tail-Cell Variance Localization**: any prime-blind test's high-frequency kinetic energy cannot be absorbed by the $n=2$ cell and is forced into the tail cells $n \ge 3$.
3. **Module 3 (`formal/GaloisForLFunctions/RHTower/EvenSectorPolarBlindSpectralGapAndClampedQuadrature.lean`):**
   - Prove `coshHalfMoment = 0` and `sinhHalfMoment = 0` for all `f : SmoothEvenPolarTestFn`.
   - Deduce the pole-free Euler–Maclaurin conservation law `rightCellQuadratureDefect + bochnerResolventEnergy = 0`, the strict kinetic spectral gap `27 * ∫ ‖f‖² < spectralSecondMoment f`, and the clamped / $S(f)$-free first-cell resolvent balance on every nonzero prime-blind `SmoothEvenPolarTestFn`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** In Option 2, `unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero` is an exact identity on `logVector F = 0`: the sum of the full right-cell quadrature defect, the Bochner resolvent energy, and $+2\operatorname{sinhHalfMoment}(f)^2$ is identically zero. Thus clamping $I_2(r)$ on the $n=2$ cell alone cannot make `rightCellQuadratureDefect + bochnerResolventEnergy + 2 sinhHalfMoment² > 0` on `logVector F = 0`.
- **Strongest positive survivor:** The exact $(1/4+r^2)$ resolvent division on the $n=2$ cell eliminates $S(F) = \int r^2|F(r)|^2\,dr$ completely from the first-cell lower bound, bounding $\int_1^2 \frac{C_f(x)-\operatorname{cellSecant}(C_f,2,x)}{\sqrt{x}}\,dx$ from below purely by $\|f\|_2^2$ and `bochnerResolventEnergy` (and via the clamped $\min((7/480)r^2, C_\infty)$ law), which—combined with the conservation identity—forces all unbounded high-frequency defect into the tail cells $n \ge 3$ (`tailCellQuadratureDefect`).
- **New insight:** Separates the $O(1)$ bounded-symbol first-cell regime ($n=2$) from the Euler–Maclaurin tail ($n \ge 3$), and shows that on the doubly polar-constrained even sector (`EWU`), the pole term $+2\operatorname{sinhHalfMoment}(f)^2$ vanishes identically, transferring the entire 27-ratio kinetic spectral gap and clamped resolvent bounds unconditionally to `SmoothEvenPolarTestFn`.
- **Status:** In progress; formalizing all three modules in Lean 4.

## Log
- 2026-10-17 — created in 1-in-progress
