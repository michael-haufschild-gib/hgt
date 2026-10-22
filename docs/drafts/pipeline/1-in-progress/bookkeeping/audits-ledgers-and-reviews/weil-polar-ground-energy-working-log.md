# Constrained (pole-vanishing) Weil form — working log

Route-specific working log for the restricted / pole-vanishing Weil positivity programme
(`CCMRestrictedWeilPolar*` modules, ground energy `μ₀`, degeneracy threshold, numerics in
`2-fully-proven/computations/weil-polar-ground-energy/`).  Moved here on 2026-09-04 from
`universal-law-field/STATUS.md`, which records only what the solution object MUST / CANNOT be.
Labels `Fnnn` / `MUST-nnn` are historical ledger numbers; `MUST-nnn` here are route tasks or
route-level facts, not constraints on the object.

---

## 2026-09-03 (viii–ix) — constrained Weil continuity and ground energy
F403/MUST-141 — Lean: a positive constrained Weil Rayleigh floor persists on a right aperture
neighborhood, including prime entries. The remaining quantitative input is Connes–Consani's
pole-vanishing Sonin inequality at `√2`.
F404/F405 — Lean: nonzero pole-vanishing smooth interior sources exist and are dense; ground energy
`μ₀` is antitone and continuous, and strict positivity is open.
MUST-142 — `WEIL-ENTRY-001` is Lean-closed modulo published numerical certificate
`μ₀(√2)>0` (margin about `0.3%`); qualitative prime-2 crossing is formal, quantitative crossing is
that one external number.
## 2026-09-03 (x) — degeneracy threshold of the pole-vanishing Weil form
F406 — Lean (`RHTower.CCMRestrictedWeilPolarGroundState`): the pole-vanishing ground energy is
attained; either it is positive at every aperture or it vanishes at a unique threshold with an
attained normalized pole-vanishing null vector and nonnegativity on the pole-vanishing subspace.
MUST-143 — Failure of Weil positivity on the pole-vanishing subspace, if it happens, is a
degenerate threshold `a*` with an attained null vector; prime entries cannot cause it
discontinuously; given Connes–Consani, `a* > (log 2)/2`. The remaining links to RH itself
(RH ⇒ no threshold by zero density; no threshold ⇒ RH by the `s(s−1)` multiplier) are paper-level.
## 2026-09-03 (xi) — pole-vanishing multiplier; RH-link status
F407 — Lean (`RHTower.CCMRestrictedWeilPolarMultiplier`): `∫ e^{sx} g'' = s² ∫ e^{sx} g` for smooth
compactly supported `g`; the operator `∂² − 1/4` sends every strict-interior source to a
pole-vanishing one (`isPolarConstrained_polarMultiplier`). The pole-vanishing smooth core is the
image of `∂² − 1/4` (converse on paper via the Green kernel `−e^{−|x|/2}`).
MUST-144 — The link `μ₀ > 0 everywhere ⇒ RH` is Bombieri–Yoshida's pole-vanishing Weil criterion;
the corpus cannot currently formalize it (two-bump localization is not pole-vanishing; the
explicit formula stops at the resolvent algebra). It is a known theorem, so it is recorded, not
pursued. The archimedean form alone is indefinite on the pole-vanishing subspace at large
apertures (Fourier mass near `|ξ| = 1/2` where `θ′ < 0`), so primes are necessary there.
- **Nugget:** the pole-vanishing subspace is the range of `∂² − 1/4`, the operator with Mellin
  symbol `s(s−1)`; Weil's pole terms and the two pole constraints are the same two-dimensional
  space seen from the test side and the zero side.
## 2026-09-03 (xii) — numerical study of the pole-vanishing Weil form
F408 — Computation (RunPod, report in `2-fully-proven/computations/weil-polar-ground-energy/`):
`μ₀(√2) = 0.54704` with second eigenvalue 0.84; `μ₀(a) > 0` at every aperture tested, converged
through `λ ≈ 2.1` and decaying super-exponentially after; archimedean-only positivity on the
pole-vanishing subspace ends at `λ_arch = 1.81451`; each prime power becomes necessary within
0.01–0.02 of aperture after its entry. Upper-bound numerics with convergence control, not
interval-certified.
MUST-145 — Numerically the constrained input of Theorem D holds with an order-one margin, and no
degeneracy threshold exists below `λ ≈ 5`; the analytic wall is unchanged (a Galerkin minimum is
an upper bound, so positivity is evidence, negativity is proof). New quantitative facts: the
archimedean threshold `λ_arch = 1.8145` and the immediate necessity of each entering prime.
F409 — Computation: the pole-vanishing ground state's Fourier zeros converge to the zeta
ordinates (eight zeros to `10⁻³` by `a = 0.9`), like the full ground state of Connes–Consani–
Moscovici; the spectral realization does not depend on the pole terms.

## 2026-09-04 — three deliverables opened (card `weil-polar-bombieri-yoshida-prime-two-entry.md`)
WP-T1 (BY): pole-vanishing ground energy ≥ 0 at all apertures ⇒ RH, via a discrete multiplier
`M(γ) = (e^{iγh}−1)(e^{iγh}−e^{h/2})(e^{iγh}−e^{−h/2})` acting by translates, the twisted ray energy, and a
weighted Widder–Landau engine (plan in the card).
WP-T2 (P2): analytic prime-2 entry — Connes–Consani's computer-checked step (115) to be replaced; explicit range.
WP-T3 (GM): Guth–Maynard-type large-values theorem in Lean.

## 2026-09-04 — WP-T1 (BY) closed
Lean: `riemannHypothesis_of_polarGroundEnergy_nonneg` (five modules; card
`3-formalized/constrained-weil-bombieri-yoshida-lean.md`).  MUST-144 resolved: the pole-vanishing Weil
criterion's hard direction is formal, via translate multipliers + a weighted Widder–Landau engine + a pole
contradiction on the connected punctured half-plane.  Open follow-up: the converse RH ⇒ μ₀^{pol} ≥ 0
(density + continuity of the form), and the strict-positivity refinement.

## 2026-09-04 — WP-T2 (P2): elementary certificate found
On `V₀` the archimedean form is `A(S)‖f‖² + ∫₀^S ½‖f−T_uf‖²K₊(u)du` with `K₊ > 0` (polar and negative
kernel parts cancel exactly), i.e. a Fourier multiplier `m_S = A(S) + Λ_S` with one negative band; the
constrained minimum at √2 (0.5425, extremal `≈ 0.87p₂ + 0.48p₄`) is certified by Taylor localization +
staircase + a finite constrained block: margin 0.43 at √2; archimedean positivity certified to λ ≈ 1.57;
with the prime 2 to λ = 1.433 (> √2). Floating-point stage; interval evaluation next. Card
`weil-polar-bombieri-yoshida-prime-two-entry.md` §(P2).

### WP-T4 (2026-09-04) — rigorous certificate v2 and the Lean kernel form
- `certificate_rigorous.py` (pod `/root/weil`, mpmath 25 digits, every series with a proven tail bound,
  band width 0.05, Lipschitz grid δ = 0.005, Ξ = 24, far tail by the elementary bound
  `m_S(ξ) ≥ A + γ + log(Sξ) − 2/(Sξ) + S/2 − 1/(2ξ) − S²/4 − S/(2ξ) − 1/ξ²`, penalised constrained
  eigenvalue as the rigorous lower bound of the finite block, Taylor localisation `M_low ≈ 10⁻¹²`).
  Certified constrained ground energy (full form, all visible prime powers):

  | S | λ = e^{S/2} | N | certified lower bound | finite block with exact multiplier |
  |---|---|---|---|---|
  | log 2 | 1.4142 | 29 | 0.5177 | 0.5223 |
  | 0.72 | 1.4333 | 30 | 0.2505 | 0.2606 |
  | 0.80 | 1.4918 | 33 | 0.1100 | 0.1244 |
  | 0.90 | 1.5683 | 37 | **0.0173** | 0.0341 |
  | 1.00 | 1.6487 | 41 | −0.0141 (not certified) | 0.0029 |

  So the constrained restricted Weil form is certified positive up to `S = 0.9` (`λ ≈ 1.568`), past
  the Connes–Consani aperture `√2`, with the prime 2 inside.  The finite-block value at `S = 1.0`
  (`0.003`) shows the true threshold of the *full* form is near `S ≈ 1.0` (`λ ≈ 1.65`); the earlier
  "threshold 1.19" was the archimedean-only form.  A first run with width 0.25 had a far-tail bound
  carrying a spurious factor `e^{−S/2}`; fixed.  An earlier version dropped the prime-2 term for
  `S ≥ log 3`; fixed (all `n ≥ 2` with `log n < S`, coefficient `2Λ(n)/√n`).
- Lean: `RHTower/SuzukiWeilConstrainedKernelForm.lean` (wired after `CCMRestrictedWeilPolarBombieriYoshida`):
  `suzukiRestrictedWeilForm_eq_constrainedKernelForm` — Suzuki's form equals
  `A(S) g(0) + ∫_0^S K₊(h)(g(0) − g(h)) dh + 2(∫e^{x/2}u)(∫e^{−x/2}u) + prime block`, with
  `K₊ = e^{h/2}/sinh h = 2e^{−h/2}/(1−e^{−2h})` and
  `A(S) = −γ − log π − log(1−e^{−2S}) − ∫_0^S (e^{h/2}−e^{−h})/sinh h`, exactly the constants of the
  certificate; `_of_moment_eq_zero` drops the pole term on the polar-constrained subspace;
  `integral_weilPositiveKernel_mul_defect_nonneg`.  Axioms `[propext, Classical.choice, Quot.sound]`.
  This closes the "classical, not formalized" clause of the kernel-sign card for the Suzuki form.

### WP-T5 (2026-09-04) — Fourier-multiplier form in Lean; certificate at S = 0.98
- `RHTower/ConstrainedWeilFourierMultiplier.lean` (wired after `ConstrainedWeilTaylorLocalization`; axioms
  `[propext, Classical.choice, Quot.sound]`):
  `autocorrelationSchwartz_eq_integral_fourier` (`g(h) = ∫ ‖𝓕u‖² 𝐞(ξh)`, Fourier inversion of the
  Schwartz autocorrelation via the corpus `fourier_autocorrelationSchwartz`),
  `suzukiCoreAutocorrelation_eq_integral_fourier_cos`, the Tonelli step
  `integral_weilPositiveKernel_mul_defect_eq_fourier` (majorant `K₊(h)h²·2π²ξ²F(ξ)`,
  `weilPositiveKernel_mul_sq_le`), and the endpoint
  `suzukiRestrictedWeilForm_eq_integral_multiplier_of_moment_eq_zero`:
  on the polar-constrained subspace `Q(u) = ∫ ‖𝓕u(ξ)‖² m_S(2πξ) dξ` with
  `weilConstrainedMultiplier S η = A(S) + Λ_S(η) − 2 Σ_{2≤n≤e^S} Λ(n)n^{−1/2} cos(η log n)` — literally
  the multiplier certified band by band.  Corollary `suzukiRestrictedWeilForm_ge_of_multiplier_ge`
  (uniform lower bound of `m_S` ⇒ lower bound of `Q` by that multiple of `‖u‖²`).
- Certificate at `S = 0.98` (width 0.01, `N = 40`): **0.00244 > 0** (`λ = e^{0.49} = 1.632`).
- What is left in Lean for the certificate chain: the staircase assembly (band projections,
  finite Legendre block, `Ω`-form) — the finite block itself stays a documented computation.

### WP-T6 (2026-09-04) — staircase assembly in Lean
- `RHTower/ConstrainedWeilStaircaseAssembly.lean` (wired after `ConstrainedWeilFourierMultiplier`; axioms
  clean): `BandProjections` (finite family of mutually orthogonal self-adjoint idempotents in a real inner
  product space), `staircaseForm c cinf v w = Σ_b c_b⟪v,P_b w⟫ + cinf(⟪v,w⟫ − Σ_b⟪v,P_b w⟫)`, Bessel
  `sum_inner_P_le`, high block `staircaseForm_self_ge_high`
  (`q(z) ≥ (c_∞ − (c_∞−c_min)⁺M)‖z‖²`), cross term `abs_staircaseForm_le_cross`
  (`|q(y,z)| ≤ D√M‖y‖‖z‖` for `y ⊥ z`), the scalar `two_by_two_certificate`, and the assembly
  `staircaseForm_ge_of_certificate`: `q(y+z) ≥ κ‖y+z‖²` from the low-block bound, the localisation
  bound, and the `2×2` conditions.  This is exactly the `Ω` step of `certificate_rigorous.py`.
- Lean chain for the certificate now: literal Suzuki form → kernel form → Fourier multiplier `m_S` →
  (staircase `m_S ≥ m_stair` + Taylor localisation `M_low` + finite block) → assembly.  Not in Lean:
  the identification of the Legendre-block Gram entries with the band projections of the multiplier
  form (a routine but long Fourier-side computation) and the finite numerical block.

### WP-T7 (2026-09-04) — correction and S = 1
- `S = 1.0` certified at band width 0.005: `μ₀(1) ≥ 0.0014` (`λ = √e`).  `S = 1.02`: −0.0003 (not certified).
- Retracted: the "threshold `S* ≈ 1.05`" reading.  The exact-multiplier finite block replaces the tail
  multiplier by `c_last` and is a lower bound of one Rayleigh quotient, not an upper bound of `μ₀`.
  Rigorous upper bounds: `certificate_upper.py` (endpoint-vanishing `V₀` test function, `|f̂| ≤ W/ξ²`).
- Position of the lane in the corpus audit (`rh-current-frontier-map.md`, branch O, gates `ORD COF`):
  the open core is the finite Gamma–Slepian head inequality *at every aperture* passed through a
  cofinal aperture family.  A certificate at fixed aperture is a receiver-side computation; it cannot
  produce the cofinal statement.  Guth–Maynard: the corpus proves `guthMaynard_inert`
  (`HTGeometry/LindelofPivotCoincidences`) — the GM bound never improves the classical bound at the
  Lindelöf pivot — so formalising GM Theorem 1.1 has no RH-lane consumer here; the GM card is parked.

### WP-T8 (2026-09-04) — two-sided bracket of μ₀(S)
- `certificate_upper.py` (pod, derivative-energy tail penalty, Ξ₂ = 1000): μ₀(log 2) ∈ [0.5177, 0.5515],
  μ₀(0.9) ∈ [0.0173, 0.0693], μ₀(1.0) ∈ [0.0014, 0.0131], μ₀(1.05) ≤ 0.0042.  The gap is the staircase
  loss on the lower side and the finite-N truncation on the upper side; no sign change anywhere.
