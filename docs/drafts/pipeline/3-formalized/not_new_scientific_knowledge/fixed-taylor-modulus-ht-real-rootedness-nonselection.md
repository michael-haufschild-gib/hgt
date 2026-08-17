# Fixed Taylor Moduli and HT Status Do Not Select Real-Rootedness

- **ID:** `fixed-taylor-modulus-ht-real-rootedness-nonselection`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / HT LANDSCAPE BRIDGE / RH-ROUTE NONSELECTION
- **Scientific status:** `[PROVED HERE] [BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** There is one full-support Taylor-modulus profile supporting both an HT entire function whose complete divisor is real and an HT entire function with a nonreal zero. Thus HT status together with all Taylor magnitudes, Newton data, order, and type cannot select real-rootedness.

## Goal

Strengthen fixed-modulus divisor blindness from “the divisor varies” to the exact qualitative property analogous to RH localization. The result is not a zeta theorem. It classifies the information lost by the quotient

`entire function |-> (HT/DA status, (|a_n|)_n)`.

## Tail-prevalence lemma `[PROVED HERE]`

Let `(r_n)` be positive and satisfy

`limsup_(n->infinity) r_n^(1/n)=0`.                                       `(1)`

For phases `theta=(theta_n)` in the infinite torus `T^N`, put

`F_theta(z)=sum_(n>=0)r_n exp(i theta_n)z^n`.                              `(2)`

Fix any `K>=0` and prescribe arbitrarily the phases `theta_0,...,theta_K`. In the remaining product torus, the phase completions for which `F_theta` is HT over `C(z)` form a dense `G_delta` set of full product Haar measure.

### Proof

Condition (1) makes every series (2) entire. By Mahler's integer-normalization theorem, every DA series satisfies at least one nonzero ADE

`P(z,F,F',...,F^(m))=0`, `P in Z[z,Y_0,...,Y_m]`.                          `(3)`

There are only countably many such `P`.

Fix one `P`, and let `D` be its maximal total `Y`-degree. Generic coefficient extraction gives finite polynomials

`C_(P,N)(X)=[z^N]P(z,F,F',...,F^(m))`.                                    `(4)`

If `D=0`, no series can satisfy `P(z)=0` unless `P` is the zero polynomial, so its solution set is empty. Assume `D>=1`.

The balanced-survival lemma supplies, for every sufficiently large `N`, a nonzero grouped degree-`D` monomial in (4) whose source indices are all `N/D+O_P(1)`. Choose `N` so large that these indices exceed `K`.

After substituting the prescribed prefix coefficients, (4) remains a nonzero polynomial in the tail variables. Indeed, the surviving monomial has tail degree `D` and uses no prefix variable. No other monomial involving a prefix variable can collapse onto it after specialization, because that would have the same tail degree `D` and positive prefix degree, exceeding the maximal total degree `D`.

On the fixed-radius tail torus, this nonzero polynomial becomes a nonzero trigonometric polynomial in finitely many phases: distinct coefficient monomials are distinct Fourier characters, and every `r_n` is nonzero. Its zero set has Haar measure zero and empty interior. This follows directly by induction on the number of variables: regard it as a one-variable Laurent polynomial and apply Fubini outside the lower-dimensional set on which all coefficient polynomials vanish.

The phase set solving the complete ADE (3) is closed and is contained in this nowhere-dense null zero set. Taking the countable union over all integer `P`, the DA phase completions form a meagre Haar-null set. Their complement is dense `G_delta`, has full Haar measure, and consists exactly of HT completions. `square`

## Real-rootedness nonselection theorem `[PROVED HERE]`

There is a positive full-support sequence `(r_n)` and phases `theta`, `phi` such that

1. `F_theta` and `F_phi` are both HT over `C(z)`;
2. their Taylor coefficients have identical moduli `r_n` term by term;
3. every zero of `F_theta` is real;
4. `F_phi` has a nonreal zero.

### Proof

Let `E(z)=1/Gamma(z)`. Every derivative `E^(n)` is a nonzero entire function: otherwise `E` would be a polynomial, contrary to its infinite zero set. The union over `n` of the real zero sets of `E^(n)` is countable. Choose a positive real `x` outside this union and put

`G(z)=E(z+x)=sum_(n>=0)a_nz^n`.                                           `(5)`

Then every `a_n=E^(n)(x)/n!` is real and nonzero. The zeros of `G` are the simple negative real points

`rho_j=-x-j`, `j>=0`.                                                      `(6)`

The function `G` is HT: if `1/Gamma(z+x)` were DA, translation and reciprocal closure of the DA field would make `Gamma` DA, contradicting Hölder's theorem.

Put `r_n=|a_n|`. These radii satisfy (1) because `G` is entire. Thus `G` is one HT member of the fixed-modulus phase fiber and has a completely real divisor.

Now rotate only the constant coefficient:

`G_t(z)=G(z)+(exp(it)-1)a_0`.                                              `(7)`

Every Taylor coefficient of `G_t` has modulus `r_n`. Fix a zero `rho_j`. By the analytic implicit-function theorem, its continuation `rho_j(t)` satisfies

`rho_j'(0)=-i a_0/G'(rho_j)`.                                              `(8)`

Both `a_0` and `G'(rho_j)` are nonzero real numbers, so (8) is nonzero and purely imaginary. Hence `G_t` has a nonreal simple zero for all sufficiently small real `t` of one sign.

Choose such a `t_0`. A small disk around that nonreal zero, disjoint from the real axis, remains a one-zero disk under sufficiently small compact-open perturbations by Rouche's theorem. The map from the phase torus to entire functions is continuous for the compact-open topology: a finite coefficient head is continuous, and (1) makes the uncontrolled tail uniformly small on each fixed compact set. Therefore the set of phases in the same modulus fiber whose function has a nonreal zero contains a nonempty open neighborhood of the phase of `G_(t_0)`.

By the tail-prevalence lemma, HT phases are dense in this fiber. The open neighborhood contains an HT phase `phi`; its function has a nonreal zero and the same coefficient moduli as `G`. Take `theta` to be the phase sequence of `G`. `square`

## Consequences

The two functions have identical:

- Taylor coefficient magnitudes;
- logarithmic Newton polygon and maximum-term function;
- order and type;
- support;
- HT status.

They disagree on real-rootedness. Therefore no selector factoring only through those common data can imply a zero-line statement on the full class of entire functions.

For RH routes, the scope is exact and limited: this excludes only implementations of Hilbert--Polya, Connes, de Branges, Weil, Li, Nyman--Beurling, heat-flow, or coefficient methods that first compress the relevant entire function to this phase-blind quotient. The complete literature criteria retain additional spectral, positivity, norm, heat, Euler, or divisor information and are not excluded by this theorem.

## Why this is not classified as new science

The proof combines Hölder's theorem, countability after Mahler normalization, the elementary zero-set theorem for trigonometric polynomials, Baire/Haar genericity, and the implicit-function theorem. The fixed-modulus and real-rootedness formulation is useful for the project, but the mechanism is a direct genericity bridge rather than a new HT obstruction. No scientific-novelty claim is made.

## Lean status

**Formalized unconditionally, 2026-08-17** — see the Lean formalization section below. The earlier assessment (that Mahler normalization, generic coefficient extraction, balanced survival, product Haar measure and Baire category would all be needed) was based on routing the construction through the tail-prevalence lemma; the formal proof does not need that route, for the reason recorded below.

## Gates

- [x] Complete unconditional paper proof.
- [x] Same full-support moduli and HT status on both sides.
- [x] All-real divisor versus nonreal zero.
- [x] Exact noncategorical RH-route scope.
- [x] Whole theorem formalized unconditionally in Lean — `fixedModulus_hypertranscendence_real_rootedness_nonselection`.

## Log

- 2026-07-11 — Proved tail-Haar prevalence of HT phases and constructed one fixed-modulus HT fiber containing both an all-real-zero reciprocal-Gamma translate and an HT member with a nonreal zero.

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/HTGeometry/FixedModulusRealRootednessNonselection.lean`
(wired into the `GaloisForLFunctions.HTGeometry` umbrella).

The capstone is

```
fixedModulus_hypertranscendence_real_rootedness_nonselection :
  ∃ f g : ℂ → ℂ,
    ContDiff ℂ ⊤ f ∧ ContDiff ℂ ⊤ g ∧
    Hypertranscendental f ∧ Hypertranscendental g ∧
    (∀ n, ‖coeff n (taylorPS f)‖ = ‖coeff n (taylorPS g)‖) ∧
    (∀ n, coeff n (taylorPS f) ≠ 0) ∧
    (∀ z, f z = 0 → z.im = 0) ∧ {z | f z = 0}.Infinite ∧
    (∃ z, g z = 0 ∧ z.im ≠ 0)
```

together with two restatements: `exists_common_modulus_profile_phases` puts the pair in the card's
phase form `a_n = r_n e^{iθ_n}` with `r_n > 0` for every `n`, and `modulusProfile_selector_blind`
states the Consequences section as a theorem — for **every** map `Φ` on modulus profiles, `Φ` agrees
on the two functions, so no selector factoring through `(|a_n|)_n` can imply real-rootedness.

| Card step | Lean name |
|---|---|
| `G = 1/Γ(· + x)` is entire | `analyticOnNhd_reciprocalGammaTranslate`, `contDiff_realCarrier` |
| Hölder: every reciprocal-Gamma translate is HT | `hypertranscendental_reciprocalGammaTranslate` |
| every derivative `E⁽ⁿ⁾` is a nonzero entire function | `exists_iteratedDeriv_ne_zero_of_hypertranscendental` |
| choice of `x` outside the countable union of derivative zero sets | `exists_pos_base_all_iteratedDeriv_ne_zero`, `fmBase` |
| zeros of `G` are exactly the simple real points `−x−j` | `realCarrier_eq_zero_iff`, `im_eq_zero_of_realCarrier_eq_zero`, `infinite_zeros_realCarrier` |
| `r_n = \|a_n\|` is full support | `coeff_taylorPS_realCarrier_ne_zero` |
| rotate the constant coefficient: `G_t = G + (e^{it}−1)a₀` | `phaseUnit`, `phaseCarrier` |
| identical Taylor moduli | `norm_coeff_phaseCarrier` |
| `G_t` is hypertranscendental | `hypertranscendental_phaseCarrier` |
| implicit-function motion `ρ'(0) = −i a₀/G'(ρ)` off the real axis | `exists_perturbed_zero_off_axis` |
| `G_t` has a nonreal zero for a suitable small `t` | `exists_phase_nonreal_zero` |

### Two deliberate route changes

1. **The tail-prevalence lemma is not needed and is not used.**  The card reaches the second member
   of the fibre by showing that HT phases are dense in the modulus fibre and picking an HT phase in
   the open set of phases whose function has a nonreal zero.  That detour is unnecessary: the phase
   rotation the card itself performs changes only the *constant* Taylor coefficient, so
   `G_t = G + c` differs from `G` by an additive constant, and adding a polynomial never changes
   differential algebraicity (`hypertranscendental_add_polynomial_iff`).  Hence `G_t` is
   hypertranscendental for **every** `t`, with no genericity input at all.  Consequently Mahler's
   integer-normalization theorem, generic coefficient extraction, balanced survival, the
   trigonometric-polynomial zero-set lemma, product Haar measure and Baire category — the whole
   apparatus of §"Tail-prevalence lemma" — are absent from the formal proof.

   The tail-prevalence lemma itself is therefore **not formalized, and is not an obligation of this
   card's theorem**: it is a sufficient-but-unnecessary intermediate step for the stated result.  It
   remains a correct standalone statement of independent interest; formalizing it would be a
   separate project.  (The corpus does already own its two hardest ingredients:
   `HTGeometry/FormalMahlerIntegerNormalization.lean` for the integer normalization and
   `HTGeometry/PrescribedResidueBalancedAtom.lean` for balanced survival.)

2. **The full-support base point is chosen from hypertranscendence, not from "E is not a
   polynomial".**  The card argues that `E⁽ⁿ⁾ ≢ 0` because otherwise `E` would be a polynomial with
   infinitely many zeros.  The formal proof observes instead that `E⁽ⁿ⁾ ≡ 0` is *already* an
   algebraic differential equation — the jet variable `Yₙ` is a nonzero differential polynomial — so
   it contradicts Hölder's theorem directly.  Each `E⁽ⁿ⁾` is then a nonzero entire function, its
   real zero set is countable (`HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd`), and the
   countable union of these sets cannot cover `(0,∞)`.

   Similarly, `Rouché` is not used: transversality of the moving zero is obtained from the analytic
   inverse function theorem (`HasStrictDerivAt.localInverse`) plus the first-order slope of
   `t ↦ Im ρ(t)` at `t = 0`, which is exactly the card's `ρ_j'(0) = −i a₀/G'(ρ_j)` computation.  The
   realness inputs the card needs are `a₀ = 1/Γ(x) > 0` (real positive for real `x > 0`) and
   `G'(−x) = E'(0) = 1` (`hasDerivAt_oneDivGamma_neg_nat 0`); the base zero `j = 0` already gives a
   nonzero purely imaginary velocity, so no digamma value is required.

Verification: `lake build GaloisForLFunctions.HTGeometry.FixedModulusRealRootednessNonselection` —
PASS; `#print axioms` on all thirteen named results reports only
`[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-17 — Formalized unconditionally in Lean 4 and promoted to stage 3.  The real-rootedness
  nonselection theorem, its phase-form restatement, and the modulus-profile selector-blindness
  corollary are unconditional Lean theorems; the tail-prevalence lemma is documented above as a
  bypassed intermediate route.
