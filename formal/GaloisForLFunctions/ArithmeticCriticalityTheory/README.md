# Arithmetic Criticality Theory (`GaloisForLFunctions.ArithmeticCriticalityTheory`)

Positive solutions, ground-state representations and criticality of the arithmetic jump operator
whose nonnegativity on odd tests is the Riemann Hypothesis.

Pointers: proposal in [docs/reports/review-1910/fable.md](../../../docs/reports/review-1910/fable.md)
Section 4; progress log and status on the pipeline card
`docs/drafts/pipeline/1-in-progress/act-arithmetic-criticality-theory-2026-10-19.md`. This file states
the mathematics only.

---

## 1. Why this programme exists

The corpus owns an RH-equivalent inequality of Hardy type
(`RHTower.riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`,
`TransHorizonIncidenceMechanics.riemannHypothesis_iff_odd_primeChain_poincare`):

    RH  ⟺  for every odd v ∈ C²_c(ℝ):   ∫ Θ(x) cosh(x/2) v(x)² dx  ≤  E_arch(v) + E_prime(v),

where `Θ` is Riemann's kernel (`riemannKernelReal`, even, positive, super-exponentially decaying),

    E_arch(v)  = ∫_{t>0} ω(t) ∫_ℝ Θ(x)Θ(x+t) (v(x) − v(x+t))² dx dt,     ω(t) = e^{−t/2}/(1 − e^{−2t}),
    E_prime(v) = Σ_{n≥2} Λ(n) n^{−1/2} ∫_ℝ Θ(x)Θ(x+log n) (v(x) − v(x+log n))² dx.

Equivalently, with `markovEnergy (Θ v) = E_arch(v) + E_prime(v) − ∫ Θ cosh(x/2) v²`
(`phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass`), RH is the statement that the
Schrödinger-type form "jump energy minus potential" is nonnegative on odd tests.

Bounding the two sides separately produces identities, finite classifications and nonselective
positivity on restricted families, never a sign. In the theory of Dirichlet forms the sign question has
a different shape: a form `E − ρ` is nonnegative if and only if a **positive supersolution** `ω` of
`Lω ≥ ρ ω` exists (Allegretto–Piepenbrink), and the proof is an exact identity, the **ground-state
representation**. Arithmetic Criticality Theory develops this mechanism for the arithmetic jump
operator: a bounding problem becomes an existence problem for one positive function, and the exact
identity shows where positivity must come from when no such function exists.

**What is new.** Criticality theory exists for local Schrödinger operators and for jump processes
with translation-invariant kernels. It does not exist for a kernel whose jump lengths are the
logarithms of prime powers, whose rates are `Λ(n) n^{−1/2}`, and whose potential is the pole of the
zeta function.

---

## 2. Objects and language

All functions below are in **Doob coordinates**: a test is `f = Θ · v`, and `v` is the object. The
corpus's "secondary odd profile" `m_a = Θ(·−a) − Θ(·+a)` is a test; its Doob coordinate is
`ω_a = m_a / Θ`. Never mix the two coordinates.

| Object | Definition | Lean |
|---|---|---|
| Riemann kernel | `Θ(u) = Σ_{n≥1} e^{u/2}(4π²n⁴e^{4u} − 6πn²e^{2u}) e^{−πn²e^{2u}}`, even, `Θ > 0`, strictly decreasing on `[0,∞)` | `riemannKernelReal` |
| Jump measure | `dm(t) = ω(t) dt + Σ_n Λ(n) n^{−1/2} δ_{log n}` on `t > 0` | `archLevyDensity`, `vonMangoldtAtom` |
| Single-shift jump | `J_v(t) = ∫_ℝ Θ(x)Θ(x+t)(v(x) − v(x+t))² dx` | `phiDoobArchShiftJump` (integrated) |
| Potential | `ρ(x) = Θ(x) cosh(x/2)` | `phiDoobCoshMass (v²)` is `∫ ρ v²` |
| Same-side ground jump | `Θ(x)Θ(x+t) ω(x)ω(x+t) (u(x) − u(x+t))²` on `x > 0` | `sameSideGroundJump` |
| Reflected ground jump | `Θ(x)Θ(t−x) ω(x)ω(t−x) (u(x) + u(t−x))²` on `0 < x < t` | `reflectedGroundJump` |
| Reflected difference jump | `Θ(x)Θ(t−x) ω(x)ω(t−x) (u(x) − u(t−x))²` on `0 < x < t` | `reflectedDifferenceJump` |
| Same-side energy | `S(ω,u) = ∫ dm(t) ∫_{x>0} sameSideGroundJump` | `sameSideEnergy` |
| Reflected sum / difference energies | `P(ω,u) = ∫ dm(t) ∫_0^t reflectedGroundJump`, `D(ω,u) = ∫ dm(t) ∫_0^t reflectedDifferenceJump` | `reflectedSumEnergy`, `reflectedDifferenceEnergy` |
| Fold excess density and weight | `(m_a(t−x) − m_a(x+t))⁺ 1_{2x<t}`; `W_a(x) = ∫ dm(t) (m_a(t−x) − m_a(x+t))⁺ 1_{2x<t}` | `foldExcessDensity`, `foldExcessWeight` |
| Ground remainder of one shift | `rem(t) = 2∫_{x>0} sameSide + ∫_{0<x<t} reflected` | `groundRemainderShift` |
| Ground remainder | `R_N(ω,u) = ∫ dm(t) rem(t)` | `groundRemainder` |
| Folded (Neumann) shift generator | `Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(|x−t|))]` | `foldedShiftGenerator` |
| Two-sided (Dirichlet) shift generator | `Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(x−t))]` | `twoSidedShiftGenerator` |
| Folded generator | `(𝓛_N ω)(x) = ∫ dm(t) foldedShiftGenerator ω t x` | `foldedGenerator` |
| Two-sided generator | `(𝓛_D ω)(x) = ∫ dm(t) twoSidedShiftGenerator ω t x` | `twoSidedGenerator` |
| Potential density | `u(x)² ω(x) foldedShiftGenerator ω t x` | `groundPotentialDensity` |
| Admissibility | integrability and summability of remainder and potential in `t` and `x` | `FoldedAdmissible` |
| Shift difference (test coordinate) | `m_a(y) = Θ(y−a) − Θ(y+a)`, odd, `> 0` on `(0,∞)` for `a > 0` | `shiftDifference` |
| Shifted ground state | `ω_a(x) = m_a(x) / Θ(x)`, odd, `> 0` on `(0,∞)` for `a > 0` | `shiftedGroundState` |
| Potential kernel of `ω_a` | `K_a(t,x)` with `groundPotentialDensity ω_a u t x = u(x)² K_a(t,x)` | `shiftedPotentialKernel` |
| Reflected collar mass | `C_a(x) = ∫_{t>0} ω(t) m_a(t−x)⁺ dt + Σ_n Λ(n)n^{−1/2} m_a(log n − x)⁺` | `shiftedCollarMass` |
| Signed prime shift sum | `Σ_n Λ(n)n^{−1/2} m_a(log n − x)` | `signedPrimeShift` |
| Collar excess constant | `K = 2|c|Θ(0) + 4∫_0^∞ gammaSourceBound + Σ_n Λ(n)n^{−1/2}Θ(log n)`, `c = (γ + log π)/2` | `collarExcessConstant` |
| Finite jump energy | `E_K(v) = ½ Σ_{i,j} K_{ij} (v_i − v_j)²` | `jumpEnergy` |
| Finite generator | `(L_K ω)_i = Σ_j K_{ij}(ω_i − ω_j)` | `generator` |
| Schrödinger matrix | `A = diag(Σ_k K_{ik} − ρ_i) − K`, so `vᵀAv = E_K(v) − Σ ρ_i v_i²` | `schroedingerMatrix` |

Terminology (Pinchover). A form `Q = E − ρ` is **supercritical** if it takes a negative value,
**critical** if it is nonnegative but admits no nonzero Hardy weight `W ≥ 0` with `Q ≥ ∫ W v²`, and
**subcritical** if such a weight exists. RH says the odd-sector arithmetic form is not supercritical.

---

## 3. Mechanisms

### 3.1 The pointwise ground-state identities (pure algebra)

For reals `ω_x, ω_y, u_x, u_y`:

    (ω_x u_x − ω_y u_y)² = ω_x ω_y (u_x − u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)        (difference)
    (ω_x u_x + ω_y u_y)² = ω_x ω_y (u_x + u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)        (sum, Neumann form)
    (ω_x u_x + ω_y u_y)² = −ω_x ω_y (u_x − u_y)² + (ω_x + ω_y)(ω_x u_x² + ω_y u_y²)      (sum, Dirichlet form)

The second factor of the last term is antisymmetric under `x ↔ y`, so after summation against a
symmetric kernel it becomes `2 Σ u² ω (Lω)`: the potential produced by the generator applied to `ω`.

### 3.2 The folded ground-state representation (GSR-N) for the odd sector

Let `v` be odd, continuous, compactly supported, and write `v = ω u` on `(0,∞)` with `ω` odd and `u`
even. Fold each shift integral onto the half line
(`integral_phiDoobArchShiftJump_eq_halfLine_of_odd`): the full-line jump at shift `t` equals twice the
same-side half-line jump plus the origin-crossing collar `∫_{0<x<t} Θ(x)Θ(t−x)(v(x) + v(t−x))²`.
Applying the difference identity to the same-side part and the Neumann sum identity to the collar gives,
exactly,

    J_v(t) = 2∫_{x>0} sameSideGroundJump + ∫_{0<x<t} reflectedGroundJump + 2∫_{x>0} u(x)² ω(x) foldedShiftGenerator ω t x dx.

Integrating against `dm(t)` and subtracting the potential
(`markovEnergy_phiDoob_eq_groundRemainder_add_potential`, under `FoldedAdmissible ω u`):

    markovEnergy(Θ v) = R_N(ω, u) + 2 ∫_{x>0} u(x)² ω(x) [ (𝓛_N ω)(x) − Θ(x) cosh(x/2) ω(x) ] dx,     R_N ≥ 0.

**Sufficiency** (`riemannHypothesis_of_foldedSupersolution`). If `ω` is odd, positive on `(0,∞)`, and
`𝓛_N ω ≥ Θ cosh(x/2) ω` on `(0,∞)`, then `markovEnergy(Θ v) ≥ 0` for every odd test factoring through
`ω`, hence RH. Section 3.5 shows the hypothesis is never satisfied; the identity itself survives.

**Reading of `𝓛_N`.** On `(0,∞)`, `foldedShiftGenerator ω t x` is the two-sided generator applied to the
**even reflection** `|ω|`. So the condition is: the even function `|ω|` is a supersolution away from
the origin. At the origin `|ω|` has a kink; that is where the Dirichlet condition `v(0) = 0` of the odd
sector lives.

### 3.3 The two generators and their difference

    (𝓛_D ω)(x) − (𝓛_N ω)(x) = 2 Θ(x) ∫_{t>x} dm(t) Θ(t−x) ω(t−x)      (x > 0, ω odd, ω > 0 on (0,∞)).

The two-sided generator is the larger one, by exactly the mass that returns from the reflected side.
The Dirichlet sum identity gives a second exact representation (GSR-D) with `𝓛_D` in the potential,
but its remainder contains `−Θ(x)Θ(t−x)ω(x)ω(t−x)(u(x) − u(t−x))²` and is indefinite. Only GSR-N has a
nonnegative remainder. A `𝓛_D`-supersolution therefore proves nothing by itself; a `𝓛_N`-supersolution
would prove RH.

### 3.4 The equation of motion and the shifted ground states

The corpus proves the pointwise harmonic identity of `Θ` (`theta_harmonic_identity`):

    Σ_n Λ(n)n^{−1/2} (Θ(y + log n) + Θ(y − log n)) = cosh(y/2) − 2c Θ(y) + ∫_0^∞ symArchTerm(y,u) du,

`c = (γ + log π)/2`, with `|∫_0^∞ symArchTerm(y,u) du| ≤ 2∫_0^∞ gammaSourceBound` uniformly in `y`
(`abs_integral_symArchTerm_le`). In Doob coordinates this says `𝓛_D 1 = 0` with the constant `1` a
**subsolution** (`0 < ρ`): the even sector is supercritical, and its negative direction is the pole
(`markovEnergy(Θ) = −1/2`, from `∫ Θ cosh(x/2) = 1/2`; `EvenSectorPoleCalibration`).

Subtracting the identity at `x − a` and `x + a` gives the exact source equation of the shifted ground
state (`twoSidedGenerator_shiftedGroundState_sub_potential`):

    (𝓛_D ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 sinh(a/2) sinh(x/2) Θ(x)      for all x,

positive on `(0,∞)`: every `ω_a` (`a > 0`) is a strict `𝓛_D`-supersolution on the half line. By 3.3
(`foldedGenerator_shiftedGroundState_sub_potential`),

    (𝓛_N ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 Θ(x) [ sinh(a/2) sinh(x/2) − C_a(x) ],

so `ω_a` is a `𝓛_N`-supersolution at `x` exactly when `C_a(x) ≤ sinh(a/2) sinh(x/2)`
(`foldedSupersolution_shiftedGroundState_iff`). The folded defect is linear on the span of the shifted
ground states, and a nonnegative nonzero combination is a folded supersolution at `x` only if one
constituent is (`ShiftedGroundStateSuperposition`).

**Collar lower bound.** Since `m_a(log n − x) = Θ(x+a−log n) − Θ(x−a−log n)`, the signed prime shift
sum equals `P(x+a) − P(x−a)` with `P(y) = Σ Λ(n)n^{−1/2}Θ(y − log n)`, and the harmonic identity gives
`P(y) = cosh(y/2) − 2cΘ(y) + ∫_0^∞ symArchTerm(y,·) − Q(y)` with `Q(y) = Σ Λ(n)n^{−1/2}Θ(y + log n)`,
`0 ≤ Q(y) ≤ Q(0)` for `y ≥ 0`. The cosh difference is exactly `2 sinh(a/2) sinh(x/2)`, and the collar
mass keeps only the positive parts of the same terms, so (`two_mul_source_sub_le_shiftedCollarMass`)

    C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K      for all x ≥ a ≥ 0,

with `K = collarExcessConstant`. No prime number theorem enters. Consequently the folded defect of `ω_a`
is at most `−2Θ(x)(sinh(a/2) sinh(x/2) − K)` for `x ≥ a` (`foldedDefect_shiftedGroundState_le`), and
`ω_a` is a strict folded subsolution on a half line `[X, ∞)`
(`exists_infinity_window_foldedGenerator_lt_potential`). The collar returns at least **twice** the
source: the prime mass below `e^x` that the folding discards is exactly the mass the two-sided source
equation accounts for.

**Sharp asymptotics (analysis, not formalised).** The prime part of `C_a(x)` is a smoothed count of
prime powers in a window of bounded logarithmic width above `e^x`; by the prime number theorem it is
asymptotic to `e^{x/2} κ(a)`, `κ(a) = ∫_0^∞ e^{s/2} m_a(s) ds`, while the source is asymptotic to
`sinh(a/2) e^{x/2}/2`. With `I(a) = ∫_a^∞ e^{u/2}Θ`, `J(a) = ∫_a^∞ e^{−u/2}Θ` and `∫_ℝ e^{u/2}Θ = 1/2`,
`κ(a) = e^{a/2}(1/2 − J(a)) − e^{−a/2} I(a)`, and the collar-to-source ratio `R(a) = 2κ(a)/sinh(a/2)`
satisfies `R(a) > 2` for every `a > 0` (`e^a J(a) + I(a) < 1/2`, strictly decreasing from the value
`1/2` at `a = 0` because `Θ` is strictly decreasing), `R(a) → 1 + 8Θ(0) + 4σ` as `a → 0` with
`σ = ∫_0^∞ Θ(u) sinh(u/2) du`, and `R(a) → 2` as `a → ∞`. This is the exact content of the corpus's
"factor two between `μ = 1/2` and `μ = 1`" and of THIM's residual `θ · sourcePair`.

### 3.5 No folded supersolution exists; the remainder-dominates-defect identity

In test coordinates `g = Θω` (odd, `g ≥ 0` on `(0,∞)`) the folded defect at `x > 0` is

    Θ(x) · [ 𝒜g(x) − 2c g(x) − Σ_n Λ(n) n^{−1/2} ( g(x + log n) + g(|x − log n|) ) ],

`𝒜g(x) = ∫_0^∞ [2ν(u) g(x) − ω(u)(g(x+u) + g(|x−u|))] du`, `ν(u) = e^{−2u}/(1 − e^{−2u})`.

- **Origin** (`exists_origin_window_foldedGenerator_lt_potential_of_profile`). For every `ω`
  odd, continuous, nonnegative on `[0,∞)` with `ω(log 2) > 0`, Lipschitz on `[−1, 1]`, and with
  `Φ ω ≤ C Φ(· − b)` on the half line, the folded defect is strictly negative on a right
  neighbourhood of `0`. The prime `2` term tends to `−2Λ(2)2^{−1/2}Φ(0)Φ(log 2)ω(log 2) < 0`; the
  archimedean integral is at most `K√x` (Lipschitz bound for shifts `t ≤ x`, the nonpositive terms
  `−Φ(x±t)ω(·)` dropped for `t > x`, Lévy density `≤ 3/(2t)` and `≤ (3/2)e^{−t/2}`); the remaining
  prime terms are at most `Φ(x)ω(x) · primeKernelSum x`, bounded by the harmonic identity; the
  potential is nonnegative. Every signed combination `c₁ω_a + c₂ω_b` that is nonnegative on the
  half line and positive at `log 2` satisfies the hypotheses
  (`exists_origin_window_signedCombination_foldedGenerator_lt_potential`), as does `ω_a` itself
  (`shiftedGroundState_origin_failure_of_profile`, recovering the prime-`2` proof).
- **Infinity.** For `ω_a`, the collar lower bound of 3.4. For a general admissible profile (bounded,
  bounded second derivative, `∫_0^∞ e^{r/2} g < ∞`) the reflected prime mass is asymptotic to
  `e^{x/2}∫_0^∞ e^{r/2} g` and the folded defect to `−e^{x/2} Θ(x) · 2∫_0^∞ cosh(r/2) g(r) dr`
  (analysis, not formalised).

So the hypothesis of `riemannHypothesis_of_foldedSupersolution` is never met: the hard direction of
Allegretto–Piepenbrink fails for the odd arithmetic form, and the reason is concrete. The reflected
prime mass returns with weight `e^{x/2} e^{±r/2}` while the potential sees `g` only at `x`. This is
the exact meaning of "the odd form is not of Z-type".

**What survives.** For `ω = ω_a` the folded ground-state representation is an exact identity with no
side hypothesis: `(ω_a, u)` is folded-admissible for every `a > 0` and every `u ∈ C¹_c`
(`foldedAdmissible_shiftedGroundState`), and for every even `u ∈ C²_c`
(`markovEnergy_phiDoob_shiftedGroundState_eq_of_contDiff`)

    markovEnergy(Θ(ω_a u)) = R_N(ω_a, u) − 4 ∫_{x>0} u(x)² ω_a(x) Θ(x) ( C_a(x) − sinh(a/2) sinh(x/2) ) dx.

Hence (`markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_of_contDiff`) Markov positivity on
`Θ(ω_a u)` is the **remainder-dominates-defect inequality**

    4 ∫_{x>0} u² ω_a Θ ( C_a − sinh(a/2) sinh(x/2) ) ≤ R_N(ω_a, u),

both sides explicit: the left side is the weighted collar excess (eventually at least
`sinh(a/2) sinh(x/2) − K` by 3.4), the right side the sum of the same-side squares `(u(x) − u(x+t))²`
and the reflected squares `(u(x) + u(t−x))²`. Positivity, if RH holds, is carried by the remainder,
never by the generator; a supersolution-based proof must be a subsolution-plus-remainder proof.

**The two-sided representation and the variation inequality.** Since
`reflectedGroundJump + reflectedDifferenceJump = 2Θ(x)Θ(t−x)ω(x)ω(t−x)(u(x)² + u(t−x)²)` and the collar
is symmetric under `x ↦ t − x`, in test coordinates
`∫_0^t reflected sum + ∫_0^t reflected difference = 4∫_0^t m_a(x) m_a(t−x) u(x)² dx`, and integrating
against `dm` (collar Fubini, `integral_dm_collar_eq_integral_sq_mul_collarMass`)

    P(ω_a,u) + D(ω_a,u) = 4 ∫_{x>0} u² m_a C_a.

The folded representation `R_N = 2S + P` therefore becomes the two-sided one
(`markovEnergy_phiDoob_shiftedGroundState_eq_twoSided`): for every `a > 0` and even `u ∈ C²_c`,

    markovEnergy(Θ(ω_a u)) = 2 S(ω_a,u) − D(ω_a,u) + 4 sinh(a/2) ∫_{x>0} u(x)² m_a(x) sinh(x/2) dx,

whose source term is the two-sided source `2 sinh(a/2) sinh(x/2) Θ` of `ω_a` and whose only indefinite
term is `−D`. Markov positivity on `Θ(ω_a u)` is the **variation inequality**
(`markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation`)

    D(ω_a,u) ≤ 2 S(ω_a,u) + 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2),

and RH implies it for every `a > 0` and even `u ∈ C²_c` (`reflectedDifferenceEnergy_le_of_riemannHypothesis`).
In the corpus's `oddProfile` coordinates (`m_a = 2 sinh(a/2) · oddProfile a`,
`oddProfileTest a w = Φ(ω_a w)/(2 sinh(a/2))`), since the Markov energy is quadratic
(`markovEnergy_real_smul`), the same identity reads (`markovEnergy_oddProfileTest_eq_twoSided`)

    markovEnergy(oddProfileTest a w) = (2S − D)/(4 sinh(a/2)²) + 2 ∫_{x>0} oddProfile a · sinh(x/2) · w²,

the last term being the half-line form of THIM's `oddSinhPotential a w`; `S/(4 sinh²)` and
`D/(4 sinh²)` are the `dm`-integrals of `oddProfileShiftJump` on the half line and of
`oddProfileCollarDiffSq` on `(0,t)`. The entire budget by which the collar may exceed twice the
direct energy is the sinh potential, with coefficient exactly `1`
(`markovEnergy_oddProfileTest_nonneg_iff_variation`). The reflected variation `(u(x) − u(t−x))²` is a variation
across the fold point `t/2`; the same-side variation `(u(x) − u(x+t))²` is a variation at distance
`t`.

**Cross-term form and far-apart bumps.** Expanding the reflected difference square and using the
collar Fubini identity, `D = 2∫u² m_a C_a − 2X` with the cross term
`X(ω_a,u) = ∫ dm(t) ∫_0^t m_a(x) m_a(t−x) u(x) u(t−x) dx`, so
(`markovEnergy_phiDoob_shiftedGroundState_eq_cross`)

    markovEnergy(Θ(ω_a u)) = 2S + 2X − 2∫_{x>0} u² m_a (C_a − 2 sinh(a/2) sinh(x/2)).

For an even `g ∈ C²_c` supported in `[−1/4, 1/4]` the two-bump profile
`u = g(·−a)/m_a + g(−·−a)/m_a(−·)` (`twoBumpProfile`) has `m_a u = g(·−a)` on the half line, so
`Θ(ω_a u) = g(x−a) − g(−x−a)` is the odd test made of two opposite copies of `g` at `±a`; its cross
term is the autocorrelation `ρ_g(t − 2a)`, and the prime part of `X` is the corpus's smoothed
log-window sum `Σ Λ(n) n^{−1/2} ρ_g(log n − 2a)`. On the window `|x−a| ≤ 1/4` the collar excess is
bounded by a universal constant (`shiftedCollarMass_sub_le_windowCollarConstant`: archimedean
collar `≤ 1`, signed prime sum by the harmonic identity, discarded negative parts
`≤ primeKernelSum(x−a)`) and `u² m_a = g²/m_a ≤ sup g²/(Φ(1/4) − Φ(7/4))`. The prime number theorem
in log windows (`exists_abs_windowSum_vonMangoldt_sub_le`) evaluates the cross term as
`2μ² cosh a + O(1 + e^{a} e^{−√(2a)/1920000})` with `μ = ∫ g(u) e^{u/2} du`. Hence
(`exists_shift_markovEnergy_twoBumpProfile_pos`): **if `μ ≠ 0`, the Markov energy of
`g(x−a) − g(−x−a)` is positive for all large `a`**, being at least `μ² e^{a} − K`. The pole of `ζ`
carries the positivity through the exponential moment `μ`; the profiles with `μ = 0` are exactly
those for which the leading order vanishes and the sign is decided by the zero sum.

**Fold domination for monotone profiles.** If `u` is even, nonnegative and nonincreasing on
`[0, ∞)`, then on `0 < x < t/2` the three points satisfy `x ≤ t − x ≤ x + t`, so
`0 ≤ u(x) − u(t−x) ≤ u(x) − u(x+t) ≤ u(x)`, and by the symmetry of the collar

    D(t) = 2∫_0^{t/2} m_a(x) m_a(t−x) (u(x) − u(t−x))² ≤ 2 S(t) + 2 E_a(t),
    E_a(t) = ∫_0^{t/2} m_a(x) (m_a(t−x) − m_a(x+t))⁺ u(x)² dx

(`integral_reflectedDifference_le_two_sameSide_add_two_foldExcess`). Integrating against `dm` and
exchanging the integrations (`integral_dm_foldExcessShift_eq_integral_sq_mul_foldExcessWeight`),

    markovEnergy(Θ(ω_a u)) ≥ 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) − 2 ∫_{x>0} u(x)² m_a(x) W_a(x) dx

(`markovEnergy_phiDoob_shiftedGroundState_ge_of_antitone`). Hence the **weight criterion**: if
`W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` for all `x > 0`, the Markov energy is nonnegative on `Θ(ω_a u)` for
every even `u ∈ C²_c` nonnegative and nonincreasing on the half line
(`markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_weight_le`). The weight is a function
of Riemann's kernel alone; it vanishes on the window `x + t ≤ a` because `m_a` is increasing on
`[0, a]` (`foldExcessDensity_eq_zero_of_add_le`), so only shifts beyond the peak of `m_a` contribute.
Both sides of the criterion vanish at `x = 0`; the comparison of slopes there is
`∫_{t > t_a} dm(t) |m_a'(t)| ≤ sinh(a/2)/2` with `t_a` the peak of `m_a`, since
`(m_a(t−x) − m_a(x+t))⁺ ≈ 2x (−m_a'(t))⁺`.

**The shift-averaged variation inequality.** The variation inequality holds for every `a > 0`
under RH and is quadratic in `m_a`, so it can be integrated over the shift. With the autocorrelation
`G = Φ ∗ Φ` of Riemann's kernel (`riemannAutocorr`), even, `0 ≤ G(z) ≤ Φ(|z|/2)`,

    ∫_0^∞ m_a(x) m_a(y) da = G(x − y) − G(x + y) =: K(x, y)            (`averagedKernel`),
    ∫_0^∞ 4 sinh(a/2) m_a(x) sinh(x/2) da = 2 sinh²(x/2),

the first because each of the four products `Φ(x ∓ a)Φ(y ∓ a)` integrates over `a ∈ ℝ` to
`G(x − y)` or `G(x + y)` and the integrand is even in `a`; the second because
`∫ Φ(s) cosh(s/2) ds = 1/2` and `∫ Φ(s) sinh(s/2) ds = 0` give `∫ sinh(a/2) Φ(x − a) da = sinh(x/2)/2`
(`integral_Ioi_shiftDifference_mul_shiftDifference`, `integral_Ioi_sinh_mul_shiftDifference`).
`K(x,y) ≥ 0` for `x, y ≥ 0` and `K ≤ Φ(0)`. For each shift `t` the averaged variations are

    D̄(t) = ∫_0^t K(x, t−x) (u(x) − u(t−x))² dx,      S̄(t) = ∫_{x>0} K(x, x+t) (u(x) − u(x+t))² dx

(`averagedReflectedShift`, `averagedSameSideShift`); all integrands are nonnegative, so the exchange
of `∫ da` with `∫ dx` needs no majorant beyond the exact `a`-integrals. For `u` bounded by `M`,
supported in `[−R, R]`, Lipschitz with constant `L` on `[−R−1, R+1]`:

    0 ≤ D̄(t) ≤ 4M²Φ(0) t,     D̄(t) ≤ 4M² t Φ((t − 2R)/2)   (t ≥ 2R),
    0 ≤ S̄(t) ≤ Φ(0)(L² + 4M²) R t,     S̄(t) ≤ 4M² R Φ(t/2),

because on the support of `(u(x) − u(t−x))²` one has `x ≤ R` or `t − x ≤ R`, hence
`|t − 2x| ≥ t − 2R` and `K(x,t−x) ≤ G(2x − t) ≤ Φ(|2x−t|/2)`. The linear bounds make the archimedean
parts integrable against `archLevyDensity(t) dt` (the density is `O(1/t)` at `0`), and the decay
bounds make the prime parts summable, since `Φ(s) ≤ C e^{−8|s|}` gives
`Σ Λ(n) n^{−1/2} (1 + log n) Φ((log n − c)/2) < ∞` (`summable_atom_mul_one_add_log_mul_kernel_half`).
A nonnegative series of integrable functions with summable integrals is integrable
(`integrable_tsum_of_nonneg`), so `a ↦ D_a(u)`, `a ↦ S_a(u)` and the source are integrable on
`(0, ∞)` and

    ∫_0^∞ D_a(u) da = D̄(u) := ∫ dm(t) D̄(t),     ∫_0^∞ S_a(u) da = S̄(u) := ∫ dm(t) S̄(t),
    ∫_0^∞ 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) da = 2 ∫_{x>0} u(x)² sinh²(x/2) dx

(`integral_Ioi_reflectedDifferenceEnergy_shiftedGroundState`,
`integral_Ioi_sameSideEnergy_shiftedGroundState`, `integral_Ioi_source_shiftedGroundState`).
Integrating the two-sided representation (`integral_Ioi_markovEnergy_phiDoob_shiftedGroundState`),

    ∫_0^∞ markovEnergy(Θ(ω_a u)) da = 2 S̄(u) − D̄(u) + 2 ∫_{x>0} u(x)² sinh²(x/2) dx,

and under RH the left side is nonnegative, which is the **shift-averaged variation inequality**
(`averagedReflectedEnergy_le_of_riemannHypothesis`,
`averaged_variation_inequality_autocorr_of_riemannHypothesis`):

    ∫ dm(t) ∫_0^t [G(2x−t) − G(t)] (u(x) − u(t−x))² dx
      ≤ 2 ∫ dm(t) ∫_{x>0} [G(t) − G(2x+t)] (u(x) − u(x+t))² dx + 2 ∫_{x>0} u(x)² sinh²(x/2) dx.

The inequality is shift-free and has explicit kernels; it is weaker than RH (an average of the
pointwise family), and it is the natural first target for an unconditional proof: on the far
diagonal `x ≈ t/2` the kernel `G(2x − t) − G(t) ≈ G(0)` is large but `(u(x) − u(t−x))²` vanishes
once `t > 2R`, so the prime sum is cut off at `log n ≤ 2R` up to the superexponential tail.

**Plateau positivity: the shifted ground state is the zero-free direction.** The half-line sinh
moment of the shift difference is exact,

    ∫_{x>0} m_a(x) sinh(x/2) dx = sinh(a/2)/2        (`integral_Ioi_shiftDifference_mul_sinh_half`),

because `∫ Φ(x − a) sinh(x/2) dx = sinh(a/2)/2`, `∫ Φ(x + a) sinh(x/2) dx = −sinh(a/2)/2` and the
integrand is even. So the source of `ω_a` against the constant profile is `2 sinh²(a/2)`; this is
the pole term of the explicit formula for the odd test `m_a`, whose Mellin transform
`∫ m_a(x) e^{(s−1/2)x} dx = −2 sinh(a(s − 1/2)) ξ(s)` vanishes at every zero of `ξ`, on or off the
line. For a profile `u` with `0 ≤ u ≤ 1` and `u = 1` on `[−L, L]` the reflected difference jump
vanishes unless one of `x, t − x` exceeds `L`, and then the far factor obeys
`m_a(M) ≤ C e^{16a} e^{−16M}` with `16M ≥ 4t + 8L`, so

    D(ω_a, u) ≤ Φ(0) C e^{16a} (∫ archLevyDensity(t) t dt + Σ n^{−2}) e^{−8L},
    ∫_{x>0} u² m_a sinh(x/2) ≥ sinh(a/2)/2 − C e^{16a} e^{−8L}

(`reflectedDifferenceEnergy_plateau_le`, `integral_sq_mul_shiftDifference_mul_sinh_ge`, with
`Φ(x) ≤ C e^{−16|x|}`). Since `S ≥ 0`, for every `a > 0` there is `L₀(a)` such that every even
`u ∈ C²_c` with `0 ≤ u ≤ 1` and `u = 1` on `[−L, L]`, `L ≥ L₀`, satisfies

    markovEnergy(Θ(ω_a u)) ≥ sinh²(a/2) > 0      (`exists_plateau_markovEnergy_phiDoob_shiftedGroundState_ge`),

unconditionally and for every shift. Together with the far-apart two-bump theorem this locates the
positivity of the ground-state family: wide plateaus (every `a`) and far narrow bumps with
`∫ Θ e^{s/2} g ≠ 0` are positive directions; the Markov form sees the zeros only through profiles
that cancel the pole term, that is through `u` with vanishing `e^{±x/2}`-moments against `m_a`.

### 3.6 The finite model (Perron–Frobenius)

For a finite symmetric nonnegative kernel `K` and any potential `ρ`, the form `E_K − Σ ρ v²` is
nonnegative if and only if a nonnegative nonzero `ω` with `L_K ω ≥ ρ ω` exists; under connectivity,
`ω > 0` (`FiniteJumpFormAllegrettoPiepenbrink`, both directions). The hard direction uses the minimiser
of the Rayleigh quotient on the unit sphere and the fact that replacing a vector by its absolute value
does not increase the form. This is the template the arithmetic problem is measured against: the
arithmetic form on the odd sector is **not** of Z-type (the reflected collar enters the operator with a
plus sign), which is exactly why the hard direction fails there (3.5).

### 3.7 Admissibility of the shifted ground states (how the integrability is discharged)

In test coordinates the potential density of `ω_a` is `u(x)² K_a(t,x)` with
`K_a(t,x) = m_a(x)[ω_a(x)(Θ(x+t) + Θ(|x−t|)) − m_a(x+t) − m_a(|x−t|)]`. For `u` supported in `[−R, R]`,
`R ≥ 1`, and `0 < x ≤ R`:

    |K_a(t,x)| ≤ K₁ t   (Lipschitz constants of Θ and m_a on [−R−1, R+1]),      |K_a(t,x)| ≤ K₂ Θ(t − R − a),

and the one-shift remainder satisfies `|rem_a(t)| ≤ C t` and `|rem_a(t)| ≤ 16 Θ(0) M_u² R Θ(t − R − a)`,
because the reflected jump on the collar `0 < x < t` lives on `x ≤ R` or `x ≥ t − R`, two intervals of
length at most `R`. Integration against the Lévy density uses `∫_0^∞ ω(t) t dt < ∞`
(`ω(t) t ≤ 6 e^{(1−t)/4}`); summation against the atoms uses `Σ Λ(n) n^{−1/2} Θ(log n − c) < ∞`
(`summable_primeShift_left`). Measurability of `t ↦ rem_a(t)` is strong measurability of a parametric
integral; measurability of the prime generator is an almost-everywhere limit of partial sums.

---

## 4. Traps and sharp boundaries

- **Averaging over all shifts loses the zeros (analysis, not formalised).** By Plancherel in `a`,
  `∫_0^∞ markovEnergy(Θ(ω_a u)) da = (1/4π) ∫ Ξ(ξ)² markovEnergy(sin(ξ·) u) dξ`, since the Fourier
  transform of `Φ` is Riemann's `Ξ`. The weight `Ξ(ξ)²` vanishes exactly at the ordinates of the
  zeros on the line, and for a zero `ρ = 1/2 + δ + iγ` the `Ξ²`-weighted contribution of the pair
  `ρ, 1 − ρ̄` to the modulated tests `sin(ξx) u(x)` is, to leading order in the width of `û`,
  `(π/2) Ξ(γ)² ∫ u²` for every `δ`, hence nonnegative. The shift-averaged variation inequality is
  therefore expected to hold unconditionally and carries no information about off-line zeros; the
  zeros are visible only in finite-window averages over `a` of width below the zero gap, or in the
  single-shift inequality itself. Test profiles `u = cos(γx) χ(x − X)` with `χ` wide and `X` large
  make the leading terms of `D̄` and of the source cancel to order `e^{X}` exactly when `Ξ(γ) = 0`,
  leaving `2 ∫ dm(t) G(t)(1 − cos γt) ≳ (G(0)/2) log γ` against `1/8`: the averaged inequality
  holds there with room, for the same reason.

| Trap | Why it fails, and the correct statement |
|---|---|
| Looking for an even positive supersolution on all of `ℝ` | It cannot exist: it would give `markovEnergy(Θ v) ≥ 0` for even `v`, but `markovEnergy(Θ) = −1/2`. The supersolution must vanish at `0` (odd, or even with a kink), and the identity must be applied only to odd tests. |
| Using `𝓛_D` (two-sided generator) as the supersolution operator | The GSR with `𝓛_D` has an indefinite remainder. Only `𝓛_N` (folded, Neumann) gives a nonnegative remainder. |
| Reading `ω_a > 0` with positive `𝓛_D`-source as a proof of RH | It is a `𝓛_D`-supersolution, not a `𝓛_N`-supersolution; the reflected collar `C_a(x)` exceeds the source for all large `x` and near `0`. |
| Looking for any folded supersolution | None exists (3.5). The live object is the remainder-dominates-defect inequality, not a sign of a generator defect. |
| Estimating a one-sided prime sum through a window prime number theorem | First evaluate the signed sum through `theta_harmonic_identity` and use positivity of the discarded part; the exact identity gives a uniform lower bound with constant `2` where the asymptotic analysis gives `R(a)`. |
| Defining the generator through a "total jump rate" | `∫ dm(t)(Θ(x+t) + Θ(x−t))` diverges (the archimedean density has a `1/t` singularity, the prime sum has `Σ Λ(n)n^{−1/2} = ∞`). Only differences `ω(x) − ω(x+t)` converge. Never split a generator into rate minus average. |
| Confusing test and Doob coordinates | `m_a` is a test; `ω_a = m_a/Θ` is the Doob coordinate. Potentials, generators and supersolutions live in Doob coordinates; bounds are easiest in test coordinates (`shiftedPotentialKernel`). |
| Requiring `v/ω` to be `C²` | The ground-state identities need no derivatives. The RH criterion needs `v ∈ C²_c`; the quotient `u = v/ω` only needs to be continuous and bounded on `(0, R]`, which holds when `ω` vanishes at most linearly at `0`. |
| Applying Perron–Frobenius to the odd sector directly | The odd-sector operator has positive off-diagonal entries from reflected jumps. Z-type arguments apply to the even sector (supercritical, pole) and to the folded operator `𝓛_N` acting on `|ω|`, not to the odd form as a whole. |
| `1 < 2 exp(−2|a|)` in THIM's gauge | The corpus's odd polar vectors require `a < (log 2)/2`, and the absorption ratio `2M cosh(R/2)/(Θ(R) sinh(a/2))` grows like `exp(πe^{2R})`. Supersolution statements here are stated pointwise in `x` and carry no aperture window. |
| `rw [mem_Iic]`, `rw [mem_Ioo]` inside an `if` | The motive is not type correct (decidability instance); use `simp only [Set.indicator_apply, mem_Iic]`. `integral_add`/`integral_sub` rewrites need lambda-typed integrability facts, not `Pi.add` forms. |

---

## 5. Open problems

1. **The remainder-dominates-defect inequality** for `ω_a` (3.5): for which even `u ∈ C²_c` does
   `4∫ u² ω_a Θ (C_a − sinh(a/2) sinh(x/2)) ≤ R_N(ω_a, u)` hold unconditionally, and what is the exact
   obstruction otherwise? Both sides are explicit; the left side grows like `e^{x/2}` on the support of
   `u`, the right side is a quadratic form in `u` with kernel `Θ(x)Θ(x±t) m_a(x) m_a(x±t)`. This is
   THIM's absorption problem in closed form.
2. **The variation inequality** `D(ω_a,u) ≤ 2 S(ω_a,u) + 4 sinh(a/2) ∫ u² m_a sinh(x/2)` (3.5): for
   which classes of even `u` is it provable? For `u` with `u(t − x) = u(x)` on `(0,t)` the collar term
   vanishes. For `u` nonnegative and nonincreasing on `[0,∞)` it follows from the weight criterion
   `W_a(x) ≤ 2 sinh(a/2) sinh(x/2)`; whether that criterion holds is a question about Riemann's
   kernel alone. The decisive region is the origin, where both sides vanish to first order and the
   slope condition reads `∫_{t > t_a} dm(t) |m_a'(t)| ≤ sinh(a/2)/2`; for large `a` the left side is
   asymptotically `e^{a/2} ∫_0^∞ e^{s/2} |Θ'(s)| ds = e^{a/2}(Θ(0) + 1/8 + σ/2)` against
   `e^{a/2}/4`, so the pointwise criterion fails for large `a` unless `Θ(0) + σ/2 ≤ 1/8`, and the
   dropped same-side terms away from the origin would have to compensate. THIM's collar-to-direct
   bounds (`oddProfileCollarDiffSq_le_two_direct_add_two_across`,
   `integral_oddProfileCollarDiffSq_le_direct_add_absorbedArchSlice`) are partial results on
   exactly this inequality, on the low-prime window `3t/2 ≤ a`.
   The shift-averaged form (3.5) is the weakest member of the family: it replaces `m_a(x)m_a(y)` by
   `G(x−y) − G(x+y)` and the source by `2 sinh²(x/2) u²`; an unconditional proof of it would be the
   first positivity statement of the programme that is not a consequence of the window structure.
3. **Signed superpositions at infinity.** Finite combinations `Σ c_j ω_{a_j}` with mixed signs that
   stay positive on `(0,∞)` fail at the origin (3.5); at infinity the folded defect is linear, so the
   question is the sign of `Σ c_j (sinh(a_j/2) sinh(x/2) − C_{a_j}(x))` for large `x`, where each
   `C_{a_j}(x) ≥ 2 sinh(a_j/2) sinh(x/2) − K_j` but the signed sum is not controlled by the lower
   bounds alone.
4. **Profiles outside the span.** The forced asymptotics at infinity of any odd profile `g` with
   finite folded generator (analysis in 3.5, not formalised), and the corresponding Lean statement.
5. **Critical Hardy weights.** If the odd form is nonnegative (RH), is it critical or subcritical?
   Candidate weights come from the remainder `R_N` itself.
6. **Selectivity.** For every statement, what it says for `ζ(s−a)ζ(s+a)` (two poles; the potential
   changes) and for a Beurling system. The identities of 3.1–3.3 hold for any even positive kernel;
   the arithmetic enters only through the equation of motion of `Θ` (3.4).

---

## 6. Navigation and discipline

- Search first: `scripts/formal_tools.py research "foldedShiftGenerator"`,
  `research "shiftedGroundState shiftedCollarMass"`, `research "theta_harmonic_identity"`.
- Umbrella: [`GaloisForLFunctions/ArithmeticCriticalityTheory.lean`](../ArithmeticCriticalityTheory.lean).
  Wire new modules by appending an import line.
- Build one module at a time:
  `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/ArithmeticCriticalityTheory/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/ArithmeticCriticalityTheory/<Module>.ilean GaloisForLFunctions/ArithmeticCriticalityTheory/<Module>.lean`.
- No `sorry`, `axiom`, raised heartbeats, or numerical experiments. Integrability hypotheses are stated
  explicitly as structure fields and discharged for concrete `ω`; an RH-strength premise is never a
  hypothesis.
- Namespace: `GaloisForLFunctions.ArithmeticCriticalityTheory`; corpus objects are used through
  `open RHTower`, `RHTower.CHMDPolar` and `RHTower.ThetaSourceWard`.
- Status, logs and dates belong on the pipeline card, not here.

## 7. Module map

| Module | Content |
|---|---|
| `GroundStateRepresentationAlgebra` | pointwise identities; finite jump form, generator, finite ground-state representation; easy Allegretto–Piepenbrink |
| `FiniteJumpFormAllegrettoPiepenbrink` | Schrödinger matrix; Rayleigh form; hard direction via minimiser and absolute value; neighbour-closed zero set; connectivity ⟹ strict positivity; the finite equivalence |
| `DoobJumpFoldedGroundStateRepresentation` | `foldedShiftGenerator`, `twoSidedShiftGenerator`, ground jumps; comparison of the two generators; folded ground-state representation of one Doob shift jump |
| `OddSupersolutionCriterion` | `foldedGenerator`, `groundRemainder`, `FoldedAdmissible`; folded ground-state representation of `markovEnergy (Θ v)`; `riemannHypothesis_of_foldedSupersolution` |
| `ShiftedGroundStateSourceEquation` | `shiftDifference`, `shiftedGroundState`, `twoSidedGenerator`; exact source equation `𝓛_D ω_a − Θ cosh ω_a = 2 sinh(a/2) sinh(x/2) Θ` |
| `ShiftedGroundStateReflectedCollarDefect` | `shiftedCollarMass`; integrability and summability of the collar; `𝓛_N ω_a = 𝓛_D ω_a − 2Θ C_a`; folded defect and the supersolution criterion for `ω_a` |
| `EvenSectorPoleCalibration` | constants are strict subsolutions of both generators; pole mass `1/2`; degenerate shift `a = 0` |
| `ShiftedGroundStateSuperposition` | linearity of the folded generator on the span of shifted ground states; folded defect of a combination; a nonnegative nonzero combination is a folded supersolution at `x` only if a constituent is |
| `ShiftedGroundStateOriginFailure` | prime-`2` lower bound for the collar; `ω_a` is a strict folded subsolution near the origin; remainder-dominates-defect identity and its nonnegativity criterion under `FoldedAdmissible` |
| `ShiftedGroundStateKernelBounds` | test-coordinate forms of the ground jumps and of the potential density of `ω_a` (`shiftedPotentialKernel`); kernel and shift-difference bounds; Lévy density bounds `ω(t) ≤ 3/(2t)`, `ω(t) ≤ (3/2)e^{−t/2}`, `∫_0^∞ ω(t) t dt < ∞`; Lipschitz and support-radius helpers |
| `ShiftedGroundStatePotentialBounds` | `|K_a(t,x)| ≤ K t` and `|K_a(t,x)| ≤ K Θ(t − R − a)` on `0 < x ≤ R`; linear and decay bounds of the same-side and reflected ground jumps |
| `ShiftedGroundStateRemainderBounds` | integrals dominated by indicators of bounded intervals; `|rem_a(t)| ≤ C t` and `|rem_a(t)| ≤ 16Θ(0)M_u²R Θ(t − R − a)`; joint continuity of the jumps and measurability of `t ↦ rem_a(t)` |
| `ShiftedGroundStateAdmissibility` | `foldedAdmissible_shiftedGroundState` for every `a > 0`, `u ∈ C¹_c`; the remainder-dominates-defect identity and its nonnegativity criterion for every even `u ∈ C²_c` (`markovEnergy_phiDoob_shiftedGroundState_eq_of_contDiff`) |
| `ShiftedGroundStateCombinationFailure` | nonnegative nonzero combinations of two shifted ground states are strict folded subsolutions near `0` and on a half line `[X, ∞)` |
| `ShiftedGroundStateCollarFubini` | the collar integral as a half-line integral of the positive part; `m_a(y−x)⁺ ≤ (Φ(0)/Φ(R+a)) Φ(y−R−a)`; product integrability of the archimedean collar; collar Fubini `∫ dm(t) ∫_0^t m_a(x)m_a(t−x)u(x)² = ∫_{x>0} u² m_a C_a`; integrability and summability of the collar marginals |
| `ShiftedGroundStateTwoSidedRepresentation` | `reflectedDifferenceJump`; `sameSideEnergy`, `reflectedSumEnergy`, `reflectedDifferenceEnergy`; `R_N = 2S + P`; `P + D = 4∫u² m_a C_a`; two-sided representation `markovEnergy = 2S − D + 4 sinh(a/2)∫u² m_a sinh(x/2)`; the variation inequality criterion and its proof from RH |
| `ShiftedGroundStateMonotoneFoldDomination` | `foldExcessDensity`, `foldExcessJump`, `foldExcessShift`, `foldExcessWeight`; monotone fold domination of one shift; fold-excess Fubini; `D ≤ 2S + 2∫u² m_a W_a` for nonincreasing nonnegative `u`; the lower bound of the Markov energy and the weight criterion; vanishing of the density on `x + t ≤ a` |
| `ShiftedGroundStateOddProfileCoordinates` | `markovEnergy (c • f) = c² markovEnergy f` for real `c`; `m_a = 2 sinh(a/2) oddProfile a`; the two-sided representation and the variation criterion for `oddProfileTest a w` |
| `OddProfileOriginFailure` | short-shift Lipschitz bound and long-shift bound of the folded shift integrand; the majorant `t^{−1/2} 1_{t≤1} + e^{−t/2} 1_{t>1}`; archimedean part `≤ K√x`; summability of the prime series for dominated profiles; prime part `≤ prime-2 term + Φ(x)ω(x) primeKernelSum x`; `primeKernelSum ≤ cosh(x/2) + 2|c|Φ(0) + 2∫gammaSourceBound`; the general origin failure |
| `SignedCombinationOriginFailure` | `Φ(y−a) ≤ (Φ(0)/Φ(b)) Φ(y−b)` for `0 ≤ a ≤ b`, `y ≥ 0`; origin failure of `ω_a` and of signed combinations `c₁ω_a + c₂ω_b` nonnegative on the half line via the general theorem |
| `ShiftedGroundStateCrossTermRepresentation` | `crossShift`, `crossEnergy`; `D = 2∫u² m_a C_a − 2X`; cross-term form of the Markov energy and its lower bound `≥ 2X − 2∫u² m_a (C_a − 2 sinh(a/2) sinh(x/2))` |
| `TwoBumpProfile` | `twoBumpProfile`; evenness, `C²`, compact support; `m_a u = g(·−a)` on the half line; cross term `= autoCorr g (t − 2a)`; prime cross energy `= windowSum Λ (2a)` |
| `FarApartBumpsPositivity` | `∫Φ ≤ 1/2`; archimedean collar `≤ 1` and the collar excess `≤ windowCollarConstant` on `|x−a| ≤ 1/4`; `windowKernelFloor`; remainder bound; archimedean cross term `≤ (3/2) sup|ρ_g|`; `exists_shift_markovEnergy_twoBumpProfile_pos` |
| `ShiftedGroundStateInfinityFailure` | uniform bound of `∫_0^∞ symArchTerm`; the signed prime shift sum `P(x+a) − P(x−a)`; `C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K` for `x ≥ a` (`two_mul_source_sub_le_shiftedCollarMass`); folded defect `≤ −2Θ(x)(sinh(a/2) sinh(x/2) − K)`; strict folded subsolution on `[X, ∞)` (`exists_infinity_window_foldedGenerator_lt_potential`) |
| `ShiftAveragedKernel` | `∫ f(c − a) da = ∫ f`; half-line integral of an even function; `G` even, `0 ≤ G ≤ Φ(|z|/2)`; the four shift integrals of translated kernel products; `∫_0^∞ m_a(x) m_a(y) da = G(x−y) − G(x+y)`; `∫ Φ sinh(s/2) = 0`; `∫ sinh(a/2) Φ(x ∓ a) da = ± sinh(x/2)/2`; `∫_0^∞ 4 sinh(a/2) m_a(x) sinh(x/2) da = 2 sinh²(x/2)` |
| `ShiftAveragedShifts` | `averagedKernel`, `averagedReflectedShift`, `averagedSameSideShift`; product integrability in `(a,x)` through the exact `a`-integrals; the shift averages of one reflected and one same-side shift; linear and decay bounds; measurability in `t` |
| `ShiftAveragedEnergies` | `integrable_tsum_of_nonneg`; `Φ ≤ C e^{−8|x|}`; `Σ Λ(n)n^{−1/2}(1 + log n) Φ((log n − c)/2) < ∞`; Fubini of the `a`-integral with the archimedean integral and the prime sum for both energies; `averagedReflectedEnergy`, `averagedSameSideEnergy`; the shift averages of `D_a`, `S_a` and of the source |
| `ShiftAveragedVariationInequality` | `K(x,t−x) = G(2x−t) − G(t)`, `K(x,x+t) = G(t) − G(2x+t)`; `∫_0^∞ markovEnergy(Θ(ω_a u)) da = 2S̄ − D̄ + 2∫u² sinh²(x/2)`; RH ⟹ the shift-averaged variation inequality, also in autocorrelation form |
| `ShiftedGroundStatePlateauPositivity` | `∫ m_a sinh(x/2) = sinh(a/2)`, half-line value `sinh(a/2)/2`; `Φ ≤ C e^{−16|x|}`; tail `∫_{x>L} m_a sinh(x/2) ≤ C e^{16a} e^{−8L}`; the source of a plateau profile `≥ sinh(a/2)/2 − C e^{16a} e^{−8L}`; pointwise and integrated bounds `D ≤ K_a e^{−8L}`; `markovEnergy(Θ(ω_a u)) ≥ sinh²(a/2)` for every `a > 0` on every wide enough plateau (unconditional) |
