# AAL — the asymptotic abscissa law

A problem dossier for research agents: the exact statement, what proving or disproving it means, everything the corpus proves around it, the models it must defeat, the routes that are closed and why, and the open problems.

**Corpus checkpoint:** commit `b75c701762` plus the working tree of 2026-11-07. Every Lean declaration cited below was located with the corpus search tool and its statement read. Lean paths are relative to `formal/GaloisForLFunctions/`. The research log is `logs/aal-report-research.md`.

**Evidence tags.** `[L]` Lean declaration, statement read. `[S]` Lean source unfinished: the statement is in a docstring and the theorem is absent. `[D]` deduction from `[L]` statements, not itself a Lean theorem. `[C]` classical result, not formalized here. `[H]` heuristic, unproved.

**Ledger names.** AAL is B83 in the obstacles ledger. The adjacent walls are Γ67 (split), Γ68 (AAL), Γ69 (producers), Γ80 (finite oscillation), Γ81 (dilation annihilation), Γ82 (rightmost-zero jets), Γ106–Γ107 (transport), Γ115 (tail of a return), B13 (finite off-line support), B89 (bounded return at a right zero) and B96 (tail law at the Kronecker scale).

---

## 0. One page

**The statement.** For every `σ ≥ ½`, the set of nontrivial zeros of `ζ` with `Re ρ > σ` is either empty or infinite. Equivalently `Θ∞ = Θ`, where `Θ = sup Re ρ` and `Θ∞` is the limit superior of `Re ρ` as `|Im ρ| → ∞`. In Lean this is `RHTower.AsymptoticAbscissaLaw`.

**Status.** Open. Three facts are proved in Lean:
- RH ⇒ AAL;
- RH ⇔ ZAL ∧ AAL, where ZAL is `Θ∞ = ½`;
- ¬AAL ⇒ quasi-RH ∧ ¬RH.

The third gives `qRH ∨ AAL`. AAL implies no zero-free region.

**Prove or disprove.** A disproof refutes RH and proves quasi-RH in the same stroke. It also needs a theorem confining every zero above some height to `Re ρ ≤ β₁ < Θ`, which no finite computation can supply. The expected answer is that AAL holds. A proof is the realistic target.

**The negation is one rigid object.** ¬AAL holds exactly when `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` for a nonzero finite real trigonometric polynomial `T`. The frequencies of `T` are the ordinates of a finite top layer of zeros. Its coefficients are `−ord/(Θ+iμ)`, and it is separated from every other zero by zero-free vertical strips at all heights.

**Sufficient conditions.** More than twenty Lean theorems produce AAL from an arithmetic or spectral input, and each input is open. They fall into two classes:
- **Attainment producers** prove more than AAL: that no zero attains a maximal real part above `½`.
- **Transport producers** prove exactly AAL. Every one of them is a reformulation, because a return of `ζ` strong enough to move a zero is itself a zero.

**Models.** Five kinds of model violate AAL (the discrete Beurling case is `[S]`, the heat case `[D]`):
- continuous positive Beurling systems;
- discrete positive Beurling systems;
- `ξ` multiplied by finitely many symmetric factors;
- symmetric zero relocation;
- the heat deformations `H_t` for `0 < t < Λ`.

So a proof must use the Dirichlet series over `ℕ`, and either integer norms or the exact functional equation. It must not be stable under the heat flow.

**The open core.** A mechanism is needed that carries one zero at bounded height to infinitely many zeros at large height with real parts arbitrarily close to it.

In the world ¬AAL the prime error is known to power precision `x^Θ`, which is beyond every unconditional estimate. So a contradiction cannot come from an estimate of `ψ`. It must come from one of three things:
1. an unconditional constraint valid at that precision, namely the exact discrete structure of `ℤ` (counts, carries, jumps, unique factorization);
2. a power-precision inequality (mean values, large sieve, Weil bounds), used so that no AAL-violating model satisfies it;
3. the qRH-strength regularity that ¬AAL itself forces at large heights, played against the zero at low height.

---

## 1. The problem

### 1.1 Definitions

| Symbol | Meaning | Lean |
|---|---|---|
| zero | nontrivial zero `ρ = β + iγ` of `ζ`, `0 < β < 1`, counted with multiplicity | `RHTower.XiZeroCopy` (a zero of `ξ` with one copy per unit of multiplicity), `RHTower/XiCanonicalProduct.lean:25` [L] |
| `Θ` | `sup Re ρ`, in `[½, 1]` | `zetaZeroAbscissa` [L] |
| `Θ∞` | `inf{σ ≥ ½ : #{ρ : Re ρ > σ} < ∞}`; equivalently `σ ≥ Θ∞` iff all zeros above some height have `Re ρ ≤ σ` | `zetaAsymptoticAbscissa`, `mem_zetaAsymptoticAbscissaSet_iff_eventually_height` in `ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean` [L] |
| `Θ₂` | `sup({½} ∪ {Re ρ : Re ρ < Θ})`, the second abscissa | `zetaSecondAbscissa`, `ZeroConfigurationGeometry/PrimeErrorFiniteOscillationRigidityAndSignChanges.lean:358` [L] |
| ZAL | zeros approach the line: `Θ∞ = ½` | `RHTower.ZerosApproachLine` (stated on the left side, `β < ½ − h`), `RHTower/LindelofCosineFiniteDefectDepth.lean:48`; `zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half` [L] |
| qRH | quasi-RH: `Θ < 1` | — |
| FOL | finitely many off-line zeros | `RHTower.FiniteOffLine`, `RHTower/XiSliceEventualPositivityFiniteOffLine.lean:39` [L] |
| attained top | some zero has `Re ρ = β₀` and none has `Re ρ > β₀` | `RHTower.AttainedTop β₀`, `RHTower/WeilLagFunctionSingleBase.lean:58` [L] |
| NAT | no attained top above the line: `¬∃ β₀ > ½, AttainedTop β₀` | — |
| right zero, top layer | a zero with `β > ½`; the zeros with `β = Θ` | — |
| `ψ`, `E(x)` | Chebyshev's function; `E(x) = ψ(x) − x` | `Chebyshev.psi` |
| `Φ` | the Weil lag function `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`, real | `weilLagFunctionReal`, `RHTower/WeilLagFunctionOneSided.lean:62` [L] |
| `E_y`, `M_y`, `ζM_y` | Euler head over primes `≤ y`, mollifier `1/E_y`, Euler tail | `RHTower.eulerHead`, `eulerMollifier`, `eulerTail` [L] |

The corpus proves `½ ≤ Θ∞ ≤ Θ ≤ 1` (`half_le_zetaAsymptoticAbscissa`, `zetaAsymptoticAbscissa_le_zetaZeroAbscissa`, `zetaAsymptoticAbscissa_le_one`) [L].

### 1.2 What is to be proved

> **AAL.** `Θ∞ = Θ`.

Equivalent wordings (a proof of any one is a proof of AAL):
1. For every `h ≥ 0`: if only finitely many zeros satisfy `Re ρ > ½ + h`, then none does. This is the Lean definition.
2. For every `σ ≥ ½`, the set `{ρ : Re ρ > σ}` is empty or infinite.
3. For every `σ < Θ`, infinitely many zeros satisfy `Re ρ > σ`.
4. For every right zero `ρ` and every `r > 0`, infinitely many zeros satisfy `Re w > Re ρ − r`.

Wordings 2–4 are direct consequences of the definition [D]. The direction 4 ⇒ AAL is `asymptoticAbscissaLaw_of_infinite_zeros` [L].

```lean
-- RHTower/ZetaWeakRecurrenceLadderCollapse.lean:282
def AsymptoticAbscissaLaw : Prop :=
  ∀ h : ℝ, 0 ≤ h → {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite →
    ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h
```

AAL says nothing about the value of `Θ`. Under AAL, `Θ` may equal `1`, and it may or may not be attained.

### 1.3 What is to be disproved

> **¬AAL.** There is `σ ≥ ½` with `{ρ : Re ρ > σ}` finite and nonempty. Equivalently `Θ∞ < Θ`.

The top is then attained, by finitely many zeros. The full structure is §4.

### 1.4 The tasks, stated for Lean

| Task | Lean target | Remarks |
|---|---|---|
| Prove AAL | `theorem : RHTower.AsymptoticAbscissaLaw` | `#print axioms` may show only `propext`, `Classical.choice`, `Quot.sound`. No added hypothesis, no `Prop` interface standing for an unproved input. |
| Prove AAL in an equivalent form | `¬ GaloisForLFunctions.ZeroConfigurationGeometry.PrimeErrorIsFiniteOscillation`; or any form in §2 | — |
| Prove AAL through a producer | the hypothesis of any producer in §5, proved for the actual `ζ` | The producer's hypothesis is the open mathematics. Citing the producer with its hypothesis assumed proves nothing. |
| Disprove AAL | `theorem : ¬ RHTower.AsymptoticAbscissaLaw` | By `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` this needs `β₁ < β* < 1`, `T* > 0`, a finite nonempty layer on `Re s = β*`, and **every zero above `T*` in `[1 − β₁, β₁]`**. The last item is a zero-free region of quasi-RH type at all large heights. |

The disproof direction is therefore not a computation. A verified off-line zero would refute RH, and it would not refute AAL until the zeros above it were confined, at all heights, strictly to its left. A disproof proves `Θ < 1` (§1.5).

### 1.5 Position relative to RH and quasi-RH

| | ZAL (`Θ∞ = ½`) | ¬ZAL (`Θ∞ > ½`) |
|---|---|---|
| **AAL (`Θ∞ = Θ`)** | RH | RH false; off-line zeros at unbounded heights with real parts accumulating at `Θ = Θ∞ > ½`; no finite top; `Θ = 1` is not excluded |
| **¬AAL (`Θ∞ < Θ`)** | finitely many zeros beyond each positive depth, a finite top at `Θ < 1`; contains the finite-support case FOL ∧ ¬RH (B13) | a finite top layer above an infinite population whose real parts accumulate at `Θ∞ ∈ (½, Θ)` |

The proved relations:
- RH ⇔ ZAL ∧ AAL (`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`, `RHTower/ZetaWeakRecurrenceLadderCollapse.lean:292`) [L].
- RH ⇒ AAL (`asymptoticAbscissaLaw_of_riemannHypothesis`) [L].
- ¬AAL ⇒ qRH: the spectral-gap theorem gives no zero with `Re s > β*` and `β* < 1` (`not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`) [L]. So `qRH ∨ AAL` is a corollary of a Lean theorem [D].
- ZAL ⇒ qRH: finitely many zeros right of `¾`, each with `Re ρ < 1` [D].
- ZAL ∧ ¬RH ⇒ the top is attained (`exists_attainedTop_of_zerosApproachLine`, `RHTower/ZerosApproachLineAttainment.lean:65`) [L]. So under ZAL, AAL ⇔ NAT ⇔ RH [D].
- AAL ⇏ qRH: AAL is satisfied by zero configurations with `Θ = Θ∞ = 1`. No implication from AAL to any zero-free region is known [D].

AAL passes the corpus validation tests T1–T7 (obstacles summary §3) [D]. It is not RH-equivalent, it is implied by RH, it is false on corpus fakes, and it moves several walls (Γ68, Γ69, Γ106, Γ115, B13).

### 1.6 Five facts that are easy to misread

1. **¬AAL does not mean finitely many off-line zeros.** Below `β₁` there may be infinitely many. The case FOL ∧ ¬RH (B13) is the special case in which all off-line zeros form the finite layers.
2. **AAL does not mean infinitely many off-line zeros.** Under RH it holds with none. AAL ∧ ¬RH does force infinitely many.
3. **AAL is weaker than NAT.** AAL permits a top `Θ > ½` attained by one zero, provided infinitely many zeros have real parts in every interval `(Θ − ε, Θ]`. Most Lean producers prove NAT (§5.1).
4. **The zero of maximal angle exists under ¬RH in every world.** In the squared variable `Q(z²) = Ξ(z)` the maximal argument is always attained (`exists_zero_of_maximal_angle`, `RigidArithmeticOfCuts/TheZeroOfMaximalAngle.lean:256`) [L]. It is not a signature of ¬AAL.
5. **A top layer lies above height 67.** No off-line zero has ordinate in `(0, 67]` (`rhVerifiedThrough_sixtySeven`, `VerifiedHeightRungs/HadamardBudget/TheVerifiedHeightSixtySeven.lean:463`) [L]. Classically, no off-line zero lies below height `3·10¹²` [C].

---

## 2. Equivalent forms

| # | Form | Lean | Tag |
|---|---|---|---|
| E1 | `Θ∞ = Θ` | `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa` (`ZeroConfigurationGeometry/AsymptoticAbscissaSpectralGapAndTopAnnihilator.lean:158`); displacement form `asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_sub_half_eq` | [L] |
| E2 | No bilateral isolated spectral gap (the configuration of §4.1, item 1) | `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` (same file, `:197`) | [L] |
| E3 | `ψ(x) − x` is not a finite oscillation: there are no `β > ½`, `η > 0`, nonzero `T(u) = Re Σ_{ω∈S} c(ω)e^{iωu}` with `|ψ(x) − x − x^β T(log x)| ≤ C x^{β−η}` for large `x` | `PrimeErrorIsFiniteOscillation` (`ZeroConfigurationGeometry/TheOneOffsAreFiniteOscillationsOfThePrimeError.lean:41`), `not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation` (`:736`) | [L] |
| E4 | For two distinct primes `p ≠ q` (any pair), no finite frequency set `S`, `β ∈ (½,1)`, `η > 0` with a zero right of `β − η` makes both dilation combinations collapse `ψ` to its linear main term to `O(x^{β−η})` | `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation` (`ZeroConfigurationGeometry/MultiplicativeDilationAnnihilationOfPrimeError.lean:820`) | [L] |
| E5 | Every right zero `ρ` and every `r > 0` have infinitely many zeros with `Re w > Re ρ − r` | ⇐ `asymptoticAbscissaLaw_of_infinite_zeros` (`ArithmeticAuxiliaryDynamics/TheMissingInputOfTransport.lean:236`); ⇒ by definition | [L]/[D] |
| E6 | For `0 ≤ a < ½`, removing finitely many zero waves from `Φ` never lowers its one-sided exponent: if `Φ_S ≤ Me^{au}` for a finite `S`, then `Φ ≤ M′e^{au}` | `exists_subtractedLag_le_exp_iff_finite_re_gt`, `exists_subtractedLag_le_exp_iff_forall_re_le_of_asymptoticAbscissaLaw` (`RHTower/WeilLagAsymptoticAbscissa.lean:64`). The converse uses Landau's theorem on the unsubtracted lag | [L]/[D] |

E3 and E4 are prime-side statements and are sign-free. E5 is the transport form. E6 says the infimal growth exponent of the lag after finite subtraction is `Θ∞ − ½`, and without subtraction it is `Θ − ½`.

---

## 3. What a proof of AAL would give

**The collapse atlas** (`riemannHypothesis_tfae_of_asymptoticAbscissaLaw`, `ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean:365`) [L]. Under AAL the following are equivalent to RH:

| Statement | Lean (same module unless stated) |
|---|---|
| ZAL | `riemannHypothesis_iff_zerosApproachLine_of_asymptoticAbscissaLaw` |
| finitely many off-line zeros | `riemannHypothesis_iff_finiteOffLine_of_asymptoticAbscissaLaw` |
| finite Krein–Langer index `κ(K_ζ) < ∞` | `riemannHypothesis_iff_negIndex_zetaKernel_lt_top_of_asymptoticAbscissaLaw` |
| bounded de Bruijn–Newman nonreal zero counts | `riemannHypothesis_iff_bounded_nonrealZeroCount_of_asymptoticAbscissaLaw` |
| finite critical source energy | `riemannHypothesis_iff_xiCriticalSourceEnergy_ne_top_of_asymptoticAbscissaLaw` |
| eventual Hadamard positivity | `riemannHypothesis_iff_eventualHadamardPositivity_of_asymptoticAbscissaLaw` |
| eventual filtered central-gap budget | `riemannHypothesis_iff_eventualFilteredCentralGapBudget_of_asymptoticAbscissaLaw` |
| finite-dimensional odd bound-state space | `finiteDimensional_oddBoundStateSpace_iff_riemannHypothesis_of_asymptoticAbscissaLaw` (`RHTower/CrossRouteReceiverBridges.lean:211`) |

Under AAL, every large-height gauge reads the global abscissa [L]:
- eventual Hadamard positivity right of `½ + h` ⇔ every zero has `Re ρ ≤ ½ + h` (`eventualHadamardPositivityRight_iff_forall_re_le_of_asymptoticAbscissaLaw`);
- the eventual central-gap rate equals the all-height rate (`eventualFilteredCentralGapRate_iff_filteredCentralGapRate_of_asymptoticAbscissaLaw`);
- both are the global cubic-spline prime-sum bound (`eventualHadamardPositivityRight_iff_spline_prime_sum_le_of_asymptoticAbscissaLaw`, `eventualFilteredCentralGapRate_iff_spline_prime_sum_le_of_asymptoticAbscissaLaw`);
- the subtracted lag exponent is the full exponent.

**Effect on the programmes** (obstacles summary §3) [L/D]:
- The finite half of "finite or shallow exceptions remain" disappears in several programmes: LA (`N_d` bounded ⇒ RH), HF, AKLT and CWS (finite index ⇒ RH), ZCG (bounded heat count ⇒ RH), and the FFP, WD and RW large-height receivers.
- The split skeleton F1 becomes the architecture: one ZAL producer closes RH.
- The one-off countermodels of APD, RAC and the continuous Beurling systems stop being models of `ζ`.
- B13 is answered.

**What AAL does not give.** It gives no zero-free region and no ZAL. RH still needs a ZAL producer, which is at least quasi-RH [D].

---

## 4. The world ¬AAL: what a proof by contradiction may assume

### 4.1 Structure

| # | Fact under ¬AAL | Lean | Tag |
|---|---|---|---|
| 1 | **Bilateral spectral gap.** There are `½ ≤ β₁ < β* < 1` and `T* > 0` such that: no zero has `Re s > β*`; a finite nonempty conjugate-symmetric layer lies on `Re s = β*` with `|γ| ≤ T*`; its reflection lies on `Re s = 1 − β*`; the strips `(β₁, β*)` and `(1 − β*, 1 − β₁)` are zero-free at all heights; every other strip zero, and every zero above `T*`, lies in `[1 − β₁, β₁]` | `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` | [L] |
| 2 | `Θ∞ ≤ Θ₂ < Θ < 1` and `Θ > ½` | `exists_primeErrorFiniteOscillation_of_lt_gap` (`…RigidityAndSignChanges.lean:475`) | [L] |
| 3 | **Finite oscillation.** `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` with `T` a nonzero finite real trigonometric polynomial. Every `0 < η < Θ − Θ₂` is achieved | `primeErrorIsFiniteOscillation_of_not_asymptoticAbscissaLaw`, `exists_primeErrorFiniteOscillation_of_lt_gap` | [L] |
| 4 | **Rigidity of every witness.** `β = Θ`. The Fourier coefficient at `μ` is `−ord_{Θ+iμ}(ζ)/(Θ+iμ)`, so the frequencies are the top ordinates and the constant mode is `0`. `(β, T)` is unique. Every valid saving satisfies `η ≤ Θ − Θ₂ ≤ Θ − Θ∞` | `abscissa_eq_zetaZeroAbscissa_of_finiteOscillation`, `oscillationCoeff_eq_neg_zeta_order_div`, `oscillationCoeff_zero_eq_zero`, `primeErrorFiniteOscillation_unique_abscissa_and_profile`, `eta_le_zetaZeroAbscissa_sub_secondAbscissa` | [L] |
| 5 | **Sign changes.** There are `L, δ > 0` with points in every log-window `[u₀, u₀ + L]` where `ψ(e^u) − e^u > δe^{Θu}`, and points where it is `< −δe^{Θu}` | `exists_bounded_log_gap_sign_changes_of_primeErrorIsFiniteOscillation` (`:588`) | [L] |
| 6 | **Parity transfer.** `Σ_{n≤x}(−1)^nΛ(n) = 2⌊log₂⌊x⌋⌋ log 2 − ψ(x)`, so the oscillation transfers with the same remainder | `sum_alternating_vonMangoldt_eq`, `alternating_vonMangoldt_finiteOscillation` | [L] |
| 7 | **Dilation annihilation at every base `b > 1`.** `Σ_k P_k ψ(x/b^k) = κ_b x + O(x^{Θ−η})` with `P = Π_ω(1 − 2b^Θ cos(ω log b)X + b^{2Θ}X²)` and `κ_b ≥ (1 − b^{Θ−1})^{2|S|} > 0`. A one-base bound pins every zero right of `σ₀` to `Re ρ = Θ` and to `α + (2π/log b)ℤ`. Two primes make the layer finite | `dilationSetOp_rpow_mul_finiteOscillation_eq_zero`, `mainTermFactor_ge_pos`, `re_eq_and_im_mem_periodic_of_dilation_bound`, `finite_xiZeroCopy_of_twoPrime_dilation_bound` | [L] |
| 8 | **Top annihilator.** `D(s) = Π_{ρ∈F}(1 − b^{ρ−s})^{m(ρ)}` vanishes on the top layer `F` and is bounded away from `0` on `Re s ≤ ½` | `singleBaseTopAnnihilator_eq_zero_of_mem`, `norm_singleBaseTopAnnihilator_ge_of_re_le_half` | [L] |
| 9 | **Twisted functional equation.** Dividing by the finite right Blaschke product `B` of the layer twists `s ↔ 1 − s` by the nonconstant phase `B(s)²` | `twisted_functionalEquation_div_finiteRightBlaschke` | [L] |
| 10 | **Persistent jets at a rightmost zero `ρ` of multiplicity `m`.** Put `a_{k,n} = Λ(n)(log n)^k/(k! n^{ρ+1})`. Then `Σ_n a_{k,n} → −m`; `Σ_n |a_{k,n}|² → 0`; the off-diagonal `Re Σ_{n≠j} a_{k,n}\overline{a_{k,j}} → m²`; and the limit `m²` survives removal of both orientations of all shifts `h ≤ ⌊r^k⌋`, for `1 < R < Re ρ + ½` and `r < R²`. Proper prime powers can be removed | `not_asymptoticAbscissaLaw_has_persistent_low_jets`, `…_has_raw_prime_moment_limit`, `…_has_nonzero_moment_and_vanishing_diagonal`, `…_has_positive_offDiagonal_limit`, `…_has_positive_limit_after_short_shifts`, `…_has_prime_only_jet_limit` (`ZeroConfigurationGeometry/FiniteExceptionalLayersForcePersistentLowJets.lean`) | [L] |
| 11 | **High jet bounds.** `ζ` is zero-free on `{Re s > β, |Im s| > H}` with a zero right of `β`. On such discs `‖(ζ′/ζ)^{(k)}‖ ≤ k! C log(t + r)/(δr^k)`, with an exponential lower bound on derivative return heights | `not_asymptoticAbscissaLaw_has_high_jet_bounds` (`ZeroConfigurationGeometry/FiniteExceptionalLayersGiveHighZeroFreeJetBounds.lean:140`) | [L] |
| 12 | **Transport fails.** Every phase return has unbounded translates on every connected domain joining a zero right of `β₁` to `Re s > 1`. At every aligned shift past a height, `|ζ| > N^A` somewhere on the disc about each such zero | `not_translatesBoundedOn_of_finite`, `exists_large_value_of_finite`, `exists_large_value_of_finite_on_disc` | [L] |
| 13 | **Returns at a top zero.** In every world, returns are tail-bad at every cut and have density zero. Under ¬AAL they have finite total measure, since returns of strength `m/2` are bounded by `2r` times the zeros in the translated strip, which are finitely many | `exists_returns_tailBad_and_rare` (`TailArithmeticOfThePrimeOrbit/TheTailOfAReturnCarriesTheZero.lean:221`), `volume_returnSet_le_zeroCount` (`ArithmeticAuxiliaryDynamics/TheTransportCountOfAZero.lean:37`) | [L]/[D] |
| 14 | **Lag excursions.** For `a < Θ − ½` and every `M`, `{L : Φ(L) > Me^{aL}}` has upper density at least `Re(1/(ρ₀(1−ρ₀)))/(4Σ|1/(ρ(1−ρ))|)`. Every lag progression `Φ(mℓ)`, `ℓ ≠ 0`, is unbounded above | `not_volume_le_of_attainedTop`, `exists_lag_progression_gt_of_attainedTop_of_ne` | [L] |
| 15 | **Spectral readings of the attained top.** The restricted Weil ground energy satisfies `μ₀(B) ≤ −c′e^{2(Θ−½)B}/B³`. `K_ζ` is bounded on only finitely many prime towers | `polarGroundEnergy_le_neg_exp_of_attainedTop` (`RHTower/ConstrainedWeilPolarGroundDecay.lean:415`), `zeta_finite_primes_bounded_of_attained_depth` | [L] |
| 16 | **The B13 sub-world** (FOL ∧ ¬RH): `κ(K_ζ) < ∞`, hence Lindelöf and quasi-RH; the inner field tends to `0` on every vertical line | `lindelof_of_negIndex_zetaKernel_lt_top`, `quasiRH_of_negIndex_zetaKernel_lt_top` (`HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean:119,127`), `infinite_or_tendsto_innerField` | [L] |

Facts that hold in every world, and so also under ¬AAL [L]:
- every right zero is a Lefschetz ratio: `W(T_{p^{m+1}}g,g)/W(T_{p^m}g,g) → p^{ρ−½}`, and two primes determine it (`zeta_exists_test_lefschetz_ratio`, `ArithmeticCastelnuovoSeveri/OffLineZerosAreLefschetzRatios.lean:180`);
- a top zero lies above height 67;
- the explicit zero-free region `1 − 1/(58 log(|t| + 5))` (`RHTower/ZetaRecurrenceAtEveryPointModuloItsZeros.lean`).

### 4.2 What ¬AAL does not supply

- **Finiteness of off-line zeros.** Only in the B13 sub-world.
- **Lindelöf from the index.** Only in the B13 sub-world. In general ¬AAL gives a zero-free half-plane `Re s > β₁` above `T*`. Classically that yields Lindelöf-type bounds `|ζ(σ+it)| = t^{o(1)}` for `σ > β₁` [C].
- **Simplicity of the top zeros** or **ℚ-linear independence of the top ordinates.** The coefficients of `T` carry multiplicities. The jets use the multiplicity `m`.
- **Anything at the second layer.** `Θ₂` may be the abscissa of another finite layer above `Θ∞`.

### 4.3 The precision of the world ¬AAL

Unconditionally, `ψ(x) − x ≪ x exp(−c(log x)^{3/5}(log log x)^{−1/5})` [C]. The corpus has the Vinogradov–Korobov rate in `ArithmeticAuxiliaryDynamics` (`hasRate_vk`) and the Vinogradov–Korobov bound on the `1`-line in `TailArithmeticOfThePrimeOrbit/TheVinogradovKorobovBoundOnTheOneLine.lean` [L].

Under ¬AAL, `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` with `Θ < 1`. No unconditional estimate of `ψ`, `M` or `L` resolves the scale `x^Θ`, so none distinguishes AAL from ¬AAL. A contradiction must come from one of three sources [D]:
1. information valid at every precision: exact identities, which are blind (§7); positivity; integrality; discreteness;
2. unconditional power-saving inequalities for other objects: mean value theorems, large sieve, Weil bounds;
3. the analytic structure that ¬AAL itself forces, such as qRH-level regularity at large heights, played against the zero at low height.

---

## 5. Sufficient conditions proved in Lean

Each row is an unconditional Lean theorem. Its hypothesis is open for `ζ`, unless the table says otherwise.

### 5.1 Attainment producers (they prove NAT)

These producers use one mechanism. An attained top `ρ₀` carries a positive weight at a real point:
- `Re 1/(ρ(1−ρ)) > 0`;
- Dirichlet's theorem aligns the finitely many top phases;
- a twist `1 + cos(γ₀L)` moves the weight to a real exponent;
- a one-round Landau theorem detects that exponent.

A non-attained supremum has no such real point. That is the only escape, which is why this class produces NAT and not RH [L].

| Input (for the actual `ζ`) | Lean | Remarks |
|---|---|---|
| `Φ(m log b)` bounded above along one geometric progression, `b ≥ 2` | `asymptoticAbscissaLaw_of_pow_integerLag_bddAbove` (`RHTower/AsymptoticAbscissaLawProducers.lean`), via `riemannHypothesis_or_not_attained_of_forall_le` (`RHTower/WeilLagFunctionSingleBase.lean:426`) | Over a finite field this is Stepanov along `qⁿ` (§8.2) |
| `Φ(mℓ)` bounded above along one progression, any `ℓ ≠ 0` | `asymptoticAbscissaLaw_of_progression_bddAbove` (`RHTower/WeilLagProgressionZerosApproachLine.lean:53`) | RH ⇔ ZAL ∧ one bounded progression. RH ⇔ the set of good spacings is not meagre (`riemannHypothesis_iff_not_isMeagre_bddAbove_progression`) |
| integer lags bounded above on a logarithmically dense set | `asymptoticAbscissaLaw_of_logDense_integerLag_bddAbove` | Samplings with power-saving gaps `O(n^{1−δ})` are RH-complete; log-dense sub-power meshes give only AAL (big-picture card, addendum 7) [L/D] |
| `∀a > 0`: `Φ(L) ≤ M_a e^{aL}` for `L ≥ 0` off a set of finite measure, of Abel density zero, or of lower density zero | `asymptoticAbscissaLaw_of_forall_le_exp_finiteMeasure` (`RHTower/WeilLagFunctionFiniteMeasureExcursion.lean:217`), `asymptoticAbscissaLaw_of_forall_le_exp_abelDensityZero` (`RHTower/WeilLagFunctionDensityZeroExcursion.lean:793`) | The lag form, §8.2 |
| subexponential lower bounds for the two-bump prime-window functional on one grid `kℓ` | `zeta_asymptoticAbscissaLaw_of_grid_primeWindow_subexponential`, `not_attainedTop_of_grid_lag_subexponential` (`RHTower/CrossRouteReceiverBridges.lean:367,404`) | The continuous-`v` version is RH (`zeta_riemannHypothesis_iff_forall_pos_lag_primeWindow_ge_neg_exp`, `:477`) |
| twisted plateau Weil energies `≥ 0` | `asymptoticAbscissaLaw_of_twistedPlateau_nonneg` | a sign statement |
| JAS real-amplitude positivity at level one above `X` | `asymptoticAbscissaLaw_of_jasRealPositiveAbove` | — |
| JAS dressed positivity at some `σ ≤ 1` | `asymptoticAbscissaLaw_of_jasDressedPSD`, via the off-line chain | — |
| typical JAS positivity at every `σ ∈ (½, 1)` | `asymptoticAbscissaLaw_of_jasTypicalPositive` (`RHTower/JointAncestryTypicalAsymptoticAbscissa.lean:54`) | "an attainment receiver" |
| JAS constant-vector positivity on infinitely many dyadic shells `(N, 2N]` | `asymptoticAbscissaLaw_of_frequently_jasConstProductPositiveOn_shell` (`ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean:264`) | — |
| `K_ζ` bounded, or positive definite, on infinitely many prime towers | `asymptoticAbscissaLaw_of_infinite_primes_bounded`, `…_posDef` (same file, `:155`, `:177`) | — |
| bounded coupling on one positive cone `⟨p⟩₊ × ⟨q⟩₊` | `asymptoticAbscissaLaw_of_bounded_coneCoupling` (`:232`) | The undamped cone bound is killed as a zero-width selector (killed routes, "coupling-growth"); it remains an AAL producer |
| subexponential floor `μ₀(B) ≥ −C_εe^{εB}` for the restricted Weil ground energy | `asymptoticAbscissaLaw_of_polarGroundEnergySubexponential` (`RHTower/PolarGroundEnergySubexponentialZerosApproachLine.lean:49`) | — |
| eventual nonnegativity of single-scale grid factorial-tent energies | `asymptoticAbscissaLaw_of_eventually_gridTentPattern_nonneg` (`arithmetic-positivity-theory/FactorialTentDepthGapClusterAndPolarGraphBridge.lean:549`) | — |
| every off-line zero is strictly exceeded in distance from the line by another | `asymptoticAbscissaLaw_of_offLine_chain` | This is a form of NAT itself |

### 5.2 Transport producers (they prove exactly AAL)

These producers use one mechanism. Kronecker phase returns `n^{−iτ_j} → 1` always exist, and translates converge to `ζ` on `Re s > 1`. A bound on the translates near a zero gives convergence near it, by Vitali or by three circles. Rouché or Hurwitz then copies the zero to the translated height.

| Input | Lean | Remarks |
|---|---|---|
| weak recurrence: return shifts beyond every height for every disc in the right strip, or only for discs about right zeros | `asymptoticAbscissaLaw_of_weaklyRecurrent`, `asymptoticAbscissaLaw_of_zeroDiscWeaklyRecurrent` (`RHTower/ZetaWeakRecurrenceLadderCollapse.lean`) | RH ⇔ ZAL ∧ zero-disc weak recurrence (`riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent`). Bagchi's strong recurrence implies weak recurrence and is RH [L/C] |
| infinitely many zeros near each right zero (E5) | `asymptoticAbscissaLaw_of_infinite_zeros` | equivalent to AAL |
| a phase return with translates bounded on a connected domain joining each right zero to `Re s > 1` | `asymptoticAbscissaLaw_of_boundedReturns` (`ArithmeticAuxiliaryDynamics/TheMissingInputOfTransport.lean:278`) | Such domains lie in `Re s > ½` (`IsPhaseReturn.re_gt_half_of_translatesBoundedOn`) |
| **slow aligned returns right of the line:** for each right zero `ρ = β + iγ` some `σ₀ ∈ [½, β)`, and head returns `IsHeadReturn N τ` of arbitrarily large length `N` and height `τ` with `|ζ(s + iτ)| ≤ N^{transportExponent β (3 − σ₀)}` on `closedBall(3 + iγ, 3 − σ₀)` | `asymptoticAbscissaLaw_of_slowReturns_right` (`ArithmeticAuxiliaryDynamics/TheSlowReturnBoundLivesRightOfTheLine.lean:1283`) | This is B89. On the disc of radius `31/10` the hypothesis is RH (`slowReturnHypothesis_iff_riemannHypothesis`, `:975`) |
| inner-field decay on every line `Re s = ½ + h` together with zero-disc weak recurrence | `riemannHypothesis_iff_tendsto_innerField_and_recurrent` (`ArithmeticInnerFunctionTheory/TheZeroOneLawOfRecurrence.lean:453`) | the split through the inner field |

**Transport is a reformulation, not a free input** [L]. The transport count `volume_returnSet_le_zeroCount` bounds returns of strength `m/2` on an isolating disc of radius `r` by `2r` times the number of zeros in the translated strip. "Returns strong enough to move the zero are as rare as the zeros they move." So every transport producer asks to produce zeros at large heights.

### 5.3 Thin, thick and compressing receivers

The `rh-big-picture-interpretation` card (addenda 5–7) states one principle, with Lean closures [L/D].
- A receiver decides RH outright when its test family is thick: an interval or non-meagre set of lag spacings, all heights, or all prime sets in dyadic windows.
- It also decides RH when its coordinate compresses height, so that every top is attained (Li/Cayley coordinates, or a compressing multiplier `H = z/log(2 − z²)`).
- A thin family in a height-uniform coordinate sees only attained tops. It is worth exactly AAL, or NAT, and needs a separate ZAL producer.

"AAL is the attainment gap of a coordinate, not of the zeros." Compression removes the gap at a resolution cost: to see a zero `(δ, γ)` one needs primes up to `γ^{(2/δ)w_max/w(γ)}` instead of `γ^{2/δ}`.

---

## 6. Models: what AAL does not follow from

### 6.1 Systems that violate AAL

| Model | What it shares with `ζ` | What it lacks | Evidence | What it rules out |
|---|---|---|---|---|
| `overRegularZeta μ ν γ`, `1/3 < μ < 1/2`, `0 < ν < 3μ − 1`, `γ ≠ 0` | positive continuous prime and integer densities; Euler product; `N(x) − ρx − C → 0`; simple pole; `ζ_B(σ + it) → 1` on vertical lines | discreteness, integer norms, functional equation | zeros right of `½` exactly `(1 − μ) ± iγ` (`overRegularZeta_right_zeroSet_eq_pair`, `ArithmeticPositiveDuality/BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean:80`); weak recurrence fails (`not_weakRecurrence_overRegularZeta`, `:198`) [L] | positivity, an Euler product and a count better than `ℤ`'s do not give AAL. The model has ZAL (no zeros at large height at all) |
| discrete Beurling one-off | discrete primes `p_k = e^{t_k}` within one of the continuous density; Euler product `ζ_c e^{sΛ(s)+R(s)}` | integer norms; continuation to `Re s = ½`, since it blows up at `s = ½` | `ArithmeticPositiveDuality/ADiscreteBeurlingOneOff.lean`: the docstring states zeros on `Re s > ½` exactly at `(1 − μ) ± iγ`, but `discreteContinuation_eq_zero_iff` and `tendsto_norm_discreteContinuation_half` are absent from the source [S] | discreteness of the primes does not give AAL. A discrete one-off reaching the line must carry Riemann's correction `−½W(x/2)` in its prime count |
| discrete Beurling systems of Broucke–Debruyne–Vindas | positive discrete Euler product | functional equation, integer norms | recorded on the `pnt-error-single-finite-oscillation` card [C] | — |
| `ξ_β = (s − β)(s − 1 + β)ξ` | functional equation, order one, reality, Gamma factor | Dirichlet series, Euler product | card `3-formalized/functional-equation-is-blind-to-rh.md`; the balance constraint `abs_density_ge_of_count_ne` (`RHTower/BeurlingRationalFactorBalance.lean:52`) [L] | functional equation, order and reality do not give AAL |
| symmetric rational zero relocation of `ξ` | functional equation, critical-line reality, `1 + O(1/|t|)` vertical asymptotics, an implanted `ρ₀` | Bohr almost periodicity and every Dirichlet-series representation on every line `Re s > 1` | `zeroRelocation_destroys_vertical_bohr_and_LSeries` (`ArithmeticPositiveDuality/SymmetricRationalZeroRelocationBohrObstruction.lean`) [L] | a proof must use the Dirichlet series on `Re s > 1` |
| heat deformation `H_t`, `0 < t < Λ` (the interval is nonempty iff RH fails, by closedness of the real-rooted times [C]) | the Fourier structure of `Ξ`, functional equation, reality | Dirichlet series | for `t > 0` no nonreal zero of small imaginary part at large height (`eventually_riemannHeat_ne_zero`, `RHTower/KiKimLeeLargeHeightReality.lean:334`) [L]; failure of AAL exactly on `(0, Λ)` (big-picture card, row 1120) [D] | a proof of AAL must not be stable under the heat flow at small positive time |
| positive Fejér configurations and exact-spline model divisors | positive weights, Riemann–von Mangoldt counts with `O(log T)` remainder | arithmetic | non-attained tops have lag excursion sets of finite measure (`WeilLagFunctionDensityZeroExcursion`); killed routes "coupling-growth" [L] | counts and densities do not decide attainment |
| Selberg zeta functions with exceptional eigenvalues `λ < ¼` | Euler product over primitive geodesics, functional equation, prime geodesic theorem | integer norms (norms `e^{ℓ}`), Dirichlet series over `ℕ` | finitely many real zeros in `(½, 1)`; in the cocompact case all other nontrivial zeros lie on `Re s = ½` [C] | the natural finite top layers are spectral and real |

### 6.2 Systems that violate RH and satisfy AAL

| Model | Evidence | What it shows |
|---|---|---|
| bounded-count model: `a(n) = 1 − 1_{2∣n} + 4·1_{8∣n}`, `ζ(s)P(2^{−s})`, `P(X) = 1 − X + 4X³`; nonnegative, integral, multiplicative, `−3 ≤ N(x) − x ≤ 0` | zeros with `½ < Re s < 1` along a full vertical progression (`exists_cubicFactor_eq_zero`, `cubicFactor_shift`, `RigidArithmeticOfCuts/ABoundedCountWithANewZero.lean`) [L] | It is a ZAL fake, not an AAL fake. A finite modification of Euler factors adds periodic zero columns and keeps AAL [D] |
| golden fake | returns exactly and fails the count (`goldenL_deepZero`, `ArithmeticAuxiliaryDynamics/TheBatteryOfAuxiliaryDynamics.lean:65`) [L] | transport is free on fakes |
| Dirichlet polynomials; periodic data | vertically recurrent (`isVerticallyRecurrent_dirichletPoly`), zeros in a strip absent or infinite (`zero_free_or_infinite_of_recurrent`, `ArithmeticInnerFunctionTheory/TheZeroOneLawOfRecurrence.lean:106`); zeros recur in every window, effectively (`exists_zero_in_every_window`, `RigidArithmeticOfCuts/ZerosOfADirichletPolynomialRecurEffectively.lean:151`) [L] | AAL is automatic for every finite truncation; any failure for `ζ` sits in the infinite tail |
| Dirichlet series absolutely convergent on `Re s > σ` | Bohr almost periodic there (`isStripAlmostPeriodic_LSeries`) [L], hence vertically recurrent and subject to the zero–one law [D] | multiplying by such a factor preserves AAL above `σ`: its zeros there are absent or infinite right of every abscissa, and a union of two such zero sets is again absent or infinite. So a finite top layer can only come from a factor that is not absolutely convergent at its abscissa [D] |
| Davenport–Heilbronn function | `≫ T` zeros in every substrip of `(½, 1)` [C] | functional equation plus a Dirichlet series without Euler product gives generic, abundant off-line zeros |
| function-field zeta functions | zeros periodic modulo `2πi/log q`, so AAL is automatic [C/D] | over `𝔽_q`, RH is ZAL (free, finite spectrum) plus one bounded progression (Stepanov along `qⁿ`) (big-picture card, row 1095) |
| near-count model: odd primes plus extra norm-3 and norm-4 labels | positive generators, integer norms, `|N(x) − x| ≪ (log x)²`; zeta `ζ(s)/((1 + 2^{−s})(1 − 3^{−s}))` with the same zeros as `ζ` on `Re s > 0` (`PositiveNearCount.zetaSeriesC_eq_continuation`, `SumProductArithmeticOfTheLogarithm/PositiveNearCountEuler.lean`) [L] | count distance alone does not measure the insertion of right zeros |

### 6.3 What the models force on a proof

1. **The Dirichlet series over `ℕ` must enter.** `ξ_β`, zero relocation and `H_t` violate AAL and lack it [L/D].
2. **Integer norms, or the exact functional equation in its Beurling-rigid form, must enter.** Continuous and discrete Beurling one-offs violate AAL with positive Euler products. The functional equation separates them: a zero `L¹` defect of the functional equation forces the rational primes, and a prime mismatch at `N` costs defect `> 1/(400N²)` (`beurling_intNorm_eq_round_and_primes_of_zero_defect`, `critical_line_defect_gt_of_not_prime_equiv`, `beurlingSystem_rigidity_of_small_critical_line_defect`, `beurling_primes_of_critical_line_defect`) [L].
3. **The infinite tail must enter.** Every finite truncation satisfies AAL [L]. TAPO locates the failure in the tail: the zeros of `ζ` are the zeros of `ζM_y` at every cut [L].
4. **No AAL-violating system with integer norms and nonnegative generators is known.** Whether one exists is open (RAC README §9.3). It is the decisive test case (§8.5).

---

## 7. Routes tried, and the exact obstruction for each

| Attempt | Obstruction | Evidence |
|---|---|---|
| Commutative Hecke `C*`-squares on truncated resonant Eisenstein states | Poisson-positive on the whole half-plane `Re u < 0`, on-line and off-line alike | `resonantHeckeStarSquare_re_nonneg` (`ArithmeticCorrespondencePositivity/ResonantHeckePoissonMixtureAndDispersion.lean`) [L] |
| Landau's theorem with a floor that makes the top wave nonnegative | the floor `Ce^{αu}` creates a real pole that shields `β ± iγ_j`; squaring creates a real pole at `2β` with residue `2Σ|c_j|²` | `tendsto_sub_mul_laplace_expBufferedWave`, `tendsto_sub_mul_laplace_conjSymWave_sq` (`ConjugateDiagonalGeometry/OscillatorySquareConjugateDiagonalRealPole.lean`) [L] |
| exact linear ledgers and cut identities | holomorphic at every zero: `ζ(ρ) = 0` cancels the top terms (zeros are the power-law kernel of the cut system) | `hasSum_ledgerMode_eq_zero`, `forall_hasSum_abelStep_mod_zero_iff` [L] |
| exact nonlinear identities (Selberg) | `ζ(A² − A′) = ζ″` holds for every analytic function in the form `f(A² − A′) = f″` | `riemannZeta_mul_selberg` [L] |
| diagonal decay of the jets | at the real centre `s = 2` the raw moments tend to `+1` while the diagonal tends to `0` | `mangoldt_at_two_has_nonzero_moment_and_vanishing_diagonal` [L] |
| positivity of `Λ` in the jets | absolute values restore the real-axis radius `σ − 1`, smaller than the detection radius `σ − β` | `pnt-error-single-finite-oscillation` card [D] |
| quantitative phase recurrence for the jets | the horizontal gain is strictly below `β − β₁ < ½`, sharply; a parameter bound, not a recurrence time | `horizontal_jet_gain_lt_half`, `tendsto_nat_mul_log_shift_ratio` (`ZeroConfigurationGeometry/TheHorizontalJetGainHasASharpGapCeiling.lean`) [L] |
| strong recurrence (Bagchi) at a zero | self-returns about a zero have density zero; strong recurrence at `z₀` holds iff `ζ(z₀) ≠ 0` | `exists_zetaSelfReturn_density_zero` (`RHTower/ZetaStrongRecurrenceReceiver.lean:302`), `exists_zetaDiscStronglyRecurrentOn_iff_ne_zero` [L] |
| typical-height or density-one estimates | returns at a right zero are tail-bad at every cut and rare; nonvanishing targets recur at positive density, targets with a zero only at tail-bad heights | `exists_returns_tailBad_and_rare`, `tail_recurrence_dichotomy` (`TailArithmeticOfThePrimeOrbit/TheRecurrenceDichotomyOfTheTail.lean:96`) [L] |
| recurrence of the primes | primes of any finite family recur at positive density, but at a zero a positive proportion of prime returns are not returns of `ζ`; the limits of translates contain the twin `ζ(2s)/ζ(s)` | `exists_primeReturn_not_zetaReturn` (`RigidArithmeticOfCuts/TheTailFailsAtAZero.lean:159`), `exists_tendsto_translate_twin` [L] |
| slow returns on discs crossing `Re s = ½` | `sup |ζ(s + iτ)| ≥ cτ^b` on every disc of radius `R > 5/2` about `3 + iγ`, while head returns have `N < 1024(log τ)⁴(log log τ)²`; the all-right-zero hypothesis on such a disc is RH | `exists_rpow_le_of_norm_le_on_disc`, `length_lt_of_isHeadReturn`, `slowReturnHypothesis_iff_riemannHypothesis` [L] |
| the random Euler model | it is almost surely zero-free on `Re s > ½`, so it assigns probability `0` to every return that copies a zero | TAPO README [D] |
| almost periodicity of `ζ` in the strip | only Besicovitch almost periodicity holds there; it does not localize | big-picture card, C1068 [D] |
| repulsion technology (Deuring–Heilbronn, Landau–Page) | it isolates exceptional zeros, so it argues towards ¬AAL. Twisting maps a complex isolated top to a real double zero of the positive family `ζ²(s)ζ(s+iγ)ζ(s−iγ)` | big-picture card, rows 1096–1097 [D/C] |
| extremal position (maximal angle, Hermite–Biehler, Stieltjes sign) | the real quadratic `w² − 2w + 2` satisfies the whole inequality with off-axis zeros | `norm_model_conj_lt` (`RigidArithmeticOfCuts/TheExtremalLawHasAModel.lean`) [L] |
| count distance | the near-count model has `ζ`'s zeros; the bounded-count model keeps AAL | §6.2 [L] |
| short-interval variance (Gallagher) | converts a second-moment bound into a prime variance bound; it does not prove one | card [D] |
| Bohr's prime inequality | needs uniform boundedness on a strip, which the `log t` bound does not supply | card [D] |
| prime-pair upper sieve | bounds unsigned pair counts, not the signed, factorially normalized correlation | `RHTower.Sieve.sum_card_primePair_le`, card [D] |
| integrable functional-equation defect rigidity | needs a positive Beurling spectrum for the deflated zeta; none is constructed | `beurlingSystem_rigidity_of_small_critical_line_defect` [L], card [D] |
| integer shifts `ΔF(s) = F(s) − F(s+1)` | the prime kernel of `Δ^kF` is `(1 − 1/n)^k`: polynomial scales replace exponential ones, but a centred cancellation estimate is missing | card [D] |
| multiplicative bilinear splitting | the phase separates exactly; no new oscillatory interaction | card [D] |
| thin samplings of the lag | telescoping circle quadrature gives discrete measures with vanishing moments and arbitrarily small weights: thin samplings are blind on the zero side | big-picture card, CANNOT-515 [L/D] |

The retired card `5-failed/aal-asymptotic-abscissa-law.md` records the first four rows, with six positive survivors, all formalized. Its insight is that a proof must use both the Euler product and the exact functional equation, and must pass outside commutative Hecke `C*`-expectations.

---

## 8. The faces of the missing input

Each face below names the exact open statement, what is proved at its boundary, why it is hard, and what counts as progress.

### 8.1 Tail and transport (B89, B96)

**Open statement.** For each right zero `ρ = β + iγ` there are `σ₀ ∈ [½, β)` and head returns, of arbitrarily large length `N` and height `τ`, with `|ζ(s + iτ)| ≤ N^{transportExponent β (3 − σ₀)}` on `closedBall(3 + iγ, 3 − σ₀)`. In tail form: at such heights the Euler tail cancels the head on a disc about the zero, at every cut.

**Proved at the boundary** [L]:
- head returns of length `N` exist with `1 ≤ τ ≤ (7N)^N` (`exists_isHeadReturn_le`);
- at large `τ`, `N < 1024(log τ)⁴(log log τ)²`, so the allowed bound `N^A` is polylogarithmic in `τ`;
- on `Re s ≥ 2` the translate is within `4/N` of `ζ`, and three circles give `|ζ(s + iτ) − ζ(s)| ≤ (4/N)^{1−t}(2M)^t`;
- the exponent `transportExponent β R = (1 − t)/(2t)`, `t = log((R + 3 − β)/2)/log R`, is positive for `3 − β < R ≤ 31/10`;
- `ζ = E_y·ζM_y`, and the head never vanishes on `Re s > 0`;
- the head is frozen below its resolution: `|log|E_y(s + iv)| − log|E_y(s)|| ≤ 2|v|(log y + log 4)` on `Re s ≥ 1`;
- every return at a zero is tail-bad at every cut, with tolerance `m/4` independent of the cut, and such returns have density zero;
- below the Kronecker scale the tail is Gaussian conditionally on the head through order `k`, while `log max A + k log Z ≪ log T` (`TheTailDecouplesFromTheHead`, `TheConditionalMomentsOfTheTail`, `TheHeadIsFrozenAtItsResolution`).

**Why it is hard.**
- On the left part of the disc, alignment forces `|E_N(s + iτ)| ≈ |E_N(s)| ≈ exp(Σ_{p≤N} p^{−σ₀})`. Heuristically this is `exp(cN^{1−σ₀}/log N)` [H].
- So the tail must cancel the head by that factor. The cancellation reproduces a zero (Rouché), and the random model assigns it probability `0` [D].
- With `N` polylogarithmic in `τ` the head lies in the Kronecker range. The cancellation is a statement about the primes in `(N, τ^{O(1)})`, which is the dark range.
- By the transport count, producing such returns is producing zeros (§5.2).

**Progress would be:**
- a slow return at one right zero in a stated class of configurations, or its exclusion in a stated class (TAPO's success criterion);
- a conditional tail law at one moment past the Kronecker scale.

The obstacles summary's first step belongs here: write the off-diagonal of `∫_T^{2T}|R|²|ζM_y|²` at resonator length `≍ T` as a sum over shifted smooth × prime products, and compute what the finite oscillation contributes to it.

### 8.2 The lag (Γ69)

**Open statement.** For every `a > 0` there is `M` with `Φ(L) ≤ Me^{aL}` for all `L ≥ 0` outside a set of Abel density zero.

**Prime form** [D, from `weilLagFunction_eq_prime_side`]. Write `x = e^L`. Then

`Φ(log x) = −x^{−½}·(x∫_x^∞ (ψ(u) − u)u^{−2} du + log 2π) + O(x^{−5/2})`.

So the input is a one-sided lower bound for the tail-averaged prime error: `x∫_x^∞(ψ(u) − u)u^{−2} du ≥ −M_a x^{½+a}` outside a set of log-scales of Abel density zero.

**Proved at the boundary** [L]:
- under RH, `Φ` is bounded above (`weilLagFunctionReal_le_of_riemannHypothesis`);
- RH ⇔ `Φ` bounded above ⇔ `Φ` bounded below (`WeilLagFunctionOneSided`);
- RH ⇔ ZAL ∧ a finite-measure (or upper-density-zero) excursion set (`riemannHypothesis_iff_zerosApproachLine_and_finiteMeasure_lagExcursion`, `riemannHypothesis_iff_zerosApproachLine_and_upperDensityZero_lagExcursion`);
- an attained top forces excursions of positive upper density, with the explicit constant of §4.1 item 14;
- abstract positive configurations with a non-attained top have excursion sets of finite measure.

**Why it is hard.** It is a one-sided bound at power precision `x^{½+a}` on a set of scales of density one. No unconditional method gives one-sided power-precision prime bounds on any set of scales of positive density [C/D]. Over `𝔽_q` the single-base form is Stepanov's argument along `qⁿ`, and it needs a Frobenius (big-picture card, addendum 4) [D].

**Open sub-question** (obstacles summary, first step 2). Is the lag hypothesis weaker than a zero-free strip for `ζ`? That is, does a zero at `β` force `Φ > e^{(β−½−ε)L}` on a set of infinite measure only for attained tops, or for every `β`? The abstract theory says only for attained tops [L]. Whether `ζ`'s configuration can have non-attained tops with density-zero excursions is open.

### 8.3 Jets and long correlations (the Turán route)

**Open statement.** Under ¬AAL, at a rightmost zero `ρ` of multiplicity `m`, the normalized long-shift correlation `Re Σ_{n≠j} a_{k,n}\overline{a_{k,j}} − 2Re Σ_{h≤⌊r^k⌋} Σ_n a_{k,n}\overline{a_{k,n+h}}` tends to `m²` [L]. The argument uses only an attained rightmost zero (card) [D]. A theorem showing that the limit is not `m²`, using the arithmetic of `Λ` at large shifts, contradicts the finite top layer, or any attained top.

**Proved at the boundary** [L]:
- the corrected and raw moment limits;
- diagonal decay;
- decay of exponentially many short shifts (`tendsto_normalizedMangoldtShortShiftCorrelations_zero`, `ZeroConfigurationGeometry/VonMangoldtShortShiftCorrelationsVanish.lean`);
- decay of proper prime powers for `d < σ − ½` (`tendsto_normalized_higher_prime_power_jets`);
- recovery of the multiplicity of a rightmost zero of an entire function by high jets (`tendsto_logDeriv_jets_at_rightmost_zero`, `ZeroConfigurationGeometry/HighDerivativesRecoverARightmostZero.lean`);
- decay of finite-pole jets far above their heights (`FinitePoleJetsDecayAwayFromTheirHeight`);
- Turán's second main theorem in separation-free form: some `ν ∈ [M+1, M+N]` has `|Σ z_i^ν| ≥ 1/(2eN(6(N+1)(M+2N+2))^N)` (`exists_norm_powerSum_ge`, `HTGeometry/PowerSumTuranLowerBound.lean:646`).

**Why it is hard.**
- The coefficient mass concentrates at `log n ≈ k/β`. The removed shifts reach `h ≈ n^{β log r}` with `β log r < 2β log(β + ½) < 1`, so what survives is a correlation at shifts beyond a fixed power of `n` [D].
- An asymptotic for `Σ Λ(n)Λ(n+h)` weighted in this way is a binary prime problem of Hardy–Littlewood type, behind the parity barrier [C/D].
- Any argument must fail at the real centre `s = 2`, where the same arithmetic sequence has a nonzero moment with vanishing diagonal [L].
- The low-height jet argument needs only an attained rightmost zero. A contradiction must use the high-height zero-free region quantitatively (`not_asymptoticAbscissaLaw_has_high_jet_bounds`); qualitative recurrence `∀k ∃t` does not relate `k` to `t` (card).

### 8.4 Integers and carries (Γ81)

**Open statement.** Show that `ψ = log lcm(1, …, ⌊x⌋)` cannot satisfy the two-prime dilation collapse of E4. Equivalently, show that `⌊x⌋` cannot coexist with a finite oscillation (SPL's "carry contradiction for finite oscillations").

**Proved at the boundary** [L]:
- the carry `⌊kx⌋ − k⌊x⌋ = ⌊k{x}⌋` is never constant for `k ≥ 2` (`not_exists_constant_carry`, `carry_eq_sum_shifts`);
- bounded multiplicities admit no Frobenius (`not_hasFrobenius_of_bounded`);
- the exact cut identity determines `λ` on every integer (`eq_liouville_of_floorSum`);
- every exact ledger is blind at every zero.

**Two observations on this face** [D]:
- **The coefficients are real.** `P_k` are polynomials in `b^Θ` and `cos(ω log b)`, so integrality of `lcm` does not pass to `Σ_k P_k ψ(x/b^k)`. What passes is the discrete support of the jumps (at `b^k m`, `m` a prime power) and their sizes `P_k log q`.
- **Chebyshev's identity is blind.** `Σ_{n≤x}Λ(n)⌊x/n⌋ = log⌊x⌋!` sees the top layer only through `Σ_{d≤x}(x/d)^ρ ≈ x^ρζ(ρ) + x/(1 − ρ)`, and `ζ(ρ) = 0` removes it. Any carry argument must use inexact information, such as the distribution of the fractional parts `{x/n}`, at precision `x^{Θ−η}`.

No Lean module attacks this face.

### 8.5 Count distance and integer Beurling systems

**Open statement.** Does a Beurling system with integer norms and nonnegative integer generators exist whose zeta has a finite top layer right of its count exponent? What is the smallest count distance that carries one? If every such system with count error below a stated threshold satisfies AAL, then AAL for `ζ` follows by taking `ℤ` itself.

**Proved at the boundary** [L]:
- count error `o(log n)` forces the rational primes (`primes_of_sublogarithmic_count_error`, `SumProductArithmeticOfTheLogarithm/LogarithmicCountFloor.lean:106`);
- every nonclassical system has `|D(n)| ≥ c log n` infinitely often;
- the count-distance trichotomy (`count_distance_trichotomy`);
- adding generators creates no zero right of the count exponent (`numerator_eq_zero_iff`): only deletion can, with exchange exponent `≥ β`;
- integer systems with count `x + O(x^σ)` exist for every `σ > 0` (`exists_abs_exchangeCount_sub_le`);
- the near-count and bounded-count models of §6.2.

**What a construction must avoid** [D]:
- multiplication by a Dirichlet series absolutely convergent at the abscissa of the new zeros, since such a factor preserves AAL (§6.2);
- a continuous prime density, since it lacks integer norms.

### 8.6 Recurrence and the inner field

**Open statement.** Zero-disc weak recurrence: for each right zero, cofinal return shifts on discs about it.

**Proved at the boundary** [L]:
- the zero–one law for vertically recurrent entire functions;
- `ζ` returns at positive lower density to the zero-erased cofactor `g` of a disc about any point, the orbit erasing the local zero divisor (`exists_zeta_recurrence_modulo_zeros`, `RHTower/ZetaRecurrenceAtEveryPointModuloItsZeros.lean:220`);
- the Dirichlet heads approximate `g` uniformly in the cutoff;
- the self-target is returned to only on a density-zero set;
- either infinitely many right zeros exist or the inner field tends to `0` on vertical lines (`infinite_or_tendsto_innerField`);
- RH ⇔ inner-field decay ∧ zero-disc weak recurrence.

**Why it is hard.** AAL asks whether the orbit ever restores the zero at large height, near `Re ρ`. By the transport count this is again the existence of zeros (§5.2).

---

## 9. Open problems

| # | Problem | Strength | Where it stands |
|---|---|---|---|
| OP1 | **AAL.** `Θ∞ = Θ` | sub-RH; implies no strip | open; the forms of §2 are equivalent |
| OP2 | **B13.** FOL ⇒ RH: `ζ` cannot have finitely many, and at least one, off-line zeros | strictly weaker than OP1 | the world has Lindelöf, quasi-RH, `κ < ∞`, inner field `→ 0`, and `ψ(x) − x = x^Θ T(log x) + O(x^{Θ−η})` with remainder exponent down to `Θ₂ + ε` [L] |
| OP3 | **ZAL ⇒ RH**, equivalently ZAL ⇒ AAL | strictly weaker than OP1; stronger than OP2 | in the world ZAL ∧ ¬RH the top is attained and `Θ∞ = ½` [L] |
| OP4 | **B89.** Existence or exclusion of slow aligned returns at a right zero, in a stated class | equivalent to OP1 if done for all right zeros | §8.1 |
| OP5 | **B96.** A conditional law of the Euler tail at one moment past the Kronecker scale; the off-diagonal of the resonator mean of `|ζM_y|²` as shifted smooth × prime counts | not implied by RH; a binary prime problem [D] | the conditional Gaussian law holds below the Kronecker scale [L] |
| OP6 | Is the lag hypothesis of §8.2 weaker than a zero-free strip for `ζ`? | decides whether the lag face is a door | the abstract theory sees only attained tops [L] |
| OP7 | The long-shift correlation of the normalized jets at a rightmost zero: prove a limit other than `m²` using the high-height zero-free region | proves AAL; proves NAT if it uses only attainment | §8.3 |
| OP8 | An integer-norm positive Beurling system with a finite top layer, or a proof that count distance below a stated threshold forbids one | decisive test case | §8.5 |
| OP9 | The carry contradiction: can `N(x) = ⌊x⌋` coexist with a finite oscillation of `ψ`? | equivalent to OP1 if decided | no module; §8.4 |
| OP10 | A one-sided bound for `Φ` along one geometric progression `b^m`: Stepanov over `ℤ` | proves NAT | Π wall; no analogue of `x ↦ x^q` over `ℤ` [D] |
| OP11 | Which property of `Q` (order `½`, log-concavity of coefficients, functional equation) contradicts the extremal position at a maximal-angle zero? | RH-level, adjacent | RAC README §9.6; the model `w² − 2w + 2` [L] |
| OP12 | Does any sub-power sampling mesh of the integer lags decide RH without ZAL? | adjacent | big-picture card, addendum 7 [D] |

**How the faces compare** [D]:
- **Transport (OP4) and recurrence (§8.6) reformulate the problem.** The transport count makes "produce a return" and "produce a zero" the same task.
- **The lag (OP6, OP10) and the jets (OP7) carry content.** They are attainment-based and so aim at NAT. Each would need an unconditional input at power precision: a one-sided prime bound on density-one scales, or a long-shift correlation of `Λ`.
- **Count distance (OP8) and carries (OP9) test integrality directly.** Integrality is the property that every AAL-violating Euler-product model lacks (§6.3). No tool reaches them.
- **No face has a tool that reaches it.**

---

## 10. Constraints on a proof

### 10.1 A proof of AAL cannot

1. use only positivity of the prime measure, an Euler product and a smooth integer count (`overRegularZeta`) [L];
2. use only discreteness of the primes with an Euler product (discrete one-off) [S];
3. use only the functional equation, order one, reality and vertical asymptotics (`ξ_β`, zero relocation) [L];
4. be stable under the heat flow at small positive time (`H_t`, `0 < t < Λ`) [D];
5. rest on an exact identity, linear or nonlinear in `Λ` [L];
6. rest on diagonal decay of moments (real-centre calibration at `s = 2`) [L];
7. rest on typical-height or density-one information: the finite top is invisible to it, and returns at zeros are density zero and tail-bad [L];
8. rest on large-height receivers alone: they read `Θ∞` [L/D];
9. rest on an unconditional estimate of `ψ`, `M` or `L` at Vinogradov–Korobov precision: ¬AAL lives at precision `x^Θ` [D];
10. rest on the random Euler model, which gives zeros probability zero [D];
11. rest on repulsion technology, which isolates exceptional zeros [D/C];
12. rest on recurrence of the primes or on transport alone: the primes always recur, at a zero the tail fails, and transport is free on the golden fake [L];
13. rest on size bounds on discs crossing `Re s = ½`: they force `|ζ| ≥ cτ^b` [L];
14. rest on extremal-position inequalities alone [L];
15. rest on count distance alone: the near-count model has `ζ`'s zeros [L].

### 10.2 A proof of AAL must

1. **Couple heights.** It must transfer information from one zero at bounded height to infinitely many heights. AAL compares `Θ`, which sees bounded heights, with `Θ∞`, which does not [D].
2. **Use the Dirichlet series over `ℕ`**, with an input that fails on continuous and discrete Beurling one-offs: integer norms `N(x) = ⌊x⌋`, or the exact functional equation through its Beurling rigidity [L/D].
3. **Be an inequality or a non-identity.** If it argues by contradiction, it may assume the whole world of §4, including the qRH-level regularity at large heights and the rigid finite oscillation [L].
4. **Say whether it proves NAT or exactly AAL.** If it is attainment-based, it must identify the real point at which the attained top is detected [L].
5. **State its scales** against the Kronecker scale `log T`, the head resolution `1/log y`, the Vinogradov–Korobov length and the diagonal range (TAPO criteria).
6. **Fail on each model of §6.1**, through a named property.

### 10.3 Checklist for a proposed argument

| Question | Required answer |
|---|---|
| Which Lean statement does it prove? | `RHTower.AsymptoticAbscissaLaw`, a form of §2, or the hypothesis of a producer of §5 for the actual `ζ` |
| Does it prove NAT, AAL, or only a weaker milestone (B13, ZAL ⇒ RH)? | stated explicitly |
| Where does the unique property of `ζ` enter? | a named step that fails for `overRegularZeta`, the discrete one-off, `ξ_β`, zero relocation and `H_t` |
| Is any step an exact identity? | if so, it is labelled a boundary condition and not the inequality |
| At what precision does the contradiction occur? | at or below `x^Θ`, with the unconditional source of that precision named |
| How does information at height `γ₀` reach large heights? | through the explicit formula, dilations, recurrence, or another named mechanism |
| Is it heat-stable? | it must not be |
| Does it confuse attained and non-attained tops, or `h = 0` with `h > 0`? | no |

---

## 11. Milestones

| Level | Milestone | Status |
|---|---|---|
| M1 | **B13**: FOL ⇒ RH | open |
| M2 | **ZAL ⇒ RH** | open |
| M3 | AAL for a stated class of top layers, for example a single simple conjugate pair, or a gap `Θ − Θ₂` above a stated bound | open; suggested scope, not a corpus target |
| M4 | a slow return at one right zero in a stated class, or its exclusion (TAPO success criterion) | open |
| M5 | a conditional tail law at one moment past the Kronecker scale (TAPO success criterion; B96) | open |
| M6 | OP6 decided: whether the lag form is weaker than a strip | open |
| M7 | OP8 decided: an integer-norm positive one-off, or a count-distance threshold that forbids it | open |
| M8 | the discrete Beurling one-off formalized (`discreteContinuation_eq_zero_iff`, `tendsto_norm_discreteContinuation_half`) | [S] |

---

## 12. Lean entry points

**Definitions:**
- `RHTower.AsymptoticAbscissaLaw`, `RHTower.ZerosApproachLine`, `RHTower.FiniteOffLine`, `RHTower.AttainedTop`;
- `RHTower.ZetaWeaklyRecurrent`, `RHTower.ZetaZeroDiscWeaklyRecurrent`;
- `GaloisForLFunctions.ZeroConfigurationGeometry.{zetaAsymptoticAbscissa, zetaSecondAbscissa, PrimeErrorIsFiniteOscillation, finiteOscillation, dilationSetOp, mainTermFactor, singleBaseTopAnnihilator, finiteRightBlaschke}`;
- `GaloisForLFunctions.ArithmeticAuxiliaryDynamics.{IsPhaseReturn, IsHeadReturn, TranslatesBoundedOn, transportExponent}`;
- `RHTower.weilLagFunctionReal`, `RHTower.eulerTail`, `RHTower.eulerDiscTailBadSet`, `RHTower.zetaReturnSet`.

**Starting points for a contradiction:**
- `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`, for the configuration;
- `exists_primeErrorFiniteOscillation_of_lt_gap`, for the expansion at any `η < Θ − Θ₂`;
- `not_asymptoticAbscissaLaw_has_persistent_low_jets` and its siblings, for the jets;
- `not_asymptoticAbscissaLaw_has_high_jet_bounds`, for the high zero-free region;
- `exists_large_value_of_finite_on_disc`, for large values along aligned shifts.

**Target templates** (statements only; each must close with standard axioms):

```lean
theorem asymptoticAbscissaLaw_holds : RHTower.AsymptoticAbscissaLaw
theorem not_primeErrorIsFiniteOscillation :
    ¬ GaloisForLFunctions.ZeroConfigurationGeometry.PrimeErrorIsFiniteOscillation
-- milestones
theorem riemannHypothesis_of_finiteOffLine : RHTower.FiniteOffLine → RiemannHypothesis
theorem riemannHypothesis_of_zerosApproachLine_only : RHTower.ZerosApproachLine → RiemannHypothesis
```

A producer's hypothesis must be proved for `ζ`. It may not appear as a binder, a structure field or a `Prop` interface.

**Programme folders** where the work lives:
- `ZeroConfigurationGeometry/` (the world ¬AAL);
- `ArithmeticAuxiliaryDynamics/` (transport);
- `TailArithmeticOfThePrimeOrbit/` (tail);
- `RigidArithmeticOfCuts/` (cuts, carries, models);
- `SumProductArithmeticOfTheLogarithm/` (count distance, carries);
- `ArithmeticPositiveDuality/` (Beurling countermodels);
- `RHTower/` (definitions, lag and JAS producers);
- `ArithmeticKreinLangerTheory/` (towers, cones, collapse atlas).

---

## 13. Reading notes on earlier reports

| Report | Reading | Corpus |
|---|---|---|
| fable.md §5 | "under ¬AAL a zero of maximal angle is attained…" | The maximal angle is attained under ¬RH in every world (`exists_zero_of_maximal_angle`). It is not a ¬AAL signature, and the extremal law has the model `w² − 2w + 2` |
| obstacles-summary.md §3, "Fakes" row | the bounded-count model listed as a fake for AAL | It satisfies AAL (zeros on a full vertical progression). The AAL fakes are those of §6.1 |
| obstacles-summary.md §3, lag form | "`ψ(x) − x` bounded below by `−M_a x^{½+a}` off a set of finite log measure" | The exact prime form is the tail-averaged error `x∫_x^∞(ψ(u) − u)u^{−2} du` (§8.2) |
| obstacles-summary.md §3, integer form | "integrality and carries of `lcm` at the dilated points" | The dilation coefficients are real, so integrality of `lcm` does not pass to the combination (§8.4) |
| several reports | "AAL producers" | Most are attainment producers and prove NAT, which is strictly stronger than AAL; the transport producers are exactly AAL (§5) |
| obstacles-summary.md §1.1 | "`qRH ∨ AAL` is a theorem [D]" | It is a direct corollary of `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` |
| rh-big-picture-interpretation.md, addendum 2 | "AAL … is RH-strength" | No theorem makes AAL RH-equivalent. AAL is implied by RH and implies no zero-free region; its difficulty relative to quasi-RH is unknown |
| fable.md §1.2, item 8 | "`Λ ≥ 0` (Rodgers–Tao) is in Lean (`newmanConstant_nonneg`)" | `newmanConstant` is an infimum over the nonnegative heat axis (`realRootedTimes` requires `0 ≤ t`), so its nonnegativity is definitional. Rodgers–Tao is not formalized here [C] |
| astra.md §2.2 | the lag receiver "excludes an attained top, stronger than merely excluding a finite isolated top" | Consistent with §5.1 |

---

## 14. Classical background [C]

- **Landau's theorem.** A Dirichlet integral of a nonnegative measure is singular at the real point of its abscissa. This is the mechanism of every attainment producer and of every Landau-type killed route.
- **Ω-theorems.** `ψ(x) − x = Ω±(x^{Θ−ε})`. An attained top gives `Ω±(x^Θ)`. Littlewood: `Ω±(√x log log log x)`.
- **Bohr–Landau.** `N(σ, T) = o(T log T)` for `σ > ½`. Zero-density estimates count zeros up to height `T` and are blind to a bounded finite set.
- **Value distribution and recurrence.** Bohr–Jessen value distribution and Borchsenius–Jessen `a`-points (positive density for `a ≠ 0`). Voronin universality for nonvanishing targets. Bagchi: strong recurrence ⇔ RH.
- **Zero-free regions.** de la Vallée Poussin and Korobov–Vinogradov; the error `x exp(−c(log x)^{3/5}(log log x)^{−1/5})`.
- **Siegel zeros and Deuring–Heilbronn repulsion.** The classical scenario of an isolated exceptional zero.
- **Selberg zeta functions.** Exceptional eigenvalues `λ < ¼` give finitely many real zeros in `(½, 1)`.
- **Davenport–Heilbronn.** Voronin: `≫ T` zeros in every substrip `½ < σ₁ < Re s < σ₂ < 1`.
- **The heat flow.** Ki–Kim–Lee: `H_t` has finitely many nonreal zeros for `t > 0`. Rodgers–Tao: `Λ ≥ 0`. The real-rooted times form a closed half-line. The Lean constant `RHTower.newmanConstant` is the infimum over `t ≥ 0` only (`RHTower/DeBruijnNewmanConstant.lean:31`), so `newmanConstant_nonneg` is definitional and is not Rodgers–Tao.
- **Numerical verification.** Platt–Trudgian: RH holds up to height `3·10¹²`.
- **Function fields.** Weil, with Stepanov's elementary proof; zeros periodic modulo `2πi/log q`.
