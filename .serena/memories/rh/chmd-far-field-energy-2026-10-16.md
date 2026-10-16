# CHMD: negative Doob energy localizes; no cusp escape above the threshold (2026-10-16)

RH goal ACTIVE. Contribution 3 of this lane (after MUST-1541/1542 polar transfer + resolvent and
MUST-1543/1544 explicit generator + threshold Weyl sequence). STATUS rows MUST-1545/1546.

## Result (all unconditional, Lean, standard axioms)
Modules (namespace `RHTower.CHMDPolar`): `RHTower/CHMDPrimeWindowTail` (34 decls),
`RHTower/CHMDFarFieldEnergy` (41 decls). Wired into `RHTower.lean`; `lake build --old` clean; final
plain `lake env lean` clean on both; `#print axioms` on all 75: propext/Classical.choice/Quot.sound only.

1. **Window tail bound** (`exists_primeTail_bound`, `primeTail_le_cosh`): the prime shifts
   `Σ Λ(n)n^{-1/2}(Θ(x±log n)·1_{|x±log n|>R})` are `≤ A·r^{⌊R⌋}(e^{x/2}+e^{−x/2})`, `r = e^{−7/2}`,
   via corpus `prime_shell_bound` (Chebyshev prefix 34√Y) grouped in log shells; `primeCross + primeTail = primeKernelSum`.
2. **Two-sided bound** `exists_primeKernelSum_two_sided`: `|primeKernelSum y − cosh(y/2)| ≤ B` (from the
   harmonic identity + corpus gamma-source bound).
3. **Window jump inequality** `window_jump_lower`: for indicators α,β∈{0,1}, δ>0:
   `(a−b)² ≥ βa² + αb² − δ⁻¹(αa²+βb²) − δ(a²+b²)`.
4. **Termwise integration** `tsum_integral_shiftPair` (symmetric prime shift series against an integrable
   weight of bounded support; uses `riemannKernelReal_shift_le`, `summable_atom_div_sq`).
5. **Compact-test confinement** `sourceEnergy_compactLift_window_lower`:
   `E(v) ≥ −(K₁ + (1+δ)B/cosh(R/2) + δ)‖v‖²_μ − (B + δ⁻¹(1+B) + δB)·nearMass_R(v)`.
6. **Completed-graph theorem** `exists_window_energy_bound`: ∀ε>0 ∃R≥0 ∃C≥0 ∀p∈SourceGraph,
   `−ε‖p.fst‖² − C·nearMass R p ≤ sourceEnergy p`, with `nearMass R p = ∫1_{|x|≤R}p² dμ = ‖nearMul R (sourceMap p)‖²`
   (`nearMul` = `lpBoundedMulCLM` of the indicator), extended from `compactTests` by `Dense.induction`.
7. `exists_farField_energy_bound`: `nearMass R p = 0 ⇒ E(p) ≥ −ε‖p‖²`.
8. **Confinement above threshold** `exists_window_mass_resolvent`: ∀μ>1/2 ∃R θ>0 η>0: unit w with
   `‖Rw − μw‖ ≤ η` has `‖nearMul R (Rw)‖² ≥ θ`; `eventually_window_mass_of_weyl`: any unit sequence with
   `‖Re_n − μe_n‖ → 0` (μ>1/2) eventually has `‖nearMul R (e_n)‖ ≥ θ > 0`.
9. **Sharpness** `threshold_escape_sequence`: the corpus normalized cusp escape `source (normalized n)` is a
   unit family with `‖Re_n − ½e_n‖ → 0` and `nearMul R₀ e_n = 0` eventually for EVERY R₀
   (`nearMul_escape_eq_zero`). So 1/2 is exactly the escape level.

## Why it moves the frontier
Negative Doob energy (= off-line zeros under the CHMD dictionary: RH ⟺ R ≤ 1/2 on even primitives)
cannot come from the cusp: all negativity is confined to a compact window up to an ε‖·‖² loss.
Spectral reading: for the compression to the far field the resolvent is ≤ 1/2 + ε; any spectrum of R
above 1/2 is produced by vectors with definite mass in a fixed window; essential spectrum ⊆ [0, 1/2]
would follow from local compactness of `nearMul R ∘ R` (open: needs a log lower bound for the Lévy
symbol `ψ(ξ) = 2∫ω(1−cos ξt)dt ≥ c log(2+|ξ|) − C`, not in corpus; corpus has only
`EvenSectorWeightGrowth.abs_gammaBracket_le_log`, an upper bound).

## Next
Local compactness ⇒ σ_ess(R) ⊆ [0,1/2] ⇒ eigenvalues of R in (1/2,1] are isolated finite-multiplicity =
nonreal Xi orbits (Birman–Schwinger count). Needs: (a) Lévy-symbol log lower bound; (b) Rellich on the
Doob graph via `SuzukiHlogCompactEmbedding.totallyBounded_of_centralSupport_of_uniformFourierTail` or
`CCMGeneralFourierWeightCompactEmbedding`.

## Lean traps met
`s.filter (fun n => …Real.log n…)` infers `n : ℝ` — annotate `fun n : ℕ`; `norm_toLp_sq` needs
`show ‖hf.toLp f‖^2 = _` then `rw`; `Measurable.tsum` is stuck unless the goal is stated as
`Measurable fun x => ∑' n, …` (use `show`); `integral_add h1 h2` fails when `h1 : Integrable (f + g)` is
a Pi-sum — give the `have` an explicit lambda type; `pow_le_pow_left` → `pow_le_pow_left₀`;
`HasCompactSupport (fun x => v x^2 * Θ x)` via `hvc.mul_right` + `funext` rewrite; `push_neg` deprecated → `rw [not_lt]`.
Card: docs/drafts/pipeline/3-formalized/chmd-far-field-energy-localization-2026-10-16.md.
