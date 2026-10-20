import GaloisForLFunctions.BiScaleUncertainty.CircleCosineDesigns

/-!
# The power-grid moment theorem

Let `q ≥ 2`, `ℓ = log q`, `F(z) = γ(‖z‖/ℓ)` the folded archimedean symbol on `ℝ/2πℤ`, and let
`J ⊆ ℕ` be any set of exponents. Put

`V_q(J) = inf { ∫ F dν : ν a probability measure on the circle, ∫ cos(jz) dν = 0 for j ∈ J, j ≥ 1 }`.

**Theorem** (`blindSymbolSlackOn_exponentNodes_iff`). The exact blind symbol slack on the powers
`{q^j : j ∈ J, j ≥ 1}` is `−V_q(J)`, with or without zero pole mass. Blind slack on any set of
powers of one integer is a moment problem for the folded symbol on the circle.

* **Lower bound.** The phase measure of a blind combination (`exists_phase_measure`), normalized,
  is admissible, and `γ` dominates its fold.
* **Upper bound.** Given an admissible `ν` and `K`, a design with mass one, exactly vanishing
  cosine moments at the exponents of `J` up to `K`, and value within `ε` of `∫ F dν` exists
  (`exists_design_exact`). Cosine/sine modulations at the folded radii of its angles, under an
  envelope whose correlation vanishes beyond `(K+1)ℓ`, are blind at every `q^j`, `j ∈ J`: up to `K`
  by the design, beyond `K` by the envelope. The envelope energy is `O(1/K)`.

The three closed-form cases are recovered as solutions of the moment problem: `V_q(ℕ) = m_q`
(uniform measure), `V_q(ℕ \ {d}) = m_q − |φ_d|`, `V_q({j : d ∤ j}) = min F_d`.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. The moment problem -/

/-- The powers `q^j`, `j ∈ J`, `j ≥ 1`. -/
abbrev exponentNodes (q : ℕ) (J : Set ℕ) : Set ℕ := {n | ∃ j ∈ J, 1 ≤ j ∧ n = q ^ j}

/-- Admissible values: `∫ F dν` over probability measures with `∫ cos(jz) dν = 0`, `j ∈ J`. -/
def powerMomentSet (q : ℕ) (J : Set ℕ) : Set ℝ :=
  {x | ∃ ν : Measure (AddCircle (2 * π)), IsProbabilityMeasure ν ∧
    (∀ j ∈ J, 1 ≤ j → ∫ z, circleCos j z ∂ν = 0) ∧ x = ∫ z, foldedSymbol (Real.log q) z ∂ν}

/-- The circle moment value `V_q(J)`. -/
def powerMomentValue (q : ℕ) (J : Set ℕ) : ℝ := sInf (powerMomentSet q J)

theorem foldedSymbol_ge (ℓ : ℝ) (z : AddCircle (2 * π)) :
    EF.gammaBracket 0 ≤ foldedSymbol ℓ z :=
  gammaBracket_le_of_abs_le (by rw [abs_zero]; exact abs_nonneg _)

theorem powerMomentSet_bddBelow (q : ℕ) (J : Set ℕ) :
    BddBelow (powerMomentSet q J) := by
  refine ⟨EF.gammaBracket 0, ?_⟩
  rintro x ⟨ν, hν, -, rfl⟩
  have := integral_mono (integrable_const (EF.gammaBracket 0))
    ((BoundedContinuousFunction.mkOfCompact ⟨_, continuous_foldedSymbol (Real.log q)⟩).integrable ν)
    (foldedSymbol_ge _)
  simpa using this

/-! ### 2. Designs as combinations -/

/-- Cosine/sine modulations at the folded radii `‖θ‖/ℓ` of the angles of a design. -/
def designCombination {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ℓ : ℝ)
    (D : List (ℝ × ℝ)) : WeilTestFn →₀ ℝ :=
  (D.map fun a => Finsupp.single (cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / ℓ)) a.1 +
    Finsupp.single (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / ℓ)) a.1).sum

theorem designCombination_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ℓ : ℝ) {D : List (ℝ × ℝ)} (hD : ∀ a ∈ D, 0 ≤ a.1) (g : WeilTestFn) :
    0 ≤ designCombination hf hfc ℓ D g := by
  classical
  induction D with
  | nil => simp [designCombination]
  | cons a D ih =>
    have ha := hD a (List.mem_cons_self ..)
    have ht := ih fun b hb => hD b (List.mem_cons_of_mem _ hb)
    simp only [designCombination, List.map_cons, List.sum_cons, Finsupp.add_apply] at ht ⊢
    rw [Finsupp.single_apply, Finsupp.single_apply]
    have h1 : 0 ≤ (if cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / ℓ) = g then a.1 else 0) := by
      split_ifs <;> simp [ha]
    have h2 : 0 ≤ (if sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / ℓ) = g then a.1 else 0) := by
      split_ifs <;> simp [ha]
    linarith

theorem linearCombination_designCombination (φ : WeilTestFn → ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ℓ : ℝ) (D : List (ℝ × ℝ)) :
    linearCombination ℝ φ (designCombination hf hfc ℓ D) =
      (D.map fun a => a.1 * (φ (cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / ℓ)) +
        φ (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / ℓ)))).sum := by
  induction D with
  | nil => simp [designCombination]
  | cons a D ih =>
    simp only [designCombination, List.map_cons, List.sum_cons, map_add,
      linearCombination_single, smul_eq_mul] at ih ⊢
    rw [ih]; ring

/-- The symbol of one cosine/sine pair is `h(0) γ(ω)` up to the envelope energy. -/
theorem archOnly_cos_add_sin_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℝ) :
    (weilArchRe (EF.weilTest (cosTest hf hfc ω).1 (cosTest hf hfc ω).1) -
        (weilPoleTerm (EF.weilTest (cosTest hf hfc ω).1 (cosTest hf hfc ω).1)).re) +
      (weilArchRe (EF.weilTest (sinTest hf hfc ω).1 (sinTest hf hfc ω).1) -
        (weilPoleTerm (EF.weilTest (sinTest hf hfc ω).1 (sinTest hf hfc ω).1)).re) ≤
      autocorr f 0 * EF.gammaBracket ω + biScaleLevyEnergy f := by
  have h1 := archOnly_realTest (contDiff_cosineSource hf ω)
    (hfc.mul_right (f' := fun u => Real.cos (ω * u)))
  have h2 := archOnly_realTest (contDiff_sineSource hf ω)
    (hfc.mul_right (f' := fun u => Real.sin (ω * u)))
  have h3 := biScaleLevyEnergy_cosine_sine_eq hf hfc ω
  have h4 : EF.gammaBracket 0 * autocorr (cosineSource f ω) 0 +
      EF.gammaBracket 0 * autocorr (sineSource f ω) 0 = EF.gammaBracket 0 * autocorr f 0 := by
    rw [← mul_add, autocorr_cos_add_sin_zero hf hfc]
  have h5 : autocorr f 0 * archFrequencyCost ω =
      autocorr f 0 * EF.gammaBracket ω - EF.gammaBracket 0 * autocorr f 0 := by
    rw [archFrequencyCost_eq_gammaBracket_sub_zero]; ring
  have h6 := (le_abs_self _).trans (abs_archEnvelopeError_le hf hfc ω)
  simp only [cosTest, sinTest] at *
  linarith

theorem massTerm_cos_add_sin {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (ω : ℝ) : (∫ x, ‖(cosTest hf hfc ω).1 x‖ ^ 2) + ∫ x, ‖(sinTest hf hfc ω).1 x‖ ^ 2 =
      autocorr f 0 := by
  simp only [cosTest, sinTest, realTest, integral_norm_sq_ofReal]
  exact autocorr_cos_add_sin_zero hf hfc ω

theorem nodeArchOnly_eq_linearCombination (c : WeilTestFn →₀ ℝ) :
    nodeArchOnly c = linearCombination ℝ (fun f : WeilTestFn =>
      weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re) c := by
  rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    Finsupp.sum, ← Finset.sum_sub_distrib]
  simp only [smul_eq_mul, mul_sub]

/-! ### 3. The theorem -/

/-- **Lower bound.** A nonnegative combination blind at every `q^j`, `j ∈ J`, has archimedean
part without the pole at least `V_q(J)` times its mass. -/
theorem powerMomentValue_mul_massOf_le {q : ℕ} (hq : 2 ≤ q) (J : Set ℕ) (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (hb : BlindOn (exponentNodes q J) c) :
    powerMomentValue q J * massOf c ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨G, hG⟩ : ∃ G, G = combinationSpectralDensity c := ⟨_, rfl⟩
  have hGc : Continuous G := hG ▸ continuous_combinationSpectralDensity c
  have hG0 : ∀ r, 0 ≤ G r := hG ▸ combinationSpectralDensity_nonneg hc
  have hGi : Integrable G := hG ▸ integrable_combinationSpectralDensity c
  have hGm : ∫ r, G r = 2 * π * massOf c := hG ▸ integral_combinationSpectralDensity c
  have hGa : ∫ r, G r * EF.gammaBracket r = 2 * π * nodeArchOnly c :=
    hG ▸ integral_combinationSpectralDensity_mul_gammaBracket c
  have iγ : Integrable fun r => G r * EF.gammaBracket r :=
    hG ▸ integrable_combinationSpectralDensity_mul_gammaBracket c
  have hpi : 0 < 2 * π := by positivity
  obtain ⟨ν, hνf, hνF, hνP⟩ := exists_phase_measure hGc hG0 hGi (Real.log q)
  -- the fold
  have hGf : Integrable fun r => G r * foldedSymbol (Real.log q) (phase (Real.log q) r) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log q)).continuousOn
    exact integrable_mul_bounded hGi ((continuous_foldedSymbol _).comp (continuous_phase _))
      (C := C) fun r => by rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have hfold := integral_mono hGf iγ fun r =>
    mul_le_mul_of_nonneg_left (foldedSymbol_phase_le hℓ r) (hG0 r)
  rw [hνP _ (continuous_foldedSymbol _) (foldedSymbol_neg _), hGa] at hfold
  -- the total mass of `ν`
  have hmass : (ν Set.univ).toReal = ∫ r, G r := by
    have h1 := hνP (fun _ => 1) continuous_const (fun _ => rfl)
    simp only [mul_one, integral_const, smul_eq_mul] at h1
    rw [h1, measureReal_def]
  rcases eq_or_lt_of_le (integral_nonneg hG0 : 0 ≤ ∫ r, G r) with h0 | hpos
  · -- zero mass: everything vanishes
    have hGz : G =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hG0 hGi).mp h0.symm
    have hA : ∫ r, G r * EF.gammaBracket r = 0 := by
      have : (fun r => G r * EF.gammaBracket r) =ᵐ[volume] fun _ => (0 : ℝ) :=
        hGz.mono fun r hr => by
          show G r * EF.gammaBracket r = 0
          rw [Pi.zero_apply] at hr; rw [hr, zero_mul]
      rw [integral_congr_ae this, integral_zero]
    have hm : massOf c = 0 := by nlinarith
    have ha : nodeArchOnly c = 0 := by nlinarith
    rw [hm, ha, mul_zero]
  · -- normalize
    set t : ENNReal := (ν Set.univ)⁻¹ with ht
    have hνne : ν Set.univ ≠ 0 := by
      intro h; rw [h, ENNReal.toReal_zero] at hmass; linarith
    have hνtop : ν Set.univ ≠ ⊤ := measure_ne_top _ _
    haveI : IsProbabilityMeasure (t • ν) := by
      constructor
      rw [Measure.smul_apply, smul_eq_mul, ht, ENNReal.inv_mul_cancel hνne hνtop]
    have htr : t.toReal = (∫ r, G r)⁻¹ := by rw [ht, ENNReal.toReal_inv, hmass]
    have hmem : (∫ r, G r)⁻¹ * ∫ z, foldedSymbol (Real.log q) z ∂ν ∈ powerMomentSet q J := by
      refine ⟨t • ν, inferInstance, fun j hj hj1 => ?_, ?_⟩
      · rw [integral_smul_measure, smul_eq_mul]
        have hc0 : ∫ z, circleCos j z ∂ν = 0 := by
          have hre : ∫ z, circleCos j z ∂ν = (∫ z, fourier (j : ℤ) z ∂ν).re := by
            have hint : Integrable (fun z => fourier (j : ℤ) z) ν :=
              (BoundedContinuousFunction.mkOfCompact (fourier (j : ℤ))).integrable ν
            rw [show (∫ z, fourier (j : ℤ) z ∂ν).re = ∫ z, (fourier (j : ℤ) z).re ∂ν from
              (integral_re hint).symm]
            rfl
          rw [hre, hνF, Complex.ofReal_re]
          have hqj : 2 ≤ q ^ j := le_trans hq (Nat.le_self_pow (by omega) q)
          rw [show ((j : ℤ) : ℝ) = (j : ℝ) by push_cast; rfl, hG,
            integral_combinationSpectralDensity_mul_cos_pow c hq hj1, hb _ ⟨j, hj, hj1, rfl⟩,
            mul_zero]
        rw [hc0, mul_zero]
      · rw [integral_smul_measure, smul_eq_mul, htr]
    have hle := csInf_le (powerMomentSet_bddBelow q J) hmem
    rw [← powerMomentValue] at hle
    have h2 : powerMomentValue q J * (∫ r, G r) ≤ ∫ z, foldedSymbol (Real.log q) z ∂ν := by
      have := mul_le_mul_of_nonneg_left hle hpos.le
      rwa [mul_comm, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    rw [hGm] at h2
    nlinarith

/-- **Upper bound.** Every admissible probability measure is approached in value by nonnegative
combinations blind at every `q^j`, `j ∈ J`. -/
theorem exists_blindOn_exponentNodes_archOnly_le {q : ℕ} (hq : 2 ≤ q) (J : Set ℕ)
    (ν : Measure (AddCircle (2 * π))) [IsProbabilityMeasure ν]
    (hν : ∀ j ∈ J, 1 ≤ j → ∫ z, circleCos j z ∂ν = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (exponentNodes q J) c ∧ 0 < massOf c ∧
      nodeArchOnly c ≤ ((∫ z, foldedSymbol (Real.log q) z ∂ν) + ε) * massOf c := by
  classical
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨Mb, hMb, hinc⟩ := exists_autocorr_increment_linear_bound contDiff_pairBump
    hasCompactSupport_pairBump
  have hb0 := autocorr_pairBump_zero_pos
  have hK0 : 0 ≤ Mb * archWeightFirstMoment := mul_nonneg hMb archWeightFirstMoment_nonneg
  set E : ℝ := Mb * archWeightFirstMoment / (4 * Real.log q * autocorr pairBump 0) with hE
  have hE0 : 0 ≤ E := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * E / ε)
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hEK : E / (K + 1) ≤ ε / 2 := by
    rw [div_le_iff₀ hK1]
    rw [div_lt_iff₀ hε] at hK
    nlinarith
  -- an exact design for the exponents up to `K`
  set JK : Finset ℕ := (Finset.Icc 1 K).filter (· ∈ J) with hJK
  obtain ⟨D, hD0, hD1, hDm, hDv⟩ := exists_design_exact ν (K := K) JK
    (fun j hj => by
      have := (Finset.mem_filter.mp hj).1
      exact ⟨(Finset.mem_Icc.mp this).1, (Finset.mem_Icc.mp this).2⟩)
    (fun j hj => hν j (Finset.mem_filter.mp hj).2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1)
    (continuous_foldedSymbol (Real.log q)) (half_pos hε)
  -- the envelope
  set δ : ℝ := 1 / (4 * (K + 1) * Real.log q) with hδdef
  have hδ : 0 < δ := by positivity
  have hf := contDiff_compressedBump δ
  have hfc := hasCompactSupport_compressedBump hδ
  have hf0 : autocorr (compressedBump δ) 0 = 4 * (K + 1) * Real.log q * autocorr pairBump 0 := by
    rw [autocorr_compressedBump_zero hδ, hδdef]; field_simp
  have hJ : biScaleLevyEnergy (compressedBump δ) ≤ Mb * archWeightFirstMoment :=
    biScaleLevyEnergy_sourceRescale_le contDiff_pairBump hasCompactSupport_pairBump hinc hδ
  set c := designCombination hf hfc (Real.log q) D with hcdef
  have hcos_rad : ∀ (θ : ℝ) (t : ℝ),
      Real.cos (‖(θ : AddCircle (2 * π))‖ / Real.log q * (t * Real.log q)) =
        Real.cos (t * ‖(θ : AddCircle (2 * π))‖) := by
    intro θ t; congr 1; field_simp
  refine ⟨c, designCombination_nonneg hf hfc _ hD0, ?_, ?_, ?_⟩
  · -- blindness
    rintro ⟨n, hn2⟩ ⟨j, hj, hj1, rfl⟩
    rw [nodeVector_apply_eq_linearCombination, linearCombination_designCombination]
    change (D.map fun a => a.1 * (logValue (cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
      Real.log q)).1 (q ^ j) + logValue (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
      Real.log q)).1 (q ^ j))).sum = 0
    have hlog : Real.log ((q ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log q := by
      rw [Nat.cast_pow, Real.log_pow]
    have e : ∀ a : ℝ × ℝ, a.1 * (logValue (cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
        Real.log q)).1 (q ^ j) + logValue (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
        Real.log q)).1 (q ^ j)) =
        2 * autocorr (compressedBump δ) ((j : ℝ) * Real.log q) / Real.sqrt ((q ^ j : ℕ) : ℝ) *
          (a.1 * Real.cos (j * a.2)) := by
      intro a
      simp only [cosTest, sinTest, logValue_realTest]
      have h := autocorr_cosineSource_add_sineSource hf.continuous hfc
        (‖(a.2 : AddCircle (2 * π))‖ / Real.log q) (Real.log ((q ^ j : ℕ) : ℝ))
      rw [hlog, hcos_rad, ← circleCos_eq_cos_norm, circleCos_coe] at h
      rw [hlog]
      linear_combination (2 * a.1 / Real.sqrt ((q ^ j : ℕ) : ℝ)) * h
    simp only [e]
    rw [List.sum_map_mul_left]
    by_cases hjK : j ≤ K
    · have hjJK : j ∈ JK := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj1, hjK⟩, hj⟩
      have := hDm j hjJK
      rw [designMoment] at this
      rw [this, mul_zero]
    · have hfar : 1 / (5 * δ) < |(j : ℝ) * Real.log q| := by
        rw [abs_of_nonneg (by positivity), hδdef]
        have : (K : ℝ) + 1 ≤ j := by exact_mod_cast (show K + 1 ≤ j by omega)
        rw [show 1 / (5 * (1 / (4 * ((K : ℝ) + 1) * Real.log q))) =
          4 / 5 * ((K : ℝ) + 1) * Real.log q by field_simp]
        nlinarith
      rw [autocorr_compressedBump_eq_zero hδ hfar]
      simp
  · -- mass
    rw [massOf_eq_linearCombination, linearCombination_designCombination]
    have e : ∀ a : ℝ × ℝ, a.1 * ((∫ x, ‖(cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
        Real.log q)).1 x‖ ^ 2) + ∫ x, ‖(sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
        Real.log q)).1 x‖ ^ 2) = autocorr (compressedBump δ) 0 * a.1 := by
      intro a
      linear_combination a.1 * massTerm_cos_add_sin hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
        Real.log q)
    simp only [e]
    rw [List.sum_map_mul_left, ← designMass, hD1, mul_one, hf0]
    positivity
  · -- symbol
    have hmass : massOf c = autocorr (compressedBump δ) 0 := by
      rw [massOf_eq_linearCombination, linearCombination_designCombination]
      have e : ∀ a : ℝ × ℝ, a.1 * ((∫ x, ‖(cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
          Real.log q)).1 x‖ ^ 2) + ∫ x, ‖(sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
          Real.log q)).1 x‖ ^ 2) = autocorr (compressedBump δ) 0 * a.1 := by
        intro a
        linear_combination a.1 * massTerm_cos_add_sin hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
          Real.log q)
      simp only [e]
      rw [List.sum_map_mul_left, ← designMass, hD1, mul_one]
    have harch : nodeArchOnly c ≤ autocorr (compressedBump δ) 0 *
        designValue (foldedSymbol (Real.log q)) D + biScaleLevyEnergy (compressedBump δ) := by
      rw [nodeArchOnly_eq_linearCombination, linearCombination_designCombination]
      have hterm : ∀ a ∈ D, a.1 * ((weilArchRe (EF.weilTest (cosTest hf hfc
            (‖(a.2 : AddCircle (2 * π))‖ / Real.log q)).1 (cosTest hf hfc
            (‖(a.2 : AddCircle (2 * π))‖ / Real.log q)).1) -
            (weilPoleTerm (EF.weilTest (cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
            Real.log q)).1 (cosTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / Real.log q)).1)).re) +
          (weilArchRe (EF.weilTest (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / Real.log q)).1
            (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ / Real.log q)).1) -
            (weilPoleTerm (EF.weilTest (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
            Real.log q)).1 (sinTest hf hfc (‖(a.2 : AddCircle (2 * π))‖ /
            Real.log q)).1)).re)) ≤
          autocorr (compressedBump δ) 0 * (a.1 * foldedSymbol (Real.log q) (a.2 : AddCircle (2 * π))) +
            a.1 * biScaleLevyEnergy (compressedBump δ) := by
        intro a ha
        have h := archOnly_cos_add_sin_le hf hfc (‖(a.2 : AddCircle (2 * π))‖ / Real.log q)
        have hF : EF.gammaBracket (‖(a.2 : AddCircle (2 * π))‖ / Real.log q) =
            foldedSymbol (Real.log q) (a.2 : AddCircle (2 * π)) := rfl
        rw [hF] at h
        have := mul_le_mul_of_nonneg_left h (hD0 a ha)
        nlinarith
      calc
        _ ≤ (D.map fun a => autocorr (compressedBump δ) 0 *
              (a.1 * foldedSymbol (Real.log q) (a.2 : AddCircle (2 * π))) +
              a.1 * biScaleLevyEnergy (compressedBump δ)).sum :=
          List.sum_le_sum fun a ha => hterm a ha
        _ = _ := by
          rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_right, ← designMass,
            hD1, one_mul, designValue]
    rw [hmass]
    have hv := mul_le_mul_of_nonneg_left hDv (autocorr_zero_nonneg (compressedBump δ))
    have hJK : biScaleLevyEnergy (compressedBump δ) ≤ ε / 2 * autocorr (compressedBump δ) 0 := by
      calc biScaleLevyEnergy (compressedBump δ) ≤ Mb * archWeightFirstMoment := hJ
        _ = E / (K + 1) * autocorr (compressedBump δ) 0 := by rw [hf0, hE]; field_simp
        _ ≤ ε / 2 * autocorr (compressedBump δ) 0 :=
          mul_le_mul_of_nonneg_right hEK (autocorr_zero_nonneg _)
    nlinarith

/-- **The power-grid moment theorem.** The exact blind symbol slack on `{q^j : j ∈ J, j ≥ 1}` is
`−V_q(J)`. -/
theorem blindSymbolSlackOn_exponentNodes_iff {q : ℕ} (hq : 2 ≤ q) (J : Set ℕ) (M : ℝ) :
    BlindSymbolSlackOn (exponentNodes q J) M ↔ -powerMomentValue q J ≤ M := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    set g : ℝ := -powerMomentValue q J - M with hg
    have hgpos : 0 < g := by linarith
    -- an admissible measure with value below `V + g/3`
    have hne : (powerMomentSet q J).Nonempty := by
      refine ⟨_, AddCircle.haarAddCircle, inferInstance, fun j _ hj1 => ?_, rfl⟩
      have hre : ∫ z, circleCos j z ∂AddCircle.haarAddCircle =
          (∫ z, fourier (j : ℤ) z ∂(AddCircle.haarAddCircle (T := 2 * π))).re := by
        have hint : Integrable (fun z => fourier (j : ℤ) z) (AddCircle.haarAddCircle (T := 2 * π)) :=
          (BoundedContinuousFunction.mkOfCompact (fourier (j : ℤ))).integrable _
        rw [show (∫ z, fourier (j : ℤ) z ∂(AddCircle.haarAddCircle (T := 2 * π))).re =
          ∫ z, (fourier (j : ℤ) z).re ∂(AddCircle.haarAddCircle (T := 2 * π)) from
            (integral_re hint).symm]
        rfl
      rw [hre, integral_fourier_haar, if_neg (by omega)]; simp
    obtain ⟨x, ⟨ν, hν, hνc, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne
      (show sInf (powerMomentSet q J) < powerMomentValue q J + g / 3 by
        rw [← powerMomentValue]; linarith)
    obtain ⟨c, hc, hb, hm, ha⟩ := exists_blindOn_exponentNodes_archOnly_le hq J ν hνc
      (show 0 < g / 3 by positivity)
    have h1 := h c hc hb
    have : (∫ z, foldedSymbol (Real.log q) z ∂ν + g / 3 + M) * massOf c < 0 := by
      have : ∫ z, foldedSymbol (Real.log q) z ∂ν + g / 3 + M < 0 := by linarith
      nlinarith
    nlinarith
  · intro h c hc hb
    have := powerMomentValue_mul_massOf_le hq J c hc hb
    have := massOf_nonneg hc
    nlinarith

/-- The moment theorem holds verbatim on zero-pole combinations. -/
theorem zeroPoleBlindSymbolSlackOn_exponentNodes_iff {q : ℕ} (hq : 2 ≤ q) (J : Set ℕ) (M : ℝ) :
    ZeroPoleBlindSymbolSlackOn (exponentNodes q J) M ↔ -powerMomentValue q J ≤ M := by
  have hsub : exponentNodes q J ⊆ powerNodes q := by
    rintro n ⟨j, -, hj, hn⟩
    exact ⟨j, hj, hn⟩
  rw [zeroPoleBlindSymbolSlackOn_iff_of_gapped ((gappedNodeSet_powers hq).mono hsub),
    blindSymbolSlackOn_exponentNodes_iff hq]

/-! ### 4. Three solved moment problems -/

theorem exponentNodes_univ (q : ℕ) : exponentNodes q Set.univ = powerNodes q := by
  ext n; simp

/-- All powers: `V_q(ℕ) = m_q`, attained by the uniform measure. -/
theorem powerMomentValue_univ {q : ℕ} (hq : 2 ≤ q) :
    powerMomentValue q Set.univ = symbolPeriodMean q := by
  have h1 := (blindSymbolSlackOn_exponentNodes_iff hq Set.univ (-symbolPeriodMean q)).mp
    (by rw [exponentNodes_univ]; exact blindSymbolSlackOn_powers hq)
  have h2 := (blindSymbolSlackOn_powers_iff hq (-powerMomentValue q Set.univ)).mp
    (by rw [← exponentNodes_univ]; exact (blindSymbolSlackOn_exponentNodes_iff hq _ _).mpr le_rfl)
  linarith

/-- All powers but `q^d`: `V_q(ℕ \ {d}) = m_q − |φ_d|`. -/
theorem powerMomentValue_punctured {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    powerMomentValue q {j | j ≠ d} = symbolPeriodMean q - |foldedCosineCoefficient q d| := by
  have hset : exponentNodes q {j | j ≠ d} = puncturedPowerNodes q d := by
    ext n; constructor
    · rintro ⟨j, hj, hj1, hn⟩; exact ⟨j, hj1, hj, hn⟩
    · rintro ⟨j, hj1, hj, hn⟩; exact ⟨j, hj, hj1, hn⟩
  have h1 := (blindSymbolSlackOn_exponentNodes_iff hq _ _).mp
    (by rw [hset]; exact blindSymbolSlackOn_punctured hq hd)
  have h2 := (blindSymbolSlackOn_punctured_iff hq hd _).mp
    (by rw [← hset]; exact (blindSymbolSlackOn_exponentNodes_iff hq _ _).mpr le_rfl)
  linarith

/-- The exponents off the multiples of `d`: `V_q({j : d ∤ j}) = min F_d`. -/
theorem powerMomentValue_offMultiples {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    powerMomentValue q {j | ¬ d ∣ j} = orbitMinimum q d := by
  have hset : exponentNodes q {j | ¬ d ∣ j} = offMultipleNodes q d := by
    ext n; constructor
    · rintro ⟨j, hj, hj1, hn⟩; exact ⟨j, hj1, hj, hn⟩
    · rintro ⟨j, hj1, hj, hn⟩; exact ⟨j, hj, hj1, hn⟩
  have h1 := (blindSymbolSlackOn_exponentNodes_iff hq _ _).mp
    (by rw [hset]; exact blindSymbolSlackOn_offMultiples hq hd)
  have h2 := (blindSymbolSlackOn_offMultiples_iff hq hd _).mp
    (by rw [← hset]; exact (blindSymbolSlackOn_exponentNodes_iff hq _ _).mpr le_rfl)
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
