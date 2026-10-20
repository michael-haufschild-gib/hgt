import GaloisForLFunctions.BiScaleUncertainty.PowerGridMomentTheorem

/-!
# The signed single-integer bathtub

For `q ≥ 2`, `ℓ = log q`, let `m_q = ∫ F` and `φ_j = ∫ F(z) cos(jz) dz/2π` be the mean and the
cosine coefficients of the folded archimedean symbol `F(z) = γ(‖z‖/ℓ)`. No blindness is assumed.

**Theorem** (`nodeArchOnly_ge_signedBathtub`). Every nonnegative combination `c` of Weil tests
satisfies

`A(c) ≥ m_q · mass(c) + Σ_{j ≥ 1} φ_j √(q^j) · v_c(q^j)`,

where `v_c(n)` is the node value at `n`; the sum is finite because node values vanish beyond the
support. The remainder is exactly the fold defect `(1/2π) ∫ G (γ − F∘phase) ≥ 0`
(`nodeArchOnly_sub_signedBathtub_eq`), so equality holds exactly when the spectral density lives
on the fundamental period `[−π/ℓ, π/ℓ]`.

**Mechanism.** The phase measure of a compact combination has only finitely many nonzero Fourier
coefficients, `ν̂(j) = π√(q^j) v_c(q^j)`; Fourier uniqueness on the circle identifies it with the
trigonometric-polynomial density `(∫G + 2 Σ_j ν̂(j) cos(jz)) dz/2π`
(`integral_mul_periodic_eq_of_cos_finite`), and integrating `F` against it gives the right side.

Each power node is priced by the corresponding Fourier coefficient of the folded symbol: blind
combinations recover the exact bathtub `A ≥ m_q · mass`, and the removal law prices one free node
at `|φ_d|`.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ### 1. Finitely many free frequencies -/

/-- **Finitely many free frequencies.** If the cosine moments of a nonnegative density `G` vanish
at every `nℓ` with `n > J₀`, then for every even continuous observable `P` of the phase
`∫ G P(phase) = (∫G) ∫P + 2 Σ_{1 ≤ n ≤ J₀} c_n ∫ P cos(n·)`, `c_n = ∫ G(r) cos(nℓr)`. -/
theorem integral_mul_periodic_eq_of_cos_finite {G : ℝ → ℝ} (hGc : Continuous G)
    (hG0 : ∀ r, 0 ≤ G r) (hGi : Integrable G) {ℓ : ℝ} (J₀ : ℕ)
    (hcos : ∀ n : ℕ, J₀ < n → ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = 0)
    {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) (heven : ∀ z, P (-z) = P z) :
    ∫ r, G r * P (phase ℓ r) = (∫ r, G r) * (∫ z, P z ∂AddCircle.haarAddCircle) +
      2 * ∑ n ∈ Finset.Icc 1 J₀, (∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ))) *
        ∫ z, P z * circleCos n z ∂AddCircle.haarAddCircle := by
  obtain ⟨ν, hνf, hνF, hνP⟩ := exists_phase_measure hGc hG0 hGi ℓ
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n : ℕ => ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) :=
    ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ r, G r := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ integral_nonneg hG0
  have hc0 : c 0 = A := by rw [hc, hA]; simp
  have hcn : ∀ n : ℕ, ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = c n := fun n => by rw [hc]
  rw [← hA]
  simp_rw [hcn]
  -- the cosine moment at an integer multiple
  have hmoment : ∀ m : ℤ, ∫ r, G r * Real.cos (r * ((m : ℝ) * ℓ)) =
      if m.natAbs ≤ J₀ then c m.natAbs else 0 := by
    intro m
    have e : ∀ r : ℝ, Real.cos (r * ((m : ℝ) * ℓ)) = Real.cos (r * ((m.natAbs : ℝ) * ℓ)) := by
      intro r
      rw [Nat.cast_natAbs, Int.cast_abs]
      rcases abs_choice (m : ℝ) with h | h <;> rw [h]
      rw [show r * (-(m : ℝ) * ℓ) = -(r * ((m : ℝ) * ℓ)) by ring, Real.cos_neg]
    simp_rw [e]
    split_ifs with h
    · exact hcn _
    · exact hcos _ (by omega)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * ∑ n ∈ Finset.Icc 1 J₀, |c n| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]; exact mul_nonneg zero_le_two (Finset.sum_nonneg fun n _ => abs_nonneg _)
  obtain ⟨D, hD⟩ : ∃ D : AddCircle (2 * π) → ℝ, D = fun z =>
    A + B + 2 * ∑ n ∈ Finset.Icc 1 J₀, c n * circleCos n z := ⟨_, rfl⟩
  have hcosb : ∀ n z, |circleCos n z| ≤ 1 := fun n z =>
    (Complex.abs_re_le_norm _).trans (((fourier (n : ℤ)).norm_coe_le_norm z).trans
      (fourier_norm _).le)
  have hDc : Continuous D := by
    rw [hD]
    exact continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_circleCos n)))
  have hD0 : ∀ z, 0 ≤ D z := by
    intro z
    have h : -(∑ n ∈ Finset.Icc 1 J₀, |c n|) ≤ ∑ n ∈ Finset.Icc 1 J₀, c n * circleCos n z := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      have := hcosb n z
      have h1 : |c n * circleCos n z| ≤ |c n| := by
        rw [abs_mul]; nlinarith [abs_nonneg (c n), abs_nonneg (circleCos n z)]
      linarith [(abs_le.mp h1).1]
    rw [hD, hB]; linarith
  set gD : AddCircle (2 * π) → NNReal := fun z => (D z).toNNReal with hgD
  have hgDm : Measurable gD := hDc.measurable.real_toNNReal
  have hDi : Integrable D (AddCircle.haarAddCircle (T := 2 * π)) :=
    (BoundedContinuousFunction.mkOfCompact ⟨D, hDc⟩).integrable _
  set ν₁ : Measure (AddCircle (2 * π)) := ν + ENNReal.ofReal B • AddCircle.haarAddCircle with hν₁
  set ν₂ : Measure (AddCircle (2 * π)) :=
    AddCircle.haarAddCircle.withDensity fun z => (gD z : ENNReal) with hν₂
  haveI : IsFiniteMeasure (ENNReal.ofReal B • AddCircle.haarAddCircle (T := 2 * π)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure ν₁ := by rw [hν₁]; infer_instance
  haveI : IsFiniteMeasure ν₂ := isFiniteMeasure_withDensity_ofReal hDi.2
  have hintν₂ : ∀ F : AddCircle (2 * π) → ℂ,
      ∫ z, F z ∂ν₂ = ∫ z, (D z : ℂ) * F z ∂AddCircle.haarAddCircle := fun F => by
    rw [hν₂, integral_withDensity_eq_integral_smul hgDm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hgD, NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ (hD0 z)]
  have hfi : ∀ (m : ℤ) (ρ : Measure (AddCircle (2 * π))) [IsFiniteMeasure ρ],
      Integrable (fun z => fourier m z) ρ := fun m ρ _ =>
    (BoundedContinuousFunction.mkOfCompact (fourier m)).integrable ρ
  have hfci : ∀ (m : ℤ) (n : ℕ), Integrable (fun z => fourier m z * (circleCos n z : ℂ))
      (AddCircle.haarAddCircle (T := 2 * π)) := fun m n =>
    (BoundedContinuousFunction.mkOfCompact ⟨fun z => fourier m z * (circleCos n z : ℂ),
      (fourier m).continuous.mul (Complex.continuous_ofReal.comp (continuous_circleCos n))⟩).integrable _
  have heq : ν₁ = ν₂ := by
    apply GaloisForLFunctions.HTGeometry.addCircle_measure_eq_of_fourier_integral_eq
    intro m
    rw [hν₁, integral_add_measure (hfi m _) (hfi m _), integral_smul_measure, hνF, hmoment,
      integral_fourier_haar, hintν₂, ENNReal.toReal_ofReal hB0]
    have e : ∀ z : AddCircle (2 * π), (D z : ℂ) * fourier m z =
        ((A + B : ℝ) : ℂ) * fourier m z +
          ∑ n ∈ Finset.Icc 1 J₀, ((2 * c n : ℝ) : ℂ) * (fourier m z * (circleCos n z : ℂ)) := by
      intro z
      rw [hD]
      push_cast
      rw [add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    simp_rw [e]
    rw [integral_add ((hfi m _).const_mul _)
      (integrable_finsetSum _ fun n _ => (hfci m n).const_mul _),
      integral_finsetSum _ fun n _ => (hfci m n).const_mul _, integral_const_mul,
      integral_fourier_haar]
    simp_rw [integral_const_mul, integral_fourier_mul_circleCos]
    simp only [Complex.real_smul]
    -- evaluate the sum of indicators
    have hsum : ∑ n ∈ Finset.Icc 1 J₀, ((2 * c n : ℝ) : ℂ) *
        (((if m + (n : ℤ) = 0 then 1 else 0) + (if m - (n : ℤ) = 0 then 1 else 0)) / 2) =
        if m ≠ 0 ∧ m.natAbs ≤ J₀ then ((c m.natAbs : ℝ) : ℂ) else 0 := by
      by_cases hm : m = 0
      · subst hm
        rw [if_neg (by simp)]
        refine Finset.sum_eq_zero fun n hn => ?_
        have hn1 := (Finset.mem_Icc.mp hn).1
        rw [if_neg (by omega), if_neg (by omega)]; simp
      · by_cases hmJ : m.natAbs ≤ J₀
        · rw [if_pos ⟨hm, hmJ⟩, Finset.sum_eq_single m.natAbs]
          · rcases lt_or_gt_of_ne hm with hneg | hpos
            · rw [if_pos (by omega), if_neg (by omega)]; push_cast; ring
            · rw [if_neg (by omega), if_pos (by omega)]; push_cast; ring
          · intro n hn hne
            rw [if_neg (by omega), if_neg (by omega)]; simp
          · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by omega, hmJ⟩) h
        · rw [if_neg (by tauto)]
          refine Finset.sum_eq_zero fun n hn => ?_
          have := (Finset.mem_Icc.mp hn).2
          rw [if_neg (by omega), if_neg (by omega)]; simp
    rw [hsum]
    by_cases hm : m = 0
    · subst hm
      simp only [Int.natAbs_zero, zero_le, if_true, ne_eq, not_true_eq_false, false_and, if_false,
        add_zero]
      rw [hc0]; push_cast; ring
    · by_cases hmJ : m.natAbs ≤ J₀ <;> simp [hm, hmJ]
  -- read off `P`
  have hPi : ∀ (ρ : Measure (AddCircle (2 * π))) [IsFiniteMeasure ρ], Integrable P ρ := fun ρ _ =>
    (BoundedContinuousFunction.mkOfCompact ⟨P, hP⟩).integrable ρ
  have hPeq : ∫ z, P z ∂ν₁ = ∫ z, P z ∂ν₂ := by rw [heq]
  rw [hν₁, integral_add_measure (hPi _) (hPi _), integral_smul_measure,
    ENNReal.toReal_ofReal hB0, smul_eq_mul, ← hνP P hP heven] at hPeq
  have hν₂P : ∫ z, P z ∂ν₂ = ∫ z, D z * P z ∂AddCircle.haarAddCircle := by
    rw [hν₂, integral_withDensity_eq_integral_smul hgDm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hgD, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hD0 z)]
  rw [hν₂P] at hPeq
  have hPci : ∀ n : ℕ, Integrable (fun z => P z * circleCos n z)
      (AddCircle.haarAddCircle (T := 2 * π)) := fun n =>
    (BoundedContinuousFunction.mkOfCompact ⟨fun z => P z * circleCos n z,
      hP.mul (continuous_circleCos n)⟩).integrable _
  have hDP : ∫ z, D z * P z ∂AddCircle.haarAddCircle = (A + B) * ∫ z, P z ∂AddCircle.haarAddCircle +
      2 * ∑ n ∈ Finset.Icc 1 J₀, c n * ∫ z, P z * circleCos n z ∂AddCircle.haarAddCircle := by
    have e : (fun z => D z * P z) = fun z => (A + B) * P z +
        ∑ n ∈ Finset.Icc 1 J₀, (2 * c n) * (P z * circleCos n z) := by
      ext z; rw [hD]; simp only
      rw [add_mul, mul_assoc, Finset.sum_mul, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun n _ => ?_; ring
    rw [e, integral_add ((hPi _).const_mul _)
      (integrable_finsetSum _ fun n _ => (hPci n).const_mul _),
      integral_finsetSum _ fun n _ => (hPci n).const_mul _, integral_const_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul]; ring
  rw [hDP] at hPeq
  linarith

/-! ### 2. The signed bathtub -/

/-- The node value of `c` at `q^n` (zero when `q^n < 2`). -/
def powerNodeValue (c : WeilTestFn →₀ ℝ) (q n : ℕ) : ℝ :=
  if h : 2 ≤ q ^ n then nodeVector c ⟨q ^ n, h⟩ else 0

/-- Node values of a compact combination vanish beyond a finite power of `q`. -/
theorem exists_nodeVector_pow_eq_zero (c : WeilTestFn →₀ ℝ) {q : ℕ} (hq : 2 ≤ q) :
    ∃ J₀ : ℕ, ∀ n : ℕ, J₀ < n → ∀ h : 2 ≤ q ^ n, nodeVector c ⟨q ^ n, h⟩ = 0 := by
  classical
  choose N hN using fun f : WeilTestFn => exists_weilTest_log_eq_zero f
  refine ⟨c.support.sup N, fun n hn h => ?_⟩
  rw [nodeVector_eq, linearCombination_logVector_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun f hf => ?_
  have hle : N f ≤ c.support.sup N := Finset.le_sup hf
  have hlt : N f < q ^ n := by
    have h2 : n < q ^ n := Nat.lt_pow_self (by omega)
    omega
  obtain ⟨h1, h2⟩ := hN f (q ^ n) hlt
  rw [logValue, h1, h2]
  simp

/-- **The signed single-integer bathtub.** For every nonnegative combination whose node values at
`q^n` vanish for `n > J₀`,
`A(c) = m_q mass(c) + Σ_{1 ≤ n ≤ J₀} φ_n √(q^n) v_c(q^n) + (fold defect)`, and the fold defect
`(1/2π) ∫ G (γ − F∘phase)` is nonnegative. -/
theorem nodeArchOnly_sub_signedBathtub_eq {q : ℕ} (hq : 2 ≤ q) (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (J₀ : ℕ)
    (hJ₀ : ∀ n : ℕ, J₀ < n → ∀ h : 2 ≤ q ^ n, nodeVector c ⟨q ^ n, h⟩ = 0) :
    nodeArchOnly c - (symbolPeriodMean q * massOf c +
      ∑ n ∈ Finset.Icc 1 J₀, foldedCosineCoefficient q n * Real.sqrt ((q ^ n : ℕ) : ℝ) *
        powerNodeValue c q n) =
      (1 / (2 * π)) * ∫ r, combinationSpectralDensity c r *
        (EF.gammaBracket r - foldedSymbol (Real.log q) (phase (Real.log q) r)) := by
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
  have hmom : ∀ n : ℕ, 1 ≤ n → ∫ r, G r * Real.cos (r * ((n : ℝ) * Real.log q)) =
      π * Real.sqrt ((q ^ n : ℕ) : ℝ) * powerNodeValue c q n := by
    intro n hn
    have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow (by omega) q)
    rw [hG, integral_combinationSpectralDensity_mul_cos_pow c hq hn, powerNodeValue, dif_pos hqn]
  have hcos : ∀ n : ℕ, J₀ < n → ∫ r, G r * Real.cos (r * ((n : ℝ) * Real.log q)) = 0 := by
    intro n hn
    have hqn : 2 ≤ q ^ n := le_trans hq (Nat.le_self_pow (by omega) q)
    rw [hG, integral_combinationSpectralDensity_mul_cos_pow c hq (by omega), hJ₀ n hn hqn,
      mul_zero]
  have hid := integral_mul_periodic_eq_of_cos_finite hGc hG0 hGi J₀ hcos
    (continuous_foldedSymbol (Real.log q)) (foldedSymbol_neg (Real.log q))
  rw [integral_foldedSymbol hℓ] at hid
  have hGf : Integrable fun r => G r * foldedSymbol (Real.log q) (phase (Real.log q) r) := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_foldedSymbol (Real.log q)).continuousOn
    exact integrable_mul_bounded hGi ((continuous_foldedSymbol _).comp (continuous_phase _))
      (C := C) fun r => by rw [← Real.norm_eq_abs]; exact hC _ (Set.mem_univ _)
  have hsub : ∫ r, G r * (EF.gammaBracket r - foldedSymbol (Real.log q) (phase (Real.log q) r)) =
      (∫ r, G r * EF.gammaBracket r) -
        ∫ r, G r * foldedSymbol (Real.log q) (phase (Real.log q) r) := by
    rw [← integral_sub iγ hGf]
    exact integral_congr_ae (Filter.Eventually.of_forall fun r => by simp only; ring)
  rw [← hG, hsub, hid, hGa, hGm]
  have hsum : ∑ n ∈ Finset.Icc 1 J₀, (∫ r, G r * Real.cos (r * ((n : ℝ) * Real.log q))) *
      ∫ z, foldedSymbol (Real.log q) z * circleCos n z ∂AddCircle.haarAddCircle =
      π * ∑ n ∈ Finset.Icc 1 J₀, foldedCosineCoefficient q n * Real.sqrt ((q ^ n : ℕ) : ℝ) *
        powerNodeValue c q n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hmom n (Finset.mem_Icc.mp hn).1]
    have hφ : ∫ z, foldedSymbol (Real.log q) z * circleCos n z ∂AddCircle.haarAddCircle =
        foldedCosineCoefficient q n := rfl
    rw [hφ]; ring
  rw [hsum]
  have hsm : symbolPeriodMean q =
      Real.log q / π * ∫ v in (0 : ℝ)..π / Real.log q, EF.gammaBracket v := rfl
  rw [← hsm]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The signed bathtub inequality.** -/
theorem nodeArchOnly_ge_signedBathtub {q : ℕ} (hq : 2 ≤ q) (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (J₀ : ℕ)
    (hJ₀ : ∀ n : ℕ, J₀ < n → ∀ h : 2 ≤ q ^ n, nodeVector c ⟨q ^ n, h⟩ = 0) :
    symbolPeriodMean q * massOf c +
      ∑ n ∈ Finset.Icc 1 J₀, foldedCosineCoefficient q n * Real.sqrt ((q ^ n : ℕ) : ℝ) *
        powerNodeValue c q n ≤ nodeArchOnly c := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have h := nodeArchOnly_sub_signedBathtub_eq hq c hc J₀ hJ₀
  have hnn : 0 ≤ (1 / (2 * π)) * ∫ r, combinationSpectralDensity c r *
      (EF.gammaBracket r - foldedSymbol (Real.log q) (phase (Real.log q) r)) := by
    refine mul_nonneg (by positivity) (integral_nonneg fun r => mul_nonneg
      (combinationSpectralDensity_nonneg hc r) ?_)
    linarith [foldedSymbol_phase_le hℓ r]
  linarith

/-- **The signed bathtub for every compact combination**: the node values at the powers of `q`
vanish beyond some `J₀`, and the archimedean part is at least the Fourier-priced sum. -/
theorem exists_signedBathtub {q : ℕ} (hq : 2 ≤ q) (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    ∃ J₀ : ℕ, (∀ n : ℕ, J₀ < n → powerNodeValue c q n = 0) ∧
      symbolPeriodMean q * massOf c +
        ∑ n ∈ Finset.Icc 1 J₀, foldedCosineCoefficient q n * Real.sqrt ((q ^ n : ℕ) : ℝ) *
          powerNodeValue c q n ≤ nodeArchOnly c := by
  obtain ⟨J₀, hJ₀⟩ := exists_nodeVector_pow_eq_zero c hq
  refine ⟨J₀, fun n hn => ?_, nodeArchOnly_ge_signedBathtub hq c hc J₀ hJ₀⟩
  rw [powerNodeValue]
  split_ifs with h
  · exact hJ₀ n hn h
  · rfl

end

end GaloisForLFunctions.BiScaleUncertainty
