import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorBudgetDominatesTheArchimedeanGenus
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelCofactorGramsSelectTheDominantZeros

/-!
# An Abel slope at the genus is RH with simple zeros

Let `g(u) = e^{−u/2}(ψ(⌊e^u⌋) − ⌊e^u⌋)` be the prime-error profile and
`2c A(c) = 2c ∫ e^{−2cu} g(u)² du` its **Abel slope** (`primeErrorAbelSlope`), the Abel mean of the
energy density; by Plancherel `2c A(c) = (c/π) ∫ ‖G(c + iy)‖² dy`.

* **Tauberian step** (`primeError_budget_of_abelSlope_le`). A bounded Abel slope on `(0, 1]` gives
  a prime-error budget: at `c = 1/(2(L + 1))`, `∫_0^L g² ≤ e·A(c) ≤ e K (L + 1)`.
* **Abel capacity** (`sum_order_sq_le_of_tendsto_abelSlope`). If the Abel slope tends to `L`,
  then `Σ_{ρ ∈ Z} m_ρ²/|ρ|² ≤ L` for every finite set `Z` of critical zeros: the window atoms of
  P41 enter the Abel mean with their full residue mass.
* **The genus case** (`riemannHypothesis_and_simple_of_tendsto_abelSlope`). If the Abel slope tends
  to the archimedean genus `2 + γ − log 4π = Σ_ρ 1/(ρ(1 − ρ))`, then RH holds (P46) and every
  critical zero is simple: the copies of the zeros already exhaust the genus, so a zero of order
  `m ≥ 2` would add `(m² − m)/|ρ|² > 0` beyond it.

The `𝔽_q` analogue is P42: a pure curve has prime-error slope `Σ_β mult(β)²`, equal to `2g` exactly
for a simple spectrum.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)

/-- The Abel slope `2c ∫ e^{−2cu} g(u)² du` of the prime-error profile. -/
def primeErrorAbelSlope (c : ℝ) : ℝ := 2 * c * abelGram (logProfile primeErrorRow) c 0 0

theorem abelGram_primeError_eq (c : ℝ) :
    abelGram (logProfile primeErrorRow) c 0 0 =
      ∫ u, Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2 := by
  simp only [abelGram, sub_zero, sq]

theorem abelGram_primeError_nonneg (c : ℝ) : 0 ≤ abelGram (logProfile primeErrorRow) c 0 0 := by
  rw [abelGram_primeError_eq]
  exact integral_nonneg fun u => by positivity

/-- Larger damping, smaller Abel energy: `A(c′) ≤ A(c)` for `0 ≤ c ≤ c′`. -/
theorem abelGram_primeError_anti {c c' : ℝ} (hcc : c ≤ c')
    (hint : Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2) :
    (Integrable fun u => Real.exp (-(2 * c' * u)) * logProfile primeErrorRow u ^ 2) ∧
      abelGram (logProfile primeErrorRow) c' 0 0 ≤ abelGram (logProfile primeErrorRow) c 0 0 := by
  have hle : ∀ u, Real.exp (-(2 * c' * u)) * logProfile primeErrorRow u ^ 2 ≤
      Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2 := by
    intro u
    rcases lt_or_ge u 0 with hu | hu
    · rw [logProfile_of_neg primeErrorRow_zero hu]; simp
    · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (sq_nonneg _)
  have hmeas : AEStronglyMeasurable
      (fun u => Real.exp (-(2 * c' * u)) * logProfile primeErrorRow u ^ 2) volume :=
    ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(2 * c' * u))).mul
      ((measurable_logProfile primeErrorRow).pow_const 2)).aestronglyMeasurable
  have hint' : Integrable fun u => Real.exp (-(2 * c' * u)) * logProfile primeErrorRow u ^ 2 :=
    hint.mono hmeas (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact hle u)
  refine ⟨hint', ?_⟩
  rw [abelGram_primeError_eq, abelGram_primeError_eq]
  exact integral_mono hint' hint hle

/-- **Tauberian step.** An Abel slope bounded by `K` on `(0, 1]` gives the prime-error budget
`∫_0^L g² ≤ e K L + e K`. -/
theorem primeError_budget_of_abelSlope_le {K : ℝ}
    (hint : ∀ c, 0 < c →
      Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2)
    (hA : ∀ c, 0 < c → c ≤ 1 → primeErrorAbelSlope c ≤ K) (L : ℝ) (hL : 0 ≤ L) :
    ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ Real.exp 1 * K * L + Real.exp 1 * K := by
  set c : ℝ := 1 / (2 * (L + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one (by positivity)]; linarith
  have h2cL : 2 * c * L ≤ 1 := by
    rw [hc]; field_simp; linarith
  have hII : IntervalIntegrable (fun u => logProfile primeErrorRow u ^ 2) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hL).mpr
      (integrableOn_logProfile_sq zero_le_one abs_primeErrorRow_le L)
  have hII' : IntervalIntegrable
      (fun u => Real.exp 1 * (Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2))
      volume 0 L := ((hint c hc0).const_mul _).intervalIntegrable
  calc ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2
      ≤ ∫ u in (0 : ℝ)..L, Real.exp 1 *
          (Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2) := by
        refine intervalIntegral.integral_mono_on hL hII hII' fun u hu => ?_
        rw [← mul_assoc, ← Real.exp_add]
        have : 0 ≤ 1 + -(2 * c * u) := by nlinarith [hu.2, hu.1]
        exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_exp this)
    _ = Real.exp 1 * ∫ u in Ioc (0 : ℝ) L,
          Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hL]
    _ ≤ Real.exp 1 * abelGram (logProfile primeErrorRow) c 0 0 := by
        rw [abelGram_primeError_eq]
        exact mul_le_mul_of_nonneg_left (setIntegral_le_integral (hint c hc0)
          (Eventually.of_forall fun u => by positivity)) (Real.exp_pos 1).le
    _ = Real.exp 1 * (primeErrorAbelSlope c * (L + 1)) := by
        rw [primeErrorAbelSlope, hc]; field_simp
    _ ≤ Real.exp 1 * (K * (L + 1)) := by
        gcongr
        exact hA c hc0 hc1
    _ = Real.exp 1 * K * L + Real.exp 1 * K := by ring

/-- A convergent Abel slope is bounded on `(0, 1]`. -/
theorem exists_abelSlope_le_of_tendsto {L : ℝ}
    (hint : ∀ c, 0 < c →
      Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2)
    (hlim : Tendsto primeErrorAbelSlope (𝓝[>] 0) (𝓝 L)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c, 0 < c → c ≤ 1 → primeErrorAbelSlope c ≤ K := by
  have h := hlim.eventually (Iio_mem_nhds (lt_add_one L))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  have hc₀0 : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
  have hc₀1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
  have hc₀ε : min (ε / 2) 1 < ε := (min_le_left _ _).trans_lt (by linarith)
  have hslope₀ : primeErrorAbelSlope (min (ε / 2) 1) < L + 1 :=
    hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hc₀0]; exact hc₀ε) hc₀0
  refine ⟨(|L| + 1) / min (ε / 2) 1, by positivity, fun c hc hc1 => ?_⟩
  rcases lt_or_ge c (min (ε / 2) 1) with hlt | hge
  · have hsl : primeErrorAbelSlope c < L + 1 :=
      hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hc]; exact hlt.trans hc₀ε) hc
    calc primeErrorAbelSlope c ≤ |L| + 1 := by linarith [le_abs_self L]
      _ ≤ (|L| + 1) / min (ε / 2) 1 := le_div_self (by positivity) hc₀0 hc₀1
  · obtain ⟨-, hanti⟩ := abelGram_primeError_anti hge (hint _ hc₀0)
    have hA := abelGram_primeError_nonneg c
    have e1 : primeErrorAbelSlope c ≤
        primeErrorAbelSlope (min (ε / 2) 1) / min (ε / 2) 1 := by
      have e0 : primeErrorAbelSlope (min (ε / 2) 1) / min (ε / 2) 1 =
          2 * abelGram (logProfile primeErrorRow) (min (ε / 2) 1) 0 0 := by
        rw [primeErrorAbelSlope]; field_simp
      rw [e0, primeErrorAbelSlope]
      nlinarith [mul_le_mul_of_nonneg_right hc1 hA]
    calc primeErrorAbelSlope c ≤ primeErrorAbelSlope (min (ε / 2) 1) / min (ε / 2) 1 := e1
      _ ≤ (|L| + 1) / min (ε / 2) 1 := by gcongr; linarith [le_abs_self L]

/-- **Abel capacity.** If the Abel slope tends to `L`, every finite set `Z` of critical zeros has
`Σ_{ρ ∈ Z} m_ρ²/|ρ|² ≤ L`. -/
theorem sum_order_sq_le_of_tendsto_abelSlope {L : ℝ}
    (hint : ∀ c, 0 < c →
      Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2)
    (hlim : Tendsto primeErrorAbelSlope (𝓝[>] 0) (𝓝 L)) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2) :
    ∑ ρ ∈ Z, ‖(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2 ≤ L := by
  obtain ⟨K, hK, hA⟩ := exists_abelSlope_le_of_tendsto hint hlim
  have hlin := primeError_budget_of_abelSlope_le hint hA
  have hS0 : 0 ≤ Real.exp 1 * K := by positivity
  have hpole : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀,
      ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
        ‖lineSymbol (logProfile primeErrorRow) e y -
          -(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ /
            ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M := fun ρ hρ =>
    exists_primeError_window_pole_bound hS0 hS0 hlin (hZ ρ hρ).1 (hZ ρ hρ).2
  have hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im := fun ρ hρ ρ' hρ' hne h =>
    hne (Complex.ext (by rw [(hZ ρ hρ).2, (hZ ρ' hρ').2]) h)
  by_contra hlt
  simp only [not_le] at hlt
  set R := ∑ ρ ∈ Z, ‖(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2 with hR
  have hRr : ∑ ρ ∈ Z, ‖-(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2 = R := by
    simp only [neg_div, norm_neg, hR]
  have hpi := Real.pi_pos
  have hcap := eventually_le_mul_integral_lineSymbol_of_poles primeErrorRow_zero hS0 hS0 hlin Z
    hsep _ hpole (M := Real.pi * (L + R) / 2) (by rw [hRr]; nlinarith)
  have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), primeErrorAbelSlope e < (L + R) / 2 :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨e, he1, he2, he0⟩ := (hcap.and (hsmall.and self_mem_nhdsWithin)).exists
  have he : (0 : ℝ) < e := he0
  have hdata := integrable_and_memLp_dampedProfile_logProfile (c := e) primeErrorRow_zero
    (add_nonneg (div_nonneg hS0 he.le) hS0) he.le
    (fun T => pronic_energy_le_of_linear hS0 hS0 hlin he T) (by linarith)
  rw [integral_norm_sq_lineSymbol hdata.1 hdata.2] at he1
  have : e * (2 * Real.pi * abelGram (logProfile primeErrorRow) e 0 0) =
      Real.pi * primeErrorAbelSlope e := by rw [primeErrorAbelSlope]; ring
  rw [this] at he1
  nlinarith

/-- **An Abel slope at the genus is RH with simple zeros.** If the Abel slope of the prime error
tends to the archimedean genus `2 + γ − log 4π`, then RH holds and every critical zero is simple. -/
theorem riemannHypothesis_and_simple_of_tendsto_abelSlope
    (hint : ∀ c, 0 < c →
      Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2)
    (hlim : Tendsto primeErrorAbelSlope (𝓝[>] 0) (𝓝 _root_.RHTower.poleSharpConstant)) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
      (analyticOrderAt riemannZeta ρ).toNat = 1 := by
  obtain ⟨K, hK, hA⟩ := exists_abelSlope_le_of_tendsto hint hlim
  have hRH := riemannHypothesis_of_primeError_budget (primeError_budget_of_abelSlope_le hint hA)
  refine ⟨hRH, fun ρ₀ hz₀ hre₀ => ?_⟩
  have hρ₀1 : ρ₀ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre₀; norm_num at hre₀
  have hρ₀0 : ρ₀ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre₀; norm_num at hre₀
  have hm₁ := one_le_toNat_analyticOrderAt_riemannZeta hz₀ hρ₀1
  by_contra hne
  have hm₂ : 2 ≤ (analyticOrderAt riemannZeta ρ₀).toNat := by omega
  have hρ₀n : 0 < ‖ρ₀‖ := norm_pos_iff.mpr hρ₀0
  have hε0 : 0 < 1 / ‖ρ₀‖ ^ 2 := by positivity
  -- a finite set of copies nearly exhausting the genus
  obtain ⟨F, hF⟩ : ∃ F : Finset _root_.RHTower.XiZeroCopy,
      _root_.RHTower.poleSharpConstant - 1 / ‖ρ₀‖ ^ 2 < ∑ q ∈ F, 1 / ‖(q.1 : ℂ)‖ ^ 2 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have := Real.tsum_le_of_sum_le (fun _ => by positivity) h
    rw [← poleSharpConstant_eq_tsum_of_riemannHypothesis hRH] at this
    linarith
  set Z₀ := (F.image Sigma.fst).map (Function.Embedding.subtype _) with hZ₀
  have hZ : ∀ ρ ∈ insert ρ₀ Z₀, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    rcases Finset.mem_insert.mp hρ with rfl | hρ
    · exact ⟨hz₀, hre₀⟩
    · obtain ⟨σ, -, rfl⟩ := Finset.mem_map.mp hρ
      exact riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH σ
  have hle := sum_order_sq_le_of_tendsto_abelSlope hint hlim _ hZ
  -- `a z = m_z/|z|²`, `b z = m_z²/|z|²`
  have hab : ∀ z : ℂ, ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2) ≤
      ‖(((analyticOrderAt riemannZeta z).toNat : ℕ) : ℂ) / z‖ ^ 2 := by
    intro z
    rw [norm_div, Complex.norm_natCast, div_pow, mul_one_div]
    gcongr
    rcases Nat.eq_zero_or_pos (analyticOrderAt riemannZeta z).toNat with h | h
    · rw [h]; simp
    · have : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta z).toNat : ℝ) := by exact_mod_cast h
      nlinarith
  have hgap : ((analyticOrderAt riemannZeta ρ₀).toNat : ℝ) * (1 / ‖ρ₀‖ ^ 2) + 2 / ‖ρ₀‖ ^ 2 ≤
      ‖(((analyticOrderAt riemannZeta ρ₀).toNat : ℕ) : ℂ) / ρ₀‖ ^ 2 := by
    rw [norm_div, Complex.norm_natCast, div_pow]
    have hm : (2 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ₀).toNat : ℝ) := by exact_mod_cast hm₂
    rw [mul_one_div, ← add_div]
    gcongr
    nlinarith
  have h1 := sum_copies_le_sum_order F
  have h2 : ∑ z ∈ Z₀, ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2) ≤
      ∑ z ∈ insert ρ₀ Z₀, ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) fun _ _ _ => by positivity
  have h3 : ∑ z ∈ insert ρ₀ Z₀, ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2) +
      2 / ‖ρ₀‖ ^ 2 ≤ ∑ z ∈ insert ρ₀ Z₀,
        ‖(((analyticOrderAt riemannZeta z).toNat : ℕ) : ℂ) / z‖ ^ 2 := by
    have hdiff := Finset.single_le_sum (s := insert ρ₀ Z₀)
      (f := fun z => ‖(((analyticOrderAt riemannZeta z).toNat : ℕ) : ℂ) / z‖ ^ 2 -
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * (1 / ‖z‖ ^ 2))
      (fun z _ => sub_nonneg.mpr (hab z)) (Finset.mem_insert_self ρ₀ Z₀)
    rw [Finset.sum_sub_distrib] at hdiff
    linarith
  have : (2 : ℝ) / ‖ρ₀‖ ^ 2 = 2 * (1 / ‖ρ₀‖ ^ 2) := by ring
  linarith

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
