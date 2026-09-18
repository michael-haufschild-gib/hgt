import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlock
import GaloisForLFunctions.RHTower.HighBlockLaw
import GaloisForLFunctions.RHTower.ZetaTwoThirdsOffLineMomentConstant

/-!
# The unconditional dyadic mean-square law and the off-line first moment

The high-block bound of `ZetaGateProductAFEHighBlock` and the crude low-block bound give, for every
`R > 0`, an unconditional constant `c` with `ZetaDyadicMeanSquareLaw R c`, hence the mollified
mean-square gate `ZetaMollifiedMeanSquareGate R c`, hence through the two-thirds proportion of
simple critical zeros the unconditional bound

  `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ C · V`   (`V` large)

for the zeros of `ξ` — the horizontal displacement of the zeros grows at most linearly in the height.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The dyadic law is monotone in its constant. -/
theorem zetaDyadicMeanSquareLaw_mono {R c c' : ℝ} (hcc' : c ≤ c') (h : ZetaDyadicMeanSquareLaw R c) :
    ZetaDyadicMeanSquareLaw R c' := by
  intro ε hε
  filter_upwards [h ε hε] with U hU
  obtain ⟨Mb, b, N, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb, hdy⟩ := hU
  refine ⟨Mb, b, N, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb, ?_⟩
  intro σ₀ hσ₀ hσ₀' hR1 hR2 a v ha hav hv2 hvU
  have := hdy σ₀ hσ₀ hσ₀' hR1 hR2 a v ha hav hv2 hvU
  have hva : 0 ≤ v - a := by linarith
  have : (c + ε) * (v - a) ≤ (c' + ε) * (v - a) := mul_le_mul_of_nonneg_right (by linarith) hva
  linarith

/-- **The unconditional dyadic mean-square law.** -/
theorem exists_zetaDyadicMeanSquareLaw_productAFE {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, 0 ≤ c ∧ ZetaDyadicMeanSquareLaw R c := by
  obtain ⟨c₀, hc₀0, hblock⟩ := exists_highBlock_bound_productAFE hR
  refine ⟨c₀, hc₀0, ?_⟩
  intro ε hε
  filter_upwards [hblock ε hε, Filter.eventually_ge_atTop (Real.exp 2),
    Filter.eventually_ge_atTop (Real.exp (8 * R) + 1),
    Filter.eventually_ge_atTop ((2 : ℝ) ^ 100),
    eventually_const_mul_rpow_neg_mul_log_pow_le (16200 * Real.exp 4) ((71 : ℝ) / 200)
      (by norm_num) 1 hε]
    with U hblockU hUe hUR hU2 hlow
  have hU1 : (1 : ℝ) ≤ U := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith only [this, hUe]
  have hU0 : (0 : ℝ) < U := by linarith only [hU1]
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith only [this]
    linarith only [this, hUe]
  have hlogU : 2 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 2) hUe
    rwa [Real.log_exp] at this
  have hlogU1 : 8 * R ≤ Real.log (U - 1) := by
    have := Real.log_le_log (Real.exp_pos _) (by linarith : Real.exp (8 * R) ≤ U - 1)
    rwa [Real.log_exp] at this
  -- the mollifier length
  have hNle : (mollN U : ℝ) ≤ U ^ ((1 : ℝ) / 100) := mollN_le hU0.le
  have hU100 : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 100) := by
    have e : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul (by norm_num),
        show ((100 : ℕ) : ℝ) * (1 / 100) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
  have hNgt := mollN_gt U
  have hN2 : 2 ≤ mollN U := by
    have h1 : (1 : ℝ) < mollN U := by linarith only [hNgt, hU100]
    have : (2 : ℝ) ≤ mollN U := by
      have : (1 : ℤ) < (mollN U : ℤ) := by exact_mod_cast h1
      have : (2 : ℤ) ≤ (mollN U : ℤ) := this
      exact_mod_cast this
    exact_mod_cast this
  have hN1 : 1 ≤ mollN U := by omega
  have hNU : (mollN U : ℝ) ≤ U - 1 := by
    have h1 : U ^ ((1 : ℝ) / 100) ≤ U ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have h2 : U ^ ((1 : ℝ) / 2) ≤ U / 2 := by
      have hsq : U ^ ((1 : ℝ) / 2) * U ^ ((1 : ℝ) / 2) = U := by
        rw [← Real.rpow_add hU0]
        norm_num
      have h4 : (2 : ℝ) ≤ U ^ ((1 : ℝ) / 2) :=
        le_trans hU100 (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num))
      nlinarith [Real.rpow_nonneg hU0.le ((1 : ℝ) / 2)]
    linarith only [hNle, h1, h2, hU3]
  have hNpos : (1 : ℝ) ≤ (mollN U : ℝ) := by exact_mod_cast hN1
  refine ⟨(mollN U : ℝ) ^ (5 : ℕ), hbCoeff (mollN U), mollN U, hN1, hbCoeff_one hN2,
    fun n hn => norm_hbCoeff_le hN2 hn, fun n _ => conj_hbCoeff _ n,
    one_le_pow₀ hNpos, sum_norm_hbCoeff_mul_rpow_le hN2, ?_, ?_⟩
  · rw [Real.log_pow]
    push_cast
    have : Real.log (mollN U : ℝ) ≤ Real.log (U - 1) :=
      Real.log_le_log (by linarith only [hNpos]) hNU
    linarith only [this]
  intro σ₀ hσ₀ hσ₀' hR1 hR2 a v ha hav hv2 hvU
  have hd : 0 < 1 / 2 - σ₀ := by linarith only [hσ₀']
  have hd8 : 1 / 2 - σ₀ ≤ 1 / 8 := by
    have hlogpos : 0 < Real.log (U - 1) := by linarith
    by_contra hcon
    rw [not_le] at hcon
    have : R < (1 / 2 - σ₀) * Real.log (U - 1) := by
      calc R = (1 / 8) * (8 * R) := by ring
        _ ≤ (1 / 8) * Real.log (U - 1) := by gcongr
        _ < (1 / 2 - σ₀) * Real.log (U - 1) := by gcongr
    linarith only [this, hR2]
  have hdU : (1 / 2 - σ₀) * Real.log U ≤ 2 * R := by
    have hlog2 : Real.log U ≤ 2 * Real.log (U - 1) := by
      have h1 : U ≤ (U - 1) ^ 2 := by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ U - 3) hU0.le
        nlinarith [this]
      have h2 : Real.log U ≤ Real.log ((U - 1) ^ 2) := Real.log_le_log hU0 h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2]
    calc (1 / 2 - σ₀) * Real.log U ≤ (1 / 2 - σ₀) * (2 * Real.log (U - 1)) :=
          mul_le_mul_of_nonneg_left hlog2 hd.le
      _ = 2 * ((1 / 2 - σ₀) * Real.log (U - 1)) := by ring
      _ ≤ 2 * R := by linarith only [hR2]
  have hpt : ∀ t : ℝ, (σ₀ : ℂ) + (t : ℂ) * I = displacedLinePt (1 / 2 - σ₀) t := fun t =>
    (displacedLinePt_half_sub σ₀ t).symm
  simp_rw [hpt]
  rcases le_or_gt (U ^ ((1 : ℝ) / 8)) a with hhigh | hlow'
  · have h := hblockU (1 / 2 - σ₀) hd hd8 hR1 hdU a v ha hhigh hav hv2 hvU
    have : ε * a ≤ ε * (a + U / Real.log U) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      have : 0 ≤ U / Real.log U := by positivity
      linarith only [this]
    linarith only [h, this]
  · -- the crude bound on the low blocks
    have hcrude := integral_normSq_zeta_mul_edPoly_crude hd (by linarith only [hσ₀])
      (by linarith only [ha]) hav (fun n hn => norm_hbCoeff_le hN2 hn)
    refine hcrude.trans ?_
    have hU8 : (1 : ℝ) ≤ U ^ ((1 : ℝ) / 8) := by
      calc (1 : ℝ) = U ^ (0 : ℝ) := (Real.rpow_zero U).symm
        _ ≤ U ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
    have hv8 : v ≤ 2 * U ^ ((1 : ℝ) / 8) := by linarith only [hv2, hlow']
    have hva : v - a ≤ 2 * U ^ ((1 : ℝ) / 8) := by linarith only [hv8, ha]
    have h1v : 1 + v ≤ 3 * U ^ ((1 : ℝ) / 8) := by linarith only [hv8, hU8]
    have h4v : 4 + v ≤ 6 * U ^ ((1 : ℝ) / 8) := by linarith only [hv8, hU8]
    have hva0 : 0 ≤ v - a := by linarith only [hav]
    have h1v0 : 0 ≤ 1 + v := by linarith only [hav, ha]
    have h4v0 : 0 ≤ 4 + v := by linarith only [hav, ha]
    have hbound : (v - a) * ((5 * Real.exp 2 * (1 + v) * (4 + v)) * (mollN U : ℝ)) ^ 2 ≤
        (2 * U ^ ((1 : ℝ) / 8)) *
          ((5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8))) *
            U ^ ((1 : ℝ) / 100)) ^ 2 := by
      have hin1 : (5 * Real.exp 2 * (1 + v) * (4 + v)) * (mollN U : ℝ) ≤
          (5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8))) *
            U ^ ((1 : ℝ) / 100) := by
        have hA : 5 * Real.exp 2 * (1 + v) ≤ 5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) :=
          mul_le_mul_of_nonneg_left h1v (by positivity)
        have hB : 5 * Real.exp 2 * (1 + v) * (4 + v) ≤
            5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8)) :=
          mul_le_mul hA h4v h4v0 (by positivity)
        exact mul_le_mul hB hNle (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hva (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        h1v0) h4v0) (Nat.cast_nonneg _)) hin1 2) (by positivity) (by positivity)
    refine hbound.trans ?_
    have hid : (2 * U ^ ((1 : ℝ) / 8)) *
        ((5 * Real.exp 2 * (3 * U ^ ((1 : ℝ) / 8)) * (6 * U ^ ((1 : ℝ) / 8))) *
          U ^ ((1 : ℝ) / 100)) ^ 2 =
        16200 * Real.exp 4 * (U ^ ((1 : ℝ) / 8) * (U ^ ((1 : ℝ) / 8)) ^ 2 * (U ^ ((1 : ℝ) / 8)) ^ 2 *
          (U ^ ((1 : ℝ) / 100)) ^ 2) := by
      rw [show Real.exp 4 = Real.exp 2 ^ 2 by rw [← Real.exp_nat_mul]; norm_num]
      ring
    have hpow : U ^ ((1 : ℝ) / 8) * (U ^ ((1 : ℝ) / 8)) ^ 2 * (U ^ ((1 : ℝ) / 8)) ^ 2 *
        (U ^ ((1 : ℝ) / 100)) ^ 2 = U ^ ((129 : ℝ) / 200) := by
      rw [← Real.rpow_natCast (U ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_natCast (U ^ ((1 : ℝ) / 100)) 2,
        ← Real.rpow_mul hU0.le, ← Real.rpow_mul hU0.le, ← Real.rpow_add hU0, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0]
      norm_num
    have hsplit : U ^ ((129 : ℝ) / 200) = U ^ (-((71 : ℝ) / 200)) * U := by
      rw [show ((129 : ℝ) / 200) = -((71 : ℝ) / 200) + 1 by norm_num, Real.rpow_add hU0,
        Real.rpow_one]
    rw [hid, hpow, hsplit]
    have hlogU0 : 0 < Real.log U := by linarith only [hlogU]
    have hid2 : 16200 * Real.exp 4 * (U ^ (-((71 : ℝ) / 200)) * U) =
        (16200 * Real.exp 4 * (U ^ (-((71 : ℝ) / 200)) * Real.log U ^ 1)) * (U / Real.log U) := by
      field_simp
      try ring
    rw [hid2]
    calc (16200 * Real.exp 4 * (U ^ (-((71 : ℝ) / 200)) * Real.log U ^ 1)) * (U / Real.log U)
        ≤ ε * (U / Real.log U) := mul_le_mul_of_nonneg_right hlow (by positivity)
      _ ≤ ε * (a + U / Real.log U) := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          linarith only [ha]
      _ ≤ (c₀ + ε) * (v - a) + ε * (a + U / Real.log U) := by
          have : 0 ≤ (c₀ + ε) * (v - a) := mul_nonneg (by positivity) hva0
          linarith only [this]

/-- **The unconditional mollified mean-square gate**, with a constant `c ≥ 1`. -/
theorem exists_zetaMollifiedMeanSquareGate_productAFE {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, 1 ≤ c ∧ ZetaMollifiedMeanSquareGate R c := by
  obtain ⟨c, hc0, hlaw⟩ := exists_zetaDyadicMeanSquareLaw_productAFE hR
  refine ⟨max c 1, le_max_right _ _, ?_⟩
  exact zetaMollifiedMeanSquareGate_of_dyadicLaw hR (zetaDyadicMeanSquareLaw_mono (le_max_left _ _) hlaw)

/-- **The horizontal displacement of the zeros of `ξ` is at most linear in the height,
unconditionally.**  There is a constant `C` with

  `Σ_{ρ, 0 < Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ C · V`   for all large `V`,

where the sum runs over the zeros of `ξ` in the box counted by `offLineMoment`. -/
theorem exists_eventually_offLineMoment_le_mul :
    ∃ C : ℝ, ∀ᶠ V in atTop, offLineMoment V ≤ C * V := by
  obtain ⟨c₁, hc₁, hgate⟩ := exists_zetaMollifiedMeanSquareGate_productAFE one_pos
  have h := eventually_offLineMoment_le_of_zetaGate_twoThirds one_pos hc₁ one_pos hgate
  refine ⟨(Real.log c₁ - (5 / 3) * 1 + 1) / (4 * Real.pi), ?_⟩
  filter_upwards [h] with V hV
  have hπ : 0 < 4 * Real.pi := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
  linarith only [hV]

end RHTower.ZetaGateProductAFE

end
