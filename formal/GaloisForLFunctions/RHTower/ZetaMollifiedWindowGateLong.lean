import GaloisForLFunctions.RHTower.ZetaGateUpperHighBlock
import GaloisForLFunctions.RHTower.ZetaMollifiedWindowGateLength

/-!
# The Barban–Vehov mollified mean square on high blocks for lengths up to `U^{21/50}`

The high-block law of `ZetaGateUpperHighBlock` holds for every coefficient family of length
`≤ U^{21/50}` bounded by `1`, given a main-term bound.  For the Barban–Vehov mollifier
`Ψ_N = Σ_{n ≤ N} μ(n) log(N/n)/log N · n^{−s}` of length `N = ⌊U^θ⌋`, `1/5 ≤ θ ≤ 21/50`, the main
term `S₂(d) ‖ζ(1 + 2d)‖ ‖∫ w χχ‖` is at most `(v − a + 2η) B_R` with an explicit `B_R`
(`bv_mainTerm_le_long`): `S₂ ≪ N^{2d}(1 + log N)/log² N`, `N^{2d} ≤ e^{2R}`, `log N ≥ log U/10`,
`‖ζ(1 + 2d)‖ ≤ 3/2 + log U/(2R)`.  Hence for every `ε > 0`, all large `U`, the displacement
`d ≈ R/log U` and every block `U^{49/50} ≤ a ≤ v ≤ 2a ≤ 2U`,

  `∫_a^v ‖ζΨ_N(½ − d + iτ)‖² dτ ≤ (B_R + ε)(v − a + 2a^{19/20})`

(`exists_bv_window_bound_long`).
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The Barban–Vehov length `⌊U^θ⌋`. -/
def bvLen (θ U : ℝ) : ℕ := ⌊U ^ θ⌋₊

theorem bvLen_le {θ U : ℝ} (hU : 0 ≤ U) : (bvLen θ U : ℝ) ≤ U ^ θ :=
  Nat.floor_le (by positivity)

theorem bvLen_gt (θ U : ℝ) : U ^ θ - 1 < (bvLen θ U : ℝ) := by
  have := Nat.lt_floor_add_one (U ^ θ)
  unfold bvLen
  linarith

/-- `U^θ/2 ≤ ⌊U^θ⌋` once `U^θ ≥ 2`. -/
theorem half_rpow_le_bvLen {θ U : ℝ} (h2 : 2 ≤ U ^ θ) : U ^ θ / 2 ≤ (bvLen θ U : ℝ) := by
  have := bvLen_gt θ U
  linarith

theorem abs_hbReal_le_one (N n : ℕ) (hn : n ∈ Finset.Icc 1 N) : |hbReal N n| ≤ 1 := by
  rcases le_or_gt 2 N with hN | hN
  · have h := norm_hbCoeff_le hN hn
    rwa [hbCoeff_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  · have hlog : Real.log (N : ℝ) = 0 := by
      interval_cases N
      · simp
      · simp
    unfold hbReal
    rw [hlog, div_zero, abs_zero]
    norm_num

/-- The main-term constant `B_R`. -/
def bvLongStar (R : ℝ) : ℝ :=
  2560 * Real.exp 1 * Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (6 * R) * (1 + 1 / R)

theorem bvLongStar_nonneg {R : ℝ} (hR : 0 < R) : 0 ≤ bvLongStar R := by
  unfold bvLongStar
  have := Sieve.coprimeLogMoebiusConst_nonneg
  positivity

/-- The scale facts for `N = ⌊U^θ⌋`, `1/5 ≤ θ ≤ 21/50`, `U ≥ 2^{50}`. -/
theorem bvLen_facts {θ U : ℝ} (hθ0 : 1 / 5 ≤ θ) (hθ1 : θ ≤ 21 / 50) (hU : (2 : ℝ) ^ 50 ≤ U) :
    2 ≤ bvLen θ U ∧ Real.log U / 10 ≤ Real.log (bvLen θ U) ∧ 1 ≤ Real.log (bvLen θ U) ∧
      (bvLen θ U : ℝ) ≤ U ^ ((21 : ℝ) / 50) := by
  have hU1 : 1 ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU
  have hU0 : 0 < U := by linarith
  have h10 : (2 : ℝ) ^ 10 ≤ U ^ θ := by
    have e : ((2 : ℝ) ^ 50) ^ ((1 : ℝ) / 5) = (2 : ℝ) ^ 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (2 : ℝ) ^ 10 = ((2 : ℝ) ^ 50) ^ ((1 : ℝ) / 5) := e.symm
      _ ≤ U ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) hU (by norm_num)
      _ ≤ U ^ θ := Real.rpow_le_rpow_of_exponent_le hU1 hθ0
  have hhalf := half_rpow_le_bvLen (le_trans (by norm_num) h10)
  have hN2 : (2 : ℝ) ≤ bvLen θ U := by linarith
  have hNpos : (0 : ℝ) < bvLen θ U := by linarith
  have hlogU : 50 * Real.log 2 ≤ Real.log U := by
    have := Real.log_le_log (by positivity) hU
    rwa [Real.log_pow] at this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : θ * Real.log U - Real.log 2 ≤ Real.log (bvLen θ U) := by
    have h := Real.log_le_log (by positivity) hhalf
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h
  refine ⟨by exact_mod_cast hN2, ?_, ?_, ?_⟩
  · have : Real.log U / 5 ≤ θ * Real.log U := by
      have := mul_le_mul_of_nonneg_right hθ0 (by linarith : (0 : ℝ) ≤ Real.log U)
      linarith
    nlinarith
  · have h7 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have : Real.log U / 5 ≤ θ * Real.log U := by
      have := mul_le_mul_of_nonneg_right hθ0 (by linarith : (0 : ℝ) ≤ Real.log U)
      linarith
    nlinarith
  · exact (bvLen_le hU0.le).trans (Real.rpow_le_rpow_of_exponent_le hU1 hθ1)

/-- `N^{2d} ≤ e^{2R}` for `N ≤ U^{21/50}` and `d log U ≤ 2R`. -/
theorem bvLen_rpow_le {d U R : ℝ} (hd : 0 < d) (hU1 : 1 ≤ U) (hdU : d * Real.log U ≤ 2 * R)
    {N : ℕ} (hN : (N : ℝ) ≤ U ^ ((21 : ℝ) / 50)) : (N : ℝ) ^ (2 * d) ≤ Real.exp (2 * R) := by
  have hU0 : 0 < U := by linarith
  calc (N : ℝ) ^ (2 * d) ≤ (U ^ ((21 : ℝ) / 50)) ^ (2 * d) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)
    _ = Real.exp (21 / 25 * (d * Real.log U)) := by
        rw [← Real.rpow_mul hU0.le, Real.rpow_def_of_pos hU0]
        congr 1
        ring
    _ ≤ Real.exp (2 * R) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ d * Real.log U := mul_nonneg hd.le (Real.log_nonneg hU1)
        nlinarith

/-- **The main term for the long Barban–Vehov mollifier.** -/
theorem bv_mainTerm_le_long {R θ U d a v η : ℝ} (hR : 0 < R) (hθ0 : 1 / 5 ≤ θ)
    (hθ1 : θ ≤ 21 / 50) (hU : (2 : ℝ) ^ 50 ≤ U) (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hRd : R ≤ d * Real.log U) (hdU1 : d * Real.log (U - 1) ≤ R) (hη : 0 < η)
    (h4 : 4 ≤ a - η) (hav : a ≤ v) (hvU : v ≤ U) (hηa : η ≤ a) :
    gcdSum₂ d (bvLen θ U) (hbReal (bvLen θ U)) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (v - a + 2 * η) * bvLongStar R := by
  obtain ⟨hN2, hlogN, hlogN1, hNle⟩ := bvLen_facts hθ0 hθ1 hU
  set N := bvLen θ U with hNdef
  have hU1 : 1 ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU
  have hU3 : 3 ≤ U := le_trans (by norm_num) hU
  have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith)
  have hdU : d * Real.log U ≤ 2 * R := by
    have h1 : Real.log U ≤ 2 * Real.log (U - 1) := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (by norm_num; nlinarith)
    have := mul_le_mul_of_nonneg_left h1 hd.le
    linarith
  have hd4 : d ≤ 1 / 4 := by linarith
  have hS := gcdSum₂_hbReal_le hd.le hN2
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have hχ := norm_integral_window_chiPairWeight_le hd hd4 hη h4 hav
  have hN2d := bvLen_rpow_le hd hU1 hdU hNle
  have hχf := chi_weight_factor_le (q := v) (η := η) hd hd8 hU1 hdU
    (by linarith only [hav, h4, hη]) (by linarith only [hvU, hηa, hav, hU1])
  have h1d := inv_two_mul_le hd hR hRd
  have hlogf : (1 + Real.log N) / Real.log N ^ 2 ≤ 20 / Real.log U := by
    have hlN : 0 < Real.log N := by linarith
    rw [div_le_div_iff₀ (by positivity) hlogU0]
    nlinarith
  have hCL := Sieve.coprimeLogMoebiusConst_nonneg
  have hS' : gcdSum₂ d N (hbReal N)
      ≤ Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (2 * R) * (64 * (20 / Real.log U)) := by
    calc gcdSum₂ d N (hbReal N)
        ≤ Sieve.coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (2 * d)
          * (64 * (1 + Real.log N)) / (Real.log N) ^ 2 := hS
      _ = Sieve.coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (2 * d)
          * (64 * ((1 + Real.log N) / (Real.log N) ^ 2)) := by ring
      _ ≤ Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (2 * R) * (64 * (20 / Real.log U)) := by
          gcongr
  have hζ' : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ 3 / 2 + Real.log U / (2 * R) :=
    hζ.trans (by linarith only [h1d])
  have hχ' : ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ (v - a + 2 * η) * (Real.exp 1 * (2 * Real.exp (4 * R))) := by
    refine hχ.trans ?_
    gcongr
  have hlen : 0 ≤ v - a + 2 * η := by linarith
  calc gcdSum₂ d N (hbReal N) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (2 * R) * (64 * (20 / Real.log U)))
        * ((3 / 2 + Real.log U / (2 * R))
          * ((v - a + 2 * η) * (Real.exp 1 * (2 * Real.exp (4 * R))))) := by
        gcongr
    _ = (v - a + 2 * η) * (2560 * Real.exp 1 * Sieve.coprimeLogMoebiusConst ^ 2
          * Real.exp (6 * R) * (3 / (2 * Real.log U) + 1 / (2 * R))) := by
        rw [show Real.exp (6 * R) = Real.exp (2 * R) * Real.exp (4 * R) by
          rw [← Real.exp_add]; ring_nf]
        field_simp
        ring
    _ ≤ (v - a + 2 * η) * bvLongStar R := by
        unfold bvLongStar
        have h1 : 3 / (2 * Real.log U) ≤ 1 := by
          have : (2 : ℝ) ≤ Real.log U := by
            have h := Real.log_le_log (by positivity) hU
            rw [Real.log_pow] at h
            have := Real.log_two_gt_d9
            push_cast at h
            linarith
          rw [div_le_one (by positivity)]
          linarith
        have h2 : 1 / (2 * R) ≤ 1 / R := by
          rw [div_le_div_iff₀ (by positivity) hR]
          linarith
        gcongr

/-- **The long Barban–Vehov high-block law.** -/
theorem exists_bv_window_bound_long {R θ : ℝ} (hR : 0 < R) (hθ0 : 1 / 5 ≤ θ)
    (hθ1 : θ ≤ 21 / 50) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (hbCoeff (bvLen θ U)) (Finset.Icc 1 (bvLen θ U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (bvLongStar R + ε) * (v - a + 2 * a ^ ((19 : ℝ) / 20)) := by
  intro ε hε
  have hN : ∀ᶠ U in atTop, (bvLen θ U : ℝ) ≤ U ^ ((21 : ℝ) / 50) := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    exact (bvLen_facts hθ0 hθ1 hU).2.2.2
  have hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (bvLen θ U) (hbReal (bvLen θ U)) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * bvLongStar R := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    intro d hd hd8 hRd hdU1 a v η hη h4 hav hvU hηa _ _
    exact bv_mainTerm_le_long hR hθ0 hθ1 hU hd hd8 hRd hdU1 hη h4 hav hvU hηa
  have h := exists_highBlock_bound_of_mainTerm_upper_window hR
    (tendsto_const_nhds (x := bvLongStar R)) (bvLen θ) (fun U => hbReal (bvLen θ U)) hN
    (fun U n hn => abs_hbReal_le_one _ n hn) hmain ε hε
  filter_upwards [h] with U hU
  intro d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  have e : (fun n => ((hbReal (bvLen θ U) n : ℝ) : ℂ)) = hbCoeff (bvLen θ U) := by
    funext n
    exact (hbCoeff_eq_ofReal _ n).symm
  have := hU d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  rwa [e] at this

end RHTower.ZetaGateProductAFE

end
