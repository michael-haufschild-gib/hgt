import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlock

/-!
# The high-block mollified mean square for every mollifier length in `[U^{1/200}/2, U^{1/100}]`

`exists_highBlock_window_bound_productAFE` bounds the Barban–Vehov mollified mean square on the
displaced line `Re s = 1/2 − d` for the length `⌊U^{1/100}⌋`. The block inequality only uses
`N ≤ U^{1/100}` (for the pair errors) and `log U ≤ 400 log N` (for the main term
`gcdSum₂ ≪ N^{2d}(1 + log N)/log² N`). So the same bound holds, with the constant doubled, for
every length in the range, uniformly:

`∫_a^v ‖ζΨ_N(1/2 − d + iτ)‖² dτ ≤ (c₀ + ε)(v − a + 2a^{95/100})`
(`exists_highBlock_window_bound_productAFE_len`), `c₀ = 400 M_R/R`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- `(1 + L)/L² ≤ 800 / L_U` when `1 ≤ L` and `L_U ≤ 400 L`. -/
theorem log_factor_le_eight_hundred {L LU : ℝ} (hL1 : 1 ≤ L) (hLU : 0 < LU)
    (hNU : LU ≤ 400 * L) : (1 + L) / L ^ 2 ≤ 800 / LU := by
  have hL0 : 0 < L := by linarith
  rw [div_le_div_iff₀ (by positivity) hLU]
  have : (1 + L) * LU ≤ (2 * L) * (400 * L) :=
    mul_le_mul (by linarith) hNU hLU.le (by linarith)
  nlinarith

/-- **The high-block window bound for every mollifier length `N ≤ U^{1/100}` with
`log U ≤ 400 log N`.** -/
theorem exists_highBlock_window_bound_productAFE_len {R : ℝ} (hR : 0 < R) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ N : ℕ, 2 ≤ N → (N : ℝ) ≤ U ^ ((1 : ℝ) / 100) → Real.log U ≤ 400 * Real.log N →
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log U ≤ 2 * R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((1 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2)
          ≤ (c₀ + ε) * (v - a + 2 * a ^ ((95 : ℝ) / 100)) := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 20) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 20 (K'' := 40) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothDiagonal_left_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualDiagonal_left_le
  have hM0 := mainStar_nonneg R
  refine ⟨400 * mainStar R / R, by positivity, fun ε hε => ?_⟩
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800), eventually_ge_atTop (Real.exp 400),
    eventually_ge_atTop (Real.exp (2400 * mainStar R / ε)),
    eventually_const_mul_rpow_neg_le (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R))
      ((1 : ℝ) / 160) (by norm_num) (half_pos hε)]
    with U hU2 hUe hUM hUerr
  intro N hN2 hNle hlogNU d hd hd8 hRd hdU a v ha haU hav hv2 hvU
  have hU1 : (1 : ℝ) ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU2
  have h2100 : (2 : ℝ) ^ 100 ≤ a := by
    have e : ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 8) = (2 : ℝ) ^ 100 := by
      rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num),
        show ((800 : ℕ) : ℝ) * (1 / 8) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (2 : ℝ) ^ 100 = ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 8) := e.symm
      _ ≤ U ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
      _ ≤ a := haU
  clear hU2
  have hd4 : d ≤ 1 / 4 := by linarith
  have hU0 : 0 < U := by linarith
  have hlogU : 400 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 400) hUe
    rwa [Real.log_exp] at this
  have hlogU0 : 0 < Real.log U := by linarith
  have hlogUM : 2400 * mainStar R / ε ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos _) hUM
    rwa [Real.log_exp] at this
  have hlogN1 : 1 ≤ Real.log N := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = a ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hu2 : 2 ≤ u := by
    have e : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul (by norm_num),
        show ((100 : ℕ) : ℝ) * (1 / 100) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [hudef, ← e]
    exact Real.rpow_le_rpow (by positivity) h2100 (by norm_num)
  have hu0 : 0 < u := by linarith
  have hNu : (N : ℝ) ≤ u ^ 8 := by
    have hUa : U ≤ a ^ 8 := by
      calc U = (U ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
            norm_num
        _ ≤ a ^ 8 := pow_le_pow_left₀ (by positivity) haU 8
    calc (N : ℝ) ≤ U ^ ((1 : ℝ) / 100) := hNle
      _ ≤ (a ^ 8) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow hU0.le hUa (by norm_num)
      _ = u ^ 8 := by
          rw [hudef, ← Real.rpow_natCast a 8, ← Real.rpow_mul ha0.le, ← Real.rpow_natCast,
            ← Real.rpow_mul ha0.le]
          norm_num
  have hu5 : U ^ ((1 : ℝ) / 160) ≤ u ^ 5 := by
    calc U ^ ((1 : ℝ) / 160) = (U ^ ((1 : ℝ) / 8)) ^ ((1 : ℝ) / 100 * 5) := by
          rw [← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ a ^ ((1 : ℝ) / 100 * 5) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
      _ = u ^ 5 := by
          rw [hudef, Real.rpow_mul ha0.le, ← Real.rpow_natCast]
          norm_num
  have hu100 : u ^ 100 = a := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  have hp : a = u ^ 100 := hu100.symm
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu2 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hη : 0 < u ^ 95 := by positivity
  have h4 : (4 : ℝ) ≤ a - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu2 100
    have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
    linarith
  have hq2 : v ≤ 2 * u ^ 100 := by rw [← hp]; exact hv2
  have hηa : u ^ 95 ≤ a := by
    rw [hp]
    linarith [pow_pos hu0 100]
  have hq3 : v + u ^ 95 ≤ 3 * U := by linarith
  have hlen : 0 ≤ v - a + 2 * u ^ 95 := by linarith
  -- window domination and the block inequality
  have hA := intervalIntegral_le_window_integral hη hav
    (continuousOn_normSq_zeta_mul_edPoly (d := d) (q := v) h4 (hbCoeff N) N)
    (fun t => by positivity)
  have hB := integral_window_normSq_le hd hd8 (x := u ^ 100) (by positivity) hη h4 hav
    (N := N) (b := hbCoeff N) (a := hbReal N) (fun n _ => hbCoeff_eq_ofReal N n)
  -- the main term
  have hS := gcdSum₂_hbReal_le hd.le hN2
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have hχ := norm_integral_window_chiPairWeight_le hd hd4 hη h4 hav
  have hN2d := mollN_rpow_le hd hU1 hdU hNle
  have hlogf := log_factor_le_eight_hundred hlogN1 hlogU0 hlogNU
  have hχf := chi_weight_factor_le hd hd8 hU1 hdU (by linarith only [hav, ha, hη]) hq3
  have h1d := inv_two_mul_le hd hR hRd
  have hS' : gcdSum₂ d N (hbReal N)
      ≤ Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * (64 * (800 / Real.log U)) := by
    have hCL := Sieve.coprimeLogMoebiusConst_nonneg
    calc gcdSum₂ d N (hbReal N)
        ≤ Sieve.coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (2 * d)
          * (64 * (1 + Real.log N)) / (Real.log N) ^ 2 := hS
      _ = Sieve.coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (2 * d)
          * (64 * ((1 + Real.log N) / (Real.log N) ^ 2)) := by ring
      _ ≤ Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * (64 * (800 / Real.log U)) := by
          gcongr
  have hζ' : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ 3 / 2 + Real.log U / (2 * R) :=
    hζ.trans (by linarith only [h1d])
  have hχ' : ‖∫ t, blockWindowC a v (u ^ 95) t * chiPairWeight d t‖
      ≤ (v - a + 2 * u ^ 95) * (Real.exp 1 * (2 * Real.exp (4 * R))) := by
    refine hχ.trans ?_
    gcongr
  have hS0 : 0 ≤ gcdSum₂ d N (hbReal N) := gcdSum₂_nonneg hd.le _ _
  have hmain : gcdSum₂ d N (hbReal N) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v (u ^ 95) t * chiPairWeight d t‖)
      ≤ (v - a + 2 * u ^ 95) * (400 * mainStar R / R + ε / 2) := by
    have hCL := Sieve.coprimeLogMoebiusConst_nonneg
    calc gcdSum₂ d N (hbReal N) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v (u ^ 95) t * chiPairWeight d t‖)
        ≤ (Sieve.coprimeLogMoebiusConst ^ 2 * Real.exp (R / 25) * (64 * (800 / Real.log U)))
          * ((3 / 2 + Real.log U / (2 * R))
            * ((v - a + 2 * u ^ 95) * (Real.exp 1 * (2 * Real.exp (4 * R))))) := by
          gcongr
      _ = (v - a + 2 * u ^ 95) * (400 * mainStar R / R + 1200 * mainStar R / Real.log U) := by
          unfold mainStar
          field_simp
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (400 * mainStar R / R + ε / 2) := by
          have : 1200 * mainStar R / Real.log U ≤ ε / 2 := by
            rw [div_le_iff₀ hlogU0]
            have := (div_le_iff₀ hε).mp hlogUM
            linarith only [this]
          gcongr
  -- the error
  have herr : ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ‖hbCoeff N h‖ * ‖hbCoeff N k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (v - a + 2 * u ^ 95) * (ε / 2) := by
    have hLf : (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) :=
      rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by linarith only [h4])
        (by linarith only [hav, hvU, hU1, hη])
    have hpair : ∀ h ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N,
        ‖hbCoeff N h‖ * ‖hbCoeff N k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
        ≤ (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
      intro h hh k hk
      have hb := norm_pairError_le_param hd hd8 hu2 hp hav hq2 hNu hh hk hCA0 hCA hC₁ hC₂ hsplit
        hK₁0 hK₂0 hK₁ hK₂
      have h1 : ‖hbCoeff N h‖ * ‖hbCoeff N k‖ ≤ 1 := by
        calc ‖hbCoeff N h‖ * ‖hbCoeff N k‖ ≤ 1 * 1 :=
              mul_le_mul (norm_hbCoeff_le hN2 hh) (norm_hbCoeff_le hN2 hk) (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
      calc ‖hbCoeff N h‖ * ‖hbCoeff N k‖
            * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
          ≤ 1 * ((v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 21)) :=
            mul_le_mul h1 hb (norm_nonneg _) zero_le_one
        _ ≤ (v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
            rw [one_mul]
            have h2 : 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * K₂ * (2 * Real.exp (4 * R)) :=
              mul_le_mul_of_nonneg_left hLf (by positivity)
            have : pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)
                ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by linarith only [h2]
            gcongr
    have hsum := Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hpair h hh k hk
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hN16 : (N : ℝ) * (N : ℝ) ≤ u ^ 16 := by
      calc (N : ℝ) * (N : ℝ) ≤ u ^ 8 * u ^ 8 :=
            mul_le_mul hNu hNu (Nat.cast_nonneg _) (by positivity)
        _ = u ^ 16 := by ring
    have hK0 : 0 ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by positivity
    have hfin : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 ≤ ε / 2 := by
      have h1 : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5
          ≤ (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) * U ^ (-((1 : ℝ) / 160)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hU0.le]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hu5) hK0
      exact h1.trans hUerr
    calc (N : ℝ) * ((N : ℝ) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)))
        = ((N : ℝ) * (N : ℝ)) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) := by ring
      _ ≤ u ^ 16 * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) :=
          mul_le_mul_of_nonneg_right hN16 (mul_nonneg hlen (div_nonneg hK0 (by positivity)))
      _ = (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5) := by
          have e : u ^ 16 * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)
              = (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 := by
            rw [mul_div_assoc', div_eq_div_iff (pow_ne_zero _ hu0.ne') (pow_ne_zero _ hu0.ne')]
            ring
          rw [← e]
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (ε / 2) := mul_le_mul_of_nonneg_left hfin hlen
  have hu95 : u ^ 95 = a ^ ((95 : ℝ) / 100) := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  calc (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
          * edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2)
      ≤ ∫ t, blockWindow a v (u ^ 95) t * ‖riemannZeta (displacedLinePt d t)
          * edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2 := hA
    _ ≤ _ := hB
    _ ≤ (v - a + 2 * u ^ 95) * (400 * mainStar R / R + ε / 2)
        + (v - a + 2 * u ^ 95) * (ε / 2) := add_le_add hmain herr
    _ = (400 * mainStar R / R + ε) * (v - a + 2 * a ^ ((95 : ℝ) / 100)) := by
        rw [hu95]
        ring

end RHTower.ZetaGateProductAFE

end
