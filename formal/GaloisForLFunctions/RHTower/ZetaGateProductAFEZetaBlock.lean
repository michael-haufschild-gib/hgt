import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlock

/-!
# The mean square of `ζ` on a high block

The block inequality of the product approximate functional equation holds for every mollifier;
with the trivial mollifier `Ψ = 1` (`N = 1`) its diagonal is `S₂ = 1` and its pair error is a single
term.  On the displaced line `Re s = ½ − d`, `R ≤ d log U ≤ 2R`, every block `[a, v]` with
`U^{1/8} ≤ a ≤ v ≤ 2a`, `v ≤ U` therefore satisfies

  `∫_a^v |ζ(½ − d + iτ)|² dτ ≤ K · a · log U`

with `K` depending only on `R` (`exists_zetaBlock_meanSquare_le`): the main term is
`|ζ(1 + 2d)| · ∫ w |χ|² ≪ (log U/R) · e^{4R} · a`.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The trivial Dirichlet polynomial is `1`. -/
theorem edPoly_one_singleton (z : ℂ) : edPoly (fun _ => (1 : ℂ)) (Finset.Icc 1 1) z = 1 := by
  unfold edPoly
  simp

theorem gcdSum₂_one (d : ℝ) : gcdSum₂ d 1 (fun _ => (1 : ℝ)) = 1 := by
  unfold gcdSum₂ reducedProd
  simp

/-- The main term of a block for the trivial mollifier. -/
theorem zetaBlock_mainTerm_le {R U d a v η : ℝ} (hR : 0 < R) (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hRd : R ≤ d * Real.log U) (hdU : d * Real.log U ≤ 2 * R) (hU1 : 1 ≤ U)
    (hlogU : 1 ≤ Real.log U) (hη : 0 < η) (h4 : 4 ≤ a - η) (hav : a ≤ v) (hq3 : v + η ≤ 3 * U)
    (hlen3 : v - a + 2 * η ≤ 3 * a) :
    ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ 6 * Real.exp (1 + 4 * R) * (3 / 2 + 1 / (2 * R)) * Real.log U * a := by
  have hd4 : d ≤ 1 / 4 := by linarith
  have ha0 : 0 < a := by linarith
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have h1d := inv_two_mul_le hd hR hRd
  have hlog0 : 0 ≤ Real.log U := by linarith
  have hZ : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ (3 / 2 + 1 / (2 * R)) * Real.log U := by
    have : Real.log U / (2 * R) = 1 / (2 * R) * Real.log U := by ring
    have h32 : 3 / 2 ≤ 3 / 2 * Real.log U := by linarith
    linarith only [hζ, h1d, this, h32]
  have hχ := norm_integral_window_chiPairWeight_le hd hd4 hη h4 hav
  have hχf := chi_weight_factor_le hd hd8 hU1 hdU (by linarith only [hav, ha0, hη]) hq3
  have hX : ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ 3 * a * (2 * Real.exp (1 + 4 * R)) := by
    refine hχ.trans ?_
    have h1 : Real.exp 1 * ((v + η) / (2 * Real.pi)) ^ (2 * d)
        ≤ 2 * Real.exp (1 + 4 * R) := by
      rw [Real.exp_add]
      nlinarith [Real.exp_pos 1]
    have hvη : 0 ≤ (v + η) / (2 * Real.pi) := by
      have : 0 ≤ v + η := by linarith
      positivity
    exact mul_le_mul hlen3 h1 (mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg hvη _))
      (by positivity)
  have hZ0 : 0 ≤ (3 / 2 + 1 / (2 * R)) * Real.log U := by positivity
  calc ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ ((3 / 2 + 1 / (2 * R)) * Real.log U) * (3 * a * (2 * Real.exp (1 + 4 * R))) :=
        mul_le_mul hZ hX (norm_nonneg _) hZ0
    _ = 6 * Real.exp (1 + 4 * R) * (3 / 2 + 1 / (2 * R)) * Real.log U * a := by ring

/-- The pair error of a block for the trivial mollifier. -/
theorem zetaBlock_pairError_le {R U d u a v P : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hU1 : 1 ≤ U)
    (hdU : d * Real.log U ≤ 2 * R) (hlogU : 1 ≤ Real.log U) (hu2 : 2 ≤ u) (hp : a = u ^ 100)
    (hav : a ≤ v) (hq2 : v ≤ 2 * u ^ 100) (hvU : v ≤ U) (h4 : 4 ≤ a - u ^ 95)
    (hlen3 : v - a + 2 * u ^ 95 ≤ 3 * a)
    {CA C₁ C₂ K₁ K₂ : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(20 : ℝ)))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 20 C₁ x p q η V * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((20 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 40 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((40 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2)
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ σ₀ c x : ℝ, 1 / 4 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K₁ * (x / c) ^ (-(1 / 4 : ℝ)))
    (hK₂ : ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 8 → 0 < c → 0 < x →
      ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d)))
    (hP : P = pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) :
    ‖pairError d (u ^ 100) a v (u ^ 95) (1 / Nat.gcd 1 1) (1 / Nat.gcd 1 1) 1 1‖
      ≤ 3 * P * Real.log U * a := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have ha0 : 0 < a := by rw [hp]; positivity
  have hN : ((1 : ℕ) : ℝ) ≤ u ^ 8 := by push_cast; exact one_le_pow₀ hu1
  have h11 : (1 : ℕ) ∈ Finset.Icc 1 1 := by simp
  have hb := norm_pairError_le_param hd hd8 hu2 hp hav hq2 hN h11 h11 hCA0 hCA hC₁ hC₂ hsplit
    hK₁0 hK₂0 hK₁ hK₂
  have hη : 0 < u ^ 95 := by positivity
  have hLf : (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) :=
    rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by linarith only [h4])
      (by linarith only [hav, hvU, hU1, hη])
  have hu21 : 1 ≤ u ^ 21 := one_le_pow₀ hu1
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  refine hb.trans ?_
  have hstar : (pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 21 ≤ P := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d) ≤ P := by
      have := mul_le_mul_of_nonneg_left hLf (show 0 ≤ 2 * K₂ by positivity)
      rw [hP]
      linarith only [this]
    nlinarith
  have hlen0 : 0 ≤ v - a + 2 * u ^ 95 := by linarith
  calc (v - a + 2 * u ^ 95)
        * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 21)
      ≤ (3 * a) * P := mul_le_mul hlen3 hstar (by positivity) (by positivity)
    _ ≤ 3 * P * Real.log U * a := by nlinarith [mul_nonneg hP0 ha0.le]

/-- **The mean square of `ζ` on a high block.** -/
theorem exists_zetaBlock_meanSquare_le {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log U ≤ 2 * R →
      ∀ a v : ℝ, U ^ ((1 : ℝ) / 8) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)‖ ^ 2) ≤ K * Real.log U * a := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 20) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 20 (K'' := 40) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothDiagonal_left_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualDiagonal_left_le
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  set P : ℝ := pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) with hP
  have hP0 : 0 ≤ P := by positivity
  refine ⟨6 * Real.exp (1 + 4 * R) * (3 / 2 + 1 / (2 * R)) + 3 * P, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800), eventually_ge_atTop (Real.exp 1)]
    with U hU2 hUe
  intro d hd hd8 hRd hdU a v haU hav hv2 hvU
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
  have hlogU : 1 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 1) hUe
    rwa [Real.log_exp] at this
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) h2100
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = a ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hu2 : 2 ≤ u := by
    have e : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul (by norm_num),
        show ((100 : ℕ) : ℝ) * (1 / 100) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [hudef, ← e]
    exact Real.rpow_le_rpow (by positivity) h2100 (by norm_num)
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
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
  have hlen3 : v - a + 2 * u ^ 95 ≤ 3 * a := by rw [hp] at hηa ⊢; linarith
  have hN : ((1 : ℕ) : ℝ) ≤ u ^ 8 := by push_cast; exact one_le_pow₀ hu1
  -- the trivial mollifier
  have hone : ∀ τ : ℝ, ‖riemannZeta (displacedLinePt d τ)‖ ^ 2 =
      ‖riemannZeta (displacedLinePt d τ)
        * edPoly (fun _ => (1 : ℂ)) (Finset.Icc 1 1) (displacedLinePt d τ)‖ ^ 2 := by
    intro τ
    rw [edPoly_one_singleton, mul_one]
  simp_rw [hone]
  have hA := intervalIntegral_le_window_integral hη hav
    (continuousOn_normSq_zeta_mul_edPoly (d := d) (q := v) h4 (fun _ => (1 : ℂ)) 1)
    (fun t => by positivity)
  have hB := integral_window_normSq_le hd hd8 (x := u ^ 100) (by positivity) hη h4 hav
    (N := 1) (b := fun _ => (1 : ℂ)) (a := fun _ => (1 : ℝ)) (fun n _ => by simp)
  rw [gcdSum₂_one, one_mul] at hB
  have hmain := zetaBlock_mainTerm_le hR hd hd8 hRd hdU hU1 hlogU hη h4 hav hq3 hlen3
  have herr : ∑ h ∈ Finset.Icc 1 1, ∑ k ∈ Finset.Icc 1 1,
        ‖(fun _ : ℕ => (1 : ℂ)) h‖ * ‖(fun _ : ℕ => (1 : ℂ)) k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ 3 * P * Real.log U * a := by
    simp only [Finset.Icc_self, Finset.sum_singleton, norm_one, one_mul]
    exact zetaBlock_pairError_le hd hd8 hU1 hdU hlogU hu2 hp hav hq2 hvU h4 hlen3 hCA0 hCA hC₁ hC₂
      hsplit hK₁0 hK₂0 hK₁ hK₂ hP
  calc (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
          * edPoly (fun _ => (1 : ℂ)) (Finset.Icc 1 1) (displacedLinePt d τ)‖ ^ 2)
      ≤ _ := hA
    _ ≤ _ := hB
    _ ≤ 6 * Real.exp (1 + 4 * R) * (3 / 2 + 1 / (2 * R)) * Real.log U * a
        + 3 * P * Real.log U * a := add_le_add hmain herr
    _ = (6 * Real.exp (1 + 4 * R) * (3 / 2 + 1 / (2 * R)) + 3 * P) * Real.log U * a := by ring

end RHTower.ZetaGateProductAFE

end
