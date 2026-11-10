import GaloisForLFunctions.MultiscaleMollifiedZetaField.AdjustableDualOffDiagonalBounds
import GaloisForLFunctions.MultiscaleMollifiedZetaField.AdjustableContourRemainders
import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockInequality

/-!
# Twisted moment errors below square-root length

The direct and dual off-diagonals, both shifted contour remainders, and the
Gaussian pole term all admit arbitrary power savings on a suitable taper.
Their bounds are uniform over every pair of mollifier coefficients.
-/

noncomputable section
open Complex MeasureTheory Finset Set Filter Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem norm_real_rpow_le_one {u e : ℝ} (hu : 1 ≤ u) (he : e ≤ 0) :
    ‖((u ^ e : ℝ) : ℂ)‖ ≤ 1 := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0 _)]
  simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hu he

/-- Only the dual remainder on the support of the taper is needed. -/
theorem norm_integral_window_dualLeft_le_local {d c x p q η M : ℝ}
    (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hc : 0 < c) (hx : 0 < x)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (p - η) (q + η), ‖dualLeft d c x t‖ ≤ M) :
    ‖∫ t, blockWindowC p q η t * dualLeft d c x t‖ ≤ (q - p + 2 * η) * M := by
  have hsub : Icc (p - η) (q + η) ⊆ Icc (-(q + η)) (q + η) := by
    intro t ht
    exact ⟨by linarith only [hL, hpq, hη, ht.1], ht.2⟩
  have hint : Integrable (fun t => blockWindowC p q η t * dualLeft d c x t) :=
    integrable_window_mul hη ((continuousOn_dualLeft hd hd8 hc hx (q + η)).mono hsub)
  have hpt : ∀ t, ‖blockWindowC p q η t * dualLeft d c x t‖ ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Icc (p - η) (q + η)
    · exact mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  calc
    _ ≤ ∫ t, ‖blockWindowC p q η t * dualLeft d c x t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
      integral_mono hint.norm ((HTGeometry.integrable_blockWindowC hη).norm.mul_const M) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM

/-- The pair decomposition needs only local bounds for its three remainders.
All coefficient prefactors are at most one. -/
theorem norm_pairError_le_components {d x p q η Ms Md Mr : ℝ}
    (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hx : 0 < x) (hη : 0 < η)
    (hL : 4 ≤ p - η) (hpq : p ≤ q)
    {g h' k' h k : ℕ} (hg : 0 < g) (hh' : 0 < h') (hk' : 0 < k')
    (hhg : h = g * h') (hkg : k = g * k')
    (hMs : 0 ≤ Ms) (hMd : 0 ≤ Md)
    (hs : ‖smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x‖ ≤ Ms)
    (hi : ‖∫ t, blockWindowC p q η t * dualLeft d ((h' * k' : ℕ) : ℝ) x t‖ ≤
      (q - p + 2 * η) * Md)
    (hr : ‖residueTerm d x p q η h k‖ ≤ (q - p + 2 * η) * Mr) :
    ‖pairError d x p q η h' k' h k‖ ≤
      (∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P) +
      (∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P) +
      (q - p + 2 * η) * (Ms + Md + Mr) := by
  have hd4 : d ≤ 1 / 4 := by linarith only [hd8]
  have hh : 0 < h := by rw [hhg]; positivity
  have hk : 0 < k := by rw [hkg]; positivity
  have hhk : (1 : ℝ) ≤ (h : ℝ) * k := by exact_mod_cast Nat.mul_pos hh hk
  have hc : (1 : ℝ) ≤ ((h' * k' : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hh' hk'
  have hlen : 0 ≤ q - p + 2 * η := by linarith only [hpq, hη]
  have hA := norm_real_rpow_le_one hhk (show -(1 / 2 - d) ≤ 0 by linarith only [hd8])
  have hB := norm_real_rpow_le_one hc (show -(1 / 2 - d) ≤ 0 by linarith only [hd8])
  have hD := norm_real_rpow_le_one hc (show -(1 / 2 + d) ≤ 0 by linarith only [hd])
  have e1 := norm_tsum_compl_directTerm_le hd hd4 hx hη hpq hg hhg hkg hh hk
  have e2 := norm_tsum_compl_dualTerm_le hd hd4 hx hη hL hpq hg hhg hkg hh hk
  have e3 : ‖((((h : ℝ) * k) ^ (-(1 / 2 - d)) : ℝ) : ℂ) *
      (((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 - d)) : ℝ) : ℂ) *
          smoothLeft (1 / 2 - d) ((h' * k' : ℕ) : ℝ) x * (∫ t, blockWindowC p q η t) +
        ((((h' * k' : ℕ) : ℝ) ^ (-(1 / 2 + d)) : ℝ) : ℂ) *
          ∫ t, blockWindowC p q η t * dualLeft d ((h' * k' : ℕ) : ℝ) x t)‖ ≤
      (q - p + 2 * η) * (Ms + Md) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * (1 * Ms * (q - p + 2 * η) + 1 * ((q - p + 2 * η) * Md)) := by
        apply mul_le_mul hA _ (norm_nonneg _) zero_le_one
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul hB hs (norm_nonneg _) zero_le_one)
            (norm_integral_blockWindowC_le hη hpq) (norm_nonneg _) (by simpa using hMs)
        · rw [norm_mul]
          exact mul_le_mul hD hi (norm_nonneg _) zero_le_one
      _ = _ := by ring
  have hnorm (z₁ z₂ z₃ z₄ : ℂ) :
      ‖z₁ + z₂ + z₃ - z₄‖ ≤ ‖z₁‖ + ‖z₂‖ + ‖z₃‖ + ‖z₄‖ :=
    (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  unfold pairError
  refine (hnorm _ _ _ _).trans ?_
  calc
    _ ≤ ((∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) x p q η h k P) +
        (∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P)) +
        (q - p + 2 * η) * (Ms + Md) + (q - p + 2 * η) * Mr :=
      add_le_add (add_le_add (add_le_add e1 e2) e3) hr
    _ = _ := by ring

/-- Every pair of coefficients below square-root length has an arbitrarily
small power remainder on a suitable sublinear taper. No analytic remainder
estimate occurs among the hypotheses. -/
theorem exists_pairError_power_saving {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (B : ℝ) :
    ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (d q : ℝ) (h k : ℕ), T ≤ q → q ≤ 2 * T → 0 < d → d ≤ 1 / 20 →
        0 < h → 0 < k → (h : ℝ) ≤ T ^ θ → (k : ℝ) ≤ T ^ θ →
        ‖pairError d T T q (T ^ a) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖ ≤
          (q - T + 2 * T ^ a) * C * T ^ (-B) := by
  let a : ℝ := 3 / 4 + θ / 2
  let b : ℝ := 1 / 4 - θ / 2
  have ha0 : 0 < a := by dsimp only [a]; linarith only [hθ0]
  have ha1 : a < 1 := by dsimp only [a]; linarith only [hθ]
  have hb : 0 < b := by dsimp only [b]; linarith only [hθ]
  have hb1 : b < 1 := by dsimp only [b]; linarith only [hθ0]
  have hab : a + b ≤ 1 := by dsimp only [a, b]; linarith
  have hgap : 1 / 2 + θ + b / 2 < a := by dsimp only [a, b]; linarith only [hθ]
  have hgap' : 1 / 2 + θ < a := by linarith only [hgap, hb]
  obtain ⟨Cd, hCd, hdir⟩ := exists_directOffDiag_power_saving hgap' B
  obtain ⟨Cu, hCu, hdual⟩ := exists_dualOffDiag_power_saving hb hb1 ha1 hab hgap B
  obtain ⟨Cs, Cv, hCs, hCv, hcontour⟩ := exists_contour_power_saving hθ B
  refine ⟨a, Cd + Cu + Cs + Cv + 18 * Real.exp 1, ha0, ha1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_rpow_le_quarter ha1,
    hdual, eventually_gaussian_split_le_rpow (by norm_num : (0 : ℝ) < 1 / 2) (B + 1)]
    with T hT hη hdualT hgauss
  intro d q h k hq hq2 hd hd20 hh hk hhT hkT
  have hT0 : 0 < T := by linarith only [hT]
  have hT1 : 1 ≤ T := by linarith only [hT]
  have hd8 : d ≤ 1 / 8 := by linarith only [hd20]
  have hη0 : 0 < T ^ a := Real.rpow_pos_of_pos hT0 _
  have hL : 4 ≤ T - T ^ a := by linarith only [hT, hη]
  have hlen : 0 ≤ q - T + 2 * T ^ a := by linarith only [hq, hη0]
  have hpow0 : 0 ≤ T ^ (-B) := Real.rpow_nonneg hT0.le _
  obtain ⟨hg, hh', hk', _, hhg, hkg⟩ := gcd_facts hh hk
  have hc1 : (1 : ℝ) ≤ (((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hh' hk'
  have hcT : ((((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) : ℝ)) ≤ T ^ (2 * θ) := by
    calc
      _ ≤ (h : ℝ) * k := by exact_mod_cast Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.div_le_self _ _)
      _ ≤ T ^ θ * T ^ θ := mul_le_mul hhT hkT (Nat.cast_nonneg _) (Real.rpow_nonneg hT0.le _)
      _ = _ := by rw [← Real.rpow_add hT0]; congr 1; ring
  obtain ⟨hsmooth, hcont⟩ := hcontour T _ d hT hc1 hcT hd hd20
  have hint := norm_integral_window_dualLeft_le_local hd hd8
    (lt_of_lt_of_le zero_lt_one hc1) hT0 hη0 hL hq (mul_nonneg hCv hpow0)
    (fun t ht => hcont t (by linarith only [ht.1, hη, hT0, le_abs_self t]))
  have hres : ‖residueTerm d T T q (T ^ a) h k‖ ≤
      (q - T + 2 * T ^ a) * (18 * Real.exp 1 * T ^ (-B)) := by
    have hpref : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := by
      have hhk : (1 : ℝ) ≤ (h : ℝ) * k := by exact_mod_cast Nat.mul_pos hh hk
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hhk
        (show -(1 / 2 - d) ≤ 0 by linarith only [hd20])
    have hsquare : ((T ^ ((1 : ℝ) / 2)) ^ 2) / 2 ≤ (T - T ^ a) ^ 2 := by
      have he : (T ^ ((1 : ℝ) / 2)) ^ 2 = T := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        norm_num
      rw [he]
      nlinarith only [hT, hη, sq_nonneg (T - T ^ a - T / 2)]
    have he : Real.exp (-((T - T ^ a) ^ 2)) ≤ T ^ (-(B + 1)) :=
      (Real.exp_le_exp.mpr (by linarith only [hsquare])).trans hgauss
    have halg : T * T ^ (-(B + 1)) = T ^ (-B) := by
      calc
        _ = T ^ (1 : ℝ) * T ^ (-(B + 1)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hT0]; congr 1; ring
    refine (norm_residueTerm_le hd (by linarith only [hd20]) hT1 hη0 hL hq hh hk).trans ?_
    calc
      _ ≤ (q - T + 2 * T ^ a) * (1 * (18 * Real.exp 1 * T * T ^ (-(B + 1)))) := by
        apply mul_le_mul_of_nonneg_left _ hlen
        exact mul_le_mul hpref (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity) zero_le_one
      _ = _ := by rw [one_mul, mul_assoc (18 * Real.exp 1), halg]
  have herr := norm_pairError_le_components hd hd8 hT0 hη0 hL hq hg hh' hk' hhg hkg
    (mul_nonneg hCs hpow0) (mul_nonneg hCv hpow0) hsmooth hint hres
  have hdirect := hdir T d T q h k hT1 hd hd8 hq hh hk hhT hkT
  have hdu := hdualT d q h k hq hq2 hd hd8 hh hk hhT hkT
  refine herr.trans ?_
  calc
    _ ≤ (q - T + 2 * T ^ a) * Cd * T ^ (-B) +
        (q - T + 2 * T ^ a) * Cu * T ^ (-B) +
        (q - T + 2 * T ^ a) * (Cs * T ^ (-B) + Cv * T ^ (-B) + 18 * Real.exp 1 * T ^ (-B)) :=
      add_le_add (add_le_add hdirect hdu) le_rfl
    _ = _ := by ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField

#print axioms GaloisForLFunctions.MultiscaleMollifiedZetaField.exists_pairError_power_saving
