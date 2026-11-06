import GaloisForLFunctions.BlackHoleRingdown.TheSharpBoundsOfTheEisensteinFunction

/-!
# Polynomial growth of the Eisenstein function

`ξ(s) = O((1+|Im s|)^N e^{-π|Im s|/4})` on vertical strips, from the sharp decay of `Γ` and the crude bound
for `ζ`. With the sharp tail bounds this gives, on `-A ≤ Re u ≤ c`, `|Im u| ≥ 1`,

`‖jet of E(u; x, Y)‖ ≤ C (1+|Im u|)^M (1 + e^{-π|Im u|/2} ‖1/ξ(1+2u)‖)`.

The last factor is polynomially bounded wherever `1/ζ(1+2u)` is: on `Re u = 0`, on `Re u ≥ ½`, on the left
of the strip, and at the good heights. So `E` and its jets grow polynomially on the lines and edges that the
contour arguments use.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### Sharp decay of `ξ` -/

/-- Sharp decay of `ξ` on the right of the critical line. -/
theorem exists_norm_xi_sharp_right (β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ β → 2 ≤ |s.im| →
      ‖xi s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im| / 4)) := by
  obtain ⟨C₁, N₁, hC₁, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip (1 / 4) (β / 2)
  refine ⟨4 * (2 + |β|) ^ 2 * C₁, N₁ + 3, by positivity, fun s h1 h2 h3 => ?_⟩
  set t := s.im with ht
  have him : t ≠ 0 := fun h => by
    rw [h, abs_zero] at h3
    norm_num at h3
  have hpi := Real.pi_pos
  set p := 1 + |t| with hp
  have hp1 : 1 ≤ p := by
    rw [hp]
    linarith [abs_nonneg t]
  have hβ : 0 ≤ |β| := abs_nonneg β
  have hβ' : β ≤ |β| := le_abs_self β
  have hre0 : 0 ≤ s.re := by linarith
  have hnorm : ‖s‖ ≤ (1 + |β|) * p := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_nonneg hre0, hp]
    nlinarith [abs_nonneg t]
  have hnorm1 : ‖s - 1‖ ≤ (2 + |β|) * p := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    nlinarith
  have hkin : ‖s * (s - 1) / 2‖ ≤ (2 + |β|) ^ 2 * p ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_ofNat]
    have h4 : ‖s‖ * ‖s - 1‖ ≤ ((2 + |β|) * p) * ((2 + |β|) * p) := by
      refine mul_le_mul (hnorm.trans ?_) hnorm1 (norm_nonneg _) (by positivity)
      nlinarith
    have h5 : 0 ≤ ‖s‖ * ‖s - 1‖ := by positivity
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg (by positivity : 0 ≤ (2 + |β|) ^ 2) (by positivity : 0 ≤ p ^ 2)]
  have hre : (s / 2).re = s.re / 2 := by simp
  have him2 : (s / 2).im = t / 2 := by simp [ht]
  have habs : |(s / 2).im| = |t| / 2 := by
    rw [him2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hG := hΓ (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [habs]; linarith)
  rw [habs] at hG
  have hhalf : |t| / 2 ≤ p := by
    rw [hp]
    linarith [abs_nonneg t]
  have hGam : ‖Complex.Gamma (s / 2)‖ ≤ C₁ * p ^ N₁ * Real.exp (-(Real.pi * |t| / 4)) := by
    refine hG.trans ?_
    have hexp : Real.exp (-(Real.pi * (|t| / 2) / 2)) = Real.exp (-(Real.pi * |t| / 4)) := by
      congr 1
      ring
    rw [hexp]
    gcongr
  have hpow : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    have : (-s / 2).re = -(s.re / 2) := by
      simp
      ring
    rw [this]
    linarith
  have hGR : ‖Complex.Gammaℝ s‖ ≤ C₁ * p ^ N₁ * Real.exp (-(Real.pi * |t| / 4)) := by
    rw [Complex.Gammaℝ_def, norm_mul]
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ ≤ 1 * ‖Complex.Gamma (s / 2)‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hGam
  have hz : ‖riemannZeta s‖ ≤ 4 * p := by
    have h := norm_riemannZeta_le_of_half_le_re (σ := s.re) (y := t) h1 h3
    rw [ht, Complex.re_add_im s] at h
    refine h.trans ?_
    rw [hp]
    linarith
  rw [xi_eq_factor him, norm_mul, norm_mul]
  calc ‖s * (s - 1) / 2‖ * (‖Complex.Gammaℝ s‖ * ‖riemannZeta s‖)
      ≤ ((2 + |β|) ^ 2 * p ^ 2) * ((C₁ * p ^ N₁ * Real.exp (-(Real.pi * |t| / 4))) * (4 * p)) :=
        mul_le_mul hkin (mul_le_mul hGR hz (norm_nonneg _) (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by ring

/-- **Sharp decay of `ξ` on vertical strips.** -/
theorem exists_norm_xi_sharp (α β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, α ≤ s.re → s.re ≤ β → 2 ≤ |s.im| →
      ‖xi s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im| / 4)) := by
  obtain ⟨C, N, hC, h⟩ := exists_norm_xi_sharp_right (max β (1 - α))
  refine ⟨C, N, hC, fun s h1 h2 h3 => ?_⟩
  rcases le_total (1 / 2) s.re with hs | hs
  · exact h s hs (h2.trans (le_max_left _ _)) h3
  · have hre : (1 - s).re = 1 - s.re := by simp
    have him : |(1 - s).im| = |s.im| := by simp
    have hm := h (1 - s) (by rw [hre]; linarith)
      (by rw [hre]; exact le_trans (by linarith) (le_max_right _ _)) (by rw [him]; exact h3)
    rw [xi_one_sub, him] at hm
    exact hm

/-! ### The jets on strips -/

/-- The elementary inequality that assembles a jet from its three parts. -/
theorem jet_assemble {A₀ K₁ K₂ p e : ℝ} {N₁ N₂ M : ℕ} (hA₀ : 0 ≤ A₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hp : 1 ≤ p) (he : 0 ≤ e) (h1 : 2 + N₁ ≤ M) (h2 : N₂ ≤ M) :
    A₀ * p ^ 2 + A₀ * p ^ 2 * (K₁ * p ^ N₁ * e) + K₂ * p ^ N₂ * e ≤
      (A₀ + A₀ * K₁ + K₂) * p ^ M * (1 + e) := by
  have hp0 : 0 ≤ p := by linarith
  set q := p ^ M with hq
  have hq0 : 0 ≤ q := by positivity
  have h3 : p ^ 2 ≤ q := pow_le_pow_right₀ hp (by omega)
  have h4 : p ^ 2 * p ^ N₁ ≤ q := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hp h1
  have h5 : p ^ N₂ ≤ q := pow_le_pow_right₀ hp h2
  have t1 : A₀ * p ^ 2 ≤ A₀ * q := mul_le_mul_of_nonneg_left h3 hA₀
  have t2 : A₀ * p ^ 2 * (K₁ * p ^ N₁ * e) ≤ A₀ * K₁ * q * e := by
    calc A₀ * p ^ 2 * (K₁ * p ^ N₁ * e) = A₀ * K₁ * (p ^ 2 * p ^ N₁) * e := by ring
      _ ≤ A₀ * K₁ * q * e := by gcongr
  have t3 : K₂ * p ^ N₂ * e ≤ K₂ * q * e := by gcongr
  have hrest : 0 ≤ A₀ * q * e + A₀ * K₁ * q + K₂ * q := by positivity
  nlinarith

/-- A jet with its three parts: a power, the scattered power, and the tail. -/
theorem norm_jet_le {a b ψ χt : ℂ} {α Ψ X : ℝ} (ha : ‖a‖ ≤ α) (hb : ‖b‖ ≤ α) (hψ : ‖ψ‖ ≤ Ψ)
    (hχ : ‖χt‖ ≤ X) (hα : 0 ≤ α) : ‖a + ψ * b + χt‖ ≤ α + α * Ψ + X := by
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans hψ
  refine (norm_add₃_le).trans ?_
  rw [norm_mul]
  have : ‖ψ‖ * ‖b‖ ≤ α * Ψ := by
    rw [mul_comm]
    exact mul_le_mul hb hψ (norm_nonneg _) hα
  linarith

/-- The weight in the strip bound. -/
def stripWeight (C : ℝ) (M : ℕ) (u : ℂ) : ℝ :=
  C * (1 + |u.im|) ^ M * (1 + Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖)

section Strip

variable {Y₀ A c B P Kt G p e : ℝ}

theorem norm_one_add_two_mul_le {u : ℂ} (hB : |u.re| ≤ B) (hB0 : 0 ≤ B) :
    ‖1 + 2 * u‖ ≤ 2 * (1 + B) * (1 + |u.im|) ∧ ‖2 * u‖ ≤ 2 * (1 + B) * (1 + |u.im|) ∧
      ‖1 / 2 + u‖ ≤ (1 + B) * (1 + |u.im|) ∧ ‖1 / 2 - u‖ ≤ (1 + B) * (1 + |u.im|) ∧
      ‖1 / 2 + u - 1‖ ≤ (1 + B) * (1 + |u.im|) ∧ ‖1 / 2 - u - 1‖ ≤ (1 + B) * (1 + |u.im|) := by
  have hT := abs_nonneg u.im
  have hn : ‖u‖ ≤ B + |u.im| := (Complex.norm_le_abs_re_add_abs_im u).trans (by linarith)
  have hBT : 0 ≤ B * |u.im| := mul_nonneg hB0 hT
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have h1 : ‖1 + 2 * u‖ ≤ 1 + 2 * ‖u‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_ofNat]
  have h2 : ‖2 * u‖ = 2 * ‖u‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h3 : ‖1 / 2 + u‖ ≤ 1 / 2 + ‖u‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [hhalf]
  have h4 : ‖1 / 2 - u‖ ≤ 1 / 2 + ‖u‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [hhalf]
  have h5 : ‖1 / 2 + u - 1‖ ≤ 1 / 2 + ‖u‖ := by
    have e1 : (1 / 2 + u - 1 : ℂ) = -(1 / 2 - u) := by ring
    rw [e1, norm_neg]
    exact h4
  have h6 : ‖1 / 2 - u - 1‖ ≤ 1 / 2 + ‖u‖ := by
    have e1 : (1 / 2 - u - 1 : ℂ) = -(1 / 2 + u) := by ring
    rw [e1, norm_neg]
    exact h3
  refine ⟨h1.trans ?_, h2.le.trans ?_, h3.trans ?_, h4.trans ?_, h5.trans ?_, h6.trans ?_⟩ <;>
    nlinarith

/-- `‖Y^w‖` on a window, for `Re w` in a bounded range. -/
theorem norm_cpow_window_le (hY₀ : 0 < Y₀) {R Y : ℝ} (hR : 1 / 2 ≤ R)
    (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) (w : ℂ) (h1 : 1 / 2 - R ≤ w.re) (h2 : w.re ≤ 1 / 2 + R) :
    ‖(Y : ℂ) ^ w‖ ≤ (2 * Y₀) ^ (1 / 2 + R) + (Y₀ / 2) ^ (1 / 2 - R) := by
  have hYpos := window_pos hY₀ hY
  have hl : 0 < Y₀ / 2 := by positivity
  refine (norm_cpow_strip_le hYpos w h1 h2).trans (add_le_add ?_ ?_)
  · exact Real.rpow_le_rpow hYpos.le hY.2 (by linarith)
  · exact Real.rpow_le_rpow_of_nonpos hl hY.1 (by linarith)

end Strip

theorem norm_scatteringPhase_strip {u : ℂ} {D Z : ℝ} (hD : 0 ≤ D) (hden : 1 ≤ ‖2 * u - 1‖)
    (n1 : ‖1 + 2 * u‖ ≤ 2 * D) (hxi : ‖xi (2 * u)‖ ≤ Z) :
    ‖scatteringPhase u‖ ≤ 2 * D * (Z * ‖(xi (1 + 2 * u))⁻¹‖) := by
  have hq : ‖(1 + 2 * u) / (2 * u - 1)‖ ≤ 2 * D := by
    rw [norm_div]
    exact div_le_of_le_mul₀ (norm_nonneg _) (by positivity)
      (n1.trans (le_mul_of_one_le_right (by positivity) hden))
  rw [scatteringPhase, norm_mul, div_eq_mul_inv (xi (2 * u)), norm_mul]
  exact mul_le_mul hq (mul_le_mul_of_nonneg_right hxi (norm_nonneg _)) (by positivity)
    (by positivity)

theorem norm_tailWeight_mul_le {u t : ℂ} {D b : ℝ} (hD : 0 ≤ D) (n1 : ‖1 + 2 * u‖ ≤ 2 * D)
    (n2 : ‖2 * u‖ ≤ 2 * D) (hb : ‖t‖ ≤ b) :
    ‖tailWeight u * t‖ ≤ 2 * D * (2 * D) * ‖(xi (1 + 2 * u))⁻¹‖ * b := by
  rw [tailWeight, norm_mul, div_eq_mul_inv, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul n1 n2 (norm_nonneg _) (by positivity))
    (norm_nonneg _)) hb (norm_nonneg _) (by positivity)

/-- The jets from their parts. -/
theorem jets_of_parts {u : ℂ} {x Y D P Ψ X : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P)
    (n3 : ‖1 / 2 + u‖ ≤ D) (n4 : ‖1 / 2 - u‖ ≤ D) (n5 : ‖1 / 2 + u - 1‖ ≤ D)
    (n6 : ‖1 / 2 - u - 1‖ ≤ D)
    (pA : ‖(Y : ℂ) ^ (1 / 2 + u)‖ ≤ P) (pB : ‖(Y : ℂ) ^ (1 / 2 - u)‖ ≤ P)
    (pA1 : ‖(Y : ℂ) ^ (1 / 2 + u - 1)‖ ≤ P) (pB1 : ‖(Y : ℂ) ^ (1 / 2 - u - 1)‖ ≤ P)
    (pA2 : ‖(Y : ℂ) ^ (1 / 2 + u - 1 - 1)‖ ≤ P) (pB2 : ‖(Y : ℂ) ^ (1 / 2 - u - 1 - 1)‖ ≤ P)
    (hψ : ‖scatteringPhase u‖ ≤ Ψ)
    (t0 : ‖tailWeight u * eisTail u x Y‖ ≤ X) (tX : ‖tailWeight u * eisTailX u x Y‖ ≤ X)
    (tXX : ‖tailWeight u * eisTailXX u x Y‖ ≤ X) (tY : ‖tailWeight u * eisTailY u x Y‖ ≤ X)
    (tYY : ‖tailWeight u * eisTailYY u x Y‖ ≤ X) :
    ‖normalizedEisenstein u x Y‖ ≤ D ^ 2 * P + D ^ 2 * P * Ψ + X ∧
      ‖eisensteinX u x Y‖ ≤ D ^ 2 * P + D ^ 2 * P * Ψ + X ∧
      ‖eisensteinXX u x Y‖ ≤ D ^ 2 * P + D ^ 2 * P * Ψ + X ∧
      ‖eisensteinY u x Y‖ ≤ D ^ 2 * P + D ^ 2 * P * Ψ + X ∧
      ‖eisensteinYY u x Y‖ ≤ D ^ 2 * P + D ^ 2 * P * Ψ + X := by
  have hD0 : 0 ≤ D := by linarith
  have hsq : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have hα : 0 ≤ D ^ 2 * P := by positivity
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans hψ
  have hP1 : P ≤ D ^ 2 * P := le_mul_of_one_le_left hP hsq
  have hone : ∀ {a b : ℂ}, ‖a‖ ≤ D → ‖b‖ ≤ P → ‖a * b‖ ≤ D ^ 2 * P := by
    intro a b ha hb
    rw [norm_mul]
    have h : ‖a‖ * ‖b‖ ≤ D * P := mul_le_mul ha hb (norm_nonneg _) hD0
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hP)
    nlinarith
  have htwo : ∀ {a a' b : ℂ}, ‖a‖ ≤ D → ‖a'‖ ≤ D → ‖b‖ ≤ P → ‖a * (a' * b)‖ ≤ D ^ 2 * P := by
    intro a a' b ha ha' hb
    rw [norm_mul, norm_mul]
    have h : ‖a‖ * (‖a'‖ * ‖b‖) ≤ D * (D * P) :=
      mul_le_mul ha (mul_le_mul ha' hb (norm_nonneg _) hD0) (by positivity) hD0
    refine h.trans (le_of_eq ?_)
    ring
  have hX : ∀ {z : ℂ}, ‖z‖ ≤ X → ‖z‖ ≤ D ^ 2 * P + D ^ 2 * P * Ψ + X := by
    intro z hz
    have : 0 ≤ D ^ 2 * P * Ψ := by positivity
    linarith
  exact ⟨norm_jet_le (pA.trans hP1) (pB.trans hP1) hψ t0 hα, hX tX, hX tXX,
    norm_jet_le (hone n3 pA1) (hone n4 pB1) hψ tY hα,
    norm_jet_le (htwo n3 n5 pA2) (htwo n4 n6 pB2) hψ tYY hα⟩

/-- The tail jets, doubled. -/
theorem eisTail_jets_le {u : ℂ} {x Y b : ℝ}
    (h₁ : ‖weightedTail u false x Y‖ ≤ b ∧ ‖weightedTailX u false x Y‖ ≤ b ∧
      ‖weightedTailXX u false x Y‖ ≤ b ∧ ‖weightedTailY u false x Y‖ ≤ b ∧
      ‖weightedTailYY u false x Y‖ ≤ b)
    (h₂ : ‖weightedTail u true x Y‖ ≤ b ∧ ‖weightedTailX u true x Y‖ ≤ b ∧
      ‖weightedTailXX u true x Y‖ ≤ b ∧ ‖weightedTailY u true x Y‖ ≤ b ∧
      ‖weightedTailYY u true x Y‖ ≤ b) :
    ‖eisTail u x Y‖ ≤ 2 * b ∧ ‖eisTailX u x Y‖ ≤ 2 * b ∧ ‖eisTailXX u x Y‖ ≤ 2 * b ∧
      ‖eisTailY u x Y‖ ≤ 2 * b ∧ ‖eisTailYY u x Y‖ ≤ 2 * b := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine (norm_add_le _ _).trans ?_ <;> linarith

/-- The powers of the height that occur in the jets. -/
theorem norm_cpow_jets_le {Y₀ Y : ℝ} (hY₀ : 0 < Y₀) {B : ℝ} (hB : 0 ≤ B)
    (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) {u : ℂ} (hu : |u.re| ≤ B) :
    ‖(Y : ℂ) ^ (1 / 2 + u)‖ ≤ (2 * Y₀) ^ (1 / 2 + (2 + B)) + (Y₀ / 2) ^ (1 / 2 - (2 + B)) ∧
      ‖(Y : ℂ) ^ (1 / 2 - u)‖ ≤ (2 * Y₀) ^ (1 / 2 + (2 + B)) + (Y₀ / 2) ^ (1 / 2 - (2 + B)) ∧
      ‖(Y : ℂ) ^ (1 / 2 + u - 1)‖ ≤ (2 * Y₀) ^ (1 / 2 + (2 + B)) + (Y₀ / 2) ^ (1 / 2 - (2 + B)) ∧
      ‖(Y : ℂ) ^ (1 / 2 - u - 1)‖ ≤ (2 * Y₀) ^ (1 / 2 + (2 + B)) + (Y₀ / 2) ^ (1 / 2 - (2 + B)) ∧
      ‖(Y : ℂ) ^ (1 / 2 + u - 1 - 1)‖ ≤ (2 * Y₀) ^ (1 / 2 + (2 + B)) + (Y₀ / 2) ^ (1 / 2 - (2 + B)) ∧
      ‖(Y : ℂ) ^ (1 / 2 - u - 1 - 1)‖ ≤ (2 * Y₀) ^ (1 / 2 + (2 + B)) + (Y₀ / 2) ^ (1 / 2 - (2 + B)) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hu
  have hR : (1 / 2 : ℝ) ≤ 2 + B := by linarith
  have hgo := fun w h₁ h₂ => norm_cpow_window_le hY₀ hR hY w h₁ h₂
  have r1 : (1 / 2 + u).re = 1 / 2 + u.re := by simp
  have r2 : (1 / 2 - u).re = 1 / 2 - u.re := by simp
  have r3 : (1 / 2 + u - 1).re = 1 / 2 + u.re - 1 := by simp
  have r4 : (1 / 2 - u - 1).re = 1 / 2 - u.re - 1 := by simp
  have r5 : (1 / 2 + u - 1 - 1).re = 1 / 2 + u.re - 1 - 1 := by simp
  have r6 : (1 / 2 - u - 1 - 1).re = 1 / 2 - u.re - 1 - 1 := by simp
  exact ⟨hgo _ (by rw [r1]; linarith) (by rw [r1]; linarith),
    hgo _ (by rw [r2]; linarith) (by rw [r2]; linarith),
    hgo _ (by rw [r3]; linarith) (by rw [r3]; linarith),
    hgo _ (by rw [r4]; linarith) (by rw [r4]; linarith),
    hgo _ (by rw [r5]; linarith) (by rw [r5]; linarith),
    hgo _ (by rw [r6]; linarith) (by rw [r6]; linarith)⟩

/-- The bound for `ξ(2u)` at the scale of `u`. -/
theorem norm_xi_two_mul_strip_le {Cξ : ℝ} {Nξ : ℕ} {α β : ℝ} (hCξ : 0 ≤ Cξ)
    (hξ : ∀ s : ℂ, α ≤ s.re → s.re ≤ β → 2 ≤ |s.im| →
      ‖xi s‖ ≤ Cξ * (1 + |s.im|) ^ Nξ * Real.exp (-(Real.pi * |s.im| / 4)))
    {u : ℂ} (h1 : α ≤ 2 * u.re) (h2 : 2 * u.re ≤ β) (h3 : 1 ≤ |u.im|) :
    ‖xi (2 * u)‖ ≤ Cξ * 2 ^ Nξ * (1 + |u.im|) ^ Nξ * Real.exp (-(Real.pi * |u.im| / 2)) := by
  have him : |(2 * u).im| = 2 * |u.im| := by
    have : (2 * u).im = 2 * u.im := by simp
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hre : (2 * u).re = 2 * u.re := by simp
  have h := hξ (2 * u) (by rw [hre]; exact h1) (by rw [hre]; exact h2) (by rw [him]; linarith)
  rw [him] at h
  have hexp : Real.exp (-(Real.pi * (2 * |u.im|) / 4)) = Real.exp (-(Real.pi * |u.im| / 2)) := by
    congr 1
    ring
  rw [hexp] at h
  have hT := abs_nonneg u.im
  have h1T : (1 + 2 * |u.im|) ^ Nξ ≤ 2 ^ Nξ * (1 + |u.im|) ^ Nξ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) Nξ
  refine h.trans ?_
  calc Cξ * (1 + 2 * |u.im|) ^ Nξ * Real.exp (-(Real.pi * |u.im| / 2))
      ≤ Cξ * (2 ^ Nξ * (1 + |u.im|) ^ Nξ) * Real.exp (-(Real.pi * |u.im| / 2)) := by gcongr
    _ = _ := by ring

/-- **The jets of `E` on a strip.** -/
theorem exists_eisenstein_strip_le {Y₀ A c : ℝ} (hY₀ : 0 < Y₀) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ (u : ℂ) (x Y : ℝ), -A ≤ u.re → u.re ≤ c → 1 ≤ |u.im| →
      Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖normalizedEisenstein u x Y‖ ≤ stripWeight C M u ∧ ‖eisensteinX u x Y‖ ≤ stripWeight C M u ∧
        ‖eisensteinXX u x Y‖ ≤ stripWeight C M u ∧ ‖eisensteinY u x Y‖ ≤ stripWeight C M u ∧
        ‖eisensteinYY u x Y‖ ≤ stripWeight C M u := by
  have hB0 : 0 ≤ A + c := by positivity
  obtain ⟨Cξ, Nξ, hCξ, hξ⟩ := exists_norm_xi_sharp (2 * -A) (2 * c)
  obtain ⟨Ct, Mt, hCt, ht⟩ := exists_weightedTail_jets_le_sharp hY₀ hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (2 * Y₀) ^ (1 / 2 + (2 + (A + c))) +
      (Y₀ / 2) ^ (1 / 2 - (2 + (A + c))) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    positivity
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = (1 + (A + c)) ^ 2 * P := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by
    rw [hA₀]
    positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 2 * (1 + (A + c)) * (Cξ * 2 ^ Nξ) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁]
    positivity
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = (2 * (1 + (A + c))) ^ 2 * (2 * Ct) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂]
    positivity
  refine ⟨A₀ + A₀ * K₁ + K₂, 3 + Nξ + (2 + Mt), by positivity, fun u x Y h1 h2 h3 hY => ?_⟩
  have hu : |u.re| ≤ A + c := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := norm_one_add_two_mul_le hu hB0
  obtain ⟨pA, pB, pA1, pB1, pA2, pB2⟩ := norm_cpow_jets_le hY₀ hB0 hY hu
  rw [← hPdef] at pA pB pA1 pB1 pA2 pB2
  have hxi := norm_xi_two_mul_strip_le hCξ hξ (u := u) (by linarith) (by linarith) h3
  have hden : 1 ≤ ‖2 * u - 1‖ := by
    have h := Complex.abs_im_le_norm (2 * u - 1)
    have him : (2 * u - 1).im = 2 * u.im := by simp
    rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  have hT0 := abs_nonneg u.im
  generalize hp : 1 + |u.im| = p at *
  have hp1 : 1 ≤ p := by linarith
  have hD1 : 1 ≤ (1 + (A + c)) * p := by nlinarith
  have hD0 : 0 ≤ (1 + (A + c)) * p := by linarith
  have n1' : ‖1 + 2 * u‖ ≤ 2 * ((1 + (A + c)) * p) := by
    refine n1.trans (le_of_eq ?_)
    ring
  have n2' : ‖2 * u‖ ≤ 2 * ((1 + (A + c)) * p) := by
    refine n2.trans (le_of_eq ?_)
    ring
  have hψ := norm_scatteringPhase_strip hD0 hden n1' hxi
  obtain ⟨t0, tX, tXX, tY, tYY⟩ := eisTail_jets_le (b := Ct * (1 + |u.im|) ^ Mt *
    Real.exp (-(Real.pi * |u.im| / 2))) (ht u false x Y hu hY) (ht u true x Y hu hY)
  rw [hp] at t0 tX tXX tY tYY
  have hmain := jets_of_parts hD1 hP0 n3 n4 n5 n6 pA pB pA1 pB1 pA2 pB2 hψ
    (norm_tailWeight_mul_le hD0 n1' n2' t0) (norm_tailWeight_mul_le hD0 n1' n2' tX)
    (norm_tailWeight_mul_le hD0 n1' n2' tXX) (norm_tailWeight_mul_le hD0 n1' n2' tY)
    (norm_tailWeight_mul_le hD0 n1' n2' tYY)
  rw [stripWeight, hp]
  have he0 : 0 ≤ Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖ := by positivity
  have hassemble := jet_assemble (N₁ := 1 + Nξ) (N₂ := 2 + Mt) (M := 3 + Nξ + (2 + Mt)) hA₀0 hK₁0
    hK₂0 hp1 he0 (by omega) (by omega)
  have hval : ((1 + (A + c)) * p) ^ 2 * P +
      ((1 + (A + c)) * p) ^ 2 * P * (2 * ((1 + (A + c)) * p) * (Cξ * 2 ^ Nξ * p ^ Nξ *
        Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖)) +
      2 * ((1 + (A + c)) * p) * (2 * ((1 + (A + c)) * p)) * ‖(xi (1 + 2 * u))⁻¹‖ *
        (2 * (Ct * p ^ Mt * Real.exp (-(Real.pi * |u.im| / 2)))) =
      A₀ * p ^ 2 + A₀ * p ^ 2 * (K₁ * p ^ (1 + Nξ) *
        (Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖)) +
      K₂ * p ^ (2 + Mt) * (Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖) := by
    rw [hA₀, hK₁, hK₂, pow_add p 1, pow_add p 2]
    ring
  rw [hval] at hmain
  obtain ⟨m0, m1, m2, m3, m4⟩ := hmain
  exact ⟨m0.trans hassemble, m1.trans hassemble, m2.trans hassemble, m3.trans hassemble,
    m4.trans hassemble⟩

/-! ### The weight on lines and edges -/

/-- From `1/ζ` to the weight: `e^{-π|Im u|/2} ‖1/ξ(1+2u)‖` against `‖1/ζ(1+2u)‖`. -/
theorem exists_exp_mul_norm_inv_xi_le (α β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u : ℂ, α ≤ (1 + 2 * u).re → (1 + 2 * u).re ≤ β → 1 ≤ |u.im| →
      Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖ ≤
        C * (1 + |u.im|) ^ N * ‖(riemannZeta (1 + 2 * u))⁻¹‖ := by
  obtain ⟨C, N, hC, h⟩ := exists_norm_inv_xi_le α β
  refine ⟨C * 2 ^ N, N, by positivity, fun u h1 h2 h3 => ?_⟩
  have him : |(1 + 2 * u).im| = 2 * |u.im| := by
    have : (1 + 2 * u).im = 2 * u.im := by simp
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := h (1 + 2 * u) h1 h2 (by rw [him]; linarith)
  rw [him] at hb
  have hT := abs_nonneg u.im
  have hexp : Real.exp (-(Real.pi * |u.im| / 2)) * Real.exp (Real.pi * (2 * |u.im|) / 4) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  have h1T : (1 + 2 * |u.im|) ^ N ≤ 2 ^ N * (1 + |u.im|) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) N
  calc Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖
      ≤ Real.exp (-(Real.pi * |u.im| / 2)) * (C * (1 + 2 * |u.im|) ^ N *
          Real.exp (Real.pi * (2 * |u.im|) / 4) * ‖(riemannZeta (1 + 2 * u))⁻¹‖) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (Real.exp (-(Real.pi * |u.im| / 2)) * Real.exp (Real.pi * (2 * |u.im|) / 4)) *
          (C * (1 + 2 * |u.im|) ^ N * ‖(riemannZeta (1 + 2 * u))⁻¹‖) := by ring
    _ = C * (1 + 2 * |u.im|) ^ N * ‖(riemannZeta (1 + 2 * u))⁻¹‖ := by rw [hexp, one_mul]
    _ ≤ C * (2 ^ N * (1 + |u.im|) ^ N) * ‖(riemannZeta (1 + 2 * u))⁻¹‖ := by gcongr
    _ = _ := by ring

/-- The strip weight against a polynomial bound of the last factor. -/
theorem stripWeight_le_of {C C' : ℝ} {M N : ℕ} {u : ℂ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (h : Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖ ≤ C' * (1 + |u.im|) ^ N) :
    stripWeight C M u ≤ C * (1 + C') * (1 + |u.im|) ^ (M + N) := by
  have hT := abs_nonneg u.im
  have hp1 : 1 ≤ 1 + |u.im| := by linarith
  have hpN : 1 ≤ (1 + |u.im|) ^ N := one_le_pow₀ hp1
  rw [stripWeight, pow_add]
  have h1 : 1 + Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖ ≤
      (1 + C') * (1 + |u.im|) ^ N := by
    have : C' ≤ C' * (1 + |u.im|) ^ N := le_mul_of_one_le_right hC' hpN
    nlinarith
  calc C * (1 + |u.im|) ^ M * (1 + Real.exp (-(Real.pi * |u.im| / 2)) * ‖(xi (1 + 2 * u))⁻¹‖)
      ≤ C * (1 + |u.im|) ^ M * ((1 + C') * (1 + |u.im|) ^ N) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- **Polynomial growth on the line `Re u = 0`.**  All jets of `E(iξ; x, Y)` are `O((1+|ξ|)^M)`,
uniformly in `x` and on a height window. -/
theorem exists_eisenstein_jets_line_le_poly {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ (ξ x Y : ℝ), Y ∈ Icc (Y₀ / 2) (2 * Y₀) →
      ‖normalizedEisenstein ((ξ : ℂ) * I) x Y‖ ≤ C * (1 + |ξ|) ^ M ∧
      ‖eisensteinX ((ξ : ℂ) * I) x Y‖ ≤ C * (1 + |ξ|) ^ M ∧
      ‖eisensteinXX ((ξ : ℂ) * I) x Y‖ ≤ C * (1 + |ξ|) ^ M ∧
      ‖eisensteinY ((ξ : ℂ) * I) x Y‖ ≤ C * (1 + |ξ|) ^ M ∧
      ‖eisensteinYY ((ξ : ℂ) * I) x Y‖ ≤ C * (1 + |ξ|) ^ M := by
  obtain ⟨C₁, M₁, hC₁, hS⟩ := exists_eisenstein_strip_le hY₀ (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  obtain ⟨C₂, N₂, hC₂, hX⟩ := exists_exp_mul_norm_inv_xi_le 1 1
  obtain ⟨K, hK, hZ⟩ := exists_norm_inv_zeta_one_line
  obtain ⟨C₃, hC₃, hG⟩ := exists_eisenstein_jets_le_gaussian hY₀ (c := 1) one_pos
  have hK0 : 0 ≤ K := hK.le
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = C₂ * (K * 2 ^ 11) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by
    rw [hC']
    positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₁ * (1 + C') + C₃ * Real.exp 1 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  refine ⟨D, M₁ + (N₂ + 11), hD0, fun ξ x Y hY => ?_⟩
  have hp1 : 1 ≤ 1 + |ξ| := by linarith [abs_nonneg ξ]
  have hpow : 1 ≤ (1 + |ξ|) ^ (M₁ + (N₂ + 11)) := one_le_pow₀ hp1
  have hbound : ∀ J : ℝ, (J ≤ C₁ * (1 + C') * (1 + |ξ|) ^ (M₁ + (N₂ + 11)) ∨
      J ≤ C₃ * Real.exp 1) → J ≤ D * (1 + |ξ|) ^ (M₁ + (N₂ + 11)) := by
    intro J hJ
    have hA : 0 ≤ C₁ * (1 + C') := by positivity
    have hB : 0 ≤ C₃ * Real.exp 1 := by positivity
    rw [hD, add_mul]
    rcases hJ with h | h
    · have : 0 ≤ C₃ * Real.exp 1 * (1 + |ξ|) ^ (M₁ + (N₂ + 11)) := by positivity
      linarith
    · have h2 : C₃ * Real.exp 1 ≤ C₃ * Real.exp 1 * (1 + |ξ|) ^ (M₁ + (N₂ + 11)) :=
        le_mul_of_one_le_right hB hpow
      have : 0 ≤ C₁ * (1 + C') * (1 + |ξ|) ^ (M₁ + (N₂ + 11)) := by positivity
      linarith
  rcases le_or_gt |ξ| 1 with hsmall | hlarge
  · obtain ⟨g0, g1, g2, g3, g4⟩ := hG ξ x Y hY
    have hE : C₃ * Real.exp (1 * ξ ^ 2) ≤ C₃ * Real.exp 1 := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₃
      have : ξ ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg ξ]
      linarith
    exact ⟨hbound _ (Or.inr (g0.trans hE)), hbound _ (Or.inr (g1.trans hE)),
      hbound _ (Or.inr (g2.trans hE)), hbound _ (Or.inr (g3.trans hE)),
      hbound _ (Or.inr (g4.trans hE))⟩
  · have hre : ((ξ : ℂ) * I).re = 0 := by simp
    have him : ((ξ : ℂ) * I).im = ξ := by simp
    have hsre : (1 + 2 * ((ξ : ℂ) * I)).re = 1 := by simp
    obtain ⟨s0, s1, s2, s3, s4⟩ := hS ((ξ : ℂ) * I) x Y (by rw [hre]; simp) (by rw [hre])
      (by rw [him]; exact hlarge.le) hY
    have hline : (1 + 2 * ((ξ : ℂ) * I)) = 1 + ((2 * ξ : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hlarge
      linarith
    have hz := hZ (2 * ξ) (by simpa using hξ0)
    rw [← hline] at hz
    have habs : |2 * ξ| = 2 * |ξ| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs] at hz
    have hxb := hX ((ξ : ℂ) * I) (by rw [hsre]) (by rw [hsre]) (by rw [him]; exact hlarge.le)
    rw [him] at hxb
    have h1T : (1 + 2 * |ξ|) ^ 11 ≤ 2 ^ 11 * (1 + |ξ|) ^ 11 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg ξ]) 11
    have hweight : Real.exp (-(Real.pi * |((ξ : ℂ) * I).im| / 2)) *
        ‖(xi (1 + 2 * ((ξ : ℂ) * I)))⁻¹‖ ≤ C' * (1 + |((ξ : ℂ) * I).im|) ^ (N₂ + 11) := by
      rw [him]
      refine hxb.trans ?_
      calc C₂ * (1 + |ξ|) ^ N₂ * ‖(riemannZeta (1 + 2 * ((ξ : ℂ) * I)))⁻¹‖
          ≤ C₂ * (1 + |ξ|) ^ N₂ * (K * (2 ^ 11 * (1 + |ξ|) ^ 11)) :=
            mul_le_mul_of_nonneg_left (hz.trans (mul_le_mul_of_nonneg_left h1T hK0)) (by positivity)
        _ = _ := by
            rw [hC', pow_add]
            ring
    have hsw := stripWeight_le_of (M := M₁) hC₁ hC'0 hweight
    rw [him] at hsw
    exact ⟨hbound _ (Or.inl (s0.trans hsw)), hbound _ (Or.inl (s1.trans hsw)),
      hbound _ (Or.inl (s2.trans hsw)), hbound _ (Or.inl (s3.trans hsw)),
      hbound _ (Or.inl (s4.trans hsw))⟩

end GaloisForLFunctions.BlackHoleRingdown

end
