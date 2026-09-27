import GaloisForLFunctions.RHTower.MobiusAbelPrefixGramIntegral

/-!
# Cubic Möbius prime insertion: the first-jet amplification law

The literal insertion `D_q = I - U_q`, `U_q F(t) = q² F(q t)`, acts on source atoms as
`D_q f_x = f_x - f_(q x)`.  On a near-collision dipole `f_(x+h) - f_x` it amplifies the first
jet: at `δ = 0`,

`‖D_q f_(x+h) - D_q f_x‖² / ‖f_(x+h) - f_x‖² → R_q = 1 + 1/q - 256 q² (-q²+3q-1)/(q+1)^7`,

with `R_2 = 4513/4374`, `R_3 = 283/192`, and `R_q > 1 + 1/q` for `q ≥ 3`, whereas the zero jet
(single atom mass) is contracted.  On the first-jet profiles `v_x = x ∂_x f_x` the dilation acts
exactly as `U_2 v_x = v_(2x)`, so a dyadically coherent signed pair telescopes,
`D_2 (v_x + v_(2x)) = v_x - v_(4x)`, and saves more than a fifth of its energy; a prime atom at
half the base scale removes a further third.  Both strict inequalities persist for small `δ > 0`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace RHTower.CubicGamma

/-! ### Mixed Gram values at `δ = 0` -/

private theorem rpow_seven_add_zero (s : ℝ) : s ^ ((7 : ℝ) + 0) = s ^ (7 : ℕ) := by
  rw [add_zero, ← Real.rpow_natCast]; norm_num

private theorem rpow_five_add_zero (s : ℝ) : s ^ ((5 : ℝ) + 0) = s ^ (5 : ℕ) := by
  rw [add_zero, ← Real.rpow_natCast]; norm_num

/-- `G_0(x,y) = 6 x y (3xy - x² - y²) / (x+y)^7`. -/
theorem abelPrefixGramKernel_zero (x y : ℝ) :
    abelPrefixGramKernel 0 x y = 6 * x * y * (3 * x * y - x ^ 2 - y ^ 2) / (x + y) ^ 7 := by
  unfold abelPrefixGramKernel abelPrefixGramNumerator abelPrefixGramCore
  rw [rpow_seven_add_zero]
  ring

/-- `K_0(x,y) = x² y² / (x+y)^5`. -/
theorem sourceKernel_zero (x y : ℝ) : sourceKernel 0 x y = x ^ 2 * y ^ 2 / (x + y) ^ 5 := by
  unfold sourceKernel
  rw [rpow_five_add_zero]

/-- **Cross-scale law** (card equation (3)).
`Γ(5) ⟨∂f_x, ∂f_y⟩_0 = 144 x y (3xy - x² - y²) / (x+y)^7`. -/
theorem gamma_five_mul_gammaInner_atomJet_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.Gamma 5 * gammaInner 0 (atomJet 1 x) (atomJet 1 y) =
      144 * x * y * (3 * x * y - x ^ 2 - y ^ 2) / (x + y) ^ 7 := by
  have h5 : Real.Gamma 5 = 24 := by
    rw [show (5 : ℝ) = (4 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]
  rw [gammaInner_atomJet_one le_rfl hx hy, abelPrefixGramKernel_zero, h5]
  ring

/-! ### The insertion ratio -/

/-- The first-jet insertion ratio `R_q`. -/
def insertionRatio (q : ℝ) : ℝ := 1 + 1 / q - 256 * q ^ 2 * (-q ^ 2 + 3 * q - 1) / (q + 1) ^ 7

theorem insertionRatio_two : insertionRatio 2 = 4513 / 4374 := by
  norm_num [insertionRatio]

theorem insertionRatio_three : insertionRatio 3 = 283 / 192 := by
  norm_num [insertionRatio]

/-- `R_q > 1 + 1/q` for every integer `q ≥ 3`. -/
theorem insertionRatio_gt {q : ℕ} (hq : 3 ≤ q) : 1 + 1 / (q : ℝ) < insertionRatio q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hneg : -(q : ℝ) ^ 2 + 3 * q - 1 < 0 := by nlinarith
  have hpos : 0 < (256 * (q : ℝ) ^ 2) / ((q : ℝ) + 1) ^ 7 := by positivity
  unfold insertionRatio
  have : 256 * (q : ℝ) ^ 2 * (-(q : ℝ) ^ 2 + 3 * q - 1) / ((q : ℝ) + 1) ^ 7 < 0 := by
    rw [mul_div_right_comm]
    exact mul_neg_of_pos_of_neg hpos hneg
  linarith

/-- `R_q > 1` for every integer `q ≥ 2`. -/
theorem one_lt_insertionRatio {q : ℕ} (hq : 2 ≤ q) : 1 < insertionRatio q := by
  rcases Nat.lt_or_ge q 3 with h | h
  · have : q = 2 := by omega
    subst this
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, insertionRatio_two]
    norm_num
  · have h1 := insertionRatio_gt h
    have : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    linarith

/-- The first-jet energy ratio at `δ = 0` is `R_q`, at every scale. -/
theorem gammaEnergy_jet_insertion_ratio {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    gammaEnergy 0 (fun t => atomJet 1 x t - q * atomJet 1 (q * x) t) /
        gammaEnergy 0 (atomJet 1 x) = insertionRatio q := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hqx : 0 < q * x := mul_pos hq hx
  have f1 := gammaFinite_atomJet hδ 1 hx
  have f2 := (gammaFinite_atomJet hδ 1 hqx).smul q
  have g := gammaFinite_atomJet hδ 1 hqx
  rw [gammaEnergy_sub hδ f1 f2, gammaInner_smul_right hδ g f1, gammaEnergy, gammaEnergy,
    gammaInner_smul_left hδ g f2, gammaInner_smul_right hδ g g,
    gammaInner_atomJet_one le_rfl hx hx, gammaInner_atomJet_one le_rfl hx hqx,
    gammaInner_atomJet_one le_rfl hqx hqx, abelPrefixGramKernel_zero,
    abelPrefixGramKernel_zero, abelPrefixGramKernel_zero]
  unfold insertionRatio
  have hq1 : q + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The zero-jet (mass) ratio `‖D_q f_x‖_0² / ‖f_x‖_0² = 1 + 1/q - 64 q² / (1+q)^5`. -/
theorem gammaEnergy_mass_insertion_ratio {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    gammaEnergy 0 (fun t => atom x t - atom (q * x) t) / gammaEnergy 0 (atom x) =
      1 + 1 / q - 64 * q ^ 2 / (1 + q) ^ 5 := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hqx : 0 < q * x := mul_pos hq hx
  rw [gammaEnergy_sub hδ (gammaFinite_atom hδ hx) (gammaFinite_atom hδ hqx), gammaEnergy,
    gammaEnergy, gammaInner_atom hδ hx hx, gammaInner_atom hδ hx hqx, gammaInner_atom hδ hqx hqx,
    sourceKernel_zero, sourceKernel_zero, sourceKernel_zero]
  have hq1 : 1 + q ≠ 0 := by linarith
  field_simp
  ring

theorem mass_insertion_ratio_two : 1 + 1 / (2 : ℝ) - 64 * 2 ^ 2 / (1 + 2) ^ 5 = 217 / 486 := by
  norm_num

theorem mass_insertion_ratio_three : 1 + 1 / (3 : ℝ) - 64 * 3 ^ 2 / (1 + 3) ^ 5 = 37 / 48 := by
  norm_num

/-- At `q = 3` the mass contracts by `11/48` while the first jet is amplified by `91/192`. -/
theorem three_insertion_mass_and_jet :
    1 - (37 / 48 : ℝ) = 11 / 48 ∧ insertionRatio 3 - 1 = 91 / 192 := by
  rw [insertionRatio_three]; norm_num

/-! ### The finite-difference limit -/

/-- The near-collision dipole `f_(x+h) - f_x`. -/
def nearDipole (x h t : ℝ) : ℝ := atom (x + h) t - atom x t

/-- The inserted dipole `D_q f_(x+h) - D_q f_x`. -/
def insertedDipole (q x h t : ℝ) : ℝ :=
  (atom (x + h) t - atom (q * (x + h)) t) - (atom x t - atom (q * x) t)

/-- The insertion-energy ratio of a near-collision dipole. -/
def insertionEnergyRatio (δ q x h : ℝ) : ℝ :=
  gammaEnergy δ (insertedDipole q x h) / gammaEnergy δ (nearDipole x h)

/-- If `‖F_h / h - F‖ → 0` then `‖F_h‖² / h² → ‖F‖²`. -/
theorem tendsto_gammaEnergy_div_sq {δ : ℝ} (hδ : 0 < 5 + δ) {F : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ᶠ h in 𝓝[>] 0, GammaFinite δ (F h)) (hG : GammaFinite δ G)
    (hlim : Tendsto (fun h => gammaNorm δ (fun t => F h t / h - G t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h => gammaEnergy δ (F h) / h ^ 2) (𝓝[>] 0) (𝓝 (gammaEnergy δ G)) := by
  have hFh : ∀ h, GammaFinite δ (F h) → GammaFinite δ (fun t => F h t / h) := fun h hh => by
    simpa [div_eq_mul_inv, mul_comm] using hh.smul h⁻¹
  have hnorm : Tendsto (fun h => gammaNorm δ (fun t => F h t / h)) (𝓝[>] 0)
      (𝓝 (gammaNorm δ G)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hF] with h hh
    rw [Real.norm_eq_abs]
    exact abs_gammaNorm_sub_le hδ (hFh h hh) hG
  have hsq := hnorm.pow 2
  rw [gammaNorm_sq hδ hG] at hsq
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hF] with h hh hfin
  rw [gammaNorm_sq hδ (hFh h hfin)]
  have hh0 : h ≠ 0 := ne_of_gt hh
  have e : (fun t => F h t / h) = fun t => h⁻¹ * F h t := by funext t; ring
  rw [e, gammaEnergy, gammaInner_smul_left hδ hfin (hfin.smul _),
    gammaInner_smul_right hδ hfin hfin, ← gammaEnergy]
  field_simp

private theorem tendsto_taylorRem_div {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun h => gammaNorm δ (fun t => (atom (x + h) t - atom x t) / h - atomJet 1 x t))
      (𝓝[>] 0) (𝓝 0) := by
  have hδ : 0 < 5 + δ := by linarith
  set K := jetConst 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ 2 with hK
  have hmaj : Tendsto (fun h : ℝ => h / 2 * (K * (x + h) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have := ((by fun_prop : Continuous fun h : ℝ => h / 2 * (K * (x + h) ^ 2)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => gammaNorm_nonneg _ _) ?_ hmaj
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (0 : ℝ) < h := hh
  have hrem := gammaNorm_taylorRem_le hδ0 hδ1 2 hx (by linarith : x ≤ x + h)
  have e : (fun t => (atom (x + h) t - atom x t) / h - atomJet 1 x t) =
      fun t => h⁻¹ * taylorRem 2 x (x + h) t := by
    funext t
    unfold taylorRem
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, atomJet_zero, Nat.factorial]
    field_simp
    ring
  rw [e, gammaNorm_smul hδ (gammaFinite_taylorRem hδ 2 hx (by linarith)), abs_inv,
    abs_of_pos hh0]
  calc h⁻¹ * gammaNorm δ (taylorRem 2 x (x + h))
      ≤ h⁻¹ * ((x + h - x) ^ 2 / ((2 : ℕ).factorial : ℝ) *
          (jetConst 2 * (x + h) ^ 2 * (x ^ ((5 + δ) / 2))⁻¹ / x ^ 2)) :=
        mul_le_mul_of_nonneg_left hrem (by positivity)
    _ = h / 2 * (K * (x + h) ^ 2) := by
        rw [hK]; simp only [Nat.factorial]; field_simp; ring

/-- The first-jet limit of the inserted dipole: `(D_q f_(x+h) - D_q f_x)/h → ∂f_x - q ∂f_(qx)`. -/
private theorem tendsto_inserted_div {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {q x : ℝ} (hq : 0 < q)
    (hx : 0 < x) :
    Tendsto (fun h => gammaNorm δ (fun t => insertedDipole q x h t / h -
      (atomJet 1 x t - q * atomJet 1 (q * x) t))) (𝓝[>] 0) (𝓝 0) := by
  have hδ : 0 < 5 + δ := by linarith
  have hqx : 0 < q * x := mul_pos hq hx
  have h1 := tendsto_taylorRem_div hδ0 hδ1 hx
  have hT : Tendsto (fun h : ℝ => q * h) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((by fun_prop : Continuous fun h : ℝ => q * h).tendsto 0)
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh; exact mul_pos hq hh
  have h2 := (tendsto_taylorRem_div hδ0 hδ1 hqx).comp hT
  have hmaj := h1.add (h2.const_mul q)
  rw [mul_zero, add_zero] at hmaj
  refine squeeze_zero' (Eventually.of_forall fun _ => gammaNorm_nonneg _ _) ?_ hmaj
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (0 : ℝ) < h := hh
  have A := GammaFinite.sub ((gammaFinite_atom hδ (by linarith : 0 < x + h)).sub
    (gammaFinite_atom hδ hx) |>.smul h⁻¹) (gammaFinite_atomJet hδ 1 hx)
  have B := GammaFinite.sub ((gammaFinite_atom hδ (by nlinarith : 0 < q * x + q * h)).sub
    (gammaFinite_atom hδ hqx) |>.smul (q * h)⁻¹) (gammaFinite_atomJet hδ 1 hqx)
  have e : (fun t => insertedDipole q x h t / h - (atomJet 1 x t - q * atomJet 1 (q * x) t)) =
      fun t => (h⁻¹ * (atom (x + h) t - atom x t) - atomJet 1 x t) +
        (-q) * ((q * h)⁻¹ * (atom (q * x + q * h) t - atom (q * x) t) - atomJet 1 (q * x) t) := by
    funext t
    unfold insertedDipole
    rw [show q * (x + h) = q * x + q * h by ring]
    field_simp
    ring
  rw [e]
  refine (gammaNorm_add_le hδ A (B.smul _)).trans ?_
  rw [gammaNorm_smul hδ B, abs_neg, abs_of_pos hq]
  have e1 : (fun t => h⁻¹ * (atom (x + h) t - atom x t) - atomJet 1 x t) =
      fun t => (atom (x + h) t - atom x t) / h - atomJet 1 x t := by
    funext t; field_simp
  have e2 : (fun t => (q * h)⁻¹ * (atom (q * x + q * h) t - atom (q * x) t) - atomJet 1 (q * x) t) =
      fun t => (atom (q * x + q * h) t - atom (q * x) t) / (q * h) - atomJet 1 (q * x) t := by
    funext t; field_simp
  rw [e1, e2]
  exact le_refl _

/-- **Card equation (1).**  At `δ = 0` the insertion-energy ratio of `f_(x+h) - f_x` tends to
`R_q` as `h → 0⁺`, independently of `x`. -/
theorem tendsto_insertionEnergyRatio {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    Tendsto (fun h => insertionEnergyRatio 0 q x h) (𝓝[>] 0) (𝓝 (insertionRatio q)) := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hqx : 0 < q * x := mul_pos hq hx
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have hTA := tendsto_taylorRem_div (δ := 0) le_rfl zero_le_one hx
  have hfinA : ∀ᶠ h in 𝓝[>] (0 : ℝ), GammaFinite 0 (nearDipole x h) := by
    filter_upwards [hev] with h hh
    exact (gammaFinite_atom hδ (by linarith)).sub (gammaFinite_atom hδ hx)
  have hA := tendsto_gammaEnergy_div_sq hδ (F := nearDipole x) hfinA
    (gammaFinite_atomJet hδ 1 hx) hTA
  have hB := tendsto_gammaEnergy_div_sq hδ (F := insertedDipole q x)
    (by filter_upwards [hev] with h hh
        have h1 : 0 < x + h := by linarith
        exact ((gammaFinite_atom hδ h1).sub (gammaFinite_atom hδ (mul_pos hq h1))).sub
          ((gammaFinite_atom hδ hx).sub (gammaFinite_atom hδ hqx)))
    ((gammaFinite_atomJet hδ 1 hx).sub ((gammaFinite_atomJet hδ 1 hqx).smul q))
    (tendsto_inserted_div le_rfl zero_le_one hq hx)
  have hpos : gammaEnergy 0 (atomJet 1 x) ≠ 0 := by
    rw [gammaEnergy, gammaInner_atomJet_one le_rfl hx hx, abelPrefixGramKernel_zero]
    have : 0 < 6 * x * x * (3 * x * x - x ^ 2 - x ^ 2) / (x + x) ^ 7 := by
      have : 3 * x * x - x ^ 2 - x ^ 2 = x ^ 2 := by ring
      rw [this]; positivity
    exact this.ne'
  have hlim := hB.div hA hpos
  rw [gammaEnergy_jet_insertion_ratio hq hx] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with h hh
  unfold insertionEnergyRatio
  have : h ^ 2 ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp

theorem atom_scale (a x t : ℝ) : x ^ 2 * atom a (x * t) = atom (x * a) t := by
  unfold atom
  rw [show a * (x * t) = x * a * t by ring]
  ring

/-- The ratio is scale-invariant: it depends only on `h / x`. -/
theorem insertionEnergyRatio_scale (δ q : ℝ) {x : ℝ} (hx : 0 < x) (h : ℝ) :
    insertionEnergyRatio δ q x h = insertionEnergyRatio δ q 1 (h / x) := by
  have e1 : x * (1 + h / x) = x + h := by field_simp
  have hA : nearDipole x h = dilate x (nearDipole 1 (h / x)) := by
    funext t
    unfold nearDipole dilate
    rw [mul_sub, atom_scale, atom_scale, e1, mul_one]
  have hB : insertedDipole q x h = dilate x (insertedDipole q 1 (h / x)) := by
    funext t
    unfold insertedDipole dilate
    have k2 : x * (q * (1 + h / x)) = q * (x + h) := by rw [← e1]; ring
    simp only [mul_sub, atom_scale, e1, k2, mul_one]
    rw [mul_comm x q]
  unfold insertionEnergyRatio
  rw [hA, hB, gammaEnergy_dilate hx, gammaEnergy_dilate hx]
  have : x ^ (-1 - δ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  by_cases h0 : gammaEnergy δ (nearDipole 1 (h / x)) = 0
  · rw [h0]; simp
  · field_simp

/-- **Finite-packet amplification.**  For every integer `q ≥ 2` there is `ε_q > 0` such that
`0 < h/x < ε_q` forces insertion-energy ratio `> 1`. -/
theorem exists_insertion_amplification {q : ℕ} (hq : 2 ≤ q) :
    ∃ ε > 0, ∀ x h : ℝ, 0 < x → 0 < h → h / x < ε → 1 < insertionEnergyRatio 0 q x h := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlim := tendsto_insertionEnergyRatio hq0 one_pos
  have hev := hlim.eventually (lt_mem_nhds (one_lt_insertionRatio hq))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ε, hε, fun x h hx hh hhx => ?_⟩
  rw [insertionEnergyRatio_scale 0 q hx h]
  apply hball
  refine ⟨?_, div_pos hh hx⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (div_pos hh hx)]
  exact hhx

/-! ### Sign chambers of the first-jet covariance at `δ = 0` -/

/-- Scales separated by more than `(3+√5)/2` have negative first-jet covariance. -/
theorem gammaInner_atomJet_one_neg_of_separated {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : (3 + Real.sqrt 5) / 2 < x / y) : gammaInner 0 (atomJet 1 x) (atomJet 1 y) < 0 := by
  rw [gammaInner_atomJet_one le_rfl hx hy, abelPrefixGramKernel_zero]
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hr : (3 + Real.sqrt 5) / 2 * y < x := by rwa [lt_div_iff₀ hy] at hxy
  have hq : 0 < x ^ 2 - 3 * x * y + y ^ 2 := by
    have h1 : Real.sqrt 5 / 2 * y < x - 3 / 2 * y := by linarith
    have h2 : 0 < Real.sqrt 5 / 2 * y := by positivity
    have h3 : (Real.sqrt 5 / 2 * y) ^ 2 < (x - 3 / 2 * y) ^ 2 := by
      exact pow_lt_pow_left₀ h1 h2.le (by norm_num)
    nlinarith
  have hden : 0 < (x + y) ^ 7 := by positivity
  apply div_neg_of_neg_of_pos _ hden
  have : 6 * x * y * (3 * x * y - x ^ 2 - y ^ 2) = -(6 * x * y * (x ^ 2 - 3 * x * y + y ^ 2)) := by
    ring
  rw [this]
  have := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hx) hy) hq
  linarith

/-- Comparable scales, strictly inside the reciprocal interval, have positive covariance. -/
theorem gammaInner_atomJet_one_pos_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < gammaInner 0 (atomJet 1 x) (atomJet 1 y) ↔
      x / y ∈ Set.Ioo ((3 + Real.sqrt 5) / 2)⁻¹ ((3 + Real.sqrt 5) / 2) := by
  rw [gammaInner_atomJet_one le_rfl hx hy, abelPrefixGramKernel_pos_iff le_rfl hx hy,
    abelTransition_upper_zero]

/-! ### The dyadic first-jet profiles -/

/-- The first-jet profile `v_x = x ∂_x f_x`. -/
def jetProfile (x t : ℝ) : ℝ := x * atomJet 1 x t

theorem gammaFinite_jetProfile {δ : ℝ} (hδ : 0 < 5 + δ) {x : ℝ} (hx : 0 < x) :
    GammaFinite δ (jetProfile x) :=
  (gammaFinite_atomJet hδ 1 hx).smul x

theorem gammaInner_jetProfile {δ : ℝ} (hδ : 0 ≤ δ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    gammaInner δ (jetProfile x) (jetProfile y) = x * y * abelPrefixGramKernel δ x y := by
  have hδ' : 0 < 5 + δ := by linarith
  have hy' := gammaFinite_jetProfile hδ' hy
  unfold jetProfile at hy' ⊢
  rw [gammaInner_smul_left hδ' (gammaFinite_atomJet hδ' 1 hx) hy',
    gammaInner_smul_right hδ' (gammaFinite_atomJet hδ' 1 hy) (gammaFinite_atomJet hδ' 1 hx),
    gammaInner_atomJet_one hδ hx hy]
  ring

/-- `⟨v_x, f_z⟩_δ = x² z² (2(x+z) - (5+δ) x) / (x+z)^(6+δ)`. -/
theorem gammaInner_jetProfile_atom {δ : ℝ} (hδ : 0 ≤ δ) {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    gammaInner δ (jetProfile x) (atom z) =
      x ^ 2 * z ^ 2 * (2 * (x + z) - (5 + δ) * x) / (x + z) ^ (6 + δ) := by
  have hδ' : 0 < 5 + δ := by linarith
  have ej : jetProfile x = fun t => (-x ^ 3) * expMono 1 x t + (2 * x ^ 2) * expMono 0 x t := by
    funext t; simp [jetProfile, atomJet, expMono]; ring
  have ea : atom z = fun t => z ^ 2 * expMono 0 z t + 0 * expMono 0 z t := by
    funext t; simp [atom, expMono]
  rw [ej, ea, gammaInner_two_two hδ' (gammaFinite_expMono hδ' 1 hx) (gammaFinite_expMono hδ' 0 hx)
    (gammaFinite_expMono hδ' 0 hz) (gammaFinite_expMono hδ' 0 hz),
    gammaInner_expMono hδ' 1 0 hx hz, gammaInner_expMono hδ' 0 0 hx hz]
  have hs : 0 < x + z := by linarith
  have hg : 0 < Real.Gamma (5 + δ) := Real.Gamma_pos_of_pos hδ'
  simp only [Nat.cast_one, Nat.cast_zero, add_zero, mul_zero]
  rw [Real.Gamma_add_one hδ'.ne']
  have e1 : (x + z) ^ (5 + δ + 1) = (x + z) ^ (5 + δ) * (x + z) := by
    rw [Real.rpow_add hs, Real.rpow_one]
  have e6 : (x + z) ^ (6 + δ) = (x + z) ^ (5 + δ) * (x + z) := by
    rw [show (6 + δ : ℝ) = 5 + δ + 1 by ring, e1]
  have hP : 0 < (x + z) ^ (5 + δ) := Real.rpow_pos_of_pos hs _
  rw [e1, e6]
  field_simp
  ring

/-- `U_q v_x = v_(q x)`. -/
theorem dilate_jetProfile (q x : ℝ) : dilate q (jetProfile x) = jetProfile (q * x) := by
  funext t
  simp only [dilate, jetProfile, atomJet]
  rw [show x * (q * t) = q * x * t by ring]
  simp
  ring

/-- **Card equation (4).**  `D_2 (v_x + v_(2x)) = v_x - v_(4x)`. -/
theorem dyadic_insertion_telescopes (x t : ℝ) :
    (jetProfile x t + jetProfile (2 * x) t) -
        dilate 2 (fun t => jetProfile x t + jetProfile (2 * x) t) t =
      jetProfile x t - jetProfile (4 * x) t := by
  have h1 := congrFun (dilate_jetProfile 2 x) t
  have h2 := congrFun (dilate_jetProfile 2 (2 * x)) t
  simp only [dilate] at h1 h2 ⊢
  rw [show (2 : ℝ) * (2 * x) = 4 * x by ring] at h2
  rw [mul_add, h1, h2]
  ring

private theorem gamma_five : Real.Gamma 5 = 24 := by
  rw [show (5 : ℝ) = (4 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num [Nat.factorial]

/-- `x Γ(5) ⟨v_(a x), v_(b x)⟩_0 = 6 a² b² (3ab - a² - b²) · 24 / (a+b)^7`. -/
private theorem scaled_jetProfile_gram {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    x * Real.Gamma 5 * gammaInner 0 (jetProfile (a * x)) (jetProfile (b * x)) =
      24 * (6 * a ^ 2 * b ^ 2 * (3 * a * b - a ^ 2 - b ^ 2)) / (a + b) ^ 7 := by
  rw [gammaInner_jetProfile le_rfl (mul_pos ha hx) (mul_pos hb hx), abelPrefixGramKernel_zero,
    gamma_five]
  rw [show a * x + b * x = (a + b) * x by ring]
  have hab : 0 < a + b := by linarith
  field_simp

/-- **Card equation (5), first value.**  `x Γ(5) ‖v_x + v_(2x)‖_0² = 27/16 + 128/243`. -/
theorem gammaEnergy_dyadic_pair {x : ℝ} (hx : 0 < x) :
    x * Real.Gamma 5 * gammaEnergy 0 (fun t => jetProfile x t + jetProfile (2 * x) t) =
      27 / 16 + 128 / 243 := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have h2x : 0 < 2 * x := by linarith
  rw [gammaEnergy_add hδ (gammaFinite_jetProfile hδ hx) (gammaFinite_jetProfile hδ h2x),
    gammaEnergy, gammaEnergy]
  have e11 := scaled_jetProfile_gram (a := 1) (b := 1) one_pos one_pos hx
  have e12 := scaled_jetProfile_gram (a := 1) (b := 2) one_pos two_pos hx
  have e22 := scaled_jetProfile_gram (a := 2) (b := 2) two_pos two_pos hx
  simp only [one_mul] at e11 e12 e22
  have expand : x * Real.Gamma 5 * (gammaInner 0 (jetProfile x) (jetProfile x) +
      2 * gammaInner 0 (jetProfile x) (jetProfile (2 * x)) +
        gammaInner 0 (jetProfile (2 * x)) (jetProfile (2 * x))) =
      x * Real.Gamma 5 * gammaInner 0 (jetProfile x) (jetProfile x) +
        2 * (x * Real.Gamma 5 * gammaInner 0 (jetProfile x) (jetProfile (2 * x))) +
        x * Real.Gamma 5 * gammaInner 0 (jetProfile (2 * x)) (jetProfile (2 * x)) := by ring
  rw [expand, e11, e12, e22]
  norm_num

/-- **Card equation (5), second value.**  `x Γ(5) ‖v_x - v_(4x)‖_0² = 45/32 + 23040/78125`. -/
theorem gammaEnergy_dyadic_telescoped {x : ℝ} (hx : 0 < x) :
    x * Real.Gamma 5 * gammaEnergy 0 (fun t => jetProfile x t - jetProfile (4 * x) t) =
      45 / 32 + 23040 / 78125 := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have h4x : 0 < 4 * x := by linarith
  rw [gammaEnergy_sub hδ (gammaFinite_jetProfile hδ hx) (gammaFinite_jetProfile hδ h4x),
    gammaEnergy, gammaEnergy]
  have e11 := scaled_jetProfile_gram (a := 1) (b := 1) one_pos one_pos hx
  have e14 := scaled_jetProfile_gram (a := 1) (b := 4) one_pos (by norm_num) hx
  have e44 := scaled_jetProfile_gram (a := 4) (b := 4) (by norm_num) (by norm_num) hx
  simp only [one_mul] at e11 e14 e44
  have expand : x * Real.Gamma 5 * (gammaInner 0 (jetProfile x) (jetProfile x) -
      2 * gammaInner 0 (jetProfile x) (jetProfile (4 * x)) +
        gammaInner 0 (jetProfile (4 * x)) (jetProfile (4 * x))) =
      x * Real.Gamma 5 * gammaInner 0 (jetProfile x) (jetProfile x) -
        2 * (x * Real.Gamma 5 * gammaInner 0 (jetProfile x) (jetProfile (4 * x))) +
        x * Real.Gamma 5 * gammaInner 0 (jetProfile (4 * x)) (jetProfile (4 * x)) := by ring
  rw [expand, e11, e14, e44]
  norm_num

/-- The rational comparison in (5). -/
theorem dyadic_rational_chain :
    (45 / 32 + 23040 / 78125 : ℝ) < 45 / 32 + 1 / 3 ∧ (45 / 32 + 1 / 3 : ℝ) = 167 / 96 ∧
      (167 / 96 : ℝ) < 7 / 4 ∧ (7 / 4 : ℝ) = 4 / 5 * (27 / 16 + 1 / 2) ∧
      (4 / 5 * (27 / 16 + 1 / 2) : ℝ) < 4 / 5 * (27 / 16 + 128 / 243) := by
  norm_num

/-- **Dyadic compensation.**  `‖D_2(v_x + v_(2x))‖_0² < (4/5) ‖v_x + v_(2x)‖_0²`. -/
theorem gammaEnergy_dyadic_contraction {x : ℝ} (hx : 0 < x) :
    gammaEnergy 0 (fun t => jetProfile x t - jetProfile (4 * x) t) <
      4 / 5 * gammaEnergy 0 (fun t => jetProfile x t + jetProfile (2 * x) t) := by
  have hc : 0 < x * Real.Gamma 5 := mul_pos hx (by rw [gamma_five]; norm_num)
  have h1 := gammaEnergy_dyadic_telescoped hx
  have h2 := gammaEnergy_dyadic_pair hx
  rw [← mul_lt_mul_iff_right₀ hc, h1, show x * Real.Gamma 5 * (4 / 5 *
    gammaEnergy 0 (fun t => jetProfile x t + jetProfile (2 * x) t)) = 4 / 5 * (x * Real.Gamma 5 *
    gammaEnergy 0 (fun t => jetProfile x t + jetProfile (2 * x) t)) by ring, h2]
  norm_num

/-! ### A literal half-scale prime compensator -/

/-- **Card equation (8), inner product law.**  `⟨v_x, f_z⟩_0 = x² z² (2z - 3x)/(x+z)^6`. -/
theorem gammaInner_jetProfile_atom_zero {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    gammaInner 0 (jetProfile x) (atom z) = x ^ 2 * z ^ 2 * (2 * z - 3 * x) / (x + z) ^ 6 := by
  rw [gammaInner_jetProfile_atom le_rfl hx hz, add_zero, add_zero,
    show (x + z) ^ (6 : ℝ) = (x + z) ^ (6 : ℕ) by norm_cast]
  ring

/-- The inserted dyadic first jet `H_x = v_x - v_(4x)`. -/
def dyadicJet (x t : ℝ) : ℝ := jetProfile x t - jetProfile (4 * x) t

theorem gammaFinite_dyadicJet {δ : ℝ} (hδ : 0 < 5 + δ) {x : ℝ} (hx : 0 < x) :
    GammaFinite δ (dyadicJet x) :=
  (gammaFinite_jetProfile hδ hx).sub (gammaFinite_jetProfile hδ (by linarith))

/-- `x ⟨H_x, f_(x/2)⟩_0 = -20512/531441`. -/
theorem dyadicJet_halfScale_inner {x : ℝ} (hx : 0 < x) :
    x * gammaInner 0 (dyadicJet x) (atom (x / 2)) = -20512 / 531441 := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hz : 0 < x / 2 := by linarith
  have h4 : 0 < 4 * x := by linarith
  unfold dyadicJet
  rw [show (fun t => jetProfile x t - jetProfile (4 * x) t) =
    fun t => 1 * jetProfile x t + (-1) * jetProfile (4 * x) t by funext t; ring]
  rw [gammaInner_comm, show atom (x / 2) = fun t => 1 * atom (x / 2) t + 0 * atom (x / 2) t by
    funext t; ring, gammaInner_two_two hδ (gammaFinite_atom hδ hz) (gammaFinite_atom hδ hz)
    (gammaFinite_jetProfile hδ hx) (gammaFinite_jetProfile hδ h4), gammaInner_comm 0 (atom (x / 2)) (jetProfile x),
    gammaInner_comm 0 (atom (x / 2)) (jetProfile (4 * x)), gammaInner_jetProfile_atom_zero hx hz,
    gammaInner_jetProfile_atom_zero h4 hz]
  field_simp
  ring

/-- `x ‖f_(x/2)‖_0² = 1/16`. -/
theorem halfScale_atom_energy {x : ℝ} (hx : 0 < x) :
    x * gammaEnergy 0 (atom (x / 2)) = 1 / 16 := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  rw [gammaEnergy, gammaInner_atom hδ (by linarith) (by linarith), sourceKernel_zero]
  field_simp
  ring

/-- `x ‖H_x‖_0² = (45/32 + 23040/78125)/24 < 71/1000`. -/
theorem dyadicJet_energy {x : ℝ} (hx : 0 < x) :
    x * gammaEnergy 0 (dyadicJet x) = (45 / 32 + 23040 / 78125) / 24 ∧
      (45 / 32 + 23040 / 78125) / 24 < (71 / 1000 : ℝ) := by
  refine ⟨?_, by norm_num⟩
  have h := gammaEnergy_dyadic_telescoped hx
  rw [gamma_five] at h
  unfold dyadicJet
  linarith

/-- **Card equation (8).**  Adding `(3/5) f_(x/2)` removes more than a third of the energy of the
inserted dyadic jet: `‖H_x + (3/5) f_(x/2)‖_0² < (2/3) ‖H_x‖_0²`. -/
theorem halfScale_compensation {x : ℝ} (hx : 0 < x) :
    x * (gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) -
        gammaEnergy 0 (dyadicJet x)) =
      9 / 400 + 6 / 5 * (x * gammaInner 0 (dyadicJet x) (atom (x / 2))) ∧
    x * (gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) -
        gammaEnergy 0 (dyadicJet x)) < -237 / 10000 ∧
    (-237 / 10000 : ℝ) < -(1 / 3) * (x * gammaEnergy 0 (dyadicJet x)) ∧
    gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) <
      2 / 3 * gammaEnergy 0 (dyadicJet x) := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have hz : 0 < x / 2 := by linarith
  have hH := gammaFinite_dyadicJet hδ hx
  have hf := (gammaFinite_atom hδ hz).smul (3 / 5)
  have hexp : gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) -
      gammaEnergy 0 (dyadicJet x) =
      9 / 25 * gammaEnergy 0 (atom (x / 2)) + 6 / 5 * gammaInner 0 (dyadicJet x) (atom (x / 2)) := by
    rw [gammaEnergy_add hδ hH hf, gammaInner_smul_right hδ (gammaFinite_atom hδ hz) hH]
    rw [show gammaEnergy 0 (fun t => 3 / 5 * atom (x / 2) t) =
      9 / 25 * gammaEnergy 0 (atom (x / 2)) by
        rw [gammaEnergy, gammaInner_smul_left hδ (gammaFinite_atom hδ hz) hf,
          gammaInner_smul_right hδ (gammaFinite_atom hδ hz) (gammaFinite_atom hδ hz)]
        unfold gammaEnergy; ring]
    ring
  have e1 : x * (gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) -
      gammaEnergy 0 (dyadicJet x)) =
      9 / 400 + 6 / 5 * (x * gammaInner 0 (dyadicJet x) (atom (x / 2))) := by
    rw [hexp, mul_add, ← mul_assoc, mul_comm x (9 / 25), mul_assoc, halfScale_atom_energy hx]
    ring
  have hi := dyadicJet_halfScale_inner hx
  have hE := (dyadicJet_energy hx).1
  refine ⟨e1, ?_, ?_, ?_⟩
  · rw [e1, hi]; norm_num
  · rw [hE]; norm_num
  · have hlt : x * (gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) -
        gammaEnergy 0 (dyadicJet x)) < -(1 / 3) * (x * gammaEnergy 0 (dyadicJet x)) := by
      rw [e1, hi, hE]; norm_num
    have : x * gammaEnergy 0 (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) <
        x * (2 / 3 * gammaEnergy 0 (dyadicJet x)) := by nlinarith
    exact lt_of_mul_lt_mul_left this hx.le

/-! ### Persistence for small `δ > 0` -/

private theorem continuous_const_rpow_delta {s c : ℝ} (hs : 0 < s) :
    Continuous fun δ : ℝ => s ^ (c + δ) :=
  continuous_const.rpow (by fun_prop) (fun _ => Or.inl hs.ne')

theorem continuous_abelPrefixGramKernel_delta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous fun δ => abelPrefixGramKernel δ a b := by
  unfold abelPrefixGramKernel abelPrefixGramNumerator abelPrefixGramCore
  have hs : 0 < a + b := by linarith
  have h := continuous_const_rpow_delta (c := 7) hs
  refine (continuous_const.div h (fun δ => (Real.rpow_pos_of_pos hs _).ne')).mul (by fun_prop)

theorem continuous_sourceKernel_delta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous fun δ => sourceKernel δ a b := by
  unfold sourceKernel
  have hs : 0 < a + b := by linarith
  exact continuous_const.div (continuous_const_rpow_delta (c := 5) hs)
    (fun δ => (Real.rpow_pos_of_pos hs _).ne')

theorem continuous_jetAtom_delta {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    Continuous fun δ : ℝ => a ^ 2 * z ^ 2 * (2 * (a + z) - (5 + δ) * a) / (a + z) ^ (6 + δ) := by
  have hs : 0 < a + z := by linarith
  exact (by fun_prop : Continuous fun δ : ℝ => a ^ 2 * z ^ 2 * (2 * (a + z) - (5 + δ) * a)).div
    (continuous_const_rpow_delta (c := 6) hs) (fun δ => (Real.rpow_pos_of_pos hs _).ne')

theorem exists_Icc_of_continuous_neg {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : φ 0 < 0) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, φ δ < 0 := by
  have hev := (hφ.tendsto 0).eventually (gt_mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε / 2, by linarith, fun δ hδ => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ.1]
  linarith [hδ.2]

/-- The energy of `v_x ± c v_(y)` combinations at scale `1`, written through the kernel. -/
theorem gammaEnergy_jet_combo {δ : ℝ} (hδ : 0 ≤ δ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c : ℝ) :
    gammaEnergy δ (fun t => jetProfile a t + c * jetProfile b t) =
      a * a * abelPrefixGramKernel δ a a + 2 * c * (a * b * abelPrefixGramKernel δ a b) +
        c ^ 2 * (b * b * abelPrefixGramKernel δ b b) := by
  have hδ' : 0 < 5 + δ := by linarith
  have fa := gammaFinite_jetProfile hδ' ha
  have fb := gammaFinite_jetProfile hδ' hb
  rw [gammaEnergy_add hδ' fa (fb.smul c), gammaInner_smul_right hδ' fb fa, gammaEnergy,
    gammaEnergy, gammaInner_smul_left hδ' fb (fb.smul c), gammaInner_smul_right hδ' fb fb,
    gammaInner_jetProfile hδ ha ha, gammaInner_jetProfile hδ ha hb, gammaInner_jetProfile hδ hb hb]
  ring

theorem dilate_add_fun (q : ℝ) (F G : ℝ → ℝ) :
    dilate q (fun t => F t + G t) = fun t => dilate q F t + dilate q G t := by
  funext t; simp only [dilate]; ring

theorem dilate_smul_fun (q c : ℝ) (F : ℝ → ℝ) :
    dilate q (fun t => c * F t) = fun t => c * dilate q F t := by
  funext t; simp only [dilate]; ring

/-- **Persistence of the dyadic contraction.**  There is `δ₀ > 0` such that for `0 ≤ δ ≤ δ₀`
and every scale `x > 0`, `‖v_x - v_(4x)‖_δ² < (39/50) ‖v_x + v_(2x)‖_δ²`; `39/50 < 4/5`. -/
theorem exists_dyadic_contraction_delta :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ x : ℝ, 0 < x →
      gammaEnergy δ (fun t => jetProfile x t - jetProfile (4 * x) t) <
        39 / 50 * gammaEnergy δ (fun t => jetProfile x t + jetProfile (2 * x) t) := by
  set φ : ℝ → ℝ := fun δ =>
    (1 * 1 * abelPrefixGramKernel δ 1 1 + 2 * (-1) * (1 * 4 * abelPrefixGramKernel δ 1 4) +
        (-1) ^ 2 * (4 * 4 * abelPrefixGramKernel δ 4 4)) -
      39 / 50 * (1 * 1 * abelPrefixGramKernel δ 1 1 + 2 * 1 * (1 * 2 * abelPrefixGramKernel δ 1 2) +
        1 ^ 2 * (2 * 2 * abelPrefixGramKernel δ 2 2)) with hφ
  have hcont : Continuous φ := by
    have c11 := continuous_abelPrefixGramKernel_delta (a := 1) (b := 1) one_pos one_pos
    have c14 := continuous_abelPrefixGramKernel_delta (a := 1) (b := 4) one_pos (by norm_num)
    have c44 := continuous_abelPrefixGramKernel_delta (a := 4) (b := 4) (by norm_num) (by norm_num)
    have c12 := continuous_abelPrefixGramKernel_delta (a := 1) (b := 2) one_pos two_pos
    have c22 := continuous_abelPrefixGramKernel_delta (a := 2) (b := 2) two_pos two_pos
    rw [hφ]; fun_prop
  have h0 : φ 0 < 0 := by
    rw [hφ]
    simp only [abelPrefixGramKernel_zero]
    norm_num
  obtain ⟨δ₀, hδ₀, hneg⟩ := exists_Icc_of_continuous_neg hcont h0
  refine ⟨δ₀, hδ₀, fun δ hδ x hx => ?_⟩
  have hd := hδ.1
  have e1 : (fun t => jetProfile x t - jetProfile (4 * x) t) =
      dilate x (fun t => jetProfile 1 t + (-1) * jetProfile 4 t) := by
    rw [dilate_add_fun, dilate_smul_fun, dilate_jetProfile, dilate_jetProfile, mul_one]
    funext t; ring_nf
  have e2 : (fun t => jetProfile x t + jetProfile (2 * x) t) =
      dilate x (fun t => jetProfile 1 t + 1 * jetProfile 2 t) := by
    rw [dilate_add_fun, dilate_smul_fun, dilate_jetProfile, dilate_jetProfile, mul_one]
    funext t; ring_nf
  rw [e1, e2, gammaEnergy_dilate hx, gammaEnergy_dilate hx,
    gammaEnergy_jet_combo hd one_pos (by norm_num), gammaEnergy_jet_combo hd one_pos two_pos]
  have hpos : 0 < x ^ (-1 - δ) := Real.rpow_pos_of_pos hx _
  have := hneg δ hδ
  simp only [hφ] at this
  nlinarith

/-- **Persistence of the half-scale compensation.**  There is `δ₁ > 0` such that for
`0 ≤ δ ≤ δ₁` and every `x > 0`, `‖H_x + (3/5) f_(x/2)‖_δ² < (333/500) ‖H_x‖_δ²`. -/
theorem exists_halfScale_compensation_delta :
    ∃ δ₁ > 0, ∀ δ ∈ Set.Icc (0 : ℝ) δ₁, ∀ x : ℝ, 0 < x →
      gammaEnergy δ (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) <
        333 / 500 * gammaEnergy δ (dyadicJet x) := by
  set EH : ℝ → ℝ := fun δ => 1 * 1 * abelPrefixGramKernel δ 1 1 +
    2 * (-1) * (1 * 4 * abelPrefixGramKernel δ 1 4) + (-1) ^ 2 * (4 * 4 * abelPrefixGramKernel δ 4 4)
    with hEH
  set IH : ℝ → ℝ := fun δ =>
    1 ^ 2 * (1 / 2) ^ 2 * (2 * (1 + 1 / 2) - (5 + δ) * 1) / (1 + 1 / 2) ^ (6 + δ) -
      4 ^ 2 * (1 / 2) ^ 2 * (2 * (4 + 1 / 2) - (5 + δ) * 4) / (4 + 1 / 2) ^ (6 + δ) with hIH
  set φ : ℝ → ℝ := fun δ => (EH δ + 2 * (3 / 5) * IH δ + (3 / 5) ^ 2 * sourceKernel δ (1 / 2) (1 / 2))
    - 333 / 500 * EH δ with hφ
  have hcont : Continuous φ := by
    have c11 := continuous_abelPrefixGramKernel_delta (a := 1) (b := 1) one_pos one_pos
    have c14 := continuous_abelPrefixGramKernel_delta (a := 1) (b := 4) one_pos (by norm_num)
    have c44 := continuous_abelPrefixGramKernel_delta (a := 4) (b := 4) (by norm_num) (by norm_num)
    have j1 := continuous_jetAtom_delta (a := 1) (z := 1 / 2) one_pos (by norm_num)
    have j4 := continuous_jetAtom_delta (a := 4) (z := 1 / 2) (by norm_num) (by norm_num)
    have k := continuous_sourceKernel_delta (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    rw [hφ, hEH, hIH]; fun_prop
  have h0 : φ 0 < 0 := by
    rw [hφ, hEH, hIH]
    simp only [abelPrefixGramKernel_zero, sourceKernel_zero, add_zero]
    rw [show ((1 + 1 / 2 : ℝ)) ^ (6 : ℝ) = (1 + 1 / 2) ^ (6 : ℕ) by norm_cast,
      show ((4 + 1 / 2 : ℝ)) ^ (6 : ℝ) = (4 + 1 / 2) ^ (6 : ℕ) by norm_cast]
    norm_num
  obtain ⟨δ₁, hδ₁, hneg⟩ := exists_Icc_of_continuous_neg hcont h0
  refine ⟨δ₁, hδ₁, fun δ hδ x hx => ?_⟩
  have hd := hδ.1
  have hδ' : 0 < 5 + δ := by linarith
  have hH1 : dyadicJet x = dilate x (fun t => jetProfile 1 t + (-1) * jetProfile 4 t) := by
    rw [dilate_add_fun, dilate_smul_fun, dilate_jetProfile, dilate_jetProfile, mul_one]
    funext t; unfold dyadicJet; ring_nf
  have hsum : (fun t => dyadicJet x t + 3 / 5 * atom (x / 2) t) =
      dilate x (fun t => (jetProfile 1 t + (-1) * jetProfile 4 t) + 3 / 5 * atom (1 / 2) t) := by
    rw [dilate_add_fun, dilate_smul_fun, dilate_atom, ← hH1]
    funext t; ring_nf
  rw [hsum, hH1, gammaEnergy_dilate hx, gammaEnergy_dilate hx]
  have fH := (gammaFinite_jetProfile hδ' one_pos).add
    ((gammaFinite_jetProfile hδ' (by norm_num : (0 : ℝ) < 4)).smul (-1))
  have ff := gammaFinite_atom hδ' (by norm_num : (0 : ℝ) < 1 / 2)
  rw [gammaEnergy_add hδ' fH (ff.smul _), gammaInner_smul_right hδ' ff fH,
    show gammaEnergy δ (fun t => 3 / 5 * atom (1 / 2) t) =
      (3 / 5) ^ 2 * sourceKernel δ (1 / 2) (1 / 2) by
        rw [gammaEnergy, gammaInner_smul_left hδ' ff (ff.smul _), gammaInner_smul_right hδ' ff ff,
          gammaInner_atom hδ' (by norm_num) (by norm_num)]; ring,
    gammaEnergy_jet_combo hd one_pos (by norm_num)]
  have hIHv : gammaInner δ (fun t => jetProfile 1 t + (-1) * jetProfile 4 t) (atom (1 / 2)) = IH δ := by
    rw [gammaInner_add_left hδ' (gammaFinite_jetProfile hδ' one_pos)
      ((gammaFinite_jetProfile hδ' (by norm_num)).smul _) ff,
      gammaInner_smul_left hδ' (gammaFinite_jetProfile hδ' (by norm_num)) ff,
      gammaInner_jetProfile_atom hd one_pos (by norm_num),
      gammaInner_jetProfile_atom hd (by norm_num) (by norm_num), hIH]
    ring
  rw [hIHv]
  have hpos : 0 < x ^ (-1 - δ) := Real.rpow_pos_of_pos hx _
  have := hneg δ hδ
  simp only [hφ] at this
  nlinarith

/-- The three unnormalized Gamma integrals of the jet proof, at `x = 1`:
`Γ(5)‖g‖² = 9/8`, `Γ(5)‖h_q‖² = 9/(8q)`, `Γ(5)⟨g, h_q⟩ = 144 q² (-q²+3q-1)/(q+1)^7`, where
`g = ∂f_1` and `h_q = q ∂f_q`. -/
theorem gamma_five_jet_integrals {q : ℝ} (hq : 0 < q) :
    Real.Gamma 5 * gammaEnergy 0 (atomJet 1 1) = 9 / 8 ∧
    Real.Gamma 5 * gammaEnergy 0 (fun t => q * atomJet 1 q t) = 9 / (8 * q) ∧
    Real.Gamma 5 * gammaInner 0 (atomJet 1 1) (fun t => q * atomJet 1 q t) =
      144 * q ^ 2 * (-q ^ 2 + 3 * q - 1) / (q + 1) ^ 7 := by
  have hδ : (0 : ℝ) < 5 + 0 := by norm_num
  have f1 := gammaFinite_atomJet hδ 1 one_pos
  have fq := gammaFinite_atomJet hδ 1 hq
  refine ⟨?_, ?_, ?_⟩
  · rw [gammaEnergy, gamma_five_mul_gammaInner_atomJet_one one_pos one_pos]; norm_num
  · rw [gammaEnergy, gammaInner_smul_left hδ fq (fq.smul q), gammaInner_smul_right hδ fq fq,
      show Real.Gamma 5 * (q * (q * gammaInner 0 (atomJet 1 q) (atomJet 1 q))) =
        q * q * (Real.Gamma 5 * gammaInner 0 (atomJet 1 q) (atomJet 1 q)) by ring,
      gamma_five_mul_gammaInner_atomJet_one hq hq]
    field_simp
    ring
  · rw [gammaInner_smul_right hδ fq f1,
      show Real.Gamma 5 * (q * gammaInner 0 (atomJet 1 1) (atomJet 1 q)) =
        q * (Real.Gamma 5 * gammaInner 0 (atomJet 1 1) (atomJet 1 q)) by ring,
      gamma_five_mul_gammaInner_atomJet_one one_pos hq]
    field_simp
    ring

end RHTower.CubicGamma
