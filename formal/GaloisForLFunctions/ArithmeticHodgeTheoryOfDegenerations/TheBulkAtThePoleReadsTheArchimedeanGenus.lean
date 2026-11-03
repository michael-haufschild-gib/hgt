import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkIsBlindToTheLowZeros
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity
import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.DyadicPoleNodalRHEquivalence
import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction

/-!
# The bulk at the pole reads the archimedean genus

A single zero `ρ` contributes `m_ρ κ y_1²/(ρ(1 − ρ))` to the normalized complete form of a fixed
conductor packet (`tendsto_bulkLedger`, `κ = (∫φ)²/∫φ²`, `y_1` the pole coefficient), and pole-free
packets are blind to all low zeros together (`tendsto_sum_bulkLedger_lowZeros`). This file sums the
pole contributions uniformly:

* **One zero with the pole** (`norm_log_div_mul_bulkLedger_sub_le`): the distance of the ledger
  entry from `m_ρ κ y_1²/(ρ(1−ρ))` is `≤ m_ρ (C₁ c/N + C₂ (|y_1| + (6 + |ρ|)²/N)/N)`: the horizon
  terms `y_1 N^ρ/ρ`, `y_1 N^{1−ρ}/(1−ρ)` multiply to `y_1² N/(ρ(1−ρ))`, the remainders are explicit
  (second-order Euler–Maclaurin), and the atom factor moves by `O(c|ρ|/N)`.
* **All low zeros with the pole** (`tendsto_sum_bulkLedger_lowZeros_pole`): along heights
  `T_N → ∞` with `c_N T_N log² T_N/N → 0` and `T_N³ log² T_N/N² → 0`,
  `Σ_{|γ| ≤ T_N} (log N/c) W_ρ/∫g² → κ y_1² Σ_ρ m_ρ/(ρ(1 − ρ))`.
* **The archimedean genus** (`tsum_mult_div_zero_mul_one_sub_eq`): `Σ_ρ m_ρ/(ρ(1 − ρ)) = 2 + γ −
  log 4π`, the first Li coefficient doubled (RHTower, Hadamard product of `ξ`). So the low zeros
  together contribute exactly `κ y_1² (2 + γ − log 4π) > 0` (`tendsto_sum_bulkLedger_lowZeros_genus`,
  heights `N^θ`, `θ < 2/3`, in `tendsto_sum_bulkLedger_lowZeros_genus_rpow`).

The pole channel of the bulk reads one number from the zeros, the archimedean genus, and it is
positive: the gluing of the bulk to the pole is a positive rank-one term computed by the zeros
below the resolution height.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open BezoutValuationIncidence SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri

/-! ### The packet with its pole -/

/-- **A packet at a zero, with its pole**: `‖√log N · D_x(γ_s) − y_1 N^s/s‖ ≤ P(5 + ‖s‖)N^{Re s − 1}`. -/
theorem norm_dirichletPoly_packet_sub_pole_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta (1 - s) = 0) {E : Finset ℕ} (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ}
    (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) {N : ℕ} (hN : 2 * L * (‖s‖ + 2) ≤ N)
    (hlog : 0 < Real.log N) :
    ‖((Real.sqrt (Real.log N) : ℝ) : ℂ) * dirichletPoly N (packetWeights E y N) (gammaOf s) -
        (poleCoefficient E y : ℂ) * (((N : ℝ) : ℂ) ^ s / s)‖ ≤
      packetConst E y * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1) := by
  have hsq : ((Real.sqrt (Real.log N) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hlog).ne'
  rw [dirichletPoly_packetWeights, ← mul_assoc, mul_inv_cancel₀ hsq, one_mul]
  have hpole : (poleCoefficient E y : ℂ) =
      if 1 ∈ E then ((y 1 / Real.sqrt (Nat.totient 1) : ℝ) : ℂ) else 0 := by
    unfold poleCoefficient
    split_ifs <;> simp
  have hsum := sum_mul_horizonTerm E (fun e => ((y e / Real.sqrt e.totient : ℝ) : ℂ)) N s
  beta_reduce at hsum
  rw [hpole, ← hsum, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold packetConst
  rw [Finset.sum_mul, Finset.sum_mul]
  refine sum_le_sum fun e he => ?_
  have hNe : 2 * e * (‖s‖ + 2) ≤ (N : ℝ) := by
    refine le_trans ?_ hN
    have : (e : ℝ) ≤ L := by exact_mod_cast hL e he
    gcongr
  have hb := norm_conductorDirichlet_sub_horizonTerm_le hs0 hs1 hz (hE e he) hNe
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |y e / Real.sqrt e.totient| * ‖conductorDirichlet e N s - horizonTerm e N s‖ ≤
        |y e / Real.sqrt e.totient| * (4 * (e : ℝ) ^ 3 * (5 + ‖s‖) * (N : ℝ) ^ (s.re - 1)) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-- The transform of a profile on `[0, 1]` moves by `≤ 2‖z‖∫|φ|` from its value at `0`. -/
theorem norm_paperFT_sub_integral_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖paperFT (cx φ) z - ((∫ u, φ u : ℝ) : ℂ)‖ ≤ 2 * ‖z‖ * ∫ u, |φ u| := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hi : ∀ w : ℂ, Integrable fun u : ℝ => cx φ u * Complex.exp (Complex.I * w * u) := by
    intro w
    refine Continuous.integrable_of_hasCompactSupport (by unfold cx; fun_prop) ?_
    exact (hφc.comp_left Complex.ofReal_zero).mul_right
  rw [← paperFT_cx_zero, paperFT_def, paperFT_def, ← integral_sub (hi _) (hi _),
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hφ.abs.integrable_of_hasCompactSupport hφc.abs).const_mul _)
    (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · have hzu : ‖Complex.I * z * u‖ ≤ ‖z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu.1]
      exact mul_le_of_le_one_right (norm_nonneg _) hu.2
    have he := Complex.norm_exp_sub_one_le (hzu.trans hz)
    rw [mul_zero, zero_mul, Complex.exp_zero, mul_one, ← mul_sub_one, norm_mul]
    simp only [cx, Complex.norm_real, Real.norm_eq_abs]
    calc |φ u| * ‖Complex.exp (Complex.I * z * u) - 1‖ ≤ |φ u| * (2 * ‖z‖) :=
          mul_le_mul_of_nonneg_left (he.trans (by linarith)) (abs_nonneg _)
      _ = 2 * ‖z‖ * |φ u| := by ring
  · simp [cx, hφsupp u hu]

/-! ### One zero with the pole -/

theorem three_lt_norm_of_mem {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    3 < ‖ρ‖ ∧ 3 < ‖(1 : ℂ) - ρ‖ := by
  have h := ConjugateDiagonalGeometry.LogScaleHeckeDefect.three_lt_abs_im_of_mem_zetaZeroConfig hρ
  refine ⟨lt_of_lt_of_le h (Complex.abs_im_le_norm ρ), lt_of_lt_of_le ?_ (Complex.abs_im_le_norm _)⟩
  simpa using h

/-- The product of two perturbed factors: if `H₁H₂ = nL`, then
`X₁X₂/n − L = (H₁(X₂ − H₂) + (X₁ − H₁)H₂ + (X₁ − H₁)(X₂ − H₂))/n`. -/
theorem mul_div_sub_eq {H₁ H₂ X₁ X₂ L n : ℂ} (hn : n ≠ 0) (hHH : H₁ * H₂ = n * L) :
    X₁ * X₂ / n - L = (H₁ * (X₂ - H₂) + (X₁ - H₁) * H₂ + (X₁ - H₁) * (X₂ - H₂)) / n := by
  have hX : X₁ * X₂ = H₁ * H₂ +
      (H₁ * (X₂ - H₂) + (X₁ - H₁) * H₂ + (X₁ - H₁) * (X₂ - H₂)) := by ring
  rw [hX, hHH, add_div, mul_div_cancel_left₀ _ hn]
  ring

/-- The core estimate: `‖(F₁F₂ − a₀²)B + a₀²(B − L)‖ ≤ δ‖L‖ + (δ + A²)E`. -/
theorem norm_ledger_core_le {F₁ F₂ a₀ B L : ℂ} {δ A E : ℝ} (hδ : ‖F₁ * F₂ - a₀ * a₀‖ ≤ δ)
    (ha₀ : ‖a₀‖ ≤ A) (hE : ‖B - L‖ ≤ E) :
    ‖(F₁ * F₂ - a₀ * a₀) * B + a₀ * a₀ * (B - L)‖ ≤ δ * ‖L‖ + (δ + A ^ 2) * E := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hBn : ‖B‖ ≤ ‖L‖ + E := by
    have := norm_sub_norm_le B L
    linarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖F₁ * F₂ - a₀ * a₀‖ * ‖B‖ ≤ δ * (‖L‖ + E) :=
    mul_le_mul hδ hBn (norm_nonneg _) hδ0
  have h2 : ‖a₀‖ * ‖a₀‖ * ‖B - L‖ ≤ A * A * E :=
    mul_le_mul (mul_le_mul ha₀ ha₀ (norm_nonneg _) ((norm_nonneg _).trans ha₀)) hE (norm_nonneg _)
      (by nlinarith [(norm_nonneg a₀).trans ha₀])
  nlinarith

/-- The atom factors: `‖F₁F₂ − a₀²‖ ≤ 2(e + 1)I₁² r` when both transforms move by `≤ 2rI₁`. -/
theorem norm_atom_product_sub_le {F₁ F₂ a₀ : ℂ} {I₁ r : ℝ} (hF₂ : ‖F₂‖ ≤ I₁ * Real.exp 1)
    (ha₀ : ‖a₀‖ ≤ I₁) (hd₁ : ‖F₁ - a₀‖ ≤ 2 * r * I₁) (hd₂ : ‖F₂ - a₀‖ ≤ 2 * r * I₁) :
    ‖F₁ * F₂ - a₀ * a₀‖ ≤ 2 * (Real.exp 1 + 1) * I₁ ^ 2 * r := by
  have e : F₁ * F₂ - a₀ * a₀ = (F₁ - a₀) * F₂ + a₀ * (F₂ - a₀) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hI : 0 ≤ I₁ := (norm_nonneg _).trans ha₀
  have hr : 0 ≤ 2 * r * I₁ := (norm_nonneg _).trans hd₁
  have h1 : ‖F₁ - a₀‖ * ‖F₂‖ ≤ (2 * r * I₁) * (I₁ * Real.exp 1) :=
    mul_le_mul hd₁ hF₂ (norm_nonneg _) hr
  have h2 : ‖a₀‖ * ‖F₂ - a₀‖ ≤ I₁ * (2 * r * I₁) := mul_le_mul ha₀ hd₂ (norm_nonneg _) hI
  nlinarith

/-- **One zero with the pole.** For a nontrivial zero `ρ`, `N ≥ 2L(‖ρ‖ + 3)`, `c(‖ρ‖ + 1) ≤ N`:
`‖(log N/c) W_ρ/∫g² − m_ρ κ y_1²/(ρ(1−ρ))‖ ≤ m_ρ (C₁ c/N + C₂ E_N(ρ))`,
`E_N(ρ) = (6|y_1|P + P²(6 + ‖ρ‖)²/N)/N`. -/
theorem norm_log_div_mul_bulkLedger_sub_le {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) {L : ℕ} (hL : ∀ e ∈ E, e ≤ L) (y : ℕ → ℝ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN2 : 2 ≤ N)
    (hNL : 2 * L * (‖ρ‖ + 3) ≤ N) (hcN : c * (‖ρ‖ + 1) ≤ N) :
    ‖((Real.log N / c : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y c N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))‖ ≤
      zetaZeroConfig.mult ρ *
        (2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * poleCoefficient E y ^ 2 / (∫ u, φ u ^ 2) *
            (c / N) +
          (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) *
            ((6 * |poleCoefficient E y| * packetConst E y +
              packetConst E y ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N)) := by
  obtain ⟨hζ, hβ0, hβ1⟩ : riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 := ⟨hρ.1, hρ.2.1, hρ.2.2⟩
  have hz1 : riemannZeta (1 - ρ) = 0 :=
    RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ hβ0 hβ1
  obtain ⟨hρ3, hρ3'⟩ := three_lt_norm_of_mem hρ
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  rw [log_div_mul_bulkLedger zetaZeroConfig hφ hφc hφ2 E y hc (by omega) ρ]
  -- the atom factors
  have hw0 : 0 < c / N := div_pos hc hN0
  have hz₁n : ‖((c / N : ℝ) : ℂ) * gammaOf ρ‖ ≤ c / N * (‖ρ‖ + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
    exact mul_le_mul_of_nonneg_left (norm_gammaOf_le ρ) hw0.le
  have hz₂n : ‖((c / N : ℝ) : ℂ) * conj (gammaOf ρ)‖ ≤ c / N * (‖ρ‖ + 1) := by
    rw [norm_mul, Complex.norm_conj, ← norm_mul]; exact hz₁n
  have hw1 : c / N * (‖ρ‖ + 1) ≤ 1 := by rw [div_mul_eq_mul_div, div_le_one hN0]; exact hcN
  have ha₀n : ‖((∫ u, φ u : ℝ) : ℂ)‖ ≤ ∫ u, |φ u| := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_integral_le_integral_abs
  have hI₁0 : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
  have hF₂n : ‖conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)))‖ ≤
      (∫ u, |φ u|) * Real.exp 1 := by
    rw [Complex.norm_conj]; exact norm_paperFT_profile_le hφ hφsupp (hz₂n.trans hw1)
  have hd₁ : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) - ((∫ u, φ u : ℝ) : ℂ)‖ ≤
      2 * (c / N * (‖ρ‖ + 1)) * ∫ u, |φ u| :=
    (norm_paperFT_sub_integral_le hφ hφsupp (hz₁n.trans hw1)).trans (by gcongr)
  have hd₂ : ‖conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) -
      ((∫ u, φ u : ℝ) : ℂ)‖ ≤ 2 * (c / N * (‖ρ‖ + 1)) * ∫ u, |φ u| := by
    have e : conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) - ((∫ u, φ u : ℝ) : ℂ) =
        conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)) - ((∫ u, φ u : ℝ) : ℂ)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [e, Complex.norm_conj]
    exact (norm_paperFT_sub_integral_le hφ hφsupp (hz₂n.trans hw1)).trans (by gcongr)
  have hδ := norm_atom_product_sub_le hF₂n ha₀n hd₁ hd₂
  -- the Dirichlet factors
  have hX₁ := norm_dirichletPoly_packet_sub_pole_le hβ0 hβ1 hz1 hE hL y (N := N)
    (by nlinarith [norm_nonneg ρ]) hlog
  have hre1 : 0 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hre2 : (1 - ρ).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hn1 : ‖(1 : ℂ) - ρ‖ ≤ 1 + ‖ρ‖ := (norm_sub_le _ _).trans (by rw [norm_one])
  have hX₂ := norm_dirichletPoly_packet_sub_pole_le hre1 hre2 (by rw [sub_sub_cancel]; exact hζ)
    hE hL y (N := N) (by nlinarith [norm_nonneg ρ]) hlog
  have hσ2 : (1 - ρ).re - 1 = -ρ.re := by simp only [Complex.sub_re, Complex.one_re]; ring
  rw [hσ2] at hX₂
  have hNC : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hB : ((Real.log N / N : ℝ) : ℂ) * (dirichletPoly N (packetWeights E y N) (gammaOf ρ) *
      dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ))) =
      (((Real.sqrt (Real.log N) : ℝ) : ℂ) * dirichletPoly N (packetWeights E y N) (gammaOf ρ)) *
        (((Real.sqrt (Real.log N) : ℝ) : ℂ) *
          dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ))) / ((N : ℝ) : ℂ) := by
    have hSS : ((Real.sqrt (Real.log N) : ℝ) : ℂ) * ((Real.sqrt (Real.log N) : ℝ) : ℂ) =
        ((Real.log N : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hlog.le]
    rw [show ((Real.log N / N : ℝ) : ℂ) = ((Real.log N : ℝ) : ℂ) / ((N : ℝ) : ℂ) by push_cast; ring,
      ← hSS]
    field_simp
  rw [hB]
  -- forget the explicit factors
  generalize ((Real.sqrt (Real.log N) : ℝ) : ℂ) *
    dirichletPoly N (packetWeights E y N) (gammaOf ρ) = X₁ at hX₁ ⊢
  generalize ((Real.sqrt (Real.log N) : ℝ) : ℂ) *
    dirichletPoly N (packetWeights E y N) (gammaOf (1 - ρ)) = X₂ at hX₂ ⊢
  generalize paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) = F₁ at hδ ⊢
  generalize conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ))) = F₂ at hδ ⊢
  generalize hP : packetConst E y = P at hX₁ hX₂ ⊢
  generalize hp : poleCoefficient E y = p at hX₁ hX₂ ⊢
  have hP0 : 0 ≤ P := hP ▸ packetConst_nonneg E y
  -- `B − L`
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, norm_zero] at hρ3; linarith
  have hρ1 : (1 : ℂ) - ρ ≠ 0 := fun h => by rw [h, norm_zero] at hρ3'; linarith
  have hNN : ((N : ℝ) : ℂ) ^ ρ * ((N : ℝ) : ℂ) ^ (1 - ρ) = ((N : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hNC, add_sub_cancel, Complex.cpow_one]
  have hHH : ((p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) * ((p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))) =
      ((N : ℝ) : ℂ) * (((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
    calc ((p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) * ((p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))) =
          (p : ℂ) ^ 2 * (((N : ℝ) : ℂ) ^ ρ * ((N : ℝ) : ℂ) ^ (1 - ρ)) * (ρ⁻¹ * (1 - ρ)⁻¹) := by
          ring
      _ = (p : ℂ) ^ 2 * ((N : ℝ) : ℂ) * (ρ⁻¹ * (1 - ρ)⁻¹) := by rw [hNN]
      _ = ((N : ℝ) : ℂ) * (((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) := by
          rw [div_eq_mul_inv, mul_inv]; push_cast; ring
  have hBL := mul_div_sub_eq (X₁ := X₁) (X₂ := X₂) hNC hHH
  have hNρ : ‖((N : ℝ) : ℂ) ^ ρ‖ = (N : ℝ) ^ ρ.re := Complex.norm_cpow_eq_rpow_re_of_pos hN0 _
  have hNρ' : ‖((N : ℝ) : ℂ) ^ (1 - ρ)‖ = (N : ℝ) ^ (1 - ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]; simp
  have hpow1 : (N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re) = 1 := by
    rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]
  have hpow2 : (N : ℝ) ^ (1 - ρ.re) * (N : ℝ) ^ (ρ.re - 1) = 1 := by
    rw [← Real.rpow_add hN0, show 1 - ρ.re + (ρ.re - 1) = 0 by ring, Real.rpow_zero]
  have hpow3 : (N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re) = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_add hN0, show ρ.re - 1 + -ρ.re = -1 by ring, Real.rpow_neg_one]
  have hNβ : 0 ≤ (N : ℝ) ^ ρ.re := by positivity
  have hNβ' : 0 ≤ (N : ℝ) ^ (1 - ρ.re) := by positivity
  have ht1 : ‖(p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ) *
      (X₂ - (p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)))‖ ≤ 3 * |p| * P := by
    rw [norm_mul, norm_mul, norm_div, hNρ, Complex.norm_real, Real.norm_eq_abs]
    have hq : (5 + ‖1 - ρ‖) / ‖ρ‖ ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc |p| * ((N : ℝ) ^ ρ.re / ‖ρ‖) *
          ‖X₂ - (p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ))‖ ≤
          |p| * ((N : ℝ) ^ ρ.re / ‖ρ‖) * (P * (5 + ‖1 - ρ‖) * (N : ℝ) ^ (-ρ.re)) :=
          mul_le_mul_of_nonneg_left hX₂ (by positivity)
      _ = |p| * P * ((5 + ‖1 - ρ‖) / ‖ρ‖) * ((N : ℝ) ^ ρ.re * (N : ℝ) ^ (-ρ.re)) := by ring
      _ ≤ |p| * P * 3 * 1 := by
          rw [hpow1]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity))
            zero_le_one
      _ = 3 * |p| * P := by ring
  have ht2 : ‖(X₁ - (p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) *
      ((p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)))‖ ≤ 3 * |p| * P := by
    rw [norm_mul, norm_mul, norm_div, hNρ', Complex.norm_real, Real.norm_eq_abs]
    have hρle : ‖ρ‖ ≤ 1 + ‖(1 : ℂ) - ρ‖ := by
      have := norm_sub_le (1 : ℂ) ((1 : ℂ) - ρ)
      rw [sub_sub_cancel, norm_one] at this; exact this
    have hq : (5 + ‖ρ‖) / ‖(1 : ℂ) - ρ‖ ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc ‖X₁ - (p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)‖ *
          (|p| * ((N : ℝ) ^ (1 - ρ.re) / ‖(1 : ℂ) - ρ‖)) ≤
          (P * (5 + ‖ρ‖) * (N : ℝ) ^ (ρ.re - 1)) *
            (|p| * ((N : ℝ) ^ (1 - ρ.re) / ‖(1 : ℂ) - ρ‖)) :=
          mul_le_mul_of_nonneg_right hX₁ (by positivity)
      _ = |p| * P * ((5 + ‖ρ‖) / ‖(1 : ℂ) - ρ‖) *
            ((N : ℝ) ^ (1 - ρ.re) * (N : ℝ) ^ (ρ.re - 1)) := by ring
      _ ≤ |p| * P * 3 * 1 := by
          rw [hpow2]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity))
            zero_le_one
      _ = 3 * |p| * P := by ring
  have ht3 : ‖(X₁ - (p : ℂ) * (((N : ℝ) : ℂ) ^ ρ / ρ)) *
      (X₂ - (p : ℂ) * (((N : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)))‖ ≤ P ^ 2 * (6 + ‖ρ‖) ^ 2 / N := by
    rw [norm_mul]
    have h56 : (5 + ‖ρ‖) * (5 + ‖1 - ρ‖) ≤ (6 + ‖ρ‖) ^ 2 := by
      calc (5 + ‖ρ‖) * (5 + ‖1 - ρ‖) ≤ (6 + ‖ρ‖) * (6 + ‖ρ‖) :=
            mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
        _ = (6 + ‖ρ‖) ^ 2 := by ring
    calc _ ≤ (P * (5 + ‖ρ‖) * (N : ℝ) ^ (ρ.re - 1)) * (P * (5 + ‖1 - ρ‖) * (N : ℝ) ^ (-ρ.re)) :=
          mul_le_mul hX₁ hX₂ (norm_nonneg _) (by positivity)
      _ = P ^ 2 * ((5 + ‖ρ‖) * (5 + ‖1 - ρ‖)) * ((N : ℝ) ^ (ρ.re - 1) * (N : ℝ) ^ (-ρ.re)) := by
          ring
      _ ≤ P ^ 2 * (6 + ‖ρ‖) ^ 2 * (N : ℝ)⁻¹ := by
          rw [hpow3]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h56 (by positivity))
            (by positivity)
      _ = P ^ 2 * (6 + ‖ρ‖) ^ 2 / N := by ring
  have hEB : ‖X₁ * X₂ / ((N : ℝ) : ℂ) - ((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤
      (6 * |p| * P + P ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N := by
    rw [hBL, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN0]
    refine div_le_div_of_nonneg_right ?_ hN0.le
    refine (norm_add₃_le).trans ?_
    linarith
  -- `‖L‖` against the overlap
  have hLn : ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤ p ^ 2 / (‖ρ‖ * ‖(1 : ℂ) - ρ‖) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
  have hmul : 3 * ‖ρ‖ ≤ ‖ρ‖ * ‖(1 : ℂ) - ρ‖ := by
    have := mul_le_mul_of_nonneg_right hρ3'.le (norm_nonneg ρ)
    linarith [mul_comm ‖(1 : ℂ) - ρ‖ ‖ρ‖]
  have hr1 : (‖ρ‖ + 1) / (‖ρ‖ * ‖(1 : ℂ) - ρ‖) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hwL : c / N * (‖ρ‖ + 1) * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤ c / N * p ^ 2 := by
    calc c / N * (‖ρ‖ + 1) * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤
          c / N * (‖ρ‖ + 1) * (p ^ 2 / (‖ρ‖ * ‖(1 : ℂ) - ρ‖)) :=
          mul_le_mul_of_nonneg_left hLn (by positivity)
      _ = c / N * p ^ 2 * ((‖ρ‖ + 1) / (‖ρ‖ * ‖(1 : ℂ) - ρ‖)) := by ring
      _ ≤ c / N * p ^ 2 * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = c / N * p ^ 2 := by ring
  -- assemble
  have hI0 : (0 : ℝ) < ∫ u, φ u ^ 2 := hφ2
  have hICne : ((∫ u, φ u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI0.ne'
  have hmain : (zetaZeroConfig.mult ρ : ℂ) * (F₁ * F₂) / ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
        (X₁ * X₂ / ((N : ℝ) : ℂ)) - (zetaZeroConfig.mult ρ : ℂ) *
        (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * (((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))) =
      (zetaZeroConfig.mult ρ : ℂ) / ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
        ((F₁ * F₂ - ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ)) * (X₁ * X₂ / ((N : ℝ) : ℂ)) +
          ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ) *
            (X₁ * X₂ / ((N : ℝ) : ℂ) - ((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) := by
    push_cast
    field_simp
    ring
  rw [hmain, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hI0]
  have hcore := norm_ledger_core_le hδ ha₀n hEB
  set δ₀ := 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * (‖ρ‖ + 1)) with hδ₀
  have hδ₀1 : δ₀ ≤ 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 :=
    mul_le_of_le_one_right (by positivity) hw1
  have hδL : δ₀ * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ ≤
      2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * p ^ 2) := by
    rw [hδ₀, mul_assoc]
    exact mul_le_mul_of_nonneg_left hwL (by positivity)
  have hEB0 : 0 ≤ (6 * |p| * P + P ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N := by positivity
  have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hfin : δ₀ * ‖((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ))‖ + (δ₀ + (∫ u, |φ u|) ^ 2) *
      ((6 * |p| * P + P ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N) ≤
      2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * p ^ 2) +
        (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 *
          ((6 * |p| * P + P ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N) := by
    have h1 : δ₀ + (∫ u, |φ u|) ^ 2 ≤ (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 := by linarith
    exact add_le_add hδL (mul_le_mul_of_nonneg_right h1 hEB0)
  calc (zetaZeroConfig.mult ρ : ℝ) / (∫ u, φ u ^ 2) *
        ‖(F₁ * F₂ - ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ)) * (X₁ * X₂ / ((N : ℝ) : ℂ)) +
          ((∫ u, φ u : ℝ) : ℂ) * ((∫ u, φ u : ℝ) : ℂ) *
            (X₁ * X₂ / ((N : ℝ) : ℂ) - ((p ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))‖ ≤
        (zetaZeroConfig.mult ρ : ℝ) / (∫ u, φ u ^ 2) *
          (2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * (c / N * p ^ 2) +
            (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 *
              ((6 * |p| * P + P ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N)) :=
        mul_le_mul_of_nonneg_left (hcore.trans hfin) (by positivity)
    _ = _ := by ring

/-! ### All low zeros with the pole -/

/-- `|ρ(1 − ρ)| ≥ (1 + |γ_ρ|²)/2` for a nontrivial zero (`|Im ρ| > 3`). -/
theorem norm_mul_one_sub_ge {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    (1 + Complex.normSq (gammaOf ρ)) / 2 ≤ ‖ρ * (1 - ρ)‖ := by
  have h3 := ConjugateDiagonalGeometry.LogScaleHeckeDefect.three_lt_abs_im_of_mem_zetaZeroConfig hρ
  have hg : Complex.normSq (gammaOf ρ) = ‖ρ - 1 / 2‖ ^ 2 := by
    unfold gammaOf
    rw [Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_eq_norm_sq]
  have hid : ρ * (1 - ρ) = 1 / 4 - (ρ - 1 / 2) ^ 2 := by ring
  have hge : ‖ρ - 1 / 2‖ ^ 2 - 1 / 4 ≤ ‖ρ * (1 - ρ)‖ := by
    rw [hid]
    have h := norm_sub_norm_le ((ρ - 1 / 2) ^ 2) (1 / 4 : ℂ)
    have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
    rw [norm_pow, h4, norm_sub_rev ((ρ - 1 / 2) ^ 2) (1 / 4)] at h
    linarith
  have him : 9 ≤ ‖ρ - 1 / 2‖ ^ 2 := by
    have hi : (ρ - 1 / 2).im = ρ.im := by simp
    have h := Complex.abs_im_le_norm (ρ - 1 / 2)
    rw [hi] at h
    nlinarith [abs_nonneg ρ.im]
  rw [hg]; linarith

/-- The zero sum `Σ_ρ m_ρ/|ρ(1 − ρ)|` converges. -/
theorem summable_norm_mult_div :
    Summable fun ρ : zetaZeroConfig.carrier =>
      ‖(zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ))‖ := by
  refine (RHTower.summable_zetaZeroConfig.mul_left 2).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun ρ => ?_
  have hge := norm_mul_one_sub_ge ρ.2
  have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
    have := Complex.normSq_nonneg (gammaOf ρ); linarith
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  rw [norm_div, Complex.norm_natCast]
  calc (zetaZeroConfig.mult ρ : ℝ) / ‖(ρ : ℂ) * (1 - ρ)‖ ≤
        (zetaZeroConfig.mult ρ : ℝ) / ((1 + Complex.normSq (gammaOf ρ)) / 2) :=
        div_le_div_of_nonneg_left hm (half_pos hpos) hge
    _ = 2 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
        field_simp

/-- The partial zero sums up to a growing height converge to the full sum. -/
theorem tendsto_sum_lowZeros_mult_div {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      (zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ))) atTop
      (𝓝 (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)))) := by
  classical
  set f : zetaZeroConfig.carrier → ℂ := fun ρ =>
    (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)) with hf
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N (ρ : zetaZeroConfig.carrier) => if |(ρ : ℂ).im| ≤ T N then f ρ else 0)
    (g := f) (bound := fun ρ => ‖f ρ‖) summable_norm_mult_div
    (fun ρ => tendsto_const_nhds.congr' (by
      filter_upwards [hT.eventually (eventually_ge_atTop |(ρ : ℂ).im|)] with N hN
      rw [if_pos hN]))
    (Eventually.of_forall fun N ρ => by split_ifs <;> simp)
  refine hlim.congr fun N => ?_
  set s := (RHTower.lowZeros_finite (T N)).toFinset with hs
  rw [tsum_eq_sum (s := s.subtype (· ∈ zetaZeroConfig.carrier))]
  · rw [show (∑ ρ ∈ s.subtype (· ∈ zetaZeroConfig.carrier),
        if |(ρ : ℂ).im| ≤ T N then f ρ else 0) =
        ∑ ρ ∈ s.subtype (· ∈ zetaZeroConfig.carrier), f ρ from
      sum_congr rfl fun ρ hρ => by
        rw [Finset.mem_subtype, hs, (RHTower.lowZeros_finite _).mem_toFinset] at hρ
        rw [if_pos hρ.2]]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun z : ℂ =>
      (zetaZeroConfig.mult z : ℂ) / (z * (1 - z)))]
    rw [Finset.filter_true_of_mem fun z hz => by
      rw [hs, (RHTower.lowZeros_finite _).mem_toFinset] at hz; exact hz.1]
  · intro ρ hρ
    rw [Finset.mem_subtype, hs, (RHTower.lowZeros_finite _).mem_toFinset] at hρ
    rw [if_neg fun h => hρ ⟨ρ.2, h⟩]

/-- **All low zeros with the pole.** Along heights `T_N → ∞` with `c_N T_N log² T_N/N → 0` and
`T_N³ log² T_N/N² → 0`, the zeros of height `≤ T_N` contribute together
`(c_N/log N) κ y_1² Σ_ρ m_ρ/(ρ(1 − ρ)) + o(c_N/log N)` to the normalized complete form of a
conductor packet. -/
theorem tendsto_sum_bulkLedger_lowZeros_pole {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) (y : ℕ → ℝ) {c T : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hT : Tendsto T atTop atTop)
    (hcT : Tendsto (fun N : ℕ => c N * T N * Real.log (T N) ^ 2 / N) atTop (𝓝 0))
    (hT3 : Tendsto (fun N : ℕ => T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop
      (𝓝 ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)))) := by
  obtain ⟨K, T₀, hK, hT₀, hcount⟩ := exists_sum_mult_lowZeros_le
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∑ e ∈ E, e := ⟨_, rfl⟩
  have hL : ∀ e ∈ E, e ≤ L := fun e he => hLdef ▸
    Finset.single_le_sum (f := fun e : ℕ => e) (fun _ _ => Nat.zero_le _) he
  have hI₁0 : 0 ≤ ∫ u, |φ u| := integral_nonneg fun u => abs_nonneg _
  obtain ⟨C₁, hC₁⟩ : ∃ C, C = 2 * (Real.exp 1 + 1) * (∫ u, |φ u|) ^ 2 * poleCoefficient E y ^ 2 /
      (∫ u, φ u ^ 2) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C, C = (2 * Real.exp 1 + 3) * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) :=
    ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hP0 : 0 ≤ packetConst E y := packetConst_nonneg E y
  -- the target sums
  have htarget := (tendsto_sum_lowZeros_mult_div hT).const_mul
    ((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ))
  -- the error sums
  obtain ⟨err, herr⟩ : ∃ f : ℕ → ℂ, f = fun N => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      (((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ -
        (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
          (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))) := ⟨_, rfl⟩
  have hbound : Tendsto (fun N : ℕ => K * (C₁ + C₂ * (6 * |poleCoefficient E y| * packetConst E y)) *
      (c N * T N * Real.log (T N) ^ 2 / N) + K * C₂ * packetConst E y ^ 2 * 64 *
        (T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2)) atTop (𝓝 0) := by
    have := (hcT.const_mul (K * (C₁ + C₂ * (6 * |poleCoefficient E y| * packetConst E y)))).add
      (hT3.const_mul (K * C₂ * packetConst E y ^ 2 * 64))
    simpa using this
  have hL1 : (0 : ℝ) < 1 / (4 * ((L : ℝ) + 1)) := by positivity
  have hev := (((hT.eventually (eventually_ge_atTop T₀)).and
    (hcT.eventually (gt_mem_nhds hL1))).and (eventually_ge_atTop (16 * (L + 1))))
  have herr0 : Tendsto err atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev] with N ⟨⟨hTN, hcTN⟩, hNL⟩
    have hT3' : 3 ≤ T N := hT₀.trans hTN
    have hN16 : 16 * ((L : ℝ) + 1) ≤ N := by exact_mod_cast hNL
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hN0 : (0 : ℝ) < N := by linarith
    have hN2 : 2 ≤ N := by omega
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hlogT : 1 ≤ Real.log (T N) := by
      have h3 : 1 ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      exact h3.trans (Real.log_le_log (by norm_num) hT3')
    have hl2 : 1 ≤ Real.log (T N) ^ 2 := by nlinarith
    have hl0 : 0 ≤ T N * Real.log (T N) ^ 2 := by positivity
    have hcTle : c N * T N * Real.log (T N) ^ 2 * (4 * ((L : ℝ) + 1)) ≤ N := by
      rw [div_lt_iff₀ hN0, one_div_mul_eq_div, lt_div_iff₀ (by positivity)] at hcTN
      linarith
    have hcT1 : c N * T N * (4 * ((L : ℝ) + 1)) ≤ N := by
      have h1 : c N * T N ≤ c N * T N * Real.log (T N) ^ 2 :=
        le_mul_of_one_le_right (by positivity) hl2
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 4 * ((L : ℝ) + 1))
      linarith
    have hTle : T N ≤ c N * T N := le_mul_of_one_le_left (by linarith) (hc1 N)
    have hper : ∀ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
        ‖((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ -
          (zetaZeroConfig.mult ρ : ℂ) * (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) *
            (((poleCoefficient E y ^ 2 : ℝ) : ℂ) / (ρ * (1 - ρ)))‖ ≤
        zetaZeroConfig.mult ρ * (C₁ * (c N / N) +
          C₂ * ((6 * |poleCoefficient E y| * packetConst E y + packetConst E y ^ 2 * (7 + T N) ^ 2 / N) / N)) := by
      intro ρ hρ
      have hρ' := (RHTower.lowZeros_finite _).mem_toFinset.mp hρ
      have hnorm := norm_le_of_mem_lowZeros hρ'
      have hNL' : 2 * (L : ℝ) * (‖ρ‖ + 3) ≤ N := by
        have h1 : 2 * (L : ℝ) * (‖ρ‖ + 3) ≤ 2 * L * ((1 + T N) + 3) := by gcongr
        have h2 : 2 * (L : ℝ) * T N ≤ N / 2 := by nlinarith
        linarith
      have hcN' : c N * (‖ρ‖ + 1) ≤ N := by
        have h1 : c N * (‖ρ‖ + 1) ≤ c N * ((1 + T N) + 1) := by gcongr
        have h2 : c N * 2 ≤ c N * T N := by nlinarith
        nlinarith
      have h := norm_log_div_mul_bulkLedger_sub_le hφ hφsupp hφ2 hE hL y hρ'.1 hc0 hN2 hNL' hcN'
      rw [← hC₁, ← hC₂] at h
      refine h.trans ?_
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      have h67 : (6 + ‖ρ‖) ^ 2 ≤ (7 + T N) ^ 2 := by
        have : 0 ≤ 6 + ‖ρ‖ := by positivity
        exact pow_le_pow_left₀ this (by linarith) 2
      have hstep : (6 * |poleCoefficient E y| * packetConst E y + packetConst E y ^ 2 * (6 + ‖ρ‖) ^ 2 / N) / N ≤
          (6 * |poleCoefficient E y| * packetConst E y + packetConst E y ^ 2 * (7 + T N) ^ 2 / N) / N := by
        refine div_le_div_of_nonneg_right ?_ hN0.le
        have : packetConst E y ^ 2 * (6 + ‖ρ‖) ^ 2 / N ≤ packetConst E y ^ 2 * (7 + T N) ^ 2 / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h67 (by positivity)) hN0.le
        linarith
      exact mul_le_mul_of_nonneg_left (by
        have := mul_le_mul_of_nonneg_left hstep hC₂0
        linarith) hm
    rw [herr]
    refine (norm_sum_le _ _).trans ((sum_le_sum hper).trans ?_)
    rw [← sum_mul]
    have hX : 0 ≤ C₁ * (c N / N) + C₂ * ((6 * |poleCoefficient E y| * packetConst E y + packetConst E y ^ 2 * (7 + T N) ^ 2 / N) / N) := by
      positivity
    have hcnt := mul_le_mul_of_nonneg_right (hcount _ hTN) hX
    refine hcnt.trans ?_
    have h1 : T N * Real.log (T N) ^ 2 ≤ c N * T N * Real.log (T N) ^ 2 := by
      have := le_mul_of_one_le_left hl0 (hc1 N)
      linarith [mul_assoc (c N) (T N) (Real.log (T N) ^ 2)]
    have h7 : (7 + T N) ^ 2 ≤ 64 * T N ^ 2 := by nlinarith
    have h2 : T N * Real.log (T N) ^ 2 * (7 + T N) ^ 2 ≤ 64 * (T N ^ 3 * Real.log (T N) ^ 2) := by
      calc T N * Real.log (T N) ^ 2 * (7 + T N) ^ 2 ≤
            T N * Real.log (T N) ^ 2 * (64 * T N ^ 2) := mul_le_mul_of_nonneg_left h7 hl0
        _ = 64 * (T N ^ 3 * Real.log (T N) ^ 2) := by ring
    have hN2' : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e1 : K * (T N * Real.log (T N) ^ 2) *
        (C₁ * (c N / N) + C₂ * ((6 * |poleCoefficient E y| * packetConst E y + packetConst E y ^ 2 * (7 + T N) ^ 2 / N) / N)) =
        K * C₁ * (c N * T N * Real.log (T N) ^ 2 / N) +
          K * C₂ * (6 * |poleCoefficient E y| * packetConst E y) * (T N * Real.log (T N) ^ 2 / N) +
          K * C₂ * packetConst E y ^ 2 * (T N * Real.log (T N) ^ 2 * (7 + T N) ^ 2 / (N : ℝ) ^ 2) := by
      field_simp
      ring
    rw [e1]
    have hA : T N * Real.log (T N) ^ 2 / N ≤ c N * T N * Real.log (T N) ^ 2 / N :=
      div_le_div_of_nonneg_right h1 hN0.le
    have hB : T N * Real.log (T N) ^ 2 * (7 + T N) ^ 2 / (N : ℝ) ^ 2 ≤
        64 * (T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right h2 hN2'.le
    have hk1 : 0 ≤ K * C₂ * (6 * |poleCoefficient E y| * packetConst E y) := by positivity
    have hk2 : 0 ≤ K * C₂ * packetConst E y ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hA hk1
    have h4 := mul_le_mul_of_nonneg_left hB hk2
    linarith
  have hsplit : ∀ N : ℕ, ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ =
      (((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 : ℝ) : ℂ) * ((poleCoefficient E y ^ 2 : ℝ) : ℂ) *
        ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
          (zetaZeroConfig.mult ρ : ℂ) / (ρ * (1 - ρ)) + err N := by
    intro N
    rw [herr, Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun ρ _ => ?_
    ring
  have := htarget.add herr0
  rw [add_zero] at this
  exact this.congr fun N => (hsplit N).symm

/-- **The archimedean genus**: `Σ_ρ m_ρ/(ρ(1 − ρ)) = 2 + γ − log 4π` over the nontrivial zeros
(Hadamard product of `ξ`, RHTower). -/
theorem tsum_mult_div_zero_mul_one_sub_eq :
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)) =
      (RHTower.poleSharpConstant : ℂ) := by
  have hsC : Summable fun q : RHTower.XiZeroCopy =>
      (1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    by_contra h
    have h0 := tsum_eq_zero_of_not_summable h
    rw [RHTower.tsum_inv_zero_mul_one_sub_zero] at h0
    exact RHTower.poleSharpConstant_pos.ne' (by exact_mod_cast h0)
  have hF : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)) := summable_norm_mult_div.of_norm
  have hre := tsum_xiZeroCopy_eq_zetaCarrier (g := fun z : ℂ => ((1 : ℂ) / (z * (1 - z))).re)
    (hsC.mapL Complex.reCLM)
  have him := tsum_xiZeroCopy_eq_zetaCarrier (g := fun z : ℂ => ((1 : ℂ) / (z * (1 - z))).im)
    (hsC.mapL Complex.imCLM)
  have hq := RHTower.tsum_inv_zero_mul_one_sub_zero
  have hqre : (∑' q : RHTower.XiZeroCopy, ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re) =
      RHTower.poleSharpConstant := by
    have := (hsC.hasSum.mapL Complex.reCLM).tsum_eq
    simp only [Complex.reCLM_apply] at this
    rw [this, hq, Complex.ofReal_re]
  have hqim : (∑' q : RHTower.XiZeroCopy, ((1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).im) = 0 := by
    have := (hsC.hasSum.mapL Complex.imCLM).tsum_eq
    simp only [Complex.imCLM_apply] at this
    rw [this, hq, Complex.ofReal_im]
  have hterm : ∀ ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) / ((ρ : ℂ) * (1 - ρ)) =
      ((zetaZeroConfig.mult ρ : ℝ) : ℂ) * ((1 : ℂ) / ((ρ : ℂ) * (1 - ρ))) := fun ρ => by
    push_cast; ring
  have hFre := (hF.hasSum.mapL Complex.reCLM).tsum_eq
  have hFim := (hF.hasSum.mapL Complex.imCLM).tsum_eq
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hFre hFim
  apply Complex.ext
  · rw [← hFre, Complex.ofReal_re, ← hqre, hre]
    refine tsum_congr fun ρ => ?_
    rw [hterm, Complex.re_ofReal_mul]
  · rw [← hFim, Complex.ofReal_im, ← hqim, him]
    refine tsum_congr fun ρ => ?_
    rw [hterm, Complex.im_ofReal_mul]

/-- **The bulk at the pole reads the archimedean genus.** Along heights `T_N → ∞` with
`c_N T_N log² T_N/N → 0` and `T_N³ log² T_N/N² → 0`, the zeros of height `≤ T_N` together
contribute `(c_N/log N) κ y_1² (2 + γ − log 4π) + o(c_N/log N)` to the normalized complete form of
every conductor packet, `κ = (∫φ)²/∫φ²`. -/
theorem tendsto_sum_bulkLedger_lowZeros_genus {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) (y : ℕ → ℝ) {c T : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hT : Tendsto T atTop atTop)
    (hcT : Tendsto (fun N : ℕ => c N * T N * Real.log (T N) ^ 2 / N) atTop (𝓝 0))
    (hT3 : Tendsto (fun N : ℕ => T N ^ 3 * Real.log (T N) ^ 2 / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite (T N)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop
      (𝓝 (((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * poleCoefficient E y ^ 2 *
        RHTower.poleSharpConstant : ℝ) : ℂ))) := by
  have h := tendsto_sum_bulkLedger_lowZeros_pole hφ hφsupp hφ2 hE y hc1 hT hcT hT3
  rw [tsum_mult_div_zero_mul_one_sub_eq] at h
  convert h using 2
  push_cast; ring

/-- **The genus at power heights.** For `0 < θ < 2/3` and `c_N log² N/N^{1−θ} → 0`, the zeros of
height `≤ N^θ` contribute `(c_N/log N) κ y_1² (2 + γ − log 4π) + o(c_N/log N)`. -/
theorem tendsto_sum_bulkLedger_lowZeros_genus_rpow {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {E : Finset ℕ}
    (hE : ∀ e ∈ E, 1 ≤ e) (y : ℕ → ℝ) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N)
    (hcN : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / (N : ℝ) ^ (1 - θ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ ρ ∈ (RHTower.lowZeros_finite ((N : ℝ) ^ θ)).toFinset,
      ((Real.log N / c N : ℝ) : ℂ) * bulkLedger zetaZeroConfig φ E y (c N) N ρ) atTop
      (𝓝 (((((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * poleCoefficient E y ^ 2 *
        RHTower.poleSharpConstant : ℝ) : ℂ))) := by
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hT : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop := (tendsto_rpow_atTop hθ0).comp hNat
  have hcT : Tendsto (fun N : ℕ => c N * (N : ℝ) ^ θ * Real.log ((N : ℝ) ^ θ) ^ 2 / N) atTop
      (𝓝 0) := by
    have h := hcN.const_mul (θ ^ 2)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.log_rpow hN0, Real.rpow_sub hN0, Real.rpow_one]
    have : (0 : ℝ) < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hN0 _
    field_simp
  set a := (2 - 3 * θ) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hlo : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ a) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero).comp hNat
  have hT3 : Tendsto (fun N : ℕ => ((N : ℝ) ^ θ) ^ 3 * Real.log ((N : ℝ) ^ θ) ^ 2 / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have h := (hlo.pow 2).const_mul (θ ^ 2)
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h3 : ((N : ℝ) ^ θ) ^ 3 = (N : ℝ) ^ (3 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have h2 : ((N : ℝ) ^ a) ^ 2 = (N : ℝ) ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    have hsum : (N : ℝ) ^ (3 * θ) * (N : ℝ) ^ (2 * a) = (N : ℝ) ^ 2 := by
      rw [← Real.rpow_add hN0, show 3 * θ + 2 * a = ((2 : ℕ) : ℝ) by rw [ha]; push_cast; ring,
        Real.rpow_natCast]
    have hpa : 0 < (N : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos hN0 _
    rw [Real.log_rpow hN0, h3, div_pow, h2, ← hsum]
    field_simp
  exact tendsto_sum_bulkLedger_lowZeros_genus hφ hφsupp hφ2 hE y hc1 hT hcT hT3

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
