import GaloisForLFunctions.RHTower.ThmEUniformArchimedean
import GaloisForLFunctions.RHTower.FamilyTaperBridge

/-!
# The archimedean diagonal at any bandwidth, uniformly in the modulus

The evaluation `𝓜[μ_q, μ_q] = 2π b L ∫_T^{2T} μ_q² + O(l² log L)` uses only the taper facts that hold at
every bandwidth (`LocalHypsCoreW`): the shear identity for the square integral and the increment bound for
`μ_q` (`mumu_core_wide`).  The fixed-modulus statement (`mumu_fixed_wide`) and the quadratic interpolation in
the shift `log q/2π` (`mumu_uniform_of_three_wide`) then give

`|𝓜[μ_q, μ_q] − 2π b L ∫ μ_q²| ≤ C (1 + log q)² l² log L`        (`prop_mumu_uniform_wide`)

for every bandwidth ratio `λ > 0`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide

noncomputable section

namespace RHTower

variable {cϱ : ℝ}

/-- **The diagonal evaluation at any bandwidth.** -/
theorem mumu_core_wide {κ q : ℕ} {p : Setting} {F : LocalFun} (hΓq : GammaFactsChi κ q) (hF : LocalHypsCoreW cϱ p F) (hT2 : 2 ≤ p.T)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |muq κ q τ| ≤ A)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t) :
    |Mform F.Phi p.T (muq κ q) (muq κ q)
        - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2|
      ≤ (A ^ 2 + A * K) * (∫ x, F.Phi x ^ 2 * |x|)
        + A * K * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
  have hμc : Continuous (muq κ q) := hΓq.smooth.continuous
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hGc : Continuous fun qq : ℝ × ℝ => muq κ q qq.1 * muq κ q qq.2 := by fun_prop
  set c : ℝ := ∫ τ' in Icc p.T (2 * p.T), muq κ q τ' ^ 2 with hc
  have hc' : ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2 = c := by
    rw [intervalIntegral.integral_of_le (by linarith), hc, integral_Icc_eq_integral_Ioc]
  have hshear : Mform F.Phi p.T (muq κ q) (muq κ q)
      = ∫ x, F.Phi x ^ 2 * ∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ' := by
    unfold Mform
    simp only [mul_assoc]
    exact sqIntegral_shear hΦc hGc
  have hfInt : Integrable (fun x => F.Phi x ^ 2 * ∫ τ' in Ix p.T x,
      muq κ q (x + τ') * muq κ q τ') := integrable_sq_mul_inner hΦc hGc
  have hgInt : Integrable (fun x => F.Phi x ^ 2 * c) := hF.Phi_sq_integrable.mul_const c
  have hmain : 2 * π * F.b * p.L * c = ∫ x, F.Phi x ^ 2 * c := by
    rw [integral_mul_const c (fun x => F.Phi x ^ 2), hF.Phi_sq_integral]
  rw [hc', hshear, hmain, ← integral_sub hfInt hgInt]
  have hpt : ∀ x : ℝ, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
      - F.Phi x ^ 2 * c|
      ≤ (A ^ 2 + A * K) * (F.Phi x ^ 2 * |x|) + A * K * (F.Phi x ^ 2 * x ^ 2) := by
    intro x
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (F.Phi x))]
    have hinner := abs_inner_sub_le_chi hΓq hT2 hA0 hμl hK0 hKinc x
    rw [← hc] at hinner
    calc F.Phi x ^ 2 * |(∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ') - c|
        ≤ F.Phi x ^ 2 * ((A ^ 2 + A * K) * |x| + A * K * x ^ 2) := by
          gcongr
      _ = (A ^ 2 + A * K) * (F.Phi x ^ 2 * |x|) + A * K * (F.Phi x ^ 2 * x ^ 2) := by ring
  calc |∫ x, (F.Phi x ^ 2 * (∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
        - F.Phi x ^ 2 * c)|
      ≤ ∫ x, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
        - F.Phi x ^ 2 * c| := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Real.norm_eq_abs]
    _ ≤ ∫ x, ((A ^ 2 + A * K) * (F.Phi x ^ 2 * |x|) + A * K * (F.Phi x ^ 2 * x ^ 2)) :=
        integral_mono (hfInt.sub hgInt).abs
          ((hF.Phi_sq_mul_abs_integrable.const_mul _).add
            (hF.Phi_sq_mul_sq_integrable.const_mul _)) hpt
    _ = (A ^ 2 + A * K) * (∫ x, F.Phi x ^ 2 * |x|)
        + A * K * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
        rw [integral_add (hF.Phi_sq_mul_abs_integrable.const_mul _)
          (hF.Phi_sq_mul_sq_integrable.const_mul _),
          integral_const_mul, integral_const_mul]


variable (cϱ lam : ℝ)

/-- The fixed-modulus diagonal evaluation at any bandwidth. -/
theorem mumu_fixed_wide {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → |mumuErr κ q p F| ≤ C * (Zeta23.l p.T ^ 2 * Real.log p.L) := by
  have hΓq := GammaChi.gammaFactsChi hκ hq
  obtain ⟨K, hK0, hKinc⟩ := muq_increment_bound hΓq hq
  obtain ⟨Ca, T₀a, hCa0, hT₀a⟩ := muq_abs_le κ q hΓq hq
  refine ⟨(Ca ^ 2 + Ca * K) * (12 + 4 * max 0 (Real.log cϱ))
      + (Ca ^ 2 + Ca * K) * (8 + 2 * cϱ ^ 2), max T₀a 2, by positivity,
    fun p F hplam hT hF => ?_⟩
  have hT2 : 2 ≤ p.T := le_trans (le_max_right _ _) hT
  have hμl := hT₀a p (le_trans (le_max_left _ _) hT)
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hA0 : (0 : ℝ) ≤ Ca * p.l := by positivity
  have hcore := mumu_core_wide hΓq hF hT2 hA0 hμl hK0 hKinc
  have hI1 := hF.integral_Phi_sq_mul_abs_le
  have hI2 := hF.integral_Phi_sq_mul_sq_le
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hlog2 : 2 ≤ Real.log p.L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  have hcϱ4 : 4 ≤ cϱ := hF.four_le_cϱ
  have hw1 : 1 ≤ p.w := hF.one_le_w
  have hm0 : 0 ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hA : ∫ x, F.Phi x ^ 2 * |x| ≤ (12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L := by
    refine hI1.trans ?_
    have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := by
      calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
            apply Real.log_le_log (by positivity)
            apply div_le_self (by positivity)
            linarith
        _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
        _ ≤ max 0 (Real.log cϱ) + Real.log p.L := by
            have := le_max_right (0 : ℝ) (Real.log cϱ)
            linarith
    have h8 : 8 * max 0 (Real.log cϱ) ≤ 4 * max 0 (Real.log cϱ) * Real.log p.L := by
      nlinarith only [hm0, hlog2]
    nlinarith only [hlogbound, h8, hlog2]
  have hB : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * cϱ ^ 2 := by
    refine hI2.trans ?_
    have hdiv : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have hdivnn : 0 ≤ cϱ / p.w := by positivity
    have : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := pow_le_pow_left₀ hdivnn hdiv 2
    linarith
  have hI1nn : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| := integral_nonneg fun x => by positivity
  have hI2nn : 0 ≤ ∫ x, F.Phi x ^ 2 * x ^ 2 := integral_nonneg fun x => by positivity
  unfold mumuErr
  refine hcore.trans ?_
  have hl2 : (1 : ℝ) ≤ p.l ^ 2 := one_le_pow₀ hl1
  have hKCa : (0:ℝ) ≤ Ca * K := by positivity
  have hCK : ((Ca * p.l) ^ 2 + (Ca * p.l) * K) ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 := by
    have : (Ca * p.l) * K ≤ Ca * K * p.l ^ 2 := by
      have h := mul_le_mul_of_nonneg_left (show p.l ≤ p.l ^ 2 by nlinarith only [hl1]) hKCa
      linarith only [h]
    have e : (Ca * p.l) ^ 2 = Ca ^ 2 * p.l ^ 2 := by ring
    linarith only [this, e]
  have hCK0 : (0:ℝ) ≤ Ca ^ 2 + Ca * K := by positivity
  have hAK0 : (0 : ℝ) ≤ (Ca * p.l) ^ 2 + (Ca * p.l) * K := by positivity
  have hlogL0 : 0 ≤ Real.log p.L := by linarith
  have s1 : ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (∫ x, F.Phi x ^ 2 * |x|)
      ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L) :=
    mul_le_mul hCK hA hI1nn (by positivity)
  have s2 : (Ca * p.l) * K * (∫ x, F.Phi x ^ 2 * x ^ 2)
      ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((8 + 2 * cϱ ^ 2) * Real.log p.L) := by
    have h1 : (Ca * p.l) * K ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 := by
      have : 0 ≤ (Ca * p.l) ^ 2 := sq_nonneg _
      linarith only [hCK, this]
    have h2 : 8 + 2 * cϱ ^ 2 ≤ (8 + 2 * cϱ ^ 2) * Real.log p.L := by
      have : 0 ≤ 8 + 2 * cϱ ^ 2 := by positivity
      nlinarith only [this, hlog2]
    exact mul_le_mul h1 (hB.trans h2) hI2nn (by positivity)
  have e : ((Ca ^ 2 + Ca * K) * (12 + 4 * max 0 (Real.log cϱ))
      + (Ca ^ 2 + Ca * K) * (8 + 2 * cϱ ^ 2)) * (Zeta23.l p.T ^ 2 * Real.log p.L)
      = (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        + (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((8 + 2 * cϱ ^ 2) * Real.log p.L) := by ring
  rw [e]
  linarith only [s1, s2]

/-- From the three moduli `1, 2, 3` to every modulus, for a fixed parity. -/
theorem mumu_uniform_of_three_wide {κ : ℕ} (hκ : κ ≤ 1) {C₁ C₂ C₃ T₁ T₂ T₃ : ℝ}
    (h₁ : ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₁ ≤ p.T → LocalHypsCoreW cϱ p F →
      |mumuErr κ 1 p F| ≤ C₁ * (Zeta23.l p.T ^ 2 * Real.log p.L))
    (h₂ : ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₂ ≤ p.T → LocalHypsCoreW cϱ p F →
      |mumuErr κ 2 p F| ≤ C₂ * (Zeta23.l p.T ^ 2 * Real.log p.L))
    (h₃ : ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₃ ≤ p.T → LocalHypsCoreW cϱ p F →
      |mumuErr κ 3 p F| ≤ C₃ * (Zeta23.l p.T ^ 2 * Real.log p.L))
    {q : ℕ} (hq : 1 ≤ q) (p : Setting) (F : LocalFun) (hp : p.lam = lam)
    (hT : max (max T₁ T₂) T₃ ≤ p.T) (hF : LocalHypsCoreW cϱ p F) :
    |mumuErr κ q p F|
      ≤ interpConst * (C₁ + C₂ + C₃) * (1 + Real.log q) ^ 2
          * (Zeta23.l p.T ^ 2 * Real.log p.L) := by
  obtain ⟨ha, hab, hb1⟩ := interp_nodes
  have hu : Continuous (muq κ 1) := (GammaChi.gammaFactsChi hκ le_rfl).smooth.continuous
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hΦe := hF.Phi_even
  set B := Zeta23.l p.T ^ 2 * Real.log p.L with hB
  have hB0 : 0 ≤ B := mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [hF.eight_le_L]))
  set x₁ := Mform F.Phi p.T (muq κ 1) (fun _ => 1)
    - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ 1 τ
  set x₂ := Mform F.Phi p.T (fun _ => 1) (fun _ => 1) - 2 * π * F.b * p.L * p.T
  have hquad : ∀ s, mumuShiftErr F.Phi p.T F.b p.L (muq κ 1) s
      = mumuShiftErr F.Phi p.T F.b p.L (muq κ 1) 0 + 2 * s * x₁ + s ^ 2 * x₂ := fun s =>
    mumuShiftErr_eq_quadratic hΦ hΦe hu F.b p.L s
  have hT₁ : T₁ ≤ p.T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hT₂ : T₂ ≤ p.T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hT₃ : T₃ ≤ p.T := (le_max_right _ _).trans hT
  have e₁ : mumuShiftErr F.Phi p.T F.b p.L (muq κ 1) 0 = mumuErr κ 1 p F := by
    rw [mumuErr_eq_shiftErr le_rfl, Nat.cast_one, Real.log_one, zero_div]
  have e₂ : mumuShiftErr F.Phi p.T F.b p.L (muq κ 1) (Real.log 2 / (2 * π)) = mumuErr κ 2 p F := by
    rw [mumuErr_eq_shiftErr (by norm_num)]; norm_num
  have e₃ : mumuShiftErr F.Phi p.T F.b p.L (muq κ 1) (Real.log 3 / (2 * π)) = mumuErr κ 3 p F := by
    rw [mumuErr_eq_shiftErr (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.log q / (2 * π) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (by positivity)
  have key := abs_quad_le_of_interp ha hab hb1 (hquad _) (hquad _) hs0
  rw [← hquad, ← mumuErr_eq_shiftErr hq, e₁, e₂, e₃] at key
  refine key.trans ?_
  have hsq : (1 + Real.log q / (2 * π)) ^ 2 ≤ (1 + Real.log q) ^ 2 := by
    have hle : Real.log q / (2 * π) ≤ Real.log q :=
      div_le_self (Real.log_nonneg (by exact_mod_cast hq)) (by nlinarith [Real.pi_gt_three])
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hsum : |mumuErr κ 1 p F| + |mumuErr κ 2 p F| + |mumuErr κ 3 p F| ≤ (C₁ + C₂ + C₃) * B := by
    have := h₁ p F hp hT₁ hF; have := h₂ p F hp hT₂ hF; have := h₃ p F hp hT₃ hF
    linarith
  have hK := interpConst_pos
  change (1 + Real.log q / (2 * π)) ^ 2 * interpConst
      * (|mumuErr κ 1 p F| + |mumuErr κ 2 p F| + |mumuErr κ 3 p F|) ≤ _
  calc (1 + Real.log q / (2 * π)) ^ 2 * interpConst
        * (|mumuErr κ 1 p F| + |mumuErr κ 2 p F| + |mumuErr κ 3 p F|)
      ≤ (1 + Real.log q) ^ 2 * interpConst * ((C₁ + C₂ + C₃) * B) := by
        gcongr
    _ = interpConst * (C₁ + C₂ + C₃) * (1 + Real.log q) ^ 2 * B := by ring

/-- **[prop:mumu] for `L(s, χ)` at any bandwidth, uniformly in the modulus.** -/
theorem prop_mumu_uniform_wide :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ (p : Setting) (F : LocalFun),
      p.lam = lam → T₀ ≤ p.T → LocalHypsCoreW cϱ p F →
      |Mform F.Phi p.T (muq κ q) (muq κ q)
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2|
        ≤ C * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L) := by
  obtain ⟨A₁, S₁, hA₁, a₁⟩ := mumu_fixed_wide cϱ lam (κ := 0) (q := 1) (by norm_num) le_rfl
  obtain ⟨A₂, S₂, hA₂, a₂⟩ := mumu_fixed_wide cϱ lam (κ := 0) (q := 2) (by norm_num) (by norm_num)
  obtain ⟨A₃, S₃, hA₃, a₃⟩ := mumu_fixed_wide cϱ lam (κ := 0) (q := 3) (by norm_num) (by norm_num)
  obtain ⟨B₁, R₁, hB₁, b₁⟩ := mumu_fixed_wide cϱ lam (κ := 1) (q := 1) le_rfl le_rfl
  obtain ⟨B₂, R₂, hB₂, b₂⟩ := mumu_fixed_wide cϱ lam (κ := 1) (q := 2) le_rfl (by norm_num)
  obtain ⟨B₃, R₃, hB₃, b₃⟩ := mumu_fixed_wide cϱ lam (κ := 1) (q := 3) le_rfl (by norm_num)
  have hK := interpConst_pos
  refine ⟨interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃),
    max (max (max S₁ S₂) S₃) (max (max R₁ R₂) R₃), by positivity,
    fun κ q hκ hq p F hp hT hF => ?_⟩
  have hTA : max (max S₁ S₂) S₃ ≤ p.T := (le_max_left _ _).trans hT
  have hTB : max (max R₁ R₂) R₃ ≤ p.T := (le_max_right _ _).trans hT
  have hB0 : 0 ≤ (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L) :=
    mul_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [hF.eight_le_L])))
  interval_cases κ
  · have h := mumu_uniform_of_three_wide cϱ lam (by norm_num) a₁ a₂ a₃ hq p F hp hTA hF
    refine h.trans ?_
    have : interpConst * (A₁ + A₂ + A₃) ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) :=
      mul_le_mul_of_nonneg_left (by linarith) hK.le
    calc interpConst * (A₁ + A₂ + A₃) * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L)
        = interpConst * (A₁ + A₂ + A₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := by ring
      _ ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := mul_le_mul_of_nonneg_right this hB0
      _ = _ := by ring
  · have h := mumu_uniform_of_three_wide cϱ lam le_rfl b₁ b₂ b₃ hq p F hp hTB hF
    refine h.trans ?_
    have : interpConst * (B₁ + B₂ + B₃) ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) :=
      mul_le_mul_of_nonneg_left (by linarith) hK.le
    calc interpConst * (B₁ + B₂ + B₃) * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L)
        = interpConst * (B₁ + B₂ + B₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := by ring
      _ ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := mul_le_mul_of_nonneg_right this hB0
      _ = _ := by ring

end RHTower
