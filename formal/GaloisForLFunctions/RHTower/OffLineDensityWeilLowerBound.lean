import GaloisForLFunctions.RHTower.LowHeightHodgeExclusion

/-!
# Depth and off-line density bound the Weil form from below

Let `Z` be a zero configuration all of whose zeros satisfy `|β - ½| ≤ η`, and suppose every unit
window `(t, t + 1]` carries off-line multiplicity at most `D` (`OffLineDensityBound`).  Then
(`re_W_ge_of_depth_offLineDensity`) every continuous test supported in `[-a, a]` satisfies

> `Re W(f, f) ≥ -3500 (2a + 3) D e^{2η(a+2)} ∫|f|²`.

No polar constraint and no smoothness is needed, and zeros on the critical line do not enter:
for `D = 0` the bound is Weil positivity.

**Proof.**
* **Depth differences.**  With `x_ρ = γ_ρ + i(½ - β_ρ)`, each term of the Weil form is
  `m_ρ Re(h_f(x_ρ) conj h_f(x̄_ρ)) ≥ -m_ρ |h_f(x_ρ) - h_f(x̄_ρ)|²/4`.  The difference is the pairing
  of `f` with the depth exponential `φ_ρ(u) = e^{ix_ρu} - e^{ix̄_ρu}`, which vanishes on the line.
* **Weighted Bessel inequality** (`weighted_bessel`).  For a weight `h ≥ c₀` on the support of
  `f`, pointwise AM-GM and the Schur test give
  `Σ m_ρ |∫ f φ_ρ|² ≤ (B/c₀) ∫|f|²`, where `B` bounds the row and column sums of the Gram kernel
  `m |∫ h φ_ρ conj(φ_σ)|`.
* **The plateau** `h_J = Σ_{|j| ≤ J} w₁(· - j)`, `J = ⌈a⌉`, is at least `(3/4)^{5/2}` on `[-J, J]`,
  and `ĥ_J(z) = (Σ_j e^{izj}) ŵ₁(z)` has `|ĥ_J(z)| ≤ 168 (2J+1) e^{|Im z|(J+1)}/(1 + |Re z|)²`.
* **Gram kernel.**  `∫ h φ_ρ conj(φ_σ)` is four values of `ĥ_J` at points with imaginary part at
  most `2η` and real part `γ_ρ - γ_σ`.  Unit windows of the off-line count
  (`window_tsum_inv_sq_le`) bound the row sums by `10 D` times the constant.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Unit-window summation against `(1 + |γ - t₀|)^{-2}` -/

/-- A family whose unit windows carry mass at most `D` has
`Σ_i g_i (1 + |γ_i - t₀|)^{-2} ≤ 10 D`. -/
theorem window_tsum_inv_sq_le {ι : Type*} (γ : ι → ℝ) {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) {D : ℝ}
    (hD : ∀ t : ℝ, ∀ s : Finset ι, (∀ i ∈ s, t < γ i ∧ γ i ≤ t + 1) → ∑ i ∈ s, g i ≤ D)
    (t₀ : ℝ) :
    Summable (fun i => g i / (1 + |γ i - t₀|) ^ 2) ∧
      ∑' i, g i / (1 + |γ i - t₀|) ^ 2 ≤ 10 * D := by
  classical
  have hD0 : 0 ≤ D := by simpa using hD 0 ∅ (by simp)
  have hS := hasSum_inv_one_add_abs_sq
  have hpi : π ^ 2 / 3 - 1 ≤ 5 / 2 := by
    have := Real.pi_lt_d2
    have hp : 0 < π := Real.pi_pos
    nlinarith
  have hnonneg : 0 ≤ fun i => g i / (1 + |γ i - t₀|) ^ 2 :=
    fun i => div_nonneg (hg i) (by positivity)
  have hfin : ∀ s : Finset ι,
      ∑ i ∈ s, g i / (1 + |γ i - t₀|) ^ 2 ≤ 4 * D * (π ^ 2 / 3 - 1) := by
    intro s
    set κ : ι → ℤ := fun i => WeilEF.key (γ i - t₀) with hκ
    rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
      (fun i hi => Finset.mem_image_of_mem κ hi)]
    have hfiber : ∀ n ∈ s.image κ,
        ∑ i ∈ s with κ i = n, g i / (1 + |γ i - t₀|) ^ 2 ≤ 4 * D * (1 / (1 + |(n : ℝ)|) ^ 2) := by
      intro n _
      have hwin := hD (t₀ + n) (s.filter fun i => κ i = n) (fun i hi => by
        simp only [Finset.mem_filter] at hi
        have h1 := WeilEF.key_lt (γ i - t₀)
        have h2 := WeilEF.le_key_add_one (γ i - t₀)
        rw [show WeilEF.key (γ i - t₀) = n from hi.2] at h1 h2
        constructor <;> linarith)
      have hpt : ∀ i ∈ s.filter (fun i => κ i = n),
          g i / (1 + |γ i - t₀|) ^ 2 ≤ (4 / (1 + |(n : ℝ)|) ^ 2) * g i := by
        intro i hi
        simp only [Finset.mem_filter] at hi
        have h1 := WeilEF.key_lt (γ i - t₀)
        have h2 := WeilEF.le_key_add_one (γ i - t₀)
        rw [show WeilEF.key (γ i - t₀) = n from hi.2] at h1 h2
        set y := γ i - t₀
        have hcmp : 1 + |(n : ℝ)| ≤ 2 * (1 + |y|) := by
          rcases le_or_gt 0 (n : ℝ) with hn | hn
          · rw [abs_of_nonneg hn]
            have : (n : ℝ) ≤ |y| := by
              rw [abs_of_pos (by linarith)]; linarith
            linarith
          · have hn' : (n : ℝ) ≤ -1 := by
              have : n < 0 := by exact_mod_cast hn
              exact_mod_cast (show n ≤ -1 by omega)
            rw [abs_of_neg hn]
            have : -(n : ℝ) - 1 ≤ |y| := by
              have := neg_abs_le y
              linarith
            linarith
        have hD' : 0 < 1 + |y| := by positivity
        have hsq : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (1 + |y|) ^ 2 := by
          have h0 : 0 ≤ 1 + |(n : ℝ)| := by positivity
          calc (1 + |(n : ℝ)|) ^ 2 ≤ (2 * (1 + |y|)) ^ 2 := pow_le_pow_left₀ h0 hcmp 2
            _ = 4 * (1 + |y|) ^ 2 := by ring
        rw [div_le_iff₀ (by positivity)]
        calc g i = g i * (1 + |(n : ℝ)|) ^ 2 / (1 + |(n : ℝ)|) ^ 2 := by field_simp
          _ ≤ g i * (4 * (1 + |y|) ^ 2) / (1 + |(n : ℝ)|) ^ 2 := by
              have := hg i
              gcongr
          _ = 4 / (1 + |(n : ℝ)|) ^ 2 * g i * (1 + |y|) ^ 2 := by ring
      calc ∑ i ∈ s with κ i = n, g i / (1 + |γ i - t₀|) ^ 2
          ≤ ∑ i ∈ s with κ i = n, (4 / (1 + |(n : ℝ)|) ^ 2) * g i := Finset.sum_le_sum hpt
        _ = (4 / (1 + |(n : ℝ)|) ^ 2) * ∑ i ∈ s with κ i = n, g i := by rw [Finset.mul_sum]
        _ ≤ (4 / (1 + |(n : ℝ)|) ^ 2) * D := mul_le_mul_of_nonneg_left hwin (by positivity)
        _ = 4 * D * (1 / (1 + |(n : ℝ)|) ^ 2) := by ring
    calc ∑ n ∈ s.image κ, ∑ i ∈ s with κ i = n, g i / (1 + |γ i - t₀|) ^ 2
        ≤ ∑ n ∈ s.image κ, 4 * D * (1 / (1 + |(n : ℝ)|) ^ 2) := Finset.sum_le_sum hfiber
      _ = 4 * D * ∑ n ∈ s.image κ, 1 / (1 + |(n : ℝ)|) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * D * (π ^ 2 / 3 - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_le_hasSum _ (fun n _ => by positivity) hS
  have hsum := summable_of_sum_le hnonneg hfin
  refine ⟨hsum, ?_⟩
  calc ∑' i, g i / (1 + |γ i - t₀|) ^ 2 ≤ 4 * D * (π ^ 2 / 3 - 1) := hsum.tsum_le_of_sum_le hfin
    _ ≤ 4 * D * (5 / 2) := mul_le_mul_of_nonneg_left hpi (by positivity)
    _ = 10 * D := by ring

/-! ### Off-line density -/

/-- The multiplicity of a zero off the critical line, and `0` on it. -/
def offLineMult (Z : ZeroConfig) (ρ : Z.carrier) : ℝ :=
  if (ρ : ℂ).re = 1 / 2 then 0 else (Z.mult ρ : ℝ)

theorem offLineMult_nonneg (Z : ZeroConfig) (ρ : Z.carrier) : 0 ≤ offLineMult Z ρ := by
  unfold offLineMult; split_ifs <;> positivity

theorem offLineMult_le (Z : ZeroConfig) (ρ : Z.carrier) : offLineMult Z ρ ≤ Z.mult ρ := by
  unfold offLineMult; split_ifs <;> simp

/-- Every unit window `(t, t + 1]` carries off-line multiplicity at most `D`. -/
def OffLineDensityBound (Z : ZeroConfig) (D : ℝ) : Prop :=
  ∀ t : ℝ, ∀ s : Finset Z.carrier, (∀ ρ ∈ s, t < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t + 1) →
    ∑ ρ ∈ s, offLineMult Z ρ ≤ D

theorem OffLineDensityBound.nonneg {Z : ZeroConfig} {D : ℝ} (hD : OffLineDensityBound Z D) :
    0 ≤ D := by simpa using hD 0 ∅ (by simp)

/-- A uniform bound on the full count bounds the off-line density. -/
theorem offLineDensityBound_of_count (Z : ZeroConfig) {D : ℝ}
    (hD : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ D) : OffLineDensityBound Z D := by
  classical
  intro t s hs
  refine le_trans ?_ (hD t)
  have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  unfold ZeroConfig.N
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨ρ.2, hs ρ hρ⟩
  have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
  rw [Finset.sum_map] at h
  calc ∑ ρ ∈ s, offLineMult Z ρ ≤ ∑ ρ ∈ s, (Z.mult ρ : ℝ) :=
        Finset.sum_le_sum fun ρ _ => offLineMult_le Z ρ
    _ ≤ _ := by exact_mod_cast h

/-! ### The plateau weight -/

/-- `h_J(u) = Σ_{|j| ≤ J} w₁(u - j)`, at least `(3/4)^{5/2}` on `[-J, J]` and supported in
`[-J-1, J+1]`. -/
def plateauWeight (J : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (-(J : ℤ)) J, sinhTestWeight 1 (u - j)

theorem continuous_plateauWeight (J : ℕ) : Continuous (plateauWeight J) :=
  continuous_finsetSum _ fun _ _ =>
    (sinhTestWeight_contDiff 1).continuous.comp (continuous_id.sub continuous_const)

theorem plateauWeight_nonneg (J : ℕ) (u : ℝ) : 0 ≤ plateauWeight J u :=
  Finset.sum_nonneg fun _ _ => sinhTestWeight_nonneg 1 _

theorem abs_intCast_le_of_mem_Icc {J : ℕ} {j : ℤ} (hj : j ∈ Finset.Icc (-(J : ℤ)) J) :
    |(j : ℝ)| ≤ J := by
  rw [Finset.mem_Icc] at hj
  rw [abs_le]
  constructor
  · have : (-(J : ℤ) : ℝ) ≤ j := by exact_mod_cast hj.1
    simpa using this
  · exact_mod_cast hj.2

theorem plateauWeight_supp (J : ℕ) : ∀ u, plateauWeight J u ≠ 0 → |u| ≤ J + 1 := by
  intro u hu
  by_contra h
  push Not at h
  apply hu
  refine Finset.sum_eq_zero fun j hj => sinhTestWeight_eq_zero zero_le_one ?_
  have hj' := abs_intCast_le_of_mem_Icc hj
  have := abs_sub_abs_le_abs_sub u j
  linarith

theorem hasCompactSupport_plateauWeight (J : ℕ) : HasCompactSupport (plateauWeight J) :=
  hasCompactSupport_of_support_subset_abs (plateauWeight_supp J)

theorem unitWeightFloor_le_sinhTestWeight_one {v : ℝ} (hv : |v| ≤ 1 / 2) :
    unitWeightFloor ≤ sinhTestWeight 1 v := by
  unfold unitWeightFloor sinhTestWeight
  apply Real.rpow_le_rpow (by norm_num) _ (by norm_num)
  have : v ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg v, sq_abs v]
  nlinarith

theorem unitWeightFloor_le_plateauWeight {J : ℕ} {u : ℝ} (hu : |u| ≤ J) :
    unitWeightFloor ≤ plateauWeight J u := by
  have h1 := abs_sub_round u
  have hj : round u ∈ Finset.Icc (-(J : ℤ)) J := by
    rw [Finset.mem_Icc]
    rw [abs_le] at hu h1
    constructor
    · by_contra hlt
      push Not at hlt
      have h2 : round u ≤ -(J : ℤ) - 1 := by omega
      have h3 : ((round u : ℤ) : ℝ) ≤ -(J : ℝ) - 1 := by exact_mod_cast h2
      linarith
    · by_contra hlt
      push Not at hlt
      have h2 : (J : ℤ) + 1 ≤ round u := by omega
      have h3 : (J : ℝ) + 1 ≤ ((round u : ℤ) : ℝ) := by exact_mod_cast h2
      linarith
  calc unitWeightFloor ≤ sinhTestWeight 1 (u - round u) :=
        unitWeightFloor_le_sinhTestWeight_one h1
    _ ≤ plateauWeight J u :=
        Finset.single_le_sum (f := fun j : ℤ => sinhTestWeight 1 (u - j))
          (fun j _ => sinhTestWeight_nonneg 1 _) hj

theorem hasCompactSupport_translate_unitWeight (j : ℝ) :
    HasCompactSupport (fun u => ((sinhTestWeight 1 (u - j) : ℝ) : ℂ)) := by
  refine hasCompactSupport_of_support_subset_abs (Λ := |j| + 1) fun u hu => ?_
  have h : sinhTestWeight 1 (u - j) ≠ 0 := fun h => hu (by simp [h])
  have := sinhTestWeight_supp zero_le_one _ h
  have := abs_sub_abs_le_abs_sub u j
  linarith

/-- The transform of the plateau is `(Σ_{|j| ≤ J} e^{izj}) ŵ₁(z)`. -/
theorem paperFT_plateauWeight (J : ℕ) (z : ℂ) :
    paperFT (fun u => (plateauWeight J u : ℂ)) z =
      (∑ j ∈ Finset.Icc (-(J : ℤ)) J, cexp (I * z * ((j : ℝ) : ℂ))) *
        paperFT (fun u => (sinhTestWeight 1 u : ℂ)) z := by
  rw [paperFT_def, paperFT_def, Finset.sum_mul]
  simp_rw [plateauWeight, Complex.ofReal_sum, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h := integral_sub_right_eq_self (μ := volume)
      (fun v : ℝ => ((sinhTestWeight 1 v : ℝ) : ℂ) * cexp (I * z * ((v + j : ℝ) : ℂ))) (j : ℝ)
    simp only [sub_add_cancel] at h
    rw [h, ← integral_const_mul]
    congr 1 with v
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  · intro j _
    exact integrable_mul_cexp
      ((Complex.continuous_ofReal.comp (sinhTestWeight_contDiff 1).continuous).comp
        (continuous_id.sub continuous_const)) (hasCompactSupport_translate_unitWeight j) z

theorem card_Icc_neg_natCast (J : ℕ) :
    ((Finset.Icc (-(J : ℤ)) J).card : ℝ) = 2 * J + 1 := by
  rw [Int.card_Icc]
  have : ((J : ℤ) + 1 - -(J : ℤ)).toNat = 2 * J + 1 := by omega
  rw [this]
  push_cast
  ring

/-- `|ĥ_J(z)| ≤ (2J + 1) e^{|Im z|(J+1)} · 168/(1 + |Re z|)²`. -/
theorem norm_paperFT_plateauWeight_le (J : ℕ) (z : ℂ) :
    ‖paperFT (fun u => (plateauWeight J u : ℂ)) z‖ ≤
      (2 * J + 1) * Real.exp (|z.im| * (J + 1)) * 168 / (1 + |z.re|) ^ 2 := by
  rw [paperFT_plateauWeight, norm_mul]
  have hsum : ‖∑ j ∈ Finset.Icc (-(J : ℤ)) J, cexp (I * z * ((j : ℝ) : ℂ))‖ ≤
      (2 * J + 1) * Real.exp (|z.im| * J) := by
    refine (norm_sum_le _ _).trans ?_
    have hpt : ∀ j ∈ Finset.Icc (-(J : ℤ)) J,
        ‖cexp (I * z * ((j : ℝ) : ℂ))‖ ≤ Real.exp (|z.im| * J) := by
      intro j hj
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : (I * z * ((j : ℝ) : ℂ)).re = -(z.im * j) := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [hre]
      have hj' := abs_intCast_le_of_mem_Icc hj
      have h1 : -(z.im * j) ≤ |z.im| * |(j : ℝ)| := by
        rw [← abs_mul]; exact neg_le_abs _
      have h2 : |z.im| * |(j : ℝ)| ≤ |z.im| * J := mul_le_mul_of_nonneg_left hj' (abs_nonneg _)
      linarith
    calc ∑ j ∈ Finset.Icc (-(J : ℤ)) J, ‖cexp (I * z * ((j : ℝ) : ℂ))‖
        ≤ ∑ j ∈ Finset.Icc (-(J : ℤ)) J, Real.exp (|z.im| * J) := Finset.sum_le_sum hpt
      _ = (2 * J + 1) * Real.exp (|z.im| * J) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_Icc_neg_natCast]
  have hS : ContDiff ℝ 2 (fun u => (sinhTestWeight 1 u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (sinhTestWeight_contDiff 1)
  have hSsupp : ∀ u, (fun u => (sinhTestWeight 1 u : ℂ)) u ≠ 0 → |u| ≤ 1 := fun u hu =>
    sinhTestWeight_supp zero_le_one u (fun h => hu (by simp [h]))
  have hw := norm_paperFT_le_decay hS hSsupp z
  change _ ≤ Real.exp _ * (4 * testNorm (sinhTestWeight 1)) / _ at hw
  have hT := testNorm_unitWeight_le
  have hw' : ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) z‖ ≤
      Real.exp (|z.im|) * 168 / (1 + |z.re|) ^ 2 := by
    refine hw.trans ?_
    rw [mul_one]
    gcongr
    linarith
  have hD : 0 < (1 + |z.re|) ^ 2 := by positivity
  calc ‖∑ j ∈ Finset.Icc (-(J : ℤ)) J, cexp (I * z * ((j : ℝ) : ℂ))‖ *
        ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) z‖
      ≤ (2 * J + 1) * Real.exp (|z.im| * J) * (Real.exp (|z.im|) * 168 / (1 + |z.re|) ^ 2) :=
        mul_le_mul hsum hw' (norm_nonneg _) (by positivity)
    _ = (2 * J + 1) * Real.exp (|z.im| * (J + 1)) * 168 / (1 + |z.re|) ^ 2 := by
        rw [mul_add, mul_one, Real.exp_add]
        ring

/-! ### The depth exponentials -/

/-- `e^{ixu} - e^{ix̄u}`, which vanishes identically for real `x`. -/
def depthExp (x : ℂ) (u : ℝ) : ℂ := cexp (I * x * u) - cexp (I * conj x * u)

theorem continuous_depthExp (x : ℂ) : Continuous (depthExp x) := by
  unfold depthExp; fun_prop

theorem depthExp_eq_zero {x : ℂ} (hx : x.im = 0) (u : ℝ) : depthExp x u = 0 := by
  have : conj x = x := Complex.conj_eq_iff_im.mpr hx
  simp [depthExp, this]

theorem integral_mul_depthExp {f : ℝ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (x : ℂ) : ∫ u, f u * depthExp x u = paperFT f x - paperFT f (conj x) := by
  simp_rw [depthExp, mul_sub]
  rw [integral_sub (integrable_mul_cexp hf hfs x) (integrable_mul_cexp hf hfs _)]
  rfl

theorem conj_cexp_I_mul (w : ℂ) (u : ℝ) :
    conj (cexp (I * w * u)) = cexp (I * (-conj w) * u) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem cexp_I_mul_mul (v w : ℂ) (u : ℝ) :
    cexp (I * v * u) * cexp (I * w * u) = cexp (I * (v + w) * u) := by
  rw [← Complex.exp_add]; congr 1; ring

/-- The Gram kernel of two depth exponentials against a weight `h` is a signed sum of four
values of `ĥ`. -/
theorem integral_weight_depthExp_mul_conj {h : ℝ → ℝ} (hh : Continuous h)
    (hhs : HasCompactSupport h) (x y : ℂ) :
    ∫ u, (h u : ℂ) * (depthExp x u * conj (depthExp y u)) =
      paperFT (fun u => (h u : ℂ)) (x - conj y) - paperFT (fun u => (h u : ℂ)) (x - y) -
        paperFT (fun u => (h u : ℂ)) (conj x - conj y) +
          paperFT (fun u => (h u : ℂ)) (conj x - y) := by
  have hc : Continuous (fun u => (h u : ℂ)) := Complex.continuous_ofReal.comp hh
  have hcs : HasCompactSupport (fun u => (h u : ℂ)) := hhs.comp_left Complex.ofReal_zero
  have hpt : ∀ u : ℝ, (h u : ℂ) * (depthExp x u * conj (depthExp y u)) =
      (h u : ℂ) * cexp (I * (x - conj y) * u) - (h u : ℂ) * cexp (I * (x - y) * u) -
        (h u : ℂ) * cexp (I * (conj x - conj y) * u) +
          (h u : ℂ) * cexp (I * (conj x - y) * u) := by
    intro u
    simp only [depthExp, map_sub, conj_cexp_I_mul, Complex.conj_conj]
    have e1 := cexp_I_mul_mul x (-conj y) u
    have e2 := cexp_I_mul_mul x (-y) u
    have e3 := cexp_I_mul_mul (conj x) (-conj y) u
    have e4 := cexp_I_mul_mul (conj x) (-y) u
    rw [← sub_eq_add_neg] at e1 e2 e3 e4
    rw [← e1, ← e2, ← e3, ← e4]
    ring
  simp_rw [hpt]
  have i1 := integrable_mul_cexp hc hcs (x - conj y)
  have i2 := integrable_mul_cexp hc hcs (x - y)
  have i3 := integrable_mul_cexp hc hcs (conj x - conj y)
  have i4 := integrable_mul_cexp hc hcs (conj x - y)
  have i12 : Integrable (fun u => (h u : ℂ) * cexp (I * (x - conj y) * u) -
      (h u : ℂ) * cexp (I * (x - y) * u)) := i1.sub i2
  have i123 : Integrable (fun u => (h u : ℂ) * cexp (I * (x - conj y) * u) -
      (h u : ℂ) * cexp (I * (x - y) * u) - (h u : ℂ) * cexp (I * (conj x - conj y) * u)) :=
    i12.sub i3
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  rfl

/-- Gram bound: for `|Im x|, |Im y| ≤ η`, the plateau Gram kernel of two depth exponentials is
at most `672 (2J + 1) e^{2η(J+1)}/(1 + |Re x - Re y|)²`. -/
theorem norm_gram_depthExp_le (J : ℕ) {η : ℝ} {x y : ℂ} (hx : |x.im| ≤ η) (hy : |y.im| ≤ η) :
    ‖∫ u, (plateauWeight J u : ℂ) * (depthExp x u * conj (depthExp y u))‖ ≤
      4 * ((2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168) / (1 + |x.re - y.re|) ^ 2 := by
  rw [integral_weight_depthExp_mul_conj (continuous_plateauWeight J)
    (hasCompactSupport_plateauWeight J)]
  have hb : ∀ w : ℂ, w.re = x.re - y.re → |w.im| ≤ 2 * η →
      ‖paperFT (fun u => (plateauWeight J u : ℂ)) w‖ ≤
        (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 / (1 + |x.re - y.re|) ^ 2 := by
    intro w hre him
    refine (norm_paperFT_plateauWeight_le J w).trans ?_
    rw [hre]
    gcongr
  have hxy : ∀ a b : ℝ, |a| ≤ η → |b| ≤ η → |a + b| ≤ 2 * η := fun a b ha hb' => by
    rw [abs_le] at ha hb' ⊢; constructor <;> linarith
  have hxy' : ∀ a b : ℝ, |a| ≤ η → |b| ≤ η → |a - b| ≤ 2 * η := fun a b ha hb' => by
    rw [abs_le] at ha hb' ⊢; constructor <;> linarith
  have hxn : |(-x.im)| ≤ η := by rwa [abs_neg]
  have hyn : |(-y.im)| ≤ η := by rwa [abs_neg]
  have b1 := hb (x - conj y) (by simp) (by simpa using hxy _ _ hx hy)
  have b2 := hb (x - y) (by simp) (by simpa using hxy' _ _ hx hy)
  have b3 := hb (conj x - conj y) (by simp) (by simpa using hxy' _ _ hxn hyn)
  have b4 := hb (conj x - y) (by simp) (by simpa [sub_eq_add_neg, add_comm] using hxy _ _ hxn hyn)
  set P := paperFT (fun u => (plateauWeight J u : ℂ)) with hP
  have n1 := norm_add_le (P (x - conj y) - P (x - y) - P (conj x - conj y)) (P (conj x - y))
  have n2 := norm_sub_le (P (x - conj y) - P (x - y)) (P (conj x - conj y))
  have n3 := norm_sub_le (P (x - conj y)) (P (x - y))
  have : (4 : ℝ) * ((2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168) / (1 + |x.re - y.re|) ^ 2 =
      (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 / (1 + |x.re - y.re|) ^ 2 +
      (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 / (1 + |x.re - y.re|) ^ 2 +
      (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 / (1 + |x.re - y.re|) ^ 2 +
      (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 / (1 + |x.re - y.re|) ^ 2 := by ring
  rw [this]
  linarith

/-! ### The weighted Bessel inequality -/

/-- The Schur test for a finite double sum: row and column sums of `m_j m_k κ_{jk}` at most `B`
give `Σ_{j,k} m_j m_k x_j x_k κ_{jk} ≤ B Σ_k m_k x_k²`. -/
theorem double_sum_le_of_row_col {ι : Type*} (s : Finset ι) {m x : ι → ℝ} {κ : ι → ι → ℝ}
    (hm : ∀ k, 0 ≤ m k) (hκ : ∀ j k, 0 ≤ κ j k) {B : ℝ}
    (hrow : ∀ j ∈ s, ∑ k ∈ s, m k * κ j k ≤ B) (hcol : ∀ k ∈ s, ∑ j ∈ s, m j * κ j k ≤ B) :
    ∑ j ∈ s, ∑ k ∈ s, m j * m k * (x j * x k) * κ j k ≤ B * ∑ k ∈ s, m k * x k ^ 2 := by
  have hpt : ∀ j k, m j * m k * (x j * x k) * κ j k ≤
      (m j * x j ^ 2 / 2) * (m k * κ j k) + (m k * x k ^ 2 / 2) * (m j * κ j k) := by
    intro j k
    have h1 : x j * x k ≤ x j ^ 2 / 2 + x k ^ 2 / 2 := by nlinarith [sq_nonneg (x j - x k)]
    have h2 : 0 ≤ m j * m k * κ j k := mul_nonneg (mul_nonneg (hm j) (hm k)) (hκ j k)
    have := mul_le_mul_of_nonneg_left h1 h2
    nlinarith
  have hA : ∑ j ∈ s, ∑ k ∈ s, (m j * x j ^ 2 / 2) * (m k * κ j k) ≤
      ∑ j ∈ s, (m j * x j ^ 2 / 2) * B := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow j hj) (by have := hm j; positivity)
  have hB : ∑ j ∈ s, ∑ k ∈ s, (m k * x k ^ 2 / 2) * (m j * κ j k) ≤
      ∑ k ∈ s, (m k * x k ^ 2 / 2) * B := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcol k hk) (by have := hm k; positivity)
  calc ∑ j ∈ s, ∑ k ∈ s, m j * m k * (x j * x k) * κ j k
      ≤ ∑ j ∈ s, ∑ k ∈ s, ((m j * x j ^ 2 / 2) * (m k * κ j k) +
          (m k * x k ^ 2 / 2) * (m j * κ j k)) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hpt j k
    _ = ∑ j ∈ s, ∑ k ∈ s, (m j * x j ^ 2 / 2) * (m k * κ j k) +
          ∑ j ∈ s, ∑ k ∈ s, (m k * x k ^ 2 / 2) * (m j * κ j k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
    _ ≤ ∑ j ∈ s, (m j * x j ^ 2 / 2) * B + ∑ k ∈ s, (m k * x k ^ 2 / 2) * B := add_le_add hA hB
    _ = B * ∑ k ∈ s, m k * x k ^ 2 := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- The synthesis function `H = Σ_k m_k conj(c_k) φ_k` of the Bessel argument. -/
def besselSynthesis {ι : Type*} (s : Finset ι) (m : ι → ℝ) (c : ι → ℂ) (φ : ι → ℝ → ℂ) :
    ℝ → ℂ :=
  fun u => ∑ k ∈ s, ((m k : ℂ) * conj (c k)) * φ k u

theorem continuous_besselSynthesis {ι : Type*} (s : Finset ι) (m : ι → ℝ) (c : ι → ℂ)
    {φ : ι → ℝ → ℂ} (hφ : ∀ k, Continuous (φ k)) : Continuous (besselSynthesis s m c φ) := by
  unfold besselSynthesis
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hφ k)

/-- `∫ f H = Σ_k m_k |c_k|²` for `c_k = ∫ f φ_k`. -/
theorem integral_mul_besselSynthesis {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    {φ : ι → ℝ → ℂ} (hφ : ∀ k, Continuous (φ k)) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) :
    ∫ u, f u * besselSynthesis s m (fun k => ∫ u, f u * φ k u) φ u =
      ((∑ k ∈ s, m k * ‖∫ u, f u * φ k u‖ ^ 2 : ℝ) : ℂ) := by
  unfold besselSynthesis
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ u, f u * ((m k : ℂ) * conj (∫ u, f u * φ k u) * φ k u) =
        ((m k : ℂ) * conj (∫ u, f u * φ k u)) * (f u * φ k u) := fun u => by ring
    simp_rw [e]
    rw [integral_const_mul, mul_assoc, Complex.conj_mul']
  · intro k _
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hf.mul (continuous_const.mul (hφ k))
    · exact hfs.mul_right

/-- `∫ h |H|² ≤ Σ_{j,k} m_j m_k |c_j| |c_k| |K_{jk}|` with the Gram kernel
`K_{jk} = ∫ h φ_j conj(φ_k)`. -/
theorem integral_weight_mul_normSq_besselSynthesis_le {ι : Type*} (s : Finset ι) {m : ι → ℝ}
    (hm : ∀ k, 0 ≤ m k) (c : ι → ℂ) {φ : ι → ℝ → ℂ} (hφ : ∀ k, Continuous (φ k))
    {h : ℝ → ℝ} (hh : Continuous h) (hhs : HasCompactSupport h) :
    ∫ u, h u * ‖besselSynthesis s m c φ u‖ ^ 2 ≤
      ∑ j ∈ s, ∑ k ∈ s, m j * m k * (‖c j‖ * ‖c k‖) *
        ‖∫ u, (h u : ℂ) * (φ j u * conj (φ k u))‖ := by
  set a : ι → ℂ := fun k => (m k : ℂ) * conj (c k) with ha
  have hna : ∀ k, ‖a k‖ = m k * ‖c k‖ := fun k => by
    rw [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm k),
      Complex.norm_conj]
  have hHH : ∀ u, ((h u * ‖besselSynthesis s m c φ u‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, (a j * conj (a k)) * ((h u : ℂ) * (φ j u * conj (φ k u))) := by
    intro u
    push_cast
    rw [← Complex.mul_conj', besselSynthesis, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    ring
  have hint : ∀ j k, Integrable (fun u => (a j * conj (a k)) *
      ((h u : ℂ) * (φ j u * conj (φ k u)))) := by
    intro j k
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_const.mul ((Complex.continuous_ofReal.comp hh).mul
        ((hφ j).mul (Complex.continuous_conj.comp (hφ k))))
    · exact (hhs.comp_left Complex.ofReal_zero).mul_right.mul_left
  have hcplx : ((∫ u, h u * ‖besselSynthesis s m c φ u‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ k ∈ s, (a j * conj (a k)) * ∫ u, (h u : ℂ) * (φ j u * conj (φ k u)) := by
    rw [← integral_complex_ofReal]
    simp_rw [hHH]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  have hle : ∫ u, h u * ‖besselSynthesis s m c φ u‖ ^ 2 ≤
      ‖((∫ u, h u * ‖besselSynthesis s m c φ u‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  refine hle.trans ?_
  rw [hcplx]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun k _ => ?_))
  rw [norm_mul, norm_mul, Complex.norm_conj, hna, hna]
  exact le_of_eq (by ring)

/-- Pointwise AM-GM: where `f ≠ 0` the weight is at least `c₀`. -/
theorem norm_mul_norm_le_bessel {x y w c₀ B : ℝ} (hw : 0 ≤ w)
    (hc₀ : 0 < c₀) (hB : 0 < B) (hfloor : x ≠ 0 → c₀ ≤ w) :
    x * y ≤ B / (2 * c₀) * x ^ 2 + 1 / (2 * B) * (w * y ^ 2) := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0]; simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_add]
    positivity
  have hw' := hfloor h0
  have h1 : c₀ * y ^ 2 ≤ w * y ^ 2 := mul_le_mul_of_nonneg_right hw' (sq_nonneg y)
  have h2 : x * y ≤ B / (2 * c₀) * x ^ 2 + 1 / (2 * B) * (c₀ * y ^ 2) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div _ _ (by positivity) (by positivity),
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (B * x - c₀ * y), mul_pos hB hc₀]
  have h3 : 1 / (2 * B) * (c₀ * y ^ 2) ≤ 1 / (2 * B) * (w * y ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

theorem bessel_combine {S I₁ F G B c₀ : ℝ} (hB : 0 < B)
    (h1 : S ≤ I₁) (h3 : I₁ ≤ B / (2 * c₀) * F + 1 / (2 * B) * G) (h2 : G ≤ B * S) :
    S ≤ B / c₀ * F := by
  have h4 : 1 / (2 * B) * G ≤ S / 2 := by
    calc 1 / (2 * B) * G ≤ 1 / (2 * B) * (B * S) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = S / 2 := by field_simp
  have h5 : B / (2 * c₀) * F = (B / c₀ * F) / 2 := by ring
  linarith

/-- `∫ ‖f‖ ‖H‖ ≤ (B/2c₀) ∫ ‖f‖² + (1/2B) ∫ h ‖H‖²`. -/
theorem integral_norm_mul_norm_le_bessel {f H : ℝ → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hHc : Continuous H) {h : ℝ → ℝ} (hh : Continuous h)
    (hhs : HasCompactSupport h) (hh0 : ∀ u, 0 ≤ h u) {c₀ B : ℝ} (hc₀ : 0 < c₀) (hB : 0 < B)
    (hfloor : ∀ u, f u ≠ 0 → c₀ ≤ h u) :
    ∫ u, ‖f u‖ * ‖H u‖ ≤
      B / (2 * c₀) * (∫ u, ‖f u‖ ^ 2) + 1 / (2 * B) * ∫ u, h u * ‖H u‖ ^ 2 := by
  have hi1 : Integrable (fun u => ‖f u‖ * ‖H u‖) := by
    have : HasCompactSupport (fun u => ‖f u‖ * ‖H u‖) := hfs.norm.mul_right
    exact (hf.norm.mul hHc.norm).integrable_of_hasCompactSupport this
  have hi2 : Integrable (fun u => ‖f u‖ ^ 2) := by
    have h2 : HasCompactSupport (fun u => ‖f u‖ * ‖f u‖) := hfs.norm.mul_right
    have : HasCompactSupport (fun u => ‖f u‖ ^ 2) := by
      rw [show (fun u => ‖f u‖ ^ 2) = fun u => ‖f u‖ * ‖f u‖ from funext fun u => sq _]
      exact h2
    exact (hf.norm.pow 2).integrable_of_hasCompactSupport this
  have hi3 : Integrable (fun u => h u * ‖H u‖ ^ 2) := by
    have : HasCompactSupport (fun u => h u * ‖H u‖ ^ 2) := hhs.mul_right
    exact (hh.mul (hHc.norm.pow 2)).integrable_of_hasCompactSupport this
  have hi4 : Integrable (fun u => B / (2 * c₀) * ‖f u‖ ^ 2 + 1 / (2 * B) * (h u * ‖H u‖ ^ 2)) :=
    (hi2.const_mul _).add (hi3.const_mul _)
  have heq : ∫ u, (B / (2 * c₀) * ‖f u‖ ^ 2 + 1 / (2 * B) * (h u * ‖H u‖ ^ 2)) =
      B / (2 * c₀) * (∫ u, ‖f u‖ ^ 2) + 1 / (2 * B) * ∫ u, h u * ‖H u‖ ^ 2 := by
    rw [integral_add (hi2.const_mul _) (hi3.const_mul _), integral_const_mul, integral_const_mul]
  rw [← heq]
  refine integral_mono hi1 hi4 fun u => ?_
  exact norm_mul_norm_le_bessel (hh0 u) hc₀ hB fun hx => hfloor u (norm_ne_zero_iff.mp hx)

/-- **Weighted Bessel inequality.**  Let `f` be continuous with compact support, `h ≥ 0` a
continuous compactly supported weight with `h ≥ c₀ > 0` where `f ≠ 0`, and let the Gram kernel
`K_{jk} = ∫ h φ_j conj(φ_k)` have row and column sums `Σ m |K|` at most `B`.  Then
`Σ_k m_k |∫ f φ_k|² ≤ (B/c₀) ∫ |f|²`. -/
theorem weighted_bessel_pos {ι : Type*} (s : Finset ι) {m : ι → ℝ} (hm : ∀ k, 0 ≤ m k)
    {φ : ι → ℝ → ℂ} (hφ : ∀ k, Continuous (φ k)) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) {h : ℝ → ℝ} (hh : Continuous h) (hhs : HasCompactSupport h)
    (hh0 : ∀ u, 0 ≤ h u) {c₀ : ℝ} (hc₀ : 0 < c₀) (hfloor : ∀ u, f u ≠ 0 → c₀ ≤ h u)
    {B : ℝ} (hB : 0 < B)
    (hrow : ∀ j ∈ s, ∑ k ∈ s, m k * ‖∫ u, (h u : ℂ) * (φ j u * conj (φ k u))‖ ≤ B)
    (hcol : ∀ k ∈ s, ∑ j ∈ s, m j * ‖∫ u, (h u : ℂ) * (φ j u * conj (φ k u))‖ ≤ B) :
    ∑ k ∈ s, m k * ‖∫ u, f u * φ k u‖ ^ 2 ≤ B / c₀ * ∫ u, ‖f u‖ ^ 2 := by
  have hHc := continuous_besselSynthesis s m (fun k => ∫ u, f u * φ k u) hφ
  have hS0 : 0 ≤ ∑ k ∈ s, m k * ‖∫ u, f u * φ k u‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hm k) (sq_nonneg _)
  refine bessel_combine hB ?_
    (integral_norm_mul_norm_le_bessel hf hfs hHc hh hhs hh0 hc₀ hB hfloor) ?_
  · have e := integral_mul_besselSynthesis s m hφ hf hfs
    have hn : ‖∫ u, f u * besselSynthesis s m (fun k => ∫ u, f u * φ k u) φ u‖ =
        ∑ k ∈ s, m k * ‖∫ u, f u * φ k u‖ ^ 2 := by
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rw [← hn]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (Eventually.of_forall fun u => norm_mul _ _)
  · refine (integral_weight_mul_normSq_besselSynthesis_le s hm _ hφ hh hhs).trans ?_
    exact double_sum_le_of_row_col s hm (fun j k => norm_nonneg _) hrow hcol

/-- The weighted Bessel inequality with a nonnegative row/column bound. -/
theorem weighted_bessel {ι : Type*} (s : Finset ι) {m : ι → ℝ} (hm : ∀ k, 0 ≤ m k)
    {φ : ι → ℝ → ℂ} (hφ : ∀ k, Continuous (φ k)) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) {h : ℝ → ℝ} (hh : Continuous h) (hhs : HasCompactSupport h)
    (hh0 : ∀ u, 0 ≤ h u) {c₀ : ℝ} (hc₀ : 0 < c₀) (hfloor : ∀ u, f u ≠ 0 → c₀ ≤ h u)
    {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ j ∈ s, ∑ k ∈ s, m k * ‖∫ u, (h u : ℂ) * (φ j u * conj (φ k u))‖ ≤ B)
    (hcol : ∀ k ∈ s, ∑ j ∈ s, m j * ‖∫ u, (h u : ℂ) * (φ j u * conj (φ k u))‖ ≤ B) :
    ∑ k ∈ s, m k * ‖∫ u, f u * φ k u‖ ^ 2 ≤ B / c₀ * ∫ u, ‖f u‖ ^ 2 := by
  set S := ∑ k ∈ s, m k * ‖∫ u, f u * φ k u‖ ^ 2 with hS
  set F := ∫ u, ‖f u‖ ^ 2 with hF
  have hF0 : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hε : ∀ ε : ℝ, 0 < ε → S ≤ (B + ε) / c₀ * F := fun ε hε =>
    weighted_bessel_pos s hm hφ hf hfs hh hhs hh0 hc₀ hfloor (by linarith)
      (fun j hj => (hrow j hj).trans (by linarith)) (fun k hk => (hcol k hk).trans (by linarith))
  refine le_of_forall_pos_le_add fun ε hε0 => ?_
  have hδ : 0 < ε * c₀ / (F + 1) := by positivity
  have h1 := hε _ hδ
  have h2 : (B + ε * c₀ / (F + 1)) / c₀ * F = B / c₀ * F + ε * (F / (F + 1)) := by
    field_simp
  have h3 : ε * (F / (F + 1)) ≤ ε := by
    have : F / (F + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  linarith

/-! ### The converse: depth and off-line density bound the Weil form below -/

theorem neg_norm_sub_sq_div_four_le_re_mul_conj (A B : ℂ) :
    -(‖A - B‖ ^ 2 / 4) ≤ (A * conj B).re := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (A.re + B.re), sq_nonneg (A.im + B.im)]

theorem re_Wsummand_self_ge (Z : ZeroConfig) (f : ℝ → ℂ) (ρ : ℂ) :
    -((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 / 4) ≤
      (Z.Wsummand f f ρ).re := by
  rw [ZeroConfig.Wsummand, mul_assoc, show ((Z.mult ρ : ℕ) : ℂ) = ((Z.mult ρ : ℝ) : ℂ) by
    push_cast; rfl, Complex.re_ofReal_mul]
  have h := neg_norm_sub_sq_div_four_le_re_mul_conj (paperFT f (gammaOf ρ))
    (paperFT f (conj (gammaOf ρ)))
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  nlinarith

theorem abs_gammaOf_im_le {ρ : ℂ} {η : ℝ} (h : |ρ.re - 1 / 2| ≤ η) : |(gammaOf ρ).im| ≤ η := by
  rw [WeilEF.gammaOf_im, abs_sub_comm]; exact h

/-- `4(2J + 1) e^{2η(J+1)} · 168`, the Gram constant of the plateau `h_J` at depth `η`. -/
def plateauGramConst (J : ℕ) (η : ℝ) : ℝ := 4 * ((2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168)

theorem plateauGramConst_nonneg (J : ℕ) (η : ℝ) : 0 ≤ plateauGramConst J η := by
  unfold plateauGramConst; positivity

/-- One Gram entry, weighted by the multiplicity of its second zero: only off-line zeros carry
a nonzero depth exponential. -/
theorem mult_mul_norm_gram_le (Z : ZeroConfig) {η : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (J : ℕ) (ρ σ : Z.carrier) :
    (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
      offLineMult Z σ * (plateauGramConst J η / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2) := by
  unfold offLineMult
  split_ifs with hσ
  · have h0 : ∀ u, depthExp (gammaOf σ) u = 0 := depthExp_eq_zero (by
      rw [WeilEF.gammaOf_im, hσ]; ring)
    simp [h0]
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h := norm_gram_depthExp_le J (abs_gammaOf_im_le (hη ρ ρ.2))
      (abs_gammaOf_im_le (hη σ σ.2))
    rw [WeilEF.gammaOf_re, WeilEF.gammaOf_re, abs_sub_comm] at h
    exact h

/-- The same entry, weighted by the multiplicity of its first zero. -/
theorem mult_mul_norm_gram_le' (Z : ZeroConfig) {η : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (J : ℕ) (ρ σ : Z.carrier) :
    (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
      offLineMult Z ρ * (plateauGramConst J η / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2) := by
  unfold offLineMult
  split_ifs with hρ
  · have h0 : ∀ u, depthExp (gammaOf ρ) u = 0 := depthExp_eq_zero (by
      rw [WeilEF.gammaOf_im, hρ]; ring)
    simp [h0]
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h := norm_gram_depthExp_le J (abs_gammaOf_im_le (hη ρ ρ.2))
      (abs_gammaOf_im_le (hη σ σ.2))
    rw [WeilEF.gammaOf_re, WeilEF.gammaOf_re] at h
    exact h

/-- Row sums of the weighted Gram kernel over any finite family of zeros. -/
theorem gram_row_sum_le (Z : ZeroConfig) {η D : ℝ} (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η)
    (hD : OffLineDensityBound Z D) (J : ℕ) (s : Finset Z.carrier) (ρ : Z.carrier) :
    ∑ σ ∈ s, (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
      plateauGramConst J η * (10 * D) := by
  obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le (fun σ : Z.carrier => (σ : ℂ).im)
    (offLineMult_nonneg Z) hD (ρ : ℂ).im
  have hK := plateauGramConst_nonneg J η
  calc ∑ σ ∈ s, (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖
      ≤ ∑ σ ∈ s, plateauGramConst J η *
          (offLineMult Z σ / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2) :=
        Finset.sum_le_sum fun σ _ => (mult_mul_norm_gram_le Z hη J ρ σ).trans (le_of_eq (by ring))
    _ = plateauGramConst J η * ∑ σ ∈ s, offLineMult Z σ / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ plateauGramConst J η * (10 * D) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact (hsum.sum_le_tsum s fun σ _ =>
          div_nonneg (offLineMult_nonneg Z σ) (by positivity)).trans hle

/-- Column sums of the weighted Gram kernel. -/
theorem gram_col_sum_le (Z : ZeroConfig) {η D : ℝ} (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η)
    (hD : OffLineDensityBound Z D) (J : ℕ) (s : Finset Z.carrier) (σ : Z.carrier) :
    ∑ ρ ∈ s, (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
      plateauGramConst J η * (10 * D) := by
  obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le (fun ρ : Z.carrier => (ρ : ℂ).im)
    (offLineMult_nonneg Z) hD (σ : ℂ).im
  have hK := plateauGramConst_nonneg J η
  calc ∑ ρ ∈ s, (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖
      ≤ ∑ ρ ∈ s, plateauGramConst J η *
          (offLineMult Z ρ / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2) :=
        Finset.sum_le_sum fun ρ _ =>
          (mult_mul_norm_gram_le' Z hη J ρ σ).trans (le_of_eq (by ring))
    _ = plateauGramConst J η * ∑ ρ ∈ s, offLineMult Z ρ / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ plateauGramConst J η * (10 * D) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact (hsum.sum_le_tsum s fun ρ _ =>
          div_nonneg (offLineMult_nonneg Z ρ) (by positivity)).trans hle

/-- **Bessel bound for the depth differences.**  For a continuous test supported in `[-J, J]`,
every finite family of zeros has
`Σ m_ρ |h_f(x_ρ) - h_f(x̄_ρ)|² ≤ 10 D · 672 (2J+1) e^{2η(J+1)}/(3/4)^{5/2} · ∫|f|²`. -/
theorem sum_mult_norm_sub_sq_le (Z : ZeroConfig) {η D : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (hD : OffLineDensityBound Z D) (J : ℕ)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ J) (s : Finset Z.carrier) :
    ∑ ρ ∈ s, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 ≤
      plateauGramConst J η * (10 * D) / unitWeightFloor * ∫ u, ‖f u‖ ^ 2 := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  have h := weighted_bessel s (m := fun ρ : Z.carrier => (Z.mult ρ : ℝ)) (fun _ => Nat.cast_nonneg _)
    (φ := fun ρ : Z.carrier => depthExp (gammaOf ρ)) (fun ρ => continuous_depthExp _) hf hcs
    (continuous_plateauWeight J) (hasCompactSupport_plateauWeight J) (plateauWeight_nonneg J)
    unitWeightFloor_pos (fun u hu => unitWeightFloor_le_plateauWeight (hfs u hu))
    (mul_nonneg (plateauGramConst_nonneg J η) (by linarith [hD.nonneg]))
    (fun ρ _ => gram_row_sum_le Z hη hD J s ρ) (fun σ _ => gram_col_sum_le Z hη hD J s σ)
  simp only [integral_mul_depthExp hf hcs] at h
  exact h

/-- **The converse bound, integer form.**  If every zero has `|β - ½| ≤ η` and every unit window
carries off-line multiplicity at most `D`, then every continuous test supported in `[-J, J]`
has `Re W(f, f) ≥ -(K_J(η) · 10 D/(4 (3/4)^{5/2})) ∫|f|²`. -/
theorem re_W_ge_of_depth_offLineDensity_nat (Z : ZeroConfig) {η D : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (hD : OffLineDensityBound Z D) (J : ℕ)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ J) :
    -(plateauGramConst J η * (10 * D) / unitWeightFloor * (∫ u, ‖f u‖ ^ 2) / 4) ≤
      (Z.W f f).re := by
  set e : Z.carrier → ℝ := fun ρ =>
    (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 with he
  have he0 : 0 ≤ e := fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hfin := sum_mult_norm_sub_sq_le Z hη hD J hf hfs
  have hsum : Summable e := summable_of_sum_le he0 hfin
  have htsum := hsum.tsum_le_of_sum_le hfin
  have hK0 : 0 ≤ plateauGramConst J η * (10 * D) / unitWeightFloor * (∫ u, ‖f u‖ ^ 2) := by
    have := plateauGramConst_nonneg J η
    have := hD.nonneg
    have := unitWeightFloor_pos
    have : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    positivity
  by_cases hW : Summable (fun ρ : Z.carrier => Z.Wsummand f f ρ)
  · rw [ZeroConfig.W, Complex.re_tsum hW]
    have hre : Summable (fun ρ : Z.carrier => (Z.Wsummand f f ρ).re) :=
      (Complex.hasSum_re hW.hasSum).summable
    have hle := Summable.tsum_le_tsum (f := fun ρ : Z.carrier => -(e ρ / 4))
      (fun ρ => re_Wsummand_self_ge Z f ρ) (hsum.div_const 4).neg hre
    rw [tsum_neg, tsum_div_const] at hle
    linarith
  · rw [ZeroConfig.W, tsum_eq_zero_of_not_summable hW, Complex.zero_re]
    linarith

/-- **The converse bound.**  Let every zero of `Z` satisfy `|β - ½| ≤ η`, with `η ≥ 0`, and let every
unit window `(t, t + 1]` carry off-line multiplicity at most `D`.  Then every continuous test
supported in `[-a, a]` satisfies
`Re W(f, f) ≥ -3500 (2a + 3) D e^{2η(a+2)} ∫|f|²`.

**Proof.**  `Re(A B̄) ≥ -|A - B|²/4` bounds each term below by the depth difference
`h_f(x_ρ) - h_f(x̄_ρ) = ∫ f (e^{ix_ρu} - e^{ix̄_ρu})`, which vanishes on the critical line.  A weighted
Bessel inequality with the plateau weight `h_J = Σ_{|j| ≤ J} w₁(· - j) ≥ (3/4)^{5/2}` on
`[-J, J]`, `J = ⌈a⌉`, bounds their sum by the Schur norm of the Gram kernel
`∫ h_J φ_ρ conj(φ_σ)`.  That kernel is four values of `ĥ_J` at points with imaginary part at most
`2η`, each at most `168 (2J+1) e^{2η(J+1)}/(1 + |γ_ρ - γ_σ|)²`, and the off-line window count
gives row sums at most `10 D` times that constant. -/
theorem re_W_ge_of_depth_offLineDensity (Z : ZeroConfig) {η D a : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ η) (hD : OffLineDensityBound Z D) (ha : 0 ≤ a)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ a) :
    -(3500 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) * ∫ u, ‖f u‖ ^ 2) ≤ (Z.W f f).re := by
  set J := ⌈a⌉₊ with hJ
  have hJa : (J : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  have haJ : a ≤ J := Nat.le_ceil a
  have hmain := re_W_ge_of_depth_offLineDensity_nat Z hη hD J hf
    (fun u hu => (hfs u hu).trans haJ)
  set F := ∫ u, ‖f u‖ ^ 2 with hF
  have hF0 : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hD0 := hD.nonneg
  have hc₀ := unitWeightFloor_ge
  have hc₀0 := unitWeightFloor_pos
  have he : Real.exp (2 * η * (J + 1)) ≤ Real.exp (2 * η * (a + 2)) := by
    apply Real.exp_le_exp.mpr
    have : (J : ℝ) + 1 ≤ a + 2 := by linarith
    nlinarith
  have hJ3 : 2 * (J : ℝ) + 1 ≤ 2 * a + 3 := by linarith
  have hbound : plateauGramConst J η * (10 * D) / unitWeightFloor * F / 4 ≤
      3500 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) * F := by
    have e1 : plateauGramConst J η * (10 * D) / unitWeightFloor * F / 4 =
        1680 * ((2 * J + 1) * Real.exp (2 * η * (J + 1)) * D * F) / unitWeightFloor := by
      unfold plateauGramConst; ring
    rw [e1, div_le_iff₀ hc₀0]
    have h2 : (2 * J + 1) * Real.exp (2 * η * (J + 1)) * D * F ≤
        (2 * a + 3) * Real.exp (2 * η * (a + 2)) * D * F := by
      have : 0 ≤ Real.exp (2 * η * (J + 1)) := (Real.exp_pos _).le
      gcongr
    have h3 : 0 ≤ (2 * a + 3) * Real.exp (2 * η * (a + 2)) * D * F := by positivity
    nlinarith
  linarith

end RHTower
