import Zeta23.ThmE.MuMuChi
import Zeta23.ThmE.GammaFactsChiProof

/-!
# The archimedean density of Dirichlet L-functions, uniformly in the modulus

The archimedean density of `L(s, χ)` for `χ` of parity `κ` modulo `q` is
`μ_q(τ) = (1/2π)(log(q/π) + Re ψ(1/4 + κ/2 + iτ/2))`, so

`μ_q = μ_1 + (log q)/(2π)`                                         (`muq_eq_muq_one_add`)

exactly.  Every statement about `μ_q` that is polynomial in the shift is therefore determined by finitely
many moduli.  For the diagonal evaluation of the bilinear form `𝓜[μ_q, μ_q]` the error

`E(s) = 𝓜[μ_1 + s, μ_1 + s] − 2π b L ∫_T^{2T} (μ_1 + s)²`

is a quadratic polynomial in `s` (`mumuShiftErr_eq_quadratic`), and Lagrange interpolation at
`s = 0, log 2/2π, log 3/2π` (`abs_quad_le_of_interp`) turns the fixed-modulus evaluations at `q = 1, 2, 3`
into one evaluation for every modulus:

`|𝓜[μ_q, μ_q] − 2π b L ∫_T^{2T} μ_q²| ≤ C (1 + log q)² l² log L`      (`prop_mumu_uniform`)

with `C` and the threshold for `T` independent of `q`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide

noncomputable section

namespace RHTower

/-- **The modulus enters the archimedean density as an additive constant.** -/
theorem muq_eq_muq_one_add (κ q : ℕ) (hq : 1 ≤ q) (τ : ℝ) :
    muq κ q τ = muq κ 1 τ + Real.log q / (2 * π) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  unfold muq
  rw [Real.log_div hq0 Real.pi_ne_zero, Nat.cast_one, Real.log_div one_ne_zero Real.pi_ne_zero,
    Real.log_one]
  field_simp
  ring

/-- **Quadratic interpolation.**  A quadratic `e₀ + 2 s x₁ + s² x₂` is controlled at every `s ≥ 0` by its
values at `0 < a < b ≤ 1`. -/
theorem abs_quad_le_of_interp {e₀ e₂ e₃ x₁ x₂ a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (h₂ : e₂ = e₀ + 2 * a * x₁ + a ^ 2 * x₂) (h₃ : e₃ = e₀ + 2 * b * x₁ + b ^ 2 * x₂)
    (hs : 0 ≤ s) :
    |e₀ + 2 * s * x₁ + s ^ 2 * x₂|
      ≤ (1 + s) ^ 2 * (1 / (a * b) + 1 / (a * (b - a)) + 1 / (b * (b - a)))
          * (|e₀| + |e₂| + |e₃|) := by
  have hb : 0 < b := ha.trans hab
  have hba : 0 < b - a := by linarith
  -- Lagrange form
  have hid : e₀ + 2 * s * x₁ + s ^ 2 * x₂
      = e₀ * ((s - a) * (s - b) / (a * b)) + e₂ * (s * (s - b) / (a * (a - b)))
        + e₃ * (s * (s - a) / (b * (b - a))) := by
    have hab' : a - b ≠ 0 := by linarith
    rw [h₂, h₃]
    field_simp
    ring
  have hl₀ : |(s - a) * (s - b) / (a * b)| ≤ (1 + s) ^ 2 * (1 / (a * b)) := by
    rw [abs_div, abs_of_pos (mul_pos ha hb), abs_mul, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : |s - a| ≤ 1 + s := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |s - b| ≤ 1 + s := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
  have hl₂ : |s * (s - b) / (a * (a - b))| ≤ (1 + s) ^ 2 * (1 / (a * (b - a))) := by
    rw [abs_div, abs_mul a, abs_of_pos ha, abs_sub_comm, abs_of_pos hba, abs_mul,
      abs_of_nonneg hs, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h2 : |s - b| ≤ 1 + s := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [sq]
    exact mul_le_mul (by linarith) h2 (abs_nonneg _) (by linarith)
  have hl₃ : |s * (s - a) / (b * (b - a))| ≤ (1 + s) ^ 2 * (1 / (b * (b - a))) := by
    rw [abs_div, abs_of_pos (mul_pos hb hba), abs_mul, abs_of_nonneg hs, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h2 : |s - a| ≤ 1 + s := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [sq]
    exact mul_le_mul (by linarith) h2 (abs_nonneg _) (by linarith)
  set K := 1 / (a * b) + 1 / (a * (b - a)) + 1 / (b * (b - a)) with hK
  have hK₀ : 1 / (a * b) ≤ K := by
    have : 0 < 1 / (a * (b - a)) + 1 / (b * (b - a)) := by positivity
    linarith
  have hK₂ : 1 / (a * (b - a)) ≤ K := by
    have : 0 < 1 / (a * b) + 1 / (b * (b - a)) := by positivity
    linarith
  have hK₃ : 1 / (b * (b - a)) ≤ K := by
    have : 0 < 1 / (a * b) + 1 / (a * (b - a)) := by positivity
    linarith
  have hs2 : 0 ≤ (1 + s) ^ 2 := sq_nonneg _
  rw [hid]
  calc |e₀ * ((s - a) * (s - b) / (a * b)) + e₂ * (s * (s - b) / (a * (a - b)))
        + e₃ * (s * (s - a) / (b * (b - a)))|
      ≤ |e₀| * |(s - a) * (s - b) / (a * b)| + |e₂| * |s * (s - b) / (a * (a - b))|
        + |e₃| * |s * (s - a) / (b * (b - a))| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |e₀| * ((1 + s) ^ 2 * K) + |e₂| * ((1 + s) ^ 2 * K) + |e₃| * ((1 + s) ^ 2 * K) := by
        gcongr
        · exact hl₀.trans (mul_le_mul_of_nonneg_left hK₀ hs2)
        · exact hl₂.trans (mul_le_mul_of_nonneg_left hK₂ hs2)
        · exact hl₃.trans (mul_le_mul_of_nonneg_left hK₃ hs2)
    _ = (1 + s) ^ 2 * K * (|e₀| + |e₂| + |e₃|) := by ring

section Shift

variable {Φ : ℝ → ℝ} {T : ℝ}

/-- `𝓜[u + s, u + s] = 𝓜[u, u] + 2 s 𝓜[u, 1] + s² 𝓜[1, 1]`. -/
theorem Mform_shift (hΦ : Continuous Φ) (hΦe : ∀ r, Φ (-r) = Φ r) {u : ℝ → ℝ}
    (hu : Continuous u) (s : ℝ) :
    Mform Φ T (fun x => u x + s) (fun x => u x + s)
      = Mform Φ T u u + 2 * s * Mform Φ T u (fun _ => 1)
        + s ^ 2 * Mform Φ T (fun _ => 1) (fun _ => 1) := by
  have e1 : (fun x => u x + s) = u + fun x => s * (fun _ : ℝ => (1 : ℝ)) x := by
    funext x; simp
  have h1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  have hs : Continuous fun x : ℝ => s * (fun _ : ℝ => (1 : ℝ)) x := continuous_const
  rw [e1, Mform_add_left hΦ hu hs (hu.add hs), Mform_add_right hΦ hu hs hu,
    Mform_add_right hΦ hu hs hs, Mform_const_mul_right, Mform_const_mul_left,
    Mform_const_mul_left, Mform_const_mul_right, Mform_comm hΦe (fun _ => (1 : ℝ)) u]
  ring

/-- `∫ (u + s)² = ∫ u² + 2 s ∫ u + s² (b − a)`. -/
theorem integral_add_const_sq {u : ℝ → ℝ} (hu : Continuous u) (a b s : ℝ) :
    ∫ τ in a..b, (u τ + s) ^ 2
      = (∫ τ in a..b, u τ ^ 2) + 2 * s * (∫ τ in a..b, u τ) + s ^ 2 * (b - a) := by
  have e : (fun τ => (u τ + s) ^ 2) = fun τ => (u τ ^ 2 + 2 * s * u τ) + s ^ 2 := by
    funext τ; ring
  have h1 : IntervalIntegrable (fun τ => u τ ^ 2 + 2 * s * u τ) volume a b :=
    (by fun_prop : Continuous fun τ => u τ ^ 2 + 2 * s * u τ).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun τ => u τ ^ 2) volume a b :=
    (by fun_prop : Continuous fun τ => u τ ^ 2).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun τ => 2 * s * u τ) volume a b :=
    (by fun_prop : Continuous fun τ => 2 * s * u τ).intervalIntegrable a b
  rw [e, intervalIntegral.integral_add h1 intervalIntegrable_const,
    intervalIntegral.integral_add h2 h3, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The diagonal error of `𝓜` for a shifted density. -/
def mumuShiftErr (Φ : ℝ → ℝ) (T b L : ℝ) (u : ℝ → ℝ) (s : ℝ) : ℝ :=
  Mform Φ T (fun x => u x + s) (fun x => u x + s)
    - 2 * π * b * L * ∫ τ in T..(2 * T), (u τ + s) ^ 2

/-- **The diagonal error is quadratic in the shift.** -/
theorem mumuShiftErr_eq_quadratic (hΦ : Continuous Φ) (hΦe : ∀ r, Φ (-r) = Φ r) {u : ℝ → ℝ}
    (hu : Continuous u) (b L s : ℝ) :
    mumuShiftErr Φ T b L u s
      = mumuShiftErr Φ T b L u 0
        + 2 * s * (Mform Φ T u (fun _ => 1) - 2 * π * b * L * ∫ τ in T..(2 * T), u τ)
        + s ^ 2 * (Mform Φ T (fun _ => 1) (fun _ => 1) - 2 * π * b * L * T) := by
  unfold mumuShiftErr
  simp only [add_zero]
  rw [Mform_shift hΦ hΦe hu, integral_add_const_sq hu]
  ring

end Shift

section Uniform

variable (cϱ lam : ℝ)

/-- The diagonal error of `𝓜[μ_q, μ_q]` at a setting. -/
def mumuErr (κ q : ℕ) (p : Setting) (F : LocalFun) : ℝ :=
  Mform F.Phi p.T (muq κ q) (muq κ q)
    - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2

theorem mumuErr_eq_shiftErr {κ q : ℕ} (hq : 1 ≤ q) (p : Setting) (F : LocalFun) :
    mumuErr κ q p F = mumuShiftErr F.Phi p.T F.b p.L (muq κ 1) (Real.log q / (2 * π)) := by
  have e : muq κ q = fun x => muq κ 1 x + Real.log q / (2 * π) :=
    funext (muq_eq_muq_one_add κ q hq)
  unfold mumuErr mumuShiftErr
  rw [e]

/-- Zeta23's fixed-modulus evaluation, with the coefficient sequence `0`. -/
theorem mumu_fixed {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F → |mumuErr κ q p F| ≤ C * (Zeta23.l p.T ^ 2 * Real.log p.L) := by
  have hc : CoeffOK q (fun _ => 0) := ⟨fun _ => by simp, fun _ _ => rfl⟩
  obtain ⟨C, T₀, hC⟩ := prop_mumu_chi cϱ lam (GammaChi.gammaFactsChi hκ hq) hc hq hlam
  exact ⟨|C|, T₀, abs_nonneg C, fun p F hp hT hF =>
    (hC p F hp hT hF).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [hF.eight_le_L]))))⟩

/-- The interpolation constant for the nodes `log 2/2π < log 3/2π`. -/
def interpConst : ℝ :=
  let a := Real.log 2 / (2 * π)
  let b := Real.log 3 / (2 * π)
  1 / (a * b) + 1 / (a * (b - a)) + 1 / (b * (b - a))

theorem interp_nodes : 0 < Real.log 2 / (2 * π) ∧ Real.log 2 / (2 * π) < Real.log 3 / (2 * π)
    ∧ Real.log 3 / (2 * π) ≤ 1 := by
  have hπ : 0 < 2 * π := by positivity
  refine ⟨div_pos (Real.log_pos (by norm_num)) hπ,
    div_lt_div_of_pos_right (Real.log_lt_log (by norm_num) (by norm_num)) hπ, ?_⟩
  rw [div_le_one hπ]
  have h3 : Real.log 3 < 3 - 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num)
    linarith
  linarith [Real.pi_gt_three]

theorem interpConst_pos : 0 < interpConst := by
  obtain ⟨ha, hab, -⟩ := interp_nodes
  have hb := ha.trans hab
  have hba : 0 < Real.log 3 / (2 * π) - Real.log 2 / (2 * π) := by linarith
  unfold interpConst
  positivity

/-- From the three moduli `1, 2, 3` to every modulus, for a fixed parity. -/
theorem mumu_uniform_of_three {κ : ℕ} (hκ : κ ≤ 1) {C₁ C₂ C₃ T₁ T₂ T₃ : ℝ}
    (h₁ : ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₁ ≤ p.T → LocalHypsCore cϱ p F →
      |mumuErr κ 1 p F| ≤ C₁ * (Zeta23.l p.T ^ 2 * Real.log p.L))
    (h₂ : ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₂ ≤ p.T → LocalHypsCore cϱ p F →
      |mumuErr κ 2 p F| ≤ C₂ * (Zeta23.l p.T ^ 2 * Real.log p.L))
    (h₃ : ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₃ ≤ p.T → LocalHypsCore cϱ p F →
      |mumuErr κ 3 p F| ≤ C₃ * (Zeta23.l p.T ^ 2 * Real.log p.L))
    {q : ℕ} (hq : 1 ≤ q) (p : Setting) (F : LocalFun) (hp : p.lam = lam)
    (hT : max (max T₁ T₂) T₃ ≤ p.T) (hF : LocalHypsCore cϱ p F) :
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

/-- **[prop:mumu] for `L(s, χ)`, uniformly in the modulus.** -/
theorem prop_mumu_uniform (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ (p : Setting) (F : LocalFun),
      p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F →
      |Mform F.Phi p.T (muq κ q) (muq κ q)
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2|
        ≤ C * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L) := by
  obtain ⟨A₁, S₁, hA₁, a₁⟩ := mumu_fixed cϱ lam (κ := 0) (q := 1) (by norm_num) le_rfl hlam
  obtain ⟨A₂, S₂, hA₂, a₂⟩ := mumu_fixed cϱ lam (κ := 0) (q := 2) (by norm_num) (by norm_num) hlam
  obtain ⟨A₃, S₃, hA₃, a₃⟩ := mumu_fixed cϱ lam (κ := 0) (q := 3) (by norm_num) (by norm_num) hlam
  obtain ⟨B₁, R₁, hB₁, b₁⟩ := mumu_fixed cϱ lam (κ := 1) (q := 1) le_rfl le_rfl hlam
  obtain ⟨B₂, R₂, hB₂, b₂⟩ := mumu_fixed cϱ lam (κ := 1) (q := 2) le_rfl (by norm_num) hlam
  obtain ⟨B₃, R₃, hB₃, b₃⟩ := mumu_fixed cϱ lam (κ := 1) (q := 3) le_rfl (by norm_num) hlam
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
  · have h := mumu_uniform_of_three cϱ lam (by norm_num) a₁ a₂ a₃ hq p F hp hTA hF
    refine h.trans ?_
    have : interpConst * (A₁ + A₂ + A₃) ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) :=
      mul_le_mul_of_nonneg_left (by linarith) hK.le
    calc interpConst * (A₁ + A₂ + A₃) * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L)
        = interpConst * (A₁ + A₂ + A₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := by ring
      _ ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := mul_le_mul_of_nonneg_right this hB0
      _ = _ := by ring
  · have h := mumu_uniform_of_three cϱ lam le_rfl b₁ b₂ b₃ hq p F hp hTB hF
    refine h.trans ?_
    have : interpConst * (B₁ + B₂ + B₃) ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) :=
      mul_le_mul_of_nonneg_left (by linarith) hK.le
    calc interpConst * (B₁ + B₂ + B₃) * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L)
        = interpConst * (B₁ + B₂ + B₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := by ring
      _ ≤ interpConst * (A₁ + A₂ + A₃ + B₁ + B₂ + B₃) * ((1 + Real.log q) ^ 2
            * (Zeta23.l p.T ^ 2 * Real.log p.L)) := mul_le_mul_of_nonneg_right this hB0
      _ = _ := by ring

end Uniform

end RHTower
