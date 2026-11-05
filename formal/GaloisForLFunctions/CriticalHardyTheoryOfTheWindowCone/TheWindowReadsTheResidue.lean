import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheDatumOfTheWindowCone

/-!
# The window reads the residue: pole and conductor trade off

The twisted-arc family has total pole term `w₀/2 > 0` and is blind. So on a window, for any weights in the
cone of the datum `(β, s)`,

  `(1 − β) w₀/2 ≤ (1 + s + 1 − β) K e^{3c − (π/16) e^{2(c−2)}} + s T₀`
  (`exists_datum_constants`).

A deficit of pole has to be paid by conductor, up to the doubly exponential ceiling. The weights do not
enter: the box of two-point resonators bounds them on any cone of any datum (`mul_div_sqrt_le_of_mem_datumCone`),
because resonators have no pole term and the conductor only adds to their energy.

* **The window reads the residue** (`exists_one_sub_le_of_datumCone`). A nonempty cone at conductor one has
  `β ≥ 1 − K′ exp(3c − (π/16) e^{2(c−2)})`: the residue of `ζ` is pinned from below with doubly
  exponential precision by positivity at a finite window, whatever the weights.
* **No pole needs conductor** (`exists_pos_forall_lt_datumCone_zero_eq_empty`). There is `s₁ > 0` such that a
  pole-free datum with log-conductor below `s₁` has an empty cone from a finite window on.

With `TheDatumOfTheWindowCone` this classifies the corners of the datum plane
(`datum_classification`).
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.ResonatorProfile _root_.Zeta23

local notation "𝔽" => xiShiftedGammaTest

/-! ### The box on the cone of any datum -/

/-- The two-point resonator has mass `2M`. -/
theorem integral_norm_twoPointResonator_sq {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∫ u, ‖twoPointResonator n σ u‖ ^ 2 = 2 * resonatorMass n := by
  set w : ℝ := 1 / ((n : ℝ) + 1) with hwdef
  have hw : 0 < w := by positivity
  have hvan0 : ∀ Y, 1 / ((n : ℝ) + 1) ≤ |Y| → EF.weilTest (gC w) (gC w) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu)
      (by rw [← hwdef] at hY; linarith)
  have hgc0 : Continuous (gC w) := (contDiff_gC w 0).continuous
  have hgs0 := hasCompactSupport_gC hw
  have hk0 : EF.weilTest (gC w) (gC w) 0 = ((resonatorMass n : ℝ) : ℂ) :=
    weilTest_self_zero_ofReal (g := gR w)
  have h1 := weilTest_translates_log hgc0 hgs0 hvan0
    (twoPointCoeff_vanish (by omega : 1 ≤ n) (σ : ℂ)) (le_refl 1)
  have hlog : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
  rw [hlog, hk0] at h1
  have hn1 : (1 : ℕ) ≠ n := by omega
  have hpt : ∀ m ∈ Finset.Icc 1 n, twoPointCoeff n (σ : ℂ) (1 * m) *
      conj (twoPointCoeff n (σ : ℂ) m) =
      (if m = 1 then (1 : ℂ) else 0) + (if m = n then 1 else 0) := by
    intro m _
    rw [one_mul]
    unfold twoPointCoeff
    by_cases h₁ : m = 1
    · subst h₁
      simp [hn1]
    · by_cases h₂ : m = n
      · subst h₂
        rcases hσ with rfl | rfl <;> simp [h₁]
      · simp [h₁, h₂]
  have hsum : ∑ m ∈ Finset.Icc 1 n, twoPointCoeff n (σ : ℂ) (1 * m) *
      conj (twoPointCoeff n (σ : ℂ) m) = 2 := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
      if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩), if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
    norm_num
  rw [hsum] at h1
  have h2 : EF.weilTest (twoPointResonator n σ) (twoPointResonator n σ) 0 =
      ((∫ u, ‖twoPointResonator n σ u‖ ^ 2 : ℝ) : ℂ) := by
    rw [_root_.RHTower.WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sub_zero]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : EF.weilTest (twoPointResonator n σ) (twoPointResonator n σ) 0 =
      ((resonatorMass n : ℝ) : ℂ) * 2 := h1
  rw [h3] at h2
  have h4 : ((∫ u, ‖twoPointResonator n σ u‖ ^ 2 : ℝ) : ℂ) = ((2 * resonatorMass n : ℝ) : ℂ) := by
    rw [← h2]
    push_cast
    ring
  exact Complex.ofReal_injective h4

/-- **The box on the cone of any datum.** Resonators have no pole term, so the pole weight does not enter,
and the conductor adds to the bound. -/
theorem mul_div_sqrt_le_of_mem_datumCone {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    {n : ℕ} (hn : 2 ≤ n) (hc : atomLevel n ≤ c) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    σ * (lam n / Real.sqrt n) ≤ Real.log n + boxConst + s := by
  obtain ⟨-, hR2, hRs, hp, -⟩ := isPolarTest_twoPointResonator hn σ
  obtain ⟨R, hR⟩ : ∃ R, R = twoPointResonator n σ := ⟨_, rfl⟩
  rw [← hR] at hR2 hRs hp
  have hfs : tsupport R ⊆ Icc (-c) c := hRs.trans (Icc_subset_Icc (by linarith) hc)
  have hfc := hasCompactSupport_of_tsupport_subset hfs
  have hM := resonatorMass_pos n
  have hmass : ∫ u, ‖R u‖ ^ 2 = 2 * resonatorMass n := by
    rw [hR]
    exact integral_norm_twoPointResonator_sq hn hσ
  have hpole : (weilPoleTerm (EF.weilTest R R)).re = 0 := by
    rw [weilPoleTerm_re_eq_two_re hR2.continuous hfc, hp]
    simp
  set g : WeilTestFn := ⟨R, hR2, hfc⟩ with hg
  have harch : (weilFullFunctional (fun _ => 0) (EF.weilTest R R)).re ≤
      2 * resonatorMass n * (Real.log n + boxConst) := by
    have h1 := re_weilFullFunctional_zero_eq g
    have h2 := BlindPrimePowerSlack.weilArchRe_sub_pole_eq g
    have h3 := archEnergy_twoPointResonator_le hn hσ
    rw [← hR] at h3
    have h4 : archEnergy R = ∫ r : ℝ, ‖paperFT R r‖ ^ 2 * EF.gammaBracket r := by
      unfold archEnergy
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only
      congr 1
      rw [WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
      unfold archimedeanWeilSymbol
      congr 2
      field_simp
    have h5 : weilArchRe (EF.weilTest R R) =
        1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT R r‖ ^ 2 * EF.gammaBracket r := by
      have h6 : weilArchRe (EF.weilTest R R) - (weilPoleTerm (EF.weilTest R R)).re =
          1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT R r‖ ^ 2 * EF.gammaBracket r := h2
      rw [hpole, sub_zero] at h6
      exact h6
    have h7 : (weilFullFunctional (fun _ => 0) (EF.weilTest R R)).re =
        weilArchRe (EF.weilTest R R) := h1
    rw [h7, h5, ← h4]
    have hπ := Real.pi_pos
    calc 1 / (2 * Real.pi) * archEnergy R
        ≤ 1 / (2 * Real.pi) * (4 * Real.pi * resonatorMass n * (Real.log n + boxConst)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by field_simp; ring
  obtain ⟨N₀, hN₀⟩ := exists_forall_log_eq_zero (EF.weilTest_hasCompactSupport hfc hfc)
  obtain ⟨N, hN⟩ : ∃ N, N = max N₀ (n + 1) := ⟨_, rfl⟩
  have hNk : ∀ m : ℕ, N ≤ m → EF.weilTest R R (Real.log m) = 0 ∧
      EF.weilTest R R (-Real.log m) = 0 :=
    fun m hm => hN₀ m ((le_max_left _ _).trans (hN ▸ hm))
  have hnN : n < N := by
    have : n + 1 ≤ N := by rw [hN]; exact le_max_right _ _
    omega
  have e := re_weilFullFunctional_eq_affine lam hNk
  have hsum : ∑ m ∈ Finset.range N, (if 2 ≤ m then lam m / Real.sqrt m else 0) *
      (EF.weilTest R R (Real.log m) + EF.weilTest R R (-Real.log m)).re =
      lam n / Real.sqrt n * (2 * resonatorMass n * σ) := by
    rw [Finset.sum_eq_single n]
    · rw [if_pos hn]
      have := atomCoeff_twoPointResonator hn σ hn
      rw [if_pos rfl, ← hR] at this
      congr 1
    · intro m _ hmn
      by_cases h2 : 2 ≤ m
      · have := atomCoeff_twoPointResonator hn σ h2
        rw [if_neg hmn, mul_zero, ← hR] at this
        rw [if_pos h2]
        change _ * atomCoeff R m = 0
        rw [this, mul_zero]
      · simp [h2]
    · exact fun hnot => absurd (Finset.mem_range.mpr hnN) hnot
  have hE := h R hR2 hfs
  rw [datumEnergy_eq, e, hsum, hpole, hmass] at hE
  have hpos : 0 < 2 * resonatorMass n := by linarith
  refine le_of_mul_le_mul_left ?_ hpos
  nlinarith

/-- On the cone of a datum with conductor `s`, the deviation from `Λ` on the integers a smaller radius sees is
bounded by `4L + C₀ + s`. -/
theorem abs_sub_vonMangoldt_div_sqrt_le_of_mem_datumCone {β s c L : ℝ} {lam : ℕ → ℝ}
    (h : lam ∈ datumCone β s c) (hLc : L + 1 / 12 ≤ c) {n : ℕ} (hn : 2 ≤ n)
    (hnL : (n : ℝ) ≤ Real.exp (2 * L)) :
    |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / Real.sqrt n ≤ 4 * L + boxConst + s := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : Real.log n ≤ 2 * L := (Real.log_le_iff_le_exp hn0).mpr hnL
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlev : atomLevel n ≤ c := by
    unfold atomLevel
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hs0 : 0 < Real.sqrt n := by linarith
  have hplus := mul_div_sqrt_le_of_mem_datumCone h hn hlev (σ := 1) (Or.inl rfl)
  have hminus := mul_div_sqrt_le_of_mem_datumCone h hn hlev (σ := -1) (Or.inr rfl)
  have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ1 : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have hΛ2 : (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n ≤ Real.log n :=
    div_le_of_le_mul₀ hs0.le hlog0 (hΛ1.trans (le_mul_of_one_le_right hlog0 hs))
  have hΛ3 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := by positivity
  have e : |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / Real.sqrt n =
      |lam n / Real.sqrt n - (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n| := by
    rw [← sub_div, abs_div, abs_of_pos hs0]
  rw [e, abs_le]
  constructor <;> linarith

/-! ### Moments of the truncated family -/

theorem abs_mul_exp_le_self (j : ℕ) (x : ℝ) :
    |𝔽 j x| * Real.exp (1 / 2 * |x|) ≤ decayConst * gammaScale j * Real.exp (-|x|) := by
  have hA := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  refine (abs_mul_exp_le_of_tail j (le_refl |x|)).trans (mul_le_mul_of_nonneg_left ?_ hA)
  exact mul_le_of_le_one_right (Real.exp_pos _).le (doubleExpTail_le_one _)

theorem abs_truncTest_sub_mul_exp_le (j : ℕ) (L t : ℝ) :
    |truncTest (𝔽 j) L t - 𝔽 j t| * Real.exp (1 / 2 * |t|) ≤
      decayConst * gammaScale j * (Real.exp (-|t|) * doubleExpTail (L - 1)) := by
  have hA := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  rcases le_or_gt |t| (L - 1) with ht | ht
  · rw [truncTest_eq_self ht, sub_self, abs_zero, zero_mul]
    exact mul_nonneg hA (mul_nonneg (Real.exp_pos _).le (doubleExpTail_pos _).le)
  · have e : truncTest (𝔽 j) L t - 𝔽 j t = 𝔽 j t * (bulkCutoff L t - 1) := by
      unfold truncTest
      ring
    have hb : |bulkCutoff L t - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [bulkCutoff_nonneg L t, bulkCutoff_le_one L t]
    rw [e, abs_mul]
    refine le_trans ?_ (abs_mul_exp_le_of_tail j ht.le)
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) hb) (Real.exp_pos _).le

section Moments

variable {E : ℝ → ℝ} (hEc : Continuous E) (hE : ∀ u, |E u| ≤ Real.exp (1 / 2 * |u|))
include hEc hE

theorem abs_integral_test_mul_le (j : ℕ) :
    Integrable (fun u => 𝔽 j u * E u) ∧
      |∫ u, 𝔽 j u * E u| ≤ decayConst * gammaScale j * absMass := by
  have hA := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  have hb : ∀ u, ‖𝔽 j u * E u‖ ≤ decayConst * gammaScale j * Real.exp (-|u|) := fun u => by
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hE u) (abs_nonneg _)).trans (abs_mul_exp_le_self j u)
  have hg : Integrable fun u : ℝ => decayConst * gammaScale j * Real.exp (-|u|) :=
    integrable_exp_neg_abs.const_mul _
  refine ⟨hg.mono' ((continuous_xiShiftedGammaTest j).mul hEc).aestronglyMeasurable
    (Eventually.of_forall hb), ?_⟩
  have h := norm_integral_le_of_norm_le hg (Eventually.of_forall hb)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  exact h

theorem abs_integral_truncTest_mul_le (j : ℕ) (L : ℝ) :
    Integrable (fun u => truncTest (𝔽 j) L u * E u) ∧
      |∫ u, truncTest (𝔽 j) L u * E u| ≤ decayConst * gammaScale j * absMass := by
  have hA := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  have hb : ∀ u, ‖truncTest (𝔽 j) L u * E u‖ ≤ decayConst * gammaScale j * Real.exp (-|u|) :=
    fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      refine le_trans ?_ (abs_mul_exp_le_self j u)
      exact mul_le_mul (abs_truncTest_le _ L u) (hE u) (abs_nonneg _) (abs_nonneg _)
  have hg : Integrable fun u : ℝ => decayConst * gammaScale j * Real.exp (-|u|) :=
    integrable_exp_neg_abs.const_mul _
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  refine ⟨hg.mono' ((contDiff_truncTest (hF j).1 L).continuous.mul hEc).aestronglyMeasurable
    (Eventually.of_forall hb), ?_⟩
  have h := norm_integral_le_of_norm_le hg (Eventually.of_forall hb)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  exact h

theorem abs_integral_truncTest_mul_sub_le (j : ℕ) (L : ℝ) :
    |(∫ u, truncTest (𝔽 j) L u * E u) - ∫ u, 𝔽 j u * E u| ≤
      decayConst * gammaScale j * absMass * doubleExpTail (L - 1) := by
  rw [← integral_sub (abs_integral_truncTest_mul_le hEc hE j L).1 (abs_integral_test_mul_le hEc hE j).1]
  set Q : ℝ := decayConst * gammaScale j * doubleExpTail (L - 1) with hQ
  have hg : Integrable fun u : ℝ => Q * Real.exp (-|u|) := integrable_exp_neg_abs.const_mul _
  have h := norm_integral_le_of_norm_le hg (f := fun u =>
      truncTest (𝔽 j) L u * E u - 𝔽 j u * E u) (Eventually.of_forall fun u => by
    have e : truncTest (𝔽 j) L u * E u - 𝔽 j u * E u = (truncTest (𝔽 j) L u - 𝔽 j u) * E u := by
      ring
    rw [Real.norm_eq_abs, e, abs_mul]
    calc |truncTest (𝔽 j) L u - 𝔽 j u| * |E u|
        ≤ |truncTest (𝔽 j) L u - 𝔽 j u| * Real.exp (1 / 2 * |u|) :=
          mul_le_mul_of_nonneg_left (hE u) (abs_nonneg _)
      _ ≤ _ := abs_truncTest_sub_mul_exp_le j L u
      _ = Q * Real.exp (-|u|) := by rw [hQ]; ring)
  rw [integral_const_mul, Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [hQ]
  unfold absMass
  ring

end Moments

theorem abs_exp_neg_half_le (u : ℝ) : |Real.exp (-u / 2)| ≤ Real.exp (1 / 2 * |u|) := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [neg_abs_le u])

theorem abs_exp_half_le (u : ℝ) : |Real.exp (u / 2)| ≤ Real.exp (1 / 2 * |u|) := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith [le_abs_self u])

/-- The pole term of a truncated family member. -/
def nullPole (j : ℕ) (L : ℝ) : ℝ :=
  2 * ((∫ u, truncTest (𝔽 j) L u * Real.exp (-u / 2)) * ∫ u, truncTest (𝔽 j) L u * Real.exp (u / 2))

/-- The pole term of the untruncated family: `½` at `j = 0` and `0` beyond. -/
theorem two_mul_moments_eq (j : ℕ) :
    2 * ((∫ u, 𝔽 j u * Real.exp (-u / 2)) * ∫ u, 𝔽 j u * Real.exp (u / 2)) =
      if j = 0 then (1 / 2 : ℝ) else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [if_pos rfl]
    exact pole_xiShiftedGammaTest_zero
  · rw [if_neg (by omega), integral_xiShiftedGammaTest_mul_exp_neg_half_of_pos hj]
    ring

/-- The pole term of a truncation deviates by the doubly exponential tail. -/
theorem abs_nullPole_sub_le (j : ℕ) (L : ℝ) :
    |nullPole j L - (if j = 0 then (1 / 2 : ℝ) else 0)| ≤
      4 * (decayConst * gammaScale j * absMass) ^ 2 * doubleExpTail (L - 1) := by
  have hcm : Continuous fun u : ℝ => Real.exp (-u / 2) := by fun_prop
  have hcp : Continuous fun u : ℝ => Real.exp (u / 2) := by fun_prop
  rw [← two_mul_moments_eq j]
  unfold nullPole
  obtain ⟨a', ha'⟩ : ∃ a', a' = ∫ u, truncTest (𝔽 j) L u * Real.exp (-u / 2) := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = ∫ u, truncTest (𝔽 j) L u * Real.exp (u / 2) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = ∫ u, 𝔽 j u * Real.exp (-u / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ∫ u, 𝔽 j u * Real.exp (u / 2) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = decayConst * gammaScale j * absMass := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg decayConst_nonneg (gammaScale_nonneg j)) absMass_nonneg
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = doubleExpTail (L - 1) := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; exact (doubleExpTail_pos _).le
  have h1 : |a' - a| ≤ A * τ := by
    rw [ha', ha, hA, hτ]
    exact abs_integral_truncTest_mul_sub_le hcm abs_exp_neg_half_le j L
  have h2 : |b' - b| ≤ A * τ := by
    rw [hb', hb, hA, hτ]
    exact abs_integral_truncTest_mul_sub_le hcp abs_exp_half_le j L
  have h3 : |a| ≤ A := by
    rw [ha, hA]
    exact (abs_integral_test_mul_le hcm abs_exp_neg_half_le j).2
  have h4 : |b'| ≤ A := by
    rw [hb', hA]
    exact (abs_integral_truncTest_mul_le hcp abs_exp_half_le j L).2
  rw [← ha', ← hb', ← ha, ← hb, ← hA, ← hτ]
  have e : 2 * (a' * b') - 2 * (a * b) = 2 * ((a' - a) * b') + 2 * (a * (b' - b)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have p1 : |a' - a| * |b'| ≤ A * τ * A := mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
  have p2 : |a| * |b' - b| ≤ A * (A * τ) := mul_le_mul h3 h2 (abs_nonneg _) hA0
  nlinarith

theorem abs_nullPole_le (j : ℕ) (L : ℝ) :
    |nullPole j L| ≤ 2 * (decayConst * gammaScale j * absMass) ^ 2 := by
  have hcm : Continuous fun u : ℝ => Real.exp (-u / 2) := by fun_prop
  have hcp : Continuous fun u : ℝ => Real.exp (u / 2) := by fun_prop
  have h1 := (abs_integral_truncTest_mul_le hcm abs_exp_neg_half_le j L).2
  have h2 := (abs_integral_truncTest_mul_le hcp abs_exp_half_le j L).2
  have hA : 0 ≤ decayConst * gammaScale j * absMass :=
    mul_nonneg (mul_nonneg decayConst_nonneg (gammaScale_nonneg j)) absMass_nonneg
  unfold nullPole
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), sq]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) hA) (by norm_num)

/-- The mass of a truncated family member. -/
def nullMass (j : ℕ) (L : ℝ) : ℝ := ∫ u, ‖nullTest j L u‖ ^ 2

theorem nullMass_nonneg (j : ℕ) (L : ℝ) : 0 ≤ nullMass j L :=
  integral_nonneg fun _ => by positivity

theorem nullMass_le (j : ℕ) (L : ℝ) :
    nullMass j L ≤ (decayConst * gammaScale j) ^ 2 * absMass := by
  have hA := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  have hg : Integrable fun u : ℝ => (decayConst * gammaScale j) ^ 2 * Real.exp (-|u|) :=
    integrable_exp_neg_abs.const_mul _
  have hle : nullMass j L ≤ ∫ u : ℝ, (decayConst * gammaScale j) ^ 2 * Real.exp (-|u|) := by
    unfold nullMass
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity) hg
      (Eventually.of_forall fun u => ?_)
    simp only [nullTest, Complex.norm_real, Real.norm_eq_abs]
    calc |truncTest (𝔽 j) L u| ^ 2 = |truncTest (𝔽 j) L u| * |truncTest (𝔽 j) L u| := sq _
      _ ≤ (decayConst * gammaScale j * Real.exp (-|u|)) * (decayConst * gammaScale j) :=
          mul_le_mul (abs_truncTest_le_exp j L u) (abs_truncTest_le_const j L u) (abs_nonneg _)
            (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by ring
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul]
  rfl

/-- The energy of a datum on a truncated family member. -/
theorem datumEnergy_nullTest (β s : ℝ) (lam : ℕ → ℝ) (j : ℕ) (L : ℝ) :
    datumEnergy β s lam (nullTest j L) =
      nullEnergy lam j L + (β - 1) * nullPole j L + s * nullMass j L := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  have hc := (contDiff_truncTest (hF j).1 L).continuous
  rw [datumEnergy_eq]
  have hp : (weilPoleTerm (EF.weilTest (nullTest j L) (nullTest j L))).re = nullPole j L :=
    re_pole_weilTest_ofReal hc (hasCompactSupport_truncTest _ L)
  rw [hp]
  rfl

/-! ### The sums over the family -/

theorem summable_nullPole {w : ℕ → ℝ} (hw : NullWeights w) (L : ℝ) :
    Summable fun j => w j * nullPole j L := by
  refine Summable.of_norm_bounded
    (g := fun j => (2 * (decayConst * absMass) ^ 2) * (w j * gammaScale j ^ 2))
    (hw.summable.mul_left _) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg j)]
  calc w j * |nullPole j L| ≤ w j * (2 * (decayConst * gammaScale j * absMass) ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_nullPole_le j L) (hw.nonneg j)
    _ = _ := by ring

theorem summable_nullMass {w : ℕ → ℝ} (hw : NullWeights w) (L : ℝ) :
    Summable fun j => w j * nullMass j L := by
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hw.nonneg j) (nullMass_nonneg j L))
    (fun j => ?_) (hw.summable.mul_left (decayConst ^ 2 * absMass))
  calc w j * nullMass j L ≤ w j * ((decayConst * gammaScale j) ^ 2 * absMass) :=
        mul_le_mul_of_nonneg_left (nullMass_le j L) (hw.nonneg j)
    _ = _ := by ring

/-- The total pole of the truncated family is `w₀/2` up to the tail. -/
theorem tsum_nullPole_ge {w : ℕ → ℝ} (hw : NullWeights w) (L : ℝ) :
    w 0 / 2 - (4 * (decayConst * absMass) ^ 2 * ∑' j, w j * gammaScale j ^ 2) *
        doubleExpTail (L - 1) ≤ ∑' j, w j * nullPole j L := by
  have hs0 : Summable fun j => w j * (if j = 0 then (1 / 2 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj
      simp [hj]
  have hs0v : ∑' j, w j * (if j = 0 then (1 / 2 : ℝ) else 0) = w 0 / 2 := by
    rw [tsum_eq_single 0 fun j hj => by simp [hj]]
    simp
    ring
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = doubleExpTail (L - 1) := ⟨_, rfl⟩
  rw [← hτ]
  have hsumr : Summable fun j => w j * (if j = 0 then (1 / 2 : ℝ) else 0) -
      (4 * (decayConst * absMass) ^ 2 * τ) * (w j * gammaScale j ^ 2) :=
    hs0.sub (hw.summable.mul_left _)
  have hvr : ∑' j, (w j * (if j = 0 then (1 / 2 : ℝ) else 0) -
      (4 * (decayConst * absMass) ^ 2 * τ) * (w j * gammaScale j ^ 2)) =
      w 0 / 2 - (4 * (decayConst * absMass) ^ 2 * ∑' j, w j * gammaScale j ^ 2) * τ := by
    rw [hs0.tsum_sub (hw.summable.mul_left _), hs0v, tsum_mul_left]
    ring
  rw [← hvr]
  refine hsumr.tsum_le_tsum (fun j => ?_) (summable_nullPole hw L)
  have h := abs_nullPole_sub_le j L
  rw [← hτ] at h
  have h2 := (abs_le.mp h).1
  have e : (4 * (decayConst * absMass) ^ 2 * τ) * (w j * gammaScale j ^ 2) =
      w j * (4 * (decayConst * gammaScale j * absMass) ^ 2 * τ) := by ring
  rw [e, ← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (hw.nonneg j)
  linarith

/-- The total mass of the truncated family is bounded uniformly in the radius. -/
theorem tsum_nullMass_le {w : ℕ → ℝ} (hw : NullWeights w) (L : ℝ) :
    ∑' j, w j * nullMass j L ≤ decayConst ^ 2 * absMass * ∑' j, w j * gammaScale j ^ 2 := by
  have hbd : Summable fun j => (decayConst ^ 2 * absMass) * (w j * gammaScale j ^ 2) :=
    hw.summable.mul_left _
  refine ((summable_nullMass hw L).tsum_le_tsum (fun j => ?_) hbd).trans (le_of_eq ?_)
  · calc w j * nullMass j L ≤ w j * ((decayConst * gammaScale j) ^ 2 * absMass) :=
          mul_le_mul_of_nonneg_left (nullMass_le j L) (hw.nonneg j)
      _ = _ := by ring
  · rw [tsum_mul_left]

/-- A point of the cone of a datum has nonnegative total energy on the family. -/
theorem tsum_datum_nonneg {w : ℕ → ℝ} (hw : NullWeights w) {β s c L : ℝ} {lam : ℕ → ℝ}
    (hlam : lam ∈ datumCone β s c) (hL : L ≤ c)
    (hsE : Summable fun j => w j * nullEnergy lam j L) :
    0 ≤ ∑' j, w j * nullEnergy lam j L + (β - 1) * ∑' j, w j * nullPole j L +
      s * ∑' j, w j * nullMass j L := by
  have hsP := summable_nullPole hw L
  have hsM := summable_nullMass hw L
  have hterm : ∀ j, 0 ≤ (w j * nullEnergy lam j L + (β - 1) * (w j * nullPole j L)) +
      s * (w j * nullMass j L) := by
    intro j
    have h := hlam (nullTest j L) (contDiff_nullTest j L) (tsupport_nullTest_subset j hL)
    rw [datumEnergy_nullTest] at h
    have := mul_nonneg (hw.nonneg j) h
    linarith
  have hsum : 0 ≤ ∑' j, ((w j * nullEnergy lam j L + (β - 1) * (w j * nullPole j L)) +
      s * (w j * nullMass j L)) := tsum_nonneg hterm
  rwa [(hsE.add (hsP.mul_left _)).tsum_add (hsM.mul_left _), hsE.tsum_add (hsP.mul_left _),
    tsum_mul_left, tsum_mul_left] at hsum

/-- The polynomial factor of the family bound on the window `c`, conductor `s`. -/
theorem polynomial_factor_le {c s : ℝ} (hc : 1 ≤ c) (hs : 0 ≤ s) :
    (1 + (4 * (c - 1 / 12) + boxConst + s)) * (Real.exp (2 * (c - 1 / 12)) + 1) ≤
      (1 + s) * (2 * (5 + boxConst)) * Real.exp (3 * c) := by
  have hC := boxConst_nonneg
  have hec : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
  have hfac1 : 1 + (4 * (c - 1 / 12) + boxConst + s) ≤ (1 + s) * ((5 + boxConst) * Real.exp c) := by
    have h1 : (5 + boxConst) * (1 + c) ≤ (5 + boxConst) * Real.exp c :=
      mul_le_mul_of_nonneg_left hec (by linarith)
    have h5 : (1 : ℝ) ≤ (5 + boxConst) * Real.exp c := by nlinarith
    have h6 : s ≤ s * ((5 + boxConst) * Real.exp c) := le_mul_of_one_le_right hs h5
    nlinarith
  have hfac2 : Real.exp (2 * (c - 1 / 12)) + 1 ≤ 2 * Real.exp (2 * c) := by
    have h1 : Real.exp (2 * (c - 1 / 12)) ≤ Real.exp (2 * c) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : (1 : ℝ) ≤ Real.exp (2 * c) := Real.one_le_exp (by linarith)
    linarith
  have h3 : Real.exp (3 * c) = Real.exp c * Real.exp (2 * c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h3]
  calc _ ≤ ((1 + s) * ((5 + boxConst) * Real.exp c)) * (2 * Real.exp (2 * c)) :=
        mul_le_mul hfac1 hfac2 (by positivity) (by positivity)
    _ = _ := by ring

theorem tail_le_ceiling {c : ℝ} (hc : 1 ≤ c) :
    Real.exp (3 * c) * doubleExpTail (c - 1 / 12 - 1) ≤ marginCeiling c ∧
      doubleExpTail (c - 1 / 12 - 1) ≤ marginCeiling c := by
  have hτ0 := (doubleExpTail_pos (c - 1 / 12 - 1)).le
  have hτ₁ : doubleExpTail (c - 1 / 12 - 1) ≤ doubleExpTail (c - 2) :=
    doubleExpTail_anti (by linarith)
  have hτ2 : Real.exp (3 * c) * doubleExpTail (c - 1 / 12 - 1) ≤ marginCeiling c := by
    rw [← exp_mul_doubleExpTail]
    exact mul_le_mul_of_nonneg_left hτ₁ (Real.exp_pos _).le
  refine ⟨hτ2, ?_⟩
  have h1 : (1 : ℝ) ≤ Real.exp (3 * c) := Real.one_le_exp (by linarith)
  calc doubleExpTail (c - 1 / 12 - 1) = 1 * doubleExpTail (c - 1 / 12 - 1) := (one_mul _).symm
    _ ≤ Real.exp (3 * c) * doubleExpTail (c - 1 / 12 - 1) := mul_le_mul_of_nonneg_right h1 hτ0
    _ ≤ _ := hτ2

/-- The arithmetic of the trade-off. -/
theorem trade_off_arith {β s E P M w₂ K₁ K₂ T₀ τ C₀ : ℝ} (hs : 0 ≤ s) (hβ : β ≤ 1) (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hC₀ : 0 ≤ C₀) (h0 : 0 ≤ E + (β - 1) * P + s * M)
    (hE : E ≤ (1 + s) * K₁ * C₀) (hP : w₂ - K₂ * τ ≤ P) (hM : M ≤ T₀) (hτ : τ ≤ C₀) :
    (1 - β) * w₂ ≤ (1 + s + (1 - β)) * (K₁ + K₂) * C₀ + s * T₀ := by
  have ha : 0 ≤ 1 - β := by linarith
  have h4 : (β - 1) * P ≤ (β - 1) * (w₂ - K₂ * τ) := mul_le_mul_of_nonpos_left hP (by linarith)
  have h5 : s * M ≤ s * T₀ := mul_le_mul_of_nonneg_left hM hs
  have h3 : (1 - β) * (K₂ * τ) ≤ (1 - β) * (K₂ * C₀) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ hK₂) ha
  have p1 : 0 ≤ (1 + s) * K₂ * C₀ := by positivity
  have p2 : 0 ≤ (1 - β) * K₁ * C₀ := by positivity
  have e1 : (1 + s + (1 - β)) * (K₁ + K₂) * C₀ =
      (1 + s) * K₁ * C₀ + (1 + s) * K₂ * C₀ + (1 - β) * K₁ * C₀ + (1 - β) * (K₂ * C₀) := by ring
  have e2 : (β - 1) * (w₂ - K₂ * τ) = -((1 - β) * w₂) + (1 - β) * (K₂ * τ) := by ring
  rw [e1]
  linarith

/-! ### The trade-off -/

/-- **Pole and conductor trade off.** There are constants `w₀ > 0`, `T₀, K ≥ 0` such that a nonempty cone
of a datum with `β ≤ 1`, `s ≥ 0` on a window `c ≥ 1` has
`(1 − β) w₀ ≤ (1 + s + 1 − β) K exp(3c − (π/16) e^{2(c−2)}) + s T₀`. -/
theorem exists_datum_constants :
    ∃ w₀ T₀ K : ℝ, 0 < w₀ ∧ 0 ≤ T₀ ∧ 0 ≤ K ∧ ∀ β s c : ℝ, β ≤ 1 → 0 ≤ s → 1 ≤ c →
      (datumCone β s c).Nonempty →
        (1 - β) * w₀ ≤ (1 + s + (1 - β)) * K * marginCeiling c + s * T₀ := by
  obtain ⟨w, hw⟩ := exists_nullWeights
  obtain ⟨K₀, hK₀, hmain⟩ := exists_tsum_nullEnergy_le hw
  obtain ⟨B, hB⟩ : ∃ B, B = ∑' j, w j * gammaScale j ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact tsum_nonneg fun j => mul_nonneg (hw.nonneg j) (sq_nonneg _)
  have hC := boxConst_nonneg
  have hI := absMass_nonneg
  have hD := decayConst_nonneg
  have hw0 := hw.pos_zero
  have hK₂0 : 0 ≤ 4 * (decayConst * absMass) ^ 2 * B := by positivity
  have hK₁0 : 0 ≤ K₀ * (2 * (5 + boxConst)) := by positivity
  refine ⟨w 0 / 2, decayConst ^ 2 * absMass * B,
    K₀ * (2 * (5 + boxConst)) + 4 * (decayConst * absMass) ^ 2 * B, by positivity, by positivity,
    add_nonneg hK₁0 hK₂0, fun β s c hβ hs hc hne => ?_⟩
  obtain ⟨lam, hlam⟩ := hne
  have hV : 0 ≤ 4 * (c - 1 / 12) + boxConst + s := by linarith
  obtain ⟨hsE, hleE⟩ := hmain (c - 1 / 12) (4 * (c - 1 / 12) + boxConst + s) lam hV
    (fun n hn hnL => abs_sub_vonMangoldt_div_sqrt_le_of_mem_datumCone hlam (by linarith) hn hnL)
  obtain ⟨hτ2, hτ3⟩ := tail_le_ceiling hc
  have hM := (marginCeiling_pos c).le
  have hτ0 := (doubleExpTail_pos (c - 1 / 12 - 1)).le
  have hEner : ∑' j, w j * nullEnergy lam j (c - 1 / 12) ≤
      (1 + s) * (K₀ * (2 * (5 + boxConst))) * marginCeiling c := by
    refine hleE.trans ?_
    calc K₀ * ((1 + (4 * (c - 1 / 12) + boxConst + s)) * (Real.exp (2 * (c - 1 / 12)) + 1)) *
          doubleExpTail (c - 1 / 12 - 1)
        ≤ K₀ * ((1 + s) * (2 * (5 + boxConst)) * Real.exp (3 * c)) *
            doubleExpTail (c - 1 / 12 - 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (polynomial_factor_le hc hs) hK₀) hτ0
      _ = (1 + s) * (K₀ * (2 * (5 + boxConst))) *
            (Real.exp (3 * c) * doubleExpTail (c - 1 / 12 - 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ2 (by positivity)
  have hP := tsum_nullPole_ge hw (c - 1 / 12)
  rw [← hB] at hP
  have hMs := tsum_nullMass_le hw (c - 1 / 12)
  rw [← hB] at hMs
  exact trade_off_arith hs hβ hK₁0 hK₂0 hM
    (tsum_datum_nonneg hw hlam (by linarith) hsE) hEner hP hMs hτ3

/-- **The window reads the residue.** A nonempty cone at conductor one has
`β ≥ 1 − K′ exp(3c − (π/16) e^{2(c−2)})`, from a finite window on, whatever the weights. -/
theorem exists_one_sub_le_of_datumCone :
    ∃ K' c₁ : ℝ, 0 < K' ∧ ∀ c β : ℝ, c₁ ≤ c → (datumCone β 0 c).Nonempty →
      1 - K' * marginCeiling c ≤ β := by
  obtain ⟨w₀, T₀, K, hw₀, -, hK, h⟩ := exists_datum_constants
  have hlim : Tendsto (fun c => K * marginCeiling c) atTop (𝓝 0) := by
    simpa using tendsto_marginCeiling.const_mul K
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hw₀)))
  refine ⟨2 * K / w₀ + 1, max c₂ 1, by positivity, fun c β hc hne => ?_⟩
  have hM := marginCeiling_pos c
  by_cases hβ : β ≤ 1
  · have h1 := h β 0 c hβ le_rfl ((le_max_right _ _).trans hc) hne
    have h2 := hc₂ c ((le_max_left _ _).trans hc)
    simp only [add_zero, zero_mul] at h1
    have h1β : 0 ≤ 1 - β := by linarith
    have h3 : (1 - β) * (w₀ / 2) ≤ K * marginCeiling c := by nlinarith
    have h4 : 1 - β ≤ 2 * K / w₀ * marginCeiling c := by
      have e : 2 * K / w₀ * marginCeiling c = (K * marginCeiling c) / (w₀ / 2) := by
        field_simp
      rw [e, le_div_iff₀ (half_pos hw₀)]
      exact h3
    nlinarith
  · have : 0 < (2 * K / w₀ + 1) * marginCeiling c := by positivity
    linarith [not_le.mp hβ]

/-- **No pole needs conductor.** There is `s₁ > 0` such that a pole-free datum with log-conductor below `s₁`
has an empty cone from a finite window on. -/
theorem exists_pos_forall_lt_datumCone_zero_eq_empty :
    ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s, s < s₁ → ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → datumCone 0 s c = ∅ := by
  obtain ⟨w₀, T₀, K, hw₀, hT₀, hK, h⟩ := exists_datum_constants
  refine ⟨w₀ / (2 * (T₀ + 1)), by positivity, fun s hs => ?_⟩
  set s₁ : ℝ := w₀ / (2 * (T₀ + 1)) with hs₁
  have hs₁0 : 0 < s₁ := by positivity
  have hlim : Tendsto (fun c => (2 + s₁) * K * marginCeiling c) atTop (𝓝 0) := by
    simpa using tendsto_marginCeiling.const_mul ((2 + s₁) * K)
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hw₀)))
  refine ⟨max c₂ 1, fun c hc => Set.eq_empty_of_forall_notMem fun lam hlam => ?_⟩
  set s' : ℝ := max s 0 with hs'
  have hs'0 : 0 ≤ s' := le_max_right _ _
  have hs'1 : s' ≤ s₁ := max_le hs.le hs₁0.le
  have hmem : lam ∈ datumCone 0 s' c := datumCone_mono_conductor (le_max_left _ _) hlam
  have h1 := h 0 s' c (by norm_num) hs'0 ((le_max_right _ _).trans hc) ⟨lam, hmem⟩
  have h2 := hc₂ c ((le_max_left _ _).trans hc)
  have hM := marginCeiling_pos c
  have h3 : s' * T₀ ≤ w₀ / 2 * (T₀ / (T₀ + 1)) := by
    have e : w₀ / 2 * (T₀ / (T₀ + 1)) = s₁ * T₀ := by
      rw [hs₁]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hs'1 hT₀
  have h4 : T₀ / (T₀ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have h5 : w₀ / 2 * (T₀ / (T₀ + 1)) < w₀ / 2 := by nlinarith
  have h6 : (1 + s' + (1 - 0)) * K * marginCeiling c ≤ (2 + s₁) * K * marginCeiling c := by
    have hp : 0 ≤ K * marginCeiling c := by positivity
    nlinarith
  simp only [sub_zero, one_mul] at h1
  have h7 : (1 + s' + 1) * K * marginCeiling c ≤ (2 + s₁) * K * marginCeiling c := by
    simpa using h6
  linarith

/-- **The corners of the datum plane.**
* Pole one, conductor below one: empty from a finite window on.
* Pole one, conductor one: nonempty at every window iff RH.
* No pole, conductor below `s₁ > 0`: empty from a finite window on.
* No pole, conductor at `log π − ψ(¼)`: the zero weights are positive at every window, and past it the
  cones contain two distinct points at every window. -/
theorem datum_classification :
    (∀ s, s < 0 → ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → datumCone 1 s c = ∅) ∧
    (RiemannHypothesis ↔ ∀ c, 3 / 10 ≤ c → (datumCone 1 0 c).Nonempty) ∧
    (∃ s₁ : ℝ, 0 < s₁ ∧ ∀ s, s < s₁ → ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → datumCone 0 s c = ∅) ∧
    (∀ s, (∀ c, (fun _ => (0 : ℝ)) ∈ datumCone 0 s c) ↔ -EF.gammaBracket 0 ≤ s) ∧
    (∀ s, -EF.gammaBracket 0 < s → ∃ lam₁ lam₂ : ℕ → ℝ, lam₁ ≠ lam₂ ∧
      ∀ c, lam₁ ∈ datumCone 0 s c ∧ lam₂ ∈ datumCone 0 s c) :=
  ⟨fun _ hs => exists_datumCone_one_eq_empty hs,
    riemannHypothesis_iff_forall_datumCone_one_zero_nonempty,
    exists_pos_forall_lt_datumCone_zero_eq_empty,
    fun _ => forall_zero_mem_datumCone_zero_iff,
    fun _ hs => exists_ne_mem_forall_datumCone_zero hs⟩

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
