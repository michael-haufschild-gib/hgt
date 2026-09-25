import GaloisForLFunctions.RHTower.SelbergEisensteinCoefficientSeries
import GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBesselOrderExteriorEnvelope

open Complex UpperHalfPlane Metric Filter Topology
open scoped MatrixGroups FourierTransform

/-!
# The non-constant part of the `Γ(N)` Eisenstein series across the critical line

For `Re s > 1/2`, summing the Fourier terms of `E^*_σ(z, s)` first over `c` turns `Σ_c |c|^{-2s} S_σ(0,n;c)` into
`D_n(s)` and `𝓕ker₀` into its Bessel form, so
`E^*_σ(z, s) = Σ_{n≠0} N^{-s} W(y/N, s, n) e(nx/N) D_n(s)` (`Estarσ_eq_EstarExt`), `W = kerBessel`.
The right side (`EstarExt`) is holomorphic on the open set `W = {Re s > 0, 2s ≠ 1, L(2s, χ) ≠ 0 ∀χ}`
(`isOpen_Wset`, `differentiableAt_EstarExt`), which contains `{Re s ≥ 1/2, s ≠ 1/2}` (`mem_Wset_of_half_le`): on
closed balls in `W` the terms are dominated by `C |n|^{k+2} e^{-2πy|n|/N}`, from the Bessel envelope
`|K_ν(a)| ≤ e^{-a} e^{|ν|²/(2a)} √(2π/a)` (`norm_bessel_le`), `|D_n(s)| ≤ B · 2n²` (`norm_Dn_le_sq`) and the power
bound `(|n|/Y)^t ≤ C |n|^k` (`rpow_natAbs_div_le`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier GaloisForLFunctions.RHTower.SelbergEisensteinCoefficientSeries
  GaloisForLFunctions.RHTower.SelbergKernelBessel GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergPoincareContinuation

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The domain of the continuation: `Re s > 0`, `2s ≠ 1`, and `L(2s, χ) ≠ 0` for every `χ mod N`. -/
def Wset : Set ℂ :=
  {s | 0 < s.re ∧ 2 * s ≠ 1 ∧ ∀ χ : DirichletCharacter ℂ N, DirichletCharacter.LFunction χ (2 * s) ≠ 0}

theorem isOpen_Wset : IsOpen (Wset N) := by
  rw [isOpen_iff_mem_nhds]
  rintro s ⟨h0, h1, h2⟩
  have hc : ∀ χ : DirichletCharacter ℂ N, ∀ᶠ t in 𝓝 s, DirichletCharacter.LFunction χ (2 * t) ≠ 0 := by
    intro χ
    have hd : ContinuousAt (fun t : ℂ => DirichletCharacter.LFunction χ (2 * t)) s :=
      ((DirichletCharacter.differentiableAt_LFunction χ (2 * s) (Or.inl h1)).comp s
        (differentiableAt_id.const_mul 2)).continuousAt
    exact hd.eventually_ne (h2 χ)
  have hall : ∀ᶠ t in 𝓝 s, ∀ χ : DirichletCharacter ℂ N, DirichletCharacter.LFunction χ (2 * t) ≠ 0 :=
    Filter.eventually_all.mpr hc
  have hre : ∀ᶠ t in 𝓝 s, 0 < t.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h0
  have hne : ∀ᶠ t in 𝓝 s, 2 * t ≠ 1 :=
    ((continuous_const.mul continuous_id).continuousAt (x := s)).eventually_ne h1
  filter_upwards [hre, hne, hall] with t ht1 ht2 ht3
  exact ⟨ht1, ht2, ht3⟩

theorem mem_Wset_of_half_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1 / 2) : s ∈ Wset N := by
  have h2 : 2 * s ≠ 1 := fun h => hs1 (by linear_combination h / 2)
  exact ⟨by linarith, h2, fun χ => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (by simp; linarith)⟩

/-- The `n`-th continued Fourier term of `E^*_σ`. -/
noncomputable def termX (n : ℤ) (s : ℂ) (z : ℍ) : ℂ :=
  if n = 0 then 0 else
    cexp (-s * (Real.log N : ℂ)) * kerBessel (z.im / N) s n * cexp (2 * Real.pi * Complex.I * n * z.re / N) *
      Dn N σ n s

/-- **The continued non-constant part** `E^*_σ(z, s) = Σ_{n≠0} N^{-s} W_s(n, y/N) e(nx/N) D_n(s)`. -/
noncomputable def EstarExt (s : ℂ) (z : ℍ) : ℂ := ∑' n : ℤ, termX N σ n s z

omit [NeZero N] in
theorem etermσ_eq (s : ℂ) (z : ℍ) {n : ℤ} (hn : n ≠ 0) (c : ℤ) :
    etermσ N σ s z (c, n) = cexp (-s * (Real.log N : ℂ)) * 𝓕 (ker 0 (z.im / N) s) n *
      cexp (2 * Real.pi * Complex.I * n * z.re / N) * ((((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * ksumσ N σ c n) := by
  unfold etermσ
  by_cases hc : c = 0
  · subst hc; simp [ksumσ_zero_left]
  · simp only [hc, hn, or_self, if_false]
    rw [cpow_neg_eq_exp hc]
    ring

/-- For `Re s > 1/2` the continued series is the Fourier series at `σ∞`. -/
theorem Estarσ_eq_EstarExt {s : ℂ} (hs : 1 / 2 < s.re) (z : ℍ) : Estarσ N σ s z = EstarExt N σ s z := by
  have hy : 0 < z.im / N := div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  have hsum := summable_etermσ N σ hs z
  unfold Estarσ EstarExt
  have hsum' : Summable (Function.uncurry fun (c n : ℤ) => etermσ N σ s z (c, n)) := hsum
  rw [show (∑' p : ℤ × ℤ, etermσ N σ s z p) = ∑' c : ℤ, ∑' n : ℤ, etermσ N σ s z (c, n) from
    hsum.tsum_prod, hsum'.tsum_comm.symm]
  apply tsum_congr
  intro n
  unfold termX
  by_cases hn : n = 0
  · subst hn; simp [etermσ]
  rw [if_neg hn]
  simp_rw [etermσ_eq N σ s z hn]
  rw [tsum_mul_left, tsum_ksumσ_eq_Dn N σ hn hs,
    fourier_ker0_eq_bessel hy hs (by exact_mod_cast hn : (n : ℝ) ≠ 0)]

omit [NeZero N] in
theorem norm_bessel_le {Y : ℝ} (hY : 0 < Y) {n : ℤ} (hn : n ≠ 0) {ν : ℂ} {R : ℝ} (hR : ‖ν‖ ≤ R) :
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (2 * Real.pi * Y * |(n : ℝ)|) ν‖ ≤
      Real.exp (-(2 * Real.pi * Y * |(n : ℝ)|)) *
        (Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) * Real.sqrt (2 * Real.pi / (2 * Real.pi * Y))) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have ha0 : 0 < 2 * Real.pi * Y := by positivity
  have ha : 0 < 2 * Real.pi * Y * |(n : ℝ)| := by positivity
  have hle : 2 * Real.pi * Y ≤ 2 * Real.pi * Y * |(n : ℝ)| := le_mul_of_one_le_right ha0.le hn1
  have h := RHTower.d4BM_norm_modifiedBesselKOrder_le ⟨2 * Real.pi * Y * |(n : ℝ)|, ha⟩ ν
  simp only at h
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
    have h1 : ‖ν‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
    calc ‖ν‖ ^ 2 / (2 * (2 * Real.pi * Y * |(n : ℝ)|)) ≤ R ^ 2 / (2 * (2 * Real.pi * Y * |(n : ℝ)|)) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ R ^ 2 / (2 * (2 * Real.pi * Y)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) ha0 hle)

theorem norm_Dn_le_sq (n : ℤ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Dn N σ n s‖ ≤ (∑ u : (ZMod N)ˣ, ‖LU N u (2 * s)‖) * (2 * (n.natAbs : ℝ) ^ 2) := by
  refine (norm_Dn_le N σ n s).trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  calc ∑ M ∈ n.natAbs.divisors, 2 * (M : ℝ) ^ (1 - 2 * s.re)
      ≤ ∑ _M ∈ n.natAbs.divisors, 2 * (n.natAbs : ℝ) := by
        refine Finset.sum_le_sum (fun M hM => ?_)
        have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.pos_of_mem_divisors hM
        have h1 : (M : ℝ) ^ (1 - 2 * s.re) ≤ (M : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
        have h2 : (M : ℝ) ≤ n.natAbs := by exact_mod_cast Nat.divisor_le hM
        rw [Real.rpow_one] at h1
        linarith
    _ = n.natAbs.divisors.card * (2 * (n.natAbs : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n.natAbs * (2 * (n.natAbs : ℝ)) := by
        gcongr; exact_mod_cast Nat.card_divisors_le_self _
    _ = 2 * (n.natAbs : ℝ) ^ 2 := by ring

omit [NeZero N] in
theorem rpow_natAbs_div_le {Y : ℝ} (hY : 0 < Y) {n : ℤ} (hn : n ≠ 0) {t lo hi : ℝ} {k : ℕ}
    (h1 : lo ≤ t) (h2 : t ≤ hi) (hlo : lo ≤ k) (hhi : hi ≤ k) :
    (|(n : ℝ)| / Y) ^ t ≤ ((Y ^ lo)⁻¹ + (Y ^ hi)⁻¹) * (n.natAbs : ℝ) ^ k := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hx : 0 < |(n : ℝ)| / Y := div_pos (by linarith) hY
  refine (rpow_le_add hx h1 h2).trans ?_
  have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by simp [Nat.cast_natAbs]
  rw [Real.div_rpow (by linarith) hY.le, Real.div_rpow (by linarith) hY.le, add_mul]
  have e1 : |(n : ℝ)| ^ lo ≤ (n.natAbs : ℝ) ^ k := by
    rw [habs, ← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (habs ▸ hn1) hlo
  have e2 : |(n : ℝ)| ^ hi ≤ (n.natAbs : ℝ) ^ k := by
    rw [habs, ← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (habs ▸ hn1) hhi
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left e1 (by positivity)) (mul_le_mul_of_nonneg_left e2 (by positivity))

/-- **Holomorphy of the continued non-constant part** on the open set `W` (which contains `Re s ≥ 1/2`, `s ≠ 1/2`). -/
theorem differentiableAt_EstarExt (z : ℍ) {s₀ : ℂ} (hs₀ : s₀ ∈ Wset N) :
    DifferentiableAt ℂ (fun s => EstarExt N σ s z) s₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_Wset N) s₀ hs₀
  set r := ε / 2
  have hr : 0 < r := by simp only [r]; linarith
  have hcb : closedBall s₀ r ⊆ Wset N := (closedBall_subset_ball (by simp only [r]; linarith)).trans hball
  have hbW : ball s₀ r ⊆ Wset N := ball_subset_closedBall.trans hcb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set Y := z.im / N
  have hY : 0 < Y := div_pos z.im_pos hN0
  -- the Gamma-factor bound
  set f1 : ℂ → ℂ := fun s => 2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf1 : Continuous f1 := (Differentiable.continuous (fun s =>
    ((differentiableAt_id.const_cpow (Or.inl hpi)).const_mul 2).mul (Complex.differentiable_one_div_Gamma s)))
  obtain ⟨B1, hB1⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hf1.continuousOn
  have hB1n : 0 ≤ B1 := (norm_nonneg _).trans (hB1 s₀ (mem_closedBall_self hr.le))
  -- the `L_u` bound
  set f2 : ℂ → ℝ := fun s => ∑ u : (ZMod N)ˣ, ‖LU N u (2 * s)‖
  have hf2 : ContinuousOn f2 (closedBall s₀ r) := by
    intro s hs
    obtain ⟨_, h1, h2⟩ := hcb hs
    refine ContinuousAt.continuousWithinAt ?_
    refine tendsto_finsetSum _ (fun u _ => ?_)
    exact ((differentiableAt_LU_of N u h1 h2).comp s (differentiableAt_id.const_mul 2)).continuousAt.norm
  obtain ⟨B2, hB2⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hf2
  have hB2' : ∀ s ∈ closedBall s₀ r, f2 s ≤ B2 := fun s hs => (le_abs_self _).trans (hB2 s hs)
  have hB2n : 0 ≤ B2 := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans (hB2' s₀ (mem_closedBall_self hr.le))
  -- exponents
  set σ₁ := s₀.re - r
  set σ₂ := s₀.re + r
  set lo := σ₁ - 1 / 2
  set hi := σ₂ - 1 / 2
  set k : ℕ := ⌈|lo| + |hi|⌉₊
  have hlo : lo ≤ k := (le_abs_self lo).trans ((le_add_of_nonneg_right (abs_nonneg hi)).trans (Nat.le_ceil _))
  have hhi : hi ≤ k := (le_abs_self hi).trans ((le_add_of_nonneg_left (abs_nonneg lo)).trans (Nat.le_ceil _))
  set R := ‖s₀‖ + r + 1 / 2
  set E0 := Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) * Real.sqrt (2 * Real.pi / (2 * Real.pi * Y))
  set C := (Y ^ σ₁ + Y ^ σ₂) * B1 * ((Y ^ lo)⁻¹ + (Y ^ hi)⁻¹) * E0 * (B2 * 2)
  have hC : 0 ≤ C := by simp only [C, E0]; positivity
  set bound : ℤ → ℝ := fun n => if n = 0 then 0 else
    C * (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(2 * Real.pi * Y) * n.natAbs)
  unfold EstarExt
  apply GaloisForLFunctions.HTGeometry.differentiableAt_tsum_of_cauchy_dominated hr (bound := bound)
  · intro n s hs
    obtain ⟨_, h1, h2⟩ := hbW hs
    apply DifferentiableAt.differentiableWithinAt
    unfold termX
    by_cases hn : n = 0
    · simp only [if_pos hn]; exact differentiableAt_const _
    simp only [if_neg hn]
    exact ((((differentiable_exp_neg_mul _).differentiableAt).mul
      (differentiableAt_kerBessel hY (by exact_mod_cast hn) s)).mul_const _).mul (differentiableAt_Dn N σ n h1 h2)
  · intro n s hs
    obtain ⟨h1, h2, h3⟩ := ball_props hs
    obtain ⟨hs0, _, _⟩ := hbW hs
    have hsc : s ∈ closedBall s₀ r := ball_subset_closedBall hs
    by_cases hn : n = 0
    · simp [termX, bound, hn]
    simp only [termX, bound, if_neg hn]
    have hEN : ‖cexp (-s * (Real.log N : ℂ))‖ ≤ 1 := by
      have := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 hs0.le
      rwa [neg_zero, Real.rpow_zero] at this
    have hex : ‖cexp (2 * Real.pi * Complex.I * n * z.re / N)‖ = 1 := norm_cexp_two_pi_I_div _ _ _
    have hK : ‖kerBessel Y s n‖ ≤ (Y ^ σ₁ + Y ^ σ₂) * B1 * (((Y ^ lo)⁻¹ + (Y ^ hi)⁻¹) * (n.natAbs : ℝ) ^ k) *
        (Real.exp (-(2 * Real.pi * Y * |(n : ℝ)|)) * E0) := by
      unfold kerBessel
      rw [norm_mul, norm_mul, norm_mul]
      have e1 : ‖((Y : ℝ) : ℂ) ^ s‖ ≤ Y ^ σ₁ + Y ^ σ₂ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]; exact rpow_le_add hY h1 h2
      have e2 : ‖2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹‖ ≤ B1 := hB1 s hsc
      have hx : 0 < |((n : ℤ) : ℝ)| / Y := div_pos (abs_pos.mpr (by exact_mod_cast hn)) hY
      have e3 : ‖(((|((n : ℤ) : ℝ)| / Y : ℝ)) : ℂ) ^ (s - 1 / 2)‖ ≤ ((Y ^ lo)⁻¹ + (Y ^ hi)⁻¹) * (n.natAbs : ℝ) ^ k := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
        rw [hre]
        exact rpow_natAbs_div_le hY hn (by simp only [lo]; linarith) (by simp only [hi]; linarith) hlo hhi
      have e4 := norm_bessel_le hY hn (ν := s - 1 / 2) (R := R) (by
        calc ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖s₀‖ + r + 1 / 2 := by
            have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
            linarith)
      gcongr
    have hD : ‖Dn N σ n s‖ ≤ B2 * (2 * (n.natAbs : ℝ) ^ 2) :=
      (norm_Dn_le_sq N σ n hs0.le).trans (mul_le_mul_of_nonneg_right (hB2' s hsc) (by positivity))
    rw [norm_mul, norm_mul, norm_mul, hex, mul_one]
    have habs : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by simp [Nat.cast_natAbs]
    calc ‖cexp (-s * (Real.log N : ℂ))‖ * ‖kerBessel Y s n‖ * ‖Dn N σ n s‖
        ≤ 1 * ((Y ^ σ₁ + Y ^ σ₂) * B1 * (((Y ^ lo)⁻¹ + (Y ^ hi)⁻¹) * (n.natAbs : ℝ) ^ k) *
            (Real.exp (-(2 * Real.pi * Y * |(n : ℝ)|)) * E0)) * (B2 * (2 * (n.natAbs : ℝ) ^ 2)) := by
          gcongr
      _ = C * (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(2 * Real.pi * Y) * n.natAbs) := by
          rw [habs]; simp only [C]; rw [pow_add]; ring_nf
  · have hbase := (Real.summable_pow_mul_exp_neg_nat_mul (k + 2) (r := 2 * Real.pi * Y) (by positivity)).mul_left C
    refine Summable.of_nat_of_neg ?_ ?_
    · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hbase
      · simp only [bound]; split_ifs <;> positivity
      · simp only [bound]
        split_ifs
        · positivity
        · simp only [Int.natAbs_natCast]; ring_nf; exact le_rfl
    · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hbase
      · simp only [bound]; split_ifs <;> positivity
      · simp only [bound]
        split_ifs
        · positivity
        · simp only [Int.natAbs_neg, Int.natAbs_natCast]; ring_nf; exact le_rfl

end GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine
