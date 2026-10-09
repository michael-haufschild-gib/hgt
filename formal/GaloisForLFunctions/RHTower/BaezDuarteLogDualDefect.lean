import GaloisForLFunctions.RHTower.ZetaSmoothedPartialSumsDisc
import GaloisForLFunctions.RHTower.BaezDuarteSmoothZeroDual

/-!
# Defects of log-weighted zero duals at a multiple zero

Let `a_ρ(k) = k^{−ρ}ψ(k/Y)` be the smoothed zero dual and `a_{ρ,j}(k) = (−log k)^j a_ρ(k)` its
`j`-th derivative in `ρ`.  If `ζ^{(i)}(ρ₀) = 0` for `i < m₀`, then for every `j < m₀` and `A > 0`
the divisor defects of `a_{ρ₀,j}` are `O(m^A Y^{−A})` (`exists_norm_bdModDefect_logZeroSmoothDual_le`).

**Proof.**  For fixed `Y, K, m` the defect `D(ρ)` of `a_ρ` is a finite exponential sum in `ρ`, and its
`j`-th derivative at `ρ₀` is the defect of `a_{ρ₀,j}` (`iteratedDeriv_sum_cpow_neg`).  Uniformly on a
disc around `ρ₀` (`exists_norm_tsum_smooth1_cpow_sub_le_disc`),
`D(ρ) = ζ(ρ)(m^{−ρ}ψ(m/Y) − ψ(1/Y)/m) + R(ρ)` with `|R(ρ)| ≤ 2Cm^AY^{−A}`, since the main terms
`m^{−ρ}c(ρ)(Y/m)^{1−ρ}` and `c(ρ)Y^{1−ρ}/m` coincide.  The first term has vanishing derivatives of
order `< m₀` at `ρ₀` (Leibniz), and Cauchy's estimate bounds the derivatives of `R`.
-/

open Complex Set Filter Topology Metric

namespace RHTower

noncomputable section

/-- The log-weighted zero dual `a_{ρ,j}(k) = (−log k)^j k^{−ρ} ψ(k/Y)`. -/
def logZeroSmoothDual (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) (j k : ℕ) : ℂ :=
  (-(Real.log k : ℂ)) ^ j * zeroSmoothDual ν ε ρ Y k

theorem hasDerivAt_natCast_cpow_neg {k : ℕ} (hk : 1 ≤ k) (ρ : ℂ) :
    HasDerivAt (fun ρ : ℂ => (k : ℂ) ^ (-ρ)) (-(Real.log k : ℂ) * (k : ℂ) ^ (-ρ)) ρ := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h := (hasDerivAt_neg ρ).const_cpow (c := (k : ℂ)) (Or.inl hk0)
  rw [Complex.natCast_log] at *
  convert h using 1
  · rw [← Complex.natCast_log]; ring

/-- `∂_ρ^j Σ_k w_k k^{−ρ} = Σ_k w_k (−log k)^j k^{−ρ}`. -/
theorem iteratedDeriv_sum_cpow_neg (s : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) (w : ℕ → ℂ) (j : ℕ) :
    iteratedDeriv j (fun ρ : ℂ => ∑ k ∈ s, w k * (k : ℂ) ^ (-ρ)) =
      fun ρ => ∑ k ∈ s, w k * (-(Real.log k : ℂ)) ^ j * (k : ℂ) ^ (-ρ) := by
  induction j with
  | zero => funext ρ; simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext ρ
    refine HasDerivAt.deriv ?_
    have h := HasDerivAt.fun_sum (u := s) (A := fun k ρ => w k * (-(Real.log k : ℂ)) ^ j *
      (k : ℂ) ^ (-ρ)) (A' := fun k => w k * (-(Real.log k : ℂ)) ^ j *
      (-(Real.log k : ℂ) * (k : ℂ) ^ (-ρ))) (x := ρ)
      (fun k hk => (hasDerivAt_natCast_cpow_neg (hs k hk) ρ).const_mul _)
    convert h using 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- The defect of the smoothed zero dual as an exponential sum in `ρ`. -/
theorem bdModDefect_zeroSmoothDual_eq_sum (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) (K m : ℕ) :
    bdModDefect (zeroSmoothDual ν ε ρ Y) K m =
      ∑ k ∈ Finset.Icc 1 K, (((if m ∣ k then 1 else 0) - 1 / (m : ℂ)) *
        (Smooth1 ν ε (k / Y) : ℂ)) * (k : ℂ) ^ (-ρ) := by
  unfold bdModDefect
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp only [zeroSmoothDual, zeroCoeff, if_neg hk1]
  split_ifs <;> ring

theorem bdModDefect_logZeroSmoothDual_eq_sum (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) (j K m : ℕ) :
    bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m =
      ∑ k ∈ Finset.Icc 1 K, (((if m ∣ k then 1 else 0) - 1 / (m : ℂ)) *
        (Smooth1 ν ε (k / Y) : ℂ)) * (-(Real.log k : ℂ)) ^ j * (k : ℂ) ^ (-ρ) := by
  unfold bdModDefect
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp only [logZeroSmoothDual, zeroSmoothDual, zeroCoeff, if_neg hk1]
  split_ifs <;> ring

/-- **The derivative identity.**  The defect of `a_{ρ,j}` is the `j`-th `ρ`-derivative of the
defect of `a_ρ`. -/
theorem iteratedDeriv_bdModDefect_zeroSmoothDual (ν : ℝ → ℝ) (ε : ℝ) (Y : ℝ) (j K m : ℕ)
    (ρ : ℂ) :
    iteratedDeriv j (fun ρ => bdModDefect (zeroSmoothDual ν ε ρ Y) K m) ρ =
      bdModDefect (logZeroSmoothDual ν ε ρ Y j) K m := by
  have e : (fun ρ => bdModDefect (zeroSmoothDual ν ε ρ Y) K m) = fun ρ =>
      ∑ k ∈ Finset.Icc 1 K, (((if m ∣ k then 1 else 0) - 1 / (m : ℂ)) *
        (Smooth1 ν ε (k / Y) : ℂ)) * (k : ℂ) ^ (-ρ) :=
    funext fun ρ => bdModDefect_zeroSmoothDual_eq_sum ν ε ρ Y K m
  rw [e, iteratedDeriv_sum_cpow_neg _ (fun k hk => (Finset.mem_Icc.mp hk).1),
    bdModDefect_logZeroSmoothDual_eq_sum]

theorem differentiable_bdModDefect_zeroSmoothDual (ν : ℝ → ℝ) (ε : ℝ) (Y : ℝ) (K m : ℕ) :
    Differentiable ℂ (fun ρ => bdModDefect (zeroSmoothDual ν ε ρ Y) K m) := by
  have e : (fun ρ => bdModDefect (zeroSmoothDual ν ε ρ Y) K m) = fun ρ =>
      ∑ k ∈ Finset.Icc 1 K, (((if m ∣ k then 1 else 0) - 1 / (m : ℂ)) *
        (Smooth1 ν ε (k / Y) : ℂ)) * (k : ℂ) ^ (-ρ) :=
    funext fun ρ => bdModDefect_zeroSmoothDual_eq_sum ν ε ρ Y K m
  rw [e]
  intro ρ
  exact (HasDerivAt.fun_sum (u := Finset.Icc 1 K) fun k hk =>
    (hasDerivAt_natCast_cpow_neg (Finset.mem_Icc.mp hk).1 ρ).const_mul _).differentiableAt

/-- **Defects of the log-weighted duals at a zero of order `≥ m₀`.** -/
theorem exists_norm_bdModDefect_logZeroSmoothDual_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {ρ₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ ρ ∈ closedBall ρ₀ r, 0 < ρ.re ∧ ρ.re < 1) {m₀ : ℕ}
    (hζ : ∀ i < m₀, iteratedDeriv i riemannZeta ρ₀ = 0) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j < m₀, ∀ Y : ℝ, 0 < Y → ∀ K : ℕ, 3 * Y ≤ K → ∀ m : ℕ, 1 ≤ m →
      ‖bdModDefect (logZeroSmoothDual ν ε ρ₀ Y j) K m‖ ≤
        C * (m : ℝ) ^ A * Y ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_tsum_smooth1_cpow_sub_le_disc hν νpos mass_one hε0 hε1 hball hA
  refine ⟨(m₀.factorial : ℝ) * (2 * C) * (1 + 1 / r) ^ m₀, by positivity,
    fun j hj Y hY K hYK m hm => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hYm : 0 < Y / m := div_pos hY hm0
  set D : ℂ → ℂ := fun ρ => bdModDefect (zeroSmoothDual ν ε ρ Y) K m with hD
  set g : ℂ → ℂ := fun ρ => (m : ℂ) ^ (-ρ) * (Smooth1 ν ε (m / Y) : ℂ) -
    (Smooth1 ν ε (1 / Y) : ℂ) / m with hg
  set T : ℂ → ℂ := riemannZeta * g with hT
  set R : ℂ → ℂ := D - T with hR
  have hne1 : ∀ ρ ∈ closedBall ρ₀ r, ρ ≠ 1 := fun ρ hρ h => by
    have := (hball ρ hρ).2; rw [h] at this; simp at this
  have hζd : DifferentiableOn ℂ riemannZeta (closedBall ρ₀ r) := fun ρ hρ =>
    (differentiableAt_riemannZeta (hne1 ρ hρ)).differentiableWithinAt
  have hgd : Differentiable ℂ g := by
    intro ρ
    have hk0 : (m : ℂ) ≠ 0 := hmC
    exact ((((hasDerivAt_neg ρ).const_cpow (c := (m : ℂ)) (Or.inl hk0)).differentiableAt).mul_const
      _).sub_const _
  have hDd : Differentiable ℂ D := differentiable_bdModDefect_zeroSmoothDual ν ε Y K m
  have hRd : DifferentiableOn ℂ R (closedBall ρ₀ r) :=
    hDd.differentiableOn.sub (hζd.mul hgd.differentiableOn)
  -- the remainder is small on the disc
  set B : ℝ := 2 * C * (m : ℝ) ^ A * Y ^ (-A) with hBdef
  have hRb : ∀ z ∈ closedBall ρ₀ r, ‖R z‖ ≤ B := by
    intro z hzb
    obtain ⟨hz0, hz1⟩ := hball z hzb
    set Φ : ℝ → ℂ := fun X => ∑' n, zeroCoeff z n * (Smooth1 ν ε (n / X) : ℂ) with hΦ
    set c : ℂ := (1 - z)⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * (1 - z)) with hc
    have hΦE : ∀ X : ℝ, 0 < X → ‖Φ X - riemannZeta z * (Smooth1 ν ε (1 / X) : ℂ) -
        c * (X : ℂ) ^ (1 - z)‖ ≤ C * X ^ (-A) := fun X hX => hC z hzb X hX
    have hall : ∑ k ∈ Finset.Icc 1 K, zeroSmoothDual ν ε z Y k = Φ Y :=
      (tsum_zeroSmoothDual_eq_sum hν hε0 hε1 z hY hYK).symm
    have hdef : D z = (m : ℂ) ^ (-z) * Φ (Y / m) - Φ Y / m := by
      simp only [hD]
      unfold bdModDefect
      rw [sum_filter_dvd_zeroSmoothDual hν hε0 hε1 z hY hYK hm, hall]
      simp only [hΦ, zeroSmoothDual]
      ring
    have hmain : (m : ℂ) ^ (-z) * (c * (((Y / m : ℝ)) : ℂ) ^ (1 - z)) -
        c * (Y : ℂ) ^ (1 - z) / m = 0 := by
      have hsplit : ((Y : ℝ) : ℂ) ^ (1 - z) =
          (((Y / m : ℝ)) : ℂ) ^ (1 - z) * ((m : ℝ) : ℂ) ^ (1 - z) := by
        rw [← Complex.mul_cpow_ofReal_nonneg hYm.le hm0.le]
        congr 1
        push_cast
        field_simp
      have hm1 : ((m : ℝ) : ℂ) ^ (1 - z) = (m : ℂ) * (m : ℂ) ^ (-z) := by
        rw [Complex.ofReal_natCast, sub_eq_add_neg, Complex.cpow_add _ _ hmC, Complex.cpow_one]
      rw [hsplit, hm1]
      field_simp
      ring
    have h1Y : (1 : ℝ) / (Y / m) = m / Y := by field_simp
    have hRz : R z = (m : ℂ) ^ (-z) * (Φ (Y / m) - riemannZeta z *
        (Smooth1 ν ε (1 / (Y / m)) : ℂ) - c * (((Y / m : ℝ)) : ℂ) ^ (1 - z)) -
        (Φ Y - riemannZeta z * (Smooth1 ν ε (1 / Y) : ℂ) - c * (Y : ℂ) ^ (1 - z)) / m := by
      simp only [hR, hT, hg, Pi.sub_apply, Pi.mul_apply]
      rw [hdef, h1Y]
      linear_combination hmain
    rw [hRz]
    have hnm : ‖(m : ℂ) ^ (-z)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by linarith)
    have hE1 := hΦE (Y / m) hYm
    have hE2 := hΦE Y hY
    have hYmA : (Y / m) ^ (-A) = (m : ℝ) ^ A * Y ^ (-A) := by
      rw [Real.div_rpow hY.le hm0.le, Real.rpow_neg hm0.le, div_inv_eq_mul, mul_comm]
    have hmA : 1 ≤ (m : ℝ) ^ A := Real.one_le_rpow (by exact_mod_cast hm) hA.le
    have hYA : 0 ≤ Y ^ (-A) := Real.rpow_nonneg hY.le _
    calc ‖(m : ℂ) ^ (-z) * (Φ (Y / m) - riemannZeta z * (Smooth1 ν ε (1 / (Y / m)) : ℂ) -
          c * (((Y / m : ℝ)) : ℂ) ^ (1 - z)) -
          (Φ Y - riemannZeta z * (Smooth1 ν ε (1 / Y) : ℂ) - c * (Y : ℂ) ^ (1 - z)) / m‖
        ≤ ‖(m : ℂ) ^ (-z)‖ * ‖Φ (Y / m) - riemannZeta z * (Smooth1 ν ε (1 / (Y / m)) : ℂ) -
            c * (((Y / m : ℝ)) : ℂ) ^ (1 - z)‖ +
          ‖Φ Y - riemannZeta z * (Smooth1 ν ε (1 / Y) : ℂ) - c * (Y : ℂ) ^ (1 - z)‖ / m := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_div, Complex.norm_natCast]
      _ ≤ 1 * (C * ((m : ℝ) ^ A * Y ^ (-A))) + C * Y ^ (-A) / 1 := by
          gcongr
          · rw [← hYmA]; exact hE1
          · exact_mod_cast hm
      _ ≤ B := by
          have : C * Y ^ (-A) ≤ C * ((m : ℝ) ^ A * Y ^ (-A)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            nlinarith
          rw [hBdef]
          nlinarith
  -- Cauchy's estimate
  have hcl : closure (ball ρ₀ r) = closedBall ρ₀ r := closure_ball ρ₀ hr.ne'
  have hRcl : DiffContOnCl ℂ R (ball ρ₀ r) := DifferentiableOn.diffContOnCl (hcl ▸ hRd)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr hRcl
    (fun z hz => hRb z (sphere_subset_closedBall hz))
  -- the derivatives of `T` vanish
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hρ₀mem : ρ₀ ∈ {s : ℂ | s ≠ 1} := hne1 ρ₀ (mem_closedBall_self hr.le)
  have hζca : ContDiffAt ℂ j riemannZeta ρ₀ := by
    have hdo : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
      (differentiableAt_riemannZeta hs).differentiableWithinAt
    have : ContDiffOn ℂ j riemannZeta {s : ℂ | s ≠ 1} := hdo.contDiffOn hopen
    exact this.contDiffAt (hopen.mem_nhds hρ₀mem)
  have hgca : ContDiffAt ℂ j g ρ₀ := hgd.contDiff.contDiffAt
  have hTca : ContDiffAt ℂ j T ρ₀ := hζca.mul hgca
  have hDca : ContDiffAt ℂ j D ρ₀ := hDd.contDiff.contDiffAt
  have hT0 : iteratedDeriv j T ρ₀ = 0 := by
    rw [hT, iteratedDeriv_mul hζca hgca]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hij : i < m₀ := by have := Finset.mem_range.mp hi; omega
    rw [hζ i hij]
    ring
  have hDR : iteratedDeriv j D ρ₀ = iteratedDeriv j R ρ₀ := by
    rw [hR, iteratedDeriv_sub hDca hTca, hT0, sub_zero]
  rw [← iteratedDeriv_bdModDefect_zeroSmoothDual, ← hD, hDR]
  refine hcauchy.trans ?_
  -- `j!/r^j ≤ m₀!(1 + 1/r)^{m₀}`
  have hfac : (j.factorial : ℝ) ≤ m₀.factorial := by
    exact_mod_cast Nat.factorial_le hj.le
  have hr1 : (1 : ℝ) ≤ 1 + 1 / r := le_add_of_nonneg_right (by positivity)
  have hpow : 1 / r ^ j ≤ (1 + 1 / r) ^ m₀ := by
    calc 1 / r ^ j = (1 / r) ^ j := by rw [one_div_pow]
      _ ≤ (1 + 1 / r) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
      _ ≤ (1 + 1 / r) ^ m₀ := pow_le_pow_right₀ hr1 hj.le
  have hB0 : 0 ≤ B := by positivity
  calc (j.factorial : ℝ) * B / r ^ j = (j.factorial : ℝ) * B * (1 / r ^ j) := by ring
    _ ≤ (m₀.factorial : ℝ) * B * (1 + 1 / r) ^ m₀ := by
        gcongr
    _ = (m₀.factorial : ℝ) * (2 * C) * (1 + 1 / r) ^ m₀ * (m : ℝ) ^ A * Y ^ (-A) := by
        rw [hBdef]; ring

end

end RHTower
