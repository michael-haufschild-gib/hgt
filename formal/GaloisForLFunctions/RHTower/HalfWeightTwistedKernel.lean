import GaloisForLFunctions.RHTower.HalfWeightTwistedRankinSelberg
import GaloisForLFunctions.RHTower.HalfWeightForcedZero
import GaloisForLFunctions.RHTower.HalfWeightTwistedTheta

/-!
# The twisted Shimura kernel `G_χ(z) = f(4z) \overline{θ_χ(z)} y^{1/4}`

For a Maass cusp form `f` on `Γ₀(N+1)` with `λ = 1/4 - τ²` and a character `χ` of prime conductor `q`:

* `norm_thetaTw_le`: `‖θ_χ(v)‖ ≤ q (1 + 1/(π Im v))`.
* **`Gtw_smul`**: `G_χ(γz) = \overline{ψ(d)} \overline{j(γ,z)} G_χ(z)` on `Γ₀(4(N+1)q²)` with `ψ = χ²`
  lifted to that level (`thetaTw_smul`, `f_four_smul`, `|J|² = |cz+d|`).
* `continuous_Gtw`, **`Gtw_hdec`** (rapid decay of all translates on `𝒟`), `integrableOn_Gtw_strip`
  (`Re w > 7/4`).
* `hasSum_integral_U_conj_theta_shift'`: `∫_0^1 U(4z) \overline{θ(z+t)} dx = Σ_j e(-4j²t) e^{-8πj²y} c(j²)`.
* **`hasSum_zeroth_tw`**: `∫_0^1 f(4z) \overline{θ_χ(z)} dx = Σ_j \overline{g_χ(4j²)} e^{-8πj²y} ρ_{j²}
  W_τ(8πj²y)`, since `Σ_a χ(a) e(-4j²a/q) = \overline{g_χ(4j²)}`.
* **`strip_integral_Gtw`**: `∫_{strip} G_χ y^w dμ = (Σ_j \overline{g_χ(4j²)} ρ_{j²}(8πj²)^{3/4-w})
  Mel_τ(w - 1/4)` for `Re w > 7/4`.
-/

open Real Complex Filter Topology MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-! ### The twisted theta series: size and the lifted character -/

section Aux

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
theorem im_add_div_nat {v : ℂ} (a : ℕ) : (v + (a : ℂ) / q).im = v.im := by
  have : ((a : ℂ) / q).im = 0 := by
    rw [show (a : ℂ) / q = (((a : ℝ) / q : ℝ) : ℂ) by push_cast; ring]; exact Complex.ofReal_im _
  rw [Complex.add_im, this, add_zero]

/-- `‖θ_χ(v)‖ ≤ q (1 + 1/(π Im v))`. -/
theorem norm_thetaTw_le {v : ℂ} (hv : 0 < v.im) : ‖thetaTw χ v‖ ≤ q * (1 + 1 / (π * v.im)) := by
  unfold thetaTw
  calc ‖∑ a : ZMod q, starRingEnd ℂ (χ a) * theta (v + ((a.val : ℕ) : ℂ) / q)‖
      ≤ ∑ a : ZMod q, ‖starRingEnd ℂ (χ a) * theta (v + ((a.val : ℕ) : ℂ) / q)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, (1 + 1 / (π * v.im)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, Complex.norm_conj]
        have hθ := norm_theta_le (v := v + ((a.val : ℕ) : ℂ) / q) (by rw [im_add_div_nat]; exact hv)
        rw [im_add_div_nat] at hθ
        exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans hθ
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

end Aux

theorem psiL_intCast {q : ℕ} [Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q) (M' : ℕ) {d : ℤ}
    (hd : IsCoprime d (4 * (M' * q ^ 2) : ℕ)) :
    psiL ψ₀ M' ((d : ℤ) : ZMod (4 * (M' * q ^ 2))) = ψ₀ ((d : ℤ) : ZMod q) := by
  have hu : IsUnit ((d : ℤ) : ZMod (4 * (M' * q ^ 2))) := by
    obtain ⟨u', v', huv⟩ := hd
    have h1 : ((d : ℤ) : ZMod (4 * (M' * q ^ 2))) * ((u' : ℤ) : ZMod (4 * (M' * q ^ 2))) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod (4 * (M' * q ^ 2))) huv
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        add_zero, Int.cast_one] at this
      exact (mul_comm _ _).trans this
    exact IsUnit.of_mul_eq_one _ h1
  obtain ⟨u, hu⟩ := hu
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ (q_dvd_level M') u
  rw [psiL, ← hu, h, hu, ZMod.cast_intCast (q_dvd_level M')]

/-! ### The zeroth coefficient against a translated theta -/

section Phase

open SelbergMaassFourier SelbergMaassMean

theorem conj_theta_shift_hasSum {x y : ℝ} (t : ℝ) (hy : 0 < y) :
    HasSum (fun m : ℤ => cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * t)) *
      (((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * x))))
      (starRingEnd ℂ (theta (point (x + t) y))) := by
  refine (conj_theta_hasSum (x := x + t) hy).congr_fun fun m => ?_
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **The zeroth coefficient against `θ(z + t)`**: for bounded continuous `1`-periodic `U`,
`∫_0^1 U(4z) \overline{θ(z+t)} dx = Σ_m e(-m²t) e^{-2πm²y} c₄(m²; 4y)`. -/
theorem hasSum_integral_U_conj_theta_shift {U : ℂ → ℂ} {y : ℝ} (hy : 0 < y) (t : ℝ) {B : ℝ}
    (hB : ∀ x : ℝ, ‖U (point x (4 * y))‖ ≤ B) (hc : Continuous fun x : ℝ => U (point x (4 * y))) :
    HasSum (fun m : ℤ => cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * t)) *
      (((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * coefficient 4 (m ^ 2) U (4 * y)))
      (∫ x in (0 : ℝ)..1, U (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point (x + t) y))) := by
  set F : ℤ → ℝ → ℂ := fun m x => U (point (4 * x) (4 * y)) *
    (cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * t)) *
      (((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * x))))
  have hc4 : Continuous fun x : ℝ => U (point (4 * x) (4 * y)) := hc.comp (continuous_const.mul continuous_id)
  have hsumE : Summable fun m : ℤ => B * Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) := by
    have hz : 0 < (point 0 y).im := by simpa [point] using hy
    have := (summable_theta_terms hz).norm.mul_left B
    refine this.congr fun m => ?_
    rw [Complex.norm_exp]
    congr 2
    rw [show ((m : ℂ) ^ 2) = (((m : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]
    simp only [point, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hphase : ∀ (m : ℤ) (u : ℝ), ‖cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * u))‖ = 1 := by
    intro m u
    rw [Complex.norm_exp]
    have him : ((m : ℂ) ^ 2).im = 0 := by rw [← Int.cast_pow, Complex.intCast_im]
    have hre : ((m : ℂ) ^ 2).re = (m : ℝ) ^ 2 := by
      rw [← Int.cast_pow, Complex.intCast_re]; push_cast; ring
    simp [Complex.mul_re, Complex.mul_im, him, hre]
  have hmain := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := 1)
    (F := F) (f := fun x => U (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point (x + t) y)))
    (fun m x => B * Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)))
    (fun m => (hc4.mul (by fun_prop)).aestronglyMeasurable)
    (fun m => Eventually.of_forall fun x _ => by
      simp only [F]
      rw [norm_mul, norm_mul, norm_mul, hphase, hphase, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), one_mul, mul_one]
      exact mul_le_mul_of_nonneg_right (hB (4 * x)) (Real.exp_pos _).le)
    (Eventually.of_forall fun x _ => hsumE)
    intervalIntegrable_const
    (Eventually.of_forall fun x _ => (conj_theta_shift_hasSum t hy).mul_left _)
  refine hmain.congr_fun fun m => ?_
  simp only [F]
  rw [← integral_eq_coefficient_four, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1; funext x; ring

theorem hasSum_integral_U_conj_theta_shift' {U : ℂ → ℂ} {y : ℝ} (hy : 0 < y) (t : ℝ) {B : ℝ}
    (hB : ∀ x : ℝ, ‖U (point x (4 * y))‖ ≤ B) (hc : Continuous fun x : ℝ => U (point x (4 * y)))
    (hper : ∀ x : ℝ, U (point (x + 1) (4 * y)) = U (point x (4 * y))) :
    HasSum (fun j : ℤ => cexp (-(2 * π * Complex.I * ((4 * j ^ 2 : ℤ) : ℂ) * t)) *
      (((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) * coefficient 1 (j ^ 2) U (4 * y)))
      (∫ x in (0 : ℝ)..1, U (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point (x + t) y))) := by
  have h := hasSum_integral_U_conj_theta_shift hy t hB hc
  set f : ℤ → ℂ := fun m => cexp (-(2 * π * Complex.I * (m : ℂ) ^ 2 * t)) *
    (((Real.exp (-(2 * π * (m : ℝ) ^ 2 * y)) : ℝ) : ℂ) * coefficient 4 (m ^ 2) U (4 * y))
  have hinj : Function.Injective (fun j : ℤ => 2 * j) := fun a b hab => by simpa using hab
  have h4 : ∀ n : ℤ, coefficient 4 n U (4 * y) = if (4 : ℤ) ∣ n then coefficient 1 (n / 4) U (4 * y) else 0 := by
    intro n
    have := coefficient_periodic 4 (by norm_num) n hc hper
    simpa using this
  have hzero : ∀ m ∉ Set.range (fun j : ℤ => 2 * j), f m = 0 := by
    intro m hm
    have hnd : ¬ (4 : ℤ) ∣ m ^ 2 := by
      rw [four_dvd_sq_iff]; rintro ⟨j, rfl⟩; exact hm ⟨j, rfl⟩
    simp only [f]
    rw [h4, if_neg hnd, mul_zero, mul_zero]
  rw [← hinj.hasSum_iff hzero] at h
  refine h.congr_fun fun j => ?_
  simp only [Function.comp, f]
  have hd : (4 : ℤ) ∣ (2 * j) ^ 2 := ⟨j ^ 2, by ring⟩
  rw [h4, if_pos hd]
  rw [show (2 * j) ^ 2 / 4 = j ^ 2 by rw [show (2 * j) ^ 2 = 4 * j ^ 2 by ring]; exact Int.mul_ediv_cancel_left _ (by norm_num)]
  congr 3
  · push_cast; ring
  · push_cast; ring_nf

end Phase

/-! ### The twisted Shimura kernel -/

section Kernel

variable (N : ℕ) {τ : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ)))
  {q : ℕ} [hq : Fact q.Prime] (χ : DirichletCharacter ℂ q)

/-- `G_χ(z) = f(4z) \overline{θ_χ(z)} y^{1/4}`. -/
def Gtw (z : ℍ) : ℂ :=
  (f.1.1 ∘ ofComplex) (4 * (z : ℂ)) * starRingEnd ℂ (thetaTw χ z) * ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ)

omit hq in
theorem Gamma0_level_le : CongruenceSubgroup.Gamma0 (4 * ((N + 1) * q ^ 2)) ≤
    CongruenceSubgroup.Gamma0 (4 * (N + 1)) := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  have h : ((4 * ((N + 1) * q ^ 2) : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_trans (by push_cast; exact ⟨q ^ 2, by ring⟩) h

/-- **Transformation law**: `G_χ(γz) = \overline{ψ(d)} \overline{j(γ,z)} G_χ(z)` on `Γ₀(4(N+1)q²)`,
with `ψ = χ²` lifted to that level. -/
theorem Gtw_smul (hq2 : q ≠ 2) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * ((N + 1) * q ^ 2))) (z : ℍ) :
    Gtw N f χ (γ • z) = starRingEnd ℂ (psiL (χ ^ 2) (N + 1) (ent γ 1 1 : ZMod (4 * ((N + 1) * q ^ 2)))) *
      starRingEnd ℂ (jU γ z) * Gtw N f χ z := by
  have hodd : Odd q := hq.out.odd_of_ne_two hq2
  have hc : ((4 * ((N + 1) * q ^ 2) : ℕ) : ℤ) ∣ ent γ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  have hθc : ((4 * q ^ 2 : ℕ) : ℤ) ∣ ent γ 1 0 := dvd_trans (by push_cast; exact ⟨N + 1, by ring⟩) hc
  have hγ4 : γ ∈ CongruenceSubgroup.Gamma0 4 := by
    rw [CongruenceSubgroup.Gamma0_mem]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact ⟨(N + 1) * q ^ 2, by ring⟩) hc
  have hJ := norm_sq_J hγ4 z
  have hJpos : 0 < ‖J γ z‖ := norm_pos_iff.2 (J_ne_zero γ z)
  have hy := z.im_pos
  have him : (γ • z).im = z.im / ‖J γ z‖ ^ 4 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ← hJ]; ring
  have hpow : (γ • z).im ^ (1 / 4 : ℝ) = z.im ^ (1 / 4 : ℝ) / ‖J γ z‖ := by
    rw [him, Real.div_rpow hy.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hJpos.le]
    norm_num
  have hd : IsCoprime (ent γ 1 1) ((4 * ((N + 1) * q ^ 2) : ℕ) : ℤ) := by
    obtain ⟨t, ht⟩ := hc
    have hdet := det_entries γ
    exact ⟨ent γ 0 0, -(ent γ 0 1 * t), by rw [ht] at hdet; linear_combination hdet⟩
  have hψ : psiL (χ ^ 2) (N + 1) (ent γ 1 1 : ZMod (4 * ((N + 1) * q ^ 2))) =
      χ ((ent γ 1 1 : ℤ) : ZMod q) ^ 2 := by
    rw [psiL_intCast (χ ^ 2) (N + 1) hd, MulChar.pow_apply' _ two_ne_zero]
  unfold Gtw
  rw [f_four_smul N f (Gamma0_level_le N hγ) z, thetaTw_smul hodd hθc, hpow, hψ, jU, map_mul, map_mul,
    map_div₀, Complex.conj_ofReal]
  push_cast
  have hJ0 : ((‖J γ z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hJpos.ne'
  field_simp

theorem continuous_Gtw : Continuous (Gtw N f χ) := by
  have hF : ContinuousOn (f.1.1 ∘ ofComplex) {w : ℂ | 0 < w.im} := f.2.2.1.1.continuousOn
  have h4 : Continuous fun z : ℍ => (f.1.1 ∘ ofComplex) (4 * (z : ℂ)) :=
    hF.comp_continuous (continuous_const.mul UpperHalfPlane.continuous_coe)
      (fun z => by simp; exact z.im_pos)
  have hθ : Continuous fun z : ℍ => thetaTw χ z :=
    continuous_iff_continuousAt.2 fun z =>
      ((differentiableAt_thetaTw χ z.im_pos).continuousAt).comp UpperHalfPlane.continuous_coe.continuousAt
  have hy : Continuous fun z : ℍ => ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.rpow_const fun z => Or.inl z.im_pos.ne')
  unfold Gtw
  exact (h4.mul (Complex.continuous_conj.comp hθ)).mul hy

variable {N f} in
/-- **Rapid decay of the translates of `G_χ` on `𝒟`**. -/
theorem Gtw_hdec (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (B : ℝ) (A : SL(2, ℤ)) :
    IntegrableOn (fun w : ℍ => ‖Gtw N f χ (A • w)‖ * ((A • w).im ^ B + (A • w).im ^ (-B)))
      ModularGroup.fd := by
  obtain ⟨E, hE1, hE⟩ := im_smul_two_sided A
  obtain ⟨C, c, t₀, hC0, hc, ht₀, hdecay⟩ := f_four_decay (f := f) hτ0 hτ1 A
  obtain ⟨Bf, hBf⟩ := gz_bounded f
  set K : ℝ := max C (max Bf 0 * Real.exp (c * t₀))
  have hK0 : 0 ≤ K := le_max_of_le_left hC0
  set m : ℝ := |B| + 2
  have hm : 1 < m := by simp only [m]; linarith [abs_nonneg B]
  have hmaj := (SelbergMaassExpDecayCell.maj_integrableOn_fd (σ := m) hm hc).norm.const_mul
    (4 * q * K * (20 * E) ^ m)
  refine hmaj.mono' ?_ (ae_restrict_of_forall_mem ModularGroup.isClosed_fd.measurableSet fun w hw => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hs : Continuous fun w : ℍ => A • w := continuous_smul_sl A
    have him : Continuous fun w : ℍ => (A • w).im := UpperHalfPlane.continuous_im.comp hs
    exact ((continuous_Gtw N f χ).comp hs).norm.mul
      ((him.rpow_const fun w => Or.inl (A • w).im_pos.ne').add
        (him.rpow_const fun w => Or.inl (A • w).im_pos.ne'))
  set t := w.im
  have ht := w.im_pos
  have ht2 := SelbergMaassExpDecayCell.one_le_im_of_mem_fd hw
  set s := (A • w).im
  have hs := (A • w).im_pos
  obtain ⟨hs1, hs2⟩ := hE w hw
  set L : ℝ := 20 * E * t
  have hL1 : 1 ≤ L := by simp only [L]; nlinarith
  have hpow : s ^ B + s ^ (-B) ≤ 2 * L ^ |B| := by
    have := rpow_le_of_mem (B := B) hs hs1 hs2
    have := rpow_le_of_mem (B := -B) hs hs1 hs2
    rw [abs_neg] at this
    linarith
  have hθ : ‖thetaTw χ ((A • w : ℍ) : ℂ)‖ ≤ q * (2 * L) := by
    have h := norm_thetaTw_le χ (v := ((A • w : ℍ) : ℂ)) hs
    have h1 : 1 / (π * s) ≤ L := by
      have : 1 / (π * s) ≤ 1 / s := by
        apply one_div_le_one_div_of_le hs; nlinarith [Real.pi_gt_three]
      linarith
    have : ((A • w : ℍ) : ℂ).im = s := rfl
    rw [this] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    linarith
  have hy : s ^ (1 / 4 : ℝ) ≤ L := by
    calc s ^ (1 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hs.le hs1 (by norm_num)
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hf : ‖(f.1.1 ∘ ofComplex) (4 * ((A • w : ℍ) : ℂ))‖ ≤ K * Real.exp (-c * t) := by
    rcases le_or_gt t₀ t with h | h
    · exact (hdecay w h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · have h1 := hBf (ofComplex (4 * ((A • w : ℍ) : ℂ)))
      have h2 : Bf ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * t) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 1 ≤ Real.exp (c * t₀ + -c * t) := Real.one_le_exp (by nlinarith)
        nlinarith [le_max_left Bf 0, le_max_right Bf 0]
      calc _ ≤ Bf := h1
        _ ≤ max Bf 0 * Real.exp (c * t₀) * Real.exp (-c * t) := h2
        _ ≤ K * Real.exp (-c * t) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hG : ‖Gtw N f χ (A • w)‖ ≤ K * Real.exp (-c * t) * (q * (2 * L)) * L := by
    unfold Gtw
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul hf hθ (norm_nonneg _) (by positivity)) hy (by positivity) (by positivity)
  have hmajw : ‖SelbergPoincareIntegrability.maj m c w‖ = t ^ m * Real.exp (-c * t) := by
    unfold SelbergPoincareIntegrability.maj
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hmajw]
  have hLm : L ^ |B| * L * L = (20 * E) ^ m * t ^ m := by
    rw [← Real.mul_rpow (by positivity) ht.le]
    simp only [L, m]
    rw [Real.rpow_add (by positivity), Real.rpow_two]
    ring
  calc ‖Gtw N f χ (A • w)‖ * (s ^ B + s ^ (-B))
      ≤ (K * Real.exp (-c * t) * (q * (2 * L)) * L) * (2 * L ^ |B|) :=
        mul_le_mul hG hpow (by positivity) (by positivity)
    _ = 4 * q * K * (L ^ |B| * L * L) * Real.exp (-c * t) := by ring
    _ = 4 * q * K * (20 * E) ^ m * (t ^ m * Real.exp (-c * t)) := by rw [hLm]; ring

variable {N f} in
/-- **Integrability of `G_χ y^w` on the strip** for `Re w > 7/4`. -/
theorem integrableOn_Gtw_strip (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 7 / 4 < w.re) :
    IntegrableOn (fun z : ℍ => Gtw N f χ z * ((z.im : ℝ) : ℂ) ^ w)
      GaloisForLFunctions.HTGeometry.modularStrip := by
  obtain ⟨K, c, hK0, hc, hK⟩ := f_four_global (f := f) hτ0 hτ1
  have hA : MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := measurableSet_Ico.prod measurableSet_Ioi
  have hpos : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ), 0 < p.2 := fun p hp => hp.2
  rw [modularStrip_eq_coord,
    GaloisForLFunctions.HTGeometry.UpperHalfPlaneCoordIntegrable.integrableOn_coord_iff hA hpos]
  set g : ℝ → ℝ := fun y => K * q * (y ^ (w.re - 7 / 4) * Real.exp (-c * y ^ (1 : ℝ)) +
    1 / π * (y ^ (w.re - 11 / 4) * Real.exp (-c * y ^ (1 : ℝ))))
  have hg : IntegrableOn g (Ioi 0) := by
    have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 7 / 4) (b := c) (by linarith)
      le_rfl hc
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re - 11 / 4) (b := c) (by linarith)
      le_rfl hc
    exact (h1.add (h2.const_mul (1 / π))).const_mul (K * q)
  have hprod := (integrable_const (1 : ℝ) (μ := volume.restrict (Ico (0 : ℝ) 1))).mul_prod hg
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine Integrable.mono' hprod ?_ ?_
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_) hA
    have hp2 : 0 < p.2 := hp.2
    have hmk : ContinuousWithinAt (fun p : ℝ × ℝ => (ofComplex (⟨p.1, p.2⟩ : ℂ) : ℍ))
        (Ico (0 : ℝ) 1 ×ˢ Ioi 0) p := by
      have e : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
        funext p; apply Complex.ext <;> simp
      have hc1 : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) := by rw [e]; fun_prop
      have hc2 : ContinuousAt (ofComplex : ℂ → ℍ) (⟨p.1, p.2⟩ : ℂ) :=
        (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) (by simpa using hp2)).continuousAt
      exact (ContinuousAt.comp (x := p) (f := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
        (g := (ofComplex : ℂ → ℍ)) hc2 hc1.continuousAt).continuousWithinAt
    have hG := ((continuous_Gtw N f χ).continuousAt).comp_continuousWithinAt hmk
    have hy : ContinuousWithinAt (fun p : ℝ × ℝ => ((ofComplex (⟨p.1, p.2⟩ : ℂ) : ℍ).im : ℂ) ^ w)
        (Ico (0 : ℝ) 1 ×ˢ Ioi 0) p := by
      have := (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (UpperHalfPlane.continuous_im.continuousAt.comp_continuousWithinAt hmk))
      refine this.cpow continuousWithinAt_const ?_
      simp only [Function.comp]
      exact Complex.ofReal_mem_slitPlane.2 (ofComplex (⟨p.1, p.2⟩ : ℂ)).im_pos
    exact (hG.mul hy).div (by fun_prop) (by exact_mod_cast (pow_pos hp2 2).ne')
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem hA fun p hp => ?_
    have hp2 : 0 < p.2 := hp.2
    set z : ℍ := ofComplex (⟨p.1, p.2⟩ : ℂ)
    have hz : (z : ℂ) = ⟨p.1, p.2⟩ := ofComplex_mk hp2
    have hzim : z.im = p.2 := by simp [UpperHalfPlane.im, hz]
    simp only [one_mul]
    rw [norm_div, norm_mul, Gtw, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.norm_cpow_eq_rpow_re_of_pos z.im_pos,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp2, hzim]
    have hf := hK z
    rw [hzim] at hf
    have hθ := norm_thetaTw_le χ (v := (z : ℂ)) z.im_pos
    have hzim' : (z : ℂ).im = p.2 := by rw [hz]
    rw [hzim'] at hθ
    set y := p.2
    have hy14 : y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 = y ^ (w.re - 7 / 4) := by
      rw [← Real.rpow_add hp2, ← Real.rpow_natCast, ← Real.rpow_sub hp2]; congr 1; push_cast; ring
    have hy11 : y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 / y = y ^ (w.re - 11 / 4) := by
      rw [hy14, ← Real.rpow_sub_one hp2.ne']; congr 1; ring
    simp only [g, Real.rpow_one]
    calc ‖(f.1.1 ∘ ofComplex) (4 * (z : ℂ))‖ * ‖thetaTw χ z‖ * y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2
        ≤ K * Real.exp (-c * y) * (q * (1 + 1 / (π * y))) * y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 := by
          gcongr
      _ = K * q * (y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 * Real.exp (-c * y) +
            1 / π * (y ^ (1 / 4 : ℝ) * y ^ w.re / y ^ 2 / y * Real.exp (-c * y))) := by
          field_simp
      _ = _ := by rw [hy11, hy14]

/-! ### The zeroth coefficient of `G_χ` and the strip integral -/

open SelbergMaassFourier SelbergMaassMean

theorem norm_gTw_le (n : ℤ) : ‖gTw χ n‖ ≤ q := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  unfold gTw
  calc ‖∑ a : ZMod q, starRingEnd ℂ (χ a) * cexp (2 * π * Complex.I * ((a.val : ℕ) : ℂ) * n / q)‖
      ≤ ∑ a : ZMod q, ‖starRingEnd ℂ (χ a) * cexp (2 * π * Complex.I * ((a.val : ℕ) : ℂ) * n / q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, Complex.norm_conj]
        have he : ‖cexp (2 * π * Complex.I * ((a.val : ℕ) : ℂ) * n / q)‖ = 1 := by
          rw [show 2 * π * Complex.I * ((a.val : ℕ) : ℂ) * n / q =
            ((2 * π * ((a.val : ℝ) * n / q) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [he, mul_one]; exact DirichletCharacter.norm_le_one _ _
    _ = q := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

theorem sum_char_phase (n : ℤ) :
    haveI : NeZero q := ⟨hq.out.ne_zero⟩
    ∑ a : ZMod q, χ a * cexp (-(2 * π * Complex.I * ((n : ℤ) : ℂ) * (((a.val : ℕ) : ℝ) / q : ℝ))) =
      starRingEnd ℂ (gTw χ n) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  unfold gTw
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, Complex.conj_conj, ← Complex.exp_conj]
  congr 2
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_intCast]
  push_cast; ring

variable {N f} in
/-- The zeroth coefficient against `θ(z + t)` in Whittaker form. -/
theorem hasSum_zeroth_shift (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (t : ℝ) {y : ℝ} (hy : 0 < y) :
    HasSum (fun j : ℤ => cexp (-(2 * π * Complex.I * ((4 * j ^ 2 : ℤ) : ℂ) * t)) *
        (((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) *
          (rhoW f hτ0 hτ1 (j ^ 2) * Wh τ (8 * π * (j : ℝ) ^ 2 * y))))
      (∫ x in (0 : ℝ)..1, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
        starRingEnd ℂ (theta (point (x + t) y))) := by
  have hy4 : 0 < 4 * y := by linarith
  obtain ⟨C, hC⟩ := gz_bounded f
  have hB : ∀ x : ℝ, ‖(f.1.1 ∘ ofComplex) (point x (4 * y))‖ ≤ C := fun x => hC _
  have h := hasSum_integral_U_conj_theta_shift' hy t hB (gz_slice_continuous N f hy4)
    (fun x => gz_periodic N f x hy4)
  refine h.congr_fun fun j => ?_
  rw [bco_eq N f (j ^ 2) hy4, bco_eq_rhoW hτ0 hτ1 _ hy4, whModal]
  congr 4
  push_cast
  rw [abs_of_nonneg (sq_nonneg _)]
  ring

variable {N f} in
/-- **The zeroth Fourier coefficient of `f(4z) \overline{θ_χ(z)}`**:
`∫_0^1 f(4z) \overline{θ_χ(z)} dx = Σ_j \overline{g_χ(4j²)} e^{-8πj²y} ρ_{j²} W_τ(8πj²y)`. -/
theorem hasSum_zeroth_tw (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {y : ℝ} (hy : 0 < y) :
    HasSum (fun j : ℤ => starRingEnd ℂ (gTw χ (4 * j ^ 2)) *
        (((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) *
          (rhoW f hτ0 hτ1 (j ^ 2) * Wh τ (8 * π * (j : ℝ) ^ 2 * y))))
      (∫ x in (0 : ℝ)..1, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
        starRingEnd ℂ (thetaTw χ (point x y))) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  set t : ZMod q → ℝ := fun a => ((a.val : ℕ) : ℝ) / q
  have hpt : ∀ (a : ZMod q) (x : ℝ), point x y + ((a.val : ℕ) : ℂ) / q = point (x + t a) y := by
    intro a x; simp only [point, t]; push_cast; ring
  have hsum := hasSum_sum (s := Finset.univ) fun a _ =>
    (hasSum_zeroth_shift (f := f) hτ0 hτ1 (t a) hy).mul_left (χ a)
  have hint : ∫ x in (0 : ℝ)..1, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
      starRingEnd ℂ (thetaTw χ (point x y)) = ∑ a : ZMod q, χ a *
        ∫ x in (0 : ℝ)..1, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
          starRingEnd ℂ (theta (point (x + t a) y)) := by
    have hy4 : 0 < 4 * y := by linarith
    have hcU : Continuous fun x : ℝ => (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) :=
      (gz_slice_continuous N f hy4).comp (continuous_const.mul continuous_id)
    have hθc : ∀ a : ZMod q, Continuous fun x : ℝ => theta (point (x + t a) y) := by
      intro a
      refine continuous_iff_continuousAt.2 fun x => ?_
      have hz : 0 < (point (x + t a) y).im := by simpa [point] using hy
      have hinner : Continuous fun x : ℝ => point (x + t a) y := by unfold point; fun_prop
      exact (differentiableAt_theta hz).continuousAt.comp (f := fun x : ℝ => point (x + t a) y)
        hinner.continuousAt
    have hI : ∀ a ∈ (Finset.univ : Finset (ZMod q)), IntervalIntegrable (fun x : ℝ => χ a *
        ((f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point (x + t a) y))))
        volume 0 1 := fun a _ =>
      ((hcU.mul (Complex.continuous_conj.comp (hθc a))).const_mul _).intervalIntegrable _ _
    calc ∫ x in (0 : ℝ)..1, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
          starRingEnd ℂ (thetaTw χ (point x y))
        = ∫ x in (0 : ℝ)..1, ∑ a : ZMod q, χ a *
            ((f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point (x + t a) y))) := by
          congr 1; funext x
          unfold thetaTw
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [map_mul, Complex.conj_conj, hpt]; ring
      _ = ∑ a : ZMod q, ∫ x in (0 : ℝ)..1, χ a *
            ((f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) * starRingEnd ℂ (theta (point (x + t a) y))) :=
          intervalIntegral.integral_finsetSum hI
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [intervalIntegral.integral_const_mul]
  rw [hint]
  refine hsum.congr_fun fun j => ?_
  rw [← sum_char_phase χ (4 * j ^ 2), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [t]; ring

theorem Gtw_coord {x y : ℝ} (hy : 0 < y) :
    Gtw N f χ (ofComplex (⟨x, y⟩ : ℂ)) = (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
      starRingEnd ℂ (thetaTw χ (point x y)) * ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
  have hz := ofComplex_mk (x := x) hy
  have hp : (⟨x, y⟩ : ℂ) = point x y := by apply Complex.ext <;> simp [point]
  have him : (ofComplex (⟨x, y⟩ : ℂ)).im = y := by
    rw [UpperHalfPlane.im, hz]
  unfold Gtw
  rw [him, hz, hp]
  congr 3
  simp only [point]; push_cast; ring

variable {N f} in
/-- **The horizontal integral of `G_χ`** at height `y`:
`∫_0^1 G_χ(x+iy) y^{w-2} dx = y^{w-7/4} Σ_j \overline{g_χ(4j²)} a_j(y)`. -/
theorem inner_integral_tw (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (w : ℂ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, Gtw N f χ (ofComplex (⟨x, y⟩ : ℂ)) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((y : ℝ) : ℂ) ^ (w - 7 / 4) *
        ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * aMode f hτ0 hτ1 j y := by
  have h := (hasSum_zeroth_tw χ (f := f) hτ0 hτ1 hy).tsum_eq
  have hc : ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ w / ((y : ℝ) : ℂ) ^ 2 =
      ((y : ℝ) : ℂ) ^ (w - 7 / 4) := by
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [Complex.ofReal_cpow hy.le, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0,
      ← Complex.cpow_sub _ _ hy0]
    congr 1; push_cast; ring
  simp_rw [Gtw_coord N f χ hy]
  have e : ∀ x : ℝ, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
      starRingEnd ℂ (thetaTw χ (point x y)) * ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ w /
        ((y : ℝ) : ℂ) ^ 2 =
      ((f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) * starRingEnd ℂ (thetaTw χ (point x y))) *
        ((y : ℝ) : ℂ) ^ (w - 7 / 4) := by
    intro x; rw [← hc]; ring
  simp_rw [e]
  rw [integral_mul_const, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← h, mul_comm]
  rfl

variable {N f} in
/-- **The twisted Shimura strip integral** for `Re w > 7/4`:
`∫_{strip} G_χ(z) y^w dμ = (Σ_j \overline{g_χ(4j²)} ρ_{j²}(8πj²)^{3/4-w}) Mel_τ(w - 1/4)`. -/
theorem strip_integral_Gtw (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 7 / 4 < w.re) :
    ∫ z in GaloisForLFunctions.HTGeometry.modularStrip, Gtw N f χ z * ((z.im : ℝ) : ℂ) ^ w =
      (∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * zCoef f hτ0 hτ1 w j) * melK τ (w - 1 / 4) := by
  obtain ⟨R, hR0, hR⟩ := rhoW_bounded (N := N) (f := f) hτ0 hτ1
  have hw34 : 3 / 4 < w.re := by linarith
  have hwτ : 1 / 4 + τ < w.re := by linarith
  rw [GaloisForLFunctions.HTGeometry.setIntegral_modularStrip_eq_iterated _
    (integrableOn_Gtw_strip χ hτ0 hτ1 hw)]
  have e : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ∫ x in Ico (0 : ℝ) 1,
      Gtw N f χ (ofComplex ⟨x, y⟩) * (((ofComplex (⟨x, y⟩ : ℂ)).im : ℝ) : ℂ) ^ w =
      ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * (((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y) := by
    intro y hy
    have hy0 : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex (⟨x, y⟩ : ℂ)).im = y := fun x => by
      rw [UpperHalfPlane.im, ofComplex_mk hy0]
    simp_rw [him]
    have h := inner_integral_tw χ (N := N) (f := f) hτ0 hτ1 w hy0
    rw [integral_div] at h
    have h2 : ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * (((y : ℝ) : ℂ) ^ (w - 7 / 4) *
        aMode f hτ0 hτ1 j y) = ((y : ℝ) : ℂ) ^ (w - 7 / 4) *
          ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * aMode f hτ0 hτ1 j y := by
      rw [← tsum_mul_left]; exact tsum_congr fun j => by ring
    rw [h2, ← h, Complex.real_smul, div_eq_inv_mul]
    push_cast; ring
  have hint : ∀ j : ℤ, Integrable (fun y : ℝ => starRingEnd ℂ (gTw χ (4 * j ^ 2)) *
      (((y : ℝ) : ℂ) ^ (w - 7 / 4) * aMode f hτ0 hτ1 j y)) (volume.restrict (Ioi 0)) :=
    fun j => ((integral_norm_aMode_le hτ0 hτ1 hR j hw34).1).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi e, ← integral_tsum_of_summable_integral_norm hint]
  · simp_rw [integral_const_mul, integral_aMode (f := f) hτ0 hτ1 _ hwτ]
    rw [← tsum_mul_right]
    exact tsum_congr fun j => by ring
  · refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_)
      (((Real.summable_abs_int_rpow (b := 2 * w.re - 3 / 2) (by linarith)).mul_left
        (q * (R * Real.sqrt (2 * π) * Real.Gamma (w.re - 3 / 4) * (8 * π) ^ (3 / 4 - w.re)))))
    have hb := (integral_norm_aMode_le hτ0 hτ1 hR j hw34).2
    simp_rw [norm_mul]
    rw [integral_const_mul]
    calc ‖starRingEnd ℂ (gTw χ (4 * j ^ 2))‖ *
          ∫ y in Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4)‖ * ‖aMode f hτ0 hτ1 j y‖
        ≤ q * (R * Real.sqrt (2 * π) * Real.Gamma (w.re - 3 / 4) * (8 * π) ^ (3 / 4 - w.re) *
            |(j : ℝ)| ^ (-(2 * w.re - 3 / 2))) := by
          rw [Complex.norm_conj]
          have hb' : ∫ y in Ioi (0 : ℝ), ‖((y : ℝ) : ℂ) ^ (w - 7 / 4)‖ * ‖aMode f hτ0 hτ1 j y‖ ≤
              R * Real.sqrt (2 * π) * Real.Gamma (w.re - 3 / 4) * (8 * π) ^ (3 / 4 - w.re) *
                |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
            simp_rw [← norm_mul]; exact hb
          exact mul_le_mul (norm_gTw_le χ _) hb' (integral_nonneg fun _ => by positivity)
            (Nat.cast_nonneg _)
      _ = _ := by ring

end Kernel

end

end GaloisForLFunctions.RHTower.HalfWeight
