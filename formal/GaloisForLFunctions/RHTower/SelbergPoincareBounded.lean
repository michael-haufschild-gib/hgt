import GaloisForLFunctions.RHTower.SelbergPoincareSeries
import GaloisForLFunctions.RHTower.SarnakXueInner
import GaloisForLFunctions.RHTower.SelbergThreeSixteenths

open UpperHalfPlane EisensteinSeries Complex
open scoped MatrixGroups

/-!
# Continuity, boundedness and the Petersson pairing of `Γ(N)` Poincaré series

`P_m(·, s)` is continuous for `Re s > 1` (locally uniform domination by `‖(c,d)‖^{-2σ}` via the Eisenstein
`r`-function, `continuous_poincare`). For `m ≥ 1` and `Re s > 2` it is bounded on `ℍ` (`poincare_bounded`): writing
`z = g⁻¹ w` with `w ∈ 𝒟`, each summand is at most `((σ/c)^σ + r(𝒟)^{-σ}) ‖(c,d)‖^{-σ}` (`summand_le`; the
translations give `t^σ e^{-ct} ≤ (σ/c)^σ`, the others `Im(δw)^σ ≤ |cw+d|^{-σ}`), and right multiplication by `g⁻¹`
permutes bottom rows injectively. Hence the unfolding applies to `g = \overline{P_n(·,s')}`:
`⟨P_m(·,s), P_n(·,s')⟩ = N ∫_0^∞ y^{s-2} e^{-2πmy/N} \overline{a_m(P_n)(y)} dy` (`poincare_pairing_poincare`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincareBounded
open GaloisForLFunctions.RHTower.SelbergPoincare CongruenceSubgroup

variable (N : ℕ)

theorem continuous_term (m : ℕ) (s : ℂ) (γ : Gamma N) : Continuous (fun z : ℍ => term N m s z γ) := by
  unfold term
  have hA := GaloisForLFunctions.RHTower.SarnakXueInner.continuous_sl_smul (γ : SL(2, ℤ))
  refine Continuous.mul ?_ ?_
  · exact Continuous.cpow (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp hA))
      continuous_const (fun z => Complex.ofReal_mem_slitPlane.mpr ((γ : SL(2, ℤ)) • z).im_pos)
  · exact Complex.continuous_exp.comp (((continuous_const.mul
      (UpperHalfPlane.continuous_coe.comp hA))).div_const _)

variable [NeZero N]

theorem continuous_termQ (m : ℕ) (s : ℂ) (q : Cosets N) : Continuous (fun z : ℍ => termQ N m s z q) := by
  have : (fun z : ℍ => termQ N m s z q) = fun z => term N m s z (Quotient.out q) := by
    funext z; conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [this]; exact continuous_term N m s _

omit [NeZero N] in
theorem bottom_ne_zero (q : Cosets N) : bottom N q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [bottom, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have hdet := ((Quotient.out q : Gamma N) : SL(2, ℤ)).2
  rw [Matrix.det_fin_two, h0, h1] at hdet
  simp at hdet

/-- **Continuity of the Poincaré series** in `z` for `Re s > 1`. -/
theorem continuous_poincare (m : ℕ) {s : ℂ} (hs : 1 < s.re) : Continuous (fun z : ℍ => poincare N m s z) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set A := |z₀.re| + 1
  set B := z₀.im / 2
  set T := 2 * z₀.im
  have hB : 0 < B := by have := z₀.im_pos; simp only [B]; positivity
  set U : Set ℍ := {z | |z.re| < A ∧ B < z.im ∧ z.im < T}
  have hUo : IsOpen U := by
    refine ((isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const).inter
      ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const)))
  have hz₀ : z₀ ∈ U := by
    have := z₀.im_pos
    refine ⟨by simp only [A]; linarith, by simp only [B]; linarith, by simp only [T]; linarith⟩
  set r₀ := r ⟨⟨A, B⟩, hB⟩
  have hr₀ : 0 < r₀ := r_pos _
  have hσ : 2 < 2 * s.re := by linarith
  set u : Cosets N → ℝ := fun q => T ^ s.re * (r₀ ^ (-2 * s.re) * ‖bottom N q‖ ^ (-(2 * s.re)))
  have hu : Summable u := by
    have := ((summable_one_div_norm_rpow hσ).comp_injective (bottom_injective N)).mul_left (r₀ ^ (-2 * s.re))
    exact this.mul_left _
  have hcont : ContinuousOn (fun z : ℍ => poincare N m s z) U := by
    unfold poincare
    refine continuousOn_tsum (fun q => (continuous_termQ N m s q).continuousOn) hu (fun q z hz => ?_)
    have hq : termQ N m s z q = term N m s z (Quotient.out q) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [hq]
    refine (norm_term_le N m s z _).trans ?_
    have hx := bottom_ne_zero N q
    have hstrip : z ∈ UpperHalfPlane.verticalStrip A B := ⟨hz.1.le, hz.2.1.le⟩
    have hrz : r₀ ≤ r z := r_lower_bound_on_verticalStrip z hB hstrip
    have hmul := r_mul_max_le z hx
    have hnx : 0 < ‖bottom N q‖ := norm_pos_iff.mpr hx
    simp only [bottom, Matrix.cons_val_zero, Matrix.cons_val_one] at hmul hnx ⊢
    set D := ‖((((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * z +
      ((((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 1 : ℤ) : ℂ)‖
    set X := ‖![((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 0, ((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 1]‖
    have hD : r₀ * X ≤ D := (mul_le_mul_of_nonneg_right hrz hnx.le).trans hmul
    have hpos : 0 < r₀ * X := by positivity
    have h1 : D ^ (-2 * s.re) ≤ (r₀ * X) ^ (-2 * s.re) :=
      Real.rpow_le_rpow_of_nonpos hpos hD (by linarith)
    have h2 : z.im ^ s.re ≤ T ^ s.re := Real.rpow_le_rpow z.im_pos.le hz.2.2.le (by linarith)
    rw [Real.mul_rpow hr₀.le hnx.le] at h1
    have e : (-2 * s.re) = -(2 * s.re) := by ring
    show _ ≤ T ^ s.re * (r₀ ^ (-2 * s.re) * X ^ (-(2 * s.re)))
    rw [← e]
    exact mul_le_mul h2 h1 (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (by positivity) _)
  exact hcont.continuousAt (hUo.mem_nhds hz₀)

open ModularGroup

/-- `t^σ e^{-ct} ≤ (σ/c)^σ` for `t ≥ 0`. -/
theorem rpow_mul_exp_le {σ c t : ℝ} (hσ : 0 < σ) (hc : 0 < c) (ht : 0 ≤ t) :
    t ^ σ * Real.exp (-c * t) ≤ (σ / c) ^ σ := by
  set u := c * t / σ
  have hu : 0 ≤ u := by positivity
  have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h2 : u ^ σ ≤ Real.exp u ^ σ := Real.rpow_le_rpow hu h1 hσ.le
  have h3 : Real.exp u ^ σ = Real.exp (c * t) := by
    rw [← Real.exp_mul]; congr 1; simp only [u]; field_simp
  have h4 : t = σ / c * u := by simp only [u]; field_simp
  rw [h4, Real.mul_rpow (by positivity) hu]
  have he : Real.exp (-c * (σ / c * u)) = (Real.exp u ^ σ)⁻¹ := by
    rw [h3, ← Real.exp_neg]; congr 1; simp only [u]; field_simp
  rw [he]
  have hpos : 0 < Real.exp u ^ σ := by positivity
  calc (σ / c) ^ σ * u ^ σ * (Real.exp u ^ σ)⁻¹ ≤ (σ / c) ^ σ * Real.exp u ^ σ * (Real.exp u ^ σ)⁻¹ := by
        gcongr
    _ = (σ / c) ^ σ := by field_simp

omit [NeZero N] in
/-- The norm of a single Poincaré summand at `δ • w`. -/
theorem norm_summand (m : ℕ) (s : ℂ) (δ : SL(2, ℤ)) (w : ℍ) :
    ‖(((δ • w).im : ℂ)) ^ s * Complex.exp (2 * Real.pi * Complex.I * m * ((δ • w : ℍ) : ℂ) / N)‖ =
      (δ • w).im ^ s.re * Real.exp (-(2 * Real.pi * m / N) * (δ • w).im) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (δ • w).im_pos, Complex.norm_exp]
  congr 2
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  · field_simp

theorem norm_vec_zero (a : ℤ) : ‖(![0, a] : Fin 2 → ℤ)‖ = ‖a‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr (fun i => ?_)
    fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![0, a] : Fin 2 → ℤ) 1

theorem half_le_im_of_mem_fd {w : ℍ} (hw : w ∈ fd) : (1 : ℝ) / 2 ≤ w.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hw
  nlinarith [w.im_pos]

/-- The lower bound for `r` on `𝒟`. -/
noncomputable def rfd : ℝ := r ⟨⟨1 / 2, 1 / 2⟩, by norm_num⟩

theorem rfd_le {w : ℍ} (hw : w ∈ fd) : rfd ≤ r w :=
  r_lower_bound_on_verticalStrip w (by norm_num) ⟨hw.2, half_le_im_of_mem_fd hw⟩

/-- **Summand bound on `𝒟`**: `Im(δw)^σ e^{-c Im(δw)} ≤ ((σ/c)^σ + r₀^{-σ}) ‖(c_δ, d_δ)‖^{-σ}` for `σ > 0`. -/
theorem summand_le {σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) (δ : SL(2, ℤ)) {w : ℍ} (hw : w ∈ fd) :
    (δ • w).im ^ σ * Real.exp (-c * (δ • w).im) ≤
      ((σ / c) ^ σ + rfd ^ (-σ)) * ‖(![δ 1 0, δ 1 1] : Fin 2 → ℤ)‖ ^ (-σ) := by
  set x : Fin 2 → ℤ := ![δ 1 0, δ 1 1]
  set t := w.im
  have ht := w.im_pos
  have hr0 : 0 < rfd := r_pos _
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    have hdet := δ.2
    rw [Matrix.det_fin_two, h0, h1] at hdet
    simp at hdet
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set D := ‖((δ 1 0 : ℤ) : ℂ) * (w : ℂ) + ((δ 1 1 : ℤ) : ℂ)‖
  have him : (δ • w).im = t / D ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
    rfl
  have he1 : Real.exp (-c * (δ • w).im) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := (δ • w).im_pos; nlinarith)
  by_cases hc0 : δ 1 0 = 0
  · -- `δ = ±T^k`: `Im(δw) = t`, `‖x‖ = 1`
    have hdet := δ.2
    rw [Matrix.det_fin_two, hc0, mul_zero, sub_zero] at hdet
    have hd : δ 1 1 = 1 ∨ δ 1 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
    have hD : D = 1 := by
      simp only [D, hc0, Int.cast_zero, zero_mul, zero_add]
      rcases hd with h | h <;> simp [h]
    have hxn : ‖x‖ = 1 := by
      simp only [x, hc0]
      rw [norm_vec_zero]
      rcases hd with h | h <;> simp [h]
    rw [him, hD, one_pow, div_one, hxn, Real.one_rpow, mul_one]
    have := rpow_mul_exp_le hσ hc ht.le
    have : 0 ≤ rfd ^ (-σ) := by positivity
    linarith
  · have hD : t ≤ D := by
      have hc1 : (1 : ℝ) ≤ |((δ 1 0 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hc0
      have him2 : (((δ 1 0 : ℤ) : ℂ) * (w : ℂ) + ((δ 1 1 : ℤ) : ℂ)).im = (δ 1 0 : ℝ) * t := by simp [t]
      calc t ≤ |((δ 1 0 : ℤ) : ℝ)| * t := le_mul_of_one_le_left ht.le hc1
        _ = |(((δ 1 0 : ℤ) : ℂ) * (w : ℂ) + ((δ 1 1 : ℤ) : ℂ)).im| := by rw [him2, abs_mul, abs_of_pos ht]
        _ ≤ D := Complex.abs_im_le_norm _
    have hDpos : 0 < D := ht.trans_le hD
    have hmul : rfd * ‖x‖ ≤ D := by
      have := r_mul_max_le w hx
      simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      exact (mul_le_mul_of_nonneg_right (rfd_le hw) hnx.le).trans this
    have h1 : (δ • w).im ^ σ ≤ D ^ (-σ) := by
      rw [him, Real.div_rpow ht.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]
      rw [div_le_iff₀ (by positivity), ← Real.rpow_add hDpos]
      have : D ^ (-σ + (2 : ℕ) * σ) = D ^ σ := by congr 1; push_cast; ring
      rw [this]
      exact Real.rpow_le_rpow ht.le hD hσ.le
    have h2 : D ^ (-σ) ≤ (rfd * ‖x‖) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by positivity) hmul (by linarith)
    rw [Real.mul_rpow hr0.le hnx.le] at h2
    have hK : 0 ≤ (σ / c) ^ σ * ‖x‖ ^ (-σ) := by positivity
    calc (δ • w).im ^ σ * Real.exp (-c * (δ • w).im) ≤ (δ • w).im ^ σ * 1 :=
          mul_le_mul_of_nonneg_left he1 (by positivity)
      _ ≤ rfd ^ (-σ) * ‖x‖ ^ (-σ) := by rw [mul_one]; exact h1.trans h2
      _ ≤ _ := by nlinarith

theorem row_eq_of_mul {A A' g : SL(2, ℤ)} (h0 : (A * g) 1 0 = (A' * g) 1 0) (h1 : (A * g) 1 1 = (A' * g) 1 1) :
    A 1 0 = A' 1 0 ∧ A 1 1 = A' 1 1 := by
  have hA : A = A * g * g⁻¹ := by group
  have hA' : A' = A' * g * g⁻¹ := by group
  have e : ∀ (B : SL(2, ℤ)) (j : Fin 2), (B * g * g⁻¹) 1 j = (B * g) 1 0 * (g⁻¹ : SL(2, ℤ)) 0 j +
      (B * g) 1 1 * (g⁻¹ : SL(2, ℤ)) 1 j := by
    intro B j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rw [hA, hA', e A 0, e A' 0, h0, h1]
  · rw [hA, hA', e A 1, e A' 1, h0, h1]

/-- **Boundedness of the Poincaré series** for `m ≥ 1`, `Re s > 2`. -/
theorem poincare_bounded (m : ℕ) (hm : 1 ≤ m) {s : ℂ} (hs : 2 < s.re) :
    ∃ K : ℝ, ∀ z, ‖poincare N m s z‖ ≤ K := by
  set σ := s.re
  have hσ : 0 < σ := by linarith
  set c : ℝ := 2 * Real.pi * m / N
  have hc : 0 < c := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  set C := (σ / c) ^ σ + rfd ^ (-σ)
  have hsum : Summable (fun x : Fin 2 → ℤ => C * ‖x‖ ^ (-σ)) :=
    (summable_one_div_norm_rpow hs).mul_left C
  refine ⟨∑' x : Fin 2 → ℤ, C * ‖x‖ ^ (-σ), fun z => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  set w := g • z
  have hz : z = g⁻¹ • w := by simp [w]
  set ι : Cosets N → (Fin 2 → ℤ) := fun q =>
    ![(((Quotient.out q : Gamma N) : SL(2, ℤ)) * g⁻¹) 1 0, (((Quotient.out q : Gamma N) : SL(2, ℤ)) * g⁻¹) 1 1]
  have hinj : Function.Injective ι := by
    intro q q' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [ι, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    obtain ⟨e0, e1⟩ := row_eq_of_mul h0 h1
    apply bottom_injective N
    ext i; fin_cases i <;> simp [bottom, e0, e1]
  have hbound : ∀ q, ‖termQ N m s z q‖ ≤ C * ‖ι q‖ ^ (-σ) := by
    intro q
    have hq : termQ N m s z q = term N m s z (Quotient.out q) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [hq]
    unfold term
    rw [hz, ← mul_smul]
    rw [norm_summand N m s _ w]
    have e : -(2 * Real.pi * m / N) = -c := rfl
    rw [e]
    exact summand_le hσ hc _ hg
  unfold poincare
  refine (norm_tsum_le_tsum_norm (summable_termQ N m (by linarith) z)).trans ?_
  have hC : 0 ≤ C := by have := r_pos (⟨⟨1 / 2, 1 / 2⟩, by norm_num⟩ : ℍ); simp only [C, rfd]; positivity
  exact Summable.tsum_le_tsum_of_inj ι hinj (fun x _ => mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)) hbound
    (summable_termQ N m (by linarith) z) hsum

open GaloisForLFunctions.RHTower.SarnakXuePretrace GaloisForLFunctions.RHTower.SelbergPoincarePairing
  GaloisForLFunctions.RHTower.SelbergMaassFourier in
/-- **Unfolded Petersson pairing of two Poincaré series** (`N ≥ 3`, `m, n ≥ 1`, `Re s > 1`, `Re s' > 2`):
`∫_{cellP} P_m(z,s) \overline{P_n(z,s')} dμ = N ∫_0^∞ y^{s-2} e^{-2πmy/N} \overline{a_m(P_n(·,s'))(y)} dy`. -/
theorem poincare_pairing_poincare (hN : 3 ≤ N) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {s s' : ℂ}
    (hs : 1 < s.re) (hs' : 2 < s'.re) :
    ∫ z in cellP N, poincare N m s z * (starRingEnd ℂ) (poincare N n s' z) =
      N * ∫ y in Set.Ioi (0 : ℝ), ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
        (starRingEnd ℂ) (coefficient N (m : ℤ) ((fun z => poincare N n s' z) ∘ ofComplex) y) := by
  obtain ⟨K, hK⟩ := poincare_bounded N n hn hs'
  have hgc : Continuous (fun z => (starRingEnd ℂ) (poincare N n s' z)) :=
    Complex.continuous_conj.comp (continuous_poincare N n (by linarith))
  have hgb : ∀ z, ‖(starRingEnd ℂ) (poincare N n s' z)‖ ≤ K := fun z => by rw [Complex.norm_conj]; exact hK z
  have hg : ∀ (γ : Gamma N) z, (starRingEnd ℂ) (poincare N n s' ((γ : SL(2, ℤ)) • z)) =
      (starRingEnd ℂ) (poincare N n s' z) := fun γ z => by rw [poincare_smul]
  rw [poincare_pairing N hN hm hs hgc hgb hg]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro y _
  simp only
  congr 1
  have := GaloisForLFunctions.RHTower.SelbergThreeSixteenths.coefficient_conj (N : ℝ) (Nat.cast_nonneg _) (m : ℤ)
    ((fun z => poincare N n s' z) ∘ ofComplex) y
  exact this

end GaloisForLFunctions.RHTower.SelbergPoincareBounded
