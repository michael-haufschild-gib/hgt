import GaloisForLFunctions.RHTower.SelbergPoincareBounded
import GaloisForLFunctions.RHTower.DeningerFourierCharacter

open Complex MeasureTheory UpperHalfPlane Set
open scoped FourierTransform

/-!
# The Petersson–Kloosterman formula for `Γ(N)` Poincaré series

Term-by-term integration over one period of the Fourier–Kloosterman form `Q_n(z,s)` (uniformly summable by Weil's
bound; `coeff_tsum`, `coeff_tsum_characters`) gives its Fourier coefficients
`a_m(Q_n(·,s))(y) = δ_{mn} y^s e^{-2πny/N} + Σ_c B_{c,m}(y)`, `B_{c,m} = c^{-2s} N^{-s} 𝓕ker_c(m) S_N(n,m;c)`
(`coefficient_Q`). With the unfolded Petersson pairing this is the arithmetic side of a Kuznetsov-type formula:
`⟨P_m(·,s), P_n(·,s')⟩ = N ∫ y^{s-2} e^{-2πmy/N} \overline{a_m(P_n(·,s'))(y)} dy` (`petersson_kloosterman`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergMaassFourier
  GaloisForLFunctions.RHTower.SelbergMaassMean _root_.RHTower GaloisForLFunctions.RHTower.KloostermanUniform

variable (N : ℕ) [NeZero N]

theorem ofComplex_point {x y : ℝ} (hy : 0 < y) :
    (ofComplex (point x y)).im = y ∧ (ofComplex (point x y)).re = x := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  rw [ofComplex_apply_of_im_pos hp]
  constructor <;> simp [point, UpperHalfPlane.im, UpperHalfPlane.re]

/-- The Fourier coefficient of a uniformly summable series of characters. -/
theorem coeff_tsum_characters {w : ℝ} (hw : 0 < w) {B : ℤ → ℂ} (hB : Summable (fun k => ‖B k‖)) (m : ℤ) :
    deningerFourierCoeff w (fun x => ∑' k, B k * deningerCharacter w k x) m = B m := by
  unfold deningerFourierCoeff
  have hcont : ∀ k, Continuous (fun x => deningerFourierKernel w m x * (B k * deningerCharacter w k x)) := by
    intro k
    unfold deningerFourierKernel deningerCharacter deningerFourierKernel
    fun_prop
  set f : ℤ → C(ℝ, ℂ) := fun k => ⟨_, hcont k⟩
  have hnorm : ∀ k x, ‖deningerFourierKernel w m x * (B k * deningerCharacter w k x)‖ = ‖B k‖ := by
    intro k x
    rw [norm_mul, norm_mul, deningerCharacter_apply]
    have h1 : ‖deningerFourierKernel w m x‖ = 1 := by
      unfold deningerFourierKernel
      rw [Complex.norm_exp]; simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * k * x / w)‖ = 1 := by
      rw [Complex.norm_exp]; simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [h1, h2]; ring
  have hsum : Summable fun k => ‖ContinuousMap.restrict (⟨Set.uIcc 0 w, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) (f k)‖ := by
    refine hB.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun x => ?_)
    simp only [ContinuousMap.restrict_apply, f, ContinuousMap.coe_mk]
    rw [hnorm]
  have h := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
  simp only [f, ContinuousMap.coe_mk] at h
  have hint : ∀ x, deningerFourierKernel w m x * ∑' k, B k * deningerCharacter w k x =
      ∑' k, deningerFourierKernel w m x * (B k * deningerCharacter w k x) := fun x => (tsum_mul_left).symm
  simp_rw [hint, ← h]
  have hk : ∀ k, (1 / w) * ∫ x in (0 : ℝ)..w, deningerFourierKernel w m x * (B k * deningerCharacter w k x) =
      B k * (if m = k then 1 else 0) := by
    intro k
    have := deningerFourierCoeff_character hw k m
    unfold deningerFourierCoeff at this
    rw [← this]
    simp_rw [mul_left_comm (deningerFourierKernel w m _) (B k)]
    rw [intervalIntegral.integral_const_mul]; ring
  rw [← tsum_mul_left]
  simp_rw [hk]
  rw [tsum_eq_single m (fun k hk' => by rw [if_neg (Ne.symm hk'), mul_zero])]
  simp

/-- The Fourier coefficient of a uniformly summable series of continuous functions. -/
theorem coeff_tsum {w : ℝ} (_hw : 0 < w) {G : ℤ → ℝ → ℂ} (hG : ∀ c, Continuous (G c)) {u : ℤ → ℝ}
    (hu : Summable u) (hGu : ∀ c x, ‖G c x‖ ≤ u c) (m : ℤ) :
    deningerFourierCoeff w (fun x => ∑' c, G c x) m = ∑' c, deningerFourierCoeff w (G c) m := by
  unfold deningerFourierCoeff
  have hcont : ∀ c, Continuous (fun x => deningerFourierKernel w m x * G c x) := by
    intro c
    exact (by unfold deningerFourierKernel; fun_prop : Continuous (deningerFourierKernel w m)).mul (hG c)
  set f : ℤ → C(ℝ, ℂ) := fun c => ⟨_, hcont c⟩
  have hK : ∀ x, ‖deningerFourierKernel w m x‖ = 1 := by
    intro x; unfold deningerFourierKernel
    rw [Complex.norm_exp]; simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  have hsum : Summable fun c => ‖ContinuousMap.restrict (⟨Set.uIcc 0 w, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ) (f c)‖ := by
    refine hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_)
    refine (ContinuousMap.norm_le _ ((norm_nonneg _).trans (hGu c 0))).mpr (fun x => ?_)
    simp only [ContinuousMap.restrict_apply, f, ContinuousMap.coe_mk]
    rw [norm_mul, hK, one_mul]; exact hGu c _
  have h := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum
  simp only [f, ContinuousMap.coe_mk] at h
  have hint : ∀ x, deningerFourierKernel w m x * ∑' c, G c x = ∑' c, deningerFourierKernel w m x * G c x :=
    fun x => (tsum_mul_left).symm
  simp_rw [hint, ← h, tsum_mul_left]

/-- The Kloosterman coefficient `B_{c,k}` of `P_n(·,s)` at height `y`. -/
noncomputable def kcoef (n : ℕ) (s : ℂ) (y : ℝ) (c k : ℤ) : ℂ :=
  if c = 0 then 0 else
    cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
      (𝓕 (ker (n / ((c : ℝ) ^ 2 * N) / N) (y / N) s) k * ksum N n c k)

omit [NeZero N] in
theorem Qc_point (n : ℕ) (s : ℂ) {x y : ℝ} (hy : 0 < y) (c : ℤ) :
    Qc N n s (ofComplex (point x y)) c = ∑' k, kcoef N n s y c k * deningerCharacter N k x := by
  obtain ⟨him, hre⟩ := ofComplex_point (x := x) hy
  unfold Qc kcoef
  by_cases hc : c = 0
  · simp [hc]
  simp only [if_neg hc, him, hre]
  rw [← tsum_mul_left]
  apply tsum_congr; intro k
  rw [deningerCharacter_apply]; push_cast; ring

theorem norm_kcoef_le (n : ℕ) (_hn : n ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) (c k : ℤ) :
    ‖kcoef N n s y c k‖ ≤ ((c : ℝ) ^ 2) ^ (-s.re) *
      (bndX N n y s.re s.re ‖s‖ / (1 + (k : ℝ) ^ 2) * kmaxU (c.sign * n) (c.natAbs * N)) := by
  unfold kcoef
  by_cases hc : c = 0
  · simp only [if_pos hc, norm_zero]
    have := bndX_nonneg N n hy s.re s.re ‖s‖ (norm_nonneg s)
    have := kmaxU_nonneg (c.sign * n) (c.natAbs * N)
    positivity
  rw [if_neg hc]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hc2 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ c ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs c]
    exact_mod_cast this
  have hE := norm_exp_neg_mul_log (s := s) hc2 le_rfl
  have hEN := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
  rw [neg_zero, Real.rpow_zero] at hEN
  set z := ofComplex (point 0 y)
  obtain ⟨him, hre⟩ := ofComplex_point (x := 0) hy
  have ht := norm_Qc_term_le N n z hc hs le_rfl le_rfl le_rfl k
  rw [him, hre] at ht
  have h1 : ‖𝓕 (ker (n / ((c : ℝ) ^ 2 * N) / N) (y / N) s) k * ksum N n c k‖ =
      ‖𝓕 (ker (n / ((c : ℝ) ^ 2 * N) / N) (y / N) s) k * cexp (2 * Real.pi * Complex.I * k * (0 : ℝ) / N) *
        ksum N n c k‖ := by simp
  rw [norm_mul, norm_mul, h1]
  have hk := norm_nonneg (𝓕 (ker (n / ((c : ℝ) ^ 2 * N) / N) (y / N) s) k *
    cexp (2 * Real.pi * Complex.I * k * (0 : ℝ) / N) * ksum N n c k)
  calc ‖cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ))‖ * ‖cexp (-s * (Real.log N : ℂ))‖ * _
      ≤ ((c : ℝ) ^ 2) ^ (-s.re) * 1 * (bndX N n y s.re s.re ‖s‖ / (1 + (k : ℝ) ^ 2) *
          kmaxU (c.sign * n) (c.natAbs * N)) := mul_le_mul (mul_le_mul hE hEN (norm_nonneg _) (by positivity)) ht
            (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem summable_kcoef (n : ℕ) (hn : n ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) (c : ℤ) :
    Summable (fun k => ‖kcoef N n s y c k‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_kcoef_le N n hn hs hy c) ?_
  have := ((summable_inv_one_add_sq.mul_left (bndX N n y s.re s.re ‖s‖)).mul_right
    (kmaxU (c.sign * n) (c.natAbs * N))).mul_left (((c : ℝ) ^ 2) ^ (-s.re))
  refine this.congr (fun k => ?_); ring

omit [NeZero N] in
theorem norm_character (k : ℤ) (x : ℝ) : ‖deningerCharacter N k x‖ = 1 := by
  rw [deningerCharacter_apply, Complex.norm_exp]; simp [Complex.div_re, Complex.mul_re, Complex.mul_im]

/-- **Fourier coefficients of the continued Poincaré series**: for `n ≥ 1`, `Re s > 3/4`, `y > 0`,
`a_m(Q_n(·,s))(y) = δ_{mn} y^s e^{-2πny/N} + Σ_c B_{c,m}(y)`. -/
theorem coefficient_Q (n : ℕ) (hn : n ≠ 0) {s : ℂ} (hs : 3 / 4 < s.re) {y : ℝ} (hy : 0 < y) (m : ℤ) :
    coefficient N m ((fun z => Q N n s z) ∘ ofComplex) y =
      (if m = n then (y : ℂ) ^ s * cexp (-(2 * Real.pi * n * y / N : ℝ)) else 0) + ∑' c, kcoef N n s y c m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs' : 1 / 2 < s.re := by linarith
  set A : ℂ := (y : ℂ) ^ s * cexp (-(2 * Real.pi * n * y / N : ℝ))
  set G : ℤ → ℝ → ℂ := fun c x => ∑' k, kcoef N n s y c k * deningerCharacter N k x
  have hpt : ∀ x, ((fun z => Q N n s z) ∘ ofComplex) (point x y) =
      A * deningerCharacter N n x + ∑' c, G c x := by
    intro x
    obtain ⟨him, hre⟩ := ofComplex_point (x := x) hy
    simp only [Function.comp_apply, Q, him]
    congr 1
    · have hp : 0 < (point x y).im := by simpa [point] using hy
      rw [ofComplex_apply_of_im_pos hp, deningerCharacter_apply]
      simp only [A, point]
      rw [mul_assoc ((y : ℂ) ^ s), ← Complex.exp_add]
      congr 2
      push_cast
      linear_combination (2 * (Real.pi : ℂ) * n * y / N) * Complex.I_sq
    · apply tsum_congr; intro c
      exact Qc_point N n s hy c
  have hGc : ∀ c, Continuous (G c) := by
    intro c
    refine continuous_tsum (fun k => continuous_const.mul ?_) (summable_kcoef N n hn hs' hy c) (fun k x => ?_)
    · rw [show deningerCharacter N k = fun x : ℝ => cexp (2 * Real.pi * Complex.I * k * (x : ℂ) / N) from
        funext (deningerCharacter_apply k)]
      fun_prop
    · rw [norm_mul, norm_character, mul_one]
  have hGu : ∀ c x, ‖G c x‖ ≤ cw N n s.re c * (bndX N n y s.re s.re ‖s‖ * zsum) := by
    intro c x
    have h := norm_Qc_le N n (ofComplex (point x y)) c hs' le_rfl le_rfl le_rfl
    obtain ⟨him, _⟩ := ofComplex_point (x := x) hy
    rw [Qc_point N n s hy c, him] at h
    exact h
  have hsumc : Summable (fun c => cw N n s.re c * (bndX N n y s.re s.re ‖s‖ * zsum)) :=
    (summable_cw N n (Nat.pos_of_ne_zero (NeZero.ne N)) hn hs).mul_right _
  have hcoefG : ∀ c, deningerFourierCoeff N (G c) m = kcoef N n s y c m :=
    fun c => coeff_tsum_characters hNpos (summable_kcoef N n hn hs' hy c) m
  unfold coefficient
  simp_rw [hpt]
  -- linearity
  have hA : Continuous (fun x => A * deningerCharacter N n x) := by
    rw [show deningerCharacter N n = fun x : ℝ => cexp (2 * Real.pi * Complex.I * n * (x : ℂ) / N) from
      funext (deningerCharacter_apply n)]
    fun_prop
  have hT : Continuous (fun x => ∑' c, G c x) := continuous_tsum hGc hsumc hGu
  have hlin : deningerFourierCoeff N (fun x => A * deningerCharacter N n x + ∑' c, G c x) m =
      deningerFourierCoeff N (fun x => A * deningerCharacter N n x) m + deningerFourierCoeff N (fun x => ∑' c, G c x) m := by
    unfold deningerFourierCoeff
    rw [← mul_add, ← intervalIntegral.integral_add]
    · congr 1; apply intervalIntegral.integral_congr; intro x _; simp only; ring
    · exact ((by unfold deningerFourierKernel; fun_prop : Continuous (deningerFourierKernel N m)).mul hA).intervalIntegrable _ _
    · exact ((by unfold deningerFourierKernel; fun_prop : Continuous (deningerFourierKernel N m)).mul hT).intervalIntegrable _ _
  rw [hlin, coeff_tsum hNpos hGc hsumc hGu m]
  simp_rw [hcoefG]
  congr 1
  have hconst : deningerFourierCoeff N (fun x => A * deningerCharacter N n x) m =
      A * deningerFourierCoeff N (deningerCharacter N n) m := by
    unfold deningerFourierCoeff
    simp_rw [mul_left_comm (deningerFourierKernel _ _ _) A]
    rw [intervalIntegral.integral_const_mul]; ring
  rw [hconst, deningerFourierCoeff_character hNpos]
  split_ifs <;> simp

open GaloisForLFunctions.RHTower.SarnakXuePretrace GaloisForLFunctions.RHTower.SelbergPoincare in
/-- **Petersson–Kloosterman formula for `Γ(N)`** (`N ≥ 3`, `m, n ≥ 1`, `Re s > 1`, `Re s' > 2`):
`⟨P_m(·,s), P_n(·,s')⟩ = N ∫_0^∞ y^{s-2} e^{-2πmy/N} \overline{δ_{mn} y^{s'} e^{-2πny/N} + Σ_c B_{c,m}(y)} dy`,
with `B_{c,m}(y) = c^{-2s'} N^{-s'} 𝓕ker_c(m) S_N(n,m;c)`. -/
theorem petersson_kloosterman (hN : 3 ≤ N) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {s s' : ℂ}
    (hs : 1 < s.re) (hs' : 2 < s'.re) :
    ∫ z in cellP N, poincare N m s z * (starRingEnd ℂ) (poincare N n s' z) =
      N * ∫ y in Set.Ioi (0 : ℝ), ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
        (starRingEnd ℂ) ((if (m : ℤ) = n then (y : ℂ) ^ s' * cexp (-(2 * Real.pi * n * y / N : ℝ)) else 0) +
          ∑' c, kcoef N n s' y c m) := by
  rw [GaloisForLFunctions.RHTower.SelbergPoincareBounded.poincare_pairing_poincare N hN hm hn hs hs']
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simp only
  congr 2
  have hPQ : (fun z => poincare N n s' z) = fun z => Q N n s' z :=
    funext (fun z => poincare_eq_Q N n hN (by linarith) z)
  rw [hPQ]
  exact coefficient_Q N n (by omega) (by linarith) hy m

end GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman
