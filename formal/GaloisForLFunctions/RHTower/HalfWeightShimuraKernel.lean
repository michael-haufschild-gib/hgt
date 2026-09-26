import GaloisForLFunctions.RHTower.HalfWeightExceptionalMaass
import GaloisForLFunctions.RHTower.HalfWeightRankinSelberg

/-!
# The Shimura kernel `G(z) = f(4z) \overline{θ(z)} y^{1/4}`

For a Maass cusp form `f` on `Γ₀(N+1)` with `λ = 1/4 - τ²`:

* `conjFour`, `conjFour_smul`, `conjFour_mem`, `f_four_smul`: `4·γz = γ'(4z)` with
  `γ' = [[a, 4b], [c/4, d]] ∈ Γ₀(N+1)` for `γ ∈ Γ₀(4(N+1))`, so `f(4γz) = f(4z)`;
* **`Gsh_smul`**: `G(γz) = \overline{j(γ,z)} G(z)` on `Γ₀(4(N+1))` (`|J|² = |cz+d|`,
  `Im(γz) = Im z/|J|⁴`): the transformation law required by `unfold_eisHalf`;
* `continuous_Gsh`;
* `hermite_four`: `4·gz = h((ez+β)/δ)` with `h ∈ SL₂(ℤ)`, `eδ = 4` (Hermite normal form of
  `diag(4,1)·g`); `f_four_decay`: `f(4gz)` decays exponentially in `Im z` for every `g`
  (`maass_decay` of the translate `f∘h`);
* `norm_theta_le`: `‖θ(v)‖ ≤ 1 + 1/(π Im v)`; `im_smul_two_sided`: on `𝒟`,
  `1/(20E y) ≤ Im(Aw) ≤ 20E y`;
* **`Gsh_hdec`**: `‖G(Aw)‖ (Im(Aw)^B + Im(Aw)^{-B})` is integrable on `𝒟` for every `A ∈ SL₂(ℤ)`
  and `B ∈ ℝ` — the rapid-decay hypothesis of `differentiableAt_rsFold`.
-/

open Real Complex Filter Topology MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

open SelbergMaassFourier SelbergMaassMean SelbergThreeSixteenths
open _root_.RHTower GaloisForLFunctions.RHTower

noncomputable section

/-! ### The Shimura kernel `G(z) = f(4z) \overline{θ(z)} y^{1/4}` -/

variable (N : ℕ) {τ : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ)))

/-- `G(z) = f(4z) \overline{θ(z)} y^{1/4}`. -/
def Gsh (z : ℍ) : ℂ :=
  (f.1.1 ∘ ofComplex) (4 * (z : ℂ)) * starRingEnd ℂ (theta z) * ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ)

/-- The conjugated matrix `[[a, 4b], [c/4, d]]`. -/
def conjFour (γ : SL(2, ℤ)) (hc : (4 : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, 4 * γ 0 1; γ 1 0 / 4, γ 1 1], by
    obtain ⟨c', hc'⟩ := hc
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of, hc', Int.mul_ediv_cancel_left _ (by norm_num)]
    rw [hc'] at hdet
    linarith⟩

theorem conjFour_smul (γ : SL(2, ℤ)) (hc : (4 : ℤ) ∣ γ 1 0) (z : ℍ) :
    ofComplex (4 * ((γ • z : ℍ) : ℂ)) = conjFour γ hc • ofComplex (4 * (z : ℂ)) := by
  have h4z : 0 < (4 * (z : ℂ)).im := by simp; exact z.im_pos
  have h4g : 0 < (4 * ((γ • z : ℍ) : ℂ)).im := by simp; exact (γ • z).im_pos
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos h4g]
  change 4 * ((γ • z : ℍ) : ℂ) = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
    ofComplex_apply_of_im_pos h4z]
  simp only [algebraMap_int_eq, eq_intCast]
  obtain ⟨c', hc'⟩ := hc
  simp only [conjFour, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [hc', Int.mul_ediv_cancel_left _ (by norm_num)]
  have hden : ((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + (γ 1 1 : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  rw [hc'] at hden
  have hden' : ((c' : ℤ) : ℂ) * (4 * (z : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro h; apply hden; push_cast at h ⊢; linear_combination h
  push_cast at hden hden' ⊢
  field_simp

theorem conjFour_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * (N + 1))) :
    ∃ hc : (4 : ℤ) ∣ γ 1 0, conjFour γ hc ∈ CongruenceSubgroup.Gamma0 (N + 1) := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have h : ((4 * (N + 1) : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  obtain ⟨m, hm⟩ := h
  have h4 : (4 : ℤ) ∣ γ 1 0 := ⟨(N + 1 : ℤ) * m, by rw [hm]; push_cast; ring⟩
  refine ⟨h4, ?_⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simp only [conjFour, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [hm, show ((4 * (N + 1) : ℕ) : ℤ) * m = 4 * ((N + 1 : ℕ) * m) by push_cast; ring,
    Int.mul_ediv_cancel_left _ (by norm_num), ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_mul_right _ _

/-- `f(4 γz) = f(4z)` for `γ ∈ Γ₀(4(N+1))`. -/
theorem f_four_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * (N + 1))) (z : ℍ) :
    (f.1.1 ∘ ofComplex) (4 * ((γ • z : ℍ) : ℂ)) = (f.1.1 ∘ ofComplex) (4 * (z : ℂ)) := by
  obtain ⟨hc, hmem⟩ := conjFour_mem N hγ
  simp only [Function.comp]
  rw [conjFour_smul γ hc z]
  have hm : integralSL2ToReal (conjFour γ hc) ∈ realImage (CongruenceSubgroup.Gamma0 (N + 1)) :=
    ⟨_, hmem, rfl⟩
  have hi := f.1.property ⟨integralSL2ToReal (conjFour γ hc), hm⟩ (ofComplex (4 * (z : ℂ)))
  rw [integral_action] at hi
  exact hi

/-- **Transformation law**: `G(γz) = \overline{j(γ,z)} G(z)` on `Γ₀(4(N+1))`. -/
theorem Gsh_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * (N + 1))) (z : ℍ) :
    Gsh N f (γ • z) = starRingEnd ℂ (jU γ z) * Gsh N f z := by
  have hγ4 : γ ∈ CongruenceSubgroup.Gamma0 4 := by
    rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
    have h : ((4 * (N + 1) : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (dvd_mul_right (4 : ℤ) (N + 1 : ℤ)).trans (by exact_mod_cast h)
  have hJ := norm_sq_J hγ4 z
  have hJpos : 0 < ‖J γ z‖ := norm_pos_iff.2 (J_ne_zero γ z)
  have hy := z.im_pos
  have him : (γ • z).im = z.im / ‖J γ z‖ ^ 4 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ← hJ]; ring
  have hpow : (γ • z).im ^ (1 / 4 : ℝ) = z.im ^ (1 / 4 : ℝ) / ‖J γ z‖ := by
    rw [him, Real.div_rpow hy.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hJpos.le]
    norm_num
  unfold Gsh
  rw [f_four_smul N f hγ z, theta_smul, hpow, jU, map_mul, map_div₀, Complex.conj_ofReal]
  push_cast
  have hJ0 : ((‖J γ z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hJpos.ne'
  field_simp

/-! ### Continuity and a Hermite decomposition of `z ↦ 4 gz` -/

theorem continuous_Gsh : Continuous (Gsh N f) := by
  have hF : ContinuousOn (f.1.1 ∘ ofComplex) {w : ℂ | 0 < w.im} := f.2.2.1.1.continuousOn
  have h4 : Continuous fun z : ℍ => (f.1.1 ∘ ofComplex) (4 * (z : ℂ)) :=
    hF.comp_continuous (continuous_const.mul UpperHalfPlane.continuous_coe)
      (fun z => by simp; exact z.im_pos)
  have hθ : Continuous fun z : ℍ => theta z :=
    continuous_iff_continuousAt.2 fun z =>
      ((differentiableAt_theta z.im_pos).continuousAt).comp UpperHalfPlane.continuous_coe.continuousAt
  have hy : Continuous fun z : ℍ => ((z.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.rpow_const fun z => Or.inl z.im_pos.ne')
  unfold Gsh
  exact (h4.mul (Complex.continuous_conj.comp hθ)).mul hy

theorem aff_im_eq (e δ β : ℤ) (hδ : 0 < δ) (z : ℂ) :
    (((e : ℂ) * z + β) / δ).im = (e : ℝ) * z.im / δ := by
  have hδ0 : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ.ne'
  rw [show ((e : ℂ) * z + β) / δ = ((e : ℂ) * z + β) * (((1 / δ : ℝ)) : ℂ) by push_cast; ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  simp
  field_simp

/-- The point `(e z + β)/δ ∈ ℍ`. -/
def affPt (e δ β : ℤ) (he : 0 < e) (hδ : 0 < δ) (z : ℍ) : ℍ :=
  ⟨((e : ℂ) * z + β) / δ, by
    rw [aff_im_eq e δ β hδ]
    have : (0 : ℝ) < e := by exact_mod_cast he
    have : (0 : ℝ) < δ := by exact_mod_cast hδ
    have := z.im_pos
    positivity⟩

theorem affPt_im (e δ β : ℤ) (he : 0 < e) (hδ : 0 < δ) (z : ℍ) :
    (affPt e δ β he hδ z).im = (e : ℝ) * z.im / δ :=
  aff_im_eq e δ β hδ z

/-- **Hermite decomposition**: `4 · (g z) = h ((e z + β)/δ)` with `h ∈ SL₂(ℤ)`, `e δ = 4`, `e, δ > 0`. -/
theorem hermite_four (g : SL(2, ℤ)) :
    ∃ (h : SL(2, ℤ)) (e δ β : ℤ) (he : 0 < e) (hδ : 0 < δ), e * δ = 4 ∧
      ∀ z : ℍ, ofComplex (4 * ((g • z : ℍ) : ℂ)) = h • affPt e δ β he hδ z := by
  set a := g 0 0
  set b := g 0 1
  set c := g 1 0
  set d := g 1 1
  have hdet : a * d - b * c = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  have hg0 : 0 < (4 * a).gcd c := by
    by_cases h : 4 * a = 0
    · have hc : c ≠ 0 := by
        intro hc; have : a = 0 := by linarith
        rw [this, hc] at hdet; simp at hdet
      exact Int.gcd_pos_of_ne_zero_right (4 * a) hc
    · exact Int.gcd_pos_of_ne_zero_left c h
  set e : ℤ := ((4 * a).gcd c : ℤ) with he_def
  have he : 0 < e := by simp only [e]; exact_mod_cast hg0
  obtain ⟨p, hp⟩ : e ∣ 4 * a := Int.gcd_dvd_left (4 * a) c
  obtain ⟨q, hq⟩ : e ∣ c := Int.gcd_dvd_right (4 * a) c
  have hg1 : (4 * a / e).gcd (c / e) = 1 := Int.gcd_div_gcd_div_gcd hg0
  have hpd : 4 * a / e = p := by rw [hp]; exact Int.mul_ediv_cancel_left _ he.ne'
  have hqd : c / e = q := by rw [hq]; exact Int.mul_ediv_cancel_left _ he.ne'
  rw [hpd, hqd] at hg1
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.2 hg1
  have hdeth : Matrix.det !![p, -v; q, u] = 1 := by rw [Matrix.det_fin_two_of]; linarith
  set h : SL(2, ℤ) := ⟨!![p, -v; q, u], hdeth⟩
  set β : ℤ := 4 * b * u + d * v
  set δ : ℤ := p * d - 4 * b * q
  have heδ : e * δ = 4 := by
    have : e * (p * d - 4 * b * q) = (e * p) * d - 4 * b * (e * q) := by ring
    simp only [δ]; rw [this, ← hp, ← hq]; linarith
  have hδ : 0 < δ := by
    by_contra hneg; push Not at hneg
    have : e * δ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he.le hneg
    linarith
  refine ⟨h, e, δ, β, he, hδ, heδ, fun z => ?_⟩
  have h4g : 0 < (4 * ((g • z : ℍ) : ℂ)).im := by simp; exact (g • z).im_pos
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos h4g]
  change 4 * ((g • z : ℍ) : ℂ) = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, affPt, h, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  set w : ℂ := ((e : ℂ) * z + β) / δ
  have hδC : ((δ : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have e1 : (e : ℂ) * p = 4 * a := by exact_mod_cast hp.symm
  have e2 : (e : ℂ) * q = c := by exact_mod_cast hq.symm
  have huvC : (u : ℂ) * p + v * q = 1 := by exact_mod_cast huv
  have hwδ : w * δ = (e : ℂ) * z + β := div_mul_cancel₀ _ hδC
  have hβ : (β : ℂ) = 4 * b * u + d * v := by simp only [β]; push_cast; ring
  have hδ' : (δ : ℂ) = p * d - 4 * b * q := by simp only [δ]; push_cast; ring
  have hnum : (p : ℂ) * w + -(v : ℂ) = (4 * a * (z : ℂ) + 4 * b) / δ := by
    rw [eq_div_iff hδC]
    linear_combination (p : ℂ) * hwδ + (z : ℂ) * e1 - (v : ℂ) * hδ' + (p : ℂ) * hβ + 4 * (b : ℂ) * huvC
  have hden : (q : ℂ) * w + (u : ℂ) = ((c : ℂ) * z + d) / δ := by
    rw [eq_div_iff hδC]
    linear_combination (q : ℂ) * hwδ + (z : ℂ) * e2 + (u : ℂ) * hδ' + (q : ℂ) * hβ + (d : ℂ) * huvC
  have hcd : ((c : ℤ) : ℂ) * (z : ℂ) + ((d : ℤ) : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero g z
  push_cast
  change 4 * (((a : ℂ) * z + b) / ((c : ℂ) * z + d)) = ((p : ℂ) * w + -(v : ℂ)) / ((q : ℂ) * w + u)
  rw [hnum, hden]
  field_simp

/-! ### Size bounds -/

/-- `‖θ(v)‖ ≤ 1 + 1/(π Im v)`. -/
theorem norm_theta_le {v : ℂ} (hv : 0 < v.im) : ‖theta v‖ ≤ 1 + 1 / (π * v.im) := by
  have h2 : 0 < (2 * v).im := by simp; linarith
  have h := norm_jacobiTheta_sub_one_le h2
  have hre : (2 * v).im = 2 * v.im := by simp
  rw [hre] at h
  set q := Real.exp (-π * (2 * v.im))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  have hkey : 2 / (1 - q) * q ≤ 1 / (π * v.im) := by
    -- `2q/(1-q) = 2/(e^{2π Im v} - 1) ≤ 2/(2π Im v)`
    have hE : 1 / q = Real.exp (π * (2 * v.im)) := by
      simp only [q]; rw [one_div, ← Real.exp_neg]; ring_nf
    have hx : 2 * π * v.im + 1 ≤ Real.exp (π * (2 * v.im)) := by
      have := Real.add_one_le_exp (π * (2 * v.im)); linarith
    have hpos : 0 < π * v.im := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) hpos]
    have : q * (2 * π * v.im + 1) ≤ 1 := by
      calc q * (2 * π * v.im + 1) ≤ q * Real.exp (π * (2 * v.im)) :=
            mul_le_mul_of_nonneg_left hx hq0.le
        _ = 1 := by rw [← hE]; field_simp
    nlinarith
  calc ‖theta v‖ = ‖(jacobiTheta (2 * v) - 1) + 1‖ := by rw [theta]; ring_nf
    _ ≤ ‖jacobiTheta (2 * v) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / (π * v.im) + 1 := by rw [norm_one]; linarith
    _ = _ := by ring

variable {N f} in
/-- **Cusp decay of `f(4 g z)`**: exponential in `Im z` for every `g ∈ SL₂(ℤ)`. -/
theorem f_four_decay (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (g : SL(2, ℤ)) :
    ∃ C c t₀ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < t₀ ∧ ∀ z : ℍ, t₀ ≤ z.im →
      ‖(f.1.1 ∘ ofComplex) (4 * ((g • z : ℍ) : ℂ))‖ ≤ C * Real.exp (-c * z.im) := by
  obtain ⟨h, e, δ, β, he, hδ, heδ, hH⟩ := hermite_four g
  have hlam : (0 : ℝ) < 1 / 4 - τ ^ (2 : ℕ) ∧ 1 / 4 - τ ^ (2 : ℕ) < 1 / 4 := by
    constructor <;> nlinarith
  set F := SelbergMaassCuspTransport.translate (N + 1) h (fG N f)
  obtain ⟨C, t₀, ht₀, hdec⟩ := SelbergMaassExpDecayCell.maass_decay N ⟨_, hlam⟩ F
  set κ : ℝ := 2 * π / ((N + 1 : ℕ) : ℝ) / 2
  have hκ : 0 < κ := by positivity
  have heδ' : (1 : ℝ) / 4 ≤ (e : ℝ) / δ := by
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hδ4 : (δ : ℝ) ≤ 4 := by
      have : (e : ℝ) * δ = 4 := by exact_mod_cast heδ
      nlinarith
    have hδp : (0 : ℝ) < δ := by exact_mod_cast hδ
    rw [div_le_div_iff₀ (by norm_num) hδp]; nlinarith
  refine ⟨max C 0, κ / 4, 4 * t₀, le_max_right _ _, by positivity, by positivity, fun z hz => ?_⟩
  have hz0 := z.im_pos
  have haff : (affPt e δ β he hδ z).im ≥ z.im / 4 := by
    rw [affPt_im]
    have hδp : (0 : ℝ) < δ := by exact_mod_cast hδ
    calc z.im / 4 = (1 / 4) * z.im := by ring
      _ ≤ (e : ℝ) / δ * z.im := mul_le_mul_of_nonneg_right heδ' hz0.le
      _ = (e : ℝ) * z.im / δ := by ring
  have hb : ‖F.1.1 (affPt e δ β he hδ z)‖ ≤ C * Real.exp (-κ * (affPt e δ β he hδ z).im) := by
    have := hdec (affPt e δ β he hδ z) (by linarith)
    convert this using 3
    simp only [κ]; ring
  simp only [Function.comp]
  rw [hH z]
  have hF : (F.1.1 (affPt e δ β he hδ z)) = f.1.1 (h • affPt e δ β he hδ z) := by
    rw [SelbergMaassCuspTransport.translate_apply]; rfl
  rw [← hF]
  calc ‖F.1.1 (affPt e δ β he hδ z)‖ ≤ C * Real.exp (-κ * (affPt e δ β he hδ z).im) := hb
    _ ≤ max C 0 * Real.exp (-κ * (affPt e δ β he hδ z).im) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (-(κ / 4) * z.im) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (le_max_right _ _)

theorem rpow_le_of_mem {s L B : ℝ} (hs : 0 < s) (h1 : s ≤ L) (h2 : 1 / s ≤ L) :
    s ^ B ≤ L ^ |B| := by
  rcases le_or_gt 0 B with hB | hB
  · rw [abs_of_nonneg hB]; exact Real.rpow_le_rpow hs.le h1 hB
  · rw [abs_of_neg hB, show s ^ B = (1 / s) ^ (-B) by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 / s), Real.div_rpow zero_le_one hs.le,
        Real.one_rpow, one_div, inv_inv]]
    exact Real.rpow_le_rpow (by positivity) h2 (by linarith)

/-- Heights under `A ∈ SL₂(ℤ)` on `𝒟`: `1/(20E t) ≤ Im(Aw) ≤ 20E t`, `E = (|c|+|d|+1)²`. -/
theorem im_smul_two_sided (A : SL(2, ℤ)) : ∃ E : ℝ, 1 ≤ E ∧ ∀ w ∈ ModularGroup.fd,
    (A • w).im ≤ 20 * E * w.im ∧ 1 / (A • w).im ≤ 20 * E * w.im := by
  set c : ℝ := (A 1 0 : ℝ)
  set d : ℝ := (A 1 1 : ℝ)
  set E := (|c| + |d| + 1) ^ 2
  have hE1 : 1 ≤ E := by
    have : 1 ≤ |c| + |d| + 1 := by linarith [abs_nonneg c, abs_nonneg d]
    nlinarith
  refine ⟨E, hE1, fun w hw => ?_⟩
  have ht := w.im_pos
  have ht2 := SelbergMaassExpDecayCell.one_le_im_of_mem_fd hw
  have hx : |w.re| ≤ 1 / 2 := hw.2
  set t := w.im
  set x := w.re
  set D := Complex.normSq (UpperHalfPlane.denom A w)
  have hD : D = (c * x + d) ^ 2 + (c * t) ^ 2 := by
    simp only [D, UpperHalfPlane.denom, Complex.normSq_apply]
    simp [c, d, x, t]; ring
  have him : (A • w).im = t / D := by rw [ModularGroup.im_smul_eq_div_normSq]
  have hDlow : 1 / 4 ≤ D := by
    by_cases hc : (A 1 0 : ℤ) = 0
    · have hdet := A.2
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      have hd1 : (A 1 1 : ℤ) = 1 ∨ (A 1 1 : ℤ) = -1 :=
        Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
      have hc' : c = 0 := by simp [c, hc]
      have hd2 : d ^ 2 = 1 := by rcases hd1 with h | h <;> simp [d, h]
      rw [hD, hc']; nlinarith
    · have hc1 : 1 ≤ c ^ 2 := by
        have : (1 : ℤ) ≤ (A 1 0) ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs (A 1 0)]
        simp only [c]; exact_mod_cast this
      have e2 : t ^ 2 ≤ c ^ 2 * t ^ 2 := by nlinarith [sq_nonneg t]
      have e3 : 1 / 4 ≤ t ^ 2 := by nlinarith
      rw [hD]; nlinarith [sq_nonneg (c * x + d)]
  have hDpos : 0 < D := by linarith
  have hDup : D ≤ E * (1 + t ^ 2) := by
    rw [hD]
    have h1 : |c * x + d| ≤ |c| + |d| := by
      calc |c * x + d| ≤ |c * x| + |d| := abs_add_le _ _
        _ = |c| * |x| + |d| := by rw [abs_mul]
        _ ≤ |c| * 1 + |d| := by gcongr; linarith
        _ = |c| + |d| := by ring
    have h2 : (c * x + d) ^ 2 ≤ E := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg c]) 2
    have h3 : (c * t) ^ 2 ≤ E * t ^ 2 := by
      rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg d]) 2
    nlinarith
  have hED : 1 / 4 ≤ E * D := by nlinarith
  have ht1 : 1 + t ^ 2 ≤ 5 * t ^ 2 := by nlinarith
  constructor
  · rw [him, div_le_iff₀ hDpos]; nlinarith
  · rw [him, one_div_div, div_le_iff₀ ht]
    nlinarith

variable {N f} in
/-- **Rapid decay of the translates of `G` on `𝒟`**: every translate `G(A w)`, weighted by any power
`Im(Aw)^{±B}`, is integrable on the modular fundamental domain. -/
theorem Gsh_hdec (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (B : ℝ) (A : SL(2, ℤ)) :
    IntegrableOn (fun w : ℍ => ‖Gsh N f (A • w)‖ * ((A • w).im ^ B + (A • w).im ^ (-B)))
      ModularGroup.fd := by
  open GaloisForLFunctions.RHTower.SelbergPoincareIntegrability in
  obtain ⟨E, hE1, hE⟩ := im_smul_two_sided A
  obtain ⟨C, c, t₀, hC0, hc, ht₀, hdecay⟩ := f_four_decay (f := f) hτ0 hτ1 A
  obtain ⟨Bf, hBf⟩ := gz_bounded f
  set K : ℝ := max C (max Bf 0 * Real.exp (c * t₀))
  have hK0 : 0 ≤ K := le_max_of_le_left hC0
  set m : ℝ := |B| + 2
  have hm : 1 < m := by simp only [m]; linarith [abs_nonneg B]
  have hmaj := (SelbergMaassExpDecayCell.maj_integrableOn_fd (σ := m) hm hc).norm.const_mul
    (4 * K * (20 * E) ^ m)
  refine hmaj.mono' ?_ (ae_restrict_of_forall_mem ModularGroup.isClosed_fd.measurableSet fun w hw => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hs : Continuous fun w : ℍ => A • w := continuous_smul_sl A
    have him : Continuous fun w : ℍ => (A • w).im := UpperHalfPlane.continuous_im.comp hs
    exact ((continuous_Gsh N f).comp hs).norm.mul
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
  -- the three factors
  have hpow : s ^ B + s ^ (-B) ≤ 2 * L ^ |B| := by
    have := rpow_le_of_mem (B := B) hs hs1 hs2
    have := rpow_le_of_mem (B := -B) hs hs1 hs2
    rw [abs_neg] at this
    linarith
  have hθ : ‖theta ((A • w : ℍ) : ℂ)‖ ≤ 2 * L := by
    have h := norm_theta_le (v := ((A • w : ℍ) : ℂ)) hs
    have h1 : 1 / (π * s) ≤ L := by
      have : 1 / (π * s) ≤ 1 / s := by
        apply one_div_le_one_div_of_le hs; nlinarith [Real.pi_gt_three]
      linarith
    change ‖theta ((A • w : ℍ) : ℂ)‖ ≤ 2 * L
    have : ((A • w : ℍ) : ℂ).im = s := rfl
    rw [this] at h
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
  have hG : ‖Gsh N f (A • w)‖ ≤ K * Real.exp (-c * t) * (2 * L) * L := by
    unfold Gsh
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul hf hθ (norm_nonneg _) (by positivity)) hy (by positivity) (by positivity)
  have hmajw : ‖maj m c w‖ = t ^ m * Real.exp (-c * t) := by
    unfold maj
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hmajw]
  have hLm : L ^ |B| * L * L = (20 * E) ^ m * t ^ m := by
    rw [← Real.mul_rpow (by positivity) ht.le]
    simp only [L, m]
    rw [Real.rpow_add (by positivity), Real.rpow_two]
    ring
  calc ‖Gsh N f (A • w)‖ * (s ^ B + s ^ (-B))
      ≤ (K * Real.exp (-c * t) * (2 * L) * L) * (2 * L ^ |B|) :=
        mul_le_mul hG hpow (by positivity) (by positivity)
    _ = 4 * K * (L ^ |B| * L * L) * Real.exp (-c * t) := by ring
    _ = 4 * K * (20 * E) ^ m * (t ^ m * Real.exp (-c * t)) := by rw [hLm]; ring
