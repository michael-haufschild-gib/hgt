import GaloisForLFunctions.RHTower.HalfWeightEisenstein
import GaloisForLFunctions.RHTower.HalfWeightKernel
import GaloisForLFunctions.RHTower.SelbergPoincareFourier

/-!
# Fourier–Kloosterman expansion of the weight-½ Eisenstein series

For `γ ∈ Γ₀(4)` with `c > 0`, `J_mul_gauss` turns `\overline{j(γ,z)} Im(γz)^w` into
`C(c,d) c^{-2w} kerH_{y,w}(x + d/c)` with the unimodular `C(c,d) = c√2/(\overline{G(-d;c)}
\overline{(ic)^{1/2}})` (`star_jU_mul_im_cpow`, via the phase identity `conj_cpow_half_div`);
`c = 0` gives `j = 1`, `Im = y` and `c < 0` reduces to `-γ`.

* `eTerm_eq_Fp`, `range_botP`: cosets `⟨T⟩\Γ₀(4M)` ↔ rows `(c,d)` with `4M ∣ c`, `(c,d) = 1`, and
  the summand is an explicit function `Fp(c,d)`.
* `rowR_zero`: the row `c = 0` is `(1 + ψ̄(-1)) y^w`.
* `rowR_ne_zero`: splitting `d` modulo `|c|` (periodicity of `ψ`, `G(-d;c)`, coprimality) and
  Poisson summation (`tsum_kerH_eq_tsum_fourier`) give
  `|c|^{-2w} Σ_n 𝓕kerH_{y,w}(n) e(nx) klH(n,c)` with
  `klH(n,c) = Σ_{r mod |c|, (c,r)=1} ψ̄(r) C(|c|, sgn(c) r) e(nr/c)`.
* `eisHalf_eq_fourier`: for `Re w > 1`,
  `E(z,w;ψ) = (1 + ψ̄(-1)) y^w + Σ_{c ≠ 0, 4M ∣ c} |c|^{-2w} Σ_n 𝓕kerH_{y,w}(n) e(nx) klH(n,c)`.
-/

open Complex Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

/-! ### The phase of a square root -/

theorem conj_cpow_half_div {ζ : ℂ} (hζ : 0 < ζ.im) :
    starRingEnd ℂ (ζ ^ (1 / 2 : ℂ)) / ((‖ζ‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
      cexp (-(I / 2) * ((Complex.log ζ).im : ℂ)) := by
  have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζ
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  rw [Complex.cpow_def_of_ne_zero hζ0, ← Complex.exp_conj]
  have hr : ((‖ζ‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) = cexp ((Real.log ‖ζ‖ : ℂ) / 2) := by
    rw [Real.rpow_def_of_pos hn, Complex.ofReal_exp]; push_cast; ring_nf
  rw [hr, ← Complex.exp_sub]
  congr 1
  have hlog : Complex.log ζ = (Real.log ‖ζ‖ : ℂ) + ((Complex.log ζ).im : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.log_re]
  have hconj : starRingEnd ℂ (Complex.log ζ) =
      (Real.log ‖ζ‖ : ℂ) - ((Complex.log ζ).im : ℂ) * I := by
    conv_lhs => rw [hlog]
    simp [Complex.conj_ofReal]
    ring
  rw [map_mul, hconj]
  have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [h2]
  ring

/-! ### The Eisenstein summand through the kernel -/

/-- The unimodular coefficient `C(c,d) = c√2 / (\overline{G(-d;c)} \overline{(ic)^{1/2}})`. -/
noncomputable def Ccoef (c : ℕ) (d : ℤ) : ℂ :=
  (c * Real.sqrt 2 : ℂ) / (starRingEnd ℂ (gaussQ (-d) c) * starRingEnd ℂ ((I * c) ^ (1 / 2 : ℂ)))

theorem gaussQ_ne_zero_of {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) {c : ℕ} [NeZero c]
    (hcγ : ent γ 1 0 = c) : gaussQ (-ent γ 1 1) c ≠ 0 := by
  intro h0
  have h := J_mul_gauss hγ hcγ UpperHalfPlane.I
  rw [h0, zero_mul, mul_zero] at h
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  have hden : ((c : ℂ) * (UpperHalfPlane.I : ℂ) + ent γ 1 1) ≠ 0 := by
    intro h1
    have := congrArg Complex.im h1
    simp at this
    exact (NeZero.ne c) this
  have hp : ((c : ℂ) * (UpperHalfPlane.I : ℂ) + ent γ 1 1) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl hden
  exact (mul_ne_zero (mul_ne_zero hc hs) hp) h.symm

/-- The value of `\overline{j(γ,z)} Im(γz)^w` for `c > 0` through the kernel `kerH`. -/
theorem star_jU_mul_im_cpow {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) {c : ℕ} [NeZero c]
    (hcγ : ent γ 1 0 = c) (w : ℂ) (z : UpperHalfPlane) :
    starRingEnd ℂ (jU γ z) * (((γ • z).im : ℝ) : ℂ) ^ w =
      Ccoef c (ent γ 1 1) * (c : ℂ) ^ (-2 * w) *
        kerH z.im w (z.re + (ent γ 1 1 : ℝ) / c) := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne c))
  have hc : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne c)
  set d := ent γ 1 1 with hd
  set t : ℝ := z.re + (d : ℝ) / c with ht
  set ζ : ℂ := wz z.im t with hζ
  have hζim : 0 < ζ.im := by rw [hζ, wz_im]; exact z.im_pos
  have hζ0 : ζ ≠ 0 := fun h => by rw [h] at hζim; simp at hζim
  have hzc : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im (z : ℂ)]
    rfl
  have hden : (c : ℂ) * z + d = ζ * (c : ℝ) := by
    rw [hζ, hzc]; unfold wz; rw [ht]; push_cast; field_simp; ring
  -- the multiplier
  have hG0 := gaussQ_ne_zero_of hγ hcγ
  have hIc0 : (I * c) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]; exact Or.inl (mul_ne_zero I_ne_zero hc)
  have hJ := J_mul_gauss hγ hcγ z
  have hJeq : J γ z = (c * Real.sqrt 2 : ℂ) * ((c : ℂ) * z + d) ^ (1 / 2 : ℂ) /
      (gaussQ (-d) c * (I * c) ^ (1 / 2 : ℂ)) := by
    rw [eq_div_iff (mul_ne_zero hG0 hIc0)]; exact hJ
  have hJn : ‖J γ z‖ = ‖(c : ℂ) * z + d‖ ^ (1 / 2 : ℝ) := by
    have h := norm_sq_J hγ z
    rw [denom_ent, hcγ] at h
    push_cast at h
    rw [← Real.sqrt_eq_rpow, ← h, Real.sqrt_sq (norm_nonneg _)]
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  have hnpos : 0 < ‖(c : ℂ) * z + d‖ := by rw [hden, norm_mul]; simp [hζ0, hcR]
  have hjU : starRingEnd ℂ (jU γ z) = Ccoef c d *
      (starRingEnd ℂ (((c : ℂ) * z + d) ^ (1 / 2 : ℂ)) /
        ((‖(c : ℂ) * z + d‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
    rw [jU, hJn, hJeq, Ccoef]
    simp only [map_div₀, map_mul, Complex.conj_ofReal, map_natCast]
    have h3 : starRingEnd ℂ (gaussQ (-d) c) ≠ 0 := by rwa [map_ne_zero]
    have h4 : starRingEnd ℂ ((I * c) ^ (1 / 2 : ℂ)) ≠ 0 := by rwa [map_ne_zero]
    have h5 : ((‖(c : ℂ) * z + d‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hnpos _).ne'
    field_simp
  -- the phase of `(cz+d)^{1/2}`
  have hcpow : ((c : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (((c : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hcR.le]; push_cast; ring_nf
  have hph : starRingEnd ℂ (((c : ℂ) * z + d) ^ (1 / 2 : ℂ)) /
      ((‖(c : ℂ) * z + d‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) = cexp (-(I / 2) * ((Complex.log ζ).im : ℂ)) := by
    rw [hden, cpow_mul_ofReal_pos hζ0 hcR, map_mul, hcpow, Complex.conj_ofReal, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcR, Real.mul_rpow (norm_nonneg _) hcR.le,
      ← conj_cpow_half_div hζim]
    have h6 : (((c : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hcR _).ne'
    push_cast
    field_simp
  -- the height
  have hwt : wt z.im t = (‖ζ‖ ^ 2)⁻¹ * z.im := by
    unfold wt; rw [← Complex.normSq_eq_norm_sq, hζ, normSq_wz]; ring
  have him : (γ • z).im = wt z.im t * ((c : ℝ) ^ 2)⁻¹ := by
    rw [ModularGroup.im_smul_eq_div_normSq, denom_ent, hcγ]
    push_cast
    rw [hden, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcR, hwt]
    field_simp
  have hwtpos : 0 < wt z.im t := wt_pos z.im_pos t
  have hIm : (((γ • z).im : ℝ) : ℂ) ^ w =
      (c : ℂ) ^ (-2 * w) * cexp (w * (Real.log (wt z.im t) : ℂ)) := by
    rw [him, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hwtpos.le (by positivity),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hwtpos.ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : ((c : ℝ) ^ 2)⁻¹ ≠ 0)),
      Complex.cpow_def_of_ne_zero hc, ← Complex.ofReal_log hwtpos.le,
      ← Complex.ofReal_log (by positivity), Real.log_inv, Real.log_pow,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log hcR.le]
    rw [mul_comm, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hjU, hph, hIm]
  unfold kerH argW
  rw [← hζ]
  rw [show w * (Real.log (wt z.im t) : ℂ) - I / 2 * ((Complex.log ζ).im : ℂ) =
      -(I / 2) * ((Complex.log ζ).im : ℂ) + w * (Real.log (wt z.im t) : ℂ) by ring,
    Complex.exp_add]
  ring

theorem J_of_c_zero (γ : SL(2, ℤ)) (hc : ent γ 1 0 = 0) (z : UpperHalfPlane) : J γ z = 1 := by
  have hdet := det_entries γ
  rw [hc, mul_zero, sub_zero] at hdet
  have hne := theta_ne_zero' z
  rw [J, coe_smul_ent, hc]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · rw [ha, hd]
    have : ((1 : ℤ) * (z : ℂ) + ent γ 0 1) / (((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ)) =
        (z : ℂ) + ent γ 0 1 := by push_cast; ring
    rw [this, theta_add_int, div_self hne]
  · rw [ha, hd]
    have : (((-1 : ℤ) : ℂ) * (z : ℂ) + ent γ 0 1) / (((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ)) =
        (z : ℂ) + ((-ent γ 0 1 : ℤ) : ℂ) := by push_cast; field_simp; ring
    rw [this, theta_add_int, div_self hne]

theorem jU_of_c_zero (γ : SL(2, ℤ)) (hc : ent γ 1 0 = 0) (z : UpperHalfPlane) : jU γ z = 1 := by
  rw [jU, J_of_c_zero γ hc]; simp

theorem im_smul_of_c_zero (γ : SL(2, ℤ)) (hc : ent γ 1 0 = 0) (z : UpperHalfPlane) :
    (γ • z).im = z.im := by
  have hdet := det_entries γ
  rw [hc, mul_zero, sub_zero] at hdet
  rw [ModularGroup.im_smul_eq_div_normSq, denom_ent, hc]
  have h1 : (ent γ 1 1) ^ 2 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num
  have : Complex.normSq (((0 : ℤ) : ℂ) * z + ent γ 1 1) = 1 := by
    rw [Complex.normSq_apply]; simp
    exact_mod_cast (by nlinarith [h1] : (ent γ 1 1) * ent γ 1 1 = 1)
  rw [this, div_one]

theorem J_neg_eq (γ : SL(2, ℤ)) (z : UpperHalfPlane) : jU (-γ) z = jU γ z := by
  rw [jU, jU, J_neg]

theorem ent_neg (γ : SL(2, ℤ)) (i j : Fin 2) : ent (-γ) i j = -ent γ i j := by
  simp [ent]

/-! ### Cosets and coprime pairs -/

variable (M : ℕ)

/-- The admissible bottom rows `(c, d)`: `4M ∣ c`, `(c, d) = 1`. -/
def adm4 : Set (ℤ × ℤ) := {p | (4 * M : ℤ) ∣ p.1 ∧ IsCoprime p.1 p.2}

/-- The bottom row of a coset. -/
noncomputable def botP (q : CosetsT M) : ℤ × ℤ :=
  (ent (Quotient.out q : Gamma0 (4 * M)) 1 0, ent (Quotient.out q : Gamma0 (4 * M)) 1 1)

theorem botP_injective : Function.Injective (botP M) := by
  intro q q' h
  apply bottomT_injective M
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  simp only [botP] at h0 h1
  ext i; fin_cases i <;> simp [bottomT, h0, h1]

theorem dvd_c_of_mem (γ : Gamma0 (4 * M)) : (4 * M : ℤ) ∣ ent γ 1 0 := by
  have := c_zmod_eq_zero M γ
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ (4 * M)).1 this

theorem isCoprime_cd (γ : SL(2, ℤ)) : IsCoprime (ent γ 1 0) (ent γ 1 1) :=
  ⟨-ent γ 0 1, ent γ 0 0, by linarith [det_entries γ]⟩

theorem botP_mk (γ : Gamma0 (4 * M)) :
    botP M (Quotient.mk _ γ) = (ent γ 1 0, ent γ 1 1) := by
  have hrel : QuotientGroup.rightRel (HinfT M) (Quotient.out (Quotient.mk _ γ : CosetsT M)) γ :=
    Quotient.exact (Quotient.out_eq _)
  rw [QuotientGroup.rightRel_apply] at hrel
  obtain ⟨k, hk⟩ := mem_HinfT M hrel
  set γ' := (Quotient.out (Quotient.mk _ γ : CosetsT M) : Gamma0 (4 * M))
  have hγ : (γ : SL(2, ℤ)) = T ^ k * (γ' : SL(2, ℤ)) := by
    rw [← hk]; simp
  simp only [botP]
  rw [hγ, ent_T_zpow_mul_10, ent_T_zpow_mul_11]

theorem range_botP : Set.range (botP M) = adm4 M := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨dvd_c_of_mem M _, isCoprime_cd _⟩
  · rintro ⟨h4, hcop⟩
    obtain ⟨γ, hc, hd⟩ := exists_sl_bottom_row hcop
    have hγ : γ ∈ Gamma0 (4 * M) := by
      rw [Gamma0_mem]
      have : (4 * M : ℤ) ∣ ent γ 1 0 := hc ▸ h4
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ (4 * M)).2 this
    refine ⟨Quotient.mk _ ⟨γ, hγ⟩, ?_⟩
    rw [botP_mk]
    exact Prod.ext hc hd

variable (ψ : DirichletCharacter ℂ (4 * M))

/-- The Eisenstein summand as a function of the bottom row. -/
noncomputable def Fp (w : ℂ) (z : UpperHalfPlane) (p : ℤ × ℤ) : ℂ :=
  starRingEnd ℂ (ψ (p.2 : ZMod (4 * M))) *
    (if p.1 = 0 then ((z.im : ℝ) : ℂ) ^ w
     else Ccoef p.1.natAbs (p.1.sign * p.2) * (p.1.natAbs : ℂ) ^ (-2 * w) *
       kerH z.im w (z.re + (p.2 : ℝ) / p.1))

theorem eTerm_eq_Fp (w : ℂ) (z : UpperHalfPlane) (γ : Gamma0 (4 * M)) :
    eTerm M ψ w z γ = Fp M ψ w z (ent γ 1 0, ent γ 1 1) := by
  unfold eTerm Fp
  rw [mul_assoc]
  congr 1
  have hγ4 : (γ : SL(2, ℤ)) ∈ Gamma0 4 := Gamma0_4M_le M γ.2
  by_cases hc : ent γ 1 0 = 0
  · simp only [hc, if_true]
    rw [jU_of_c_zero _ hc, im_smul_of_c_zero _ hc]
    simp
  · simp only [hc, if_false]
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · -- `c < 0`: pass to `-γ`
      have hn : 0 < ent (-(γ : SL(2, ℤ))) 1 0 := by rw [ent_neg]; linarith
      have hm4 : -(γ : SL(2, ℤ)) ∈ Gamma0 4 := by
        have h4 := hγ4
        rw [Gamma0_mem] at h4 ⊢
        have : ((-(γ : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
            -((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by simp
        rw [this]; push_cast; rw [h4]; simp
      haveI : NeZero (ent γ 1 0).natAbs := ⟨by simpa using hc⟩
      have hcγ : ent (-(γ : SL(2, ℤ))) 1 0 = ((ent γ 1 0).natAbs : ℤ) := by
        rw [ent_neg]; omega
      have h := star_jU_mul_im_cpow hm4 hcγ w z
      rw [J_neg_eq, ModularGroup.SL_neg_smul, ent_neg] at h
      rw [h, Int.sign_eq_neg_one_of_neg hneg]
      congr 2
      · ring_nf
      · congr 1
        have hcR : ((ent γ 1 0).natAbs : ℝ) = -(ent γ 1 0 : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
        rw [hcR]; push_cast; ring
    · -- `c > 0`
      haveI : NeZero (ent γ 1 0).natAbs := ⟨by simpa using hc⟩
      have hcγ : ent (γ : SL(2, ℤ)) 1 0 = ((ent γ 1 0).natAbs : ℤ) := by omega
      have h := star_jU_mul_im_cpow hγ4 hcγ w z
      rw [h, Int.sign_eq_one_of_pos hpos, one_mul]
      congr 2
      have hcR : ((ent γ 1 0).natAbs : ℝ) = (ent γ 1 0 : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
      rw [hcR]

theorem eTermQ_eq_Fp (w : ℂ) (z : UpperHalfPlane) (q : CosetsT M) :
    eTermQ M ψ w z q = Fp M ψ w z (botP M q) := by
  have hq : eTermQ M ψ w z q = eTerm M ψ w z (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, eTerm_eq_Fp]
  rfl

/-- `E` as a sum over all pairs, weighted by the indicator of the admissible rows. -/
theorem eisHalf_eq_tsum_indicator (w : ℂ) (z : UpperHalfPlane) :
    eisHalf M ψ w z = ∑' p : ℤ × ℤ, (adm4 M).indicator (Fp M ψ w z) p := by
  unfold eisHalf
  rw [tsum_congr (eTermQ_eq_Fp M ψ w z)]
  rw [← tsum_range (Fp M ψ w z) (botP_injective M)]
  rw [tsum_subtype (Set.range (botP M)) (Fp M ψ w z)]
  rw [range_botP]

theorem summable_indicator {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    Summable fun p : ℤ × ℤ => ‖(adm4 M).indicator (Fp M ψ w z) p‖ := by
  have h2 : Summable fun q : CosetsT M => ‖Fp M ψ w z (botP M q)‖ :=
    (summable_eTermQ M ψ hw z).congr fun q => by rw [eTermQ_eq_Fp]
  have h3 : Summable fun x : Set.range (botP M) => ‖Fp M ψ w z x‖ :=
    (Equiv.ofInjective (botP M) (botP_injective M)).summable_iff.1 h2
  have h4 := (summable_subtype_iff_indicator (s := Set.range (botP M))
    (f := fun p => ‖Fp M ψ w z p‖)).1 h3
  rw [range_botP] at h4
  refine h4.congr fun p => ?_
  rw [norm_indicator_eq_indicator_norm]

/-! ### Rows -/

/-- The row `c` of the Eisenstein series. -/
noncomputable def rowR (w : ℂ) (z : UpperHalfPlane) (c : ℤ) : ℂ :=
  ∑' d : ℤ, (adm4 M).indicator (Fp M ψ w z) (c, d)

theorem eisHalf_eq_tsum_rows {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisHalf M ψ w z = ∑' c : ℤ, rowR M ψ w z c := by
  rw [eisHalf_eq_tsum_indicator]
  have hs := (summable_indicator M ψ hw z).of_norm
  exact hs.tsum_prod' (fun c => hs.prod_factor c)

theorem mem_adm4_zero_iff (d : ℤ) : ((0 : ℤ), d) ∈ adm4 M ↔ d = 1 ∨ d = -1 := by
  simp only [adm4, Set.mem_setOf_eq, dvd_zero, true_and, isCoprime_zero_left, Int.isUnit_iff]

/-- The row `c = 0`: `(1 + ψ̄(-1)) y^w`. -/
theorem rowR_zero (w : ℂ) (z : UpperHalfPlane) :
    rowR M ψ w z 0 = (1 + starRingEnd ℂ (ψ (-1))) * ((z.im : ℝ) : ℂ) ^ w := by
  unfold rowR
  rw [tsum_eq_sum (s := {1, -1}) (fun d hd => by
    rw [Set.indicator_of_notMem]
    rw [mem_adm4_zero_iff]
    simpa using hd)]
  rw [Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1)]
  rw [Set.indicator_of_mem ((mem_adm4_zero_iff M 1).2 (Or.inl rfl)),
    Set.indicator_of_mem ((mem_adm4_zero_iff M (-1)).2 (Or.inr rfl))]
  simp only [Fp, if_true]
  push_cast
  rw [map_one, map_one]
  ring

/-! ### Periodicity in `d` -/

theorem gaussQ_add_mul (a : ℤ) (c : ℕ) (k : ℤ) : gaussQ (a + c * k) c = gaussQ a c := by
  unfold gaussQ
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hc : (c : ℂ) = 0
  · simp [hc]
  rw [show 2 * π * I * (((a + c * k : ℤ) : ℂ) * ((r : ℕ) : ℂ) ^ 2 / c) =
      2 * π * I * (a * ((r : ℕ) : ℂ) ^ 2 / c) + ((k * (r : ℕ) ^ 2 : ℤ) : ℂ) * (2 * π * I) by
      push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Ccoef_add_mul (c : ℕ) (d k : ℤ) : Ccoef c (d + c * k) = Ccoef c d := by
  unfold Ccoef
  rw [show -(d + c * k) = -d + c * (-k) by ring, gaussQ_add_mul]

theorem psi_add_mul {c : ℤ} (hc : (4 * M : ℤ) ∣ c) (d k : ℤ) :
    ψ ((d + c * k : ℤ) : ZMod (4 * M)) = ψ (d : ZMod (4 * M)) := by
  congr 1
  push_cast
  have : ((c : ℤ) : ZMod (4 * M)) = 0 := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd c (4 * M)).2 (by exact_mod_cast hc)
  rw [this, zero_mul, add_zero]

/-! ### Fourier summability of the kernel -/

theorem summable_norm_fourier_kerH {y : ℝ} {s : ℂ} (hy : 0 < y) (hs : 1 / 2 < s.re) :
    Summable (fun n : ℤ => ‖FourierTransform.fourier (kerH y s) n‖) := by
  set C := dconstH y s * (y ^ (1 - s.re) * cst s.re) / (2 * Real.pi) ^ 2
  have hsum : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) hsum ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_le] at hn
  by_contra h0
  apply hn.not_ge
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0
  have h := norm_fourier_kerH_le_sq hy hs n
  rw [norm_norm]
  have hpos : 0 < (2 * Real.pi * |(n : ℝ)|) ^ 2 := by positivity
  rw [show C * (1 / (n : ℝ) ^ 2) = dconstH y s * (y ^ (1 - s.re) * cst s.re) /
      (2 * Real.pi * |(n : ℝ)|) ^ 2 by
    simp only [C]; rw [mul_pow, mul_pow, sq_abs]; field_simp]
  rw [le_div_iff₀ hpos, mul_comm]
  exact h

/-! ### The rows `c ≠ 0` -/

/-- The weight-½ Kloosterman-type sum `Σ_{r mod |c|, (c,r)=1} ψ̄(r) C(|c|, sgn(c) r) e(nr/c)`. -/
noncomputable def klH (n c : ℤ) : ℂ :=
  ∑ r ∈ Finset.range c.natAbs, if IsCoprime c (r : ℤ) then
    starRingEnd ℂ (ψ ((r : ℤ) : ZMod (4 * M))) * Ccoef c.natAbs (c.sign * r) *
      cexp (2 * π * I * n * (r : ℂ) / c) else 0

theorem natAbs_eq_mul_sign (c : ℤ) : (c.natAbs : ℤ) = c * c.sign := by
  rcases lt_trichotomy c 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; omega
  · subst h; simp
  · rw [Int.sign_eq_one_of_pos h]; omega

theorem G_residue {w : ℂ} (z : UpperHalfPlane) {c : ℤ} (hc : c ≠ 0) (h4 : (4 * M : ℤ) ∣ c)
    (r j : ℤ) :
    (adm4 M).indicator (Fp M ψ w z) (c, r + c.natAbs * j) =
      if IsCoprime c r then starRingEnd ℂ (ψ (r : ZMod (4 * M))) * Ccoef c.natAbs (c.sign * r) *
        (c.natAbs : ℂ) ^ (-2 * w) * kerH z.im w ((z.re + (r : ℝ) / c) + c.sign * j) else 0 := by
  have hK : (c.natAbs : ℤ) * j = c * (c.sign * j) := by rw [natAbs_eq_mul_sign]; ring
  have hmem : (c, r + c.natAbs * j) ∈ adm4 M ↔ IsCoprime c r := by
    simp only [adm4, Set.mem_setOf_eq, h4, true_and]
    rw [hK]; exact IsCoprime.add_mul_left_right_iff
  by_cases hcop : IsCoprime c r
  · rw [Set.indicator_of_mem (hmem.2 hcop), if_pos hcop]
    simp only [Fp, hc, if_false]
    rw [hK, psi_add_mul M ψ h4]
    have hC : c.sign * (r + c * (c.sign * j)) = c.sign * r + c.natAbs * (c.sign * j) := by
      rw [natAbs_eq_mul_sign]; ring_nf
    rw [hC, Ccoef_add_mul]
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hx : z.re + ((r + c * (c.sign * j) : ℤ) : ℝ) / c = (z.re + (r : ℝ) / c) + c.sign * j := by
      push_cast; field_simp; ring
    rw [hx]
    ring
  · rw [Set.indicator_of_notMem (fun h => hcop (hmem.1 h)), if_neg hcop]

theorem norm_cexp_two_pi_I_mul (t : ℝ) : ‖cexp (2 * π * I * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Poisson summation along one residue class. -/
theorem tsum_kerH_sign {w : ℂ} (hw : 3 / 4 ≤ w.re) {y : ℝ} (hy : 0 < y) {c : ℤ} (hc : c ≠ 0)
    (t : ℝ) :
    ∑' j : ℤ, kerH y w (t + c.sign * j) =
      ∑' n : ℤ, FourierTransform.fourier (kerH y w) n * cexp (2 * π * I * n * t) := by
  have h1 := SelbergPoincareFourier.tsum_sign hc (fun j : ℤ => kerH y w (t + j))
  simp only [Int.cast_mul] at h1
  rw [h1, tsum_kerH_eq_tsum_fourier hy hw t]
  refine tsum_congr fun n => ?_
  rw [fourier_coe_apply]
  congr 2
  push_cast; ring

/-- **The row `c ≠ 0`** of the weight-½ Eisenstein series:
`|c|^{-2w} Σ_n 𝓕kerH_{y,w}(n) e(nx) klH(n, c)`. -/
theorem rowR_ne_zero {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) {c : ℤ} (hc : c ≠ 0)
    (h4 : (4 * M : ℤ) ∣ c) :
    rowR M ψ w z c = (c.natAbs : ℂ) ^ (-2 * w) *
      ∑' n : ℤ, FourierTransform.fourier (kerH z.im w) n * cexp (2 * π * I * n * z.re) *
        klH M ψ n c := by
  have hw34 : 3 / 4 ≤ w.re := by linarith
  have hw12 : 1 / 2 < w.re := by linarith
  unfold rowR
  have hG : Summable fun d : ℤ => (adm4 M).indicator (Fp M ψ w z) (c, d) :=
    ((summable_indicator M ψ hw z).of_norm).prod_factor c
  rw [SelbergPoincareFourier.tsum_eq_sum_residues hG c.natAbs (Int.natAbs_pos.2 hc)]
  have hF := summable_norm_fourier_kerH z.im_pos hw12
  -- each residue class
  have hres : ∀ r ∈ Finset.range c.natAbs,
      ∑' j : ℤ, (adm4 M).indicator (Fp M ψ w z) (c, (r : ℤ) + (c.natAbs : ℤ) * j) =
        ∑' n : ℤ, (if IsCoprime c (r : ℤ) then
          starRingEnd ℂ (ψ ((r : ℤ) : ZMod (4 * M))) * Ccoef c.natAbs (c.sign * r) *
            (c.natAbs : ℂ) ^ (-2 * w) * (FourierTransform.fourier (kerH z.im w) n *
              cexp (2 * π * I * n * (z.re + ((r : ℤ) : ℝ) / c))) else 0) := by
    intro r _
    simp_rw [G_residue M ψ z hc h4]
    by_cases hcop : IsCoprime c (r : ℤ)
    · simp only [if_pos hcop]
      rw [tsum_mul_left, tsum_mul_left, tsum_kerH_sign hw34 z.im_pos hc]
      congr 1
      refine tsum_congr fun n => ?_
      push_cast
      ring
    · simp only [if_neg hcop, tsum_zero]
  rw [Finset.sum_congr rfl hres]
  have hsr : ∀ r ∈ Finset.range c.natAbs, Summable fun n : ℤ => (if IsCoprime c (r : ℤ) then
      starRingEnd ℂ (ψ ((r : ℤ) : ZMod (4 * M))) * Ccoef c.natAbs (c.sign * r) *
        (c.natAbs : ℂ) ^ (-2 * w) * (FourierTransform.fourier (kerH z.im w) n *
          cexp (2 * π * I * n * (z.re + ((r : ℤ) : ℝ) / c))) else 0) := by
    intro r _
    by_cases hcop : IsCoprime c (r : ℤ)
    · simp only [if_pos hcop]
      refine Summable.mul_left _ (Summable.of_norm ?_)
      refine hF.congr fun n => ?_
      rw [norm_mul, show (2 * π * I * n * (z.re + ((r : ℤ) : ℝ) / c) : ℂ) =
        2 * π * I * (((n : ℝ) * (z.re + ((r : ℤ) : ℝ) / c) : ℝ) : ℂ) by push_cast; ring,
        norm_cexp_two_pi_I_mul, mul_one]
    · simp only [if_neg hcop]; exact summable_zero
  rw [← Summable.tsum_finsetSum hsr, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold klH
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hcop : IsCoprime c (r : ℤ)
  · simp only [if_pos hcop]
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [show (2 * π * I * n * (z.re + ((r : ℤ) : ℝ) / c) : ℂ) =
        2 * π * I * n * z.re + 2 * π * I * n * (r : ℂ) / c by push_cast; field_simp,
      Complex.exp_add]
    ring
  · simp only [if_neg hcop, mul_zero]

theorem rowR_of_not_dvd (w : ℂ) (z : UpperHalfPlane) {c : ℤ} (h4 : ¬ (4 * M : ℤ) ∣ c) :
    rowR M ψ w z c = 0 := by
  unfold rowR
  refine (tsum_congr fun d => ?_).trans tsum_zero
  exact Set.indicator_of_notMem (fun h => h4 h.1) _

/-- The `c`-th term of the Fourier–Kloosterman expansion. -/
noncomputable def cTerm (w : ℂ) (z : UpperHalfPlane) (c : ℤ) : ℂ :=
  if c ≠ 0 ∧ (4 * M : ℤ) ∣ c then
    (c.natAbs : ℂ) ^ (-2 * w) * ∑' n : ℤ, FourierTransform.fourier (kerH z.im w) n *
      cexp (2 * π * I * n * z.re) * klH M ψ n c
  else 0

/-- **Fourier–Kloosterman expansion of the weight-½ Eisenstein series** (`Re w > 1`):
`E(z,w;ψ) = (1 + ψ̄(-1)) y^w + Σ_{c ≠ 0, 4M ∣ c} |c|^{-2w} Σ_n 𝓕kerH_{y,w}(n) e(nx) klH(n,c)`. -/
theorem eisHalf_eq_fourier {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisHalf M ψ w z = (1 + starRingEnd ℂ (ψ (-1))) * ((z.im : ℝ) : ℂ) ^ w +
      ∑' c : ℤ, cTerm M ψ w z c := by
  rw [eisHalf_eq_tsum_rows M ψ hw z]
  have hs := (summable_indicator M ψ hw z).of_norm
  have hrow : Summable (rowR M ψ w z) := hs.prod
  rw [hrow.tsum_eq_add_tsum_ite 0, rowR_zero]
  congr 1
  refine tsum_congr fun c => ?_
  unfold cTerm
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc]
    by_cases h4 : (4 * M : ℤ) ∣ c
    · rw [if_pos ⟨hc, h4⟩, rowR_ne_zero M ψ hw z hc h4]
    · rw [if_neg (fun h => h4 h.2), rowR_of_not_dvd M ψ w z h4]

end GaloisForLFunctions.RHTower.HalfWeight
