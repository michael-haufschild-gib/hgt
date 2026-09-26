import GaloisForLFunctions.RHTower.HalfWeightEisensteinCoefficients

/-!
# The dual weight-½ Eisenstein series

For a row weight `κ : ℤ → ℂ` with `|κ| ≤ 1`,
`E_κ(z, w) = Σ_{γ ∈ ⟨T⟩\Γ₀(4M)} κ(c_γ) \overline{j(γ,z)} Im(γz)^w`   (`eisK`)
is the Poincaré series of `Γ₀(4M)` in which the character acts on the lower-left entry `c`
instead of on `d`.

* `eisK_eq_tsum_rows`: `E_κ = Σ_c κ(c) row_c`, with `row_c` the rows of the untwisted series;
  `eisK_smul`: if `κ(c_γ) = μ κ(c_{γδ})` for all `γ`, then `E_κ(δz) = μ j(δ,z) E_κ(z)`.
* `eisK_eq_coeffs`: for `κ(0) = 0`, `κ(-c) = ε κ(c)`, `Re w > 1`:
  `E_κ(z,w) = (1 + ε) Σ_n 𝓕kerH_{y,w}(n) e(nx) D^κ_n(w)`,
  `D^κ_n(w) = Σ_{c ≥ 1, 4M ∣ c} κ(c) c^{-2w} klH(n,c)` (`DserK`, evaluated in `DserK_eq`).

For a character `ψ₀` of prime modulus `q` and `M = M'q`, the weight `κ(c) = ψ₀(c/q)` (`kapQ`)
gives the **dual series** `Ê = eisDual`. It transforms like the series of `ψ₀` at level
`4M'q²`: `Ê(δz, w) = ψ₀(d_δ) j(δ,z) Ê(z, w)` for `δ ∈ Γ₀(4M'q²)` (`eisDual_smul`). It has no `y^w`
term at `∞`. It is the partner of the regularised series `E*_ψ` of Shimura's integral under
`w ↦ 1 - w`, the analogue of the Poisson duality between the Epstein zeta functions
`Σ ψ̄(n)|mq²z + n|^{-2s}` and `Σ ψ(m)|mqz + n|^{-2s}`.
-/

open Complex Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

section RowWeighted

variable (M : ℕ) (κ : ℤ → ℂ)

/-- The row-weighted summand `κ(c) \overline{j(γ,z)} Im(γz)^w`. -/
def eTermK (w : ℂ) (z : UpperHalfPlane) (γ : Gamma0 (4 * M)) : ℂ :=
  κ (ent γ 1 0) * eTerm M 1 w z γ

theorem eTermK_HinfT (w : ℂ) (z : UpperHalfPlane) {h : Gamma0 (4 * M)} (hh : h ∈ HinfT M)
    (γ : Gamma0 (4 * M)) : eTermK M κ w z (h * γ) = eTermK M κ w z γ := by
  obtain ⟨k, hk⟩ := mem_HinfT M hh
  have hc : ((h * γ : Gamma0 (4 * M)) : SL(2, ℤ)) = T ^ k * (γ : SL(2, ℤ)) := by
    rw [Subgroup.coe_mul, hk]
  unfold eTermK
  rw [eTerm_HinfT M 1 w z hh γ, hc, ent_T_zpow_mul_10]

/-- The row-weighted summand on cosets. -/
def eTermKQ (w : ℂ) (z : UpperHalfPlane) : CosetsT M → ℂ :=
  Quotient.lift (eTermK M κ w z) (by
    intro a b hab
    have hmem : b * a⁻¹ ∈ HinfT M := QuotientGroup.rightRel_apply.mp hab
    have := eTermK_HinfT M κ w z hmem a
    rw [inv_mul_cancel_right] at this
    exact this.symm)

/-- **The row-weighted weight-½ Eisenstein series** `Σ_{⟨T⟩\Γ₀(4M)} κ(c) \overline{j(γ,z)} Im(γz)^w`. -/
def eisK (w : ℂ) (z : UpperHalfPlane) : ℂ := ∑' q : CosetsT M, eTermKQ M κ w z q

/-- The weighted summand as a function of the bottom row. -/
def FpK (w : ℂ) (z : UpperHalfPlane) (p : ℤ × ℤ) : ℂ := κ p.1 * Fp M 1 w z p

theorem eTermKQ_eq_FpK (w : ℂ) (z : UpperHalfPlane) (q : CosetsT M) :
    eTermKQ M κ w z q = FpK M κ w z (botP M q) := by
  have hq : eTermKQ M κ w z q = eTermK M κ w z (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, eTermK, eTerm_eq_Fp]
  rfl

theorem summable_eTermKQ (hκ : ∀ c, ‖κ c‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    Summable fun q : CosetsT M => ‖eTermKQ M κ w z q‖ := by
  refine (summable_eTermQ M 1 hw z).of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
  rw [eTermKQ_eq_FpK, eTermQ_eq_Fp, FpK, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hκ _)

theorem eisK_eq_tsum_indicator (w : ℂ) (z : UpperHalfPlane) :
    eisK M κ w z = ∑' p : ℤ × ℤ, (adm4 M).indicator (FpK M κ w z) p := by
  unfold eisK
  rw [tsum_congr (eTermKQ_eq_FpK M κ w z)]
  rw [← tsum_range (FpK M κ w z) (botP_injective M)]
  rw [tsum_subtype (Set.range (botP M)) (FpK M κ w z)]
  rw [range_botP]

theorem summable_indicatorK (hκ : ∀ c, ‖κ c‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    Summable fun p : ℤ × ℤ => ‖(adm4 M).indicator (FpK M κ w z) p‖ := by
  refine (summable_indicator M 1 hw z).of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
  rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
  by_cases h : p ∈ adm4 M
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, FpK, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hκ _)
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

theorem rowK_eq (w : ℂ) (z : UpperHalfPlane) (c : ℤ) :
    ∑' d : ℤ, (adm4 M).indicator (FpK M κ w z) (c, d) = κ c * rowR M 1 w z c := by
  unfold rowR
  rw [← tsum_mul_left]
  refine tsum_congr fun d => ?_
  by_cases h : (c, d) ∈ adm4 M
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, FpK]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- The row decomposition `Σ_c κ(c) row_c`. -/
theorem eisK_eq_tsum_rows (hκ : ∀ c, ‖κ c‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisK M κ w z = ∑' c : ℤ, κ c * rowR M 1 w z c := by
  rw [eisK_eq_tsum_indicator]
  have hs := (summable_indicatorK M κ hκ hw z).of_norm
  rw [hs.tsum_prod' (fun c => hs.prod_factor c)]
  exact tsum_congr fun c => rowK_eq M κ w z c

/-! ### The transformation law -/

theorem one_apply_d (δ : Gamma0 (4 * M)) :
    (1 : DirichletCharacter ℂ (4 * M)) (ent δ 1 1 : ZMod (4 * M)) = 1 :=
  MulChar.one_apply (isUnit_d M δ)

theorem eTermK_smul (w : ℂ) (z : UpperHalfPlane) (γ δ : Gamma0 (4 * M)) (μ : ℂ)
    (hμ : κ (ent γ 1 0) = μ * κ (ent ((γ * δ : Gamma0 (4 * M)) : SL(2, ℤ)) 1 0)) :
    eTermK M κ w ((δ : SL(2, ℤ)) • z) γ = μ * jU δ z * eTermK M κ w z (γ * δ) := by
  unfold eTermK
  rw [eTerm_smul M 1 w z γ δ, hμ, one_apply_d]
  ring

/-- **Automorphy of the row-weighted series**: if `κ(c_γ) = μ κ(c_{γδ})` for every `γ`, then
`E_κ(δz, w) = μ j(δ, z) E_κ(z, w)`. -/
theorem eisK_smul (w : ℂ) (z : UpperHalfPlane) (δ : Gamma0 (4 * M)) (μ : ℂ)
    (hμ : ∀ γ : Gamma0 (4 * M), κ (ent γ 1 0) = μ * κ (ent ((γ * δ : Gamma0 (4 * M)) : SL(2, ℤ)) 1 0)) :
    eisK M κ w ((δ : SL(2, ℤ)) • z) = μ * jU δ z * eisK M κ w z := by
  unfold eisK
  have h : ∀ q : CosetsT M, eTermKQ M κ w ((δ : SL(2, ℤ)) • z) q =
      μ * jU δ z * eTermKQ M κ w z (rightMulT M δ q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h a => exact eTermK_smul M κ w z a δ μ (hμ a)
  rw [tsum_congr h, tsum_mul_left, (rightMulT M δ).tsum_eq (eTermKQ M κ w z)]

/-! ### The positive rows and the coefficient form -/

theorem rowR_one_neg (w : ℂ) (z : UpperHalfPlane) (c : ℤ) :
    rowR M 1 w z (-c) = rowR M 1 w z c := by
  rw [rowR_neg]
  have h : (1 : DirichletCharacter ℂ (4 * M)) (-1) = 1 := MulChar.one_apply isUnit_one.neg
  rw [h, map_one, one_mul]

theorem summable_rowK (hκ : ∀ c, ‖κ c‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    Summable fun c : ℤ => κ c * rowR M 1 w z c := by
  have hs := (summable_indicatorK M κ hκ hw z).of_norm
  exact hs.prod.congr fun c => rowK_eq M κ w z c

/-- For `κ(0) = 0` and `κ(-c) = ε κ(c)`: `E_κ = (1 + ε) Σ_{c ≥ 1} κ(c) row_c`. -/
theorem eisK_eq_pos_rows (hκ : ∀ c, ‖κ c‖ ≤ 1) (h0 : κ 0 = 0) (ε : ℂ)
    (hneg : ∀ c, κ (-c) = ε * κ c) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisK M κ w z = (1 + ε) * ∑' k : ℕ, κ ((k : ℤ) + 1) * rowR M 1 w z ((k : ℤ) + 1) := by
  rw [eisK_eq_tsum_rows M κ hκ hw z]
  set g : ℤ → ℂ := fun c => κ c * rowR M 1 w z c with hg
  have hrow : Summable g := summable_rowK M κ hκ hw z
  have hi1 : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := fun a b h => by simpa using h
  have hi2 : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := fun a b h => by simpa using h
  have h1 := hrow.comp_injective hi1
  have h2 := hrow.comp_injective hi2
  have e := tsum_of_add_one_of_neg_add_one h1 h2
  rw [e]
  have hn : ∀ k : ℕ, g (-((k : ℤ) + 1)) = ε * g ((k : ℤ) + 1) := fun k => by
    simp only [hg]; rw [hneg, rowR_one_neg]; ring
  rw [tsum_congr hn, tsum_mul_left]
  simp only [hg, h0, zero_mul]
  ring

/-- The Dirichlet series of the `n`-th Fourier coefficient of `E_κ`:
`D^κ_n(w) = Σ_{c ≥ 1, 4M ∣ c} κ(c) c^{-2w} klH(n, c)` (trivial nebentypus in `klH`). -/
def DserK (n : ℤ) (w : ℂ) : ℂ :=
  ∑' k : ℕ, if 4 * M ∣ k + 1 then κ ((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℂ) ^ (-2 * w) *
    klH M 1 n ((k + 1 : ℕ) : ℤ) else 0

/-- **The coefficient form of the Fourier expansion of `E_κ`** (`Re w > 1`, `κ(0) = 0`,
`κ(-c) = ε κ(c)`): `E_κ(z,w) = (1 + ε) Σ_n 𝓕kerH_{y,w}(n) e(nx) D^κ_n(w)`; there is no `y^w` term. -/
theorem eisK_eq_coeffs (hκ : ∀ c, ‖κ c‖ ≤ 1) (h0 : κ 0 = 0) (ε : ℂ)
    (hneg : ∀ c, κ (-c) = ε * κ c) {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisK M κ w z = (1 + ε) * ∑' n : ℤ, FourierTransform.fourier (kerH z.im w) n *
      cexp (2 * π * I * n * z.re) * DserK M κ n w := by
  rw [eisK_eq_pos_rows M κ hκ h0 ε hneg hw z]
  congr 1
  set T : ℕ → ℤ → ℂ := fun k n => if 4 * M ∣ k + 1 then κ ((k + 1 : ℕ) : ℤ) *
    (((k + 1 : ℕ) : ℂ) ^ (-2 * w) * (FourierTransform.fourier (kerH z.im w) n *
      cexp (2 * π * I * n * z.re) * klH M 1 n ((k + 1 : ℕ) : ℤ))) else 0 with hT
  have hrow : ∀ k : ℕ, κ ((k : ℤ) + 1) * rowR M 1 w z ((k : ℤ) + 1) = ∑' n : ℤ, T k n := by
    intro k
    have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    by_cases h4 : 4 * M ∣ k + 1
    · have h4' : (4 * M : ℤ) ∣ ((k : ℤ) + 1) := by rw [hk]; exact_mod_cast h4
      rw [rowR_ne_zero M 1 hw z (by omega) h4', hk, Int.natAbs_natCast, ← tsum_mul_left,
        ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      simp only [hT, if_pos h4]
    · have h4' : ¬ (4 * M : ℤ) ∣ ((k : ℤ) + 1) := by rw [hk]; exact_mod_cast h4
      rw [rowR_of_not_dvd M 1 w z h4']
      simp only [hT, if_neg h4, tsum_zero, mul_zero]
  simp_rw [hrow]
  have hF := summable_norm_fourier_kerH z.im_pos (show 1 / 2 < w.re by linarith)
  have hA := summable_shift_rpow hw
  have hbound : ∀ k n, ‖T k n‖ ≤ ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * w.re) *
      ‖FourierTransform.fourier (kerH z.im w) n‖ := by
    intro k n
    simp only [hT]
    split_ifs with h4
    · haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
      have h4' : (4 : ℤ) ∣ ((k + 1 : ℕ) : ℤ) := by
        have : (4 : ℕ) ∣ k + 1 := dvd_trans (dvd_mul_right 4 M) h4
        exact_mod_cast this
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_natCast_cpow]
      have he : ‖cexp (2 * π * I * n * z.re)‖ = 1 := by
        rw [show (2 * π * I * n * z.re : ℂ) = 2 * π * I * (((n : ℝ) * z.re : ℝ) : ℂ) by
          push_cast; ring]
        exact norm_cexp_two_pi_I_mul _
      rw [he, mul_one]
      have hk := norm_klH_le M 1 h4' n
      have hκk := hκ ((k + 1 : ℕ) : ℤ)
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hpow : ((k + 1 : ℕ) : ℝ) ^ (1 - 2 * w.re) =
          ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) * ((k + 1 : ℕ) : ℝ) := by
        rw [show (1 - 2 * w.re) = -2 * w.re + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
      rw [hpow]
      have h0' : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) := by positivity
      have hF0 := norm_nonneg (FourierTransform.fourier (kerH z.im w) n)
      calc ‖κ ((k + 1 : ℕ) : ℤ)‖ * (((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) *
            (‖FourierTransform.fourier (kerH z.im w) n‖ * ‖klH M 1 n ((k + 1 : ℕ) : ℤ)‖))
          ≤ 1 * (((k + 1 : ℕ) : ℝ) ^ (-2 * w.re) *
            (‖FourierTransform.fourier (kerH z.im w) n‖ * ((k + 1 : ℕ) : ℝ))) := by
            gcongr
        _ = _ := by ring
    · simp only [norm_zero]; positivity
  have hprod : Summable fun p : ℕ × ℤ => ((p.1 + 1 : ℕ) : ℝ) ^ (1 - 2 * w.re) *
      ‖FourierTransform.fourier (kerH z.im w) p.2‖ :=
    hA.mul_of_nonneg hF (fun k => by positivity) (fun n => norm_nonneg _)
  have hTs : Summable (Function.uncurry T) :=
    Summable.of_norm_bounded hprod (fun p => hbound p.1 p.2)
  rw [← hTs.tsum_comm' (fun k => hTs.prod_factor k)
    (fun n => (hTs.comp_injective (fun a b h => by simpa using h) :
      Summable fun k => Function.uncurry T (k, n)))]
  refine tsum_congr fun n => ?_
  unfold DserK
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [hT]
  split_ifs <;> ring

/-- With `klH` evaluated (`klH_one_pos`):
`D^κ_n(w) = i^{1/2}/√2 · Σ_{c ≥ 1, 4M ∣ c} κ(c) c^{1/2-2w} Σ_{e ∣ c} μ(e) N_{c/e}(n)`. -/
theorem DserK_eq (n : ℤ) (w : ℂ) :
    DserK M κ n w = I ^ (1 / 2 : ℂ) / Real.sqrt 2 *
      ∑' k : ℕ, if 4 * M ∣ k + 1 then κ ((k + 1 : ℕ) : ℤ) * ((k + 1 : ℕ) : ℂ) ^ (1 / 2 - 2 * w) *
        muN n (k + 1) else 0 := by
  unfold DserK
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  split_ifs with h4
  · haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
    rw [klH_one_pos M h4 n]
    have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hsplit : (I * ((k + 1 : ℕ) : ℂ)) ^ (1 / 2 : ℂ) =
        I ^ (1 / 2 : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (1 / 2 : ℂ) := by
      have := cpow_mul_ofReal_pos (x := I) Complex.I_ne_zero hpos (1 / 2 : ℂ)
      simpa using this
    have hk0 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [hsplit, show (1 / 2 - 2 * w : ℂ) = -2 * w + 1 / 2 by ring, Complex.cpow_add _ _ hk0]
    ring
  · simp

end RowWeighted

section Dual

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q) (M' : ℕ)

/-- The dual row weight `κ(c) = ψ₀(c/q)` for `q ∣ c`, and `0` otherwise. -/
def kapQ (c : ℤ) : ℂ := if (q : ℤ) ∣ c then ψ₀ ((c / q : ℤ) : ZMod q) else 0

theorem norm_kapQ_le (c : ℤ) : ‖kapQ ψ₀ c‖ ≤ 1 := by
  unfold kapQ
  split_ifs
  · exact DirichletCharacter.norm_le_one _ _
  · simp

theorem kapQ_zero : kapQ ψ₀ 0 = 0 := by
  unfold kapQ
  simp only [dvd_zero, if_true, Int.zero_ediv, Int.cast_zero]
  exact MulChar.map_zero ψ₀

theorem kapQ_neg (c : ℤ) : kapQ ψ₀ (-c) = ψ₀ (-1) * kapQ ψ₀ c := by
  unfold kapQ
  by_cases h : (q : ℤ) ∣ c
  · rw [if_pos (dvd_neg.2 h), if_pos h, Int.neg_ediv_of_dvd h, ← map_mul]
    push_cast; ring_nf
  · rw [if_neg (fun h' => h (dvd_neg.1 h')), if_neg h, mul_zero]

omit hq in
theorem q_dvd_level' : q ∣ 4 * (M' * q) := ⟨4 * M', by ring⟩

omit hq in
theorem Gamma0_q2_le : Gamma0 (4 * (M' * q ^ 2)) ≤ Gamma0 (4 * (M' * q)) := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
    (dvd_trans (by exact_mod_cast (⟨q, by ring⟩ : 4 * (M' * q) ∣ 4 * (M' * q ^ 2))) h)

/-- The transformation of the dual weight: for `δ ∈ Γ₀(4M'q²)` and `γ ∈ Γ₀(4M'q)`,
`ψ₀(c_γ/q) = ψ₀(d_δ) ψ₀(c_{γδ}/q)`. -/
theorem kapQ_mul (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 (4 * (M' * q ^ 2))) (γ : Gamma0 (4 * (M' * q))) :
    kapQ ψ₀ (ent γ 1 0) = ψ₀ (ent δ 1 1 : ZMod q) *
      kapQ ψ₀ (ent ((γ : SL(2, ℤ)) * δ) 1 0) := by
  have hγq : (q : ℤ) ∣ ent γ 1 0 :=
    dvd_trans ⟨4 * M', by push_cast; ring⟩ (dvd_c_of_mem (M' * q) γ)
  have hδ' : (4 * (M' * q ^ 2) : ℤ) ∣ ent δ 1 0 := by
    have := hδ
    rw [Gamma0_mem] at this
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hδq : (q : ℤ) ^ 2 ∣ ent δ 1 0 := dvd_trans ⟨4 * M', by ring⟩ hδ'
  obtain ⟨c, hc⟩ := hγq
  obtain ⟨e, he⟩ := hδq
  have hmul : ent ((γ : SL(2, ℤ)) * δ) 1 0 = ent γ 1 0 * ent δ 0 0 + ent γ 1 1 * ent δ 1 0 := by
    simp [ent, Matrix.mul_apply, Fin.sum_univ_two]
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdiv : ent ((γ : SL(2, ℤ)) * δ) 1 0 = q * (c * ent δ 0 0 + ent γ 1 1 * q * e) := by
    rw [hmul, hc, he]; ring
  unfold kapQ
  rw [if_pos ⟨c, hc⟩, if_pos ⟨_, hdiv⟩, hc, hdiv, Int.mul_ediv_cancel_left _ hq0,
    Int.mul_ediv_cancel_left _ hq0]
  -- modulo `q`, `c a + d q e ≡ c a` and `a d ≡ 1`
  have hdet := det_entries δ
  have had : ((ent δ 0 0 : ℤ) : ZMod q) * ((ent δ 1 1 : ℤ) : ZMod q) = 1 := by
    have h1 := congrArg (fun x : ℤ => (x : ZMod q)) hdet
    push_cast at h1
    rw [he] at h1
    push_cast at h1
    rw [ZMod.natCast_self] at h1
    linear_combination h1
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_mul, add_zero, ← map_mul]
  congr 1
  linear_combination (-(c : ZMod q)) * had

/-- **The dual weight-½ Eisenstein series** `Ê(z,w) = Σ_{⟨T⟩\Γ₀(4M'q)} ψ₀(c/q) \overline{j(γ,z)} Im(γz)^w`. -/
def eisDual (w : ℂ) (z : UpperHalfPlane) : ℂ := eisK (M' * q) (kapQ ψ₀) w z

/-- **Automorphy of `Ê`**: `Ê(δz, w) = ψ₀(d) j(δ, z) Ê(z, w)` for `δ ∈ Γ₀(4M'q²)`. -/
theorem eisDual_smul (w : ℂ) (z : UpperHalfPlane) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 (4 * (M' * q ^ 2))) :
    eisDual ψ₀ M' w (δ • z) = ψ₀ (ent δ 1 1 : ZMod q) * jU δ z * eisDual ψ₀ M' w z := by
  have := eisK_smul (M' * q) (kapQ ψ₀) w z ⟨δ, Gamma0_q2_le M' hδ⟩ (ψ₀ (ent δ 1 1 : ZMod q))
    (fun γ => kapQ_mul ψ₀ M' δ hδ γ)
  exact this

/-- **Fourier expansion of `Ê`** (`Re w > 1`): `Ê(z,w) = (1 + ψ₀(-1)) Σ_n 𝓕kerH_{y,w}(n) e(nx) D̂_n(w)`
with `D̂_n(w) = Σ_{c ≥ 1, 4M'q ∣ c} ψ₀(c/q) c^{-2w} klH(n,c)`. -/
theorem eisDual_eq_coeffs {w : ℂ} (hw : 1 < w.re) (z : UpperHalfPlane) :
    eisDual ψ₀ M' w z = (1 + ψ₀ (-1)) * ∑' n : ℤ, FourierTransform.fourier (kerH z.im w) n *
      cexp (2 * π * I * n * z.re) * DserK (M' * q) (kapQ ψ₀) n w :=
  eisK_eq_coeffs (M' * q) (kapQ ψ₀) (norm_kapQ_le ψ₀) (kapQ_zero ψ₀) (ψ₀ (-1)) (kapQ_neg ψ₀) hw z

end Dual

end

end GaloisForLFunctions.RHTower.HalfWeight
