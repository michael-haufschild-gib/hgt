import GaloisForLFunctions.RHTower.HalfWeightCoefficientBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiPoleAvoidingConductorStrip

/-!
# Regularised Eisenstein coefficients with polynomial bounds

Multiplying the weight-½ Eisenstein series by `(4w-3) · (4w-2)ζ(4w-1)` removes every pole on
`Re w > 1/4`: the pole at `w = 3/4` (from `L(2w-½, χ)` for principal `χ` and from `ζ(4w-2)` in the
constant term) and the zeros of `ζ(4w-1)` in `1/4 < Re w < 1/2`.

* `norm_LFunction_le_of_ne_one`: for every non-principal `χ` mod `N`,
  `‖L(s,χ)‖ ≤ 4C N³ ‖s-4‖³` on `0 ≤ Re s ≤ 2` (primitive reduction: `L(s,χ) = L(s,χ*) ∏_{p∣N}(1-χ*(p)p^{-s})`
  with the conductor-uniform bound `RHTower.norm_primitiveLFunction_conductorUniform_strip_le`).
* `norm_LFunction_le_two`: `‖L(s,χ)‖ ≤ ζ(2) < 2` on `Re s ≥ 2`.
* `Lreg`: `(s-1)L(s,χ)`, entire (`differentiable_Lreg`), with `‖Lreg‖ ≤ (4|n|M)³ G(s)` on `Re s ≥ 0`
  (`norm_Lreg_le`).
* `Dstar`: `D*_n(w) = (4w-3)(4w-2)ζ(4w-1) D_n(w)` (`Dstar_eq`, `Re w > 3/4`), holomorphic on
  `Re w > 1/4` (`differentiableAt_Dstar`), and **polynomially bounded in `n`** (`norm_Dstar_le`):
  `‖D*_n(w)‖ ≤ √2 ‖4w-2‖ G(2w-½) (4|n|M)^{4 + γ(4Re w-1) + β(2Re w-½)}` for `Re w > 1/4`.
* `phiStar`: the regularised constant term `(4w-3)(4w-2)ζ(4w-1) φ(w)` (`phiStar_eq`), holomorphic on
  `Re w > 1/4` (`differentiableAt_phiStar`).
-/

open Real Complex

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-- The constant `4C` of the conductor-uniform strip bound. -/
def stripC : ℝ := 4 * RHTower.cglDirichletLRightEdgeConstant

theorem stripC_pos : 0 < stripC := by
  unfold stripC; have := RHTower.cglDirichletLRightEdgeConstant_pos; positivity

/-- **Strip bound for every non-principal character** (via its primitive character):
`‖L(s,χ)‖ ≤ 4C N³ ‖s-4‖³` for `0 ≤ Re s ≤ 2`. -/
theorem norm_LFunction_le_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {s : ℂ} (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ stripC * (N : ℝ) ^ 3 * ‖s - 4‖ ^ 3 := by
  have hf : χ.conductor ≠ 0 := χ.conductor_ne_zero
  haveI : NeZero χ.conductor := ⟨hf⟩
  have hne : χ.primitiveCharacter ≠ 1 := by
    intro h
    have hind := χ.changeLevel_primitiveCharacter
    rw [h, DirichletCharacter.changeLevel_one] at hind
    exact hχ hind.symm
  have hL := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := s) (Or.inl hne)
  rw [χ.changeLevel_primitiveCharacter] at hL
  let P : RHTower.CGLLemma62PrimitiveCharacter :=
    ⟨⟨χ.conductor, Nat.pos_of_ne_zero hf⟩, χ.primitiveCharacter, hne, χ.primitiveCharacter_isPrimitive⟩
  have hP := RHTower.norm_primitiveLFunction_conductorUniform_strip_le P s (by linarith) h2
  have hfN : (χ.conductor : ℝ) ≤ N := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ.conductor_dvd_level
  have hf1 : (1 : ℝ) ≤ χ.conductor := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hf
  have hprod := norm_prod_one_sub_le (NeZero.ne N) h0 (fun p => χ.primitiveCharacter (p : ZMod χ.conductor))
    (fun p => DirichletCharacter.norm_le_one _ _)
  have hC := RHTower.cglDirichletLRightEdgeConstant_pos
  rw [hL, norm_mul]
  have hP' : ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖ ≤
      stripC * (N : ℝ) ^ 2 * ‖s - 4‖ ^ 3 := by
    refine hP.trans ?_
    have : (P.modulus.value : ℝ) ^ (2 : ℝ) ≤ (N : ℝ) ^ 2 := by
      rw [Real.rpow_two]; exact pow_le_pow_left₀ (by linarith) hfN 2
    unfold stripC
    gcongr
  calc _ ≤ (stripC * (N : ℝ) ^ 2 * ‖s - 4‖ ^ 3) * N :=
        mul_le_mul hP' hprod (norm_nonneg _) (by have := stripC_pos; positivity)
    _ = _ := by ring


/-- On `Re s ≥ 2` every Dirichlet `L`-function is bounded by `ζ(2) < 2`. -/
theorem norm_LFunction_le_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by linarith)]
  have hb : ∀ n : ℕ, ‖LSeries.term (fun m : ℕ => χ (m : ZMod N)) s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn]
    have h1 : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2 : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hs
    have h3 : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := by positivity
    rw [Real.rpow_two] at h2 h3
    calc ‖χ (n : ZMod N)‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le h3 h2
  have hz := hasSum_zeta_two
  have hsn : Summable fun n : ℕ => ‖LSeries.term (fun m : ℕ => χ (m : ZMod N)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hz.summable
  calc ‖LSeries (fun m : ℕ => χ (m : ZMod N)) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun m : ℕ => χ (m : ZMod N)) s n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := hsn.tsum_le_tsum hb hz.summable
    _ = Real.pi ^ 2 / 6 := hz.tsum_eq
    _ ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]


/-! ### The regularised `L`-factor `(s-1) L(s, χ)` -/

section Regularised

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

open Classical in
/-- `(s-1) L(s,χ)`, entire: `(s-1)ζ(s) ∏_{p∣4nM}(1-p^{-s})` when `χ` is principal. -/
def Lreg (s : ℂ) : ℂ :=
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  if kronChar hn hM = 1 then RHTower.zetaResidueFactor s * eulerFin (kmod n M) s
  else (s - 1) * DirichletCharacter.LFunction (kronChar hn hM) s

theorem Lreg_eq {s : ℂ} (hs : s ≠ 1) :
    haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
    Lreg hn hM s = (s - 1) * DirichletCharacter.LFunction (kronChar hn hM) s := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  classical
  unfold Lreg
  split_ifs with h
  · rw [h, LFunction_one_eq _ hs, RHTower.zetaResidueFactor_of_ne hs, eulerFin]; ring
  · rfl

theorem differentiable_Lreg : Differentiable ℂ (Lreg hn hM) := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  classical
  unfold Lreg
  split_ifs with h
  · exact RHTower.differentiable_zetaResidueFactor.mul (differentiable_eulerFin _)
  · exact (differentiable_id.sub_const 1).mul (DirichletCharacter.differentiable_LFunction h)

/-- `G(s) = 4C ‖s-1‖ ‖s-4‖³ + ‖(s-1)ζ(s)‖ + 2‖s-1‖`, the `n`-independent part of the bound. -/
def Gbound (s : ℂ) : ℝ :=
  stripC * ‖s - 1‖ * ‖s - 4‖ ^ 3 + ‖RHTower.zetaResidueFactor s‖ + 2 * ‖s - 1‖

include hn hM in
theorem kmod_one_le : (1 : ℝ) ≤ kmod n M := by
  have := kmod_pos hn hM
  exact_mod_cast this

/-- `‖(s-1)L(s,χ)‖ ≤ (4|n|M)³ G(s)` for `Re s ≥ 0`. -/
theorem norm_Lreg_le {s : ℂ} (h0 : 0 ≤ s.re) :
    ‖Lreg hn hM s‖ ≤ (kmod n M : ℝ) ^ 3 * Gbound s := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  classical
  have hk := kmod_one_le hn hM
  have hk3 : (1 : ℝ) ≤ (kmod n M : ℝ) ^ 3 := one_le_pow₀ hk
  have hC := stripC_pos
  have hA : 0 ≤ stripC * ‖s - 1‖ * ‖s - 4‖ ^ 3 :=
    mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 3)
  have hB := norm_nonneg (RHTower.zetaResidueFactor s)
  have hD := norm_nonneg (s - 1)
  unfold Lreg Gbound
  split_ifs with h
  · rw [norm_mul]
    have hE := norm_eulerFin_le (kmod_pos hn hM).ne' h0
    calc ‖RHTower.zetaResidueFactor s‖ * ‖eulerFin (kmod n M) s‖
        ≤ ‖RHTower.zetaResidueFactor s‖ * (kmod n M : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left (hE.trans (le_self_pow₀ hk (by norm_num))) (norm_nonneg _)
      _ ≤ _ := by nlinarith
  · rw [norm_mul]
    rcases le_or_gt s.re 2 with h2 | h2
    · have hL := norm_LFunction_le_of_ne_one h h0 h2
      calc ‖s - 1‖ * ‖DirichletCharacter.LFunction (kronChar hn hM) s‖
          ≤ ‖s - 1‖ * (stripC * (kmod n M : ℝ) ^ 3 * ‖s - 4‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hL (norm_nonneg _)
        _ ≤ _ := by nlinarith
    · have hL := norm_LFunction_le_two (kronChar hn hM) h2.le
      calc ‖s - 1‖ * ‖DirichletCharacter.LFunction (kronChar hn hM) s‖ ≤ ‖s - 1‖ * 2 :=
            mul_le_mul_of_nonneg_left hL (norm_nonneg _)
        _ ≤ _ := by nlinarith

end Regularised


/-! ### The regularised coefficients `D*_n = (4w-3)(4w-2)ζ(4w-1) D_n` -/

theorem norm_I_cpow_half : ‖I ^ (1 / 2 : ℂ)‖ = 1 := by
  rw [Complex.norm_cpow_of_ne_zero Complex.I_ne_zero]
  simp

section Regularised2

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

/-- `D*_n(w) = (i^{1/2}/√2) · 2 (s-1)L(s,χ) · (4w-2) ∏_{p∣4nM}(1-p^{1-4w})⁻¹ · L(e_L, s)`,
`s = 2w - 1/2`: entire in `Re w > 1/4`. -/
def Dstar (w : ℂ) : ℂ :=
  I ^ (1 / 2 : ℂ) / Real.sqrt 2 * 2 * Lreg hn hM (2 * w - 1 / 2) * (4 * w - 2) *
    (eulerFin (kmod n M) (4 * w - 1))⁻¹ * LSeries (fun c => eL (n := n) (M := M) c) (2 * w - 1 / 2)

/-- `D*_n(w) = (4w-3) · (4w-2)ζ(4w-1) · D_n(w)` for `Re w > 3/4`. -/
theorem Dstar_eq [NeZero M] {w : ℂ} (hw : 3 / 4 < w.re) :
    Dstar hn hM w = (4 * w - 3) * RHTower.zetaResidueFactor (4 * w - 1) *
      Dser M (1 : DirichletCharacter ℂ (4 * M)) n w := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have hs : (2 * w - 1 / 2 : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hF := zetaResidueFactor_ne_zero (u := 4 * w - 1) (by simp; linarith)
  have hE := eulerFin_ne_zero (kmod n M) (u := 4 * w - 1) (by simp; linarith)
  rw [Dser_eq_Dtil hn hM hw, Dstar, Dtil, invLOne, Lreg_eq hn hM hs]
  set F := RHTower.zetaResidueFactor (4 * w - 1)
  set E := eulerFin (kmod n M) (4 * w - 1)
  field_simp
  ring

theorem differentiableAt_Dstar {w₀ : ℂ} (hw : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (Dstar hn hM) w₀ := by
  have hs : 0 < (2 * w₀ - 1 / 2).re := by simp; linarith
  have hu : 0 < (4 * w₀ - 1).re := by simp; linarith
  have hlin : ∀ a b : ℂ, DifferentiableAt ℂ (fun w : ℂ => a * w - b) w₀ := fun a b =>
    (differentiableAt_id.const_mul a).sub_const b
  have hL : DifferentiableAt ℂ (fun w => Lreg hn hM (2 * w - 1 / 2)) w₀ :=
    (differentiable_Lreg hn hM _).comp w₀ (hlin 2 (1 / 2))
  have hEi : DifferentiableAt ℂ (fun w => (eulerFin (kmod n M) (4 * w - 1))⁻¹) w₀ :=
    ((differentiable_eulerFin _ _).comp w₀ (hlin 4 1)).inv (eulerFin_ne_zero _ hu)
  have hS : DifferentiableAt ℂ (fun w => LSeries (fun c => eL (n := n) (M := M) c) (2 * w - 1 / 2)) w₀ := by
    have := (differentiableAt_LSeries_of_summable (fun s hs => lseriesSummable_eL (M := M) hn hs)
      hs).comp w₀ (hlin 2 (1 / 2))
    exact this
  unfold Dstar
  exact ((((hL.const_mul _).mul (hlin 4 2)).mul hEi).mul hS)

/-- **Polynomial bound**: for `Re w > 1/4`,
`‖D*_n(w)‖ ≤ √2 ‖4w-2‖ G(2w-½) (4|n|M)^{4 + γ(4Re w - 1) + β(2Re w - 1/2)}`. -/
theorem norm_Dstar_le {w : ℂ} (h1 : 1 / 4 < w.re) :
    ‖Dstar hn hM w‖ ≤ Real.sqrt 2 * ‖4 * w - 2‖ * Gbound (2 * w - 1 / 2) *
      (kmod n M : ℝ) ^ (4 + gammaE (4 * w.re - 1) + betaE (2 * w.re - 1 / 2)) := by
  have hk := kmod_one_le hn hM
  have hk0 : (0 : ℝ) < kmod n M := by linarith
  have hsre : (2 * w - 1 / 2).re = 2 * w.re - 1 / 2 := by simp
  have hure : (4 * w - 1).re = 4 * w.re - 1 := by simp
  have hLr := norm_Lreg_le hn hM (s := 2 * w - 1 / 2) (by rw [hsre]; linarith)
  have hEi := norm_eulerFin_inv_le (kmod_pos hn hM).ne' (u := 4 * w - 1) (by rw [hure]; linarith)
  have hS := norm_LSeries_eL_le hn hM (s := 2 * w - 1 / 2) (by rw [hsre]; linarith)
  rw [hure] at hEi
  rw [hsre] at hS
  have hn4 : (4 * n.natAbs : ℝ) ≤ kmod n M := by
    have : 4 * n.natAbs ≤ kmod n M := Nat.le_mul_of_pos_right _ hM
    exact_mod_cast this
  have hG : 0 ≤ Gbound (2 * w - 1 / 2) := by
    unfold Gbound; have := stripC_pos; positivity
  have h2s : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hsq : (0 : ℝ) < Real.sqrt 2 := by positivity
  unfold Dstar
  simp only [norm_mul, norm_div, norm_I_cpow_half, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsq, h2s]
  have hpow : (kmod n M : ℝ) ^ (4 + gammaE (4 * w.re - 1) + betaE (2 * w.re - 1 / 2)) =
      (kmod n M : ℝ) ^ 3 * (kmod n M : ℝ) ^ gammaE (4 * w.re - 1) * (kmod n M : ℝ) *
        (kmod n M : ℝ) ^ betaE (2 * w.re - 1 / 2) := by
    rw [Real.rpow_add hk0, Real.rpow_add hk0, show (4 : ℝ) = 3 + 1 by norm_num,
      Real.rpow_add hk0, Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hpow]
  have hS' : ‖LSeries (fun c => eL (n := n) (M := M) c) (2 * w - 1 / 2)‖ ≤
      (kmod n M : ℝ) * (kmod n M : ℝ) ^ betaE (2 * w.re - 1 / 2) :=
    hS.trans (mul_le_mul_of_nonneg_right hn4 (by positivity))
  calc 1 / Real.sqrt 2 * 2 * ‖Lreg hn hM (2 * w - 1 / 2)‖ * ‖4 * w - 2‖ *
        ‖(eulerFin (kmod n M) (4 * w - 1))⁻¹‖ * ‖LSeries (fun c => eL (n := n) (M := M) c) (2 * w - 1 / 2)‖
      ≤ 1 / Real.sqrt 2 * 2 * ((kmod n M : ℝ) ^ 3 * Gbound (2 * w - 1 / 2)) * ‖4 * w - 2‖ *
          (kmod n M : ℝ) ^ gammaE (4 * w.re - 1) *
          ((kmod n M : ℝ) * (kmod n M : ℝ) ^ betaE (2 * w.re - 1 / 2)) := by
        gcongr
    _ = (2 / Real.sqrt 2) * ‖4 * w - 2‖ * Gbound (2 * w - 1 / 2) *
          ((kmod n M : ℝ) ^ 3 * (kmod n M : ℝ) ^ gammaE (4 * w.re - 1) * (kmod n M : ℝ) *
            (kmod n M : ℝ) ^ betaE (2 * w.re - 1 / 2)) := by ring
    _ = _ := by
        rw [show (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 by
          rw [div_eq_iff hsq.ne']; exact (Real.mul_self_sqrt (by norm_num)).symm]

end Regularised2


/-! ### The regularised constant term -/

section Constant2

variable (M : ℕ) [NeZero M]

/-- `φ*(w) = (4w-3)(4w-2)ζ(4w-1) φ(w)`, entire in `Re w > 1/4`. -/
def phiStar (w : ℂ) : ℂ :=
  I ^ (1 / 2 : ℂ) / Real.sqrt 2 * ((mZero (4 * M)).totient : ℂ) *
    (mZero (4 * M) : ℂ) ^ (-(4 * w - 1)) * RHTower.zetaResidueFactor (4 * w - 2) *
      (2 * (eulerFin (4 * M) (4 * w - 1))⁻¹) * (cK 1 w / (2 * w))

theorem phiStar_eq {w : ℂ} (hw : 3 / 4 < w.re) :
    phiStar M w = (4 * w - 3) * RHTower.zetaResidueFactor (4 * w - 1) * phiC M w := by
  have hu : (4 * w - 2 : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hF := zetaResidueFactor_ne_zero (u := 4 * w - 1) (by simp; linarith)
  have hE := eulerFin_ne_zero (4 * M) (u := 4 * w - 1) (by simp; linarith)
  rw [phiStar, phiC, RHTower.zetaResidueFactor_of_ne hu]
  field_simp
  ring

theorem differentiableAt_phiStar {w₀ : ℂ} (hw : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (phiStar M) w₀ := by
  have hu : 0 < (4 * w₀ - 1).re := by simp; linarith
  have hw0 : w₀ ≠ 0 := by rintro rfl; simp at hw; linarith
  have hlin : ∀ a b : ℂ, DifferentiableAt ℂ (fun w : ℂ => a * w - b) w₀ := fun a b =>
    (differentiableAt_id.const_mul a).sub_const b
  have hm0 : (mZero (4 * M) : ℂ) ≠ 0 := by exact_mod_cast (mZero_pos (4 * M)).ne'
  have hEi : DifferentiableAt ℂ (fun w => 2 * (eulerFin (4 * M) (4 * w - 1))⁻¹) w₀ :=
    (((differentiable_eulerFin _ _).comp w₀ (hlin 4 1)).inv (eulerFin_ne_zero _ hu)).const_mul _
  have hc : DifferentiableAt ℂ (fun w => cK 1 w / (2 * w)) w₀ :=
    (differentiableAt_cK 1 (by push_cast; linarith)).div (differentiableAt_id.const_mul 2)
      (mul_ne_zero two_ne_zero hw0)
  have hpow : DifferentiableAt ℂ (fun w => (mZero (4 * M) : ℂ) ^ (-(4 * w - 1))) w₀ :=
    ((hlin 4 1).neg).const_cpow (Or.inl hm0)
  have hz : DifferentiableAt ℂ (fun w => RHTower.zetaResidueFactor (4 * w - 2)) w₀ :=
    (RHTower.differentiable_zetaResidueFactor _).comp w₀ (hlin 4 2)
  unfold phiStar
  exact ((((hpow.const_mul _).mul hz).mul hEi).mul hc)

end Constant2
