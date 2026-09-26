import GaloisForLFunctions.RHTower.HalfWeightConstantCoefficient
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# Continuation of the Fourier coefficients of the weight-½ Eisenstein series

* `kronChar_sq`: the Kronecker character is quadratic, `χ² = 1`, so the denominator
  `L(4w-1, χ²)` of `LSeries_gL` is the principal `L`-function
  `L(u, 1_N) = ζ(u) ∏_{p∣N} (1 - p^{-u})` (`LFunction_one_eq`).
* `invLOne N u = (u-1)/((u-1)ζ(u) · ∏_{p∣N}(1-p^{-u}))` continues `1/L(u, 1_N)` (`invLOne_eq`); it is
  holomorphic wherever `(u-1)ζ(u)` (extended by `1` at `u = 1`, `RHTower.zetaResidueFactor`) does not
  vanish and `Re u > 0` (`differentiableAt_invLOne`), in particular on `Re u ≥ 1`.
* `Dtil`: `D̃_n(w) = (i^{1/2}/√2) L(2w-½, χ) · invLOne(4|n|M, 4w-1) · L(e_L, 2w-½)`;
  `Dser_eq_Dtil`: it equals `D_n(w)` for `Re w > 3/4`; `differentiableAt_Dtil`: holomorphic on
  `Re w > 1/4` away from the zeros of `ζ(4w-1)` and, when `χ` is principal, from `w = 3/4`.
* `phiC`: the continued constant term,
  `φ(w) = (i^{1/2}/√2) φ(m₀) m₀^{1-4w} ζ(4w-2) · 2/((4w-2)ζ(4w-1) ∏_{p∣2M}(1-p^{1-4w})) · c_1(w)/(2w)`;
  `Dser_zero_mul_integral`: `D_0(w) ∫kerH_{y,w} = y^{1-w} φ(w)` for `Re w > 3/4`;
  `differentiableAt_phiC`: holomorphic on `Re w > 1/4`, `w ≠ 0, 3/4`, away from zeros of `ζ(4w-1)`.

At `w = 1/2` the pole of `∫kerH_{y,w}` (the factor `1/(2w-1)`) is absorbed by the zero of
`1/ζ(4w-1)`, so the constant term is holomorphic across `Re w = 1/2`.
-/

open Real Complex ArithmeticFunction Filter Topology

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-! ### The Kronecker character is quadratic -/

/-- `χ² = 1`: the Kronecker character takes values `±1` on units. -/
theorem kronChar_sq {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M) : kronChar hn hM ^ 2 = 1 := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  refine MulChar.ext fun u => ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, kronChar_apply, if_pos u.isUnit]
  have hc : (u : ZMod (kmod n M)).val.Coprime (kmod n M) := by
    have hx := u.isUnit
    rw [← ZMod.natCast_zmod_val (u : ZMod (kmod n M))] at hx
    exact (ZMod.isUnit_iff_coprime _ _).1 hx
  have hg : n.gcd ((u : ZMod (kmod n M)).val : ℤ) = 1 := by
    have h1 : n.natAbs.Coprime (u : ZMod (kmod n M)).val :=
      (Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ 4) M) hc).symm
    show Nat.gcd n.natAbs ((u : ZMod (kmod n M)).val : ℤ).natAbs = 1
    rw [Int.natAbs_natCast]; exact h1
  have := jacobiSym.sq_one hg
  exact_mod_cast this

/-! ### The principal `L`-function and its reciprocal -/

/-- `L(u, 1_N) = ζ(u) ∏_{p ∣ N} (1 - p^{-u})` for `u ≠ 1`. -/
theorem LFunction_one_eq (N : ℕ) [NeZero N] {u : ℂ} (hu : u ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) u =
      riemannZeta u * ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-u)) := by
  have h := DirichletCharacter.LFunction_changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1)
    (Or.inr hu)
  rw [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- The finite Euler factor `∏_{p ∣ N} (1 - p^{-u})`. -/
def eulerFin (N : ℕ) (u : ℂ) : ℂ := ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-u))

theorem eulerFin_ne_zero (N : ℕ) {u : ℂ} (hu : 0 < u.re) : eulerFin N u ≠ 0 := by
  rw [eulerFin, Finset.prod_ne_zero_iff]
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hn : ‖(p : ℂ) ^ (-u)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hp).pos]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hn
  exact lt_irrefl _ hn

theorem differentiable_eulerFin (N : ℕ) : Differentiable ℂ (eulerFin N) := by
  intro u
  have h := DifferentiableAt.finsetProd (𝕜 := ℂ) (x := u) (u := N.primeFactors)
    (f := fun p v => 1 - (p : ℂ) ^ (-v)) (fun p hp => by
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact (differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow (Or.inl hp0)))
  rw [Finset.prod_fn] at h
  exact h

/-- `1/L(u, 1_N)` continued: `(u-1)/((u-1)ζ(u) · ∏_{p∣N}(1-p^{-u}))`. -/
def invLOne (N : ℕ) (u : ℂ) : ℂ := (u - 1) / (RHTower.zetaResidueFactor u * eulerFin N u)

theorem invLOne_eq (N : ℕ) [NeZero N] {u : ℂ} (hu : u ≠ 1) :
    invLOne N u = (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) u)⁻¹ := by
  rw [invLOne, LFunction_one_eq N hu, RHTower.zetaResidueFactor_of_ne hu, eulerFin]
  have h1 : u - 1 ≠ 0 := sub_ne_zero.2 hu
  by_cases hz : riemannZeta u * ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-u)) = 0
  · rw [hz, inv_zero, mul_assoc, hz, mul_zero, div_zero]
  · rw [mul_assoc, div_mul_cancel_left₀ h1]

theorem zetaResidueFactor_ne_zero {u : ℂ} (hu : 1 ≤ u.re) : RHTower.zetaResidueFactor u ≠ 0 := by
  rcases eq_or_ne u 1 with rfl | h1
  · simp
  · rw [RHTower.zetaResidueFactor_of_ne h1]
    exact mul_ne_zero (sub_ne_zero.2 h1) (riemannZeta_ne_zero_of_one_le_re hu)

theorem differentiableAt_invLOne (N : ℕ) {u : ℂ} (hu : 0 < u.re)
    (hF : RHTower.zetaResidueFactor u ≠ 0) : DifferentiableAt ℂ (invLOne N) u := by
  unfold invLOne
  exact (differentiableAt_id.sub_const 1).div
    ((RHTower.differentiable_zetaResidueFactor u).mul (differentiable_eulerFin N u))
    (mul_ne_zero hF (eulerFin_ne_zero N hu))


/-! ### The continued non-constant coefficients -/

theorem differentiableAt_LSeries_of_summable {f : ℕ → ℂ} (hf : ∀ s : ℂ, 0 < s.re → LSeriesSummable f s)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (LSeries f) s := by
  have ha : LSeries.abscissaOfAbsConv f ≤ ((0 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hf y (by simpa using hy)
  exact (LSeries_hasDerivAt (lt_of_le_of_lt ha (by exact_mod_cast hs))).differentiableAt

section NonConstant

variable {n : ℤ} {M : ℕ} (hn : n ≠ 0) (hM : 0 < M)

/-- The continued coefficient
`D̃_n(w) = (i^{1/2}/√2) L(2w-½, χ) L(4w-1, 1_{4|n|M})^{-1} L(e_L, 2w-½)`. -/
def Dtil (w : ℂ) : ℂ :=
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  I ^ (1 / 2 : ℂ) / Real.sqrt 2 * DirichletCharacter.LFunction (kronChar hn hM) (2 * w - 1 / 2) *
    invLOne (kmod n M) (4 * w - 1) * LSeries (fun c => eL (n := n) (M := M) c) (2 * w - 1 / 2)

/-- `D̃_n` continues `D_n`. -/
theorem Dser_eq_Dtil [NeZero M] {w : ℂ} (hw : 3 / 4 < w.re) :
    Dser M (1 : DirichletCharacter ℂ (4 * M)) n w = Dtil hn hM w := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have hs : 1 < (2 * w - 1 / 2).re := by simp; linarith
  have hu : (4 * w - 1 : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Dser_one_eq_LSeries, LSeries_gL hn hM hs, kronChar_sq,
    show 2 * (2 * w - 1 / 2) = 4 * w - 1 by ring, Dtil, invLOne_eq _ hu]
  ring

/-- `D̃_n` is holomorphic at every `w₀` with `Re w₀ > 1/4`, `(4w₀-1)ζ(4w₀-1) ≠ 0` at the
continued point, and `2w₀ - ½ ≠ 1` unless `χ` is non-principal. -/
theorem differentiableAt_Dtil {w₀ : ℂ} (hw : 1 / 4 < w₀.re)
    (hF : RHTower.zetaResidueFactor (4 * w₀ - 1) ≠ 0)
    (hχ : 2 * w₀ - 1 / 2 ≠ 1 ∨ kronChar hn hM ≠ 1) : DifferentiableAt ℂ (Dtil hn hM) w₀ := by
  haveI : NeZero (kmod n M) := ⟨(kmod_pos hn hM).ne'⟩
  have hs : 0 < (2 * w₀ - 1 / 2).re := by simp; linarith
  have hu : 0 < (4 * w₀ - 1).re := by simp; linarith
  have hlin1 : DifferentiableAt ℂ (fun w : ℂ => 2 * w - 1 / 2) w₀ :=
    (differentiableAt_id.const_mul 2).sub_const _
  have hlin2 : DifferentiableAt ℂ (fun w : ℂ => 4 * w - 1) w₀ :=
    (differentiableAt_id.const_mul 4).sub_const _
  have hL : DifferentiableAt ℂ (fun w => DirichletCharacter.LFunction (kronChar hn hM) (2 * w - 1 / 2)) w₀ :=
    (DirichletCharacter.differentiableAt_LFunction _ _ hχ).comp w₀ hlin1
  have hI : DifferentiableAt ℂ (fun w => invLOne (kmod n M) (4 * w - 1)) w₀ := by
    have := (differentiableAt_invLOne (kmod n M) hu hF).comp w₀ hlin2
    exact this
  have hE : DifferentiableAt ℂ (fun w => LSeries (fun c => eL (n := n) (M := M) c) (2 * w - 1 / 2)) w₀ := by
    have := (differentiableAt_LSeries_of_summable (fun s hs => lseriesSummable_eL (M := M) hn hs)
      hs).comp w₀ hlin1
    exact this
  unfold Dtil
  exact ((hL.const_mul _).mul hI).mul hE

/-- On `Re w ≥ 1/2` the zeta condition holds automatically. -/
theorem zetaResidueFactor_ne_zero_of_half_le {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    RHTower.zetaResidueFactor (4 * w - 1) ≠ 0 :=
  zetaResidueFactor_ne_zero (by simp; linarith)

end NonConstant


/-! ### The continued constant term -/

section Constant

variable (M : ℕ) [NeZero M]

/-- The continued constant-term coefficient `φ(w)`, so that `D_0(w) ∫ kerH_{y,w} = y^{1-w} φ(w)`:
`φ(w) = (i^{1/2}/√2) φ(m₀) m₀^{1-4w} ζ(4w-2) · 2/((4w-2)ζ(4w-1) ∏_{p∣2M}(1-p^{1-4w})) · c_1(w)/(2w)`. -/
def phiC (w : ℂ) : ℂ :=
  I ^ (1 / 2 : ℂ) / Real.sqrt 2 * ((mZero (4 * M)).totient : ℂ) *
    (mZero (4 * M) : ℂ) ^ (-(4 * w - 1)) * riemannZeta (4 * w - 2) *
      (2 / (RHTower.zetaResidueFactor (4 * w - 1) * eulerFin (4 * M) (4 * w - 1))) *
        (cK 1 w / (2 * w))

/-- **The constant term**: `D_0(w) ∫ kerH_{y,w} = y^{1-w} φ(w)` for `Re w > 3/4`. -/
theorem Dser_zero_mul_integral {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : 3 / 4 < w.re) :
    Dser M (1 : DirichletCharacter ℂ (4 * M)) 0 w * (∫ x, kerH y w x) = (y : ℂ) ^ (1 - w) * phiC M w := by
  have hK := integral_kerH_eq hy 1 (show 1 / 2 < w.re by linarith)
  have hD := Dser_zero_mul (M := M) hw
  have hu : (4 * w - 1 : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hF : RHTower.zetaResidueFactor (4 * w - 1) = (4 * w - 1 - 1) * riemannZeta (4 * w - 1) :=
    RHTower.zetaResidueFactor_of_ne hu
  have hζ : riemannZeta (4 * w - 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hE : eulerFin (4 * M) (4 * w - 1) ≠ 0 := eulerFin_ne_zero _ (by simp; linarith)
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  have hw1 : 2 * w - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hP : Pk 1 (2 * w) = 2 * w * (2 * w - 1) := Pk_one _
  rw [hP] at hK
  unfold phiC
  rw [hF]
  rw [eulerFin] at hE ⊢
  have hint : (∫ x, kerH y w x) = (y : ℂ) ^ (1 - w) * cK 1 w / (2 * w * (2 * w - 1)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hw0) hw1), mul_comm]; exact hK
  rw [hint]
  have hD' : Dser M (1 : DirichletCharacter ℂ (4 * M)) 0 w = I ^ (1 / 2 : ℂ) / Real.sqrt 2 *
      ((mZero (4 * M)).totient : ℂ) * (mZero (4 * M) : ℂ) ^ (-(4 * w - 1)) * riemannZeta (4 * w - 2) /
        (riemannZeta (4 * w - 1) * ∏ p ∈ (4 * M).primeFactors, (1 - (p : ℂ) ^ (-(4 * w - 1)))) := by
    rw [eq_div_iff (mul_ne_zero hζ hE)]; exact hD
  rw [hD']
  field_simp
  ring

theorem differentiableAt_phiC {w₀ : ℂ} (hw : 1 / 4 < w₀.re) (hw0 : w₀ ≠ 0) (h34 : w₀ ≠ 3 / 4)
    (hF : RHTower.zetaResidueFactor (4 * w₀ - 1) ≠ 0) : DifferentiableAt ℂ (phiC M) w₀ := by
  have hu : 0 < (4 * w₀ - 1).re := by simp; linarith
  have hlin : ∀ a b : ℂ, DifferentiableAt ℂ (fun w : ℂ => a * w - b) w₀ := fun a b =>
    (differentiableAt_id.const_mul a).sub_const b
  have hm0 : (mZero (4 * M) : ℂ) ≠ 0 := by exact_mod_cast (mZero_pos (4 * M)).ne'
  have hz : DifferentiableAt ℂ (fun w => riemannZeta (4 * w - 2)) w₀ := by
    refine (differentiableAt_riemannZeta ?_).comp w₀ (hlin 4 2)
    intro h; apply h34
    linear_combination h / 4
  have hden : DifferentiableAt ℂ (fun w => 2 / (RHTower.zetaResidueFactor (4 * w - 1) *
      eulerFin (4 * M) (4 * w - 1))) w₀ :=
    (differentiableAt_const _).div
      (((RHTower.differentiable_zetaResidueFactor _).comp w₀ (hlin 4 1)).mul
        ((differentiable_eulerFin _ _).comp w₀ (hlin 4 1)))
      (mul_ne_zero hF (eulerFin_ne_zero _ hu))
  have hc : DifferentiableAt ℂ (fun w => cK 1 w / (2 * w)) w₀ :=
    (differentiableAt_cK 1 (by push_cast; linarith)).div (differentiableAt_id.const_mul 2)
      (mul_ne_zero two_ne_zero hw0)
  have hpow : DifferentiableAt ℂ (fun w => (mZero (4 * M) : ℂ) ^ (-(4 * w - 1))) w₀ :=
    ((hlin 4 1).neg).const_cpow (Or.inl hm0)
  unfold phiC
  exact ((((hpow.const_mul _).mul hz).mul hden).mul hc)

end Constant
