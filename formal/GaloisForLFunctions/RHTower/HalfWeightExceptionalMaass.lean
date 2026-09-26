import GaloisForLFunctions.RHTower.HalfWeightShimuraCoefficient
import GaloisForLFunctions.RHTower.SelbergThreeSixteenths
import GaloisForLFunctions.RHTower.SelbergExceptionalCuspMean

/-!
# Exceptional Maass cusp forms on `Γ₀(N+1)`: Whittaker coefficients and the Shimura zeroth coefficient

Let `f` be a Maass cusp form on `Γ₀(N+1)` with eigenvalue `λ = 1/4 - τ²`, `0 < τ < 1/2`.

* `gz_periodic`: `f` is `1`-periodic (`T ∈ Γ₀(N+1)`); `bco k` is its width-`1` Fourier coefficient,
  realised as the width-`(N+1)` coefficient of index `(N+1)k` of the restriction to `Γ(N+1)`
  (`bco_eq`, via `coefficient_periodic`).
* `bco_zero`: the constant term vanishes (`maassMean_eq_zero_of_exceptional`).
* **`bco_whittaker`**, `bco_eq_rhoW`: `c_k(y) = ρ_k W_τ(2π|k|y)` for every `k` (modal rigidity
  `modal_eq_whittaker`); `rhoW_bounded`: the `ρ_k` are bounded.
* **`hasSum_zeroth`**: `∫_0^1 f(4z) \overline{θ(z)} dx = Σ_{j ∈ ℤ} e^{-8πj²y} ρ_{j²} W_τ(8πj²y)`.
-/

open Real Complex Filter Topology MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

open SelbergMaassFourier SelbergMaassMean SelbergModalEnergy SelbergThreeSixteenths
open _root_.RHTower GaloisForLFunctions.RHTower

noncomputable section

/-! ### Maass cusp forms on `Γ₀(N+1)` below `1/4` -/

theorem Gamma_le_Gamma0' (M : ℕ) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma0 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem]
  rw [CongruenceSubgroup.Gamma_mem] at hA
  exact hA.2.2.1

variable (N : ℕ) {τ : ℝ}

/-- The restriction of a `Γ₀(N+1)` Maass cusp form to `Γ(N+1)`. -/
def fG (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ))) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (1 / 4 - τ ^ (2 : ℕ)) :=
  restrictMaass (Subgroup.map_mono (Gamma_le_Gamma0' (N + 1))) f

variable (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ)))

/-- A `Γ₀(N+1)` form is `1`-periodic. -/
theorem gz_periodic (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (f.1.1 ∘ ofComplex) (point (x + 1) y) = (f.1.1 ∘ ofComplex) (point x y) := by
  have hg : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (N + 1) := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.coe_T]
  have hm : integralSL2ToReal ModularGroup.T ∈ realImage (CongruenceSubgroup.Gamma0 (N + 1)) :=
    ⟨ModularGroup.T, hg, rfl⟩
  have hp : 0 < (point x y).im := by simpa [point] using hy
  let z : ℍ := ⟨point x y, hp⟩
  have hi := f.1.property ⟨integralSL2ToReal ModularGroup.T, hm⟩ z
  rw [integral_action, UpperHalfPlane.modular_T_smul] at hi
  have hz : ofComplex (point (x + 1) y) = (1 : ℝ) +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point, z, UpperHalfPlane.coe_vadd]
    ring
  change f.1.1 (ofComplex (point (x + 1) y)) = f.1.1 (ofComplex (point x y))
  rw [hz, ofComplex_apply_of_im_pos hp]
  exact hi

theorem gz_slice_continuous {y : ℝ} (hy : 0 < y) : Continuous fun x : ℝ => (f.1.1 ∘ ofComplex) (point x y) :=
  slice_continuous (f.2.2.1.1.continuousOn) hy

/-- The width-`1` Fourier coefficients of the `Γ₀(N+1)` form, as coefficients of its `Γ(N+1)` restriction. -/
def bco (k : ℤ) : ℝ → ℂ := maassCoefficient N (fG N f) ((N + 1 : ℕ) * k)

theorem bco_eq (k : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient 1 k (f.1.1 ∘ ofComplex) y = bco N f k y := by
  have h := coefficient_periodic (N + 1) (Nat.succ_pos N) ((N + 1 : ℕ) * k)
    (gz_slice_continuous N f hy) (fun x => gz_periodic N f x hy)
  rw [if_pos (dvd_mul_right _ _), Int.mul_ediv_cancel_left _ (by exact_mod_cast Nat.succ_ne_zero N)] at h
  rw [bco, maassCoefficient, ← h]
  rfl

variable {N f}

theorem bco_zero (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {y : ℝ} (hy : 0 < y) : bco N f 0 y = 0 := by
  rw [bco, mul_zero, maassCoefficient_zero]
  have := SelbergEulerDecay.maassMean_eq_zero_of_exceptional N hτ0 hτ1 (fG N f) (Real.log y)
  rw [Real.exp_log hy] at this
  rw [this, mul_zero]

theorem bco_bounded : ∃ B : ℝ, ∀ (k : ℤ) (y : ℝ), 0 < y → ‖bco N f k y‖ ≤ B := by
  obtain ⟨B, hB⟩ := maassCoefficient_bounded N (fG N f)
  exact ⟨B, fun k y hy => hB _ y hy⟩

/-- **Whittaker form of the coefficients**: `c_k(y) = ρ_k W_τ(2π|k|y)` for `k ≠ 0`. -/
theorem bco_whittaker (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {k : ℤ} (hk : k ≠ 0) :
    ∃ c : ℂ, ∀ y, 0 < y → bco N f k y = c * whModal τ (2 * π * |(k : ℝ)|) y := by
  have hk0 : 0 < 2 * π * |(k : ℝ)| := by
    have : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
    positivity
  obtain ⟨B, hB⟩ := maassCoefficient_bounded N (fG N f)
  refine modal_eq_whittaker hτ0 hτ1 hk0 (a := bco N f k) (a' := deriv (bco N f k))
    (a'' := deriv (deriv (bco N f k))) (fun y hy => maassCoefficient_hasDerivAt N (fG N f) _ hy)
    (fun y hy => maassCoefficient_second_hasDerivAt N (fG N f) _ hy) ?_ (B := B) (fun y hy => hB _ y hy)
    (maassCoefficient_decay N (fG N f) _)
  intro y hy
  have h := maassCoefficient_modal_equation N (fG N f) ((N + 1 : ℕ) * k) hy
  have hsf : signedFrequency (N + 1 : ℕ) ((N + 1 : ℕ) * k) = 2 * π * k := by
    unfold signedFrequency; push_cast; field_simp
  rw [hsf] at h
  simp only [bco]
  have hsq : ((2 * π * |(k : ℝ)|) ^ 2 : ℝ) = (2 * π * k) ^ 2 := by rw [mul_pow, sq_abs, ← mul_pow]
  rw [hsq]
  push_cast at h ⊢
  linear_combination -h

variable (f) in
/-- The Whittaker coefficient `ρ_k`: `c_k(y) = ρ_k W_τ(2π|k|y)` (and `ρ_0 = 0`). -/
def rhoW (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (k : ℤ) : ℂ :=
  if hk : k = 0 then 0 else Classical.choose (bco_whittaker (N := N) (f := f) hτ0 hτ1 hk)

theorem bco_eq_rhoW (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (k : ℤ) {y : ℝ} (hy : 0 < y) :
    bco N f k y = rhoW f hτ0 hτ1 k * whModal τ (2 * π * |(k : ℝ)|) y := by
  by_cases hk : k = 0
  · subst hk
    rw [bco_zero hτ0 hτ1 hy, rhoW, dif_pos rfl, zero_mul]
  · rw [rhoW, dif_neg hk]
    exact Classical.choose_spec (bco_whittaker (N := N) (f := f) hτ0 hτ1 hk) y hy

variable (f) in
theorem gz_bounded : ∃ C : ℝ, ∀ z : ℍ, ‖f.1.1 z‖ ≤ C :=
  MaassCongruenceL2.source_bounded N (fG N f)

/-- **The zeroth Fourier coefficient of `f(4z) \overline{θ(z)}`** in Whittaker form:
`∫_0^1 f(4z) \overline{θ(z)} dx = Σ_{j ∈ ℤ} e^{-8πj²y} ρ_{j²} W_τ(8πj²y)`. -/
theorem hasSum_zeroth (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {y : ℝ} (hy : 0 < y) :
    HasSum (fun j : ℤ => ((Real.exp (-(8 * π * (j : ℝ) ^ 2 * y)) : ℝ) : ℂ) *
        (rhoW f hτ0 hτ1 (j ^ 2) * Wh τ (8 * π * (j : ℝ) ^ 2 * y)))
      (∫ x in (0 : ℝ)..1, (f.1.1 ∘ ofComplex) (point (4 * x) (4 * y)) *
        starRingEnd ℂ (theta (point x y))) := by
  have hy4 : 0 < 4 * y := by linarith
  obtain ⟨C, hC⟩ := gz_bounded f
  have hB : ∀ x : ℝ, ‖(f.1.1 ∘ ofComplex) (point x (4 * y))‖ ≤ C := fun x => hC _
  have h := hasSum_integral_U_conj_theta' hy hB (gz_slice_continuous N f hy4)
    (fun x => gz_periodic N f x hy4)
  refine h.congr_fun fun j => ?_
  rw [bco_eq N f (j ^ 2) hy4, bco_eq_rhoW hτ0 hτ1 _ hy4, whModal]
  congr 3
  push_cast
  rw [abs_of_nonneg (sq_nonneg _)]
  ring

/-- The Whittaker coefficients are bounded. -/
theorem rhoW_bounded (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℤ, ‖rhoW f hτ0 hτ1 k‖ ≤ R := by
  obtain ⟨B, hB⟩ := bco_bounded (N := N) (f := f)
  have hW : 0 < ‖Wh τ 1‖ := norm_pos_iff.2 (Wh_ne_zero one_pos)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 1 one_pos)
  refine ⟨B / ‖Wh τ 1‖, by positivity, fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk; rw [rhoW, dif_pos rfl, norm_zero]; positivity
  · have hkp : 0 < 2 * π * |(k : ℝ)| := by
      have : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
      positivity
    set y₀ := 1 / (2 * π * |(k : ℝ)|)
    have hy₀ : 0 < y₀ := by positivity
    have h := bco_eq_rhoW (N := N) (f := f) hτ0 hτ1 k hy₀
    have hw : whModal τ (2 * π * |(k : ℝ)|) y₀ = Wh τ 1 := by
      rw [whModal]; congr 1; simp only [y₀]; field_simp
    rw [hw] at h
    have := hB k y₀ hy₀
    rw [h, norm_mul] at this
    rw [le_div_iff₀ hW]
    exact this
