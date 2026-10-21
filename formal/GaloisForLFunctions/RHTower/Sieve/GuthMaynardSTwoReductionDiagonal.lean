import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionPlanes
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum

/-!
# Guth–Maynard §6: the diagonal of `S₂`

From `S₂ = 3N³ Σ_{x,y,z∈W} A(x−y) A(y−z) ĥ_{z−x}(0)` (`gmS2_eq_three_mul`), Guth–Maynard
(proof of Proposition 6.1) keep only `z = x`: for `z ≠ x` the factor `ĥ_{z−x}(0)` is tiny by (5.1),
and for `z = x` the conjugation symmetry `ĥ_{−t}(ξ) = conj ĥ_t(−ξ)` of the real bump gives
`A(y−x) = conj A(x−y)`, whence

`S₂ = 3N³ ĥ₀(0) Σ_{x,y∈W} |A(x−y)|² + E`,   `|E| ≤ 3N³ |W|³ α² β`,

where `α` bounds `|A|` on `W − W` and `β` bounds `|ĥ_{z−x}(0)|` for `z ≠ x`.  For a `δ`-separated
`W`, Lemma 4.3(2) at `ξ = 0` gives `β = B_j / δ^j` for every `j`.
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform ComplexConjugate

noncomputable section

namespace RHTower.GuthMaynard

local notation "P" => CGLProposition51PuncturedFrequency

/-- Negation on the punctured integers. -/
def gmPuncturedNeg : P ≃ P :=
  Equiv.subtypeEquiv (Equiv.neg ℤ) (fun a => by simp)

/-- **Conjugation symmetry.** `A(−τ) = conj A(τ)` for the real Chen–Gupta–Li bump. -/
theorem gmNonzero_neg (w : CGLRealSmoothBump) (N τ : ℝ) :
    gmNonzero w N (-τ) = conj (gmNonzero w N τ) := by
  unfold gmNonzero cglGMNonzeroModeSum
  rw [Complex.conj_tsum]
  have hterm : ∀ m : P, 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump (-τ) : ℝ → ℂ) ((m : ℝ) * N) =
      conj (𝓕 (cglSmoothBumpHt w.toCGLSmoothBump τ : ℝ → ℂ) (((gmPuncturedNeg m : P) : ℝ) * N)) := by
    intro m
    have hcast : (((gmPuncturedNeg m : P) : ℤ) : ℝ) * N = -((m : ℝ) * N) := by
      simp [gmPuncturedNeg]
    rw [hcast, cglGM_fourier_neg_eq_conj w τ, Complex.conj_conj]
  rw [tsum_congr hterm]
  exact gmPuncturedNeg.tsum_eq
    (fun m : P => conj (𝓕 (cglSmoothBumpHt w.toCGLSmoothBump τ : ℝ → ℂ) ((m : ℝ) * N)))

/-- `F(x,y,x) = ĥ₀(0) |A(x−y)|²`. -/
theorem gmS2Kernel_diag (w : CGLRealSmoothBump) (N x y : ℝ) :
    gmS2Kernel w N x y x = gmHat w 0 0 * ((‖gmNonzero w N (x - y)‖ ^ 2 : ℝ) : ℂ) := by
  rw [gmS2Kernel, show y - x = -(x - y) by ring, gmNonzero_neg, sub_self, Complex.mul_conj']
  push_cast
  ring

/-- The diagonal sum `D = Σ_{x,y∈W} |A(x−y)|²`. -/
def gmS2Diagonal (w : CGLRealSmoothBump) (N : ℝ) (W : Finset ℝ) : ℝ :=
  ∑ x ∈ W, ∑ y ∈ W, ‖gmNonzero w N (x - y)‖ ^ 2

/-- **Diagonal extraction (exact).**
`Σ_{x,y,z∈W} F = ĥ₀(0) Σ_{x,y} |A(x−y)|² + Σ_{x,y} Σ_{z ∈ W, z ≠ x} F`. -/
theorem sum_gmS2Kernel_eq_diag_add (w : CGLRealSmoothBump) (N : ℝ) (W : Finset ℝ) :
    ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W, gmS2Kernel w N x y z =
      gmHat w 0 0 * (gmS2Diagonal w N W : ℂ) +
        ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W.erase x, gmS2Kernel w N x y z := by
  classical
  rw [gmS2Diagonal]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.add_sum_erase W _ hx, gmS2Kernel_diag]
  push_cast
  ring

/-- **The off-diagonal error.** If `|A| ≤ α` on `W − W` and `|ĥ_{z−x}(0)| ≤ β` for `z ≠ x`, then
`‖S₂ − 3N³ ĥ₀(0) D‖ ≤ 3N³ |W|³ α² β`. -/
theorem norm_gmS2_sub_diag_le (w : CGLRealSmoothBump) {N α β : ℝ} (hN : 0 < N)
    (W : Finset ℝ) (hα : ∀ x ∈ W, ∀ y ∈ W, ‖gmNonzero w N (x - y)‖ ≤ α) (hβ0 : 0 ≤ β)
    (hβ : ∀ x ∈ W, ∀ z ∈ W, z ≠ x → ‖gmHat w (z - x) 0‖ ≤ β) :
    ‖gmS2 w N W - 3 * ((N : ℂ) ^ 3 * (gmHat w 0 0 * (gmS2Diagonal w N W : ℂ)))‖ ≤
      3 * N ^ 3 * ((W.card : ℝ) ^ 3 * (α ^ 2 * β)) := by
  classical
  rw [gmS2_eq_three_mul w hN W, sum_gmS2Kernel_eq_diag_add]
  have hdiff : 3 * ((N : ℂ) ^ 3 * (gmHat w 0 0 * (gmS2Diagonal w N W : ℂ) +
      ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W.erase x, gmS2Kernel w N x y z)) -
      3 * ((N : ℂ) ^ 3 * (gmHat w 0 0 * (gmS2Diagonal w N W : ℂ))) =
      ((3 * N ^ 3 : ℝ) : ℂ) * ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W.erase x, gmS2Kernel w N x y z := by
    push_cast
    ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 3 * N ^ 3)
  have hterm : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W.erase x, ‖gmS2Kernel w N x y z‖ ≤ α ^ 2 * β := by
    intro x hx y hy z hz
    have hzW := Finset.mem_of_mem_erase hz
    have hzx := Finset.ne_of_mem_erase hz
    have h1 := hα x hx y hy
    have h2 := hα y hy z hzW
    have h3 := hβ x hx z hzW hzx
    have hα0 : 0 ≤ α := (norm_nonneg _).trans h1
    rw [gmS2Kernel, norm_mul, norm_mul, sq]
    exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hα0) h3 (norm_nonneg _)
      (mul_nonneg hα0 hα0)
  have hcard : ∀ x ∈ W, ((W.erase x).card : ℝ) ≤ W.card := fun x _ => by
    exact_mod_cast Finset.card_erase_le
  calc ‖∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W.erase x, gmS2Kernel w N x y z‖
      ≤ ∑ x ∈ W, ∑ y ∈ W, ∑ z ∈ W.erase x, ‖gmS2Kernel w N x y z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => norm_sum_le _ _))
    _ ≤ ∑ x ∈ W, ∑ y ∈ W, (W.card : ℝ) * (α ^ 2 * β) := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        calc ∑ z ∈ W.erase x, ‖gmS2Kernel w N x y z‖
            ≤ ((W.erase x).card : ℝ) * (α ^ 2 * β) := by
              have := Finset.sum_le_card_nsmul (W.erase x) (fun z => ‖gmS2Kernel w N x y z‖)
                (α ^ 2 * β) (hterm x hx y hy)
              simpa [nsmul_eq_mul] using this
          _ ≤ (W.card : ℝ) * (α ^ 2 * β) :=
              mul_le_mul_of_nonneg_right (hcard x hx) (by positivity)
    _ = (W.card : ℝ) ^ 3 * (α ^ 2 * β) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Lemma 4.3(2) at `ξ = 0`: `|ĥ_τ(0)| ≤ B_j / |τ|^j` for `τ ≠ 0`. -/
theorem norm_gmHat_zero_le (w : CGLRealSmoothBump) (j : ℕ) {τ : ℝ} (hτ : τ ≠ 0) :
    ‖gmHat w τ 0‖ ≤ cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump j / |τ| ^ j := by
  have h := cglSmoothBumpHt_allOrder_reciprocalParameter_fourier_decay w.toCGLSmoothBump j τ 0
  rw [abs_zero, add_zero, one_pow, mul_one] at h
  rw [le_div_iff₀ (pow_pos (abs_pos.mpr hτ) j), mul_comm]
  exact h

/-- (5.1) for a `δ`-separated set: `|ĥ_{z−x}(0)| ≤ B_j / δ^j` for `z ≠ x` in `W`. -/
theorem norm_gmHat_zero_le_of_separated (w : CGLRealSmoothBump) (j : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {W : Finset ℝ} (hW : IsSeparated δ W) {x z : ℝ} (hx : x ∈ W) (hz : z ∈ W) (hzx : z ≠ x) :
    ‖gmHat w (z - x) 0‖ ≤ cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump j / δ ^ j := by
  have hsep := hW z hz x hx hzx
  have hτ : z - x ≠ 0 := sub_ne_zero.mpr hzx
  refine (norm_gmHat_zero_le w j hτ).trans ?_
  have hB : 0 ≤ cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump j := by
    have := (norm_nonneg (gmHat w (z - x) 0)).trans (norm_gmHat_zero_le w j hτ)
    exact (div_nonneg_iff.mp this).elim (fun h => h.1)
      (fun h => absurd h.2 (not_le.mpr (pow_pos (abs_pos.mpr hτ) j)))
  exact div_le_div_of_nonneg_left hB (pow_pos hδ j) (pow_le_pow_left₀ hδ.le hsep j)

end RHTower.GuthMaynard
