import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# Boundary values of top Takagi profiles along the aperture flow

Let `p_1, …, p_m` be distinct nodes with positive real part and let `H = [(p_j + p̄_k)⁻¹]` be the
Gram matrix of the exponentials `e^{−p̄_k s}` in `L²(0, ∞)`. A coefficient vector `y` is the profile
`w(s) = Σ_k y_k e^{−p̄_k s}` with `‖w‖² = y*Hy`, `(Hy)_j = ∫₀^∞ e^{−p_j s} w(s) ds` and boundary value
`w(0) = Σ_k y_k`. For masses `μ` the Takagi form is `T_μ(y) = Σ_j μ_j ((Hy)_j)²`, and a top vector
maximizes `|T_μ(y)| / ‖w‖²`.

* `hGram` is positive definite (`gNorm_pos`), through the integral representation and the Cauchy
  determinant.
* **Boundary law** (`IsTop.boundary_law`). At a top vector with value `N` and phase
  `c = conj T / |T|`, `Re(c Σ_j p_j μ_j (Hy)_j²) = (N/2)|Σ_k y_k|²`. The proof uses the first
  variation `c μ_j (Hy)_j = N ȳ_j` and the displacement identity `p_j H_jk + H_jk p̄_k = 1`. So the
  derivative of the top value along the flow `μ_j ↦ μ_j e^{2a p_j}` is `N |w(0)|² / ‖w‖²`.

**Theorem** (`exists_boundary_nondegenerate_window`). Suppose all nodes have the same real part
`δ > 0` and the masses `M_j` are positive. Along the phase orbit `μ_j(a) = M_j e^{2a(p_j − δ)}`
there is a length `L` such that every window `[a₀, a₀ + L]` contains an aperture at which top
vectors exist and every top vector has `Σ_k y_k ≠ 0`.

**Proof.** Otherwise, for every `a ∈ [a₀, a₀ + L]` some top vector of the flow `M_j e^{2a p_j}` has `w(0) = 0`.
The boundary law then makes the top value `N(a)` satisfy
`N(a − h) ≥ N(a) − K e^{2aδ} h²` for small `h`. Chaining gives `N(a₀) ≥ N(a₀ + L)`.
But `N(a) = e^{2aδ} Λ(a)`, where the phase value `Λ` is bounded above and below by positive
constants (the lower bound comes from the vector with `Hy = e_{j₀}`), and `L` is chosen so that
`e^{2δL}` exceeds their ratio. This is a contradiction.
-/

namespace GaloisForLFunctions.HTGeometry.CauchyTakagi

open Matrix Complex MeasureTheory Set Filter
open scoped ComplexConjugate

noncomputable section

variable {m : ℕ}

/-! ## The Hermitian Cauchy Gram matrix -/

/-- The Hermitian Cauchy Gram matrix `[(p_j + p̄_k)⁻¹]` of the exponentials `e^{−p̄_k s}`. -/
def hGram (p : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun j k => (p j + conj (p k))⁻¹

theorem hGram_apply (p : Fin m → ℂ) (j k : Fin m) : hGram p j k = (p j + conj (p k))⁻¹ := rfl

theorem conj_hGram (p : Fin m → ℂ) (j k : Fin m) : conj (hGram p j k) = hGram p k j := by
  simp [hGram_apply, map_inv₀, add_comm]

theorem re_add_conj_pos {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (j k : Fin m) :
    0 < (p j + conj (p k)).re := by
  simp only [add_re, conj_re]; linarith [hp j, hp k]

theorem add_conj_ne_zero {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (j k : Fin m) :
    p j + conj (p k) ≠ 0 := fun h => by
  have := re_add_conj_pos hp j k
  rw [h, zero_re] at this
  exact lt_irrefl 0 this

/-- The displacement identity `p_j H_jk + H_jk p̄_k = 1`. -/
theorem displacement {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (j k : Fin m) :
    p j * hGram p j k + hGram p j k * conj (p k) = 1 := by
  have h := add_conj_ne_zero hp j k
  rw [hGram_apply]
  field_simp

theorem det_hGram_ne_zero {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p) :
    (hGram p).det ≠ 0 := by
  have hc : hGram p = cauchyMatrix p (fun k => conj (p k)) := by
    ext j k; simp [hGram_apply, cauchyMatrix_apply]
  have hdet := det_cauchyMatrix p (fun k => conj (p k)) (fun j k => add_conj_ne_zero hp j k)
  have hne : ∏ i, ∏ j ∈ Finset.Ioi i, ((p i - p j) * (conj (p i) - conj (p j))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    have h1 : p i - p j ≠ 0 := sub_ne_zero.mpr (hinj.ne hij)
    have h2 : conj (p i) - conj (p j) ≠ 0 := by
      rw [← map_sub]; exact (map_ne_zero _).mpr h1
    exact mul_ne_zero h1 h2
  intro h0
  rw [hc] at h0
  rw [h0, zero_mul] at hdet
  exact hne hdet.symm

/-! ## Integral representation and positivity -/

/-- The profile `w(s) = Σ_k y_k e^{−p̄_k s}`. -/
def profile (p y : Fin m → ℂ) (s : ℝ) : ℂ := ∑ k, y k * Complex.exp (-conj (p k) * s)

theorem integral_exp_neg_mul_Ioi {q : ℂ} (hq : 0 < q.re) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (-q * s) = q⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (by simpa using hq) 0]
  simp [neg_div, div_neg]

theorem integrableOn_exp_neg_mul {q : ℂ} (hq : 0 < q.re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-q * s)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hq) 0

theorem exp_mul_profile_term (p y : Fin m → ℂ) (j k : Fin m) (s : ℝ) :
    Complex.exp (-p j * s) * (y k * Complex.exp (-conj (p k) * s)) =
      y k * Complex.exp (-(p j + conj (p k)) * s) := by
  rw [show -(p j + conj (p k)) * (s : ℂ) = -p j * s + -conj (p k) * s by ring, Complex.exp_add]
  ring

theorem integrableOn_exp_mul_profile {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (y : Fin m → ℂ)
    (j : Fin m) : IntegrableOn (fun s : ℝ => Complex.exp (-p j * s) * profile p y s) (Ioi 0) := by
  simp only [profile, Finset.mul_sum, exp_mul_profile_term]
  exact integrable_finsetSum _ fun k _ =>
    (integrableOn_exp_neg_mul (re_add_conj_pos hp j k)).const_mul (y k)

/-- `(Hy)_j = ∫₀^∞ e^{−p_j s} w(s) ds`. -/
theorem hGram_mulVec_eq_integral {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (y : Fin m → ℂ)
    (j : Fin m) :
    (hGram p *ᵥ y) j = ∫ s in Ioi (0 : ℝ), Complex.exp (-p j * s) * profile p y s := by
  simp only [profile, Finset.mul_sum, exp_mul_profile_term]
  rw [integral_finsetSum _ fun k _ =>
    (integrableOn_exp_neg_mul (re_add_conj_pos hp j k)).const_mul (y k)]
  simp only [mulVec, dotProduct, hGram_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_exp_neg_mul_Ioi (re_add_conj_pos hp j k)]
  ring

theorem conj_profile (p y : Fin m → ℂ) (s : ℝ) :
    conj (profile p y s) = ∑ j, conj (y j) * Complex.exp (-p j * s) := by
  simp [profile, map_sum, ← Complex.exp_conj]

/-- `y*Hy = ∫₀^∞ |w(s)|² ds`. -/
theorem star_dotProduct_hGram_eq_integral {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (y : Fin m → ℂ) :
    star y ⬝ᵥ (hGram p *ᵥ y) = ((∫ s in Ioi (0 : ℝ), ‖profile p y s‖ ^ 2 : ℝ) : ℂ) := by
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin m)), Integrable
      (fun s : ℝ => conj (y j) * (Complex.exp (-p j * s) * profile p y s))
      (volume.restrict (Ioi 0)) := fun j _ =>
    (integrableOn_exp_mul_profile hp y j).const_mul _
  simp only [dotProduct, Pi.star_apply, Complex.star_def, hGram_mulVec_eq_integral hp]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hint, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  have h := Complex.normSq_eq_conj_mul_self (z := profile p y s)
  rw [Complex.normSq_eq_norm_sq, conj_profile, Finset.sum_mul] at h
  push_cast at h ⊢
  rw [h]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The squared norm `‖w‖² = y*Hy` of the profile. -/
def gNorm (p y : Fin m → ℂ) : ℝ := (star y ⬝ᵥ (hGram p *ᵥ y)).re

theorem gNorm_nonneg {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (y : Fin m → ℂ) :
    0 ≤ gNorm p y := by
  rw [gNorm, star_dotProduct_hGram_eq_integral hp, ofReal_re]
  exact setIntegral_nonneg measurableSet_Ioi fun s _ => by positivity

theorem gNorm_pos {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    {y : Fin m → ℂ} (hy : y ≠ 0) : 0 < gNorm p y := by
  rcases (gNorm_nonneg hp y).lt_or_eq with h | h
  · exact h
  exfalso
  rw [gNorm, star_dotProduct_hGram_eq_integral hp, ofReal_re] at h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun s => ‖profile p y s‖ ^ 2 :=
    Eventually.of_forall fun s => by positivity
  have hI : Integrable (fun s => ‖profile p y s‖ ^ 2) (volume.restrict (Ioi 0)) := by
    have hc : Integrable (fun s : ℝ => ∑ j, conj (y j) * (Complex.exp (-p j * s) * profile p y s))
        (volume.restrict (Ioi 0)) :=
      integrable_finsetSum _ fun j _ => (integrableOn_exp_mul_profile hp y j).const_mul _
    refine hc.re.congr (Eventually.of_forall fun s => ?_)
    have h := Complex.normSq_eq_conj_mul_self (z := profile p y s)
    rw [Complex.normSq_eq_norm_sq, conj_profile, Finset.sum_mul] at h
    simp only [RCLike.re_to_complex]
    rw [show (∑ j, conj (y j) * (Complex.exp (-p j * s) * profile p y s)) =
      ∑ j, conj (y j) * Complex.exp (-p j * s) * profile p y s from
        Finset.sum_congr rfl fun j _ => by ring, ← h]
    norm_cast
  have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hI).mp h.symm
  apply hy
  apply Matrix.eq_zero_of_mulVec_eq_zero (det_hGram_ne_zero hp hinj)
  funext j
  rw [hGram_mulVec_eq_integral hp, Pi.zero_apply]
  have hz : (fun s : ℝ => Complex.exp (-p j * s) * profile p y s) =ᵐ[volume.restrict (Ioi 0)]
      0 := by
    filter_upwards [h0] with s hs
    have : profile p y s = 0 := by simpa using hs
    simp [this]
  rw [integral_congr_ae hz]
  simp

/-! ## The Takagi form and its first variation -/

/-- The Takagi form `T_μ(y) = Σ_j μ_j ((Hy)_j)²`. -/
def tForm (p μ y : Fin m → ℂ) : ℂ := ∑ j, μ j * (hGram p *ᵥ y) j ^ 2

theorem star_dotProduct_hGram_swap (p y d : Fin m → ℂ) :
    star y ⬝ᵥ (hGram p *ᵥ d) = conj (star d ⬝ᵥ (hGram p *ᵥ y)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, map_sum, map_mul,
    Complex.conj_conj, conj_hGram, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tForm_add_smul (p μ y d : Fin m → ℂ) (ε : ℝ) :
    tForm p μ (y + (ε : ℂ) • d) = tForm p μ y +
      ((2 * ε : ℝ) : ℂ) * ∑ j, μ j * (hGram p *ᵥ y) j * (hGram p *ᵥ d) j +
        ((ε ^ 2 : ℝ) : ℂ) * tForm p μ d := by
  simp only [tForm, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem gNorm_add_smul (p y d : Fin m → ℂ) (ε : ℝ) :
    gNorm p (y + (ε : ℂ) • d) =
      gNorm p y + 2 * ε * (star d ⬝ᵥ (hGram p *ᵥ y)).re + ε ^ 2 * gNorm p d := by
  have hsw := star_dotProduct_hGram_swap p y d
  have hc : star (y + (ε : ℂ) • d) ⬝ᵥ (hGram p *ᵥ (y + (ε : ℂ) • d)) =
      star y ⬝ᵥ (hGram p *ᵥ y) + (ε : ℂ) * (star y ⬝ᵥ (hGram p *ᵥ d)) +
        (ε : ℂ) * (star d ⬝ᵥ (hGram p *ᵥ y)) + (ε : ℂ) ^ 2 * (star d ⬝ᵥ (hGram p *ᵥ d)) := by
    simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [gNorm, hc, hsw, gNorm, gNorm]
  simp only [add_re, re_ofReal_mul, conj_re, ← ofReal_pow]
  ring

theorem eq_zero_of_forall_quad_le {L Q : ℝ} (h : ∀ ε : ℝ, 2 * ε * L + ε ^ 2 * Q ≤ 0) :
    L = 0 := by
  by_contra hL
  set t : ℝ := 1 / (|Q| + 1) with ht_def
  have ht : 0 < t := by positivity
  have htQ : t * |Q| < 1 := by
    rw [ht_def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have h1 := h (t * L)
  have h2 : 0 < 2 + t * Q := by
    have := neg_abs_le Q
    nlinarith
  have h3 : 0 < t * L ^ 2 * (2 + t * Q) := by positivity
  nlinarith

/-- **First variation.** If `y` maximizes `Re(c T_μ(z)) − N ‖z‖²`, the linear part vanishes. -/
theorem first_variation {p μ y : Fin m → ℂ} {c : ℂ} {N : ℝ}
    (hle : ∀ z, (c * tForm p μ z).re ≤ N * gNorm p z)
    (heq : (c * tForm p μ y).re = N * gNorm p y) (d : Fin m → ℂ) :
    (c * ∑ j, μ j * (hGram p *ᵥ y) j * (hGram p *ᵥ d) j).re =
      N * (star d ⬝ᵥ (hGram p *ᵥ y)).re := by
  have key : ∀ ε : ℝ, 2 * ε * ((c * ∑ j, μ j * (hGram p *ᵥ y) j * (hGram p *ᵥ d) j).re -
      N * (star d ⬝ᵥ (hGram p *ᵥ y)).re) +
        ε ^ 2 * ((c * tForm p μ d).re - N * gNorm p d) ≤ 0 := by
    intro ε
    have h := hle (y + (ε : ℂ) • d)
    rw [tForm_add_smul, gNorm_add_smul] at h
    simp only [mul_add, add_re, mul_left_comm c ((2 * ε : ℝ) : ℂ),
      mul_left_comm c ((ε ^ 2 : ℝ) : ℂ), re_ofReal_mul] at h
    nlinarith
  linarith [eq_zero_of_forall_quad_le key]

/-- **Lagrange relation.** At a maximizer of `Re(c T_μ(z)) − N ‖z‖²`, `c μ_j (Hy)_j = N ȳ_j`. -/
theorem lagrange {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    {c : ℂ} {N : ℝ} (hle : ∀ z, (c * tForm p μ z).re ≤ N * gNorm p z)
    (heq : (c * tForm p μ y).re = N * gNorm p y) (j : Fin m) :
    c * (μ j * (hGram p *ᵥ y) j) = N * conj (y j) := by
  set v := hGram p *ᵥ y with hv_def
  have hcol : ∀ (k : Fin m) (e : ℂ) (i : Fin m), (hGram p *ᵥ Pi.single k e) i = hGram p i k * e := by
    intro k e i
    simp [mulVec, dotProduct, Pi.single_apply]
  have hdot : ∀ (k : Fin m) (e : ℂ), star (Pi.single k e) ⬝ᵥ v = conj e * v k := by
    intro k e
    rw [Pi.star_single]
    simp [dotProduct, Pi.single_apply]
  have hk : ∀ k, c * ∑ i, μ i * v i * hGram p i k = N * conj (v k) := by
    intro k
    have h1 := first_variation hle heq (Pi.single k 1)
    have h2 := first_variation hle heq (Pi.single k I)
    simp only [hcol, hdot, ← hv_def] at h1 h2
    have e1 : c * ∑ i, μ i * v i * (hGram p i k * 1) = c * ∑ i, μ i * v i * hGram p i k := by
      simp
    have e2 : c * ∑ i, μ i * v i * (hGram p i k * I) = I * (c * ∑ i, μ i * v i * hGram p i k) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1] at h1
    rw [e2] at h2
    set A := c * ∑ i, μ i * v i * hGram p i k with hA
    have h1' : A.re = N * (v k).re := by simpa using h1
    have h2' : -A.im = N * (v k).im := by simpa [Complex.mul_re] using h2
    apply Complex.ext
    · rw [h1', re_ofReal_mul, conj_re]
    · rw [im_ofReal_mul, conj_im]; linarith
  have hz : (hGram p)ᵀ *ᵥ (fun i => c * (μ i * v i) - N * conj (y i)) = 0 := by
    funext k
    have hvk : conj (v k) = ∑ i, hGram p i k * conj (y i) := by
      simp [hv_def, mulVec, dotProduct, map_sum, conj_hGram]
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib]
    have e1 : ∑ i, hGram p i k * (c * (μ i * v i)) = c * ∑ i, μ i * v i * hGram p i k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ i, hGram p i k * (N * conj (y i)) = N * conj (v k) := by
      rw [hvk, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2, hk k, sub_self]
  have hdet : ((hGram p)ᵀ).det ≠ 0 := by rw [det_transpose]; exact det_hGram_ne_zero hp hinj
  have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hz) j
  simp only [Pi.zero_apply] at this
  linear_combination this

/-- **Boundary law for a maximizer.** `Re(c Σ_j p_j μ_j (Hy)_j²) = (N/2)|Σ_k y_k|²`. -/
theorem boundary_law {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    {c : ℂ} {N : ℝ} (hle : ∀ z, (c * tForm p μ z).re ≤ N * gNorm p z)
    (heq : (c * tForm p μ y).re = N * gNorm p y) :
    (c * ∑ j, p j * μ j * (hGram p *ᵥ y) j ^ 2).re = N / 2 * ‖∑ j, y j‖ ^ 2 := by
  set v := hGram p *ᵥ y with hv_def
  have h1 : c * ∑ j, p j * μ j * v j ^ 2 = (N : ℂ) * ∑ j, conj (y j) * p j * v j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := lagrange hp hinj hle heq j
    rw [← hv_def] at this
    linear_combination (p j * v j) * this
  have hX : (∑ j, conj (y j) * p j * v j) + conj (∑ j, conj (y j) * p j * v j) =
      ∑ j, ∑ k, conj (y j) * y k := by
    simp only [hv_def, mulVec, dotProduct, map_sum, map_mul, Complex.conj_conj, conj_hGram,
      Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j k => y j * conj (p j) * (hGram p k j * conj (y k))),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := displacement hp j k
    linear_combination (conj (y j) * y k) * this
  have hS : (∑ j, ∑ k, conj (y j) * y k) = ((‖∑ j, y j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.sum_mul_sum, ← map_sum, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have h2 : (∑ j, conj (y j) * p j * v j).re = ‖∑ j, y j‖ ^ 2 / 2 := by
    have := congrArg Complex.re (hX.trans hS)
    rw [add_re, conj_re, ofReal_re] at this
    linarith
  rw [h1, re_ofReal_mul, h2]
  ring

/-! ## Top vectors -/

/-- `y` is a top Takagi vector for the masses `μ`: it maximizes `|T_μ(z)| / ‖z‖²`. -/
def IsTop (p μ y : Fin m → ℂ) : Prop :=
  y ≠ 0 ∧ ∀ z, ‖tForm p μ z‖ * gNorm p y ≤ ‖tForm p μ y‖ * gNorm p z

theorem tForm_smul (p μ z : Fin m → ℂ) (r : ℝ) :
    tForm p μ ((r : ℂ) • z) = (r : ℂ) ^ 2 * tForm p μ z := by
  simp only [tForm, mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gNorm_smul (p z : Fin m → ℂ) (r : ℝ) : gNorm p ((r : ℂ) • z) = r ^ 2 * gNorm p z := by
  have hc : star ((r : ℂ) • z) ⬝ᵥ (hGram p *ᵥ ((r : ℂ) • z)) =
      ((r ^ 2 : ℝ) : ℂ) * (star z ⬝ᵥ (hGram p *ᵥ z)) := by
    simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [gNorm, hc, re_ofReal_mul, gNorm]

theorem tForm_mass_smul (p μ z : Fin m → ℂ) (r : ℂ) :
    tForm p (fun j => r * μ j) z = r * tForm p μ z := by
  simp only [tForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isTop_mass_smul_iff (p μ y : Fin m → ℂ) {r : ℝ} (hr : 0 < r) :
    IsTop p (fun j => (r : ℂ) * μ j) y ↔ IsTop p μ y := by
  simp only [IsTop, tForm_mass_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, mul_assoc]
  refine and_congr Iff.rfl (forall_congr' fun z => ?_)
  exact mul_le_mul_iff_of_pos_left hr

theorem continuous_tForm (p μ : Fin m → ℂ) : Continuous (tForm p μ) := by
  unfold tForm; simp only [mulVec, dotProduct]; fun_prop

theorem continuous_gNorm (p : Fin m → ℂ) : Continuous (gNorm p) := by
  unfold gNorm; simp only [mulVec, dotProduct, Pi.star_apply]; fun_prop

/-- Every `z ≠ 0` is a positive real multiple of a unit vector. -/
theorem exists_unit_smul {z : Fin m → ℂ} (hz : z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : Fin m → ℂ) 1, z = (r : ℂ) • u := by
  refine ⟨‖z‖, norm_pos_iff.mpr hz, ((‖z‖⁻¹ : ℝ) : ℂ) • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [smul_smul, ← ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), ofReal_one, one_smul]

/-- **Top vectors exist.** -/
theorem exists_isTop {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (hm : 0 < m) (μ : Fin m → ℂ) : ∃ y, IsTop p μ y := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hS := isCompact_sphere (0 : Fin m → ℂ) 1
  have hne : (Metric.sphere (0 : Fin m → ℂ) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hpos : ∀ u ∈ Metric.sphere (0 : Fin m → ℂ) 1, 0 < gNorm p u := fun u hu =>
    gNorm_pos hp hinj (ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩)
  have hcont : ContinuousOn (fun z => ‖tForm p μ z‖ / gNorm p z) (Metric.sphere 0 1) :=
    ((continuous_tForm p μ).norm.continuousOn).div (continuous_gNorm p).continuousOn
      fun u hu => (hpos u hu).ne'
  obtain ⟨y, hyS, hymax⟩ := hS.exists_isMaxOn hne hcont
  have hy0 : y ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨y, hyS⟩
  refine ⟨y, hy0, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : tForm p μ 0 = 0 := by simp [tForm]
    have h1 : gNorm p 0 = 0 := by simp [gNorm]
    rw [h0, h1]; simp
  obtain ⟨r, hr, u, hu, rfl⟩ := exists_unit_smul hz
  have hmax := hymax hu
  simp only [mem_setOf_eq] at hmax
  rw [div_le_div_iff₀ (hpos u hu) (hpos y hyS)] at hmax
  rw [tForm_smul, gNorm_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  nlinarith [sq_nonneg r, hmax, mul_le_mul_of_nonneg_left hmax (sq_nonneg r)]

/-- A uniform bound `Σ_j M_j |(Hz)_j|² ≤ B ‖z‖²`. -/
theorem exists_mass_bound {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (M : Fin m → ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ∑ j, M j * ‖(hGram p *ᵥ z) j‖ ^ 2 ≤ B * gNorm p z := by
  set f : (Fin m → ℂ) → ℝ := fun z => (∑ j, M j * ‖(hGram p *ᵥ z) j‖ ^ 2) / gNorm p z
  have hpos : ∀ u ∈ Metric.sphere (0 : Fin m → ℂ) 1, 0 < gNorm p u := fun u hu =>
    gNorm_pos hp hinj (ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩)
  have hcont : ContinuousOn f (Metric.sphere 0 1) := by
    refine ContinuousOn.div ?_ (continuous_gNorm p).continuousOn fun u hu => (hpos u hu).ne'
    simp only [mulVec, dotProduct]
    exact Continuous.continuousOn (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin m → ℂ) 1).exists_bound_of_continuousOn hcont
  refine ⟨|C|, abs_nonneg C, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [gNorm]
  obtain ⟨r, hr, u, hu, rfl⟩ := exists_unit_smul hz
  have hb := (le_abs_self _).trans ((hC u hu).trans (le_abs_self C))
  simp only [f] at hb
  rw [div_le_iff₀ (hpos u hu)] at hb
  rw [gNorm_smul]
  have hsm : ∀ j, ‖(hGram p *ᵥ ((r : ℂ) • u)) j‖ ^ 2 = r ^ 2 * ‖(hGram p *ᵥ u) j‖ ^ 2 := by
    intro j
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    ring
  simp only [hsm]
  rw [show ∑ j, M j * (r ^ 2 * ‖(hGram p *ᵥ u) j‖ ^ 2) =
    r ^ 2 * ∑ j, M j * ‖(hGram p *ᵥ u) j‖ ^ 2 by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  nlinarith [sq_nonneg r]


/-- A vector with `Hy = e_{j₀}`. -/
theorem exists_unit_value {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (j₀ : Fin m) : ∃ y, y ≠ 0 ∧ hGram p *ᵥ y = Pi.single j₀ 1 := by
  have hu : IsUnit (hGram p).det := isUnit_iff_ne_zero.mpr (det_hGram_ne_zero hp hinj)
  have hval : hGram p *ᵥ ((hGram p)⁻¹ *ᵥ Pi.single j₀ 1) = Pi.single j₀ 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  refine ⟨(hGram p)⁻¹ *ᵥ Pi.single j₀ 1, fun h => ?_, hval⟩
  rw [h, mulVec_zero] at hval
  have := congrFun hval j₀
  simp at this

/-- At a top vector with nonzero value, the phase `c = conj T / |T|` and the value
`N = |T| / ‖y‖²` satisfy the variational inequality and equality. -/
theorem IsTop.variational {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (hinj : Function.Injective p) (hy : IsTop p μ y) (hT : tForm p μ y ≠ 0) :
    (∀ z, (conj (tForm p μ y) / (‖tForm p μ y‖ : ℂ) * tForm p μ z).re ≤
        ‖tForm p μ y‖ / gNorm p y * gNorm p z) ∧
      (conj (tForm p μ y) / (‖tForm p μ y‖ : ℂ) * tForm p μ y).re =
        ‖tForm p μ y‖ / gNorm p y * gNorm p y := by
  have hg := gNorm_pos hp hinj hy.1
  have hTn : 0 < ‖tForm p μ y‖ := norm_pos_iff.mpr hT
  have hc1 : ‖conj (tForm p μ y) / (‖tForm p μ y‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self hTn.ne']
  refine ⟨fun z => ?_, ?_⟩
  · refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, hc1, one_mul, div_mul_eq_mul_div, le_div_iff₀ hg]
    exact hy.2 z
  · rw [div_mul_cancel₀ _ hg.ne', div_mul_eq_mul_div, Complex.conj_mul', ← ofReal_pow,
      ← ofReal_div, ofReal_re, sq, mul_div_assoc, div_self hTn.ne', mul_one]

/-- **Boundary law at a top vector.** The derivative of the top value along `μ_j ↦ μ_j e^{2a p_j}`
is `N |w(0)|² / ‖w‖²` in the form `Re(c Σ_j p_j μ_j (Hy)_j²) = (N/2)|Σ_k y_k|²`. -/
theorem IsTop.boundary_law {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (hinj : Function.Injective p) (hy : IsTop p μ y) (hT : tForm p μ y ≠ 0) :
    (conj (tForm p μ y) / (‖tForm p μ y‖ : ℂ) * ∑ j, p j * μ j * (hGram p *ᵥ y) j ^ 2).re =
      ‖tForm p μ y‖ / gNorm p y / 2 * ‖∑ j, y j‖ ^ 2 :=
  GaloisForLFunctions.HTGeometry.CauchyTakagi.boundary_law hp hinj (hy.variational hp hinj hT).1
    (hy.variational hp hinj hT).2

/-! ## The aperture flow -/

/-- The aperture flow `μ_j(a) = M_j e^{2a p_j}`. -/
def flowMass (p : Fin m → ℂ) (M : Fin m → ℝ) (a : ℝ) (j : Fin m) : ℂ :=
  (M j : ℂ) * Complex.exp (2 * a * p j)

/-- The phase orbit `μ_j(a) = M_j e^{2a(p_j − δ)}`; for `p_j = δ − iτ_j` the phases are
`e^{−2iτ_j a}`. -/
def phaseMass (δ : ℝ) (p : Fin m → ℂ) (M : Fin m → ℝ) (a : ℝ) (j : Fin m) : ℂ :=
  (M j : ℂ) * Complex.exp (2 * a * (p j - δ))

theorem flowMass_eq (δ : ℝ) (p : Fin m → ℂ) (M : Fin m → ℝ) (a : ℝ) :
    flowMass p M a = fun j => ((Real.exp (2 * a * δ) : ℝ) : ℂ) * phaseMass δ p M a j := by
  funext j
  simp only [flowMass, phaseMass, ofReal_exp]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem norm_flowMass {δ : ℝ} {p : Fin m → ℂ} (hre : ∀ j, (p j).re = δ) {M : Fin m → ℝ}
    (hM : ∀ j, 0 ≤ M j) (a : ℝ) (j : Fin m) :
    ‖flowMass p M a j‖ = M j * Real.exp (2 * a * δ) := by
  rw [flowMass, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hM j),
    Complex.norm_exp]
  congr 2
  simp [mul_re, hre j]

theorem flowMass_sub (p : Fin m → ℂ) (M : Fin m → ℝ) (a h : ℝ) (j : Fin m) :
    flowMass p M (a - h) j = flowMass p M a j * Complex.exp (-(2 * h * p j)) := by
  simp only [flowMass]
  rw [mul_assoc (M j : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **One step of the flow at a top vector with vanishing boundary value.** -/
theorem step_lower {δ : ℝ} {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hre : ∀ j, (p j).re = δ)
    (hinj : Function.Injective p) {M : Fin m → ℝ} (hM : ∀ j, 0 ≤ M j) {B P : ℝ}
    (hB : ∀ z, ∑ j, M j * ‖(hGram p *ᵥ z) j‖ ^ 2 ≤ B * gNorm p z) (hP : ∀ j, ‖p j‖ ≤ P)
    {a h : ℝ} (hh : 0 ≤ h) (hhP : 2 * h * P ≤ 1) {y : Fin m → ℂ}
    (hy : IsTop p (flowMass p M a) y) (hT : tForm p (flowMass p M a) y ≠ 0)
    (hsum : ∑ j, y j = 0) :
    ‖tForm p (flowMass p M a) y‖ / gNorm p y - 4 * P ^ 2 * B * Real.exp (2 * a * δ) * h ^ 2 ≤
      ‖tForm p (flowMass p M (a - h)) y‖ / gNorm p y := by
  have hg := gNorm_pos hp hinj hy.1
  set T := tForm p (flowMass p M a) y with hT_def
  set c : ℂ := conj T / (‖T‖ : ℂ) with hc_def
  set v := hGram p *ᵥ y with hv_def
  have hTn : 0 < ‖T‖ := norm_pos_iff.mpr hT
  have hc1 : ‖c‖ = 1 := by
    rw [hc_def, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self hTn.ne']
  have hcT : (c * T).re = ‖T‖ := by
    have := (hy.variational hp hinj hT).2
    rw [div_mul_cancel₀ _ hg.ne'] at this
    exact this
  have hlaw : (c * ∑ j, p j * flowMass p M a j * v j ^ 2).re = 0 := by
    have := hy.boundary_law hp hinj hT
    rw [hsum, norm_zero, sq, mul_zero, mul_zero] at this
    exact this
  set E : Fin m → ℂ := fun j => Complex.exp (-(2 * h * p j)) - 1 - (-(2 * h * p j)) with hE_def
  have hE : ∀ j, ‖E j‖ ≤ 4 * h ^ 2 * P ^ 2 := by
    intro j
    have hn : ‖-(2 * h * p j)‖ = 2 * h * ‖p j‖ := by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh,
        Complex.norm_ofNat]
    have hpj := hP j
    have hle1 : ‖-(2 * h * p j)‖ ≤ 1 := by
      rw [hn]; nlinarith [norm_nonneg (p j)]
    refine (Complex.norm_exp_sub_one_sub_id_le hle1).trans ?_
    rw [hn]
    have h0 : 0 ≤ 2 * h * ‖p j‖ := by positivity
    have h2 : 2 * h * ‖p j‖ ≤ 2 * h * P := by nlinarith
    calc (2 * h * ‖p j‖) ^ 2 ≤ (2 * h * P) ^ 2 := pow_le_pow_left₀ h0 h2 2
      _ = 4 * h ^ 2 * P ^ 2 := by ring
  have hsplit : tForm p (flowMass p M (a - h)) y = T +
      ((-(2 * h) : ℝ) : ℂ) * (∑ j, p j * flowMass p M a j * v j ^ 2) +
        ∑ j, flowMass p M a j * v j ^ 2 * E j := by
    simp only [tForm, flowMass_sub, hT_def, ← hv_def, hE_def, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hR : ‖∑ j, flowMass p M a j * v j ^ 2 * E j‖ ≤
      4 * h ^ 2 * P ^ 2 * Real.exp (2 * a * δ) * (B * gNorm p y) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j, ‖flowMass p M a j * v j ^ 2 * E j‖ ≤
        4 * h ^ 2 * P ^ 2 * Real.exp (2 * a * δ) * (M j * ‖v j‖ ^ 2) := by
      intro j
      rw [norm_mul, norm_mul, norm_pow, norm_flowMass hre hM]
      have := hE j
      have h0 : 0 ≤ M j * Real.exp (2 * a * δ) * ‖v j‖ ^ 2 := by
        have := hM j; positivity
      calc M j * Real.exp (2 * a * δ) * ‖v j‖ ^ 2 * ‖E j‖
          ≤ M j * Real.exp (2 * a * δ) * ‖v j‖ ^ 2 * (4 * h ^ 2 * P ^ 2) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [← Finset.mul_sum]
    have hK : 0 ≤ 4 * h ^ 2 * P ^ 2 * Real.exp (2 * a * δ) := by positivity
    exact mul_le_mul_of_nonneg_left (hB y) hK
  have hre_low : ‖T‖ - 4 * h ^ 2 * P ^ 2 * Real.exp (2 * a * δ) * (B * gNorm p y) ≤
      ‖tForm p (flowMass p M (a - h)) y‖ := by
    have h1 : (c * tForm p (flowMass p M (a - h)) y).re ≤ ‖tForm p (flowMass p M (a - h)) y‖ := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, hc1, one_mul]
    have h2 : (c * tForm p (flowMass p M (a - h)) y).re = ‖T‖ + -(2 * h) *
        (c * ∑ j, p j * flowMass p M a j * v j ^ 2).re +
          (c * ∑ j, flowMass p M a j * v j ^ 2 * E j).re := by
      rw [hsplit, mul_add, mul_add, add_re, add_re, hcT, mul_left_comm, re_ofReal_mul]
    have h3 : -‖∑ j, flowMass p M a j * v j ^ 2 * E j‖ ≤
        (c * ∑ j, flowMass p M a j * v j ^ 2 * E j).re := by
      have := Complex.abs_re_le_norm (c * ∑ j, flowMass p M a j * v j ^ 2 * E j)
      rw [norm_mul, hc1, one_mul] at this
      linarith [neg_abs_le (c * ∑ j, flowMass p M a j * v j ^ 2 * E j).re]
    rw [hlaw, mul_zero, add_zero] at h2
    linarith
  rw [div_sub' hg.ne', div_le_div_iff_of_pos_right hg]
  nlinarith [hre_low]

/-- **Boundary nondegeneracy along the phase orbit, in windows of bounded length.** For distinct
nodes of common real part `δ > 0` and positive masses there is a length `L > 0` such that every
window `[a₀, a₀ + L]` of the phase orbit `M_j e^{2a(p_j − δ)}` contains an aperture at which top
Takagi vectors exist and all of them have nonzero boundary value `w(0) = Σ_k y_k`. -/
theorem exists_boundary_nondegenerate_window {δ : ℝ} (hδ : 0 < δ) {p : Fin m → ℂ}
    (hre : ∀ j, (p j).re = δ) (hinj : Function.Injective p) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j)
    (hm : 0 < m) :
    ∃ L : ℝ, 0 < L ∧ ∀ a₀ : ℝ, ∃ a, a₀ ≤ a ∧ a ≤ a₀ + L ∧
      (∃ y, IsTop p (phaseMass δ p M a) y) ∧
        ∀ y, IsTop p (phaseMass δ p M a) y → ∑ j, y j ≠ 0 := by
  have hp : ∀ j, 0 < (p j).re := fun j => (hre j).symm ▸ hδ
  have hM0 : ∀ j, 0 ≤ M j := fun j => (hM j).le
  have hiff : ∀ a y, IsTop p (flowMass p M a) y ↔ IsTop p (phaseMass δ p M a) y := fun a y => by
    rw [flowMass_eq δ]; exact isTop_mass_smul_iff _ _ _ (Real.exp_pos _)
  obtain ⟨B, hB0, hB⟩ := exists_mass_bound hp hinj M
  set P : ℝ := ∑ j, ‖p j‖ with hP_def
  have hP : ∀ j, ‖p j‖ ≤ P := fun j =>
    Finset.single_le_sum (fun i _ => norm_nonneg (p i)) (Finset.mem_univ j)
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  set j₀ : Fin m := ⟨0, hm⟩
  obtain ⟨y₁, hy₁, hHy₁⟩ := exists_unit_value hp hinj j₀
  have hg₁ := gNorm_pos hp hinj hy₁
  set c₀ : ℝ := M j₀ / gNorm p y₁ with hc₀_def
  have hc₀ : 0 < c₀ := div_pos (hM j₀) hg₁
  set L : ℝ := (B / c₀ + 1) / δ with hL_def
  have hL : 0 < L := by
    have : 0 ≤ B / c₀ := div_nonneg hB0 hc₀.le
    positivity
  refine ⟨L, hL, fun a₀ => ?_⟩
  by_contra hcon
  push Not at hcon
  have hdeg : ∀ a : ℝ, ∃ y, a₀ ≤ a → a ≤ a₀ + L →
      IsTop p (flowMass p M a) y ∧ ∑ j, y j = 0 := by
    intro a
    by_cases ha : a₀ ≤ a ∧ a ≤ a₀ + L
    · obtain ⟨y₀, hy₀⟩ := exists_isTop hp hinj hm (phaseMass δ p M a)
      obtain ⟨y, hy, hs⟩ := hcon a ha.1 ha.2 ⟨y₀, hy₀⟩
      exact ⟨y, fun _ _ => ⟨(hiff a y).mpr hy, hs⟩⟩
    · exact ⟨0, fun h h' => absurd ⟨h, h'⟩ ha⟩
  choose Y hY using hdeg
  set N : ℝ → ℝ := fun a => ‖tForm p (flowMass p M a) (Y a)‖ / gNorm p (Y a) with hN_def
  have hF1 : ∀ a, a₀ ≤ a → a ≤ a₀ + L → ∀ z, ‖tForm p (flowMass p M a) z‖ ≤ N a * gNorm p z := by
    intro a ha ha' z
    have hy := (hY a ha ha').1
    have hg := gNorm_pos hp hinj hy.1
    rw [hN_def, div_mul_eq_mul_div, le_div_iff₀ hg]
    exact hy.2 z
  have hF2 : ∀ a, a₀ ≤ a → a ≤ a₀ + L → c₀ * Real.exp (2 * a * δ) ≤ N a := by
    intro a ha ha'
    have h1 := hF1 a ha ha' y₁
    have hT1 : tForm p (flowMass p M a) y₁ = flowMass p M a j₀ := by
      simp [tForm, hHy₁, Pi.single_apply]
    rw [hT1, norm_flowMass hre hM0] at h1
    rw [hc₀_def, div_mul_eq_mul_div, div_le_iff₀ hg₁]
    linarith
  have hF3 : ∀ a, a₀ ≤ a → a ≤ a₀ + L → N a ≤ B * Real.exp (2 * a * δ) := by
    intro a ha ha'
    have hy := (hY a ha ha').1
    have hg := gNorm_pos hp hinj hy.1
    have h1 : ‖tForm p (flowMass p M a) (Y a)‖ ≤
        Real.exp (2 * a * δ) * (B * gNorm p (Y a)) := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ j, ‖flowMass p M a j * (hGram p *ᵥ Y a) j ^ 2‖ =
          Real.exp (2 * a * δ) * (M j * ‖(hGram p *ᵥ Y a) j‖ ^ 2) := by
        intro j
        rw [norm_mul, norm_pow, norm_flowMass hre hM0]
        ring
      simp only [hterm, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hB _) (Real.exp_pos _).le
    rw [hN_def, div_le_iff₀ hg]
    linarith
  have hF4 : ∀ a h, a₀ ≤ a - h → a ≤ a₀ + L → 0 ≤ h → 2 * h * P ≤ 1 →
      N a - 4 * P ^ 2 * B * Real.exp (2 * a * δ) * h ^ 2 ≤ N (a - h) := by
    intro a h hah ha' hh hhP
    have ha : a₀ ≤ a := by linarith
    have hy := (hY a ha ha').1
    have hT : tForm p (flowMass p M a) (Y a) ≠ 0 := by
      intro h0
      have := hF2 a ha ha'
      rw [hN_def] at this
      simp only [h0, norm_zero, zero_div] at this
      have : 0 < c₀ * Real.exp (2 * a * δ) := mul_pos hc₀ (Real.exp_pos _)
      linarith
    have hstep := step_lower hp hre hinj hM0 hB hP hh hhP hy hT (hY a ha ha').2
    have hmax := hF1 (a - h) hah (by linarith) (Y a)
    have hg := gNorm_pos hp hinj hy.1
    have : ‖tForm p (flowMass p M (a - h)) (Y a)‖ / gNorm p (Y a) ≤ N (a - h) := by
      rw [div_le_iff₀ hg]; exact hmax
    exact hstep.trans this
  have hF5 : ∀ h : ℝ, 0 ≤ h → 2 * h * P ≤ 1 → ∀ b : ℝ, b ≤ a₀ + L → ∀ n : ℕ, a₀ + n * h ≤ b →
      N b - n * (4 * P ^ 2 * B * Real.exp (2 * b * δ) * h ^ 2) ≤ N (b - n * h) := by
    intro h hh hhP b hbL n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hb
      push_cast at hb ⊢
      have hb' : a₀ + n * h ≤ b := by nlinarith
      have h1 := ih hb'
      have h2 := hF4 (b - n * h) h (by linarith) (by nlinarith) hh hhP
      have hmono : Real.exp (2 * (b - n * h) * δ) ≤ Real.exp (2 * b * δ) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (n : ℝ) * h := by positivity
        nlinarith
      have hK : 0 ≤ 4 * P ^ 2 * B * h ^ 2 := by positivity
      rw [show b - (n + 1) * h = b - n * h - h by ring]
      nlinarith [mul_le_mul_of_nonneg_left hmono hK]
  set K₀ : ℝ := 4 * P ^ 2 * B with hK₀_def
  have hK₀ : 0 ≤ K₀ := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K₀ * L ^ 2 / c₀ + 2 * L * P + 1)
  have hnpos : (0 : ℝ) < n := by
    have : 0 ≤ 2 * K₀ * L ^ 2 / c₀ := by positivity
    nlinarith
  set h : ℝ := L / n with hh_def
  have hh : 0 ≤ h := by positivity
  have hnh : (n : ℝ) * h = L := by rw [hh_def]; field_simp
  have hhP : 2 * h * P ≤ 1 := by
    rw [hh_def, show 2 * (L / n) * P = 2 * L * P / n by ring, div_le_one hnpos]
    nlinarith [div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hK₀) (sq_nonneg L))
      hc₀.le]
  set b : ℝ := a₀ + L with hb_def
  have hchain := hF5 h hh hhP b le_rfl n (by rw [hnh])
  rw [hnh, show b - L = a₀ by rw [hb_def]; ring] at hchain
  have herr : (n : ℝ) * (K₀ * Real.exp (2 * b * δ) * h ^ 2) ≤ c₀ / 2 * Real.exp (2 * b * δ) := by
    have hEb := Real.exp_pos (2 * b * δ)
    have h1 : (n : ℝ) * (K₀ * Real.exp (2 * b * δ) * h ^ 2) =
        K₀ * L ^ 2 / n * Real.exp (2 * b * δ) := by
      rw [hh_def]; field_simp
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ hEb.le
    rw [div_le_iff₀ hnpos]
    have : 2 * K₀ * L ^ 2 / c₀ < n := by
      have : 0 ≤ 2 * L * P := by positivity
      linarith
    rw [div_lt_iff₀ hc₀] at this
    nlinarith
  have hlow := hF2 b (by rw [hb_def]; linarith) le_rfl
  have hup := hF3 a₀ le_rfl (by linarith)
  have hsplit : Real.exp (2 * b * δ) = Real.exp (2 * a₀ * δ) * Real.exp (2 * L * δ) := by
    rw [← Real.exp_add, hb_def]; ring_nf
  have hexpL : 3 + 2 * (B / c₀) ≤ Real.exp (2 * L * δ) := by
    have := Real.add_one_le_exp (2 * L * δ)
    have hLd : 2 * L * δ = 2 * (B / c₀ + 1) := by rw [hL_def]; field_simp
    linarith
  have hfinal : c₀ / 2 * Real.exp (2 * b * δ) ≤ B * Real.exp (2 * a₀ * δ) := by
    have : N b - (n : ℝ) * (K₀ * Real.exp (2 * b * δ) * h ^ 2) ≤ N a₀ := hchain
    linarith
  rw [hsplit] at hfinal
  have hEa := Real.exp_pos (2 * a₀ * δ)
  have hcB : c₀ / 2 * (3 + 2 * (B / c₀)) = 3 * c₀ / 2 + B := by field_simp
  have : c₀ / 2 * Real.exp (2 * L * δ) ≤ B := by
    have h' : Real.exp (2 * a₀ * δ) * (c₀ / 2 * Real.exp (2 * L * δ)) ≤
        Real.exp (2 * a₀ * δ) * B := by linarith
    exact le_of_mul_le_mul_left h' hEa
  nlinarith [mul_le_mul_of_nonneg_left hexpL (by positivity : (0 : ℝ) ≤ c₀ / 2)]


/-- **Boundary nondegeneracy along the phase orbit.** Every half-line of the phase orbit contains an
aperture at which top Takagi vectors exist and all have nonzero boundary value. -/
theorem exists_boundary_nondegenerate {δ : ℝ} (hδ : 0 < δ) {p : Fin m → ℂ}
    (hre : ∀ j, (p j).re = δ) (hinj : Function.Injective p) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j)
    (hm : 0 < m) (a₀ : ℝ) :
    ∃ a, a₀ ≤ a ∧ (∃ y, IsTop p (phaseMass δ p M a) y) ∧
      ∀ y, IsTop p (phaseMass δ p M a) y → ∑ j, y j ≠ 0 := by
  obtain ⟨L, -, hwin⟩ := exists_boundary_nondegenerate_window hδ hre hinj hM hm
  obtain ⟨a, ha, -, hex, hall⟩ := hwin a₀
  exact ⟨a, ha, hex, hall⟩

/-- For the nodes `p_j = δ − iτ_j` the phase orbit is `M_j e^{−2iτ_j a}`. -/
theorem phaseMass_ordinates (δ : ℝ) (τ M : Fin m → ℝ) (a : ℝ) (j : Fin m) :
    phaseMass δ (fun k => (δ : ℂ) - I * τ k) M a j =
      (M j : ℂ) * Complex.exp (-(2 * τ j * a : ℝ) * I) := by
  simp only [phaseMass]
  congr 2
  push_cast
  ring

/-- **Boundary nondegeneracy for ordinates.** For distinct ordinates `τ_j`, depth `δ > 0` and
positive masses, the top Takagi vectors for the Gram matrix of `e^{−(δ + iτ_k)s}` and the masses
`M_j e^{−2iτ_j a}` all have nonzero boundary value at some aperture `a ≥ a₀`, for every `a₀`. -/
theorem exists_boundary_nondegenerate_ordinates {δ : ℝ} (hδ : 0 < δ) {τ : Fin m → ℝ}
    (hτ : Function.Injective τ) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) (hm : 0 < m) (a₀ : ℝ) :
    ∃ a, a₀ ≤ a ∧
      (∃ y, IsTop (fun k => (δ : ℂ) - I * τ k)
        (fun j => (M j : ℂ) * Complex.exp (-(2 * τ j * a : ℝ) * I)) y) ∧
      ∀ y, IsTop (fun k => (δ : ℂ) - I * τ k)
        (fun j => (M j : ℂ) * Complex.exp (-(2 * τ j * a : ℝ) * I)) y → ∑ j, y j ≠ 0 := by
  have hre : ∀ j, ((fun k => (δ : ℂ) - I * τ k) j).re = δ := fun j => by simp
  have hinj : Function.Injective fun k => (δ : ℂ) - I * τ k := by
    intro j k h
    have := congrArg Complex.im h
    simp at this
    exact hτ this
  obtain ⟨a, ha, hex, hall⟩ := exists_boundary_nondegenerate hδ hre hinj hM hm a₀
  have hμ : phaseMass δ (fun k => (δ : ℂ) - I * τ k) M a =
      fun j => (M j : ℂ) * Complex.exp (-(2 * τ j * a : ℝ) * I) :=
    funext (phaseMass_ordinates δ τ M a)
  rw [hμ] at hex hall
  exact ⟨a, ha, hex, hall⟩

end

end GaloisForLFunctions.HTGeometry.CauchyTakagi
