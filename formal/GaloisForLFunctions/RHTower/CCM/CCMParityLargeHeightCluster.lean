import GaloisForLFunctions.RHTower.CCM.CCMParityDeepLimit
import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerNoGo
import GaloisForLFunctions.HTGeometry.CauchyTakagiApertureSimplicity

/-!
# The parity balance of a clustered top layer at large height

Take a top layer of off-line spectral points with common offset `δ > 0`, distinct ordinates
`t_j = T + τ_j` and multiplicities `M_j > 0`, and let the height `T` tend to infinity with the cluster
shape `τ` fixed. In the coefficients `x = ȳ` the Cauchy boundary vector of the leading-order parity
model splits as `(Gz)_j = (Hy)_j + (S_T ȳ)_j`. Here `H = [(p_j + p̄_k)⁻¹]` is the difference Gram of
the nodes `p_j = δ − iτ_j`, independent of `T`, and `S_T = [(2δ − i(t_j + t_k))⁻¹] = (i/2T)𝟙𝟙ᵀ +
O(T⁻²)` is the sum Gram (`boundary_inl`, `hGram_lhNodes_shift`).

At `S = 0` the model is the Takagi problem of `T_μ(y) = Σ_j μ_j ((Hy)_j)²`, `μ_j = M_j e^{iθ_j}`. Its
spectrum is symmetric, so the balance vanishes. The sum Gram contributes at first order. On the
unit sphere of `‖y‖²_H`, write `Δ_T(y)` for the change of the Rayleigh quotient caused by `S_T`.
Then `F ≥ Δ_T(y₀) + Δ_T(z)`, where `y₀` maximizes `Re T_μ` and `z` maximizes the half-turned quotient
(`balance_ge_delta_add_delta`).
-/

open Matrix Complex Filter Topology Set
open RHTower.CCMParityCauchy RHTower.CCMParityTopLayer RHTower.CCMParityQuartet
  GaloisForLFunctions.HTGeometry.CauchyTakagi
open scoped ComplexConjugate

namespace RHTower.CCMParityLargeHeight

noncomputable section

variable {m : ℕ}

/-! ## Block decomposition -/

/-- The nodes `δ − i t_j`. -/
def lhNodes (δ : ℝ) (t : Fin m → ℝ) : Fin m → ℂ := fun j => (δ : ℂ) - I * t j

/-- The sum Gram `S_jk = (2δ − i(t_j + t_k))⁻¹`. -/
def sumGram (δ : ℝ) (t : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun j k => (lhNodes δ t j + lhNodes δ t k)⁻¹

theorem conj_lhNodes (δ : ℝ) (t : Fin m → ℝ) (k : Fin m) :
    conj (lhNodes δ t k) = (δ : ℂ) + I * t k := by
  simp [lhNodes, map_sub, Complex.conj_ofReal]

theorem boundary_inl (δ : ℝ) (t : Fin m → ℝ) (y : Fin m → ℂ) (j : Fin m) :
    (cauchyGram (ccmNodes δ t) *ᵥ realLift (star y)) (Sum.inl j) =
      (hGram (lhNodes δ t) *ᵥ y) j + (sumGram δ t *ᵥ star y) j := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, cauchyGram, Matrix.of_apply,
    ccmNodes, Sum.elim_inl, Sum.elim_inr, realLift, hGram_apply, sumGram, Pi.star_apply,
    Complex.star_def, Complex.conj_conj, conj_lhNodes]
  rw [add_comm]
  rfl

/-- `normForm = 2‖y‖²_H + 2 Re(ȳᵀ S ȳ)`. -/
theorem normForm_star (δ : ℝ) (t : Fin m → ℝ) (y : Fin m → ℂ) :
    normForm δ t (star y) = 2 * gNorm (lhNodes δ t) y +
      2 * (∑ j, conj (y j) * (sumGram δ t *ᵥ star y) j).re := by
  rw [normForm_eq_sum_inl]
  simp only [boundary_inl, Pi.star_apply, Complex.star_def, mul_add, Complex.add_re,
    Finset.sum_add_distrib, gNorm, dotProduct, Complex.re_sum, Finset.mul_sum]

/-- `quadForm = Σ_j M_j Re(e^{iθ_j}((Hy)_j + (Sȳ)_j)²)`. -/
theorem quadForm_star (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) :
    quadForm δ t M θ (star y) = ∑ j, M j * (Complex.exp ((θ j : ℂ) * I) *
      ((hGram (lhNodes δ t) *ᵥ y) j + (sumGram δ t *ᵥ star y) j) ^ 2).re := by
  rw [quadForm_eq_sum_inl]
  simp only [boundary_inl]

/-- The difference Gram does not see the height. -/
theorem hGram_lhNodes_shift (δ T : ℝ) (τ : Fin m → ℝ) :
    hGram (lhNodes δ fun j => T + τ j) = hGram (lhNodes δ τ) := by
  ext j k
  rw [hGram_apply, hGram_apply, conj_lhNodes, conj_lhNodes]
  simp only [lhNodes]
  push_cast
  ring_nf


/-! ## Rayleigh quotients -/

/-- The Rayleigh quotient of the parity model in the coordinates `x = ȳ`. -/
def ratio (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  quadForm δ t M θ (star y) / normForm δ t (star y)

theorem star_real_smul (r : ℝ) (y : Fin m → ℂ) :
    star ((r : ℂ) • y) = fun j => (r : ℂ) * star y j := by
  funext j; simp [Complex.conj_ofReal]

theorem ratio_real_smul (δ : ℝ) (t M θ : Fin m → ℝ) {r : ℝ} (hr : r ≠ 0) (y : Fin m → ℂ) :
    ratio δ t M θ ((r : ℂ) • y) = ratio δ t M θ y := by
  rw [ratio, ratio, star_real_smul, quadForm_real_smul, normForm_smul]
  have : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [mul_div_mul_left _ _ this]

theorem ratio_halfTurn (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) :
    ratio δ t M (halfTurn θ) y = -ratio δ t M θ y := by
  rw [ratio, ratio, quadForm_halfTurn, neg_div]

/-- Every quotient is at most `λ_max`. -/
theorem ratio_le_lambdaMax {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) {y : Fin m → ℂ} (hy : y ≠ 0) :
    ratio δ t M θ y ≤ ccmLambdaMax δ t M θ := by
  have hx : star y ≠ 0 := fun h => hy (star_eq_zero.mp h)
  have hn := normForm_pos hδ ht htpos hx
  have h := quadForm_le_lambdaMax_mul hδ ht htpos hm M θ (star y)
  rw [ratio, div_le_iff₀ hn]
  exact h

/-- `λ_max` is attained by a quotient on the unit sphere. -/
theorem exists_sphere_ratio_eq_lambdaMax {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) :
    ∃ y ∈ Metric.sphere (0 : Fin m → ℂ) 1, ratio δ t M θ y = ccmLambdaMax δ t M θ := by
  obtain ⟨x, hx, hxq, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  have hx1 : normForm δ t x = 1 := hx
  have hx0 : x ≠ 0 := by
    intro h; rw [h, normForm_zero] at hx1; exact zero_ne_one hx1
  have hy0 : star x ≠ 0 := fun h => hx0 (star_eq_zero.mp h)
  obtain ⟨r, hr, u, hu, hxu⟩ := exists_unit_smul hy0
  refine ⟨u, hu, ?_⟩
  have h1 : ratio δ t M θ (star x) = ccmLambdaMax δ t M θ := by
    rw [ratio, star_star, hx1, div_one, hxq]
  rw [← h1, hxu, ratio_real_smul δ t M θ hr.ne']

/-! ## The perturbation by the sum Gram -/

/-- The phase masses `μ_j = M_j e^{iθ_j}`. -/
def phaseMu (M θ : Fin m → ℝ) : Fin m → ℂ := fun j => (M j : ℂ) * Complex.exp ((θ j : ℂ) * I)

/-- The leading quotient `L_μ(y) = Re T_μ(y)/‖y‖²_H`. -/
def leadRatio (p μ y : Fin m → ℂ) : ℝ := (tForm p μ y).re / gNorm p y

theorem leadRatio_I_smul (p μ y : Fin m → ℂ) : leadRatio p μ (I • y) = -leadRatio p μ y := by
  have hT : tForm p μ (I • y) = -tForm p μ y := by
    simp only [tForm, mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_pow, I_sq]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hg : gNorm p (I • y) = gNorm p y := by
    have := gNorm_smul p y 1
    rw [gNorm, gNorm, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, Complex.star_def, conj_I, ← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I,
        neg_neg], one_mul]
  rw [leadRatio, leadRatio, hT, hg, neg_re, neg_div]

/-- The quotient change `Δ = R − L/2` caused by the sum Gram. -/
def deltaS (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  ratio δ t M θ y - leadRatio (lhNodes δ t) (phaseMu M θ) y / 2

theorem quadForm_star_eq (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) :
    quadForm δ t M θ (star y) = (tForm (lhNodes δ t) (phaseMu M θ) y).re +
      (∑ j, phaseMu M θ j * (2 * (hGram (lhNodes δ t) *ᵥ y) j * (sumGram δ t *ᵥ star y) j +
        (sumGram δ t *ᵥ star y) j ^ 2)).re := by
  rw [quadForm_star, tForm, ← Complex.add_re, ← Finset.sum_add_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phaseMu, ← Complex.re_ofReal_mul]
  congr 1
  ring

/-- **The balance inequality.** If `y₀` maximizes `L_μ` on the unit sphere and `z` attains
`λ_max` of the half-turned model, then `F ≥ Δ(y₀) + Δ(z)`. -/
theorem balance_ge_delta_add_delta {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    {y₀ z : Fin m → ℂ} (hy₀ : y₀ ∈ Metric.sphere (0 : Fin m → ℂ) 1)
    (hmax : ∀ w ∈ Metric.sphere (0 : Fin m → ℂ) 1,
      leadRatio (lhNodes δ t) (phaseMu M θ) w ≤ leadRatio (lhNodes δ t) (phaseMu M θ) y₀)
    (hz : z ∈ Metric.sphere (0 : Fin m → ℂ) 1)
    (hzmax : ratio δ t M (halfTurn θ) z = ccmLambdaMax δ t M (halfTurn θ)) :
    deltaS δ t M θ y₀ + deltaS δ t M θ z ≤ ccmParityBalance δ t M θ := by
  have hy₀0 : y₀ ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨y₀, hy₀⟩
  have hlow := ratio_le_lambdaMax hδ ht htpos hm M θ hy₀0
  have hIz : I • z ∈ Metric.sphere (0 : Fin m → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_I, one_mul]
    exact mem_sphere_zero_iff_norm.mp hz
  have h1 := hmax (I • z) hIz
  rw [leadRatio_I_smul] at h1
  rw [ratio_halfTurn] at hzmax
  unfold ccmParityBalance deltaS at *
  linarith


/-! ## The scaled perturbation -/

/-- The numerator of the scaled quotient change. -/
def psiNum (p μ : Fin m → ℂ) (A S : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  gNorm p y * (∑ j, μ j * (2 * (hGram p *ᵥ y) j * (A *ᵥ star y) j +
      (S *ᵥ star y) j * (A *ᵥ star y) j)).re -
    (∑ j, conj (y j) * (A *ᵥ star y) j).re * (tForm p μ y).re

/-- The denominator of the scaled quotient change. -/
def psiDen (p : Fin m → ℂ) (S : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  2 * gNorm p y * (gNorm p y + (∑ j, conj (y j) * (S *ᵥ star y) j).re)

/-- The scaled quotient change `Ψ(μ, A, S, y)`; for `A = T S` it is `T Δ`. -/
def psi (p μ : Fin m → ℂ) (A S : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  psiNum p μ A S y / psiDen p S y

/-- **`T Δ_T = Ψ(μ, T S, S, y)`.** -/
theorem mul_deltaS_eq_psi {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (M θ : Fin m → ℝ) {T : ℝ} {y : Fin m → ℂ} (hy : y ≠ 0) :
    T * deltaS δ t M θ y = psi (lhNodes δ t) (phaseMu M θ) ((T : ℂ) • sumGram δ t)
      (sumGram δ t) y := by
  have hx : star y ≠ 0 := fun h => hy (star_eq_zero.mp h)
  have hn := normForm_pos hδ ht htpos hx
  have hinj : Function.Injective (lhNodes δ t) := by
    intro j k h
    have := congrArg Complex.im h
    simp [lhNodes] at this
    exact ht this
  have hp : ∀ j, 0 < (lhNodes δ t j).re := fun j => by simp [lhNodes, hδ]
  have hg := gNorm_pos hp hinj hy
  rw [normForm_star] at hn
  set g := gNorm (lhNodes δ t) y with hg_def
  set r := (∑ j, conj (y j) * (sumGram δ t *ᵥ star y) j).re with hr_def
  set E := (∑ j, phaseMu M θ j * (2 * (hGram (lhNodes δ t) *ᵥ y) j * (sumGram δ t *ᵥ star y) j +
    (sumGram δ t *ᵥ star y) j ^ 2)).re with hE_def
  set R := (tForm (lhNodes δ t) (phaseMu M θ) y).re with hR_def
  have hgr : 0 < g + r := by linarith
  have hAv : ∀ j, (((T : ℂ) • sumGram δ t) *ᵥ star y) j = (T : ℂ) * (sumGram δ t *ᵥ star y) j := by
    intro j; rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have hnum : psiNum (lhNodes δ t) (phaseMu M θ) ((T : ℂ) • sumGram δ t) (sumGram δ t) y =
      T * (g * E - r * R) := by
    rw [psiNum]
    simp only [hAv]
    have h1 : (∑ j, phaseMu M θ j * (2 * (hGram (lhNodes δ t) *ᵥ y) j *
        ((T : ℂ) * (sumGram δ t *ᵥ star y) j) + (sumGram δ t *ᵥ star y) j *
          ((T : ℂ) * (sumGram δ t *ᵥ star y) j))).re = T * E := by
      rw [hE_def, ← Complex.re_ofReal_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : (∑ j, conj (y j) * ((T : ℂ) * (sumGram δ t *ᵥ star y) j)).re = T * r := by
      rw [hr_def, ← Complex.re_ofReal_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2, ← hg_def, ← hR_def]
    ring
  have hden : psiDen (lhNodes δ t) (sumGram δ t) y = 2 * g * (g + r) := rfl
  rw [psi, hnum, hden, deltaS, ratio, quadForm_star_eq, normForm_star, leadRatio]
  rw [← hg_def, ← hr_def, ← hE_def, ← hR_def]
  field_simp
  ring

theorem continuous_psiNum (p : Fin m → ℂ) :
    Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ×
      (Fin m → ℂ) => psiNum p q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  have cy : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => q.2.2.2 := by fun_prop
  have cμ : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => q.1 := by fun_prop
  have cA : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => q.2.1 := by fun_prop
  have cS : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => q.2.2.1 := by fun_prop
  have cyb := continuous_star.comp cy
  have cAv := cA.matrix_mulVec cyb
  have cSv := cS.matrix_mulVec cyb
  have cHy := (continuous_const (y := hGram p)).matrix_mulVec cy
  have cg : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => gNorm p q.2.2.2 := (continuous_gNorm p).comp cy
  have cT : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => tForm p q.1 q.2.2.2 := by
    unfold tForm
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp cμ).mul (((continuous_apply j).comp cHy).pow 2)
  have c1 : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => ∑ j, q.1 j * (2 * (hGram p *ᵥ q.2.2.2) j *
        (q.2.1 *ᵥ star q.2.2.2) j + (q.2.2.1 *ᵥ star q.2.2.2) j * (q.2.1 *ᵥ star q.2.2.2) j) :=
    continuous_finsetSum _ fun j _ => ((continuous_apply j).comp cμ).mul
      ((continuous_const.mul ((continuous_apply j).comp cHy)).mul ((continuous_apply j).comp cAv)
        |>.add (((continuous_apply j).comp cSv).mul ((continuous_apply j).comp cAv)))
  have c2 : Continuous fun q : (Fin m → ℂ) × Matrix (Fin m) (Fin m) ℂ ×
      Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => ∑ j, conj (q.2.2.2 j) * (q.2.1 *ᵥ star q.2.2.2) j :=
    continuous_finsetSum _ fun j _ =>
      (Complex.continuous_conj.comp ((continuous_apply j).comp cy)).mul
        ((continuous_apply j).comp cAv)
  unfold psiNum
  exact (cg.mul (Complex.continuous_re.comp c1)).sub
    ((Complex.continuous_re.comp c2).mul (Complex.continuous_re.comp cT))

theorem continuous_psiDen (p : Fin m → ℂ) :
    Continuous fun q : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => psiDen p q.1 q.2 := by
  have cy : Continuous fun q : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => q.2 := continuous_snd
  have cS : Continuous fun q : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) => q.1 := continuous_fst
  have cSv := cS.matrix_mulVec (continuous_star.comp cy)
  have cg := (continuous_gNorm p).comp cy
  have c2 : Continuous fun q : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) =>
      ∑ j, conj (q.2 j) * (q.1 *ᵥ star q.2) j :=
    continuous_finsetSum _ fun j _ =>
      (Complex.continuous_conj.comp ((continuous_apply j).comp cy)).mul
        ((continuous_apply j).comp cSv)
  unfold psiDen
  exact (continuous_const.mul cg).mul (cg.add (Complex.continuous_re.comp c2))

/-- **Convergence of the scaled quotient change.** -/
theorem tendsto_psi {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    {μn : ℕ → Fin m → ℂ} {An Sn : ℕ → Matrix (Fin m) (Fin m) ℂ} {yn : ℕ → Fin m → ℂ}
    {μ : Fin m → ℂ} {A : Matrix (Fin m) (Fin m) ℂ} {y : Fin m → ℂ}
    (hμ : Tendsto μn atTop (𝓝 μ)) (hA : Tendsto An atTop (𝓝 A)) (hS : Tendsto Sn atTop (𝓝 0))
    (hy : Tendsto yn atTop (𝓝 y)) (hy0 : y ≠ 0) :
    Tendsto (fun n => psi p (μn n) (An n) (Sn n) (yn n)) atTop (𝓝 (psi p μ A 0 y)) := by
  unfold psi
  have h4 : Tendsto (fun n => (μn n, An n, Sn n, yn n)) atTop (𝓝 (μ, A, 0, y)) :=
    hμ.prodMk_nhds (hA.prodMk_nhds (hS.prodMk_nhds hy))
  have hnum := ((continuous_psiNum p).continuousAt (x := (μ, A, 0, y))).tendsto.comp h4
  have h2 : Tendsto (fun n => (Sn n, yn n)) atTop (𝓝 ((0 : Matrix (Fin m) (Fin m) ℂ), y)) :=
    hS.prodMk_nhds hy
  have hden := ((continuous_psiDen p).continuousAt (x := ((0 : Matrix (Fin m) (Fin m) ℂ), y))).tendsto.comp h2
  simp only [Function.comp_def] at hnum hden
  have hg := gNorm_pos hp hinj hy0
  have hden0 : psiDen p 0 y ≠ 0 := by
    have : psiDen p 0 y = 2 * gNorm p y * gNorm p y := by
      rw [psiDen]; simp only [zero_mulVec, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        Complex.zero_re, add_zero]
    rw [this]; positivity
  exact hnum.div hden hden0

/-- **`Ψ` at a phase-fixed Takagi top.** If `T_μ(y) = N ‖y‖²_H` with `N > 0` at a Takagi top,
then `Ψ(μ, A, 0, y) = Ψ(μ, A, 0, iy) = N Re(ȳᵀAȳ)/(2‖y‖²_H)`. -/
theorem psi_top_eq {p μ y : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    (hy : IsTop p μ y) {N : ℝ} (hN : 0 < N) (hT : tForm p μ y = ((N * gNorm p y : ℝ) : ℂ))
    (A : Matrix (Fin m) (Fin m) ℂ) :
    psi p μ A 0 y = N * (∑ j, conj (y j) * (A *ᵥ star y) j).re / (2 * gNorm p y) ∧
      psi p μ A 0 (I • y) = N * (∑ j, conj (y j) * (A *ᵥ star y) j).re / (2 * gNorm p y) := by
  have hg := gNorm_pos hp hinj hy.1
  have hTn : tForm p μ y ≠ 0 := by
    rw [hT]; exact_mod_cast (mul_pos hN hg).ne'
  have hnorm : ‖tForm p μ y‖ = N * gNorm p y := by
    rw [hT, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hN hg)]
  have hvar := hy.variational hp hinj hTn
  have hc : conj (tForm p μ y) / ((‖tForm p μ y‖ : ℝ) : ℂ) = 1 := by
    rw [hnorm, hT, Complex.conj_ofReal, div_self]
    exact_mod_cast (mul_pos hN hg).ne'
  have hL : ∀ j, μ j * (hGram p *ᵥ y) j = (N : ℂ) * conj (y j) := by
    intro j
    have := lagrange hp hinj hvar.1 hvar.2 j
    rw [hc, one_mul, hnorm, mul_div_cancel_right₀ _ hg.ne'] at this
    exact this
  set r := (∑ j, conj (y j) * (A *ᵥ star y) j).re with hr
  have hE : (∑ j, μ j * (2 * (hGram p *ᵥ y) j * (A *ᵥ star y) j +
      ((0 : Matrix (Fin m) (Fin m) ℂ) *ᵥ star y) j * (A *ᵥ star y) j)).re = 2 * N * r := by
    simp only [zero_mulVec, Pi.zero_apply, zero_mul, add_zero]
    have : ∑ j, μ j * (2 * (hGram p *ᵥ y) j * (A *ᵥ star y) j) =
        ((2 * N : ℝ) : ℂ) * ∑ j, conj (y j) * (A *ᵥ star y) j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hL j
      push_cast
      linear_combination (2 * (A *ᵥ star y) j) * this
    rw [this, Complex.re_ofReal_mul]
  have hden0 : psiDen p 0 y = 2 * gNorm p y * gNorm p y := by simp [psiDen]
  have hRe : (tForm p μ y).re = N * gNorm p y := by rw [hT, Complex.ofReal_re]
  constructor
  · rw [psi, psiNum, hE, hRe, hden0, ← hr]
    field_simp
    ring
  · -- the rotated vector
    have hstar : star (I • y) = (-I) • star y := by
      funext j; simp
    have hgI : gNorm p (I • y) = gNorm p y := by
      have h := normSq_hInner_le hp hinj y y
      rw [gNorm, gNorm, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, Complex.star_def, conj_I, ← mul_assoc, show -I * I = 1 by
          rw [neg_mul, I_mul_I, neg_neg], one_mul]
    have hTI : tForm p μ (I • y) = -tForm p μ y := by
      simp only [tForm, mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_pow, I_sq]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hrI : (∑ j, conj ((I • y) j) * (A *ᵥ star (I • y)) j).re = -r := by
      rw [hstar, mulVec_smul, hr, ← Complex.neg_re]
      congr 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conj_I]
      ring_nf
      rw [I_sq]; ring
    have hEI : (∑ j, μ j * (2 * (hGram p *ᵥ (I • y)) j * (A *ᵥ star (I • y)) j +
        ((0 : Matrix (Fin m) (Fin m) ℂ) *ᵥ star (I • y)) j * (A *ᵥ star (I • y)) j)).re =
        2 * N * r := by
      rw [← hE, hstar, mulVec_smul, mulVec_smul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, zero_mulVec, Pi.zero_apply, zero_mul, add_zero]
      ring_nf
      rw [I_sq]; ring
    have hden0I : psiDen p 0 (I • y) = 2 * gNorm p y * gNorm p y := by
      simp [psiDen, hgI]
    rw [psi, psiNum, hEI, hrI, hTI, Complex.neg_re, hRe, hden0I, hgI]
    field_simp
    ring


/-! ## The aperture family at large height -/

/-- The aperture `a_T ∈ [a*, a* + π/T]` at which the common phase `−2T a_T` equals `c` mod `2π`. -/
def apT (a c T : ℝ) : ℝ := (2 * Real.pi * ⌈(2 * T * a + c) / (2 * Real.pi)⌉ - c) / (2 * T)

theorem apT_bounds {a c T : ℝ} (hT : 0 < T) : a ≤ apT a c T ∧ apT a c T ≤ a + Real.pi / T := by
  set x := (2 * T * a + c) / (2 * Real.pi) with hx
  have h1 := Int.le_ceil x
  have h2 := Int.ceil_lt_add_one x
  have hpi := Real.pi_pos
  have e : 2 * Real.pi * x = 2 * T * a + c := by rw [hx]; field_simp
  constructor
  · rw [apT, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [apT, div_le_iff₀ (by positivity)]
    have : a + Real.pi / T = (2 * T * a + 2 * Real.pi) / (2 * T) := by field_simp
    rw [this, div_mul_cancel₀ _ (by positivity)]
    nlinarith

theorem tendsto_apT (a c : ℝ) : Tendsto (apT a c) atTop (𝓝 a) := by
  have hup : Tendsto (fun T : ℝ => a + Real.pi / T) atTop (𝓝 a) := by
    have := (tendsto_const_nhds (x := a)).add
      ((tendsto_const_nhds (x := Real.pi)).div_atTop (tendsto_id (α := ℝ)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT using (apT_bounds hT).1
  · filter_upwards [eventually_gt_atTop 0] with T hT using (apT_bounds hT).2

/-- The phases `θ_j = −2(T + τ_j) a_T`. -/
def thetaT (τ : Fin m → ℝ) (a c T : ℝ) : Fin m → ℝ := fun j => -2 * (T + τ j) * apT a c T

theorem exp_neg_two_T_apT (a c : ℝ) {T : ℝ} (hT : 0 < T) :
    Complex.exp ((-2 * T * apT a c T : ℝ) * I) = Complex.exp ((c : ℂ) * I) := by
  have e : (-2 * T * apT a c T : ℝ) = c - 2 * Real.pi * ⌈(2 * T * a + c) / (2 * Real.pi)⌉ := by
    rw [apT]; field_simp; ring
  rw [e]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, show ((2 * Real.pi *
    (⌈(2 * T * a + c) / (2 * Real.pi)⌉ : ℝ) : ℝ) : ℂ) * I =
      (⌈(2 * T * a + c) / (2 * Real.pi)⌉ : ℤ) * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- The limit masses `μ*_j = e^{ic} M_j e^{−2iτ_j a*}`. -/
def muStar (τ M : Fin m → ℝ) (a c : ℝ) : Fin m → ℂ :=
  fun j => Complex.exp ((c : ℂ) * I) * ((M j : ℂ) * Complex.exp ((-2 * τ j * a : ℝ) * I))

theorem phaseMu_thetaT (τ M : Fin m → ℝ) (a c : ℝ) {T : ℝ} (hT : 0 < T) :
    phaseMu M (thetaT τ a c T) = muStar τ M (apT a c T) c := by
  funext j
  simp only [phaseMu, thetaT, muStar]
  rw [← exp_neg_two_T_apT a c hT, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem tendsto_phaseMu_thetaT (τ M : Fin m → ℝ) (a c : ℝ) :
    Tendsto (fun T => phaseMu M (thetaT τ a c T)) atTop (𝓝 (muStar τ M a c)) := by
  have hcont : Continuous fun b : ℝ => muStar τ M b c := by
    unfold muStar; fun_prop
  have h := (hcont.tendsto a).comp (tendsto_apT a c)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (phaseMu_thetaT τ M a c hT).symm

/-- The limit of the scaled sum Gram: `T S_T → (i/2)𝟙𝟙ᵀ`. -/
def aInf : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun _ _ => I / 2

theorem tendsto_smul_sumGram (δ : ℝ) (τ : Fin m → ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ) • sumGram δ (fun j => T + τ j)) atTop (𝓝 (aInf (m := m))) := by
  refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun k => ?_
  simp only [Matrix.smul_apply, sumGram, Matrix.of_apply, lhNodes, aInf, smul_eq_mul]
  have hden : Tendsto (fun T : ℝ => ((2 * δ : ℝ) : ℂ) * ((T : ℂ))⁻¹ -
      I * (2 + ((τ j + τ k : ℝ) : ℂ) * ((T : ℂ))⁻¹)) atTop (𝓝 (-(I * 2))) := by
    have hinv : Tendsto (fun T : ℝ => ((T : ℂ))⁻¹) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      simpa [Function.comp_def] using this
    have := ((tendsto_const_nhds (x := ((2 * δ : ℝ) : ℂ))).mul hinv).sub
      ((tendsto_const_nhds (x := I)).mul ((tendsto_const_nhds (x := (2 : ℂ))).add
        ((tendsto_const_nhds (x := ((τ j + τ k : ℝ) : ℂ))).mul hinv)))
    simpa using this
  have hlim := hden.inv₀ (by simp)
  have e : (-(I * 2))⁻¹ = I / 2 := by
    rw [inv_neg, mul_inv, Complex.inv_I]; ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp
  ring

theorem tendsto_sumGram (δ : ℝ) (τ : Fin m → ℝ) :
    Tendsto (fun T : ℝ => sumGram δ (fun j => T + τ j)) atTop (𝓝 0) := by
  have h := tendsto_smul_sumGram δ τ
  have hinv : Tendsto (fun T : ℝ => ((T : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have := hinv.smul h
  rw [zero_smul] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [smul_smul, inv_mul_cancel₀ hT0, one_smul]


/-! ## Leading maximizers -/

theorem continuous_tForm_joint (p : Fin m → ℂ) :
    Continuous fun q : (Fin m → ℂ) × (Fin m → ℂ) => tForm p q.1 q.2 := by
  have cHy := (continuous_const (y := hGram p)).matrix_mulVec
    (continuous_snd : Continuous fun q : (Fin m → ℂ) × (Fin m → ℂ) => q.2)
  unfold tForm
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_fst).mul (((continuous_apply j).comp cHy).pow 2)

theorem tendsto_leadRatio {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re) (hinj : Function.Injective p)
    {μn : ℕ → Fin m → ℂ} {yn : ℕ → Fin m → ℂ} {μ y : Fin m → ℂ} (hμ : Tendsto μn atTop (𝓝 μ))
    (hy : Tendsto yn atTop (𝓝 y)) (hy0 : y ≠ 0) :
    Tendsto (fun n => leadRatio p (μn n) (yn n)) atTop (𝓝 (leadRatio p μ y)) := by
  unfold leadRatio
  have h1 := ((continuous_re.comp (continuous_tForm_joint p)).continuousAt
    (x := (μ, y))).tendsto.comp (hμ.prodMk_nhds hy)
  have h2 := ((continuous_gNorm p).continuousAt (x := y)).tendsto.comp hy
  simp only [Function.comp_def] at h1 h2
  exact h1.div h2 (gNorm_pos hp hinj hy0).ne'

theorem exists_leadRatio_max {p : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (hinj : Function.Injective p) (hm : 0 < m) (μ : Fin m → ℂ) :
    ∃ y ∈ Metric.sphere (0 : Fin m → ℂ) 1, ∀ w ∈ Metric.sphere (0 : Fin m → ℂ) 1,
      leadRatio p μ w ≤ leadRatio p μ y := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hS := isCompact_sphere (0 : Fin m → ℂ) 1
  have hne : (Metric.sphere (0 : Fin m → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hpos : ∀ u ∈ Metric.sphere (0 : Fin m → ℂ) 1, 0 < gNorm p u := fun u hu =>
    gNorm_pos hp hinj (ne_zero_of_mem_sphere one_ne_zero ⟨u, hu⟩)
  have hcont : ContinuousOn (leadRatio p μ) (Metric.sphere 0 1) := by
    unfold leadRatio
    exact (continuous_re.comp (continuous_tForm p μ)).continuousOn.div
      (continuous_gNorm p).continuousOn fun u hu => (hpos u hu).ne'
  obtain ⟨y, hyS, hmax⟩ := hS.exists_isMaxOn hne hcont
  exact ⟨y, hyS, fun w hw => hmax hw⟩

theorem leadRatio_real_smul (p μ y : Fin m → ℂ) {r : ℝ} (hr : r ≠ 0) :
    leadRatio p μ ((r : ℂ) • y) = leadRatio p μ y := by
  rw [leadRatio, leadRatio, tForm_smul, gNorm_smul, ← ofReal_pow, Complex.re_ofReal_mul]
  have : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [mul_div_mul_left _ _ this]

theorem psiNum_real_smul (p μ : Fin m → ℂ) (A S : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (r : ℝ) : psiNum p μ A S ((r : ℂ) • y) = (r ^ 2 * r ^ 2) * psiNum p μ A S y := by
  have hstar : star ((r : ℂ) • y) = (r : ℂ) • star y := by
    funext j; simp [Complex.conj_ofReal]
  have hHy : hGram p *ᵥ ((r : ℂ) • y) = (r : ℂ) • (hGram p *ᵥ y) := mulVec_smul _ _ _
  have hAy : A *ᵥ star ((r : ℂ) • y) = (r : ℂ) • (A *ᵥ star y) := by rw [hstar, mulVec_smul]
  have hSy : S *ᵥ star ((r : ℂ) • y) = (r : ℂ) • (S *ᵥ star y) := by rw [hstar, mulVec_smul]
  have e1 : (∑ j, μ j * (2 * (hGram p *ᵥ ((r : ℂ) • y)) j * (A *ᵥ star ((r : ℂ) • y)) j +
      (S *ᵥ star ((r : ℂ) • y)) j * (A *ᵥ star ((r : ℂ) • y)) j)).re =
      r ^ 2 * (∑ j, μ j * (2 * (hGram p *ᵥ y) j * (A *ᵥ star y) j +
        (S *ᵥ star y) j * (A *ᵥ star y) j)).re := by
    rw [hHy, hAy, hSy, ← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have e2 : (∑ j, conj (((r : ℂ) • y) j) * (A *ᵥ star ((r : ℂ) • y)) j).re =
      r ^ 2 * (∑ j, conj (y j) * (A *ᵥ star y) j).re := by
    rw [hAy, ← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    push_cast; ring
  rw [psiNum, psiNum, e1, e2, tForm_smul, gNorm_smul, ← ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem psiDen_real_smul (p : Fin m → ℂ) (S : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    (r : ℝ) : psiDen p S ((r : ℂ) • y) = (r ^ 2 * r ^ 2) * psiDen p S y := by
  have hstar : star ((r : ℂ) • y) = (r : ℂ) • star y := by
    funext j; simp [Complex.conj_ofReal]
  have e2 : (∑ j, conj (((r : ℂ) • y) j) * (S *ᵥ star ((r : ℂ) • y)) j).re =
      r ^ 2 * (∑ j, conj (y j) * (S *ᵥ star y) j).re := by
    rw [hstar, mulVec_smul, ← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    push_cast; ring
  rw [psiDen, psiDen, e2, gNorm_smul]
  ring

theorem psi_real_smul (p μ : Fin m → ℂ) (A S : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ)
    {r : ℝ} (hr : r ≠ 0) : psi p μ A S ((r : ℂ) • y) = psi p μ A S y := by
  have h4 : r ^ 2 * r ^ 2 ≠ 0 := by positivity
  rw [psi, psi, psiNum_real_smul, psiDen_real_smul, mul_div_mul_left _ _ h4]

/-- Takagi tops are not changed by a unimodular factor on the masses. -/
theorem isTop_unit_smul_iff (p μ y : Fin m → ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    IsTop p (fun j => u * μ j) y ↔ IsTop p μ y := by
  simp only [GaloisForLFunctions.HTGeometry.CauchyTakagi.IsTop, tForm_mass_smul, norm_mul, hu,
    one_mul]

/-- **Leading extremizers at a simple top.** Let `y_c` be a Takagi top of `μ` with
`T_μ(y_c) = N‖y_c‖²_H`, `N > 0`, and suppose all Takagi tops are proportional to `y_c`. A vector with
`L_μ = N` is a real multiple of `y_c`; a vector with `L_μ = −N` is a real multiple of `i y_c`. -/
theorem leadRatio_extreme {p μ yc : Fin m → ℂ} (hp : ∀ j, 0 < (p j).re)
    (hinj : Function.Injective p) (htop : IsTop p μ yc) {N : ℝ} (hN : 0 < N)
    (hT : tForm p μ yc = ((N * gNorm p yc : ℝ) : ℂ))
    (hprop : ∀ y, IsTop p μ y → ∃ κ : ℂ, y = κ • yc) :
    (∀ w, w ≠ 0 → leadRatio p μ w ≤ N ∧ -N ≤ leadRatio p μ w) ∧
    (∀ y, y ≠ 0 → leadRatio p μ y = N → ∃ r : ℝ, y = (r : ℂ) • yc) ∧
    (∀ y, y ≠ 0 → leadRatio p μ y = -N → ∃ r : ℝ, y = (r : ℂ) • (I • yc)) := by
  have hgc := gNorm_pos hp hinj htop.1
  have hnormc : ‖tForm p μ yc‖ = N * gNorm p yc := by
    rw [hT, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hN hgc)]
  have hbound : ∀ w, ‖tForm p μ w‖ ≤ N * gNorm p w := by
    intro w
    have := htop.2 w
    rw [hnormc] at this
    nlinarith
  have hext : ∀ y, y ≠ 0 → ‖tForm p μ y‖ = N * gNorm p y → IsTop p μ y := by
    intro y hy hy'
    refine ⟨hy, fun z => ?_⟩
    rw [hy']
    have := hbound z
    have hgy := gNorm_pos hp hinj hy
    nlinarith
  refine ⟨fun w hw => ?_, fun y hy hL => ?_, fun y hy hL => ?_⟩
  · have hgw := gNorm_pos hp hinj hw
    have h1 := hbound w
    have h2 := Complex.abs_re_le_norm (tForm p μ w)
    rw [leadRatio]
    constructor
    · rw [div_le_iff₀ hgw]; linarith [le_abs_self (tForm p μ w).re]
    · rw [le_div_iff₀ hgw]; linarith [neg_abs_le (tForm p μ w).re]
  · have hgy := gNorm_pos hp hinj hy
    rw [leadRatio, div_eq_iff hgy.ne'] at hL
    have h1 := hbound y
    have h2 := Complex.re_le_norm (tForm p μ y)
    have hnorm : ‖tForm p μ y‖ = N * gNorm p y := le_antisymm h1 (by linarith)
    obtain ⟨κ, hκ⟩ := hprop y (hext y hy hnorm)
    -- `κ` is real
    have hTy : tForm p μ y = κ ^ 2 * tForm p μ yc := by
      rw [hκ]; simp only [tForm, mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hgy' : gNorm p y = ‖κ‖ ^ 2 * gNorm p yc := by
      rw [hκ, gNorm, gNorm, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, Complex.star_def, ← mul_assoc, Complex.conj_mul', ← ofReal_pow,
        Complex.re_ofReal_mul]
    rw [hTy, hT, hgy'] at hL
    have hre : (κ ^ 2).re * (N * gNorm p yc) = N * (‖κ‖ ^ 2 * gNorm p yc) := by
      rw [← hL, Complex.re_mul_ofReal]
    have hk : (κ ^ 2).re = ‖κ‖ ^ 2 := by
      have : (N * gNorm p yc) ≠ 0 := (mul_pos hN hgc).ne'
      field_simp at hre
      nlinarith [hre]
    have him : κ.im = 0 := by
      rw [sq, Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hk
      nlinarith [sq_nonneg κ.im]
    refine ⟨κ.re, ?_⟩
    rw [hκ]
    congr 1
    exact Complex.ext (by simp) (by simp [him])
  · have hgy := gNorm_pos hp hinj hy
    rw [leadRatio, div_eq_iff hgy.ne'] at hL
    have h1 := hbound y
    have h2 := neg_abs_le (tForm p μ y).re
    have h3 := Complex.abs_re_le_norm (tForm p μ y)
    have hnorm : ‖tForm p μ y‖ = N * gNorm p y := le_antisymm h1 (by linarith)
    obtain ⟨κ, hκ⟩ := hprop y (hext y hy hnorm)
    have hTy : tForm p μ y = κ ^ 2 * tForm p μ yc := by
      rw [hκ]; simp only [tForm, mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hgy' : gNorm p y = ‖κ‖ ^ 2 * gNorm p yc := by
      rw [hκ, gNorm, gNorm, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, Complex.star_def, ← mul_assoc, Complex.conj_mul', ← ofReal_pow,
        Complex.re_ofReal_mul]
    rw [hTy, hT, hgy'] at hL
    have hre : (κ ^ 2).re * (N * gNorm p yc) = -N * (‖κ‖ ^ 2 * gNorm p yc) := by
      rw [← hL, Complex.re_mul_ofReal]
    have hk : (κ ^ 2).re = -‖κ‖ ^ 2 := by
      have : (N * gNorm p yc) ≠ 0 := (mul_pos hN hgc).ne'
      field_simp at hre
      nlinarith [hre]
    have hre0 : κ.re = 0 := by
      rw [sq, Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hk
      nlinarith [sq_nonneg κ.re]
    refine ⟨κ.im, ?_⟩
    rw [hκ, smul_smul]
    congr 1
    apply Complex.ext <;> simp [hre0]


/-! ## Complex scaling of tops -/

theorem tForm_csmul (p μ y : Fin m → ℂ) (c : ℂ) : tForm p μ (c • y) = c ^ 2 * tForm p μ y := by
  simp only [tForm, mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gNorm_csmul (p y : Fin m → ℂ) (c : ℂ) : gNorm p (c • y) = ‖c‖ ^ 2 * gNorm p y := by
  rw [gNorm, gNorm, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, Complex.star_def, ← mul_assoc, Complex.conj_mul', ← ofReal_pow,
    Complex.re_ofReal_mul]

theorem isTop_csmul {p μ y : Fin m → ℂ} {c : ℂ} (hc : c ≠ 0) (hy : IsTop p μ y) :
    IsTop p μ (c • y) := by
  refine ⟨smul_ne_zero hc hy.1, fun z => ?_⟩
  rw [tForm_csmul, gNorm_csmul, norm_mul, norm_pow]
  have := hy.2 z
  have hc2 : 0 ≤ ‖c‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hc2]

theorem sum_aInf (y : Fin m → ℂ) :
    ∑ j, conj (y j) * (aInf *ᵥ star y) j = I / 2 * (∑ j, conj (y j)) ^ 2 := by
  have h : ∀ j, (aInf *ᵥ star y) j = I / 2 * ∑ k, conj (y k) := by
    intro j
    simp only [mulVec, dotProduct, aInf, Matrix.of_apply, Pi.star_apply, Complex.star_def,
      Finset.mul_sum]
  simp only [h]
  rw [← Finset.sum_mul, sq]
  ring

theorem psi_congr {q q' : Fin m → ℂ} (h : hGram q = hGram q') :
    psi q = psi q' := by
  funext μ A S y
  simp only [psi, psiNum, psiDen, gNorm, tForm, h]

theorem leadRatio_congr {q q' : Fin m → ℂ} (h : hGram q = hGram q') :
    leadRatio q = leadRatio q' := by
  funext μ y
  simp only [leadRatio, gNorm, tForm, h]

theorem phaseMass_lhNodes (δ : ℝ) (τ M : Fin m → ℝ) (a : ℝ) :
    phaseMass δ (lhNodes δ τ) M a = fun j => (M j : ℂ) * Complex.exp ((-2 * τ j * a : ℝ) * I) := by
  funext j
  simp only [phaseMass, lhNodes]
  congr 2
  push_cast
  ring


/-! ## The large-height theorem -/

theorem norm_unit_exp (x : ℝ) : ‖Complex.exp ((x : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

/-- **Clustered top layers at large height.** For distinct cluster offsets `τ_j`, depth `δ > 0` and
positive multiplicities `M_j` there are an aperture `a*` and a common phase `c` such that the
leading-order parity balance at the apertures `a_T` (common phase `c`, relative phases tending to
those of `a*`) is positive for every sufficiently large height `T`. -/
theorem exists_eventually_balance_pos {δ : ℝ} (hδ : 0 < δ) {τ M : Fin m → ℝ}
    (hτ : Function.Injective τ) (hM : ∀ j, 0 < M j) (hm : 0 < m) :
    ∃ a c : ℝ, ∀ᶠ T in atTop, 0 < ccmParityBalance δ (fun j => T + τ j) M (thetaT τ a c T) := by
  set p := lhNodes δ τ with hp_def
  have hre : ∀ j, (p j).re = δ := fun j => by simp [hp_def, lhNodes]
  have hp : ∀ j, 0 < (p j).re := fun j => (hre j).symm ▸ hδ
  have hinj : Function.Injective p := by
    intro j k h
    have := congrArg Complex.im h
    simp [hp_def, lhNodes] at this
    exact hτ this
  obtain ⟨L, -, hwin⟩ := exists_simple_boundary_nondegenerate_window hδ hre hinj hM hm
  obtain ⟨a, -, -, ⟨y₀, hy₀⟩, hprop, hsum⟩ := hwin 0
  set ν := phaseMass δ p M a with hν
  have hνj : ∀ j, ν j = (M j : ℂ) * Complex.exp ((-2 * τ j * a : ℝ) * I) := fun j => by
    rw [hν, hp_def, phaseMass_lhNodes]
  set j₀ : Fin m := ⟨0, hm⟩
  obtain ⟨y₁, hy₁, hHy₁⟩ := exists_unit_value hp hinj j₀
  have hTν : tForm p ν y₀ ≠ 0 := by
    intro h0
    have h1 := hy₀.2 y₁
    have hT1 : tForm p ν y₁ = ν j₀ := by simp [tForm, hHy₁, Pi.single_apply]
    rw [h0, hT1, norm_zero, zero_mul, hνj, norm_mul, Complex.norm_real, norm_unit_exp,
      Real.norm_eq_abs, abs_of_pos (hM j₀), mul_one] at h1
    have hg0 := gNorm_pos hp hinj hy₀.1
    have := hM j₀
    nlinarith
  -- phase-fixed top of `ν`
  set φ := Complex.arg (tForm p ν y₀) with hφ
  set u : ℂ := Complex.exp ((-(φ / 2) : ℝ) * I) with hu
  have hu1 : ‖u‖ = 1 := norm_unit_exp _
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  set yν := u • y₀ with hyν
  have htopν : IsTop p ν yν := isTop_csmul hu0 hy₀
  have hu2 : u ^ 2 = Complex.exp (-(φ : ℂ) * I) := by
    rw [hu, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hpolar : tForm p ν y₀ = (‖tForm p ν y₀‖ : ℂ) * Complex.exp ((φ : ℂ) * I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have hTyν : tForm p ν yν = (‖tForm p ν y₀‖ : ℂ) := by
    rw [hyν, tForm_csmul, hu2]
    conv_lhs => rw [hpolar]
    rw [mul_left_comm, ← Complex.exp_add, show -(φ : ℂ) * I + (φ : ℂ) * I = 0 by ring,
      Complex.exp_zero, mul_one]
  set w := ∑ j, yν j with hw_def
  have hw : w ≠ 0 := hsum yν htopν
  -- the common phase
  set c := Complex.arg (w ^ 2) - Real.pi / 2 with hc
  set e : ℂ := Complex.exp ((c : ℂ) * I) with he
  have he1 : ‖e‖ = 1 := norm_unit_exp _
  set μs := muStar τ M a c with hμs
  have hμs' : μs = fun j => e * ν j := by
    funext j; rw [hμs, muStar, hνj]
  set v : ℂ := Complex.exp ((-(c / 2) : ℝ) * I) with hv
  have hv1 : ‖v‖ = 1 := norm_unit_exp _
  have hv0 : v ≠ 0 := Complex.exp_ne_zero _
  have hev : e * v ^ 2 = 1 := by
    rw [he, hv, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : (c : ℂ) * I + ((2 : ℕ) : ℂ) * ((-(c / 2) : ℝ) * I) = 0 := by push_cast; ring
    rw [this, Complex.exp_zero]
  set yc := v • yν with hyc
  have hgc_eq : gNorm p yc = gNorm p y₀ := by
    rw [hyc, gNorm_csmul, hv1, hyν, gNorm_csmul, hu1]; ring
  have hgc := gNorm_pos hp hinj (smul_ne_zero hv0 htopν.1)
  set N : ℝ := ‖tForm p ν y₀‖ / gNorm p yc with hN_def
  have hN : 0 < N := div_pos (norm_pos_iff.mpr hTν) hgc
  have hTc : tForm p μs yc = ((N * gNorm p yc : ℝ) : ℂ) := by
    rw [hμs', tForm_mass_smul, hyc, tForm_csmul, hTyν, ← mul_assoc, hev, one_mul, hN_def,
      div_mul_cancel₀ _ hgc.ne']
  have htopc : IsTop p μs yc := by
    rw [hμs', isTop_unit_smul_iff p ν yc he1]; exact isTop_csmul hv0 htopν
  have hpropc : ∀ y, IsTop p μs y → ∃ κ : ℂ, y = κ • yc := by
    intro y hy
    rw [hμs', isTop_unit_smul_iff p ν y he1] at hy
    exact hprop yc y (isTop_csmul hv0 htopν) hy
  -- the boundary sign
  set rc := (∑ j, conj (yc j) * (aInf *ᵥ star yc) j).re with hrc_def
  have hrc : 0 < rc := by
    have hsumc : ∑ j, yc j = v * w := by
      rw [hw_def, Finset.mul_sum]; rfl
    have hsq : (∑ j, yc j) ^ 2 = I * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [hsumc, mul_pow]
      have hv2 : v ^ 2 = Complex.exp (-(c : ℂ) * I) := by
        rw [hv, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
      have hw2 : w ^ 2 = ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp ((Complex.arg (w ^ 2) : ℂ) * I) := by
        rw [← norm_pow]; exact (Complex.norm_mul_exp_arg_mul_I (w ^ 2)).symm
      rw [hv2, hw2, mul_left_comm, ← Complex.exp_add]
      have : -(c : ℂ) * I + (Complex.arg (w ^ 2) : ℂ) * I = ((Real.pi / 2 : ℝ) : ℂ) * I := by
        rw [hc]; push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      push_cast; ring
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    rw [hrc_def, sum_aInf, ← map_sum, ← map_pow, hsq, map_mul, conj_I, Complex.conj_ofReal]
    have : I / 2 * (-I * ((‖w‖ ^ 2 : ℝ) : ℂ)) = (((‖w‖ ^ 2 / 2) : ℝ) : ℂ) := by
      rw [show I / 2 * (-I * ((‖w‖ ^ 2 : ℝ) : ℂ)) = -(I * I) * ((‖w‖ ^ 2 : ℝ) : ℂ) / 2 by ring,
        I_mul_I]
      push_cast; ring
    rw [this, ofReal_re]
    positivity
  -- the contradiction
  refine ⟨a, c, ?_⟩
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set T₁ : ℝ := ∑ j, |τ j| + 1 with hT₁
  have hτle : ∀ j, |τ j| ≤ ∑ k, |τ k| := fun j =>
    Finset.single_le_sum (fun k _ => abs_nonneg (τ k)) (Finset.mem_univ j)
  have hfreq : ∀ n : ℕ, ∃ T, max (n : ℝ) T₁ ≤ T ∧
      ¬ 0 < ccmParityBalance δ (fun j => T + τ j) M (thetaT τ a c T) :=
    fun n => (Filter.frequently_atTop.mp hcon) (max n T₁)
  choose Tn hTn hFn using hfreq
  have hTnT₁ : ∀ n, T₁ ≤ Tn n := fun n => le_trans (le_max_right _ _) (hTn n)
  have hTnpos : ∀ n, 0 < Tn n := fun n => by
    have : 0 ≤ ∑ k, |τ k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith [hTnT₁ n]
  have hTnt : Tendsto Tn atTop atTop :=
    tendsto_atTop_mono (fun n => le_trans (le_max_left _ _) (hTn n)) tendsto_natCast_atTop_atTop
  have htpos : ∀ n j, 0 < Tn n + τ j := fun n j => by
    have := hτle j; have := neg_abs_le (τ j); linarith [hTnT₁ n]
  have htinj : ∀ n, Function.Injective fun j => Tn n + τ j := fun n j k h => hτ (by simpa using h)
  have hshift : ∀ n, hGram (lhNodes δ fun j => Tn n + τ j) = hGram p := fun n =>
    hGram_lhNodes_shift δ (Tn n) τ
  set μn : ℕ → Fin m → ℂ := fun n => phaseMu M (thetaT τ a c (Tn n)) with hμn
  set An : ℕ → Matrix (Fin m) (Fin m) ℂ := fun n => (Tn n : ℂ) • sumGram δ fun j => Tn n + τ j
  set Sn : ℕ → Matrix (Fin m) (Fin m) ℂ := fun n => sumGram δ fun j => Tn n + τ j
  -- maximizers
  choose Y hYS hYmax using fun n => exists_leadRatio_max hp hinj hm (μn n)
  choose Z hZS hZeq using fun n => exists_sphere_ratio_eq_lambdaMax hδ (htinj n) (htpos n) hm M
    (halfTurn (thetaT τ a c (Tn n)))
  have hpsi : ∀ n y, y ≠ 0 → Tn n * deltaS δ (fun j => Tn n + τ j) M (thetaT τ a c (Tn n)) y =
      psi p (μn n) (An n) (Sn n) y := by
    intro n y hy
    rw [mul_deltaS_eq_psi hδ (htinj n) (htpos n) M (thetaT τ a c (Tn n)) hy,
      psi_congr (hshift n)]
  have hlead : ∀ n, leadRatio (lhNodes δ fun j => Tn n + τ j) = leadRatio p :=
    fun n => leadRatio_congr (hshift n)
  have hineq : ∀ n, psi p (μn n) (An n) (Sn n) (Y n) + psi p (μn n) (An n) (Sn n) (Z n) ≤ 0 := by
    intro n
    have hY0 : Y n ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hYS n⟩
    have hZ0 : Z n ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hZS n⟩
    have hb := balance_ge_delta_add_delta hδ (htinj n) (htpos n) hm M (thetaT τ a c (Tn n))
      (hYS n) (fun w hw => by rw [hlead n]; exact hYmax n w hw) (hZS n) (hZeq n)
    have hF := not_lt.mp (hFn n)
    rw [← hpsi n _ hY0, ← hpsi n _ hZ0]
    have := hTnpos n
    nlinarith
  -- a convergent subsequence of maximizers
  obtain ⟨⟨y', z'⟩, hmem, ψ, hψ, hlim⟩ := ((isCompact_sphere (0 : Fin m → ℂ) 1).prod
    (isCompact_sphere (0 : Fin m → ℂ) 1)).tendsto_subseq (x := fun n => (Y n, Z n))
      (fun n => ⟨hYS n, hZS n⟩)
  have hy'lim : Tendsto (fun n => Y (ψ n)) atTop (𝓝 y') :=
    ((continuous_fst.tendsto _).comp hlim)
  have hz'lim : Tendsto (fun n => Z (ψ n)) atTop (𝓝 z') :=
    ((continuous_snd.tendsto _).comp hlim)
  have hy'0 : y' ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hmem.1⟩
  have hz'0 : z' ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hmem.2⟩
  have hTψ : Tendsto (fun n => Tn (ψ n)) atTop atTop := hTnt.comp hψ.tendsto_atTop
  have hμψ : Tendsto (fun n => μn (ψ n)) atTop (𝓝 μs) :=
    (tendsto_phaseMu_thetaT τ M a c).comp hTψ
  have hAψ : Tendsto (fun n => An (ψ n)) atTop (𝓝 aInf) := (tendsto_smul_sumGram δ τ).comp hTψ
  have hSψ : Tendsto (fun n => Sn (ψ n)) atTop (𝓝 0) := (tendsto_sumGram δ τ).comp hTψ
  have hpsiY := tendsto_psi hp hinj hμψ hAψ hSψ hy'lim hy'0
  have hpsiZ := tendsto_psi hp hinj hμψ hAψ hSψ hz'lim hz'0
  have hsumlim : psi p μs aInf 0 y' + psi p μs aInf 0 z' ≤ 0 :=
    le_of_tendsto' (hpsiY.add hpsiZ) fun n => hineq (ψ n)
  obtain ⟨hbd, hmaxc, hminc⟩ := leadRatio_extreme hp hinj htopc hN hTc hpropc
  have hLc : leadRatio p μs yc = N := by
    rw [leadRatio, hTc, ofReal_re, mul_div_cancel_right₀ _ hgc.ne']
  have hLIc : leadRatio p μs (I • yc) = -N := by rw [leadRatio_I_smul, hLc]
  have hyc0 : yc ≠ 0 := htopc.1
  have hIyc0 : I • yc ≠ 0 := smul_ne_zero I_ne_zero hyc0
  -- normalized test vectors
  obtain ⟨r₁, hr₁, w₁, hw₁S, hw₁⟩ := exists_unit_smul hyc0
  obtain ⟨r₂, hr₂, w₂, hw₂S, hw₂⟩ := exists_unit_smul hIyc0
  have hw₁0 : w₁ ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hw₁S⟩
  have hw₂0 : w₂ ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hw₂S⟩
  have hLw₁ : leadRatio p μs w₁ = N := by
    rw [← hLc, hw₁, leadRatio_real_smul _ _ _ hr₁.ne']
  have hLw₂ : leadRatio p μs w₂ = -N := by
    rw [← hLIc, hw₂, leadRatio_real_smul _ _ _ hr₂.ne']
  -- `y'` attains the maximum `N`
  have hy'max : leadRatio p μs y' = N := by
    have h := le_of_tendsto_of_tendsto' (tendsto_leadRatio hp hinj hμψ tendsto_const_nhds hw₁0)
      (tendsto_leadRatio hp hinj hμψ hy'lim hy'0) fun n => hYmax (ψ n) w₁ hw₁S
    rw [hLw₁] at h
    linarith [(hbd y' hy'0).1]
  -- `z'` attains the minimum `−N`
  have hz'min : leadRatio p μs z' = -N := by
    have hkey : ∀ n, leadRatio p (μn (ψ n)) (Z (ψ n)) / 2 +
        psi p (μn (ψ n)) (An (ψ n)) (Sn (ψ n)) (Z (ψ n)) / Tn (ψ n) ≤
          leadRatio p (μn (ψ n)) w₂ / 2 +
            psi p (μn (ψ n)) (An (ψ n)) (Sn (ψ n)) w₂ / Tn (ψ n) := by
      intro n
      have hZ0 : Z (ψ n) ≠ 0 := ne_zero_of_mem_sphere one_ne_zero ⟨_, hZS (ψ n)⟩
      have h1 := ratio_le_lambdaMax hδ (htinj (ψ n)) (htpos (ψ n)) hm M
        (halfTurn (thetaT τ a c (Tn (ψ n)))) hw₂0
      rw [← hZeq (ψ n), ratio_halfTurn, ratio_halfTurn] at h1
      have hTp := hTnpos (ψ n)
      have hd : ∀ y, y ≠ 0 → ratio δ (fun j => Tn (ψ n) + τ j) M (thetaT τ a c (Tn (ψ n))) y =
          leadRatio p (μn (ψ n)) y / 2 + psi p (μn (ψ n)) (An (ψ n)) (Sn (ψ n)) y / Tn (ψ n) := by
        intro y hy
        rw [← hpsi (ψ n) y hy, mul_div_cancel_left₀ _ hTp.ne', deltaS, hlead (ψ n)]
        ring
      rw [hd _ hZ0, hd _ hw₂0] at h1
      linarith
    have hinv : Tendsto (fun n => (Tn (ψ n))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hTψ
    have hl1 : Tendsto (fun n => leadRatio p (μn (ψ n)) (Z (ψ n)) / 2 +
        psi p (μn (ψ n)) (An (ψ n)) (Sn (ψ n)) (Z (ψ n)) / Tn (ψ n)) atTop
          (𝓝 (leadRatio p μs z' / 2 + psi p μs aInf 0 z' * 0)) := by
      refine ((tendsto_leadRatio hp hinj hμψ hz'lim hz'0).div_const 2).add ?_
      simpa [div_eq_mul_inv] using hpsiZ.mul hinv
    have hl2 : Tendsto (fun n => leadRatio p (μn (ψ n)) w₂ / 2 +
        psi p (μn (ψ n)) (An (ψ n)) (Sn (ψ n)) w₂ / Tn (ψ n)) atTop
          (𝓝 (leadRatio p μs w₂ / 2 + psi p μs aInf 0 w₂ * 0)) := by
      refine ((tendsto_leadRatio hp hinj hμψ tendsto_const_nhds hw₂0).div_const 2).add ?_
      simpa [div_eq_mul_inv] using
        (tendsto_psi hp hinj hμψ hAψ hSψ tendsto_const_nhds hw₂0).mul hinv
    have h := le_of_tendsto_of_tendsto' hl1 hl2 hkey
    rw [hLw₂, mul_zero, mul_zero, add_zero, add_zero] at h
    linarith [(hbd z' hz'0).2]
  obtain ⟨s₁, hs₁⟩ := hmaxc y' hy'0 hy'max
  obtain ⟨s₂, hs₂⟩ := hminc z' hz'0 hz'min
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl; apply hy'0; rw [hs₁]; simp
  have hs₂0 : s₂ ≠ 0 := by
    rintro rfl; apply hz'0; rw [hs₂]; simp
  rw [hs₁, psi_real_smul _ _ _ _ _ hs₁0, hs₂, psi_real_smul _ _ _ _ _ hs₂0] at hsumlim
  obtain ⟨e1, e2⟩ := psi_top_eq hp hinj htopc hN hTc aInf
  rw [e1, e2, ← hrc_def] at hsumlim
  have : 0 < N * rc / (2 * gNorm p yc) := by positivity
  linarith


/-- **CCM parity selection fails for clustered top layers at large height.** For every cluster shape
`τ` (distinct offsets), depth `δ > 0` and multiplicities `M_j > 0` there is a height `T₀` such that
every finite off-line set whose top layer sits at the ordinates `T + τ_j` with `T ≥ T₀` and has
multiplicities `M` has only reflection-odd ground states of the CCM restricted Weil form at
arbitrarily large apertures. This holds whatever integer relations the ordinates satisfy. -/
theorem exists_height_ground_odd {δ : ℝ} (hδ : 0 < δ) {τ M : Fin m → ℝ}
    (hτ : Function.Injective τ) (hM : ∀ j, 0 < M j) (hm : 0 < m) :
    ∃ T₀ : ℝ, ∀ T, T₀ ≤ T → ∀ h : FiniteTopLayer δ (fun j => T + τ j), h.mult = M → ∀ A : ℝ,
      ∃ a : SuzukiPositiveAperture, A < a.1 ∧
        ∀ u : CCMArchimedeanFormDomain a,
          ccmRestrictedWeilSourceQuadratic a u =
              ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
            ccmArchimedeanFormReflection a u = -u := by
  obtain ⟨a, c, hev⟩ := exists_eventually_balance_pos hδ hτ hM hm
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨T₀, fun T hT h hmult A => ?_⟩
  refine exists_aperture_ground_odd h ⟨apT a c T, ?_⟩ A
  rw [hmult]
  exact hT₀ T hT

end

end RHTower.CCMParityLargeHeight
