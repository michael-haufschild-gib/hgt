import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsVanishAtTheCusp
import GaloisForLFunctions.BlackHoleRingdown.TheLiftOfAnyModularWave

/-!
# The cusp channel

Every element `U` of the level-one cuspidal eigenbasis has `λ = ¼ + t²` with `t` real, so `e^{∓itτ} U` solves
the modular wave equation and lifts to solutions of the wave equation of the metric with frequencies
`ω = ±t - iD`, `D = ½` for Neumann and `D = 3/2` for Dirichlet data. Both branches occur, the damping rate is
exactly `D`, and nothing depends on a zero of `ξ`. The horocycle mean vanishes, so the echo channel, which reads
the horocycle mean, does not see these modes.

On the whole cuspidal space `C(τ) f = Σ cos(t_j τ) ⟨u_j, f⟩ u_j` is a strongly continuous contractive cosine
family: d'Alembert's law holds, and each coefficient solves `c'' = (¼ - λ_j) c`.

The corpus has no Weyl law, so it does not show that the level-one eigenbasis is nonempty.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace lp

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)

/-! ### The Laplacian in the chart -/

theorem hasDerivAt_mk_re (x y : ℝ) : HasDerivAt (fun q : ℝ => (⟨q, y⟩ : ℂ)) 1 x := by
  have h := ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
  have he : (fun q : ℝ => (⟨q, y⟩ : ℂ)) = fun q => ((id q : ℝ) : ℂ) + (y : ℂ) * I := by
    funext q
    apply Complex.ext <;> simp
  rw [he]
  simpa using h

theorem hasDerivAt_mk_im (x y : ℝ) : HasDerivAt (fun q : ℝ => (⟨x, q⟩ : ℂ)) I y := by
  have h := (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
  have he : (fun q : ℝ => (⟨x, q⟩ : ℂ)) = fun q => (x : ℂ) + ((id q : ℝ) : ℂ) * I := by
    funext q
    apply Complex.ext <;> simp
  rw [he]
  simpa using h

section Chart

variable {G : ℂ → ℂ} (hG : ContDiffOn ℝ 2 G {ζ : ℂ | 0 < ζ.im})

include hG

theorem contDiffAt_chart {ζ : ℂ} (hζ : 0 < ζ.im) : ContDiffAt ℝ 2 G ζ :=
  hG.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ)

theorem differentiableAt_fderiv_apply {ζ : ℂ} (hζ : 0 < ζ.im) (v : ℂ) :
    DifferentiableAt ℝ (fun w => fderiv ℝ G w v) ζ := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ G) ζ := (contDiffAt_chart hG hζ).fderiv_right (m := 1) (by norm_num)
  exact (h1.clm_apply contDiffAt_const).differentiableAt (by norm_num)

theorem hasDerivAt_chart_re (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => G ⟨q, y⟩) (fderiv ℝ G ⟨x, y⟩ 1) x :=
  ((contDiffAt_chart hG (ζ := ⟨x, y⟩) hy).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_mk_re x y)

theorem hasDerivAt_chart_im (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => G ⟨x, q⟩) (fderiv ℝ G ⟨x, y⟩ I) y :=
  ((contDiffAt_chart hG (ζ := ⟨x, y⟩) hy).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt y
    (hasDerivAt_mk_im x y)

theorem deriv_deriv_chart_re (x : ℝ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv fun q : ℝ => G ⟨q, y⟩) x = fderiv ℝ (fun w => fderiv ℝ G w 1) ⟨x, y⟩ 1 := by
  have h1 : (deriv fun q : ℝ => G ⟨q, y⟩) = fun q => fderiv ℝ G ⟨q, y⟩ 1 :=
    funext fun q => (hasDerivAt_chart_re hG q hy).deriv
  rw [h1]
  exact ((differentiableAt_fderiv_apply hG (ζ := ⟨x, y⟩) hy 1).hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_mk_re x y)).deriv

theorem deriv_deriv_chart_im (x : ℝ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv fun q : ℝ => G ⟨x, q⟩) y = fderiv ℝ (fun w => fderiv ℝ G w I) ⟨x, y⟩ I := by
  have h1 : (deriv fun q : ℝ => G ⟨x, q⟩) =ᶠ[𝓝 y] fun q => fderiv ℝ G ⟨x, q⟩ I := by
    filter_upwards [lt_mem_nhds hy] with q hq using (hasDerivAt_chart_im hG x hq).deriv
  rw [h1.deriv_eq]
  exact ((differentiableAt_fderiv_apply hG (ζ := ⟨x, y⟩) hy I).hasFDerivAt.comp_hasDerivAt y
    (hasDerivAt_mk_im x y)).deriv

end Chart

/-- **A Maass eigenfunction in the chart.** -/
theorem chart_laplacian {lam : ℝ} {f : UpperHalfPlane → ℂ} (hf : IsMaassEigenfunction lam f) (x : ℝ)
    {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * (deriv (deriv fun q : ℝ => f (ofComplex ⟨q, y⟩)) x +
      deriv (deriv fun q : ℝ => f (ofComplex ⟨x, q⟩)) y) = -(lam : ℂ) * f (ofComplex ⟨x, y⟩) := by
  have hmem : 0 < (⟨x, y⟩ : ℂ).im := hy
  have he := hf.2 (ofComplex ⟨x, y⟩)
  have h1 := deriv_deriv_chart_re hf.1 x hy
  have h2 := deriv_deriv_chart_im hf.1 x hy
  have hc : ((ofComplex (⟨x, y⟩ : ℂ) : UpperHalfPlane) : ℂ) = ⟨x, y⟩ := by
    rw [ofComplex_apply_of_im_pos hmem]
  have him : (ofComplex (⟨x, y⟩ : ℂ) : UpperHalfPlane).im = y := by
    rw [ofComplex_apply_of_im_pos hmem]
    rfl
  unfold positiveHyperbolicLaplacian at he
  rw [hc, him] at he
  have h1' : deriv (deriv fun q : ℝ => f (ofComplex ⟨q, y⟩)) x = _ := h1
  have h2' : deriv (deriv fun q : ℝ => f (ofComplex ⟨x, q⟩)) y = _ := h2
  rw [h1', h2']
  linear_combination -he

/-! ### The modes -/

/-- The frequency of an eigenvalue. -/
def cuspFrequency (lam : ℝ) : ℝ := Real.sqrt (lam - 1 / 4)

theorem cuspFrequency_sq {lam : ℝ} (h : 1 / 4 ≤ lam) : cuspFrequency lam ^ 2 = lam - 1 / 4 :=
  Real.sq_sqrt (by linarith)

theorem hasDerivAt_cexp_mul_real (w : ℂ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Complex.exp (w * τ)) (w * Complex.exp (w * τ)) τ := by
  have h := (((hasDerivAt_id τ).ofReal_comp).const_mul w).cexp
  simpa [mul_comm] using h

/-- The mode `e^{-isτ} U`. -/
def cuspMode (U : UpperHalfPlane → DeckSpace 0) (q : Deck 0) (s τ x y : ℝ) : ℂ :=
  Complex.exp (-(I * s) * τ) * U (ofComplex ⟨x, y⟩) q

section Mode

variable {lam s : ℝ} {U : UpperHalfPlane → DeckSpace 0} (q : Deck 0)

theorem hasDerivAt_cuspMode (U : UpperHalfPlane → DeckSpace 0) (q : Deck 0) (s τ x y : ℝ) :
    HasDerivAt (fun τ => cuspMode U q s τ x y) (-(I * s) * cuspMode U q s τ x y) τ := by
  have h := (hasDerivAt_cexp_mul_real (-(I * s)) τ).mul_const (U (ofComplex ⟨x, y⟩) q)
  refine h.congr_deriv ?_
  rw [cuspMode]
  ring

/-- **The cusp mode solves the modular wave equation.** -/
theorem isModularWave_cuspMode (hU : IsCuspLaplaceEigen 0 lam U) (hs : s ^ 2 = lam - 1 / 4) :
    IsModularWave (cuspMode U q s) := by
  have ht : ∀ x y : ℝ, (deriv fun τ => cuspMode U q s τ x y) =
      fun τ => -(I * s) * cuspMode U q s τ x y := fun x y =>
    funext fun τ => (hasDerivAt_cuspMode U q s τ x y).deriv
  have hd : ∀ x y : ℝ, Differentiable ℝ fun τ => cuspMode U q s τ x y := fun x y τ =>
    (hasDerivAt_cuspMode U q s τ x y).differentiableAt
  refine ⟨fun x y _ => hd x y, fun x y _ => ?_, fun τ x y hy => ?_⟩
  · rw [ht]
    exact (hd x y).const_mul _
  · rw [ht]
    have h2 := ((hasDerivAt_cuspMode U q s τ x y).const_mul (-(I * s))).deriv
    have hsC : (s : ℂ) ^ 2 = (lam : ℂ) - 1 / 4 := by
      rw [← Complex.ofReal_pow, hs]
      push_cast
      ring
    have hlap := chart_laplacian (hU.isMaassEigenfunction_component q) x hy
    simp only [component] at hlap
    have hxx : ∀ c : ℂ, (deriv fun x' : ℝ => c * U (ofComplex ⟨x', y⟩) q) =
        fun x' => c * deriv (fun x'' : ℝ => U (ofComplex ⟨x'', y⟩) q) x' := fun c =>
      funext fun x' => deriv_const_mul_field c
    have hyy : ∀ c : ℂ, (deriv fun y' : ℝ => c * U (ofComplex ⟨x, y'⟩) q) =
        fun y' => c * deriv (fun y'' : ℝ => U (ofComplex ⟨x, y''⟩) q) y' := fun c =>
      funext fun y' => deriv_const_mul_field c
    simp only [cuspMode] at h2 ⊢
    rw [h2, hxx, hyy, deriv_const_mul_field, deriv_const_mul_field]
    set c := Complex.exp (-(I * s) * τ)
    set u := U (ofComplex ⟨x, y⟩) q
    linear_combination -c * hlap + (-(c * u)) * hsC + (c * u * (s : ℂ) ^ 2) * I_sq

/-- The mode has vanishing horocycle mean. -/
theorem integral_cuspMode (hU : IsCuspLaplaceEigen 0 lam U) (s τ : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, cuspMode U q s τ x y = 0 := by
  simp only [cuspMode]
  rw [intervalIntegral.integral_const_mul, mean_slice hU q hy, mul_zero]

/-- The horizon profile of a mode keeps its modulus: there is no damping on the horizon. -/
theorem norm_cuspMode (U : UpperHalfPlane → DeckSpace 0) (s τ x y : ℝ) :
    ‖cuspMode U q s τ x y‖ = ‖U (ofComplex ⟨x, y⟩) q‖ := by
  have him : -(I * (s : ℂ)) * (τ : ℂ) = ((-(s * τ) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [cuspMode, norm_mul, him, Complex.norm_exp_ofReal_mul_I, one_mul]

variable {t r x y : ℝ}

/-- **The Neumann field of a cusp mode**: it is `e^{-iωτ} U / r` with `ω = s - i/2`. -/
theorem conformalScalar_neumann_cuspMode (U : UpperHalfPlane → DeckSpace 0) (s : ℝ) :
    conformalScalar (neumannWave (cuspMode U q s)) t r x y =
      Complex.exp (-(I * ((s : ℂ) - I / 2)) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
        U (ofComplex ⟨x, y⟩) q := by
  have he : -(I * ((s : ℂ) - I / 2)) * (hyperboloidalTime t (tortoise r) : ℂ) =
      -(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ) +
        -(I * s) * (hyperboloidalTime t (tortoise r) : ℂ) := by
    linear_combination (hyperboloidalTime t (tortoise r) : ℂ) / 2 * I_sq
  rw [he, Complex.exp_add]
  simp only [conformalScalar, neumannWave, neumannLift, dampedProfile, cuspMode]
  ring

/-- **The Dirichlet field of a cusp mode**: `tanh(x_*) e^{-iωτ} U / r` with `ω = s - 3i/2`. -/
theorem conformalScalar_dirichlet_cuspMode (U : UpperHalfPlane → DeckSpace 0) (s : ℝ) :
    conformalScalar (dirichletWave (cuspMode U q s)) t r x y =
      (Real.tanh (tortoise r) : ℂ) *
        (Complex.exp (-(I * ((s : ℂ) - 3 * I / 2)) * (hyperboloidalTime t (tortoise r) : ℂ)) /
          (r : ℂ)) * U (ofComplex ⟨x, y⟩) q := by
  have he : -(I * ((s : ℂ) - 3 * I / 2)) * (hyperboloidalTime t (tortoise r) : ℂ) =
      -(3 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ) +
        -(I * s) * (hyperboloidalTime t (tortoise r) : ℂ) := by
    linear_combination 3 * (hyperboloidalTime t (tortoise r) : ℂ) / 2 * I_sq
  rw [he, Complex.exp_add]
  simp only [conformalScalar, dirichletWave, dirichletLift, dampedProfile, cuspMode]
  ring

/-- **The rate is exactly `½`.** -/
theorem norm_neumann_cuspMode (U : UpperHalfPlane → DeckSpace 0) (s : ℝ) (hr : 0 < r) :
    ‖conformalScalar (neumannWave (cuspMode U q s)) t r x y‖ =
      Real.exp (-(hyperboloidalTime t (tortoise r)) / 2) / r * ‖U (ofComplex ⟨x, y⟩) q‖ := by
  rw [conformalScalar_neumann_cuspMode, norm_mul, norm_div, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  congr 3
  have h1 : (-(I * ((s : ℂ) - I / 2)) * (hyperboloidalTime t (tortoise r) : ℂ)) =
      ((-(hyperboloidalTime t (tortoise r)) / 2 : ℝ) : ℂ) +
        ((-(s * hyperboloidalTime t (tortoise r)) : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (hyperboloidalTime t (tortoise r) : ℂ) / 2 * I_sq
  rw [h1]
  simp

/-- **The rate is exactly `3/2`.** -/
theorem norm_dirichlet_cuspMode (U : UpperHalfPlane → DeckSpace 0) (s : ℝ) (hr : 0 < r) :
    ‖conformalScalar (dirichletWave (cuspMode U q s)) t r x y‖ =
      |Real.tanh (tortoise r)| * (Real.exp (-(3 * hyperboloidalTime t (tortoise r)) / 2) / r) *
        ‖U (ofComplex ⟨x, y⟩) q‖ := by
  rw [conformalScalar_dirichlet_cuspMode, norm_mul, norm_mul, norm_div, Complex.norm_exp,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le, Real.norm_eq_abs]
  congr 4
  have h1 : (-(I * ((s : ℂ) - 3 * I / 2)) * (hyperboloidalTime t (tortoise r) : ℂ)) =
      ((-(3 * hyperboloidalTime t (tortoise r)) / 2 : ℝ) : ℂ) +
        ((-(s * hyperboloidalTime t (tortoise r)) : ℝ) : ℂ) * I := by
    push_cast
    linear_combination 3 * (hyperboloidalTime t (tortoise r) : ℂ) / 2 * I_sq
  rw [h1]
  simp

end Mode

/-! ### The modes of the basis -/

/-- **Each element of the level-one eigenbasis gives modes on both branches.** -/
theorem exists_cuspEigenBasis_modes (i : CuspEigenIndex 0) :
    ∃ (U : UpperHalfPlane → DeckSpace 0) (hU : IsCuspLaplaceEigen 0 i.1 U),
      ((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0) = toDeckL2 U hU.memLp ∧
      (∀ q : Deck 0, IsModularWave (cuspMode U q (cuspFrequency i.1))) ∧
      (∀ q : Deck 0, IsModularWave (cuspMode U q (-cuspFrequency i.1))) ∧
      cuspFrequency i.1 ^ 2 = i.1 - 1 / 4 := by
  obtain ⟨U, hU, hb⟩ := cuspEigenBasis_spec i
  have hq := one_quarter_le_cuspEigenBasis i
  have hs := cuspFrequency_sq hq
  exact ⟨U, hU, hb, fun q => isModularWave_cuspMode q hU hs,
    fun q => isModularWave_cuspMode q hU (by rw [neg_sq, hs]), hs⟩

/-! ### Diagonal operators on a Hilbert basis -/

section Diagonal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A contractive symbol acting on `ℓ²`. -/
def lpSymbol (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (a : ℓ²(ι, ℂ)) : ℓ²(ι, ℂ) :=
  ⟨fun i => (c i : ℂ) * a i, by
    have hs := (lp.memℓp a).summable (by norm_num : 0 < (2 : ENNReal).toReal)
    refine memℓp_gen (hs.of_nonneg_of_le (fun i => by positivity) fun i => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (hc i)⟩

theorem lpSymbol_apply (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (a : ℓ²(ι, ℂ)) (i : ι) :
    lpSymbol c hc a i = (c i : ℂ) * a i := rfl

theorem norm_lpSymbol_le (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (a : ℓ²(ι, ℂ)) :
    ‖lpSymbol c hc a‖ ≤ ‖a‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp (lpSymbol c hc a)
  have h2 := lp.norm_rpow_eq_tsum hp a
  have hsa := (lp.memℓp a).summable hp
  have hle : ‖lpSymbol c hc a‖ ^ (2 : ENNReal).toReal ≤ ‖a‖ ^ (2 : ENNReal).toReal := by
    rw [h1, h2]
    refine Summable.tsum_le_tsum (fun i => ?_) ((lp.memℓp _).summable hp) hsa
    rw [lpSymbol_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (hc i)
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp).mp hle

/-- The diagonal operator of a contractive symbol on a Hilbert basis. -/
def diagOp (b : HilbertBasis ι ℂ H) (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : H) : H :=
  b.repr.symm (lpSymbol c hc (b.repr f))

theorem repr_diagOp (b : HilbertBasis ι ℂ H) (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : H) (i : ι) :
    b.repr (diagOp b c hc f) i = (c i : ℂ) * b.repr f i := by
  rw [diagOp, LinearIsometryEquiv.apply_symm_apply, lpSymbol_apply]

theorem norm_diagOp_le (b : HilbertBasis ι ℂ H) (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : H) :
    ‖diagOp b c hc f‖ ≤ ‖f‖ := by
  rw [diagOp, LinearIsometryEquiv.norm_map]
  simpa using norm_lpSymbol_le c hc (b.repr f)

theorem diagOp_basis (b : HilbertBasis ι ℂ H) (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (i : ι) [DecidableEq ι] :
    diagOp b c hc (b i) = (c i : ℂ) • b i := by
  apply b.repr.injective
  refine lp.ext (funext fun j => ?_)
  rw [repr_diagOp, map_smul, lp.coeFn_smul, Pi.smul_apply, b.repr_self, lp.single_apply]
  by_cases hij : j = i
  · subst hij
    simp
  · simp [hij]

/-- D'Alembert's law for symbols. -/
theorem diagOp_add_diagOp (b : HilbertBasis ι ℂ H) (c₁ c₂ c₃ c₄ : ι → ℝ) (h₁ : ∀ i, |c₁ i| ≤ 1)
    (h₂ : ∀ i, |c₂ i| ≤ 1) (h₃ : ∀ i, |c₃ i| ≤ 1) (h₄ : ∀ i, |c₄ i| ≤ 1)
    (hsym : ∀ i, c₁ i + c₂ i = 2 * (c₃ i * c₄ i)) (f : H) :
    diagOp b c₁ h₁ f + diagOp b c₂ h₂ f =
      diagOp b c₃ h₃ (diagOp b c₄ h₄ f) + diagOp b c₃ h₃ (diagOp b c₄ h₄ f) := by
  apply b.repr.injective
  refine lp.ext (funext fun i => ?_)
  rw [map_add, map_add, lp.coeFn_add, lp.coeFn_add, Pi.add_apply, Pi.add_apply, repr_diagOp,
    repr_diagOp, repr_diagOp, repr_diagOp]
  have hC : (c₁ i : ℂ) + (c₂ i : ℂ) = 2 * ((c₃ i : ℂ) * (c₄ i : ℂ)) := by exact_mod_cast hsym i
  linear_combination (b.repr f i) * hC

end Diagonal

/-! ### The cosine family of the cuspidal space -/

/-- The cuspidal cosine family at level one. -/
def cuspCosine (τ : ℝ) (f : CuspidalL2 0) : CuspidalL2 0 :=
  diagOp (cuspEigenBasis 0) (fun i => Real.cos (cuspFrequency i.1 * τ)) (fun _ => Real.abs_cos_le_one _) f

theorem repr_cuspCosine (τ : ℝ) (f : CuspidalL2 0) (i : CuspEigenIndex 0) :
    (cuspEigenBasis 0).repr (cuspCosine τ f) i =
      (Real.cos (cuspFrequency i.1 * τ) : ℂ) * (cuspEigenBasis 0).repr f i :=
  repr_diagOp _ _ _ f i

/-- **Contractivity.** -/
theorem norm_cuspCosine_le (τ : ℝ) (f : CuspidalL2 0) : ‖cuspCosine τ f‖ ≤ ‖f‖ :=
  norm_diagOp_le _ _ _ f

theorem cuspCosine_zero (f : CuspidalL2 0) : cuspCosine 0 f = f := by
  apply (cuspEigenBasis 0).repr.injective
  refine lp.ext (funext fun i => ?_)
  rw [repr_cuspCosine, mul_zero, Real.cos_zero, Complex.ofReal_one, one_mul]

/-- **D'Alembert's law.** -/
theorem cuspCosine_add_sub (τ σ : ℝ) (f : CuspidalL2 0) :
    cuspCosine (τ + σ) f + cuspCosine (τ - σ) f =
      cuspCosine τ (cuspCosine σ f) + cuspCosine τ (cuspCosine σ f) :=
  diagOp_add_diagOp _ _ _ _ _ _ _ _ _ (fun i => by
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring) f

/-- **Strong continuity.** -/
theorem continuous_cuspCosine (f : CuspidalL2 0) : Continuous fun τ => cuspCosine τ f := by
  refine continuous_iff_continuousAt.mpr fun τ₀ => ?_
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hs := (lp.memℓp ((cuspEigenBasis 0).repr f)).summable hp
  have hdiff : ∀ τ, ‖cuspCosine τ f - cuspCosine τ₀ f‖ ^ (2 : ENNReal).toReal =
      ∑' i, ‖((Real.cos (cuspFrequency i.1 * τ) : ℂ) - Real.cos (cuspFrequency i.1 * τ₀)) *
        (cuspEigenBasis 0).repr f i‖ ^ (2 : ENNReal).toReal := fun τ => by
    rw [← LinearIsometryEquiv.norm_map (cuspEigenBasis 0).repr, map_sub, lp.norm_rpow_eq_tsum hp]
    refine tsum_congr fun i => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, repr_cuspCosine, repr_cuspCosine, sub_mul]
  have hlim : Tendsto (fun τ => ∑' i, ‖((Real.cos (cuspFrequency i.1 * τ) : ℂ) -
      Real.cos (cuspFrequency i.1 * τ₀)) * (cuspEigenBasis 0).repr f i‖ ^ (2 : ENNReal).toReal) (𝓝 τ₀)
      (𝓝 (∑' _i : CuspEigenIndex 0, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun i =>
      4 * ‖(cuspEigenBasis 0).repr f i‖ ^ (2 : ENNReal).toReal) (hs.mul_left 4) (fun i => ?_) ?_
    · have hc : Continuous fun τ : ℝ => ((Real.cos (cuspFrequency i.1 * τ) : ℂ) -
          Real.cos (cuspFrequency i.1 * τ₀)) * (cuspEigenBasis 0).repr f i ^ 1 := by
        fun_prop
      have hat := hc.tendsto τ₀
      simp only [sub_self, zero_mul, pow_one] at hat
      have := (hat.norm).rpow_const (p := (2 : ENNReal).toReal) (Or.inr hp.le)
      simpa [norm_zero, Real.zero_rpow hp.ne'] using this
    · refine Eventually.of_forall fun τ i => ?_
      have hb : ‖(Real.cos (cuspFrequency i.1 * τ) : ℂ) - Real.cos (cuspFrequency i.1 * τ₀)‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        linarith [Real.abs_cos_le_one (cuspFrequency i.1 * τ),
          Real.abs_cos_le_one (cuspFrequency i.1 * τ₀)]
      have h2 : (2 : ENNReal).toReal = (2 : ℕ) := by norm_num
      rw [norm_mul, Real.norm_of_nonneg (by positivity), h2, Real.rpow_natCast, Real.rpow_natCast,
        mul_pow]
      gcongr
      nlinarith [norm_nonneg ((Real.cos (cuspFrequency i.1 * τ) : ℂ) - Real.cos (cuspFrequency i.1 * τ₀))]
  rw [tsum_zero] at hlim
  have h2 : Tendsto (fun τ => ‖cuspCosine τ f - cuspCosine τ₀ f‖ ^ (2 : ENNReal).toReal) (𝓝 τ₀) (𝓝 0) := by
    simpa only [hdiff] using hlim
  have h3 := h2.rpow_const (p := ((2 : ENNReal).toReal)⁻¹) (Or.inr (by positivity))
  rw [Real.zero_rpow (by positivity)] at h3
  have h4 : Tendsto (fun τ => ‖cuspCosine τ f - cuspCosine τ₀ f‖) (𝓝 τ₀) (𝓝 0) := by
    refine h3.congr fun τ => ?_
    rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hp.ne', Real.rpow_one]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h4

/-- **The wave equation, coefficient by coefficient.**  Each coefficient of `C(τ) f` solves
`c'' = (¼ - λ) c`. -/
theorem hasDerivAt_repr_cuspCosine (f : CuspidalL2 0) (i : CuspEigenIndex 0) (τ : ℝ) :
    HasDerivAt (fun τ => (cuspEigenBasis 0).repr (cuspCosine τ f) i)
      ((-(cuspFrequency i.1 * Real.sin (cuspFrequency i.1 * τ)) : ℝ) * (cuspEigenBasis 0).repr f i) τ ∧
    HasDerivAt (fun τ => ((-(cuspFrequency i.1 * Real.sin (cuspFrequency i.1 * τ)) : ℝ) : ℂ) *
        (cuspEigenBasis 0).repr f i)
      (((1 / 4 - i.1 : ℝ) : ℂ) * (cuspEigenBasis 0).repr (cuspCosine τ f) i) τ := by
  have hs := cuspFrequency_sq (one_quarter_le_cuspEigenBasis i)
  have hu : HasDerivAt (fun τ : ℝ => cuspFrequency i.1 * τ) (cuspFrequency i.1) τ := by
    simpa using (hasDerivAt_id τ).const_mul (cuspFrequency i.1)
  constructor
  · have h := ((Real.hasDerivAt_cos _).comp τ hu).ofReal_comp.mul_const ((cuspEigenBasis 0).repr f i)
    simp only [repr_cuspCosine]
    refine h.congr_deriv ?_
    push_cast
    ring
  · have h := (((Real.hasDerivAt_sin _).comp τ hu).const_mul (cuspFrequency i.1)).neg.ofReal_comp.mul_const
      ((cuspEigenBasis 0).repr f i)
    refine h.congr_deriv ?_
    rw [repr_cuspCosine]
    have hsC : (cuspFrequency i.1 : ℂ) ^ 2 = (i.1 : ℂ) - 1 / 4 := by
      rw [← Complex.ofReal_pow, hs]
      push_cast
      ring
    push_cast
    linear_combination (-(Complex.cos ((cuspFrequency i.1 : ℂ) * τ)) *
      (cuspEigenBasis 0).repr f i) * hsC

end GaloisForLFunctions.BlackHoleRingdown

end
