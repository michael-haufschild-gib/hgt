import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative

/-!
# Exponential polynomials on the real line

An *exponential polynomial* is a finite sum `∑ⱼ Pⱼ(x)·e^{λⱼ x}` with complex polynomial
coefficients and complex frequencies.  This module builds the two spaces

* `expPolySpaceC` — exponential polynomials as entire functions of a complex variable;
* `expPolySpace` — their restrictions to the real line,

and the elementary calculus of the blocks `polyExpC P μ : z ↦ P(z)·e^{μ z}`:

* `deriv_polyExpC` — the block differentiates to a block with the same frequency;
* `exists_poly_deriv_add_smul` — the map `Q ↦ Q′ + ν·Q` on `ℂ[X]` is surjective, so every block
  is the value `G′ − λ·G` of a block `G` (the first-order inhomogeneous solve at any `λ`);
* `sub_smul_mem_expPolySpace_solvable` — hence `G ↦ G′ − λ·G` is surjective on `expPolySpace`;
* `eq_const_mul_exp_of_deriv_eq_smul` — the homogeneous solutions of `u′ = λ·u` on `ℝ` are the
  constant multiples of `x ↦ e^{λ x}`.

Together these are exactly what is needed to integrate a constant-coefficient linear ODE one root
at a time, which is done in `AnseloneKorevaarTranslationRank`.

Only classical one-variable calculus is used; nothing here is specific to any research target.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-! ## Blocks -/

/-- The entire exponential-polynomial block `z ↦ P(z)·e^{μ z}`. -/
def polyExpC (P : Polynomial ℂ) (μ : ℂ) : ℂ → ℂ := fun z => P.eval z * Complex.exp (μ * z)

/-- The restriction of an exponential-polynomial block to the real line. -/
def polyExp (P : Polynomial ℂ) (μ : ℂ) : ℝ → ℂ := fun x => polyExpC P μ (x : ℂ)

theorem polyExpC_apply (P : Polynomial ℂ) (μ z : ℂ) :
    polyExpC P μ z = P.eval z * Complex.exp (μ * z) := rfl

theorem polyExp_apply (P : Polynomial ℂ) (μ : ℂ) (x : ℝ) :
    polyExp P μ x = P.eval (x : ℂ) * Complex.exp (μ * (x : ℂ)) := rfl

theorem polyExpC_zero_poly (μ : ℂ) : polyExpC 0 μ = 0 := by
  funext z; simp [polyExpC]

theorem polyExpC_add_poly (P Q : Polynomial ℂ) (μ : ℂ) :
    polyExpC (P + Q) μ = polyExpC P μ + polyExpC Q μ := by
  funext z; simp [polyExpC, add_mul]

theorem polyExpC_smul_poly (c : ℂ) (P : Polynomial ℂ) (μ : ℂ) :
    polyExpC (c • P) μ = c • polyExpC P μ := by
  funext z; simp [polyExpC, Polynomial.smul_eq_C_mul, mul_assoc]

theorem polyExp_add_poly (P Q : Polynomial ℂ) (μ : ℂ) :
    polyExp (P + Q) μ = polyExp P μ + polyExp Q μ := by
  funext x
  have := congrArg (fun F : ℂ → ℂ => F (x : ℂ)) (polyExpC_add_poly P Q μ)
  simpa [polyExp] using this

theorem polyExp_smul_poly (c : ℂ) (P : Polynomial ℂ) (μ : ℂ) :
    polyExp (c • P) μ = c • polyExp P μ := by
  funext x
  have := congrArg (fun F : ℂ → ℂ => F (x : ℂ)) (polyExpC_smul_poly c P μ)
  simpa [polyExp] using this

/-- The frequency-preserving polynomial shift produced by differentiating a block. -/
def shiftPoly (μ : ℂ) (P : Polynomial ℂ) : Polynomial ℂ := Polynomial.derivative P + μ • P

theorem hasDerivAt_polyExpC (P : Polynomial ℂ) (μ z : ℂ) :
    HasDerivAt (polyExpC P μ) (polyExpC (shiftPoly μ P) μ z) z := by
  have h1 : HasDerivAt (fun w : ℂ => P.eval w) ((Polynomial.derivative P).eval z) z :=
    P.hasDerivAt z
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (μ * w)) (Complex.exp (μ * z) * μ) z := by
    have hlin : HasDerivAt (fun w : ℂ => μ * w) μ z := by
      simpa using (hasDerivAt_id z).const_mul μ
    simpa using hlin.cexp
  have h := h1.mul h2
  refine h.congr_deriv ?_
  simp only [polyExpC, shiftPoly, Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  ring

theorem deriv_polyExpC (P : Polynomial ℂ) (μ : ℂ) :
    deriv (polyExpC P μ) = polyExpC (shiftPoly μ P) μ := by
  funext z
  exact (hasDerivAt_polyExpC P μ z).deriv

theorem hasDerivAt_polyExp (P : Polynomial ℂ) (μ : ℂ) (x : ℝ) :
    HasDerivAt (polyExp P μ) (polyExp (shiftPoly μ P) μ x) x :=
  (hasDerivAt_polyExpC P μ (x : ℂ)).comp_ofReal

theorem deriv_polyExp (P : Polynomial ℂ) (μ : ℂ) :
    deriv (polyExp P μ) = polyExp (shiftPoly μ P) μ := by
  funext x
  exact (hasDerivAt_polyExp P μ x).deriv

theorem analyticOnNhd_polyExpC (P : Polynomial ℂ) (μ : ℂ) :
    AnalyticOnNhd ℂ (polyExpC P μ) (Set.univ : Set ℂ) := by
  have hP : AnalyticOnNhd ℂ (fun z : ℂ => P.eval z) (Set.univ : Set ℂ) :=
    AnalyticOnNhd.eval_polynomial P
  have hE : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (μ * z)) (Set.univ : Set ℂ) :=
    (analyticOnNhd_const.mul analyticOnNhd_id).cexp
  exact hP.mul hE

theorem differentiable_polyExpC (P : Polynomial ℂ) (μ : ℂ) :
    Differentiable ℂ (polyExpC P μ) := fun z => (hasDerivAt_polyExpC P μ z).differentiableAt

theorem contDiff_polyExpC (P : Polynomial ℂ) (μ : ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (polyExpC P μ) :=
  (analyticOnNhd_polyExpC P μ).contDiff

theorem contDiff_polyExp (P : Polynomial ℂ) (μ : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (polyExp P μ) :=
  ((contDiff_polyExpC P μ).restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

/-! ## The exponential-polynomial spaces -/

/-- Restriction of a function of a complex variable to the real line, as a linear map. -/
def restrictReal : (ℂ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun F := fun x : ℝ => F (x : ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictReal_apply (F : ℂ → ℂ) (x : ℝ) : restrictReal F x = F (x : ℂ) := rfl

theorem restrictReal_polyExpC (P : Polynomial ℂ) (μ : ℂ) :
    restrictReal (polyExpC P μ) = polyExp P μ := rfl

/-- Entire exponential polynomials. -/
def expPolySpaceC : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ (Set.range fun p : Polynomial ℂ × ℂ => polyExpC p.1 p.2)

/-- Exponential polynomials as functions on the real line. -/
def expPolySpace : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun p : Polynomial ℂ × ℂ => polyExp p.1 p.2)

theorem polyExpC_mem_expPolySpaceC (P : Polynomial ℂ) (μ : ℂ) :
    polyExpC P μ ∈ expPolySpaceC :=
  Submodule.subset_span ⟨(P, μ), rfl⟩

theorem polyExp_mem_expPolySpace (P : Polynomial ℂ) (μ : ℂ) :
    polyExp P μ ∈ expPolySpace :=
  Submodule.subset_span ⟨(P, μ), rfl⟩

/-- **The real exponential polynomials are exactly the restrictions of the entire ones.** -/
theorem expPolySpace_eq_map : expPolySpace = expPolySpaceC.map restrictReal := by
  rw [expPolySpaceC, Submodule.map_span, expPolySpace]
  congr 1
  rw [← Set.range_comp]
  rfl

theorem exists_entire_extension {g : ℝ → ℂ} (hg : g ∈ expPolySpace) :
    ∃ G : ℂ → ℂ, G ∈ expPolySpaceC ∧ ∀ x : ℝ, G (x : ℂ) = g x := by
  rw [expPolySpace_eq_map] at hg
  obtain ⟨G, hGmem, hGeq⟩ := hg
  exact ⟨G, hGmem, fun x => congrFun hGeq x⟩

/-! ## Analytic and smooth regularity -/

theorem analyticOnNhd_of_mem_expPolySpaceC {G : ℂ → ℂ} (hG : G ∈ expPolySpaceC) :
    AnalyticOnNhd ℂ G (Set.univ : Set ℂ) := by
  induction hG using Submodule.span_induction with
  | mem F hF => obtain ⟨p, rfl⟩ := hF; exact analyticOnNhd_polyExpC p.1 p.2
  | zero => exact analyticOnNhd_const
  | add F H _ _ hF hH => exact hF.add hH
  | smul c F _ hF =>
      have hsm : (c • F) = fun z : ℂ => c * F z := rfl
      rw [hsm]
      exact analyticOnNhd_const.mul hF

theorem contDiff_of_mem_expPolySpace {g : ℝ → ℂ} (hg : g ∈ expPolySpace) :
    ContDiff ℝ (⊤ : ℕ∞) g := by
  induction hg using Submodule.span_induction with
  | mem f hf => obtain ⟨p, rfl⟩ := hf; exact contDiff_polyExp p.1 p.2
  | zero => exact contDiff_const
  | add f h _ _ hf hh => exact hf.add hh
  | smul c f _ hf => exact hf.const_smul c

theorem differentiable_of_mem_expPolySpace {g : ℝ → ℂ} (hg : g ∈ expPolySpace) :
    Differentiable ℝ g :=
  (contDiff_of_mem_expPolySpace hg).differentiable (by simp)

/-- `expPolySpace` is closed under differentiation. -/
theorem deriv_mem_expPolySpace {g : ℝ → ℂ} (hg : g ∈ expPolySpace) :
    deriv g ∈ expPolySpace := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, rfl⟩ := hf
      rw [deriv_polyExp]
      exact polyExp_mem_expPolySpace _ _
  | zero => simp
  | add f h hf hh ihf ihh =>
      have hdf := differentiable_of_mem_expPolySpace hf
      have hdh := differentiable_of_mem_expPolySpace hh
      have : deriv (f + h) = deriv f + deriv h := by
        funext x; exact deriv_add (hdf x) (hdh x)
      rw [this]
      exact Submodule.add_mem _ ihf ihh
  | smul c f hf ihf =>
      have : deriv (c • f) = c • deriv f := by
        funext x
        simpa using deriv_const_smul (hf := (differentiable_of_mem_expPolySpace hf) x) c
      rw [this]
      exact Submodule.smul_mem _ c ihf

/-! ## Surjectivity of `Q ↦ Q′ + ν·Q` on polynomials -/

private theorem exists_poly_deriv_add_smul_of_ne {ν : ℂ} (hν : ν ≠ 0) :
    ∀ n : ℕ, ∀ P : Polynomial ℂ, P.natDegree ≤ n →
      ∃ Q : Polynomial ℂ, Polynomial.derivative Q + ν • Q = P := by
  intro n
  induction n with
  | zero =>
      intro P hP
      refine ⟨Polynomial.C (P.coeff 0 / ν), ?_⟩
      have hPC : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
      rw [Polynomial.derivative_C, zero_add, Polynomial.smul_C, smul_eq_mul,
        mul_div_cancel₀ _ hν, ← hPC]
  | succ n ih =>
      intro P hP
      set Q₀ : Polynomial ℂ := ν⁻¹ • P with hQ₀
      have hdegD : (Polynomial.derivative P).natDegree ≤ n := by
        have := Polynomial.natDegree_derivative_le P
        omega
      have hR : (-(ν⁻¹ • Polynomial.derivative P)).natDegree ≤ n := by
        have h1 : (-(ν⁻¹ • Polynomial.derivative P)).natDegree
            = (ν⁻¹ • Polynomial.derivative P).natDegree := Polynomial.natDegree_neg _
        have h2 : (ν⁻¹ • Polynomial.derivative P).natDegree
            ≤ (Polynomial.derivative P).natDegree := by
          rw [Polynomial.smul_eq_C_mul]
          exact le_trans (Polynomial.natDegree_mul_le) (by simp)
        omega
      obtain ⟨Q₁, hQ₁⟩ := ih _ hR
      refine ⟨Q₀ + Q₁, ?_⟩
      have hQ₀eq : Polynomial.derivative Q₀ + ν • Q₀ = ν⁻¹ • Polynomial.derivative P + P := by
        rw [hQ₀, Polynomial.derivative_smul, smul_smul, mul_inv_cancel₀ hν, one_smul]
      have hexp : Polynomial.derivative (Q₀ + Q₁) + ν • (Q₀ + Q₁)
          = (Polynomial.derivative Q₀ + ν • Q₀) + (Polynomial.derivative Q₁ + ν • Q₁) := by
        rw [map_add, smul_add]; abel
      rw [hexp, hQ₀eq, hQ₁]
      abel

theorem exists_poly_deriv_add_smul (ν : ℂ) (P : Polynomial ℂ) :
    ∃ Q : Polynomial ℂ, Polynomial.derivative Q + ν • Q = P := by
  rcases eq_or_ne ν 0 with rfl | hν
  · exact ⟨polyAntideriv P, by rw [derivative_polyAntideriv, zero_smul, add_zero]⟩
  · exact exists_poly_deriv_add_smul_of_ne hν P.natDegree P le_rfl

/-! ## Solving the first-order inhomogeneous equation inside `expPolySpace` -/

/-- The functions of the form `G′ − λ·G` with `G` an exponential polynomial. -/
private def solvableSpace (lam : ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {u : ℝ → ℂ | ∃ G : ℝ → ℂ, G ∈ expPolySpace ∧ deriv G - lam • G = u}
  add_mem' := by
    rintro u v ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
    refine ⟨G + H, Submodule.add_mem _ hG hH, ?_⟩
    have hd : deriv (G + H) = deriv G + deriv H := by
      funext x
      exact deriv_add ((differentiable_of_mem_expPolySpace hG) x)
        ((differentiable_of_mem_expPolySpace hH) x)
    rw [hd]
    module
  zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
  smul_mem' := by
    rintro c u ⟨G, hG, rfl⟩
    refine ⟨c • G, Submodule.smul_mem _ c hG, ?_⟩
    have hd : deriv (c • G) = c • deriv G := by
      funext x
      simpa using deriv_const_smul (hf := (differentiable_of_mem_expPolySpace hG) x) c
    rw [hd]
    module

/-- **Every exponential polynomial is `G′ − λ·G` for some exponential polynomial `G`.** -/
theorem exists_expPolySpace_solve (lam : ℂ) {h : ℝ → ℂ} (hh : h ∈ expPolySpace) :
    ∃ G : ℝ → ℂ, G ∈ expPolySpace ∧ deriv G - lam • G = h := by
  have hsub : expPolySpace ≤ solvableSpace lam := by
    rw [expPolySpace]
    refine Submodule.span_le.mpr ?_
    rintro u ⟨p, rfl⟩
    obtain ⟨Q, hQ⟩ := exists_poly_deriv_add_smul (p.2 - lam) p.1
    refine ⟨polyExp Q p.2, polyExp_mem_expPolySpace _ _, ?_⟩
    rw [deriv_polyExp]
    funext x
    have hstep : polyExp (shiftPoly p.2 Q) p.2 x - lam * polyExp Q p.2 x
        = polyExp (Polynomial.derivative Q + (p.2 - lam) • Q) p.2 x := by
      simp only [polyExp, polyExpC, shiftPoly, Polynomial.eval_add, Polynomial.eval_smul,
        smul_eq_mul, sub_mul]
      ring
    simpa [hQ] using hstep
  exact hsub hh

/-! ## The homogeneous first-order equation -/

/-- **`u′ = λ·u` on the real line forces `u(x) = u(0)·e^{λ x}`.** -/
theorem eq_const_mul_exp_of_deriv_eq_smul {lam : ℂ} {u : ℝ → ℂ} (hu : Differentiable ℝ u)
    (hrel : ∀ x, deriv u x = lam * u x) :
    ∀ x : ℝ, u x = u 0 * Complex.exp (lam * (x : ℂ)) := by
  set v : ℝ → ℂ := fun x => u x * Complex.exp (-(lam * (x : ℂ))) with hv
  have hvderiv : ∀ x : ℝ, HasDerivAt v 0 x := by
    intro x
    have h1 : HasDerivAt u (deriv u x) x := (hu x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => Complex.exp (-(lam * (y : ℂ))))
        (Complex.exp (-(lam * (x : ℂ))) * (-lam)) x := by
      have hz : HasDerivAt (fun w : ℂ => Complex.exp (-(lam * w)))
          (Complex.exp (-(lam * (x : ℂ))) * (-lam)) (x : ℂ) := by
        have hlin : HasDerivAt (fun w : ℂ => -(lam * w)) (-lam) (x : ℂ) := by
          have hbase : HasDerivAt (fun w : ℂ => (-lam) * w) (-lam) (x : ℂ) := by
            simpa using (hasDerivAt_id (x : ℂ)).const_mul (-lam)
          simpa only [neg_mul] using hbase
        simpa using hlin.cexp
      exact hz.comp_ofReal
    have h := h1.mul h2
    refine h.congr_deriv ?_
    rw [hrel x]
    ring
  have hvdiff : Differentiable ℝ v := fun x => (hvderiv x).differentiableAt
  have hvzero : ∀ x : ℝ, deriv v x = 0 := fun x => (hvderiv x).deriv
  have hconst : ∀ x : ℝ, v x = v 0 := fun x => is_const_of_deriv_eq_zero hvdiff hvzero x 0
  intro x
  have hx := hconst x
  simp only [hv, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hx
  have hne : Complex.exp (-(lam * (x : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hx
  rw [← hx]
  rw [mul_assoc, ← Complex.exp_add]
  simp

/-- The homogeneous solutions live in `expPolySpace`. -/
theorem mem_expPolySpace_of_deriv_eq_smul {lam : ℂ} {u : ℝ → ℂ} (hu : Differentiable ℝ u)
    (hrel : ∀ x, deriv u x = lam * u x) : u ∈ expPolySpace := by
  have hform := eq_const_mul_exp_of_deriv_eq_smul hu hrel
  have : u = polyExp (Polynomial.C (u 0)) lam := by
    funext x
    rw [hform x, polyExp_apply, Polynomial.eval_C]
  rw [this]
  exact polyExp_mem_expPolySpace _ _

end

end GaloisForLFunctions.HTGeometry
