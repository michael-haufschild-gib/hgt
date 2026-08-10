import Mathlib
import GaloisForLFunctions.HTGeometry.QPochhammer

/-!
# The q-Gamma function as an analytic function of its argument

`QPochhammer` carries the q-Gamma function on a structure encoding the right half-plane.  For the
differential theory the function has to be a plain analytic function of `z`, so this file builds
the denominator product `(qᶻ; q)_∞` as a locally uniform infinite product on `{Re z > 0}`, proves
it is holomorphic and nonvanishing there, and records Jackson's translation law for the resulting
plain function.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Filter Topology

noncomputable section

/-- The open right half-plane carrying the q-Gamma function. -/
def qHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

theorem isOpen_qHalfPlane : IsOpen qHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem norm_qcpow (q : RealEulerNome) (z : ℂ) : ‖(q.val : ℂ) ^ z‖ = q.val ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos q.pos z

/-- The `k`-th denominator factor `1 − q^{z+k}`. -/
def qDenomFactor (q : RealEulerNome) (k : ℕ) (z : ℂ) : ℂ :=
  1 - (q.val : ℂ) ^ (z + (k : ℂ))

/-- The denominator product `(qᶻ; q)_∞`, as a function of `z`. -/
def qDenomProduct (q : RealEulerNome) (z : ℂ) : ℂ := ∏' k : ℕ, qDenomFactor q k z

theorem qcpow_add_natCast (q : RealEulerNome) (z : ℂ) (k : ℕ) :
    (q.val : ℂ) ^ (z + (k : ℂ)) = (q.val : ℂ) ^ z * (q.val : ℂ) ^ k := by
  rw [Complex.cpow_add _ _ q.complex_ne_zero, Complex.cpow_natCast]

/-- The denominator product is the corpus q-Pochhammer symbol at `qᶻ`. -/
theorem qDenomProduct_eq (q : RealEulerNome) (z : ℂ) :
    qDenomProduct q z = qPochhammerInf ((q.val : ℂ) ^ z) q.toEulerNome := by
  rw [qDenomProduct, qPochhammerInf]
  refine tprod_congr fun k => ?_
  rw [qDenomFactor, qcpow_add_natCast, RealEulerNome.toEulerNome_coe]

theorem qDenomProduct_ne_zero (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    qDenomProduct q z ≠ 0 := by
  rw [qDenomProduct_eq]
  exact qPochhammerInf_ne_zero
    (EulerQGammaPoint.denominatorDatum ⟨q, z, hz⟩)

theorem differentiable_qDenomFactor (q : RealEulerNome) (k : ℕ) :
    Differentiable ℂ (qDenomFactor q k) := by
  intro z
  refine (analyticAt_const.sub ?_).differentiableAt
  refine AnalyticAt.cpow analyticAt_const ?_ ?_
  · exact analyticAt_id.add analyticAt_const
  · exact Or.inl (by
      have : (0 : ℝ) < q.val := q.pos
      simpa using this)

/-- The denominator product converges locally uniformly on the half-plane. -/
theorem hasProdLocallyUniformlyOn_qDenomFactor (q : RealEulerNome) :
    HasProdLocallyUniformlyOn (fun k : ℕ => qDenomFactor q k) (qDenomProduct q) qHalfPlane := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_qHalfPlane ?_
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    have hu : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
    have hbound : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ (∅ : Set ℂ),
        ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖ ≤ 0 := by
      filter_upwards with k
      intro z hz
      exact absurd hz (Set.notMem_empty z)
    have hcont : ∀ k : ℕ, ContinuousOn (fun z : ℂ => -((q.val : ℂ) ^ (z + (k : ℂ))))
        (∅ : Set ℂ) := fun k => continuousOn_empty _
    have hmain := Summable.hasProdUniformlyOn_one_add hK hu hbound hcont
    have hfun : (fun (k : ℕ) (z : ℂ) => 1 + -((q.val : ℂ) ^ (z + (k : ℂ))))
        = fun (k : ℕ) => qDenomFactor q k := by
      funext k z
      rw [qDenomFactor]
      ring
    have hval : (fun z : ℂ => ∏' k : ℕ, (1 + -((q.val : ℂ) ^ (z + (k : ℂ)))))
        = qDenomProduct q := by
      funext z
      rw [qDenomProduct]
      refine tprod_congr fun k => ?_
      rw [qDenomFactor]
      ring
    rw [hfun, hval] at hmain
    exact hmain
  · obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
    set δ : ℝ := z₀.re with hδ
    have hδpos : 0 < δ := hKsub hz₀K
    have hδle : ∀ z ∈ K, δ ≤ z.re := fun z hz => hz₀ hz
    have hu : Summable (fun k : ℕ => q.val ^ δ * q.val ^ k) :=
      (summable_geometric_of_lt_one q.pos.le q.lt_one).mul_left _
    have hbound : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K,
        ‖-((q.val : ℂ) ^ (z + (k : ℂ)))‖ ≤ q.val ^ δ * q.val ^ k := by
      filter_upwards with k
      intro z hz
      rw [norm_neg, qcpow_add_natCast, norm_mul, norm_qcpow, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.pos]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg q.pos.le k)
      exact Real.rpow_le_rpow_of_exponent_ge q.pos q.lt_one.le (hδle z hz)
    have hcont : ∀ k : ℕ, ContinuousOn (fun z : ℂ => -((q.val : ℂ) ^ (z + (k : ℂ)))) K := by
      intro k
      refine ContinuousOn.neg ?_
      refine ContinuousOn.cpow continuousOn_const (Continuous.continuousOn (by fun_prop)) ?_
      intro z _
      refine Or.inl ?_
      have hqpos : (0 : ℝ) < q.val := q.pos
      simpa using hqpos
    have hmain := Summable.hasProdUniformlyOn_one_add hK hu hbound hcont
    have hfun : (fun (k : ℕ) (z : ℂ) => 1 + -((q.val : ℂ) ^ (z + (k : ℂ))))
        = fun (k : ℕ) => qDenomFactor q k := by
      funext k z
      rw [qDenomFactor]
      ring
    have hval : (fun z : ℂ => ∏' k : ℕ, (1 + -((q.val : ℂ) ^ (z + (k : ℂ)))))
        = qDenomProduct q := by
      funext z
      rw [qDenomProduct]
      refine tprod_congr fun k => ?_
      rw [qDenomFactor]
      ring
    rw [hfun, hval] at hmain
    exact hmain

/-- The denominator product is holomorphic on the half-plane. -/
theorem differentiableOn_qDenomProduct (q : RealEulerNome) :
    DifferentiableOn ℂ (qDenomProduct q) qHalfPlane := by
  have hprod := hasProdLocallyUniformlyOn_qDenomFactor q
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ k ∈ S, qDenomFactor q k z) qHalfPlane := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun k _ =>
      (differentiable_qDenomFactor q k).differentiableOn
  exact ht.differentiableOn hd isOpen_qHalfPlane

/-- **Jackson's q-Gamma as a plain function** on the right half-plane. -/
def qGammaOn (q : RealEulerNome) (z : ℂ) : ℂ :=
  ((1 - q.val : ℝ) : ℂ) ^ (1 - z) * (((realQFactorialInf q : ℝ) : ℂ) / qDenomProduct q z)

theorem qPochhammerInf_nome_eq (q : RealEulerNome) :
    qPochhammerInf (q.val : ℂ) q.toEulerNome = ((realQFactorialInf q : ℝ) : ℂ) := by
  have hreal : HasProd (fun j : ℕ => (1 - q.val ^ (j + 1))) (realQFactorialInf q) :=
    (realQFactorial_multipliable q).hasProd
  have hmap : HasProd (fun j : ℕ => (1 - (q.val : ℂ) * (q.val : ℂ) ^ j))
      ((realQFactorialInf q : ℝ) : ℂ) := by
    have hcomp := hreal.map (Complex.ofRealHom : ℝ →+* ℂ) Complex.continuous_ofReal
    refine hcomp.congr_fun fun j => ?_
    simp only [Function.comp_apply, Complex.ofRealHom_eq_coe]
    push_cast
    ring
  rw [qPochhammerInf, RealEulerNome.toEulerNome_coe]
  exact hmap.tprod_eq

/-- The plain function agrees with the structured q-Gamma of `QPochhammer`. -/
theorem qGammaOn_eq_qGamma (x : EulerQGammaPoint) : qGammaOn x.q x.z = qGamma x := by
  rw [qGammaOn, qGamma, qGammaCore, qDenomProduct_eq, qPochhammerInf_nome_eq]

theorem qGammaOn_ne_zero (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    qGammaOn q z ≠ 0 := by
  have heq : qGammaOn q z = qGamma ⟨q, z, hz⟩ := qGammaOn_eq_qGamma ⟨q, z, hz⟩
  rw [heq, qGamma]
  refine mul_ne_zero ?_ (qGammaCore_ne_zero _)
  intro h0
  rw [Complex.cpow_eq_zero_iff] at h0
  exact q.one_sub_complex_ne_zero h0.1

theorem differentiableOn_qGammaOn (q : RealEulerNome) :
    DifferentiableOn ℂ (qGammaOn q) qHalfPlane := by
  intro z hz
  have hprod : DifferentiableWithinAt ℂ (qDenomProduct q) qHalfPlane z :=
    differentiableOn_qDenomProduct q z hz
  have hcpow : DifferentiableWithinAt ℂ
      (fun w : ℂ => ((1 - q.val : ℝ) : ℂ) ^ (1 - w)) qHalfPlane z := by
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.const_cpow ?_ (Or.inl q.one_sub_complex_ne_zero)
    exact (differentiableAt_const _).sub differentiableAt_id
  refine hcpow.mul (DifferentiableWithinAt.div ?_ hprod (qDenomProduct_ne_zero q hz))
  exact (differentiableAt_const _).differentiableWithinAt

/-- **Jackson's translation law** for the plain function. -/
theorem qGammaOn_shift (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    qGammaOn q (z + 1)
      = ((1 - (q.val : ℂ) ^ z) / ((1 - q.val : ℝ) : ℂ)) * qGammaOn q z := by
  have h := qGamma_shift ⟨q, z, hz⟩
  have h1 : qGammaOn q (z + 1) = qGamma (⟨q, z, hz⟩ : EulerQGammaPoint).shift :=
    qGammaOn_eq_qGamma (⟨q, z, hz⟩ : EulerQGammaPoint).shift
  have h2 : qGammaOn q z = qGamma (⟨q, z, hz⟩ : EulerQGammaPoint) :=
    qGammaOn_eq_qGamma ⟨q, z, hz⟩
  rw [h1, h2, h]

end

end GaloisForLFunctions.HTGeometry
