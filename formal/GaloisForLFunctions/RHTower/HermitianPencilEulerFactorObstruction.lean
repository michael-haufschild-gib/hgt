import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Instances.Matrix
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Hermitian pencils: real roots, and no local Euler factors

For a Hermitian `B` and a positive-definite `H`:

* `im_eq_zero_of_det_pencil_eq_zero`: every root `t` of `det(B + tH)` is real, since
  `v*(B + tH)v = 0` with `v*Bv ∈ ℝ` and `v*Hv > 0`.  Hence a representation `Ξ = c·det(B + tH)`
  would give RH (`riemannHypothesis_of_XiC_eq_det_pencil`): all the content is in the metric `H`.
* `continuousAt_pencilResolventTrace`: the resolvent trace `t ↦ Tr((B + tH)⁻¹ A)` is continuous at
  every nonreal `t`, so all its poles are real.
* `not_pencilResolventTrace_eq_eulerFactor`: such a trace never agrees, off the real axis, with a
  local Euler factor `-p^{-s}/(1 - p^{-s})`, `s = ½ + it`, because the latter has a pole at the
  nonreal point `t = i/2`.
-/

open Complex Matrix Filter Topology
open scoped Real ComplexOrder

namespace RHTower.HermitianPencil

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Real roots.**  For `B` Hermitian and `H` positive definite, every root of `det(B + tH)` is
real. -/
theorem im_eq_zero_of_det_pencil_eq_zero {B H : Matrix n n ℂ} (hB : B.IsHermitian) (hH : H.PosDef)
    {t : ℂ} (ht : (B+t • H).det=0) : t.im=0 := by
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ht
  have hsplit : star v ⬝ᵥ (B *ᵥ v)+t*(star v ⬝ᵥ (H *ᵥ v))=0 := by
    have h := congrArg (fun w => star v ⬝ᵥ w) hBv
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, dotProduct_zero] using h
  have hb : (star v ⬝ᵥ (B *ᵥ v)).im=0 := hB.im_star_dotProduct_mulVec_self v
  have hh : (star v ⬝ᵥ (H *ᵥ v)).im=0 := hH.1.im_star_dotProduct_mulVec_self v
  have hpos : 0<(star v ⬝ᵥ (H *ᵥ v)).re := hH.re_dotProduct_pos hv
  have him := congrArg Complex.im hsplit
  simp only [Complex.add_im, Complex.mul_im, hb, hh, mul_zero, zero_add, Complex.zero_im] at him
  exact (mul_eq_zero.mp him).resolve_right hpos.ne'

theorem det_pencil_ne_zero {B H : Matrix n n ℂ} (hB : B.IsHermitian) (hH : H.PosDef) {t : ℂ}
    (ht : t.im≠0) : (B+t • H).det≠0 :=
  fun h => ht (im_eq_zero_of_det_pencil_eq_zero hB hH h)

/-- A determinant representation `Ξ = c·det(B + tH)` with a Hermitian `B` and a positive-definite
time metric `H` would prove RH. -/
theorem riemannHypothesis_of_XiC_eq_det_pencil {B H : Matrix n n ℂ} (hB : B.IsHermitian)
    (hH : H.PosDef) {c : ℂ} (hc : c≠0) (hXi : ∀ t : ℂ, XiC t=c*(B+t • H).det) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  intro t ht
  rw [hXi] at ht
  exact im_eq_zero_of_det_pencil_eq_zero hB hH ((mul_eq_zero.mp ht).resolve_left hc)

/-- The resolvent trace of the pencil. -/
noncomputable def pencilResolventTrace (B H A : Matrix n n ℂ) (t : ℂ) : ℂ :=
  ((B+t • H)⁻¹*A).trace

/-- **The resolvent trace has only real poles**: it is continuous at every nonreal `t`. -/
theorem continuousAt_pencilResolventTrace {B H : Matrix n n ℂ} (hB : B.IsHermitian)
    (hH : H.PosDef) (A : Matrix n n ℂ) {t₀ : ℂ} (ht₀ : t₀.im≠0) :
    ContinuousAt (pencilResolventTrace B H A) t₀ := by
  have hP : Continuous (fun t : ℂ => B+t • H) := continuous_const.add (continuous_id.smul continuous_const)
  have hdet : Continuous (fun t : ℂ => (B+t • H).det) := hP.matrix_det
  have hadj : Continuous (fun t : ℂ => (B+t • H).adjugate) := hP.matrix_adjugate
  have hform : pencilResolventTrace B H A=
      fun t => (((B+t • H).det)⁻¹ • (B+t • H).adjugate*A).trace := by
    funext t
    rw [pencilResolventTrace, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [hform]
  have hinv : ContinuousAt (fun t : ℂ => ((B+t • H).det)⁻¹) t₀ :=
    hdet.continuousAt.inv₀ (det_pencil_ne_zero hB hH ht₀)
  exact (continuous_id.matrix_trace).continuousAt.comp
    (((hinv.smul hadj.continuousAt).mul continuousAt_const))

/-- **No local Euler factor.**  The resolvent trace of a Hermitian pencil with a positive-definite
time metric never agrees, at all nonreal regular points, with `-p^{-s}/(1 - p^{-s})`,
`s = ½ + it`: the latter has a pole at `t = i/2`, where the trace is continuous. -/
theorem not_pencilResolventTrace_eq_eulerFactor {B H : Matrix n n ℂ} (hB : B.IsHermitian)
    (hH : H.PosDef) (A : Matrix n n ℂ) {p : ℕ} (hp : 2≤p) :
    ¬ ∀ t : ℂ, t.im≠0 → 1-(p:ℂ)^(-(1/2+I*t))≠0 →
      pencilResolventTrace B H A t=-(p:ℂ)^(-(1/2+I*t))/(1-(p:ℂ)^(-(1/2+I*t))) := by
  intro hEq
  set t₀ : ℂ := I/2 with ht₀def
  have ht₀ : t₀.im≠0 := by simp [t₀]
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuousAt_pencilResolventTrace hB hH A ht₀) 1 one_pos
  set M : ℝ := ‖pencilResolventTrace B H A t₀‖+1 with hM
  set L : ℝ := Real.log p with hL
  have hL0 : 0<L := Real.log_pos (by exact_mod_cast (show 1<p by omega))
  set ε : ℝ := min (δ/2) (min (1/(L*(M+2))) (π/L)) with hε
  have hM0 : 0<M+2 := by positivity
  have hε0 : 0<ε := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hεδ : ε<δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεL1 : ε*L≤1/(M+2) := by
    have := min_le_left (1/(L*(M+2))) (π/L)
    have h2 : ε≤1/(L*(M+2)) := le_trans (min_le_right _ _) this
    calc ε*L≤1/(L*(M+2))*L := mul_le_mul_of_nonneg_right h2 hL0.le
      _=1/(M+2) := by field_simp
  have hεLπ : ε*L≤π := by
    have h2 : ε≤π/L := le_trans (min_le_right _ _) (min_le_right _ _)
    calc ε*L≤π/L*L := mul_le_mul_of_nonneg_right h2 hL0.le
      _=π := by field_simp
  set t : ℂ := t₀+(ε:ℂ) with htdef
  have hdist : dist t t₀<δ := by
    rw [htdef, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε0]
    exact hεδ
  have htim : t.im≠0 := by simp [t, t₀]
  -- the Euler factor at `t`: `p^{-s} = e^{i(-εL)}`
  have hs : -(1/2+I*t)=I*((-ε : ℝ) : ℂ) := by
    rw [htdef, ht₀def]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hpow : (p:ℂ)^(-(1/2+I*t))=Complex.exp (I*((-(ε*L) : ℝ) : ℂ)) := by
    rw [hs, Complex.cpow_def_of_ne_zero hp0, show (p:ℂ)=((p:ℝ):ℂ) by norm_cast,
      ← Complex.ofReal_log (by positivity)]
    congr 1
    rw [← hL]; push_cast; ring
  have hnum : ‖(p:ℂ)^(-(1/2+I*t))‖=1 := by
    rw [hpow, Complex.norm_exp_I_mul_ofReal]
  have hden_le : ‖1-(p:ℂ)^(-(1/2+I*t))‖≤ε*L := by
    rw [hpow, norm_sub_rev]
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(ε*L))
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (mul_pos hε0 hL0)] at this
    exact this
  have hden_ne : 1-(p:ℂ)^(-(1/2+I*t))≠0 := by
    rw [hpow, sub_ne_zero]
    intro h1
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1.symm
    have hk' : -(ε*L)=2*π*k := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hεL0 : 0<ε*L := mul_pos hε0 hL0
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · have : (k:ℝ)≤-1 := by exact_mod_cast (show k≤-1 by omega)
      nlinarith [Real.pi_pos]
    · have hk00 : (k:ℝ)=0 := by exact_mod_cast hk0
      rw [hk00, mul_zero] at hk'
      linarith
    · have : (1:ℝ)≤k := by exact_mod_cast hk0
      nlinarith [Real.pi_pos]
  have hval := hEq t htim hden_ne
  have hbig : M+2≤‖pencilResolventTrace B H A t‖ := by
    rw [hval, norm_div, norm_neg, hnum]
    have hdpos : 0<‖1-(p:ℂ)^(-(1/2+I*t))‖ := norm_pos_iff.mpr hden_ne
    rw [le_div_iff₀ hdpos]
    calc (M+2)*‖1-(p:ℂ)^(-(1/2+I*t))‖≤(M+2)*(ε*L) := mul_le_mul_of_nonneg_left hden_le hM0.le
      _≤(M+2)*(1/(M+2)) := mul_le_mul_of_nonneg_left hεL1 hM0.le
      _=1 := by field_simp
  have hsmall := hcont hdist
  rw [dist_eq_norm] at hsmall
  have htri : ‖pencilResolventTrace B H A t‖≤
      ‖pencilResolventTrace B H A t-pencilResolventTrace B H A t₀‖+
        ‖pencilResolventTrace B H A t₀‖ := norm_le_norm_sub_add _ _
  linarith

end RHTower.HermitianPencil
