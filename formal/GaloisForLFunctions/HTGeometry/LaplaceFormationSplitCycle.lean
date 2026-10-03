import GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity
import GaloisForLFunctions.HTGeometry.PositiveInvolutionIsIdentity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Laplace formation: the source-generated passive split cycle

Let `ν` be a probability measure on `[0, ∞)` other than `δ₀`.  Its complete Laplace response
`a_n = ∫ e^{-nx} dν(x)`, `n ≥ 1`, satisfies `0 < a_n ≤ a_1 < 1`, and the hidden defect
`d_n = √(1 - a_n²)` satisfies `0 < d_1 ≤ d_n < 1`.  On the response space `ℓ^∞` (indexed by
`k = n - 1 ∈ ℕ`) the visible formation `A b = (a_n b_n)` and hidden formation `D b = (d_n b_n)`
combine into the split encoder `C b = (A b, D b)` into `ℓ^∞(ℂ²)` (fibrewise Euclidean norm):

* `C` is an isometry and the fibrewise row decoder `Q(u, v) = (a_n u_n + d_n v_n)` is a contraction
  with `Q C = I`;
* `‖A b‖ ≤ a_1 ‖b‖` and `‖D b‖ ≥ d_1 ‖b‖`;
* no contraction recovers a nonzero state from its visible formation alone;
* the fibrewise matrices `[[a_n, d_n], [d_n, -a_n]]` form the unique marked self-adjoint unitary
  completion, an isometric involution `𝒥` with `𝒥(b, 0) = C b`;
* a positive contractive involution of a Hilbert space is the identity
  (`eq_one_of_isPositive_of_mul_self_eq_one`).
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal InnerProductSpace ComplexOrder

namespace GaloisForLFunctions.HTGeometry

/-- A nontrivial positive half-line formation law: a probability measure on `[0, ∞)`, not `δ₀`. -/
structure HalfLineFormationLaw where
  measure : Measure ℝ
  isProbability : IsProbabilityMeasure measure
  support : measure (Ici 0)ᶜ = 0
  ne_dirac : measure ≠ Measure.dirac 0

attribute [instance] HalfLineFormationLaw.isProbability

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

theorem ae_nonneg : ∀ᵐ x ∂ν.measure, 0 ≤ x := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) ν.support
  simpa using hx

/-- The Laplace response `L_ν(n) = ∫ e^{-nx} dν`. -/
def laplace (n : ℕ) : ℝ := ∫ x, Real.exp (-(n * x)) ∂ν.measure

theorem integrable_exp_neg (n : ℕ) : Integrable (fun x => Real.exp (-(n * x))) ν.measure := by
  refine Integrable.of_bound (by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(n * x))).aestronglyMeasurable 1 ?_
  filter_upwards [ν.ae_nonneg] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem laplace_pos (n : ℕ) : 0 < ν.laplace n := by
  rw [laplace]
  exact integral_exp_pos (ν.integrable_exp_neg n)

theorem laplace_zero : ν.laplace 0 = 1 := by
  simp [laplace]

theorem laplace_le_laplace_one {n : ℕ} (hn : 1 ≤ n) : ν.laplace n ≤ ν.laplace 1 := by
  refine integral_mono_ae (ν.integrable_exp_neg n) (ν.integrable_exp_neg 1) ?_
  filter_upwards [ν.ae_nonneg] with x hx
  apply Real.exp_le_exp.2
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  nlinarith

theorem laplace_one_lt_one : ν.laplace 1 < 1 := by
  by_contra hge
  have hge' : 1 ≤ ν.laplace 1 := not_lt.1 hge
  have hle : ν.laplace 1 ≤ 1 := by
    rw [laplace]
    calc ∫ x, Real.exp (-((1 : ℕ) * x)) ∂ν.measure ≤ ∫ _x, (1 : ℝ) ∂ν.measure :=
          integral_mono_ae (ν.integrable_exp_neg 1) (integrable_const 1) (by
            filter_upwards [ν.ae_nonneg] with x hx
            rw [Real.exp_le_one_iff, neg_nonpos]; push_cast; linarith)
      _ = 1 := by simp
  have heq : ∫ x, (1 - Real.exp (-((1 : ℕ) * x))) ∂ν.measure = 0 := by
    rw [integral_sub (integrable_const 1) (ν.integrable_exp_neg 1)]
    simp only [integral_const, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
      Measure.real]
    change 1 - ν.laplace 1 = 0
    linarith
  have hnn : 0 ≤ᵐ[ν.measure] fun x => 1 - Real.exp (-((1 : ℕ) * x)) := by
    filter_upwards [ν.ae_nonneg] with x hx
    have : Real.exp (-((1 : ℕ) * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]; push_cast; linarith
    simp only [Pi.zero_apply]; linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn
    ((integrable_const 1).sub (ν.integrable_exp_neg 1))).1 heq
  have hconc : ∀ᵐ x ∂ν.measure, x ∈ ({0} : Set ℝ) := by
    filter_upwards [hzero, ν.ae_nonneg] with x hx hx0
    simp only [Pi.zero_apply, sub_eq_zero] at hx
    have h1 : -((1 : ℕ) * x) = 0 := by
      have := Real.exp_eq_one_iff (-((1 : ℕ) * x)) |>.1 hx.symm
      exact this
    simp only [Nat.cast_one, one_mul, neg_eq_zero] at h1
    exact h1
  apply ν.ne_dirac
  rw [← Measure.restrict_eq_self_of_ae_mem hconc, Measure.restrict_singleton]
  have h0 : ν.measure {0} = 1 := by
    rw [← measure_univ (μ := ν.measure)]
    refine le_antisymm (measure_mono (subset_univ _)) ?_
    rw [← Measure.restrict_eq_self_of_ae_mem hconc] at *
    simp
  rw [h0, one_smul]

/-- Visible amplitude `a_k = L_ν(k + 1)`. -/
def visible (k : ℕ) : ℝ := ν.laplace (k + 1)

/-- Hidden amplitude `d_k = √(1 - a_k²)`. -/
def hidden (k : ℕ) : ℝ := Real.sqrt (1 - ν.visible k ^ 2)

theorem visible_pos (k : ℕ) : 0 < ν.visible k := ν.laplace_pos _

theorem visible_le (k : ℕ) : ν.visible k ≤ ν.visible 0 :=
  ν.laplace_le_laplace_one (by omega)

theorem visible_lt_one (k : ℕ) : ν.visible k < 1 :=
  (ν.visible_le k).trans_lt ν.laplace_one_lt_one

theorem visible_sq_add_hidden_sq (k : ℕ) : ν.visible k ^ 2 + ν.hidden k ^ 2 = 1 := by
  rw [hidden, Real.sq_sqrt (by nlinarith [ν.visible_pos k, ν.visible_lt_one k])]
  ring

theorem hidden_pos (k : ℕ) : 0 < ν.hidden k :=
  Real.sqrt_pos.2 (by nlinarith [ν.visible_pos k, ν.visible_lt_one k])

theorem hidden_lt_one (k : ℕ) : ν.hidden k < 1 := by
  rw [hidden, Real.sqrt_lt' one_pos]
  nlinarith [ν.visible_pos k]

theorem hidden_zero_le (k : ℕ) : ν.hidden 0 ≤ ν.hidden k := by
  apply Real.sqrt_le_sqrt
  have h1 := ν.visible_le k
  have h2 := ν.visible_pos k
  nlinarith

/-- **(LFD.4)** `0 < a_n ≤ a_1 < 1` and `0 < d_1 ≤ d_n < 1`. -/
theorem amplitude_bounds (k : ℕ) :
    0 < ν.visible k ∧ ν.visible k ≤ ν.visible 0 ∧ ν.visible 0 < 1 ∧
      0 < ν.hidden 0 ∧ ν.hidden 0 ≤ ν.hidden k ∧ ν.hidden k < 1 :=
  ⟨ν.visible_pos k, ν.visible_le k, ν.visible_lt_one 0, ν.hidden_pos 0, ν.hidden_zero_le k,
    ν.hidden_lt_one k⟩

end HalfLineFormationLaw

/-! ## The split cycle on the response space -/

/-- Response space `ℓ^∞`, indexed by `k = n - 1`. -/
abbrev LaplaceResponseSpace := lp (fun _ : ℕ => ℂ) ⊤

/-- Fibre-Hilbert sum `ℓ^∞(ℂ²)` with fibrewise Euclidean norm. -/
abbrev LaplaceSplitSpace := lp (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) ⊤

theorem norm_euclidean_two (u v : ℂ) :
    ‖(WithLp.toLp 2 ![u, v] : EuclideanSpace ℂ (Fin 2))‖ = Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  rfl

theorem bddAbove_of_le_norm {E : Type*} [NormedAddCommGroup E] {f : ℕ → E} (b : LaplaceResponseSpace)
    {c : ℝ} (h : ∀ k, ‖f k‖ ≤ c * ‖b k‖) (hc : 0 ≤ c) : BddAbove (Set.range fun k => ‖f k‖) := by
  refine ⟨c * ‖b‖, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (h k).trans (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) b k) hc)

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

/-- Visible formation `A_ν b = (a_n b_n)`. -/
def visibleFormation (b : LaplaceResponseSpace) : LaplaceResponseSpace :=
  ⟨fun k => (ν.visible k : ℂ) * b k, memℓp_infty (bddAbove_of_le_norm b (c := 1) (fun k => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos k).le]
    exact mul_le_mul_of_nonneg_right (ν.visible_lt_one k).le (norm_nonneg _)) zero_le_one)⟩

/-- Hidden formation `D_ν b = (d_n b_n)`. -/
def hiddenFormation (b : LaplaceResponseSpace) : LaplaceResponseSpace :=
  ⟨fun k => (ν.hidden k : ℂ) * b k, memℓp_infty (bddAbove_of_le_norm b (c := 1) (fun k => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.hidden_pos k).le]
    exact mul_le_mul_of_nonneg_right (ν.hidden_lt_one k).le (norm_nonneg _)) zero_le_one)⟩

theorem norm_fibre (k : ℕ) (z : ℂ) :
    ‖(WithLp.toLp 2 ![(ν.visible k : ℂ) * z, (ν.hidden k : ℂ) * z] : EuclideanSpace ℂ (Fin 2))‖ =
      ‖z‖ := by
  rw [norm_euclidean_two, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (ν.visible_pos k).le, Real.norm_of_nonneg (ν.hidden_pos k).le, mul_pow,
    mul_pow, ← add_mul, ν.visible_sq_add_hidden_sq, one_mul, Real.sqrt_sq (norm_nonneg _)]

/-- Split encoder `C_ν b = (A_ν b, D_ν b)`. -/
def splitEncoder (b : LaplaceResponseSpace) : LaplaceSplitSpace :=
  ⟨fun k => WithLp.toLp 2 ![(ν.visible k : ℂ) * b k, (ν.hidden k : ℂ) * b k],
    memℓp_infty (bddAbove_of_le_norm b (c := 1) (fun k => by rw [ν.norm_fibre, one_mul])
      zero_le_one)⟩

theorem fibre_decode_le (k : ℕ) (y : EuclideanSpace ℂ (Fin 2)) :
    ‖(ν.visible k : ℂ) * y.ofLp 0 + (ν.hidden k : ℂ) * y.ofLp 1‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (ν.visible_pos k).le, Real.norm_of_nonneg (ν.hidden_pos k).le]
  have h := ν.visible_sq_add_hidden_sq k
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (ν.visible k * ‖y.ofLp 1‖ - ν.hidden k * ‖y.ofLp 0‖), norm_nonneg (y.ofLp 0),
    norm_nonneg (y.ofLp 1), ν.visible_pos k, ν.hidden_pos k]

/-- Fibrewise row decoder `Q_ν(u, v) = (a_n u_n + d_n v_n)`. -/
def splitDecoder (y : LaplaceSplitSpace) : LaplaceResponseSpace :=
  ⟨fun k => (ν.visible k : ℂ) * (y k).ofLp 0 + (ν.hidden k : ℂ) * (y k).ofLp 1,
    memℓp_infty ⟨‖y‖, by
      rintro _ ⟨k, rfl⟩
      exact (ν.fibre_decode_le k (y k)).trans (lp.norm_apply_le_norm (by simp) y k)⟩⟩

theorem norm_splitEncoder (b : LaplaceResponseSpace) : ‖ν.splitEncoder b‖ = ‖b‖ := by
  rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
  congr 1
  funext k
  exact ν.norm_fibre k (b k)

theorem norm_splitDecoder_le (y : LaplaceSplitSpace) : ‖ν.splitDecoder y‖ ≤ ‖y‖ :=
  lp.norm_le_of_forall_le (norm_nonneg _) fun k =>
    (ν.fibre_decode_le k (y k)).trans (lp.norm_apply_le_norm (by simp) y k)

theorem splitDecoder_splitEncoder (b : LaplaceResponseSpace) :
    ν.splitDecoder (ν.splitEncoder b) = b := by
  apply lp.ext
  funext k
  change (ν.visible k : ℂ) * ((ν.visible k : ℂ) * b k) + (ν.hidden k : ℂ) * ((ν.hidden k : ℂ) * b k) =
    b k
  have h := ν.visible_sq_add_hidden_sq k
  have hc : ((ν.visible k : ℂ)) ^ 2 + ((ν.hidden k : ℂ)) ^ 2 = 1 := by exact_mod_cast h
  linear_combination (b k) * hc

/-- **Theorem 3.1 (LFD.11)** The source-generated split cycle: `C_ν` is isometric, `Q_ν` is
contractive, and `Q_ν C_ν = I`; consequently `Q_ν` has norm one. -/
theorem splitCycle (b : LaplaceResponseSpace) :
    ‖ν.splitEncoder b‖ = ‖b‖ ∧ (∀ y, ‖ν.splitDecoder y‖ ≤ ‖y‖) ∧
      ν.splitDecoder (ν.splitEncoder b) = b ∧
      (b ≠ 0 → ‖ν.splitDecoder (ν.splitEncoder b)‖ = ‖ν.splitEncoder b‖) :=
  ⟨ν.norm_splitEncoder b, ν.norm_splitDecoder_le, ν.splitDecoder_splitEncoder b,
    fun _ => by rw [ν.splitDecoder_splitEncoder, ν.norm_splitEncoder]⟩

/-- **Corollary 3.2 (LFD.12)** `‖A_ν b‖ ≤ a_1 ‖b‖` and `‖D_ν b‖ ≥ √(1 - a_1²) ‖b‖`. -/
theorem visible_hidden_bounds (b : LaplaceResponseSpace) :
    ‖ν.visibleFormation b‖ ≤ ν.visible 0 * ‖b‖ ∧ ν.hidden 0 * ‖b‖ ≤ ‖ν.hiddenFormation b‖ := by
  constructor
  · refine lp.norm_le_of_forall_le (mul_nonneg (ν.visible_pos 0).le (norm_nonneg _)) fun k => ?_
    change ‖(ν.visible k : ℂ) * b k‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.visible_pos k).le]
    exact mul_le_mul (ν.visible_le k) (lp.norm_apply_le_norm (by simp) b k) (norm_nonneg _)
      (ν.visible_pos 0).le
  · have hd := ν.hidden_pos 0
    rw [← le_div_iff₀' hd]
    refine lp.norm_le_of_forall_le (div_nonneg (norm_nonneg _) hd.le) fun k => ?_
    rw [le_div_iff₀' hd]
    have hk : ‖(ν.hiddenFormation b) k‖ ≤ ‖ν.hiddenFormation b‖ :=
      lp.norm_apply_le_norm (by simp) _ k
    change ‖(ν.hidden k : ℂ) * b k‖ ≤ _ at hk
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.hidden_pos k).le] at hk
    exact (mul_le_mul_of_nonneg_right (ν.hidden_zero_le k) (norm_nonneg _)).trans hk

/-- **Corollary 3.3 (LFD.13)** No contraction recovers a nonzero state from its visible
formation alone. -/
theorem eq_zero_of_visible_recovery (R : LaplaceResponseSpace → LaplaceResponseSpace)
    (hR : ∀ x, ‖R x‖ ≤ ‖x‖) {b : LaplaceResponseSpace} (hb : R (ν.visibleFormation b) = b) :
    b = 0 := by
  by_contra hne
  have hpos : 0 < ‖b‖ := norm_pos_iff.2 hne
  have h1 : ‖b‖ ≤ ν.visible 0 * ‖b‖ := by
    calc ‖b‖ = ‖R (ν.visibleFormation b)‖ := by rw [hb]
      _ ≤ ‖ν.visibleFormation b‖ := hR _
      _ ≤ ν.visible 0 * ‖b‖ := (ν.visible_hidden_bounds b).1
  have := ν.visible_lt_one 0
  nlinarith

/-! ## The marked conservative involution -/

/-- Embedding of a state into the visible sheet: `b ↦ (b, 0)`. -/
def visibleSheet (b : LaplaceResponseSpace) : LaplaceSplitSpace :=
  ⟨fun k => WithLp.toLp 2 ![b k, 0], memℓp_infty (bddAbove_of_le_norm b (c := 1) (fun k => by
    rw [norm_euclidean_two, norm_zero, one_mul]; simp [Real.sqrt_sq (norm_nonneg _)])
    zero_le_one)⟩

theorem fibre_involution_norm (k : ℕ) (u v : ℂ) :
    ‖(WithLp.toLp 2 ![(ν.visible k : ℂ) * u + (ν.hidden k : ℂ) * v,
        (ν.hidden k : ℂ) * u - (ν.visible k : ℂ) * v] : EuclideanSpace ℂ (Fin 2))‖ =
      ‖(WithLp.toLp 2 ![u, v] : EuclideanSpace ℂ (Fin 2))‖ := by
  rw [norm_euclidean_two, norm_euclidean_two]
  congr 1
  have h := ν.visible_sq_add_hidden_sq k
  set a := ν.visible k
  set d := ν.hidden k
  have e1 : ‖(a : ℂ) * u + (d : ℂ) * v‖ ^ 2 + ‖(d : ℂ) * u - (a : ℂ) * v‖ ^ 2 =
      (a ^ 2 + d ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e1, h, one_mul]

/-- The conservative sheet involution `𝒥_ν(u, v) = (A u + D v, D u - A v)`. -/
def sheetInvolution (y : LaplaceSplitSpace) : LaplaceSplitSpace :=
  ⟨fun k => WithLp.toLp 2 ![(ν.visible k : ℂ) * (y k).ofLp 0 + (ν.hidden k : ℂ) * (y k).ofLp 1,
      (ν.hidden k : ℂ) * (y k).ofLp 0 - (ν.visible k : ℂ) * (y k).ofLp 1],
    memℓp_infty ⟨‖y‖, by
      rintro _ ⟨k, rfl⟩
      dsimp only
      rw [ν.fibre_involution_norm]
      have hy : (WithLp.toLp 2 ![(y k).ofLp 0, (y k).ofLp 1] : EuclideanSpace ℂ (Fin 2)) = y k := by
        apply WithLp.ofLp_injective
        funext i; fin_cases i <;> rfl
      rw [hy]
      exact lp.norm_apply_le_norm (by simp) y k⟩⟩

/-- **Theorem 4.1 (LFD.15)** `𝒥_ν` is an isometric involution with `𝒥_ν(b, 0) = C_ν b`. -/
theorem sheetInvolution_laws (y : LaplaceSplitSpace) (b : LaplaceResponseSpace) :
    ‖ν.sheetInvolution y‖ = ‖y‖ ∧ ν.sheetInvolution (ν.sheetInvolution y) = y ∧
      ν.sheetInvolution (visibleSheet b) = ν.splitEncoder b := by
  have hy : ∀ k, (WithLp.toLp 2 ![(y k).ofLp 0, (y k).ofLp 1] : EuclideanSpace ℂ (Fin 2)) = y k :=
    fun k => by
      apply WithLp.ofLp_injective
      funext i; fin_cases i <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
    congr 1
    funext k
    change ‖(WithLp.toLp 2 ![_, _] : EuclideanSpace ℂ (Fin 2))‖ = _
    rw [ν.fibre_involution_norm, hy]
  · apply lp.ext
    funext k
    apply WithLp.ofLp_injective
    funext i
    have h := ν.visible_sq_add_hidden_sq k
    have hc : ((ν.visible k : ℂ)) ^ 2 + ((ν.hidden k : ℂ)) ^ 2 = 1 := by exact_mod_cast h
    fin_cases i
    · change (ν.visible k : ℂ) * ((ν.visible k : ℂ) * (y k).ofLp 0 + (ν.hidden k : ℂ) * (y k).ofLp 1) +
        (ν.hidden k : ℂ) * ((ν.hidden k : ℂ) * (y k).ofLp 0 - (ν.visible k : ℂ) * (y k).ofLp 1) =
          (y k).ofLp 0
      linear_combination ((y k).ofLp 0) * hc
    · change (ν.hidden k : ℂ) * ((ν.visible k : ℂ) * (y k).ofLp 0 + (ν.hidden k : ℂ) * (y k).ofLp 1) -
        (ν.visible k : ℂ) * ((ν.hidden k : ℂ) * (y k).ofLp 0 - (ν.visible k : ℂ) * (y k).ofLp 1) =
          (y k).ofLp 1
      linear_combination ((y k).ofLp 1) * hc
  · apply lp.ext
    funext k
    apply WithLp.ofLp_injective
    funext i
    fin_cases i
    · change (ν.visible k : ℂ) * b k + (ν.hidden k : ℂ) * 0 = (ν.visible k : ℂ) * b k
      ring
    · change (ν.hidden k : ℂ) * b k - (ν.visible k : ℂ) * 0 = (ν.hidden k : ℂ) * b k
      ring

/-- **Theorem 4.1, uniqueness.**  A self-adjoint unitary `2 × 2` matrix with first column the
marked positive vector `(a, d)`, `d ≠ 0`, is `[[a, d], [d, -a]]`. -/
theorem marked_completion_unique (k : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hself : M.conjTranspose = M) (hunit : M * M.conjTranspose = 1)
    (h00 : M 0 0 = ν.visible k) (h10 : M 1 0 = ν.hidden k) :
    M = !![(ν.visible k : ℂ), ν.hidden k; ν.hidden k, -(ν.visible k : ℂ)] := by
  have h01 : M 0 1 = ν.hidden k := by
    have := congrFun (congrFun hself 0) 1
    simp only [Matrix.conjTranspose_apply] at this
    rw [← this, h10, Complex.star_def, Complex.conj_ofReal]
  have horth := congrFun (congrFun hunit 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply,
    one_ne_zero, if_false] at horth
  rw [h10, h00, h01] at horth
  have hconj : (starRingEnd ℂ) (ν.hidden k : ℂ) = ν.hidden k := Complex.conj_ofReal _
  have hconj' : (starRingEnd ℂ) (ν.visible k : ℂ) = ν.visible k := Complex.conj_ofReal _
  simp only [Complex.star_def, hconj, hconj'] at horth
  have hd : (ν.hidden k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ν.hidden_pos k).ne'
  have h11 : M 1 1 = -(ν.visible k : ℂ) := by
    have : (ν.hidden k : ℂ) * ((ν.visible k : ℂ) + M 1 1) = 0 := by linear_combination horth
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hd
    · linear_combination h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

/-! ## Operator form of the decoder and of the fibre involution -/

/-- The row decoder `Q_ν` as a bounded operator `ℓ^∞(ℂ²) → ℓ^∞`. -/
def splitDecoderCLM : LaplaceSplitSpace →L[ℂ] LaplaceResponseSpace :=
  LinearMap.mkContinuous
    { toFun := ν.splitDecoder
      map_add' := fun y z => by
        apply lp.ext; funext k
        change (ν.visible k : ℂ) * ((y k).ofLp 0 + (z k).ofLp 0) +
            (ν.hidden k : ℂ) * ((y k).ofLp 1 + (z k).ofLp 1) =
          ((ν.visible k : ℂ) * (y k).ofLp 0 + (ν.hidden k : ℂ) * (y k).ofLp 1) +
            ((ν.visible k : ℂ) * (z k).ofLp 0 + (ν.hidden k : ℂ) * (z k).ofLp 1)
        ring
      map_smul' := fun c y => by
        apply lp.ext; funext k
        change (ν.visible k : ℂ) * (c * (y k).ofLp 0) + (ν.hidden k : ℂ) * (c * (y k).ofLp 1) =
          c * ((ν.visible k : ℂ) * (y k).ofLp 0 + (ν.hidden k : ℂ) * (y k).ofLp 1)
        ring }
    1 (fun y => by rw [one_mul]; exact ν.norm_splitDecoder_le y)

theorem splitDecoderCLM_apply (y : LaplaceSplitSpace) : ν.splitDecoderCLM y = ν.splitDecoder y :=
  rfl

/-- **(LFD.11)** `‖Q_ν‖ = 1`. -/
theorem norm_splitDecoderCLM : ‖ν.splitDecoderCLM‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  classical
  set b : LaplaceResponseSpace := lp.single ⊤ 0 (1 : ℂ)
  have hb : ‖b‖ = 1 := by rw [lp.norm_single (by simp), norm_one]
  have h := ν.splitDecoderCLM.le_opNorm (ν.splitEncoder b)
  rw [splitDecoderCLM_apply, ν.splitDecoder_splitEncoder, ν.norm_splitEncoder, hb, mul_one] at h
  exact h

/-- The fibre matrix `J_k = [[a_k, d_k], [d_k, -a_k]]` of the sheet involution. -/
def sheetFibreMatrix (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(ν.visible k : ℂ), ν.hidden k; ν.hidden k, -(ν.visible k : ℂ)]

/-- **Theorem 4.1** Each fibre matrix is self-adjoint and squares to the identity, hence is a
self-adjoint unitary. -/
theorem sheetFibreMatrix_selfAdjoint_unitary (k : ℕ) :
    (ν.sheetFibreMatrix k).conjTranspose = ν.sheetFibreMatrix k ∧
      ν.sheetFibreMatrix k * ν.sheetFibreMatrix k = 1 := by
  have hc : ((ν.visible k : ℂ)) ^ 2 + ((ν.hidden k : ℂ)) ^ 2 = 1 := by
    exact_mod_cast ν.visible_sq_add_hidden_sq k
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetFibreMatrix, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  · have e1 : (ν.visible k : ℂ) * ν.visible k + (ν.hidden k : ℂ) * ν.hidden k = 1 := by
      linear_combination hc
    have e2 : (ν.visible k : ℂ) * ν.hidden k + (ν.hidden k : ℂ) * -(ν.visible k : ℂ) = 0 := by ring
    have e3 : (ν.hidden k : ℂ) * ν.visible k + -(ν.visible k : ℂ) * ν.hidden k = 0 := by ring
    have e4 : (ν.hidden k : ℂ) * ν.hidden k + -(ν.visible k : ℂ) * -(ν.visible k : ℂ) = 1 := by
      linear_combination hc
    rw [sheetFibreMatrix, Matrix.mul_fin_two, e1, e2, e3, e4, Matrix.one_fin_two]

end HalfLineFormationLaw

end GaloisForLFunctions.HTGeometry
