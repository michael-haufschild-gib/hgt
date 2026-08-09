import Mathlib
import GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt

/-!
# The constitutive soldering intertwiner-energy law

For two unitary representations of a finite group on the same space, a constitutive soldering is a
unitary comparison `s`, and its transport defect `Q_s(g) = ρ_T(g) s − s ρ_K(g)` obeys the cocycle
rule `Q_s(gh) = ρ_T(g) Q_s(h) + Q_s(g) ρ_K(h)`.

The averaged Hilbert–Schmidt curvature energy is exactly the norm defect of the Reynolds
intertwiner projection,

`E(s) = ‖s‖² − ‖Π(s)‖²`,

so `E(s) = 0` exactly when `s` intertwines the two representations.  A minimal nonflat source
history is `G = C₂` acting by `+1` and `−1` on `ℂ`, where every soldering has energy `1`.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix QuantumAlg

section Energy

variable {m : Type*} [Fintype m]

/-! ## Hilbert–Schmidt energy -/

/-- The Hilbert–Schmidt squared norm. -/
noncomputable def hsNormSq (A : Matrix m m ℂ) : ℝ := (hsInner A A).re

theorem hsNormSq_nonneg (A : Matrix m m ℂ) : 0 ≤ hsNormSq A :=
  hsInner_self_re_nonneg A

theorem hsNormSq_sub (A B : Matrix m m ℂ) :
    hsNormSq (A - B) = hsNormSq A + hsNormSq B - 2 * (hsInner A B).re := by
  have hexp : hsInner (A - B) (A - B)
      = hsInner A A - hsInner A B - (hsInner B A - hsInner B B) := by
    rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right]
  have hconj : (hsInner B A).re = (hsInner A B).re := by
    rw [hsInner_conj_symm]
    simp
  simp only [hsNormSq, hexp, Complex.sub_re]
  rw [hconj]
  ring

theorem hsNormSq_eq_sum (A : Matrix m m ℂ) :
    hsNormSq A = ∑ i, ∑ k, Complex.normSq (A k i) := by
  simp only [hsNormSq, hsInner_def, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, RCLike.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem hsNormSq_eq_zero_iff (A : Matrix m m ℂ) : hsNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [hsNormSq_eq_sum] at h
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)).1 h j
      (Finset.mem_univ j)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg _)).1 h1 i (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.1 h2
  · rintro rfl
    simp [hsNormSq, hsInner_def]

end Energy

section Unitary

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ## Unitary invariance -/

theorem hsInner_left_unitary {U : Matrix m m ℂ} (hU : Uᴴ * U = 1) (A B : Matrix m m ℂ) :
    hsInner (U * A) (U * B) = hsInner A B := by
  simp only [hsInner_def, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U B, hU, Matrix.one_mul]

theorem hsInner_right_unitary {V : Matrix m m ℂ} (hV : Vᴴ * V = 1) (A B : Matrix m m ℂ) :
    hsInner (A * V) (B * V) = hsInner A B := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  simp only [hsInner_def, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hV',
    Matrix.mul_one]

theorem hsNormSq_right_unitary {V : Matrix m m ℂ} (hV : Vᴴ * V = 1) (A : Matrix m m ℂ) :
    hsNormSq (A * V) = hsNormSq A := by
  simp only [hsNormSq, hsInner_right_unitary hV]

/-! ## The transport defect and its cocycle -/

/-- The transport defect of a constitutive soldering. -/
def solderDefect (rK rT : Matrix m m ℂ) (s : Matrix m m ℂ) : Matrix m m ℂ :=
  rT * s - s * rK

/-- **Card `(4)`.**  The transport defect is a cocycle for the two representations. -/
theorem solderDefect_mul (rK rT rK' rT' s : Matrix m m ℂ) :
    solderDefect (rK * rK') (rT * rT') s
      = rT * solderDefect rK' rT' s + solderDefect rK rT s * rK' := by
  simp only [solderDefect]
  noncomm_ring

/-! ## The Reynolds projection and the curvature energy -/

variable {G : Type*} [Group G] [Fintype G]

/-- The unitary conjugation action on solderings. -/
def solderAction (rK rT : G → Matrix m m ℂ) (g : G) (s : Matrix m m ℂ) : Matrix m m ℂ :=
  rT g * s * (rK g)ᴴ

/-- **Card `(5)`.**  The Reynolds intertwiner projection. -/
noncomputable def reynoldsProj (rK rT : G → Matrix m m ℂ) (s : Matrix m m ℂ) : Matrix m m ℂ :=
  ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, solderAction rK rT g s

/-- **Card `(6)`, left side.**  The constitutive curvature energy. -/
noncomputable def curvatureEnergy (rK rT : G → Matrix m m ℂ) (s : Matrix m m ℂ) : ℝ :=
  (2 * (Fintype.card G : ℝ))⁻¹ * ∑ g : G, hsNormSq (solderDefect (rK g) (rT g) s)

variable (rK rT : G → Matrix m m ℂ)
  (hK : ∀ g, (rK g)ᴴ * rK g = 1) (hT : ∀ g, (rT g)ᴴ * rT g = 1)
  (hKmul : ∀ g h : G, rK (g * h) = rK g * rK h) (hTmul : ∀ g h : G, rT (g * h) = rT g * rT h)

omit [Group G] [Fintype G] in
include hK in
/-- The transport defect is the displacement of the conjugation action, right-translated by a
unitary. -/
theorem solderDefect_eq_solderAction (g : G) (s : Matrix m m ℂ) :
    solderDefect (rK g) (rT g) s = (solderAction rK rT g s - s) * rK g := by
  have hK' : (rK g)ᴴ * rK g = 1 := hK g
  simp only [solderDefect, solderAction, Matrix.sub_mul, Matrix.mul_assoc, hK', Matrix.mul_one]

omit [Group G] [Fintype G] in
include hK in
theorem hsNormSq_solderDefect (g : G) (s : Matrix m m ℂ) :
    hsNormSq (solderDefect (rK g) (rT g) s) = hsNormSq (solderAction rK rT g s - s) := by
  rw [solderDefect_eq_solderAction rK rT hK g s, hsNormSq_right_unitary (hK g)]

omit [Group G] [Fintype G] in
include hK hT in
theorem hsInner_solderAction (g : G) (A B : Matrix m m ℂ) :
    hsInner (solderAction rK rT g A) (solderAction rK rT g B) = hsInner A B := by
  have hKH : ((rK g)ᴴ)ᴴ * (rK g)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 (hK g)
  simp only [solderAction]
  rw [hsInner_right_unitary hKH, hsInner_left_unitary (hT g)]

omit [Group G] [Fintype G] in
include hK hT in
theorem hsNormSq_solderAction (g : G) (A : Matrix m m ℂ) :
    hsNormSq (solderAction rK rT g A) = hsNormSq A := by
  simp only [hsNormSq, hsInner_solderAction rK rT hK hT]

omit [DecidableEq m] in
include hKmul hTmul in
/-- The Reynolds projection is fixed by the action. -/
theorem solderAction_reynoldsProj (h : G) (s : Matrix m m ℂ) :
    solderAction rK rT h (reynoldsProj rK rT s) = reynoldsProj rK rT s := by
  simp only [solderAction, reynoldsProj, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  have hstep : ∀ g : G, rT h * (rT g * s * (rK g)ᴴ) * (rK h)ᴴ
      = rT (h * g) * s * (rK (h * g))ᴴ := by
    intro g
    rw [hTmul, hKmul, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [Finset.sum_congr rfl fun g _ => hstep g]
  exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ fun g => rfl

/-! ## The curvature energy identity -/

include hK hT hKmul hTmul in
/-- **Card `(6)`.**  The constitutive curvature energy is the Hilbert–Schmidt norm defect of the
Reynolds intertwiner projection. -/
theorem curvatureEnergy_eq (s : Matrix m m ℂ) :
    curvatureEnergy rK rT s = hsNormSq s - hsNormSq (reynoldsProj rK rT s) := by
  have hcardR : (Fintype.card G : ℝ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hcardC : (Fintype.card G : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hreal : ∀ z : ℂ, (((Fintype.card G : ℂ))⁻¹ * z).re = ((Fintype.card G : ℝ))⁻¹ * z.re := by
    intro z
    have hc : ((Fintype.card G : ℂ))⁻¹ = ((((Fintype.card G : ℝ))⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hc]
    simp [Complex.mul_re]
  have hterm : ∀ g : G, hsNormSq (solderDefect (rK g) (rT g) s)
      = 2 * hsNormSq s - 2 * (hsInner (solderAction rK rT g s) s).re := by
    intro g
    rw [hsNormSq_solderDefect rK rT hK g s, hsNormSq_sub,
      hsNormSq_solderAction rK rT hK hT g s]
    ring
  have hinnerProj : hsInner (reynoldsProj rK rT s) s
      = ((Fintype.card G : ℂ))⁻¹ * ∑ g : G, hsInner (solderAction rK rT g s) s := by
    rw [reynoldsProj, hsInner_smul_left, hsInner_sum_left]
    simp
  have hsumre : ∑ g : G, (hsInner (solderAction rK rT g s) s).re
      = (Fintype.card G : ℝ) * (hsInner (reynoldsProj rK rT s) s).re := by
    rw [hinnerProj, hreal, Complex.re_sum]
    field_simp
  have hprojNorm : hsNormSq (reynoldsProj rK rT s) = (hsInner (reynoldsProj rK rT s) s).re := by
    have hfix : ∀ g : G, hsInner (reynoldsProj rK rT s) (solderAction rK rT g s)
        = hsInner (reynoldsProj rK rT s) s := by
      intro g
      conv_lhs => rw [← solderAction_reynoldsProj rK rT hKmul hTmul g s]
      exact hsInner_solderAction rK rT hK hT g _ _
    have hself : hsInner (reynoldsProj rK rT s) (reynoldsProj rK rT s)
        = hsInner (reynoldsProj rK rT s) s := by
      nth_rewrite 2 [reynoldsProj]
      rw [hsInner_smul_right, hsInner_sum_right,
        Finset.sum_congr rfl fun g _ => hfix g, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcardC, one_mul]
    simp only [hsNormSq, hself]
  rw [curvatureEnergy, Finset.sum_congr rfl fun g _ => hterm g, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hsumre, hprojNorm]
  field_simp

omit hK hT in
/-- **Card, items 1–3.**  The curvature energy vanishes exactly when the soldering intertwines the
two representations. -/
theorem curvatureEnergy_eq_zero_iff (s : Matrix m m ℂ) :
    curvatureEnergy rK rT s = 0 ↔ ∀ g : G, rT g * s = s * rK g := by
  have hcardR : (0 : ℝ) < 2 * (Fintype.card G : ℝ) := by
    have hpos : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  constructor
  · intro hz g
    have hsum : ∑ g : G, hsNormSq (solderDefect (rK g) (rT g) s) = 0 := by
      rw [curvatureEnergy] at hz
      field_simp at hz
      simpa using hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _ => hsNormSq_nonneg _)).1 hsum g (Finset.mem_univ g)
    have hzero : solderDefect (rK g) (rT g) s = 0 := (hsNormSq_eq_zero_iff _).1 hall
    rw [solderDefect, sub_eq_zero] at hzero
    exact hzero
  · intro hint
    have hsum : ∑ g : G, hsNormSq (solderDefect (rK g) (rT g) s) = 0 := by
      refine Finset.sum_eq_zero fun g _ => ?_
      have hzero : solderDefect (rK g) (rT g) s = 0 := by
        rw [solderDefect, sub_eq_zero]
        exact hint g
      rw [hzero]
      simp [hsNormSq, hsInner_def]
    rw [curvatureEnergy, hsum, mul_zero]

omit hK hT in
/-- **Card, items 1–2.**  Some constitutive soldering is flat exactly when some unitary
intertwines the two representations. -/
theorem exists_unitary_curvatureEnergy_eq_zero_iff :
    (∃ s : Matrix m m ℂ, sᴴ * s = 1 ∧ curvatureEnergy rK rT s = 0)
      ↔ (∃ s : Matrix m m ℂ, sᴴ * s = 1 ∧ ∀ g : G, rT g * s = s * rK g) := by
  constructor
  · rintro ⟨s, hs, hE⟩
    exact ⟨s, hs, (curvatureEnergy_eq_zero_iff rK rT s).1 hE⟩
  · rintro ⟨s, hs, hint⟩
    exact ⟨s, hs, (curvatureEnergy_eq_zero_iff rK rT s).2 hint⟩

/-! ## The positive curvature gap -/

/-- The set of constitutive solderings. -/
def solderingSet (m : Type*) [Fintype m] [DecidableEq m] : Set (Matrix m m ℂ) :=
  {s : Matrix m m ℂ | sᴴ * s = 1}

omit hK hT hKmul hTmul in
theorem isClosed_solderingSet : IsClosed (solderingSet m) := by
  have hcont : Continuous fun s : Matrix m m ℂ => sᴴ * s := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact continuous_finsetSum _ fun k _ =>
      (Complex.continuous_conj.comp ((continuous_apply i).comp (continuous_apply k))).mul
        ((continuous_apply j).comp (continuous_apply k))
  exact isClosed_eq hcont continuous_const

omit hK hT hKmul hTmul in
theorem norm_le_one_of_mem_solderingSet {s : Matrix m m ℂ} (hs : s ∈ solderingSet m) (i j : m) :
    ‖s i j‖ ≤ 1 := by
  have hcol : ∑ k, Complex.normSq (s k j) = 1 := by
    have h1 : (sᴴ * s) j j = 1 := by
      have := congrFun (congrFun hs j) j
      simpa [Matrix.one_apply] using this
    have h2 : (sᴴ * s) j j = ∑ k, Complex.normSq (s k j) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
        ← Complex.normSq_eq_conj_mul_self]
      push_cast
      rfl
    rw [h2] at h1
    exact_mod_cast h1
  have hle : Complex.normSq (s i j) ≤ 1 := by
    rw [← hcol]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (s k j))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hsq : ‖s i j‖ ^ 2 ≤ 1 := by
    have hz : Complex.normSq (s i j) = ‖s i j‖ ^ 2 := by
      simpa using (RCLike.normSq_eq_def' (K := ℂ) (s i j))
    rw [← hz]
    exact hle
  nlinarith [norm_nonneg (s i j)]

omit hK hT hKmul hTmul in
theorem isCompact_solderingSet : IsCompact (solderingSet m) := by
  have hcpt : IsCompact (Set.univ.pi fun _ : m => Set.univ.pi fun _ : m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1
  refine hcpt.of_isClosed_subset isClosed_solderingSet ?_
  intro s hs
  refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
  simpa [Metric.mem_closedBall, dist_zero_right] using
    norm_le_one_of_mem_solderingSet hs i j

omit [DecidableEq m] [Group G] hK hT hKmul hTmul in
theorem continuous_curvatureEnergy : Continuous (curvatureEnergy rK rT) := by
  refine continuous_const.mul (continuous_finsetSum _ fun g _ => ?_)
  simp only [hsNormSq, hsInner_def, solderDefect]
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_trace ?_
  refine Continuous.matrix_mul ?_ ?_
  · refine Continuous.matrix_conjTranspose ?_
    exact ((continuous_const.matrix_mul continuous_id).sub
      (continuous_id.matrix_mul continuous_const))
  · exact ((continuous_const.matrix_mul continuous_id).sub
      (continuous_id.matrix_mul continuous_const))

omit hK hT in
/-- **Card `(7)`.**  If no constitutive soldering is flat, the curvature energy has a positive
minimum on the compact soldering set. -/
theorem exists_positive_gap (hne : (solderingSet m).Nonempty)
    (hno : ∀ s : Matrix m m ℂ, sᴴ * s = 1 → ¬ ∀ g : G, rT g * s = s * rK g) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ s ∈ solderingSet m, eps ≤ curvatureEnergy rK rT s := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_solderingSet.exists_isMinOn hne
    (continuous_curvatureEnergy rK rT).continuousOn
  refine ⟨curvatureEnergy rK rT s₀, ?_, fun s hs => hmin hs⟩
  have hpos : 0 ≤ curvatureEnergy rK rT s₀ := by
    rw [curvatureEnergy]
    have hcard : (0 : ℝ) ≤ (2 * (Fintype.card G : ℝ))⁻¹ := by positivity
    exact mul_nonneg hcard (Finset.sum_nonneg fun g _ => hsNormSq_nonneg _)
  rcases lt_or_eq_of_le hpos with h | h
  · exact h
  · exact absurd ((curvatureEnergy_eq_zero_iff rK rT s₀).1 h.symm) (hno s₀ hs₀)

omit hK hT hKmul hTmul in
/-- A constitutive soldering has Hilbert–Schmidt energy equal to the dimension. -/
theorem hsNormSq_of_unitary {s : Matrix m m ℂ} (hs : sᴴ * s = 1) :
    hsNormSq s = (Fintype.card m : ℝ) := by
  simp [hsNormSq, hsInner_def, hs, Matrix.trace_one]

end Unitary

/-! ## The minimal nonflat source history -/

section MinimalExample

/-- The two-element source-history group. -/
abbrev C2 : Type := Multiplicative (ZMod 2)

/-- The nontrivial element of `C₂`. -/
def c2Gen : C2 := Multiplicative.ofAdd 1

theorem c2_cases (g : C2) : g = 1 ∨ g = c2Gen := by
  revert g
  decide

theorem c2Gen_ne_one : c2Gen ≠ 1 := by decide

theorem c2Gen_mul_self : c2Gen * c2Gen = 1 := by decide

theorem c2_univ : (Finset.univ : Finset C2) = {1, c2Gen} := by decide

/-- The trivial representation of `C₂`. -/
def c2Trivial : C2 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1

/-- The sign representation of `C₂`. -/
noncomputable def c2Sign : C2 → Matrix (Fin 1) (Fin 1) ℂ := fun g => if g = 1 then 1 else -1

@[simp] theorem c2Sign_one : c2Sign 1 = 1 := by simp [c2Sign]

@[simp] theorem c2Sign_gen : c2Sign c2Gen = -1 := by simp [c2Sign, c2Gen_ne_one]

theorem c2Trivial_unitary (g : C2) : (c2Trivial g)ᴴ * c2Trivial g = 1 := by
  simp [c2Trivial]

theorem c2Sign_unitary (g : C2) : (c2Sign g)ᴴ * c2Sign g = 1 := by
  rcases c2_cases g with rfl | rfl <;> simp

theorem c2Trivial_mul (g h : C2) : c2Trivial (g * h) = c2Trivial g * c2Trivial h := by
  simp [c2Trivial]

theorem c2Sign_mul (g h : C2) : c2Sign (g * h) = c2Sign g * c2Sign h := by
  rcases c2_cases g with rfl | rfl <;> rcases c2_cases h with rfl | rfl <;>
    simp [c2Gen_mul_self]

/-- **Card `(8)`.**  The Reynolds projection of the minimal nonflat history is zero. -/
theorem c2_reynoldsProj (s : Matrix (Fin 1) (Fin 1) ℂ) :
    reynoldsProj c2Trivial c2Sign s = 0 := by
  have hcard : (Fintype.card C2 : ℂ) = 2 := by simp
  simp only [reynoldsProj, solderAction, c2_univ, hcard]
  rw [Finset.sum_insert (by simp [Ne.symm c2Gen_ne_one]), Finset.sum_singleton]
  simp [c2Trivial]

/-- **Card `(8)`.**  Every constitutive soldering of the minimal nonflat history has curvature
energy `1`. -/
theorem c2_curvatureEnergy (s : Matrix (Fin 1) (Fin 1) ℂ) (hs : sᴴ * s = 1) :
    curvatureEnergy c2Trivial c2Sign s = 1 := by
  rw [curvatureEnergy_eq c2Trivial c2Sign c2Trivial_unitary c2Sign_unitary c2Trivial_mul
    c2Sign_mul s, c2_reynoldsProj, hsNormSq_of_unitary hs]
  simp [hsNormSq, hsInner_def]

/-- The minimal nonflat history has no flat soldering at all. -/
theorem c2_no_flat_soldering (s : Matrix (Fin 1) (Fin 1) ℂ) (hs : sᴴ * s = 1) :
    curvatureEnergy c2Trivial c2Sign s ≠ 0 := by
  rw [c2_curvatureEnergy s hs]
  norm_num

end MinimalExample

end HTGeometry.ConstraintRelativity
