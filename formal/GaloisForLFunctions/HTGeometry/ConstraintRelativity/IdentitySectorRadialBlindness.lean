import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.GeneralizedPrimeCountermodel

/-!
# Identity-sector radial gauge blindness

A character of the grading group of a graded algebra acts by an algebra automorphism which is
diagonal on homogeneous components.  Consequently every operation built from products of
homogeneous factors — Hochschild faces, degeneracies, cyclic rotation — preserves the total grade,
and the whole one-parameter family of gauges acts trivially on the total-grade-zero sector.

The last three sections give the exact boundary: a logarithmic grading derivation and its cyclic
one-cocycle are still gauge equivariant; a line spanned by two distinct absolute grades has trivial
stabilizer; but the family of such lines is a single transitive orbit, so trivial stabilizer does
not select a member.
-/

namespace HTGeometry.ConstraintRelativity

open DirectSum

/-! ## The diagonal gauge of a graded algebra -/

section GradedGauge

variable {ι A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommRing A] [Algebra ℂ A]
  (𝒜 : ι → Submodule ℂ A) [GradedAlgebra 𝒜]

/-- The homogeneous component of degree `i`, as a `ℂ`-linear map. -/
noncomputable def gradeComponent (i : ι) : A →ₗ[ℂ] A :=
  ((𝒜 i).subtype).comp
    ((DirectSum.component ℂ ι (fun j => 𝒜 j) i).comp
      (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap)

@[simp]
theorem gradeComponent_of_mem {i : ι} {x : A} (hx : x ∈ 𝒜 i) :
    gradeComponent 𝒜 i x = x := by
  have h1 : gradeComponent 𝒜 i x = ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A) := rfl
  rw [h1, DirectSum.decompose_of_mem_same 𝒜 hx]

theorem gradeComponent_of_mem_ne {i j : ι} (hij : j ≠ i) {x : A} (hx : x ∈ 𝒜 j) :
    gradeComponent 𝒜 i x = 0 := by
  have h1 : gradeComponent 𝒜 i x = ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A) := rfl
  rw [h1, DirectSum.decompose_of_mem_ne 𝒜 hx hij]

/-- The diagonal endomorphism attached to a multiplier `f` on grades. -/
noncomputable def gradeDiag (f : ι → ℂ) : A →ₗ[ℂ] A :=
  (DirectSum.toModule ℂ ι A fun i => f i • (𝒜 i).subtype).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

@[simp]
theorem gradeDiag_of_mem (f : ι → ℂ) {i : ι} {x : A} (hx : x ∈ 𝒜 i) :
    gradeDiag 𝒜 f x = f i • x := by
  simp [gradeDiag, DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem 𝒜 hx,
    ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]

/-- The gauge preserves every homogeneous component. -/
theorem gradeComponent_gradeDiag (f : ι → ℂ) (i : ι) (x : A) :
    gradeComponent 𝒜 i (gradeDiag 𝒜 f x) = f i • gradeComponent 𝒜 i x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous j m =>
    rcases eq_or_ne j i with rfl | hji
    · rw [gradeDiag_of_mem 𝒜 f m.2, map_smul, gradeComponent_of_mem 𝒜 m.2]
    · rw [gradeDiag_of_mem 𝒜 f m.2, map_smul, gradeComponent_of_mem_ne 𝒜 hji m.2]
      simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

/-- **Theorem 1.1.**  A character multiplier gives an algebra endomorphism. -/
theorem gradeDiag_mul {f : ι → ℂ} (hf : ∀ i j, f (i + j) = f i * f j) (x y : A) :
    gradeDiag 𝒜 f (x * y) = gradeDiag 𝒜 f x * gradeDiag 𝒜 f y := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m =>
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j n =>
      rw [gradeDiag_of_mem 𝒜 f (SetLike.mul_mem_graded m.2 n.2), gradeDiag_of_mem 𝒜 f m.2,
        gradeDiag_of_mem 𝒜 f n.2, hf, smul_mul_smul_comm]
    | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]
  | add x z hx hz => rw [add_mul, map_add, map_add, hx, hz, add_mul]

theorem gradeDiag_one {f : ι → ℂ} (hf0 : f 0 = 1) : gradeDiag 𝒜 f 1 = 1 := by
  rw [gradeDiag_of_mem 𝒜 f (SetLike.one_mem_graded 𝒜), hf0, one_smul]

/-- Composition of gauges multiplies their multipliers. -/
theorem gradeDiag_comp (f g : ι → ℂ) (x : A) :
    gradeDiag 𝒜 f (gradeDiag 𝒜 g x) = gradeDiag 𝒜 (fun i => f i * g i) x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m =>
    rw [gradeDiag_of_mem 𝒜 g m.2, map_smul, gradeDiag_of_mem 𝒜 f m.2,
      gradeDiag_of_mem 𝒜 (fun i => f i * g i) m.2, smul_smul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem gradeDiag_one_multiplier (x : A) : gradeDiag 𝒜 (fun _ => (1 : ℂ)) x = x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m => rw [gradeDiag_of_mem 𝒜 _ m.2, one_smul]
  | add x y hx hy => rw [map_add, hx, hy]

/-- The algebra endomorphism attached to a character of the grading group. -/
noncomputable def gradeGaugeHom (f : ι → ℂ) (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j) :
    A →ₐ[ℂ] A where
  toFun := gradeDiag 𝒜 f
  map_one' := gradeDiag_one 𝒜 hf0
  map_mul' := gradeDiag_mul 𝒜 hf
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun r => by
    show gradeDiag 𝒜 f (algebraMap ℂ A r) = algebraMap ℂ A r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, gradeDiag_one 𝒜 hf0]

@[simp]
theorem gradeGaugeHom_apply (f : ι → ℂ) (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j)
    (x : A) : gradeGaugeHom 𝒜 f hf0 hf x = gradeDiag 𝒜 f x := rfl

/-- **Theorem 1.1.**  The gauge attached to a character of the grading group is an algebra
automorphism, with inverse the gauge of the inverse character. -/
noncomputable def gradeGauge (f : ι → ℂ) (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j) :
    A ≃ₐ[ℂ] A :=
  have hf0' : f (-0 : ι) = 1 := by simpa using hf0
  have hf' : ∀ i j : ι, f (-(i + j)) = f (-i) * f (-j) := fun i j => by rw [neg_add, hf]
  have hmul : (fun i : ι => f i * f (-i)) = fun _ : ι => (1 : ℂ) :=
    funext fun i => by rw [← hf, add_neg_cancel, hf0]
  have hmul' : (fun i : ι => f (-i) * f i) = fun _ : ι => (1 : ℂ) :=
    funext fun i => by rw [← hf, neg_add_cancel, hf0]
  AlgEquiv.ofAlgHom (gradeGaugeHom 𝒜 f hf0 hf) (gradeGaugeHom 𝒜 (fun i => f (-i)) hf0' hf')
    (by
      ext x
      simp only [AlgHom.coe_comp, Function.comp_apply, gradeGaugeHom_apply, AlgHom.coe_id, id_eq]
      rw [gradeDiag_comp, hmul, gradeDiag_one_multiplier])
    (by
      ext x
      simp only [AlgHom.coe_comp, Function.comp_apply, gradeGaugeHom_apply, AlgHom.coe_id, id_eq]
      rw [gradeDiag_comp, hmul', gradeDiag_one_multiplier])

@[simp]
theorem gradeGauge_apply (f : ι → ℂ) (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j) (x : A) :
    gradeGauge 𝒜 f hf0 hf x = gradeDiag 𝒜 f x := rfl

end GradedGauge

/-! ## Total grade of a cyclic chain -/

section TotalGrade

variable {ι : Type*} [AddCommGroup ι]

/-- The total grade of a homogeneous cyclic chain. -/
def totalGrade (l : List ι) : ι := l.sum

/-- **Theorem 1.3.**  A Hochschild face multiplies two adjacent factors and preserves the total
grade. -/
theorem totalGrade_face (l₁ l₂ : List ι) (a b : ι) :
    totalGrade (l₁ ++ (a + b) :: l₂) = totalGrade (l₁ ++ a :: b :: l₂) := by
  simp [totalGrade, List.sum_append, add_assoc]

/-- **Theorem 1.3.**  The last face wraps around; it preserves the total grade because the grading
group is abelian. -/
theorem totalGrade_lastFace (a b : ι) (l : List ι) :
    totalGrade ((b + a) :: l) = totalGrade (a :: (l ++ [b])) := by
  show (b + a) + l.sum = a + (l ++ [b]).sum
  rw [List.sum_append, List.sum_singleton]
  abel

/-- **Theorem 1.3.**  A degeneracy inserts the unit, of grade zero. -/
theorem totalGrade_degeneracy (l₁ l₂ : List ι) :
    totalGrade (l₁ ++ (0 : ι) :: l₂) = totalGrade (l₁ ++ l₂) := by
  simp [totalGrade, List.sum_append]

/-- **Theorem 1.3.**  Cyclic rotation preserves the total grade. -/
theorem totalGrade_rotate (l : List ι) (n : ℕ) : totalGrade (l.rotate n) = totalGrade l :=
  (l.rotate_perm n).sum_eq

/-- **Theorem 1.2.**  On a homogeneous chain the gauge acts by the character of the total grade. -/
theorem prod_multiplier_eq {f : ι → ℂ} (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j)
    (l : List ι) : (l.map f).prod = f (totalGrade l) := by
  induction l with
  | nil => simpa [totalGrade] using hf0.symm
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, totalGrade, List.sum_cons, hf]

/-- **Theorem 1.4.**  The total-grade-zero cyclic sector is pointwise fixed by the whole gauge
family. -/
theorem prod_multiplier_eq_one {f : ι → ℂ} (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j)
    {l : List ι} (hl : totalGrade l = 0) : (l.map f).prod = 1 := by
  rw [prod_multiplier_eq hf0 hf, hl, hf0]

/-- **Corollary 2, equation (10).**  A prime/inverse-prime atom has total grade zero, so every
gauge fixes it. -/
theorem prod_multiplier_primeAtom {f : ι → ℂ} (hf0 : f 0 = 1) (hf : ∀ i j, f (i + j) = f i * f j)
    (i : ι) : ([i, -i].map f).prod = 1 :=
  prod_multiplier_eq_one hf0 hf (by simp [totalGrade])

end TotalGrade

/-! ## The logarithmic grading derivation stays equivariant -/

section LogDerivation

variable {ι A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommRing A] [Algebra ℂ A]
  (𝒜 : ι → Submodule ℂ A) [GradedAlgebra 𝒜]

/-- **Theorem 3, equation (11).**  An additive multiplier gives a derivation. -/
theorem gradeDiag_leibniz {L : ι → ℂ} (hL : ∀ i j, L (i + j) = L i + L j) (x y : A) :
    gradeDiag 𝒜 L (x * y) = gradeDiag 𝒜 L x * y + x * gradeDiag 𝒜 L y := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m =>
    induction y using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j n =>
      rw [gradeDiag_of_mem 𝒜 L (SetLike.mul_mem_graded m.2 n.2), gradeDiag_of_mem 𝒜 L m.2,
        gradeDiag_of_mem 𝒜 L n.2, hL, smul_mul_assoc, mul_smul_comm, add_smul]
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]; ring
  | add x z hx hz => rw [add_mul, map_add, hx, hz, map_add, add_mul]; ring

/-- **Theorem 3, equation (12) first half.**  The logarithmic derivation commutes with every
gauge: both act diagonally. -/
theorem gradeDiag_commute (f L : ι → ℂ) (x : A) :
    gradeDiag 𝒜 L (gradeDiag 𝒜 f x) = gradeDiag 𝒜 f (gradeDiag 𝒜 L x) := by
  rw [gradeDiag_comp, gradeDiag_comp]
  simp only [mul_comm]

/-- The identity-coefficient trace. -/
noncomputable def identityTrace : A →ₗ[ℂ] A := gradeComponent 𝒜 0

/-- The trace is gauge invariant, because a character takes the value one at the identity grade. -/
theorem identityTrace_gradeDiag {f : ι → ℂ} (hf0 : f 0 = 1) (x : A) :
    identityTrace 𝒜 (gradeDiag 𝒜 f x) = identityTrace 𝒜 x := by
  rw [identityTrace, gradeComponent_gradeDiag, hf0, one_smul]

/-- The Kummer one-cocycle `φ_L(a,b) = τ(a · ∂_L b)`. -/
noncomputable def kummerCocycle (L : ι → ℂ) (x y : A) : A :=
  identityTrace 𝒜 (x * gradeDiag 𝒜 L y)

/-- **Theorem 3, equation (12) second half.**  The Kummer cocycle is invariant under the whole
radial gauge family, so it cannot detect the gauge parameter. -/
theorem kummerCocycle_gradeDiag {f L : ι → ℂ} (hf0 : f 0 = 1)
    (hf : ∀ i j, f (i + j) = f i * f j) (x y : A) :
    kummerCocycle 𝒜 L (gradeDiag 𝒜 f x) (gradeDiag 𝒜 f y) = kummerCocycle 𝒜 L x y := by
  rw [kummerCocycle, gradeDiag_commute, ← gradeDiag_mul 𝒜 hf, identityTrace_gradeDiag 𝒜 hf0,
    kummerCocycle]

end LogDerivation

/-! ## Cross-grade lines: trivial stabilizer, single radial orbit -/

section RadialMultiplier

variable {ι : Type*} [AddCommGroup ι]

/-- The radial multiplier of drift `c` attached to a positive absolute grade `ν`. -/
noncomputable def radialMultiplier (ν : ι → ℝ) (c : ℝ) (i : ι) : ℂ := ((ν i ^ c : ℝ) : ℂ)

theorem radialMultiplier_zero {ν : ι → ℝ} (hν0 : ν 0 = 1) (c : ℝ) :
    radialMultiplier ν c 0 = 1 := by
  simp [radialMultiplier, hν0]

theorem radialMultiplier_add {ν : ι → ℝ} (hνpos : ∀ i, 0 < ν i)
    (hν : ∀ i j, ν (i + j) = ν i * ν j) (c : ℝ) (i j : ι) :
    radialMultiplier ν c (i + j) = radialMultiplier ν c i * radialMultiplier ν c j := by
  simp only [radialMultiplier, hν]
  rw [Real.mul_rpow (hνpos i).le (hνpos j).le]
  push_cast
  ring

/-- Two distinct positive grades have equal radial multiplier only at zero drift. -/
theorem rpow_eq_rpow_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    a ^ c = b ^ c ↔ c = 0 := by
  constructor
  · intro h
    have hlog : c * Real.log a = c * Real.log b := by
      rw [← Real.log_rpow ha, ← Real.log_rpow hb, h]
    have hne : Real.log a ≠ Real.log b := fun hcon =>
      hab (Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 hb) hcon)
    by_contra hc
    exact hne (mul_left_cancel₀ hc hlog)
  · rintro rfl
    simp

/-- **Theorem 5.**  The radial family acts transitively on the positive cross-grade parameters, so
no member of the family is selected. -/
theorem radial_parameter_transitive {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {lam mu : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) : ∃ c : ℝ, lam * r ^ c = mu := by
  have hlogne : Real.log r ≠ 0 := by
    intro hcon
    exact hr1 (Real.eq_one_of_pos_of_log_eq_zero hr hcon)
  refine ⟨Real.log (mu / lam) / Real.log r, ?_⟩
  have hcancel : Real.log r * (Real.log (mu / lam) / Real.log r) = Real.log (mu / lam) := by
    field_simp
  rw [Real.rpow_def_of_pos hr, hcancel, Real.exp_log (div_pos hmu hlam)]
  field_simp

end RadialMultiplier

section CrossGrade

variable {ι A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommRing A] [Algebra ℂ A]
  (𝒜 : ι → Submodule ℂ A) [GradedAlgebra 𝒜]

/-- **Theorem 4.**  A line spanned by a vector with two distinct absolute grades is gauge invariant
only at zero drift. -/
theorem radial_line_invariant_iff {ν : ι → ℝ} (hνpos : ∀ i, 0 < ν i) {i j : ι} (hij : ν i ≠ ν j)
    {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (c : ℝ) :
    (∃ lam : ℂ, gradeDiag 𝒜 (radialMultiplier ν c) (x + y) = lam • (x + y)) ↔ c = 0 := by
  have hne : j ≠ i := fun h => hij (by rw [h])
  constructor
  · rintro ⟨lam, hlam⟩
    rw [map_add, gradeDiag_of_mem 𝒜 _ hx, gradeDiag_of_mem 𝒜 _ hy, smul_add] at hlam
    have hi : radialMultiplier ν c i • x = lam • x := by
      have := congrArg (gradeComponent 𝒜 i) hlam
      simpa [gradeComponent_of_mem 𝒜 hx, gradeComponent_of_mem_ne 𝒜 hne hy] using this
    have hj : radialMultiplier ν c j • y = lam • y := by
      have := congrArg (gradeComponent 𝒜 j) hlam
      simpa [gradeComponent_of_mem 𝒜 hy,
        gradeComponent_of_mem_ne 𝒜 (fun h => hij (by rw [h])) hx] using this
    have hxi : radialMultiplier ν c i = lam := by
      by_contra hcon
      exact hx0 (by
        have : (radialMultiplier ν c i - lam) • x = 0 := by rw [sub_smul, hi, sub_self]
        exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hcon))
    have hyj : radialMultiplier ν c j = lam := by
      by_contra hcon
      exact hy0 (by
        have : (radialMultiplier ν c j - lam) • y = 0 := by rw [sub_smul, hj, sub_self]
        exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hcon))
    have : ν i ^ c = ν j ^ c := by
      have h := hxi.trans hyj.symm
      simpa [radialMultiplier, Complex.ofReal_inj] using h
    exact (rpow_eq_rpow_iff (hνpos i) (hνpos j) hij).1 this
  · rintro rfl
    exact ⟨1, by
      rw [map_add, gradeDiag_of_mem 𝒜 _ hx, gradeDiag_of_mem 𝒜 _ hy]
      simp [radialMultiplier]⟩

/-- **Theorem 5, equation (15).**  The gauge moves the cross-grade line of parameter `λ` to the
line of parameter `λ (ν j / ν i)^c`. -/
theorem radial_line_transport {ν : ι → ℝ} (hνpos : ∀ i, 0 < ν i) {i j : ι}
    {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) (lam : ℂ) (c : ℝ) :
    gradeDiag 𝒜 (radialMultiplier ν c) (x + lam • y)
      = ((ν i ^ c : ℝ) : ℂ) • (x + (lam * (((ν j / ν i) ^ c : ℝ) : ℂ)) • y) := by
  rw [map_add, gradeDiag_of_mem 𝒜 _ hx, map_smul, gradeDiag_of_mem 𝒜 _ hy]
  rw [Real.div_rpow (hνpos j).le (hνpos i).le]
  have hi : ((ν i ^ c : ℝ) : ℂ) ≠ 0 := by
    simpa using (Real.rpow_pos_of_pos (hνpos i) c).ne'
  simp only [radialMultiplier, smul_add, smul_smul, Complex.ofReal_div]
  congr 1
  field_simp

end CrossGrade

/-! ## The reciprocal and adelic countermodels -/

section Countermodel

open Matrix

/-- **Equation (17).**  The reciprocal two-leg transport preserves the indefinite Stokes form at
every drift; this is `legTransport_stokes`. -/
theorem reciprocal_stokes_blind (P c : ℝ) (hP : 0 < P) :
    (legTransport P c)ᵀ * stokesForm * legTransport P c = stokesForm :=
  legTransport_stokes P c hP

/-- **Equation (18).**  The adelic product formula is blind to the radial parameter: the product of
all absolute values raised to any real power is one. -/
theorem adelic_product_blind {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {x : K}
    (hx : x ≠ 0) (c : ℝ) :
    (((Height.AdmissibleAbsValues.archAbsVal (K := K)).map (fun v => v x)).prod
      * ∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), v.val x) ^ c = 1 := by
  rw [Height.AdmissibleAbsValues.product_formula hx, Real.one_rpow]

end Countermodel

end HTGeometry.ConstraintRelativity
