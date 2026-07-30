import GaloisForLFunctions.HTGeometry.FiniteBlaschkeBoundary
import GaloisForLFunctions.HTGeometry.AnalyticSquareRoot
import Mathlib.Algebra.Polynomial.Splits

open Complex Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Roots of `p` strictly inside the unit disk, with multiplicity. -/
def polynomialInsideRoots (p : ℂ[X]) : Multiset ℂ :=
  p.roots.filter (fun a => ‖a‖ < 1)

/-- Roots of `p` outside the open unit disk, with multiplicity. -/
def polynomialOutsideRoots (p : ℂ[X]) : Multiset ℂ :=
  p.roots.filter (fun a => ¬ ‖a‖ < 1)

/-- The finite Blaschke product contributed by the roots of `p` in the open unit disk. -/
def polynomialBlaschke (p : ℂ[X]) (z : ℂ) : ℂ :=
  ((polynomialInsideRoots p).map fun a => (z - a) / (1 - star a * z)).prod

/-- The zero-free polynomial factor obtained by reflecting every open-disk root of `p`. -/
def polynomialOuterization (p : ℂ[X]) (z : ℂ) : ℂ :=
  p.leadingCoeff *
    ((polynomialInsideRoots p).map fun a => 1 - star a * z).prod *
    ((polynomialOutsideRoots p).map fun a => z - a).prod

lemma polynomialInsideRoots_add_outsideRoots (p : ℂ[X]) :
    polynomialInsideRoots p + polynomialOutsideRoots p = p.roots := by
  exact Multiset.filter_add_not (fun a : ℂ => ‖a‖ < 1) p.roots

lemma polynomialBlaschke_mul_outerization (p : ℂ[X])
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polynomialBlaschke p z * polynomialOuterization p z = p.eval z := by
  let I := polynomialInsideRoots p
  let O := polynomialOutsideRoots p
  have hpair :
      (I.map fun a => ((z - a) / (1 - star a * z)) * (1 - star a * z)).prod =
        (I.map fun a => z - a).prod := by
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro a ha
    have haI : ‖a‖ < 1 := (Multiset.mem_filter.mp ha).2
    exact div_mul_cancel₀ (z - a) (blaschkeFactor_den_ne_zero haI hz)
  have hprod :
      (I.map fun a => (z - a) / (1 - star a * z)).prod *
          (I.map fun a => 1 - star a * z).prod =
        (I.map fun a => z - a).prod := by
    rw [← Multiset.prod_map_mul]
    exact hpair
  have hroots : p.eval z = p.leadingCoeff * (p.roots.map fun a => z - a).prod :=
    (IsAlgClosed.splits p).eval_eq_prod_roots z
  rw [polynomialBlaschke, polynomialOuterization]
  change (I.map fun a => (z - a) / (1 - star a * z)).prod *
      (p.leadingCoeff * (I.map fun a => 1 - star a * z).prod *
        (O.map fun a => z - a).prod) = p.eval z
  rw [hroots]
  rw [← polynomialInsideRoots_add_outsideRoots p]
  simp only [Multiset.map_add, Multiset.prod_add]
  calc
    (I.map fun a => (z - a) / (1 - star a * z)).prod *
        (p.leadingCoeff * (I.map fun a => 1 - star a * z).prod *
          (O.map fun a => z - a).prod) =
      p.leadingCoeff *
        ((I.map fun a => (z - a) / (1 - star a * z)).prod *
          (I.map fun a => 1 - star a * z).prod) *
        (O.map fun a => z - a).prod := by ring
    _ = p.leadingCoeff * (I.map fun a => z - a).prod *
        (O.map fun a => z - a).prod := by rw [hprod]
    _ = p.leadingCoeff *
        ((polynomialInsideRoots p).map fun a => z - a).prod *
        ((polynomialOutsideRoots p).map fun a => z - a).prod := by rfl
    _ = p.leadingCoeff *
        (((polynomialInsideRoots p).map fun a => z - a).prod *
          ((polynomialOutsideRoots p).map fun a => z - a).prod) := by ring

private lemma norm_multiset_prod_eq_one {s : Multiset ℂ}
    (h : ∀ x ∈ s, ‖x‖ = 1) : ‖s.prod‖ = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.prod_cons, norm_mul, h a (by simp)]
      rw [ih (fun x hx => h x (by simp [hx]))]
      norm_num

/-- The inner factor contributed by the open-disk roots of a polynomial has boundary modulus one. -/
theorem norm_polynomialBlaschke_eq_one (p : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖polynomialBlaschke p z‖ = 1 := by
  apply norm_multiset_prod_eq_one
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
  exact norm_blaschkeFactor_eq_one (Multiset.mem_filter.mp ha).2 hz

/-- Reflecting the open-disk roots preserves the boundary modulus of the original polynomial. -/
theorem norm_polynomialOuterization_eq (p : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖polynomialOuterization p z‖ = ‖p.eval z‖ := by
  have hfactor := polynomialBlaschke_mul_outerization p hz.le
  have hnorm := congrArg norm hfactor
  rw [norm_mul, norm_polynomialBlaschke_eq_one p hz, one_mul] at hnorm
  exact hnorm

/-- If `p` has no root on the unit circle, its outerization is zero-free on the closed disk. -/
theorem polynomialOuterization_ne_zero {p : ℂ[X]} (hp : p ≠ 0)
    (hunit : ∀ a ∈ p.roots, ‖a‖ ≠ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polynomialOuterization p z ≠ 0 := by
  rw [polynomialOuterization]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact leadingCoeff_ne_zero.mpr hp
    · apply Multiset.prod_ne_zero
      intro hzero
      obtain ⟨a, ha, heq⟩ := Multiset.mem_map.mp hzero
      exact blaschkeFactor_den_ne_zero (Multiset.mem_filter.mp ha).2 hz heq
  · apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨a, ha, heq⟩ := Multiset.mem_map.mp hzero
    have ha' := Multiset.mem_filter.mp ha
    have hza : z = a := sub_eq_zero.mp heq
    have hge : 1 ≤ ‖a‖ := le_of_not_gt ha'.2
    have hle : ‖a‖ ≤ 1 := by simpa [← hza] using hz
    exact hunit a ha'.1 (le_antisymm hle hge)

/-- Without any boundary-root assumption, the outerization is zero-free on the open unit disk. -/
theorem polynomialOuterization_ne_zero_open {p : ℂ[X]} (hp : p ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) : polynomialOuterization p z ≠ 0 := by
  rw [polynomialOuterization]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact leadingCoeff_ne_zero.mpr hp
    · apply Multiset.prod_ne_zero
      intro hzero
      obtain ⟨a, ha, heq⟩ := Multiset.mem_map.mp hzero
      exact blaschkeFactor_den_ne_zero (Multiset.mem_filter.mp ha).2 hz.le heq
  · apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨a, ha, heq⟩ := Multiset.mem_map.mp hzero
    have ha' := Multiset.mem_filter.mp ha
    have hza : z = a := sub_eq_zero.mp heq
    exact ha'.2 (by simpa [← hza] using hz)

private theorem differentiable_multiset_prod {ι : Type*} (s : Multiset ι)
    (f : ι → ℂ → ℂ) (hf : ∀ a, Differentiable ℂ (f a)) :
    Differentiable ℂ (fun z => (s.map fun a => f a z).prod) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simpa using! (hf a).mul ih

/-- The outerization is an entire function. -/
theorem differentiable_polynomialOuterization (p : ℂ[X]) :
    Differentiable ℂ (polynomialOuterization p) := by
  unfold polynomialOuterization
  exact (differentiable_const p.leadingCoeff).mul
    (differentiable_multiset_prod (polynomialInsideRoots p)
      (fun a z => 1 - star a * z) (fun _ => by fun_prop)) |>.mul
    (differentiable_multiset_prod (polynomialOutsideRoots p)
      (fun a z => z - a) (fun _ => by fun_prop))

/-- A polynomial outerization with no boundary zeros has a holomorphic square root on a disk
strictly larger than the closed unit disk. -/
theorem exists_polynomialOuterization_sqrt {p : ℂ[X]} (hp : p ≠ 0)
    (hunit : ∀ a ∈ p.roots, ‖a‖ ≠ 1) :
    ∃ R : ℝ, 1 < R ∧ ∃ s : ℂ → ℂ,
      DifferentiableOn ℂ s (Metric.ball 0 R) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, s z ^ 2 = polynomialOuterization p z := by
  let U : Set ℂ := polynomialOuterization p ⁻¹' ({0} : Set ℂ)ᶜ
  have hUopen : IsOpen U :=
    isClosed_singleton.isOpen_compl.preimage (differentiable_polynomialOuterization p).continuous
  have hclosed : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    intro z hz
    have hznorm : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    change polynomialOuterization p z ∈ ({0} : Set ℂ)ᶜ
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      polynomialOuterization_ne_zero hp hunit (z := z) hznorm
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hUopen hclosed
  rw [thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1) 0] at hthick
  let R : ℝ := δ + 1
  have hR : 1 < R := by dsimp [R]; linarith
  have hne : ∀ z ∈ Metric.ball (0 : ℂ) R, polynomialOuterization p z ≠ 0 := by
    intro z hz
    have hzU : z ∈ U := hthick (by simpa [R, add_comm] using hz)
    simpa only [U, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hzU
  obtain ⟨s, hs, hsq⟩ := exists_sqrt_of_ne_zero
    ((differentiable_polynomialOuterization p).differentiableOn) hne
  exact ⟨R, hR, s, hs, hsq⟩

/-- On the unit circle, the square-root outer factor has squared modulus equal to the modulus of
the original polynomial. -/
theorem exists_polynomialOuterization_sqrt_boundary_norm {p : ℂ[X]} (hp : p ≠ 0)
    (hunit : ∀ a ∈ p.roots, ‖a‖ ≠ 1) :
    ∃ R : ℝ, 1 < R ∧ ∃ s : ℂ → ℂ,
      DifferentiableOn ℂ s (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) R, s z ^ 2 = polynomialOuterization p z) ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖s z‖ ^ 2 = ‖p.eval z‖ := by
  obtain ⟨R, hR, s, hs, hsq⟩ := exists_polynomialOuterization_sqrt hp hunit
  refine ⟨R, hR, s, hs, hsq, ?_⟩
  intro z hz
  have hzR : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, hz]
    exact hR
  have hnorm := congrArg norm (hsq z hzR)
  rw [norm_pow, norm_polynomialOuterization_eq p hz] at hnorm
  exact hnorm

private theorem differentiableOn_multiset_prod {ι : Type*} (s : Multiset ι)
    (f : ι → ℂ → ℂ) (t : Set ℂ)
    (hf : ∀ a ∈ s, DifferentiableOn ℂ (f a) t) :
    DifferentiableOn ℂ (fun z => (s.map fun a => f a z).prod) t := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simpa using! (hf a (by simp)).mul
        (ih (fun x hx => hf x (by simp [hx])))

/-- The finite Blaschke factor of a polynomial is holomorphic on the open unit disk. -/
theorem differentiableOn_polynomialBlaschke (p : ℂ[X]) :
    DifferentiableOn ℂ (polynomialBlaschke p) (Metric.ball 0 1) := by
  unfold polynomialBlaschke
  apply differentiableOn_multiset_prod
  intro a ha
  have haI : ‖a‖ < 1 := (Multiset.mem_filter.mp ha).2
  apply DifferentiableOn.div (by fun_prop) (by fun_prop)
  intro z hz
  apply blaschkeFactor_den_ne_zero haI
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact hz.le

/-- **Open-disk polynomial Hardy factorization, with no boundary-root restriction.**  Every
nonzero complex polynomial factors as `p = g h` on the open unit disk.  The two factors are
holomorphic there, and their radial squared moduli are given explicitly by the finite Blaschke
factor and the polynomial outerization. -/
theorem exists_polynomial_hardy_factorization_open {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ g h : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1) ∧
      DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, g z * h z = p.eval z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1,
        ‖h z‖ ^ 2 = ‖polynomialOuterization p z‖) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        ‖g z‖ ^ 2 = ‖polynomialBlaschke p z‖ ^ 2 *
          ‖polynomialOuterization p z‖ := by
  obtain ⟨s, hs, hsq⟩ := exists_sqrt_of_ne_zero
    ((differentiable_polynomialOuterization p).differentiableOn)
    (fun z hz => polynomialOuterization_ne_zero_open hp (by
      change dist z (0 : ℂ) < 1 at hz
      simpa [dist_zero_right] using hz))
  let g : ℂ → ℂ := fun z => polynomialBlaschke p z * s z
  let h : ℂ → ℂ := s
  refine ⟨g, h, (differentiableOn_polynomialBlaschke p).mul hs, hs, ?_, ?_, ?_⟩
  · intro z hz
    have hfactor := polynomialBlaschke_mul_outerization p
      (show ‖z‖ ≤ 1 by
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact hz.le)
    dsimp [g, h]
    rw [← hfactor, ← hsq z hz]
    ring
  · intro z hz
    dsimp [h]
    have hnorm := congrArg norm (hsq z hz)
    rwa [norm_pow] at hnorm
  · intro z hz
    dsimp [g]
    rw [norm_mul, mul_pow]
    congr 1
    have hnorm := congrArg norm (hsq z hz)
    rwa [norm_pow] at hnorm

/-- **Finite analytic-polynomial `H¹ = H² · H²` factorization.**  A nonzero complex polynomial
with no unit-circle roots factors on the unit disk as `p = g h`, where both factors are
holomorphic and each has boundary squared modulus exactly `|p|`. -/
theorem exists_polynomial_hardy_factorization {p : ℂ[X]} (hp : p ≠ 0)
    (hunit : ∀ a ∈ p.roots, ‖a‖ ≠ 1) :
    ∃ g h : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1) ∧
      DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, g z * h z = p.eval z) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖g z‖ ^ 2 = ‖p.eval z‖ ∧ ‖h z‖ ^ 2 = ‖p.eval z‖ := by
  obtain ⟨R, hR, s, hs, hsq, hsnorm⟩ :=
    exists_polynomialOuterization_sqrt_boundary_norm hp hunit
  let g : ℂ → ℂ := fun z => polynomialBlaschke p z * s z
  let h : ℂ → ℂ := s
  have hball : Metric.ball (0 : ℂ) 1 ⊆ Metric.ball 0 R := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    exact hz.trans hR
  have hsunit : DifferentiableOn ℂ s (Metric.ball 0 1) := hs.mono hball
  have hB : DifferentiableOn ℂ (polynomialBlaschke p) (Metric.ball 0 1) := by
    unfold polynomialBlaschke
    apply differentiableOn_multiset_prod
    intro a ha
    have haI : ‖a‖ < 1 := (Multiset.mem_filter.mp ha).2
    apply DifferentiableOn.div (by fun_prop) (by fun_prop)
    intro z hz
    apply blaschkeFactor_den_ne_zero haI
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hz.le
  refine ⟨g, h, hB.mul hsunit, hsunit, ?_, ?_⟩
  · intro z hz
    have hsqz := hsq z (hball hz)
    have hfactor := polynomialBlaschke_mul_outerization p
      (show ‖z‖ ≤ 1 by
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact hz.le)
    dsimp [g, h]
    rw [← hfactor, ← hsqz]
    ring
  · intro z hz
    constructor
    · dsimp [g]
      rw [norm_mul, norm_polynomialBlaschke_eq_one p hz, one_mul]
      exact hsnorm z hz
    · exact hsnorm z hz

end
end GaloisForLFunctions.HTGeometry
