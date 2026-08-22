import GaloisForLFunctions.HTGeometry.Octonion.RegularInverse

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- Ordinary iterated composition of an octonion endomorphism. -/
def operatorPower (F : RealOctonion → RealOctonion) : ℕ → RealOctonion → RealOctonion
  | 0 => id
  | n + 1 => F ∘ operatorPower F n

@[simp] theorem operatorPower_zero (F : RealOctonion → RealOctonion) (x : RealOctonion) :
    operatorPower F 0 x = x := rfl

@[simp] theorem operatorPower_succ (F : RealOctonion → RealOctonion)
    (n : ℕ) (x : RealOctonion) :
    operatorPower F (n + 1) x = F (operatorPower F n x) := rfl

/-- The paper's `C_J`-extendable power-associativity condition specialized to `𝕆`:
all ordinary powers commute on the right with a slice scalar when started on the real part. -/
def IsSliceExtendable (F : RealOctonion → RealOctonion) (J : ImaginaryUnit) : Prop :=
  ∀ n : ℕ, ∀ r : ℝ, ∀ c : RealOctonion, c ∈ complexSliceSubmodule J →
    operatorPower F n (scalarEmbed r * c) =
      operatorPower F n (scalarEmbed r) * c

theorem operatorPower_leftAction_mem_generatedSubmodule
    (a c x : RealOctonion) (hx : x ∈ generatedSubmodule a c) (n : ℕ) :
    operatorPower (leftAction a) n x ∈ generatedSubmodule a c := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    change a * operatorPower (leftAction a) n x ∈ generatedSubmodule a c
    exact mul_mem_generatedSubmodule a c a _ (s_mem_generatedSubmodule a c) ih

theorem leftAction_mul_right_of_mem_generatedSubmodule
    (a c x : RealOctonion) (hx : x ∈ generatedSubmodule a c) :
    leftAction a (x * c) = leftAction a x * c := by
  change a * (x * c) = (a * x) * c
  exact (sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule a c a x c
    (s_mem_generatedSubmodule a c) hx (q_mem_generatedSubmodule a c))).symm

/-- Every left-multiplication operator is slice-extendable. -/
theorem leftAction_isSliceExtendable (a : RealOctonion) (J : ImaginaryUnit) :
    IsSliceExtendable (leftAction a) J := by
  intro n r c _
  have hscalar : scalarEmbed r ∈ generatedSubmodule a c :=
    scalarEmbed_mem_generatedSubmodule a c r
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [operatorPower_succ, operatorPower_succ, ih]
    exact leftAction_mul_right_of_mem_generatedSubmodule a c
      (operatorPower (leftAction a) n (scalarEmbed r))
      (operatorPower_leftAction_mem_generatedSubmodule a c (scalarEmbed r) hscalar n)

/-- On the two-generated associative subalgebra, the genuine real-linear inverse agrees
with the inverse in paper equation (8.7). -/
theorem sylvesterDifferenceEquiv_symm_eq_restrictedResolventInverse
    (s q : RealOctonion) (hquad : quadratic s q ≠ 0)
    {x : RealOctonion} (hx : x ∈ generatedSubmodule s q) :
    (sylvesterDifferenceEquiv s q hquad).symm x = restrictedResolventInverse s q x := by
  let e := sylvesterDifferenceEquiv s q hquad
  apply e.injective
  calc
    e (e.symm x) = x := e.apply_symm_apply _
    _ = resolventDifference s q (restrictedResolventInverse s q x) :=
      (resolventDifference_restrictedResolventInverse_apply s q x hquad hx).symm
    _ = e (restrictedResolventInverse s q x) := by rfl

theorem sylvesterDifferenceEquiv_symm_mem_generatedSubmodule
    (s q : RealOctonion) (hquad : quadratic s q ≠ 0)
    {x : RealOctonion} (hx : x ∈ generatedSubmodule s q) :
    (sylvesterDifferenceEquiv s q hquad).symm x ∈ generatedSubmodule s q := by
  rw [sylvesterDifferenceEquiv_symm_eq_restrictedResolventInverse s q hquad hx]
  exact restrictedResolventInverse_mem_generatedSubmodule s q x hx

theorem operatorPower_sylvesterDifferenceEquiv_symm_mem_generatedSubmodule
    (s q : RealOctonion) (hquad : quadratic s q ≠ 0)
    {x : RealOctonion} (hx : x ∈ generatedSubmodule s q) (n : ℕ) :
    operatorPower (sylvesterDifferenceEquiv s q hquad).symm n x ∈
      generatedSubmodule s q := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    change (sylvesterDifferenceEquiv s q hquad).symm
      (operatorPower (sylvesterDifferenceEquiv s q hquad).symm n x) ∈
        generatedSubmodule s q
    exact sylvesterDifferenceEquiv_symm_mem_generatedSubmodule s q hquad ih

theorem restrictedResolventInverse_mul_right_of_mem_generatedSubmodule
    (s q : RealOctonion) (J : ImaginaryUnit)
    (hs : s ∈ complexSliceSubmodule J)
    {x c : RealOctonion}
    (hx : x ∈ generatedSubmodule s q) (hc : c ∈ generatedSubmodule s q)
    (hcJ : c ∈ complexSliceSubmodule J) :
    restrictedResolventInverse s q (x * c) = restrictedResolventInverse s q x * c := by
  let M := generatedSubmodule s q
  have hsM : s ∈ M := by simpa only [M] using s_mem_generatedSubmodule s q
  have hqM : q ∈ M := by simpa only [M] using q_mem_generatedSubmodule s q
  have hbarM : star s ∈ M := by simpa only [M] using star_s_mem_generatedSubmodule s q
  have hquadM : quadratic s q ∈ M := by simpa only [M] using quadratic_mem_generatedSubmodule s q
  have hinvM : inverse (quadratic s q) ∈ M := by
    simpa only [M] using inverse_mem_generatedSubmodule s q _ hquadM
  have hxcM : x * c ∈ M := by
    simpa only [M] using mul_mem_generatedSubmodule s q x c hx hc
  have hdiffM : x * star s - q * x ∈ M := by
    exact Submodule.sub_mem M
      (mul_mem_generatedSubmodule s q x (star s) hx hbarM)
      (mul_mem_generatedSubmodule s q q x hqM hx)
  have hassoc {u v w : RealOctonion}
      (hu : u ∈ M) (hv : v ∈ M) (hw : w ∈ M) : (u * v) * w = u * (v * w) := by
    exact sub_eq_zero.mp (associator_eq_zero_of_mem_generatedSubmodule s q u v w hu hv hw)
  have hcomm : c * star s = star s * c :=
    complexSliceSubmodule_commutes_star J hs hcJ
  have hright : (x * c) * star s = (x * star s) * c := by
    calc
      (x * c) * star s = x * (c * star s) := hassoc hx hc hbarM
      _ = x * (star s * c) := by rw [hcomm]
      _ = (x * star s) * c := (hassoc hx hbarM hc).symm
  have hleft : q * (x * c) = (q * x) * c := (hassoc hqM hx hc).symm
  unfold restrictedResolventInverse resolventDifference leftAction rightAction
  calc
    inverse (quadratic s q) * ((x * c) * star s - q * (x * c)) =
      inverse (quadratic s q) * ((x * star s - q * x) * c) := by
        rw [hright, hleft, sub_mul]
    _ = (inverse (quadratic s q) * (x * star s - q * x)) * c :=
      (hassoc hinvM hdiffM hc).symm

theorem sylvesterDifferenceEquiv_symm_mul_right_of_coeff_ne_zero
    (s q : RealOctonion) (J : ImaginaryUnit) (a b : ℝ)
    (hs : s = scalarEmbed a + scalarEmbed b * J.val) (hb : b ≠ 0)
    (hquad : quadratic s q ≠ 0)
    {x c : RealOctonion}
    (hx : x ∈ generatedSubmodule s q) (hc : c ∈ complexSliceSubmodule J) :
    (sylvesterDifferenceEquiv s q hquad).symm (x * c) =
      (sylvesterDifferenceEquiv s q hquad).symm x * c := by
  have hcM : c ∈ generatedSubmodule s q :=
    complexSliceSubmodule_mem_generatedSubmodule_of_coeff_ne_zero s q J a b hs hb hc
  have hxcM : x * c ∈ generatedSubmodule s q :=
    mul_mem_generatedSubmodule s q x c hx hcM
  calc
    (sylvesterDifferenceEquiv s q hquad).symm (x * c) =
      restrictedResolventInverse s q (x * c) :=
        sylvesterDifferenceEquiv_symm_eq_restrictedResolventInverse s q hquad hxcM
    _ = restrictedResolventInverse s q x * c :=
      restrictedResolventInverse_mul_right_of_mem_generatedSubmodule s q J
        (by rw [hs]; exact ⟨a, b, rfl⟩) hx hcM hc
    _ = (sylvesterDifferenceEquiv s q hquad).symm x * c := by
      rw [sylvesterDifferenceEquiv_symm_eq_restrictedResolventInverse s q hquad hx]

theorem sylvesterDifferenceEquiv_symm_isSliceExtendable_of_coeff_ne_zero
    (s q : RealOctonion) (J : ImaginaryUnit) (a b : ℝ)
    (hs : s = scalarEmbed a + scalarEmbed b * J.val) (hb : b ≠ 0)
    (hquad : quadratic s q ≠ 0) :
    IsSliceExtendable (sylvesterDifferenceEquiv s q hquad).symm J := by
  intro n r c hc
  have hscalar : scalarEmbed r ∈ generatedSubmodule s q :=
    scalarEmbed_mem_generatedSubmodule s q r
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [operatorPower_succ, operatorPower_succ, ih]
    exact sylvesterDifferenceEquiv_symm_mul_right_of_coeff_ne_zero s q J a b hs hb hquad
      (x := operatorPower (sylvesterDifferenceEquiv s q hquad).symm n (scalarEmbed r))
      (c := c)
      (operatorPower_sylvesterDifferenceEquiv_symm_mem_generatedSubmodule
        s q hquad hscalar n) hc

theorem sylvesterDifferenceEquiv_symm_eq_leftAction_formula_of_scalar
    (a : ℝ) (q : RealOctonion) (hquad : quadratic (scalarEmbed a) q ≠ 0) :
    (sylvesterDifferenceEquiv (scalarEmbed a) q hquad).symm =
      leftAction (inverse (quadratic (scalarEmbed a) q) *
        (star (scalarEmbed a) - q)) := by
  funext x
  let e := sylvesterDifferenceEquiv (scalarEmbed a) q hquad
  apply e.injective
  calc
    e (e.symm x) = x := e.apply_symm_apply _
    _ = resolventDifference (scalarEmbed a) q
        ((inverse (quadratic (scalarEmbed a) q) *
          (star (scalarEmbed a) - q)) * x) :=
      (resolventDifference_sliceFormula_apply_of_scalar a q x hquad).symm
    _ = e ((inverse (quadratic (scalarEmbed a) q) *
          (star (scalarEmbed a) - q)) * x) := by rfl

theorem sylvesterDifferenceEquiv_symm_isSliceExtendable_of_scalar
    (a : ℝ) (q : RealOctonion) (J : ImaginaryUnit)
    (hquad : quadratic (scalarEmbed a) q ≠ 0) :
    IsSliceExtendable (sylvesterDifferenceEquiv (scalarEmbed a) q hquad).symm J := by
  rw [sylvesterDifferenceEquiv_symm_eq_leftAction_formula_of_scalar a q hquad]
  exact leftAction_isSliceExtendable _ J

/-- The pull-back slice-resolvent set for left multiplication on the one-dimensional
octonion module.  The inverse is the genuine real-linear inverse; the final conjunct is
the source paper's `C_J`-extendability condition. -/
def leftMultiplicationPullbackSliceResolventSet
    (q : RealOctonion) (J : ImaginaryUnit) : Set RealOctonion :=
  {s | s ∈ complexSliceSubmodule J ∧
    ∃ hquad : quadratic s q ≠ 0,
      IsSliceExtendable (sylvesterDifferenceEquiv s q hquad).symm J}

/-- The exact one-dimensional pull-back slice-resolvent classification in Theorem 8.7. -/
theorem leftMultiplicationPullbackSliceResolventSet_eq
    (q : RealOctonion) (J : ImaginaryUnit) :
    leftMultiplicationPullbackSliceResolventSet q J =
      (complexSliceSubmodule J : Set RealOctonion) \ conjugacySphere q := by
  ext s
  constructor
  · rintro ⟨hs, hquad, _⟩
    exact ⟨hs, fun hmem => hquad ((mem_conjugacySphere_iff_quadratic_eq_zero s q).mp hmem)⟩
  · rintro ⟨hs, hnot⟩
    have hquad : quadratic s q ≠ 0 := quadratic_ne_zero_of_not_mem_conjugacySphere s q hnot
    refine ⟨hs, hquad, ?_⟩
    rcases hs with ⟨a, b, hs⟩
    by_cases hb : b = 0
    · have hsreal : s = scalarEmbed a := by rw [hs, hb]; simp
      have hquadreal : quadratic (scalarEmbed a) q ≠ 0 := by
        simpa [hs, hb] using hquad
      simpa only [hsreal] using
        sylvesterDifferenceEquiv_symm_isSliceExtendable_of_scalar a q J hquadreal
    · exact sylvesterDifferenceEquiv_symm_isSliceExtendable_of_coeff_ne_zero
        s q J a b hs hb hquad

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
