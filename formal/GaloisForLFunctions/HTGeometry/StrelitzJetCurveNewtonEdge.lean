import GaloisForLFunctions.HTGeometry.StrelitzJetCurveNewtonSlope

/-!
# Exact Newton edge of a Strelitz jet curve

The finite rational slope extracted from an exact numerical root branch determines a maximal
Newton face of the fixed jet curve.  The two monomials defining that slope both lie on the face,
so the corresponding leading-coefficient polynomial has a nonzero complex root.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Newton weight of one power of the second logarithmic jet. -/
def strelitzJetCurveNewtonWeight (S : MvPolynomial (Fin 2) ℂ) (p : ℝ) (k : ℕ) : ℝ :=
  ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)).natDegree : ℝ) +
    (k : ℝ) * p

/-- Maximal Newton face at a specified weight. -/
def strelitzJetCurveMaxNewtonFace
    (S : MvPolynomial (Fin 2) ℂ) (p w : ℝ) : Finset ℕ :=
  (strelitzJetCurvePolynomial S).support.filter fun k =>
    strelitzJetCurveNewtonWeight S p k = w

/-- Leading-coefficient polynomial carried by one Newton face. -/
def strelitzJetCurveNewtonEdgePolynomial
    (S : MvPolynomial (Fin 2) ℂ) (p w : ℝ) : Polynomial ℂ :=
  ∑ k ∈ strelitzJetCurveMaxNewtonFace S p w,
    Polynomial.C
        (finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)).leadingCoeff *
      Polynomial.X ^ k

/-- The explicit rational slope determined by two distinct powers equalizes their Newton
weights. -/
theorem strelitzJetCurveNewtonWeight_eq_of_ne
    (S : MvPolynomial (Fin 2) ℂ) {i j : ℕ} (hij : i ≠ j) :
    strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i =
      strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) j := by
  have hden : (i : ℝ) - (j : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hij)
  rw [strelitzJetCurveNewtonWeight, strelitzJetCurveNewtonWeight,
    strelitzJetCurveNewtonSlope]
  field_simp [hden]
  ring

/-- Two distinct supporting monomials on one Newton face force that exact edge polynomial to have
a nonzero complex root. -/
theorem exists_ne_zero_isRoot_strelitzJetCurveNewtonEdge
    (S : MvPolynomial (Fin 2) ℂ) {p : ℝ} {i j : ℕ}
    (hi : i ∈ (strelitzJetCurvePolynomial S).support)
    (hj : j ∈ (strelitzJetCurvePolynomial S).support)
    (hij : i ≠ j)
    (hweight : strelitzJetCurveNewtonWeight S p i =
      strelitzJetCurveNewtonWeight S p j) :
    ∃ c : ℂ, c ≠ 0 ∧
      (strelitzJetCurveNewtonEdgePolynomial S p
        (strelitzJetCurveNewtonWeight S p i)).IsRoot c := by
  let face := strelitzJetCurveMaxNewtonFace S p
    (strelitzJetCurveNewtonWeight S p i)
  let q : ℕ → Polynomial ℂ := fun k =>
    finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)
  have hq : ∀ k ∈ face, q k ≠ 0 := by
    intro k hk
    apply finOnePolynomial_ne_zero
    exact Polynomial.mem_support_iff.mp (Finset.mem_filter.mp hk).1
  have hinj : Set.InjOn (fun k : ℕ => k) face := by
    intro a ha b hb hab
    exact hab
  have hif : i ∈ face := by
    exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hjf : j ∈ face := by
    exact Finset.mem_filter.mpr ⟨hj, hweight.symm⟩
  obtain ⟨c, hc, hroot⟩ :=
    exists_ne_zero_isRoot_edge face q (fun k : ℕ => k) hq hinj hif hjf hij
  refine ⟨c, hc, ?_⟩
  simpa [strelitzJetCurveNewtonEdgePolynomial, face, q] using hroot

/-- **Exact Newton edge package.** Every eventually nonzero exact root branch over an escaping base
has a cofinal subsequence converging in logarithmic slope to a rational Newton slope, and the
corresponding maximal edge polynomial has a genuine nonzero complex root. -/
theorem exists_strelitzJetCurveNewtonEdgeRoot_tendsto_subsequence
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0) :
    ∃ i ∈ (strelitzJetCurvePolynomial S).support,
      ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
        ∃ ns : ℕ → ℕ, StrictMono ns ∧
          Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
            (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
          (∀ k ∈ (strelitzJetCurvePolynomial S).support,
            strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) k ≤
              strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i) ∧
          ∃ c : ℂ, c ≠ 0 ∧
            (strelitzJetCurveNewtonEdgePolynomial S
              (strelitzJetCurveNewtonSlope S i j)
              (strelitzJetCurveNewtonWeight S
                (strelitzJetCurveNewtonSlope S i j) i)).IsRoot c := by
  obtain ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax⟩ :=
    exists_strelitzJetCurveNewtonSlope_tendsto_subsequence hS huTop hroot hroot0
  have hweight := strelitzJetCurveNewtonWeight_eq_of_ne S hij
  obtain ⟨c, hc, hcroot⟩ :=
    exists_ne_zero_isRoot_strelitzJetCurveNewtonEdge S hi hj hij hweight
  refine ⟨i, hi, j, hj, hij, ns, hns, hslope, ?_, c, hc, hcroot⟩
  intro k hk
  simpa [strelitzJetCurveNewtonWeight] using hmax k hk

end

end GaloisForLFunctions.HTGeometry
