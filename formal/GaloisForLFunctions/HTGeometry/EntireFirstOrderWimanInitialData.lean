import GaloisForLFunctions.HTGeometry.IrreducibleFirstOrderWimanNewtonEdge
import GaloisForLFunctions.HTGeometry.TranscendentalEntireTaylorSupport
import GaloisForLFunctions.HTGeometry.GoldbergFiniteOrder

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A nonzero first-order relation on a transcendental entire function genuinely contains its
derivative variable.  Otherwise renaming its support into the first two coordinates would give an
order-zero algebraic differential equation. -/
theorem derivative_mem_vars_of_transcendental_firstOrder_relation
    {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    {P : MvPolynomial (Fin 3) ℂ} (hP : P ≠ 0)
    (hrel : ∀ z : ℂ, MvPolynomial.eval
      (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) P = 0) :
    (2 : Fin 3) ∈ P.vars := by
  by_contra hnot
  let g : Fin 2 → Fin 3 := Fin.castLE (by omega)
  have hginj : Function.Injective g := Fin.castLE_injective (by omega)
  have hvars : (P.vars : Set (Fin 3)) ⊆ Set.range g := by
    intro i hi
    have hine : i ≠ (2 : Fin 3) := by
      intro hieq
      exact hnot (hieq ▸ hi)
    have hiv : i.val < 2 := by omega
    refine ⟨⟨i.val, hiv⟩, ?_⟩
    exact Fin.ext rfl
  obtain ⟨Q, hQ⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range P g hginj hvars
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hQ
    exact hP hQ.symm
  apply not_differentiallyAlgebraicOfOrder_zero_of_transcendental hf.1 hf.2
  refine ⟨Q, hQne, ?_⟩
  intro z
  have hz := hrel z
  rw [← hQ, MvPolynomial.eval_rename] at hz
  have hv : (Fin.cons z fun j : Fin 1 => iteratedDeriv (j : ℕ) f z) =
      (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) ∘ g := by
    funext j
    fin_cases j <;> rfl
  rw [hv]
  exact hz

/-- Exact nondegenerate Newton initial data extracted from a transcendental entire first-order
differential-algebraic function.  The coefficient row reconstructs one irreducible relation on the
actual analytic derivative component; its displayed maximal face has two distinct derivative
powers and a prescribed nonzero root at rational slope `p`, with positive charge `p + 1`. -/
structure EntireFirstOrderWimanInitialData (f : ℂ → ℂ) where
  P : MvPolynomial (Fin 3) ℂ
  indexSupport : Finset (ℕ × ℕ)
  coeff : ℕ × ℕ → Polynomial ℂ
  totalDegree : ℕ
  slope : ℚ
  weight : ℝ
  firstIndex : ℕ × ℕ
  secondIndex : ℕ × ℕ
  root : ℂ
  polynomial_ne_zero : P ≠ 0
  polynomial_irreducible : Irreducible P
  derivative_mem_vars : (2 : Fin 3) ∈ P.vars
  relation : ∀ z : ℂ, MvPolynomial.eval
    (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) P = 0
  coefficient_reconstruction : firstOrderMvPoly indexSupport coeff = P
  coefficient_ne_zero : ∀ i, i ∈ indexSupport → coeff i ≠ 0
  support_degree_le : ∀ i, i ∈ indexSupport → i.1 + i.2 ≤ totalDegree
  first_mem_face : firstIndex ∈ firstOrderMaxNewtonFace indexSupport coeff
    totalDegree (slope : ℝ) weight
  second_mem_face : secondIndex ∈ firstOrderMaxNewtonFace indexSupport coeff
    totalDegree (slope : ℝ) weight
  weight_maximal : ∀ i ∈ firstOrderTopNewtonFace indexSupport coeff totalDegree,
    firstOrderNewtonWeight coeff (slope : ℝ) i ≤ weight
  indices_ne : firstIndex ≠ secondIndex
  derivativeExponents_ne : firstIndex.2 ≠ secondIndex.2
  charge_pos : 0 < (slope : ℝ) + 1
  root_ne_zero : root ≠ 0
  edge_root : (firstOrderNewtonEdgePolynomial
    (firstOrderMaxNewtonFace indexSupport coeff totalDegree (slope : ℝ) weight)
      coeff).IsRoot root

/-- **Reduction-I initial-data theorem.**  Every transcendental entire order-one ADE supplies the
exact irreducible, two-term, prescribed-root Wiman initial data needed by the finite cascade
prolongation. -/
theorem exists_entireFirstOrderWimanInitialData
    {f : ℂ → ℂ} (hf : TranscendentalEntire f)
    (hDA : DifferentiallyAlgebraicOfOrder f 1) :
    Nonempty (EntireFirstOrderWimanInitialData f) := by
  let a : ℕ → ℂ := taylorCoeff f
  have ha : EntireCoeffs a := entireCoeffs_taylorCoeff hf.1
  obtain ⟨n₀, hn₀⟩ := exists_taylorCoeff_ne_zero_of_transcendentalEntire hf
  have htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0 :=
    fun M => exists_taylorCoeff_ne_zero_ge_of_transcendentalEntire hf M
  have hcoeff : coeffFun a = f := coeffFun_taylorCoeff hf.1
  have hDAa : DifferentiallyAlgebraicOfOrder (coeffFun a) 1 := by
    rw [hcoeff]
    exact hDA
  obtain ⟨P, S, S₀, A, A₀, d, m, y, z, q, i₁, i₂, c,
    hP, hPirred, hPrel, hdeg, hrel, hmpos, hmle, htarget, htopdeg, hAne, hAdeg,
    hqpos, hρ, hz, hνpos, hslope, htoplim, hdefectlim, hpoly, hshift,
    hsourcePoly, hsourceA, hsourceS, hsourceCoeff, hsourceDeg, hsourceFace,
    hi₁, hi₂, hi₁₂, hweight, ⟨pRat, hpRat, hpRatPos⟩, hmax, hcne, hcroot,
    hsourceRoot⟩ := exists_irreducibleFirstOrderWimanNewtonEdge ha hn₀ htrans hDAa
  have hi₁S : i₁ ∈ S := by
    have h := hi₁
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at h
    exact h.1.1
  have hi₂S : i₂ ∈ S := by
    have h := hi₂
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at h
    exact h.1.1
  rw [hsourceS] at hi₁S hi₂S
  obtain ⟨u₁, hu₁, hu₁shift⟩ := Finset.mem_image.mp hi₁S
  obtain ⟨u₂, hu₂, hu₂shift⟩ := Finset.mem_image.mp hi₂S
  have hu₁Source : u₁ ∈ firstOrderSourceNewtonFace S₀ S A d (q - 1)
      (firstOrderNewtonWeight A (q - 1) i₁) := by
    rw [firstOrderSourceNewtonFace, Finset.mem_filter]
    refine ⟨hu₁, ?_⟩
    rwa [hu₁shift]
  have hu₂Source : u₂ ∈ firstOrderSourceNewtonFace S₀ S A d (q - 1)
      (firstOrderNewtonWeight A (q - 1) i₁) := by
    rw [firstOrderSourceNewtonFace, Finset.mem_filter]
    refine ⟨hu₂, ?_⟩
    rwa [hu₂shift]
  have hu₁Face : u₁ ∈ firstOrderMaxNewtonFace S₀ A₀ (d - 1) (q - 1)
      (firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1)) := by
    rw [← hsourceFace]
    exact hu₁Source
  have hu₂Face : u₂ ∈ firstOrderMaxNewtonFace S₀ A₀ (d - 1) (q - 1)
      (firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1)) := by
    rw [← hsourceFace]
    exact hu₂Source
  have hsourceMax : ∀ u ∈ firstOrderTopNewtonFace S₀ A₀ (d - 1),
      firstOrderNewtonWeight A₀ (q - 1) u ≤
        firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1) := by
    intro u hu
    have hu' := hu
    rw [firstOrderTopNewtonFace, Finset.mem_filter] at hu'
    obtain ⟨huS₀, huDeg, huA₀⟩ := hu'
    have hshiftMem : firstOrderDerivativeShift u ∈ S := by
      rw [hsourceS, Finset.mem_image]
      exact ⟨u, huS₀, rfl⟩
    have hshiftTop : firstOrderDerivativeShift u ∈ firstOrderTopNewtonFace S A d := by
      rw [firstOrderTopNewtonFace, Finset.mem_filter]
      refine ⟨hshiftMem, ?_, ?_⟩
      · simp only [firstOrderDerivativeShift]
        omega
      · rw [hsourceCoeff u huS₀]
        exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) huA₀
    have hdegree :
        (A (firstOrderDerivativeShift u)).natDegree = d + (A₀ u).natDegree := by
      rw [hsourceCoeff u huS₀, Polynomial.natDegree_mul
        (pow_ne_zero _ Polynomial.X_ne_zero) huA₀, Polynomial.natDegree_X_pow]
    have hweightShift :
        firstOrderNewtonWeight A (q - 1) (firstOrderDerivativeShift u) =
          firstOrderNewtonWeight A₀ (q - 1) u + d + (q - 1) := by
      rw [firstOrderNewtonWeight, firstOrderNewtonWeight, hdegree]
      simp only [firstOrderDerivativeShift]
      push_cast
      ring
    calc
      firstOrderNewtonWeight A₀ (q - 1) u =
          firstOrderNewtonWeight A (q - 1) (firstOrderDerivativeShift u) - d -
            (q - 1) := by rw [hweightShift]; ring
      _ ≤ firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1) := by
        gcongr
        exact hmax (firstOrderDerivativeShift u) hshiftTop
  have hu₁₂ : u₁ ≠ u₂ := by
    intro h
    apply hi₁₂
    rw [← hu₁shift, ← hu₂shift, h]
  have hu₁deg : u₁.1 + u₁.2 = d - 1 := by
    have h := hu₁Face
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at h
    exact h.1.2.1
  have hu₂deg : u₂.1 + u₂.2 = d - 1 := by
    have h := hu₂Face
    rw [firstOrderMaxNewtonFace, Finset.mem_filter,
      firstOrderTopNewtonFace, Finset.mem_filter] at h
    exact h.1.2.1
  have hu₁₂snd : u₁.2 ≠ u₂.2 :=
    snd_ne_of_ne_of_add_eq_add_eq hu₁deg hu₂deg hu₁₂
  let w₀ : ℝ := firstOrderNewtonWeight A (q - 1) i₁ - d - (q - 1)
  refine ⟨{
    P := P
    indexSupport := S₀
    coeff := A₀
    totalDegree := d - 1
    slope := pRat
    weight := w₀
    firstIndex := u₁
    secondIndex := u₂
    root := c
    polynomial_ne_zero := hP
    polynomial_irreducible := hPirred
    derivative_mem_vars :=
      derivative_mem_vars_of_transcendental_firstOrder_relation hf hP ?_
    relation := ?_
    coefficient_reconstruction := hsourcePoly
    coefficient_ne_zero := hsourceA
    support_degree_le := hsourceDeg
    first_mem_face := ?_
    second_mem_face := ?_
    weight_maximal := ?_
    indices_ne := hu₁₂
    derivativeExponents_ne := hu₁₂snd
    charge_pos := hpRatPos
    root_ne_zero := hcne
    edge_root := ?_ }⟩
  · simpa only [hcoeff] using hPrel
  · simpa only [hcoeff] using hPrel
  · simpa only [hpRat, w₀] using hu₁Face
  · simpa only [hpRat, w₀] using hu₂Face
  · simpa only [hpRat, w₀] using hsourceMax
  · simpa only [hpRat, w₀] using hsourceRoot

end

end GaloisForLFunctions.HTGeometry
