import GaloisForLFunctions.HTGeometry.PPMatrixRankFormula

/-!
# Consequences of the periodic-pencil matrix-rank formula

The central equality `ppDim_eq_matrixCost` is proved in `PPMatrixRankFormula`.  This module closes
the remaining existence statements from the card: PP-admissible matrices exist for every finite
facet system, the natural-number matrix cost is attained, and the rational-kernel correction is
always a single bit.
-/


namespace GaloisForLFunctions

open scoped Matrix Classical

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
theorem exists_ppAdmissible (faces : A → Finset V) :
    ∃ M : A → V → ℂ, PPAdmissible faces M := by
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  let ν : V → ℕ := fun v => ((Fintype.equivFin V) v : ℕ)
  have hν : Function.Injective ν :=
    Fin.val_injective.comp (Fintype.equivFin V).injective
  let M : A → V → ℂ := fun B v => if v ∈ faces B then τ ^ (ν v + 1) else 0
  refine ⟨M, ?_⟩
  intro B
  constructor
  · intro v hv
    exact ⟨0, by simp [M, hv]⟩
  · let μ : Option (faces B) → ℕ := fun i => i.elim 0 (fun v => ν (v : V) + 1)
    have hμ : Function.Injective μ := by
      intro i j hij
      cases i with
      | none =>
          cases j with
          | none => rfl
          | some j => simp [μ] at hij
      | some i =>
          cases j with
          | none => simp [μ] at hij
          | some j =>
              apply congrArg some
              apply Subtype.ext
              apply hν
              simp only [μ, Option.elim_some] at hij
              omega
    have hlin := transcendental_pow_comp_linearIndependent hτ hμ
    convert! hlin using 1
    funext i
    cases i with
    | none => simp [μ]
    | some i => simp [μ, M]

omit [Fintype A] [DecidableEq A] in
theorem matrixCost_attained (faces : A → Finset V) :
    ∃ M : A → V → ℂ, PPAdmissible faces M ∧
      matrixCost faces = (Matrix.of M).rank + epsQ M := by
  obtain ⟨M, hM⟩ := exists_ppAdmissible faces
  have hne : {n | ∃ M : A → V → ℂ, PPAdmissible faces M ∧
      n = (Matrix.of M).rank + epsQ M}.Nonempty :=
    ⟨(Matrix.of M).rank + epsQ M, M, hM, rfl⟩
  obtain ⟨M', hM', hval⟩ := Nat.sInf_mem hne
  refine ⟨M', hM', ?_⟩
  simpa [matrixCost] using hval

omit [Fintype A] [DecidableEq V] [DecidableEq A] in
theorem epsQ_le_one (M : A → V → ℂ) : epsQ M ≤ 1 := by
  unfold epsQ
  split_ifs <;> omega

omit [Fintype A] [DecidableEq A] in
theorem ppDim_le_card (faces : A → Finset V) : ppDim faces ≤ Fintype.card V := by
  obtain ⟨M, hM⟩ := exists_ppAdmissible faces
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let a : V → Fin (Fintype.card V) → ℂ :=
    fun v => (Pi.single (e v) (1 : ℂ) : Fin (Fintype.card V) → ℂ)
  let U : A → Fin (Fintype.card V) → ℂ := fun B i => M B (e.symm i)
  have ha : LinearIndependent ℚ a := by
    have hC : LinearIndependent ℂ (fun v : V =>
        (Pi.single (e v) (1 : ℂ) : Fin (Fintype.card V) → ℂ)) := by
      have hb := (Pi.basisFun ℂ (Fin (Fintype.card V))).linearIndependent.comp e e.injective
      simpa [Function.comp_def, Pi.basisFun_apply] using hb
    have hCq := hC.restrict_scalars (R := ℚ) (by
      intro p q hpq
      have hpc : (p : ℂ) = (q : ℂ) := by simpa [Rat.smul_one_eq_cast] using hpq
      exact_mod_cast hpc)
    simpa [a] using hCq
  apply Nat.sInf_le
  refine ⟨a, ha, U, ?_⟩
  have heval : (fun B v => ∑ i, U B i * a v i) = M := by
    funext B v
    simp [U, a, Pi.single_apply, e]
  rw [heval]
  exact hM

omit [DecidableEq A] in
theorem matrixCost_le_card (faces : A → Finset V) : matrixCost faces ≤ Fintype.card V := by
  rw [← ppDim_eq_matrixCost]
  exact ppDim_le_card faces

/-! ## The boundary-wedge pencil -/

/-- Facets of `∂σʳ ∨ ∂σˢ`, indexed by the omitted vertex in the left or right block. -/
abbrev BoundaryWedgeFacetIndex (r s : ℕ) := Fin r ⊕ Fin s

/-- Vertices of the boundary wedge: the common centre and the two disjoint noncentral blocks. -/
abbrev PPBoundaryWedgeVertex (r s : ℕ) := Option (Fin r ⊕ Fin s)

/-- The facet obtained by omitting one vertex from one boundary-simplex block. -/
noncomputable def boundaryWedgeFacet {r s : ℕ} (B : BoundaryWedgeFacetIndex r s) :
    Finset (PPBoundaryWedgeVertex r s) :=
  Finset.univ.filter fun v =>
    match B, v with
    | Sum.inl u, none => True
    | Sum.inl u, some (Sum.inl i) => i ≠ u
    | Sum.inl _, some (Sum.inr _) => False
    | Sum.inr u, none => True
    | Sum.inr u, some (Sum.inr i) => i ≠ u
    | Sum.inr _, some (Sum.inl _) => False

@[simp] theorem none_mem_boundaryWedgeFacet_left {r s : ℕ} (u : Fin r) :
    none ∈ boundaryWedgeFacet (s := s) (Sum.inl u) := by
  simp [boundaryWedgeFacet]

@[simp] theorem inl_mem_boundaryWedgeFacet_left {r s : ℕ} (u i : Fin r) :
    some (Sum.inl i) ∈ boundaryWedgeFacet (s := s) (Sum.inl u) ↔ i ≠ u := by
  simp [boundaryWedgeFacet]

@[simp] theorem not_inr_mem_boundaryWedgeFacet_left {r s : ℕ} (u : Fin r) (j : Fin s) :
    some (Sum.inr j) ∉ boundaryWedgeFacet (Sum.inl u) := by
  simp [boundaryWedgeFacet]

@[simp] theorem none_mem_boundaryWedgeFacet_right {r s : ℕ} (u : Fin s) :
    none ∈ boundaryWedgeFacet (r := r) (Sum.inr u) := by
  simp [boundaryWedgeFacet]

@[simp] theorem inr_mem_boundaryWedgeFacet_right {r s : ℕ} (u i : Fin s) :
    some (Sum.inr i) ∈ boundaryWedgeFacet (r := r) (Sum.inr u) ↔ i ≠ u := by
  simp [boundaryWedgeFacet]

@[simp] theorem not_inl_mem_boundaryWedgeFacet_right {r s : ℕ} (u : Fin s) (i : Fin r) :
    some (Sum.inl i) ∉ boundaryWedgeFacet (Sum.inr u) := by
  simp [boundaryWedgeFacet]

/-- Exponents obtained by restoring the omitted left vertex as the distinguished `1` entry. -/
def boundaryWedgeLeftFacetExponent {r s : ℕ} (u : Fin r) :
    Option (boundaryWedgeFacet (s := s) (Sum.inl u)) → ℕ
  | none => u
  | some v =>
      match v.1 with
      | none => r
      | some (Sum.inl i) => i
      | some (Sum.inr _) => r + 1

/-- Exponents obtained by restoring the omitted right vertex as the distinguished `1` entry. -/
def boundaryWedgeRightFacetExponent {r s : ℕ} (u : Fin s) :
    Option (boundaryWedgeFacet (r := r) (Sum.inr u)) → ℕ
  | none => u
  | some v =>
      match v.1 with
      | none => s
      | some (Sum.inr i) => i
      | some (Sum.inl _) => s + 1

theorem boundaryWedgeLeftFacetExponent_injective {r s : ℕ} (u : Fin r) :
    Function.Injective (boundaryWedgeLeftFacetExponent (s := s) u) := by
  intro x y h
  rcases x with _ | ⟨x, hx⟩
  · rcases y with _ | ⟨y, hy⟩
    · rfl
    · rcases y with _ | (k | l)
      · have h' : (u : ℕ) = r := by simpa [boundaryWedgeLeftFacetExponent] using h
        exact ((Nat.ne_of_lt u.isLt) h').elim
      · have h' : u = k := Fin.ext (by simpa [boundaryWedgeLeftFacetExponent] using h)
        exact ((inl_mem_boundaryWedgeFacet_left u k).mp hy h'.symm).elim
      · exact (not_inr_mem_boundaryWedgeFacet_left u l hy).elim
  · rcases x with _ | (i | j)
    · rcases y with _ | ⟨y, hy⟩
      · have h' : r = (u : ℕ) := by simpa [boundaryWedgeLeftFacetExponent] using h
        exact ((Nat.ne_of_lt u.isLt) h'.symm).elim
      · rcases y with _ | (k | l)
        · rfl
        · have h' : r = (k : ℕ) := by simpa [boundaryWedgeLeftFacetExponent] using h
          exact ((Nat.ne_of_lt k.isLt) h'.symm).elim
        · exact (not_inr_mem_boundaryWedgeFacet_left u l hy).elim
    · rcases y with _ | ⟨y, hy⟩
      · have h' : (i : ℕ) = (u : ℕ) := by
          simpa [boundaryWedgeLeftFacetExponent] using h
        exact ((inl_mem_boundaryWedgeFacet_left u i).mp hx (Fin.ext h')).elim
      · rcases y with _ | (k | l)
        · have h' : (i : ℕ) = r := by simpa [boundaryWedgeLeftFacetExponent] using h
          exact ((Nat.ne_of_lt i.isLt) h').elim
        · have hik : i = k := Fin.ext (by simpa [boundaryWedgeLeftFacetExponent] using h)
          subst k
          rfl
        · exact (not_inr_mem_boundaryWedgeFacet_left u l hy).elim
    · exact (not_inr_mem_boundaryWedgeFacet_left u j hx).elim

theorem boundaryWedgeRightFacetExponent_injective {r s : ℕ} (u : Fin s) :
    Function.Injective (boundaryWedgeRightFacetExponent (r := r) u) := by
  intro x y h
  rcases x with _ | ⟨x, hx⟩
  · rcases y with _ | ⟨y, hy⟩
    · rfl
    · rcases y with _ | (k | l)
      · have h' : (u : ℕ) = s := by simpa [boundaryWedgeRightFacetExponent] using h
        exact ((Nat.ne_of_lt u.isLt) h').elim
      · exact (not_inl_mem_boundaryWedgeFacet_right u k hy).elim
      · have h' : u = l := Fin.ext (by simpa [boundaryWedgeRightFacetExponent] using h)
        exact ((inr_mem_boundaryWedgeFacet_right u l).mp hy h'.symm).elim
  · rcases x with _ | (i | j)
    · rcases y with _ | ⟨y, hy⟩
      · have h' : s = (u : ℕ) := by simpa [boundaryWedgeRightFacetExponent] using h
        exact ((Nat.ne_of_lt u.isLt) h'.symm).elim
      · rcases y with _ | (k | l)
        · rfl
        · exact (not_inl_mem_boundaryWedgeFacet_right u k hy).elim
        · have h' : s = (l : ℕ) := by simpa [boundaryWedgeRightFacetExponent] using h
          exact ((Nat.ne_of_lt l.isLt) h'.symm).elim
    · exact (not_inl_mem_boundaryWedgeFacet_right u i hx).elim
    · rcases y with _ | ⟨y, hy⟩
      · have h' : (j : ℕ) = (u : ℕ) := by
          simpa [boundaryWedgeRightFacetExponent] using h
        exact ((inr_mem_boundaryWedgeFacet_right u j).mp hx (Fin.ext h')).elim
      · rcases y with _ | (k | l)
        · have h' : (j : ℕ) = s := by simpa [boundaryWedgeRightFacetExponent] using h
          exact ((Nat.ne_of_lt j.isLt) h').elim
        · exact (not_inl_mem_boundaryWedgeFacet_right u k hy).elim
        · have hjl : j = l := Fin.ext (by simpa [boundaryWedgeRightFacetExponent] using h)
          subst l
          rfl

/-- A family is independent if multiplication by one nonzero scalar turns it into distinct
powers of a transcendental number. -/
theorem linearIndependent_of_mul_eq_transcendental_powers
    {ι : Type*} [Fintype ι] {τ c : ℂ} (hτ : Transcendental ℚ τ)
    (μ : ι → ℕ) (hμ : Function.Injective μ) (f : ι → ℂ)
    (hscale : ∀ i, c * f i = τ ^ μ i) : LinearIndependent ℚ f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  apply transcendental_pow_combination_eq_zero hτ hμ g
  calc
    ∑ i, g i • τ ^ μ i = ∑ i, g i • (c * f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hscale]
    _ = c * ∑ i, g i • f i := by
      simp only [Rat.smul_def, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hg, mul_zero]

/-- The normalized evaluation matrix of the boundary-wedge periodic pencil. -/
noncomputable def boundaryWedgePencilMatrix (τ : ℂ) (r s : ℕ) :
    BoundaryWedgeFacetIndex r s → PPBoundaryWedgeVertex r s → ℂ
  | Sum.inl u, none => τ ^ r / τ ^ (u : ℕ)
  | Sum.inl u, some (Sum.inl i) => τ ^ (i : ℕ) / τ ^ (u : ℕ)
  | Sum.inl _, some (Sum.inr _) => 0
  | Sum.inr u, none => τ ^ s / τ ^ (u : ℕ)
  | Sum.inr u, some (Sum.inr i) => τ ^ (i : ℕ) / τ ^ (u : ℕ)
  | Sum.inr _, some (Sum.inl _) => 0

/-- The two-coordinate translation vectors underlying the boundary-wedge pencil. -/
noncomputable def boundaryWedgePencilVector (τ : ℂ) (r s : ℕ) :
    PPBoundaryWedgeVertex r s → Fin 2 → ℂ := fun v =>
  ![(wedgeVec τ r s v).1, (wedgeVec τ r s v).2]

/-- The normalized left- and right-coordinate pencil forms. -/
noncomputable def boundaryWedgePencilForm (τ : ℂ) {r s : ℕ} :
    BoundaryWedgeFacetIndex r s → Fin 2 → ℂ
  | Sum.inl u => ![0, (τ ^ (u : ℕ))⁻¹]
  | Sum.inr u => ![(τ ^ (u : ℕ))⁻¹, 0]

theorem boundaryWedgePencilVector_linearIndependent {τ : ℂ}
    (hτ : Transcendental ℚ τ) (r s : ℕ) :
    LinearIndependent ℚ (boundaryWedgePencilVector τ r s) := by
  let e : (ℂ × ℂ) ≃ₗ[ℚ] (Fin 2 → ℂ) :=
    (LinearEquiv.piFinTwo ℚ (fun _ => ℂ)).symm
  have h := (wedge_realization_linearIndependent hτ r s).map' e.toLinearMap e.ker
  simpa [e, boundaryWedgePencilVector] using! h

theorem boundaryWedgePencil_evaluation (τ : ℂ) (r s : ℕ) :
    (fun B v => ∑ i, boundaryWedgePencilForm τ B i *
      boundaryWedgePencilVector τ r s v i) = boundaryWedgePencilMatrix τ r s := by
  funext B v
  rcases B with u | u <;> rcases v with _ | (i | j) <;>
    simp [boundaryWedgePencilForm, boundaryWedgePencilVector, boundaryWedgePencilMatrix,
      wedgeVec, Fin.sum_univ_two, div_eq_mul_inv, mul_comm]

theorem boundaryWedgePencilMatrix_ppAdmissible {τ : ℂ} (hτ : Transcendental ℚ τ)
    (r s : ℕ) :
    PPAdmissible (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) (boundaryWedgePencilMatrix τ r s) := by
  have hτ0 : τ ≠ 0 := by
    intro h
    subst τ
    exact hτ isAlgebraic_zero
  intro B
  constructor
  · intro v hv
    rcases B with u | u
    · rcases v with _ | (i | j)
      · simp [boundaryWedgeFacet] at hv
      · have hi : i = u := by simpa [boundaryWedgeFacet] using hv
        subst i
        exact ⟨1, by simp [boundaryWedgePencilMatrix, hτ0]⟩
      · exact ⟨0, by simp [boundaryWedgePencilMatrix]⟩
    · rcases v with _ | (i | j)
      · simp [boundaryWedgeFacet] at hv
      · exact ⟨0, by simp [boundaryWedgePencilMatrix]⟩
      · have hj : j = u := by simpa [boundaryWedgeFacet] using hv
        subst j
        exact ⟨1, by simp [boundaryWedgePencilMatrix, hτ0]⟩
  · rcases B with u | u
    · apply linearIndependent_of_mul_eq_transcendental_powers
        (τ := τ) (c := τ ^ (u : ℕ)) hτ
        (boundaryWedgeLeftFacetExponent (s := s) u)
        (boundaryWedgeLeftFacetExponent_injective u)
      intro i
      rcases i with _ | ⟨(_ | (j | k)), hj⟩
      · simp [boundaryWedgeLeftFacetExponent]
      · change τ ^ (u : ℕ) * (τ ^ r / τ ^ (u : ℕ)) = τ ^ r
        field_simp [pow_ne_zero _ hτ0]
      · change τ ^ (u : ℕ) * (τ ^ (j : ℕ) / τ ^ (u : ℕ)) = τ ^ (j : ℕ)
        field_simp [pow_ne_zero _ hτ0]
      · simp [boundaryWedgeFacet] at hj
    · apply linearIndependent_of_mul_eq_transcendental_powers
        (τ := τ) (c := τ ^ (u : ℕ)) hτ
        (boundaryWedgeRightFacetExponent (r := r) u)
        (boundaryWedgeRightFacetExponent_injective u)
      intro i
      rcases i with _ | ⟨(_ | (j | k)), hj⟩
      · simp [boundaryWedgeRightFacetExponent]
      · change τ ^ (u : ℕ) * (τ ^ s / τ ^ (u : ℕ)) = τ ^ s
        field_simp [pow_ne_zero _ hτ0]
      · simp [boundaryWedgeFacet] at hj
      · change τ ^ (u : ℕ) * (τ ^ (k : ℕ) / τ ^ (u : ℕ)) = τ ^ (k : ℕ)
        field_simp [pow_ne_zero _ hτ0]

/-- Every boundary wedge has a periodic-pencil separation in two complex coordinates. -/
theorem boundaryWedge_ppDim_le_two {r s : ℕ} :
    ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) ≤ 2 := by
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  apply Nat.sInf_le
  refine ⟨boundaryWedgePencilVector τ r s,
    boundaryWedgePencilVector_linearIndependent hτ r s,
    boundaryWedgePencilForm τ, ?_⟩
  rw [boundaryWedgePencil_evaluation]
  exact boundaryWedgePencilMatrix_ppAdmissible hτ r s

/-- A boundary wedge with two noncentral vertices in each block cannot be represented by a
one-dimensional periodic pencil.  Two distinct vertices outside one left facet would both be
rational multiples of the same scalar, contradicting global `ℚ`-independence. -/
theorem boundaryWedge_two_le_ppDim {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    2 ≤ ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) := by
  rw [ppDim]
  apply le_csInf
  · obtain ⟨τ, hτ⟩ := exists_transcendental_complex
    refine ⟨2, boundaryWedgePencilVector τ r s,
      boundaryWedgePencilVector_linearIndependent hτ r s,
      boundaryWedgePencilForm τ, ?_⟩
    rw [boundaryWedgePencil_evaluation]
    exact boundaryWedgePencilMatrix_ppAdmissible hτ r s
  · intro d hd
    rcases hd with ⟨a, ha, U, hPP⟩
    by_contra hnot
    have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl
    · apply ha.ne_zero (none : PPBoundaryWedgeVertex r s)
      funext i
      exact Fin.elim0 i
    · let u : Fin r := ⟨0, by omega⟩
      let j₀ : Fin s := ⟨0, by omega⟩
      let j₁ : Fin s := ⟨1, by omega⟩
      let B : BoundaryWedgeFacetIndex r s := Sum.inl u
      let v₀ : PPBoundaryWedgeVertex r s := some (Sum.inr j₀)
      let v₁ : PPBoundaryWedgeVertex r s := some (Sum.inr j₁)
      have hv₀ : v₀ ∉ boundaryWedgeFacet B := by
        simp [v₀, B, boundaryWedgeFacet]
      have hv₁ : v₁ ∉ boundaryWedgeFacet B := by
        simp [v₁, B, boundaryWedgeFacet]
      obtain ⟨z₀, hz₀⟩ := (hPP B).1 v₀ hv₀
      obtain ⟨z₁, hz₁⟩ := (hPP B).1 v₁ hv₁
      have hcenterMem : none ∈ boundaryWedgeFacet B := by
        simp [B]
      have hcenter := (hPP B).2.ne_zero (some ⟨none, hcenterMem⟩)
      have hcenter' : U B 0 * a none 0 ≠ 0 := by
        simpa using hcenter
      have hU : U B 0 ≠ 0 := fun h => hcenter' (by simp [h])
      have hz₀' : U B 0 * a v₀ 0 = (z₀ : ℂ) := by
        simpa using hz₀
      have hz₁' : U B 0 * a v₁ 0 = (z₁ : ℂ) := by
        simpa using hz₁
      have ha₀ : a v₀ 0 = (z₀ : ℂ) / U B 0 := by
        apply (eq_div_iff hU).2
        simpa [mul_comm] using hz₀'
      have ha₁ : a v₁ 0 = (z₁ : ℂ) / U B 0 := by
        apply (eq_div_iff hU).2
        simpa [mul_comm] using hz₁'
      let e : Fin 2 → PPBoundaryWedgeVertex r s := ![v₀, v₁]
      have he : Function.Injective e := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [e, v₀, v₁, j₀, j₁]
      have hpair : LinearIndependent ℚ ![a v₀, a v₁] := by
        have heval : a ∘ e = ![a v₀, a v₁] := by
          funext i
          fin_cases i <;> rfl
        rw [← heval]
        exact ha.comp e he
      have hrel : (z₁ : ℚ) • a v₀ + (-(z₀ : ℚ)) • a v₁ = 0 := by
        funext i
        fin_cases i
        simp only [Pi.add_apply, Pi.smul_apply, Rat.smul_def, Pi.zero_apply]
        push_cast
        change (z₁ : ℂ) * a v₀ 0 + -(z₀ : ℂ) * a v₁ 0 = 0
        rw [ha₀, ha₁]
        field_simp [hU]
        ring
      have hz := hpair.eq_zero_of_pair hrel
      have hz₀q : (z₀ : ℚ) = 0 := by simpa using hz.2
      have hz₀c : (z₀ : ℂ) = 0 := by exact_mod_cast hz₀q
      have ha₀zero : a v₀ 0 = 0 := by simp [ha₀, hz₀c]
      apply ha.ne_zero v₀
      funext i
      fin_cases i
      exact ha₀zero

/-- **Exact periodic-pencil dimension of every nondegenerate boundary wedge.** -/
theorem boundaryWedge_ppDim_eq_two {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ppDim (boundaryWedgeFacet : BoundaryWedgeFacetIndex r s →
      Finset (PPBoundaryWedgeVertex r s)) = 2 := by
  exact Nat.le_antisymm boundaryWedge_ppDim_le_two (boundaryWedge_two_le_ppDim hr hs)

end GaloisForLFunctions
