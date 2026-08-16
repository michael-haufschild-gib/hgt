import GaloisForLFunctions.HTGeometry.StabilizerTwoDesignCollision

/-!
# A Hermitian idempotent of trace one is a pure state

Its eigenvalues are zero or one and total one, so exactly one eigenvector survives and the matrix
acts as the orthogonal projection onto that vector.  Its diagonal in any state is therefore the
squared overlap with that vector.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section PureState

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem mulVec_finsetSum {ι : Type*} (A : Matrix α α ℂ) (s : Finset ι) (c : ι → ℂ)
    (v : ι → α → ℂ) : A *ᵥ (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k • (A *ᵥ v k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, ih]
      congr 1
      funext x
      simp only [mulVec_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring

theorem mulVec_smul_vec (A : Matrix α α ℂ) (c : ℂ) (v : α → ℂ) :
    A *ᵥ (c • v) = c • (A *ᵥ v) := by
  funext x
  simp only [mulVec_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **A Hermitian idempotent of trace one is a pure state.** -/
theorem exists_pure_state_of_projector {ρ : Matrix α α ℂ} (hherm : ρ.IsHermitian)
    (hidem : ρ * ρ = ρ) (htrace : Matrix.trace ρ = 1) :
    ∃ χ : α → ℂ, (∑ x, ‖χ x‖ ^ 2) = 1 ∧
      ∀ ψ : α → ℂ, matDiag ρ ψ = ((finitePureStateFidelity ψ χ : ℝ) : ℂ) := by
  classical
  set f : α → α → ℂ := hermitianEigenBasis ρ hherm with hf
  set lam : α → ℝ := hherm.eigenvalues with hlam
  have hbasis : IsOrthoEigenBasis ρ f lam := isOrthoEigenBasis_hermitian ρ hherm
  have hfne : ∀ k, f k ≠ 0 := by
    intro k hk
    have h := hbasis.orth k k
    rw [hk, if_pos rfl] at h
    simp [finiteComplexInner] at h
  have hsq : ∀ k, lam k * lam k = lam k := by
    intro k
    have h1 : ρ *ᵥ (ρ *ᵥ f k) = ((lam k : ℝ) : ℂ) • (((lam k : ℝ) : ℂ) • f k) := by
      calc ρ *ᵥ (ρ *ᵥ f k) = ρ *ᵥ (((lam k : ℝ) : ℂ) • f k) := by rw [hbasis.eigen k]
        _ = ((lam k : ℝ) : ℂ) • (ρ *ᵥ f k) := mulVec_smul_vec ρ _ _
        _ = ((lam k : ℝ) : ℂ) • (((lam k : ℝ) : ℂ) • f k) := by rw [hbasis.eigen k]
    rw [Matrix.mulVec_mulVec, hidem, hbasis.eigen k, smul_smul] at h1
    have h2 : (((lam k : ℝ) : ℂ) * ((lam k : ℝ) : ℂ) - ((lam k : ℝ) : ℂ)) • f k = 0 := by
      rw [sub_smul, ← h1, sub_self]
    have h3 : ((lam k : ℝ) : ℂ) * ((lam k : ℝ) : ℂ) - ((lam k : ℝ) : ℂ) = 0 :=
      (smul_eq_zero.mp h2).resolve_right (hfne k)
    have h4 : (((lam k * lam k : ℝ)) : ℂ) = (((lam k : ℝ)) : ℂ) := by
      push_cast
      linear_combination h3
    exact_mod_cast h4
  have hzeroone : ∀ k, lam k = 0 ∨ lam k = 1 := by
    intro k
    have h : lam k * (lam k - 1) = 0 := by linear_combination hsq k
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  have hsumreal : (∑ k, lam k) = 1 := by
    have hc : (∑ k, ((lam k : ℝ) : ℂ)) = 1 := by
      have ht := Matrix.IsHermitian.trace_eq_sum_eigenvalues hherm
      rw [htrace] at ht
      rw [hlam]
      exact ht.symm
    exact_mod_cast hc
  set s : Finset α := Finset.univ.filter fun k => lam k = 1 with hs
  have hcard : (s.card : ℝ) = 1 := by
    have hsplit : (∑ k ∈ s, lam k) +
        (∑ k ∈ Finset.univ.filter fun k => ¬ (lam k = 1), lam k) = ∑ k, lam k :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have h1 : (∑ k ∈ s, lam k) = (s.card : ℝ) := by
      rw [Finset.sum_congr rfl fun k hk => (Finset.mem_filter.mp hk).2, Finset.sum_const,
        nsmul_eq_mul, mul_one]
    have h2 : (∑ k ∈ Finset.univ.filter fun k => ¬ (lam k = 1), lam k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_filter] at hk
      exact (hzeroone k).resolve_right hk.2
    rw [h1, h2, add_zero, hsumreal] at hsplit
    exact hsplit
  have hcardnat : s.card = 1 := by exact_mod_cast hcard
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcardnat
  have hk₀mem : k₀ ∈ s := by rw [hk₀]; exact Finset.mem_singleton_self k₀
  have hlamk₀ : lam k₀ = 1 := (Finset.mem_filter.mp hk₀mem).2
  have hlamother : ∀ k, k ≠ k₀ → lam k = 0 := by
    intro k hk
    refine (hzeroone k).resolve_right fun hcon => ?_
    have : k ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hcon⟩
    rw [hk₀, Finset.mem_singleton] at this
    exact hk this
  refine ⟨f k₀, ?_, ?_⟩
  · have h := hbasis.orth k₀ k₀
    rw [if_pos rfl, finiteComplexInner_self] at h
    exact_mod_cast h
  · intro ψ
    have hact : ρ *ᵥ ψ = (finiteComplexInner (f k₀) ψ) • f k₀ := by
      have hc := hbasis.complete ψ
      calc ρ *ᵥ ψ = ρ *ᵥ (∑ k, finiteComplexInner (f k) ψ • f k) := by rw [hc]
        _ = ∑ k, finiteComplexInner (f k) ψ • (ρ *ᵥ f k) := mulVec_finsetSum ρ _ _ _
        _ = ∑ k, finiteComplexInner (f k) ψ • (((lam k : ℝ) : ℂ) • f k) :=
            Finset.sum_congr rfl fun k _ => by rw [hbasis.eigen k]
        _ = (finiteComplexInner (f k₀) ψ) • f k₀ := by
            rw [Finset.sum_eq_single k₀]
            · rw [hlamk₀]
              simp
            · intro k _ hk
              rw [hlamother k hk]
              simp
            · intro hcon
              exact absurd (Finset.mem_univ k₀) hcon
    rw [matDiag, hact, finiteComplexInner_smul_right,
      finiteComplexInner_conj_symm (f k₀) ψ, finitePureStateFidelity]
    have hz := Complex.mul_conj (finiteComplexInner ψ (f k₀))
    rw [Complex.sq_norm]
    rw [← hz]
    ring

end PureState

section Projector

variable {n : ℕ} {b : Fin n → PauliSymp n}

theorem conj_signOf (z : ZMod 2) : (starRingEnd ℂ) (signOf z) = signOf z := by
  rcases zmodTwo_cases z with rfl | rfl <;> simp [signOf]

theorem stabFactor_isHermitian (ε : Fin n → ZMod 2) (i : Fin n) :
    (stabFactor b ε i).IsHermitian := by
  rw [Matrix.IsHermitian, stabFactor, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul]
  have hQ : (pauliMat (b i))ᴴ = pauliMat (b i) := finitePauliMatrix_isHermitian _
  rw [hQ, RCLike.star_def, conj_signOf]
  congr 1
  rw [map_inv₀, Complex.conj_ofNat]

theorem stabFactor_mul_self (ε : Fin n → ZMod 2) (i : Fin n) :
    stabFactor b ε i * stabFactor b ε i = stabFactor b ε i := by
  have hexp : ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i)) *
      ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i)) =
      (2 : ℂ) • ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, pauliMat_mul_self, signOf_sq, one_smul,
      two_smul, smul_add]
    module
  show ((2 : ℂ)⁻¹ • ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i))) *
      ((2 : ℂ)⁻¹ • ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i))) =
      (2 : ℂ)⁻¹ • ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i))
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hexp, smul_smul]
  congr 1
  norm_num

theorem commute_stabFactor_stabProjectorOn (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) (a : Fin n) (T : Finset (Fin n)) :
    Commute (stabFactor b ε a) (stabProjectorOn b hb ε T) := by
  classical
  induction T using Finset.induction with
  | empty =>
      rw [stabProjectorOn_empty]
      exact Commute.one_right _
  | insert c T hc ih =>
      rw [stabProjectorOn_insert hb ε hc]
      exact (commute_stabFactor hb ε a c).mul_right ih

theorem stabProjectorOn_mul_self (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2)
    (T : Finset (Fin n)) :
    stabProjectorOn b hb ε T * stabProjectorOn b hb ε T = stabProjectorOn b hb ε T := by
  classical
  induction T using Finset.induction with
  | empty =>
      rw [stabProjectorOn_empty, Matrix.one_mul]
  | insert a T ha ih =>
      rw [stabProjectorOn_insert hb ε ha]
      have hcomm := commute_stabFactor_stabProjectorOn hb ε a T
      calc (stabFactor b ε a * stabProjectorOn b hb ε T) *
            (stabFactor b ε a * stabProjectorOn b hb ε T)
          = stabFactor b ε a * (stabProjectorOn b hb ε T * stabFactor b ε a) *
              stabProjectorOn b hb ε T := by
            simp only [mul_assoc]
        _ = stabFactor b ε a * (stabFactor b ε a * stabProjectorOn b hb ε T) *
              stabProjectorOn b hb ε T := by rw [hcomm.eq]
        _ = (stabFactor b ε a * stabFactor b ε a) *
              (stabProjectorOn b hb ε T * stabProjectorOn b hb ε T) := by
            simp only [mul_assoc]
        _ = stabFactor b ε a * stabProjectorOn b hb ε T := by
            rw [stabFactor_mul_self, ih]

theorem stabProjectorOn_isHermitian (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2)
    (T : Finset (Fin n)) : (stabProjectorOn b hb ε T).IsHermitian := by
  classical
  induction T using Finset.induction with
  | empty =>
      rw [stabProjectorOn_empty]
      exact Matrix.isHermitian_one
  | insert a T ha ih =>
      rw [stabProjectorOn_insert hb ε ha, Matrix.IsHermitian, Matrix.conjTranspose_mul,
        ih, stabFactor_isHermitian]
      exact (commute_stabFactor_stabProjectorOn hb ε a T).eq.symm

theorem trace_pauliMat (v : PauliSymp n) :
    Matrix.trace (pauliMat v) = if v = 0 then (2 : ℂ) ^ n else 0 := by
  classical
  have h := trace_star_finitePauliMatrix_mul (pauliOf v) (fun _ : Fin n => (none : Option (Fin 3)))
  rw [finitePauliMatrix_const_none, Matrix.mul_one] at h
  have hstar : star (finitePauliMatrix (pauliOf v)) = finitePauliMatrix (pauliOf v) :=
    finitePauliMatrix_isHermitian _
  rw [hstar, Fintype.card_fin] at h
  rw [pauliMat, h]
  by_cases hv : v = 0
  · subst hv
    rw [if_pos rfl, if_pos]
    exact pauliOf_zero
  · rw [if_neg hv, if_neg]
    intro hcon
    exact hv (pauliOf_injective (hcon.trans pauliOf_zero.symm))

theorem stabSign_empty (hb : ∀ i j, symForm (b i) (b j) = 0) : stabSign b hb ∅ = 1 := by
  have hprod : stabProd b hb ∅ = (1 : ℂ) • pauliMat (labSum b ∅) := by
    rw [stabProd_empty, labSum, Finset.sum_empty, pauliMat_zero, one_smul]
  rw [stabSign, hprod, pauliCoeff_smul_pauliMat]

theorem labSum_eq_zero_iff (hbasis : IsLagrBasis b) (S : Finset (Fin n)) :
    labSum b S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    have hzero : labSum b ∅ = 0 := by rw [labSum, Finset.sum_empty]
    exact injOn_subsetSum hbasis (Finset.mem_coe.mpr (Finset.mem_univ S))
      (Finset.mem_coe.mpr (Finset.mem_univ ∅)) (h.trans hzero.symm)
  · intro h
    rw [h, labSum, Finset.sum_empty]

theorem trace_stabProjector (hbasis : IsLagrBasis b) (ε : Fin n → ZMod 2) :
    Matrix.trace (stabProjector b hbasis.1 ε) = 1 := by
  classical
  rw [stabProjector_eq_smul_expansion, Matrix.trace_smul, Matrix.trace_sum]
  have hterm : ∀ S : Finset (Fin n),
      Matrix.trace (signOf (∑ i ∈ S, ε i) • stabProd b hbasis.1 S) =
        if S = ∅ then (2 : ℂ) ^ n else 0 := by
    intro S
    rw [stabProd_eq_smul, smul_smul, Matrix.trace_smul, trace_pauliMat, smul_eq_mul]
    by_cases hS : S = ∅
    · subst hS
      rw [if_pos (labSum_eq_zero_iff hbasis ∅ |>.mpr rfl), if_pos rfl, Finset.sum_empty,
        stabSign_empty, signOf, if_pos rfl]
      ring
    · rw [if_neg (fun hcon => hS ((labSum_eq_zero_iff hbasis S).mp hcon)), if_neg hS, mul_zero]
  rw [Finset.sum_congr rfl fun S _ => hterm S, Finset.sum_ite_eq' Finset.univ (∅ : Finset (Fin n)),
    if_pos (Finset.mem_univ _), smul_eq_mul]
  field_simp

/-- **A stabilizer state is a pure state.** -/
theorem exists_stabilizer_pure_state (hbasis : IsLagrBasis b) (ε : Fin n → ZMod 2) :
    ∃ χ : FiniteQubitConfiguration (Fin n) → ℂ, (∑ x, ‖χ x‖ ^ 2) = 1 ∧
      ∀ ψ, matDiag (stabProjector b hbasis.1 ε) ψ =
        ((finitePureStateFidelity ψ χ : ℝ) : ℂ) :=
  exists_pure_state_of_projector (stabProjectorOn_isHermitian hbasis.1 ε Finset.univ)
    (stabProjectorOn_mul_self hbasis.1 ε Finset.univ) (trace_stabProjector hbasis ε)

end Projector

section Capstone

variable {n : ℕ}

/-- **The exact stabilizer two-design collision law.**  Against any family of unit states, the
collision of a stabilizer state averages to `2/(D+1)`. -/
theorem exists_stabilizer_states_collision_eq
    (e : FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ)
    (hunit : ∀ j, (∑ x, ‖e j x‖ ^ 2) = 1) :
    ∃ χ : (Fin n → PauliSymp n) → (Fin n → ZMod 2) →
        (FiniteQubitConfiguration (Fin n) → ℂ),
      (∀ b ∈ lagrBases n, ∀ ε, (∑ x, ‖χ b ε x‖ ^ 2) = 1) ∧
        ((2 : ℝ) ^ n + 1) * (∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
            ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2) =
          ((lagrBases n).card : ℝ) * 2 ^ (n + 1) := by
  classical
  choose! χ hunitχ hdiag using fun (b : Fin n → PauliSymp n) (hbasis : IsLagrBasis b)
    (ε : Fin n → ZMod 2) => exists_stabilizer_pure_state hbasis ε
  refine ⟨χ, fun b hb ε => hunitχ b (mem_lagrBases.mp hb) ε, ?_⟩
  have hcomplex := sum_lagrBases_sign_collision e hunit
  have hterm : ∀ b ∈ lagrBases n, (∑ ε : Fin n → ZMod 2,
      ∑ j, (matDiag (stabProjectorOf b ε) (e j)) ^ 2) =
      ((∑ ε : Fin n → ZMod 2,
        ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2 : ℝ) : ℂ) := by
    intro b hb
    have hbasis := mem_lagrBases.mp hb
    push_cast
    refine Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun j _ => ?_
    rw [stabProjectorOf_eq hbasis.1, hdiag b hbasis ε (e j)]
  rw [Finset.sum_congr rfl hterm] at hcomplex
  have hcast : (((2 : ℝ) ^ n + 1 : ℝ) : ℂ) *
      ((∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
        ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2 : ℝ) : ℂ) =
      ((((lagrBases n).card : ℝ) * 2 ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    push_cast at hcomplex
    rw [← hcomplex]
  exact_mod_cast hcast

end Capstone

end GaloisForLFunctions.HTGeometry
