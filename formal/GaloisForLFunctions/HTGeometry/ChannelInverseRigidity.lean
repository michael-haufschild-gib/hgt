import GaloisForLFunctions.HTGeometry.MatrixStarAutomorphismInner
import GaloisForLFunctions.HTGeometry.QuantumChannelDiamond

/-!
# A channel with a channel inverse is a unitary conjugation

Corollary C of the Markovian return law.  If a quantum channel `Φ` has a two-sided inverse which
is again a quantum channel, then `Φ(X) = W X Wᴴ` for a unitary `W`.

The proof normalises: `P = Φ(1)` is positive definite because a positive linear functional
annihilating the unit annihilates everything, and `Φ` is onto.  Conjugating by `P^{-1/2}` turns
`Φ` into a *unital* completely positive map whose inverse is again unital and completely positive,
so the Kadison--Schwarz inequality is saturated in both directions and the normalised map is a
star automorphism of the matrix algebra, hence inner.  Trace preservation then forces the
remaining positive factor to be one.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Two elementary facts about positive matrices -/

/-- A positive semidefinite matrix is dominated by its trace times the unit. -/
theorem posSemidef_le_trace_smul_one {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A ≤ ((A.trace.re : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
  classical
  set U : Matrix n n ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUmem : U ∈ unitary (Matrix n n ℂ) := hA.isHermitian.eigenvectorUnitary.2
  have hUUH : Uᴴ * U = 1 := by
    have := hUmem.1
    simpa [Matrix.star_eq_conjTranspose] using this
  have hUHU : U * Uᴴ = 1 := by
    have := hUmem.2
    simpa [Matrix.star_eq_conjTranspose] using this
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) with hDdef
  have hAeq : A = U * D * Uᴴ := hermitian_eq_conj_diagonal hA.isHermitian
  set t : ℝ := A.trace.re with htdef
  have htsum : t = ∑ i, hA.isHermitian.eigenvalues i := trace_re_eq_sum_eigenvalues _
  have hdiff : ((t : ℝ) : ℂ) • (1 : Matrix n n ℂ) - A
      = U * (Matrix.diagonal (fun i => ((t - hA.isHermitian.eigenvalues i : ℝ) : ℂ))) * Uᴴ := by
    have hone : U * (1 : Matrix n n ℂ) * Uᴴ = 1 := by rw [Matrix.mul_one, hUHU]
    have hdi : Matrix.diagonal (fun i => ((t - hA.isHermitian.eigenvalues i : ℝ) : ℂ))
        = ((t : ℝ) : ℂ) • (1 : Matrix n n ℂ) - D := by
      rw [hDdef]
      ext p q
      by_cases h : p = q <;> simp [h]
    rw [hdi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hone, hAeq]
  rw [Matrix.le_iff, hdiff]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  refine Complex.zero_le_real.mpr ?_
  rw [sub_nonneg, htsum]
  exact Finset.single_le_sum (f := hA.isHermitian.eigenvalues)
    (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- A complex-linear functional vanishing on positive matrices vanishes. -/
theorem linear_eq_zero_of_eqOn_posSemidef {f : Matrix n n ℂ → ℂ}
    (hadd : ∀ X Y, f (X + Y) = f X + f Y) (hsmul : ∀ (c : ℂ) (X), f (c • X) = c * f X)
    (h : ∀ A : Matrix n n ℂ, A.PosSemidef → f A = 0) (X : Matrix n n ℂ) : f X = 0 := by
  have hzero : f 0 = 0 := by simpa using hsmul 0 0
  have hsub : ∀ X Y, f (X - Y) = f X - f Y := by
    intro X Y
    have hneg : f (-Y) = -f Y := by
      have := hsmul (-1) Y
      simpa using this
    rw [sub_eq_add_neg, hadd, hneg, ← sub_eq_add_neg]
  have hherm : ∀ A : Matrix n n ℂ, A.IsHermitian → f A = 0 := by
    intro A hA
    rw [← hermPos_sub_hermNeg hA, hsub, h _ (hermPos_posSemidef A), h _ (hermNeg_posSemidef A)]
    ring
  obtain ⟨A, B, hA, hB, hX⟩ := QuantumChannel.exists_hermitian_decomposition X
  rw [hX, hadd, hsmul, hherm A hA, hherm B hB]
  ring

/-- A matrix pairing with the trace like the unit is the unit. -/
theorem eq_one_of_trace_mul_eq {M : Matrix n n ℂ} (h : ∀ X, (M * X).trace = X.trace) :
    M = 1 := by
  ext i j
  have hX := h (Matrix.single j i (1 : ℂ))
  have hl : (M * Matrix.single j i (1 : ℂ)).trace = M i j := by
    rw [Matrix.trace]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hc; exact absurd (Finset.mem_univ j) hc
    · intro b _ hb
      rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_zero]
      intro r _
      simp [Ne.symm hb]
    · intro hc; exact absurd (Finset.mem_univ i) hc
  have hr : (Matrix.single j i (1 : ℂ)).trace = (1 : Matrix n n ℂ) i j := by
    rw [Matrix.trace]
    by_cases h' : i = j
    · subst h'
      rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply_eq]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro hc; exact absurd (Finset.mem_univ i) hc
    · rw [Finset.sum_eq_zero, Matrix.one_apply_ne h']
      intro b _
      rw [Matrix.diag_apply, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h' rfl
  rw [hl, hr] at hX
  exact hX

/-! ## Corollary C -/

namespace QuantumChannel

/-- The rank-one positive matrix built from a vector. -/
def rankOne (v : n → ℂ) : Matrix n n ℂ := Matrix.of fun p q => v p * star (v q)

omit [DecidableEq n] in
theorem rankOne_mulVec (v : n → ℂ) : rankOne v *ᵥ v = (star v ⬝ᵥ v) • v := by
  funext p
  rw [Matrix.mulVec, dotProduct, dotProduct]
  simp only [rankOne, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- **The unit image of a channel with a channel inverse is nonsingular.** -/
theorem det_map_one_ne_zero (Φ Ψ : QuantumChannel n)
    (hΦΨ : ∀ X, Φ.map (Ψ.map X) = X) : (Φ.map 1).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hvP⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hP0 : star v ⬝ᵥ (Φ.map 1) *ᵥ v = 0 := by rw [hvP, dotProduct_zero]
  have hfvanish : ∀ A : Matrix n n ℂ, A.PosSemidef → star v ⬝ᵥ (Φ.map A) *ᵥ v = 0 := by
    intro A hA
    have hpos : 0 ≤ star v ⬝ᵥ (Φ.map A) *ᵥ v := (Φ.positive hA).dotProduct_mulVec_nonneg v
    have hle : Φ.map A ≤ ((A.trace.re : ℝ) : ℂ) • Φ.map 1 := by
      have := Φ.isPositiveTP.pos
      have hmono : Φ.map A ≤ Φ.map (((A.trace.re : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := by
        rw [Matrix.le_iff, ← Φ.isPositiveTP.map_sub]
        exact Φ.positive (Matrix.le_iff.mp (posSemidef_le_trace_smul_one hA))
      rwa [Φ.map_smul] at hmono
    have hup : star v ⬝ᵥ (Φ.map A) *ᵥ v ≤ star v ⬝ᵥ (((A.trace.re : ℝ) : ℂ) • Φ.map 1) *ᵥ v := by
      have hd := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg v
      rw [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hd
      exact hd
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hP0, mul_zero] at hup
    exact le_antisymm hup hpos
  have hall : ∀ X : Matrix n n ℂ, star v ⬝ᵥ (Φ.map X) *ᵥ v = 0 := by
    refine linear_eq_zero_of_eqOn_posSemidef ?_ ?_ hfvanish
    · intro X Y
      rw [Φ.map_add, Matrix.add_mulVec, dotProduct_add]
    · intro c X
      rw [Φ.map_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcontra := hall (Ψ.map (rankOne v))
  rw [hΦΨ, rankOne_mulVec, dotProduct_smul, smul_eq_mul] at hcontra
  have hpos : (0 : ℂ) < star v ⬝ᵥ v := Matrix.dotProduct_star_self_pos_iff.mpr hv0
  exact absurd hcontra (by positivity)

/-- **Corollary C.**  A quantum channel whose two-sided inverse is again a quantum channel is a
unitary conjugation. -/
theorem exists_unitary_of_channel_inverse (Φ Ψ : QuantumChannel n)
    (hΨΦ : ∀ X, Ψ.map (Φ.map X) = X) (hΦΨ : ∀ X, Φ.map (Ψ.map X) = X) :
    ∃ W : Matrix n n ℂ, W ∈ unitary (Matrix n n ℂ) ∧ ∀ X, Φ.map X = W * X * star W := by
  classical
  have honePSD : (1 : Matrix n n ℂ).PosSemidef := by
    rw [← Matrix.diagonal_one]
    exact Matrix.posSemidef_diagonal_iff.mpr fun _ => zero_le_one
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix n n ℂ, P = Φ.map 1 := ⟨_, rfl⟩
  have hPpsd : P.PosSemidef := by rw [hPdef]; exact Φ.positive honePSD
  have hPdet : P.det ≠ 0 := by rw [hPdef]; exact Φ.det_map_one_ne_zero Ψ hΦΨ
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix n n ℂ, S = CFC.sqrt P := ⟨_, rfl⟩
  have hSstar : star S = S := by
    rw [hSdef]
    exact (CFC.sqrt_nonneg P).star_eq
  have hSS : S * S = P := by
    rw [hSdef]
    have := CFC.sq_sqrt P hPpsd.nonneg
    rwa [pow_two] at this
  have hSdetUnit : IsUnit S.det := by
    have hd : S.det * S.det = P.det := by rw [← Matrix.det_mul, hSS]
    refine isUnit_iff_ne_zero.mpr fun hz => hPdet ?_
    rw [← hd, hz, zero_mul]
  obtain ⟨R, hRdef⟩ : ∃ R : Matrix n n ℂ, R = S⁻¹ := ⟨_, rfl⟩
  have hRS : R * S = 1 := by rw [hRdef]; exact Matrix.nonsing_inv_mul S hSdetUnit
  have hSR : S * R = 1 := by rw [hRdef]; exact Matrix.mul_nonsing_inv S hSdetUnit
  have hSconj : Sᴴ = S := by simpa [Matrix.star_eq_conjTranspose] using hSstar
  have hRstar : star R = R := by
    show Rᴴ = R
    rw [hRdef, Matrix.conjTranspose_nonsing_inv, hSconj]
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : Matrix n n ℂ → Matrix n n ℂ,
      Θ = fun X => R * Φ.map X * star R := ⟨_, rfl⟩
  obtain ⟨Ξ, hΞdef⟩ : ∃ Ξ : Matrix n n ℂ → Matrix n n ℂ,
      Ξ = fun Y => Ψ.map (S * Y * star S) := ⟨_, rfl⟩
  have hΘcp : IsCP Θ := by
    refine ⟨?_, ?_, ?_⟩
    · intro X Y
      rw [hΘdef]
      simp [Φ.map_add, Matrix.mul_add, Matrix.add_mul]
    · intro c X
      rw [hΘdef]
      simp [Φ.map_smul]
    · intro m _ _ Z hZ
      have hstep : amplify Θ m Z
          = (R ⊗ₖ (1 : Matrix m m ℂ)) * (amplify Φ.map m Z)
            * star (R ⊗ₖ (1 : Matrix m m ℂ)) := by
        rw [hΘdef]
        rw [show amplify (fun X => R * Φ.map X * star R) m Z
            = amplify (fun O => R * O * star R) m (amplify Φ.map m Z) from rfl]
        rw [amplify_conj]
      rw [hstep]
      have := (Φ.completelyPositive m Z hZ).mul_mul_conjTranspose_same
        (R ⊗ₖ (1 : Matrix m m ℂ))
      simpa [Matrix.star_eq_conjTranspose] using this
  have hΞcp : IsCP Ξ := by
    refine ⟨?_, ?_, ?_⟩
    · intro X Y
      rw [hΞdef]
      simp [Matrix.mul_add, Matrix.add_mul, Ψ.map_add]
    · intro c X
      rw [hΞdef]
      simp [Ψ.map_smul]
    · intro m _ _ Z hZ
      have hstep : amplify Ξ m Z
          = amplify Ψ.map m ((S ⊗ₖ (1 : Matrix m m ℂ)) * Z
            * star (S ⊗ₖ (1 : Matrix m m ℂ))) := by
        rw [hΞdef]
        rw [show amplify (fun Y => Ψ.map (S * Y * star S)) m Z
            = amplify Ψ.map m (amplify (fun O => S * O * star S) m Z) from rfl, amplify_conj]
      rw [hstep]
      refine Ψ.completelyPositive m _ ?_
      have := hZ.mul_mul_conjTranspose_same (S ⊗ₖ (1 : Matrix m m ℂ))
      simpa [Matrix.star_eq_conjTranspose] using this
  have hΘ1 : Θ 1 = 1 := by
    rw [hΘdef]
    show R * Φ.map 1 * star R = 1
    rw [hRstar, ← hPdef, ← hSS]
    calc R * (S * S) * R = (R * S) * (S * R) := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hRS, hSR, Matrix.one_mul]
  have hΞ1 : Ξ 1 = 1 := by
    rw [hΞdef]
    show Ψ.map (S * 1 * star S) = 1
    rw [hSstar, Matrix.mul_one, hSS, hPdef, hΨΦ]
  have hΞΘ : ∀ X, Ξ (Θ X) = X := by
    intro X
    rw [hΞdef, hΘdef]
    show Ψ.map (S * (R * Φ.map X * star R) * star S) = X
    rw [hRstar, hSstar]
    calc Ψ.map (S * (R * Φ.map X * R) * S)
        = Ψ.map ((S * R) * Φ.map X * (R * S)) := by
          congr 1
          simp [Matrix.mul_assoc]
      _ = X := by rw [hRS, hSR, Matrix.one_mul, Matrix.mul_one, hΨΦ]
  have hΘΞ : ∀ Y, Θ (Ξ Y) = Y := by
    intro Y
    rw [hΘdef, hΞdef]
    show R * Φ.map (Ψ.map (S * Y * star S)) * star R = Y
    rw [hΦΨ, hRstar, hSstar]
    calc R * (S * Y * S) * R = (R * S) * Y * (S * R) := by simp [Matrix.mul_assoc]
      _ = Y := by rw [hRS, hSR, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨V, hVunit, hV⟩ :=
    exists_unitary_conjugation_of_starAlgHom hΘcp.map_add hΘcp.map_smul
      (hΘcp.map_mul_of_inverse hΞcp hΘ1 hΞ1 hΞΘ hΘΞ) hΘcp.map_conjTranspose hΘ1
      (Function.LeftInverse.injective hΞΘ)
  have hΦS : ∀ X, Φ.map X = S * Θ X * S := by
    intro X
    rw [hΘdef]
    show Φ.map X = S * (R * Φ.map X * star R) * S
    rw [hRstar]
    calc Φ.map X = (S * R) * Φ.map X * (R * S) := by rw [hRS, hSR, Matrix.one_mul, Matrix.mul_one]
      _ = S * (R * Φ.map X * R) * S := by simp [Matrix.mul_assoc]
  refine ⟨S * V, ?_, ?_⟩
  · have hmap : ∀ X, Φ.map X = (S * V) * X * star (S * V) := by
      intro X
      rw [hΦS X, hV X, star_mul, hSstar]
      simp [Matrix.mul_assoc]
    have htr : ∀ X : Matrix n n ℂ, (star (S * V) * (S * V) * X).trace = X.trace := by
      intro X
      have h1 := Φ.tracePreserving X
      rw [hmap X] at h1
      rw [← h1, Matrix.trace_mul_cycle (star (S * V)) (S * V) X,
        Matrix.trace_mul_cycle X (star (S * V)) (S * V)]
    have hSV : star (S * V) * (S * V) = 1 := eq_one_of_trace_mul_eq htr
    exact ⟨hSV, mul_eq_one_comm.mpr hSV⟩
  · intro X
    rw [hΦS X, hV X, star_mul, hSstar]
    simp [Matrix.mul_assoc]

end QuantumChannel

end

end GaloisForLFunctions.HTGeometry
