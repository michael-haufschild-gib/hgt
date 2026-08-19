import Mathlib

/-!
# Connes--van Suijlekom, Appendix B: the three-dimensional cone

This module formalizes the finite real-matrix calculation in Lemma B.2 of
Connes--van Suijlekom, arXiv:2511.23257v1.  The source cone consists of

`μ(a,b,c) = [[a,c,c],[c,b,c],[c,c,a]]`.

The displayed coordinates of the compression to
`E = span ((0,1,0), (1/sqrt 2,0,1/sqrt 2))` are the source's concrete
two-dimensional model.  Subsequent declarations prove the cone equivalence
and then its extreme-ray statement.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real symmetric matrix `μ(a,b,c)` in Appendix B. -/
def connesVanSuijlekomB2Mu (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, c, c;
     c, b, c;
     c, c, a]

/-- Matrix of the Appendix-B compression in its displayed orthonormal basis of `E`. -/
def connesVanSuijlekomB2Rho (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b, Real.sqrt 2 * c;
     Real.sqrt 2 * c, a + c]

/-- The source half-space `H = {[[x,y],[y,z]] | z ≥ √2 y}`. -/
def connesVanSuijlekomB2HalfSpace (Q : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Real.sqrt 2 * Q 0 1 ≤ Q 1 1

/-- The inclusion of the Appendix-B plane `E` in the source three-space. -/
def connesVanSuijlekomB2Embed : Matrix (Fin 3) (Fin 2) ℝ :=
  !![0, (Real.sqrt 2)⁻¹;
     1, 0;
     0, (Real.sqrt 2)⁻¹]

/-- The inclusion of the odd line orthogonal to the Appendix-B plane `E`. -/
def connesVanSuijlekomB2OddEmbed : Matrix (Fin 3) (Fin 1) ℝ :=
  !![(Real.sqrt 2)⁻¹;
     0;
     -(Real.sqrt 2)⁻¹]

/-- Explicit adjoint of the inclusion of `E`. -/
def connesVanSuijlekomB2EmbedAdjoint : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, 1, 0;
     (Real.sqrt 2)⁻¹, 0, (Real.sqrt 2)⁻¹]

/-- Explicit adjoint of the inclusion of the odd line. -/
def connesVanSuijlekomB2OddEmbedAdjoint : Matrix (Fin 1) (Fin 3) ℝ :=
  !![(Real.sqrt 2)⁻¹, 0, -(Real.sqrt 2)⁻¹]

private theorem connesVanSuijlekomB2_sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

private theorem connesVanSuijlekomB2_sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

private theorem connesVanSuijlekomB2_embed_conjTranspose :
    connesVanSuijlekomB2Embedᴴ = connesVanSuijlekomB2EmbedAdjoint := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Embed, connesVanSuijlekomB2EmbedAdjoint,
      Matrix.conjTranspose_apply]

private theorem connesVanSuijlekomB2_oddEmbed_conjTranspose :
    connesVanSuijlekomB2OddEmbedᴴ = connesVanSuijlekomB2OddEmbedAdjoint := by
  ext i j
  fin_cases i
  fin_cases j <;>
    simp [connesVanSuijlekomB2OddEmbed, connesVanSuijlekomB2OddEmbedAdjoint,
      Matrix.conjTranspose_apply]

/-- In the source coordinates, the Appendix-B half-space is exactly `c ≤ a`. -/
theorem connesVanSuijlekomB2_rho_mem_halfSpace_iff (a b c : ℝ) :
    connesVanSuijlekomB2HalfSpace (connesVanSuijlekomB2Rho a b c) ↔ c ≤ a := by
  change Real.sqrt 2 * (Real.sqrt 2 * c) ≤ a + c ↔ c ≤ a
  have hsquare : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    calc
      Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
      _ = 2 := connesVanSuijlekomB2_sqrt_two_sq
  rw [← mul_assoc, hsquare]
  constructor <;> intro h <;> linarith

/-- The displayed compression coordinates recover the three source parameters. -/
theorem connesVanSuijlekomB2_rho_injective :
    Function.Injective (fun p : ℝ × ℝ × ℝ =>
      connesVanSuijlekomB2Rho p.1 p.2.1 p.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [connesVanSuijlekomB2Rho] at h00 h01 h11
  have hc : c = c' := by
    exact h01
  have ha : a = a' := by linarith
  subst a'
  subst b'
  subst c'
  rfl

/-- The inverse coordinate map from a real selfadjoint `2 × 2` matrix. -/
def connesVanSuijlekomB2RhoInverse (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ × ℝ × ℝ :=
  (Q 1 1 - Q 0 1 / Real.sqrt 2, Q 0 0, Q 0 1 / Real.sqrt 2)

/-- The explicit inverse reconstructs every real selfadjoint compressed matrix. -/
theorem connesVanSuijlekomB2_rho_inverse_apply (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.IsHermitian) :
    connesVanSuijlekomB2Rho (connesVanSuijlekomB2RhoInverse Q).1
        (connesVanSuijlekomB2RhoInverse Q).2.1
        (connesVanSuijlekomB2RhoInverse Q).2.2 = Q := by
  have h10 : Q 1 0 = Q 0 1 := by
    have h := congrFun (congrFun hQ.eq 1) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Rho, connesVanSuijlekomB2RhoInverse, h10]
  all_goals field_simp [connesVanSuijlekomB2_sqrt_two_ne_zero]

/-- Lemma B.2(i): each real selfadjoint compression has one and only one source matrix. -/
theorem connesVanSuijlekomB2_rho_existsUnique (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.IsHermitian) :
    ∃! p : ℝ × ℝ × ℝ, connesVanSuijlekomB2Rho p.1 p.2.1 p.2.2 = Q := by
  refine ⟨connesVanSuijlekomB2RhoInverse Q,
    connesVanSuijlekomB2_rho_inverse_apply Q hQ, ?_⟩
  intro p hp
  apply connesVanSuijlekomB2_rho_injective
  change connesVanSuijlekomB2Rho p.1 p.2.1 p.2.2 =
    connesVanSuijlekomB2Rho (connesVanSuijlekomB2RhoInverse Q).1
      (connesVanSuijlekomB2RhoInverse Q).2.1
      (connesVanSuijlekomB2RhoInverse Q).2.2
  rw [hp, connesVanSuijlekomB2_rho_inverse_apply Q hQ]

/-- The compression coordinates preserve addition of source parameters. -/
theorem connesVanSuijlekomB2_rho_add (a b c a' b' c' : ℝ) :
    connesVanSuijlekomB2Rho (a + a') (b + b') (c + c') =
      connesVanSuijlekomB2Rho a b c + connesVanSuijlekomB2Rho a' b' c' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Rho]
  all_goals ring

/-- The compression coordinates preserve real scalar multiplication. -/
theorem connesVanSuijlekomB2_rho_smul (r a b c : ℝ) :
    connesVanSuijlekomB2Rho (r * a) (r * b) (r * c) =
      r • connesVanSuijlekomB2Rho a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Rho]
  all_goals ring

/-- The source compression has exactly the coordinates printed in Lemma B.2. -/
theorem connesVanSuijlekomB2_compression_eq_rho (a b c : ℝ) :
    connesVanSuijlekomB2Embed.conjTranspose * connesVanSuijlekomB2Mu a b c *
        connesVanSuijlekomB2Embed =
      connesVanSuijlekomB2Rho a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Embed, connesVanSuijlekomB2Mu,
      connesVanSuijlekomB2Rho, Matrix.mul_apply,
      Fin.sum_univ_three]
  all_goals
    field_simp [connesVanSuijlekomB2_sqrt_two_ne_zero]
    rw [connesVanSuijlekomB2_sqrt_two_sq]
    ring

/-- The source matrix is the orthogonal sum of its compressed and odd components. -/
theorem connesVanSuijlekomB2_orthogonal_decomposition (a b c : ℝ) :
    connesVanSuijlekomB2Mu a b c =
      connesVanSuijlekomB2Embed * connesVanSuijlekomB2Rho a b c *
          connesVanSuijlekomB2Embed.conjTranspose +
        (a - c) •
          (connesVanSuijlekomB2OddEmbed * connesVanSuijlekomB2OddEmbed.conjTranspose) := by
  rw [connesVanSuijlekomB2_embed_conjTranspose,
    connesVanSuijlekomB2_oddEmbed_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesVanSuijlekomB2Mu, connesVanSuijlekomB2Rho,
      connesVanSuijlekomB2Embed, connesVanSuijlekomB2OddEmbed,
      connesVanSuijlekomB2EmbedAdjoint, connesVanSuijlekomB2OddEmbedAdjoint]
  all_goals
    field_simp [connesVanSuijlekomB2_sqrt_two_ne_zero]
  all_goals
    simp only [connesVanSuijlekomB2_sqrt_two_sq]
    ring

/-- **Connes--van Suijlekom, Lemma B.2(i--ii), coordinate cone form.**

The Appendix-B compression identifies the positive cone of the source matrices
with the positive semidefinite `2 × 2` cone subject to the source half-space
`z ≥ sqrt(2) y`.  In the displayed coordinates that half-space is `c ≤ a`.
-/
theorem connesVanSuijlekomB2_cone_iff (a b c : ℝ) :
    (connesVanSuijlekomB2Mu a b c).PosSemidef ↔
      (connesVanSuijlekomB2Rho a b c).PosSemidef ∧ c ≤ a := by
  constructor
  · intro hMu
    refine ⟨?_, ?_⟩
    · have hCompression := hMu.conjTranspose_mul_mul_same connesVanSuijlekomB2Embed
      rw [connesVanSuijlekomB2_compression_eq_rho] at hCompression
      exact hCompression
    · let odd : Fin 3 → ℝ := ![1, 0, -1]
      have hOdd := hMu.dotProduct_mulVec_nonneg odd
      change 0 ≤ star odd ⬝ᵥ (connesVanSuijlekomB2Mu a b c).mulVec odd at hOdd
      simp [odd, connesVanSuijlekomB2Mu, dotProduct, Matrix.mulVec,
        Fin.sum_univ_three] at hOdd
      linarith
  · rintro ⟨hRho, hca⟩
    rw [connesVanSuijlekomB2_orthogonal_decomposition]
    have hEven := hRho.conjTranspose_mul_mul_same connesVanSuijlekomB2Embed.conjTranspose
    have hOdd :
        (connesVanSuijlekomB2OddEmbed * connesVanSuijlekomB2OddEmbed.conjTranspose).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose connesVanSuijlekomB2OddEmbed
    simpa using hEven.add (hOdd.smul (sub_nonneg.mpr hca))

/-- Lemma B.2(ii) in the source's printed half-space coordinates. -/
theorem connesVanSuijlekomB2_cone_iff_psd_inter_halfSpace (a b c : ℝ) :
    (connesVanSuijlekomB2Mu a b c).PosSemidef ↔
      (connesVanSuijlekomB2Rho a b c).PosSemidef ∧
        connesVanSuijlekomB2HalfSpace (connesVanSuijlekomB2Rho a b c) := by
  rw [connesVanSuijlekomB2_cone_iff, connesVanSuijlekomB2_rho_mem_halfSpace_iff]

/-! ### Extreme-ray transport -/

/-- A nonzero element of a real cone spans an extreme ray when every cone decomposition is along
that same ray. -/
def IsExtremeRay {V : Type*} [AddCommMonoid V] [SMul ℝ V] (K : Set V) (x : V) : Prop :=
  x ∈ K ∧ x ≠ 0 ∧ ∀ u v, u ∈ K → v ∈ K → u + v = x →
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ u = r • x ∧ v = s • x

/-- Parameter-space model of the positive cone `C₊` in Appendix B. -/
def connesVanSuijlekomB2SourceCone : Set (ℝ × ℝ × ℝ) :=
  {p | (connesVanSuijlekomB2Mu p.1 p.2.1 p.2.2).PosSemidef}

/-- The exact image cone `S(E)₊ ∩ H` in Appendix B. -/
def connesVanSuijlekomB2TargetCone : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {Q | Q.PosSemidef ∧ connesVanSuijlekomB2HalfSpace Q}

/-- The ambient `2 × 2` positive-semidefinite cone in the source's real coordinates. -/
def connesVanSuijlekomB2PsdCone : Set (Matrix (Fin 2) (Fin 2) ℝ) :=
  {Q | Q.PosSemidef}

/-- The first coordinate rank-one ray used to split positive-definite target matrices. -/
def connesVanSuijlekomB2E00 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, 0]

private theorem connesVanSuijlekomB2_e00_posSemidef :
    connesVanSuijlekomB2E00.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · show connesVanSuijlekomB2E00ᴴ = connesVanSuijlekomB2E00
    ext i j
    fin_cases i <;> fin_cases j <;> simp [connesVanSuijlekomB2E00]
  · intro x
    have hx : x = (![x 0, x 1] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    simp [connesVanSuijlekomB2E00, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    exact mul_self_nonneg _

private theorem connesVanSuijlekomB2_offDiag_eq (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.PosSemidef) : Q 1 0 = Q 0 1 := by
  have h := congrFun (congrFun hQ.isHermitian.eq 1) 0
  simpa [Matrix.conjTranspose_apply] using h.symm

private theorem connesVanSuijlekomB2_matrix_fin_two_eq
    {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  rw [Matrix.eta_fin_two A, Matrix.eta_fin_two B]
  simp [h00, h01, h10, h11]

/-- A positive semidefinite `2 × 2` matrix with positive determinant remains positive
semidefinite after removing a nonzero small multiple of `E₀₀`. -/
private theorem connesVanSuijlekomB2_sub_det_half_e00_posSemidef
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosSemidef) (hdet : 0 < Q.det) :
    (Q - (Q.det / (2 * Q 1 1)) • connesVanSuijlekomB2E00).PosSemidef := by
  have h10 : Q 1 0 = Q 0 1 := connesVanSuijlekomB2_offDiag_eq Q hQ
  have h11nonneg : 0 ≤ Q 1 1 := hQ.diag_nonneg
  have h11pos : 0 < Q 1 1 := by
    by_contra hnot
    have h11 : Q 1 1 = 0 := le_antisymm (le_of_not_gt hnot) h11nonneg
    have hsq : 0 ≤ Q 0 1 * Q 0 1 := mul_self_nonneg _
    rw [Matrix.det_fin_two, h10, h11] at hdet
    nlinarith
  have heps : (Q.det / (2 * Q 1 1)) * Q 1 1 = Q.det / 2 := by
    field_simp
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · show (Q - (Q.det / (2 * Q 1 1)) • connesVanSuijlekomB2E00)ᴴ =
      Q - (Q.det / (2 * Q 1 1)) • connesVanSuijlekomB2E00
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [connesVanSuijlekomB2E00, Matrix.conjTranspose_apply,
        h10]
  · intro v
    have hv : v = (![v 0, v 1] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    have hsq : 0 ≤ (Q 1 1 * v 1 + Q 0 1 * v 0) ^ 2 := sq_nonneg _
    have hterm : 0 ≤ (Q.det / 2) * (v 0) ^ 2 := by
      exact mul_nonneg (by linarith) (sq_nonneg _)
    have hprod : 0 ≤ Q 1 1 *
        (star (![v 0, v 1] : Fin 2 → ℝ) ⬝ᵥ
          ((Q - (Q.det / (2 * Q 1 1)) • connesVanSuijlekomB2E00) *ᵥ
            (![v 0, v 1] : Fin 2 → ℝ))) := by
      have hid : Q 1 1 *
          (star (![v 0, v 1] : Fin 2 → ℝ) ⬝ᵥ
            ((Q - (Q.det / (2 * Q 1 1)) • connesVanSuijlekomB2E00) *ᵥ
              (![v 0, v 1] : Fin 2 → ℝ))) =
          (Q 1 1 * v 1 + Q 0 1 * v 0) ^ 2 + (Q.det / 2) * (v 0) ^ 2 := by
        simp [connesVanSuijlekomB2E00, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
          Matrix.det_fin_two, h10]
        field_simp
        ring
      rw [hid]
      exact add_nonneg hsq hterm
    nlinarith

private theorem connesVanSuijlekomB2_target_not_extreme_of_det_pos
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosSemidef)
    (hH : connesVanSuijlekomB2HalfSpace Q) (hdet : 0 < Q.det) :
    ¬ IsExtremeRay connesVanSuijlekomB2TargetCone Q := by
  intro hExtreme
  have h10 : Q 1 0 = Q 0 1 := connesVanSuijlekomB2_offDiag_eq Q hQ
  have h11nonneg : 0 ≤ Q 1 1 := hQ.diag_nonneg
  have h11pos : 0 < Q 1 1 := by
    by_contra hnot
    have h11 : Q 1 1 = 0 := le_antisymm (le_of_not_gt hnot) h11nonneg
    have hsq : 0 ≤ Q 0 1 * Q 0 1 := mul_self_nonneg _
    rw [Matrix.det_fin_two, h10, h11] at hdet
    nlinarith
  let ε : ℝ := Q.det / (2 * Q 1 1)
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact div_pos hdet (by positivity)
  have hBpsd : (ε • connesVanSuijlekomB2E00).PosSemidef :=
    connesVanSuijlekomB2_e00_posSemidef.smul hεpos.le
  have hCpsd : (Q - ε • connesVanSuijlekomB2E00).PosSemidef := by
    simpa [ε] using connesVanSuijlekomB2_sub_det_half_e00_posSemidef Q hQ hdet
  have hBH : connesVanSuijlekomB2HalfSpace (ε • connesVanSuijlekomB2E00) := by
    simp [connesVanSuijlekomB2HalfSpace, connesVanSuijlekomB2E00]
  have hCH : connesVanSuijlekomB2HalfSpace (Q - ε • connesVanSuijlekomB2E00) := by
    simpa [connesVanSuijlekomB2HalfSpace, connesVanSuijlekomB2E00] using hH
  have hB : ε • connesVanSuijlekomB2E00 ∈ connesVanSuijlekomB2TargetCone :=
    ⟨hBpsd, hBH⟩
  have hC : Q - ε • connesVanSuijlekomB2E00 ∈ connesVanSuijlekomB2TargetCone :=
    ⟨hCpsd, hCH⟩
  have hsum : ε • connesVanSuijlekomB2E00 + (Q - ε • connesVanSuijlekomB2E00) = Q := by
    abel
  obtain ⟨r, s, hr, hs, hBscale, hCscale⟩ :=
    hExtreme.2.2 _ _ hB hC hsum
  have hrzero : r = 0 := by
    have hentry := congrFun (congrFun hBscale 1) 1
    simp [connesVanSuijlekomB2E00] at hentry
    rcases hentry with hrzero | hQzero
    · exact hrzero
    · linarith
  have hBzero : ε • connesVanSuijlekomB2E00 = 0 := by
    simpa [hrzero] using hBscale
  have hentry := congrFun (congrFun hBzero 0) 0
  simp [connesVanSuijlekomB2E00] at hentry
  exact hεpos.ne' hentry

private theorem connesVanSuijlekomB2_psd_summand_mulVec_zero
    (B C Q : Matrix (Fin 2) (Fin 2) ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hsum : B + C = Q) (w : Fin 2 → ℝ) (hw : Q *ᵥ w = 0) :
    B *ᵥ w = 0 ∧ C *ᵥ w = 0 := by
  have hBnonneg : 0 ≤ star w ⬝ᵥ (B *ᵥ w) := hB.dotProduct_mulVec_nonneg w
  have hCnonneg : 0 ≤ star w ⬝ᵥ (C *ᵥ w) := hC.dotProduct_mulVec_nonneg w
  have hsumzero : star w ⬝ᵥ (B *ᵥ w) + star w ⬝ᵥ (C *ᵥ w) = 0 := by
    calc
      star w ⬝ᵥ (B *ᵥ w) + star w ⬝ᵥ (C *ᵥ w) =
          star w ⬝ᵥ ((B + C) *ᵥ w) := by
            simp [add_mulVec]
            ring
      _ = star w ⬝ᵥ (Q *ᵥ w) := by rw [hsum]
      _ = 0 := by rw [hw]; simp
  have hBzero : star w ⬝ᵥ (B *ᵥ w) = 0 := by linarith
  have hCzero : star w ⬝ᵥ (C *ᵥ w) = 0 := by linarith
  exact ⟨hB.dotProduct_mulVec_zero_iff w |>.mp hBzero,
    hC.dotProduct_mulVec_zero_iff w |>.mp hCzero⟩

private theorem connesVanSuijlekomB2_psd_rowcol_zero_of_diag_zero
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B.PosSemidef) (h00 : B 0 0 = 0) :
    B 0 1 = 0 ∧ B 1 0 = 0 := by
  let e0 : Fin 2 → ℝ := ![1, 0]
  have hdot : star e0 ⬝ᵥ (B *ᵥ e0) = 0 := by
    simp [e0, dotProduct, Matrix.mulVec, Fin.sum_univ_two, h00]
  have hvec : B *ᵥ e0 = 0 := hB.dotProduct_mulVec_zero_iff e0 |>.mp hdot
  have h10 : B 1 0 = 0 := by
    have h := congrFun hvec 1
    simpa [e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have h01 : B 0 1 = 0 := by
    have h := congrFun (congrFun hB.isHermitian.eq 0) 1
    simpa [Matrix.conjTranspose_apply, h10] using h.symm
  exact ⟨h01, h10⟩

private theorem connesVanSuijlekomB2_psd_summand_eq_smul_of_det_zero
    (B C Q : Matrix (Fin 2) (Fin 2) ℝ) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hQ : Q.PosSemidef) (hsum : B + C = Q) (hdet : Q.det = 0) (hQne : Q ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ B = r • Q := by
  have hQ10 : Q 1 0 = Q 0 1 := connesVanSuijlekomB2_offDiag_eq Q hQ
  by_cases hQ00 : Q 0 0 = 0
  · have hQ01 : Q 0 1 = 0 := by
      rw [Matrix.det_fin_two, hQ10, hQ00] at hdet
      nlinarith [sq_nonneg (Q 0 1)]
    have hQ11ne : Q 1 1 ≠ 0 := by
      intro hQ11
      apply hQne
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hQ00, hQ01, hQ10, hQ11]
    have hQ11nonneg : 0 ≤ Q 1 1 := hQ.diag_nonneg
    have hB00nonneg : 0 ≤ B 0 0 := hB.diag_nonneg
    have hC00nonneg : 0 ≤ C 0 0 := hC.diag_nonneg
    have hsum00 := congrFun (congrFun hsum 0) 0
    have hB00 : B 0 0 = 0 := by
      simp [hQ00] at hsum00
      linarith
    have hBrows := connesVanSuijlekomB2_psd_rowcol_zero_of_diag_zero B hB hB00
    refine ⟨B 1 1 / Q 1 1, div_nonneg (hB.diag_nonneg) hQ11nonneg, ?_⟩
    apply connesVanSuijlekomB2_matrix_fin_two_eq
    · simp [hB00, hQ00]
    · simp [hBrows.1, hQ01]
    · simp [hBrows.2, hQ10, hQ01]
    · simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp
  · have hQ00nonneg : 0 ≤ Q 0 0 := hQ.diag_nonneg
    have hQ00pos : 0 < Q 0 0 := lt_of_le_of_ne hQ00nonneg (Ne.symm hQ00)
    let w : Fin 2 → ℝ := ![-Q 0 1, Q 0 0]
    have hQvec : Q *ᵥ w = 0 := by
      ext i
      fin_cases i
      · simp [w, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      · rw [Matrix.det_fin_two, hQ10] at hdet
        simp [w, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hQ10]
        linarith
    have hBvec :=
      (connesVanSuijlekomB2_psd_summand_mulVec_zero B C Q hB hC hsum w hQvec).1
    have hB10 : B 1 0 = B 0 1 := connesVanSuijlekomB2_offDiag_eq B hB
    have hBrow0 := congrFun hBvec 0
    have hBrow1 := congrFun hBvec 1
    simp [w, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hBrow0 hBrow1
    rw [hB10] at hBrow1
    have hdet' : Q 0 0 * Q 1 1 = (Q 0 1) ^ 2 := by
      rw [Matrix.det_fin_two, hQ10] at hdet
      nlinarith
    have hBsq : B 1 1 * (Q 0 0) ^ 2 = B 0 0 * (Q 0 1) ^ 2 := by
      linear_combination Q 0 0 * hBrow1 + Q 0 1 * hBrow0
    have hB11mul : B 1 1 * Q 0 0 = B 0 0 * Q 1 1 := by
      apply mul_right_cancel₀ hQ00
      calc
        (B 1 1 * Q 0 0) * Q 0 0 = B 1 1 * (Q 0 0) ^ 2 := by ring
        _ = B 0 0 * (Q 0 1) ^ 2 := hBsq
        _ = B 0 0 * (Q 0 0 * Q 1 1) := by rw [hdet']
        _ = (B 0 0 * Q 1 1) * Q 0 0 := by ring
    have hB00eq : B 0 0 = (B 0 0 / Q 0 0) * Q 0 0 := by
      field_simp
    have hB01eq : B 0 1 = (B 0 0 / Q 0 0) * Q 0 1 := by
      field_simp
      linarith [hBrow0]
    have hB10eq : B 1 0 = (B 0 0 / Q 0 0) * Q 1 0 := by
      rw [hB10, hQ10]
      exact hB01eq
    have hB11eq : B 1 1 = (B 0 0 / Q 0 0) * Q 1 1 := by
      field_simp
      linarith [hB11mul]
    refine ⟨B 0 0 / Q 0 0, div_nonneg (hB.diag_nonneg) hQ00nonneg, ?_⟩
    apply connesVanSuijlekomB2_matrix_fin_two_eq
    · simpa only [Matrix.smul_apply, smul_eq_mul] using hB00eq
    · simpa only [Matrix.smul_apply, smul_eq_mul] using hB01eq
    · simpa only [Matrix.smul_apply, smul_eq_mul] using hB10eq
    · simpa only [Matrix.smul_apply, smul_eq_mul] using hB11eq

private theorem connesVanSuijlekomB2_psd_extreme_of_det_zero
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosSemidef)
    (hdet : Q.det = 0) (hQne : Q ≠ 0) :
    IsExtremeRay connesVanSuijlekomB2PsdCone Q := by
  refine ⟨hQ, hQne, ?_⟩
  intro B C hB hC hsum
  obtain ⟨r, hr, hBscale⟩ :=
    connesVanSuijlekomB2_psd_summand_eq_smul_of_det_zero B C Q hB hC hQ hsum hdet hQne
  obtain ⟨s, hs, hCscale⟩ :=
    connesVanSuijlekomB2_psd_summand_eq_smul_of_det_zero C B Q hC hB hQ
      (by simpa [add_comm] using hsum) hdet hQne
  exact ⟨r, s, hr, hs, hBscale, hCscale⟩

/-- The compression in source-parameter coordinates. -/
def connesVanSuijlekomB2RhoMap (p : ℝ × ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  connesVanSuijlekomB2Rho p.1 p.2.1 p.2.2

theorem connesVanSuijlekomB2_rhoMap_injective :
    Function.Injective connesVanSuijlekomB2RhoMap :=
  connesVanSuijlekomB2_rho_injective

theorem connesVanSuijlekomB2_rhoMap_add (p q : ℝ × ℝ × ℝ) :
    connesVanSuijlekomB2RhoMap (p + q) =
      connesVanSuijlekomB2RhoMap p + connesVanSuijlekomB2RhoMap q := by
  rcases p with ⟨a, b, c⟩
  rcases q with ⟨a', b', c'⟩
  simpa [connesVanSuijlekomB2RhoMap] using connesVanSuijlekomB2_rho_add a b c a' b' c'

theorem connesVanSuijlekomB2_rhoMap_smul (r : ℝ) (p : ℝ × ℝ × ℝ) :
    connesVanSuijlekomB2RhoMap (r • p) = r • connesVanSuijlekomB2RhoMap p := by
  rcases p with ⟨a, b, c⟩
  simpa [connesVanSuijlekomB2RhoMap] using connesVanSuijlekomB2_rho_smul r a b c

theorem connesVanSuijlekomB2_rhoMap_zero :
    connesVanSuijlekomB2RhoMap (0 : ℝ × ℝ × ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [connesVanSuijlekomB2RhoMap,
    connesVanSuijlekomB2Rho]

theorem connesVanSuijlekomB2_rhoMap_mem_targetCone_iff (p : ℝ × ℝ × ℝ) :
    connesVanSuijlekomB2RhoMap p ∈ connesVanSuijlekomB2TargetCone ↔
      p ∈ connesVanSuijlekomB2SourceCone := by
  rcases p with ⟨a, b, c⟩
  simpa [connesVanSuijlekomB2RhoMap, connesVanSuijlekomB2TargetCone,
    connesVanSuijlekomB2SourceCone] using
    (connesVanSuijlekomB2_cone_iff_psd_inter_halfSpace a b c).symm

/-- The coordinate isomorphism preserves and reflects extreme rays of its exact image cone. -/
theorem connesVanSuijlekomB2_isExtremeRay_source_iff_target (p : ℝ × ℝ × ℝ) :
    IsExtremeRay connesVanSuijlekomB2SourceCone p ↔
      IsExtremeRay connesVanSuijlekomB2TargetCone (connesVanSuijlekomB2RhoMap p) := by
  constructor
  · rintro ⟨hp, hp0, hpExtreme⟩
    refine ⟨(connesVanSuijlekomB2_rhoMap_mem_targetCone_iff p).mpr hp, ?_, ?_⟩
    · intro hzero
      apply hp0
      apply connesVanSuijlekomB2_rhoMap_injective
      simpa [connesVanSuijlekomB2_rhoMap_zero] using hzero
    · intro y z hy hz hyz
      let u := connesVanSuijlekomB2RhoInverse y
      let v := connesVanSuijlekomB2RhoInverse z
      have huMap : connesVanSuijlekomB2RhoMap u = y := by
        exact connesVanSuijlekomB2_rho_inverse_apply y hy.1.isHermitian
      have hvMap : connesVanSuijlekomB2RhoMap v = z := by
        exact connesVanSuijlekomB2_rho_inverse_apply z hz.1.isHermitian
      have hu : u ∈ connesVanSuijlekomB2SourceCone :=
        (connesVanSuijlekomB2_rhoMap_mem_targetCone_iff u).mp (by simpa [huMap] using hy)
      have hv : v ∈ connesVanSuijlekomB2SourceCone :=
        (connesVanSuijlekomB2_rhoMap_mem_targetCone_iff v).mp (by simpa [hvMap] using hz)
      have huvMap : connesVanSuijlekomB2RhoMap (u + v) =
          connesVanSuijlekomB2RhoMap p := by
        rw [connesVanSuijlekomB2_rhoMap_add, huMap, hvMap, hyz]
      have huv : u + v = p := connesVanSuijlekomB2_rhoMap_injective huvMap
      obtain ⟨r, s, hr, hs, hur, hvs⟩ := hpExtreme u v hu hv huv
      refine ⟨r, s, hr, hs, ?_, ?_⟩
      · calc
          y = connesVanSuijlekomB2RhoMap u := huMap.symm
          _ = connesVanSuijlekomB2RhoMap (r • p) := by rw [hur]
          _ = r • connesVanSuijlekomB2RhoMap p := connesVanSuijlekomB2_rhoMap_smul r p
      · calc
          z = connesVanSuijlekomB2RhoMap v := hvMap.symm
          _ = connesVanSuijlekomB2RhoMap (s • p) := by rw [hvs]
          _ = s • connesVanSuijlekomB2RhoMap p := connesVanSuijlekomB2_rhoMap_smul s p
  · rintro ⟨hp, hp0, hpExtreme⟩
    refine ⟨(connesVanSuijlekomB2_rhoMap_mem_targetCone_iff p).mp hp, ?_, ?_⟩
    · intro hzero
      apply hp0
      simpa [hzero] using connesVanSuijlekomB2_rhoMap_zero
    · intro u v hu hv huv
      have huTarget : connesVanSuijlekomB2RhoMap u ∈ connesVanSuijlekomB2TargetCone :=
        (connesVanSuijlekomB2_rhoMap_mem_targetCone_iff u).mpr hu
      have hvTarget : connesVanSuijlekomB2RhoMap v ∈ connesVanSuijlekomB2TargetCone :=
        (connesVanSuijlekomB2_rhoMap_mem_targetCone_iff v).mpr hv
      have huvTarget : connesVanSuijlekomB2RhoMap u + connesVanSuijlekomB2RhoMap v =
          connesVanSuijlekomB2RhoMap p := by
        rw [← connesVanSuijlekomB2_rhoMap_add, huv]
      obtain ⟨r, s, hr, hs, hur, hvs⟩ := hpExtreme _ _ huTarget hvTarget huvTarget
      refine ⟨r, s, hr, hs, ?_, ?_⟩
      · apply connesVanSuijlekomB2_rhoMap_injective
        rw [connesVanSuijlekomB2_rhoMap_smul]
        exact hur
      · apply connesVanSuijlekomB2_rhoMap_injective
        rw [connesVanSuijlekomB2_rhoMap_smul]
        exact hvs

private theorem connesVanSuijlekomB2_target_extreme_det_eq_zero
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hExtreme : IsExtremeRay connesVanSuijlekomB2TargetCone Q) : Q.det = 0 := by
  have hQ : Q.PosSemidef := hExtreme.1.1
  have hH : connesVanSuijlekomB2HalfSpace Q := hExtreme.1.2
  by_contra hdetne
  have hdetpos : 0 < Q.det :=
    lt_of_le_of_ne hQ.det_nonneg (Ne.symm hdetne)
  exact connesVanSuijlekomB2_target_not_extreme_of_det_pos Q hQ hH hdetpos hExtreme

/-- The extreme rays of the PSD cone that lie in `H` are precisely the extreme rays of
`S(E)₊ ∩ H` in the Appendix-B coordinates. -/
theorem connesVanSuijlekomB2_target_extreme_iff_psd_extreme_and_halfSpace
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    IsExtremeRay connesVanSuijlekomB2TargetCone Q ↔
      IsExtremeRay connesVanSuijlekomB2PsdCone Q ∧ connesVanSuijlekomB2HalfSpace Q := by
  constructor
  · intro hExtreme
    exact ⟨connesVanSuijlekomB2_psd_extreme_of_det_zero Q hExtreme.1.1
      (connesVanSuijlekomB2_target_extreme_det_eq_zero Q hExtreme) hExtreme.2.1,
      hExtreme.1.2⟩
  · rintro ⟨hPsdExtreme, hH⟩
    refine ⟨⟨hPsdExtreme.1, hH⟩, hPsdExtreme.2.1, ?_⟩
    intro B C hB hC hsum
    exact hPsdExtreme.2.2 B C hB.1 hC.1 hsum

/-- **Appendix B, Lemma B.2(iii).**  Under `ρ`, the extreme rays of `C₊` map exactly to
the extreme rays of `S(E)₊` contained in the source's half-space `H`. -/
theorem connesVanSuijlekomB2_extreme_rays_iff
    (p : ℝ × ℝ × ℝ) :
    IsExtremeRay connesVanSuijlekomB2SourceCone p ↔
      IsExtremeRay connesVanSuijlekomB2PsdCone (connesVanSuijlekomB2RhoMap p) ∧
        connesVanSuijlekomB2HalfSpace (connesVanSuijlekomB2RhoMap p) := by
  rw [connesVanSuijlekomB2_isExtremeRay_source_iff_target,
    connesVanSuijlekomB2_target_extreme_iff_psd_extreme_and_halfSpace]

end

end GaloisForLFunctions.HTGeometry
