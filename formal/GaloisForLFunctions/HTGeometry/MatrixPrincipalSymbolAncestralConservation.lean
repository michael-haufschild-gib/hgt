import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolLowerLaw

/-!
# Conservation of ancestral hypertranscendence

An everywhere-regular finite-rank principal law cannot create algebraic independence from a
dependent source.  At every finite jet depth it is an invertible linear change of coordinates;
hence, on the complete packet, algebraic independence of the target is equivalent to algebraic
independence of the ancestral source.  Singular principal symbols may destroy independence, but a
regular tower only transports information already present before the law is iterated.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

/-- Matrix linear forms compose according to matrix multiplication. -/
theorem matrixPrincipalLinearForms_mul
    {τ : Type*} [Fintype τ]
    (M N : Matrix τ τ K) (x : τ → L) :
    matrixLinearForms M (matrixLinearForms N x) =
      matrixLinearForms (M * N) x := by
  funext i
  simp only [matrixLinearForms, Matrix.mul_apply, map_sum, map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The identity coefficient matrix leaves a packet unchanged. -/
theorem matrixPrincipalLinearForms_one
    {τ : Type*} [Fintype τ] [DecidableEq τ] (x : τ → L) :
    matrixLinearForms (1 : Matrix τ τ K) x = x := by
  funext i
  simp [matrixLinearForms, Matrix.one_apply]

/-- An invertible square linear transformation preserves algebraic independence in both
directions, with no independence hypothesis placed on the source in advance. -/
theorem algebraicIndependent_matrixLinearForms_iff_of_det_ne_zero
    {τ : Type*} [Fintype τ] [DecidableEq τ]
    (M : Matrix τ τ K) (x : τ → L) (hdet : M.det ≠ 0) :
    AlgebraicIndependent K (matrixLinearForms M x) ↔
      AlgebraicIndependent K x := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  constructor
  · intro hy
    have hback := algebraicIndependent_matrixLinearForms_of_mul_eq_one
      M⁻¹ M (Matrix.nonsing_inv_mul M hunit) (matrixLinearForms M x) hy
    rw [matrixPrincipalLinearForms_mul, Matrix.nonsing_inv_mul M hunit,
      matrixPrincipalLinearForms_one] at hback
    exact hback
  · intro hx
    exact algebraicIndependent_matrixLinearForms_of_mul_eq_one
      M M⁻¹ (Matrix.mul_nonsing_inv M hunit) x hx

/-- **Ancestral conservation theorem.**  If all principal symbols of a realized complete packet
are nonsingular, the target packet is algebraically independent exactly when the source packet is.
Thus regular finite-rank principal evolution transports but never creates hypertranscendence. -/
theorem matrixPrincipalPacket_ancestral_independence_iff
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K)
    (hreal : MatrixPrincipalPacketRealization u y symbol)
    (hsymbol : ∀ n, (symbol n).det ≠ 0) :
    AlgebraicIndependent K (fun p : ℕ × ι ↦ y p.1 p.2) ↔
      AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2) := by
  constructor
  · intro hy
    apply algebraicIndependent_of_finite_type
    intro t ht
    letI : Fintype t := ht.fintype
    let N : ℕ := t.toFinset.sup (fun p : ℕ × ι ↦ p.1) + 1
    let includeInitial : Fin N × ι → ℕ × ι :=
      fun p ↦ ((p.1 : ℕ), p.2)
    have hincludeInitial : Function.Injective includeInitial := by
      intro p q hpq
      apply Prod.ext
      · exact Fin.ext (congrArg Prod.fst hpq)
      · exact congrArg (fun z : ℕ × ι ↦ z.2) hpq
    have hyN : AlgebraicIndependent K
        (fun p : Fin N × ι ↦ y p.1 p.2) := by
      simpa [includeInitial, Function.comp_def] using
        hy.comp includeInitial hincludeInitial
    obtain ⟨M, hpacket, htri, hdiag⟩ := hreal N
    have hblocks : ∀ n : Fin N,
        (M.toSquareBlock matrixPrincipalLayerOrder (OrderDual.toDual n)).det ≠ 0 := by
      intro n
      rw [hdiag n, Matrix.det_reindex_self]
      exact hsymbol n
    have hdet : M.det ≠ 0 := by
      rw [htri.det_fintype]
      exact Finset.prod_ne_zero_iff.mpr fun n _ ↦ hblocks (OrderDual.ofDual n)
    rw [hpacket] at hyN
    have huN : AlgebraicIndependent K
        (fun p : Fin N × ι ↦ u p.1 p.2) :=
      (algebraicIndependent_matrixLinearForms_iff_of_det_ne_zero
        M (fun p : Fin N × ι ↦ u p.1 p.2) hdet).mp hyN
    let embed : t → Fin N × ι := fun p ↦
      (⟨p.1.1, Nat.lt_succ_of_le (Finset.le_sup
        (f := fun q : ℕ × ι ↦ q.1)
        (show p.1 ∈ t.toFinset by simp [p.2]))⟩, p.1.2)
    have hembed : Function.Injective embed := by
      intro p q hpq
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : Fin N × ι ↦ (z.1 : ℕ)) hpq
      · exact congrArg (fun z : Fin N × ι ↦ z.2) hpq
    simpa [embed, Function.comp_def] using huN.comp embed hembed
  · intro hu
    exact (matrixPrincipalPacket_algebraicIndependent_iff
      u y symbol hreal hu).mpr hsymbol

/-- Explicit strict-lower principal laws satisfy ancestral conservation without any packet oracle. -/
theorem matrixPrincipalLowerLaw_ancestral_independence_iff
    (u y : ℕ → ι → L) (symbol : ℕ → Matrix ι ι K)
    (hlaw : MatrixPrincipalLowerLaw u y symbol)
    (hsymbol : ∀ n, (symbol n).det ≠ 0) :
    AlgebraicIndependent K (fun p : ℕ × ι ↦ y p.1 p.2) ↔
      AlgebraicIndependent K (fun p : ℕ × ι ↦ u p.1 p.2) :=
  matrixPrincipalPacket_ancestral_independence_iff u y symbol
    (matrixPrincipalPacketRealization_of_lowerLaw u y symbol hlaw) hsymbol

end

end GaloisForLFunctions.HTGeometry
