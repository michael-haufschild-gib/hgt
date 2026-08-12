/-
The trace-norm bound: the approximation numbers of a product of two Hilbert–Schmidt operators are
summable with `∑ₙ aₙ(A∘B) ≤ ‖A‖_HS·‖B‖_HS` — the sharp constant, through the singular value
decomposition of the product.

Each singular value of `M = A∘B` is read off by the singular pair: `sₙ = ⟨fₙ, M eₙ⟩ =
⟨A† fₙ, B eₙ⟩ ≤ ‖A† fₙ‖·‖B eₙ‖`.  Summing over a finite set, Cauchy–Schwarz splits the right side
into two Bessel sums: the left and right singular families are orthonormal (with zeros), so
`∑ ‖A† fₙ‖² ≤ ‖A‖²_HS` and `∑ ‖B eₙ‖² ≤ ‖B‖²_HS` by extending each family to a Hilbert basis.
Every partial sum of approximation numbers is therefore bounded by `‖A‖_HS·‖B‖_HS`, giving both
summability — membership in the Schatten 1-class — and the trace-norm inequality.  A factorized
trace-class operator in the `IsTraceClass` sense thus has finite trace norm.
-/
import GaloisForLFunctions.HTGeometry.SVDExpansion
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Bessel for Hilbert–Schmidt sums.**  The squared image norms of a Hilbert–Schmidt operator
over any orthonormal-with-zeros family are dominated by the Hilbert–Schmidt norm: extend the
nonzero members to a Hilbert basis and compare with the full series. -/
theorem sum_normSq_apply_le_hsNormSq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (hT : T.IsHilbertSchmidt)
    (v : ℕ → E) (hv : ∀ n, v n = 0 ∨ ‖v n‖ = 1)
    (horth : ∀ m n, m ≠ n → inner ℂ (v m) (v n) = 0) (s : Finset ℕ) :
    ∑ n ∈ s, ‖T (v n)‖ ^ 2 ≤ ContinuousLinearMap.hsNormSq T := by
  classical
  have hsplit : ∑ n ∈ s, ‖T (v n)‖ ^ 2
      = ∑ n ∈ s.filter (fun n => v n ≠ 0), ‖T (v n)‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun n => v n ≠ 0)]
    have hz : ∑ n ∈ s.filter (fun n => ¬v n ≠ 0), ‖T (v n)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have h0 := (Finset.mem_filter.mp hn).2
      rw [not_not] at h0
      rw [h0]
      simp
    rw [hz, add_zero]
  rw [hsplit]
  set t := s.filter (fun n => v n ≠ 0) with ht
  have hunit : ∀ n ∈ t, ‖v n‖ = 1 := by
    intro n hn
    rcases hv n with h | h
    · exact absurd h (Finset.mem_filter.mp hn).2
    · exact h
  have hinj : Set.InjOn v t := by
    intro m hm n hn hmn
    by_contra hne
    have h0 := horth m n hne
    rw [hmn, inner_self_eq_norm_sq_to_K, hunit n hn] at h0
    norm_num at h0
  have hA_orth : Orthonormal ℂ (Subtype.val : (v '' t) → E) := by
    rw [orthonormal_subtype_iff_ite]
    rintro x ⟨m, hm, rfl⟩ y ⟨n, hn, rfl⟩
    by_cases hxy : v m = v n
    · rw [hxy, if_pos rfl, inner_self_eq_norm_sq_to_K, hunit n hn]
      norm_num
    · rw [if_neg hxy]
      refine horth m n fun h => hxy ?_
      rw [h]
  obtain ⟨w, b, hAw, hb⟩ := hA_orth.exists_hilbertBasis_extension
  have hmemw : ∀ n ∈ t, v n ∈ w := fun n hn => hAw ⟨n, hn, rfl⟩
  set u : Finset ↥w := t.attach.image
    (fun p => (⟨v p.1, hmemw p.1 p.2⟩ : ↥w)) with hu
  have himg_inj : Set.InjOn (fun p : {x // x ∈ t} => (⟨v p.1, hmemw p.1 p.2⟩ : ↥w))
      ↑t.attach := by
    intro p hp q hq h
    exact Subtype.ext (hinj p.2 q.2 (congrArg Subtype.val h))
  have hsum_eq : ∑ n ∈ t, ‖T (v n)‖ ^ 2 = ∑ x ∈ u, ‖T (↑x : E)‖ ^ 2 := by
    rw [hu, Finset.sum_image himg_inj, Finset.sum_attach t (fun n => ‖T (v n)‖ ^ 2)]
  rw [hsum_eq]
  have hsummable : Summable (fun x : ↥w => ‖T (↑x : E)‖ ^ 2) := by
    have h1 := hT.summable b
    refine h1.congr fun x => ?_
    rw [hb]
  calc ∑ x ∈ u, ‖T (↑x : E)‖ ^ 2
      ≤ ∑' x : ↥w, ‖T (↑x : E)‖ ^ 2 :=
        hsummable.sum_le_tsum u (fun x _ => by positivity)
    _ = ContinuousLinearMap.hsNormSq T := by
        rw [hsNormSq_eq hT b]
        exact tsum_congr fun x => by rw [hb]

section TraceNorm

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {A : K →L[ℂ] H} {B : H →L[ℂ] K}

/-- **The partial trace-norm bound.**  Every finite sum of approximation numbers of `A∘B` is
bounded by `‖A‖_HS·‖B‖_HS`. -/
theorem sum_approxNumber_comp_le (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    (s : Finset ℕ) :
    ∑ n ∈ s, approxNumber (A ∘L B) n
      ≤ ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
  classical
  have hM : (A ∘L B).IsHilbertSchmidt := hB.comp_left A
  have hMcpt : IsCompactOperator (A ∘L B) := hM.isCompactOperator
  have hsymM := energyOp_symmetric (A ∘L B)
  have hposM := energyOp_pos (A ∘L B)
  have hScptM := energyOp_compact hMcpt
  -- per-index bound
  have hkey : ∀ n, approxNumber (A ∘L B) n
      ≤ ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
        * ‖B (svVec (energyOp (A ∘L B)) n)‖ := by
    intro n
    rw [approxNumber_eq_singVal hMcpt n]
    have h2 : singVal (A ∘L B) n
        = RCLike.re (inner ℂ (svdVec (A ∘L B) n)
            ((A ∘L B) (svVec (energyOp (A ∘L B)) n))) := by
      rw [inner_svdVec_apply hMcpt n]
      simp
    rw [h2]
    have h3 : inner ℂ (svdVec (A ∘L B) n) ((A ∘L B) (svVec (energyOp (A ∘L B)) n))
        = inner ℂ (ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n))
            (B (svVec (energyOp (A ∘L B)) n)) := by
      rw [comp_apply, adjoint_inner_left]
    rw [h3]
    calc RCLike.re (inner ℂ (ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n))
            (B (svVec (energyOp (A ∘L B)) n)))
        ≤ ‖inner ℂ (ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n))
            (B (svVec (energyOp (A ∘L B)) n))‖ := RCLike.re_le_norm _
      _ ≤ ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
            * ‖B (svVec (energyOp (A ∘L B)) n)‖ := norm_inner_le_norm _ _
  -- Cauchy–Schwarz over the finset
  have hCS : ∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
        * ‖B (svVec (energyOp (A ∘L B)) n)‖
      ≤ Real.sqrt (∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖ ^ 2)
        * Real.sqrt (∑ n ∈ s, ‖B (svVec (energyOp (A ∘L B)) n)‖ ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun n => ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖)
      (fun n => ‖B (svVec (energyOp (A ∘L B)) n)‖)
    have h2 : 0 ≤ ∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
        * ‖B (svVec (energyOp (A ∘L B)) n)‖ :=
      Finset.sum_nonneg fun n _ => by positivity
    calc ∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
          * ‖B (svVec (energyOp (A ∘L B)) n)‖
        = Real.sqrt ((∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
            * ‖B (svVec (energyOp (A ∘L B)) n)‖) ^ 2) := (Real.sqrt_sq h2).symm
      _ ≤ Real.sqrt ((∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖ ^ 2)
            * ∑ n ∈ s, ‖B (svVec (energyOp (A ∘L B)) n)‖ ^ 2) := Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_mul (Finset.sum_nonneg fun n _ => by positivity) _
  -- the two Bessel bounds
  have hBesselA : ∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖ ^ 2
      ≤ ContinuousLinearMap.hsNormSq A := by
    have h1 := sum_normSq_apply_le_hsNormSq hA.adjoint (svdVec (A ∘L B))
      (fun n => by
        rcases eq_or_ne (singVal (A ∘L B) n) 0 with h0 | hne
        · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
        · exact Or.inr (norm_svdVec_sq hMcpt hne))
      (fun m n h => inner_svdVec_svdVec_of_ne _ h) s
    rwa [hA.hsNormSq_adjoint] at h1
  have hBesselB : ∑ n ∈ s, ‖B (svVec (energyOp (A ∘L B)) n)‖ ^ 2
      ≤ ContinuousLinearMap.hsNormSq B := by
    refine sum_normSq_apply_le_hsNormSq hB (svVec (energyOp (A ∘L B)))
      (fun n => ?_) (fun m n h => inner_svVec_svVec_of_ne _ h) s
    rcases eq_or_ne (svVal (energyOp (A ∘L B)) n) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr (norm_svVec_of_ne_zero hScptM hsymM hposM hne)
  -- assemble
  calc ∑ n ∈ s, approxNumber (A ∘L B) n
      ≤ ∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖
          * ‖B (svVec (energyOp (A ∘L B)) n)‖ := Finset.sum_le_sum fun n _ => hkey n
    _ ≤ Real.sqrt (∑ n ∈ s, ‖ContinuousLinearMap.adjoint A (svdVec (A ∘L B) n)‖ ^ 2)
          * Real.sqrt (∑ n ∈ s, ‖B (svVec (energyOp (A ∘L B)) n)‖ ^ 2) := hCS
    _ ≤ Real.sqrt (ContinuousLinearMap.hsNormSq A)
          * Real.sqrt (ContinuousLinearMap.hsNormSq B) := by
        have hs1 := Real.sqrt_le_sqrt hBesselA
        have hs2 := Real.sqrt_le_sqrt hBesselB
        exact mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B := by
        rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm]

/-- **The approximation numbers of a Hilbert–Schmidt product are summable.** -/
theorem summable_approxNumber_comp (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    Summable (fun n => approxNumber (A ∘L B) n) :=
  summable_of_sum_le (fun n => approxNumber_nonneg _ n) (sum_approxNumber_comp_le hA hB)

/-- **The trace-norm inequality.**  `∑ₙ aₙ(A∘B) ≤ ‖A‖_HS·‖B‖_HS`, with the sharp constant. -/
theorem tsum_approxNumber_comp_le (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    ∑' n, approxNumber (A ∘L B) n
      ≤ ContinuousLinearMap.hsNorm A * ContinuousLinearMap.hsNorm B :=
  Real.tsum_le_of_sum_le (fun n => approxNumber_nonneg _ n) (sum_approxNumber_comp_le hA hB)

/-- **Hilbert–Schmidt products lie in the Schatten 1-class.** -/
theorem memSchattenClass_one_comp (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) :
    MemSchattenClass 1 (A ∘L B) := by
  refine (summable_approxNumber_comp hA hB).congr fun n => ?_
  rw [Real.rpow_one]

/-- **Trace-class operators have finite trace norm**: a factorized trace-class operator lies in
the Schatten 1-class, so `IsTraceClass` carries a genuine summable singular-value series. -/
theorem IsTraceClass.memSchattenClass_one {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    MemSchattenClass 1 T := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hT
  exact memSchattenClass_one_comp hS hU

end TraceNorm

end RHTower
