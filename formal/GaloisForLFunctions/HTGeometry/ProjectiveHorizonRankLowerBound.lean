import GaloisForLFunctions.HTGeometry.ProjectiveHorizonObserverJacobian
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# The transcendence degree of the horizon field of a span

The observer Jacobian of a covector span is nondegenerate.  A vector in the kernel of its transpose
is a combination of infinitesimal observers annihilating the whole reduced block; multiplying by the
inverse jet frame concentrates that combination on the omitted row, and the traceless condition then
forces it to be a multiple of the omitted coordinate, which the nonvanishing of the diagonal
cofactor of the jet frame rules out.

With the Jacobian criterion this makes the reduced block algebraically independent over the horizon
field.  Together with the reconstruction of the jet field from the horizon field and the reduced
block, the horizon field of a span of rank `r` in `N` directions has codimension exactly `rN-1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The diagonal entry of the inverse jet frame -/

omit [Fintype n] in
theorem jetFrame_inv_diag_ne_zero (t : Finset n) (m₀ : ↥t) :
    (jetFrame (K := K) t)⁻¹ m₀ m₀ ≠ 0 := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (jetFrame_det_ne_zero t))
    (adjugate_jetFrame_diag_ne_zero t m₀)

/-! ## Nondegeneracy of the observer Jacobian -/

/-- **The observer Jacobian is nondegenerate.** -/
theorem observerJacobian_det_ne_zero (t : Finset n) (m₀ : ↥t) :
    (observerJacobian (K := K) t m₀).det ≠ 0 := by
  classical
  intro hdet
  have hdetT : (observerJacobian (K := K) t m₀)ᵀ.det = 0 := by
    rw [Matrix.det_transpose]
    exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetT
  set P : Matrix ↥t ↥t (HomogeneousJetField n K) := jetFrame t with hPdef
  have hPunit : IsUnit P.det := jetFrame_isUnit_det t
  set V : n × ↥t → HomogeneousJetField n K := fun p =>
    if h : p = ((m₀ : n), m₀) then 0 else v ⟨p, h⟩ with hVdef
  have hVzero : V ((m₀ : n), m₀) = 0 := dif_pos rfl
  have hVcoe : ∀ p : ReducedIndex t m₀, V (p : n × ↥t) = v p := fun p => dif_neg p.2
  set row : n → ↥t → HomogeneousJetField n K := fun k c => V (k, c) with hrowdef
  set τ : HomogeneousJetField n K := ∑ c : ↥t, V ((c : n), c) with hτdef
  have hkey : ∀ q : ReducedIndex t m₀,
      (row (q : n × ↥t).1 ᵥ* P) (q : n × ↥t).2 =
        (if (m₀ : n) = (q : n × ↥t).1 then τ * P m₀ (q : n × ↥t).2 else 0) := by
    intro q
    have hq : ∑ p : ReducedIndex t m₀, observerJacobian (K := K) t m₀ p q * v p = 0 := by
      have h := congrFun hv q
      rw [mulVec_apply_eq_sum] at h
      simpa using h
    set G : n × ↥t → HomogeneousJetField n K := fun p =>
      ((if p.1 = (q : n × ↥t).1 then P p.2 (q : n × ↥t).2 else 0) -
        (if p.1 = (p.2 : n) then
          (if (m₀ : n) = (q : n × ↥t).1 then P m₀ (q : n × ↥t).2 else 0) else 0)) * V p
      with hGdef
    have hGsub : ∀ p : ReducedIndex t m₀,
        G (p : n × ↥t) = observerJacobian (K := K) t m₀ p q * v p := by
      intro p
      simp only [hGdef]
      rw [observerJacobian_apply, hVcoe p]
    have hGzero : G ((m₀ : n), m₀) = 0 := by
      simp only [hGdef, hVzero, mul_zero]
    have hfull : ∑ p : n × ↥t, G p = 0 := by
      have h1 : ∑ p ∈ Finset.univ.erase ((m₀ : n), m₀), G p =
          ∑ p : ReducedIndex t m₀, G (p : n × ↥t) :=
        Finset.sum_subtype (Finset.univ.erase ((m₀ : n), m₀)) (fun x => by simp) G
      have h2 : ∑ p ∈ Finset.univ.erase ((m₀ : n), m₀), G p = ∑ p : n × ↥t, G p := by
        refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
        have hxx : x = ((m₀ : n), m₀) := by
          by_contra hne
          exact hx (Finset.mem_erase.2 ⟨hne, Finset.mem_univ x⟩)
        rw [hxx, hGzero]
      rw [← h2, h1, Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hGsub p]
      exact hq
    rw [Fintype.sum_prod_type] at hfull
    have hterm : ∀ (k : n) (c : ↥t), G (k, c) =
        (if k = (q : n × ↥t).1 then P c (q : n × ↥t).2 * V (k, c) else 0) -
          (if k = (c : n) then
            (if (m₀ : n) = (q : n × ↥t).1 then
              P m₀ (q : n × ↥t).2 * V (k, c) else 0) else 0) := by
      intro k c
      simp only [hGdef]
      by_cases h1 : k = (q : n × ↥t).1 <;> by_cases h2 : k = (c : n) <;>
        by_cases h3 : (m₀ : n) = (q : n × ↥t).1 <;>
        simp [h1, h2, h3, sub_mul]
    have hsplit : ∑ k : n, ∑ c : ↥t, G (k, c) =
        (∑ k : n, ∑ c : ↥t,
          (if k = (q : n × ↥t).1 then P c (q : n × ↥t).2 * V (k, c) else 0)) -
        (∑ k : n, ∑ c : ↥t,
          (if k = (c : n) then
            (if (m₀ : n) = (q : n × ↥t).1 then
              P m₀ (q : n × ↥t).2 * V (k, c) else 0) else 0)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => hterm k c
    have hfirst : (∑ k : n, ∑ c : ↥t,
        (if k = (q : n × ↥t).1 then P c (q : n × ↥t).2 * V (k, c) else 0)) =
        (row (q : n × ↥t).1 ᵥ* P) (q : n × ↥t).2 := by
      rw [Finset.sum_eq_single (q : n × ↥t).1]
      · have hin : ∀ c : ↥t, (if (q : n × ↥t).1 = (q : n × ↥t).1 then
            P c (q : n × ↥t).2 * V ((q : n × ↥t).1, c) else 0) =
            V ((q : n × ↥t).1, c) * P c (q : n × ↥t).2 := fun c => by
          rw [if_pos rfl, mul_comm]
        rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hin c, Matrix.vecMul]
        rfl
      · intro k _ hk
        exact Finset.sum_eq_zero fun c _ => if_neg hk
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    have hsecond : (∑ k : n, ∑ c : ↥t,
        (if k = (c : n) then
          (if (m₀ : n) = (q : n × ↥t).1 then
            P m₀ (q : n × ↥t).2 * V (k, c) else 0) else 0)) =
        (if (m₀ : n) = (q : n × ↥t).1 then τ * P m₀ (q : n × ↥t).2 else 0) := by
      by_cases h3 : (m₀ : n) = (q : n × ↥t).1
      · rw [if_pos h3, hτdef, Finset.sum_mul, Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_eq_single (c : n)]
        · rw [if_pos rfl, if_pos h3, mul_comm]
        · intro k _ hk
          rw [if_neg hk]
        · intro hcon
          exact absurd (Finset.mem_univ _) hcon
      · rw [if_neg h3]
        refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun c _ => ?_
        by_cases h2 : k = (c : n)
        · rw [if_pos h2, if_neg h3]
        · rw [if_neg h2]
    rw [hsplit, hfirst, hsecond] at hfull
    exact sub_eq_zero.1 hfull
  have hrow_off : ∀ k : n, k ≠ (m₀ : n) → row k = 0 := by
    intro k hk
    have hzero : row k ᵥ* P = 0 := by
      funext c'
      have hqne : ((k, c') : n × ↥t) ≠ ((m₀ : n), m₀) := fun h => hk (congrArg Prod.fst h)
      have h := hkey ⟨(k, c'), hqne⟩
      rw [if_neg fun hcon => hk hcon.symm] at h
      exact h
    have h := congrArg (fun w => w ᵥ* P⁻¹) hzero
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hPunit, Matrix.vecMul_one] using h
  have hτzero : τ = 0 := by
    rw [hτdef]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases eq_or_ne c m₀ with rfl | hc
    · exact hVzero
    · exact congrFun (hrow_off (c : n) fun h => hc (Subtype.ext h)) c
  have hrow_m₀ : row (m₀ : n) = 0 := by
    set y : ↥t → HomogeneousJetField n K := row (m₀ : n) ᵥ* P with hydef
    have hyoff : ∀ c' : ↥t, c' ≠ m₀ → y c' = 0 := by
      intro c' hc'
      have hqne : (((m₀ : n), c') : n × ↥t) ≠ ((m₀ : n), m₀) := fun h =>
        hc' (congrArg Prod.snd h)
      have h := hkey ⟨((m₀ : n), c'), hqne⟩
      rw [if_pos rfl, hτzero, zero_mul] at h
      exact h
    have hback : row (m₀ : n) = y ᵥ* P⁻¹ := by
      rw [hydef, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hPunit, Matrix.vecMul_one]
    have hrowval : ∀ c : ↥t, row (m₀ : n) c = y m₀ * P⁻¹ m₀ c := by
      intro c
      have h1 : row (m₀ : n) c = ∑ c' : ↥t, y c' * P⁻¹ c' c := by
        rw [hback, Matrix.vecMul]
        rfl
      rw [h1, Finset.sum_eq_single m₀]
      · intro c' _ hc'
        rw [hyoff c' hc', zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    have hy0 : y m₀ = 0 := by
      have h := hrowval m₀
      rw [show row (m₀ : n) m₀ = V ((m₀ : n), m₀) from rfl, hVzero] at h
      rcases mul_eq_zero.1 h.symm with h1 | h2
      · exact h1
      · exact absurd h2 (jetFrame_inv_diag_ne_zero t m₀)
    funext c
    rw [hrowval c, hy0, zero_mul]
    rfl
  refine hv0 ?_
  funext p
  have hrow : row (p : n × ↥t).1 = 0 := by
    rcases eq_or_ne (p : n × ↥t).1 (m₀ : n) with h | h
    · rw [h]
      exact hrow_m₀
    · exact hrow_off _ h
  rw [← hVcoe p]
  show V ((p : n × ↥t).1, (p : n × ↥t).2) = 0
  exact congrFun hrow (p : n × ↥t).2

/-! ## Algebraic independence and the codimension -/

/-- **The reduced block is algebraically independent over the horizon field.** -/
theorem algebraicIndependent_reducedFamily [CharZero K] (t : Finset n) (m₀ : ↥t) :
    AlgebraicIndependent ↥(horizonField (K := K) (↑t : Set n)) (reducedFamily (K := K) t m₀) := by
  classical
  haveI : CharZero ↥(horizonField (K := K) (↑t : Set n)) :=
    charZero_of_injective_algebraMap
      (algebraMap K ↥(horizonField (K := K) (↑t : Set n))).injective
  refine algebraicIndependent_of_domain_jacobian
    (K := ↥(horizonField (K := K) (↑t : Set n)))
    (R := HomogeneousJetField n K)
    (reducedFamily t m₀)
    (fun i f => jetDerivation (reducedGen t m₀ (i : n × ↥t)) f)
    (fun i a b => map_add _ a b)
    (fun i a b => by
      rw [Derivation.leibniz]
      simp only [smul_eq_mul])
    (fun i c => ?_)
    (observerJacobian t m₀) (observerJacobian_det_ne_zero t m₀)
    (fun i j => rfl)
  show jetDerivation (reducedGen t m₀ (i : n × ↥t)) ((c : HomogeneousJetField n K)) = 0
  exact jetDerivation_eq_zero_of_mem_span (reducedGen_mem_span t m₀ i.2) c.2

omit [Fintype n] [DecidableEq n] in
theorem range_reducedFamily (t : Finset n) (m₀ : ↥t) :
    Set.range (reducedFamily (K := K) t m₀) = reducedJetBlock t m₀ K := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q : n × ↥t), q.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- **The codimension of the horizon field of a covector span.**  For a span of rank `r` in `N`
directions the horizon field together with `rN-1` jet coordinates generates the whole jet field,
and those `rN-1` coordinates are algebraically independent over the horizon field: the
transcendence degree of the jet field over the horizon field of the span is exactly `rN-1`. -/
theorem horizonField_transcendence_degree [CharZero K] (t : Finset n) (m₀ : ↥t) :
    IntermediateField.adjoin K (reducedFrameGenerators t m₀ K) = ⊤ ∧
      AlgebraicIndependent ↥(horizonField (K := K) (↑t : Set n))
        (reducedFamily (K := K) t m₀) ∧
      Nat.card (ReducedIndex t m₀) = Nat.card n * t.card - 1 :=
  ⟨reducedFrameGenerators_adjoin_eq_top t m₀, algebraicIndependent_reducedFamily t m₀,
    card_reducedJetBlockIndex t m₀⟩

end

end GaloisForLFunctions.HTGeometry
