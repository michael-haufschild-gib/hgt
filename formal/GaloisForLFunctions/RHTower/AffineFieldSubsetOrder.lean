import GaloisForLFunctions.RHTower.SignedScalarMergeOrder

/-!
# Complete subset orders from increasing marginals and affine fields

Increasing insertion marginals admit a distinct complete order below the
larger endpoint value. A contracting first insertion permits induction; if
none exists, every later insertion is nondecreasing and the final endpoint
bounds all intermediate subsets. Two such block orders require only their
shared separating endpoint in addition. Cauchy–Schwarz also splits any affine
field family into two classes with nonnegative pair inner products, using
the sign of its inner product with the common direction.
-/

noncomputable section
open Finset
namespace RHTower
variable {α ι : Type*} [DecidableEq α]


private theorem subset_value_le_of_increments (F : Finset α → ℝ) (P U : Finset α) (hPU : P⊆U)
    (hstep : ∀ S⊆U,∀ q∈U,q∉S → F S≤F (insert q S)) : F P≤F U := by
  have h : F P≤F (P∪(U\P)) := by
    refine Finset.induction_on' (motive := fun S => F P≤F (P∪S)) (U\P) ?_ ?_
    · simp
    · intro q S hq hS hqS ih
      have hqP : q∉P := (mem_sdiff.mp hq).2
      have hPS : P∪S⊆U := union_subset hPU (hS.trans sdiff_subset)
      have hqPS : q∉P∪S := by simp [hqP,hqS]
      have hs := hstep (P∪S) hPS q (mem_sdiff.mp hq).1 hqPS
      simpa only [union_insert] using ih.trans hs
  rwa [union_sdiff_of_subset hPU] at h

private theorem increasing_marginal_safe_first (F : Finset α → ℝ) (U : Finset α)
    (hU : U.Nonempty)
    (hinc : ∀ A B : Finset α,A⊆B → B⊆U → ∀ p∈U,p∉B →
      F (insert p A)-F A≤F (insert p B)-F B) :
    ∃ p∈U,F {p}≤max (F ∅) (F U) := by
  by_cases h : ∃ p∈U,F {p}≤F ∅
  · obtain ⟨p,hp,he⟩ := h
    exact ⟨p,hp,he.trans (le_max_left _ _)⟩
  · obtain ⟨p,hp⟩ := hU
    refine ⟨p,hp,(subset_value_le_of_increments F {p} U (by simpa using hp) ?_).trans (le_max_right _ _)⟩
    intro S hSU q hq hqS
    have hq0 : F ∅<F {q} := lt_of_not_ge (fun hn => h ⟨q,hq,hn⟩)
    have hi := hinc ∅ S (empty_subset _) hSU q hq hqS
    simp only [insert_empty_eq] at hi
    linarith only [hq0,hi]

/-- Increasing insertion marginals admit a complete distinct order below the larger endpoint value. -/
theorem exists_increasingMarginalSubsetOrder (F : Finset α → ℝ) (U : Finset α)
    (hinc : ∀ A B : Finset α,A⊆B → B⊆U → ∀ p∈U,p∉B →
      F (insert p A)-F A≤F (insert p B)-F B) :
    ∃ l : List α,l.Nodup ∧ l.toFinset=U ∧ ∀ k : ℕ,
      F (l.take k).toFinset≤max (F ∅) (F U) := by
  revert F
  refine Finset.strongInductionOn U ?_
  intro U ih F hinc
  by_cases hU : U.Nonempty
  · obtain ⟨p,hp,hsafe⟩ := increasing_marginal_safe_first F U hU hinc
    have hinc' : ∀ A B : Finset α,A⊆B → B⊆U.erase p → ∀ q∈U.erase p,q∉B →
        F (insert p (insert q A))-F (insert p A)≤
          F (insert p (insert q B))-F (insert p B) := by
      intro A B hAB hBU q hq hqB
      have hqP : q≠p := (mem_erase.mp hq).1
      have hi := hinc (insert p A) (insert p B) (insert_subset_insert p hAB)
        (insert_subset hp (hBU.trans (erase_subset p U))) q (mem_erase.mp hq).2
        (by simp [hqP,hqB])
      simpa only [insert_comm p q] using hi
    obtain ⟨l,hl,hset,hbound⟩ := ih (U.erase p) (erase_ssubset hp) (fun S => F (insert p S)) hinc'
    have hpL : p∉l := by
      intro h
      have hm := List.mem_toFinset.mpr h
      rw [hset] at hm
      exact notMem_erase p U hm
    refine ⟨p::l,List.nodup_cons.mpr ⟨hpL,hl⟩,?_,?_⟩
    · simp [hset,insert_erase hp]
    · intro k
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.take_succ_cons,List.toFinset_cons]
        refine (hbound k).trans ?_
        simp only [insert_empty_eq,insert_erase hp]
        exact max_le hsafe (le_max_right _ _)
  · have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    subst U
    exact ⟨[],by simp,by simp,by simp⟩

omit [DecidableEq α] in
/-- Two points on an affine field have nonnegative inner product whenever their transverse coordinates have the same sign. -/
theorem affineField_inner_nonneg_of_transverse_product (I : Finset ι) (A D : ι → ℝ) (t u : ℝ)
    (htrans : 0≤(∑ i∈I,(A i+t*D i)*D i)*(∑ i∈I,(A i+u*D i)*D i)) :
    0≤∑ i∈I,(A i+t*D i)*(A i+u*D i) := by
  let H := ∑ i∈I,(A i)^2
  let C := ∑ i∈I,A i*D i
  let Q := ∑ i∈I,(D i)^2
  have hH : 0≤H := sum_nonneg (fun i _ => sq_nonneg _)
  have hQ : 0≤Q := sum_nonneg (fun i _ => sq_nonneg _)
  have hc : C^2≤H*Q := Finset.sum_mul_sq_le_sq_mul_sq I A D
  have hproj (v : ℝ) : (∑ i∈I,(A i+v*D i)*D i)=C+v*Q := by
    calc
      _ = ∑ i∈I,(A i*D i+v*(D i)^2) := sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [sum_add_distrib,← mul_sum]
  have hgram : (∑ i∈I,(A i+t*D i)*(A i+u*D i))=H+(t+u)*C+t*u*Q := by
    calc
      _ = ∑ i∈I,((A i)^2+(t+u)*(A i*D i)+t*u*(D i)^2) :=
        sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [sum_add_distrib,sum_add_distrib,← mul_sum,← mul_sum]
  rw [hproj,hproj] at htrans
  rw [hgram]
  by_cases hQ0 : Q=0
  · rw [hQ0,mul_zero] at hc
    have hC0 : C=0 := by nlinarith only [hc,sq_nonneg C]
    simp only [hQ0,hC0,mul_zero,add_zero]
    exact hH
  · have hQp : 0<Q := lt_of_le_of_ne hQ (Ne.symm hQ0)
    have hprod : 0≤Q*(H+(t+u)*C+t*u*Q) := by
      nlinarith only [hc,htrans]
    exact nonneg_of_mul_nonneg_right hprod hQp

/-- Two complete block orders combine with only their shared separating endpoint added to the ceiling. -/
theorem exists_twoBlockSubsetOrder (F : Finset α → ℝ) (A B : Finset α)
    (hdis : Disjoint A B)
    (ha : ∃ l : List α,l.Nodup ∧ l.toFinset=A ∧ ∀ k : ℕ,
      F (l.take k).toFinset≤max (F ∅) (F A))
    (hb : ∃ l : List α,l.Nodup ∧ l.toFinset=B ∧ ∀ k : ℕ,
      F (A∪(l.take k).toFinset)≤max (F A) (F (A∪B))) :
    ∃ l : List α,l.Nodup ∧ l.toFinset=A∪B ∧ ∀ k : ℕ,
      F (l.take k).toFinset≤max (F ∅) (max (F A) (F (A∪B))) := by
  obtain ⟨la,hla,hseta,hba⟩ := ha
  obtain ⟨lb,hlb,hsetb,hbb⟩ := hb
  have hld : ∀ p∈la,∀ q∈lb,p≠q := by
    intro p hpa q hqb hpq
    have ha : p∈A := hseta ▸ List.mem_toFinset.mpr hpa
    have hb : q∈B := hsetb ▸ List.mem_toFinset.mpr hqb
    exact disjoint_left.mp hdis ha (hpq.symm ▸ hb)
  refine ⟨la++lb,List.nodup_append.mpr ⟨hla,hlb,hld⟩,?_,?_⟩
  · simp only [List.toFinset_append,hseta,hsetb]
  · intro k
    by_cases hk : k≤la.length
    · rw [List.take_append_of_le_length hk]
      exact (hba k).trans (max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _)))
    · rw [List.take_append,List.take_of_length_le (by omega : la.length≤k),List.toFinset_append,hseta]
      exact (hbb (k-la.length)).trans (le_max_right _ _)

end RHTower
