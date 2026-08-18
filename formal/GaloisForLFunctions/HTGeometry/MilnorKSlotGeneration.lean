import GaloisForLFunctions.HTGeometry.MilnorWittWittComparison

/-!
# Slot-wise generation of Milnor `K`-theory

Each slot of a Milnor symbol is a homomorphism of the unit group, so membership of symbol classes in
a subgroup of `K_n^M(K)` propagates along any generating set of `Kˣ`, one slot at a time.  The
degree-two case is `symbolSubgroup_closure_le`; this is the statement in every degree, and it is what
makes the degree filtration of Milnor's exact sequence exhaustive: the nonzero polynomials generate
`(F(t))ˣ`, so every symbol class of `K_n^M(F(t))` is a combination of classes of *polynomial*
symbols.

* `milnorClassDeg_one_of_eq` : a symbol with a `1` in some slot has vanishing class.
* `milnorClassDeg_inv_of_eq` : inverting one slot negates the class.
* `milnorClassDeg_mem_of_generating` : **slot-wise generation.**
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- A symbol with a `1` in some slot has vanishing class. -/
theorem milnorClassDeg_one_of_eq {n : ℕ} (l₁ l₂ : List Kˣ) {L : List Kˣ}
    (hL : L = l₁ ++ (1 : Kˣ) :: l₂) (p : L.length = n) :
    milnorClassDeg K n ⟨L, p⟩ = 0 := by
  have h := milnorClassDeg_mul_of_eq (F := K) (1 : Kˣ) (1 : Kˣ) l₁ l₂
    (Lab := L) (La := L) (Lb := L) (by rw [hL, one_mul]) hL hL p p p
  have h2 : milnorClassDeg K n ⟨L, p⟩ + 0
      = milnorClassDeg K n ⟨L, p⟩ + milnorClassDeg K n ⟨L, p⟩ := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- Inverting one slot negates the class. -/
theorem milnorClassDeg_inv_of_eq {n : ℕ} (b : Kˣ) (l₁ l₂ : List Kˣ)
    {Lb Li : List Kˣ} (hb : Lb = l₁ ++ b :: l₂) (hi : Li = l₁ ++ b⁻¹ :: l₂)
    (pb : Lb.length = n) (pi : Li.length = n) :
    milnorClassDeg K n ⟨Li, pi⟩ = -milnorClassDeg K n ⟨Lb, pb⟩ := by
  have hone : (l₁ ++ (1 : Kˣ) :: l₂).length = n := by
    rw [hb] at pb
    simpa using pb
  have h := milnorClassDeg_mul_of_eq (F := K) b b⁻¹ l₁ l₂
    (Lab := l₁ ++ (1 : Kˣ) :: l₂) (La := Lb) (Lb := Li) (by rw [mul_inv_cancel]) hb hi
    hone pb pi
  rw [milnorClassDeg_one_of_eq l₁ l₂ rfl hone] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **Slot-wise generation.**  If a subgroup of `K_n^M(K)` contains the classes of all symbols whose
entries lie in a generating set of `Kˣ`, then it contains every symbol class. -/
theorem milnorClassDeg_mem_of_generating {n : ℕ} (S : AddSubgroup (MilnorKDeg K n))
    {G : Set Kˣ} (hG : Subgroup.closure G = ⊤)
    (hS : ∀ (l : List Kˣ) (p : l.length = n), (∀ a ∈ l, a ∈ G) →
      milnorClassDeg K n ⟨l, p⟩ ∈ S) :
    ∀ (l : List Kˣ) (p : l.length = n), milnorClassDeg K n ⟨l, p⟩ ∈ S := by
  classical
  have key : ∀ (l₂ l₁ : List Kˣ) (p : (l₁ ++ l₂).length = n), (∀ a ∈ l₁, a ∈ G) →
      milnorClassDeg K n ⟨l₁ ++ l₂, p⟩ ∈ S := by
    intro l₂
    induction l₂ with
    | nil =>
        intro l₁ p h1
        refine hS (l₁ ++ []) p ?_
        intro a ha
        rw [List.append_nil] at ha
        exact h1 a ha
    | cons a t ih =>
        intro l₁ p h1
        have hlen : ∀ b : Kˣ, (l₁ ++ b :: t).length = n := by
          intro b
          simpa using p
        set T : Subgroup Kˣ :=
          { carrier := {b | milnorClassDeg K n ⟨l₁ ++ b :: t, hlen b⟩ ∈ S}
            one_mem' := by
              show milnorClassDeg K n ⟨l₁ ++ (1 : Kˣ) :: t, hlen 1⟩ ∈ S
              rw [milnorClassDeg_one_of_eq l₁ t rfl (hlen 1)]
              exact S.zero_mem
            mul_mem' := by
              intro x y hx hy
              show milnorClassDeg K n ⟨l₁ ++ (x * y) :: t, hlen (x * y)⟩ ∈ S
              rw [milnorClassDeg_mul_of_eq (F := K) x y l₁ t rfl rfl rfl
                (hlen (x * y)) (hlen x) (hlen y)]
              exact S.add_mem hx hy
            inv_mem' := by
              intro x hx
              show milnorClassDeg K n ⟨l₁ ++ x⁻¹ :: t, hlen x⁻¹⟩ ∈ S
              rw [milnorClassDeg_inv_of_eq x l₁ t rfl rfl (hlen x) (hlen x⁻¹)]
              exact S.neg_mem hx } with hT
        have hGT : G ⊆ (T : Set Kˣ) := by
          intro b hb
          show milnorClassDeg K n ⟨l₁ ++ b :: t, hlen b⟩ ∈ S
          have happ : (l₁ ++ [b]) ++ t = l₁ ++ b :: t := by
            rw [List.append_assoc, List.singleton_append]
          have hlen' : ((l₁ ++ [b]) ++ t).length = n := by
            rw [happ]
            exact hlen b
          have hmem := ih (l₁ ++ [b]) hlen' (by
            intro c hc
            rcases List.mem_append.1 hc with hc' | hc'
            · exact h1 c hc'
            · rw [List.mem_singleton.1 hc']
              exact hb)
          have : milnorClassDeg K n ⟨(l₁ ++ [b]) ++ t, hlen'⟩
              = milnorClassDeg K n ⟨l₁ ++ b :: t, hlen b⟩ :=
            congrArg (milnorClassDeg K n) (Subtype.ext happ)
          rwa [this] at hmem
        have hTop : T = ⊤ := by
          refine eq_top_iff.2 ?_
          rw [← hG]
          exact (Subgroup.closure_le T).2 hGT
        have : a ∈ T := by rw [hTop]; exact Subgroup.mem_top a
        exact this
  intro l p
  have h := key l [] (by simpa using p) (by simp)
  have heq : milnorClassDeg K n ⟨[] ++ l, by simpa using p⟩
      = milnorClassDeg K n ⟨l, p⟩ :=
    congrArg (milnorClassDeg K n) (Subtype.ext (List.nil_append l))
  rwa [heq] at h

end GaloisForLFunctions.HTGeometry
