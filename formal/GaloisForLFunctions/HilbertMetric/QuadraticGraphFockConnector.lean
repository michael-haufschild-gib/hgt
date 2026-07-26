import GaloisForLFunctions.HilbertMetric.QuadraticGraphCompletion
import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# The symmetric-Fock connector of the quadratic graph completion law

`QuadraticGraphCompletion` proves the two finite algebraic layers of the quadratic graph
completion law.  This module supplies the connector: it realises the subspace

```text
S_L = ℝΩ ⊕ E ⊕ {q + L q : q ∈ T},      T ⊆ Sym²(E),   L : T → W,
```

inside the truncated symmetric Fock space of degrees at most two over the mode set `E ⊕ W`, and
computes the squared norm of the top exterior vector of its degree-dilated spanning family:

```text
Z_L(t) = t^(e+m) det (t I + Lᵀ L).
```

* `HilbertMetric.quadFockAnnihilation_mem_quadraticGraphSubspace` — annihilation invariance of
  `S_L`, for the canonical symmetric-Fock lowering operators of `SymmetricFockShadow`;
* `HilbertMetric.quadFockGram_quadFockFamily` — the exact block Gram of the dilated family;
* `HilbertMetric.quadraticFockVolume_eq` — the determinant law;
* `HilbertMetric.quadraticGraphCompletion_invariant_and_volume` — both together.

The degree-two family `q` is only required to be orthonormal; no genericity, rank, or
graded-splitting assumption is used, so the statement covers every quadratic graph completion.

The three homogeneous channels are handled by `quadDegZero`, `quadDegOne`, `quadDegTwo`, whose
mutual inner products are computed once and for all.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {e : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- One-particle modes: `e` base modes and the transverse modes `κ`. -/
abbrev QuadMode (e : ℕ) (κ : Type*) := Fin e ⊕ κ

/-- Orthonormal index set of the truncated symmetric Fock space of degrees at most two. -/
abbrev QuadFockIdx (e : ℕ) (κ : Type*) [DecidableEq κ] :=
  Sym (QuadMode e κ) 0 ⊕ Sym (QuadMode e κ) 1 ⊕ Sym (QuadMode e κ) 2

/-- Homogeneous Fock degree of a basis index. -/
def quadFockDegree : QuadFockIdx e κ → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- Degree dilation: homogeneous degree `n` is scaled by `t ^ (n / 2)`. -/
def quadFockDilate (t : ℝ) (v : QuadFockIdx e κ → ℝ) : QuadFockIdx e κ → ℝ :=
  fun x => Real.sqrt t ^ quadFockDegree x * v x

/-- The degree-zero (vacuum) channel. -/
def quadDegZero (c : ℝ) : QuadFockIdx e κ → ℝ
  | Sum.inl _ => c
  | Sum.inr _ => 0

/-- The degree-one (one-particle) channel. -/
def quadDegOne (u : QuadMode e κ → ℝ) : QuadFockIdx e κ → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl α) => u (Sym.oneEquiv.symm α)
  | Sum.inr (Sum.inr _) => 0

/-- The degree-two channel. -/
def quadDegTwo (w : Sym (QuadMode e κ) 2 → ℝ) : QuadFockIdx e κ → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr β) => w β

/-- Euclidean inner product of two Fock coordinate vectors. -/
def quadFockInner (v w : QuadFockIdx e κ → ℝ) : ℝ := ∑ x, v x * w x

/-- Euclidean Gram matrix of a family of Fock coordinate vectors. -/
def quadFockGram {ι : Type*} (v : ι → QuadFockIdx e κ → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => quadFockInner (v i) (v j)

/-! ### The three channels are mutually orthogonal -/

private theorem sum_quadFockIdx {M : Type*} [AddCommMonoid M] (f : QuadFockIdx e κ → M) :
    ∑ x, f x = (∑ a : Sym (QuadMode e κ) 0, f (Sum.inl a))
      + ((∑ α : Sym (QuadMode e κ) 1, f (Sum.inr (Sum.inl α)))
        + ∑ β : Sym (QuadMode e κ) 2, f (Sum.inr (Sum.inr β))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]

theorem quadFockInner_degZero_degZero (a b : ℝ) :
    quadFockInner (e := e) (κ := κ) (quadDegZero a) (quadDegZero b) = a * b := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegZero]

theorem quadFockInner_degZero_degOne (a : ℝ) (u : QuadMode e κ → ℝ) :
    quadFockInner (quadDegZero a) (quadDegOne u) = 0 := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegZero, quadDegOne]

theorem quadFockInner_degZero_degTwo (a : ℝ) (w : Sym (QuadMode e κ) 2 → ℝ) :
    quadFockInner (quadDegZero a) (quadDegTwo w) = 0 := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegZero, quadDegTwo]

theorem quadFockInner_degOne_degZero (u : QuadMode e κ → ℝ) (a : ℝ) :
    quadFockInner (quadDegOne u) (quadDegZero a) = 0 := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegZero, quadDegOne]

theorem quadFockInner_degTwo_degZero (w : Sym (QuadMode e κ) 2 → ℝ) (a : ℝ) :
    quadFockInner (quadDegTwo w) (quadDegZero a) = 0 := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegZero, quadDegTwo]

theorem quadFockInner_degOne_degTwo (u : QuadMode e κ → ℝ) (w : Sym (QuadMode e κ) 2 → ℝ) :
    quadFockInner (quadDegOne u) (quadDegTwo w) = 0 := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegOne, quadDegTwo]

theorem quadFockInner_degTwo_degOne (w : Sym (QuadMode e κ) 2 → ℝ) (u : QuadMode e κ → ℝ) :
    quadFockInner (quadDegTwo w) (quadDegOne u) = 0 := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegOne, quadDegTwo]

theorem quadFockInner_degOne_degOne (u v : QuadMode e κ → ℝ) :
    quadFockInner (quadDegOne u) (quadDegOne v) = ∑ i : QuadMode e κ, u i * v i := by
  rw [quadFockInner, sum_quadFockIdx]
  simp only [quadDegOne, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
  exact Equiv.sum_comp Sym.oneEquiv.symm fun i => u i * v i

theorem quadFockInner_degTwo_degTwo (w z : Sym (QuadMode e κ) 2 → ℝ) :
    quadFockInner (quadDegTwo w) (quadDegTwo z) = ∑ β, w β * z β := by
  rw [quadFockInner, sum_quadFockIdx]
  simp [quadDegTwo]

theorem quadFockInner_add_left (u v w : QuadFockIdx e κ → ℝ) :
    quadFockInner (u + v) w = quadFockInner u w + quadFockInner v w := by
  rw [quadFockInner, quadFockInner, quadFockInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by simp [add_mul]

theorem quadFockInner_add_right (u v w : QuadFockIdx e κ → ℝ) :
    quadFockInner u (v + w) = quadFockInner u v + quadFockInner u w := by
  rw [quadFockInner, quadFockInner, quadFockInner, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by simp [mul_add]

/-! ### Degree dilation acts channelwise -/

omit [Fintype κ] in
theorem quadFockDilate_degZero (t : ℝ) (c : ℝ) :
    quadFockDilate (e := e) (κ := κ) t (quadDegZero c) = quadDegZero c := by
  funext x
  cases x with
  | inl a => simp [quadFockDilate, quadFockDegree, quadDegZero]
  | inr y => cases y <;> simp [quadFockDilate, quadDegZero]

omit [Fintype κ] in
theorem quadFockDilate_degOne (t : ℝ) (u : QuadMode e κ → ℝ) :
    quadFockDilate t (quadDegOne u) = quadDegOne (fun i => Real.sqrt t * u i) := by
  funext x
  cases x with
  | inl a => simp [quadFockDilate, quadFockDegree, quadDegOne]
  | inr y =>
      cases y with
      | inl α => simp [quadFockDilate, quadFockDegree, quadDegOne]
      | inr β => simp [quadFockDilate, quadFockDegree, quadDegOne]

omit [Fintype κ] in
theorem quadFockDilate_degTwo (t : ℝ) (ht : 0 ≤ t) (w : Sym (QuadMode e κ) 2 → ℝ) :
    quadFockDilate t (quadDegTwo w) = quadDegTwo (fun β => t * w β) := by
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  funext x
  cases x with
  | inl a => simp [quadFockDilate, quadFockDegree, quadDegTwo]
  | inr y =>
      cases y with
      | inl α => simp [quadFockDilate, quadFockDegree, quadDegTwo]
      | inr β => simp [quadFockDilate, quadFockDegree, quadDegTwo, hsq]

omit [Fintype κ] in
theorem quadFockDilate_add (t : ℝ) (u v : QuadFockIdx e κ → ℝ) :
    quadFockDilate t (u + v) = quadFockDilate t u + quadFockDilate t v := by
  funext x
  simp [quadFockDilate, mul_add]

/-! ### The spanning family of the quadratic graph completion -/

/-- The transverse one-particle vector `L q_r`. -/
def quadTransverseMode {m : ℕ} (L : Matrix κ (Fin m) ℝ) (r : Fin m) : QuadMode e κ → ℝ :=
  Sum.elim (fun _ => 0) (fun k => L k r)

/-- The dilated spanning family of `S_L`: the vacuum, the base modes, and the graph vectors. -/
def quadFockFamily {m : ℕ} (q : Fin m → Sym (QuadMode e κ) 2 → ℝ) (L : Matrix κ (Fin m) ℝ)
    (t : ℝ) : Unit ⊕ (Fin e ⊕ Fin m) → QuadFockIdx e κ → ℝ
  | Sum.inl _ => quadFockDilate t (quadDegZero 1)
  | Sum.inr (Sum.inl i) =>
      quadFockDilate t (quadDegOne fun u => if u = Sum.inl i then 1 else 0)
  | Sum.inr (Sum.inr r) =>
      quadFockDilate t (quadDegTwo (q r) + quadDegOne (quadTransverseMode L r))

/-- The squared norm of the top exterior vector of the dilated family. -/
def quadraticFockVolume {m : ℕ} (q : Fin m → Sym (QuadMode e κ) 2 → ℝ)
    (L : Matrix κ (Fin m) ℝ) (t : ℝ) : ℝ :=
  (quadFockGram (quadFockFamily q L t)).det

/-- **Exact block Gram of the dilated graph family.**  The vacuum, the base modes, and the graph
vectors occupy mutually orthogonal Fock channels except inside the graph block, whose Gram is the
quadratic graph Gram of `QuadraticGraphCompletion`. -/
theorem quadFockGram_quadFockFamily {m : ℕ}
    (q : Fin m → Sym (QuadMode e κ) 2 → ℝ) (L : Matrix κ (Fin m) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hq : ∀ r s, ∑ β, q r β * q s β = if r = s then 1 else 0) :
    quadFockGram (quadFockFamily q L t)
      = Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) 0 0
          (Matrix.fromBlocks (t • (1 : Matrix (Fin e) (Fin e) ℝ)) 0 0
            (quadraticGraphGram L t)) := by
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hmul : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  ext x y
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          simp only [quadFockGram, Matrix.of_apply, quadFockFamily, quadFockDilate_degZero,
            Matrix.fromBlocks_apply₁₁, quadFockInner_degZero_degZero, Matrix.one_apply_eq]
          norm_num
      | inr y' =>
          cases y' with
          | inl i =>
              simp [quadFockGram, quadFockFamily, quadFockDilate_degZero, quadFockDilate_degOne,
                quadFockInner_degZero_degOne]
          | inr r =>
              simp [quadFockGram, quadFockFamily, quadFockDilate_degZero, quadFockDilate_add,
                quadFockDilate_degOne, quadFockDilate_degTwo t ht,
                quadFockInner_add_right, quadFockInner_degZero_degOne,
                quadFockInner_degZero_degTwo]
  | inr x' =>
      cases x' with
      | inl i =>
          cases y with
          | inl b =>
              simp [quadFockGram, quadFockFamily, quadFockDilate_degZero, quadFockDilate_degOne,
                quadFockInner_degOne_degZero]
          | inr y' =>
              cases y' with
              | inl j =>
                  simp only [quadFockGram, Matrix.of_apply, quadFockFamily, quadFockDilate_degOne,
                    Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
                    quadFockInner_degOne_degOne, Matrix.smul_apply, Matrix.one_apply,
                    smul_eq_mul]
                  rw [Fintype.sum_sum_type]
                  simp only [Sum.inl.injEq]
                  rw [Finset.sum_eq_single i]
                  · by_cases hij : i = j
                    · subst hij; simp [hmul]
                    · simp [hij]
                  · intro b _ hb
                    simp [hb]
                  · intro hi
                    exact absurd (Finset.mem_univ i) hi
              | inr r =>
                  simp [quadFockGram, quadFockFamily, quadFockDilate_degOne, quadFockDilate_add,
                    quadFockDilate_degTwo t ht, quadFockInner_add_right,
                    quadFockInner_degOne_degTwo, quadFockInner_degOne_degOne,
                    quadTransverseMode]
      | inr r =>
          cases y with
          | inl b =>
              simp [quadFockGram, quadFockFamily, quadFockDilate_degZero, quadFockDilate_add,
                quadFockDilate_degOne, quadFockDilate_degTwo t ht, quadFockInner_add_left,
                quadFockInner_degOne_degZero, quadFockInner_degTwo_degZero]
          | inr y' =>
              cases y' with
              | inl j =>
                  simp [quadFockGram, quadFockFamily, quadFockDilate_degOne, quadFockDilate_add,
                    quadFockDilate_degTwo t ht, quadFockInner_add_left,
                    quadFockInner_degTwo_degOne, quadFockInner_degOne_degOne,
                    quadTransverseMode]
              | inr s =>
                  simp only [quadFockGram, Matrix.of_apply, quadFockFamily, quadFockDilate_add,
                    quadFockDilate_degOne, quadFockDilate_degTwo t ht,
                    Matrix.fromBlocks_apply₂₂, quadFockInner_add_left, quadFockInner_add_right,
                    quadFockInner_degTwo_degTwo, quadFockInner_degTwo_degOne,
                    quadFockInner_degOne_degTwo, quadFockInner_degOne_degOne, add_zero, zero_add]
                  rw [quadraticGraphGram_eq L t ht]
                  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
                    Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
                  have hdeg2 : ∑ β : Sym (QuadMode e κ) 2, t * q r β * (t * q s β)
                      = t ^ 2 * (if r = s then 1 else 0) := by
                    rw [← hq r s, Finset.mul_sum]
                    exact Finset.sum_congr rfl fun β _ => by ring
                  have hdeg1 : ∑ i : QuadMode e κ,
                      Real.sqrt t * quadTransverseMode L r i *
                        (Real.sqrt t * quadTransverseMode L s i)
                      = t * ∑ k : κ, L k r * L k s := by
                    rw [Fintype.sum_sum_type, Finset.mul_sum]
                    simp only [quadTransverseMode, Sum.elim_inl, Sum.elim_inr, mul_zero,
                      Finset.sum_const_zero, zero_add]
                    refine Finset.sum_congr rfl fun k _ => ?_
                    rw [show Real.sqrt t * L k r * (Real.sqrt t * L k s)
                        = Real.sqrt t * Real.sqrt t * (L k r * L k s) by ring, hmul]
                  rw [hdeg2, hdeg1]

/-- **Quadratic graph completion volume law.**  The squared norm of the top exterior vector of the
degree-dilated spanning family of `ℝΩ ⊕ E ⊕ {q + Lq}` is `t^(e+m) det (t I + Lᵀ L)`. -/
theorem quadraticFockVolume_eq {m : ℕ}
    (q : Fin m → Sym (QuadMode e κ) 2 → ℝ) (L : Matrix κ (Fin m) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hq : ∀ r s, ∑ β, q r β * q s β = if r = s then 1 else 0) :
    quadraticFockVolume q L t
      = t ^ (e + m) * (t • (1 : Matrix (Fin m) (Fin m) ℝ) + L.transpose * L).det := by
  rw [quadraticFockVolume, quadFockGram_quadFockFamily q L t ht hq,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    det_quadraticGraphGram L t ht, Matrix.det_smul]
  simp only [Matrix.det_one, Matrix.det_unique, Matrix.one_apply_eq, mul_one, one_mul,
    Fintype.card_fin, pow_add]
  ring

/-! ### Annihilation invariance of the quadratic graph completion -/

/-- The undilated spanning family of `S_L`. -/
def quadFockBasis {m : ℕ} (q : Fin m → Sym (QuadMode e κ) 2 → ℝ) (L : Matrix κ (Fin m) ℝ) :
    Unit ⊕ (Fin e ⊕ Fin m) → QuadFockIdx e κ → ℝ
  | Sum.inl _ => quadDegZero 1
  | Sum.inr (Sum.inl i) => quadDegOne fun u => if u = Sum.inl i then 1 else 0
  | Sum.inr (Sum.inr r) => quadDegTwo (q r) + quadDegOne (quadTransverseMode L r)

omit [Fintype κ] in
theorem quadFockFamily_eq_dilate {m : ℕ} (q : Fin m → Sym (QuadMode e κ) 2 → ℝ)
    (L : Matrix κ (Fin m) ℝ) (t : ℝ) (x : Unit ⊕ (Fin e ⊕ Fin m)) :
    quadFockFamily q L t x = quadFockDilate t (quadFockBasis q L x) := by
  cases x with
  | inl a => rfl
  | inr y => cases y with
    | inl i => rfl
    | inr r => rfl

/-- The annihilation-invariant quadratic graph completion `S_L = ℝΩ ⊕ E ⊕ {q + Lq}`. -/
def quadraticGraphSubspace {m : ℕ} (q : Fin m → Sym (QuadMode e κ) 2 → ℝ)
    (L : Matrix κ (Fin m) ℝ) : Submodule ℝ (QuadFockIdx e κ → ℝ) :=
  Submodule.span ℝ (Set.range (quadFockBasis q L))

/-- Mode-`i` annihilation on the truncated Fock space, assembled from the canonical
symmetric-Fock lowering matrices of `SymmetricFockShadow`. -/
def quadFockAnnihilation (i : QuadMode e κ) (v : QuadFockIdx e κ → ℝ) : QuadFockIdx e κ → ℝ
  | Sum.inl a => ∑ α : Sym (QuadMode e κ) 1,
      symmetricFockAnnihilationMatrix 0 i a α * v (Sum.inr (Sum.inl α))
  | Sum.inr (Sum.inl α) => ∑ β : Sym (QuadMode e κ) 2,
      symmetricFockAnnihilationMatrix 1 i α β * v (Sum.inr (Sum.inr β))
  | Sum.inr (Sum.inr _) => 0

theorem quadFockAnnihilation_add (i : QuadMode e κ) (v w : QuadFockIdx e κ → ℝ) :
    quadFockAnnihilation i (v + w)
      = quadFockAnnihilation i v + quadFockAnnihilation i w := by
  funext x
  cases x with
  | inl a =>
      simp only [quadFockAnnihilation, Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
  | inr y =>
      cases y with
      | inl α =>
          simp only [quadFockAnnihilation, Pi.add_apply, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun β _ => by ring
      | inr β => simp [quadFockAnnihilation]

theorem quadFockAnnihilation_smul (i : QuadMode e κ) (c : ℝ) (v : QuadFockIdx e κ → ℝ) :
    quadFockAnnihilation i (c • v) = c • quadFockAnnihilation i v := by
  funext x
  cases x with
  | inl a =>
      simp only [quadFockAnnihilation, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
  | inr y =>
      cases y with
      | inl α =>
          simp only [quadFockAnnihilation, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun β _ => by ring
      | inr β => simp [quadFockAnnihilation]

theorem quadFockAnnihilation_degZero (i : QuadMode e κ) (c : ℝ) :
    quadFockAnnihilation i (quadDegZero c) = 0 := by
  funext x
  cases x with
  | inl a => simp [quadFockAnnihilation, quadDegZero]
  | inr y => cases y <;> simp [quadFockAnnihilation, quadDegZero]

omit [Fintype κ] [DecidableEq κ] in
private theorem oneEquiv_eq_cons_nil (i : QuadMode e κ) :
    (Sym.oneEquiv i : Sym (QuadMode e κ) 1) = i ::ₛ (Sym.nil : Sym (QuadMode e κ) 0) := by
  apply Subtype.ext
  rfl

theorem quadFockAnnihilation_degOne (i : QuadMode e κ) (u : QuadMode e κ → ℝ) :
    quadFockAnnihilation i (quadDegOne u) = quadDegZero (u i) := by
  funext x
  cases x with
  | inl a =>
      have ha : a = Sym.nil := Subsingleton.elim _ _
      subst ha
      simp only [quadFockAnnihilation, quadDegOne, quadDegZero]
      rw [Finset.sum_eq_single (Sym.oneEquiv i)]
      · rw [symmetricFockAnnihilationMatrix, if_pos (oneEquiv_eq_cons_nil i),
          Equiv.symm_apply_apply]
        have hcount : Multiset.count i
            ((Sym.oneEquiv i : Sym (QuadMode e κ) 1) : Multiset (QuadMode e κ)) = 1 := by
          simp [Sym.oneEquiv_apply]
        rw [hcount]
        norm_num
      · intro α _ hα
        rw [symmetricFockAnnihilationMatrix, if_neg, zero_mul]
        rw [← oneEquiv_eq_cons_nil i]
        exact hα
      · intro h
        exact absurd (Finset.mem_univ _) h
  | inr y => cases y <;> simp [quadFockAnnihilation, quadDegOne, quadDegZero]

/-- The canonical one-mode lowering of a degree-two coordinate vector. -/
def quadLower (i : QuadMode e κ) (w : Sym (QuadMode e κ) 2 → ℝ) : QuadMode e κ → ℝ :=
  fun j => ∑ β : Sym (QuadMode e κ) 2,
    symmetricFockAnnihilationMatrix 1 i (Sym.oneEquiv j) β * w β

theorem quadFockAnnihilation_degTwo (i : QuadMode e κ) (w : Sym (QuadMode e κ) 2 → ℝ) :
    quadFockAnnihilation i (quadDegTwo w) = quadDegOne (quadLower i w) := by
  funext x
  cases x with
  | inl a => simp [quadFockAnnihilation, quadDegTwo, quadDegOne]
  | inr y =>
      cases y with
      | inl α =>
          simp only [quadFockAnnihilation, quadDegTwo, quadDegOne, quadLower]
          rw [Equiv.apply_symm_apply]
      | inr β => simp [quadFockAnnihilation, quadDegOne]

/-- A degree-two vector supported on base multisets lowers into the base modes. -/
theorem quadLower_transverse_eq_zero (i : QuadMode e κ) (w : Sym (QuadMode e κ) 2 → ℝ)
    (hw : ∀ β : Sym (QuadMode e κ) 2,
      (∃ k : κ, Sum.inr k ∈ (β : Multiset (QuadMode e κ))) → w β = 0) (k : κ) :
    quadLower i w (Sum.inr k) = 0 := by
  rw [quadLower]
  refine Finset.sum_eq_zero fun β _ => ?_
  by_cases hβ : β = i ::ₛ (Sym.oneEquiv (Sum.inr k) : Sym (QuadMode e κ) 1)
  · have hmem : Sum.inr k ∈ (β : Multiset (QuadMode e κ)) := by
      rw [hβ]
      simp [Sym.oneEquiv_apply]
    rw [hw β ⟨k, hmem⟩, mul_zero]
  · rw [symmetricFockAnnihilationMatrix, if_neg hβ, zero_mul]

omit [Fintype κ] in
theorem quadDegZero_eq_smul (c : ℝ) :
    quadDegZero (e := e) (κ := κ) c = c • quadDegZero 1 := by
  funext x
  cases x with
  | inl a => simp [quadDegZero]
  | inr y => cases y <;> simp [quadDegZero]

omit [Fintype κ] in
theorem quadDegOne_eq_sum_base (u : QuadMode e κ → ℝ) (hu : ∀ k : κ, u (Sum.inr k) = 0) :
    quadDegOne u
      = ∑ j : Fin e, u (Sum.inl j) • quadDegOne fun x => if x = Sum.inl j then 1 else 0 := by
  funext x
  cases x with
  | inl a => simp [quadDegOne]
  | inr y =>
      cases y with
      | inl α =>
          simp only [quadDegOne, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
            mul_one, mul_zero]
          rcases hy : (Sym.oneEquiv.symm α : QuadMode e κ) with j | k
          · rw [Finset.sum_eq_single j]
            · simp
            · intro b _ hb
              simp [Ne.symm hb]
            · intro h
              exact absurd (Finset.mem_univ _) h
          · rw [hu k, Finset.sum_eq_zero]
            intro b _
            simp
      | inr β => simp [quadDegOne]

/-- **Annihilation invariance of the quadratic graph completion.**  Every mode annihilator maps
`S_L` into itself: the vacuum is killed, a base mode goes to a multiple of the vacuum, and a graph
vector `q + Lq` goes to the base-mode lowering of `q` plus a multiple of the vacuum. -/
theorem quadFockAnnihilation_mem_quadraticGraphSubspace {m : ℕ}
    (q : Fin m → Sym (QuadMode e κ) 2 → ℝ) (L : Matrix κ (Fin m) ℝ)
    (hsupp : ∀ r, ∀ β : Sym (QuadMode e κ) 2,
      (∃ k : κ, Sum.inr k ∈ (β : Multiset (QuadMode e κ))) → q r β = 0)
    (i : QuadMode e κ) {v : QuadFockIdx e κ → ℝ} (hv : v ∈ quadraticGraphSubspace q L) :
    quadFockAnnihilation i v ∈ quadraticGraphSubspace q L := by
  have hvac : quadDegZero (e := e) (κ := κ) 1 ∈ quadraticGraphSubspace q L :=
    Submodule.subset_span ⟨Sum.inl (), rfl⟩
  have hbase : ∀ j : Fin e,
      (quadDegOne fun x : QuadMode e κ => if x = Sum.inl j then (1 : ℝ) else 0)
        ∈ quadraticGraphSubspace q L :=
    fun j => Submodule.subset_span ⟨Sum.inr (Sum.inl j), rfl⟩
  have hgen : ∀ x, quadFockAnnihilation i (quadFockBasis q L x)
      ∈ quadraticGraphSubspace q L := by
    intro x
    cases x with
    | inl a =>
        rw [quadFockBasis, quadFockAnnihilation_degZero]
        exact Submodule.zero_mem _
    | inr y =>
        cases y with
        | inl j =>
            rw [quadFockBasis, quadFockAnnihilation_degOne, quadDegZero_eq_smul]
            exact Submodule.smul_mem _ _ hvac
        | inr r =>
            rw [quadFockBasis, quadFockAnnihilation_add, quadFockAnnihilation_degTwo,
              quadFockAnnihilation_degOne, quadDegZero_eq_smul,
              quadDegOne_eq_sum_base (quadLower i (q r))
                (quadLower_transverse_eq_zero i (q r) (hsupp r))]
            exact Submodule.add_mem _
              (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbase j))
              (Submodule.smul_mem _ _ hvac)
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro w ⟨x, rfl⟩
    exact hgen x
  · rw [show (0 : QuadFockIdx e κ → ℝ) = quadDegZero 0 by
        funext x; cases x with
        | inl a => simp [quadDegZero]
        | inr y => cases y <;> simp [quadDegZero],
      quadFockAnnihilation_degZero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [quadFockAnnihilation_add]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [quadFockAnnihilation_smul]
    exact Submodule.smul_mem _ _ ha

/-- **Quadratic graph completion law.**  The subspace `S_L` is annihilation invariant and the
squared norm of the top exterior vector of its degree-dilated spanning family is
`t^(e+m) det (t I + Lᵀ L)`. -/
theorem quadraticGraphCompletion_invariant_and_volume {m : ℕ}
    (q : Fin m → Sym (QuadMode e κ) 2 → ℝ) (L : Matrix κ (Fin m) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hq : ∀ r s, ∑ β, q r β * q s β = if r = s then 1 else 0)
    (hsupp : ∀ r, ∀ β : Sym (QuadMode e κ) 2,
      (∃ k : κ, Sum.inr k ∈ (β : Multiset (QuadMode e κ))) → q r β = 0) :
    (∀ (i : QuadMode e κ) {v : QuadFockIdx e κ → ℝ}, v ∈ quadraticGraphSubspace q L →
        quadFockAnnihilation i v ∈ quadraticGraphSubspace q L) ∧
      quadraticFockVolume q L t
        = t ^ (e + m) * (t • (1 : Matrix (Fin m) (Fin m) ℝ) + L.transpose * L).det :=
  ⟨fun i _ hv => quadFockAnnihilation_mem_quadraticGraphSubspace q L hsupp i hv,
    quadraticFockVolume_eq q L t ht hq⟩

end

end GaloisForLFunctions.HilbertMetric
