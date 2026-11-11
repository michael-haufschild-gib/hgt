import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCountOfASectionOnTwoGraphsIsTheSplitNorm
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# The count of sections in a box is its volume over the gluing index

The functions of the square on finitely many graphs are a lattice of finite index in `ℤ^S`: the
gluing index. Count the sections whose values lie in a box.

* **A lattice in a box** (`card_filter_mem_alignedBox_mul_index`). For a subgroup `L` of `ℤ^ι`
  that contains `d ℤ^ι`, and a box whose sides are multiples of `d`,
  `#(L ∩ box) · [ℤ^ι : L] = vol(box)`: an identity, with no error term. Each residue class
  modulo `d` has the same number of points in the box, and `L` is a union of `d^ι/[ℤ^ι : L]`
  classes.
* **Two graphs** (`card_pairRing_box`). On `Γ_m ∪ Γ_n`, glued along `J`, the sections in a box
  with sides multiples of `#(ℤ/J)` number `area / #(ℤ/J)`.
* **The first `N` graphs** (`sectionLattice`, `mem_sectionLattice_iff`,
  `index_sectionLattice`, `card_sections_alignedBox`). The values of the sections on
  `Γ_1, …, Γ_N` are a lattice of index `N!`, and in a box with sides multiples of `N!` there
  are `vol / N!` of them.

So the logarithm of the count is the logarithm of the volume minus the sum of the contacts
(`log N! = Σ_{m ∣ n ≤ N} Λ(n/m)`): the contacts enter once, as a constant, with the sign of a
condition and without the multiplicities of the divisor. A count of sections of the object in
archimedean boxes has no quadratic term; its Tate limit is not the pairing, in which the contact
of `Γ_m` and `Γ_n` enters with the product of the multiplicities and the opposite sign.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Residues in an interval -/

/-- An interval of `r k` integers has `k` members in each residue class modulo `r`. -/
theorem card_Ico_filter_modEq (a v : ℤ) {r : ℤ} (hr : 0 < r) (k : ℕ) :
    ((Finset.Ico a (a + r * k)).filter fun x : ℤ => x ≡ v [ZMOD r]).card = k := by
  have h := Int.Ico_filter_modEq_card a (a + r * k) hr v
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have e : (((a + r * k : ℤ) : ℚ) - v) / r = ((a : ℚ) - v) / r + ((k : ℤ) : ℚ) := by
    rw [div_eq_iff hrq, add_mul, div_mul_cancel₀ _ hrq]
    push_cast
    ring
  rw [e, Int.ceil_add_intCast, add_sub_cancel_left, max_eq_left (Int.natCast_nonneg k)] at h
  exact_mod_cast h

theorem card_Ico_filter_residue {d : ℕ} [NeZero d] (a : ℤ) (k : ℕ) (ρ : ZMod d) :
    ((Finset.Ico a (a + d * k)).filter fun x : ℤ => (x : ZMod d) = ρ).card = k := by
  obtain ⟨v, rfl⟩ := ZMod.intCast_surjective ρ
  have hd : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  refine Eq.trans ?_ (card_Ico_filter_modEq a v hd k)
  congr 1
  exact Finset.filter_congr fun x _ => ZMod.intCast_eq_intCast_iff x v d

/-! ### A lattice in a box -/

section Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The box with corner `a` and sides `d k_i`. -/
def alignedBox (d : ℕ) (a : ι → ℤ) (k : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun i => Finset.Ico (a i) (a i + d * k i)

theorem card_alignedBox (d : ℕ) (a : ι → ℤ) (k : ι → ℕ) :
    (alignedBox d a k).card = ∏ i, d * k i := by
  rw [alignedBox, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Ico, add_sub_cancel_left, ← Nat.cast_mul, Int.toNat_natCast]

/-- Reduction modulo `d` in every coordinate. -/
def reduceMod (d : ℕ) : (ι → ℤ) →+ (ι → ZMod d) := (Int.castAddHom (ZMod d)).compLeft ι

omit [Fintype ι] [DecidableEq ι] in
theorem reduceMod_surjective (d : ℕ) : Function.Surjective (reduceMod (ι := ι) d) := fun y =>
  ⟨fun i => (ZMod.intCast_surjective (y i)).choose,
    funext fun i => (ZMod.intCast_surjective (y i)).choose_spec⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A subgroup that contains `d ℤ^ι` contains the kernel of the reduction modulo `d`. -/
theorem ker_reduceMod_le {d : ℕ} [NeZero d] {L : AddSubgroup (ι → ℤ)}
    (hL : ∀ x : ι → ℤ, d • x ∈ L) : (reduceMod d).ker ≤ L := by
  intro x hx
  have hx' : ∀ i, (d : ℤ) ∣ x i := fun i =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd (x i) d).mp (congrFun hx i)
  choose y hy using hx'
  have hxy : x = d • y := funext fun i => by rw [Pi.smul_apply, nsmul_eq_mul, hy i]
  rw [hxy]
  exact hL y

/-- **A lattice in a box.** If `L` contains `d ℤ^ι` and the sides of the box are multiples of
`d`, then `#(L ∩ box) · [ℤ^ι : L] = vol(box)`. -/
theorem card_filter_mem_alignedBox_mul_index {d : ℕ} [NeZero d] (L : AddSubgroup (ι → ℤ))
    (hL : ∀ x : ι → ℤ, d • x ∈ L) (a : ι → ℤ) (k : ι → ℕ) :
    ((alignedBox d a k).filter (· ∈ L)).card * L.index = ∏ i, d * k i := by
  set r := reduceMod (ι := ι) d with hr
  set T : Finset (ι → ZMod d) := Finset.univ.filter (· ∈ L.map r) with hT
  have hTmem : ∀ ρ : ι → ZMod d, ρ ∈ T ↔ ρ ∈ L.map r := fun ρ => by
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- membership in `L` is read off the residues
  have hmem : ∀ x : ι → ℤ, x ∈ L ↔ r x ∈ T := fun x => by
    rw [hTmem]
    constructor
    · exact fun hx => AddSubgroup.mem_map_of_mem r hx
    · rintro ⟨y, hy, hxy⟩
      have hk : x - y ∈ r.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
      have h2 := L.add_mem (ker_reduceMod_le hL hk) hy
      rwa [sub_add_cancel] at h2
  -- each residue class has `∏ k_i` points in the box
  have hfiber : ∀ ρ : ι → ZMod d,
      ((alignedBox d a k).filter fun x => r x = ρ).card = ∏ i, k i := fun ρ => by
    have hset : (alignedBox d a k).filter (fun x => r x = ρ) =
        Fintype.piFinset fun i =>
          (Finset.Ico (a i) (a i + d * k i)).filter fun x : ℤ => (x : ZMod d) = ρ i := by
      ext x
      simp only [alignedBox, Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hx, hρ⟩ i
        exact ⟨hx i, congrFun hρ i⟩
      · intro h
        exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩
    rw [hset, Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun i _ => card_Ico_filter_residue (a i) (k i) (ρ i)
  have hcount : ((alignedBox d a k).filter (· ∈ L)).card = T.card * ∏ i, k i := by
    have h1 : (alignedBox d a k).filter (· ∈ L) = (alignedBox d a k).filter fun x => r x ∈ T :=
      Finset.filter_congr fun x _ => hmem x
    rw [h1, ← Finset.sum_card_fiberwise_eq_card_filter]
    simp only [hfiber]
    rw [Finset.sum_const, smul_eq_mul]
  -- `L` is a union of `d^ι / [ℤ^ι : L]` residue classes
  have hindex : T.card * L.index = d ^ Fintype.card ι := by
    have h1 : Nat.card (L.map r) = T.card := Nat.subtype_card T hTmem
    have h2 : (L.map r).index = L.index :=
      AddSubgroup.index_map_eq L (reduceMod_surjective d) (ker_reduceMod_le hL)
    have h3 := AddSubgroup.card_mul_index (L.map r)
    rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] at h3
    exact h3
  rw [hcount, mul_right_comm, hindex, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

end Lattice

/-! ### Two graphs -/

/-- **The sections of two graphs in a box.** On two graphs glued along `J ≠ 0` the sections with
values in a box whose sides are multiples of `c = #(ℤ/J)` number the area divided by `c`. -/
theorem card_pairRing_box {J : Ideal ℤ} (hJ : J ≠ ⊥) (a₁ a₂ : ℤ) (k₁ k₂ : ℕ) :
    (((Finset.Ico a₁ (a₁ + Ideal.absNorm J * k₁)) ×ˢ
        (Finset.Ico a₂ (a₂ + Ideal.absNorm J * k₂))).filter
          fun z : ℤ × ℤ => z ∈ pairRing J).card * Ideal.absNorm J =
      (Ideal.absNorm J * k₁) * (Ideal.absNorm J * k₂) := by
  set c : ℕ := Ideal.absNorm J with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)
  have hcz : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc0
  have hspan : J = Ideal.span {(c : ℤ)} := (Int.ideal_span_absNorm_eq_self J).symm
  have hmem : ∀ x y : ℤ, (x, y) ∈ pairRing J ↔ y ≡ x [ZMOD (c : ℤ)] := fun x y => by
    rw [mem_pairRing, hspan, Ideal.mem_span_singleton, Int.modEq_iff_dvd]
  rw [Finset.card_filter, Finset.sum_product]
  have hinner : ∀ x : ℤ, (∑ y ∈ Finset.Ico a₂ (a₂ + c * k₂),
      if (x, y) ∈ pairRing J then 1 else 0) = k₂ := fun x => by
    rw [← Finset.card_filter]
    refine Eq.trans ?_ (card_Ico_filter_modEq a₂ x hcz k₂)
    congr 1
    exact Finset.filter_congr fun y _ => hmem x y
  simp only [hinner]
  rw [Finset.sum_const, Int.card_Ico, add_sub_cancel_left, ← Nat.cast_mul, Int.toNat_natCast,
    smul_eq_mul]
  ring

/-! ### The first `N` graphs -/

/-- The lattice of the values of the sections of the square on `Γ_1, …, Γ_N`: the integer
combinations of the columns of the necklace matrix. -/
def sectionLattice (N : ℕ) : AddSubgroup (Fin N → ℤ) :=
  (LinearMap.range (Matrix.mulVecLin (necklaceMatrix N))).toAddSubgroup

theorem mem_sectionLattice {N : ℕ} {y : Fin N → ℤ} :
    y ∈ sectionLattice N ↔ ∃ b : Fin N → ℤ, (necklaceMatrix N).mulVec b = y := Iff.rfl

/-- A row of the necklace matrix is a sum over the divisors. -/
theorem necklaceMatrix_mulVec (N : ℕ) (b : ℕ → ℤ) (i : Fin N) :
    (necklaceMatrix N).mulVec (fun j : Fin N => b ((j : ℕ) + 1)) i =
      ∑ d ∈ ((i : ℕ) + 1).divisors, (d : ℤ) * b d := by
  show ∑ j : Fin N, necklaceMatrix N i j * b ((j : ℕ) + 1) = _
  have hterm : ∀ j : Fin N, necklaceMatrix N i j * b ((j : ℕ) + 1) =
      if ((j : ℕ) + 1) ∣ ((i : ℕ) + 1) then (((j : ℕ) + 1 : ℕ) : ℤ) * b ((j : ℕ) + 1) else 0 :=
    fun j => by
      rw [necklaceMatrix, Matrix.of_apply]
      split_ifs
      · rfl
      · rw [zero_mul]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => (j : ℕ) + 1) ?_ ?_ ?_ ?_
  · intro j hj
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hj).2, Nat.succ_ne_zero _⟩
  · intro j₁ _ j₂ _ h
    exact Fin.ext (Nat.succ_injective h)
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos _)
    have hdle : d ≤ (i : ℕ) + 1 := Nat.le_of_dvd (Nat.succ_pos _) hdvd
    have hlt : d - 1 < N := by
      have := i.2
      omega
    refine ⟨⟨d - 1, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · show (d - 1 + 1) ∣ (i : ℕ) + 1
      rwa [Nat.sub_add_cancel hd1]
    · show d - 1 + 1 = d
      exact Nat.sub_add_cancel hd1
  · intro j _
    rfl

/-- **The lattice is the values of the sections on the first `N` graphs.** -/
theorem mem_sectionLattice_iff {N : ℕ} (y : Fin N → ℤ) :
    y ∈ sectionLattice N ↔
      ∃ x : ghostRing, ∀ i : Fin N, ghostComponent ⟨(i : ℕ) + 1, Nat.succ_pos _⟩ x = y i := by
  rw [mem_sectionLattice]
  constructor
  · rintro ⟨b, rfl⟩
    -- the necklace coordinates, extended by zero
    set B : ℕ → ℤ := fun d => if h : d - 1 < N then b ⟨d - 1, h⟩ else 0 with hB
    have hBj : (fun j : Fin N => B ((j : ℕ) + 1)) = b := funext fun j => by
      have hj : (j : ℕ) + 1 - 1 < N := by
        rw [Nat.add_sub_cancel]
        exact j.2
      rw [hB]
      simp only [dif_pos hj]
      exact congrArg b (Fin.ext (Nat.add_sub_cancel (j : ℕ) 1))
    refine ⟨⟨fun n => ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * B d,
      isGhost_of_necklace (b := B) fun _ => rfl⟩, fun i => ?_⟩
    rw [← hBj]
    exact (necklaceMatrix_mulVec N B i).symm
  · rintro ⟨x, hx⟩
    obtain ⟨B, hB⟩ := (isGhost_iff_exists_necklace x.1).mp x.2
    refine ⟨fun j => B ((j : ℕ) + 1), funext fun i => ?_⟩
    rw [necklaceMatrix_mulVec, ← hx i, ghostComponent_apply]
    exact (hB ⟨(i : ℕ) + 1, Nat.succ_pos _⟩).symm

/-- `N!` times every vector is a vector of values of a section. -/
theorem factorial_smul_mem_sectionLattice (N : ℕ) (x : Fin N → ℤ) :
    N.factorial • x ∈ sectionLattice N := by
  rw [mem_sectionLattice]
  refine ⟨(necklaceMatrix N).adjugate.mulVec x, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, det_necklaceMatrix, Matrix.smul_mulVec,
    Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]

/-- **The gluing index of the first `N` graphs**, as the index of the lattice of sections. -/
theorem index_sectionLattice (N : ℕ) : (sectionLattice N).index = N.factorial := by
  have hdet : (necklaceMatrix N).det ≠ 0 := by
    rw [det_necklaceMatrix]
    exact_mod_cast N.factorial_ne_zero
  have hinj : Function.Injective (Matrix.mulVecLin (necklaceMatrix N)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.mulVecLin (necklaceMatrix N)))
    (LinearEquiv.ofInjective (Matrix.mulVecLin (necklaceMatrix N)) hinj)
  have hcomp : (LinearMap.range (Matrix.mulVecLin (necklaceMatrix N))).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap
        ((LinearEquiv.ofInjective (Matrix.mulVecLin (necklaceMatrix N)) hinj :
          (Fin N → ℤ) ≃ₗ[ℤ] _) : (Fin N → ℤ) →+ _) =
      Matrix.toLin' (necklaceMatrix N) := by
    refine LinearMap.ext fun v => ?_
    rfl
  rw [hcomp, LinearMap.det_toLin', det_necklaceMatrix, Int.natAbs_natCast] at h
  exact h.symm

/-- **The sections of the first `N` graphs in a box.** In a box whose sides are multiples of
`N!` the vectors of values of the sections of the square number the volume divided by `N!`. -/
theorem card_sections_alignedBox (N : ℕ) (a : Fin N → ℤ) (k : Fin N → ℕ) :
    ((alignedBox N.factorial a k).filter (· ∈ sectionLattice N)).card * N.factorial =
      ∏ i, N.factorial * k i := by
  haveI : NeZero N.factorial := ⟨N.factorial_ne_zero⟩
  have h := card_filter_mem_alignedBox_mul_index (sectionLattice N)
    (factorial_smul_mem_sectionLattice N) a k
  rwa [index_sectionLattice] at h

/-- **The logarithm of the count is the logarithm of the volume minus the logarithm of the
gluing index.** The contacts of the first `N` graphs, whose sum is `log N!`, enter the count
once and as a constant: the sides of the box do not multiply them. -/
theorem log_card_sections_alignedBox (N : ℕ) (a : Fin N → ℤ) {k : Fin N → ℕ}
    (hk : ∀ i, 1 ≤ k i) :
    Real.log (((alignedBox N.factorial a k).filter (· ∈ sectionLattice N)).card : ℝ) =
      (∑ i, Real.log ((N.factorial * k i : ℕ) : ℝ)) - Real.log (N.factorial : ℝ) := by
  have h := card_sections_alignedBox N a k
  have hf : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have hprod : ∀ i ∈ (Finset.univ : Finset (Fin N)), ((N.factorial * k i : ℕ) : ℝ) ≠ 0 :=
    fun i _ => by
      have : N.factorial * k i ≠ 0 := Nat.mul_ne_zero N.factorial_ne_zero (by have := hk i; omega)
      exact_mod_cast this
  have hcard : (((alignedBox N.factorial a k).filter (· ∈ sectionLattice N)).card : ℝ) ≠ 0 := by
    intro h0
    have h0' : ((alignedBox N.factorial a k).filter (· ∈ sectionLattice N)).card = 0 := by
      exact_mod_cast h0
    rw [h0', zero_mul] at h
    exact (Finset.prod_ne_zero_iff.mpr fun i _ =>
      Nat.mul_ne_zero N.factorial_ne_zero (by have := hk i; omega)) h.symm
  have hR : (((alignedBox N.factorial a k).filter (· ∈ sectionLattice N)).card : ℝ) *
      (N.factorial : ℝ) = ∏ i, ((N.factorial * k i : ℕ) : ℝ) := by
    exact_mod_cast h
  have hlog := congrArg Real.log hR
  rw [Real.log_mul hcard hf, Real.log_prod hprod] at hlog
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
