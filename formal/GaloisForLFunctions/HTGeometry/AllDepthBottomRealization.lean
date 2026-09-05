import GaloisForLFunctions.HTGeometry.AllDepthBottomCharge
import GaloisForLFunctions.HTGeometry.AllDepthAtomRealization
import GaloisForLFunctions.HTGeometry.AllDepthTelescope

/-!
# Realizing a prescribed bottom charge

The all-depth descent needs, for the bottom charge of a member of the mixed-constraint class, a
differentially algebraic function with exactly the same charge.  The charge is a divisor on the
elliptic quotient `ℂ / (ℤ + ℤσ)`, concentrated in finitely many orders; the realization is a finite
sum of line-atom jets, one family for each order.

* `lineLattice`, `sameLine_iff_sub_mem` — the line relation as a subgroup coset relation;
* `multiAtomRealization` and its exact Laurent data;
* `laurentCoeff_diffCube` — the difference cube acts on Laurent coefficients by the translated
  cube of the coefficient function.
-/

open Filter Set Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The line lattice -/

/-- The lattice `ℤ + ℤσ`. -/
def lineLattice (σ : ℂ) : AddSubgroup ℂ where
  carrier := {p | ∃ a b : ℤ, p = (a : ℂ) + (b : ℂ) * σ}
  zero_mem' := ⟨0, 0, by norm_num⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩

theorem mem_lineLattice_iff {σ p : ℂ} :
    p ∈ lineLattice σ ↔ ∃ a b : ℤ, p = (a : ℂ) + (b : ℂ) * σ := Iff.rfl

theorem sameLine_iff_sub_mem {σ q r : ℂ} : sameLine σ q r ↔ r - q ∈ lineLattice σ := Iff.rfl

/-! ## The multi-order atom realization -/

/-- The atom sum realizing prescribed coefficients at every order `-(j+1)`, `j < N`. -/
def multiAtomRealization (σ : ℂ) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ j ∈ Finset.range N, atomRealization σ j R (c j) z

theorem multiAtomRealization_periodic (σ : ℂ) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) (z : ℂ) :
    multiAtomRealization σ N R c (z + 1) = multiAtomRealization σ N R c z :=
  Finset.sum_congr rfl fun j _ => atomRealization_periodic σ j R (c j) z

theorem meromorphicOn_multiAtomRealization {σ : ℂ} (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) : MeromorphicOn (multiAtomRealization σ N R c) (Set.univ : Set ℂ) := by
  intro z _
  have hfun : multiAtomRealization σ N R c
      = ∑ j ∈ Finset.range N, atomRealization σ j R (c j) := by
    funext w
    simp only [multiAtomRealization, Finset.sum_apply]
  rw [hfun]
  exact MeromorphicAt.sum fun j _ => meromorphicOn_atomRealization hσ j R (c j) z (Set.mem_univ z)

theorem laurentCoeff_multiAtomRealization {σ : ℂ} (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) (w : ℂ) (ℓ : ℤ) :
    laurentCoeff (multiAtomRealization σ N R c) w ℓ =
      ∑ j ∈ Finset.range N, laurentCoeff (atomRealization σ j R (c j)) w ℓ := by
  classical
  have hfun : multiAtomRealization σ N R c = fun z => ∑ j ∈ Finset.range N,
      (1 : ℂ) * atomRealization σ j R (c j) z := by
    funext z
    simp [multiAtomRealization]
  rw [hfun, laurentCoeff_sum (Finset.range N) _ _ w ℓ
    (fun j _ => meromorphicOn_atomRealization hσ j R (c j) w (Set.mem_univ w))]
  exact Finset.sum_congr rfl fun j _ => one_mul _

/-- **The multi-order atom sum has the prescribed coefficient on each prescribed line.** -/
theorem laurentCoeff_multiAtomRealization_line {σ : ℂ} (hσ : 0 < σ.im) {N : ℕ} (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) (hdist : ∀ q ∈ R, ∀ r ∈ R, sameLine σ q r → q = r)
    {q : ℂ} (hq : q ∈ R) {w : ℂ} (hw : sameLine σ q w) {j : ℕ} (hj : j < N) :
    laurentCoeff (multiAtomRealization σ N R c) w (-((j : ℤ) + 1)) = c j q := by
  classical
  rw [laurentCoeff_multiAtomRealization hσ N R c w]
  have hterm : ∀ i ∈ Finset.range N,
      laurentCoeff (atomRealization σ i R (c i)) w (-((j : ℤ) + 1))
        = if i = j then c j q else 0 := by
    intro i _
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact laurentCoeff_atomRealization_line hσ i R (c i) hdist hq hw
    · rw [if_neg hij]
      refine laurentCoeff_atomRealization_of_ne_order hσ i R (c i) w (by omega) ?_
      intro hcon
      exact hij (by omega)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range N) j (fun _ => c j q),
    if_pos (Finset.mem_range.mpr hj)]

/-- **Off every prescribed line the multi-order atom sum has no principal part.** -/
theorem laurentCoeff_multiAtomRealization_off {σ : ℂ} (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) {w : ℂ} (hw : ∀ q ∈ R, ¬ sameLine σ q w) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (multiAtomRealization σ N R c) w ℓ = 0 := by
  classical
  rw [laurentCoeff_multiAtomRealization hσ N R c w]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : ℓ = -((j : ℤ) + 1)
  · subst hj
    exact laurentCoeff_atomRealization_off hσ j R (c j) hw
  · exact laurentCoeff_atomRealization_of_ne_order hσ j R (c j) w hℓ hj

/-- **The multi-order atom sum is invisible below its top order.** -/
theorem laurentCoeff_multiAtomRealization_of_lt {σ : ℂ} (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ < -(N : ℤ)) :
    laurentCoeff (multiAtomRealization σ N R c) w ℓ = 0 := by
  classical
  rw [laurentCoeff_multiAtomRealization hσ N R c w]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjN : (j : ℤ) < (N : ℤ) := by exact_mod_cast Finset.mem_range.mp hj
  exact laurentCoeff_atomRealization_of_ne_order hσ j R (c j) w (by omega) (by omega)

theorem realizedDA_multiAtomRealization {σ : ℂ} (hσ : 0 < σ.im) (N : ℕ) (R : Finset ℂ)
    (c : ℕ → ℂ → ℂ) : RealizedDA (multiAtomRealization σ N R c) := by
  classical
  have hfun : multiAtomRealization σ N R c
      = ∑ j ∈ Finset.range N, atomRealization σ j R (c j) := by
    funext z
    simp only [multiAtomRealization, Finset.sum_apply]
  rw [hfun]
  exact RealizedDA.sum _ _ fun j _ => realizedDA_atomRealization hσ j R (c j)

/-! ## Laurent coefficients of a difference cube -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **The difference cube acts on Laurent coefficients as the translated cube.** -/
theorem laurentCoeff_diffCube (τ : ι → ℂ) (s : Finset ι) {G : ℂ → ℂ}
    (hG : MeromorphicOn G (Set.univ : Set ℂ)) (p : ℂ) (ℓ : ℤ) :
    laurentCoeff (HTGeometry.diffCube τ s G) p ℓ =
      ∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) *
        laurentCoeff G (p + ∑ i ∈ E, τ i) ℓ := by
  classical
  have hfun : HTGeometry.diffCube τ s G = fun z => ∑ E ∈ s.powerset,
      ((-1 : ℂ) ^ (s.card - E.card)) * (fun w => G (w + ∑ i ∈ E, τ i)) z := rfl
  rw [hfun, laurentCoeff_sum s.powerset _ _ p ℓ
    (fun E _ => meromorphicAt_comp_add.mpr (hG (p + ∑ i ∈ E, τ i) (Set.mem_univ _)))]
  exact Finset.sum_congr rfl fun E _ => by rw [laurentCoeff_comp_add G p _ ℓ]

/-! ## Realizing a prescribed charge -/

/-- **Every prescribed bottom charge is realized by an atom sum.**  A divisor on the elliptic
quotient, concentrated in finitely many orders and with vanishing line sums in every transverse
direction, is the full difference cube of the principal-part data of a finite atom sum. -/
theorem exists_multiAtomRealization_of_bottomCharge
    {σ : ℂ} (hσ : 0 < σ.im) {κ : Type} [DecidableEq κ] (s : Finset κ) (w : κ → ℂ)
    (hfree : ∀ i ∈ s, ∀ n : ℤ, (n : ℂ) * w i ∈ lineLattice σ → n = 0)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ n m : ℤ,
      (n : ℂ) * w i + (m : ℂ) * w j ∈ lineLattice σ → n = 0 ∧ m = 0)
    (D : ℤ → ℂ → ℂ) (N : ℕ)
    (hDinv : ∀ ℓ : ℤ, ℓ < 0 → ∀ p g : ℂ, g ∈ lineLattice σ → D ℓ (p + g) = D ℓ p)
    (hDtop : ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p, D ℓ p = 0)
    (hDfin : ∀ ℓ : ℤ, ℓ < 0 → ∃ S : Finset ℂ, ∀ p, D ℓ p ≠ 0 → ∃ q ∈ S, sameLine σ q p)
    (hDline : ∀ i ∈ s, ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ, ∑ᶠ m : ℤ, D ℓ (p + (m : ℂ) * w i) = 0) :
    ∃ (R : Finset ℂ) (c : ℕ → ℂ → ℂ),
      (∀ q ∈ R, ∀ r ∈ R, sameLine σ q r → q = r) ∧
      ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
        (∑ E ∈ s.powerset, (-1 : ℂ) ^ (s.card - E.card) *
            laurentCoeff (multiAtomRealization σ N R c) (p + ∑ i ∈ E, w i) ℓ) = D ℓ p := by
  classical
  set Λ : AddSubgroup ℂ := lineLattice σ with hΛ
  set Q := ℂ ⧸ Λ
  set mk : ℂ → Q := fun z => (QuotientAddGroup.mk z : Q) with hmk
  have hmk_eq : ∀ a b : ℂ, mk a = mk b ↔ a - b ∈ Λ := fun a b =>
    QuotientAddGroup.eq_iff_sub_mem
  have hout : ∀ x : Q, mk (Quotient.out x) = x := fun x => QuotientAddGroup.out_eq' x
  -- the divisor descends
  have hDdesc : ∀ ℓ : ℤ, ℓ < 0 → ∀ a b : ℂ, mk a = mk b → D ℓ a = D ℓ b := by
    intro ℓ hℓ a b hab
    have hmem : a - b ∈ Λ := (hmk_eq a b).mp hab
    have := hDinv ℓ hℓ b (a - b) hmem
    rw [show b + (a - b) = a from by ring] at this
    exact this
  set wq : κ → Q := fun i => mk (-(w i)) with hwq
  have hzsmul : ∀ (n : ℤ) (y : ℂ), (n • mk y : Q) = mk ((n : ℂ) * y) := by
    intro n y
    rw [hmk]
    show (n • (QuotientAddGroup.mk y : Q)) = QuotientAddGroup.mk ((n : ℂ) * y)
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    rw [zsmul_eq_mul]
  have hwq_smul : ∀ (n : ℤ) (i : κ), (n • wq i : Q) = mk (-((n : ℂ) * w i)) := by
    intro n i
    rw [hwq]
    show (n • mk (-(w i)) : Q) = _
    rw [hzsmul]
    congr 1
    ring
  have hmk_zero_eq : mk (0 : ℂ) = (0 : Q) := rfl
  have hmk_zero : ∀ y : ℂ, (mk y = (0 : Q)) ↔ y ∈ Λ := by
    intro y
    rw [← hmk_zero_eq, hmk_eq, sub_zero]
  have hwq_free : ∀ i ∈ s, ∀ n : ℤ, n • wq i = 0 → n = 0 := by
    intro i hi n hn
    rw [hwq_smul] at hn
    have hmem : -((n : ℂ) * w i) ∈ Λ := (hmk_zero _).mp hn
    have hneg := neg_mem hmem
    rw [neg_neg] at hneg
    exact hfree i hi n hneg
  have hwq_pair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ n m : ℤ,
      n • wq i + m • wq j = 0 → n = 0 ∧ m = 0 := by
    intro i hi j hj hij n m hnm
    rw [hwq_smul, hwq_smul] at hnm
    have hsum : mk (-((n : ℂ) * w i) + -((m : ℂ) * w j)) = (0 : Q) := by
      rw [hmk]
      show QuotientAddGroup.mk _ = _
      rw [QuotientAddGroup.mk_add]
      exact hnm
    have hmem := (hmk_zero _).mp hsum
    refine hpair i hi j hj hij n m ?_
    have hneg := neg_mem hmem
    rw [show -(-((n : ℂ) * w i) + -((m : ℂ) * w j))
      = (n : ℂ) * w i + (m : ℂ) * w j from by ring] at hneg
    exact hneg
  -- the descended divisor at each order
  set Dbar : ℕ → Q → ℂ := fun j x => D (-((j : ℤ) + 1)) (Quotient.out x) with hDbar
  have hDbar_mk : ∀ (j : ℕ) (p : ℂ), Dbar j (mk p) = D (-((j : ℤ) + 1)) p := by
    intro j p
    exact hDdesc _ (by omega) _ _ (hout (mk p))
  have key : ∀ j : ℕ, ∃ (C : Q → ℂ) (S' : Finset Q), (∀ x, C x ≠ 0 → x ∈ S') ∧
      ∀ x, telescopeCube wq s C x = Dbar j x := by
    intro j
    obtain ⟨S₀, hS₀⟩ := hDfin (-((j : ℤ) + 1)) (by omega)
    refine exists_telescopeCube wq s (fun i hi => hwq_free i hi)
      (fun i hi j' hj' hij => hwq_pair i hi j' hj' hij) (Dbar j) (S₀.image mk) ?_ ?_
    · intro x hx
      obtain ⟨q, hq, hql⟩ := hS₀ _ hx
      refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
      have hql' : Quotient.out x - q ∈ Λ := hql
      have hneg := neg_mem hql'
      rw [neg_sub] at hneg
      have hqx : mk q = mk (Quotient.out x) := (hmk_eq _ _).mpr hneg
      rw [hqx, hout]
    · intro i hi x
      have hterm : ∀ m : ℤ, Dbar j (x + m • wq i) = D (-((j : ℤ) + 1))
          (Quotient.out x + ((-m : ℤ) : ℂ) * w i) := by
        intro m
        have harg : x + m • wq i = mk (Quotient.out x + ((-m : ℤ) : ℂ) * w i) := by
          have h1 : mk (Quotient.out x + ((-m : ℤ) : ℂ) * w i)
              = mk (Quotient.out x) + mk (((-m : ℤ) : ℂ) * w i) := by
            rw [hmk]
            exact map_add (QuotientAddGroup.mk' Λ) _ _
          rw [h1, hout, hwq_smul]
          congr 2
          push_cast
          ring
        rw [harg, hDbar_mk]
      rw [finsum_congr hterm]
      have hreindex : ∑ᶠ m : ℤ, D (-((j : ℤ) + 1)) (Quotient.out x + ((-m : ℤ) : ℂ) * w i)
          = ∑ᶠ m : ℤ, D (-((j : ℤ) + 1)) (Quotient.out x + (m : ℂ) * w i) :=
        finsum_comp_equiv (e := (Equiv.neg ℤ))
          (f := fun m : ℤ => D (-((j : ℤ) + 1)) (Quotient.out x + (m : ℂ) * w i))
      rw [hreindex]
      exact hDline i hi _ (by omega) _
  choose C S' hS' hC using key
  set R : Finset ℂ := (Finset.range N).biUnion (fun j => (S' j).image Quotient.out) with hR
  have hRmem : ∀ q ∈ R, ∃ x : Q, q = Quotient.out x := by
    intro q hq
    obtain ⟨j, -, hq'⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq'
    exact ⟨x, rfl⟩
  have hdist : ∀ q ∈ R, ∀ r ∈ R, sameLine σ q r → q = r := by
    intro q hq r hr hqr
    obtain ⟨x, rfl⟩ := hRmem q hq
    obtain ⟨y, rfl⟩ := hRmem r hr
    have hqr' : Quotient.out y - Quotient.out x ∈ Λ := hqr
    have hneg := neg_mem hqr'
    rw [neg_sub] at hneg
    have hmkeq : mk (Quotient.out x) = mk (Quotient.out y) := (hmk_eq _ _).mpr hneg
    rw [hout, hout] at hmkeq
    rw [hmkeq]
  refine ⟨R, fun j q => C j (mk q), hdist, ?_⟩
  -- the Laurent data of the realization
  have hcoeff : ∀ (j : ℕ), j < N → ∀ v : ℂ,
      laurentCoeff (multiAtomRealization σ N R (fun j q => C j (mk q))) v (-((j : ℤ) + 1))
        = C j (mk v) := by
    intro j hj v
    by_cases hcase : ∃ q ∈ R, sameLine σ q v
    · obtain ⟨q, hq, hqv⟩ := hcase
      rw [laurentCoeff_multiAtomRealization_line hσ R _ hdist hq hqv hj]
      congr 1
      have hqv' : v - q ∈ Λ := hqv
      have hneg := neg_mem hqv'
      rw [neg_sub] at hneg
      exact (hmk_eq q v).mpr hneg
    · push Not at hcase
      rw [laurentCoeff_multiAtomRealization_off hσ N R _ hcase (by omega)]
      by_contra hne
      have hxmem : mk v ∈ S' j := hS' j _ (Ne.symm hne)
      have hqR : Quotient.out (mk v) ∈ R :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
          Finset.mem_image.mpr ⟨mk v, hxmem, rfl⟩⟩
      refine hcase _ hqR ?_
      show v - Quotient.out (mk v) ∈ Λ
      refine (hmk_eq v (Quotient.out (mk v))).mp ?_
      rw [hout]
  intro ℓ hℓ p
  by_cases hcase : ∃ j : ℕ, j < N ∧ ℓ = -((j : ℤ) + 1)
  · obtain ⟨j, hj, rfl⟩ := hcase
    have hterms : ∀ E ∈ s.powerset,
        (-1 : ℂ) ^ (s.card - E.card) *
            laurentCoeff (multiAtomRealization σ N R (fun j q => C j (mk q)))
              (p + ∑ i ∈ E, w i) (-((j : ℤ) + 1))
          = (-1 : ℂ) ^ (s.card - E.card) * C j (mk p - ∑ i ∈ E, wq i) := by
      intro E _
      rw [hcoeff j hj]
      congr 2
      have hsum : ∑ i ∈ E, wq i = mk (-(∑ i ∈ E, w i)) := by
        rw [hwq, hmk]
        show ∑ i ∈ E, (QuotientAddGroup.mk' Λ) (-(w i))
          = (QuotientAddGroup.mk' Λ) (-(∑ i ∈ E, w i))
        rw [← map_sum]
        congr 1
        rw [← Finset.sum_neg_distrib]
      rw [hsum, hmk]
      show (QuotientAddGroup.mk' Λ) (p + ∑ i ∈ E, w i)
        = (QuotientAddGroup.mk' Λ) p - (QuotientAddGroup.mk' Λ) (-(∑ i ∈ E, w i))
      rw [← map_sub]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterms]
    have := hC j (mk p)
    rw [telescopeCube] at this
    rw [this, hDbar_mk]
  · push Not at hcase
    have hbig : ℓ < -(N : ℤ) := by
      by_contra hcon
      push Not at hcon
      have hℓ' : -(N : ℤ) ≤ ℓ := hcon
      obtain ⟨j, hj⟩ : ∃ j : ℕ, ℓ = -((j : ℤ) + 1) := by
        refine ⟨(-ℓ - 1).toNat, ?_⟩
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      exact absurd hj (hcase j (by omega))
    have hzero : ∀ E ∈ s.powerset,
        (-1 : ℂ) ^ (s.card - E.card) *
            laurentCoeff (multiAtomRealization σ N R (fun j q => C j (mk q)))
              (p + ∑ i ∈ E, w i) ℓ = 0 := by
      intro E _
      rw [laurentCoeff_multiAtomRealization_of_lt hσ N R _ _ hbig, mul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact (hDtop ℓ hbig p).symm

end

end GaloisForLFunctions.HTGeometry
