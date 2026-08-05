import Mathlib.FieldTheory.Finiteness
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Symplectic.CentralizerStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Quantum

open NQubitPauliOperator Module Submodule
open Quantum.StabilizerGroup

variable {n : ℕ}

/-- A family of mutually commuting Pauli operators occupies at most half the
binary symplectic dimension. -/
theorem commutingPauli_span_finrank_le
    (A : Finset (NQubitPauliOperator n))
    (hcomm : ∀ p ∈ A, ∀ q ∈ A, symplecticInner p q = 0) :
    finrank (ZMod 2)
        (span (ZMod 2) ((fun p => toSymplectic p) '' (A : Set (NQubitPauliOperator n)))) ≤ n := by
  classical
  let S : Set (Fin (n + n) → ZMod 2) :=
    (fun p => toSymplectic p) '' (A : Set (NQubitPauliOperator n))
  let W : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) := span (ZMod 2) S
  have hpair : ∀ s ∈ S, ∀ t ∈ S, symplecticBilinear s t = 0 := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [symplecticBilinear_toSymplectic]
    exact hcomm p hp q hq
  have hW : W ≤ LinearMap.BilinForm.orthogonal (sympBilinForm n) W := by
    intro w hw
    change w ∈ span (ZMod 2) S at hw
    change w ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n) (span (ZMod 2) S)
    rw [mem_sympBilinForm_orthogonal_span_iff]
    intro s hs
    induction hw using Submodule.span_induction with
    | mem t ht => exact hpair s hs t ht
    | zero => simp [symplecticBilinear]
    | add x y _ _ hx hy => rw [symplecticBilinear_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [symplecticBilinear_smul_right, hx, mul_zero]
  have hdim : finrank (ZMod 2) W ≤
      finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (sympBilinForm n) W) :=
    Submodule.finrank_mono hW
  rw [LinearMap.BilinForm.finrank_orthogonal sympBilinForm_nondegenerate] at hdim
  have hfull : finrank (ZMod 2) (Fin (n + n) → ZMod 2) = n + n := by simp
  rw [hfull] at hdim
  change finrank (ZMod 2) W ≤ n
  omega

/-- Any finite family of mutually commuting `n`-qubit Pauli operators has at
most `2^n` distinct operator parts. -/
theorem card_commutingPauli_le_pow
    (A : Finset (NQubitPauliOperator n))
    (hcomm : ∀ p ∈ A, ∀ q ∈ A, symplecticInner p q = 0) :
    A.card ≤ 2 ^ n := by
  classical
  let S : Set (Fin (n + n) → ZMod 2) :=
    (fun p => toSymplectic p) '' (A : Set (NQubitPauliOperator n))
  let W : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) := span (ZMod 2) S
  let f : {p // p ∈ A} → W := fun p =>
    ⟨toSymplectic p.1, subset_span ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply toSymplectic_injective
    exact congrArg Subtype.val hpq
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hcard
  rw [Module.card_eq_pow_finrank (K := ZMod 2)] at hcard
  have hdim : finrank (ZMod 2) W ≤ n := by
    exact commutingPauli_span_finrank_le A hcomm
  norm_num at hcard ⊢
  exact hcard.trans (Nat.pow_le_pow_right (by omega) hdim)

/-- Reindex an operator to its coordinates on a chosen support. -/
def restrictPauli (S : Finset (Fin n)) (p : NQubitPauliOperator n) :
    NQubitPauliOperator S.card :=
  fun i => p (S.orderIsoOfFin rfl i)

lemma restrictPauli_injective_on_support (S : Finset (Fin n))
    {p q : NQubitPauliOperator n} (hp : support p = S) (hq : support q = S)
    (h : restrictPauli S p = restrictPauli S q) : p = q := by
  ext i
  by_cases hi : i ∈ S
  · let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨i, hi⟩
    have hj := congrFun h j
    simpa [restrictPauli, j] using hj
  · have hpi : p i = PauliOperator.I := by
      by_contra hne
      exact hi (hp ▸ (mem_support p i).2 hne)
    have hqi : q i = PauliOperator.I := by
      by_contra hne
      exact hi (hq ▸ (mem_support q i).2 hne)
    rw [hpi, hqi]

lemma symplecticInner_restrictPauli (S : Finset (Fin n))
    {p q : NQubitPauliOperator n} (hp : support p = S) :
    symplecticInner (restrictPauli S p) (restrictPauli S q) = symplecticInner p q := by
  classical
  unfold symplecticInner restrictPauli
  let f : S → ZMod 2 := fun i =>
    PauliOperator.symplecticProductSingle (p i.1) (q i.1)
  change (∑ i : Fin S.card, f ((S.orderIsoOfFin rfl).toEquiv i)) = _
  rw [Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv f]
  let g : Fin n → ZMod 2 := fun i =>
    PauliOperator.symplecticProductSingle (p i) (q i)
  change (∑ i : S, g i.1) = ∑ i : Fin n, g i
  rw [← Finset.sum_subtype S (by simp) g]
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  have hpi : p i = PauliOperator.I := by
    by_contra hne
    exact hi (hp ▸ (mem_support p i).2 hne)
  simp [g, hpi, PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle]

lemma restrictPauli_ne_identity (S : Finset (Fin n))
    {p : NQubitPauliOperator n} (hp : support p = S)
    (hne : p ≠ identity n) : restrictPauli S p ≠ identity S.card := by
  intro h
  apply hne
  ext i
  by_cases hi : i ∈ S
  · let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨i, hi⟩
    have hj := congrFun h j
    simpa [restrictPauli, identity, j] using hj
  · have hpi : p i = PauliOperator.I := by
      by_contra hpi
      exact hi (hp ▸ (mem_support p i).2 hpi)
    simpa [identity] using hpi

/-- On one exact support of size `k`, a commuting nonidentity family has at
most `2^k - 1` elements. -/
theorem card_commutingPauli_fixedSupport_le
    (A : Finset (NQubitPauliOperator n)) (S : Finset (Fin n))
    (hsupport : ∀ p ∈ A, support p = S)
    (hne : ∀ p ∈ A, p ≠ identity n)
    (hcomm : ∀ p ∈ A, ∀ q ∈ A, symplecticInner p q = 0) :
    A.card ≤ 2 ^ S.card - 1 := by
  classical
  let B : Finset (NQubitPauliOperator S.card) := A.image (restrictPauli S)
  have hinj : Set.InjOn (restrictPauli S) (A : Set (NQubitPauliOperator n)) := by
    intro p hp q hq h
    exact restrictPauli_injective_on_support S (hsupport p hp) (hsupport q hq) h
  have hcardB : B.card = A.card := Finset.card_image_iff.mpr hinj
  have hcommB : ∀ p ∈ insert (identity S.card) B,
      ∀ q ∈ insert (identity S.card) B, symplecticInner p q = 0 := by
    intro p hp q hq
    simp only [Finset.mem_insert] at hp hq
    rcases hp with rfl | hp
    · simp [symplecticInner, identity, PauliOperator.symplecticProductSingle]
    rcases hq with rfl | hq
    · simp [symplecticInner, identity, PauliOperator.symplecticProductSingle]
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
    rw [symplecticInner_restrictPauli S (hsupport p0 hp0)]
    exact hcomm p0 hp0 q0 hq0
  have hcap := card_commutingPauli_le_pow (insert (identity S.card) B) hcommB
  have hid : identity S.card ∉ B := by
    intro hid
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hid
    exact restrictPauli_ne_identity S (hsupport p hp) (hne p hp) heq
  rw [Finset.card_insert_of_notMem hid, hcardB] at hcap
  omega

/-- Exact support-summed capacity bound for commuting nonidentity Pauli words
of weight at most `q`. -/
theorem card_commutingPauli_weight_le_supportSum
    (A : Finset (NQubitPauliOperator n)) (q : ℕ)
    (hweight : ∀ p ∈ A, weight p ≤ q)
    (hne : ∀ p ∈ A, p ≠ identity n)
    (hcomm : ∀ p ∈ A, ∀ r ∈ A, symplecticInner p r = 0) :
    A.card ≤ ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.filter fun S => S.card ≤ q),
      (2 ^ S.card - 1) := by
  classical
  let T : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter fun S => S.card ≤ q
  have hall : ∀ p ∈ A, support p ∈ T := by
    intro p hp
    simp only [T, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    simpa [weight] using hweight p hp
  have hpart := Finset.sum_card_fiberwise_eq_card_filter A T support
  have hfilter : A.filter (fun p => support p ∈ T) = A :=
    Finset.filter_eq_self.mpr hall
  rw [hfilter] at hpart
  change A.card ≤ ∑ S ∈ T, (2 ^ S.card - 1)
  rw [← hpart]
  apply Finset.sum_le_sum
  intro S hS
  apply card_commutingPauli_fixedSupport_le (A.filter fun p => support p = S) S
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    exact hne p (Finset.mem_filter.mp hp).1
  · intro p hp r hr
    exact hcomm p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1

/-- The support-summed capacity is exactly the binomial expression used in
the recurrence codimension comparison. -/
theorem commutingPauli_supportSum_eq_chooseSum (n q : ℕ) :
    (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.filter fun S => S.card ≤ q),
      (2 ^ S.card - 1)) =
    ∑ k ∈ Finset.range (q + 1), ((n.choose k) * (2 ^ k - 1)) := by
  classical
  let T : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter fun S => S.card ≤ q
  have hmap : ∀ S ∈ T, S.card ∈ Finset.range (q + 1) := by
    intro S hS
    simp only [T, Finset.mem_filter] at hS
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun S => 2 ^ S.card - 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k ≤ q := by
    simp only [Finset.mem_range] at hk
    omega
  have hfiber : T.filter (fun S => S.card = k) =
      (Finset.univ : Finset (Fin n)).powersetCard k := by
    ext S
    simp only [T, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    omega
  rw [hfiber]
  have hconst : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      2 ^ S.card - 1 = 2 ^ k - 1 := by
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_const_nat hconst, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

def commutingPauliCapacity (n q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range q, (2 ^ (j + 1) - 1) * n.choose (j + 1)

def nonidentityPauliWeightCount (n q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range q, 3 ^ (j + 1) * n.choose (j + 1)

def productInputObserverRank (n q : ℕ) : ℕ :=
  2 * ∑ j ∈ Finset.range q, n.choose (j + 1)

lemma two_pow_add_one_le_three_pow_succ (j : ℕ) :
    2 ^ (j + 1) + 1 ≤ 3 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      calc
        2 ^ (j + 1 + 1) + 1 = 2 * 2 ^ (j + 1) + 1 := by ring
        _ ≤ 2 * (2 ^ (j + 1) + 1) := by omega
        _ ≤ 2 * 3 ^ (j + 1) := Nat.mul_le_mul_left 2 ih
        _ ≤ 3 * 3 ^ (j + 1) := by
          exact Nat.mul_le_mul_right (3 ^ (j + 1)) (by omega)
        _ = 3 ^ (j + 1 + 1) := by ring

/-- The observer-stationary codimension never exceeds the codimension of a
commuting Pauli recurrence carrier. -/
theorem commutingPauliCapacity_add_observerRank_le_pauliWeightCount (n q : ℕ) :
    commutingPauliCapacity n q + productInputObserverRank n q ≤
      nonidentityPauliWeightCount n q := by
  unfold commutingPauliCapacity productInputObserverRank nonidentityPauliWeightCount
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have htwo : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
  have heq :
      (2 ^ (j + 1) - 1) * n.choose (j + 1) + 2 * n.choose (j + 1) =
        (2 ^ (j + 1) + 1) * n.choose (j + 1) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  rw [heq]
  exact Nat.mul_le_mul_right (n.choose (j + 1)) (two_pow_add_one_le_three_pow_succ j)

end Quantum
