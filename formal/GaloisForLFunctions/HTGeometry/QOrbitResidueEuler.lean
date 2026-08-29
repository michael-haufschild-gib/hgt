import GaloisForLFunctions.HTGeometry.QOrbitResidue
import GaloisForLFunctions.HTGeometry.EulerPolePartCalculus

/-!
# The Euler operator on `q`-discrete residues

The Euler operator `x d/dx` raises the pole order by one and acts on the residues along a fixed
multiplicative orbit by

`ρ_(d+1)(δ f) = −(d+1)·ρ_(d+1)(f) − d·a·ρ_d(f)`.

Consequently, if all residues of `f` above order `d` vanish and `ρ_d(f) ≠ 0`, then the top residue
of any nonzero constant-coefficient Euler polynomial applied to `f` is again nonzero, so no such
combination is `q`-summable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

theorem qOrbitResidue_add {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) (C₁ C₂ : RatFunc K) :
    qOrbitResidue q a d (C₁ + C₂) = qOrbitResidue q a d C₁ + qOrbitResidue q a d C₂ := by
  classical
  set s : Finset ℤ :=
    (finite_support_polePart_multOrbit (g := C₁) hq ha hqtor hd).toFinset ∪
      (finite_support_polePart_multOrbit (g := C₂) hq ha hqtor hd).toFinset with hs
  have hmem₁ : ∀ n : ℤ, polePart C₁ (multOrbit q a n) d ≠ 0 → n ∈ s := by
    intro n hn
    exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hn)
  have hmem₂ : ∀ n : ℤ, polePart C₂ (multOrbit q a n) d ≠ 0 → n ∈ s := by
    intro n hn
    exact Finset.mem_union_right _ (by rw [Set.Finite.mem_toFinset]; exact hn)
  have hmem : ∀ n : ℤ, polePart (C₁ + C₂) (multOrbit q a n) d ≠ 0 → n ∈ s := by
    intro n hn
    rw [polePart_add] at hn
    by_cases h1 : polePart C₁ (multOrbit q a n) d = 0
    · exact hmem₂ n (fun h2 => hn (by rw [h1, h2, add_zero]))
    · exact hmem₁ n h1
  rw [qOrbitResidue_eq_sum _ s hmem, qOrbitResidue_eq_sum _ s hmem₁,
    qOrbitResidue_eq_sum _ s hmem₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [polePart_add]
  ring

theorem qOrbitResidue_smul {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) (c : K) (C : RatFunc K) :
    qOrbitResidue q a d (algebraMap K (RatFunc K) c * C) = c * qOrbitResidue q a d C := by
  classical
  set s : Finset ℤ :=
    (finite_support_polePart_multOrbit (g := C) hq ha hqtor hd).toFinset with hs
  have hmem : ∀ n : ℤ, polePart C (multOrbit q a n) d ≠ 0 → n ∈ s := by
    intro n hn
    rw [hs, Set.Finite.mem_toFinset]
    exact hn
  have hmem' : ∀ n : ℤ, polePart (algebraMap K (RatFunc K) c * C) (multOrbit q a n) d ≠ 0 →
      n ∈ s := by
    intro n hn
    rw [polePart_smul] at hn
    refine hmem n ?_
    intro h0
    exact hn (by rw [h0, mul_zero])
  rw [qOrbitResidue_eq_sum _ s hmem', qOrbitResidue_eq_sum _ s hmem, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [polePart_smul]
  ring

theorem weight_mul_multOrbit {q : K} (hq : q ≠ 0) (a : K) (d : ℕ) (n : ℤ) :
    (q ^ (-(((d + 1 : ℕ)) : ℤ))) ^ n * multOrbit q a n = a * (q ^ (-(d : ℤ))) ^ n := by
  rw [multOrbit, ← zpow_mul, ← zpow_mul, ← mul_assoc,
    mul_comm (q ^ (-(((d + 1 : ℕ)) : ℤ) * n)) a, mul_assoc, ← zpow_add₀ hq]
  congr 2
  push_cast
  ring

/-- **The Euler operator on `q`-discrete residues.** -/
theorem qOrbitResidue_ratFuncEulerOp {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (d : ℕ) (f : RatFunc K) :
    qOrbitResidue q a (d + 1) (ratFuncEulerOp f)
      = (-((d : K) + 1)) * qOrbitResidue q a (d + 1) f
        + (-(d : K)) * a * qOrbitResidue q a d f := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hzero : (-((0 : ℕ) : K)) * a * qOrbitResidue q a 0 f = 0 := by
      push_cast
      ring
    rw [hzero, add_zero]
    set s : Finset ℤ :=
      (finite_support_polePart_multOrbit (g := ratFuncEulerOp f) hq ha hqtor
          (d := 0 + 1) (by omega)).toFinset ∪
        (finite_support_polePart_multOrbit (g := f) hq ha hqtor
          (d := 0 + 1) (by omega)).toFinset with hs
    have hmemL : ∀ n : ℤ, polePart (ratFuncEulerOp f) (multOrbit q a n) (0 + 1) ≠ 0 → n ∈ s := by
      intro n hn
      exact Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hn)
    have hmemR : ∀ n : ℤ, polePart f (multOrbit q a n) (0 + 1) ≠ 0 → n ∈ s := by
      intro n hn
      exact Finset.mem_union_right _ (by rw [Set.Finite.mem_toFinset]; exact hn)
    rw [qOrbitResidue_eq_sum _ s hmemL, qOrbitResidue_eq_sum _ s hmemR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [polePart_eulerOp f (multOrbit q a n) 0]
    push_cast
    ring
  · set s : Finset ℤ :=
      ((finite_support_polePart_multOrbit (g := ratFuncEulerOp f) hq ha hqtor
          (d := d + 1) (by omega)).toFinset ∪
        (finite_support_polePart_multOrbit (g := f) hq ha hqtor
          (d := d + 1) (by omega)).toFinset) ∪
        (finite_support_polePart_multOrbit (g := f) hq ha hqtor (d := d) hd).toFinset with hs
    have hmemL : ∀ n : ℤ, polePart (ratFuncEulerOp f) (multOrbit q a n) (d + 1) ≠ 0 → n ∈ s := by
      intro n hn
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (by rw [Set.Finite.mem_toFinset]; exact hn))
    have hmemR : ∀ n : ℤ, polePart f (multOrbit q a n) (d + 1) ≠ 0 → n ∈ s := by
      intro n hn
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (by rw [Set.Finite.mem_toFinset]; exact hn))
    have hmemD : ∀ n : ℤ, polePart f (multOrbit q a n) d ≠ 0 → n ∈ s := by
      intro n hn
      exact Finset.mem_union_right _ (by rw [Set.Finite.mem_toFinset]; exact hn)
    rw [qOrbitResidue_eq_sum _ s hmemL, qOrbitResidue_eq_sum _ s hmemR,
      qOrbitResidue_eq_sum _ s hmemD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [polePart_eulerOp f (multOrbit q a n) d, mul_add]
    have hw := weight_mul_multOrbit hq a d n
    have hexp : (-((d : K) + 1)) * ((q ^ (-(((d + 1 : ℕ)) : ℤ))) ^ n * polePart f (multOrbit q a n) (d + 1))
        = (q ^ (-(((d + 1 : ℕ)) : ℤ))) ^ n * ((((-(d : ℤ) - 1 : ℤ) : K)) * polePart f (multOrbit q a n) (d + 1)) := by
      push_cast
      ring
    have hcross : (-(d : K)) * a * ((q ^ (-(d : ℤ))) ^ n * polePart f (multOrbit q a n) d)
        = (q ^ (-(((d + 1 : ℕ)) : ℤ))) ^ n *
            (multOrbit q a n * (((-(d : ℤ) : ℤ) : K)) * polePart f (multOrbit q a n) d) := by
      rw [show (q ^ (-(((d + 1 : ℕ)) : ℤ))) ^ n *
            (multOrbit q a n * (((-(d : ℤ) : ℤ) : K)) * polePart f (multOrbit q a n) d)
          = ((q ^ (-(((d + 1 : ℕ)) : ℤ))) ^ n * multOrbit q a n) *
            ((((-(d : ℤ) : ℤ) : K)) * polePart f (multOrbit q a n) d) by ring, hw]
      push_cast
      ring
    rw [hexp, hcross]


@[simp] theorem qOrbitResidue_zero (q a : K) (d : ℕ) :
    qOrbitResidue q a d (0 : RatFunc K) = 0 := by
  rw [qOrbitResidue_eq_sum _ (∅ : Finset ℤ) (fun n hn => absurd (polePart_zero _ _) hn),
    Finset.sum_empty]

theorem qOrbitResidue_sum {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) {ι : Type*} (s : Finset ι)
    (F : ι → RatFunc K) :
    qOrbitResidue q a d (∑ i ∈ s, F i) = ∑ i ∈ s, qOrbitResidue q a d (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, qOrbitResidue_add hq ha hqtor hd, ih]

/-- Above the top nonvanishing residue level, every Euler jet still has vanishing residues. -/
theorem qOrbitResidue_iterate_eulerOp_eq_zero {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (D : ℕ) (r : RatFunc K)
    (hvanish : ∀ e : ℕ, D < e → qOrbitResidue q a e r = 0) :
    ∀ j e : ℕ, D + j < e → qOrbitResidue q a e (ratFuncEulerOp^[j] r) = 0 := by
  intro j
  induction j with
  | zero => intro e he; simpa using hvanish e (by omega)
  | succ j ih =>
      intro e he
      obtain ⟨d, rfl⟩ : ∃ d : ℕ, e = d + 1 := ⟨e - 1, by omega⟩
      rw [Function.iterate_succ_apply', qOrbitResidue_ratFuncEulerOp hq ha hqtor d,
        ih (d + 1) (by omega), ih d (by omega)]
      ring

/-- The top residue of the `j`-th Euler jet. -/
theorem qOrbitResidue_iterate_eulerOp_top {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (D : ℕ) (r : RatFunc K)
    (hvanish : ∀ e : ℕ, D < e → qOrbitResidue q a e r = 0) (j : ℕ) :
    qOrbitResidue q a (D + j) (ratFuncEulerOp^[j] r)
      = (∏ i ∈ Finset.range j, (-((D + i : ℕ) : K) * a)) * qOrbitResidue q a D r := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : D + (j + 1) = (D + j) + 1 := by omega
      rw [hstep, Function.iterate_succ_apply',
        qOrbitResidue_ratFuncEulerOp hq ha hqtor (D + j),
        qOrbitResidue_iterate_eulerOp_eq_zero hq ha hqtor D r hvanish j (D + j + 1) (by omega),
        ih, Finset.prod_range_succ]
      push_cast
      ring

/-- **A nonzero top residue survives every nonzero constant-coefficient Euler polynomial.** -/
theorem qOrbitResidue_eulerCombination_ne_zero [CharZero K] {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {D : ℕ} (hD : 0 < D) (r : RatFunc K)
    (hvanish : ∀ e : ℕ, D < e → qOrbitResidue q a e r = 0)
    (hres : qOrbitResidue q a D r ≠ 0) (J : ℕ) (c : ℕ → K) (hc : c J ≠ 0) :
    qOrbitResidue q a (D + J)
        (∑ j ∈ Finset.range (J + 1),
          algebraMap K (RatFunc K) (c j) * ratFuncEulerOp^[j] r) ≠ 0 := by
  classical
  have hDJ : 0 < D + J := by omega
  rw [qOrbitResidue_sum hq ha hqtor hDJ]
  have hterm : ∀ j ∈ Finset.range (J + 1), j ≠ J →
      qOrbitResidue q a (D + J) (algebraMap K (RatFunc K) (c j) * ratFuncEulerOp^[j] r) = 0 := by
    intro j hj hne
    have hlt : j < J := by
      have := Finset.mem_range.1 hj
      omega
    rw [qOrbitResidue_smul hq ha hqtor hDJ,
      qOrbitResidue_iterate_eulerOp_eq_zero hq ha hqtor D r hvanish j (D + J) (by omega), mul_zero]
  rw [Finset.sum_eq_single J hterm (fun h => absurd (Finset.self_mem_range_succ J) h)]
  rw [qOrbitResidue_smul hq ha hqtor hDJ,
    qOrbitResidue_iterate_eulerOp_top hq ha hqtor D r hvanish J]
  refine mul_ne_zero hc (mul_ne_zero ?_ hres)
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  refine mul_ne_zero (neg_ne_zero.2 ?_) ha
  exact_mod_cast Nat.cast_ne_zero.2 (by omega : D + i ≠ 0)

/-- **No nonzero Euler combination of a function with a nonzero top residue is `q`-summable.** -/
theorem not_dilationTelescoped_eulerCombination [CharZero K] {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {D : ℕ} (hD : 0 < D) (r : RatFunc K)
    (hvanish : ∀ e : ℕ, D < e → qOrbitResidue q a e r = 0)
    (hres : qOrbitResidue q a D r ≠ 0) (J : ℕ) (c : ℕ → K) (hc : c J ≠ 0) :
    ¬ ∃ k : RatFunc K,
      (∑ j ∈ Finset.range (J + 1), algebraMap K (RatFunc K) (c j) * ratFuncEulerOp^[j] r)
        = ratFuncScale q hq k - k :=
  not_dilationTelescoped_of_qOrbitResidue_ne_zero hq ha hqtor (by omega) _
    (qOrbitResidue_eulerCombination_ne_zero hq ha hqtor hD r hvanish hres J c hc)

end

end GaloisForLFunctions.HTGeometry
