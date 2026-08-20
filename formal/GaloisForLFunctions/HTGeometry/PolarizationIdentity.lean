/-
# Polarization: a product of linear forms is a combination of `k`-th powers

The alternating sum of `(∑_{i ∈ S} x_i)^k` over all subsets `S` of a `k`-element index set expands,
by the multinomial expansion, into a sum over all maps `p : Fin k → Fin k`; the inner alternating
sum over the subsets containing the image of `p` vanishes unless `p` is onto, hence a permutation.
What survives is `k!` copies of the full product.  Applied pointwise to linear forms, this writes
every product of `k` linear forms -- in particular every degree-`k` monomial -- as a finite linear
combination of `k`-th powers of linear forms.

This is the classical Waring/polarization input that the several-variable determinant-completion
law needs: the eigenvalues of a diagonal operator pencil are *linear* in the parameter, so the
`k`-th power trace of such a pencil is a sum of `k`-th powers of linear forms, and polarization is
what makes an arbitrary homogeneous defect reachable.

Main results:
* `sum_powerset_superset_sign` — the alternating sum over the supersets of a set.
* `polarization` — **the polarization identity**.
* `prod_coord_mem_span_linearPow` — **a product of `k` coordinates is a combination of `k`-th
  powers of linear forms**.
-/
import Mathlib

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The alternating sum over the supersets of a set.**  Summing `(-1)^{|S|}` over the subsets `S`
of a `k`-element set that contain `A` gives `(-1)^k` when `A` is everything and `0` otherwise. -/
theorem sum_powerset_superset_sign {k : ℕ} (A : Finset (Fin k)) :
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℂ) ^ S.card * (if A ⊆ S then (1 : ℂ) else 0))
      = if A = Finset.univ then (-1 : ℂ) ^ k else 0 := by
  classical
  have hprod := Finset.prod_add (fun _ : Fin k => (-1 : ℂ))
    (fun i : Fin k => if i ∈ A then (0 : ℂ) else 1) Finset.univ
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (∏ _i ∈ S, (-1 : ℂ)) * ∏ i ∈ Finset.univ \ S, (if i ∈ A then (0 : ℂ) else 1)
        = (-1 : ℂ) ^ S.card * (if A ⊆ S then (1 : ℂ) else 0) := by
    intro S _
    rw [Finset.prod_const]
    congr 1
    by_cases hAS : A ⊆ S
    · rw [if_pos hAS]
      refine Finset.prod_eq_one fun i hi => ?_
      have hnot : i ∉ A := by
        intro hiA
        exact (Finset.mem_sdiff.mp hi).2 (hAS hiA)
      rw [if_neg hnot]
    · rw [if_neg hAS]
      obtain ⟨i, hiA, hiS⟩ := Finset.not_subset.mp hAS
      refine Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS⟩) ?_
      rw [if_pos hiA]
  rw [← Finset.sum_congr rfl hterm, ← hprod]
  have hfac : ∀ i : Fin k, (-1 : ℂ) + (if i ∈ A then (0 : ℂ) else 1)
      = if i ∈ A then (-1 : ℂ) else 0 := by
    intro i
    by_cases hi : i ∈ A <;> simp [hi]
  rw [Finset.prod_congr rfl fun i _ => hfac i]
  by_cases hA : A = Finset.univ
  · rw [if_pos hA]
    have : ∀ i : Fin k, (if i ∈ A then (-1 : ℂ) else 0) = -1 := by
      intro i
      rw [if_pos (hA ▸ Finset.mem_univ i)]
    rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · rw [if_neg hA]
    obtain ⟨i, hi⟩ : ∃ i : Fin k, i ∉ A := by
      by_contra hcon
      exact hA (Finset.eq_univ_of_forall (by simpa using hcon))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **The polarization identity.**  The alternating sum of the `k`-th powers of the partial sums is
`k!` times the full product. -/
theorem polarization {k : ℕ} (x : Fin k → ℂ) :
    (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, (-1 : ℂ) ^ S.card * (∑ i ∈ S, x i) ^ k)
      = (-1 : ℂ) ^ k * (Nat.factorial k : ℂ) * ∏ i, x i := by
  classical
  -- expand each power over the maps into `S`
  have hexp : ∀ S : Finset (Fin k), (∑ i ∈ S, x i) ^ k
      = ∑ p ∈ Finset.univ.filter (fun p : Fin k → Fin k => ∀ r, p r ∈ S), ∏ r, x (p r) := by
    intro S
    rw [Finset.sum_pow' S x k]
    refine Finset.sum_congr ?_ fun p _ => rfl
    ext p
    simp [Fintype.mem_piFinset]
  have hstep : (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℂ) ^ S.card * (∑ i ∈ S, x i) ^ k)
      = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
          ∑ p ∈ Finset.univ.filter (fun p : Fin k → Fin k => ∀ r, p r ∈ S),
            (-1 : ℂ) ^ S.card * ∏ r, x (p r) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hexp S, Finset.mul_sum]
  rw [hstep]
  -- swap the two sums
  have hswap : (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        ∑ p ∈ Finset.univ.filter (fun p : Fin k → Fin k => ∀ r, p r ∈ S),
          (-1 : ℂ) ^ S.card * ∏ r, x (p r))
      = ∑ p ∈ (Finset.univ : Finset (Fin k → Fin k)),
          ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.filter
            (fun S => ∀ r, p r ∈ S), (-1 : ℂ) ^ S.card * ∏ r, x (p r) := by
    refine Finset.sum_comm' ?_
    intro S p
    simp [Finset.mem_filter]
  rw [hswap]
  -- the inner sum is the superset indicator
  have hinner : ∀ p : Fin k → Fin k,
      (∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.filter (fun S => ∀ r, p r ∈ S),
          (-1 : ℂ) ^ S.card * ∏ r, x (p r))
        = (if Finset.univ.image p = Finset.univ then (-1 : ℂ) ^ k else 0) * ∏ r, x (p r) := by
    intro p
    rw [← Finset.sum_mul]
    congr 1
    rw [← sum_powerset_superset_sign (Finset.univ.image p)]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hiff : (∀ r, p r ∈ S) ↔ Finset.univ.image p ⊆ S := by
      constructor
      · intro h y hy
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hy
        exact h r
      · intro h r
        exact h (Finset.mem_image_of_mem p (Finset.mem_univ r))
    by_cases hcase : ∀ r, p r ∈ S
    · rw [if_pos hcase, if_pos (hiff.mp hcase), mul_one]
    · rw [if_neg hcase, if_neg (fun hc => hcase (hiff.mpr hc)), mul_zero]
  rw [Finset.sum_congr rfl fun p _ => hinner p]
  -- only the permutations survive
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k → Fin k))
    (fun p => Finset.univ.image p = Finset.univ)]
  have hzero : (∑ p ∈ Finset.univ.filter
      (fun p : Fin k → Fin k => ¬ (Finset.univ.image p = Finset.univ)),
        (if Finset.univ.image p = Finset.univ then (-1 : ℂ) ^ k else 0) * ∏ r, x (p r)) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg (Finset.mem_filter.mp hp).2, zero_mul]
  rw [hzero, add_zero]
  have hsurj : (∑ p ∈ Finset.univ.filter
      (fun p : Fin k → Fin k => Finset.univ.image p = Finset.univ),
        (if Finset.univ.image p = Finset.univ then (-1 : ℂ) ^ k else 0) * ∏ r, x (p r))
      = (-1 : ℂ) ^ k * ∑ p ∈ Finset.univ.filter
        (fun p : Fin k → Fin k => Finset.univ.image p = Finset.univ), ∏ r, x (p r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [if_pos (Finset.mem_filter.mp hp).2]
  rw [hsurj]
  -- each surviving term is the full product, and there are `k!` of them
  have hterm : ∀ p ∈ Finset.univ.filter
      (fun p : Fin k → Fin k => Finset.univ.image p = Finset.univ),
      (∏ r, x (p r)) = ∏ i, x i := by
    intro p hp
    have himg := (Finset.mem_filter.mp hp).2
    have hsurjp : Function.Surjective p := by
      intro y
      have hy : y ∈ Finset.univ.image p := by rw [himg]; exact Finset.mem_univ y
      obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hy
      exact ⟨r, hr⟩
    have hbijp : Function.Bijective p :=
      Finite.injective_iff_bijective.mp (Finite.injective_iff_surjective.mpr hsurjp)
    exact Fintype.prod_bijective p hbijp _ _ (fun r => rfl)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun p : Fin k → Fin k => Finset.univ.image p = Finset.univ)).card
      = Nat.factorial k := by
    have hbij : (Finset.univ.filter
        (fun p : Fin k → Fin k => Finset.univ.image p = Finset.univ))
        = Finset.univ.image (fun σ : Equiv.Perm (Fin k) => (σ : Fin k → Fin k)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro himg
        have hsurjp : Function.Surjective p := by
          intro y
          have hy : y ∈ Finset.univ.image p := by rw [himg]; exact Finset.mem_univ y
          obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hy
          exact ⟨r, hr⟩
        have hbijp : Function.Bijective p :=
          Finite.injective_iff_bijective.mp (Finite.injective_iff_surjective.mpr hsurjp)
        exact ⟨Equiv.ofBijective p hbijp, rfl⟩
      · rintro ⟨σ, rfl⟩
        exact Finset.eq_univ_of_forall fun y =>
          Finset.mem_image.mpr ⟨σ.symm y, Finset.mem_univ _, σ.apply_symm_apply y⟩
    rw [hbij, Finset.card_image_of_injective _ (fun σ τ h => Equiv.coe_fn_injective h),
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hcard]
  ring

/-! ## Waring: products of linear forms are combinations of `k`-th powers -/

/-- The set of `k`-th powers of linear forms on `ℂ^d`. -/
def linearPowSet (d k : ℕ) : Set ((Fin d → ℂ) → ℂ) :=
  {F | ∃ c : Fin d → ℂ, F = fun v => (∑ a, c a * v a) ^ k}

/-- **A product of `k` linear forms is a finite linear combination of `k`-th powers of linear
forms.** -/
theorem prod_linear_mem_span_linearPow {d k : ℕ} (c : Fin k → Fin d → ℂ) :
    (fun v : Fin d → ℂ => ∏ r, ∑ a, c r a * v a) ∈
      Submodule.span ℂ (linearPowSet d k) := by
  classical
  have hne : ((-1 : ℂ) ^ k * (Nat.factorial k : ℂ)) ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact_mod_cast (Nat.factorial_pos k).ne'
  have hfun : (fun v : Fin d → ℂ => ∏ r, ∑ a, c r a * v a)
      = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
          (((-1 : ℂ) ^ k * (Nat.factorial k : ℂ))⁻¹ * (-1 : ℂ) ^ S.card) •
            (fun v : Fin d → ℂ => (∑ a, (∑ r ∈ S, c r a) * v a) ^ k) := by
    funext v
    rw [Finset.sum_apply]
    have hlin : ∀ S : Finset (Fin k),
        (∑ r ∈ S, ∑ a, c r a * v a) = ∑ a, (∑ r ∈ S, c r a) * v a := by
      intro S
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_mul]
    have hpol := polarization (fun r => ∑ a, c r a * v a)
    simp only [hlin] at hpol
    have hgoal : (∏ r, ∑ a, c r a * v a)
        = ((-1 : ℂ) ^ k * (Nat.factorial k : ℂ))⁻¹ *
          ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
            (-1 : ℂ) ^ S.card * (∑ a, (∑ r ∈ S, c r a) * v a) ^ k := by
      rw [hpol]
      have hfac : ((Nat.factorial k : ℂ)) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos k).ne'
      field_simp
    rw [hgoal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  refine Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨fun a => ∑ r ∈ S, c r a, rfl⟩

/-- **A product of `k` coordinates is a finite linear combination of `k`-th powers of linear
forms**: every degree-`k` monomial function is reachable. -/
theorem prod_coord_mem_span_linearPow {d k : ℕ} (j : Fin k → Fin d) :
    (fun v : Fin d → ℂ => ∏ r, v (j r)) ∈ Submodule.span ℂ (linearPowSet d k) := by
  classical
  have hc : (fun v : Fin d → ℂ => ∏ r, v (j r))
      = fun v : Fin d → ℂ => ∏ r, ∑ a, (if a = j r then (1 : ℂ) else 0) * v a := by
    funext v
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single (j r)]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (j r)) h
  rw [hc]
  exact prod_linear_mem_span_linearPow _

end

end GaloisForLFunctions.HTGeometry
