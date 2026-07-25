import GaloisForLFunctions.HTGeometry.ShiftRationalBase
import Mathlib

/-!
# Polar parts of rational functions

Let `K` be a field over `C` and `x` a transcendental element.  A *polar datum* is a finitely
supported family `c : (C x N) ->_0 C`, interpreted as

`polarSum x c = sum over (a, j) of c (a, j) / (x - a) ^ (j + 1)`.

The fact proved here is that a polynomial plus a polar sum vanishes only trivially
(`polar_injective`): the polynomial part and every polar coefficient of an element of `C(x)` are
uniquely determined.  This is the uniqueness half of the partial-fraction decomposition, in the
form the shift-defect classification consumes.
-/

open Polynomial
open scoped Classical

namespace HTGeometry

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- The elementary polar term `1 / (x - a) ^ (j + 1)`. -/
noncomputable def polarTerm (x : K) (α : ℂ) (j : ℕ) : K :=
  (x - algebraMap ℂ K α)⁻¹ ^ (j + 1)

/-- The rational function attached to a finite polar datum. -/
noncomputable def polarSum (x : K) (c : (ℂ × ℕ) →₀ ℂ) : K :=
  c.sum fun p t => algebraMap ℂ K t * polarTerm x p.1 p.2

@[simp] theorem polarSum_zero (x : K) : polarSum x 0 = 0 := by
  simp [polarSum]

theorem polarSum_add (x : K) (c d : (ℂ × ℕ) →₀ ℂ) :
    polarSum x (c + d) = polarSum x c + polarSum x d := by
  classical
  refine Finsupp.sum_add_index' (fun p => by simp) (fun p t u => ?_)
  simp [map_add, add_mul]

theorem polarSum_smul (x : K) (r : ℂ) (c : (ℂ × ℕ) →₀ ℂ) :
    polarSum x (r • c) = algebraMap ℂ K r * polarSum x c := by
  classical
  rw [polarSum, polarSum, Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [map_mul, mul_assoc]

/-- The largest pole order occurring at `beta` in a polar datum. -/
noncomputable def polarTop (c : (ℂ × ℕ) →₀ ℂ) (β : ℂ) : ℕ :=
  (c.support.filter (fun p : ℂ × ℕ => p.1 = β)).sup Prod.snd

/-- The set of poles of a polar datum. -/
noncomputable def polarPoles (c : (ℂ × ℕ) →₀ ℂ) : Finset ℂ :=
  c.support.image Prod.fst

theorem le_polarTop {c : (ℂ × ℕ) →₀ ℂ} {α : ℂ} {j : ℕ} (hj : (α, j) ∈ c.support) :
    j ≤ polarTop c α := by
  have hmem : ((α, j) : ℂ × ℕ) ∈ c.support.filter (fun p : ℂ × ℕ => p.1 = α) :=
    Finset.mem_filter.mpr ⟨hj, rfl⟩
  exact Finset.le_sup (f := Prod.snd) hmem

theorem mem_polarPoles {c : (ℂ × ℕ) →₀ ℂ} {α : ℂ} {j : ℕ} (hj : (α, j) ∈ c.support) :
    α ∈ polarPoles c :=
  Finset.mem_image.mpr ⟨(α, j), hj, rfl⟩

theorem polarTop_mem_support {c : (ℂ × ℕ) →₀ ℂ} {β : ℂ} (hβ : β ∈ polarPoles c) :
    (β, polarTop c β) ∈ c.support := by
  obtain ⟨q, hq, hq1⟩ := Finset.mem_image.mp hβ
  have hne : (c.support.filter (fun p : ℂ × ℕ => p.1 = β)).Nonempty :=
    ⟨q, Finset.mem_filter.mpr ⟨hq, hq1⟩⟩
  obtain ⟨r, hr, hrM⟩ := Finset.exists_mem_eq_sup _ hne (Prod.snd : ℂ × ℕ → ℕ)
  obtain ⟨hrs, hr1⟩ := Finset.mem_filter.mp hr
  have hreq : r = (β, polarTop c β) := by
    refine Prod.ext hr1 ?_
    rw [polarTop, ← hrM]
  rwa [hreq] at hrs

section Injective

variable {x : K}

theorem coord_sub_const_ne_zero (hx : Transcendental ℂ x) (α : ℂ) :
    x - algebraMap ℂ K α ≠ 0 := by
  intro h
  refine hx ⟨X - Polynomial.C α, Polynomial.X_sub_C_ne_zero α, ?_⟩
  simpa using h

/-- The common denominator clearing a polar sum. -/
noncomputable def polarDen (c : (ℂ × ℕ) →₀ ℂ) : ℂ[X] :=
  ∏ β ∈ polarPoles c, (X - Polynomial.C β) ^ (polarTop c β + 1)

/-- The cofactor of a single polar term inside `polarDen`. -/
noncomputable def polarCof (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) : ℂ[X] :=
  (X - Polynomial.C α) ^ (polarTop c α - j)
    * ∏ β ∈ (polarPoles c).erase α, (X - Polynomial.C β) ^ (polarTop c β + 1)

theorem polarCof_mul (c : (ℂ × ℕ) →₀ ℂ) {α : ℂ} {j : ℕ} (hj : (α, j) ∈ c.support) :
    (X - Polynomial.C α) ^ (j + 1) * polarCof c α j = polarDen c := by
  have hmem : α ∈ polarPoles c := mem_polarPoles hj
  have hjM : j ≤ polarTop c α := le_polarTop hj
  have hexp : j + 1 + (polarTop c α - j) = polarTop c α + 1 := by omega
  rw [polarCof, polarDen, ← Finset.prod_erase_mul _ _ hmem, ← mul_assoc, ← pow_add, hexp]
  ring

theorem polarDen_ne_zero (c : (ℂ × ℕ) →₀ ℂ) : polarDen c ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun β _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero β)

theorem polarDen_eval (c : (ℂ × ℕ) →₀ ℂ) {β : ℂ} (hβ : β ∈ polarPoles c) :
    (polarDen c).eval β = 0 := by
  rw [polarDen, Polynomial.eval_prod]
  refine Finset.prod_eq_zero hβ ?_
  simp

/-- Only the top-order cofactor at `beta` survives evaluation at `beta`. -/
theorem polarCof_eval_eq_zero (c : (ℂ × ℕ) →₀ ℂ) {β α : ℂ} {j : ℕ}
    (hβ : β ∈ polarPoles c) (hj : (α, j) ∈ c.support)
    (hne : ¬(α = β ∧ j = polarTop c β)) :
    (polarCof c α j).eval β = 0 := by
  by_cases hab : α = β
  · subst hab
    have hle := le_polarTop hj
    have hjne : j ≠ polarTop c α := fun h => hne ⟨rfl, h⟩
    have hpos : 0 < polarTop c α - j := by omega
    rw [polarCof, Polynomial.eval_mul, Polynomial.eval_pow]
    simp [zero_pow hpos.ne']
  · have hmem : β ∈ (polarPoles c).erase α := Finset.mem_erase.mpr ⟨Ne.symm hab, hβ⟩
    rw [polarCof, Polynomial.eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hmem ?_)
    simp

theorem polarCof_eval_top_ne_zero (c : (ℂ × ℕ) →₀ ℂ) (β : ℂ) :
    (polarCof c β (polarTop c β)).eval β ≠ 0 := by
  rw [polarCof]
  simp only [Nat.sub_self, pow_zero, one_mul, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  refine Finset.prod_ne_zero_iff.mpr fun γ hγ => ?_
  obtain ⟨hγne, -⟩ := Finset.mem_erase.mp hγ
  exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hγne))

theorem aeval_polarDen_mul_polarTerm (hx : Transcendental ℂ x) (c : (ℂ × ℕ) →₀ ℂ)
    {α : ℂ} {j : ℕ} (hj : (α, j) ∈ c.support) :
    Polynomial.aeval x (polarDen c) * polarTerm x α j
      = Polynomial.aeval x (polarCof c α j) := by
  have hne : x - algebraMap ℂ K α ≠ 0 := coord_sub_const_ne_zero hx α
  rw [← polarCof_mul c hj, map_mul, polarTerm]
  have hpow : Polynomial.aeval x ((X - Polynomial.C α) ^ (j + 1))
      = (x - algebraMap ℂ K α) ^ (j + 1) := by simp
  rw [hpow, mul_comm ((x - algebraMap ℂ K α) ^ (j + 1)), mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hne, one_pow, mul_one]

/-- **A polynomial plus a polar sum vanishes only trivially.** -/
theorem polar_injective (hx : Transcendental ℂ x) {p : ℂ[X]} {c : (ℂ × ℕ) →₀ ℂ}
    (h : Polynomial.aeval x p + polarSum x c = 0) : p = 0 ∧ c = 0 := by
  classical
  have hc : c = 0 := by
    by_contra hcne
    obtain ⟨q, hq⟩ := Finsupp.support_nonempty_iff.mpr hcne
    set β : ℂ := q.1 with hβdef
    have hβ : β ∈ polarPoles c := mem_polarPoles hq
    have hβsupp : (β, polarTop c β) ∈ c.support := polarTop_mem_support hβ
    have hclear : Polynomial.aeval x
        (p * polarDen c + ∑ r ∈ c.support, Polynomial.C (c r) * polarCof c r.1 r.2) = 0 := by
      have hmul := congrArg (fun z : K => Polynomial.aeval x (polarDen c) * z) h
      simp only [mul_add, mul_zero] at hmul
      have hsum : ∑ r ∈ c.support,
            Polynomial.aeval x (Polynomial.C (c r) * polarCof c r.1 r.2)
          = Polynomial.aeval x (polarDen c) * polarSum x c := by
        rw [polarSum, Finsupp.sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr' : (r.1, r.2) ∈ c.support := by simpa using hr
        rw [map_mul, Polynomial.aeval_C, ← aeval_polarDen_mul_polarTerm hx c hr']
        ring
      rw [map_add, map_mul, map_sum, hsum, mul_comm (Polynomial.aeval x p)]
      exact hmul
    have hpoly : p * polarDen c
        + ∑ r ∈ c.support, Polynomial.C (c r) * polarCof c r.1 r.2 = 0 :=
      aeval_coord_injective hx (by simpa using hclear)
    have heval := congrArg (fun f : ℂ[X] => f.eval β) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_zero,
      Polynomial.eval_finsetSum, Polynomial.eval_C] at heval
    rw [polarDen_eval c hβ, mul_zero, zero_add] at heval
    have hsingle : ∑ r ∈ c.support, c r * (polarCof c r.1 r.2).eval β
        = c (β, polarTop c β) * (polarCof c β (polarTop c β)).eval β := by
      refine Finset.sum_eq_single (β, polarTop c β) ?_ ?_
      · intro r hr hrne
        have hr' : (r.1, r.2) ∈ c.support := by simpa using hr
        have hnot : ¬(r.1 = β ∧ r.2 = polarTop c β) := by
          rintro ⟨h1, h2⟩
          exact hrne (Prod.ext h1 h2)
        rw [polarCof_eval_eq_zero c hβ hr' hnot, mul_zero]
      · intro hnot
        exact absurd hβsupp hnot
    rw [hsingle] at heval
    rcases mul_eq_zero.mp heval with h0 | h0
    · exact absurd h0 (Finsupp.mem_support_iff.mp hβsupp)
    · exact absurd h0 (polarCof_eval_top_ne_zero c β)
  refine ⟨?_, hc⟩
  rw [hc, polarSum_zero, add_zero] at h
  exact aeval_coord_injective hx (by simpa using h)

end Injective


theorem polarSum_single (x : K) (α : ℂ) (j : ℕ) (t : ℂ) :
    polarSum x (Finsupp.single (α, j) t) = algebraMap ℂ K t * polarTerm x α j := by
  classical
  rw [polarSum, Finsupp.sum_single_index (by simp)]

section Existence

variable {x : K}

theorem exists_polarSum_aux (hx : Transcendental ℂ x) :
    ∀ (n : ℕ) (A B : ℂ[X]), B ≠ 0 → B.natDegree ≤ n →
      ∃ (p : ℂ[X]) (c : (ℂ × ℕ) →₀ ℂ),
        Polynomial.aeval x A / Polynomial.aeval x B
          = Polynomial.aeval x p + polarSum x c := by
  intro n
  induction n with
  | zero =>
      intro A B hB hdeg
      have hB0 : B.natDegree = 0 := Nat.le_zero.mp hdeg
      obtain ⟨b, hb0, rfl⟩ : ∃ b : ℂ, b ≠ 0 ∧ B = Polynomial.C b := by
        refine ⟨B.coeff 0, ?_, Polynomial.eq_C_of_natDegree_eq_zero hB0⟩
        intro h
        exact hB (by rw [Polynomial.eq_C_of_natDegree_eq_zero hB0, h, map_zero])
      refine ⟨A * Polynomial.C b⁻¹, 0, ?_⟩
      rw [polarSum_zero, add_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_C,
        div_eq_iff (by simpa using hb0), mul_assoc, ← map_mul, inv_mul_cancel₀ hb0,
        map_one, mul_one]
  | succ n ih =>
      intro A B hB hdeg
      rcases Nat.eq_zero_or_pos B.natDegree with hB0 | hBpos
      · exact ih A B hB (by omega)
      obtain ⟨α, hα⟩ := Complex.exists_root (f := B)
        (Polynomial.natDegree_pos_iff_degree_pos.mp hBpos)
      set m : ℕ := B.rootMultiplicity α with hm
      have hmpos : 0 < m := (Polynomial.rootMultiplicity_pos hB).mpr hα
      set B₁ : ℂ[X] := B /ₘ (X - Polynomial.C α) ^ m with hB₁
      have hBfac : B = (X - Polynomial.C α) ^ m * B₁ :=
        (Polynomial.pow_mul_divByMonic_rootMultiplicity_eq B α).symm
      have hB₁ne : B₁ ≠ 0 := by
        intro h
        exact hB (by rw [hBfac, h, mul_zero])
      have hB₁α : B₁.eval α ≠ 0 :=
        Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero α hB
      set t : ℂ := A.eval α / B₁.eval α with ht
      have hroot : (A - Polynomial.C t * B₁).eval α = 0 := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ht]
        field_simp
        simp
      obtain ⟨A₂, hA₂⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      set B' : ℂ[X] := (X - Polynomial.C α) ^ (m - 1) * B₁ with hB'
      have hB'ne : B' ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hB₁ne
      have hdegB : B.natDegree = m + B₁.natDegree := by
        rw [hBfac, Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hB₁ne,
          Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      have hdegB' : B'.natDegree = (m - 1) + B₁.natDegree := by
        rw [hB', Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hB₁ne,
          Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      obtain ⟨p, c, hpc⟩ := ih A₂ B' hB'ne (by omega)
      refine ⟨p, c + Finsupp.single (α, m - 1) t, ?_⟩
      have hxα : x - algebraMap ℂ K α ≠ 0 := coord_sub_const_ne_zero hx α
      have hB₁K : Polynomial.aeval x B₁ ≠ 0 := by
        intro h
        exact hB₁ne (aeval_coord_injective hx (by simpa using h))
      have hpow : Polynomial.aeval x ((X - Polynomial.C α) ^ (m - 1))
          = (x - algebraMap ℂ K α) ^ (m - 1) := by simp
      have hmsucc : m - 1 + 1 = m := by omega
      have hBK : Polynomial.aeval x B
          = (x - algebraMap ℂ K α) ^ m * Polynomial.aeval x B₁ := by
        rw [hBfac, map_mul]
        congr 1
        simp
      have hB'K : Polynomial.aeval x B'
          = (x - algebraMap ℂ K α) ^ (m - 1) * Polynomial.aeval x B₁ := by
        rw [hB', map_mul, hpow]
      have hAK : Polynomial.aeval x A
          = algebraMap ℂ K t * Polynomial.aeval x B₁
            + (x - algebraMap ℂ K α) * Polynomial.aeval x A₂ := by
        have := congrArg (fun q : ℂ[X] => Polynomial.aeval x q) hA₂
        simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] at this
        linear_combination this
      rw [polarSum_add, polarSum_single, ← add_assoc, ← hpc, hAK, hBK, hB'K, polarTerm,
        hmsucc]
      have hpowne : (x - algebraMap ℂ K α) ^ m ≠ 0 := pow_ne_zero _ hxα
      have hpowne' : (x - algebraMap ℂ K α) ^ (m - 1) ≠ 0 := pow_ne_zero _ hxα
      have hinv : ((x - algebraMap ℂ K α)⁻¹) ^ m * (x - algebraMap ℂ K α) ^ m = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hxα, one_pow]
      have hsplit : (x - algebraMap ℂ K α) ^ m
          = (x - algebraMap ℂ K α) ^ (m - 1) * (x - algebraMap ℂ K α) := by
        rw [← pow_succ, hmsucc]
      rw [inv_pow, ← div_eq_mul_inv, div_add_div _ _ (mul_ne_zero hpowne' hB₁K) hpowne,
        div_eq_div_iff (mul_ne_zero hpowne hB₁K)
          (mul_ne_zero (mul_ne_zero hpowne' hB₁K) hpowne), hsplit]
      ring

/-- **Every element of `C(x)` is a polynomial plus a polar sum.** -/
theorem exists_polarSum (hx : Transcendental ℂ x) {v : K} (hv : v ∈ coordBase x) :
    ∃ (p : ℂ[X]) (c : (ℂ × ℕ) →₀ ℂ), v = Polynomial.aeval x p + polarSum x c := by
  classical
  obtain ⟨A, B, hAB⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ v).mp hv
  rcases eq_or_ne B 0 with rfl | hB
  · exact ⟨0, 0, by simpa using hAB⟩
  · obtain ⟨p, c, hpc⟩ := exists_polarSum_aux hx B.natDegree A B hB (le_refl _)
    exact ⟨p, c, by rw [hAB, hpc]⟩

end Existence

end HTGeometry
