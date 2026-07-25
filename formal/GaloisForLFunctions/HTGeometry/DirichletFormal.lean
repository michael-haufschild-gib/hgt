import GaloisForLFunctions.HTGeometry.DirichletLeadingTerm
import Mathlib

/-!
# The formal ring of Dirichlet series with polynomial coefficients

Dirichlet series `sum_{m >= 1} A_m(s) m^(-s)` with coefficients in `C[X]` form, formally, the ring
of arithmetic functions valued in `C[X]` under Dirichlet convolution.  The shift `s -> s+1` acts by

`A_m(s) -> A_m(s+1) / m`,

which is a ring automorphism precisely because the convolution is indexed by factorisations.

This file equips that ring with its least index and leading coefficient and verifies the
`DirichletLead` interface.  Everything here is formal: no convergence is involved.
-/

open Polynomial ArithmeticFunction

namespace HTGeometry

/-- Formal Dirichlet series with polynomial coefficients. -/
abbrev DirFormal := ArithmeticFunction (ℂ[X])

namespace DirFormal

/-- The least index carrying a nonzero coefficient. -/
noncomputable def ord (f : DirFormal) : ℕ := sInf {n | f n ≠ 0}

/-- The coefficient at the least index. -/
noncomputable def lead (f : DirFormal) : ℂ[X] := f (ord f)

theorem exists_ne_zero {f : DirFormal} (hf : f ≠ 0) : ∃ n, f n ≠ 0 := by
  by_contra h
  push_neg at h
  exact hf (ArithmeticFunction.ext fun n => by simp [h n])

theorem lead_ne_zero' {f : DirFormal} (hf : f ≠ 0) : lead f ≠ 0 :=
  Nat.sInf_mem (exists_ne_zero hf)

theorem coeff_eq_zero_of_lt {f : DirFormal} {n : ℕ} (h : n < ord f) : f n = 0 := by
  by_contra hne
  have hle : ord f ≤ n := Nat.sInf_le (show f n ≠ 0 from hne)
  omega

theorem ord_pos' {f : DirFormal} (hf : f ≠ 0) : 0 < ord f := by
  rcases Nat.eq_zero_or_pos (ord f) with h0 | h
  · exfalso
    have hl := lead_ne_zero' hf
    rw [lead, h0] at hl
    exact hl (by simp)
  · exact h

@[simp] theorem lead_zero' : lead (0 : DirFormal) = 0 := rfl

/-- Below the product of the two least indices every convolution term vanishes. -/
theorem mul_coeff_eq_zero_of_lt {f g : DirFormal} (hf : f ≠ 0) (hg : g ≠ 0)
    {n : ℕ} (hn : n < ord f * ord g) : (f * g) n = 0 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  by_cases hlt : x.1 < ord f
  · rw [coeff_eq_zero_of_lt hlt, zero_mul]
  · have hge : ord f ≤ x.1 := by omega
    have hb : x.2 < ord g := by
      by_contra hb
      push_neg at hb
      have : ord f * ord g ≤ x.1 * x.2 := Nat.mul_le_mul hge hb
      omega
    rw [coeff_eq_zero_of_lt hb, mul_zero]

/-- At the product of the two least indices only one convolution term survives. -/
theorem mul_coeff_at {f g : DirFormal} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g) (ord f * ord g) = lead f * lead g := by
  classical
  rw [ArithmeticFunction.mul_apply]
  have hmem : (ord f, ord g) ∈ (ord f * ord g).divisorsAntidiagonal := by
    refine Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, ?_⟩
    exact Nat.mul_ne_zero (ord_pos' hf).ne' (ord_pos' hg).ne'
  rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr hmem)]
  · simp [lead]
  · intro x hx hxns
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hne : x ≠ (ord f, ord g) := by simpa using hxns
    by_cases hlt : x.1 < ord f
    · rw [coeff_eq_zero_of_lt hlt, zero_mul]
    · have hge : ord f ≤ x.1 := by omega
      have hb : x.2 < ord g := by
        by_contra hb'
        push_neg at hb'
        have hx2pos : 0 < x.2 := by
          rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
          · exact absurd (by rw [← hxn, h0, mul_zero]) hn0
          · exact hpos
        have hle1 : ord f * x.2 ≤ x.1 * x.2 := Nat.mul_le_mul_right _ hge
        have hle2 : ord f * ord g ≤ ord f * x.2 := Nat.mul_le_mul_left _ hb'
        have heq : ord f * x.2 = x.1 * x.2 := le_antisymm hle1 (hxn ▸ hle2)
        have h1 : ord f = x.1 := Nat.eq_of_mul_eq_mul_right hx2pos heq
        have h2 : x.2 = ord g := by
          have hfp : 0 < ord f := ord_pos' hf
          have hxn' : ord f * x.2 = ord f * ord g := by
            conv_lhs => rw [h1]
            exact hxn
          exact Nat.eq_of_mul_eq_mul_left hfp hxn'
        exact hne (Prod.ext h1.symm h2)
      rw [coeff_eq_zero_of_lt hb, mul_zero]

theorem mul_ne_zero'' {f g : DirFormal} (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := by
  intro h
  have := mul_coeff_at hf hg
  rw [h] at this
  exact (mul_ne_zero (lead_ne_zero' hf) (lead_ne_zero' hg)) (by simpa using this.symm)

theorem ord_mul' {f g : DirFormal} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord (f * g) = ord f * ord g := by
  refine le_antisymm (Nat.sInf_le ?_) ?_
  · have := mul_coeff_at hf hg
    simp only [Set.mem_setOf_eq, this]
    exact mul_ne_zero (lead_ne_zero' hf) (lead_ne_zero' hg)
  · by_contra hlt
    push_neg at hlt
    have := lead_ne_zero' (mul_ne_zero'' hf hg)
    rw [lead] at this
    exact this (mul_coeff_eq_zero_of_lt hf hg hlt)

theorem lead_mul' {f g : DirFormal} (hf : f ≠ 0) (hg : g ≠ 0) :
    lead (f * g) = lead f * lead g := by
  rw [lead, ord_mul' hf hg, mul_coeff_at hf hg]

/-- The shift `s ↦ s + 1` on coefficients: `A_m(s) ↦ A_m(s+1) / m`. -/
noncomputable def shiftFun (f : DirFormal) : DirFormal :=
  ⟨fun n => Polynomial.C ((n : ℂ)⁻¹) * (f n).comp (X + 1), by simp⟩

@[simp] theorem shiftFun_apply (f : DirFormal) (n : ℕ) :
    shiftFun f n = Polynomial.C ((n : ℂ)⁻¹) * (f n).comp (X + 1) := rfl

/-- The inverse shift. -/
noncomputable def unshiftFun (f : DirFormal) : DirFormal :=
  ⟨fun n => Polynomial.C ((n : ℂ)) * (f n).comp (X - 1), by simp⟩

@[simp] theorem unshiftFun_apply (f : DirFormal) (n : ℕ) :
    unshiftFun f n = Polynomial.C ((n : ℂ)) * (f n).comp (X - 1) := rfl

theorem comp_add_sub (p : ℂ[X]) : (p.comp (X + 1)).comp (X - 1) = p := by
  rw [Polynomial.comp_assoc]
  simp

theorem comp_sub_add (p : ℂ[X]) : (p.comp (X - 1)).comp (X + 1) = p := by
  rw [Polynomial.comp_assoc]
  simp

/-- The shift is a ring automorphism of the formal Dirichlet ring. -/
noncomputable def sigmaEquiv : DirFormal ≃+* DirFormal where
  toFun := shiftFun
  invFun := unshiftFun
  left_inv f := by
    refine ArithmeticFunction.ext fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hne : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [unshiftFun_apply, shiftFun_apply, Polynomial.mul_comp, Polynomial.C_comp,
        comp_add_sub, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hne, Polynomial.C_1,
        one_mul]
  right_inv f := by
    refine ArithmeticFunction.ext fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hne : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [shiftFun_apply, unshiftFun_apply, Polynomial.mul_comp, Polynomial.C_comp,
        comp_sub_add, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hne, Polynomial.C_1,
        one_mul]
  map_add' f g := by
    refine ArithmeticFunction.ext fun n => ?_
    simp [Polynomial.add_comp, mul_add]
  map_mul' f g := by
    classical
    refine ArithmeticFunction.ext fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [shiftFun_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    have hsum : (∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2).comp (X + 1)
        = ∑ x ∈ n.divisorsAntidiagonal, (f x.1 * g x.2).comp (X + 1) := by
      simp only [Polynomial.comp, Polynomial.eval₂_finsetSum]
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx1 : ((x.1 : ℂ)) ≠ 0 := by
      refine Nat.cast_ne_zero.mpr ?_
      intro h0
      rw [h0, zero_mul] at hxn
      exact hn0 hxn.symm
    have hx2 : ((x.2 : ℂ)) ≠ 0 := by
      refine Nat.cast_ne_zero.mpr ?_
      intro h0
      rw [h0, mul_zero] at hxn
      exact hn0 hxn.symm
    have hcast : ((n : ℂ))⁻¹ = ((x.1 : ℂ))⁻¹ * ((x.2 : ℂ))⁻¹ := by
      rw [← hxn]
      push_cast
      rw [mul_inv]
    simp only [shiftFun_apply, Polynomial.mul_comp]
    rw [hcast, Polynomial.C_mul]
    ring

@[simp] theorem sigmaEquiv_apply (f : DirFormal) (n : ℕ) :
    sigmaEquiv f n = Polynomial.C ((n : ℂ)⁻¹) * (f n).comp (X + 1) := rfl

/-- The index-one embedding of the polynomial ring. -/
noncomputable def embHom : ℂ[X] →+* DirFormal where
  toFun p := ⟨fun n => if n = 1 then p else 0, by simp⟩
  map_one' := by refine ArithmeticFunction.ext fun n => ?_; by_cases h : n = 1 <;> simp [h]
  map_mul' p q := by
    classical
    refine ArithmeticFunction.ext fun n => ?_
    show (if n = 1 then p * q else 0) = _
    rw [ArithmeticFunction.mul_apply]
    by_cases h : n = 1
    · subst h; simp
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun x hx => ?_).symm
      obtain ⟨hxn, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      show (if x.1 = 1 then p else 0) * (if x.2 = 1 then q else 0) = 0
      by_cases h1 : x.1 = 1
      · have h2 : x.2 ≠ 1 := by
          intro h2
          rw [h1, h2, one_mul] at hxn
          exact h hxn.symm
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  map_zero' := by refine ArithmeticFunction.ext fun n => ?_; by_cases h : n = 1 <;> simp [h]
  map_add' p q := by
    refine ArithmeticFunction.ext fun n => ?_; by_cases h : n = 1 <;> simp [h]

@[simp] theorem embHom_apply (p : ℂ[X]) (n : ℕ) :
    embHom p n = if n = 1 then p else 0 := rfl

theorem sub_apply' (f g : DirFormal) (n : ℕ) : (f - g) n = f n - g n := rfl

theorem comp_add_one_eq_zero_iff {p : ℂ[X]} : p.comp (X + 1) = 0 ↔ p = 0 := by
  constructor
  · intro h
    have := comp_add_sub p
    rw [h] at this
    simpa using this.symm
  · intro h; simp [h]

theorem ord_sigma' (f : DirFormal) : ord (sigmaEquiv f) = ord f := by
  have hset : {n | (sigmaEquiv f) n ≠ 0} = {n | f n ≠ 0} := by
    ext n
    simp only [Set.mem_setOf_eq, sigmaEquiv_apply, ne_eq, mul_eq_zero, not_or]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hne : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      constructor
      · rintro ⟨-, h2⟩
        exact fun h0 => h2 (by rw [h0]; simp)
      · intro h0
        refine ⟨?_, ?_⟩
        · simpa using inv_ne_zero hne
        · exact fun hc => h0 (comp_add_one_eq_zero_iff.mp hc)
  rw [ord, ord, hset]

/-- The formal Dirichlet ring carries the leading-term interface. -/
noncomputable def dirichletLead : DirichletLead DirFormal where
  sigma := sigmaEquiv
  ord := ord
  lead := lead
  emb := embHom
  lead_zero := lead_zero'
  ord_pos := ord_pos'
  lead_ne_zero := lead_ne_zero'
  ord_mul := ord_mul'
  lead_mul := lead_mul'
  sigma_ne_zero := fun {f} hf h => hf (sigmaEquiv.injective (by simpa using h))
  ord_sigma := fun {f} _ => ord_sigma' f
  lead_sigma := by
    intro f hf
    have hpos : 0 < ord f := ord_pos' hf
    have hne : ((ord f : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [lead, ord_sigma' f, sigmaEquiv_apply, ← mul_assoc, ← Polynomial.C_mul,
      mul_inv_cancel₀ hne, Polynomial.C_1, one_mul, lead]
  le_ord_sub := by
    intro f g hf hg hord hsub
    by_contra hlt
    push_neg at hlt
    have h1 : f (ord (f - g)) = 0 := coeff_eq_zero_of_lt hlt
    have h2 : g (ord (f - g)) = 0 := coeff_eq_zero_of_lt (by rw [← hord]; exact hlt)
    exact lead_ne_zero' hsub (by rw [lead, sub_apply', h1, h2, sub_zero])
  lead_sub := by
    intro f g hf hg hord hsubord
    rw [lead, lead, lead, hsubord, ← hord, sub_apply']
  lead_eq_of_ord_lt := by
    intro f g hf hg hord hlt
    have h0 : (f - g) (ord f) = 0 := coeff_eq_zero_of_lt hlt
    have : f (ord f) - g (ord f) = 0 := by simpa using h0
    rw [lead, lead, ← hord]
    linear_combination this
  sigma_emb := by
    intro p
    refine ArithmeticFunction.ext fun n => ?_
    by_cases h : n = 1
    · subst h; simp
    · simp [h]
  emb_ne_zero := by
    intro p hp h
    have := congrArg (fun u : DirFormal => u 1) h
    simpa using hp this
  ord_emb := by
    intro p hp
    have hset : {n | (embHom p) n ≠ 0} = {1} := by
      ext n
      by_cases h : n = 1 <;> simp [h, hp]
    rw [ord, hset]
    simp
  lead_emb := by
    intro p hp
    have hord : ord (embHom p) = 1 := by
      have hset : {n | (embHom p) n ≠ 0} = {1} := by
        ext n
        by_cases h : n = 1 <;> simp [h, hp]
      rw [ord, hset]; simp
    rw [lead, hord]
    simp

end DirFormal

end HTGeometry
