import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.AffineVacuum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.DyadicCompletion

/-!
# Full-spectrum rigidity for a freely scaled oscillator and two balanced coordinates

The state labeled one determines an integral oscillator base. Its zero-occupation
sector then tiles exactly the integers indivisible by that base, which forces
all four real parameters.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

abbrev Coordinates (C : Radix) := ℕ × Half C × Half C

def affineGround {C : Radix} (K A D : ℝ) (p : Half C × Half C) :=
  K+A*(p.1.val:ℝ)+D*(p.2.val:ℝ)

def FullSpectrum (C : Radix) (b K A D : ℝ) : Prop :=
  ∃ e : Coordinates C ≃ ℕ+, ∀ u, ((e u).val:ℝ) = b^u.1*affineGround K A D u.2

private def excite {C : Radix} (u : Coordinates C) : Coordinates C := (u.1+1,u.2)

private theorem integer_parameters {C : Radix} {b K A D : ℝ} (h : FullSpectrum C b K A D) :
    ∃ q : Radix, ∃ a d : ℕ, b = (q.val:ℝ) ∧ K = 1 ∧ A = (a:ℝ) ∧ D = (d:ℝ) := by
  obtain ⟨e,he⟩ := h
  obtain ⟨u,hu⟩ := e.surjective 1
  let q := (e (excite u)).val
  have hq := (e (excite u)).pos
  have huval : ((e u).val:ℝ) = 1 := by rw [hu]; norm_num
  have hu₁ := huval.symm.trans (he u)
  have hb : (q:ℝ) = b := by
    change ((e (excite u)).val:ℝ) = b
    rw [he]
    change b^(u.1+1)*affineGround K A D u.2 = b
    rw [pow_succ]
    linear_combination -b * hu₁
  have hq₁ : 1 < q := by
    by_contra! hle
    have hx : (e (excite u)).val = 1 := by change q = 1; omega
    have H : excite u = u := e.injective (by rw [hu]; exact PNat.coe_injective hx)
    have HH : u.1+1 = u.1 := congrArg Prod.fst H
    omega
  have hge (p : Half C × Half C) : 1 ≤ affineGround K A D p := by
    have hh := he (0,p)
    change ((e (0,p)).val:ℝ) = b^0*affineGround K A D p at hh
    rw [pow_zero,one_mul] at hh
    rw [← hh]
    exact_mod_cast (e (0,p)).pos
  have hg : affineGround K A D u.2 = 1 := by
    have hpow : 1 ≤ b^u.1 := one_le_pow₀ (by rw [← hb]; exact_mod_cast hq₁.le)
    have hle := mul_le_mul_of_nonneg_right hpow (zero_le_one.trans (hge u.2))
    rw [one_mul,← hu₁] at hle
    exact le_antisymm hle (hge u.2)
  have lower (p : Half C × Half C) : affineGround K A D u.2 ≤ affineGround K A D p := by
    rw [hg]; exact hge p
  obtain ⟨x,hx⟩ := exists_large C u.2.1.val
  obtain ⟨y,hy⟩ := exists_large C u.2.2.val
  have hAx : A*u.2.1.val ≤ A*x.val := by
    have H := lower (x,u.2.2)
    unfold affineGround at H
    linarith only [H]
  have hDy : D*u.2.2.val ≤ D*y.val := by
    have H := lower (u.2.1,y)
    unfold affineGround at H
    linarith only [H]
  have hA : 0 ≤ A := by
    by_contra! hneg
    exact (not_lt_of_ge hAx) (mul_lt_mul_of_neg_left (by exact_mod_cast hx) hneg)
  have hD : 0 ≤ D := by
    by_contra! hneg
    exact (not_lt_of_ge hDy) (mul_lt_mul_of_neg_left (by exact_mod_cast hy) hneg)
  let o := origin C
  let i := single C ⟨1,C.property⟩
  have hi : i.val = 1 := single_val C _
  have ho : o.val = 0 := rfl
  have hK : K = 1 := by
    have hl := hge (o,o)
    simp only [affineGround,ho,Nat.cast_zero,mul_zero,add_zero] at hl
    unfold affineGround at hg
    linarith only [hl,hg,mul_nonneg hA (Nat.cast_nonneg (α := ℝ) u.2.1.val),
      mul_nonneg hD (Nat.cast_nonneg (α := ℝ) u.2.2.val)]
  let a := (e (0,i,o)).val
  let d := (e (0,o,i)).val
  have h₁ : (a:ℝ) = 1+A := by
    simpa only [a,affineGround,hK,hi,ho,Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,add_zero,pow_zero,one_mul]
      using he (0,i,o)
  have h₂ : (d:ℝ) = 1+D := by
    simpa only [d,affineGround,hK,hi,ho,Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,add_zero,pow_zero,one_mul]
      using he (0,o,i)
  refine ⟨⟨q,hq₁⟩,a-1,d-1,hb.symm,hK,?_,?_⟩
  · rw [Nat.cast_sub (show 1 ≤ a from (e (0,i,o)).pos),Nat.cast_one]
    linarith only [h₁]
  · rw [Nat.cast_sub (show 1 ≤ d from (e (0,o,i)).pos),Nat.cast_one]
    linarith only [h₂]

private theorem vacuum_of_full {C q : Radix} {a d : ℕ}
    (h : FullSpectrum C (q.val:ℝ) 1 (a:ℝ) (d:ℝ)) : SimpleVacuum C q.val a d := by
  obtain ⟨e,he⟩ := h
  have H (u : Coordinates C) : (e u).val = q.val^u.1*vacuumLabel a d u.2 := by
    have hh := he u
    unfold affineGround at hh
    unfold vacuumLabel
    exact_mod_cast hh
  have hz (p : Half C × Half C) : (e (0,p)).val = vacuumLabel a d p := by
    simpa only [pow_zero,one_mul] using H (0,p)
  have hs (u : Coordinates C) : (e (excite u)).val = q.val*(e u).val := by rw [H,H,excite,pow_succ]; ring
  constructor
  · intro p r hr
    have heq := e.injective (PNat.coe_injective ((hz p).trans (hr.trans (hz r).symm)))
    exact congrArg Prod.snd heq
  · intro n
    constructor
    · rintro ⟨p,rfl⟩
      have hn : 0 < vacuumLabel a d p := by rw [← hz]; exact (e (0,p)).pos
      refine ⟨hn,?_⟩
      rintro ⟨k,hk⟩
      have hk₀ : 0 < k := by
        by_contra! hle
        have h₀ : k = 0 := by omega
        rw [hk,h₀,mul_zero] at hn
        exact hn.false
      obtain ⟨u,hu⟩ := e.surjective (⟨k,hk₀⟩ : ℕ+)
      have huval : (e u).val = k := congrArg PNat.val hu
      have hw : (e (excite u)).val = (e (0,p)).val := by rw [hs,huval,hz,hk]
      have hf : u.1+1 = 0 := congrArg Prod.fst (e.injective (PNat.coe_injective hw))
      omega
    · rintro ⟨hn,hd⟩
      obtain ⟨u,hu⟩ := e.surjective (⟨n,hn⟩ : ℕ+)
      have huval : (e u).val = n := congrArg PNat.val hu
      have hu' := huval.symm.trans (H u)
      cases hm : u.1 with
      | zero => exact ⟨u.2,by simpa only [hm,pow_zero,one_mul] using hu'.symm⟩
      | succ m =>
        exact (hd ⟨q.val^m*vacuumLabel a d u.2,by rw [hu',hm,pow_succ]; ring⟩).elim

private theorem canonical_full (C : Radix) : FullSpectrum C 2 1 2 (2*(C.val:ℝ)) := by
  let e := ((Equiv.refl ℕ).prodCongr (interleave C)).trans binaryIndex
  refine ⟨e,fun u => ?_⟩
  change ((2^u.1*(2*interleave C u.2+1):ℕ):ℝ) = 2^u.1*affineGround 1 2 (2*(C.val:ℝ)) u.2
  rw [interleave_apply,affineGround]
  push_cast
  ring

private theorem full_swap {C : Radix} {b K A D : ℝ} (h : FullSpectrum C b K A D) :
    FullSpectrum C b K D A := by
  obtain ⟨e,he⟩ := h
  let swap := (Equiv.refl ℕ).prodCongr (Equiv.prodComm (Half C) (Half C))
  refine ⟨swap.trans e,fun u => ?_⟩
  change ((e (u.1,u.2.swap)).val:ℝ) = _
  rw [he]
  change b^u.1*(K+A*u.2.2.val+D*u.2.1.val) = b^u.1*(K+D*u.2.1.val+A*u.2.2.val)
  ring

/-- A complete integer labeling forces the oscillator base, ground offset and both slopes simultaneously. -/
theorem full_spectrum_rigidity (C : Radix) (b K A D : ℝ) :
    FullSpectrum C b K A D ↔ b = 2 ∧ K = 1 ∧
      ((A = 2 ∧ D = 2*(C.val:ℝ)) ∨ (D = 2 ∧ A = 2*(C.val:ℝ))) := by
  constructor
  · intro h
    obtain ⟨q,a,d,rfl,rfl,rfl,rfl⟩ := integer_parameters h
    have ⟨hb,hp⟩ := (vacuum_spectrum_iff C q a d).mp (vacuum_of_full h)
    refine ⟨by exact_mod_cast hb,rfl,?_⟩
    rcases hp with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · exact Or.inl ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
    · exact Or.inr ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
  · rintro ⟨rfl,rfl,h|h⟩ <;> rcases h with ⟨rfl,rfl⟩
    · exact canonical_full C
    · exact full_swap (canonical_full C)

/-- Multiplicity-one integer labels for the actual two-cutoff gas and one oscillator. -/
def CompleteLevels (t : ExceptionalTime) (j : ℕ) (b K A D : ℝ) : Prop :=
  ∃ e : Mode t j ≃ ℕ+, ∀ u, ((e u).val:ℝ) =
    b^u.1*(K+A*(u.2.1.val:ℝ)+D*(u.2.2.val:ℝ))

theorem complete_levels_iff (t : ExceptionalTime) (j : ℕ) (b K A D : ℝ) :
    CompleteLevels t j b K A D ↔ b = 2 ∧ K = 1 ∧
      ((A = 2 ∧ D = 2*((tailRadix t j).val:ℝ)) ∨ (D = 2 ∧ A = 2*((tailRadix t j).val:ℝ))) := by
  let C := clockRadix t j
  change CompleteLevels t j b K A D ↔ b = 2 ∧ K = 1 ∧
    ((A = 2 ∧ D = 2*(C.val:ℝ)) ∨ (D = 2 ∧ A = 2*(C.val:ℝ)))
  rw [← full_spectrum_rigidity C b K A D]
  let F := (Equiv.refl ℕ).prodCongr (pairDigits t j)
  constructor
  · rintro ⟨e,he⟩
    refine ⟨F.symm.trans e,fun u => ?_⟩
    have h := he (F.symm u)
    change ((e (F.symm u)).val:ℝ) = b^(F (F.symm u)).1*affineGround K A D (F (F.symm u)).2 at h
    change ((e (F.symm u)).val:ℝ) = b^u.1*affineGround K A D u.2
    rwa [F.apply_symm_apply] at h
  · rintro ⟨e,he⟩
    exact ⟨F.trans e,fun u => he (F u)⟩

#print axioms complete_levels_iff

#print axioms full_spectrum_rigidity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
