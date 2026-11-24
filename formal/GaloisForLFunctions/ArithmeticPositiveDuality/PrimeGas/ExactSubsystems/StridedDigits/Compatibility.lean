import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.StridedDigits.Single

/-! # Compatibility of strided occupation digits at one prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

/-- Both labeled digits and one common complement compose freely to the full gas. -/
def jointDigits (q : Nat.Primes) (a d b e : ℕ+) :=
  ∃ C : Set ℕ+, exactLabelProduct
    (fun ij : Fin d.val × Fin e.val => strideLabel q a d ij.1 * strideLabel q b e ij.2)
    (fun c : C => c.val)

private theorem ray_mul (q : Nat.Primes) (i j : ℕ) :
    primeRayLabel q i * primeRayLabel q j = primeRayLabel q (i+j) := (pow_add _ _ _).symm

private theorem digit_zero_of_small {a n r : ℕ} (hr : r < a) (h : a*n ≤ r) : n = 0 := by
  by_contra! hn
  have hl := Nat.mul_le_mul_left a (show 1 ≤ n by omega)
  rw [Nat.mul_one] at hl
  omega

private theorem initial_ray {q : Nat.Primes} {a d b e : ℕ+} (hab : a.val ≤ b.val) {C : Set ℕ+}
    (h : exactLabelProduct (fun ij : Fin d.val × Fin e.val => strideLabel q a d ij.1 * strideLabel q b e ij.2)
      (fun c : C => c.val)) (r : Fin a.val) : primeRayLabel q r.val ∈ C := by
  obtain ⟨⟨⟨i,j⟩,c⟩,hv⟩ := h.2 (primeRayLabel q r.val)
  change (primeRayLabel q (a.val*i.val)*primeRayLabel q (b.val*j.val))*c.val = _ at hv
  rw [ray_mul] at hv
  have hc := congrArg (primeCoordinates q) hv
  rw [primeCoordinates_mul_ray,primeCoordinates_ray] at hc
  have he : a.val*i.val+b.val*j.val+(primeCoordinates q c.val).1 = r.val := congrArg Prod.fst hc
  have hi := digit_zero_of_small r.isLt (show a.val*i.val ≤ r.val by omega)
  have hj := digit_zero_of_small (r.isLt.trans_le hab) (show b.val*j.val ≤ r.val by omega)
  simp only [hi,hj,Nat.mul_zero,Nat.zero_add,primeRayLabel,pow_zero,one_mul] at hv
  have hn : c.val = primeRayLabel q r.val := hv
  exact hn ▸ c.property

private theorem joint_necessity {q : Nat.Primes} {a d b e : ℕ+} (hab : a.val ≤ b.val)
    (hd : 1 < d.val) (he : 1 < e.val) (h : jointDigits q a d b e) : a.val*d.val ∣ b.val := by
  obtain ⟨C,hC⟩ := h
  let A := strideLabel q a d
  let B := strideLabel q b e
  let rest := fun v : Fin e.val × C => B v.1*v.2.val
  have hrest : exactLabelProduct A rest := by
    let f := fun v : (Fin d.val × Fin e.val) × C => A v.1.1 * B v.1.2 * v.2.val
    have hp (v : Fin d.val × (Fin e.val × C)) : A v.1 * rest v.2 = f ((Equiv.prodAssoc _ _ _).symm v) :=
      (mul_assoc _ _ _).symm
    change Function.Bijective (fun v : Fin d.val × (Fin e.val × C) => _)
    rw [funext hp]
    exact hC.comp (Equiv.prodAssoc _ _ _).symm.bijective
  have ht := (stride_complement_iff q a d _).mp (exact_range_right hrest)
  apply (full_run_iff a d hd b.val).mp
  intro r
  apply (strideTail_ray q a d _).mp
  rw [← ht]
  refine ⟨(⟨1,he⟩,⟨primeRayLabel q r.val,initial_ray hab hC r⟩),?_⟩
  change primeRayLabel q (b.val*1)*primeRayLabel q r.val = _
  rw [Nat.mul_one,ray_mul]

/-- Nesting the second quotient inside the first complementary block gives the joint bijection. -/
private theorem joint_sufficiency (q : Nat.Primes) (a d b e : ℕ+) (h : a.val*d.val ∣ b.val) :
    jointDigits q a d b e := by
  obtain ⟨k,hk⟩ := h
  have hkpos : 0 < k := by
    by_contra! hz
    have hb := b.pos
    rw [Nat.eq_zero_of_le_zero hz,Nat.mul_zero] at hk
    omega
  let K : ℕ+ := ⟨k,hkpos⟩
  let W := Fin a.val × (Fin k × ℕ)
  let reorder : (Fin d.val × Fin e.val) × W ≃ Fin d.val × (Fin a.val × (Fin e.val × (Fin k × ℕ))) :=
    ⟨fun v => (v.1.1,v.2.1,v.1.2,v.2.2),fun w => ((w.1,w.2.2.1),(w.2.1,w.2.2.2)),fun _ => rfl,fun _ => rfl⟩
  let E := (reorder.trans ((Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr (strideEquiv K e)))).trans (strideEquiv a d)
  let c := fun w : W => w.1.val+(a.val*d.val)*blockStart K e w.2
  let p := fun ij : Fin d.val × Fin e.val => a.val*ij.1.val+b.val*ij.2.val
  have hm (v : (Fin d.val × Fin e.val) × W) : p v.1+c v.2 = E v := by
    change _ = strideEquiv a d (v.1.1,v.2.1,strideEquiv K e (v.1.2,v.2.2))
    simp only [p,c,strideEquiv_apply,blockStart,hk,show K.val = k from rfl]
    change _ = a.val*v.1.1.val + (v.2.1.val + (a.val*d.val)*(k*v.1.2.val + (v.2.2.1.val+(k*e.val)*v.2.2.2)))
    ring
  have hp : Function.Bijective (fun v : (Fin d.val × Fin e.val) × W => p v.1+c v.2) := by
    rw [funext hm]
    exact E.bijective
  have hfull := exact_range_right (lift_exact q (a := p) (c := c) hp)
  refine ⟨Set.range (liftLabel q c),?_⟩
  simpa only [strideLabel,ray_mul,p] using hfull

/-- For two nontrivial digits at ordered strides, coexistence is precisely divisibility by the first block length. -/
theorem jointDigits_iff (q : Nat.Primes) (a d b e : ℕ+) (hab : a.val ≤ b.val) (hd : 1 < d.val) (he : 1 < e.val) :
    jointDigits q a d b e ↔ a.val*d.val ∣ b.val :=
  ⟨joint_necessity hab hd he,joint_sufficiency q a d b e⟩

#print axioms jointDigits_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
