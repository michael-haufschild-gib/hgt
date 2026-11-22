import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.DyadicTower

/-!
# Basis and lowest energy of the remainder under clock refinement

The remaining positive windings are multiples of the current phase order.
The gcd recovers the common radial label, then the product and orientation
distinguish all coordinates of the basis.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture.Binary

def saturated (t : ExceptionalTime) (y : Word) := ∃ i, rejected (refined t i).val y

def remainder (t : ExceptionalTime) (j : ℕ) (y : Word) := saturated t y ∧ ¬rejected (refined t j).val y

abbrev TailIndex := Bool × (ℕ × ℕ+)

/-- Winding multiple and common radial label in a fixed orientation. -/
def tailWord (t : ExceptionalTime) (j : ℕ) (x : leastWords t) (p : TailIndex) : Word :=
  ray (x.val false) (x.val true) p.1 (windingOrder (refined t j)*(p.2.1+1)) p.2.2

theorem remainder_iff (t : ExceptionalTime) (j : ℕ) (x : leastWords t) (y : Word) :
    remainder t j y ↔ ∃ p, y = tailWord t j x p := by
  let v := refined t j
  let u : leastWords v := ⟨x.val,(refined_parameters t j).1.symm ▸ x.property⟩
  have hm : 0 < windingOrder v := Nat.zero_lt_one.trans (order_nontrivial v)
  constructor
  · rintro ⟨hs,hn⟩
    obtain ⟨r,k,n,rfl⟩ := (refined_union t x y).mp hs
    have hd : windingOrder v ∣ k.val := Classical.byContradiction fun h =>
      hn ((least_ray_rejected v u r k.val n).mpr h)
    obtain ⟨l,hl⟩ := hd
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show l ≠ 0 from
      fun h => k.ne_zero (by simpa only [h,Nat.mul_zero] using hl))
    exact ⟨(r,i,n),congrArg (fun d => ray (x.val false) (x.val true) r d n) hl⟩
  · rintro ⟨⟨r,i,n⟩,rfl⟩
    refine ⟨(refined_union t x _).mpr ⟨r,⟨_,Nat.mul_pos hm (Nat.succ_pos i)⟩,n,rfl⟩,?_⟩
    exact fun h => ((least_ray_rejected v u r _ n).mp h) (dvd_mul_right _ _)

private theorem ray_gcd {a b : ℕ+} (hc : a.Coprime b) (r : Bool) (k : ℕ) (n : ℕ+) :
    (ray a b r k n false).val.gcd (ray a b r k n true).val = n.val := by
  have hg (u v : ℕ+) (h : u.Coprime v) : (u.val^k*n.val).gcd (v.val^k*n.val) = n.val := by
    rw [Nat.gcd_mul_right,((PNat.coprime_coe.mpr h).pow k k).gcd_eq_one,Nat.one_mul]
  cases r
  · exact hg a b hc
  · exact hg b a (PNat.coprime_coe.mp (PNat.coprime_coe.mpr hc).symm)

theorem tail_product (t : ExceptionalTime) (j : ℕ) (x : leastWords t) (p : TailIndex) :
    tailWord t j x p false * tailWord t j x p true =
      (block t)^(windingOrder (refined t j)*(p.2.1+1))*p.2.2^2 := by
  rw [tailWord,ray_product,x.property.2]

private theorem tail_injective (t : ExceptionalTime) (j : ℕ) (x : leastWords t) :
    Function.Injective (tailWord t j x) := by
  rintro ⟨r,i,n⟩ ⟨s,l,v⟩ he
  have hg := congrArg (fun y : Word => (y false).val.gcd (y true).val) he
  change (ray _ _ r _ n false).val.gcd (ray _ _ r _ n true).val =
    (ray _ _ s _ v false).val.gcd (ray _ _ s _ v true).val at hg
  rw [ray_gcd (least_coprime t x),ray_gcd (least_coprime t x)] at hg
  obtain rfl : n = v := PNat.coe_injective hg
  have hp := congrArg (fun y : Word => y false*y true) he
  change tailWord t j x _ false * tailWord t j x _ true = tailWord t j x _ false * tailWord t j x _ true at hp
  rw [tail_product,tail_product] at hp
  let M := windingOrder (refined t j)
  have hM : 0 < M := Nat.zero_lt_one.trans (order_nontrivial _)
  have heq : (block t)^(M*(i+1)) = (block t)^(M*(l+1)) := mul_right_cancel hp
  have hk := Nat.pow_right_injective (block_nontrivial t) (congrArg PNat.val heq)
  obtain rfl : i = l := Nat.succ.inj (Nat.mul_left_cancel hM hk)
  have hd : x.val false ≠ x.val true := by
    obtain ⟨a,b,_,hab,_,hw,_⟩ := least_coordinates t
    rcases (hw _).mp x.property with h | h
    · rw [h]; exact hab
    · rw [h]; exact hab.symm
  have hk₀ := (Nat.mul_pos hM (Nat.succ_pos i)).ne'
  have diff : (x.val false)^(M*(i+1))*n ≠ (x.val true)^(M*(i+1))*n :=
    fun h => hd (PNat.coe_injective (Nat.pow_left_injective hk₀ (congrArg PNat.val (mul_right_cancel h))))
  cases r <;> cases s
  · rfl
  · exact (diff (congrArg (fun y : Word => y false) he)).elim
  · exact (diff (congrArg (fun y : Word => y false) he.symm)).elim
  · rfl

def tailBasis (t : ExceptionalTime) (j : ℕ) (x : leastWords t) : TailIndex ≃ {y // remainder t j y} :=
  Equiv.ofBijective (fun p => ⟨tailWord t j x p,(remainder_iff t j x _).mpr ⟨p,rfl⟩⟩)
    ⟨fun _ _ h => tail_injective t j x (congrArg Subtype.val h),fun y => by
      obtain ⟨p,hp⟩ := (remainder_iff t j x _).mp y.property
      exact ⟨p,Subtype.ext hp.symm⟩⟩

/-- Least product on which the finite projector and limiting projector differ. -/
theorem remainder_least_product (t : ExceptionalTime) (j : ℕ) :
    IsLeast {N : ℕ+ | ∃ y, remainder t j y ∧ y false*y true = N} ((block t)^(windingOrder (refined t j))) := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  let u : leastWords t := ⟨x,hx⟩
  let p : TailIndex := (false,0,1)
  refine ⟨⟨tailWord t j u p,(remainder_iff t j u _).mpr ⟨p,rfl⟩,?_⟩,?_⟩
  · simp only [tail_product,p,Nat.zero_add,one_pow,mul_one]
  · rintro N ⟨y,hy,rfl⟩
    obtain ⟨q,rfl⟩ := (remainder_iff t j u _).mp hy
    rw [tail_product]
    exact (Nat.pow_le_pow_right (block t).pos (Nat.le_mul_of_pos_right _ (Nat.succ_pos q.2.1))).trans
      (Nat.le_mul_of_pos_right _ (q.2.2^2).pos)

#print axioms remainder_iff
#print axioms tailBasis
#print axioms remainder_least_product

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
