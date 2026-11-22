import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.LowestShell

/-!
# Phase order and the least occupied pair

The least product leaves only winding one and radial multiplier one.
Either orientation then generates the rejected words. Its actual phase
has precisely the periods omitted by their winding indices.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture DyadicAperture.Binary

def leastWords (t : ExceptionalTime) : Set Word :=
  {x | rejected t.val x ∧ x false*x true = block t}

def raySector (a b : ℕ+) (m : ℕ) : Set Word :=
  {x | ∃ (r : Bool) (k : Missing m) (n : ℕ+), x = ray a b r k.val n}

private theorem floor_indices {H n : ℕ+} {k : ℕ} (hH : 1 < H.val) (hk : k ≠ 0) (he : H^k*n^2 = H) :
    k = 1 ∧ n = 1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [pow_succ',mul_assoc] at he
  have h : H^j*n^2 = 1 := mul_left_cancel (he.trans (mul_one H).symm)
  have hn : H.val^j*n.val^2 = 1 := congrArg PNat.val h
  have hpow : H.val^j = 1 := Nat.eq_one_of_mul_eq_one_right hn
  have hsq : n.val^2 = 1 := Nat.eq_one_of_mul_eq_one_left hn
  have hj : j = 0 := Nat.pow_right_injective hH (hpow.trans (pow_zero _).symm)
  exact ⟨by rw [hj],PNat.coe_injective ((pow_eq_one_iff_left (by norm_num : (2:ℕ) ≠ 0)).mp hsq)⟩

private theorem first_ray (a b : ℕ+) (r : Bool) : ray a b r 1 1 = if r then pair b a else pair a b := by
  cases r <;> funext i <;> cases i <;> change _^1*1 = _ <;> simp only [pow_one,mul_one] <;> rfl

theorem ray_exchange (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    ray b a r k n = ray a b (!r) k n := by cases r <;> rfl

private theorem raySector_comm (a b : ℕ+) (m : ℕ) : raySector a b m = raySector b a m := by
  have incl (u v : ℕ+) : raySector u v m ⊆ raySector v u m := by
    rintro x ⟨r,k,n,he⟩
    exact ⟨!r,k,n,he.trans (ray_exchange v u r _ _)⟩
  exact Set.Subset.antisymm (incl a b) (incl b a)

/-- The two least words are exactly the exchanged reduced direction. -/
theorem least_coordinates (t : ExceptionalTime) : ∃ a b : ℕ+, a.Coprime b ∧ a ≠ b ∧ a*b = block t ∧
    (∀ x, x ∈ leastWords t ↔ x = pair a b ∨ x = pair b a) ∧
    ∀ x, rejected t.val x ↔ x ∈ raySector a b (windingOrder t) := by
  obtain ⟨a,b,hc,hd,hb,e,he⟩ := block_basis t
  have hs (x : Word) : rejected t.val x ↔ x ∈ raySector a b (windingOrder t) := by
    constructor
    · intro hx
      obtain ⟨p,hp⟩ := e.surjective ⟨x,hx⟩
      have hword : (e p).val = x := congrArg Subtype.val hp
      exact ⟨p.1,p.2.1,p.2.2,hword.symm.trans (he p)⟩
    · rintro ⟨r,k,n,rfl⟩
      have hx := (e (r,k,n)).property
      rwa [he] at hx
  refine ⟨a,b,hc,hd,hb,fun x => ?_,hs⟩
  let k₁ : Missing (windingOrder t) := ⟨1,fun h => (not_le.mpr (order_nontrivial t)) (Nat.le_of_dvd Nat.zero_lt_one h)⟩
  constructor
  · rintro ⟨hx,hprod⟩
    obtain ⟨r,k,n,hr⟩ := (hs x).mp hx
    rw [hr,ray_product,hb] at hprod
    have hk₀ : k.val ≠ 0 := fun hz => k.property (hz ▸ dvd_zero _)
    obtain ⟨hk,hn⟩ := floor_indices (block_nontrivial t) hk₀ hprod
    rw [hr,hk,hn,first_ray]
    cases r <;> simp
  · rintro (rfl | rfl)
    · exact ⟨(hs _).mpr ⟨false,k₁,1,(first_ray a b false).symm⟩,hb⟩
    · exact ⟨(hs _).mpr ⟨true,k₁,1,(first_ray a b true).symm⟩,(mul_comm b a).trans hb⟩

theorem leastWords_nonempty (t : ExceptionalTime) : (leastWords t).Nonempty := (block_least t).1

theorem least_support (t : ExceptionalTime) (x : leastWords t) (y : Word) :
    rejected t.val y ↔ y ∈ raySector (x.val false) (x.val true) (windingOrder t) := by
  obtain ⟨a,b,_,_,_,hf,hs⟩ := least_coordinates t
  rcases (hf _).mp x.property with h | h
  · rw [h]; exact hs y
  · rw [h]; change _ ↔ y ∈ raySector b a _
    rw [raySector_comm b a]; exact hs y

theorem least_coprime (t : ExceptionalTime) (x : leastWords t) : (x.val false).Coprime (x.val true) := by
  obtain ⟨a,b,hc,_,_,hf,_⟩ := least_coordinates t
  rcases (hf _).mp x.property with h | h
  · rw [h]; exact hc
  · rw [h]; exact PNat.coprime_coe.mp (PNat.coprime_coe.mpr hc).symm

private theorem ray_log_gap (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    gap (ray a b r k n false) (ray a b r k n true) =
      if r then -((k:ℝ)*gap a b) else (k:ℝ)*gap a b := by
  have hp (c : ℕ+) : energy (c^k) = (k:ℝ)*energy c := by simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]
  cases r
  · change energy (a^k*n)-energy (b^k*n) = k*(energy a-energy b)
    rw [energy_mul,energy_mul,hp,hp]; ring
  · change energy (b^k*n)-energy (a^k*n) = -(k*(energy a-energy b))
    rw [energy_mul,energy_mul,hp,hp]; ring

theorem ray_phase (t : ℝ) (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    (binary t).phase () (ray a b r k n) =
      if r then (((binary t).phase () (pair a b))^k)⁻¹ else ((binary t).phase () (pair a b))^k := by
  change Circle.exp (t*gap (ray a b r k n false) (ray a b r k n true)) = if r then ((Circle.exp (t*gap a b))^k)⁻¹ else (Circle.exp (t*gap a b))^k
  rw [ray_log_gap,← Circle.exp_natCast_mul]
  cases r
  · change Circle.exp (t*(k*gap a b)) = Circle.exp (k*(t*gap a b))
    congr 1; ring
  · change Circle.exp (t*(-(k*gap a b))) = (Circle.exp (k*(t*gap a b)))⁻¹
    rw [← Circle.exp_neg]; congr 1; ring

private theorem abs_ray_gap (a b : ℕ+) (r : Bool) (k : ℕ) (n : ℕ+) :
    |gap (ray a b r k n false) (ray a b r k n true)| = (k:ℝ)*|gap a b| := by
  rw [ray_log_gap]
  cases r <;> simp [abs_mul,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)]

theorem least_ray_rejected (t : ExceptionalTime) (x : leastWords t) (r : Bool) (k : ℕ) (n : ℕ+) :
    rejected t.val (ray (x.val false) (x.val true) r k n) ↔ ¬windingOrder t ∣ k := by
  let a := x.val false
  let b := x.val true
  have hd : gap a b ≠ 0 := by
    intro h
    have hp := ((misses_iff_return _).mp ((rejected_iff _ _).mp x.property.1)).2
    exact hp (by change Circle.exp (t.val*gap a b) = 1; rw [h,mul_zero,Circle.exp_zero])
  rw [least_support t x]
  constructor
  · rintro ⟨s,l,u,he⟩
    have hg := congrArg (fun w : Word => |gap (w false) (w true)|) he
    change |gap (ray a b r k n false) (ray a b r k n true)| =
      |gap (ray a b s l.val u false) (ray a b s l.val u true)| at hg
    rw [abs_ray_gap,abs_ray_gap] at hg
    have hkl : k = l.val := Nat.cast_injective (R := ℝ) (mul_right_cancel₀ (abs_ne_zero.mpr hd) hg)
    exact hkl.symm ▸ l.property
  · exact fun h => ⟨r,⟨k,h⟩,n,rfl⟩

/-- The physical phase on either least word has the intrinsic winding order. -/
theorem least_phase_order (t : ExceptionalTime) (x : leastWords t) :
    orderOf ((binary t.val).phase () x.val) = windingOrder t := by
  let z := (binary t.val).phase () x.val
  obtain ⟨⟨j,hj⟩,_⟩ := (misses_iff_return _).mp ((rejected_iff _ _).mp x.property.1)
  change z^(2^j : ℕ) = 1 at hj
  have periods (k : ℕ) : windingOrder t ∣ k ↔ orderOf z ∣ k := by
    have hr : DyadicReturn (z^k) := ⟨j,by rw [← pow_mul,mul_comm,pow_mul,hj,one_pow]⟩
    have he := least_ray_rejected t x false k 1
    rw [rejected_iff,misses_iff_return,ray_phase] at he
    change (DyadicReturn (z^k) ∧ z^k ≠ 1) ↔ ¬windingOrder t ∣ k at he
    rw [and_iff_right hr] at he
    exact (not_iff_not.mp he.symm).trans orderOf_dvd_iff_pow_eq_one.symm
  exact Nat.dvd_antisymm ((periods _).mp dvd_rfl) ((periods _).mpr dvd_rfl)

#print axioms least_coordinates
#print axioms least_support
#print axioms least_coprime
#print axioms least_ray_rejected
#print axioms least_phase_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
