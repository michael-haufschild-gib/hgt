import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Partition

/-!
# The vacuum slice of an exceptional clock

A vacuum label forces both the radial multiplier and one primitive label
to be one. The remaining label then detects the block and its exact phase order.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture DyadicAperture.Binary

abbrev VacuumTime := {t : ExceptionalTime // ∃ N : ℕ+, rejected t.val (pair N 1)}

private theorem vacuum_factors {a b n N : ℕ+} {k : ℕ} (hk : k ≠ 0)
    (ha : a^k*n = N) (hb : b^k*n = 1) : b = 1 ∧ N = (a*b)^k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hn : n.val ≤ (b^(j+1)*n).val := Nat.le_mul_of_pos_left _ (b^(j+1)).pos
  have hbase : b.val ≤ (b^(j+1)*n).val := by
    rw [pow_succ',mul_assoc]
    exact Nat.le_mul_of_pos_right _ (b^j*n).pos
  rw [hb] at hn hbase
  have hn' : n = 1 := PNat.coe_injective (by have := n.pos; change n.val ≤ 1 at hn; change n.val = 1; omega)
  have hb' : b = 1 := PNat.coe_injective (by have := b.pos; change b.val ≤ 1 at hbase; change b.val = 1; omega)
  exact ⟨hb',by simpa only [hn',hb',mul_one] using ha.symm⟩

private theorem ray_to_vacuum {a b n N : ℕ+} {k : ℕ} (hk : k ≠ 0) (r : Bool)
    (he : ray a b r k n = pair N 1) : (a = 1 ∨ b = 1) ∧ N = (a*b)^k := by
  have hf := congrFun he false
  have ht := congrFun he true
  cases r
  · obtain ⟨h,hN⟩ := vacuum_factors (a := a) (b := b) hk hf ht
    exact ⟨Or.inr h,hN⟩
  · obtain ⟨h,hN⟩ := vacuum_factors (a := b) (b := a) hk hf ht
    exact ⟨Or.inl h,by rwa [mul_comm b a] at hN⟩

private theorem vacuum_to_ray {a b : ℕ+} (h : a = 1 ∨ b = 1) (k : ℕ) :
    ∃ r : Bool, ray a b r k 1 = pair ((a*b)^k) 1 := by
  rcases h with rfl | rfl
  · refine ⟨true,funext fun i => ?_⟩
    cases i
    · change b^k*1 = (1*b)^k; simp
    · change (1:ℕ+)^k*1 = 1; simp
  · refine ⟨false,funext fun i => ?_⟩
    cases i
    · change a^k*1 = (a*1)^k; simp
    · change (1:ℕ+)^k*1 = 1; simp

/-- A nonempty vacuum slice is exactly the missing powers of the lowest block. -/
theorem vacuum_support (v : VacuumTime) (N : ℕ+) : rejected v.val.val (pair N 1) ↔
    ∃ k : Missing (windingOrder v.val), N = (block v.val)^k.val := by
  obtain ⟨a,b,_,_,hab,e,he⟩ := block_basis v.val
  have label (L : ℕ+) (hL : rejected v.val.val (pair L 1)) :
      (a = 1 ∨ b = 1) ∧ ∃ k : Missing (windingOrder v.val), L = (block v.val)^k.val := by
    obtain ⟨p,hp⟩ := e.surjective ⟨pair L 1,hL⟩
    have hr : (e p).val = pair L 1 := congrArg Subtype.val hp
    rw [he] at hr
    have hk : p.2.1.val ≠ 0 := fun hz => p.2.1.property (hz ▸ dvd_zero _)
    obtain ⟨hone,hpow⟩ := ray_to_vacuum hk p.1 hr
    exact ⟨hone,p.2.1,by rwa [hab] at hpow⟩
  constructor
  · exact fun h => (label N h).2
  · rintro ⟨k,rfl⟩
    obtain ⟨L,hL⟩ := v.property
    obtain ⟨r,hr⟩ := vacuum_to_ray (label L hL).1 k.val
    have hx := (e (r,k,1)).property
    rw [he] at hx
    change rejected v.val.val (ray a b r k.val 1) at hx
    rwa [hr,hab] at hx

private theorem power_index {B : ℕ+} (hB : 1 < B.val) {j k : ℕ} (he : B^j = B^k) : j = k := by
  have h := congrArg energy he
  simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow] at h
  exact Nat.cast_injective (R := ℝ) (mul_right_cancel₀ (Real.log_pos (by exact_mod_cast hB)).ne' h)

theorem vacuum_powers (v : VacuumTime) (k : ℕ) :
    rejected v.val.val (pair ((block v.val)^k) 1) ↔ ¬windingOrder v.val ∣ k := by
  rw [vacuum_support]
  constructor
  · rintro ⟨i,hi⟩
    exact (power_index (block_nontrivial v.val) hi).symm ▸ i.property
  · exact fun h => ⟨⟨k,h⟩,rfl⟩

theorem vacuum_phase (t : ℝ) (B : ℕ+) (k : ℕ) : (binary t).phase () (pair (B^k) 1) =
    (Circle.exp (t*energy B))^k := by
  rw [← Circle.exp_natCast_mul]
  change Circle.exp (t*(energy (B^k)-energy 1)) = _
  congr 1
  rw [show energy 1 = 0 by norm_num [energy],sub_zero]
  simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]
  ring

/-- On a nonempty vacuum slice the spectral winding order is the orbit length of the block. -/
theorem vacuum_phase_order (v : VacuumTime) :
    orderOf (Circle.exp (v.val.val*energy (block v.val))) = windingOrder v.val := by
  let z := Circle.exp (v.val.val*energy (block v.val))
  have hfirst := (vacuum_powers v 1).mpr (fun h => (not_le.mpr (order_nontrivial v.val)) (Nat.le_of_dvd Nat.zero_lt_one h))
  rw [rejected_iff,misses_iff_return,vacuum_phase,pow_one] at hfirst
  obtain ⟨j,hj⟩ := hfirst.1
  change z^(2^j : ℕ) = 1 at hj
  have periods (k : ℕ) : windingOrder v.val ∣ k ↔ orderOf z ∣ k := by
    have hr : DyadicReturn (z^k) := ⟨j,by rw [← pow_mul,mul_comm,pow_mul,hj,one_pow]⟩
    have he := vacuum_powers v k
    rw [rejected_iff,misses_iff_return,vacuum_phase] at he
    change (DyadicReturn (z^k) ∧ z^k ≠ 1) ↔ ¬windingOrder v.val ∣ k at he
    rw [and_iff_right hr] at he
    exact (not_iff_not.mp he.symm).trans orderOf_dvd_iff_pow_eq_one.symm
  exact Nat.dvd_antisymm ((periods _).mp dvd_rfl) ((periods _).mpr dvd_rfl)

#print axioms vacuum_support
#print axioms vacuum_powers
#print axioms vacuum_phase_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
