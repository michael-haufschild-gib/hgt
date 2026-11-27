import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Counting
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal.Thresholds

/-! # Exact sets of invisible elementary primes at prescribed rational damping -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration

open Real Finset

private def key (A : ℕ) (p : Nat.Primes) : ℚ :=
  ((p.val : ℚ)^A)+((p.val : ℚ)^A)⁻¹

private theorem key_props {A : ℕ} (ha : 0<A) :
    (∀ p, 2<key A p) ∧ Function.Injective (key A) := by
  have one (p : Nat.Primes) : (1 : ℚ)<(p.val : ℚ)^A :=
    one_lt_pow₀ (Nat.one_lt_cast.mpr p.property.one_lt) ha.ne'
  have inc {a b : ℚ} (ag : 1<a) (lt : a<b) : a+a⁻¹<b+b⁻¹ := by
    have ap := zero_lt_one.trans ag
    have bp := ap.trans lt
    have ab : 1<a*b := ag.trans (by simpa only [mul_one] using mul_lt_mul_of_pos_left (ag.trans lt) ap)
    have product := mul_pos (sub_pos.mpr lt) (sub_pos.mpr ab)
    apply (mul_lt_mul_iff_left₀ (mul_pos ap bp)).mp
    rw [show (a+a⁻¹)*(a*b)=a^2*b+b by field_simp,
      show (b+b⁻¹)*(a*b)=a*b^2+a by field_simp]
    nlinarith only [product]
  refine ⟨fun p => ?_,?_⟩
  · let v := (p.val : ℚ)^A
    have vg : 1<v := one p
    have pos := zero_lt_one.trans vg
    change 2<v+v⁻¹
    have sq := sq_pos_of_pos (sub_pos.mpr vg)
    apply (mul_lt_mul_iff_left₀ pos).mp
    rw [add_mul,inv_mul_cancel₀ pos.ne']
    nlinarith only [sq]
  · have strict {p q : Nat.Primes} (lt : p.val<q.val) : key A p<key A q := by
      apply inc (one p)
      exact pow_lt_pow_left₀ (Nat.cast_lt.mpr lt) (Nat.cast_nonneg _) ha.ne'
    intro p q eq
    rcases lt_trichotomy p.val q.val with lt | same | gt
    · exact ((strict lt).ne eq).elim
    · exact Subtype.ext same
    · exact ((strict gt).ne eq.symm).elim

private theorem measured (A : ℕ) (p : Nat.Primes) :
    coordinate ((A : ℝ)*log p.val)=(key A p : ℝ) := by
  have pp : 0<(p.val : ℝ) := Nat.cast_pos.mpr p.property.pos
  simp only [coordinate,exp_neg,exp_nat_mul,exp_log pp,key,Rat.cast_add,Rat.cast_inv,
    Rat.cast_pow,Rat.cast_natCast]

/-- At any prescribed positive rational damping, precisely the prescribed
primes can fail, using the minimum possible number of distinct occupations. -/
theorem prescribed_prime_set (S : Finset Nat.Primes) {q : ℚ} (hq : 0<q) :
    ∃ (n : ℕ) (k : Fin n → ℕ), levelCount k=S.card+2 ∧ ¬Reflects (levels k) ∧
      ∀ p : Nat.Primes, accepts k p q ↔ p ∈ S := by
  classical
  let A := q.num.toNat
  let B := q.den
  have ha : 0<A := by have h := Rat.num_pos.mpr hq; dsimp only [A]; omega
  have bpos : 0<B := q.den_pos
  have bp : 0<(B : ℝ) := Nat.cast_pos.mpr bpos
  have qa : (q : ℝ)*B=A := by
    have num : (A : ℝ)=(q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr hq).le
    rw [num,Rat.cast_def,div_mul_cancel₀ _ bp.ne']
  obtain ⟨above,inj⟩ := key_props ha
  let T := S.image (key A)
  have good (r : ℚ) (hr : r ∈ T) : 2<r := by
    obtain ⟨p,_,rfl⟩ := mem_image.mp hr
    exact above p
  let ref : Nat.Primes := ⟨2,Nat.prime_two⟩
  obtain ⟨n,a,count,asym,law⟩ := Optimal.optimal_prime_schedule ref T good
  let k (i : Fin n) := B*a i
  have scaled : levels k=fun i => (B : ℝ)*levels a i+0 := by
    funext i; simp only [levels,k,Nat.cast_mul,add_zero]
  have ain : levelCount a=T.card+2 := by rwa [← physical_level_count ref]
  have kin : levelCount k=levelCount a := by
    have eq : univ.image k=(univ.image a).image (fun i => B*i) := by rw [image_image]; rfl
    rw [levelCount,levelCount,eq,card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left bpos h)]
  have refl : Reflects (levels k) ↔ Reflects (primeModes ref a) := by
    rw [scaled,affine_reflects _ _ _ bp.ne',Sparse.mode_grid,affine_reflects _ _ _ (log_pos_prime ref).ne']
  refine ⟨n,k,kin.trans (ain.trans (by dsimp only [T]; rw [card_image_of_injective _ inj])),fun h => asym (refl.mp h),?_⟩
  intro p
  let v := (A : ℝ)*log p.val
  have vp : 0<v := mul_pos (Nat.cast_pos.mpr ha) (log_pos_prime p)
  have cancel : v/log ref.val*log ref.val=v := div_mul_cancel₀ _ (log_pos_prime ref).ne'
  have test := law (v/log ref.val) (div_pos vp (log_pos_prime ref))
  rw [Sparse.mode_grid,agrees_affine,cancel] at test
  rw [accepts_iff,abs_of_pos (Rat.cast_pos.mpr hq),scaled,agrees_affine,
    show (q : ℝ)*log p.val*B=v by rw [mul_right_comm,qa],test,measured]
  constructor
  · rintro ⟨r,hr,e⟩
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hr
    exact (inj (Rat.cast_injective e)) ▸ hs
  · intro hp
    exact ⟨key A p,mem_image_of_mem _ hp,rfl⟩

#print axioms prescribed_prime_set

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration
