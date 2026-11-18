import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.DyadicUnitEquationHeights

/-!
# Effective uniqueness for large odd dyadic targets

For distinct positive odd coefficients A and B, a sufficiently large odd
target has at most one signed dyadic representation. Beyond an explicit
threshold one summand is divisible by a large power of two; the remaining
summand is one of ±A, ±B. Their residues distinguish both the coefficient
and its sign. This proves the one-prime case of the normalized large-height
conclusion by parity and congruence alone.
-/

noncomputable section
namespace GaloisForLFunctions.KodairaParshinAbc
open GaloisForLFunctions.RHTower
local notation "U" => fieldOneSUnitSubgroup dyadicUnitPlaces

private theorem nat_odd_nonzero {n : ℕ} (h : Odd n) : n ≠ 0 := by
  obtain ⟨m,hm⟩ := h
  omega

/-- Odd integers have dyadic order zero. -/
theorem dyadicOdd_integer_valuation (c : ℤ) (h : Odd c) : padicValRat 2 (c:ℚ) = 0 := by
  have hnd : ¬ (2:ℤ) ∣ c := by
    obtain ⟨m,hm⟩ := h
    rintro ⟨n,hn⟩
    omega
  simp only [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnd, Nat.cast_zero]

/-- A dyadic rescaling between two odd integers changes only the sign. -/
theorem odd_dyadic_ratio (b c : ℤ) (hb : Odd b) (hc : Odd c) (u : U)
    (he : (b:ℚ) * (u.val:ℚ) = (c:ℚ)) : (u.val:ℚ) = 1 ∨ (u.val:ℚ) = -1 := by
  have hbq : (b:ℚ) ≠ 0 := Int.cast_ne_zero.mpr (by obtain ⟨m,hm⟩ := hb; omega)
  have hv := congrArg (padicValRat 2) he
  rw [padicValRat.mul hbq u.val.ne_zero, dyadicOdd_integer_valuation _ hb, dyadicOdd_integer_valuation _ hc, zero_add] at hv
  have ha := dyadicUnit_abs_val u
  rw [hv,zpow_zero] at ha
  rcases le_or_gt 0 (u.val:ℚ) with h | h
  · exact Or.inl ((abs_of_nonneg h).symm.trans ha)
  · right
    rw [abs_of_neg h] at ha
    exact neg_eq_iff_eq_neg.mp ha

private theorem dyadic_multiple_of_large (u : U) (k : ℕ) (hl : (2:ℚ)^k < |(u.val:ℚ)|) :
    ∃ z : ℤ, (2:ℤ)^k ∣ z ∧ (2:ℤ) ∣ z ∧ (u.val:ℚ) = z := by
  have hm : |(u.val:ℚ)| ∈ Set.range (fun e : ℤ => (2:ℚ)^e) := dyadicUnit_abs_range ▸ ⟨u,rfl⟩
  obtain ⟨e,he⟩ := hm
  change (2:ℚ)^e = |(u.val:ℚ)| at he
  cases e with
  | ofNat n =>
    change (2:ℚ)^n = |(u.val:ℚ)| at he
    have hkn : k < n := by
      by_contra! h
      exact hl.not_ge (he ▸ pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) h)
    have ht : (2:ℤ)^k ∣ (2:ℤ)^n := pow_dvd_pow 2 hkn.le
    have htwo : (2:ℤ) ∣ (2:ℤ)^n := dvd_pow_self _ (by omega)
    rcases le_or_gt 0 (u.val:ℚ) with h | h
    · refine ⟨2^n,ht,htwo,?_⟩
      simpa only [Int.cast_pow, Int.cast_ofNat, abs_of_nonneg h] using he.symm
    · refine ⟨-(2^n),dvd_neg.mpr ht,dvd_neg.mpr htwo,?_⟩
      rw [abs_of_neg h] at he
      simpa only [Int.cast_neg,Int.cast_pow,Int.cast_ofNat,neg_neg] using congrArg Neg.neg he.symm
  | negSucc n =>
    rw [← he,zpow_negSucc] at hl
    have h1 : (1:ℚ) ≤ 2^k := one_le_pow₀ (by norm_num)
    have h2 : (1:ℚ) ≤ 2^(n+1) := one_le_pow₀ (by norm_num)
    exact (not_lt_of_ge ((inv_le_one_of_one_le₀ h2).trans h1) hl).elim

/-- The small signed summand of a solution together with its residue constraint. -/
def dyadicSignedAnchor (m C k : ℕ) (u : U) : Prop :=
  ∃ e : ℤ, (e=1 ∨ e= -1) ∧ (u.val:ℚ) = e ∧ (2:ℤ)^k ∣ (C:ℤ) - m*e

private theorem anchor_from_large (a b C k : ℕ) (hb : Odd b) (hc : Odd C) (x y : U)
    (he : (a:ℚ)*(x.val:ℚ) + b*(y.val:ℚ) = C) (hx : (2:ℚ)^k < |(x.val:ℚ)|) :
    dyadicSignedAnchor b C k y := by
  obtain ⟨z,hzk,hz2,hxz⟩ := dyadic_multiple_of_large x k hx
  let c : ℤ := C - a*z
  have hodd : Odd c := by
    obtain ⟨m,hm⟩ := hc
    obtain ⟨n,hn⟩ := hz2
    refine ⟨(m:ℤ)-a*n,?_⟩
    dsimp [c]
    rw [hm,hn]
    push_cast
    ring
  have hby : (↑(b:ℤ):ℚ)*(y.val:ℚ) = c := by
    dsimp [c]
    push_cast
    rw [hxz] at he
    linear_combination he
  have hbz : Odd (b:ℤ) := by exact_mod_cast hb
  have hd (e : ℤ) (hey : (y.val:ℚ) = e) : (2:ℤ)^k ∣ (C:ℤ) - b*e := by
    rw [hxz,hey] at he
    have hr : (C:ℚ) - (b:ℚ)*(e:ℚ) = (a:ℚ)*(z:ℚ) := by linear_combination -he
    have hr' : (C:ℤ) - b*e = a*z := by exact_mod_cast hr
    rw [hr']
    exact dvd_mul_of_dvd_right hzk _
  obtain h | h := odd_dyadic_ratio _ _ hbz hodd y hby
  · have hey : (y.val:ℚ) = ((1:ℤ):ℚ) := by simpa only [Int.cast_one] using h
    exact ⟨1,Or.inl rfl,hey,hd 1 hey⟩
  · have hey : (y.val:ℚ) = ((-1:ℤ):ℚ) := by simpa only [Int.cast_neg,Int.cast_one] using h
    exact ⟨-1,Or.inr rfl,hey,hd (-1) hey⟩

/-- Beyond the stated bound a solution has a signed unit anchor determined modulo 2^k. -/
theorem dyadicLargeTarget_residues (A B C k : ℕ) (hA : Odd A) (hB : Odd B) (hC : Odd C)
    (hlarge : (A+B)*2^k < C) (z : RationalUnitSolutions dyadicUnitPlaces A B C) :
    dyadicSignedAnchor A C k z.val.1 ∨ dyadicSignedAnchor B C k z.val.2 := by
  have he := z.property
  by_cases hx : (2:ℚ)^k < |(z.val.1.val:ℚ)|
  · exact Or.inr (anchor_from_large A B C k hB hC _ _ he hx)
  · have hy : (2:ℚ)^k < |(z.val.2.val:ℚ)| := by
      by_contra! hy
      have htri := abs_add_le ((A:ℚ)*(z.val.1.val:ℚ)) ((B:ℚ)*(z.val.2.val:ℚ))
      rw [he] at htri
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) C),
        abs_of_nonneg (Nat.cast_nonneg (α := ℚ) A), abs_of_nonneg (Nat.cast_nonneg (α := ℚ) B)] at htri
      have hle := add_le_add (mul_le_mul_of_nonneg_left (le_of_not_gt hx) (Nat.cast_nonneg (α := ℚ) A))
        (mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg (α := ℚ) B))
      rw [← add_mul] at hle
      exact (not_le_of_gt (by exact_mod_cast hlarge : ((A:ℚ)+B)*2^k < C)) (htri.trans hle)
    exact Or.inl (anchor_from_large B A C k hA hC _ _ ((add_comm _ _).trans he) hy)

private theorem anchor_eq {A B C k : ℕ} {x y : U} (M : ℕ) (hA : A ≤ M) (hB : B ≤ M)
    (hsep : 2*M < 2^k) (hx : dyadicSignedAnchor A C k x) (hy : dyadicSignedAnchor B C k y) :
    A = B ∧ (x.val:ℚ) = (y.val:ℚ) ∨ A=0 ∧ B=0 := by
  obtain ⟨i,hi,hxi,hdi⟩ := hx
  obtain ⟨j,hj,hyj,hdj⟩ := hy
  have hd : (2:ℤ)^k ∣ (A:ℤ)*i-B*j := by
    have hr := dvd_sub hdj hdi
    rwa [show (C:ℤ)-B*j-((C:ℤ)-A*i) = (A:ℤ)*i-B*j by ring] at hr
  have hZ : (A:ℤ)*i = B*j := by
    have hs : (2:ℤ)*M < 2^k := by exact_mod_cast hsep
    have ha : (A:ℤ) ≤ M := by exact_mod_cast hA
    have hb : (B:ℤ) ≤ M := by exact_mod_cast hB
    have ha₀ : 0 ≤ (A:ℤ) := Int.natCast_nonneg _
    have hb₀ : 0 ≤ (B:ℤ) := Int.natCast_nonneg _
    rcases lt_trichotomy ((A:ℤ)*i) (B*j) with h | h | h
    · have hd' : (2:ℤ)^k ∣ B*j-(A:ℤ)*i := by rwa [← neg_sub, dvd_neg]
      have hlt := Int.le_of_dvd (sub_pos.mpr h) hd'
      rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> simp only [mul_one,mul_neg_one] at hlt <;> omega
    · exact h
    · have hlt := Int.le_of_dvd (sub_pos.mpr h) hd
      rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> simp only [mul_one,mul_neg_one] at hlt <;> omega
  rcases hi with rfl|rfl <;> rcases hj with rfl|rfl
  · simp only [mul_one] at hZ
    exact Or.inl ⟨by exact_mod_cast hZ,hxi.trans hyj.symm⟩
  · simp only [mul_one,mul_neg_one] at hZ
    right; omega
  · simp only [mul_one,mul_neg_one] at hZ
    right; omega
  · simp only [mul_neg_one,neg_inj] at hZ
    exact Or.inl ⟨by exact_mod_cast hZ,hxi.trans hyj.symm⟩

/-- For distinct fixed odd coefficients, the large odd target determines at most one solution. -/
theorem dyadicLargeTarget_unique (A B C k : ℕ) (hA : Odd A) (hB : Odd B) (hC : Odd C)
    (hne : A ≠ B) (hsep : 2*max A B < 2^k) (hlarge : (A+B)*2^k < C) :
    Subsingleton (RationalUnitSolutions dyadicUnitPlaces A B C) := by
  constructor
  intro v w
  have hdec := dyadicLargeTarget_residues A B C k hA hB hC hlarge
  have ha : (A:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (nat_odd_nonzero hA)
  have hb : (B:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (nat_odd_nonzero hB)
  have hval (h : (v.val.1.val:ℚ)=(w.val.1.val:ℚ) ∨ (v.val.2.val:ℚ)=(w.val.2.val:ℚ)) :
      v=w := by
    have he := v.property.trans w.property.symm
    have hpair : (v.val.1.val:ℚ)=(w.val.1.val:ℚ) ∧ (v.val.2.val:ℚ)=(w.val.2.val:ℚ) := by
      rcases h with h | h
      · rw [h] at he
        exact ⟨h,mul_left_cancel₀ hb (add_left_cancel he)⟩
      · rw [h] at he
        exact ⟨mul_left_cancel₀ ha (add_right_cancel he),h⟩
    exact Subtype.ext (Prod.ext (Subtype.ext (Units.ext hpair.1)) (Subtype.ext (Units.ext hpair.2)))
  rcases hdec v with vx|vy <;> rcases hdec w with wx|wy
  · rcases anchor_eq (max A B) (le_max_left _ _) (le_max_left _ _) hsep vx wx with h|h
    · exact hval (Or.inl h.2)
    · exact ((nat_odd_nonzero hA) h.1).elim
  · rcases anchor_eq (max A B) (le_max_left _ _) (le_max_right _ _) hsep vx wy with h|h
    · exact (hne h.1).elim
    · exact ((nat_odd_nonzero hA) h.1).elim
  · rcases anchor_eq (max A B) (le_max_left _ _) (le_max_right _ _) hsep wx vy with h|h
    · exact (hne h.1).elim
    · exact ((nat_odd_nonzero hA) h.1).elim
  · rcases anchor_eq (max A B) (le_max_right _ _) (le_max_right _ _) hsep vy wy with h|h
    · exact hval (Or.inr h.2)
    · exact ((nat_odd_nonzero hB) h.1).elim

/-- The elementary bound 4 max(A,B)(A+B) suffices for uniqueness on every normalized odd target. -/
theorem dyadicOddTarget_unique_above (A B C : ℕ) (hA : Odd A) (hB : Odd B) (hC : Odd C)
    (hne : A ≠ B) (hlarge : 4*max A B*(A+B) < C) :
    Subsingleton (RationalUnitSolutions dyadicUnitPlaces A B C) := by
  let M := max A B
  let k := Nat.log 2 (2*M) + 1
  have hM : 0 < M := (Nat.pos_of_ne_zero (nat_odd_nonzero hA)).trans_le (le_max_left A B)
  have hsep : 2*M < 2^k := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have hbase := Nat.pow_log_le_self 2 (mul_ne_zero (by norm_num : (2:ℕ) ≠ 0) hM.ne')
  have hpow : 2^k ≤ 4*M := by
    dsimp only [k]
    rw [pow_succ]
    omega
  apply dyadicLargeTarget_unique A B C k hA hB hC hne hsep
  exact (Nat.mul_le_mul_left (A+B) hpow).trans_lt ((Nat.mul_comm (A+B) (4*M)) ▸ hlarge)

/-- The single-solution bound is attained at arbitrarily large logarithmic height. -/
theorem dyadicOddTarget_unique_unbounded (T : ℝ) :
    ∃ C : ℕ, Odd C ∧ T < Height.logHeight₁ (C:ℚ) ∧
      Nonempty (RationalUnitSolutions dyadicUnitPlaces 3 5 C) ∧
      Subsingleton (RationalUnitSolutions dyadicUnitPlaces 3 5 C) := by
  let b : ℕ := 4*max 3 5*(3+5)
  obtain ⟨C,hC,hT,he⟩ := dyadic_odd_solvable_targets (max T (Real.log (b:ℝ)))
  letI : NeZero C := ⟨(nat_odd_nonzero hC)⟩
  have hlt := (le_max_right T (Real.log (b:ℝ))).trans_lt hT
  rw [Rat.logHeight₁_natCast] at hlt
  have hb : 0 < (b:ℝ) := by change 0 < (↑(4*max 3 5*(3+5):ℕ):ℝ); positivity
  have hc : 0 < (C:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (nat_odd_nonzero hC)
  have h : b < C := by exact_mod_cast (Real.log_lt_log_iff hb hc).1 hlt
  refine ⟨C,hC,(le_max_left _ _).trans_lt hT,he,?_⟩
  exact dyadicOddTarget_unique_above 3 5 C ⟨1,by omega⟩ ⟨2,by omega⟩ hC (by omega) h

/-- Each of the two signs gives a shifted geometric progression of targets. -/
def dyadicTargetRay (A B C : ℕ) : Prop :=
  ∃ k : ℕ, C = A*2^(k+1)+B ∨ C+B = A*2^(k+1)

/-- A positive dyadic unit strictly above one has a positive integral exponent. -/
theorem dyadicUnit_positive_power_of_one_lt (u : U) (hu : 1 < (u.val:ℚ)) :
    ∃ k : ℕ, (u.val:ℚ) = 2^(k+1) := by
  have hm : |(u.val:ℚ)| ∈ Set.range (fun e : ℤ => (2:ℚ)^e) := dyadicUnit_abs_range ▸ ⟨u,rfl⟩
  obtain ⟨e,he⟩ := hm
  change (2:ℚ)^e = |(u.val:ℚ)| at he
  rw [abs_of_pos (zero_lt_one.trans hu)] at he
  cases e with
  | ofNat n =>
    change (2:ℚ)^n = (u.val:ℚ) at he
    cases n with
    | zero => rw [pow_zero] at he; exact (hu.ne he).elim
    | succ k => exact ⟨k,he.symm⟩
  | negSucc k =>
    rw [← he,zpow_negSucc] at hu
    exact (hu.not_ge (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℚ)≤2)))).elim

private theorem ray_of_anchor (A B C : ℕ) (hl : A+B<C) (x y : U)
    (he : (A:ℚ)*(x.val:ℚ)+B*(y.val:ℚ)=C) (hy : (y.val:ℚ)=1 ∨ (y.val:ℚ)= -1) :
    ∃ k : ℕ, (x.val:ℚ) = 2^(k+1) ∧ (C=A*2^(k+1)+B ∨ C+B=A*2^(k+1)) := by
  have hlarge : (A:ℚ)+B<C := by exact_mod_cast hl
  have hx : 1 < (x.val:ℚ) := by
    by_contra! h
    have hle := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℚ) A)
    rcases hy with h|h <;> rw [h] at he <;> linarith [Nat.cast_nonneg (α := ℚ) B]
  obtain ⟨k,hk⟩ := dyadicUnit_positive_power_of_one_lt x hx
  refine ⟨k,hk,?_⟩
  rw [hk] at he
  rcases hy with h|h
  · rw [h,mul_one] at he
    exact Or.inl (by exact_mod_cast he.symm)
  · rw [h,mul_neg_one] at he
    exact Or.inr (by exact_mod_cast (show (C:ℚ)+B=(A:ℚ)*2^(k+1) by linarith only [he]))

private def negativeUnit : U := ⟨-1,fieldOne_negOne_mem_sUnitSubgroup _⟩

/-- Each nonnegative integral power of two is represented by a positive dyadic unit. -/
theorem dyadicUnit_positive_power_exists (n : ℕ) : ∃ u : U, (u.val:ℚ)=2^n := by
  have hm : (2:ℚ)^n ∈ Set.range (fun e : ℤ => (2:ℚ)^e) := ⟨n,zpow_natCast _ _⟩
  rw [← dyadicUnit_abs_range] at hm
  obtain ⟨u,hu⟩ := hm
  change |(u.val:ℚ)| = 2^n at hu
  rcases le_or_gt 0 (u.val:ℚ) with h|h
  · exact ⟨u,(abs_of_nonneg h).symm.trans hu⟩
  · refine ⟨negativeUnit*u,?_⟩
    change (-1:ℚ)*(u.val:ℚ)=_
    rw [neg_one_mul,← abs_of_neg h,hu]

private theorem ray_solution (A B C : ℕ) (h : dyadicTargetRay A B C) :
    Nonempty (RationalUnitSolutions dyadicUnitPlaces A B C) := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨u,hu⟩ := dyadicUnit_positive_power_exists (k+1)
  rcases hk with h|h
  · refine ⟨⟨(u,1),?_⟩⟩
    change (A:ℚ)*(u.val:ℚ)+B*1=C
    rw [hu,mul_one]; exact_mod_cast h.symm
  · refine ⟨⟨(u,negativeUnit),?_⟩⟩
    change (A:ℚ)*(u.val:ℚ)+B*(-1)=C
    rw [hu,mul_neg_one]
    have he : (C:ℚ)+B=(A:ℚ)*2^(k+1) := by exact_mod_cast h
    linarith only [he]

/-- The complete large odd target spectrum is the union of four explicit shifted powers of two. -/
theorem dyadicOddTarget_spectrum (A B C : ℕ) (hA : Odd A) (hB : Odd B) (hC : Odd C)
    (hl : A+B<C) : Nonempty (RationalUnitSolutions dyadicUnitPlaces A B C) ↔
      dyadicTargetRay A B C ∨ dyadicTargetRay B A C := by
  constructor
  · rintro ⟨z⟩
    have h := dyadicLargeTarget_residues A B C 0 hA hB hC (by simpa only [pow_zero,mul_one] using hl) z
    have hs {m : ℕ} {u : U} (hu : dyadicSignedAnchor m C 0 u) :
        (u.val:ℚ)=1 ∨ (u.val:ℚ)= -1 := by
      obtain ⟨e,he,hu,_⟩ := hu
      rcases he with rfl|rfl
      · exact Or.inl (by simpa using hu)
      · exact Or.inr (by simpa using hu)
    rcases h with h|h
    · obtain ⟨k,_,hk⟩ := ray_of_anchor B A C (by rwa [add_comm]) _ _
        ((add_comm _ _).trans z.property) (hs h)
      exact Or.inr ⟨k,hk⟩
    · obtain ⟨k,_,hk⟩ := ray_of_anchor A B C hl _ _ z.property (hs h)
      exact Or.inl ⟨k,hk⟩
  · rintro (h|h)
    · exact ray_solution A B C h
    · obtain ⟨z⟩ := ray_solution B A C h
      exact ⟨⟨(z.val.2,z.val.1),(add_comm _ _).trans z.property⟩⟩

/-- The two representations of 31 with coefficients 7 and 3 exhaust its signed dyadic fiber. -/
theorem dyadicTarget31_classification (z : RationalUnitSolutions dyadicUnitPlaces 7 3 31) :
    ((z.val.1.val:ℚ) = 4 ∧ (z.val.2.val:ℚ) = 1) ∨
    ((z.val.1.val:ℚ) = 1 ∧ (z.val.2.val:ℚ) = 8) := by
  have hz := z.property
  have h := dyadicLargeTarget_residues 7 3 31 0 ⟨3,rfl⟩ ⟨1,rfl⟩ ⟨15,rfl⟩ (by norm_num) z
  have hs {m : ℕ} {u : U} (hu : dyadicSignedAnchor m 31 0 u) :
      (u.val:ℚ)=1 ∨ (u.val:ℚ)= -1 := by
    obtain ⟨e,he,hu,_⟩ := hu
    rcases he with rfl|rfl <;> simp_all
  rcases h with h|h
  · obtain ⟨k,hk,hr⟩ := ray_of_anchor 3 7 31 (by norm_num) _ _ ((add_comm _ _).trans hz) (hs h)
    have hn : (2:ℕ)^(k+1)=8 := by omega
    have hy : (z.val.2.val:ℚ)=8 := hk.trans (by exact_mod_cast hn)
    exact Or.inr ⟨by rw [hy] at hz; linarith only [hz],hy⟩
  · obtain ⟨k,hk,hr⟩ := ray_of_anchor 7 3 31 (by norm_num) _ _ hz (hs h)
    have hn : (2:ℕ)^(k+1)=4 := by omega
    have hx : (z.val.1.val:ℚ)=4 := hk.trans (by exact_mod_cast hn)
    exact Or.inl ⟨hx,by rw [hx] at hz; linarith only [hz]⟩

/-- Every signed dyadic rescaling of 31 has exactly two solutions, including arbitrarily
small and arbitrarily large rescalings. -/
theorem dyadicTarget31_scaled_card (w : U) :
    Nat.card (RationalUnitSolutions dyadicUnitPlaces 7 3 (31*(w.val:ℚ))) = 2 := by
  classical
  let Z := RationalUnitSolutions dyadicUnitPlaces 7 3 31
  let e : Z ≃ RationalUnitSolutions dyadicUnitPlaces 7 3 (31*(w.val:ℚ)) := by
    simpa using rationalUnitSolutionsRescale dyadicUnitPlaces 7 3 31 1 1 w
  let code : Z → Bool := fun z => decide ((z.val.1.val:ℚ) = 4)
  have hi : Function.Injective code := by
    intro x y he
    change decide ((x.val.1.val:ℚ) = 4) = decide ((y.val.1.val:ℚ) = 4) at he
    rcases dyadicTarget31_classification x with ⟨hx,hx'⟩|⟨hx,hx'⟩ <;>
      rcases dyadicTarget31_classification y with ⟨hy,hy'⟩|⟨hy,hy'⟩ <;>
      simp only [hx,hy] at he
    all_goals norm_num at he
    all_goals
      apply Subtype.ext
      exact Prod.ext (Subtype.ext (Units.ext (hx.trans hy.symm))) (Subtype.ext (Units.ext (hx'.trans hy'.symm)))
  have h₀ : (31:ℚ)*2^(0:ℕ)=31 := by rw [pow_zero,mul_one]
  obtain ⟨x,y,hxy⟩ : ∃ x y : Z, x ≠ y :=
    (congrArg (fun c : ℚ => ∃ x y : RationalUnitSolutions dyadicUnitPlaces 7 3 c, x ≠ y) h₀).mp
      (dyadic_two_solutions 0)
  have hsur : Function.Surjective code := by
    have hd := hi.ne hxy
    intro b
    cases b <;> cases hx : code x <;> cases hy : code y <;> first
      | exact ⟨x,hx⟩
      | exact ⟨y,hy⟩
      | exact (hd (hx.trans hy.symm)).elim
  rw [← Nat.card_congr e, Nat.card_congr (Equiv.ofBijective code ⟨hi,hsur⟩)]
  simp

#print axioms dyadicOdd_integer_valuation
#print axioms dyadicUnit_positive_power_of_one_lt
#print axioms dyadicUnit_positive_power_exists
#print axioms dyadicTarget31_classification
#print axioms dyadicTarget31_scaled_card
#print axioms dyadicOddTarget_spectrum
#print axioms dyadicOddTarget_unique_above
#print axioms dyadicOddTarget_unique_unbounded
#print axioms odd_dyadic_ratio
#print axioms dyadicLargeTarget_residues
#print axioms dyadicLargeTarget_unique

end GaloisForLFunctions.KodairaParshinAbc
