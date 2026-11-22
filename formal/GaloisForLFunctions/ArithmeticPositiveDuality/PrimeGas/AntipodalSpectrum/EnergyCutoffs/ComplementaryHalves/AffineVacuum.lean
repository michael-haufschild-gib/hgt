import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.SpectralRigidity

/-!
# Which oscillator vacuum can be tiled by two balanced coordinates?

All positive integers outside the multiples of an oscillator base must occur
once at zero occupation. The first missing digit and a two-digit obstruction
force the base to be two, even when both coordinate slopes can vary.
-/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

def vacuumLabel {C : Radix} (a d : ℕ) (p : Half C × Half C) := 1+a*p.1.val+d*p.2.val

/-- Every positive label indivisible by the oscillator base occurs once at zero occupation. -/
def SimpleVacuum (C : Radix) (b a d : ℕ) : Prop :=
  Function.Injective (vacuumLabel (C := C) a d) ∧
    ∀ n : ℕ, (∃ p : Half C × Half C, vacuumLabel a d p = n) ↔ 0 < n ∧ ¬ b ∣ n

private def unitDigit (C : Radix) := single C ⟨1,C.property⟩

private theorem unit_val (C : Radix) : (unitDigit C).val = 1 := single_val C _

private theorem vacuum_swap (C : Radix) (b a d : ℕ) :
    SimpleVacuum C b a d → SimpleVacuum C b d a := by
  rintro ⟨hi,hs⟩
  have he (p : Half C × Half C) : vacuumLabel d a p = vacuumLabel a d p.swap := by
    change 1+d*p.1.val+a*p.2.val = 1+a*p.2.val+d*p.1.val
    omega
  refine ⟨fun u v h => Prod.swap_injective (hi ((he u).symm.trans (h.trans (he v)))),fun n => ?_⟩
  rw [← hs]
  constructor <;> rintro ⟨p,hp⟩
  · exact ⟨p.swap,(he p).symm.trans hp⟩
  · exact ⟨p.swap,(he p.swap).trans hp⟩

private theorem vacuum_slope_pos {C : Radix} {b a d : ℕ} (h : SimpleVacuum C b a d) : 0 < a := by
  by_contra! ha
  have hzero : a = 0 := by omega
  have he : vacuumLabel a d (unitDigit C,origin C) = vacuumLabel a d (origin C,origin C) := by
    simp only [vacuumLabel,hzero,zero_mul]
  have hx : (unitDigit C).val = 0 := congrArg (fun p : Half C × Half C => p.1.val) (h.1 he)
  rw [unit_val] at hx
  omega

private theorem least_increment {C : Radix} {a d : ℕ} (had : a ≤ d) (p : Half C × Half C)
    (h : 1 < vacuumLabel a d p) : 1+a ≤ vacuumLabel a d p := by
  change 1 < 1+a*p.1.val+d*p.2.val at h
  change 1+a ≤ 1+a*p.1.val+d*p.2.val
  rcases Nat.eq_zero_or_pos p.1.val with hx|hx
  · rw [hx,mul_zero,add_zero] at h ⊢
    have hy : 0 < p.2.val := by
      by_contra! hy
      have h₀ : p.2.val = 0 := by omega
      rw [h₀,mul_zero] at h
      omega
    have hd := Nat.le_mul_of_pos_right d hy
    omega
  · have ha := Nat.le_mul_of_pos_right a hx
    omega

/-- Digits (C−1,1) produce a forbidden multiple when the first omitted level is C+1. -/
private theorem two_digit_multiple (C : Radix) :
    ∃ x : Half C, 1+x.val = (C.val+1)*C.val := by
  let d := C.val-1
  have hc := C.property
  have hd : d < C.val := by dsimp [d]; omega
  have hB : 1 < C.val^2 := one_lt_pow₀ hc (by norm_num)
  have hdB := hd.trans_le (show C.val ≤ C.val^2 by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (zero_lt_one.trans hc))
  let n := d+C.val^2*1
  have hn : 0 < n := by dsimp [n]; omega
  have hmem : ∀ i ∈ (C.val^2).digits n, i < C.val := by
    rw [Nat.digits_def' hB hn]
    change ∀ i ∈ (d+C.val^2*1)%(C.val^2) :: (C.val^2).digits ((d+C.val^2*1)/(C.val^2)), i < C.val
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hdB,Nat.add_mul_div_left _ _ (zero_lt_one.trans hB),
      Nat.div_eq_of_lt hdB,zero_add,List.forall_mem_cons]
    have h₁ := (single C ⟨1,hc⟩).property
    rw [single_val] at h₁
    exact ⟨hd,h₁⟩
  refine ⟨⟨n,hmem⟩,?_⟩
  change 1+(d+C.val^2*1) = (C.val+1)*C.val
  have hd' : d+1 = C.val := by dsimp [d]; omega
  calc
    _ = C.val^2+(d+1) := by ring
    _ = _ := by rw [hd']; ring

private theorem unit_slope_impossible {C : Radix} {b d : ℕ} (hb : 1 < b)
    (h : SimpleVacuum C b 1 d) : False := by
  have forbidden (x : Half C × Half C) : ¬b ∣ vacuumLabel 1 d x := ((h.2 _).mp ⟨x,rfl⟩).2
  have low (k : ℕ) (hk : k < C.val) : vacuumLabel 1 d (single C ⟨k,hk⟩,origin C) = 1+k := by
    simp only [vacuumLabel,single_val,origin,one_mul,mul_zero,add_zero]
  rcases lt_trichotomy d C.val with hd|hd|hd
  · have he : vacuumLabel 1 d (single C ⟨d,hd⟩,origin C) = vacuumLabel 1 d (origin C,unitDigit C) := by
      rw [low]; simp only [vacuumLabel,origin,unit_val,mul_zero,add_zero,mul_one]
    have hz : 0 = (unitDigit C).val := congrArg (fun p : Half C × Half C => p.2.val) (h.1 he)
    rw [unit_val] at hz
    omega
  · subst d
    let p := (interleave C).symm (b-1)
    have hp : p.1.val+C.val*p.2.val = b-1 := (interleave C).apply_symm_apply _
    have he : vacuumLabel 1 C.val p = b := by unfold vacuumLabel; rw [one_mul]; omega
    exact forbidden p (by rw [he])
  · have missing : ¬∃ p : Half C × Half C, vacuumLabel 1 d p = C.val+1 := by
      rintro ⟨p,hp⟩
      change 1+1*p.1.val+d*p.2.val = C.val+1 at hp
      rw [one_mul] at hp
      rcases Nat.eq_zero_or_pos p.2.val with hz|hy
      · rw [hz,mul_zero,add_zero] at hp
        exact excludes_radix C p.1 (by omega)
      · have H := Nat.le_mul_of_pos_right d hy
        omega
    have hdvd : b ∣ C.val+1 := by
      by_contra hn
      exact missing ((h.2 _).mpr ⟨Nat.succ_pos _,hn⟩)
    have hle := Nat.le_of_dvd (Nat.succ_pos _) hdvd
    have hbase : b = C.val+1 := by
      by_contra hne
      have hk : b-1 < C.val := by omega
      have he := low (b-1) hk
      have H := forbidden (single C ⟨b-1,hk⟩,origin C)
      rw [he,show 1+(b-1) = b by omega] at H
      exact H dvd_rfl
    obtain ⟨x,hx⟩ := two_digit_multiple C
    have H := forbidden (x,origin C)
    change ¬ b ∣ 1+1*x.val+d*0 at H
    rw [one_mul,mul_zero,add_zero,hx,hbase] at H
    exact H ⟨C.val,rfl⟩

private theorem ordered_vacuum {C : Radix} {b a d : ℕ} (hb : 1 < b) (had : a ≤ d)
    (h : SimpleVacuum C b a d) : b = 2 ∧ a = 2 ∧ d = 2*C.val := by
  have ha := vacuum_slope_pos h
  have hbase : b = 2 := by
    by_contra hne
    obtain ⟨p,hp⟩ := (h.2 2).mpr ⟨by omega,fun hd => by have H := Nat.le_of_dvd (by decide : 0 < 2) hd; omega⟩
    have hmin := least_increment had p (by rw [hp]; omega)
    rw [hp] at hmin
    obtain rfl : a = 1 := by omega
    exact unit_slope_impossible hb h
  subst b
  have hodd (p : Half C × Half C) : ¬2 ∣ vacuumLabel a d p := ((h.2 _).mp ⟨p,rfl⟩).2
  have hae := hodd (unitDigit C,origin C)
  have hde := hodd (origin C,unitDigit C)
  simp only [vacuumLabel,unit_val,origin,mul_one,mul_zero,add_zero] at hae hde
  obtain ⟨p,hp⟩ := (h.2 3).mpr ⟨by omega,by omega⟩
  have hmin := least_increment had p (by rw [hp]; omega)
  rw [hp] at hmin
  obtain rfl : a = 2 := by omega
  let q := d/2
  have hd : d = 2*q := by dsimp [q]; omega
  have he (p : Half C × Half C) : vacuumLabel 2 d p = 1+2*scaled C q p := by
    rw [hd,vacuumLabel,scaled]
    ring
  have hi : Function.Injective (scaled C q) := fun u v huv => h.1 (by rw [he,he,huv])
  have hs : Function.Surjective (scaled C q) := by
    intro n
    obtain ⟨u,hu⟩ := (h.2 (1+2*n)).mpr ⟨by omega,by omega⟩
    rw [he] at hu
    exact ⟨u,by omega⟩
  exact ⟨rfl,rfl,hd.trans (congrArg (2*·) ((integral_scale_iff C q).mp ⟨hi,hs⟩))⟩

private theorem canonical_vacuum (C : Radix) : SimpleVacuum C 2 2 (2*C.val) := by
  have he (p : Half C × Half C) : vacuumLabel 2 (2*C.val) p = 1+2*interleave C p := by
    rw [vacuumLabel,interleave_apply]; ring
  constructor
  · intro p r h
    rw [he,he] at h
    exact (interleave C).injective (by omega)
  · intro n
    constructor
    · rintro ⟨p,rfl⟩
      rw [he]; omega
    · rintro ⟨hn,hd⟩
      refine ⟨(interleave C).symm (n/2),?_⟩
      rw [he,Equiv.apply_symm_apply]; omega

/-- The oscillator vacuum determines base two and both balanced slopes up to exchange. -/
theorem vacuum_spectrum_iff (C b : Radix) (a d : ℕ) :
    SimpleVacuum C b.val a d ↔ b.val = 2 ∧
      ((a = 2 ∧ d = 2*C.val) ∨ (d = 2 ∧ a = 2*C.val)) := by
  constructor
  · intro h
    rcases le_total a d with had|hda
    · obtain ⟨hb,ha,hd⟩ := ordered_vacuum b.property had h
      exact ⟨hb,Or.inl ⟨ha,hd⟩⟩
    · obtain ⟨hb,hd,ha⟩ := ordered_vacuum b.property hda (vacuum_swap C _ _ _ h)
      exact ⟨hb,Or.inr ⟨hd,ha⟩⟩
  · rintro ⟨hb,h|h⟩ <;> rcases h with ⟨rfl,rfl⟩ <;> rw [hb]
    · exact canonical_vacuum C
    · exact vacuum_swap C _ _ _ (canonical_vacuum C)

#print axioms vacuum_spectrum_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
