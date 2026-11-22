import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.VacuumSpectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.LowestShell

/-!
# Exact range of the antipodal spectral parameters

A turn of 1/M on a prescribed nonsquare label realizes that very label
as the lowest block. A proper root would have a nontrivial dyadic
exponent and would make the prescribed label square.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture DyadicAperture.Binary

private theorem turn_period (N : ℕ) (hN : N ≠ 0) (k : ℕ) :
    (Circle.exp (2*Real.pi/(N:ℝ)))^k = 1 ↔ N ∣ k := by
  rw [← Circle.exp_natCast_mul,Circle.exp_eq_one]
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hπ : 2*Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  constructor
  · rintro ⟨j,hj⟩
    have he : (k:ℝ)*(2*Real.pi) = ((j:ℝ)*(2*Real.pi))*N :=
      (div_eq_iff hn).mp (by rw [mul_div_assoc]; exact hj)
    have h : (k:ℝ) = (N:ℝ)*(j:ℝ) := mul_right_cancel₀ hπ (he.trans (by ring))
    have hi : (k:ℤ) = (N:ℤ)*j := by exact_mod_cast h
    exact_mod_cast (show (N:ℤ) ∣ (k:ℤ) from ⟨j,hi⟩)
  · rintro ⟨l,rfl⟩
    refine ⟨(l:ℤ),?_⟩
    rw [Int.cast_natCast,Nat.cast_mul]
    field_simp [hn]

theorem turn_order (N : ℕ) (hN : N ≠ 0) : orderOf (Circle.exp (2*Real.pi/(N:ℝ))) = N :=
  Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((turn_period _ hN _).mpr dvd_rfl))
    ((turn_period _ hN _).mp (pow_orderOf_eq_one _))

/-- Time for a forward fraction of a full turn on the occupation H against vacuum. -/
def calibration (H : ℕ+) (M : ℕ) : ℝ := 2*Real.pi/((M:ℝ)*energy H)

private theorem energy_pos {H : ℕ+} (hH : 1 < H.val) : 0 < energy H := Real.log_pos (by exact_mod_cast hH)

private theorem calibration_rejects (H : ℕ+) (hH : 1 < H.val) (M : ℕ) (hm : 1 < M)
    (hd : ∃ j : ℕ, M = 2^j) : rejected (calibration H M) (pair H 1) := by
  have hM : M ≠ 0 := by omega
  have he : (calibration H M)*energy H = 2*Real.pi/(M:ℝ) := by
    unfold calibration
    field_simp [(energy_pos hH).ne',Nat.cast_ne_zero.mpr hM]
  let z := Circle.exp (2*Real.pi/(M:ℝ))
  have hz : orderOf z = M := turn_order _ hM
  have hphase : (binary (calibration H M)).phase () (pair H 1) = z := by
    change Circle.exp (calibration H M*(energy H-energy 1)) = z
    rw [show energy 1 = 0 by norm_num [energy],sub_zero,he]
  rw [rejected_iff,misses_iff_return,hphase]
  obtain ⟨j,hj⟩ := hd
  refine ⟨⟨j,orderOf_dvd_iff_pow_eq_one.mp (by rw [hz,hj])⟩,?_⟩
  intro hone
  have : orderOf z = 1 := orderOf_eq_one_iff.mpr hone
  omega

/-- The prescribed block and order are attained at the explicit calibration time. -/
theorem calibrated_parameters (H : {H : ℕ+ // 1 < H.val ∧ ¬IsSquare H.val})
    (M : {M : ℕ // 1 < M ∧ ∃ j : ℕ, M = 2^j}) :
    ∃ ht : calibration H.val M.val ∈ exceptional,
      block ⟨_,ht⟩ = H.val ∧ windingOrder ⟨_,ht⟩ = M.val := by
  let t := calibration H.val M.val
  have hx : rejected t (pair H.val 1) := calibration_rejects _ H.property.1 _ M.property.1 M.property.2
  let u : ExceptionalTime := ⟨t,⟨_,hx⟩⟩
  let v : VacuumTime := ⟨u,⟨_,hx⟩⟩
  obtain ⟨k,hk⟩ := (vacuum_support v H.val).mp hx
  change H.val = (block u)^k.val at hk
  have hk₀ : k.val ≠ 0 := fun h => k.property (h ▸ dvd_zero _)
  have hm₀ : M.val ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one M.property.1)
  have hlog : energy H.val = (k.val:ℝ)*energy (block u) := by
    rw [hk]
    simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]
  have hturn : t*energy (block u) = 2*Real.pi/((M.val*k.val:ℕ):ℝ) := by
    change (2*Real.pi/((M.val:ℝ)*energy H.val))*energy (block u) = _
    rw [hlog,Nat.cast_mul]
    field_simp [(energy_pos (block_nontrivial u)).ne',Nat.cast_ne_zero.mpr hk₀,Nat.cast_ne_zero.mpr hm₀]
  have horder := vacuum_phase_order v
  change orderOf (Circle.exp (t*energy (block u))) = windingOrder u at horder
  rw [hturn,turn_order _ (Nat.mul_ne_zero hm₀ hk₀)] at horder
  obtain ⟨j,hj⟩ := order_dyadic u
  have hd : k.val ∣ 2^j := ⟨M.val,hj.symm.trans (horder.symm.trans (Nat.mul_comm _ _))⟩
  obtain ⟨i,_,hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hone : k.val = 1 := by
    cases i with
    | zero => simpa only [pow_zero] using hi
    | succ l =>
      exfalso
      apply H.property.2
      rw [hk,PNat.pow_coe,hi,pow_succ,pow_mul,pow_two]
      exact ⟨_,rfl⟩
  refine ⟨u.property,?_,?_⟩
  · simpa only [hone,pow_one] using hk.symm
  · simpa only [hone,Nat.mul_one] using horder.symm

/-- Exact range of the joint observation of lowest product and missing-winding period. -/
theorem spectral_range (H : ℕ+) (M : ℕ) :
    (∃ t : ExceptionalTime, block t = H ∧ windingOrder t = M) ↔
      (1 < H.val ∧ ¬IsSquare H.val) ∧ (1 < M ∧ ∃ j : ℕ, M = 2^j) := by
  constructor
  · rintro ⟨t,rfl,rfl⟩
    exact ⟨⟨block_nontrivial t,block_nonsquare t⟩,order_nontrivial t,order_dyadic t⟩
  · rintro ⟨hH,hM⟩
    obtain ⟨ht,hb,hm⟩ := calibrated_parameters ⟨H,hH⟩ ⟨M,hM⟩
    exact ⟨⟨_,ht⟩,hb,hm⟩

#print axioms turn_order
#print axioms calibrated_parameters
#print axioms spectral_range

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
