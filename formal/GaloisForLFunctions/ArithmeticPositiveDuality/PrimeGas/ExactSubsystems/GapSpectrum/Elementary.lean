import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Readout

/-! # Recovering elementary prime species from the spectrum of finite-factor measurements -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- A positive minimizing line is elementary when two positive minimizing lines cannot add up to it. -/
def elementaryOverlapLine (x ω : ℝ) : Prop :=
  minimumLossLine x ω ∧ ∀ u v : ℝ, minimumLossLine x u → minimumLossLine x v → u+v ≠ ω

private theorem energy_pos_iff_nonvacuum (n : ℕ+) : 0 < energy n ↔ n ≠ 1 := by
  constructor
  · rintro hn rfl
    simp [energy] at hn
  · intro hn
    have hval : n.val ≠ 1 := fun he => hn (PNat.coe_injective he)
    have hpos := n.pos
    exact Real.log_pos (by exact_mod_cast (show 1 < n.val by omega))

/-- The observed elementary frequencies are exactly twice the prime energies.
The test uses only time, Fourier intensity, and addition of observed frequencies. -/
theorem elementaryOverlapLine_iff_prime {x ω : ℝ} (hx : 1/2 < x) :
    elementaryOverlapLine x ω ↔ ∃ p : Nat.Primes, 2*Real.log (p.val:ℝ) = ω := by
  constructor
  · rintro ⟨hmin,hatom⟩
    obtain ⟨n,hn,hfreq⟩ := (minimumLossLine_iff hx).mp hmin
    have hn1 : n.val ≠ 1 := fun he => (energy_pos_iff_nonvacuum n).mp hn (PNat.coe_injective he)
    obtain ⟨p,hp,k,hk⟩ := Nat.exists_prime_and_dvd hn1
    by_cases hk1 : k = 1
    · have hnp : n.val = p := by simpa only [hk1,Nat.mul_one] using hk
      exact ⟨⟨p,hp⟩,by change 2*Real.log (p:ℝ) = ω; rw [← hnp]; exact hfreq⟩
    · have hkpos : 0 < k := Nat.pos_of_ne_zero (fun he => n.ne_zero (by simpa only [he,Nat.mul_zero] using hk))
      let a : ℕ+ := ⟨p,hp.pos⟩
      let b : ℕ+ := ⟨k,hkpos⟩
      have ha : 0 < energy a := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hb : 0 < energy b := (energy_pos_iff_nonvacuum b).mpr (fun he => hk1 (congrArg PNat.val he))
      have hnab : n = a*b := PNat.coe_injective hk
      exfalso
      apply hatom (2*energy a) (2*energy b) ((minimumLossLine_iff hx).mpr ⟨a,ha,rfl⟩)
        ((minimumLossLine_iff hx).mpr ⟨b,hb,rfl⟩)
      rw [← hfreq,hnab,energy_mul,mul_add]
  · rintro ⟨p,rfl⟩
    let n : ℕ+ := ⟨p.val,p.property.pos⟩
    have hn : 0 < energy n := Real.log_pos (by exact_mod_cast p.property.one_lt)
    refine ⟨(minimumLossLine_iff hx).mpr ⟨n,hn,rfl⟩,?_⟩
    intro u v hu hv he
    obtain ⟨a,ha,rfl⟩ := (minimumLossLine_iff hx).mp hu
    obtain ⟨b,hb,rfl⟩ := (minimumLossLine_iff hx).mp hv
    change 2*energy a + 2*energy b = 2*energy n at he
    have hnab : n = a*b := label_of_energy_eq (by rw [energy_mul]; linarith only [he])
    have ha1 : a.val ≠ 1 := fun h => (energy_pos_iff_nonvacuum a).mp ha (PNat.coe_injective h)
    have han : a = n := PNat.coe_injective ((p.property.eq_one_or_self_of_dvd a.val
      ⟨b.val,congrArg PNat.val hnab⟩).resolve_left ha1)
    exact (energy_pos_iff_nonvacuum b).mp hb (mul_left_cancel (hnab.symm.trans (han.symm.trans (mul_one a).symm)))

#print axioms elementaryOverlapLine_iff_prime

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
