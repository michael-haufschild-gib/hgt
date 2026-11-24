import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Envelope

/-! # Equality in the visibility bound fixes the phase of every complementary state -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

/-- A nonzero total with a unit vacuum term has full modulus precisely when every term is positive real. -/
private theorem full_modulus_terms {J : Type*} {f : J → ℂ} (hf : Summable (fun j => ‖f j‖))
    {v : J} (hv : f v = 1) (ht : (∑' j, f j) ≠ 0)
    (he : ‖∑' j, f j‖ = ∑' j, ‖f j‖) : ∀ j, f j = (‖f j‖ : ℂ) := by
  let T := ∑' j, f j
  let c : ℂ := (‖T‖:ℂ)/T
  have hc : ‖c‖ = 1 := by
    rw [show ‖c‖ = _ from norm_div _ _,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr ht)]
  have hrot : Summable (fun j => c*f j) := hf.of_norm.mul_left c
  have hr := (Complex.hasSum_re hrot.hasSum).summable
  have hle (j : J) : (c*f j).re ≤ ‖f j‖ := by
    simpa only [norm_mul,hc,one_mul] using Complex.re_le_norm (c*f j)
  have hsum : (∑' j, (c*f j).re) = ∑' j, ‖f j‖ := by
    rw [← Complex.re_tsum hrot,tsum_mul_left]
    change (c*T).re = _
    rw [show c*T = (‖T‖:ℂ) from div_mul_cancel₀ _ ht]
    exact he
  have hp (j : J) : (c*f j).re = ‖f j‖ := by
    have hj := (hf.sub hr).le_tsum j (fun k _ => sub_nonneg.mpr (hle k))
    rw [hf.tsum_sub hr,hsum,sub_self] at hj
    exact le_antisymm (hle j) (sub_nonpos.mp hj)
  have hterm (j : J) : c*f j = (‖f j‖:ℂ) := by
    apply Complex.ext (hp j)
    apply Complex.abs_re_eq_norm.mp
    rw [hp,abs_of_nonneg (norm_nonneg _),norm_mul,hc,one_mul]
  have hc1 : c = 1 := by simpa only [hv,mul_one,norm_one,Complex.ofReal_one] using hterm v
  simpa only [hc1,one_mul] using hterm

theorem visibility_eq_iff_complement {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes)
    {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P)) {s : ℂ} (hs : 0 < s.re) :
    traceVisibility a s = eulerEnvelope P s ↔
      ∀ j : WindowState (primeWindow P) b, heat s (b j.val) = heat (s.re:ℂ) (b j.val) := by
  let W := primeWindow P
  let f (j : WindowState W b) := heat s (b j.val)
  have hf := (exactWindow_absolute W (primeWindow_primes P) h hs).2
  have ht := (exactWindow_zero_free W (primeWindow_primes P) h hs).2
  have htr := (exactWindow_zero_free W (primeWindow_primes P) h (s := (s.re:ℂ)) hs).2
  have hsum : windowTrace W b (s.re:ℂ) = ((∑' j, ‖f j‖ : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun j => real_heat_eq_norm s (b j.val))
  have hprod := visibility_product P h ha hs
  constructor
  · intro he
    have hV : traceVisibility a s ≠ 0 := div_ne_zero
      (norm_ne_zero_iff.mpr (finiteSubsystem_zero_free h hs))
      (norm_ne_zero_iff.mpr (finiteSubsystem_zero_free h (s := (s.re:ℂ)) hs))
    have hc := mul_left_cancel₀ hV (hprod.trans (he.symm.trans (mul_one _).symm))
    have heq := (div_eq_one_iff_eq (norm_ne_zero_iff.mpr htr)).mp hc
    change ‖∑' j, f j‖ = ‖windowTrace W b (s.re:ℂ)‖ at heq
    rw [hsum,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))] at heq
    obtain ⟨⟨i,v⟩,hv⟩ := h.2 1
    have hb : b v = 1 := PNat.coe_injective (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val hv))
    let j0 : WindowState W b := ⟨v,by rw [hb]; exact Nat.mem_factoredNumbers.mpr ⟨one_ne_zero,by simp⟩⟩
    have hv0 : f j0 = 1 := by change heat s (b v) = 1; simp [hb,heat,energy]
    intro j
    rw [real_heat_eq_norm s]
    exact full_modulus_terms hf hv0 ht heq j
  · intro hphase
    have heq : windowTrace W b s = windowTrace W b (s.re:ℂ) := tsum_congr hphase
    change traceVisibility a s*(‖windowTrace W b s‖/‖windowTrace W b (s.re:ℂ)‖) = _ at hprod
    rwa [heq,div_self (norm_ne_zero_iff.mpr htr),mul_one] at hprod

#print axioms visibility_eq_iff_complement

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
