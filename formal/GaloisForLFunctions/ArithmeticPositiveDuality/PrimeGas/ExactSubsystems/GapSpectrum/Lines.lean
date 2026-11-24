import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Carrier
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayArithmeticPartition

/-! # Fourier lines of the optimal overlap are indexed by reduced positive ratios -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open CopyExchange

theorem label_of_energy_eq {a b : ℕ+} (h : energy a = energy b) : a = b := by
  have he := congrArg Real.exp h
  rw [energy,energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) he)

theorem gapFrequency_scale (a b k : ℕ+) : gapFrequency (a*k,b*k) = gapFrequency (a,b) := by
  simp only [gapFrequency,energy_mul,add_sub_add_right_eq_sub]

/-- Dividing out a common factor preserves the line, and every representation of a reduced ratio arises in this way. -/
theorem gapFrequency_fiber {a b : ℕ+} (hc : a.Coprime b) (q : ℕ+ × ℕ+) :
    gapFrequency q = gapFrequency (a,b) ↔ ∃ k : ℕ+, q = (a*k,b*k) := by
  constructor
  · intro h
    have he : q.1*b = q.2*a := by
      apply label_of_energy_eq
      simp only [energy_mul]
      unfold gapFrequency at h
      linarith only [h]
    have hm : q.1.val*b.val = q.2.val*a.val := congrArg PNat.val he
    have hd : a.val ∣ q.1.val*b.val := ⟨q.2.val,hm.trans (Nat.mul_comm _ _)⟩
    obtain ⟨k,h₁⟩ := (PNat.coprime_coe.mpr hc).dvd_of_dvd_mul_right hd
    have hk : 0 < k := Nat.pos_of_ne_zero (fun hz => q.1.ne_zero (by simpa only [hz,Nat.mul_zero] using h₁))
    have h₂ : q.2.val = b.val*k := by
      apply Nat.eq_of_mul_eq_mul_left a.pos
      calc
        a.val*q.2.val = q.1.val*b.val := (Nat.mul_comm _ _).trans hm.symm
        _ = a.val*(b.val*k) := by rw [h₁]; ac_rfl
    exact ⟨⟨k,hk⟩,Prod.ext (PNat.coe_injective h₁) (PNat.coe_injective h₂)⟩
  · rintro ⟨k,rfl⟩
    exact gapFrequency_scale a b k

private def gapFiberEquiv {a b : ℕ+} (hc : a.Coprime b) :
    ℕ+ ≃ {q : ℕ+ × ℕ+ // gapFrequency q = gapFrequency (a,b)} :=
  Equiv.ofBijective (fun k => ⟨(a*k,b*k),gapFrequency_scale a b k⟩)
    ⟨fun k l h => mul_left_cancel (congrArg (fun q : {q : ℕ+ × ℕ+ // gapFrequency q = gapFrequency (a,b)} => q.val.1) h),
      fun q => by
        obtain ⟨k,hk⟩ := (gapFrequency_fiber hc q.val).mp q.property
        exact ⟨k,Subtype.ext hk.symm⟩⟩

private theorem gapAmplitude_scale (x : ℝ) (a b k : ℕ+) :
    gapAmplitude x (a*k,b*k) = (heat ((x+x:ℝ):ℂ) (a*b) / (‖riemannZeta ((x+x:ℝ):ℂ)‖:ℂ)^2) *
      heat (((x+x)+(x+x):ℝ):ℂ) k := by
  rw [gapAmplitude,Complex.ofReal_add (x+x) (x+x),heat_add]
  simp only [heat_mul]
  ring

/-- Every reduced line carries the product weight times the diagonal partition at doubled inverse temperature. -/
theorem overlapCoefficient_reduced {x : ℝ} (hx : 1/2 < x) {a b : ℕ+} (hc : a.Coprime b) :
    overlapCoefficient x (gapFrequency (a,b)) =
      (heat ((x+x:ℝ):ℂ) (a*b) / (‖riemannZeta ((x+x:ℝ):ℂ)‖:ℂ)^2) *
        riemannZeta (((x+x)+(x+x):ℝ):ℂ) := by
  rw [overlapCoefficient_fiber hx,fiberAmplitude,← (gapFiberEquiv hc).tsum_eq]
  change (∑' k : ℕ+, gapAmplitude x (a*k,b*k)) = _
  simp_rw [gapAmplitude_scale]
  rw [tsum_mul_left,(heat_hasSum ⟨(((x+x)+(x+x):ℝ):ℂ),by change 1 < (x+x)+(x+x); linarith⟩).tsum_eq]

/-- The zero-frequency reading is the Gibbs probability that the two integer labels coincide. -/
theorem overlapCoefficient_zero {x : ℝ} (hx : 1/2 < x) :
    overlapCoefficient x 0 = riemannZeta (((x+x)+(x+x):ℝ):ℂ) / (‖riemannZeta ((x+x:ℝ):ℂ)‖:ℂ)^2 := by
  have hc : (1:ℕ+).Coprime 1 := PNat.coprime_coe.mp (by simp)
  have he := overlapCoefficient_reduced hx hc
  simp only [gapFrequency,sub_self,mul_zero,one_mul,show heat ((x+x:ℝ):ℂ) 1 = 1 by simp [heat,energy]] at he
  rw [he]
  ring

theorem overlapCoefficient_zero_ne {x : ℝ} (hx : 1/2 < x) : overlapCoefficient x 0 ≠ 0 := by
  rw [overlapCoefficient_zero hx]
  have h1 : 1 < x+x := by linarith
  have h2 : 1 < (x+x)+(x+x) := by linarith
  exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (s := (((x+x)+(x+x):ℝ):ℂ)) h2)
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re
      (s := ((x+x:ℝ):ℂ)) h1))))

/-- Normalization by the measured constant coefficient removes both zeta factors. -/
theorem relative_overlap_line {x : ℝ} (hx : 1/2 < x) {a b : ℕ+} (hc : a.Coprime b) :
    overlapCoefficient x (gapFrequency (a,b)) / overlapCoefficient x 0 = heat ((x+x:ℝ):ℂ) (a*b) := by
  apply (div_eq_iff (overlapCoefficient_zero_ne hx)).mpr
  rw [overlapCoefficient_reduced hx hc,overlapCoefficient_zero hx]
  ring

/-- The spectrum consists exactly of the doubled energy differences of reduced positive integer pairs. -/
theorem overlapCoefficient_support {x : ℝ} (hx : 1/2 < x) (ω : ℝ) :
    overlapCoefficient x ω ≠ 0 ↔ ∃ a b : ℕ+, a.Coprime b ∧ gapFrequency (a,b) = ω := by
  constructor
  · intro h
    have hpair : ∃ q : ℕ+ × ℕ+, gapFrequency q = ω := by
      by_contra! hn
      apply h
      rw [overlapCoefficient_fiber hx,fiberAmplitude]
      letI : IsEmpty {q : ℕ+ × ℕ+ // gapFrequency q = ω} := ⟨fun q => hn q.val q.property⟩
      simp
    obtain ⟨q,hq⟩ := hpair
    obtain ⟨⟨⟨⟨a,b⟩,hc⟩,k⟩,he⟩ := _root_.RHTower.thetaCuspPrimitiveRayIndexEquivPositivePair.surjective q
    change (a*k,b*k) = q at he
    exact ⟨a,b,hc,(gapFrequency_scale a b k).symm.trans ((congrArg gapFrequency he).trans hq)⟩
  · rintro ⟨a,b,hc,rfl⟩ hz
    have hline := relative_overlap_line hx hc
    rw [hz,zero_div] at hline
    exact Complex.exp_ne_zero _ hline.symm

#print axioms label_of_energy_eq
#print axioms gapFrequency_scale
#print axioms gapFrequency_fiber
#print axioms overlapCoefficient_reduced
#print axioms overlapCoefficient_zero
#print axioms overlapCoefficient_zero_ne
#print axioms relative_overlap_line
#print axioms overlapCoefficient_support

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
