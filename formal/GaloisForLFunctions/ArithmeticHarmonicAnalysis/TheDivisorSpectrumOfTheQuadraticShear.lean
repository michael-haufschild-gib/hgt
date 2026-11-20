import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TheFourierTransformOfTheFixedGapQuadratic

/-!
# The divisor spectrum of the quadratic shear

At an arbitrary gap frequency j, the dual linear congruence retains the
gcd strata d dividing j. Each stratum contributes d times a Ramanujan
sum at complementary modulus N/d. This determines the whole twisted
root response even when the frequency and modulus share prime powers.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Finset
open _root_.RHTower _root_.RHTower.Sieve
noncomputable section
open scoped Classical

private theorem annihilator_modulus {N : ℕ} [NeZero N] (x s : ZMod N) :
    x*s=0 ↔ (N/x.val.gcd N)∣s.val := by
  let d := x.val.gcd N
  have hd : 0<d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hx : d*(x.val/d)=x.val := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hn : d*(N/d)=N := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hc := (Nat.coprime_div_gcd_div_gcd hd).symm
  have he : ((x.val*s.val:ℕ):ZMod N)=x*s := by rw [Nat.cast_mul,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  rw [←he,ZMod.natCast_eq_zero_iff]
  change N∣x.val*s.val ↔ N/d∣s.val
  calc
    _ ↔ d*(N/d)∣d*((x.val/d)*s.val) := by rw [←mul_assoc,hx,hn]
    _ ↔ N/d∣(x.val/d)*s.val := Nat.mul_dvd_mul_iff_left hd
    _ ↔ _ := hc.dvd_mul_left

private theorem gcd_annihilator_fourier {N : ℕ} [NeZero N] (x j : ZMod N) :
    ((univ.filter (fun u : ZMod N => u*x+j=0)).card:ℂ)=
      if x.val.gcd N∣j.val then (x.val.gcd N:ℂ) else 0 := by
  let d := x.val.gcd N
  have hn := Nat.pos_of_ne_zero (NeZero.ne N)
  have hd : 0<d := Nat.gcd_pos_of_pos_right _ hn
  have hv : d∣N := Nat.gcd_dvd_right _ _
  have hq : 0<N/d := Nat.div_pos (Nat.le_of_dvd hn hv) hd
  have hprod : d*(N/d)=N := Nat.mul_div_cancel' hv
  have hdiv : N/(N/d)=d := Nat.div_eq_of_eq_mul_left hq hprod.symm
  rw [←annihilator_fourier_count ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar N)]
  simp only [annihilator_modulus,mul_comm j]
  have he := sum_stdAddChar_divisible hn (Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd hv,hn.ne'⟩ : N/d∈N.divisors) j
  rwa [hdiv] at he

private theorem val_finEquiv {N : ℕ} [NeZero N] (b : Fin N) : (ZMod.finEquiv N b).val=b.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

/-- Every gcd stratum has the Fourier transform of the units at its
complementary modulus, including the stratum containing the zero residue. -/
theorem gcd_stratum_ramanujan {N d : ℕ} [NeZero N] (hd : d∈N.divisors) (m : ZMod N) :
    (∑ x : ZMod N, if x.val.gcd N=d then ZMod.stdAddChar (x*m) else 0) =
      cglRamanujanAdditiveSum ⟨N/d,Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
        (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)⟩ (m.val:ZMod (N/d)) := by
  let q := N/d
  have hn := Nat.pos_of_ne_zero (NeZero.ne N)
  have hd₀ := Nat.pos_of_mem_divisors hd
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hq : 0<q := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd₀
  letI : NeZero q := ⟨hq.ne'⟩
  have hN : d*q=N := Nat.mul_div_cancel' hdvd
  let F (x : ZMod N) := if x.val.gcd N=d then ZMod.stdAddChar (x*m) else 0
  have hrestrict : ∑ x : ZMod N, F x = ∑ x : {x : ZMod N // d∣x.val}, F x.val := by
    rw [←sum_subtype (univ.filter (fun x : ZMod N => d∣x.val)) (by simp) F]
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro x _ h
    apply if_neg
    intro he
    exact h (mem_filter.mpr ⟨mem_univ _,he ▸ Nat.gcd_dvd_left x.val N⟩)
  rw [show (∑ x : ZMod N, if x.val.gcd N=d then ZMod.stdAddChar (x*m) else 0)=
      ∑ x : ZMod N, F x from rfl,hrestrict,←(ramanujanMultiplesFinEquiv hn hd).sum_comp]
  let G (x : ZMod q) := if IsUnit x then ZMod.stdAddChar (x*(m.val:ZMod q)) else 0
  have each (b : Fin q) : F ((ramanujanMultiplesFinEquiv hn hd b).val)=G (ZMod.finEquiv q b) := by
    have hlt : d*b.val<N := ((Nat.mul_lt_mul_left hd₀).mpr b.isLt).trans_eq hN
    have hg : (d*b.val).gcd N=d*b.val.gcd q := by rw [←hN,Nat.gcd_mul_left]
    have hu : IsUnit (ZMod.finEquiv q b) ↔ b.val.Coprime q := by
      simpa only [ZMod.natCast_zmod_val,val_finEquiv] using
        (ZMod.isUnit_iff_coprime (ZMod.finEquiv q b).val q)
    have hcop : d*b.val.gcd q=d ↔ b.val.Coprime q := by
      change d*b.val.gcd q=d ↔ b.val.gcd q=1
      conv_lhs => rhs; rw [←mul_one d]
      exact Nat.mul_left_cancel_iff_of_pos hd₀
    simp only [F,G,ramanujanMultiplesFinEquiv_apply,ZMod.val_natCast_of_lt hlt,hg,hcop,hu]
    split_ifs
    · rw [stdAddChar_divisorMultiple hn hd]
      have hb : (b.val:ZMod q)=ZMod.finEquiv q b := by
        rw [←val_finEquiv b,ZMod.natCast_zmod_val]
      rw [hb]
    · rfl
  rw [sum_congr rfl (fun b _ => each b),(ZMod.finEquiv q).toEquiv.sum_comp G]
  change (∑ x : ZMod q, if IsUnit x then ZMod.stdAddChar (x*(m.val:ZMod q)) else 0)=_
  rw [←sum_filter]
  rfl

/-- The full fixed-gap quadratic transform at every modulus and every
frequency. The primitive formula is its single-divisor case. -/
theorem quadratic_shear_full_divisor_spectrum (M : ℕ+) (j a : ZMod (M:ℕ)) :
    fixedGapQuadraticTransform ZMod.stdAddChar j a =
      ∑ d ∈ (M:ℕ).divisors.attach, if d.val∣j.val then (d.val:ℂ)*
        cglRamanujanAdditiveSum ⟨(M:ℕ)/d.val,Nat.div_pos (Nat.le_of_dvd M.pos
          (Nat.dvd_of_mem_divisors d.property)) (Nat.pos_of_mem_divisors d.property)⟩
          ((a-j).val:ZMod ((M:ℕ)/d.val)) else 0 := by
  rw [fixedGapQuadraticTransform_linear_fibres ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (M:ℕ))]
  simp only [gcd_annihilator_fourier]
  let D := (M:ℕ).divisors
  let m := a-j
  let χ (x : ZMod (M:ℕ)) := ZMod.stdAddChar (x*m)
  have entry (x : ZMod (M:ℕ)) :
      (if x.val.gcd M∣j.val then (x.val.gcd M:ℂ) else 0)*ZMod.stdAddChar ((a-j)*x) =
      ∑ d ∈ D.attach, (if d.val∣j.val then (d.val:ℂ) else 0)*
        (if x.val.gcd M=d.val then χ x else 0) := by
    let d₀ : D := ⟨x.val.gcd M,Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,M.pos.ne'⟩⟩
    rw [sum_eq_single_of_mem d₀ (mem_attach _ _)]
    · simp only [d₀,if_true,χ,m,mul_comm (a-j)]
    · intro d _ hd
      rw [if_neg (show x.val.gcd M≠d.val from fun h => hd (Subtype.ext h.symm)),mul_zero]
  rw [sum_congr rfl fun x _ => entry x,sum_comm]
  apply sum_congr rfl
  intro d _
  rw [←mul_sum]
  change (if d.val∣j.val then (d.val:ℂ) else 0)*
    (∑ x : ZMod (M:ℕ), if x.val.gcd M=d.val then ZMod.stdAddChar (x*m) else 0) = _
  rw [gcd_stratum_ramanujan d.property m]
  split_ifs <;> simp only [zero_mul]

#print axioms gcd_stratum_ramanujan
#print axioms quadratic_shear_full_divisor_spectrum
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
