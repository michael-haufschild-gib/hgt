import GaloisForLFunctions.RHTower.BlindLogNodeDecay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.Diameter

/-! # Counting all frequencies cancelled by a bounded physical record -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {J : Type*} [Fintype J]

private def cosineJet (p h : J → ℝ) (k : ℕ) (y : ℝ) :=
  ∑ j, (p j*h j^k)*cos (y*h j+(k:ℝ)*(π/2))

private theorem jet_derivative (p h : J → ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (cosineJet p h k) (cosineJet p h (k+1) x) x := by
  apply HasDerivAt.fun_sum
  intro j _
  have hd := (((hasDerivAt_id x).mul_const (h j)).add_const ((k:ℝ)*(π/2))).cos.const_mul (p j*h j^k)
  convert hd using 1
  simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,←add_assoc,cos_add_pi_div_two,pow_succ]
  ring

private theorem centered_zero (p t : J → ℝ) (c w : ℝ) (hz : ∑ j, (p j:ℂ)*wave w (t j)=0) :
    cosineJet p (fun j => t j-c) 0 w=0 := by
  have h (j : J) : (p j:ℂ)*wave w (t j-c)=((p j:ℂ)*wave w (t j))*wave w (-c) := by
    rw [sub_eq_add_neg,wave_add,mul_assoc]
  have he : ∑ j, (p j:ℂ)*wave w (t j-c)=0 := by simp only [h,←sum_mul,hz,zero_mul]
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.re_ofReal_mul,wave,Complex.exp_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,mul_one,
    add_zero,Real.exp_zero,one_mul,Complex.zero_re,cosineJet,Nat.cast_zero,pow_zero,zero_mul] using hr

/-- Vanishing at n distinct signed frequencies in a band imposes a
factorial lower bound, even when some frequencies almost coincide.
The centered real Fourier transform is one at zero; interpolate it at
its n zeros and bound its n-th derivative by the n-th power of the half-span. -/
theorem cancellation_factorial {n : ℕ} (v : Fin n → ℝ) (hi : Function.Injective v)
    (p t : J → ℝ) (hp : ∀ j, 0≤p j) (hm : ∑ j, p j=1) {a b W : ℝ}
    (hab : a≤b) (hr : ∀ j, t j∈Set.Icc a b) (hW : 0≤W) (hv : ∀ i, |v i|≤W)
    (hz : ∀ i, ∑ j, (p j:ℂ)*wave (v i) (t j)=0) :
    (n.factorial:ℝ)≤((b-a)*W/2)^n := by
  let c := (a+b)/2
  let R := (b-a)/2
  let h (j : J) := t j-c
  let f := cosineJet p h 0
  have hR : 0≤R := div_nonneg (sub_nonneg.mpr hab) (by norm_num)
  have hrad (j : J) : |h j|≤R := by
    obtain ⟨hlo,hhi⟩ := hr j
    apply abs_le.mpr
    dsimp only [h,c,R]
    constructor <;> linarith only [hlo,hhi]
  have hs : ContDiff ℝ n f := by dsimp only [f,cosineJet]; fun_prop
  have hd (k : ℕ) : iteratedDeriv k f=cosineJet p h k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      exact funext fun x => (jet_derivative p h k x).deriv
  have hM (x : ℝ) : |iteratedDeriv n f x|≤R^n := by
    rw [hd]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ j, p j*R^n := by
        apply sum_le_sum
        intro j _
        rw [abs_mul,abs_mul,abs_of_nonneg (hp j),abs_pow]
        exact (mul_le_of_le_one_right (mul_nonneg (hp j) (pow_nonneg (abs_nonneg _) _))
          (abs_cos_le_one _)).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hrad j) _) (hp j))
      _ = _ := by rw [←Finset.sum_mul,hm,one_mul]
  have hzero (i : Fin n) : f (v i)=0 := centered_zero p t c (v i) (hz i)
  have hf : f 0=1 := by simp [f,cosineJet,hm]
  have hh := RHTower.BlindLogNodeDecay.abs_le_div_factorial_mul_prod hs hM v hi hzero 0
  rw [hf,abs_one] at hh
  simp only [zero_sub,abs_neg] at hh
  have hprod : (∏ i, |v i|)≤W^n := by
    simpa only [prod_const,card_univ,Fintype.card_fin] using
      (prod_le_prod (s:=univ) (fun i _ => abs_nonneg (v i)) (fun i _ => hv i))
  have hN : 0<(n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hprod (div_nonneg (pow_nonneg hR _) hN.le))
  rw [div_mul_eq_mul_div,le_div_iff₀ hN,one_mul,←mul_pow] at hh'
  simpa only [R,div_mul_eq_mul_div] using hh'

/-- Counting distinct Fourier zeros costs bandwidth times duration.
There is no minimum-spacing assumption. -/
theorem cancellation_count {n : ℕ} (v : Fin n → ℝ) (hi : Function.Injective v)
    (p t : J → ℝ) (hp : ∀ j, 0≤p j) (hm : ∑ j, p j=1) {a b W : ℝ}
    (hab : a≤b) (hr : ∀ j, t j∈Set.Icc a b) (hW : 0≤W) (hv : ∀ i, |v i|≤W)
    (hz : ∀ i, ∑ j, (p j:ℂ)*wave (v i) (t j)=0) :
    (n:ℝ)*log 2≤(b-a)*W := by
  let x := (b-a)*W
  have hx : 0≤x := mul_nonneg (sub_nonneg.mpr hab) hW
  have hh := cancellation_factorial v hi p t hp hm hab hr hW hv hz
  change (n.factorial:ℝ)≤(x/2)^n at hh
  have hN : 0<(n.factorial:ℝ) := by exact_mod_cast n.factorial_pos
  have hb : (2:ℝ)^n≤x^n/n.factorial := by
    apply (le_div_iff₀ hN).mpr
    exact (mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤2^n)).trans_eq
      (by rw [←mul_pow]; congr 1; ring)
  have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) n)
    (hb.trans (Real.pow_div_factorial_le_exp hx n))
  simpa only [Real.log_pow,Real.log_exp] using hl

#print axioms cancellation_count
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
