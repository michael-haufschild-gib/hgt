import GaloisForLFunctions.PNTPlus.BrunTitchmarsh
import GaloisForLFunctions.RHTower.Sieve.MaynardLocalPrimePowerLeakage
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# The Mangoldt mass in intervals of power width

On intervals from exp(t) of width at least exp(t/4) and at most exp(t), the
Selberg sieve bounds the ordinary primes. Root intervals bound the proper
powers. Their combined Mangoldt mass is at most a constant times the width.
-/

noncomputable section
open Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- A linear upper bound for the actual Mangoldt mass on every interval
starting at exp(t) whose width lies between exp(t/4) and exp(t). -/
theorem mangoldt_mass_on_power_width :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ H : ℝ, Real.exp (t/4) ≤ H → H ≤ Real.exp t →
      ∑ n ∈ Finset.Ioc ⌊Real.exp t⌋₊ ⌊Real.exp t+H⌋₊, vonMangoldt n ≤ C*H := by
  let C := 256+384+8192/Real.log 2
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp only [C]; positivity,fun t ht H hH hH' => ?_⟩
  let X := Real.exp t
  let z := Real.exp (t/64)
  let y := X+H
  have hX : 0 < X := Real.exp_pos _
  have hX2 : 2 ≤ X := by dsimp only [X]; linarith only [Real.add_one_le_exp t, ht]
  have hz : 1 < z := Real.one_lt_exp_iff.mpr (by linarith)
  have hzlog : Real.log z=t/64 := Real.log_exp _
  have hH1 : 1 ≤ H := (Real.one_le_exp (by linarith : 0 ≤ t/4)).trans hH
  have hH0 := zero_lt_one.trans_le hH1
  have hxy : X ≤ y := le_add_of_nonneg_right hH0.le
  have hLy : Real.log y ≤ t+1 := by
    apply (Real.log_le_iff_le_exp (hX.trans_le hxy)).2
    rw [Real.exp_add]
    calc y ≤ X*2 := by dsimp only [y,X]; linarith only [hH']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp 1]) hX.le
  have hLy0 := Real.log_nonneg (by linarith only [hxy,hX2] : 1 ≤ y)
  have hsmall : 1+t/64 ≤ z := by simpa only [add_comm] using Real.add_one_le_exp (t/64)
  have hbig : t+1 ≤ 64*z := by linarith only [hsmall]
  have hpowers (n : ℕ) (hn : n ≤ 16) : z^n ≤ H := by
    dsimp only [z]; rw [← Real.exp_nat_mul]
    apply (Real.exp_le_exp.2 _).trans hH
    have hnr : (n:ℝ) ≤ 16 := by exact_mod_cast hn
    nlinarith only [mul_nonneg (sub_nonneg.mpr hnr) (show 0 ≤ t by linarith only [ht])]
  have hz2 : z^2 ≤ Real.sqrt H := by
    rw [← Real.sqrt_sq (sq_nonneg z)]
    exact Real.sqrt_le_sqrt ((show (z^2)^2 = z^4 by ring).le.trans (hpowers 4 (by decide)))
  have hpcount : ((_root_.RHTower.windowPrimes X y).card : ℝ) ≤
      2*H/Real.log z+6*z*(1+Real.log z)^3 := by
    apply le_trans _ (BrunTitchmarsh.primesBetween_le X H z hX hH0 hz)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hprime,hlo,hhi⟩ := (_root_.RHTower.mem_windowPrimes hX.le (hX.trans_le hxy).le).mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo.le,Nat.le_floor hhi⟩,hprime⟩
  have hmain : (2*H/(t/64))*Real.log y ≤ 256*H := by
    calc _ ≤ (2*H/(t/64))*(2*t) := mul_le_mul_of_nonneg_left
                     (by linarith only [hLy,ht]) (by positivity)
      _ = 256*H := by field_simp [show t ≠ 0 by linarith only [ht]]; ring
  have herr : (6*z*(1+t/64)^3)*Real.log y ≤ 384*H := by
    have hpow := pow_le_pow_left₀ (by linarith only [ht] : 0 ≤ 1+t/64) hsmall 3
    calc _ ≤ (6*z*z^3)*(64*z) := mul_le_mul
             (mul_le_mul_of_nonneg_left hpow (by positivity)) (hLy.trans hbig) hLy0 (by positivity)
      _ = 384*z^5 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hpowers 5 (by decide)) (by norm_num)
  have hprime := _root_.RHTower.PrimeCells.theta_sub_le_card_mul_log hX.le hxy
  have htheta : Chebyshev.theta y - Chebyshev.theta X ≤ (256+384)*H := by
    apply hprime.trans
    apply (mul_le_mul_of_nonneg_right hpcount hLy0).trans
    rw [hzlog,add_mul]
    linarith only [hmain,herr]
  have hroot1 : 1 ≤ Real.sqrt H := by simpa using Real.sqrt_le_sqrt hH1
  have hproper : (Real.log y/Real.log 2)*(Real.sqrt H+1)*Real.log y ≤ (8192/Real.log 2)*H := by
    have hsq : (Real.log y)^2 ≤ (64*z)^2 := pow_le_pow_left₀ hLy0 (hLy.trans hbig) 2
    have haux : (Real.sqrt H+1)*(Real.log y)^2 ≤ 8192*H := by
      calc _ ≤ (2*Real.sqrt H)*((64*z)^2) := mul_le_mul (by linarith only [hroot1]) hsq (sq_nonneg _) (by positivity)
        _ = 8192*(Real.sqrt H*z^2) := by ring
        _ ≤ 8192*(Real.sqrt H*Real.sqrt H) := mul_le_mul_of_nonneg_left
                   (mul_le_mul_of_nonneg_left hz2 (Real.sqrt_nonneg _)) (by norm_num)
        _ = _ := by rw [Real.mul_self_sqrt hH0.le]
    calc _ = ((Real.sqrt H+1)*(Real.log y)^2) / Real.log 2 := by ring
      _ ≤ (8192*H)/Real.log 2 := div_le_div_of_nonneg_right haux hL2.le
      _ = _ := by ring
  have hpsi := _root_.RHTower.Sieve.chebyshevPsi_window_le_theta_window_add_local_primePower
    hX2 hxy (show 1 ≤ y-X by dsimp only [y]; linarith only [hH1])
  rw [show y-X=H by dsimp only [y]; ring] at hpsi
  have hsum : Chebyshev.psi y-Chebyshev.psi X =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊y⌋₊, vonMangoldt n := by
    unfold Chebyshev.psi
    rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (vonMangoldt n : ℝ))
      (Nat.zero_le ⌊X⌋₊) (Nat.floor_mono hxy)]
    ring
  rw [← hsum]
  dsimp only [C]
  linarith only [hpsi,htheta,hproper]
#print axioms mangoldt_mass_on_power_width
end GaloisForLFunctions.ExclusionOfTheCriticalState
