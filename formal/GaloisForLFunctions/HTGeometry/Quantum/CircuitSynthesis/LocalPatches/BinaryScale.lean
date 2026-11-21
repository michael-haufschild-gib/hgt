import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PrefixCircuit
import Mathlib.Data.Nat.Sqrt

/-! # Choosing the patch radius and timestep on a binary spacetime scale -/
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

private theorem patch_polynomial (p : ℕ) (hp : 64 ≤ p) : 1400*(p+1)^3 ≤ 2^p := by
  induction p,hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    have h : (p+2)^3 ≤ 2*(p+1)^3 := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hp
      ring_nf
      omega
    calc
      _ ≤ 2*(1400*(p+1)^3) := by nlinarith only [h]
      _ ≤ 2*2^p := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ (2:ℕ) p,Nat.mul_comm]

private theorem patch_gate_binary (p : ℕ) (hp : 64 ≤ p) : patchGateCost p 21 ≤ 2^(2*p) := by
  have h (j : ℕ) (hj : 64 ≤ j) : 42*(j+1)*3^j ≤ 4^j := by
    induction j,hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      rw [pow_succ (3:ℕ),pow_succ (4:ℕ)]
      calc
        _ = (42*(j+2)*3)*3^j := by ring
        _ ≤ (4*(42*(j+1)))*3^j := Nat.mul_le_mul_right _ (by omega)
        _ = (42*(j+1)*3^j)*4 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ ih
  calc
    patchGateCost p 21 = 42*(p+1)*3^p := by unfold patchGateCost; ring
    _ ≤ 4^p := h p hp
    _ = 2^(2*p) := by norm_num [pow_mul]

private theorem patch_scale_binary (d p : ℕ) (hd : d<(2*p+2)^2) (hp : 64 ≤ p)
    (R : ℝ) (hR' : R ≤ 2*(d:ℝ)) :
    patchScale p (21*R) ≤ (2:ℝ)^(4*p) := by
  have hpoly : 1400*((p:ℝ)+1)^3 ≤ (2:ℝ)^p := by exact_mod_cast patch_polynomial p hp
  have hdim : (d:ℝ) ≤ (2*(p:ℝ)+2)^2 := by exact_mod_cast hd.le
  have hpay : 8*(1+((p:ℝ)+1)*(21*R)) ≤ (2:ℝ)^p := by
    apply le_trans _ hpoly
    have hm := mul_le_mul_of_nonneg_left (hR'.trans (mul_le_mul_of_nonneg_left hdim (by norm_num)))
      (by positivity : 0 ≤ (p:ℝ)+1)
    nlinarith only [hm,Nat.cast_nonneg (α := ℝ) p,sq_nonneg (p:ℝ),
      pow_nonneg (Nat.cast_nonneg (α := ℝ) p) 3]
  calc
    patchScale p (21*R) = (2:ℝ)^(3*p)*(8*(1+((p:ℝ)+1)*(21*R))) := by
      dsimp [patchScale]
      rw [pow_succ (8:ℝ) p,pow_mul]
      ring
    _ ≤ (2:ℝ)^(3*p)*2^p := mul_le_mul_of_nonneg_left hpay (by positivity)
    _ = _ := by rw [←pow_add]; congr 1; omega

/-- For spacetime volume at most 2^d, radius floor(sqrt(d)/2) suffices.
The number of timesteps tracks actual duration, also when d is only an upper scale. -/
theorem binary_patch_schedule (N d : ℕ) (t R : ℝ) (ht : 0 ≤ t)
    (hvol : (N:ℝ)*(1+t) ≤ (2:ℝ)^d) (hroot : 128 ≤ d.sqrt)
    (hR : 0 ≤ R) (hcap : R ≤ 2*(d:ℝ)) :
    ∃ p r : ℕ, 0 < r ∧
      14*(N:ℝ)*(patchScale p (21*R)*t)*(patchScale p (21*R)*t/r)^p ≤ 1/100 ∧
      ((r*(N*patchGateCost p 21):ℕ):ℝ) ≤ (N:ℝ)*(1+t)*2^(5*d.sqrt+17) := by
  let p := d.sqrt/2
  let K := patchScale p (21*R)
  let T := (1+t)*(2:ℝ)^(8*p+16)
  let r := ⌈T⌉₊
  have hp : 64 ≤ p := by dsimp [p]; omega
  have hd : d < (2*p+2)^2 := (Nat.lt_succ_sqrt d).trans_le (by
    rw [← pow_two]
    exact Nat.pow_le_pow_left (by dsimp [p]; omega) 2)
  have hK : K ≤ (2:ℝ)^(4*p) := patch_scale_binary d p hd hp R hcap
  have hK0 : 0 ≤ K := by dsimp [K,patchScale]; positivity
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le (by linarith only [ht]) (one_le_pow₀ (by norm_num))
  have hrL : T ≤ (r:ℝ) := Nat.le_ceil _
  have hrpos : 0 < (r:ℝ) := zero_lt_one.trans_le (hT.trans hrL)
  have hrU : (r:ℝ) ≤ 2*T := (Nat.ceil_lt_add_one (zero_le_one.trans hT)).le.trans (by linarith only [hT])
  have hx : K*t/r ≤ 1/(2:ℝ)^(4*p+16) := by
    rw [div_le_div_iff₀ hrpos (by positivity),one_mul]
    apply le_trans _ hrL
    calc
      _ ≤ (2:ℝ)^(4*p)*(1+t)*2^(4*p+16) := by gcongr; linarith only [ht]
      _ = T := by dsimp [T]; rw [mul_right_comm,←pow_add,show 4*p+(4*p+16)=8*p+16 by omega,mul_comm]
  have hn : (N:ℝ)*t ≤ (2:ℝ)^d := (mul_le_mul_of_nonneg_left (by linarith : t ≤ 1+t) (by positivity)).trans hvol
  have he : d+4*p+11 ≤ (4*p+16)*p := by nlinarith only [hd,hp]
  have hcoef : 100*(14*(N:ℝ)*(K*t)) ≤ (2:ℝ)^((4*p+16)*p) := calc
    _ = 1400*((N:ℝ)*t)*K := by ring
    _ ≤ (2:ℝ)^11*2^d*2^(4*p) := mul_le_mul (mul_le_mul (by norm_num) hn (by positivity) (by positivity))
      hK hK0 (by positivity)
    _ ≤ _ := by rw [←pow_add,←pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨p,r,by exact_mod_cast hrpos,?_,?_⟩
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<100)).mpr
    calc
      _ = (100*(14*(N:ℝ)*(K*t)))*(K*t/r)^p := by ring
      _ ≤ (2:ℝ)^((4*p+16)*p)*(1/(2:ℝ)^(4*p+16))^p := mul_le_mul hcoef
        (pow_le_pow_left₀ (by positivity) hx _) (by positivity) (by positivity)
      _ = 1 := by rw [one_div,inv_pow,←pow_mul]; exact mul_inv_cancel₀ (by positivity)
  · have hg : (patchGateCost p 21:ℝ) ≤ 2^(2*p) := by exact_mod_cast patch_gate_binary p hp
    push_cast
    calc
      _ ≤ (2*T)*((N:ℝ)*2^(2*p)) := mul_le_mul hrU (mul_le_mul_of_nonneg_left hg (by positivity))
        (by positivity) (by positivity)
      _ = (N:ℝ)*(1+t)*2^(8*p+16+2*p+1) := by dsimp [T]; rw [pow_succ (2:ℝ) (8*p+16+2*p),pow_add (2:ℝ) (8*p+16) (2*p)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (by dsimp [p]; omega)) (by positivity)

#print axioms binary_patch_schedule
end
end GaloisForLFunctions.HTGeometry.LocalPatches
