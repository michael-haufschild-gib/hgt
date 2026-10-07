import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction
import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# Exact coefficient mass from rounded integer samples

For the literal Fejer profile on a lattice with spacing at least four, each rounded
integer sample isolates one covariance coefficient. The exact finite pole pairing
recovers the full coefficient mass and retains the defect of arbitrary coefficients.
One actual vanishing half-pole gives a weighted stability bound. Every nonzero
nonnegative mixture in this class has a strictly negative sampled atom.

This is a quantitative source-class law, not universal Weil positivity. It neither
restricts arbitrary repairs nor assumes an archimedean energy sign.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/LATTICE-REPAIR-PROOF.md.
-/

open MeasureTheory Complex Real Set Filter Topology
open scoped ComplexConjugate
open Zeta23
noncomputable section
namespace RHTower.ExposingRayLattice
open RHTower.WeilSpectral
local notation "R" => flatBumpCorr (17/50) (17/1000)

/-- The actual common-profile packet, with all complex coefficients retained. -/
def packet {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) : ℝ → ℂ :=
  ∑ j,c j • transl ((j : ℝ)*X) fejerTest

/-- Its real covariance at a nonnegative integer lattice difference. -/
def lagCoeff {M : ℕ} (c : Fin (M+1) → ℂ) (d : ℕ) : ℝ :=
  ∑ j,∑ k,if k.val+d=j.val then (conj (c k)*c j).re else 0

/-- Rounded integer sample nearest the right side of the `d`th positive correlation window. -/
def sample (X : ℝ) (d : ℕ) : ℕ := ⌈Real.exp (d*X)⌉₊
def sampleError (X : ℝ) (d : ℕ) : ℝ := Real.log (sample X d)-d*X

private theorem sample_bounds {X : ℝ} (hX : 4 ≤ X) {d : ℕ} (hd : 1 ≤ d) :
    2 ≤ sample X d ∧ 0 ≤ sampleError X d ∧ sampleError X d ≤ 1/4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : 4 ≤ (d : ℝ)*X := by nlinarith
  have he : 5 ≤ Real.exp (d*X) := by linarith [Real.add_one_le_exp ((d : ℝ)*X)]
  have hlo : Real.exp (d*X) ≤ (sample X d : ℝ) := Nat.le_ceil _
  have hup : (sample X d : ℝ) < Real.exp (d*X)+1 := Nat.ceil_lt_add_one (by positivity)
  have hn : 2 ≤ sample X d := by exact_mod_cast (show (2 : ℝ) ≤ sample X d by linarith)
  have hn0 : (0 : ℝ) < sample X d := by exact_mod_cast (show 0 < sample X d by omega)
  have hl := Real.log_le_log (Real.exp_pos ((d : ℝ)*X)) hlo
  rw [Real.log_exp] at hl
  have hu : (sample X d : ℝ) ≤ Real.exp ((d : ℝ)*X+1/4) := by
    rw [Real.exp_add]
    have hp := Real.add_one_le_exp (1/4 : ℝ)
    nlinarith [Real.exp_pos ((d : ℝ)*X)]
  have hlog := Real.log_le_log hn0 hu
  rw [Real.log_exp] at hlog
  exact ⟨hn,by dsimp [sampleError];linarith,by dsimp [sampleError];linarith⟩

private theorem sample_corr_pos {X : ℝ} (hX : 4 ≤ X) {d : ℕ} (hd : 1 ≤ d) :
    1/4 ≤ R (sampleError X d) := by
  have h := sample_bounds hX hd
  have h0 := flatBumpCorr_zero_ge (b := (17/50 : ℝ)) (d := 17/1000) (by norm_num) (by norm_num)
  have h1 := flatBumpCorr_sub_le (b := (17/50 : ℝ)) (d := 17/1000) (by norm_num) (by norm_num) h.2.1
  linarith [h.2.2]

private theorem covariance_formula {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) (y : ℝ) :
    (EF.weilTest (packet X c) (packet X c) y).re =
      ∑ j,∑ k,(conj (c k)*c j).re*R (y-((j : ℝ)-(k : ℝ))*X) := by
  have hψ (v : ℝ) : EF.weilTest fejerTest fejerTest v = (R v : ℂ) := weilTest_flatBump _ _ _
  rw [packet,weilTest_sum_transl continuous_fejerTest hasCompactSupport_fejerTest]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,transl,hψ,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [star_def]
  congr 2
  ring

private theorem window_isolation {M d : ℕ} {X : ℝ} (hX : 4 ≤ X) (hd : 1 ≤ d)
    (j k : Fin (M+1)) :
    R (Real.log (sample X d)-((j : ℝ)-(k : ℝ))*X) =
      if k.val+d=j.val then R (sampleError X d) else 0 := by
  have he := sample_bounds hX hd
  split_ifs with h
  · congr 1
    have hc : (k : ℝ)+(d : ℝ)=(j : ℝ) := by exact_mod_cast h
    dsimp [sampleError]
    nlinarith
  · apply flatBumpCorr_eq_zero (by norm_num : (0 : ℝ)<17/1000)
    have hlog : Real.log (sample X d) = d*X+sampleError X d := by dsimp [sampleError];ring
    rw [hlog]
    rcases lt_or_gt_of_ne h with hlt|hgt
    · have hc : (k : ℝ)+(d : ℝ)+1 ≤ (j : ℝ) := by
        have hNat : k.val+d+1 ≤ j.val := by omega
        exact_mod_cast hNat
      have hp := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ X)
      have hz : d*X+sampleError X d-((j : ℝ)-(k : ℝ))*X ≤ -(17/25 : ℝ) := by nlinarith [he.2.2]
      exact (by norm_num : (2 : ℝ)*(17/50)=17/25) ▸ le_trans (by linarith) (neg_le_abs _)
    · have hc : (j : ℝ)+1 ≤ (k : ℝ)+(d : ℝ) := by
        have hNat : j.val+1 ≤ k.val+d := by omega
        exact_mod_cast hNat
      have hp := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ X)
      exact le_trans (by nlinarith [he.2.1]) (le_abs_self _)

/-- Every rounded sample isolates exactly one covariance coefficient. -/
theorem sampled_trace {M d : ℕ} {X : ℝ} (hX : 4 ≤ X) (hd : 1 ≤ d)
    (c : Fin (M+1) → ℂ) :
    atomCoeff (packet X c) (sample X d) = 2*lagCoeff c d*R (sampleError X d) := by
  have hn := congrArg Complex.re (congrFun (tilde_weilTest_self (packet X c))
    (Real.log (sample X d)))
  simp only [EF.tilde,Complex.conj_re] at hn
  unfold atomCoeff
  rw [Complex.add_re,hn]
  rw [covariance_formula]
  simp_rw [window_isolation hX hd]
  unfold lagCoeff
  have he : ∀ j k : Fin (M+1),
      (conj (c k)*c j).re*(if k.val+d=j.val then R (sampleError X d) else 0) =
        (if k.val+d=j.val then (conj (c k)*c j).re else 0)*R (sampleError X d) := by
    intro j k
    split_ifs <;> simp
  simp_rw [he]
  simp_rw [← Finset.sum_mul]
  ring

/-- Exact coefficient mass of the actual packet. -/
def mass {M : ℕ} (c : Fin (M+1) → ℂ) : ℝ := ∑ j,Complex.normSq (c j)

def polePlus {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) : ℂ :=
  ∑ j,c j*(Real.exp ((j : ℝ)*X/2) : ℂ)
def poleMinus {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) : ℂ :=
  ∑ j,c j*(Real.exp (-((j : ℝ)*X/2)) : ℂ)

private theorem coeff_symm {M : ℕ} (c : Fin (M+1) → ℂ) (j k : Fin (M+1)) :
    (conj (c k)*c j).re=(conj (c j)*c k).re := by
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

private theorem triangular_sum {M : ℕ} (A : Fin (M+1) → Fin (M+1) → ℝ)
    (hA : ∀ j k,A j k=A k j) :
    (∑ j,∑ k,A j k)=(∑ j,A j j)+2*∑ j,∑ k,if k<j then A j k else 0 := by
  classical
  have he (j k : Fin (M+1)) : A j k=(if k=j then A j j else 0)+
      (if k<j then A j k else 0)+(if j<k then A j k else 0) := by
    by_cases h:k=j
    · subst k;simp
    · rcases lt_or_gt_of_ne h with hlt|hgt
      · simp [h,hlt,not_lt_of_ge hlt.le]
      · simp [h,hgt,not_lt_of_ge hgt.le]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ =>
    Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => he j k))
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  have hu : (∑ j : Fin (M+1),∑ k,if j<k then A j k else 0)=
      ∑ j : Fin (M+1),∑ k,if k<j then A j k else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hA]
  rw [hu] at hs
  linarith

private theorem lag_sum {M : ℕ} (c : Fin (M+1) → ℂ) (h : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 M,h d*lagCoeff c d)=
      ∑ j,∑ k,if k<j then (conj (c k)*c j).re*h (j.val-k.val) else 0 := by
  classical
  unfold lagCoeff
  simp_rw [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj:k<j
  · rw [if_pos hkj,Finset.sum_eq_single (j.val-k.val)]
    · rw [if_pos (by have := hkj; omega)]
      ring
    · intro d hd hne
      rw [if_neg (by have := hkj; omega)]
    · intro hn
      exact (hn (Finset.mem_Icc.mpr ⟨by have := hkj;omega,by omega⟩)).elim
  · rw [if_neg hkj]
    apply Finset.sum_eq_zero
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    rw [if_neg (by have := hkj;omega)]

private theorem pole_pair {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) :
    (polePlus X c*conj (poleMinus X c)).re =
      ∑ j,∑ k,(conj (c k)*c j).re*Real.exp (((j : ℝ)-(k : ℝ))*X/2) := by
  unfold polePlus poleMinus
  simp only [map_sum,map_mul,Complex.conj_ofReal,Finset.sum_mul,Finset.mul_sum,Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he : Real.exp (((j : ℝ)-(k : ℝ))*X/2)=
      Real.exp ((j : ℝ)*X/2)*Real.exp (-((k : ℝ)*X/2)) := by
    rw [← Real.exp_add];congr 1;ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

private theorem cosh_pair {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) :
    (∑ j,∑ k,(conj (c k)*c j).re*Real.cosh (((j : ℝ)-(k : ℝ))*X/2)) =
      (polePlus X c*conj (poleMinus X c)).re := by
  rw [pole_pair]
  have hn : (∑ j,∑ k,(conj (c k)*c j).re*Real.exp (-(((j : ℝ)-(k : ℝ))*X/2))) =
      ∑ j,∑ k,(conj (c k)*c j).re*Real.exp (((j : ℝ)-(k : ℝ))*X/2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_symm]
    congr 2
    ring
  simp only [Real.cosh_eq,← mul_div_assoc,mul_add,← Finset.sum_div,Finset.sum_add_distrib]
  rw [hn]
  ring

private theorem coefficient_balance {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) :
    mass c+2*∑ d ∈ Finset.Icc 1 M,Real.cosh (d*X/2)*lagCoeff c d =
      (polePlus X c*conj (poleMinus X c)).re := by
  rw [lag_sum,← cosh_pair]
  have hs := triangular_sum
    (fun j k : Fin (M+1) => (conj (c k)*c j).re*Real.cosh (((j : ℝ)-(k : ℝ))*X/2))
    (by
      intro j k
      rw [coeff_symm]
      have he : ((k : ℝ)-(j : ℝ))*X/2 = -(((j : ℝ)-(k : ℝ))*X/2) := by ring
      rw [he,Real.cosh_neg])
  rw [hs]
  congr 1
  · simp [mass,Complex.normSq_apply]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · rw [Nat.cast_sub (by have := h;omega)]
    · rfl

/-- Exact sampled mass, retaining the polar defect for arbitrary complex coefficients. -/
theorem sampled_mass_balance {M : ℕ} {X : ℝ} (hX : 4 ≤ X) (c : Fin (M+1) → ℂ) :
    mass c+∑ d ∈ Finset.Icc 1 M,
      Real.cosh (d*X/2)*atomCoeff (packet X c) (sample X d)/R (sampleError X d) =
        (polePlus X c*conj (poleMinus X c)).re := by
  rw [← coefficient_balance,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hR : R (sampleError X d) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (sample_corr_pos hX hd1))
  rw [sampled_trace hX hd1]
  field_simp

private theorem fejer_half_pole_ne : paperFT fejerTest (I/2) ≠ 0 := by
  let G (u : ℝ) := flatBump (17/50) (17/1000) u*Real.exp (-u/2)
  have hc : Continuous G := (continuous_flatBump _ _).mul (by fun_prop)
  have hs : HasCompactSupport G :=
    (hasCompactSupport_flatBump (b := (17/50 : ℝ)) (d := 17/1000) (by norm_num) (by norm_num)).mul_right
  have hi : Integrable G := hc.integrable_of_hasCompactSupport hs
  have hg : ∀ u,0 ≤ G u := fun u => mul_nonneg (flatBump_nonneg u) (Real.exp_pos _).le
  have hpos : 0 < ∫ u,G u := by
    apply (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hg) hi).mpr
    have hsub : Icc (-(1/10 : ℝ)) (1/10 : ℝ) ⊆ Function.support G := by
      intro u hu
      rw [Function.mem_support]
      have hb : flatBump (17/50) (17/1000) u = 1 :=
        flatBump_eq_one (by norm_num) (by have := abs_le.mpr hu;linarith)
      dsimp [G]
      rw [hb,one_mul]
      exact (Real.exp_pos _).ne'
    exact lt_of_lt_of_le (by rw [Real.volume_Icc];norm_num) (measure_mono hsub)
  have hFT : paperFT fejerTest (I/2)=((∫ u,G u : ℝ) : ℂ) := by
    unfold paperFT
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with u
    have he : I*(I/2)*(u : ℂ)=((-u/2 : ℝ) : ℂ) := by
      push_cast
      calc I*(I/2)*(u : ℂ)=(I*I)*(u : ℂ)/2 := by ring
        _ = _ := by rw [Complex.I_mul_I];ring
    rw [he,← Complex.ofReal_exp]
    change (flatBump (17/50) (17/1000) u : ℂ)*(Real.exp (-u/2) : ℂ)=_
    exact (Complex.ofReal_mul _ _).symm
  intro hz
  have he : (∫ u,G u)=0 := by exact_mod_cast (hFT.symm.trans hz)
  linarith

private theorem paperFT_packet {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ) (z : ℂ) :
    paperFT (packet X c) z=paperFT fejerTest z*
      ∑ j,c j*Complex.exp (I*z*((j : ℝ)*X)) := by
  have hi (j : Fin (M+1)) : Integrable (fun u => c j*(fejerTest (u-(j : ℝ)*X)*Complex.exp (I*z*u))) :=
    (integrable_fejerTest_shift_mul_cexp ((j : ℝ)*X) z).const_mul _
  have he (u : ℝ) : (∑ j,c j*fejerTest (u-(j : ℝ)*X))*Complex.exp (I*z*u)=
      ∑ j,c j*(fejerTest (u-(j : ℝ)*X)*Complex.exp (I*z*u)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold paperFT
  simp only [packet,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,transl,he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_const_mul]
  change (∑ j,c j*paperFT (fun u => fejerTest (u-(j : ℝ)*X)) z)=paperFT fejerTest z*_
  simp_rw [paperFT_translate']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

private theorem poleMinus_eq_zero {M : ℕ} (X : ℝ) (c : Fin (M+1) → ℂ)
    (hp : paperFT (packet X c) (I/2)=0) : poleMinus X c=0 := by
  have hf := paperFT_packet X c (I/2)
  have he (j : Fin (M+1)) : Complex.exp (I*(I/2)*((j : ℝ)*X)) =
      (Real.exp (-((j : ℝ)*X/2)) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    calc I*(I/2)*((j : ℂ)*X)=(I*I)*((j : ℂ)*X)/2 := by ring
      _ = _ := by rw [Complex.I_mul_I];ring
  simp_rw [he] at hf
  change paperFT (packet X c) (I/2)=paperFT fejerTest (I/2)*poleMinus X c at hf
  exact (mul_eq_zero.mp (hf.symm.trans hp)).resolve_left fejer_half_pole_ne

/-- One actual half-pole already determines the full coefficient mass from integer samples. -/
theorem polar_mass_identity {M : ℕ} {X : ℝ} (hX : 4 ≤ X) (c : Fin (M+1) → ℂ)
    (hp : paperFT (packet X c) (I/2)=0) :
    mass c = -(∑ d ∈ Finset.Icc 1 M,
      Real.cosh (d*X/2)*atomCoeff (packet X c) (sample X d)/R (sampleError X d)) := by
  have h := sampled_mass_balance hX c
  rw [poleMinus_eq_zero X c hp,map_zero,mul_zero,Complex.zero_re] at h
  linarith

/-- Positive finite mixtures retain the exact recovered mass; coefficients and profiles are literal. -/
theorem mixture_mass_identity {ι : Type*} [Fintype ι] {M : ℕ} {X : ℝ} (hX : 4 ≤ X)
    (w : ι → ℝ) (c : ι → Fin (M+1) → ℂ)
    (hp : ∀ i,paperFT (packet X (c i)) (I/2)=0) :
    (∑ i,w i*mass (c i)) = -(∑ d ∈ Finset.Icc 1 M,
      Real.cosh (d*X/2)*(∑ i,w i*atomCoeff (packet X (c i)) (sample X d))/R (sampleError X d)) := by
  simp_rw [polar_mass_identity hX _ (hp _),mul_neg,Finset.sum_neg_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Approximate sampled blindness has an explicit, source-faithful coefficient-mass cost. -/
theorem mixture_mass_stability {ι : Type*} [Fintype ι] {M : ℕ} {X : ℝ} (hX : 4 ≤ X)
    (w : ι → ℝ) (c : ι → Fin (M+1) → ℂ)
    (hp : ∀ i,paperFT (packet X (c i)) (I/2)=0) :
    (∑ i,w i*mass (c i)) ≤ 4*∑ d ∈ Finset.Icc 1 M,
      Real.cosh (d*X/2)*|∑ i,w i*atomCoeff (packet X (c i)) (sample X d)| := by
  rw [mixture_mass_identity hX w c hp,← Finset.sum_neg_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hR := sample_corr_pos hX hd1
  have hR0 : 0 < R (sampleError X d) := by linarith
  let T := ∑ i,w i*atomCoeff (packet X (c i)) (sample X d)
  have hC : 0 ≤ Real.cosh (d*X/2) := (Real.cosh_pos _).le
  have hCT : 0 ≤ Real.cosh (d*X/2)*|T| := mul_nonneg hC (abs_nonneg _)
  have hneg := mul_le_mul_of_nonneg_left (neg_le_abs T) hC
  have hscale := mul_le_mul_of_nonneg_left hR hCT
  rw [← neg_div]
  apply (div_le_iff₀ hR0).mpr
  change -(Real.cosh (d*X/2)*T) ≤ (4*(Real.cosh (d*X/2)*|T|))*R (sampleError X d)
  nlinarith

private theorem mass_nonneg {M : ℕ} (c : Fin (M+1) → ℂ) : 0 ≤ mass c :=
  Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (c j))

/-- Every nonzero nonnegative half-polar mixture has a strictly negative sampled atom. -/
theorem exists_negative_sample {ι : Type*} [Fintype ι] {M : ℕ} {X : ℝ} (hX : 4 ≤ X)
    (w : ι → ℝ) (c : ι → Fin (M+1) → ℂ) (hw : ∀ i,0 ≤ w i)
    (hp : ∀ i,paperFT (packet X (c i)) (I/2)=0)
    (hne : ∃ i,0<w i ∧ ∃ j,c i j ≠ 0) :
    ∃ d ∈ Finset.Icc 1 M,2 ≤ sample X d ∧
      (∑ i,w i*atomCoeff (packet X (c i)) (sample X d))<0 := by
  classical
  obtain ⟨i,hi,j,hj⟩ := hne
  have hm : 0 < mass (c i) :=
    lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
      (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (c i k)) (Finset.mem_univ j))
  have hmass : 0 < ∑ k,w k*mass (c k) :=
    lt_of_lt_of_le (mul_pos hi hm)
      (Finset.single_le_sum (fun k _ => mul_nonneg (hw k) (mass_nonneg (c k))) (Finset.mem_univ i))
  by_contra hn
  have htrace : ∀ d ∈ Finset.Icc 1 M,0 ≤ ∑ k,w k*atomCoeff (packet X (c k)) (sample X d) := by
    intro d hd
    have hd2 := (sample_bounds hX (Finset.mem_Icc.mp hd).1).1
    by_contra h
    exact hn ⟨d,hd,hd2,lt_of_not_ge h⟩
  have hs : 0 ≤ ∑ d ∈ Finset.Icc 1 M,
      Real.cosh (d*X/2)*(∑ k,w k*atomCoeff (packet X (c k)) (sample X d))/R (sampleError X d) := by
    apply Finset.sum_nonneg
    intro d hd
    exact div_nonneg (mul_nonneg (Real.cosh_pos _).le (htrace d hd))
      (le_trans (by norm_num) (sample_corr_pos hX (Finset.mem_Icc.mp hd).1))
  have he := mixture_mass_identity hX w c hp
  linarith

/-- Exact sampled nonnegativity classifies the zero active rows; zero-trace repair is a special case. -/
theorem sampled_nonnegative_iff_zero_active {ι : Type*} [Fintype ι] {M : ℕ} {X : ℝ} (hX : 4 ≤ X)
    (w : ι → ℝ) (c : ι → Fin (M+1) → ℂ) (hw : ∀ i,0 ≤ w i)
    (hp : ∀ i,paperFT (packet X (c i)) (I/2)=0) :
    (∀ d ∈ Finset.Icc 1 M,0 ≤ ∑ i,w i*atomCoeff (packet X (c i)) (sample X d)) ↔
      ∀ i,0<w i → c i=0 := by
  classical
  constructor
  · intro hs i hi
    funext j
    by_contra hj
    obtain ⟨d,hd,_,hneg⟩ := exists_negative_sample hX w c hw hp ⟨i,hi,j,hj⟩
    exact (not_lt_of_ge (hs d hd)) hneg
  · intro hz d hd
    have hzero : ∑ i,w i*atomCoeff (packet X (c i)) (sample X d)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi:0<w i
      · rw [hz i hi]
        simp [packet,atomCoeff,weilTest_apply]
      · have hwi : w i=0 := le_antisymm (le_of_not_gt hi) (hw i)
        rw [hwi,zero_mul]
    rw [hzero]

end RHTower.ExposingRayLattice
