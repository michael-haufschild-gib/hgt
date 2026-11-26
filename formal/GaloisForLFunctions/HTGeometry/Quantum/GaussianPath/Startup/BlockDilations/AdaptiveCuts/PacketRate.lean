import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.RegularityScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.MassScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.LengthScales

/-! # Date tails in terms of the energy on the selected weakest bonds -/

open Real MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

/-- For a buffer of length M and q=K/M buffers, the affordable mass
is exponentially small in q while the time times the seam price
per buffer is at most a constant times M/q. -/
theorem weak_seam_packet_rate {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    ∃ τ>0, ∃ c>0, ∃ t₀>0, ∃ η>0, ∃ U V : ℝ, ∀ (n N : ℕ) (hN : 0<N),
      let K : ℝ := (n+2:ℕ)
      let M := 3*N
      let L := 2*M
      let q := K/M
      let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
      U≤(L:ℝ) → V≤q → ∀ {w R t : ℝ}, 0≤w → 0≤R → t₀≤t → t*q*w*R≤η*L →
        μ.real (affordableDraw n ⌊τ*K⌋₊ (5/16) t ∩ adaptiveDraw hN (u*K) (v*K) w R)≤exp (-c*q) := by
  obtain ⟨C,hC,γ,hγ,hγ₁,hmass⟩ := exists_mass_scales (half_pos hu) (half_pos hv)
  let A := 8*π/(u/2)
  let ρ := log (4/3)
  have hA : 0<A := by dsimp only [A]; positivity
  have hρ : 0<ρ := log_pos (by norm_num)
  have hρ₂ : ρ≤log 2 := log_le_log (by norm_num) (by norm_num)
  have hl₂ : 0<log 2 := log_pos (by norm_num)
  obtain ⟨α,hα,U,_,hsparse⟩ := exists_wire_fraction hA hC
  let τ := α*γ*ρ/(16*log 2)
  let c := γ*ρ/4
  let t₀ := max 1 (96*A/(γ*ρ))
  let η := 1/(32*84*9*A)
  have hτ : 0<τ := by dsimp only [τ]; positivity
  have hc : 0<c := by dsimp only [c]; positivity
  have ht₀ : 0<t₀ := zero_lt_one.trans_le (le_max_left ..)
  have hη : 0<η := by dsimp only [η]; positivity
  refine ⟨τ,hτ,c,hc,t₀,ht₀,η,hη,max (max 1 A) U,max 1 (2/γ),?_⟩
  intro n N hN K M L q μ hL hq w R t hw hR ht htcut
  have hM : 0<M := Nat.mul_pos (by decide) hN
  have hM' : 0<(M:ℝ) := Nat.cast_pos.mpr hM
  have hL₁ : 1≤(L:ℝ) := (le_max_left ..).trans ((le_max_left ..).trans hL)
  have hAL : A≤(L:ℝ) := (le_max_right ..).trans ((le_max_left ..).trans hL)
  have hUL : U≤(L:ℝ) := (le_max_right ..).trans hL
  have hL' := zero_lt_one.trans_le hL₁
  have hq₁ : 1≤q := (le_max_left ..).trans hq
  have hqp := zero_lt_one.trans_le hq₁
  have ht' := ht₀.trans_le ht
  have ht₁ : 1≤t := (le_max_left ..).trans ht
  have hKpos : 0<K := by dsimp only [K]; positivity
  have hQM : q*(M:ℝ)=K := div_mul_cancel₀ K hM'.ne'
  have hQL : q*(L:ℝ)=2*K := by change q*((2*M:ℕ):ℝ)=_; push_cast; rw [←hQM]; ring
  have hK : K≤q*L := by rw [hQL]; linarith only [hKpos]
  let a := A/(L:ℝ)/t
  let g := ⌊γ*q⌋₊
  let r := ⌊α*(L:ℝ)⌋₊
  let s := ⌊τ*K⌋₊
  let b := (n+1)/M+1
  let k := 2*s/(r+1)
  have ha : 0≤a := div_nonneg (div_nonneg hA.le hL'.le) ht'.le
  have ha₁ : a≤1 := (div_le_one ht').mpr ((div_le_one hL').mpr hAL |>.trans ht₁)
  have hta : t*a=A/L := by dsimp only [a]; field_simp
  have hcuts : (((n+1)/M:ℕ):ℝ)≤q := Nat.cast_div_le.trans
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (by omega : n+1≤n+2)) hM'.le)
  let price := t^2*a*((84:ℝ)*((9*((n+1)/M):ℕ):ℝ)*w*R)
  have hprice : price≤1/32 := by
    have hfactor : 0≤t^2*a := mul_nonneg (sq_nonneg t) ha
    have hcap := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcuts (by norm_num : (0:ℝ)≤84*9)) hw) hR) hfactor
    have hiden : t^2*a*(84*9*q*w*R)=(t*q*w*R)*(84*9*A)/(L:ℝ) := by dsimp only [a]; field_simp; ring
    apply (show price≤t^2*a*(84*9*q*w*R) by
      dsimp only [price]; push_cast; simpa only [mul_assoc] using hcap).trans
    rw [hiden,div_le_iff₀ hL']
    apply (mul_le_mul_of_nonneg_right htcut (by positivity : 0≤84*9*A)).trans_eq
    dsimp only [η]; field_simp; ring
  have hg₀ : (g:ℝ)≤γ*q := Nat.floor_le (mul_nonneg hγ.le hqp.le)
  have hg₁ : γ*q/2≤(g:ℝ) := by
    have h := (div_le_iff₀ hγ).mp ((le_max_right ..).trans hq)
    linarith only [h,Nat.lt_floor_add_one (γ*q)]
  obtain ⟨hb,hb',_⟩ := packet_number (n:=n) hM
  have hb₂ : (b:ℝ)≤2*q := by linarith only [hb',hq₁]
  let m := (u/2)*L/16
  have hcross : π≤2*(t*a)*m := by
    rw [hta]; dsimp only [A,m]; apply le_of_eq; field_simp; ring
  have htest := hsparse hUL (Nat.floor_le (mul_nonneg hα.le hL'.le))
  have hf := hmass hL' hqp hb₂ hg₀ ha ha₁
  rw [hQL,show (v/2)*(2*K)=v*K by ring,show (u/2)*(2*K)=u*K by ring] at hf
  have hphysical := physical_weak_seam_mass (n:=n) hN r s g ht'.le ha hw hR (5/16) (u*K) (v*K)
    (m:=m) (C:=C*sqrt L) (by dsimp only [m]; positivity) (mul_pos hC (sqrt_pos.mpr hL')) hcross
    (by change 2*(5/16+price)+(t*a)*_*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1
        rw [hta]; linarith only [htest,hprice]) hf
  let p := μ.real (affordableDraw n s (5/16) t ∩ adaptiveDraw hN (u*K) (v*K) w R)
  by_cases hp : 0<p
  · have hdim : Fintype.card (PathLabel n)≤12*(n+2) := by
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; omega
    have hcost := packet_bit_budget hα hL' hτ.le hqp.le (s:=s) (r:=r)
      ((Nat.floor_le (mul_nonneg hτ.le hKpos.le)).trans (mul_le_mul_of_nonneg_left hK hτ.le))
      (Nat.lt_floor_add_one (α*(L:ℝ))).le
    have hbit : (k:ℝ)*log 2≤γ*q*ρ/8 := by
      apply (mul_le_mul_of_nonneg_right hcost hl₂.le).trans_eq
      dsimp only [τ]; field_simp; ring
    have hkb : k≤b := by
      apply Nat.cast_le.mp (le_trans (b:=q) ?_ hb)
      apply le_of_mul_le_mul_right _ hl₂
      apply hbit.trans
      have h := mul_le_mul_of_nonneg_left hρ₂ (mul_nonneg hγ.le hqp.le)
      have h' := mul_le_mul_of_nonneg_right hγ₁ (mul_nonneg hqp.le hl₂.le)
      nlinarith only [h,h',mul_nonneg hqp.le hl₂.le]
    have hgb : g≤b := Nat.cast_le.mp ((hg₀.trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hγ₁ hqp.le)).trans hb)
    have hjac : (Fintype.card (PathLabel n):ℝ)*a≤γ*q*ρ/8 := by
      have htbig : 96*A/(γ*ρ)≤t := (le_max_right ..).trans ht
      have htime := (div_le_iff₀ (mul_pos hγ hρ)).mp htbig
      have hd : (Fintype.card (PathLabel n):ℝ)≤12*K := by dsimp only [K]; exact_mod_cast hdim
      apply (mul_le_mul_of_nonneg_right hd ha).trans
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ)≤12)) ha).trans
      have he : 12*(q*L)*a=12*q*A/t := by dsimp only [a]; field_simp
      rw [he,div_le_iff₀ ht']
      nlinarith only [mul_le_mul_of_nonneg_left htime hqp.le]
    have hlog := log_of_packet_count hp ha b _ k g hkb hgb hphysical
    have hprice := mul_le_mul_of_nonneg_right hg₁ hρ.le
    apply (le_of_eq (exp_log hp).symm).trans (exp_le_exp.mpr ?_)
    dsimp only [c]
    linarith only [hlog,hjac,hbit,hprice]
  · exact (le_of_not_gt hp).trans (exp_pos _).le

#print axioms weak_seam_packet_rate
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
