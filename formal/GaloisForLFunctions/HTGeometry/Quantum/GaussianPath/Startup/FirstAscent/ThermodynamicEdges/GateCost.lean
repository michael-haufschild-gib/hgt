import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Density
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.DeepResidence

/-! # Minimum physical gate cost just beyond the first scalar exit -/

open Filter Set Real MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SharpOccupation ReturnSpacing.PhysicalComponents
noncomputable section

/-- Extra time purchased near the first scalar exit by s physical gates. -/
def gateDelay (N s : ℝ) := s*sqrt (log (N/s))/N^2

private theorem delay_scale {m N s : ℝ} (hm : 1 ≤ m) (hs : 0 < s) (hN : 0 < N) (hcut : m^2*s ≤ N) :
    m/2*gateDelay N s ≤ gateDelay N (m*s) := by
  have hm' := zero_lt_one.trans_le hm
  let q := N/(m*s)
  have hq : m ≤ q := (le_div_iff₀ (mul_pos hm' hs)).mpr (by linarith only [hcut])
  have hp : 0 < q := hm'.trans_le hq
  have hlog := log_nonneg (hm.trans hq)
  have he : N/s=m*q := by dsimp only [q]; field_simp
  have hroot : sqrt (log (N/s)) ≤ 2*sqrt (log q) := by
    rw [he,log_mul hm'.ne' hp.ne']
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,sq_sqrt hlog]
    linarith only [log_le_log hm' hq,hlog]
  calc m/2*gateDelay N s = (m*s/(2*N^2))*sqrt (log (N/s)) := by unfold gateDelay; ring
       _ ≤ (m*s/(2*N^2))*(2*sqrt (log q)) := mul_le_mul_of_nonneg_left hroot (by positivity)
       _ = gateDelay N (m*s) := by dsimp only [gateDelay,q]; ring

/-- Throughout a band of lags specified by the budget s, every fit uses
more than s gates and some fit uses at most a fixed multiple of s.
The conclusion also holds after any inverse-square-accurate scalar return. -/
theorem gaussian_gate_cost_at_exit :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      let τ := 4*arcsin (1/20)/circuitHamiltonianSpectralWidth H
      ∀ v : ℝ, HasProjectiveCircuitApproximation N (1/(N:ℝ)^2) 0 (unitaryEvolution H.val v) →
      ∀ s : ℕ, 0 < s → m^3*s ≤ N →
        ∀ t ∈ Icc (τ+gateDelay N ((m:ℝ)*s)) (τ+2*gateDelay N ((m:ℝ)*s)),
        ∃ g : ℕ, IsLeast {j : ℕ | HasProjectiveCircuitApproximation N (1/10) j (unitaryEvolution H.val (v+t))} g ∧
          s < g ∧ g ≤ m^2*s := by
  obtain ⟨b,c,C,M,_,hc,hC,hM,hr⟩ := gaussian_deep_residence
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2*C) (4/c))
  let m := max M (max 2 k)
  have hm : 2 ≤ m := (le_max_left ..).trans (le_max_right ..)
  have hM' : M ≤ m := le_max_left ..
  have hkm : (k:ℝ) ≤ m := by exact_mod_cast (le_max_right 2 k).trans (le_max_right M (max 2 k))
  have hC' : C < (m:ℝ)/2 := by linarith only [(le_max_left ..).trans_lt hk,hkm]
  have hc' : 2 ≤ c*((m:ℝ)/2) := by
    have h := (div_lt_iff₀ hc).mp ((le_max_right ..).trans_lt hk)
    linarith only [h,mul_le_mul_of_nonneg_right hkm hc.le]
  refine ⟨m,hm,?_⟩
  filter_upwards [hr] with ω hω
  filter_upwards [hω] with n hn
  intro N H τ v hv s hs hsize t ht
  have hm₁ : 1 ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hmp : 0 < m := by omega
  have hsp : 0 < (s:ℝ) := Nat.cast_pos.mpr hs
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have h₂ : m^2*s ≤ m^3*s := Nat.mul_le_mul_right s (Nat.pow_le_pow_right hmp (by decide : 2 ≤ 3))
  have hmul : M*(m^2*s) ≤ N := by
    apply (Nat.mul_le_mul_right _ hM').trans
    simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hsize
  have hsmall : M*s ≤ N := (Nat.mul_le_mul_left M (Nat.le_mul_of_pos_left s (pow_pos hmp 2))).trans hmul
  let d := gateDelay (N:ℝ) (s:ℝ)
  let e := gateDelay (N:ℝ) ((m:ℝ)*s)
  let f := gateDelay (N:ℝ) ((m:ℝ)^2*s)
  have he := delay_scale hm₁ hsp hN (by exact_mod_cast h₂.trans hsize)
  have hf := delay_scale hm₁ (mul_pos (zero_lt_one.trans_le hm₁) hsp) hN
    (show (m:ℝ)^2*((m:ℝ)*s) ≤ (N:ℝ) by
      rw [←mul_assoc,←pow_succ]; exact_mod_cast hsize)
  change (m:ℝ)/2*d ≤ e at he
  change (m:ℝ)/2*e ≤ gateDelay (N:ℝ) ((m:ℝ)*((m:ℝ)*s)) at hf
  rw [←mul_assoc,←sq] at hf
  have htwo : 2*s ≤ m^2*s := Nat.mul_le_mul_right s (hm.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hmp (by decide : 1 ≤ 2)))
  have hratio : 1 < (N:ℝ)/s := (one_lt_div hsp).mpr (by exact_mod_cast (show s < N by omega))
  have hd : 0 < d := div_pos (mul_pos hsp (sqrt_pos.mpr (log_pos hratio))) (sq_pos_of_pos hN)
  have he₀ : 0 ≤ e := by dsimp only [e,gateDelay]; positivity
  have hlow : C*d < e := (mul_lt_mul_of_pos_right hC' hd).trans_le he
  have hhigh : 2*e ≤ c*f := (mul_le_mul_of_nonneg_right hc' he₀).trans
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hf hc.le)
  change t∈Icc (τ+e) (τ+2*e) at ht
  have hτ : 0 ≤ τ := div_nonneg (mul_nonneg (by norm_num) (arcsin_pos.mpr (by norm_num)).le)
    (circuitHamiltonianSpectralWidth_nonneg H)
  have hL := (hn v hv (m^2*s) (Nat.mul_pos (pow_pos hmp 2) hs) hmul).1
  have ht' : t∈Icc (0:ℝ) (τ+c*f) := ⟨(add_nonneg hτ he₀).trans ht.1,ht.2.trans (add_le_add le_rfl hhigh)⟩
  have hbig := hL (by simpa only [f,gateDelay,Nat.cast_mul,Nat.cast_pow] using ht')
  have hbound := (hn v hv s hs hsmall).2.1
  have hnot : ¬HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (v+t)) := by
    intro hfit
    have hu := (hbound ⟨hbig.1,hfit⟩).2
    change t ≤ τ+C*d at hu
    linarith only [hlow,ht.1,hu]
  let S := {j : ℕ | HasProjectiveCircuitApproximation N (1/10) j (unitaryEvolution H.val (v+t))}
  have hg : IsLeast S (sInf S) := ⟨Nat.sInf_mem ⟨_,hbig.2⟩,fun _ h => Nat.sInf_le h⟩
  refine ⟨_,hg,lt_of_not_ge (fun hh => hnot ?_),hg.2 hbig.2⟩
  obtain ⟨z,hz,V,hV,heV⟩ := hg.1
  exact ⟨z,hz,V,hV.trans hh,heV⟩

#print axioms gaussian_gate_cost_at_exit

/-- Beyond every fixed positive excess over the thermodynamic exit date,
a positive fraction of the spin count is needed in gates throughout a
fixed forward window after every deep scalar visit. -/
theorem gaussian_linear_cost_after_exit :
    ∃ w b : ℝ, 0 < w ∧ 0 < b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      Tendsto (fun n : ℕ => physicalWidth ω n/((n+2 : ℕ) : ℝ)) atTop (𝓝 w) ∧
      ∀ z : ℝ, 0 < z → ∃ p : ℝ, 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H := shellOperator (pathPauliDisorderShell ω n)
        ∀ v : ℝ, HasProjectiveCircuitApproximation N (1/(N:ℝ)^2) 0 (unitaryEvolution H.val v) →
        ∀ t ∈ Icc ((4*arcsin (1/20)/w+z)/N) b, ∀ s : ℕ,
          HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (v+t)) →
          p*N < (s:ℝ)+1 := by
  obtain ⟨w,hw,_,hwidth⟩ := gaussian_energy_density
  obtain ⟨b,_,C,M,hb,_,hC,hM,hr⟩ := gaussian_deep_residence
  refine ⟨w,b,hw,hb,?_⟩
  filter_upwards [hwidth,hr] with ω hd hr
  refine ⟨hd,?_⟩
  intro z hz
  obtain ⟨m,hm⟩ := exists_nat_gt (2*C/z)
  have hm' : 0 < (m:ℝ) := (div_pos (mul_pos zero_lt_two hC) hz).trans hm
  let K := max M (m^2)
  have hK : 0 < (K:ℝ) := Nat.cast_pos.mpr (hM.trans_le (le_max_left ..))
  let θ := 4*arcsin (1/20)
  have ha : 0 < θ/w := div_pos (mul_pos (by norm_num) (arcsin_pos.mpr (by norm_num))) hw
  have hlim := (tendsto_const_nhds (x:=θ)).div hd hw.ne'
  refine ⟨1/K,one_div_pos.mpr hK,?_⟩
  filter_upwards [hr,hlim.eventually_lt_const (lt_add_of_pos_right (θ/w) (half_pos hz))] with n hn htime
  intro N H v hv t ht s hs
  by_contra! hcheap
  have hN : 0 < (N:ℝ) := by dsimp only [N]; positivity
  let j := s+1
  have hj : 0 < j := Nat.succ_pos _
  have hjr : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
  have hbudget : K*j ≤ N := by
    have h : (j:ℝ) ≤ (N:ℝ)/K := by simpa only [j,Nat.cast_add,Nat.cast_one,one_div_mul_eq_div] using hcheap
    have h' := (le_div_iff₀ hK).mp h
    rw [mul_comm] at h'
    exact_mod_cast h'
  have hcan : M*j ≤ N := (Nat.mul_le_mul_right j (le_max_left ..)).trans hbudget
  have hcut : m^2*j ≤ N := (Nat.mul_le_mul_right j (le_max_right ..)).trans hbudget
  have hle := (Nat.le_mul_of_pos_left j hM).trans hcan
  let q := (j:ℝ)/(N:ℝ)*sqrt (log ((N:ℝ)/j))
  have hq : (m:ℝ)*q ≤ 1 := by
    rw [←mul_assoc]
    exact budget_mass_bound hm'.le hjr hN (by exact_mod_cast hle) (by exact_mod_cast hcut)
  have hcor : C*q < z/2 := by
    have hq' : q ≤ 1/(m:ℝ) := (le_div_iff₀ hm').mpr (by rwa [mul_comm])
    have hcoeff : C/(m:ℝ) < z/2 := (div_lt_iff₀ hm').mpr (by linarith only [(div_lt_iff₀ hz).mp hm])
    exact (mul_le_mul_of_nonneg_left hq' hC.le).trans_lt (by rwa [mul_one_div])
  have hfit : v+t ∈ visitSet H j (1/10) := by
    obtain ⟨p,hp,V,hV,hE⟩ := hs
    exact ⟨p,hp,V,hV.trans (Nat.le_succ _),hE⟩
  have ht₀ : 0 ≤ t := (div_nonneg (add_pos ha hz).le hN.le).trans ht.1
  have h := ((hn v hv j hj hcan).2.1 ⟨⟨ht₀,ht.2⟩,hfit⟩).2
  let W := physicalWidth ω n
  change t ≤ θ/W+C*((j:ℝ)*sqrt (log ((N:ℝ)/j))/(N:ℝ)^2) at h
  have htime' : (N:ℝ)*(θ/W) < θ/w+z/2 := by
    change θ/(W/(N:ℝ)) < _ at htime
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,mul_left_comm,mul_comm] using htime
  have he : (N:ℝ)*(C*((j:ℝ)*sqrt (log ((N:ℝ)/j))/(N:ℝ)^2))=C*q := by
    dsimp only [q]; field_simp
  have hu := mul_le_mul_of_nonneg_left h hN.le
  rw [mul_add,he] at hu
  have hl := (div_le_iff₀ hN).mp ht.1
  change θ/w+z ≤ t*(N:ℝ) at hl
  linarith only [hl,hu,htime',hcor]

#print axioms gaussian_linear_cost_after_exit
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
