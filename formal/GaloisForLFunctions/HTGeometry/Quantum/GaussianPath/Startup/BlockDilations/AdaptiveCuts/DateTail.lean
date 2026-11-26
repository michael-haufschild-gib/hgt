import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalDraw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PacketRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail

/-! # Inverse-power date tails through a superlinear physical time -/

open Filter Real MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

private theorem candidates_pos (n : ℕ) : 0<sizeRoot (n+2)^62 :=
  pow_pos (root_bounds (by omega : 0<n+2)).1 _

/-- The same typical condition on the frozen coefficients applies to
every date. The cutoff is the sixty-fifth power of the integer
sixty-fourth root of system size. -/
theorem gaussian_superlinear_date_tail :
    ∃ τ>0, ∃ a>0, ∃ δ∈Ioc (0:ℝ) 1, ∃ E : ℕ→Set PathPauliDisorder,
    (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∈E n) ∧ ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let q : ℝ := sizeRoot (n+2)
      ∀ t∈Icc a (δ*q^65),
        pathPauliDisorderLaw.real (((fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹'
          affordableDraw n ⌊τ*K⌋₊ (5/16) t) ∩ E n)≤1/K^6 := by
  obtain ⟨u,v,hu,hv,hreg⟩ := gaussian_adaptive_draw
  obtain ⟨τ,hτ,c,hc,a,ha,η,hη,U,V,hp⟩ := weak_seam_packet_rate hu hv
  let C := (2:ℝ)^64
  have hC : 0<C := pow_pos two_pos _
  let δ := min 1 (η/C)
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hη hC)
  let Z (n : ℕ) := let K : ℝ := (n+2:ℕ); let q : ℝ := sizeRoot (n+2)
    adaptiveDraw (n:=n) (candidates_pos n) (u*K) (v*K) (3*(q^6)⁻¹) q
  let πn (n : ℕ) := fun (ω : PathPauliDisorder) (l : PathLabel n) => pathPauliDisorderShell ω n l
  refine ⟨τ,hτ,a,ha,δ,⟨hδ,min_le_left ..⟩,fun n => πn n ⁻¹' Z n,?_,?_⟩
  · filter_upwards [hreg] with ω hω
    filter_upwards [hω] with n hn
    exact hn (candidates_pos n)
  have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp (sizeRoot_tendsto.comp (tendsto_add_atTop_nat 2))
  have hl := (tendsto_add_atTop_nat 2).eventually (log_root_eventually (by positivity : 0<c/3) 6 0)
  filter_upwards [ht.eventually (eventually_ge_atTop (max 3 (max U V))),hl] with n hq hn
  intro K q t htime
  let N := sizeRoot (n+2)^62
  let M := 3*N
  let L := 2*M
  let z := K/M
  have hq₃ : 3≤q := (le_max_left ..).trans hq
  have hq₁ : 1≤q := (by norm_num : (1:ℝ)≤3).trans hq₃
  have hq' := zero_lt_one.trans_le hq₁
  have hK : 0<K := by dsimp only [K]; positivity
  have hL : (L:ℝ)=6*q^62 := by dsimp only [L,M,N,q]; push_cast; ring
  obtain ⟨hlo,hhi⟩ := packet_quotient (by omega : 0<n+2)
  change q^2/3≤K/(3*q^62) at hlo
  change K/(3*q^62)≤C*q^2/3 at hhi
  have hz : z=K/(3*q^62) := by dsimp only [z,M,N,q]; push_cast; rfl
  rw [←hz] at hlo hhi
  have hz' : 0<z := (div_pos (sq_pos_of_pos hq') (by norm_num)).trans_le hlo
  have hUL : U≤(L:ℝ) := by
    have hUq := (le_max_left U V).trans ((le_max_right ..).trans hq)
    have hh : q≤q^62 := by simpa only [pow_one] using pow_le_pow_right₀ hq₁ (by decide : 1≤62)
    rw [hL]
    linarith only [hUq,hh,pow_nonneg hq'.le 62]
  have hVz : V≤z := by
    have hVq := (le_max_right U V).trans ((le_max_right ..).trans hq)
    nlinarith only [hVq,hlo,mul_nonneg hq'.le (sub_nonneg.mpr hq₃)]
  have hbound : t*z*(3*(q^6)⁻¹)*q≤η*L := by
    have hzcap : z≤C*q^2 := hhi.trans (by linarith only [mul_pos hC (sq_pos_of_pos hq')])
    have h := mul_le_mul htime.2 hzcap hz'.le (mul_nonneg hδ.le (pow_nonneg hq'.le _))
    have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h
      (show 0≤3*(q^6)⁻¹ by positivity)) hq'.le
    apply h'.trans
    rw [hL,show δ*q^65*(C*q^2)*(3*(q^6)⁻¹)*q=(δ*C)*(3*q^62) by field_simp; ring]
    have hdC := (le_div_iff₀ hC).mp (min_le_right 1 (η/C))
    nlinarith only [mul_le_mul_of_nonneg_right hdC (pow_nonneg hq'.le 62),mul_nonneg hη.le (pow_nonneg hq'.le 62)]
  have hm := hp n N (candidates_pos n) hUL hVz (by positivity : 0≤3*(q^6)⁻¹) hq'.le htime.1 hbound
  let A := affordableDraw n ⌊τ*K⌋₊ (5/16) t
  have hmeas : MeasurableSet (A ∩ Z n) := (measurable_affordableDraw ..).inter (measurable_adaptiveDraw ..)
  change pathPauliDisorderLaw.real (πn n ⁻¹' (A ∩ Z n))≤_
  rw [measureReal_def,(prefix_measure n).measure_preimage hmeas.nullMeasurableSet]
  apply hm.trans
  have hs : 6*log K≤c*z := by
    have hlog : 6*log K+0≤c/3*q^2 := hn
    linarith only [hlog,mul_le_mul_of_nonneg_left hlo hc.le]
  apply (exp_le_exp.mpr (show -c*z≤ -(6*log K) by linarith only [hs])).trans_eq
  rw [exp_neg,show (6:ℝ)*log K=(6:ℕ)*log K by norm_num,exp_nat_mul,exp_log hK,one_div]

#print axioms gaussian_superlinear_date_tail
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
