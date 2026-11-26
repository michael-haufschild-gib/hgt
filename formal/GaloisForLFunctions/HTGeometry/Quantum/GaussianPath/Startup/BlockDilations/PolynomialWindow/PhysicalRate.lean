import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.BoundedProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.RegularityScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.MassScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.LengthScales

/-! # Exponential exclusion in the number of physical packets -/

open MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- For fixed positive field density and total energy density, the probability
of an extensive gate fit decays exponentially in the number of packets.
The time range is proportional to the packet length divided by that number. -/
theorem physical_packet_rate {u v B : ℝ} (hu : 0<u) (hv : 0<v) (hB : 0<B) :
    ∃ τ>0, ∃ c>0, ∃ t₀>0, ∃ η>0, ∃ L₀ q₀ : ℝ, ∀ (n L : ℕ),
    let K : ℝ := (n+2:ℕ)
    let q := K/L
    let T := seamNeighbourhood (SpectralGapMass.Bulk.PeriodicCuts.labels (n:=n) L none)
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    L₀≤(L:ℝ) → q₀≤q → ∀ t : ℝ, t₀≤t → t≤η*L/q →
    μ.real (affordableDraw n ⌊τ*K⌋₊ (5/16) t ∩ drawBounds T (u*K) (v*K) (B*q))≤exp (-c*q) := by
  obtain ⟨C,hC,γ,hγ,hγ₁,hmass⟩ := exists_mass_scales hu hv
  let A := 8*π/u
  let ρ := log (4/3)
  have hA : 0<A := by dsimp only [A]; positivity
  have hρ : 0<ρ := log_pos (by norm_num)
  have hρ₂ : ρ≤log 2 := log_le_log (by norm_num) (by norm_num)
  have hl₂ : 0<log 2 := log_pos (by norm_num)
  obtain ⟨α,hα,U,hU,hsparse⟩ := exists_wire_fraction hA hC
  let τ := α*γ*ρ/(16*log 2)
  let c := γ*ρ/4
  let t₀ := max 1 (96*A/(γ*ρ))
  let η := 1/(32*84*A*B)
  have hτ : 0<τ := by dsimp only [τ]; positivity
  have hc : 0<c := by dsimp only [c]; positivity
  have ht₀ : 0<t₀ := zero_lt_one.trans_le (le_max_left ..)
  have hη : 0<η := by dsimp only [η]; positivity
  refine ⟨τ,hτ,c,hc,t₀,ht₀,η,hη,max (max 1 A) U,max 1 (2/γ),?_⟩
  intro n L K q T μ hL hq t ht hend
  have hL₁ : 1≤(L:ℝ) := (le_max_left ..).trans ((le_max_left ..).trans hL)
  have hAL : A≤(L:ℝ) := (le_max_right ..).trans ((le_max_left ..).trans hL)
  have hUL : U≤(L:ℝ) := (le_max_right ..).trans hL
  have hL' := zero_lt_one.trans_le hL₁
  have hq₁ : 1≤q := (le_max_left ..).trans hq
  have hqp := zero_lt_one.trans_le hq₁
  have ht' := ht₀.trans_le ht
  have ht₁ : 1≤t := (le_max_left ..).trans ht
  have hK : K=q*L := (div_mul_cancel₀ K hL'.ne').symm
  let a := A/(L:ℝ)/t
  let g := ⌊γ*q⌋₊
  let r := ⌊α*(L:ℝ)⌋₊
  let s := ⌊τ*K⌋₊
  let b := (n+1)/L+1
  let k := 2*s/(r+1)
  have ha : 0≤a := div_nonneg (div_nonneg hA.le hL'.le) ht'.le
  have ha₁ : a≤1 := (div_le_one ht').mpr ((div_le_one hL').mpr hAL |>.trans ht₁)
  have hta : t*a=A/L := by dsimp only [a]; field_simp
  have hδ : t^2*a*(84*(B*q))≤1/32 := by
    have hz := (le_div_iff₀ hqp).mp hend
    have hid : t^2*a*(84*(B*q))=(t*q)*(84*A*B)/(L:ℝ) := by
      dsimp only [a]; field_simp; ring
    rw [hid,div_le_iff₀ hL']
    have h := mul_le_mul_of_nonneg_right hz (show 0≤84*A*B by positivity)
    apply h.trans_eq
    dsimp only [η]; field_simp; ring
  have hg₀ : (g:ℝ)≤γ*q := Nat.floor_le (mul_nonneg hγ.le hqp.le)
  have hg₁ : γ*q/2≤(g:ℝ) := by
    have h := (div_le_iff₀ hγ).mp ((le_max_right ..).trans hq)
    linarith only [h,Nat.lt_floor_add_one (γ*q)]
  obtain ⟨hb,hb',_⟩ := packet_number (n:=n) (Nat.cast_pos.mp hL')
  have hb₂ : (b:ℝ)≤2*q := by linarith only [hb',hq₁]
  have hh := bounded_cheap_mass (n:=n) L r s g (Nat.cast_pos.mp hL') ht'.le ha
    (5/16) (u*K) (v*K) (B*q) (m:=u*L/16) (C:=C*sqrt L) (by positivity)
    (mul_pos hC (sqrt_pos.mpr hL'))
  have hcross : π≤2*(t*a)*(u*L/16) := by
    rw [hta]; dsimp only [A]; apply le_of_eq; field_simp; ring
  have htest := hsparse hUL (Nat.floor_le (mul_nonneg hα.le hL'.le))
  have hphysical := hh hcross (by rw [hta]; linarith only [htest,hδ])
    (by rw [hK]; exact hmass hL' hqp hb₂ hg₀ ha ha₁)
  let p := μ.real (affordableDraw n s (5/16) t ∩ drawBounds T (u*K) (v*K) (B*q))
  by_cases hp : 0<p
  · have hdim : Fintype.card (PathLabel n)≤12*(n+2) := by
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; omega
    have hcost := packet_bit_budget hα hL' hτ.le hqp.le (s:=s) (r:=r)
      (by rw [←hK]; exact Nat.floor_le (mul_nonneg hτ.le (show 0≤K by positivity)))
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
      have hd : (Fintype.card (PathLabel n):ℝ)≤12*K := by exact_mod_cast hdim
      apply (mul_le_mul_of_nonneg_right hd ha).trans
      rw [hK]
      have he : 12*(q*L)*a=12*q*A/t := by dsimp only [a]; field_simp; ring
      rw [he,div_le_iff₀ ht']
      nlinarith only [mul_le_mul_of_nonneg_left htime hqp.le]
    have hlog := log_of_packet_count hp ha b _ k g hkb hgb hphysical
    have hprice := mul_le_mul_of_nonneg_right hg₁ hρ.le
    apply (le_of_eq (exp_log hp).symm).trans (exp_le_exp.mpr ?_)
    dsimp only [c]
    linarith only [hlog,hjac,hbit,hprice]
  · exact (le_of_not_gt hp).trans (exp_pos _).le

#print axioms physical_packet_rate
end
end GaloisForLFunctions.HTGeometry.BlockDilations
