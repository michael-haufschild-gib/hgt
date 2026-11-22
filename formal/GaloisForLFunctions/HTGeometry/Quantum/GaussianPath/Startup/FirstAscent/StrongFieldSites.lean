import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.StrongFieldCounts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.FieldScales

/-! # Isolated spins at the Gaussian order-statistic scale -/
open Real MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section

private theorem height_sq (h : ℕ) : fieldHeight h^2 = h*log 2/24 :=
  sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by norm_num))) (by norm_num))

private theorem scale_threshold (c : ℝ) (hc : 0<c) :
    ∃ H : ℕ, ∀ h ≥ H, 1 ≤ h ∧ 1 ≤ c*(4:ℝ)^h ∧ 126 ≤ fieldHeight h := by
  have hl : 0<log 2 := log_pos (by norm_num)
  obtain ⟨a,ha⟩ := exists_nat_ge (24*(126:ℝ)^2/log 2)
  obtain ⟨b,hb⟩ := pow_unbounded_of_one_lt (1/c) (by norm_num : (1:ℝ)<4)
  refine ⟨max 1 (max a b),fun h hh => ⟨(le_max_left ..).trans hh,?_,?_⟩⟩
  · have he := hb.le.trans (pow_le_pow_right₀ (by norm_num) (((le_max_right a b).trans (le_max_right ..)).trans hh))
    simpa only [mul_comm] using (div_le_iff₀ hc).mp he
  · have he : (a:ℝ) ≤ h := by exact_mod_cast (((le_max_left a b).trans (le_max_right ..)).trans hh)
    have hv := (div_le_iff₀ hl).mp (ha.trans he)
    have hf : 0 ≤ fieldHeight h := sqrt_nonneg _
    apply (sq_le_sq₀ (by norm_num) hf).mp
    rw [height_sq]
    linarith only [hv]

private theorem height_lower {N s h : ℕ} (hs : 0<s) (hN : 0<N) (hh : 1 ≤ h)
    (hfit : N ≤ 16*8^(h+1)*s) : sqrt (log ((N:ℝ)/s)) ≤ 18*fieldHeight h := by
  have hs' : 0<(s:ℝ) := by exact_mod_cast hs
  have hN' : 0<(N:ℝ) := by exact_mod_cast hN
  have hratio : (N:ℝ)/s ≤ 16*(8:ℝ)^(h+1) := (div_le_iff₀ hs').mpr (by exact_mod_cast hfit)
  have he := log_le_log (div_pos hN' hs') hratio
  rw [log_mul (by norm_num) (by positivity),log_pow,
    show log 16=4*log 2 by rw [show (16:ℝ)=2^4 by norm_num,log_pow]; norm_num,
    show log 8=3*log 2 by rw [show (8:ℝ)=2^3 by norm_num,log_pow]; norm_num] at he
  have hp : 0 ≤ fieldHeight h := sqrt_nonneg _
  apply sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,height_sq]
  push_cast at he
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
  nlinarith only [he,mul_le_mul_of_nonneg_right hh' hlog,hlog]

/-- For every budget up to a deterministic positive fraction of a long
prefix there are s isolated spins at a common field at least √log(N/s)/18. -/
theorem gaussian_strong_field_sites :
    ∃ M : ℕ, 0<M ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, 0<s → M*s ≤ n+2 → ∃ q : ℝ, 126 ≤ q ∧ sqrt (log (((n+2:ℕ):ℝ)/s)) ≤ 18*q ∧
        ∃ S : Finset (Fin (n+2)), S.card=s ∧
          ∀ v ∈ S, isolatedLongitudinalSite (pathPauliDisorderShell ω n) q 1 v := by
  classical
  obtain ⟨c,hc,hω⟩ := gaussian_strong_field_counts
  obtain ⟨H,hH⟩ := scale_threshold c hc
  refine ⟨16*8^H,by positivity,?_⟩
  filter_upwards [hω] with ω hω
  filter_upwards [tendsto_pairScale.eventually hω] with n hn
  intro s hs hsize
  let j := pairScale n
  obtain ⟨h,hh,hj,hm,hu⟩ := exists_budget_scale hs hsize
  obtain ⟨hh1,hpow,hlarge⟩ := hH h hh
  let q := fieldHeight h
  let A := (Finset.range (8^j)).filter fun i => pathPauliBlock ω i ∈ strongFieldBox q
  have hcount := hn h hj
  change c*(8:ℝ)^j/(2:ℝ)^h ≤ (A.card:ℝ) at hcount
  have hfit : (s:ℝ)*(8:ℝ)^h ≤ (8:ℝ)^j := by exact_mod_cast hm
  have hA' : (s:ℝ) ≤ A.card := by
    apply le_trans _ hcount
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (s:ℝ)*2^h*(c*4^h) := le_mul_of_one_le_right (by positivity) hpow
      _ = c*((s:ℝ)*8^h) := by rw [show (8:ℝ)^h=2^h*4^h by rw [←mul_pow]; norm_num]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfit hc.le
  have hA : s ≤ A.card := by exact_mod_cast hA'
  obtain ⟨T,hTA,hT⟩ := Finset.exists_subset_card_eq hA
  have hm' := (pairScale_bounds n).1
  let g : {i // i∈T} ↪ Fin (n+2) := {
    toFun := fun i => ⟨2*i.val+1,by
      have hi := Finset.mem_range.mp (Finset.mem_filter.mp (hTA i.2)).1
      change 2*8^j ≤ n+2 at hm'
      omega⟩
    inj' := by intro a b e; apply Subtype.ext; have he := congrArg Fin.val e
               change 2*a.val+1=2*b.val+1 at he; omega }
  refine ⟨q,hlarge,height_lower hs (by omega) hh1 hu,T.attach.map g,by simp [hT],?_⟩
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
  apply isolated_odd_site_of_block ω q 1 (j := i.val) rfl
  intro l
  have hl := mem_univ_pi.mp (Finset.mem_filter.mp (hTA i.2)).2 l
  change isolatedFieldBlockCenter q l-1 ≤ _ ∧ _ ≤ isolatedFieldBlockCenter q l+1 at hl
  exact abs_le.mpr ⟨by linarith only [hl.1],by linarith only [hl.2]⟩

#print axioms gaussian_strong_field_sites
end
end GaloisForLFunctions.HTGeometry.FirstAscent
