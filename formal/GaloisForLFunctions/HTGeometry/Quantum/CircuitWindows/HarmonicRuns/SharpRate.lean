import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.PacketCover
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.OffsetTargets

/-! # Sharp joint occupation exponent for consecutive affordable harmonics -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

private theorem cover_fraction {n : ℕ} {I : Type*} [Fintype I] (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    (A : Set ℝ) (ψ : I → (Fin n → Bool) → ℝ) (r : Icc (0:ℝ) (1/2))
    (hA : A ⊆ ⋃ i, shiftedTimes H (ψ i) r) (a b : ℝ)
    (hb : (Fintype.card I:ℝ)*zeroGateArcDensity (2^n) r < b) :
    ∀ᶠ T : ℝ in atTop, volume.real (A ∩ Icc a T)/(T-a) < b := by
  classical
  let S (i : I) := shiftedTimes H (ψ i) r
  have hsum : Tendsto (fun T => ∑ i : I, volume.real (S i ∩ Icc a T)/(T-a)) atTop
      (𝓝 ((Fintype.card I:ℝ)*zeroGateArcDensity (2^n) r)) := by
    simpa [S] using tendsto_finsetSum Finset.univ (fun i _ => shiftedTimes_occupation H hi (ψ i) r a)
  filter_upwards [hsum.eventually_lt_const hb,eventually_gt_atTop a] with T ht hT
  apply lt_of_le_of_lt _ ht
  rw [←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  let B (i : I) := S i ∩ Icc a T
  have hbound : (⋃ i, B i) ⊆ Icc a T := iUnion_subset fun _ => inter_subset_right
  apply (measureReal_mono (s₂ := ⋃ i, B i) _ (measure_ne_top_of_subset hbound measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le B)
  rintro t ⟨ht,hI⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hA ht)
  exact mem_iUnion.mpr ⟨i,hi,hI⟩

/-- The circuit mesh and the angular grid give a finite-prefix asymptotic bound for any gate budget. -/
theorem offset_mesh_bound {n m Q : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (s : ℕ) (hm : 0 < m) (u : Fin m → ℝ)
    {ε δ y γ : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y) (hγ : 0 ≤ γ) (hshort : 3*(y+γ)<1)
    (g : Fin Q → UnitAddCircle) (hg : ∀ z : UnitAddCircle, ∃ i, z-g i ∈ forwardUnitArc γ)
    (hε : ε+δ ≤ zeroGateArcTolerance y) (a b : ℝ)
    (hb : ((Q:ℝ)*(((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s))^m *
      zeroGateArcDensity (2^n) ((y+γ)/(m:ℝ)) < b) :
    ∀ᶠ T : ℝ in atTop, volume.real (offsetRunSet H s ε u ∩ Icc a T)/(T-a) < b := by
  classical
  obtain ⟨F,hcover,hcard⟩ := exists_budget_net n s δ hδ
  obtain ⟨W,hword⟩ := offset_run_subset_words H ε δ u F hcover
  choose ψ hψ using fun f : Fin m → F => itinerary_cover H hm (W f) g hg hy hγ hshort hε
  let J := (Fin m → F) × (Fin m → Fin Q)
  let q (j : J) := ψ j.1 j.2
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  let r : Icc (0:ℝ) (1/2) := ⟨(y+γ)/(m:ℝ),div_nonneg (add_nonneg hy hγ) (Nat.cast_nonneg _),
    (div_le_self (add_nonneg hy hγ) hm1).trans (by linarith only [hshort])⟩
  have hin : offsetRunSet H s ε u ⊆ ⋃ j : J, shiftedTimes H (q j) r := by
    intro t ht
    obtain ⟨f,hf⟩ := mem_iUnion.mp (hword ht)
    obtain ⟨v,hv⟩ := mem_iUnion.mp (hψ f hf)
    exact mem_iUnion.mpr ⟨(f,v),hv⟩
  apply cover_fraction H hi _ q r hin a b
  apply lt_of_le_of_lt _ hb
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg r.2.1 _))
  simp only [J,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
  rw [mul_pow (Q:ℝ) _ m,mul_comm ((Q:ℝ)^m)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard m) (by positivity)

/-- The bound on the original unshifted observation dates. -/
theorem mesh_bound {n m Q : ℕ} (H : selfAdjoint (Register n))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (s : ℕ) (hm : 0 < m)
    {ε δ y γ : ℝ} (hδ : 0 < δ) (hy : 0 ≤ y) (hγ : 0 ≤ γ) (hshort : 3*(y+γ)<1)
    (g : Fin Q → UnitAddCircle) (hg : ∀ z : UnitAddCircle, ∃ i, z-g i ∈ forwardUnitArc γ)
    (hε : ε+δ ≤ zeroGateArcTolerance y) (a b : ℝ)
    (hb : ((Q:ℝ)*(((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s))^m *
      zeroGateArcDensity (2^n) ((y+γ)/(m:ℝ)) < b) :
    ∀ᶠ T : ℝ in atTop, volume.real (circuitRunSet H s m ε ∩ Icc a T)/(T-a) < b := by
  simpa only [offsetRunSet,circuitRunSet,add_zero] using
    offset_mesh_bound H hi s hm (fun _ => 0) hδ hy hγ hshort g hg hε a b hb

private theorem net_entropy (n s m Q : ℕ) {δ : ℝ} (hδ : 0 < δ) (hs : s ≤ 2^n) :
    ((Q:ℝ)*(((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s))^m ≤
      Real.exp (((Q:ℝ)+(36+128/δ))*((n:ℝ)+1)*((m*(s+1):ℕ)+1:ℝ)) := by
  let C : ℝ := 36+128/δ
  let P : ℝ := ((n:ℝ)+1)*((s:ℝ)+1)
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le (by linarith only [Nat.cast_nonneg (α := ℝ) n])
    (by linarith only [Nat.cast_nonneg (α := ℝ) s])
  have hQ : (Q:ℝ) ≤ Real.exp Q := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hh := net_envelope_le_exp n s δ hδ hs
  have hnet := mul_le_mul hQ hh (by positivity) (Real.exp_pos _).le
  rw [←Real.exp_add] at hnet
  apply (pow_le_pow_left₀ (by positivity) hnet m).trans
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hq := le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) Q) hP
  have he : (Q:ℝ)+C*((n:ℝ)+1)*((s:ℝ)+1) ≤ ((Q:ℝ)+C)*P := by
    dsimp only [P] at *
    nlinarith only [hq]
  apply (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg m)).trans
  change (m:ℝ)*(((Q:ℝ)+C)*P) ≤ ((Q:ℝ)+C)*((n:ℝ)+1)*_
  push_cast
  have hc : 0 ≤ ((Q:ℝ)+C)*((n:ℝ)+1) := by dsimp [C]; positivity
  dsimp only [P]
  nlinarith only [hc]

/-- The fraction of m-term runs, multiplied by m^(D−1), has the same
sharp exponential rate as one affordable visit when m(s+1)=o(D/N). -/
theorem gaussian_sharp_run_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s m : ℕ → ℕ, (∀ n, 0 < m n) →
      subcriticalBudget (fun n => m n*(s n+1)) → ∀ x ∈ Ioo (0:ℝ) (1/3),
      ∀ l b : ℝ, 0 ≤ l → l < x → x < b → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let M := m N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          let f := volume.real (circuitRunSet H (s N) M (zeroGateArcTolerance x) ∩ Icc a T)/(T-a)
          l^D/(M:ℝ)^(D-1) < f ∧ f < b^D/(M:ℝ)^(D-1) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro s m hm hs x hx l b hl hlx hxb
  obtain ⟨z,hxz,hz⟩ := exists_between (lt_min hxb hx.2)
  obtain ⟨y,hxy,hyz⟩ := exists_between hxz
  have hzb := hz.trans_le (min_le_left ..)
  have hzthird := hz.trans_le (min_le_right ..)
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  let γ := z-y
  have hγ : 0 < γ := sub_pos.mpr hyz
  have hsum : y+γ = z := by dsimp [γ]; ring
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance
    ⟨hx.1.le,by linarith only [hx.2]⟩ ⟨(hx.1.trans hxy).le,by linarith only [hyz,hzthird]⟩ hxy)
  obtain ⟨Q,g,hg⟩ := finite_forward_grid hγ
  have he := enlarged_arc_eventually_lt hs ((Q:ℝ)+(36+128/δ)) z b (hx.1.trans hxz) hzb
  filter_upwards [(tendsto_add_atTop_nat 3).eventually (he.and (budget_le_dimension_eventually hs))]
    with k hk
  intro N D M H a
  have hM : 0 < M := hm N
  have hM' : 0 < (M:ℝ) := Nat.cast_pos.mpr hM
  have hD : 0 < D := by dsimp [D]; positivity
  have hsn : s N ≤ D := (Nat.le_succ _).trans ((Nat.le_mul_of_pos_left _ hM).trans hk.2)
  have hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues := hω k
  have hhigh := mesh_bound H hi (s N) hM hδ (hx.1.trans hxy).le hγ.le
    (by rw [hsum]; linarith only [hzthird]) g hg (by dsimp [δ]; linarith : zeroGateArcTolerance x+δ ≤ _)
    a (b^D/(M:ℝ)^(D-1)) (by
      simp only [hsum,zeroGateArcDensity,div_pow,←mul_div_assoc]
      apply (div_lt_div_iff_of_pos_right (pow_pos hM' _)).mpr
      apply (mul_le_mul_of_nonneg_right (net_entropy N (s N) M Q hδ hsn)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx.1.trans hxz).le _))).trans_lt
      simpa only [N,D,M,Nat.cast_pow,Nat.cast_ofNat] using hk.1)
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  let r : Icc (0:ℝ) (1/2) := ⟨x/(M:ℝ),div_nonneg hx.1.le hM'.le,
    (div_le_self hx.1.le hM1).trans (by linarith only [hx.2])⟩
  have hin : zeroGateReturnSet H r ⊆ circuitRunSet H (s N) M (zeroGateArcTolerance x) := by
    rw [show zeroGateReturnSet H r = runSet H (zeroGateArcTolerance x) M from
      (runSet_eq H hx.1.le (by linarith only [hx.2]) M hM).symm]
    intro t ht i
    obtain ⟨c,hc,C,hC,herr⟩ := ht (i.val+1) i.isLt
    exact ⟨c,hc,C,hC.trans (Nat.zero_le _),by simpa only [Nat.cast_add_one] using herr⟩
  have hlo : l^D/(M:ℝ)^(D-1) < zeroGateArcDensity D r := by
    simp only [r,zeroGateArcDensity,div_pow,←mul_div_assoc]
    apply (div_lt_div_iff_of_pos_right (pow_pos hM' _)).mpr
    apply (pow_lt_pow_left₀ hlx hl hD.ne').trans_le
    rw [show x^D = x*x^(D-1) by rw [←pow_succ',Nat.sub_add_cancel hD]]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx.1.le _)
    exact (by linarith only [hx.2] : x ≤ 1).trans (by exact_mod_cast hD)
  have hlow := (maximallyProjective_zeroGateOccupation_from_start H hi r a).eventually_const_lt hlo
  filter_upwards [hlow,hhigh,eventually_gt_atTop a] with T hlow hhigh hT
  refine ⟨hlow.trans_le ?_,hhigh⟩
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  exact measureReal_mono (inter_subset_inter_left _ hin) (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

#print axioms gaussian_sharp_run_rate
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
