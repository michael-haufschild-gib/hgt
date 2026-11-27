import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.RampWindows.SparseReadings.Dilation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalHorizon

/-! # Extensive circuit cost on prescribed observations of the frozen chain -/

open MeasureTheory Filter Real Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows.SparseReadings
open PrescribedTimes PrescribedTimes.ShortWindows
noncomputable section

private theorem dimension_bound (k : ℕ) :
    (Fintype.card (PrefixIndex (k+1)):ℝ) ≤ 16*((k+3:ℕ):ℝ) := by
  rw [Fintype.card_congr (pathCoeffEquiv (k+1))]
  simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  push_cast
  linarith only [Nat.cast_nonneg (α:=ℝ) k]

/-- The reciprocal number of separated dilations has one contribution from
Gaussian density change and one from the length of the forbidden lag band. -/
private theorem window_mass {k s : ℕ} (P : Option ℕ) {g T w l H : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hH : 0 < H) (hw : 0≤w) (hl : l ≤ g/2-2*w) (hh : 4*w ≤ H) :
    let K : ℝ := (k+3:ℕ)
    pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
      (visit (k+1) s P T w \ cheapLag (k+1) s l H)) ≤
      2*exp 1*(16*K*g/T+2*g/H) := by
  intro K
  let b := 16*K*g/T+2*g/H
  have hK : 1 ≤ K := by
    change (1:ℝ) ≤ ((k+3:ℕ):ℝ)
    exact_mod_cast (show 1 ≤ k+3 by omega)
  have hb₁ : 16*K*g/T ≤ b := le_add_of_nonneg_right (by positivity)
  have hb₂ : 2*g/H ≤ b := le_add_of_nonneg_left (by positivity : 0 ≤ 16*K*g/T)
  have hb : 0 < b := (div_pos (mul_pos two_pos hg) hH).trans_le hb₂
  have he : 1 ≤ exp 1 := Real.one_le_exp (by norm_num)
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  by_cases hsmall : 2 ≤ 1/b
  · let m := ⌊1/b⌋₊
    have hfloor : (m:ℝ) ≤ 1/b := Nat.floor_le (by positivity)
    have hnext : 1/b < (m:ℝ)+1 := Nat.lt_floor_add_one _
    have hm : 0 < m := Nat.floor_pos.mpr (by linarith only [hsmall])
    have hm0 : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
    have hmb : (m:ℝ)*b ≤ 1 := (le_div_iff₀ hb).mp hfloor
    have htime : (m:ℝ)*(16*K*g) ≤ T := by
      have h := (mul_le_mul_of_nonneg_left hb₁ (Nat.cast_nonneg m)).trans hmb
      rwa [←mul_div_assoc,div_le_one hT] at h
    have hspan : (m:ℝ)*g ≤ T := by
      have hbig : g ≤ 16*K*g := le_mul_of_one_le_left hg.le (by linarith only [hK])
      exact (mul_le_mul_of_nonneg_left hbig (Nat.cast_nonneg _)).trans htime
    have hprice : (Fintype.card (PrefixIndex (k+1)):ℝ)*((m:ℝ)*g) ≤ T := calc
      _ ≤ (16*K)*((m:ℝ)*g) := mul_le_mul_of_nonneg_right (dimension_bound k) (by positivity)
      _ = (m:ℝ)*(16*K*g) := by ring
      _ ≤ T := htime
    have hband : (m:ℝ)*g+2*w ≤ H := by
      have h := (mul_le_mul_of_nonneg_left hb₂ (Nat.cast_nonneg m)).trans hmb
      rw [←mul_div_assoc,div_le_one hH] at h
      linarith only [h,hh]
    have hlarge : 1 ≤ (2*(m:ℝ))*b :=
      (div_le_iff₀ hb).mp (by linarith only [hsmall,hnext] : 1/b ≤ 2*(m:ℝ))
    apply (window_grid_mass P hm hg.le hT hspan hprice hw hl hband).trans
    apply (div_le_iff₀ hm0).mpr
    change exp 1 ≤ 2*exp 1*b*(m:ℝ)
    linarith only [mul_le_mul_of_nonneg_left hlarge (exp_pos 1).le]
  · have hlarge := (div_lt_iff₀ hb).mp (lt_of_not_ge hsmall)
    apply measureReal_le_one.trans
    change 1 ≤ 2*exp 1*b
    have hbig : 1 ≤ 2*b := by linarith only [hlarge]
    linarith only [mul_le_mul_of_nonneg_left hbig (exp_pos 1).le,he]

private theorem lag_exception {κ A δ : ℝ} (hκ : 0<κ) (hA : 0 < A)
    (h : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ t : ℝ, A≤K*|t| → |t|≤δ*K^(65/64:ℝ) → ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → κ*K<(s:ℝ)) :
    let B (k : ℕ) := let K : ℝ := (k+3:ℕ)
      prefixPoint k ⁻¹' cheapLag (k+1) ⌊(κ/2)*K⌋₊ (A/K) (δ*K^(65/64:ℝ))
    Tendsto (fun k => pathPauliDisorderLaw.real (B k)) atTop (𝓝 0) := by
  intro B
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  apply probability_vanishes _ B (fun k => (measurable_cheapLag ..).preimage
    (gaussian_pauli_prefix_coordinates_law (k+1)).measurable)
  filter_upwards [h] with ω hω
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω] with k hk
  let K : ℝ := (k+3:ℕ)
  have hK : 0 < K := by dsimp [K]; positivity
  let s := ⌊(κ/2)*K⌋₊
  have hs : (s:ℝ) ≤ (κ/2)*K := Nat.floor_le (by positivity)
  rintro ⟨t,ht,hc⟩
  have ht0 := (div_pos hA hK).le.trans ht.1
  have hlow := (div_le_iff₀ hK).mp ht.1
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr hc
  rw [show numberedGenerator (k+1) (prefixPoint k ω)=pathHamiltonian (pathPauliDisorderShell ω (k+1))
    from numberedGenerator_shell _] at hfit
  have hcost := hk t (by rw [abs_of_nonneg ht0,mul_comm]; exact hlow)
    (by rw [abs_of_nonneg ht0]; exact ht.2) (s+s) hfit
  change κ*K < ((s+s:ℕ):ℝ) at hcost
  push_cast at hcost
  linarith only [hs,hcost]

/-- At error 1/8, a collection of inverse-size windows costs one exceptional
disorder probability plus the sum of the individual dilation bounds. Origins
and delays may vary across the collection. The constants are uniform in them. -/
theorem gaussian_sparse_readings :
    ∃ c>0, ∃ C>0, ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
      let K : ℝ := (k+3:ℕ)
      ∀ (J : ℕ) (P : Fin J → Option ℕ) (T : Fin J → ℝ), (∀ i, 0 < T i) →
        pathPauliDisorderLaw.real (⋃ i, prefixPoint k ⁻¹'
          visit (k+1) ⌊c*K⌋₊ (P i) (T i) K⁻¹) ≤
        r k+C*∑ i, ((T i)⁻¹+(K*K^(65/64:ℝ))⁻¹) := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,h⟩ := BlockDilations.AdaptiveCuts.gaussian_superlinear_from_startup
  let K (k : ℕ) : ℝ := (k+3:ℕ)
  let B (k : ℕ) := cheapLag (k+1) ⌊(κ/2)*K k⌋₊ (A/K k) (δ*(K k)^(65/64:ℝ))
  let q := 2*A+4
  let C := 2*exp 1*(16*q+2*q/δ)
  refine ⟨κ/2,by positivity,C,by dsimp [C,q]; positivity,
    fun k => pathPauliDisorderLaw.real (prefixPoint k ⁻¹' B k),lag_exception hκ hA h,?_⟩
  have hKlim : Tendsto K atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  filter_upwards [hKlim.eventually_ge_atTop (4/δ)] with k hk
  intro N J P T hT
  have hn : 1 ≤ N := by
    change (1:ℝ) ≤ ((k+3:ℕ):ℝ)
    exact_mod_cast (show 1 ≤ k+3 by omega)
  have hn0 := zero_lt_one.trans_le hn
  have hq : 0 < q := by dsimp [q]; positivity
  let H := δ*N^(65/64:ℝ)
  have hH : 0 < H := mul_pos hδ (rpow_pos_of_pos hn0 _)
  have hpow : N ≤ N^(65/64:ℝ) := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hn (by norm_num : (1:ℝ) ≤ 65/64)
  have hδN : 4 ≤ δ*N := by
    rw [mul_comm]; exact (div_le_iff₀ hδ).mp hk
  have hwide : 4*N⁻¹ ≤ H := calc
    _ ≤ 4*1 := mul_le_mul_of_nonneg_left ((inv_le_one₀ hn0).mpr hn) (by norm_num)
    _ ≤ δ*N := by simpa using hδN
    _ ≤ H := mul_le_mul_of_nonneg_left hpow hδ.le
  let E (i : Fin J) := visit (k+1) ⌊(κ/2)*N⌋₊ (P i) (T i) N⁻¹
  let b := prefixPoint k ⁻¹' B k
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hcost (i : Fin J) : pathPauliDisorderLaw.real (prefixPoint k ⁻¹' (E i \ B k)) ≤
      C*((T i)⁻¹+(N*N^(65/64:ℝ))⁻¹) := by
    have hlo : A/N ≤ (q/N)/2-2*N⁻¹ := by
      apply le_of_eq
      dsimp [q]
      simp only [div_eq_mul_inv]
      ring
    have hb := window_mass (k:=k) (s:=⌊(κ/2)*N⌋₊) (P i) (div_pos hq hn0) (hT i) hH
      (inv_nonneg.mpr hn0.le) hlo hwide
    apply hb.trans
    change 2*exp 1*(16*N*(q/N)/T i+2*(q/N)/H) ≤ _
    have heq : 16*N*(q/N)/T i+2*(q/N)/H =
        (16*q)*(T i)⁻¹+(2*q/δ)*(N*N^(65/64:ℝ))⁻¹ := by
      dsimp [H]
      field_simp [hn0.ne',hδ.ne',(hT i).ne', (rpow_pos_of_pos hn0 (65/64:ℝ)).ne']
    rw [heq]
    dsimp only [C]
    rw [mul_assoc (2*exp 1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h₁ : 0 ≤ (16*q)*(N*N^(65/64:ℝ))⁻¹ := by positivity
    have h₂ := mul_nonneg (show 0≤2*q/δ by positivity) (inv_nonneg.mpr (hT i).le)
    linarith only [h₁,h₂]
  have hsub : (⋃ i, prefixPoint k ⁻¹' E i) ⊆ b ∪ ⋃ i, prefixPoint k ⁻¹' (E i \ B k) := by
    intro ω hω
    by_cases hb : ω∈b
    · exact Or.inl hb
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hω
      exact Or.inr (mem_iUnion.mpr ⟨i,hi,hb⟩)
  apply (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  apply add_le_add le_rfl
  rw [Finset.mul_sum]
  exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ => hcost i)

/-- Any quadratic number of inverse-size observation windows beyond cubic time
simultaneously require an extensive circuit, with probability tending to one.
The delays have no upper bound. -/
theorem gaussian_quadratic_observations :
    ∃ c>0, ∀ (P : (k : ℕ) → Fin ((k+3)^2) → Option ℕ)
      (T : (k : ℕ) → Fin ((k+3)^2) → ℝ),
      (∀ k i, ((k+3:ℕ):ℝ)^3 ≤ T k i) →
      Tendsto (fun k => let K : ℝ := (k+3:ℕ)
        pathPauliDisorderLaw.real (⋃ i, prefixPoint k ⁻¹'
          visit (k+1) ⌊c*K⌋₊ (P k i) (T k i) K⁻¹)) atTop (𝓝 0) := by
  obtain ⟨c,hc,C,hC,r,hr,hs⟩ := gaussian_sparse_readings
  refine ⟨c,hc,fun P T hT => ?_⟩
  let K (k : ℕ) : ℝ := (k+3:ℕ)
  have hlim : Tendsto K atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hi := tendsto_inv_atTop_zero.comp hlim
  have hj := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/64)).comp hlim)
  have hb : Tendsto (fun k => r k+C*((K k)⁻¹+((K k)^(1/64:ℝ))⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,add_zero,mul_zero] using hr.add ((hi.add hj).const_mul C)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hb
  filter_upwards [hs] with k hk
  let N := K k
  have hn : 0 < N := by dsimp [N,K]; positivity
  have hp : N^(65/64:ℝ)=N*N^(1/64:ℝ) := by
    rw [show (65/64:ℝ)=1+1/64 by norm_num,rpow_add hn,rpow_one]
  have ht (i) : 0 < T k i := (pow_pos hn 3).trans_le (hT k i)
  apply (hk _ (P k) (T k) ht).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left _ hC.le))
  calc
    _ ≤ ∑ _ : Fin ((k+3)^2), ((N^3)⁻¹+(N*N^(65/64:ℝ))⁻¹) :=
      Finset.sum_le_sum fun i _ => add_le_add ((inv_le_inv₀ (ht i) (pow_pos hn 3)).mpr (hT k i)) le_rfl
    _ = N⁻¹+(N^(1/64:ℝ))⁻¹ := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,hp]
      change N^2*((N^3)⁻¹+(N*(N*N^(1/64:ℝ)))⁻¹)=_
      field_simp [hn.ne',(rpow_pos_of_pos hn (1/64:ℝ)).ne']

#print axioms gaussian_quadratic_observations
#print axioms gaussian_sparse_readings
end
end GaloisForLFunctions.HTGeometry.LocalPatches.RampWindows.SparseReadings
