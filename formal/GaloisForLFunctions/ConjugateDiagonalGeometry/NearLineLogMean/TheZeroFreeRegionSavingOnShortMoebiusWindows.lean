import GaloisForLFunctions.RHTower.MobiusCubicSourceMertensEnergy
import GaloisForLFunctions.RHTower.MobiusCoprimeSignatureRH
import GaloisForLFunctions.RHTower.MobiusWeightedLineEnergyExponentLaw
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PoissonEnergyOfTheMertensPrefixes

/-!
# Cancellation for Möbius sections on short vertical windows

The zero-free-region saving for the summatory Möbius function survives
Abel summation at every fixed real part strictly between zero and one.
The weighted sum is the discrete upper bound corresponding to the
Karamata integral estimate of Fino and Majdoub, Lemma 2.1(K2).
At real part one half this makes the signed second moment sublinear in
length throughout a growing stretched-exponential range of ordinates.
-/
noncomputable section
open Finset Filter Complex MeasureTheory Topology
open _root_.RHTower _root_.RHTower.CubicGamma
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- The full summatory saving survives passage to a Dirichlet section.
The constant is uniform in both the frequency and the cutoff. -/
theorem mertens_section_strip_saving {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (s : ℂ), s.re = σ →
      ‖edPoly mobCoeff (Icc 1 N) s‖ ≤
        C*(1+‖s‖)*(N:ℝ)^(1-σ)*mertensSaving N := by
  obtain ⟨B,hB,hM⟩ := exists_abs_abelMertens_le
  obtain ⟨K,hK,hweights⟩ := sum_rpow_neg_mul_mertensSaving_le h0 h1
  refine ⟨B*(1+K),by positivity,fun N hN s hs => ?_⟩
  let E := fun n : ℕ => (n:ℝ)^(-σ)*mertensSaving n
  have epos (n : ℕ) : 0 ≤ E n :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (mertensSaving_pos _).le
  have bound (k : ℕ) (hk : 1 ≤ k) :
      ‖mobiusMertensPartialSum k‖ ≤ B*k*mertensSaving k := by
    rw [mobiusMertensPartialSum_eq_sieveMertensM,Complex.norm_real,Real.norm_eq_abs,
      ←abelMertens_eq_mertensM]
    exact hM k hk
  have xp : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have pp (x : ℝ) (hx : 0 < x) (p : ℝ) : x^p*x=x^(p+1) := by
    rw [Real.rpow_add hx,Real.rpow_one]
  have left : ‖(((N:ℝ):ℂ)^(-s))*mobiusMertensPartialSum N‖ ≤
      B*(N:ℝ)^(1-σ)*mertensSaving N := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos xp,Complex.neg_re,hs]
    refine (mul_le_mul_of_nonneg_left (bound N hN) (Real.rpow_nonneg xp.le _)).trans_eq ?_
    calc (N:ℝ)^(-σ)*(B*N*mertensSaving N) =
          B*((N:ℝ)^(-σ)*(N:ℝ))*mertensSaving N := by ring
         _ = _ := by rw [pp _ xp,show -σ+1=1-σ by ring]
  let g := fun k : ℕ => mobCoeff (k+1)
  have head (k : ℕ) : coeffPartial g k=mobiusMertensPartialSum k :=
    sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum k
  have row (i : ℕ) : ‖coeffPartial g (i+1) *
      (((((i:ℝ)+1):ℝ):ℂ)^(-s)-((((i:ℝ)+2):ℝ):ℂ)^(-s))‖ ≤
      (B*‖s‖)*E (i+1) := by
    let x := (i:ℝ)+1
    have hx : 0 < x := by dsimp [x]; positivity
    have diff := _root_.RHTower.norm_cpow_shift_sub_le_of_nonneg
      (x:=x) (b:=1) hx zero_le_one (by rwa [hs] : 0 < s.re)
    rw [show x+1=(i:ℝ)+2 by dsimp [x]; ring,mul_one,hs,norm_sub_rev] at diff
    have hk := bound (i+1) (by omega)
    rw [Nat.cast_succ] at hk
    rw [norm_mul,head]
    refine (mul_le_mul hk diff (norm_nonneg _) ((norm_nonneg _).trans hk)).trans_eq ?_
    dsimp only [E]
    simp only [Nat.cast_succ]
    change B*x*mertensSaving x*(‖s‖*x^(-σ-1)) = B*‖s‖*(x^(-σ)*mertensSaving x)
    calc _ = B*‖s‖*((x^(-σ-1)*x)*mertensSaving x) := by ring
         _ = _ := by rw [pp _ hx,sub_add_cancel]
  have he := hweights N hN
  rw [_root_.RHTower.sum_Icc_eq_sum_range_shift] at he
  have he' : ∑ i ∈ range (N-1), E (i+1) ≤ K*(N:ℝ)^(1-σ)*mertensSaving N :=
    (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.sub_le N 1))
      (fun i _ _ => epos (i+1))).trans he
  have right := (norm_sum_le _ _).trans (sum_le_sum (s:=range (N-1)) (fun i _ => row i))
  rw [←mul_sum] at right
  rw [edPoly_mobCoeff_Icc_eq_sum_range]
  simp only [smul_eq_mul]
  rw [sum_eq_abelPartial g s N,head]
  refine (norm_add_le _ _).trans ((add_le_add left
    (right.trans (mul_le_mul_of_nonneg_left he' (by positivity)))).trans ?_)
  have hp := Real.rpow_nonneg xp.le (1-σ)
  have hE := (mertensSaving_pos (N:ℝ)).le
  have p1 := mul_nonneg (mul_nonneg (mul_nonneg hB.le hK.le) hp) hE
  have p2 := mul_nonneg (mul_nonneg (mul_nonneg hB.le (norm_nonneg s)) hp) hE
  linarith only [p1,p2]

private theorem square_saving_sum :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ Icc 1 N, (mertensSaving k)^2 ≤ D*N*(mertensSaving N)^2 := by
  obtain ⟨K,hK,hs⟩ := mertensSaving_slow (η:=1/2) (by norm_num)
  obtain ⟨C,hC,hc⟩ := sum_rpow_neg_mul_mertensSaving_le (s:=1/2) (by norm_num) (by norm_num)
  refine ⟨K*C,mul_pos hK hC,fun N hN => ?_⟩
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let A := K*mertensSaving N*(N:ℝ)^((1:ℝ)/2)
  have ha : 0 ≤ A := mul_nonneg (mul_nonneg hK.le (mertensSaving_pos _).le) (Real.rpow_nonneg hn.le _)
  have row (k : ℕ) (hk : k ∈ Icc 1 N) :
      (mertensSaving k)^2 ≤ A*((k:ℝ)^(-(1/2:ℝ))*mertensSaving k) := by
    obtain ⟨hk1,hkN⟩ := mem_Icc.mp hk
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hk1
    have h := hs k N (Nat.one_le_cast.mpr hk1) (Nat.cast_le.mpr hkN)
    rw [Real.div_rpow hn.le hk'.le,div_eq_mul_inv,←Real.rpow_neg hk'.le] at h
    rw [sq]
    exact (mul_le_mul_of_nonneg_right h (mertensSaving_pos _).le).trans_eq (by dsimp only [A]; ring)
  have he : (N:ℝ)^((1:ℝ)/2)*(N:ℝ)^(1-1/2:ℝ) = N := by
    rw [←Real.rpow_add hn]; norm_num
  have h := sum_le_sum row
  rw [←mul_sum] at h
  refine h.trans ((mul_le_mul_of_nonneg_left (hc N hN) ha).trans_eq ?_)
  calc _ = K*C*((N:ℝ)^((1:ℝ)/2)*(N:ℝ)^(1-1/2:ℝ))*(mertensSaving N)^2 := by dsimp only [A]; ring
       _ = _ := by rw [he]

/-- Squaring the Mertens estimate inside the exact positive prefix
decomposition preserves two copies of the zero-free-region saving. -/
theorem mertens_gram_zero_free_region_saving :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 1 ≤ N →
      mertensPoissonGram N ≤ D*N*(mertensSaving N)^2 := by
  obtain ⟨B,hB,hM⟩ := exists_abs_abelMertens_le
  obtain ⟨K,hK,hE⟩ := square_saving_sum
  refine ⟨B^2*(1+K),by positivity,fun N hN => ?_⟩
  have bound (k : ℕ) (hk : 1 ≤ k) :
      ‖mobiusMertensPartialSum k‖^2 ≤ (B*k*mertensSaving k)^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [mobiusMertensPartialSum_eq_sieveMertensM,Complex.norm_real,Real.norm_eq_abs,
      ←abelMertens_eq_mertensM]
    exact hM k hk
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have ht := div_le_div_of_nonneg_right (bound N hN) hn.le
  have hterm : ‖mobiusMertensPartialSum N‖^2/(N:ℝ) ≤ B^2*N*(mertensSaving N)^2 :=
    ht.trans_eq (by field_simp)
  have row (k : ℕ) (hk : k ∈ Icc 1 (N-1)) :
      ((k:ℝ)⁻¹-((k:ℝ)+1)⁻¹)*‖mobiusMertensPartialSum k‖^2 ≤ B^2*(mertensSaving k)^2 := by
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    have hk1 : 0 < (k:ℝ)+1 := by positivity
    have hw : (k:ℝ)⁻¹ - ((k:ℝ)+1)⁻¹ = (1/(k:ℝ))/((k:ℝ)+1) := by
      field_simp; ring
    rw [hw]
    refine (mul_le_mul_of_nonneg_left (bound k (mem_Icc.mp hk).1) (by positivity)).trans ?_
    calc _ = (B^2*(mertensSaving k)^2)*((k:ℝ)/((k:ℝ)+1)) := by field_simp
         _ ≤ _ := mul_le_of_le_one_right (by positivity)
           ((div_le_one hk1).mpr (le_add_of_nonneg_right zero_le_one))
  have hs := sum_le_sum row
  rw [←mul_sum] at hs
  have hsub : Icc 1 (N-1) ⊆ Icc 1 N := Icc_subset_Icc_right (Nat.sub_le _ _)
  have hs' := (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => sq_nonneg (mertensSaving k))).trans (hE N hN)
  rw [mertens_gram_prefix_squares hN]
  exact (add_le_add hterm (hs.trans (mul_le_mul_of_nonneg_left hs' (sq_nonneg B)))).trans_eq (by ring)

/-- A fixed Poisson kernel pays only quadratic height on a sharp
window. Its exact arithmetic energy supplies the squared saving. -/
theorem signed_moebius_window_saving :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2) ≤
        D*T^2*N*(mertensSaving N)^2 := by
  obtain ⟨K,hK,h⟩ := mertens_gram_zero_free_region_saving
  refine ⟨4*Real.pi*K,by positivity,fun N hN T hT => ?_⟩
  have hbase := sharp_moebius_moment_le_mertens_gram N hT
  simp only [edPoly_moebiusMollifierCoeff_eq_moebiusPoly] at hbase
  exact hbase.trans
    ((mul_le_mul_of_nonneg_left (h N hN) (by positivity)).trans_eq (by ring))

/-- Throughout a stretched-exponential window the signed energy,
divided by the length N, tends to zero uniformly in the final height. -/
theorem signed_moebius_sublinear_on_growing_windows {a : ℝ} (ha : a < 1) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, 1 ≤ T →
      T ≤ Real.exp (a*(Real.log N)^((1:ℝ)/3)/108) →
      (∫ t in (1:ℝ)..T, ‖moebiusPoly N (MultiscaleMollifiedZetaField.linePoint t)‖^2) ≤ ε*N := by
  obtain ⟨D,hD,h⟩ := signed_moebius_window_saving
  let u := fun N : ℕ => (Real.log N)^((1:ℝ)/3)/108
  have hu : Tendsto u atTop atTop := (Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ)<108)
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)))
  have hg := hu.const_mul_atTop (by linarith only [ha] : 0 < 2-2*a)
  have hlim := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hg).const_mul D
  rw [mul_zero] at hlim
  intro ε hε
  filter_upwards [hlim.eventually_lt_const hε,eventually_ge_atTop 1] with N hsmall hN T hT ht
  have hs := h N hN T hT
  have he : (Real.exp (a*(u N)))^2*(mertensSaving N)^2 =
      Real.exp (-((2-2*a)*u N)) := by
    change (Real.exp (a*u N))^2*(Real.exp (-(u N)))^2=_
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1; push_cast; ring
  have ht' : T ≤ Real.exp (a*u N) := by simpa only [u,mul_div_assoc] using ht
  have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hT) ht' 2)
    (sq_nonneg (mertensSaving N))
  rw [he] at hc
  change D*Real.exp (-((2-2*a)*u N)) < ε at hsmall
  have hw := (mul_le_mul_of_nonneg_left hc hD.le).trans hsmall.le
  calc _ ≤ D*T^2*N*(mertensSaving N)^2 := hs
       _ = (D*(T^2*(mertensSaving N)^2))*N := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg N)

#print axioms mertens_section_strip_saving
#print axioms mertens_gram_zero_free_region_saving
#print axioms signed_moebius_window_saving
#print axioms signed_moebius_sublinear_on_growing_windows
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
