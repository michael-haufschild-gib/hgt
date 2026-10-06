import GaloisForLFunctions.RHTower.Sieve.SecondDerivativeTest
import GaloisForLFunctions.RHTower.ChiPhysicalMatrixMultiplier
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicSharpEdges

/-!
# Cancellation of the allowed prime collision in the Gaussian cubic

The original cubic excludes p=r and q=r, but retains p=q≠r. This whole
remaining collision sector has complex norm o(N/log²N), without an
analytic premise. Complete quadratic integer correlations and a Schur
bound control the matrix exp(2πi p²/r); prime restrictions remain in its
coefficients. The actual physical logarithmic Schwartz multiplier keeps
the original W window, and the all-equal diagonal costs only a constant.

The pairwise-distinct cubic and the complete global defect cancellation
remain separate mathematical obligations.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter GaloisForLFunctions.RHTower
open scoped BigOperators Topology InnerProductSpace
namespace RHTower.BAGTrace

private theorem quadratic_correlation {N : ℕ} (hN : 1≤N)
    {r s : ℝ} (hr : r∈Icc (N : ℝ) (2*N))
    (hs : s∈Icc (N : ℝ) (2*N)) (hrs : r<s) :
    ‖∑ j∈Finset.range (N+1),Complex.exp
      (((2*Real.pi*((s-r)/(r*s))*((N : ℝ)+j)^2 : ℝ) : ℂ)*I)‖≤
        96*(N : ℝ)/Real.sqrt (s-r) := by
  have hn : (1 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)<N := by linarith
  have hr0 : 0<r := hn0.trans_le hr.1
  have hs0 : 0<s := hn0.trans_le hs.1
  have hd : 0<s-r := sub_pos.mpr hrs
  have hdN : s-r≤N := by linarith [hr.1,hs.2]
  have hprod0 : 0<r*s := mul_pos hr0 hs0
  have hlo : (N : ℝ)^2≤r*s := by nlinarith [mul_le_mul hr.1 hs.1 hn0.le hr0.le]
  have hhi : r*s≤4*(N : ℝ)^2 := by nlinarith [mul_le_mul hr.2 hs.2 hs0.le (by positivity : (0 : ℝ)≤2*N)]
  let a : ℝ := (s-r)/(r*s)
  let lam : ℝ := (s-r)/(4*(N : ℝ)^2)
  have hl0 : 0<lam := by dsimp [lam]; positivity
  have hl1 : lam≤1 := by
    dsimp only [lam]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*(N : ℝ)^2)).2
    nlinarith
  have hcurvLo : lam≤2*a := by
    dsimp only [lam,a]
    rw [show 2*((s-r)/(r*s))=(2*(s-r))/(r*s) by ring]
    apply (div_le_div_iff₀ (by positivity) hprod0).2
    nlinarith [mul_le_mul_of_nonneg_left hhi hd.le]
  have hcurvHi : 2*a≤8*lam := by
    dsimp only [lam,a]
    rw [show 2*((s-r)/(r*s))=(2*(s-r))/(r*s) by ring,
      show 8*((s-r)/(4*(N : ℝ)^2))=(2*(s-r))/(N : ℝ)^2 by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlo
  have hb := Sieve.second_derivative_test'
    (fun x : ℝ => a*x^2) (fun x : ℝ => 2*a*x) (fun _ : ℝ => 2*a)
    (N : ℝ) (N+1) (by omega) hl0 hl1
    (fun x _ => by
      convert! ((hasDerivAt_id x).pow 2).const_mul a using 1
      simp only [id_eq,mul_one]
      ring)
    (fun x _ => by
      simpa only [id_eq,mul_one] using! (hasDerivAt_id x).const_mul (2*a))
    (fun _ _ => hcurvLo) (fun _ _ => hcurvHi)
  have hroot : Real.sqrt lam=Real.sqrt (s-r)/(2*(N : ℝ)) := by
    dsimp only [lam]
    rw [Real.sqrt_div hd.le,show 4*(N : ℝ)^2=(2*(N : ℝ))^2 by ring,
      Real.sqrt_sq (by positivity)]
  have hterm (j : ℕ) : 2*Real.pi*(a*((N : ℝ)+j)^2)=
      2*Real.pi*((s-r)/(r*s))*((N : ℝ)+j)^2 := by dsimp only [a];ring
  simp only [hterm] at hb
  rw [hroot] at hb
  have hdroot : 0<Real.sqrt (s-r) := Real.sqrt_pos.mpr hd
  have hsmall : Real.sqrt (s-r)≤(N : ℝ)/Real.sqrt (s-r) := by
    apply (le_div_iff₀ hdroot).2
    simpa only [Real.mul_self_sqrt hd.le] using hdN
  have hNp : ((N+1 : ℕ) : ℝ)≤2*(N : ℝ) := by push_cast;linarith
  calc
    _ ≤ 8*((N+1 : ℕ) : ℝ)*8*(Real.sqrt (s-r)/(2*(N : ℝ)))+
        12/(Real.sqrt (s-r)/(2*(N : ℝ))) := hb
    _ ≤ 8*(2*(N : ℝ))*8*(Real.sqrt (s-r)/(2*(N : ℝ)))+
        12/(Real.sqrt (s-r)/(2*(N : ℝ))) := by gcongr
    _ = 64*Real.sqrt (s-r)+24*(N : ℝ)/Real.sqrt (s-r) := by field_simp;ring
    _ ≤ 88*((N : ℝ)/Real.sqrt (s-r)) := by
      apply (add_le_add_left (mul_le_mul_of_nonneg_left hsmall
        (by norm_num : (0 : ℝ)≤64)) (24*(N : ℝ)/Real.sqrt (s-r))).trans_eq
      ring
    _ ≤ 96*((N : ℝ)/Real.sqrt (s-r)) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

private def collisionRow (N : ℕ) (r : ℝ) : EuclideanSpace ℂ (Fin (N+1)) :=
  WithLp.toLp 2 (fun j : Fin (N+1) => Complex.exp
    (((2*Real.pi*((N : ℝ)+j.val)^2/r : ℝ) : ℂ)*I))

private theorem collisionRow_norm (N : ℕ) (r : ℝ) :
    ‖collisionRow N r‖^2=((N+1 : ℕ) : ℝ) := by
  rw [EuclideanSpace.norm_eq,Real.sq_sqrt (by positivity)]
  have h (j : Fin (N+1)) : ‖collisionRow N r j‖^2=1 := by
    change ‖Complex.exp (((2*Real.pi*((N : ℝ)+j.val)^2/r : ℝ) : ℂ)*I)‖^2=1
    rw [Complex.norm_exp_ofReal_mul_I]
    norm_num
  simp_rw [h]
  simp

private theorem collisionRow_inner (N : ℕ) (r s : ℝ) :
    ⟪collisionRow N s,collisionRow N r⟫_ℂ=
      ∑ j∈Finset.range (N+1),Complex.exp
        (((2*Real.pi*(1/r-1/s)*((N : ℝ)+j)^2 : ℝ) : ℂ)*I) := by
  rw [PiLp.inner_apply]
  simp only [collisionRow,RCLike.inner_apply]
  rw [←Fin.sum_univ_eq_sum_range (fun j : ℕ => Complex.exp
    (((2*Real.pi*(1/r-1/s)*((N : ℝ)+j)^2 : ℝ) : ℂ)*I)) (N+1)]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Complex.exp_conj,←Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring

private theorem collisionRow_inner_bound {N : ℕ} (hN : 1≤N)
    {r s : ℝ} (hr : r∈Icc (N : ℝ) (2*N))
    (hs : s∈Icc (N : ℝ) (2*N)) (hrs : r≠s) :
    ‖⟪collisionRow N r,collisionRow N s⟫_ℂ‖≤
      96*(N : ℝ)/Real.sqrt |s-r| := by
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hr0 : r≠0 := (hn.trans_le hr.1).ne'
  have hs0 : s≠0 := (hn.trans_le hs.1).ne'
  rcases lt_or_gt_of_ne hrs with h | h
  · rw [Sieve.norm_inner_symm,collisionRow_inner,abs_of_pos (sub_pos.mpr h),
      show 1/r-1/s=(s-r)/(r*s) by field_simp [hr0,hs0]]
    exact quadratic_correlation hN hr hs h
  · rw [collisionRow_inner,abs_of_neg (sub_neg.mpr h),neg_sub,
      show 1/s-1/r=(r-s)/(s*r) by field_simp [hr0,hs0]]
    exact quadratic_correlation hN hs hr h

private def collisionGramBudget (N : ℕ) : ℝ :=
  (N+1 : ℕ)+96*(N : ℝ)*Real.sqrt (N+1 : ℕ)*Real.sqrt (2*(1+Real.log (N+1 : ℕ)))

private theorem collisionRow_gram {N : ℕ} (hN : 1≤N) {r : ℕ} (hr : r<N+1) :
    ∑ s∈Finset.range (N+1),
      ‖⟪collisionRow N ((N : ℝ)+r),collisionRow N ((N : ℝ)+s)⟫_ℂ‖≤
        collisionGramBudget N := by
  let lam : ℕ→ℝ := fun j => (N : ℝ)+j
  let S := (Finset.range (N+1)).erase r
  have hmem (j : ℕ) (hj : j<N+1) : lam j∈Icc (N : ℝ) (2*N) := by
    have hjN : (j : ℝ)≤N := by exact_mod_cast (show j≤N by omega)
    dsimp only [lam]
    exact ⟨le_add_of_nonneg_right (Nat.cast_nonneg j),by linarith⟩
  have hgap (j : ℕ) : lam j+1≤lam (j+1) := by dsimp only [lam];push_cast;linarith
  have hh := Sieve.sum_inv_abs_dist_le (by norm_num : (0 : ℝ)<1) hgap hr
  have hH : (∑ j∈Finset.range (N+1),1/((j : ℝ)+1))≤1+Real.log (N+1 : ℕ) := by
    rw [←Sieve.sum_Icc_one_div_eq_sum_range]
    exact Sieve.sum_Icc_one_div_le_one_add_log (N+1)
  have hh' : (∑ s∈S,1/|lam s-lam r|)≤2*(1+Real.log (N+1 : ℕ)) := by
    simpa only [div_one] using hh.trans (mul_le_mul_of_nonneg_left hH (by norm_num))
  have hcard : (S.card : ℝ)≤(N+1 : ℕ) := by
    exact_mod_cast (Finset.card_erase_le.trans_eq (Finset.card_range (N+1)))
  have hsquares : (∑ s∈S,(1/Real.sqrt |lam s-lam r|)^2)=∑ s∈S,1/|lam s-lam r| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [div_pow,one_pow,Real.sq_sqrt (abs_nonneg _)]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ))
    (fun s => 1/Real.sqrt |lam s-lam r|)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hCS
  have hsqrt : (∑ s∈S,1/Real.sqrt |lam s-lam r|)≤
      Real.sqrt (N+1 : ℕ)*Real.sqrt (2*(1+Real.log (N+1 : ℕ))) := by
    rw [hsquares] at hCS
    apply hCS.trans
    exact mul_le_mul (Real.sqrt_le_sqrt hcard) (Real.sqrt_le_sqrt hh')
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hoff : (∑ s∈S,‖⟪collisionRow N (lam r),collisionRow N (lam s)⟫_ℂ‖)≤
      96*(N : ℝ)*(Real.sqrt (N+1 : ℕ)*Real.sqrt (2*(1+Real.log (N+1 : ℕ)))) := by
    calc
      _ ≤ ∑ s∈S,96*(N : ℝ)*(1/Real.sqrt |lam s-lam r|) := by
        apply Finset.sum_le_sum
        intro s hs
        have hsr : s≠r := (Finset.mem_erase.mp hs).1
        have hsN : s<N+1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hs)
        have hne : lam r≠lam s := by
          intro he
          apply hsr
          dsimp only [lam] at he
          exact_mod_cast (show (s : ℝ)=r by linarith)
        simpa only [mul_one_div] using collisionRow_inner_bound hN (hmem r hr) (hmem s hsN) hne
      _ = 96*(N : ℝ)*(∑ s∈S,1/Real.sqrt |lam s-lam r|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hdiag : ‖⟪collisionRow N (lam r),collisionRow N (lam r)⟫_ℂ‖=((N+1 : ℕ) : ℝ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change ‖(‖collisionRow N (lam r)‖ : ℂ)^2‖=((N+1 : ℕ) : ℝ)
    rw [norm_pow,Complex.norm_of_nonneg (norm_nonneg _),collisionRow_norm]
  change (∑ s∈Finset.range (N+1),‖⟪collisionRow N (lam r),collisionRow N (lam s)⟫_ℂ‖)≤_
  rw [←Finset.sum_erase_add _ _ (Finset.mem_range.mpr hr),hdiag]
  dsimp only [collisionGramBudget]
  linarith [hoff]

private def collisionKernel (N r p : ℕ) : ℂ :=
  Complex.exp (((2*Real.pi*((N : ℝ)+p)^2/((N : ℝ)+r) : ℝ) : ℂ)*I)

private theorem collisionGramBudget_nonneg (N : ℕ) : 0≤collisionGramBudget N := by
  dsimp only [collisionGramBudget]
  positivity

private theorem collision_form {N : ℕ} (hN : 1≤N) (c d : ℕ→ℂ) :
    ‖∑ r∈Finset.range (N+1),∑ p∈Finset.range (N+1),c r*d p*collisionKernel N r p‖≤
      Real.sqrt (collisionGramBudget N)*Real.sqrt (∑r∈Finset.range (N+1),‖c r‖^2)*
        Real.sqrt (∑p∈Finset.range (N+1),‖d p‖^2) := by
  let V := ∑r∈Finset.range (N+1),c r•collisionRow N ((N : ℝ)+r)
  have hv (p : Fin (N+1)) : V p=∑r∈Finset.range (N+1),c r*collisionKernel N r p := by
    simp [V,WithLp.ofLp_sum,WithLp.ofLp_smul,collisionRow,collisionKernel,Finset.sum_apply]
  have he : (∑r∈Finset.range (N+1),∑p∈Finset.range (N+1),c r*d p*collisionKernel N r p)=
      ∑p : Fin (N+1),V p*d p := by
    simp_rw [hv,Finset.sum_mul]
    rw [Fin.sum_univ_eq_sum_range (fun p : ℕ =>
      ∑r∈Finset.range (N+1),c r*collisionKernel N r p*d p) (N+1),Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hV : ‖V‖≤Real.sqrt (collisionGramBudget N)*
      Real.sqrt (∑r∈Finset.range (N+1),‖c r‖^2) := by
    have h := Real.sqrt_le_sqrt (Sieve.norm_sum_smul_sq_le_of_schur
      (Finset.range (N+1)) (fun r => collisionRow N ((N : ℝ)+r))
      (fun r hr => collisionRow_gram hN (Finset.mem_range.mp hr)) c)
    rw [Real.sqrt_sq (norm_nonneg _),Real.sqrt_mul (collisionGramBudget_nonneg N)] at h
    exact h
  rw [he]
  calc
    _ ≤ ∑p : Fin (N+1),‖V p‖*‖d p‖ := by
      simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset (Fin (N+1))) (fun p => V p*d p)
    _ ≤ Real.sqrt (∑p : Fin (N+1),‖V p‖^2)*Real.sqrt (∑p : Fin (N+1),‖d p‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖V‖*Real.sqrt (∑p∈Finset.range (N+1),‖d p‖^2) := by
      rw [←EuclideanSpace.norm_eq,Fin.sum_univ_eq_sum_range (fun p : ℕ => ‖d p‖^2) (N+1)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hV (Real.sqrt_nonneg _)

private theorem collision_weighted_form {N : ℕ} (hN : 1≤N) (c d : ℕ→ℂ) :
    ‖∑r∈Finset.range (N+1),∑p∈Finset.range (N+1),c r*d p*collisionKernel N r p*
      GaloisForLFunctions.RHTower.physicalLogWindow
        (-Real.log ((N : ℝ)+r)+2*Real.log ((N : ℝ)+p)-Real.log N)‖≤
      GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget*Real.sqrt (collisionGramBudget N)*
        Real.sqrt (∑r∈Finset.range (N+1),‖c r‖^2)*Real.sqrt (∑p∈Finset.range (N+1),‖d p‖^2) := by
  exact GaloisForLFunctions.RHTower.norm_schwartz_weighted_matrix_form_le
    (Finset.range (N+1)) (Finset.range (N+1)) (collisionKernel N)
    GaloisForLFunctions.RHTower.physicalLogWindowSchwartz (collision_form hN)
    (fun r => -Real.log ((N : ℝ)+r)) (fun p => 2*Real.log ((N : ℝ)+p)) (-Real.log N) c d

private theorem collision_budget_tendsto :
    Tendsto (fun N : ℕ => (Real.log N)^2/(N : ℝ)*Real.sqrt (collisionGramBudget N))
      atTop (𝓝 0) := by
  have hz : Tendsto (fun N : ℕ => (Real.log N)^5/Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)/2) 5 (by norm_num)).tendsto_div_nhds_zero
    simp only [show (5 : ℝ)=((5 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] at h
    convert! h.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    simp only [Real.sqrt_eq_rpow]
    rfl
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Tendsto (fun N : ℕ => ((Real.log N)^2/(N : ℝ)*Real.sqrt (collisionGramBudget N))^2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ (by simpa only [mul_zero] using hz.const_mul 600)
    filter_upwards [eventually_ge_atTop 2,hlog.eventually_ge_atTop 1] with N hN hL
    change 1≤Real.log (N : ℝ) at hL
    have hn : (2 : ℝ)≤N := by exact_mod_cast hN
    have hn0 : (0 : ℝ)<N := by linarith
    have hsq := Real.sq_sqrt hn0.le
    have hsqpos := Real.sqrt_pos.mpr hn0
    have hsqr : 1≤Real.sqrt (N : ℝ) := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
    have hNp : ((N+1 : ℕ) : ℝ)≤2*(N : ℝ) := by push_cast;linarith
    have hlog' : 1+Real.log (N+1 : ℕ)≤3*Real.log N := by
      have ha : ((N+1 : ℕ) : ℝ)≤(N : ℝ)^2 := by push_cast;nlinarith
      have hb := Real.log_le_log (by positivity : (0 : ℝ)<(N+1 : ℕ)) ha
      rw [Real.log_pow] at hb
      norm_num only [Nat.cast_ofNat] at hb
      linarith
    have hrootN : Real.sqrt (N+1 : ℕ)≤2*Real.sqrt (N : ℝ) := by
      apply Real.sqrt_le_iff.2
      exact ⟨by positivity,by nlinarith⟩
    have hrootL : Real.sqrt (2*(1+Real.log (N+1 : ℕ)))≤3*Real.log N := by
      apply Real.sqrt_le_iff.2
      exact ⟨by linarith,by nlinarith⟩
    have hbudget : collisionGramBudget N≤600*(N : ℝ)*Real.sqrt (N : ℝ)*Real.log N := by
      calc
        _ ≤ 2*(N : ℝ)+96*(N : ℝ)*(2*Real.sqrt (N : ℝ))*(3*Real.log N) := by
          dsimp only [collisionGramBudget]
          gcongr
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (show 1≤Real.sqrt (N : ℝ)*Real.log N by nlinarith) hn0.le]
    calc
      _ = ((Real.log N)^2/(N : ℝ))^2*collisionGramBudget N := by
        rw [mul_pow,Real.sq_sqrt (collisionGramBudget_nonneg N)]
      _ ≤ ((Real.log N)^2/(N : ℝ))^2*(600*(N : ℝ)*Real.sqrt (N : ℝ)*Real.log N) := by gcongr
      _ = 600*((Real.log N)^5/Real.sqrt (N : ℝ)) := by
        field_simp [hn0.ne',hsqpos.ne']
        rw [hsq]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have he (N : ℕ) : Real.sqrt (((Real.log N)^2/(N : ℝ)*Real.sqrt (collisionGramBudget N))^2)=
      (Real.log N)^2/(N : ℝ)*Real.sqrt (collisionGramBudget N) := Real.sqrt_sq (by positivity)
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun N => he N)

private theorem collision_sum_band (N:ℕ) (f:ℕ→ℂ) :
    ∑ p∈primeProfileBand (N:ℝ),f p =
      ∑ j∈Finset.range (N+1),if N+j∈primeProfileBand (N:ℝ) then f (N+j) else 0 := by
  have hsub : primeProfileBand (N:ℝ) ⊆ Finset.Icc N (2*N) := by
    intro p hp
    obtain ⟨_,hlo,hhi⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hp
    have hlo' : N<p := by exact_mod_cast hlo
    have hhi' : p≤2*N := by exact_mod_cast hhi
    exact Finset.mem_Icc.mpr ⟨hlo'.le,hhi'⟩
  have he : (Finset.Icc N (2*N)).filter (fun p => p∈primeProfileBand (N:ℝ)) =
      primeProfileBand (N:ℝ) := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
  rw [← he,Finset.sum_filter]
  apply Finset.sum_bij (fun p _ => p-N)
  · intro p hp
    have hp' := Finset.mem_Icc.mp hp
    exact Finset.mem_range.mpr (by omega)
  · intro p hp q hq heq
    have hp' := Finset.mem_Icc.mp hp
    have hq' := Finset.mem_Icc.mp hq
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ⟨N+j,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro p hp
    have hp' := Finset.mem_Icc.mp hp
    rw [Nat.add_sub_cancel' hp'.1]
    rw [he]


private def collisionColumn (N j : ℕ) : ℂ :=
  if N+j∈primeProfileBand (N : ℝ) then
    ((Real.sqrt N/Real.sqrt (N+j : ℕ) : ℝ) : ℂ)*
      (starRingEnd ℂ) (smoothAFECutoff (((N+j : ℕ) : ℝ)/N)) else 0
private def collisionSample (N j : ℕ) : ℂ :=
  if N+j∈primeProfileBand (N : ℝ) then
    (((N : ℝ)/(N+j : ℕ) : ℝ) : ℂ)*smoothAFECutoff (((N+j : ℕ) : ℝ)/N)^2 else 0

private theorem collisionColumn_norm {N : ℕ} (hN : 1≤N) (j : ℕ) :
    ‖collisionColumn N j‖≤1 := by
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hj0 : (0 : ℝ)<(N+j : ℕ) := by exact_mod_cast (show 0<N+j by omega)
  have hnle : (N : ℝ)≤(N+j : ℕ) := by exact_mod_cast (show N≤N+j by omega)
  unfold collisionColumn
  split_ifs with h
  · rw [norm_mul,norm_conj,Complex.norm_of_nonneg (by positivity)]
    have hb : Real.sqrt (N : ℝ)/Real.sqrt (N+j : ℕ)≤1 :=
      (div_le_one (Real.sqrt_pos.mpr hj0)).2 (Real.sqrt_le_sqrt hnle)
    exact (mul_le_mul hb (norm_smoothAFECutoff_le_one (div_pos hj0 hn0))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp

private theorem collisionSample_norm {N : ℕ} (hN : 1≤N) (j : ℕ) :
    ‖collisionSample N j‖≤1 := by
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hj0 : (0 : ℝ)<(N+j : ℕ) := by exact_mod_cast (show 0<N+j by omega)
  have hnle : (N : ℝ)≤(N+j : ℕ) := by exact_mod_cast (show N≤N+j by omega)
  unfold collisionSample
  split_ifs with h
  · rw [norm_mul,norm_pow,Complex.norm_of_nonneg (by positivity)]
    have hb : (N : ℝ)/(N+j : ℕ)≤1 := (div_le_one hj0).2 hnle
    have hv := norm_smoothAFECutoff_le_one (div_pos hj0 hn0)
    have hv2 : ‖smoothAFECutoff (((N+j : ℕ) : ℝ)/N)‖^2≤1 := by
      nlinarith [norm_nonneg (smoothAFECutoff (((N+j : ℕ) : ℝ)/N))]
    exact (mul_le_mul hb hv2 (sq_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp

private theorem collision_window {N p r : ℝ} (hN : 0<N) (hp : 0<p) (hr : 0<r) :
    GaloisForLFunctions.RHTower.physicalLogWindow (-Real.log r+2*Real.log p-Real.log N)=
      ((p/(Real.sqrt r*Real.sqrt N)*bagPhysicalHeightWindow (p^2/(r*N)) : ℝ) : ℂ) := by
  have hx : 0<p^2/(r*N) := by positivity
  have hl : -Real.log r+2*Real.log p-Real.log N=Real.log (p^2/(r*N)) := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_mul hr.ne' hN.ne']
    norm_num
    ring
  have hs : Real.sqrt (p^2/(r*N))=p/(Real.sqrt r*Real.sqrt N) := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hp.le,Real.sqrt_mul hr.le]
  rw [hl,GaloisForLFunctions.RHTower.physicalLogWindow,Real.exp_log hx,
    ←Real.log_sqrt hx.le,Real.exp_log (Real.sqrt_pos.mpr hx),hs]

private theorem collision_entry {N : ℕ} (hN : 1≤N) (r p : ℕ)
    (hr : N+r∈primeProfileBand (N : ℝ)) (hp : N+p∈primeProfileBand (N : ℝ)) :
    primeGaussianCubicMainEntry N (N+p) (N+p) (N+r)=
      (2*Real.pi/(N : ℝ) : ℂ)*(collisionColumn N r*collisionSample N p*collisionKernel N r p*
        GaloisForLFunctions.RHTower.physicalLogWindow
          (-Real.log ((N : ℝ)+r)+2*Real.log ((N : ℝ)+p)-Real.log N)) := by
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hr0 : (0 : ℝ)<(N : ℝ)+r := by positivity
  have hp0 : (0 : ℝ)<(N : ℝ)+p := by positivity
  rw [collision_window hn0 hp0 hr0]
  simp only [collisionColumn,collisionSample,if_pos hr,if_pos hp,collisionKernel,
    primeGaussianCubicMainEntry,bourgainOscillation]
  push_cast
  have hnC : (N : ℂ)≠0 := by exact_mod_cast hn0.ne'
  have hpC : (N : ℂ)+p≠0 := by exact_mod_cast hp0.ne'
  have hrC : (N : ℂ)+r≠0 := by exact_mod_cast hr0.ne'
  have hnS : (Real.sqrt (N : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn0).ne'
  have hrS : (Real.sqrt ((N : ℝ)+r) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr0).ne'
  have hsR : (Real.sqrt ((N : ℝ)+r) : ℂ)^2=(N : ℂ)+r := by exact_mod_cast Real.sq_sqrt hr0.le
  have heW : ((N : ℝ)+p)*((N : ℝ)+p)/(((N : ℝ)+r)*N)=((N : ℝ)+p)^2/(((N : ℝ)+r)*N) := by ring
  have heP : (I : ℂ)*(2*Real.pi*(((N : ℂ)+p)*((N : ℂ)+p)/((N : ℂ)+r)))=
      (2*Real.pi*((N : ℂ)+p)^2/((N : ℂ)+r))*I := by ring
  rw [heW,heP]
  field_simp
  linear_combination (norm := ring_nf)
    smoothAFECutoff (((N : ℝ)+p)/N)^2*
      (starRingEnd ℂ) (smoothAFECutoff (((N : ℝ)+r)/N))*
      (bagPhysicalHeightWindow (((N : ℝ)+p)^2/(((N : ℝ)+r)*N)) : ℂ)*hsR

private theorem collision_full_sum_bound {N : ℕ} (hN : 1≤N) :
    ‖∑r∈primeProfileBand (N : ℝ),∑p∈primeProfileBand (N : ℝ),
      primeGaussianCubicMainEntry N p p r‖≤
      (4*Real.pi*GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget)*
        Real.sqrt (collisionGramBudget N) := by
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : (∑r∈primeProfileBand (N : ℝ),∑p∈primeProfileBand (N : ℝ),
      primeGaussianCubicMainEntry N p p r)=
      (2*Real.pi/(N : ℝ) : ℂ)*(∑r∈Finset.range (N+1),∑p∈Finset.range (N+1),
        collisionColumn N r*collisionSample N p*collisionKernel N r p*
          GaloisForLFunctions.RHTower.physicalLogWindow
            (-Real.log ((N : ℝ)+r)+2*Real.log ((N : ℝ)+p)-Real.log N)) := by
    rw [collision_sum_band N,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : N+r∈primeProfileBand (N : ℝ)
    · rw [if_pos hr,collision_sum_band N,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : N+p∈primeProfileBand (N : ℝ)
      · rw [if_pos hp]
        exact collision_entry hN r p hr hp
      · simp only [if_neg hp,collisionSample,zero_mul,mul_zero]
    · simp only [if_neg hr,collisionColumn,zero_mul,Finset.sum_const_zero,mul_zero]
  have hcol : Real.sqrt (∑r∈Finset.range (N+1),‖collisionColumn N r‖^2)≤Real.sqrt (N+1 : ℕ) := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑r∈Finset.range (N+1),(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        nlinarith [collisionColumn_norm hN r,norm_nonneg (collisionColumn N r)]
      _ = _ := by simp
  have hsample : Real.sqrt (∑p∈Finset.range (N+1),‖collisionSample N p‖^2)≤Real.sqrt (N+1 : ℕ) := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑p∈Finset.range (N+1),(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        nlinarith [collisionSample_norm hN p,norm_nonneg (collisionSample N p)]
      _ = _ := by simp
  have hB := GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget_nonneg
  have hNp : ((N+1 : ℕ) : ℝ)≤2*(N : ℝ) := by
    have hn : (1 : ℝ)≤N := by exact_mod_cast hN
    push_cast
    linarith
  rw [he,norm_mul,norm_div,norm_mul,Complex.norm_ofNat,
    Complex.norm_of_nonneg Real.pi_pos.le,Complex.norm_of_nonneg hn0.le]
  calc
    _ ≤ (2*Real.pi/(N : ℝ))*(GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget*
        Real.sqrt (collisionGramBudget N)*Real.sqrt (N+1 : ℕ)*Real.sqrt (N+1 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (collision_weighted_form hN (collisionColumn N) (collisionSample N)).trans
        (by gcongr)
    _ = (2*Real.pi*GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget*
        Real.sqrt (collisionGramBudget N))/(N : ℝ)*
          (Real.sqrt (N+1 : ℕ)*Real.sqrt (N+1 : ℕ)) := by ring
    _ = (2*Real.pi*GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget*
        Real.sqrt (collisionGramBudget N))/(N : ℝ)*(N+1 : ℕ) := by
      rw [Real.mul_self_sqrt (by positivity : (0 : ℝ)≤(N+1 : ℕ))]
    _ ≤ (2*Real.pi*GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget*
        Real.sqrt (collisionGramBudget N))/(N : ℝ)*(2*(N : ℝ)) := by gcongr
    _ = _ := by field_simp; ring

/-- The complete allowed first/second-prime collision sector. Both original
contractions remain excluded: p=q is allowed precisely when p differs from r. -/
def bagCubicAllowedPrimeCollision (N : ℕ) : ℂ :=
  ∑r∈primeProfileBand (N : ℝ),∑p∈primeProfileBand (N : ℝ),
    if p=r then 0 else primeGaussianCubicMainEntry N p p r

private theorem collision_sub_diagonal (N : ℕ) :
    bagCubicAllowedPrimeCollision N=
      (∑r∈primeProfileBand (N : ℝ),∑p∈primeProfileBand (N : ℝ),primeGaussianCubicMainEntry N p p r)-
        ∑r∈primeProfileBand (N : ℝ),primeGaussianCubicMainEntry N r r r := by
  have hr (r : ℕ) (hr : r∈primeProfileBand (N : ℝ)) :
      (∑p∈primeProfileBand (N : ℝ),primeGaussianCubicMainEntry N p p r)=
      primeGaussianCubicMainEntry N r r r+
        ∑p∈primeProfileBand (N : ℝ),if p=r then 0 else primeGaussianCubicMainEntry N p p r := by
    have he (p : ℕ) : primeGaussianCubicMainEntry N p p r=
        (if p=r then primeGaussianCubicMainEntry N r r r else 0)+
          (if p=r then 0 else primeGaussianCubicMainEntry N p p r) := by
      by_cases h : p=r <;> simp [h]
    rw [Finset.sum_congr rfl (fun p _ => he p),Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',hr,if_true]
  have hh := Finset.sum_congr rfl hr
  rw [Finset.sum_add_distrib] at hh
  change _=(∑r∈primeProfileBand (N : ℝ),primeGaussianCubicMainEntry N r r r)+
    bagCubicAllowedPrimeCollision N at hh
  rw [hh]
  ring

private theorem collision_diagonal_bound {N : ℕ} (hN : 1≤N) :
    ‖∑r∈primeProfileBand (N : ℝ),primeGaussianCubicMainEntry N r r r‖≤16 := by
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    _ ≤ ∑r∈primeProfileBand (N : ℝ),‖primeGaussianCubicMainEntry N r r r‖ := norm_sum_le _ _
    _ ≤ ∑r∈primeProfileBand (N : ℝ),8/(N : ℝ) :=
      Finset.sum_le_sum (fun r hr => primeGaussianCubicMainEntry_norm_le hN hr hr hr)
    _ = ((primeProfileBand (N : ℝ)).card : ℝ)*(8/(N : ℝ)) := by simp
    _ ≤ (2*(N : ℝ))*(8/(N : ℝ)) :=
      mul_le_mul_of_nonneg_right (primeProfileBand_card_le_twice N) (by positivity)
    _ = _ := by field_simp; ring

/-- Unconditional cancellation of the entire allowed p=q≠r prime sector,
with the original physical window and sharp prime band. -/
theorem bagCubicAllowedPrimeCollision_norm_tendsto :
    Tendsto (fun N : ℕ => (Real.log N)^2/(N : ℝ)*‖bagCubicAllowedPrimeCollision N‖)
      atTop (𝓝 0) := by
  have hz : Tendsto (fun N : ℕ => (Real.log N)^2/(N : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ)) 2 (by norm_num)).tendsto_div_nhds_zero
    simp only [Real.rpow_one,show (2 : ℝ)=((2 : ℕ) : ℝ) by norm_num,Real.rpow_natCast] at h
    convert! h.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
  have hh := (collision_budget_tendsto.const_mul
    (4*Real.pi*GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget)).add (hz.mul_const 16)
  simp only [mul_zero,zero_mul,add_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hh
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hb : ‖bagCubicAllowedPrimeCollision N‖≤
      (4*Real.pi*GaloisForLFunctions.RHTower.physicalLogWindowFourierBudget)*
        Real.sqrt (collisionGramBudget N)+16 := by
    rw [collision_sub_diagonal]
    exact (norm_sub_le _ _).trans (add_le_add (collision_full_sum_bound hN) (collision_diagonal_bound hN))
  have h := mul_le_mul_of_nonneg_left hb (by positivity : 0≤(Real.log N)^2/(N : ℝ))
  convert! h using 1
  ring

end RHTower.BAGTrace
