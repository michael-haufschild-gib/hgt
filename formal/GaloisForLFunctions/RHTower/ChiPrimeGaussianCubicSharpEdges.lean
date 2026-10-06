import GaloisForLFunctions.RHTower.ChiCubicControlledCutoff
import GaloisForLFunctions.RHTower.Sieve.KuzminLandauInterval
import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality
import GaloisForLFunctions.RHTower.Sieve.SeparatedRowSum
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.LogPhasePhysicalWindow
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain

/-!
# Smooth edges of the actual signed Gaussian prime cubic

The literal physical window is retained in a complete integer bilinear Gram
estimate. Abel summation, quarter-band separation and harmonic Schur control
both reciprocal and linear frequency families. Prime masks enter only after
Cauchy; both contraction exclusions remain in the final source.

The complete sharp cubic admits smooth band cutoffs with growing N^(1/4)
boundary strips and error o(N/log(N)^2), along integer band scales. Every
original prime triple and all three band factors are included. This removes
the sharp-to-smooth transfer obstruction. It does not bound the remaining
signed interior aggregate or provide a uniform stationary expansion for the
scale-dependent cutoff derivatives.
-/

noncomputable section
open Complex Set Filter Finset
open scoped Topology InnerProductSpace ContDiff
namespace RHTower
open GaloisForLFunctions.RHTower

private theorem edge_complex_abel (f g : ℕ → ℂ) (n : ℕ) {B : ℝ}
    (hB : ∀ k ≤ n, ‖∑ j ∈ Finset.range k, g j‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, f i * g i‖ ≤
      B * (‖f (n-1)‖ + ∑ i ∈ Finset.range (n-1), ‖f (i+1)-f i‖) := by
  have hp := Finset.sum_range_by_parts f g n
  simp only [smul_eq_mul] at hp
  rw [hp]
  refine (norm_sub_le _ _).trans ?_
  have hh : ‖f (n-1) * ∑ i ∈ Finset.range n, g i‖ ≤ ‖f (n-1)‖ * B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB n le_rfl) (norm_nonneg _)
  have ht : ‖∑ i ∈ Finset.range (n-1),
      (f (i+1)-f i) * ∑ j ∈ Finset.range (i+1), g j‖ ≤
      (∑ i ∈ Finset.range (n-1), ‖f (i+1)-f i‖) * B := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hB (i+1) (by have := Finset.mem_range.mp hi; omega)) (norm_nonneg _)
  nlinarith only [hh, ht]

private theorem edge_linear_prefix {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/2)
    (x : ℝ) (n : ℕ) :
    ‖∑ j ∈ Finset.range n,
      Complex.exp (((2*Real.pi*(δ*(x+j)) : ℝ) : ℂ)*I)‖ ≤ 3/δ := by
  rcases n with _ | m
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have h := Sieve.kuzminLandau_interval (fun y => δ*y) (fun _ => δ) x m 0 hδ
    (fun y _ => by simpa using (hasDerivAt_id y).const_mul δ)
    (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => by simp)
    (fun _ _ => by simp only [Int.cast_zero]; linarith)
  refine h.trans ?_
  apply (le_div_iff₀ hδ).mpr
  have hmul : (3/(2*δ)+1)*δ = 3/2+δ := by field_simp
  rw [hmul]
  linarith

private def edgeWindowPair (α β x : ℝ) : ℂ :=
  (bagPhysicalHeightWindow (α*x) : ℂ) * (bagPhysicalHeightWindow (β*x) : ℂ)

private theorem edge_window_pair_norm (α β x : ℝ) : ‖edgeWindowPair α β x‖ ≤ 1 := by
  rw [edgeWindowPair, norm_mul,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  exact (mul_le_mul bagPhysicalHeightWindow.le_one bagPhysicalHeightWindow.le_one
    bagPhysicalHeightWindow.nonneg zero_le_one).trans_eq (one_mul 1)

private theorem edge_window_pair_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ α ∈ Icc (0:ℝ) 2, ∀ β ∈ Icc (0:ℝ) 2,
      ∀ x ∈ Icc (1:ℝ) 2, ∀ y ∈ Icc (1:ℝ) 2,
        ‖edgeWindowPair α β y - edgeWindowPair α β x‖ ≤ L * |y-x| := by
  have hc : Continuous (deriv (fun y:ℝ => bagPhysicalHeightWindow y)) :=
    (bagPhysicalHeightWindow.contDiff (n:=1)).continuous_deriv_one
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn (deriv (fun y:ℝ => bagPhysicalHeightWindow y)) (Icc (0:ℝ) 4))
  have hw {a b:ℝ} (ha:a∈Icc (0:ℝ) 4) (hb:b∈Icc (0:ℝ) 4) :
      ‖(bagPhysicalHeightWindow b:ℂ)-(bagPhysicalHeightWindow a:ℂ)‖ ≤ |M| * |b-a| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z (_:z∈Icc (0:ℝ) 4) =>
        (bagPhysicalHeightWindow.contDiff (n:=1)).differentiable (by norm_num) z)
      (fun z hz => (hM z hz).trans (le_abs_self M)) (convex_Icc (0:ℝ) 4) ha hb
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h
  refine ⟨4 * |M|,by positivity,?_⟩
  intro α hα β hβ x hx y hy
  have hmem {a z:ℝ} (ha:a∈Icc (0:ℝ) 2) (hz:z∈Icc (1:ℝ) 2) : a*z∈Icc (0:ℝ) 4 :=
    ⟨mul_nonneg ha.1 (by linarith only [hz.1]),
      (mul_le_mul ha.2 hz.2 (by linarith only [hz.1]) (by norm_num)).trans_eq (by norm_num)⟩
  have hdiff {a:ℝ} (ha:a∈Icc (0:ℝ) 2) :
      ‖(bagPhysicalHeightWindow (a*y):ℂ)-(bagPhysicalHeightWindow (a*x):ℂ)‖ ≤
        2 * |M| * |y-x| := by
    have h := hw (hmem ha hx) (hmem ha hy)
    rw [← mul_sub,abs_mul,abs_of_nonneg ha.1] at h
    have hm := mul_le_mul_of_nonneg_left ha.2
      (mul_nonneg (abs_nonneg M) (abs_nonneg (y-x)))
    exact h.trans (by nlinarith only [hm])
  have he : edgeWindowPair α β y-edgeWindowPair α β x =
      ((bagPhysicalHeightWindow (α*y):ℂ)-(bagPhysicalHeightWindow (α*x):ℂ))*
        (bagPhysicalHeightWindow (β*y):ℂ)+
      (bagPhysicalHeightWindow (α*x):ℂ)*
        ((bagPhysicalHeightWindow (β*y):ℂ)-(bagPhysicalHeightWindow (β*x):ℂ)) := by
    dsimp [edgeWindowPair]; ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,norm_mul,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  have h1 := mul_le_mul (hdiff hα) (bagPhysicalHeightWindow.le_one (x:=β*y))
    bagPhysicalHeightWindow.nonneg (by positivity : 0≤2 * |M| * |y-x|)
  have h2 := mul_le_mul (bagPhysicalHeightWindow.le_one (x:=α*x)) (hdiff hβ)
    (norm_nonneg _) zero_le_one
  nlinarith only [h1,h2]

private theorem edge_weighted_correlation :
    ∃ C : ℝ, 0<C ∧ ∀ N:ℕ, 1≤N → ∀ α∈Icc (0:ℝ) 2, ∀ β∈Icc (0:ℝ) 2,
      ∀ δ:ℝ, 0<δ → δ≤1/2 →
      ‖∑ j ∈ Finset.range (N+1),
        edgeWindowPair α β (1+(j:ℝ)/N)*
          Complex.exp (((2*Real.pi*(δ*((N:ℝ)+j)):ℝ):ℂ)*I)‖ ≤ C/δ := by
  obtain ⟨L,hL,hLip⟩ := edge_window_pair_lipschitz
  refine ⟨3*(1+L),by positivity,?_⟩
  intro N hN α hα β hβ δ hδ hδhi
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hx (j:ℕ) (hj:j≤N) : 1+(j:ℝ)/N∈Icc (1:ℝ) 2 := by
    have hjN : (j:ℝ)≤N := by exact_mod_cast hj
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have := (div_le_one hN0).mpr hjN; linarith
  have hv : ∑ j ∈ Finset.range N,
      ‖edgeWindowPair α β (1+((j+1:ℕ):ℝ)/N)-edgeWindowPair α β (1+(j:ℝ)/N)‖ ≤ L := by
    calc
      _ ≤ ∑ _j ∈ Finset.range N, L/(N:ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        have h := hLip α hα β hβ _ (hx j (by omega)) _ (hx (j+1) (by omega))
        have he : (1+((j+1:ℕ):ℝ)/N)-(1+(j:ℝ)/N) = 1/N := by push_cast; ring
        rw [he,abs_of_pos (one_div_pos.mpr hN0)] at h
        simpa only [mul_one_div] using h
      _ = L := by simp; field_simp
  have h := edge_complex_abel
    (fun j => edgeWindowPair α β (1+(j:ℝ)/N))
    (fun j => Complex.exp (((2*Real.pi*(δ*((N:ℝ)+j)):ℝ):ℂ)*I)) (N+1)
    (fun k _ => edge_linear_prefix hδ hδhi N k)
  simp only [Nat.add_sub_cancel] at h
  refine h.trans ?_
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (edge_window_pair_norm α β (1+(N:ℝ)/N)) hv)
    (by positivity : 0≤3/δ)
  calc
    _ ≤ (3/δ)*(1+L) := hb
    _ = _ := by ring

private def edgePhaseRow (N:ℕ) (θ:ℝ) : EuclideanSpace ℂ (Fin (N+1)) :=
  WithLp.toLp 2 (fun j:Fin (N+1) =>
    (bagPhysicalHeightWindow (θ*(1+(j:ℝ)/N)):ℂ)*
      Complex.exp (((2*Real.pi*(θ*((N:ℝ)+j)):ℝ):ℂ)*I))

private theorem edge_phase_row_norm (N:ℕ) (θ:ℝ) :
    ‖edgePhaseRow N θ‖^2 ≤ (N:ℝ)+1 := by
  rw [EuclideanSpace.norm_eq,Real.sq_sqrt (by positivity)]
  have hterm (j:Fin (N+1)) : ‖edgePhaseRow N θ j‖^2 ≤ 1 := by
    change ‖(bagPhysicalHeightWindow (θ*(1+(j:ℝ)/N)):ℂ)*
      Complex.exp (((2*Real.pi*(θ*((N:ℝ)+j)):ℝ):ℂ)*I)‖^2 ≤ 1
    rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,
      Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
    nlinarith only [bagPhysicalHeightWindow.nonneg (x:=θ*(1+(j:ℝ)/N)),
      bagPhysicalHeightWindow.le_one (x:=θ*(1+(j:ℝ)/N))]
  calc
    _ ≤ ∑ _j:Fin (N+1), (1:ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by simp

private theorem edge_phase_row_inner (N:ℕ) (α β:ℝ) :
    ⟪edgePhaseRow N α,edgePhaseRow N β⟫_ℂ =
      ∑ j ∈ Finset.range (N+1), edgeWindowPair α β (1+(j:ℝ)/N)*
        Complex.exp (((2*Real.pi*((β-α)*((N:ℝ)+j)):ℝ):ℂ)*I) := by
  rw [PiLp.inner_apply]
  simp only [edgePhaseRow,RCLike.inner_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun j:ℕ => edgeWindowPair α β (1+(j:ℝ)/N)*
        Complex.exp (((2*Real.pi*((β-α)*((N:ℝ)+j)):ℝ):ℂ)*I)) (N+1)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul,Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  have he : Complex.exp (((2*Real.pi*(β*((N:ℝ)+j)):ℝ):ℂ)*I)*
      Complex.exp ((starRingEnd ℂ) (((2*Real.pi*(α*((N:ℝ)+j)):ℝ):ℂ)*I)) =
      Complex.exp (((2*Real.pi*((β-α)*((N:ℝ)+j)):ℝ):ℂ)*I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  dsimp only [edgeWindowPair]
  calc
    _ = ((bagPhysicalHeightWindow (α*(1+(j:ℝ)/N)):ℂ)*
      (bagPhysicalHeightWindow (β*(1+(j:ℝ)/N)):ℂ))*
      (Complex.exp (((2*Real.pi*(β*((N:ℝ)+j)):ℝ):ℂ)*I)*
      Complex.exp ((starRingEnd ℂ) (((2*Real.pi*(α*((N:ℝ)+j)):ℝ):ℂ)*I))) := by ring
    _ = _ := by rw [he]

private theorem edge_phase_gram_bound :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℕ, 1≤N → ∀ α∈Icc (0:ℝ) 2, ∀ β∈Icc (0:ℝ) 2,
      α≠β → |β-α|≤1/2 →
      ‖⟪edgePhaseRow N α,edgePhaseRow N β⟫_ℂ‖≤C/|β-α| := by
  obtain ⟨C,hC,h⟩ := edge_weighted_correlation
  refine ⟨C,hC,?_⟩
  intro N hN α hα β hβ hne hgap
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [edge_phase_row_inner,abs_of_pos (sub_pos.mpr hlt)]
    apply h N hN α hα β hβ _ (sub_pos.mpr hlt)
    rwa [abs_of_pos (sub_pos.mpr hlt)] at hgap
  · rw [Sieve.norm_inner_symm,edge_phase_row_inner,
      abs_of_neg (sub_neg.mpr hlt),neg_sub]
    apply h N hN β hβ α hα _ (sub_pos.mpr hlt)
    rwa [abs_of_neg (sub_neg.mpr hlt),neg_sub] at hgap

private theorem edge_phase_operator_bound :
    ∃ D:ℝ, 0<D ∧ ∀ N:ℕ, 1≤N → ∀ S:Finset ℕ, S⊆Finset.range (N+1) →
      ∀ θ:ℕ→ℝ, (∀ r∈S, θ r∈Icc (0:ℝ) 2) →
      (∀ r∈S, ∀ s∈S, r≠s →
        |(s:ℝ)-r|/(4*N)≤|θ s-θ r| ∧ |θ s-θ r|≤1/2) →
      ∀ c:ℕ→ℂ,
      ‖∑ r∈S,c r • edgePhaseRow N (θ r)‖^2 ≤
        D*N*(1+Real.log ((N+1:ℕ):ℝ))*∑ r∈S,‖c r‖^2 := by
  obtain ⟨C,hC,hgram⟩ := edge_phase_gram_bound
  refine ⟨2+8*C,by positivity,?_⟩
  intro N hN S hS θ hθ hsep c
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hH : ∑ j∈Finset.range (N+1), 1/((j:ℝ)+1) ≤
      1+Real.log ((N+1:ℕ):ℝ) := by
    rw [← Sieve.sum_Icc_one_div_eq_sum_range]
    exact Sieve.sum_Icc_one_div_le_one_add_log (N+1)
  have hlog := Real.log_natCast_nonneg (N+1)
  apply Sieve.norm_sum_smul_sq_le_of_schur S (fun r => edgePhaseRow N (θ r))
  intro r hr
  have hrN := Finset.mem_range.mp (hS hr)
  have hinv := Sieve.sum_inv_abs_dist_le (lam:=fun j => (j:ℝ))
    (by norm_num : (0:ℝ)<1) (fun j => by push_cast; linarith) hrN
  norm_num only [div_one] at hinv
  have hpoint (s:ℕ) (hs:s∈S.erase r) :
      ‖⟪edgePhaseRow N (θ r),edgePhaseRow N (θ s)⟫_ℂ‖ ≤
        (4*C*N)*(1/|(s:ℝ)-r|) := by
    have hsS := Finset.mem_of_mem_erase hs
    have hsr := (Finset.mem_erase.mp hs).1
    have hd : 0 < |(s:ℝ)-r| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hsr))
    obtain ⟨hlo,hhi⟩ := hsep r hr s hsS (Ne.symm hsr)
    have ht : 0 < |θ s-θ r| := lt_of_lt_of_le (div_pos hd (by positivity)) hlo
    have hne : θ r≠θ s := by intro he; rw [he,sub_self,abs_zero] at ht; exact (lt_irrefl 0) ht
    calc
      _ ≤ C/|θ s-θ r| := hgram N hN _ (hθ r hr) _ (hθ s hsS) hne hhi
      _ ≤ C/(|(s:ℝ)-r|/(4*N)) :=
        div_le_div_of_nonneg_left hC.le (div_pos hd (by positivity)) hlo
      _ = _ := by field_simp
  have hsuminv : ∑ s∈S.erase r,1/|(s:ℝ)-r| ≤
      2*(1+Real.log ((N+1:ℕ):ℝ)) := by
    calc
      _ ≤ ∑ s∈(Finset.range (N+1)).erase r,1/|(s:ℝ)-r| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset_erase r hS)
          (fun _ _ _ => by positivity)
      _ ≤ 2*∑ j∈Finset.range (N+1),1/((j:ℝ)+1) := hinv
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (by norm_num)
  have hoff : ∑ s∈S.erase r,‖⟪edgePhaseRow N (θ r),edgePhaseRow N (θ s)⟫_ℂ‖ ≤
      8*C*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
    calc
      _ ≤ ∑ s∈S.erase r,(4*C*N)*(1/|(s:ℝ)-r|) := Finset.sum_le_sum hpoint
      _ = (4*C*N)*∑ s∈S.erase r,1/|(s:ℝ)-r| := (Finset.mul_sum _ _ _).symm
      _ ≤ (4*C*N)*(2*(1+Real.log ((N+1:ℕ):ℝ))) :=
        mul_le_mul_of_nonneg_left hsuminv (by positivity)
      _ = _ := by ring
  have hdiag : ‖⟪edgePhaseRow N (θ r),edgePhaseRow N (θ r)⟫_ℂ‖≤(N:ℝ)+1 := by
    simpa [inner_self_eq_norm_sq_to_K] using edge_phase_row_norm N (θ r)
  rw [← Finset.sum_erase_add _ _ hr]
  have hNH := mul_nonneg hN0.le hlog
  nlinarith only [hoff,hdiag,hN1,hNH]

private theorem edge_ratio_mem {N a b:ℝ} (hN:0<N)
    (ha:a∈Icc N (2*N)) (hb:b∈Icc N (2*N)) : a/b∈Icc (0:ℝ) 2 := by
  have hb0 := hN.trans_le hb.1
  exact ⟨div_nonneg (hN.trans_le ha.1).le hb0.le,
    (div_le_iff₀ hb0).mpr (by linarith only [ha.2,hb.1])⟩

private theorem edge_reciprocal_gap {N p a b:ℝ} (hN:0<N)
    (hp:p∈Icc N (2*N)) (ha:a∈Icc N (2*N)) (hb:b∈Icc N (2*N))
    (hd:|b-a|≤N/4) :
    |b-a|/(4*N)≤|p/b-p/a| ∧ |p/b-p/a|≤1/2 := by
  have hp0 := hN.trans_le hp.1
  have ha0 := hN.trans_le ha.1
  have hb0 := hN.trans_le hb.1
  have he : |p/b-p/a| = p*|b-a|/(a*b) := by
    rw [show p/b-p/a = p*(a-b)/(a*b) by field_simp,
      abs_div,abs_mul,abs_of_pos hp0,abs_of_pos (mul_pos ha0 hb0),abs_sub_comm a b]
  have hlo : N*N≤a*b := mul_le_mul ha.1 hb.1 hN.le ha0.le
  have hhi : a*b≤4*N*N := by
    have := mul_le_mul ha.2 hb.2 hb0.le (by positivity : 0≤2*N)
    nlinarith only [this]
  rw [he]
  constructor
  · calc
      _ = (N*|b-a|)/(4*N*N) := by field_simp
      _ ≤ (p*|b-a|)/(4*N*N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp.1 (abs_nonneg _)) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos ha0 hb0) hhi
  · calc
      _ ≤ p*|b-a|/(N*N) := div_le_div_of_nonneg_left (by positivity) (mul_pos hN hN) hlo
      _ ≤ (2*N)*|b-a|/(N*N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _)) (by positivity)
      _ = 2*|b-a|/N := by field_simp
      _ ≤ 1/2 := (div_le_iff₀ hN).mpr (by linarith only [hd])

private theorem edge_linear_gap {N p a b:ℝ} (hN:0<N)
    (hp:p∈Icc N (2*N)) (hd:|b-a|≤N/4) :
    |b-a|/(4*N)≤|b/p-a/p| ∧ |b/p-a/p|≤1/2 := by
  have hp0 := hN.trans_le hp.1
  rw [← sub_div,abs_div,abs_of_pos hp0]
  constructor
  · exact div_le_div_of_nonneg_left (abs_nonneg _) hp0 (by linarith only [hp.2,hN])
  · calc
      _ ≤ |b-a|/N := div_le_div_of_nonneg_left (abs_nonneg _) hN hp.1
      _ ≤ 1/2 := (div_le_iff₀ hN).mpr (by linarith only [hd,hN])

private def edgeFrequency (reciprocal:Bool) (N:ℕ) (p:ℝ) (r:ℕ) : ℝ :=
  if reciprocal then p/((N:ℝ)+r) else ((N:ℝ)+r)/p

private theorem edge_frequency_geometry (reciprocal:Bool) {N:ℕ} (hN:1≤N)
    {p:ℝ} (hp:p∈Icc (N:ℝ) (2*N)) {r s:ℕ} (hr:r≤N) (hs:s≤N)
    (hd:|(s:ℝ)-r|≤(N:ℝ)/4) :
    edgeFrequency reciprocal N p r∈Icc (0:ℝ) 2 ∧
      |(s:ℝ)-r|/(4*N)≤|edgeFrequency reciprocal N p s-edgeFrequency reciprocal N p r| ∧
      |edgeFrequency reciprocal N p s-edgeFrequency reciprocal N p r|≤1/2 := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hm (j:ℕ) (hj:j≤N) : (N:ℝ)+j∈Icc (N:ℝ) (2*N) := by
    have hj' : (j:ℝ)≤N := by exact_mod_cast hj
    constructor <;> linarith only [hj',Nat.cast_nonneg (α:=ℝ) j]
  have he : ((N:ℝ)+s)-((N:ℝ)+r) = (s:ℝ)-r := by ring
  have hd' : |((N:ℝ)+s)-((N:ℝ)+r)|≤(N:ℝ)/4 := by rwa [he]
  cases reciprocal
  · refine ⟨edge_ratio_mem hN0 (hm r hr) hp,?_⟩
    simpa only [edgeFrequency,Bool.false_eq_true,if_false,he] using
      edge_linear_gap hN0 hp hd'
  · refine ⟨edge_ratio_mem hN0 hp (hm r hr),?_⟩
    simpa only [edgeFrequency,if_true,he] using
      edge_reciprocal_gap hN0 hp (hm r hr) (hm s hs) hd'

private theorem edge_norm_sum_sq {E:Type*} [NormedAddCommGroup E]
    (S:Finset ℕ) (f:ℕ→E) :
    ‖∑ r∈S,f r‖^2 ≤ (S.card:ℝ)*∑ r∈S,‖f r‖^2 := by
  have htri := norm_sum_le S f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun r => ‖f r‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have hnn : (0:ℝ)≤∑ r∈S,‖f r‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith only [htri,hcs,hnn,norm_nonneg (∑ r∈S,f r)]

private theorem edge_full_operator_bound :
    ∃ D:ℝ, 0<D ∧ ∀ reciprocal:Bool, ∀ N:ℕ, 1≤N →
      ∀ p∈Icc (N:ℝ) (2*N), ∀ c:ℕ→ℂ,
      ‖∑ r∈Finset.range (N+1),c r • edgePhaseRow N (edgeFrequency reciprocal N p r)‖^2 ≤
        D*N*(1+Real.log ((N+1:ℕ):ℝ))*∑ r∈Finset.range (N+1),‖c r‖^2 := by
  obtain ⟨D,hD,hOp⟩ := edge_phase_operator_bound
  refine ⟨4*D,by positivity,?_⟩
  intro reciprocal N hN p hp c
  let d := N/4+1
  let g : ℕ→ℕ := fun j => j/d
  let S : ℕ→Finset ℕ := fun k => (Finset.range (N+1)).filter (fun j => g j=k)
  have hd : 0<d := by dsimp [d]; omega
  have hg : ∀ j∈Finset.range (N+1),g j∈Finset.range 4 := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    by_contra h
    have hm := Nat.mul_le_mul_left d (show 4≤j/d by simpa only [g] using Nat.le_of_not_gt h)
    have he := Nat.mod_add_div j d
    have hn := Nat.mod_add_div N 4
    have hnmod := Nat.mod_lt N (by norm_num : 0<4)
    dsimp only [d] at hm he
    omega
  have hdiam {k r s:ℕ} (hr:r∈S k) (hs:s∈S k) : |(s:ℝ)-r|≤(N:ℝ)/4 := by
    have hrg : r/d=k := (Finset.mem_filter.mp hr).2
    have hsg : s/d=k := (Finset.mem_filter.mp hs).2
    have hre := Nat.mod_add_div r d
    have hse := Nat.mod_add_div s d
    have hrm := Nat.mod_lt r hd
    have hsm := Nat.mod_lt s hd
    rw [hrg] at hre
    rw [hsg] at hse
    dsimp only [d] at hre hse hrm hsm
    have hrs : r ≤ s+N/4 := by omega
    have hsr : s ≤ r+N/4 := by omega
    have hn : 4*(N/4)≤N := Nat.mul_div_le N 4
    have hn' : ((N/4:ℕ):ℝ)≤(N:ℝ)/4 := by
      have hreal : 4*((N/4:ℕ):ℝ)≤(N:ℝ) := by exact_mod_cast hn
      linarith only [hreal]
    have hrs' : (r:ℝ) ≤ s+(N/4:ℕ) := by exact_mod_cast hrs
    have hsr' : (s:ℝ) ≤ r+(N/4:ℕ) := by exact_mod_cast hsr
    exact abs_le.mpr ⟨by linarith only [hrs',hn'],by linarith only [hsr',hn']⟩
  have hpart (f:ℕ→EuclideanSpace ℂ (Fin (N+1))) :
      ∑ k∈Finset.range 4,∑ r∈S k,f r = ∑ r∈Finset.range (N+1),f r :=
    Finset.sum_fiberwise_of_maps_to hg f
  have hpartR : ∑ k∈Finset.range 4,∑ r∈S k,‖c r‖^2 =
      ∑ r∈Finset.range (N+1),‖c r‖^2 :=
    Finset.sum_fiberwise_of_maps_to hg (fun r => ‖c r‖^2)
  have hlocal (k:ℕ) :
      ‖∑ r∈S k,c r • edgePhaseRow N (edgeFrequency reciprocal N p r)‖^2 ≤
        D*N*(1+Real.log ((N+1:ℕ):ℝ))*∑ r∈S k,‖c r‖^2 := by
    have hsub : S k⊆Finset.range (N+1) := Finset.filter_subset _ _
    apply hOp N hN (S k) hsub (edgeFrequency reciprocal N p)
    · intro r hr
      have hrN : r≤N := by have := Finset.mem_range.mp (hsub hr); omega
      exact (edge_frequency_geometry reciprocal hN hp hrN hrN
        (by rw [sub_self,abs_zero]; positivity)).1
    · intro r hr s hs _
      have hrN : r≤N := by have := Finset.mem_range.mp (hsub hr); omega
      have hsN : s≤N := by have := Finset.mem_range.mp (hsub hs); omega
      exact (edge_frequency_geometry reciprocal hN hp hrN hsN (hdiam hr hs)).2
  rw [← hpart]
  refine (edge_norm_sum_sq (Finset.range 4)
    (fun k => ∑ r∈S k,c r • edgePhaseRow N (edgeFrequency reciprocal N p r))).trans ?_
  simp only [Finset.card_range,Nat.cast_ofNat]
  calc
    _ ≤ 4*∑ k∈Finset.range 4,
        D*N*(1+Real.log ((N+1:ℕ):ℝ))*∑ r∈S k,‖c r‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hlocal k)) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum,hpartR]; ring

private theorem edge_complex_cauchy (S:Finset ℕ) (a b:ℕ→ℂ) :
    ‖∑ j∈S,a j*b j‖^2 ≤ (∑ j∈S,‖a j‖^2)*(∑ j∈S,‖b j‖^2) := by
  have ht : ‖∑ j∈S,a j*b j‖ ≤ ∑ j∈S,‖a j‖*‖b j‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun _ _ => le_of_eq (norm_mul _ _))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun j => ‖a j‖) (fun j => ‖b j‖)
  have hn : (0:ℝ)≤∑ j∈S,‖a j‖*‖b j‖ := by positivity
  nlinarith only [ht,hc,hn,norm_nonneg (∑ j∈S,a j*b j)]

private def edgeEntry (N:ℕ) (θ:ℝ) (j:ℕ) : ℂ :=
  (bagPhysicalHeightWindow (θ*(1+(j:ℝ)/N)):ℂ)*
    Complex.exp (((2*Real.pi*(θ*((N:ℝ)+j)):ℝ):ℂ)*I)

private theorem edge_bilinear_bound :
    ∃ D:ℝ, 0<D ∧ ∀ reciprocal:Bool, ∀ N:ℕ, 1≤N →
      ∀ p∈Icc (N:ℝ) (2*N), ∀ a c:ℕ→ℂ,
      ‖∑ j∈Finset.range (N+1),a j*
        ∑ r∈Finset.range (N+1),c r*edgeEntry N (edgeFrequency reciprocal N p r) j‖^2 ≤
        D*N*(1+Real.log ((N+1:ℕ):ℝ))*
          (∑ j∈Finset.range (N+1),‖a j‖^2)*(∑ r∈Finset.range (N+1),‖c r‖^2) := by
  obtain ⟨D,hD,hOp⟩ := edge_full_operator_bound
  refine ⟨D,hD,?_⟩
  intro reciprocal N hN p hp a c
  let θ := edgeFrequency reciprocal N p
  let X := ∑ r∈Finset.range (N+1),c r • edgePhaseRow N (θ r)
  have heval (S:Finset ℕ) (j:Fin (N+1)) :
      (∑ r∈S,c r • edgePhaseRow N (θ r)) j = ∑ r∈S,c r*edgeEntry N (θ r) j := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,ih]
      rfl
  have he : ∑ j∈Finset.range (N+1),‖∑ r∈Finset.range (N+1),c r*edgeEntry N (θ r) j‖^2 = ‖X‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [X,heval]
    exact (Fin.sum_univ_eq_sum_range _ (N+1)).symm
  have hc := edge_complex_cauchy (Finset.range (N+1)) a
    (fun j => ∑ r∈Finset.range (N+1),c r*edgeEntry N (θ r) j)
  rw [he] at hc
  have hop := hOp reciprocal N hN p hp c
  have hh := mul_le_mul_of_nonneg_left hop
    (show 0≤∑ j∈Finset.range (N+1),‖a j‖^2 by positivity)
  calc
    _ ≤ (∑ j∈Finset.range (N+1),‖a j‖^2)*‖X‖^2 := hc
    _ ≤ _ := by dsimp only [X,θ] at *; nlinarith only [hh]

private theorem edge_normalized_bilinear_bound :
    ∃ D:ℝ, 0<D ∧ ∀ reciprocal:Bool, ∀ N:ℕ, 1≤N →
      ∀ p∈Icc (N:ℝ) (2*N), ∀ a c:ℕ→ℂ,
      (∀ j∈Finset.range (N+1),‖a j‖≤1) →
      (∀ r∈Finset.range (N+1),‖c r‖≤1) →
      ‖(∑ j∈Finset.range (N+1),a j*
        ∑ r∈Finset.range (N+1),c r*edgeEntry N (edgeFrequency reciprocal N p r) j)/(N:ℂ)‖^2 ≤
        D*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨D,hD,hbil⟩ := edge_bilinear_bound
  refine ⟨4*D,by positivity,?_⟩
  intro reciprocal N hN p hp a c ha hc
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have henergy (v:ℕ→ℂ) (hv:∀ j∈Finset.range (N+1),‖v j‖≤1) :
      ∑ j∈Finset.range (N+1),‖v j‖^2≤2*(N:ℝ) := by
    calc
      _ ≤ ∑ _j∈Finset.range (N+1),(1:ℝ) := Finset.sum_le_sum (fun j hj => by
        nlinarith only [hv j hj,norm_nonneg (v j)])
      _ ≤ _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one]; linarith only [hN1]
  have hb := hbil reciprocal N hN p hp a c
  have hnn : 0≤D*N*(1+Real.log ((N+1:ℕ):ℝ)) := by positivity
  have he := mul_le_mul (henergy a ha) (henergy c hc) (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left he hnn
  rw [norm_div,Complex.norm_natCast,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hN0)).mpr
  nlinarith only [hb,hh]

private theorem edge_sum_band (N:ℕ) (f:ℕ→ℂ) :
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

private def edgePrimeSample (N:ℕ) (u:ℕ→ℂ) (j:ℕ) : ℂ :=
  if N+j∈primeProfileBand (N:ℝ) then u (N+j)*smoothAFECutoff (((N+j:ℕ):ℝ)/N) else 0

private def edgePrimeColumn (reciprocal:Bool) (N p:ℕ) (v:ℕ→ℂ) (j:ℕ) : ℂ :=
  if N+j∈primeProfileBand (N:ℝ) then
    v (N+j)*(if reciprocal then (N:ℂ)/(N+j:ℕ)*
      (starRingEnd ℂ) (smoothAFECutoff (((N+j:ℕ):ℝ)/N)) else
      (N:ℂ)/p*smoothAFECutoff (((N+j:ℕ):ℝ)/N)) else 0

private theorem edge_prime_sample_norm {N:ℕ} (hN:1≤N) (u:ℕ→ℂ)
    (hu:∀ q∈primeProfileBand (N:ℝ),‖u q‖≤1) (j:ℕ) : ‖edgePrimeSample N u j‖≤1 := by
  unfold edgePrimeSample
  split_ifs with hj
  · have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    have hj0 : (0:ℝ)<(N+j:ℕ) := by push_cast; positivity
    rw [norm_mul]
    exact (mul_le_mul (hu _ hj) (norm_smoothAFECutoff_le_one (div_pos hj0 hN0))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp

private theorem edge_prime_column_norm (reciprocal:Bool) {N p:ℕ} (hN:1≤N)
    (hp:N≤p) (v:ℕ→ℂ) (hv:∀ r∈primeProfileBand (N:ℝ),‖v r‖≤1) (j:ℕ) :
    ‖edgePrimeColumn reciprocal N p v j‖≤1 := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hj0 : (0:ℝ)<(N+j:ℕ) := by push_cast; positivity
  have hp0 : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hratio {r:ℕ} (hr:N≤r) : ‖(N:ℂ)/(r:ℂ)‖≤1 := by
    rw [norm_div,Complex.norm_natCast,Complex.norm_natCast]
    exact (div_le_one (by exact_mod_cast (by omega : 0<r))).mpr (by exact_mod_cast hr)
  unfold edgePrimeColumn
  split_ifs with hj hmode
  · rw [norm_mul,norm_mul,norm_conj]
    have hcol := mul_le_mul (hratio (r:=N+j) (by omega))
      (norm_smoothAFECutoff_le_one (div_pos hj0 hN0)) (norm_nonneg _) zero_le_one
    exact (mul_le_mul (hv _ hj) hcol (by positivity) zero_le_one).trans_eq (by ring)
  · rw [norm_mul,norm_mul]
    have hcol := mul_le_mul (hratio hp)
      (norm_smoothAFECutoff_le_one (div_pos hj0 hN0)) (norm_nonneg _) zero_le_one
    exact (mul_le_mul (hv _ hj) hcol (by positivity) zero_le_one).trans_eq (by ring)
  · simp

private def edgeFixedFactor (reciprocal:Bool) (N p:ℕ) : ℂ :=
  (2*Real.pi:ℂ)*(if reciprocal then smoothAFECutoff ((p:ℝ)/N)
    else (starRingEnd ℂ) (smoothAFECutoff ((p:ℝ)/N)))

private def edgeFixedEntry (reciprocal:Bool) (N p q r:ℕ) : ℂ :=
  if reciprocal then primeGaussianCubicMainEntry N p q r
    else primeGaussianCubicMainEntry N q r p

private theorem edge_entry_false {N p:ℕ} (hN:1≤N) (hp:N≤p) (j r:ℕ) :
    edgeEntry N (edgeFrequency false N p r) j =
      (bagPhysicalHeightWindow (((N+j:ℕ):ℝ)*(N+r:ℕ)/((p:ℝ)*N)):ℂ)*
      bourgainOscillation (2*Real.pi*(((N+j:ℕ):ℝ)*(N+r:ℕ)/p)) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hw : (((N:ℝ)+r)/p)*(1+(j:ℝ)/N) =
      ((N+j:ℕ):ℝ)*(N+r:ℕ)/((p:ℝ)*N) := by push_cast; field_simp
  have he : (((2*Real.pi*((((N:ℝ)+r)/p)*((N:ℝ)+j)):ℝ):ℂ)*I) =
      I*((2*Real.pi*(((N+j:ℕ):ℝ)*(N+r:ℕ)/p)):ℝ) := by push_cast; ring
  simp only [edgeEntry,edgeFrequency,Bool.false_eq_true,if_false,hw,bourgainOscillation,he]

private theorem edge_entry_true {N:ℕ} (hN:1≤N) (p j r:ℕ) :
    edgeEntry N (edgeFrequency true N p r) j =
      (bagPhysicalHeightWindow ((p:ℝ)*(N+j:ℕ)/(((N+r:ℕ):ℝ)*N)):ℂ)*
      bourgainOscillation (2*Real.pi*((p:ℝ)*(N+j:ℕ)/(N+r:ℕ))) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  have hr0 : (N:ℝ)+r≠0 := by positivity
  have hw : ((p:ℝ)/((N:ℝ)+r))*(1+(j:ℝ)/N) =
      (p:ℝ)*(N+j:ℕ)/(((N+r:ℕ):ℝ)*N) := by push_cast; field_simp
  have he : (((2*Real.pi*(((p:ℝ)/((N:ℝ)+r))*((N:ℝ)+j)):ℝ):ℂ)*I) =
      I*((2*Real.pi*((p:ℝ)*(N+j:ℕ)/(N+r:ℕ))):ℝ) := by push_cast; ring
  simp only [edgeEntry,edgeFrequency,if_true,hw,bourgainOscillation,he]

private theorem edge_prime_factorization (reciprocal:Bool) {N p:ℕ} (hN:1≤N)
    (hp:N≤p) (u v:ℕ→ℂ) :
    ∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
      u q*v r*edgeFixedEntry reciprocal N p q r =
    edgeFixedFactor reciprocal N p*
      ((∑ j∈Finset.range (N+1),edgePrimeSample N u j*
        ∑ r∈Finset.range (N+1),edgePrimeColumn reciprocal N p v r*
          edgeEntry N (edgeFrequency reciprocal N p r) j)/(N:ℂ)) := by
  have hN0 : (N:ℂ)≠0 := by exact_mod_cast (by omega : N≠0)
  rw [edge_sum_band]
  simp_rw [edge_sum_band]
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
  by_cases hjB : N+j∈primeProfileBand (N:ℝ)
  · rw [if_pos hjB]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrB : N+r∈primeProfileBand (N:ℝ)
    · simp only [edgePrimeSample,edgePrimeColumn,if_pos hjB,if_pos hrB]
      cases reciprocal
      · rw [edge_entry_false hN hp]
        simp only [edgeFixedFactor,edgeFixedEntry,Bool.false_eq_true,if_false,primeGaussianCubicMainEntry]
        field_simp
      · rw [edge_entry_true hN]
        simp only [edgeFixedFactor,edgeFixedEntry,if_true,primeGaussianCubicMainEntry]
        field_simp
    · simp [hrB,edgePrimeColumn]
  · simp [hjB,edgePrimeSample]

private theorem edge_fixed_factor_norm (reciprocal:Bool) {N p:ℕ} (hN:1≤N)
    (hp:N≤p) : ‖edgeFixedFactor reciprocal N p‖≤8 := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hp0 : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hv := norm_smoothAFECutoff_le_one (div_pos hp0 hN0)
  have hpi : 0≤2*Real.pi := by positivity
  cases reciprocal <;>
    simp only [edgeFixedFactor,Bool.false_eq_true,if_false,if_true,norm_mul,norm_conj,
      Complex.norm_ofNat,Complex.norm_of_nonneg Real.pi_pos.le] <;>
    nlinarith only [mul_le_mul_of_nonneg_left hv hpi,Real.pi_lt_four]

private theorem edge_prime_slice_bound :
    ∃ C:ℝ, 0<C ∧ ∀ reciprocal:Bool, ∀ N:ℕ, 1≤N →
      ∀ p:ℕ, N≤p → p≤2*N → ∀ u v:ℕ→ℂ,
      (∀ q∈primeProfileBand (N:ℝ),‖u q‖≤1) →
      (∀ r∈primeProfileBand (N:ℝ),‖v r‖≤1) →
      ‖∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
        u q*v r*edgeFixedEntry reciprocal N p q r‖^2 ≤
        C*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨D,hD,hbil⟩ := edge_normalized_bilinear_bound
  refine ⟨64*D,by positivity,?_⟩
  intro reciprocal N hN p hp hp2 u v hu hv
  have hpR : (p:ℝ)∈Icc (N:ℝ) (2*N) := ⟨by exact_mod_cast hp,by exact_mod_cast hp2⟩
  have hh := hbil reciprocal N hN p hpR (edgePrimeSample N u)
    (edgePrimeColumn reciprocal N p v)
    (fun j _ => edge_prime_sample_norm hN u hu j)
    (fun r _ => edge_prime_column_norm reciprocal hN hp v hv r)
  rw [edge_prime_factorization reciprocal hN hp u v,norm_mul,mul_pow]
  have hf : ‖edgeFixedFactor reciprocal N p‖^2≤64 := by
    nlinarith only [edge_fixed_factor_norm reciprocal hN hp,norm_nonneg (edgeFixedFactor reciprocal N p)]
  have hm := mul_le_mul hf hh (sq_nonneg _) (by norm_num : (0:ℝ)≤64)
  calc
    _ ≤ 64*(D*N*(1+Real.log ((N+1:ℕ):ℝ))) := hm
    _ = _ := by ring

/-- Uniform size bound for each actual cubic entry in the physical prime band. -/
theorem primeGaussianCubicMainEntry_norm_le {N:ℕ} (hN:1≤N) {p q r:ℕ}
    (hp:p∈primeProfileBand (N:ℝ)) (hq:q∈primeProfileBand (N:ℝ)) (hr:r∈primeProfileBand (N:ℝ)) :
    ‖primeGaussianCubicMainEntry N p q r‖≤8/(N:ℝ) := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hp0 := hN0.trans (primeProfileBand_mem hN0.le hp).2.1
  have hq0 := hN0.trans (primeProfileBand_mem hN0.le hq).2.1
  have hrN := (primeProfileBand_mem hN0.le hr).2.1
  have hr0 := hN0.trans hrN
  have hpV := norm_smoothAFECutoff_le_one (div_pos hp0 hN0)
  have hqV := norm_smoothAFECutoff_le_one (div_pos hq0 hN0)
  have hrV := norm_smoothAFECutoff_le_one (div_pos hr0 hN0)
  have hw := bagPhysicalHeightWindow.le_one (x:=(p:ℝ)*q/((r:ℝ)*N))
  simp only [primeGaussianCubicMainEntry,norm_mul,norm_div,norm_conj,
    Complex.norm_natCast,norm_bourgainOscillation,mul_one]
  rw [Complex.norm_ofNat,Complex.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  calc
    _ ≤ (2*Real.pi)*1*1*1/r*1 := by
      gcongr
      exact bagPhysicalHeightWindow.nonneg
    _ ≤ 8/(N:ℝ) := by
      simp only [mul_one]
      apply (div_le_div_iff₀ hr0 hN0).mpr
      nlinarith only [Real.pi_lt_four,hrN,hN0]

/-- The physical prime band is contained in the full integer interval. -/
theorem primeProfileBand_card_le_twice (N:ℕ) : ((primeProfileBand (N:ℝ)).card:ℝ)≤2*N := by
  have hc : (primeProfileBand (N:ℝ)).card≤⌊2*(N:ℝ)⌋₊ :=
    (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ioc]; exact Nat.sub_le _ _)
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by positivity))

private def edgeOffEntry (reciprocal:Bool) (N p q r:ℕ) : ℂ :=
  if reciprocal then
    (if p=r ∨ q=r then 0 else primeGaussianCubicMainEntry N p q r)
  else (if q=p ∨ r=p then 0 else primeGaussianCubicMainEntry N q r p)

private theorem edge_off_slice_bound :
    ∃ C:ℝ, 0<C ∧ ∀ reciprocal:Bool, ∀ N:ℕ, 1≤N →
      ∀ p∈primeProfileBand (N:ℝ), ∀ u v:ℕ→ℂ,
      (∀ q∈primeProfileBand (N:ℝ),‖u q‖≤1) →
      (∀ r∈primeProfileBand (N:ℝ),‖v r‖≤1) →
      ‖∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
        u q*v r*edgeOffEntry reciprocal N p q r‖^2 ≤
        C*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hSlice⟩ := edge_prime_slice_bound
  refine ⟨2*C+512,by positivity,?_⟩
  intro reciprocal N hN p hp u v hu hv
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hpR := primeProfileBand_mem hN0.le hp
  have hpN : N≤p := by exact_mod_cast hpR.2.1.le
  have hp2 : p≤2*N := by exact_mod_cast hpR.2.2
  have hscale : 1≤(N:ℝ)*(1+Real.log ((N+1:ℕ):ℝ)) := by
    have := mul_nonneg hN0.le (Real.log_natCast_nonneg (N+1))
    nlinarith only [this,hN1]
  let v' : ℕ→ℂ := fun r => if r=p then 0 else v r
  have hv' (r:ℕ) (hr:r∈primeProfileBand (N:ℝ)) : ‖v' r‖≤1 := by
    dsimp [v']; split_ifs <;> simp_all only [norm_zero,zero_le_one]
  cases reciprocal
  · let u' : ℕ→ℂ := fun q => if q=p then 0 else u q
    have hu' (q:ℕ) (hq:q∈primeProfileBand (N:ℝ)) : ‖u' q‖≤1 := by
      dsimp [u']; split_ifs <;> simp_all only [norm_zero,zero_le_one]
    have he : (∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
        u q*v r*edgeOffEntry false N p q r) =
        ∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
          u' q*v' r*edgeFixedEntry false N p q r := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      by_cases hq:q=p <;> by_cases hr:r=p <;> simp [edgeOffEntry,edgeFixedEntry,u',v',hq,hr]
    rw [he]
    have h := hSlice false N hN p hpN hp2 u' v' hu' hv'
    have hh := mul_nonneg (show 0≤C+512 by positivity) (le_trans zero_le_one hscale)
    nlinarith only [h,hh]
  · let A := ∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
        u q*v' r*edgeFixedEntry true N p q r
    let B := ∑ q∈primeProfileBand (N:ℝ),u q*v' q*primeGaussianCubicMainEntry N p q q
    have he : (∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
        u q*v r*edgeOffEntry true N p q r) = A-B := by
      dsimp only [A,B]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_erase_add _ _ hq]
      simp only [edgeFixedEntry,if_true]
      have hz : u q*v q*edgeOffEntry true N p q q=0 := by simp [edgeOffEntry]
      rw [← Finset.sum_erase_add _ _ hq,hz,add_zero,add_sub_cancel_right]
      apply Finset.sum_congr rfl
      intro r hr
      have hrq := (Finset.mem_erase.mp hr).1
      by_cases hrp:r=p <;> simp [edgeOffEntry,v',hrp,Ne.symm hrq,eq_comm]
    have hA : ‖A‖^2≤C*N*(1+Real.log ((N+1:ℕ):ℝ)) := hSlice true N hN p hpN hp2 u v' hu hv'
    have hB : ‖B‖≤16 := by
      calc
        _ ≤ ∑ q∈primeProfileBand (N:ℝ),‖u q*v' q*primeGaussianCubicMainEntry N p q q‖ := norm_sum_le _ _
        _ ≤ ∑ _q∈primeProfileBand (N:ℝ),8/(N:ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul,norm_mul]
          have hc := mul_le_mul (hu q hq) (hv' q hq) (norm_nonneg _) zero_le_one
          exact (mul_le_mul hc (primeGaussianCubicMainEntry_norm_le hN hp hq hq) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
        _ ≤ 16 := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          have hc := mul_le_mul_of_nonneg_right (primeProfileBand_card_le_twice N) (by positivity : 0≤8/(N:ℝ))
          have he : (2*(N:ℝ))*(8/(N:ℝ))=16 := by field_simp; ring
          exact hc.trans_eq he
    rw [he]
    have ht := norm_sub_le A B
    have hs := sq_nonneg (‖A‖-‖B‖)
    have hb2 : ‖B‖^2≤256 := by nlinarith only [hB,norm_nonneg B]
    nlinarith only [ht,hs,hb2,hA,hscale,norm_nonneg (A-B),norm_nonneg A,norm_nonneg B]

private theorem edge_off_swap (N p q r:ℕ) :
    edgeOffEntry true N p q r = edgeOffEntry true N q p r := by
  simp only [edgeOffEntry,if_true]
  by_cases h:p=r ∨ q=r
  · simp [h,or_comm]
  · have h' : ¬(q=r ∨ p=r) := by simpa only [or_comm] using h
    rw [if_neg h,if_neg h']
    unfold primeGaussianCubicMainEntry
    rw [mul_comm (p:ℝ) q]
    ring

private theorem edge_localized_slice_bound :
    ∃ C:ℝ, 0<C ∧ ∀ reciprocal:Bool, ∀ N:ℕ, 1≤N →
      ∀ E:Finset ℕ, ∀ η:ℕ→ℝ,
      (∀ p∈primeProfileBand (N:ℝ),η p∈Icc (0:ℝ) 1) →
      (∀ p∈primeProfileBand (N:ℝ),p∉E → η p=1) →
      ∀ u v:ℕ→ℂ,
      (∀ q∈primeProfileBand (N:ℝ),‖u q‖≤1) →
      (∀ r∈primeProfileBand (N:ℝ),‖v r‖≤1) →
      ‖∑ p∈primeProfileBand (N:ℝ),(1-(η p:ℂ))*
        ∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
          u q*v r*edgeOffEntry reciprocal N p q r‖^2 ≤
        C*(E.card:ℝ)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hSlice⟩ := edge_off_slice_bound
  refine ⟨C,hC,?_⟩
  intro reciprocal N hN E η hη hsupport u v hu hv
  let S := (primeProfileBand (N:ℝ)).filter (fun p => p∈E)
  let F : ℕ→ℂ := fun p => (1-(η p:ℂ))*
    ∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
      u q*v r*edgeOffEntry reciprocal N p q r
  have hsub : S⊆primeProfileBand (N:ℝ) := Finset.filter_subset _ _
  have hc : (S.card:ℝ)≤E.card := by
    exact_mod_cast Finset.card_le_card (show S⊆E from fun p hp => (Finset.mem_filter.mp hp).2)
  have he : ∑ p∈primeProfileBand (N:ℝ),F p = ∑ p∈S,F p := by
    symm
    apply Finset.sum_subset hsub
    intro p hp hpS
    have hpE : p∉E := by intro he; exact hpS (Finset.mem_filter.mpr ⟨hp,he⟩)
    simp [F,hsupport p hp hpE]
  have hb (p:ℕ) (hp:p∈S) : ‖F p‖^2≤C*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
    have hpB := hsub hp
    have heta := hη p hpB
    have ha : ‖1-(η p:ℂ)‖^2≤1 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_of_nonneg (by linarith only [heta.2])]
      nlinarith only [heta.1,heta.2]
    dsimp only [F]
    rw [norm_mul,mul_pow]
    have hm := mul_le_mul ha (hSlice reciprocal N hN p hpB u v hu hv) (sq_nonneg _) zero_le_one
    simpa only [one_mul] using hm
  change ‖∑ p∈primeProfileBand (N:ℝ),F p‖^2≤_
  rw [he]
  refine (edge_norm_sum_sq S F).trans ?_
  calc
    _ ≤ (S.card:ℝ)*∑ _p∈S,C*N*(1+Real.log ((N+1:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) (Nat.cast_nonneg _)
    _ = C*(S.card:ℝ)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := by gcongr

private def edgeSmoothedCubic (N:ℕ) (η:ℕ→ℝ) : ℂ :=
  ∑ p∈primeProfileBand (N:ℝ),∑ q∈primeProfileBand (N:ℝ),∑ r∈primeProfileBand (N:ℝ),
    (η p:ℂ)*(η q:ℂ)*(η r:ℂ)*edgeOffEntry true N p q r

private theorem edge_cutoff_comparison :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℕ, 1≤N → ∀ E:Finset ℕ, ∀ η:ℕ→ℝ,
      (∀ p∈primeProfileBand (N:ℝ),η p∈Icc (0:ℝ) 1) →
      (∀ p∈primeProfileBand (N:ℝ),p∉E → η p=1) →
      ‖primeGaussianCubicOffDiagonal (N:ℝ)-edgeSmoothedCubic N η‖^2 ≤
        C*(E.card:ℝ)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hlocal⟩ := edge_localized_slice_bound
  refine ⟨9*C,by positivity,?_⟩
  intro N hN E η hη hsupport
  let B := primeProfileBand (N:ℝ)
  let X := ∑ p∈B,(1-(η p:ℂ))*∑ q∈B,∑ r∈B,edgeOffEntry true N p q r
  let Y := ∑ q∈B,(1-(η q:ℂ))*∑ p∈B,∑ r∈B,(η p:ℂ)*edgeOffEntry true N q p r
  let Z := ∑ r∈B,(1-(η r:ℂ))*∑ p∈B,∑ q∈B,(η p:ℂ)*(η q:ℂ)*edgeOffEntry false N r p q
  have hnorm (p:ℕ) (hp:p∈B) : ‖(η p:ℂ)‖≤1 := by
    rw [Complex.norm_of_nonneg (hη p hp).1]
    exact (hη p hp).2
  have hX : ‖X‖^2≤C*(E.card:ℝ)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
    simpa only [one_mul] using hlocal true N hN E η hη hsupport
      (fun _ => 1) (fun _ => 1) (by simp) (by simp)
  have hY : ‖Y‖^2≤C*(E.card:ℝ)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
    simpa only [mul_one] using hlocal true N hN E η hη hsupport
      (fun p => (η p:ℂ)) (fun _ => 1) hnorm (by simp)
  have hZ : ‖Z‖^2≤C*(E.card:ℝ)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) :=
    hlocal false N hN E η hη hsupport (fun p => (η p:ℂ)) (fun q => (η q:ℂ)) hnorm hnorm
  have he : primeGaussianCubicOffDiagonal (N:ℝ)-edgeSmoothedCubic N η=X+Y+Z := by
    have hYeq : Y = ∑ p∈B,∑ q∈B,∑ r∈B,
        (η p:ℂ)*(1-(η q:ℂ))*edgeOffEntry true N p q r := by
      dsimp only [Y]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      rw [edge_off_swap N q p r]
      ring
    have hZeq : Z = ∑ p∈B,∑ q∈B,∑ r∈B,
        (η p:ℂ)*(η q:ℂ)*(1-(η r:ℂ))*edgeOffEntry true N p q r := by
      dsimp only [Z]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      change (1-(η r:ℂ))*((η p:ℂ)*(η q:ℂ)*edgeOffEntry true N p q r)=_
      ring
    rw [hYeq,hZeq]
    have hoff : primeGaussianCubicOffDiagonal (N:ℝ) =
        ∑ p∈B,∑ q∈B,∑ r∈B,edgeOffEntry true N p q r := by
      unfold primeGaussianCubicOffDiagonal
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      rfl
    rw [hoff]
    dsimp only [X,edgeSmoothedCubic,B]
    simp_rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    change edgeOffEntry true N p q r-(η p:ℂ)*(η q:ℂ)*(η r:ℂ)*edgeOffEntry true N p q r=_
    ring
  rw [he]
  have ht := (norm_add_le (X+Y) Z).trans (add_le_add (norm_add_le X Y) (le_refl ‖Z‖))
  have hs1 := sq_nonneg (‖X‖-‖Y‖)
  have hs2 := sq_nonneg (‖X‖-‖Z‖)
  have hs3 := sq_nonneg (‖Y‖-‖Z‖)
  nlinarith only [ht,hX,hY,hZ,hs1,hs2,hs3,norm_nonneg (X+Y+Z),norm_nonneg X,norm_nonneg Y,norm_nonneg Z]

/-- The complete Gaussian cubic with three literal smooth band factors and
both contraction exclusions retained. -/
def primeGaussianCubicSmoothedOffDiagonal (N:ℝ) (η:ℝ→ℝ) : ℂ :=
  ∑ p∈primeProfileBand N,∑ q∈primeProfileBand N,∑ r∈primeProfileBand N,
    (η p:ℂ)*(η q:ℂ)*(η r:ℂ)*
      (if p=r ∨ q=r then 0 else primeGaussianCubicMainEntry N p q r)

private theorem edge_band_cutoff_comparison :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℕ, 1≤N → ∀ H:ℝ, 0<H → ∀ η:ℝ→ℝ,
      (∀ x:ℝ,η x∈Icc (0:ℝ) 1) →
      (∀ x∈Icc ((N:ℝ)+H) (2*N-H),η x=1) →
      ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N η‖^2 ≤
        C*(H+1)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hcompare⟩ := edge_cutoff_comparison
  refine ⟨4*C,by positivity,?_⟩
  intro N hN H hH η hη hone
  let M := ⌈H⌉₊
  let E := Finset.Ioc N (N+M) ∪ Finset.Ioc (2*N-M) (2*N)
  have hM : H≤(M:ℝ) := Nat.le_ceil H
  have hMupper : (M:ℝ)≤H+1 := (Nat.ceil_lt_add_one hH.le).le
  have hsupport (p:ℕ) (hp:p∈primeProfileBand (N:ℝ)) (hpE:p∉E) : η (p:ℝ)=1 := by
    obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem (Nat.cast_nonneg N) hp
    have hpN' : N<p := by exact_mod_cast hpN
    have hp2' : p≤2*N := by exact_mod_cast hp2
    have hnot : ¬(N<p ∧ p≤N+M) ∧ ¬(2*N-M<p ∧ p≤2*N) := by
      simpa only [E,Finset.mem_union,Finset.mem_Ioc,not_or] using hpE
    have hlo : N+M<p := by omega
    have hhi : p+M≤2*N := by omega
    have hloR : (N:ℝ)+M<(p:ℝ) := by exact_mod_cast hlo
    have hhiR : (p:ℝ)+M≤2*(N:ℝ) := by exact_mod_cast hhi
    exact hone p ⟨by linarith only [hloR,hM],by linarith only [hhiR,hM]⟩
  have hcard : (E.card:ℝ)≤2*(H+1) := by
    have hc := Finset.card_union_le (Finset.Ioc N (N+M)) (Finset.Ioc (2*N-M) (2*N))
    simp only [Nat.card_Ioc] at hc
    have hc' : E.card≤2*M := by dsimp only [E]; omega
    have hcR : (E.card:ℝ)≤2*(M:ℝ) := by exact_mod_cast hc'
    linarith only [hcR,hMupper]
  have hb := hcompare N hN E (fun p => η (p:ℝ)) (fun p _ => hη p) hsupport
  change ‖primeGaussianCubicOffDiagonal (N:ℝ)-edgeSmoothedCubic N (fun p => η (p:ℝ))‖^2≤_
  refine hb.trans ?_
  calc
    _ ≤ C*(2*(H+1))^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by gcongr
    _ = _ := by ring

/-- Smoothly removing growing boundary strips has a bilinear, rather than
termwise, cost in the actual complete noncontracting Gaussian cubic. -/
theorem exists_primeGaussianCubic_smooth_band_comparison :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℕ, 1≤N → ∀ H:ℝ, 0<H → H<(N:ℝ)/2 →
      ∃ η:ℝ→ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        (∀ x:ℝ,η x∈Icc (0:ℝ) 1) ∧
        (∀ x:ℝ,x∉Ioo (N:ℝ) (2*N) → η x=0) ∧
        (∀ x∈Icc ((N:ℝ)+H) (2*N-H),η x=1) ∧
        ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N η‖^2 ≤
          C*(H+1)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hcompare⟩ := edge_band_cutoff_comparison
  refine ⟨C,hC,?_⟩
  intro N hN H hH hHN
  let η : ContDiffBump (3*(N:ℝ)/2) :=
    ⟨(N:ℝ)/2-H,(N:ℝ)/2,by linarith only [hHN],by linarith only [hH]⟩
  have hη : ∀ x:ℝ,η x∈Icc (0:ℝ) 1 := fun _ => ⟨η.nonneg,η.le_one⟩
  have hzero (x:ℝ) (hx:x∉Ioo (N:ℝ) (2*N)) : η x=0 := by
    apply η.zero_of_le_dist
    rw [Real.dist_eq,abs_sub_comm]
    change (N:ℝ)/2 ≤ |3*(N:ℝ)/2-x|
    simp only [Set.mem_Ioo,not_and_or,not_lt] at hx
    rcases hx with hlo | hhi
    · exact (by linarith only [hlo] : (N:ℝ)/2≤3*(N:ℝ)/2-x).trans (le_abs_self _)
    · exact (by linarith only [hhi] : (N:ℝ)/2≤-(3*(N:ℝ)/2-x)).trans (neg_le_abs _)
  have hone (x:ℝ) (hx:x∈Icc ((N:ℝ)+H) (2*N-H)) : η x=1 := by
    apply η.one_of_mem_closedBall
    rw [Metric.mem_closedBall,Real.dist_eq]
    change |x-3*(N:ℝ)/2|≤(N:ℝ)/2-H
    exact abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
  refine ⟨η,η.contDiff,η.hasCompactSupport,hη,hzero,hone,?_⟩
  exact hcompare N hN H hH η hη hone

private theorem edge_quarter_small :
    ∀ᶠ N:ℕ in atTop, 1≤N ∧ (N:ℝ)^((1:ℝ)/4)<(N:ℝ)/2 := by
  have ht : Tendsto (fun N:ℕ => (N:ℝ)^((1:ℝ)/4)/(N:ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)).comp
      tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hN0 : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
    change (N:ℝ)^(-(3/4:ℝ))=(N:ℝ)^((1:ℝ)/4)/(N:ℝ)
    rw [show -(3/4:ℝ)=(1:ℝ)/4-1 by ring,Real.rpow_sub_one hN0]
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))] with N hN hsmall
  refine ⟨hN,?_⟩
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have h := (div_lt_iff₀ hN0).mp hsmall
  linarith only [h]

private theorem edge_log_power_limit :
    Tendsto (fun N:ℕ => (Real.log (N:ℝ))^5/(N:ℝ)^((1:ℝ)/2)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s:=(1:ℝ)/2) 5 (by norm_num)).tendsto_div_nhds_zero
  have he : (fun x:ℝ => Real.log x^(5:ℝ)/x^((1:ℝ)/2)) =
      (fun x:ℝ => Real.log x^(5:ℕ)/x^((1:ℝ)/2)) := by
    funext x
    rw [show (5:ℝ)=((5:ℕ):ℝ) from rfl,Real.rpow_natCast]
  rw [he] at h
  exact h.comp tendsto_natCast_atTop_atTop

private theorem edge_quarter_majorant {C:ℝ} (hC:0<C) {N:ℕ}
    (hN:(2:ℝ)≤N) (hlog:1≤Real.log (N:ℝ)) :
    ((Real.log (N:ℝ))^2/(N:ℝ))^2 *
      (C*((N:ℝ)^((1:ℝ)/4)+1)^2*N*(1+Real.log ((N+1:ℕ):ℝ))) ≤
        12*C*((Real.log (N:ℝ))^5/(N:ℝ)^((1:ℝ)/2)) := by
  have hN0 : (0:ℝ)<N := by linarith only [hN]
  have hN1 : (1:ℝ)≤N := by linarith only [hN]
  have hR0 := Real.rpow_pos_of_pos hN0 ((1:ℝ)/2)
  have hH1 := Real.one_le_rpow hN1 (by norm_num : (0:ℝ)≤1/4)
  have hHsq : ((N:ℝ)^((1:ℝ)/4))^2=(N:ℝ)^((1:ℝ)/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    norm_num
  have hRsq : ((N:ℝ)^((1:ℝ)/2))^2=(N:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    norm_num
  have hH : ((N:ℝ)^((1:ℝ)/4)+1)^2≤4*(N:ℝ)^((1:ℝ)/2) := by
    nlinarith only [hH1,hHsq]
  have hlog' : 1+Real.log ((N+1:ℕ):ℝ)≤3*Real.log (N:ℝ) := by
    have hn : ((N+1:ℕ):ℝ)≤(N:ℝ)^2 := by push_cast; nlinarith only [hN]
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(N+1:ℕ)) hn
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,hlog]
  calc
    _ ≤ ((Real.log (N:ℝ))^2/(N:ℝ))^2 *
        (C*(4*(N:ℝ)^((1:ℝ)/2))*N*(3*Real.log (N:ℝ))) := by gcongr
    _ = _ := by field_simp; nlinarith only [hRsq]

/-- The actual sharp cubic admits smooth full-band representatives with growing
N^(1/4) boundary strips and error o(N/log(N)^2). The signed interior remains. -/
theorem exists_primeGaussianCubic_smooth_band_negligible_error :
    ∃ η:ℕ→ℝ→ℝ,
      (∀ᶠ N:ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ x:ℝ,η N x∈Icc (0:ℝ) 1) ∧
        (∀ x:ℝ,x∉Ioo (N:ℝ) (2*N) → η N x=0) ∧
        (∀ x∈Icc ((N:ℝ)+(N:ℝ)^((1:ℝ)/4)) (2*N-(N:ℝ)^((1:ℝ)/4)),η N x=1)) ∧
      Tendsto (fun N:ℕ => (Real.log (N:ℝ))^2/(N:ℝ)*
        ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N (η N)‖)
        atTop (𝓝 0) := by
  obtain ⟨C,hC,hcompare⟩ := exists_primeGaussianCubic_smooth_band_comparison
  let Good : ℕ→Prop := fun N => 1≤N ∧ (N:ℝ)^((1:ℝ)/4)<(N:ℝ)/2
  have hex (N:ℕ) : ∃ η:ℝ→ℝ, Good N →
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      (∀ x:ℝ,η x∈Icc (0:ℝ) 1) ∧
      (∀ x:ℝ,x∉Ioo (N:ℝ) (2*N) → η x=0) ∧
      (∀ x∈Icc ((N:ℝ)+(N:ℝ)^((1:ℝ)/4)) (2*N-(N:ℝ)^((1:ℝ)/4)),η x=1) ∧
      ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N η‖^2 ≤
        C*((N:ℝ)^((1:ℝ)/4)+1)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
    by_cases hg:Good N
    · have hN0 : (0:ℝ)<N := by exact_mod_cast (by have := hg.1; omega : 0<N)
      obtain ⟨η,hη⟩ := hcompare N hg.1 ((N:ℝ)^((1:ℝ)/4))
        (Real.rpow_pos_of_pos hN0 _) hg.2
      exact ⟨η,fun _ => hη⟩
    · exact ⟨fun _ => 0,fun h => (hg h).elim⟩
  choose η hη using hex
  refine ⟨η,?_,?_⟩
  · filter_upwards [edge_quarter_small] with N hN
    obtain ⟨h1,h2,h3,h4,h5,_⟩ := hη N hN
    exact ⟨h1,h2,h3,h4,h5⟩
  let e : ℕ→ℝ := fun N => (Real.log (N:ℝ))^2/(N:ℝ)*
    ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N (η N)‖
  have he0 (N:ℕ) : 0≤e N := by dsimp [e]; positivity
  have hdom : ∀ᶠ N:ℕ in atTop,
      (e N)^2 ≤ 12*C*((Real.log (N:ℝ))^5/(N:ℝ)^((1:ℝ)/2)) := by
    have hl : ∀ᶠ N:ℕ in atTop,1≤Real.log (N:ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    have hn : ∀ᶠ N:ℕ in atTop,(2:ℝ)≤N := tendsto_natCast_atTop_atTop.eventually_ge_atTop 2
    filter_upwards [edge_quarter_small,hl,hn] with N hN hlog hlarge
    have hb := (hη N hN).2.2.2.2.2
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ((Real.log (N:ℝ))^2/(N:ℝ)))
    dsimp only [e]
    rw [mul_pow]
    exact hm.trans (edge_quarter_majorant hC hlarge hlog)
  have hsq : Tendsto (fun N => (e N)^2) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun N => sq_nonneg (e N))) hdom
      (by simpa only [mul_zero] using edge_log_power_limit.const_mul (12*C))
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_zero] at hsqrt
  have heq : (fun N => Real.sqrt ((e N)^2))=e := by
    funext N
    exact Real.sqrt_sq (he0 N)
  change Tendsto (fun N => Real.sqrt ((e N)^2)) atTop (𝓝 0) at hsqrt
  rw [heq] at hsqrt
  exact hsqrt

private theorem controlled_cutoff_comparison :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℕ, 1≤N → ∀ H:ℝ, 0<H → H<(N:ℝ)/2 →
      ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N
        (BAGTrace.bagCubicControlledBandCutoff (N:ℝ) H)‖^2 ≤
          C*(H+1)^2*N*(1+Real.log ((N+1:ℕ):ℝ)) := by
  obtain ⟨C,hC,hcompare⟩ := edge_band_cutoff_comparison
  refine ⟨C,hC,?_⟩
  intro N hN H hH hHN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  let η := BAGTrace.bagCubicControlledBandCutoff (N:ℝ) H
  obtain ⟨_,_,hη,_,hone⟩ := BAGTrace.bagCubicControlledBandCutoff_properties
    ⟨N,hN0⟩ ⟨H,hH,hHN⟩
  exact hcompare N hN H hH η hη hone

/-- The explicitly controlled shrinking cutoff retains the original sharp/smooth
error at the physical scale. Its normalized relative edges have uniform first
variation and every higher derivative budget from ChiCubicControlledCutoff. -/
theorem primeGaussianCubic_controlled_cutoff_negligible_error :
    Tendsto (fun N:ℕ => (Real.log (N:ℝ))^2/(N:ℝ)*
      ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N
        (BAGTrace.bagCubicControlledBandCutoff (N:ℝ) ((N:ℝ)^((1:ℝ)/4)))‖)
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hcompare⟩ := controlled_cutoff_comparison
  let η := fun N:ℕ => BAGTrace.bagCubicControlledBandCutoff (N:ℝ) ((N:ℝ)^((1:ℝ)/4))
  let e : ℕ→ℝ := fun N => (Real.log (N:ℝ))^2/(N:ℝ)*
    ‖primeGaussianCubicOffDiagonal (N:ℝ)-primeGaussianCubicSmoothedOffDiagonal N (η N)‖
  have he0 (N:ℕ) : 0≤e N := by dsimp [e]; positivity
  have hdom : ∀ᶠ N:ℕ in atTop,
      (e N)^2 ≤ 12*C*((Real.log (N:ℝ))^5/(N:ℝ)^((1:ℝ)/2)) := by
    have hl : ∀ᶠ N:ℕ in atTop,1≤Real.log (N:ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    have hn : ∀ᶠ N:ℕ in atTop,(2:ℝ)≤N := tendsto_natCast_atTop_atTop.eventually_ge_atTop 2
    filter_upwards [edge_quarter_small,hl,hn] with N hN hlog hlarge
    have hN0 : (0:ℝ)<N := by exact_mod_cast (by have := hN.1; omega : 0<N)
    have hb := hcompare N hN.1 ((N:ℝ)^((1:ℝ)/4))
      (Real.rpow_pos_of_pos hN0 _) hN.2
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ((Real.log (N:ℝ))^2/(N:ℝ)))
    dsimp only [e]
    rw [mul_pow]
    exact hm.trans (edge_quarter_majorant hC hlarge hlog)
  have hsq : Tendsto (fun N => (e N)^2) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun N => sq_nonneg (e N))) hdom
      (by simpa only [mul_zero] using edge_log_power_limit.const_mul (12*C))
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Real.sqrt_zero] at hsqrt
  have heq : (fun N => Real.sqrt ((e N)^2))=e := by
    funext N
    exact Real.sqrt_sq (he0 N)
  change Tendsto (fun N => Real.sqrt ((e N)^2)) atTop (𝓝 0) at hsqrt
  rw [heq] at hsqrt
  exact hsqrt

end RHTower
