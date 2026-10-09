import GaloisForLFunctions.HTGeometry.ZeroDivisorCount

/-!
# Symmetric Rouché: a slit-plane quotient on a circle preserves the zero count

Let `F, G` be holomorphic on a neighbourhood of `closedBall c R`, `0 < t < R`, with `G ≠ 0` on the
circle `|z − c| = t` and `F/G` in the slit plane `ℂ ∖ (−∞, 0]` there.  Then `F` and `G` have the
same number of zeros, counted with multiplicity, in `|z − c| < t`
(`zeroSumBall_eq_of_quotient_mem_slitPlane`).  If moreover `G` has no zero in the closed disc,
neither has `F` in the open disc (`zeroFree_ball_of_quotient_mem_slitPlane`).

Proof.  `H_s = (1 − s)G + sF = G · ((1 − s) + s F/G)` does not vanish on the circle for
`s ∈ [0, 1]`, because `(1 − s) + sw = 0` forces `w = −(1 − s)/s ≤ 0`.  The zero count of `H_s` is
locally constant in `s` (`exists_eps_zeroSumBall_eq`: `‖H_s − H_{s₀}‖ ≤ |s − s₀| sup ‖F − G‖`),
hence constant on the connected interval `[0, 1]`.
-/

open Complex Metric Set Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- On the slit plane, `(1 − s) + s w ≠ 0` for `s ∈ [0, 1]`. -/
theorem one_sub_add_mul_ne_zero_of_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ((1 - s : ℝ) : ℂ) + (s : ℂ) * w ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.zero_re, Complex.add_im, Complex.mul_im, zero_add, Complex.zero_im] at hre him
  rcases mem_slitPlane_iff.1 hw with hpos | hne
  · nlinarith [mul_nonneg hs0 hpos.le]
  · rcases eq_or_lt_of_le hs0 with h0 | hpos
    · rw [← h0] at hre; norm_num at hre
    · exact hne (by
        have : s * w.im = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact h)

/-- A zero inside the circle of a function nonvanishing on the circle has multiplicity `≥ 1`. -/
theorem one_le_zeroMult_of_zero {c : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hne : ∀ ζ ∈ sphere c t, f ζ ≠ 0)
    {z : ℂ} (hz : z ∈ ball c t) (hfz : f z = 0) : 1 ≤ zeroMult f z := by
  have hballR : ball c R ⊆ U := ball_subset_closedBall.trans hsub
  have han : AnalyticOnNhd ℂ f (ball c R) := (hf.analyticOnNhd hU).mono hballR
  have hzR : z ∈ ball c R := ball_subset_ball htR.le hz
  have hζ : c + (t : ℂ) ∈ sphere c t := by
    rw [mem_sphere, dist_eq_norm]; simp [abs_of_pos ht]
  have hζR : c + (t : ℂ) ∈ ball c R := by
    rw [mem_ball, dist_eq_norm]; simpa [abs_of_pos ht] using htR
  have hfin : analyticOrderAt f z ≠ ⊤ := by
    refine han.analyticOrderAt_ne_top_of_isPreconnected (convex_ball c R).isPreconnected hζR hzR ?_
    have h0 : analyticOrderAt f (c + (t : ℂ)) = 0 :=
      ((han _ hζR).analyticOrderAt_eq_zero).2 (hne _ hζ)
    rw [h0]; exact ENat.zero_ne_top
  have hnz : analyticOrderAt f z ≠ 0 := fun h => ((han z hzR).analyticOrderAt_eq_zero.1 h) hfz
  unfold zeroMult
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hn, ENat.toNat_coe]
  rw [← hn] at hnz
  have : n ≠ 0 := fun h => hnz (by rw [h]; rfl)
  omega

/-- **Symmetric Rouché.**  If `G ≠ 0` and `F/G ∈ slitPlane` on the circle `|z − c| = t`, then `F`
and `G` have the same zero count in `|z − c| < t`. -/
theorem zeroSumBall_eq_of_quotient_mem_slitPlane {F G : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {t R : ℝ}
    (ht : 0 < t) (htR : t < R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hG : DifferentiableOn ℂ G U)
    (hG0 : ∀ ζ ∈ sphere c t, G ζ ≠ 0)
    (hslit : ∀ ζ ∈ sphere c t, F ζ / G ζ ∈ slitPlane) :
    zeroSumBall F c t = zeroSumBall G c t := by
  set H : ℝ → ℂ → ℂ := fun s z => ((1 - s : ℝ) : ℂ) * G z + (s : ℂ) * F z with hH
  have hHd : ∀ s, DifferentiableOn ℂ (H s) U := fun s =>
    (hG.const_mul _).add (hF.const_mul _)
  have hHne : ∀ s : Set.Icc (0 : ℝ) 1, ∀ ζ ∈ sphere c t, H s ζ ≠ 0 := by
    intro s ζ hζ
    have hfac : H s ζ = G ζ * (((1 - s : ℝ) : ℂ) + (s : ℂ) * (F ζ / G ζ)) := by
      simp only [hH]
      field_simp [hG0 ζ hζ]
    rw [hfac]
    exact mul_ne_zero (hG0 ζ hζ)
      (one_sub_add_mul_ne_zero_of_mem_slitPlane (hslit ζ hζ) s.2.1 s.2.2)
  -- a uniform bound for `F − G` on the closed disc
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    ((hF.sub hG).mono hsub).continuousOn
  have hdiff : ∀ s s' : ℝ, ∀ z ∈ closedBall c R, ‖H s' z - H s z‖ ≤ |s' - s| * M := by
    intro s s' z hz
    have : H s' z - H s z = ((s' - s : ℝ) : ℂ) * (F z - G z) := by
      simp only [hH]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM z hz) (abs_nonneg _)
  -- the zero count is locally constant on `[0, 1]`
  set φ : Set.Icc (0 : ℝ) 1 → ℂ := fun s => zeroSumBall (H s) c t with hφ
  have hloc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s₀
    obtain ⟨ε, hε, hεH⟩ := exists_eps_zeroSumBall_eq ht htR hU hsub (hHd s₀) (hHne s₀)
    have hδ : 0 < ε / (|M| + 1) := by positivity
    rw [Metric.eventually_nhds_iff]
    refine ⟨ε / (|M| + 1), hδ, fun s hs => ?_⟩
    rw [Subtype.dist_eq, Real.dist_eq] at hs
    refine (hεH (H s) (hHd s) fun z hz => ?_).2
    calc ‖H s z - H s₀ z‖ ≤ |(s : ℝ) - s₀| * M := hdiff s₀ s z hz
      _ ≤ |(s : ℝ) - s₀| * (|M| + 1) := by
          gcongr; linarith [le_abs_self M]
      _ ≤ ε / (|M| + 1) * (|M| + 1) := by gcongr
      _ = ε := by field_simp
  have h01 := hloc.apply_eq_of_preconnectedSpace ⟨0, by norm_num, by norm_num⟩
    ⟨1, by norm_num, by norm_num⟩
  have hH0 : H 0 = G := by funext z; simp [hH]
  have hH1 : H 1 = F := by funext z; simp [hH]
  simp only [hφ, hH0, hH1] at h01
  exact h01.symm

/-- **Zero-freeness from a slit-plane quotient.**  If `G` has no zero in the closed disc
`|z − c| ≤ t` and `F/G` omits `(−∞, 0]` on the circle `|z − c| = t`, then `F` has no zero in the
open disc. -/
theorem zeroFree_ball_of_quotient_mem_slitPlane {F G : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {t R : ℝ}
    (ht : 0 < t) (htR : t < R) (hU : IsOpen U) (hsub : closedBall c R ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hG : DifferentiableOn ℂ G U)
    (hG0 : ∀ z ∈ closedBall c t, G z ≠ 0)
    (hslit : ∀ ζ ∈ sphere c t, F ζ / G ζ ∈ slitPlane) :
    ∀ z ∈ ball c t, F z ≠ 0 := by
  have hGs : ∀ ζ ∈ sphere c t, G ζ ≠ 0 := fun ζ hζ => hG0 ζ (sphere_subset_closedBall hζ)
  have hFs : ∀ ζ ∈ sphere c t, F ζ ≠ 0 := fun ζ hζ h0 =>
    slitPlane_ne_zero (hslit ζ hζ) (by rw [h0, zero_div])
  have heq := zeroSumBall_eq_of_quotient_mem_slitPlane ht htR hU hsub hF hG hGs hslit
  obtain ⟨ZG, hZGball, hZGzero, hZGsum⟩ := exists_zeroSet_zeroSumBall ht htR hU hsub hG hGs
  have hZGempty : ZG = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun ρ hρ => ?_
    exact hG0 ρ (ball_subset_closedBall (hZGball ρ hρ)) ((hZGzero ρ (hZGball ρ hρ)).2 hρ)
  obtain ⟨ZF, hZFball, hZFzero, hZFsum⟩ := exists_zeroSet_zeroSumBall ht htR hU hsub hF hFs
  intro z hz hFz
  have hzZ : z ∈ ZF := (hZFzero z hz).1 hFz
  have hsum0 : (∑ ρ ∈ ZF, (zeroMult F ρ : ℂ)) = 0 := by
    rw [← hZFsum, heq, hZGsum, hZGempty, Finset.sum_empty]
  have hpos : 1 ≤ ∑ ρ ∈ ZF, zeroMult F ρ :=
    le_trans (one_le_zeroMult_of_zero ht htR hU hsub hF hFs hz hFz)
      (Finset.single_le_sum (fun ρ _ => Nat.zero_le _) hzZ)
  have hcast : ((∑ ρ ∈ ZF, zeroMult F ρ : ℕ) : ℂ) = 0 := by push_cast; exact hsum0
  have : (∑ ρ ∈ ZF, zeroMult F ρ) = 0 := by exact_mod_cast hcast
  omega

end

end GaloisForLFunctions.HTGeometry
