import GaloisForLFunctions.Bottcher.MontelNormal
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneExhaustion
import Mathlib.Analysis.Complex.Convex

open Complex Metric Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

private def upperPatchCauchyRadius (m : ℕ) : ℝ :=
  1 / (2 * ((m : ℝ) + 1))

private theorem upperPatchCauchyRadius_pos (m : ℕ) :
    0 < upperPatchCauchyRadius m := by
  simp [upperPatchCauchyRadius]
  positivity

private theorem upperPatch_ball_subset_upperHalfPlane (m : ℕ) {z : ℂ}
    (hz : z ∈ upperPatch m) :
    ball z (upperPatchCauchyRadius m) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hnorm : ‖w - z‖ < upperPatchCauchyRadius m := by
    simpa [mem_ball, dist_eq] using hw
  have himnorm : |w.im - z.im| ≤ ‖w - z‖ := by
    simpa [Complex.sub_im] using abs_im_le_norm (w - z)
  have himlt : |w.im - z.im| < upperPatchCauchyRadius m :=
    lt_of_le_of_lt himnorm hnorm
  have hrhalf : upperPatchCauchyRadius m < (1 : ℝ) / ((m : ℝ) + 1) := by
    rw [upperPatchCauchyRadius]
    apply one_div_lt_one_div_of_lt
    · positivity
    · have hmpos : 0 < (m : ℝ) + 1 := by positivity
      linarith
  rw [abs_lt] at himlt
  have hzlow : (1 : ℝ) / ((m : ℝ) + 1) ≤ z.im := hz.1
  have hrz : upperPatchCauchyRadius m < z.im := lt_of_lt_of_le hrhalf hzlow
  have hzw : z.im - upperPatchCauchyRadius m < w.im := by linarith [himlt.1]
  change 0 < w.im
  linarith

private theorem convex_upperPatch (m : ℕ) : Convex ℝ (upperPatch m) := by
  have hshape : upperPatch m =
      {z : ℂ | (1 : ℝ) / (m + 1) ≤ z.im} ∩
        closedBall 0 ((m : ℝ) + 1) := by
    ext z
    simp [upperPatch, mem_closedBall]
  rw [hshape]
  exact (convex_halfSpace_im_ge _).inter (convex_closedBall _ _)

private theorem equicontinuous_family_on_upperPatch
    {ι : Type*} {F : ι → ℂ → ℂ} {C : ℝ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) {z : ℂ | 0 < z.im})
    (hbd : ∀ i, ∀ z : ℂ, 0 < z.im → ‖F i z‖ ≤ C)
    (m : ℕ) :
    Equicontinuous (fun (i : ι) (p : ↥(upperPatch m)) => F i p.1) := by
  let R : ℝ := upperPatchCauchyRadius m
  let L : ℝ := 2 * C / R
  have hR : 0 < R := upperPatchCauchyRadius_pos m
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hderiv : ∀ i, ∀ z ∈ upperPatch m, ‖deriv (F i) z‖ ≤ L := by
    intro i z hz
    have hlocaldiff : DifferentiableOn ℂ (F i) (ball z R) :=
      (hF i).mono (upperPatch_ball_subset_upperHalfPlane m hz)
    have hlocalbd : ∀ w ∈ ball z R, ‖F i w‖ ≤ C := by
      intro w hw
      exact hbd i w (upperPatch_ball_subset_upperHalfPlane m hz hw)
    exact Bottcher.norm_deriv_le_of_bounded_on_ball hR hlocaldiff hlocalbd z
      (mem_ball_self (half_pos hR))
  have hhas : ∀ i, ∀ z ∈ upperPatch m,
      HasDerivAt (F i) (deriv (F i) z) z := by
    intro i z hz
    exact ((hF i).differentiableAt
      (hopen.mem_nhds (upperPatch_subset m hz))).hasDerivAt
  refine Metric.equicontinuous_of_continuity_modulus (fun d => L * d) ?_ _ ?_
  · have hcont : Continuous (fun d : ℝ => L * d) := continuous_const.mul continuous_id
    simpa using hcont.tendsto 0
  · intro x y i
    rw [Complex.dist_eq, Subtype.dist_eq, Complex.dist_eq]
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hhas i z hz).hasDerivWithinAt) (hderiv i)
      (convex_upperPatch m) y.2 x.2

private theorem exists_subseq_tendstoUniformlyOn_upperPatch
    {F : ℕ → ℂ → ℂ} {C : ℝ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im})
    (hbd : ∀ n, ∀ z : ℂ, 0 < z.im → ‖F n z‖ ≤ C)
    (ψ : ℕ → ℕ) (m : ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun k => F (ψ (σ k))) g atTop (upperPatch m) := by
  classical
  haveI hcs : CompactSpace ↥(upperPatch m) :=
    isCompact_iff_compactSpace.mp (isCompact_upperPatch m)
  have hcont : ∀ n, ContinuousOn (F (ψ n)) (upperPatch m) := fun n =>
    ((hF (ψ n)).continuousOn).mono (upperPatch_subset m)
  let cmap : ℕ → C(↥(upperPatch m), ℂ) :=
    fun n => ⟨(upperPatch m).restrict (F (ψ n)), (hcont n).restrict⟩
  let bcfF : ℕ → ↥(upperPatch m) →ᵇ ℂ := fun n => mkOfCompact (cmap n)
  have hval : ∀ n (x : ↥(upperPatch m)), bcfF n x = F (ψ n) (x : ℂ) :=
    fun n x => rfl
  have hG0 : Equicontinuous
      (fun (n : ℕ) (p : ↥(upperPatch m)) => F (ψ n) (p : ℂ)) :=
    equicontinuous_family_on_upperPatch (fun n => hF (ψ n))
      (fun n => hbd (ψ n)) m
  set A : Set (↥(upperPatch m) →ᵇ ℂ) := Set.range bcfF with hA
  have hsec : ∀ a : ↥A, bcfF ((a.2).choose) = (a : ↥(upperPatch m) →ᵇ ℂ) :=
    fun a => (a.2).choose_spec
  have hHcoe : ((↑) : ↥A → ↥(upperPatch m) → ℂ) =
      (fun (n : ℕ) (p : ↥(upperPatch m)) => F (ψ n) (p : ℂ)) ∘
        (fun a : ↥A => (a.2).choose) := by
    funext a x
    exact (DFunLike.congr_fun (hsec a) x).symm.trans (hval _ x)
  have hH : Equicontinuous ((↑) : ↥A → ↥(upperPatch m) → ℂ) := by
    rw [hHcoe]
    exact hG0.comp _
  have hin : ∀ (f : ↥(upperPatch m) →ᵇ ℂ) (x : ↥(upperPatch m)),
      f ∈ A → f x ∈ closedBall (0 : ℂ) C := by
    intro f x hf
    obtain ⟨n, rfl⟩ := hf
    rw [mem_closedBall, dist_zero_right, hval n x]
    exact hbd (ψ n) (x : ℂ) (upperPatch_subset m x.2)
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C)
      (isCompact_closedBall _ _) A hin hH
  have hmem : ∀ n, bcfF n ∈ closure A := fun n => subset_closure (mem_range_self n)
  obtain ⟨g, -, σ, hσmono, hσtends⟩ := hcompact.tendsto_subseq hmem
  have hunif := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).mp hσtends
  simp only [Function.comp_apply] at hunif
  let G : ℂ → ℂ := fun z => if h : z ∈ upperPatch m then g ⟨z, h⟩ else 0
  have hGcoe : (G ∘ ((↑) : ↥(upperPatch m) → ℂ)) =
      (g : ↥(upperPatch m) → ℂ) := by
    funext x
    show (if h : (x : ℂ) ∈ upperPatch m then g ⟨(x : ℂ), h⟩ else 0) = g x
    rw [dif_pos x.2]
  have hfameq : (fun k => ((bcfF (σ k)) : ↥(upperPatch m) → ℂ)) =
      (fun k (x : ↥(upperPatch m)) => F (ψ (σ k)) (x : ℂ)) := by
    funext k x
    exact hval (σ k) x
  rw [hfameq, ← hGcoe] at hunif
  exact ⟨σ, hσmono, G,
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mpr hunif⟩

/-- Domain Montel theorem on the open upper half-plane. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_upperHalfPlane
    {F : ℕ → ℂ → ℂ} {C : ℝ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im})
    (hbd : ∀ n, ∀ z : ℂ, 0 < z.im → ‖F n z‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun k => F (φ k)) g atTop {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im → ‖g z‖ ≤ C := by
  classical
  choose σ hσmono G hG using
    exists_subseq_tendstoUniformlyOn_upperPatch hF hbd
  obtain ⟨Ψ, hΨ0, hΨs⟩ : ∃ Ψ : ℕ → (ℕ → ℕ), Ψ 0 = id ∧
      ∀ j, Ψ (j + 1) = Ψ j ∘ σ (Ψ j) j :=
    ⟨fun m => Nat.rec (motive := fun _ => ℕ → ℕ) id
      (fun j ih => ih ∘ σ ih j) m, rfl, fun _ => rfl⟩
  have hΨmono : ∀ m, StrictMono (Ψ m) := by
    intro m
    induction m with
    | zero => rw [hΨ0]; exact strictMono_id
    | succ j ih => rw [hΨs j]; exact ih.comp (hσmono (Ψ j) j)
  have hΨsub : ∀ m j, m ≤ j → ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ k, Ψ j k = Ψ m (ρ k) := by
    intro m j hmj
    induction j, hmj using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, fun k => rfl⟩
    | succ j hmj ih =>
        obtain ⟨ρ, hρ, hρeq⟩ := ih
        refine ⟨ρ ∘ σ (Ψ j) j, hρ.comp (hσmono (Ψ j) j), fun k => ?_⟩
        rw [hΨs j]
        exact hρeq _
  let φ : ℕ → ℕ := fun k => Ψ (k + 1) k
  have hφmono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨ρ, hρ, hρeq⟩ := hΨsub (k + 1) (k + 2) (by omega)
    change Ψ (k + 1) k < Ψ (k + 2) (k + 1)
    rw [hρeq (k + 1)]
    exact hΨmono (k + 1) (lt_of_lt_of_le (Nat.lt_succ_self k) hρ.le_apply)
  have hpatch : ∀ m : ℕ,
      TendstoUniformlyOn (fun k => F (φ k)) (G (Ψ m) m) atTop (upperPatch m) := by
    intro m
    have hbase : TendstoUniformlyOn (fun k => F (Ψ (m + 1) k))
        (G (Ψ m) m) atTop (upperPatch m) := by
      have h := hG (Ψ m) m
      refine h.congr (Filter.Eventually.of_forall fun k => ?_)
      intro z _
      rw [hΨs m]
      rfl
    rw [Metric.tendstoUniformlyOn_iff] at hbase ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hbase ε hε)
    refine eventually_atTop.2 ⟨max N m, fun k hk z hz => ?_⟩
    obtain ⟨ρ, hρ, hρeq⟩ := hΨsub (m + 1) (k + 1) (by omega)
    have hkφ : φ k = Ψ (m + 1) (ρ k) := hρeq k
    have hρk : N ≤ ρ k := le_trans (le_trans (le_max_left N m) hk) hρ.le_apply
    rw [hkφ]
    exact hN (ρ k) hρk z hz
  have hexists : ∀ z : ℂ, 0 < z.im →
      ∃ L : ℂ, Tendsto (fun k => F (φ k) z) atTop (nhds L) := by
    intro z hz
    have hzu : z ∈ ⋃ m, upperPatch m := by
      rw [iUnion_upperPatch]
      exact hz
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzu
    exact ⟨G (Ψ m) m z, (hpatch m).tendsto_at hm⟩
  let g : ℂ → ℂ := fun z => if hz : 0 < z.im then (hexists z hz).choose else 0
  have hg : ∀ z : ℂ, 0 < z.im →
      Tendsto (fun k => F (φ k) z) atTop (nhds (g z)) := by
    intro z hz
    change Tendsto (fun k => F (φ k) z) atTop
      (nhds (if hz' : 0 < z.im then (hexists z hz').choose else 0))
    rw [dif_pos hz]
    exact (hexists z hz).choose_spec
  have hlocal : TendstoLocallyUniformlyOn (fun k => F (φ k)) g atTop
      {z : ℂ | 0 < z.im} := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro z hz
    change 0 < z.im at hz
    have hzu : z ∈ ⋃ m, upperPatch m := by
      rw [iUnion_upperPatch]
      exact hz
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzu
    have hzint : z ∈ interior (upperPatch (m + 1)) :=
      upperPatch_subset_interior_succ m hm
    refine ⟨interior (upperPatch (m + 1)),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (isOpen_interior.mem_nhds hzint), ?_⟩
    refine ((hpatch (m + 1)).mono interior_subset).congr_right fun w hw => ?_
    have hwmem : w ∈ upperPatch (m + 1) := interior_subset hw
    exact tendsto_nhds_unique ((hpatch (m + 1)).tendsto_at hwmem)
      (hg w (upperPatch_subset (m + 1) hwmem))
  have hdiff : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} :=
    hlocal.differentiableOn (Eventually.of_forall fun k => hF (φ k))
      (isOpen_lt continuous_const Complex.continuous_im)
  have hlimbd : ∀ z : ℂ, 0 < z.im → ‖g z‖ ≤ C := by
    intro z hz
    have hmem : g z ∈ closedBall (0 : ℂ) C :=
      isClosed_closedBall.mem_of_tendsto (hg z hz)
        (Eventually.of_forall fun k => by
          rw [mem_closedBall, dist_zero_right]
          exact hbd (φ k) z hz)
    simpa [mem_closedBall, dist_zero_right] using hmem
  exact ⟨φ, g, hφmono, hlocal, hdiff, hlimbd⟩

end RHTower

end
