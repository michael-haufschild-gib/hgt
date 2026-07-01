import GaloisForLFunctions.Bottcher.FarFieldUnivalence
import GaloisForLFunctions.Bottcher.BottcherAsymptotic
import GaloisForLFunctions.Bottcher.FarFieldInverseFE

open Complex Metric Set Filter Topology Bornology Function

namespace Bottcher

/-- The exterior `{z : ℂ | R < ‖z‖}` (`R > 0`) is path-connected: it is `exp '' {Re > log R}`, the
continuous image of a (convex) half-plane. -/
theorem isPathConnected_exterior {R : ℝ} (hR : 0 < R) :
    IsPathConnected {z : ℂ | R < ‖z‖} := by
  have hset : {z : ℂ | R < ‖z‖} = Complex.exp '' {w : ℂ | Real.log R < w.re} := by
    ext z
    simp only [mem_setOf_eq, Set.mem_image]
    constructor
    · intro hz
      have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
      exact ⟨Complex.log z, by rw [Complex.log_re]; exact Real.log_lt_log hR hz,
        Complex.exp_log hz0⟩
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.norm_exp]
      calc R = Real.exp (Real.log R) := (Real.exp_log hR).symm
        _ < Real.exp w.re := Real.exp_lt_exp.mpr hw
  rw [hset]
  exact ((convex_halfSpace_re_gt (Real.log R)).isPathConnected
    ⟨Real.log R + 1, by simp⟩).image Complex.continuous_exp

/-- The far-field image of the Böttcher coordinate is open: each image point `φ_c z₀` has the whole
image as a neighborhood, because `ψ` (the far-field inverse) is a continuous right inverse there and
maps a neighborhood back into the far field. -/
theorem isOpen_far_image {c : ℂ} {R : ℝ} (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    IsOpen (bottcherCoord c '' {z | R < ‖z‖}) := by
  obtain ⟨ψ, hψleft, hψan, hψright⟩ := exists_analytic_inverse_far hR1 hR2
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z₀, hz₀, rfl⟩
  have hψcont : ContinuousAt ψ (bottcherCoord c z₀) := (hψan z₀ hz₀).continuousAt
  have hψval : ψ (bottcherCoord c z₀) = z₀ := hψleft z₀ hz₀
  have hAnhds : {z | R < ‖z‖} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz₀
  have hInA : ∀ᶠ w in 𝓝 (bottcherCoord c z₀), ψ w ∈ {z | R < ‖z‖} :=
    hψcont.preimage_mem_nhds (by rw [hψval]; exact hAnhds)
  filter_upwards [hψright z₀ hz₀, hInA] with w hwright hwInA
  exact ⟨ψ w, hwInA, hwright⟩

/-- **Far-field Böttcher surjectivity.** For `R` in the far-field regime, the image
`φ_c '' {‖z‖ > R}` covers a neighborhood of `∞`: there is `R'` such that every `w` with `‖w‖ > R'`
is `φ_c z` for some `z` with `‖z‖ > R`. The image is open (`isOpen_far_image`) and, using
`‖z‖-1 < ‖φ_c z‖ < ‖z‖+1` (from `tendsto_bottcherCoord_sub_id`), closed in `{‖w‖ > R'}` — an
approximating preimage of a boundary `w` is confined to a compact annulus on which `φ_c` is a closed
map. Open + closed + connected target (`isPathConnected_exterior`) gives the whole exterior. -/
theorem exists_bottcher_far_preimage {c : ℂ} {R : ℝ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    ∃ R' : ℝ, ∀ w : ℂ, R' < ‖w‖ → ∃ z : ℂ, R < ‖z‖ ∧ bottcherCoord c z = w := by
  have hmaxlt : max 2 ‖c‖ < R := by
    have : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)
    linarith
  have hRpos : (0:ℝ) < R := lt_trans (lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)) hmaxlt
  set S : Set ℂ := bottcherCoord c '' {z | R < ‖z‖} with hSdef
  have hSopen : IsOpen S := isOpen_far_image hR1 hR2
  have hsub : ∀ z : ℂ, R ≤ ‖z‖ → z ∈ escapeOpen c := by
    intro z hz; rw [escapeOpen, mem_setOf_eq]; exact lt_of_lt_of_le hmaxlt hz
  have hφcont : ContinuousOn (bottcherCoord c) {z | R ≤ ‖z‖} :=
    (analyticOnNhd_bottcherCoord_full c).continuousOn.mono (fun z hz => hsub z hz)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z : ℂ, M < ‖z‖ → ‖bottcherCoord c z - z‖ < 1 := by
    have h := (tendsto_bottcherCoord_sub_id c).eventually (Metric.ball_mem_nhds (0:ℂ) one_pos)
    rw [← comap_norm_atTop, eventually_comap] at h
    obtain ⟨M, hM⟩ := eventually_atTop.mp h
    exact ⟨M, fun z hz => by have h2 := hM ‖z‖ hz.le z rfl; rwa [dist_zero_right] at h2⟩
  set M₀ : ℝ := max M R + 1 with hM₀def
  have hM₀R : R < M₀ := by rw [hM₀def]; have := le_max_right M R; linarith
  have hM₀M : M < M₀ := by rw [hM₀def]; have := le_max_left M R; linarith
  have hM₀pos : (0:ℝ) < M₀ := lt_trans hRpos hM₀R
  have hclcompact : IsCompact {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ ≤ M₀} := by
    apply (isCompact_closedBall (0:ℂ) M₀).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz; rw [mem_closedBall_zero_iff]; exact hz.2
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ ≤ M₀}, ‖bottcherCoord c z‖ ≤ C :=
    hclcompact.exists_bound_of_continuousOn (hφcont.mono (fun z hz => hz.1))
  set R' : ℝ := max M₀ (C + 2) with hR'def
  have hR'M₀ : M₀ ≤ R' := le_max_left _ _
  have hR'C : C + 2 ≤ R' := le_max_right _ _
  have hR'pos : (0:ℝ) < R' := lt_of_lt_of_le hM₀pos hR'M₀
  set T : Set ℂ := {w | R' < ‖w‖} with hTdef
  have hTconn : IsPreconnected T := (isPathConnected_exterior hR'pos).isConnected.isPreconnected
  have hclosed : ∀ w ∈ T, w ∈ closure S → w ∈ S := by
    intro w hwT hwcl
    have hwn : R' < ‖w‖ := hwT
    have hAnncompact : IsCompact {z : ℂ | M₀ ≤ ‖z‖ ∧ ‖z‖ ≤ ‖w‖ + 2} := by
      apply (isCompact_closedBall (0:ℂ) (‖w‖ + 2)).of_isClosed_subset
      · exact (isClosed_le continuous_const continuous_norm).inter
          (isClosed_le continuous_norm continuous_const)
      · intro z hz; rw [mem_closedBall_zero_iff]; exact hz.2
    have hAnnimg_closed : IsClosed (bottcherCoord c '' {z : ℂ | M₀ ≤ ‖z‖ ∧ ‖z‖ ≤ ‖w‖ + 2}) :=
      (hAnncompact.image_of_continuousOn
        (hφcont.mono (fun z hz => le_trans hM₀R.le hz.1))).isClosed
    have hwAnn : w ∈ bottcherCoord c '' {z : ℂ | M₀ ≤ ‖z‖ ∧ ‖z‖ ≤ ‖w‖ + 2} := by
      rw [← hAnnimg_closed.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      set ε' : ℝ := min ε 1 with hε'def
      have hε'pos : 0 < ε' := lt_min hε (by norm_num)
      have hε'1 : ε' ≤ 1 := min_le_right _ _
      rw [Metric.mem_closure_iff] at hwcl
      obtain ⟨v, hvS, hvw⟩ := hwcl ε' hε'pos
      obtain ⟨z, hzA, rfl⟩ := hvS
      have hzR : R < ‖z‖ := hzA
      have hdvw' : ‖bottcherCoord c z - w‖ < ε' := by rwa [dist_comm, dist_eq_norm] at hvw
      have hab : |‖bottcherCoord c z‖ - ‖w‖| < ε' :=
        lt_of_le_of_lt (abs_norm_sub_norm_le _ _) hdvw'
      rw [abs_lt] at hab
      have hzM₀ : M₀ < ‖z‖ := by
        by_contra hcon
        rw [not_lt] at hcon
        have hCz := hC z ⟨hzR.le, hcon⟩
        nlinarith [hab.1, hwn, hε'1, hCz, hR'C]
      have hzhi : ‖z‖ < ‖w‖ + 2 := by
        have hasy : ‖bottcherCoord c z - z‖ < 1 := hM z (lt_trans hM₀M hzM₀)
        have habz : |‖bottcherCoord c z‖ - ‖z‖| < 1 :=
          lt_of_le_of_lt (abs_norm_sub_norm_le _ _) hasy
        rw [abs_lt] at habz
        nlinarith [habz.1, hab.2, hε'1]
      refine ⟨bottcherCoord c z, ⟨z, ⟨hzM₀.le, hzhi.le⟩, rfl⟩, ?_⟩
      rw [dist_comm, dist_eq_norm]; exact lt_of_lt_of_le hdvw' (min_le_left _ _)
    obtain ⟨z', hz'Ann, hz'w⟩ := hwAnn
    exact ⟨z', lt_of_lt_of_le hM₀R hz'Ann.1, hz'w⟩
  have hUne : (T ∩ S).Nonempty := by
    set z₀ : ℂ := ((R' + M₀ + 10 : ℝ) : ℂ) with hz₀def
    have hz₀n : ‖z₀‖ = R' + M₀ + 10 := by
      rw [hz₀def, Complex.norm_real]; exact abs_of_nonneg (by positivity)
    have hz₀A : R < ‖z₀‖ := by rw [hz₀n]; nlinarith [hR'pos, hM₀pos, hRpos]
    have hz₀M : M < ‖z₀‖ := by rw [hz₀n]; nlinarith [hR'M₀, hM₀M, hM₀pos]
    have hasy : ‖bottcherCoord c z₀ - z₀‖ < 1 := hM z₀ hz₀M
    have habig : |‖bottcherCoord c z₀‖ - ‖z₀‖| < 1 :=
      lt_of_le_of_lt (abs_norm_sub_norm_le _ _) hasy
    rw [abs_lt, hz₀n] at habig
    have hbig : R' < ‖bottcherCoord c z₀‖ := by nlinarith [habig.1, hM₀pos, hRpos]
    exact ⟨bottcherCoord c z₀, hbig, ⟨z₀, hz₀A, rfl⟩⟩
  have hVopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
  have hUV : T ⊆ S ∪ (closure S)ᶜ := by
    intro w hw
    by_cases hcl : w ∈ closure S
    · exact Or.inl (hclosed w hw hcl)
    · exact Or.inr hcl
  have hUVdisj : ¬ (T ∩ (S ∩ (closure S)ᶜ)).Nonempty := by
    rintro ⟨w, -, hwU, hwV⟩; exact hwV (subset_closure hwU)
  have hTV_empty : ¬ (T ∩ (closure S)ᶜ).Nonempty := by
    intro hne
    exact hUVdisj (hTconn S (closure S)ᶜ hSopen hVopen hUV hUne hne)
  refine ⟨R', fun w hw => ?_⟩
  have hwS : w ∈ S := by
    by_contra hcon
    have hwcl : w ∉ closure S := fun h => hcon (hclosed w hw h)
    exact hTV_empty ⟨w, hw, hwcl⟩
  obtain ⟨z, hzA, hzw⟩ := hwS
  exact ⟨z, hzA, hzw⟩

/-- **Inverse Böttcher on a genuine neighborhood of `∞`.** Combining far-field surjectivity
(`exists_bottcher_far_preimage`) with the local analytic inverse (`exists_analytic_inverse_far`) and the
banked functional-equation/oddness lemmas: there is a threshold `R' > 0` and a map `ψ` that on the
whole exterior `{‖w‖ > R'}` is analytic, is a right inverse of `φ_c`, and satisfies the inverse
Böttcher functional equation `ψ(w²)=ψ(w)²+c` and oddness `ψ(-w)=-ψ(w)`. This is the genuine
inverse coordinate on which the even disk model `h(t)=t·ψ(1/t)` is built. -/
theorem exists_far_inverse {c : ℂ} {R : ℝ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    ∃ (R' : ℝ) (ψ : ℂ → ℂ), 0 < R' ∧
      (∀ w, R' < ‖w‖ → AnalyticAt ℂ ψ w) ∧
      (∀ w, R' < ‖w‖ → bottcherCoord c (ψ w) = w) ∧
      (∀ w, R' < ‖w‖ → ψ (w ^ 2) = (ψ w) ^ 2 + c) ∧
      (∀ w, R' < ‖w‖ → ψ (-w) = -ψ w) := by
  have hRpos : (0:ℝ) < R := by
    have : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)
    linarith
  obtain ⟨ψ, hψleft, hψan, hψright⟩ := exists_analytic_inverse_far hR1 hR2
  obtain ⟨R', hRpre⟩ := exists_bottcher_far_preimage hR1 hR2
  refine ⟨max R' 1, ψ, lt_of_lt_of_le one_pos (le_max_right _ _), ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left _ _) hw)
    exact hzw ▸ hψan z hz
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left _ _) hw)
    rw [← hzw, hψleft z hz]
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left _ _) hw)
    rw [← hzw]
    exact psi_functional_eq_of_inverts hR1 hR2 hψleft z hz
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hRpre w (lt_of_le_of_lt (le_max_left _ _) hw)
    rw [← hzw]
    exact psi_odd_of_inverts hRpos.le hψleft z hz

/-- **The inverse `ψ` is asymptotic to the identity.** For `ψ` a far-field left inverse of `φ_c`
(from `exists_analytic_inverse_far`), `ψ(w) - w → 0` as `w → ∞`. Since `ψ w = z` with `φ_c z = w`,
`‖ψ w - w‖ = ‖φ_c z - z‖`, and the preimage is confined by `‖z‖ > ‖w‖-1` (compact-annulus bound), so
`z → ∞` and `‖φ_c z - z‖ → 0`. -/
theorem tendsto_psi_sub_id {c : ℂ} {R : ℝ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2)
    {ψ : ℂ → ℂ} (hψleft : ∀ z, R < ‖z‖ → ψ (bottcherCoord c z) = z) :
    Tendsto (fun w => ψ w - w) (cobounded ℂ) (𝓝 0) := by
  have hmaxlt : max 2 ‖c‖ < R := by
    have : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)
    linarith
  have hRpos : (0:ℝ) < R := lt_trans (lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)) hmaxlt
  have hsub : ∀ z : ℂ, R ≤ ‖z‖ → z ∈ escapeOpen c := by
    intro z hz; rw [escapeOpen, mem_setOf_eq]; exact lt_of_lt_of_le hmaxlt hz
  have hφcont : ContinuousOn (bottcherCoord c) {z | R ≤ ‖z‖} :=
    (analyticOnNhd_bottcherCoord_full c).continuousOn.mono (fun z hz => hsub z hz)
  obtain ⟨R', hRpre⟩ := exists_bottcher_far_preimage hR1 hR2
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  -- asymptotic threshold for ε and for 1
  obtain ⟨Mε, hMε⟩ : ∃ Mε : ℝ, ∀ z : ℂ, Mε < ‖z‖ → ‖bottcherCoord c z - z‖ < ε := by
    have h := (tendsto_bottcherCoord_sub_id c).eventually (Metric.ball_mem_nhds (0:ℂ) hε)
    rw [← comap_norm_atTop, eventually_comap] at h
    obtain ⟨Mε, hMε⟩ := eventually_atTop.mp h
    exact ⟨Mε, fun z hz => by have h2 := hMε ‖z‖ hz.le z rfl; rwa [dist_zero_right] at h2⟩
  obtain ⟨M1, hM1⟩ : ∃ M1 : ℝ, ∀ z : ℂ, M1 < ‖z‖ → ‖bottcherCoord c z - z‖ < 1 := by
    have h := (tendsto_bottcherCoord_sub_id c).eventually (Metric.ball_mem_nhds (0:ℂ) one_pos)
    rw [← comap_norm_atTop, eventually_comap] at h
    obtain ⟨M1, hM1⟩ := eventually_atTop.mp h
    exact ⟨M1, fun z hz => by have h2 := hM1 ‖z‖ hz.le z rfl; rwa [dist_zero_right] at h2⟩
  set M' : ℝ := max (max M1 Mε) R + 1 with hM'def
  have hM'M1 : M1 < M' := by rw [hM'def]; have := le_max_left M1 Mε; have := le_max_left (max M1 Mε) R; linarith
  have hM'Mε : Mε < M' := by rw [hM'def]; have := le_max_right M1 Mε; have := le_max_left (max M1 Mε) R; linarith
  have hM'R : R < M' := by rw [hM'def]; have := le_max_right (max M1 Mε) R; linarith
  -- C bound on compact ring
  have hclcompact : IsCompact {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ ≤ M'} := by
    apply (isCompact_closedBall (0:ℂ) M').of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz; rw [mem_closedBall_zero_iff]; exact hz.2
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ ≤ M'}, ‖bottcherCoord c z‖ ≤ C :=
    hclcompact.exists_bound_of_continuousOn (hφcont.mono (fun z hz => hz.1))
  -- eventually ‖w‖ > max (max R' (C+1)) (Mε+1)
  rw [← comap_norm_atTop, eventually_comap, eventually_atTop]
  refine ⟨max (max (R' + 1) (C + 1)) (Mε + 1), fun r hr w hw => ?_⟩
  subst hw
  have hb1 : max (R' + 1) (C + 1) ≤ ‖w‖ := le_trans (le_max_left _ _) hr
  have hb2 : Mε + 1 ≤ ‖w‖ := le_trans (le_max_right _ _) hr
  have hwR' : R' < ‖w‖ := by
    have := le_trans (le_max_left (R' + 1) (C + 1)) hb1; linarith
  have hwC : C < ‖w‖ := by
    have := le_trans (le_max_right (R' + 1) (C + 1)) hb1; linarith
  have hwMε : Mε < ‖w‖ := by linarith
  obtain ⟨z, hzR, hzw⟩ := hRpre w hwR'
  have hψz : ψ w = z := by rw [← hzw, hψleft z hzR]
  -- ‖z‖ > M' (else compact bound contradicts ‖w‖ > C+1)
  have hzM' : M' < ‖z‖ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hCz := hC z ⟨hzR.le, hcon⟩
    rw [hzw] at hCz
    linarith
  -- ‖z‖ > ‖w‖ - 1 via asymptotic at z
  have hasy1 : ‖bottcherCoord c z - z‖ < 1 := hM1 z (lt_trans hM'M1 hzM')
  have hzlow : ‖w‖ - 1 < ‖z‖ := by
    have hb := abs_norm_sub_norm_le (bottcherCoord c z) z
    have h2 : |‖bottcherCoord c z‖ - ‖z‖| < 1 := lt_of_le_of_lt hb hasy1
    rw [abs_lt] at h2
    have hwz : ‖w‖ = ‖bottcherCoord c z‖ := by rw [hzw]
    linarith [h2.2]
  -- so ‖z‖ > Mε, and ‖ψ w - w‖ = ‖φ_c z - z‖ < ε
  have hzMε : Mε < ‖z‖ := by linarith [hzlow, hwMε]
  have hasyε : ‖bottcherCoord c z - z‖ < ε := hMε z hzMε
  rw [hψz]
  calc ‖z - w‖ = ‖bottcherCoord c z - z‖ := by rw [← hzw]; rw [norm_sub_rev]
    _ < ε := hasyε

/-- **The even disk model `h(t)=t·ψ(1/t)` as a genuine holomorphic germ at `0`.** For `c` with the
far-field bounds, there is a disk `ball 0 ρ` (`ρ = (max R' 1)⁻¹ > 0`) on which the disk model — built
from the inverse Böttcher coordinate `ψ` and extended over `0` by the removable-singularity value
`h(0)=1` — is holomorphic, even, and satisfies the model functional equation `h(t²)=h(t)²+c·t²`.
This packages `exists_far_inverse` (ψ on `{‖w‖>R'}`), `tendsto_psi_sub_id` (`ψ(w)-w→0`, giving
`h→1` at `0` via `model_tendsto_one`), `model_even_and_fe` (even + FE), and Riemann's removable
singularity. It is the germ that seeds the outward FE-square-root continuation to the full basin. -/
theorem exists_disk_model {c : ℂ} {R : ℝ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    ∃ (ρ : ℝ) (h : ℂ → ℂ), 0 < ρ ∧
      DifferentiableOn ℂ h (ball 0 ρ) ∧
      (∀ t ∈ ball (0:ℂ) ρ, h (-t) = h t) ∧
      (∀ t ∈ ball (0:ℂ) ρ, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2) ∧
      h 0 = 1 := by
  obtain ⟨ψ, hψleft, hψan, hψright⟩ := exists_analytic_inverse_far hR1 hR2
  obtain ⟨R', hRpre⟩ := exists_bottcher_far_preimage hR1 hR2
  have hRpos : (0:ℝ) < R := by
    have : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left 2 ‖c‖)
    linarith
  set R'' : ℝ := max R' 1 with hR''def
  have hR''pos : (0:ℝ) < R'' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hpreR'' : ∀ w, R'' < ‖w‖ → ∃ z, R < ‖z‖ ∧ bottcherCoord c z = w :=
    fun w hw => hRpre w (lt_of_le_of_lt (le_max_left R' 1) hw)
  have hψan'' : ∀ w, R'' < ‖w‖ → AnalyticAt ℂ ψ w := by
    intro w hw; obtain ⟨z, hz, hzw⟩ := hpreR'' w hw; exact hzw ▸ hψan z hz
  have hψfe'' : ∀ w, R'' < ‖w‖ → ψ (w ^ 2) = (ψ w) ^ 2 + c := by
    intro w hw; obtain ⟨z, hz, hzw⟩ := hpreR'' w hw
    rw [← hzw]; exact psi_functional_eq_of_inverts hR1 hR2 hψleft z hz
  have hψodd'' : ∀ w, R'' < ‖w‖ → ψ (-w) = -ψ w := by
    intro w hw; obtain ⟨z, hz, hzw⟩ := hpreR'' w hw
    rw [← hzw]; exact psi_odd_of_inverts hRpos.le hψleft z hz
  have htend : Tendsto (fun w => ψ w - w) (cobounded ℂ) (𝓝 0) :=
    tendsto_psi_sub_id hR1 hR2 hψleft
  have hlim1 : Tendsto (fun t : ℂ => t * ψ (1 / t)) (𝓝[≠] 0) (𝓝 1) := model_tendsto_one htend
  set ρ : ℝ := R''⁻¹ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact inv_pos.mpr hR''pos
  set h₀ : ℂ → ℂ := fun t => t * ψ (1 / t) with hh₀def
  set h : ℂ → ℂ := Function.update h₀ 0 1 with hhdef
  -- differentiability on the punctured disk
  have hinvbig : ∀ t : ℂ, t ≠ 0 → ‖t‖ < ρ → R'' < ‖(1:ℂ) / t‖ := by
    intro t ht0 htR
    have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    rw [one_div, norm_inv]
    exact (lt_inv_comm₀ hR''pos htn).mpr htR
  have hdon : DifferentiableOn ℂ h₀ (ball 0 ρ \ {0}) := by
    intro t ht
    have ht0 : t ≠ 0 := fun hc => ht.2 (by simp [hc])
    have htR : ‖t‖ < ρ := by rw [← mem_ball_zero_iff]; exact ht.1
    have hbig := hinvbig t ht0 htR
    have hψd : DifferentiableAt ℂ ψ (1 / t) := (hψan'' (1 / t) hbig).differentiableAt
    have hinvd : DifferentiableAt ℂ (fun t : ℂ => 1 / t) t :=
      (differentiableAt_const (1:ℂ)).div differentiableAt_id ht0
    exact ((differentiableAt_id).mul (hψd.comp t hinvd)).differentiableWithinAt
  have hballnhds : ball (0:ℂ) ρ ∈ 𝓝 (0:ℂ) := isOpen_ball.mem_nhds (mem_ball_self hρpos)
  have hcong : Set.EqOn h h₀ (ball (0:ℂ) ρ \ {0}) := by
    intro t ht
    have ht0 : t ≠ 0 := fun hc => ht.2 (by simp [hc])
    exact Function.update_of_ne ht0 _ _
  have hcont0 : ContinuousAt h 0 := continuousAt_update_same.mpr hlim1
  have hdisk : DifferentiableOn ℂ h (ball 0 ρ) :=
    (differentiableOn_compl_singleton_and_continuousAt_iff hballnhds).mp
      ⟨hdon.congr hcong, hcont0⟩
  have hh0 : h 0 = 1 := Function.update_self 0 1 h₀
  have heven : ∀ t ∈ ball (0:ℂ) ρ, h (-t) = h t := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · have htR : ‖t‖ < ρ := by rw [← mem_ball_zero_iff]; exact ht
      have hmodel := (model_even_and_fe hR''pos hψodd'' hψfe'' t ht0 htR).1
      have hneg0 : -t ≠ 0 := neg_ne_zero.mpr ht0
      have e1 : h (-t) = (-t) * ψ (1 / -t) := Function.update_of_ne hneg0 _ _
      have e2 : h t = t * ψ (1 / t) := Function.update_of_ne ht0 _ _
      rw [e1, e2]; exact hmodel
  have hfe : ∀ t ∈ ball (0:ℂ) ρ, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2 := by
    intro t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · simp [hh0]
    · have htR : ‖t‖ < ρ := by rw [← mem_ball_zero_iff]; exact ht
      have hmodel := (model_even_and_fe hR''pos hψodd'' hψfe'' t ht0 htR).2
      have hsq0 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
      have e1 : h (t ^ 2) = (t ^ 2) * ψ (1 / t ^ 2) := Function.update_of_ne hsq0 _ _
      have e2 : h t = t * ψ (1 / t) := Function.update_of_ne ht0 _ _
      rw [e1, e2]; exact hmodel
  exact ⟨ρ, h, hρpos, hdisk, heven, hfe, hh0⟩

end Bottcher
