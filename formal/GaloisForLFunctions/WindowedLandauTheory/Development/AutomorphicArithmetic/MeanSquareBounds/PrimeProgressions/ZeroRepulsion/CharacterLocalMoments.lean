import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.CauchyMoments
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.NonprincipalLocalMoments
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroChangeLevel

/-! Local moments at the principal character after removing its simple pole. -/

open Finset Complex Classical Filter Topology

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

lemma dhl_ne_one {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  rw [h, Complex.one_re] at hs
  exact lt_irrefl _ hs

lemma dhl_triv_ld (M : ℕ) [NeZero M] (z : ℂ) (hz : 1 < z.re) :
    -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)
      = negLD (1 : DirichletCharacter ℂ M) z - 1 / (z - 1) := by
  have hz1 : z ≠ 1 := dhl_ne_one hz
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hL0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re
    (1 : DirichletCharacter ℂ M) (Or.inr hz1) hz.le
  rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one M hz1, hf z hz1]
  unfold negLD
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring

lemma dhl_negLD_contDiffAt (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    ContDiffAt ℂ k (negLD (1 : DirichletCharacter ℂ M)) s := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M))
      {w : ℂ | 1 < w.re} := by
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction _ w
      (Or.inl (dhl_ne_one hw))).differentiableWithinAt
  have hD : DifferentiableOn ℂ (negLD (1 : DirichletCharacter ℂ M)) {w : ℂ | 1 < w.re} := by
    unfold negLD
    refine ((hLd.deriv hU).div hLd ?_).neg
    intro w hw
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr (dhl_ne_one hw)) (le_of_lt hw)
  exact (hD.contDiffOn hU).contDiffAt (hU.mem_nhds hs)

lemma dhl_pole_contDiffAt (s : ℂ) (hs : s ≠ 1) (k : ℕ) :
    ContDiffAt ℂ k (fun z : ℂ => 1 / (z - 1)) s := by
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hs)

lemma dhl_triv_iter (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z =>
      -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)) s
      = (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s
        - 1 / (s - 1) ^ (k + 1) := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z /
      DirichletCharacter.LFunctionTrivChar₁ M z)) =ᶠ[nhds s]
      (negLD (1 : DirichletCharacter ℂ M) - fun z : ℂ => 1 / (z - 1)) := by
    filter_upwards [hU.mem_nhds hs] with z hz
    rw [Pi.sub_apply]
    exact dhl_triv_ld M z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_sub (dhl_negLD_contDiffAt M s hs k)
    (dhl_pole_contDiffAt s (dhl_ne_one hs) k), mul_sub, dhl_pole k s]

lemma dhl_triv {A : ℝ} (hA : 0 < A) (hCau : DHCauchyFor A) (K : ℝ) (hK : 10400 ≤ K) (M : ℕ) [NeZero M]
    (t : ℝ) : DHLocalAt (6 * A * (Real.log K + 2)) M (1 : DirichletCharacter ℂ M) t := by
  have hX := dhl_X M t
  have hK1 : 1 ≤ K := by linarith
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hf1 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero M
  have hz0re : ((26 / 25 : ℂ) + ↑t * I).re = 26 / 25 := dhl_z0re t
  have hz0ne : (26 / 25 : ℂ) + ↑t * I ≠ 1 := dhl_ne_one (by rw [hz0re]; norm_num)
  have hLz0 := dhl_inv M (1 : DirichletCharacter ℂ M) t
  have hnz0 : 1 / 650 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    rw [hf _ hz0ne, norm_mul]
    have ha : 1 / 25 ≤ ‖(26 / 25 : ℂ) + ↑t * I - 1‖ := by
      have := Complex.re_le_norm ((26 / 25 : ℂ) + ↑t * I - 1)
      rw [Complex.sub_re, hz0re, Complex.one_re] at this
      linarith
    nlinarith [norm_nonneg (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) ((26 / 25 : ℂ) + ↑t * I))]
  have hfz0 : DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnz0
    norm_num at hnz0
  have hgrowth : ∀ z : ℂ, ‖z - ((26 / 25 : ℂ) + ↑t * I)‖ ≤ 12 / 25 →
      ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    intro z hz
    obtain ⟨hre, hn⟩ := dhl_geom t z hz
    have h1 := dhl_triv_growth M z hre
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
    have h2 : ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤ 16 * M * (|t| + 2) ^ 2 := by
      have hsq : (1 + ‖z‖) ^ 2 ≤ (2 * (|t| + 2)) ^ 2 := by
        have : 0 ≤ 1 + ‖z‖ := by positivity
        gcongr
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * M)
      nlinarith
    have h3 : 16 * M * (|t| + 2) ^ 2 ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) := by
      have hKM : 10400 ≤ K * M := by nlinarith
      have hT : 0 ≤ (M : ℝ) * (|t| + 2) ^ 2 := by positivity
      have e : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) = (K * M) * (M * (|t| + 2) ^ 2) / 650 := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hKM hT
      linarith
    have h4 : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
      apply mul_le_mul_of_nonneg_left hnz0
      positivity
    linarith
  obtain ⟨Z, m, hZ, hm, horder, hcount, hbd⟩ := dhl_core hA hCau (DirichletCharacter.LFunctionTrivChar₁ M) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunctionTrivChar₁ M) hfz0 hgrowth
  have hzero : ∀ ρ : ℂ, DirichletCharacter.LFunctionTrivChar₁ M ρ = 0 ↔
      IsLZero (1 : DirichletCharacter ℂ M) ρ := by
    intro ρ
    constructor
    · intro h
      have hρ : ρ ≠ 1 := fun e => hf1 (e ▸ h)
      refine ⟨Or.inr hρ, ?_⟩
      rw [hf ρ hρ] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)
    · rintro ⟨h1, h2⟩
      have hρ : ρ ≠ 1 := h1.resolve_left (fun h => h rfl)
      rw [hf ρ hρ, h2, mul_zero]
  unfold DHLocalAt
  refine ⟨Z, m, ?_, hm, ?_, ?_, hcount, ?_⟩
  · intro ρ
    rw [hZ ρ, hzero ρ]
  · intro ρ hρ
    have hz := (hzero ρ).mp ((hZ ρ).mp hρ).2
    have hρ₁ : ρ ≠ 1 := hz.1.resolve_left (fun h => h rfl)
    have hev : DirichletCharacter.LFunctionTrivChar₁ M =ᶠ[nhds ρ]
        (fun z : ℂ => z - 1) * (1 : DirichletCharacter ℂ M).LFunction := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hρ₁] with z hz
      exact hf z hz
    have ha : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ := analyticAt_id.sub analyticAt_const
    rw [horder ρ hρ]
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul ha (lFunction_analyticAt _ hz.1),
      ha.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ₁), zero_add]
  · intro ρ hρ
    obtain ⟨_, hfρ⟩ := (hZ ρ).mp hρ
    obtain ⟨h1, h2⟩ := (hzero ρ).mp hfρ
    by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ h1 hge h2
  · intro k s hs hsd
    have hs1 : s ≠ 1 := dhl_ne_one hs
    have hfs : DirichletCharacter.LFunctionTrivChar₁ M s ≠ 0 := by
      rw [hf s hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hs1) hs.le)
    have hb := hbd k s hsd hfs
    rw [if_pos rfl, ← dhl_triv_iter M s hs k]
    exact hb

theorem deuring_heilbronn_local : DHLocal := by
  obtain ⟨A, hA, hCau⟩ := deuring_heilbronn_cauchy
  have hlog : 0 ≤ Real.log (10400 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨6 * A * (Real.log 10400 + 2), by positivity, ?_⟩
  intro M _ ψ t
  by_cases hψ : ψ = 1
  · subst ψ
    exact dhl_triv hA hCau 10400 le_rfl M t
  · apply dhl_nontriv hA hCau 2 10400 ?_ (by norm_num) (by norm_num) M ψ hψ t
    intro N _ χ hχ s hs
    have hs' : 0 < s.re := by linarith
    have h := Zeta23.ThmE.norm_LFunction_le_of_re_pos hχ hs'
    refine h.trans ?_
    rw [div_le_iff₀ hs']
    have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * N * (1 + ‖s‖) by positivity)
    linarith only [hp, show 0 ≤ (N : ℝ) by positivity]

end QH.PrimeProgressions
