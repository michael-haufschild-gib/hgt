import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import GaloisForLFunctions.HTGeometry.RightHalfPlanePrimitive
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential

/-!
# The reciprocal zeta function of a Weil-positive system

Let `lam` (with `lam(1) = 0`) be Weil-positive in Herglotz form for a datum `A`, with Herglotz
function `Φ` on `Re s > 1/2`.  The reciprocal `1/F = exp(−Σ lam(n) n^{−s}/log n)` of its zeta
function continues holomorphically to the whole half-plane `Re s > 1/2`
(`exists_reciprocalZeta_continuation`).

**Proof.**  `E = A − Φ` is holomorphic on `Re s > 1/2`; let `P` be a primitive there
(`isExactOn_rightHalfPlane`).  Put `G(s) = c (s − 1) e^{P(s)}`.  Then
`G'/G = 1/(s−1) + E = Σ lam(n) n^{−s}` on `Re s > 1`, so `G · exp L` has zero derivative there
and is constant; the constant `c` is fixed at `s = 2`.
-/

open Complex Metric Set

noncomputable section

namespace RHTower

/-- **Continuation of the reciprocal zeta function of a producer.** -/
theorem exists_reciprocalZeta_continuation {lam : ℕ → ℝ} {A : ℂ → ℂ}
    (hW : HerglotzWeilPositive lam A) (h1 : lam 1 = 0)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re}) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → G s = cexp (-LSeries (logZetaCoeff lam) s) := by
  obtain ⟨Φ, hΦd, -, hΦid⟩ := hW.herglotz
  have hsum := hW.summable
  set H : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hH
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hEd : DifferentiableOn ℂ (fun s => A s - Φ s) H := hA.sub hΦd
  obtain ⟨P, hP2, hPd⟩ := (GaloisForLFunctions.HTGeometry.isExactOn_rightHalfPlane hEd).with_val_at
    2 0
  set c : ℂ := cexp (-LSeries (logZetaCoeff lam) 2) with hc
  set G : ℂ → ℂ := fun s => c * ((s - 1) * cexp (P s)) with hG
  have hGd : ∀ s ∈ H, HasDerivAt G (c * (1 * cexp (P s) + (s - 1) * (cexp (P s) * (A s - Φ s))))
      s := fun s hs =>
    (((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul c
  refine ⟨G, fun s hs => (hGd s hs).differentiableAt.differentiableWithinAt, ?_⟩
  set U : Set ℂ := {s : ℂ | 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUH : U ⊆ H := fun s (hs : 1 < s.re) => show 1 / 2 < s.re by linarith
  set L : ℂ → ℂ := LSeries (logZetaCoeff lam) with hL
  have hLd : ∀ s ∈ U, HasDerivAt L (-LSeries (fun n => (lam n : ℂ)) s) s := fun s hs =>
    hasDerivAt_LSeries_logZetaCoeff hsum h1 hs
  -- `Q = G · exp L` is constant on `Re s > 1`
  set Q : ℂ → ℂ := fun s => G s * cexp (L s) with hQ
  have hQd : ∀ s ∈ U, HasDerivAt Q 0 s := by
    intro s hs
    show HasDerivAt (fun y => G y * cexp (L y)) 0 s
    refine ((hGd s (hUH hs)).mul (hLd s hs).cexp).congr_deriv ?_
    have hs1 : s - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      have hs' : 1 < s.re := hs
      linarith
    have hD := hΦid s hs
    have hE : A s - Φ s = LSeries (fun n => (lam n : ℂ)) s - 1 / (s - 1) := by
      rw [hD]; ring
    rw [hE]
    simp only [hG]
    field_simp
    ring
  have h2U : (2 : ℂ) ∈ U := by show (1 : ℝ) < (2 : ℂ).re; norm_num
  have hQ2 : Q 2 = 1 := by
    simp only [hQ, hG, hP2, Complex.exp_zero, mul_one, hc]
    norm_num
    rw [← Complex.exp_add]
    simp
  have hconst := hUo.eqOn_of_deriv_eq (convex_halfSpace_re_gt 1).isPreconnected
    (fun s hs => (hQd s hs).differentiableAt.differentiableWithinAt)
    (differentiableOn_const (1 : ℂ))
    (fun s hs => by rw [(hQd s hs).deriv, deriv_const]) h2U (by rw [hQ2])
  intro s hs
  have hQs : G s * cexp (L s) = 1 := hconst hs
  have hexp : cexp (L s) ≠ 0 := Complex.exp_ne_zero _
  calc G s = G s * cexp (L s) * cexp (-L s) := by
        rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    _ = cexp (-L s) := by rw [hQs, one_mul]

/-- On a disc meeting `Re s > 1` at its centre, a holomorphic continuation of `exp(−L)` is
`exp(−g)` for every holomorphic continuation `g` of `L`. -/
theorem eqOn_exp_neg_of_agree {G g L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (hc : 1 < c.re)
    (hG : DifferentiableOn ℂ G (ball c R)) (hg : DifferentiableOn ℂ g (ball c R))
    (hGL : ∀ s ∈ ball c R, 1 < s.re → G s = cexp (-L s))
    (hgL : ∀ s ∈ ball c R, 1 < s.re → g s = L s) :
    EqOn G (fun s => cexp (-g s)) (ball c R) := by
  have hGa := hG.analyticOnNhd isOpen_ball
  have hga : AnalyticOnNhd ℂ (fun s => cexp (-g s)) (ball c R) :=
    (hg.neg.cexp).analyticOnNhd isOpen_ball
  refine hGa.eqOn_of_preconnected_of_eventuallyEq hga (convex_ball c R).isPreconnected
    (mem_ball_self hR) ?_
  have hopen : ball c R ∩ {s : ℂ | 1 < s.re} ∈ nhds c :=
    (isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)).mem_nhds
      ⟨mem_ball_self hR, hc⟩
  filter_upwards [hopen] with s hs
  rw [hGL s hs.1 hs.2, hgL s hs.1 hs.2]

/-- **Subpolynomial growth of the reciprocal zeta function of a producer.** -/
theorem exists_reciprocalZeta_subpolynomial {lam : ℕ → ℝ} {A : ℂ → ℂ}
    (hW : HerglotzWeilPositive lam A) (h1 : lam 1 = 0) {K : ℝ} (hK : 0 ≤ K)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) {ε : ℝ} (hε : 0 < ε) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGL : ∀ s : ℂ, 1 < s.re → G s = cexp (-LSeries (logZetaCoeff lam) s)) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 5 / 2 →
      ‖G ((σ : ℂ) + t * I)‖ ≤ (|t| + 3) ^ ε := by
  obtain ⟨T₀, hT₀⟩ := exists_producerZeta_subpolynomial hW h1 hK hA hAK hδ hδ1 hε
  refine ⟨T₀, fun t ht σ hσ hσ2 => ?_⟩
  obtain ⟨g, hgd, hgL, hbd⟩ := hT₀ t ht
  have hR : (0 : ℝ) < 5 / 2 - δ / 4 := by linarith
  have hcre : 1 < ((3 : ℂ) + t * I).re := by simp
  have hsub : ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4) ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro w hw
    rw [mem_ball_iff_norm] at hw
    have h := Complex.abs_re_le_norm (w - ((3 : ℂ) + t * I))
    have hre3 : ((3 : ℂ) + t * I).re = 3 := by simp
    rw [Complex.sub_re, hre3] at h
    have := neg_abs_le (w.re - 3)
    show 1 / 2 < w.re
    linarith
  have heq := eqOn_exp_neg_of_agree hR hcre (hGd.mono hsub) hgd
    (fun s _ hs => hGL s hs) hgL
  have hmem : (σ : ℂ) + t * I ∈ ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4) := by
    rw [mem_ball_iff_norm, norm_vertical_sub_center σ t (by linarith)]
    linarith
  rw [heq hmem]
  obtain ⟨hlow, -⟩ := hbd σ hσ hσ2
  have hpos : 0 < (|t| + 3) ^ (-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hexp : ‖cexp (-g ((σ : ℂ) + t * I))‖ = ‖cexp (g ((σ : ℂ) + t * I))‖⁻¹ := by
    rw [Complex.exp_neg, norm_inv]
  rw [hexp, Real.rpow_neg (by positivity)] at *
  rw [inv_le_comm₀ (lt_of_lt_of_le hpos hlow) (by positivity)]
  exact hlow

/-- **Strip bound for the reciprocal zeta function of a producer.**  On `1/2 + δ ≤ Re s ≤ 2`,
`‖1/F_lam(s)‖ ≤ K (2 + |Im s|)^ε`. -/
theorem exists_reciprocalZeta_strip_bound {lam : ℕ → ℝ} {A : ℂ → ℂ}
    (hW : HerglotzWeilPositive lam A) (h1 : lam 1 = 0) {K : ℝ} (hK : 0 ≤ K)
    (hA : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAK : ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 2 → ‖A s‖ ≤ K * Real.log (|s.im| + 3))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) {ε : ℝ} (hε : 0 < ε) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGL : ∀ s : ℂ, 1 < s.re → G s = cexp (-LSeries (logZetaCoeff lam) s)) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ s ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2 + δ) 2,
      ‖G s‖ ≤ Kb * (2 + |s.im|) ^ ε := by
  obtain ⟨T₀, hT₀⟩ := exists_reciprocalZeta_subpolynomial hW h1 hK hA hAK hδ hδ1 hε hGd hGL
  set Kset : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) ''
    (Icc (1 / 2 + δ) 2 ×ˢ Icc (-|T₀|) |T₀|) with hKset
  have hKc : IsCompact Kset := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKH : Kset ⊆ {s : ℂ | 1 / 2 < s.re} := by
    rintro _ ⟨p, hp, rfl⟩
    show 1 / 2 < ((p.1 : ℂ) + p.2 * I).re
    simp
    linarith [hp.1.1]
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hGd.continuousOn.mono hKH)
  refine ⟨max C 1 * 2 ^ ε, by positivity, fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have h2t : 1 ≤ (2 + |s.im|) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hε.le
  have h2e : 1 ≤ (2 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) hε.le
  have hM1 : 1 ≤ max C 1 := le_max_right _ _
  rcases le_or_gt T₀ |s.im| with ht | ht
  · have h := hT₀ s.im ht s.re hs1 (by linarith)
    rw [Complex.re_add_im] at h
    have hmono : (|s.im| + 3) ^ ε ≤ (2 * (2 + |s.im|)) ^ ε :=
      Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hε.le
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hmono
    have hpos : 0 ≤ 2 ^ ε * (2 + |s.im|) ^ ε := by positivity
    calc ‖G s‖ ≤ 2 ^ ε * (2 + |s.im|) ^ ε := h.trans hmono
      _ ≤ max C 1 * 2 ^ ε * (2 + |s.im|) ^ ε := by nlinarith
  · have hmem : s ∈ Kset := ⟨(s.re, s.im), ⟨⟨hs1, hs2⟩, ⟨by
        have := neg_abs_le s.im
        have := le_abs_self T₀
        linarith [abs_lt.mp (ht.trans_le (le_abs_self T₀))], by
        have := le_abs_self s.im
        linarith [le_abs_self T₀]⟩⟩, Complex.re_add_im s⟩
    have hb := hC s hmem
    have : C ≤ max C 1 := le_max_left _ _
    have hp : 1 ≤ 2 ^ ε * (2 + |s.im|) ^ ε := one_le_mul_of_one_le_of_one_le h2e h2t
    calc ‖G s‖ ≤ max C 1 := hb.trans this
      _ = max C 1 * 1 := (mul_one _).symm
      _ ≤ max C 1 * (2 ^ ε * (2 + |s.im|) ^ ε) := by
          exact mul_le_mul_of_nonneg_left hp (by linarith)
      _ = max C 1 * 2 ^ ε * (2 + |s.im|) ^ ε := by ring

/-- The Möbius function of a producer: the Dirichlet coefficients of `1/F = exp(−L)`. -/
def producerMobius (lam : ℕ → ℝ) : ℕ → ℂ :=
  GaloisForLFunctions.HTGeometry.dirichletExp fun n => -logZetaCoeff lam n

/-- On `Re s > 1`, `Σ μ_lam(n) n^{−s}` converges absolutely and equals `exp(−L(s)) = 1/F(s)`. -/
theorem LSeries_producerMobius {lam : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (producerMobius lam) s ∧
      LSeries (producerMobius lam) s = cexp (-LSeries (logZetaCoeff lam) s) := by
  have habs : LSeries.abscissaOfAbsConv (logZetaCoeff lam) < s.re :=
    (abscissaOfAbsConv_logZetaCoeff_le hsum).trans_lt (by exact_mod_cast hs)
  have hL : LSeriesSummable (logZetaCoeff lam) s := LSeriesSummable_of_abscissaOfAbsConv_lt_re habs
  have hneg : LSeriesSummable (fun n => -logZetaCoeff lam n) s := hL.neg
  have h := GaloisForLFunctions.HTGeometry.LSeries_dirichletExp (f := fun n => -logZetaCoeff lam n)
    (by simp [logZetaCoeff]) (by simp [logZetaCoeff]) hneg
  refine ⟨h.1, ?_⟩
  rw [producerMobius, h.2]
  congr 1
  rw [show (fun n => -logZetaCoeff lam n) = -logZetaCoeff lam from rfl, LSeries_neg]

end RHTower

end
