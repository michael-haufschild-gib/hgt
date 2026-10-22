import GaloisForLFunctions.RHTower.Suzuki.SuzukiModelPointEval
import GaloisForLFunctions.RHTower.Suzuki.SuzukiV0WeilMass

noncomputable section

/-!
# The Weil hermitian form on `V(0)`

Suzuki's Weil hermitian form is `⟨ψ₁,ψ₂⟩_W = Σ_γ m_γ ψ̂₁(γ) (ψ̂₂)^♯(γ)`, the sum running over the
zero set `Γ` of `A = XiC` with multiplicity.  On `V(0) = L²(0,∞) ∩ K L²(0,∞)` the values `ψ̂(γ)` are
the bounded point evaluations of the model space supplied by `SuzukiModelPointEval`, so the form is
defined with no appeal to RH.  (The index type `XiZeroCopy` already carries the multiplicity, and
`Γ` is stable under `γ ↦ -γ` because `A` is even, so summing `ψ̂(γ)` over the spectral points is the
same sum as the source's `ψ̂(-γ)` over `Γ`.)

Two halves of Suzuki's Proposition 5.1 are proved here, both under RH:

* the mass identity `‖ψ‖² = π ⟨ψ,ψ⟩_W` on `V(0)` — the corpus's Fourier transform is unitary, so
  the source's factor `2^{-1}` becomes `π`;
* the existence of peaked test functions, from the orthonormal family `F_γ`, in the sharp form with
  *exact* vanishing at the other zeros.

The module also collects the summability facts the converse needs: only finitely many spectral
points lie in a bounded region, and the three-halves weight stays summable when recentred.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-! ## Summability toolkit -/

/-- The square of a summable nonnegative family is summable: each term is bounded by the total. -/
theorem summable_sq_of_summable_nonneg {ι : Type*} {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hf : Summable f) : Summable (fun i => f i ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) (hf.mul_left (∑' j, f j))
  have hle : f i ≤ ∑' j, f j := hf.le_tsum i (fun j _ => hf0 j)
  nlinarith [hf0 i]

/-- Only finitely many spectral points lie in a bounded region: the three-halves weight is
summable, so it exceeds any positive threshold only finitely often. -/
theorem finite_xiSpectralPoint_norm_le (R : ℝ) :
    {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ R}.Finite := by
  have hpos : ∀ q : XiZeroCopy, 0 < ‖xiSpectralPoint q‖ :=
    fun q => norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  rcases le_or_gt R 0 with hR | hR
  · refine Set.Finite.subset Set.finite_empty ?_
    intro q hq
    have hq' : ‖xiSpectralPoint q‖ ≤ R := hq
    exact absurd (le_trans hq' hR) (not_le.mpr (hpos q))
  · set δ : ℝ := 1 / (R * Real.sqrt R) with hδdef
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
    have hδ : 0 < δ := by positivity
    have htend := xiSpectralPoint_inv_three_halves_summable.tendsto_cofinite_zero
    have hev : ∀ᶠ q in Filter.cofinite,
        1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖) ∈ Metric.ball (0 : ℝ) δ :=
      htend (Metric.ball_mem_nhds 0 hδ)
    have hfin : {q : XiZeroCopy |
        ¬ (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖) ∈
          Metric.ball (0 : ℝ) δ)}.Finite := Filter.eventually_cofinite.mp hev
    refine Set.Finite.subset hfin ?_
    intro q hq
    have hle : ‖xiSpectralPoint q‖ ≤ R := hq
    simp only [Set.mem_setOf_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    have hprod : ‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖ ≤ R * Real.sqrt R := by
      have h1 : Real.sqrt ‖xiSpectralPoint q‖ ≤ Real.sqrt R := Real.sqrt_le_sqrt hle
      have := hpos q
      nlinarith [Real.sqrt_nonneg ‖xiSpectralPoint q‖]
    have hqpos : 0 < ‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖ := by
      have := hpos q
      have : 0 < Real.sqrt ‖xiSpectralPoint q‖ := Real.sqrt_pos.mpr (hpos q)
      positivity
    rw [abs_of_pos (by positivity)]
    rw [hδdef]
    exact one_div_le_one_div_of_le hqpos hprod


theorem summable_xiSpectralPoint_shift_three_halves (c : ℂ) :
    Summable (fun q : XiZeroCopy =>
      1 / (‖c - xiSpectralPoint q‖ * Real.sqrt ‖c - xiSpectralPoint q‖)) := by
  have hS : {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ 2 * ‖c‖ + 2}.Finite :=
    finite_xiSpectralPoint_norm_le _
  rw [← hS.summable_compl_iff]
  refine Summable.of_nonneg_of_le (fun q => div_nonneg zero_le_one (by positivity)) ?_
    ((xiSpectralPoint_inv_three_halves_summable.subtype
      ({q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ 2 * ‖c‖ + 2}ᶜ)).mul_left 4)
  rintro ⟨q, hq⟩
  have hfar : 2 * ‖c‖ + 2 < ‖xiSpectralPoint q‖ := by
    simpa [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] using hq
  set a : ℝ := ‖xiSpectralPoint q‖ with hadef
  set b : ℝ := ‖c - xiSpectralPoint q‖ with hbdef
  have hcnn : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have ha : 0 < a := by linarith
  have hab : a / 2 ≤ b := by
    have h1 : a - ‖c‖ ≤ b := by
      have := norm_sub_norm_le (xiSpectralPoint q) c
      rw [hbdef, ← norm_neg (c - xiSpectralPoint q)]
      simp only [neg_sub]
      linarith
    linarith
  have hb : 0 < b := by linarith
  have hsq : Real.sqrt a / 2 ≤ Real.sqrt b := by
    refine Real.le_sqrt_of_sq_le ?_
    have hs := Real.sq_sqrt ha.le
    nlinarith
  have hprod : a * Real.sqrt a / 4 ≤ b * Real.sqrt b := by
    have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    nlinarith
  have hposa : 0 < a * Real.sqrt a := by
    have : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    positivity
  have hposb : 0 < b * Real.sqrt b := by
    have : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    positivity
  have hkey : 1 / (b * Real.sqrt b) ≤ 4 * (1 / (a * Real.sqrt a)) := by
    rw [show (4 : ℝ) * (1 / (a * Real.sqrt a)) = 1 / (a * Real.sqrt a / 4) by
      field_simp]
    exact one_div_le_one_div_of_le (by positivity) hprod
  simpa using hkey

theorem hasSum_xiZeroCopy_of_support {g : XiDivisorSupport → ℝ} (hg : ∀ ρ, 0 ≤ g ρ) {t : ℝ}
    (h : HasSum (fun ρ => (xiSupportMult ρ : ℝ) * g ρ) t) :
    HasSum (fun q : XiZeroCopy => g q.1) t := by
  have hfib : ∀ ρ : XiDivisorSupport,
      HasSum (fun _ : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) => g ρ)
        ((xiSupportMult ρ : ℝ) * g ρ) := by
    intro ρ
    have hb := hasSum_fintype
      (fun _ : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) => g ρ)
    simpa [xiSupportMult, Finset.sum_const, nsmul_eq_mul] using hb
  have hnn : ∀ q : XiZeroCopy, 0 ≤ g q.1 := fun q => hg q.1
  have hsum : Summable (fun q : XiZeroCopy => g q.1) := by
    rw [summable_sigma_of_nonneg hnn]
    refine ⟨fun ρ => (hfib ρ).summable, ?_⟩
    refine h.summable.congr fun ρ => ?_
    exact ((hfib ρ).tsum_eq).symm
  have h2 : HasSum (fun ρ : XiDivisorSupport => (xiSupportMult ρ : ℝ) * g ρ)
      (∑' q : XiZeroCopy, g q.1) := hsum.hasSum.sigma hfib
  exact (h2.unique h) ▸ hsum.hasSum

/-! ## `Γ` and the Riemann hypothesis -/

/-- `Γ` is the zero set of `A = XiC`, and RH says exactly that it is real. -/
theorem riemannHypothesis_iff_forall_XiC_zero_im_eq_zero :
    RiemannHypothesis ↔ ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h z hz
    have hxi : xi (1 / 2 + z * Complex.I) = 0 := hz
    have hre := h _ hxi
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.div_re] at hre
    simp at hre
    linarith
  · intro h ρ hρ
    have hz : XiC ((ρ - 1 / 2) * (-Complex.I)) = 0 := by
      show xi (1 / 2 + (ρ - 1 / 2) * (-Complex.I) * Complex.I) = 0
      have hval : (1 : ℂ) / 2 + (ρ - 1 / 2) * (-Complex.I) * Complex.I = ρ := by
        have hI : (-Complex.I) * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]; ring
        rw [mul_assoc, hI, mul_one]
        ring
      rw [hval]
      exact hρ
    have him := h _ hz
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im] at him
    simp at him
    linarith

/-! ## The Weil hermitian form -/

def suzukiV0Eval (ψ : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) : ℂ :=
  suzukiModelEval ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ) w

theorem exists_xiSpectralPointSupport_eq {z : ℂ} (hz : XiC z = 0) :
    ∃ ρ : XiDivisorSupport, xiSpectralPointSupport ρ = z := by
  have hxi : xi (1 / 2 + z * Complex.I) = 0 := hz
  refine ⟨⟨1 / 2 + z * Complex.I, mem_xi_divisor_support_of_eq_zero hxi⟩, ?_⟩
  show ((1 / 2 + z * Complex.I : ℂ) - 1 / 2) * (-Complex.I) = z
  have hI : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I]; ring
  rw [add_sub_cancel_left, mul_assoc, hI, mul_one]

theorem suzukiV0Eval_add (ψ φ : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) :
    suzukiV0Eval (ψ + φ) w = suzukiV0Eval ψ w + suzukiV0Eval φ w := by
  simp only [suzukiV0Eval, map_add, suzukiModelEval_add]

theorem suzukiV0Eval_sub (ψ φ : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) :
    suzukiV0Eval (ψ - φ) w = suzukiV0Eval ψ w - suzukiV0Eval φ w := by
  simp only [suzukiV0Eval, map_sub, suzukiModelEval_sub]

theorem suzukiV0Eval_smul (a : ℂ) (ψ : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) :
    suzukiV0Eval (a • ψ) w = a * suzukiV0Eval ψ w := by
  simp only [suzukiV0Eval, map_smul, suzukiModelEval_smul]

/-- **The Weil hermitian form** of Suzuki (1.2), written through the spectral values:
`⟨ψ,φ⟩_W = Σ_γ m_γ ψ̂(γ) (φ̂)^♯(γ)`. -/
def suzukiV0WeilForm (ψ φ : Lp ℂ 2 (volume : Measure ℝ)) : ℂ :=
  ∑' q : XiZeroCopy, suzukiV0Eval ψ (xiSpectralPoint q)
      * (starRingEnd ℂ) (suzukiV0Eval φ ((starRingEnd ℂ) (xiSpectralPoint q)))

theorem suzukiV0Eval_xiSpectralPoint (hRH : RiemannHypothesis)
    (ψ : Lp ℂ 2 (volume : Measure ℝ)) (q : XiZeroCopy) :
    suzukiV0Eval ψ (xiSpectralPoint q)
      = suzukiRestriction hRH ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ) q.1 := by
  rw [suzukiV0Eval, xiSpectralPoint_eq_support, suzukiModelEval_xiSpectralPointSupport]

theorem conj_xiSpectralPoint_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
  rw [xiSpectralPoint_eq_ofReal_of_rh hRH q, Complex.conj_ofReal]

/-- **Suzuki Proposition 5.1 (1), forward.**  Under RH the `L²` mass of `ψ ∈ V(0)` is `π` times its
Weil mass. -/
theorem hasSum_suzukiV0WeilTerm (hRH : RiemannHypothesis)
    {ψ : Lp ℂ 2 (volume : Measure ℝ)} (hψ : ψ ∈ suzukiV0) :
    HasSum (fun q : XiZeroCopy => suzukiV0Eval ψ (xiSpectralPoint q)
        * (starRingEnd ℂ) (suzukiV0Eval ψ ((starRingEnd ℂ) (xiSpectralPoint q))))
      (((‖ψ‖ ^ (2 : ℕ) / Real.pi : ℝ)) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set F : Lp ℂ 2 (volume : Measure ℝ) := (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ with hFdef
  have hF : F ∈ suzukiModelSpace := mem_suzukiModelSpace_fourier_of_suzukiV0 hψ
  have hnorm : ‖F‖ = ‖ψ‖ := (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).norm_map ψ
  have hbase := hasSum_suzukiClarkWeight_normSq_restriction hRH hF
  have hdiv : HasSum (fun ρ : XiDivisorSupport =>
      (xiSupportMult ρ : ℝ) * ‖suzukiRestriction hRH F ρ‖ ^ (2 : ℕ)) (‖ψ‖ ^ (2 : ℕ) / Real.pi) := by
    have h := hbase.div_const Real.pi
    rw [hnorm] at h
    refine h.congr fun ρ => ?_
    simp only [suzukiClarkWeight]
    field_simp
  have hreal := hasSum_xiZeroCopy_of_support
    (g := fun ρ => ‖suzukiRestriction hRH F ρ‖ ^ (2 : ℕ)) (fun ρ => sq_nonneg _) hdiv
  have hC := Complex.hasSum_ofReal.mpr hreal
  refine hC.congr_fun fun q => ?_
  rw [conj_xiSpectralPoint_of_rh hRH q, suzukiV0Eval_xiSpectralPoint hRH ψ q]
  rw [Complex.mul_conj, ← Complex.sq_norm]

/-- **Suzuki Proposition 5.1 (1), forward.**  Under RH the `L²` mass of `ψ ∈ V(0)` is `π` times its
Weil mass. -/
theorem norm_sq_eq_pi_mul_suzukiV0WeilForm (hRH : RiemannHypothesis)
    {ψ : Lp ℂ 2 (volume : Measure ℝ)} (hψ : ψ ∈ suzukiV0) :
    ((‖ψ‖ ^ (2 : ℕ) : ℝ) : ℂ) = (Real.pi : ℂ) * suzukiV0WeilForm ψ ψ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (hasSum_suzukiV0WeilTerm hRH hψ).tsum_eq
  rw [suzukiV0WeilForm, h]
  push_cast
  field_simp

/-- **Suzuki Proposition 5.1 (2), forward.**  Under RH the basis vector `F_γ` supplies a test
function in `V(0)` whose spectral transform is `1` at `γ` and `0` at every other zero of `A`. -/
theorem exists_peaked_suzukiV0 (hRH : RiemannHypothesis) {γ : ℂ} (hγ : XiC γ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ ∈ suzukiV0, suzukiV0Eval ψ γ = 1 ∧
      ∀ w : ℂ, XiC w = 0 → w ≠ γ →
        ‖suzukiV0Eval ψ w‖ ≤ ε / (‖γ - w‖ * Real.sqrt ‖γ - w‖) := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_xiSpectralPointSupport_eq hγ
  have hcw : 0 < suzukiClarkWeight ρ₀ := suzukiClarkWeight_pos ρ₀
  have hsne : ((Real.sqrt (suzukiClarkWeight ρ₀) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hcw))
  set F : Lp ℂ 2 (volume : Measure ℝ) :=
    ((Real.sqrt (suzukiClarkWeight ρ₀) : ℝ) : ℂ) • suzukiFGammaFamily hRH ρ₀ with hFdef
  have hFmem : F ∈ suzukiModelSpace :=
    Submodule.smul_mem _ _ (suzukiFGammaFamily_mem hRH ρ₀)
  obtain ⟨ψ, hψ, hψF⟩ : ∃ ψ ∈ suzukiV0,
      (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ψ = F := by
    rw [← map_fourier_suzukiV0] at hFmem
    obtain ⟨ψ, hψ, h⟩ := hFmem
    exact ⟨ψ, hψ, h⟩
  have hev : ∀ w : ℂ, suzukiV0Eval ψ w = suzukiModelEval F w := by
    intro w; rw [suzukiV0Eval, hψF]
  have hrestr : ∀ ρ : XiDivisorSupport, suzukiModelEval F (xiSpectralPointSupport ρ)
      = if ρ = ρ₀ then 1 else 0 := by
    intro ρ
    rw [suzukiModelEval_xiSpectralPointSupport hRH F ρ, suzukiRestriction, hFdef,
      inner_smul_right]
    by_cases h : ρ = ρ₀
    · subst h
      have hnorm : ‖suzukiFGammaFamily hRH ρ‖ = 1 := norm_suzukiFGammaFamily hRH ρ
      have hself : (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiFGammaFamily hRH ρ) : ℂ) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hnorm]
        norm_num
      rw [if_pos rfl, hself, mul_one, div_self hsne]
    · have hzero : (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiFGammaFamily hRH ρ₀) : ℂ) = 0 :=
        (orthonormal_suzukiFGammaVec hRH).2 h
      rw [if_neg h, hzero, mul_zero, zero_div]
  refine ⟨ψ, hψ, ?_, ?_⟩
  · rw [hev, ← hρ₀, hrestr ρ₀, if_pos rfl]
  · intro w hw hwne
    obtain ⟨ρ, hρ⟩ := exists_xiSpectralPointSupport_eq hw
    have hne : ρ ≠ ρ₀ := by
      intro h
      exact hwne (by rw [← hρ, h, hρ₀])
    rw [hev, ← hρ, hrestr ρ, if_neg hne, norm_zero]
    positivity

end RHTower
