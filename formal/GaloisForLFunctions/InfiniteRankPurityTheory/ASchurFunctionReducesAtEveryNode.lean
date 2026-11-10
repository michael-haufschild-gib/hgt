import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfIndexOneIsPureOffTheRealAxis

/-!
# A Schur function reduces at every node

The tool behind the index law at any index. A Schur function on the half-plane `Re s > ½` is a
holomorphic function bounded by `1` there.

* `norm_le_norm_defectFactor`: the Schwarz lemma on the half-plane. A Schur function vanishing at
  `s₀` is bounded by the defect factor `b_{s₀}`.
* `exists_quotient_by_defectFactor`: such a function is `φ · b_{s₀}` with `φ` again a Schur function.
* `exists_schur_reduction`: for a Schur function `θ` and a node `s₀` with `‖θ(s₀)‖ < 1` there is a
  Schur function `φ` with `φ · b_{s₀} = M_{θ(s₀)} ∘ θ`, where `M_v(z) = (z − v)/(1 − v̄ z)`.
* `eqOn_const_of_norm_eq_one`: a Schur function attaining modulus one is constant.
* `mobius_injOn`: `M_v` is injective on the closed disc.

One step of the reduction lowers the degree of a finite Blaschke product by one and keeps every
other agreement of two Schur functions.
-/

open Complex Set Metric Filter Topology

namespace GaloisForLFunctions.InfiniteRankPurityTheory

noncomputable section

/-! ### The disc automorphism `M_v` -/

/-- `M_v(z) = (z − v)/(1 − v̄ z)`. -/
def mobius (v z : ℂ) : ℂ := (z - v) / (1 - (starRingEnd ℂ) v * z)

theorem mobius_denom_ne_zero {v z : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - (starRingEnd ℂ) v * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) v * z = 1 := by linear_combination -h
  have h2 : ‖(starRingEnd ℂ) v * z‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, RCLike.norm_conj] at h2
  have h3 : ‖v‖ * ‖z‖ ≤ ‖v‖ := mul_le_of_le_one_right (norm_nonneg v) hz
  linarith

/-- `|1 − v̄ z|² − |z − v|² = (1 − |v|²)(1 − |z|²)`. -/
theorem normSq_mobius_identity (v z : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) v * z) - Complex.normSq (z - v) =
      (1 - Complex.normSq v) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, sub_re, sub_im, one_re, one_im, mul_re, mul_im, conj_re,
    conj_im]
  ring

theorem norm_mobius_le {v z : ℂ} (hv : ‖v‖ < 1) (hz : ‖z‖ ≤ 1) : ‖mobius v z‖ ≤ 1 := by
  have hD := mobius_denom_ne_zero hv hz
  rw [mobius, norm_div, div_le_one (norm_pos_iff.mpr hD)]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hid := normSq_mobius_identity v z
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq] at hid
  have h1 : 0 ≤ (1 - ‖v‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
    mul_nonneg (by nlinarith [norm_nonneg v]) (by nlinarith [norm_nonneg z])
  linarith

theorem mobius_self (v : ℂ) : mobius v v = 0 := by rw [mobius, sub_self, zero_div]

/-- `M_v` is injective on the closed unit disc. -/
theorem mobius_injOn {v z₁ z₂ : ℂ} (hv : ‖v‖ < 1) (h₁ : ‖z₁‖ ≤ 1) (h₂ : ‖z₂‖ ≤ 1)
    (h : mobius v z₁ = mobius v z₂) : z₁ = z₂ := by
  have d₁ := mobius_denom_ne_zero hv h₁
  have d₂ := mobius_denom_ne_zero hv h₂
  rw [mobius, mobius, div_eq_div_iff d₁ d₂] at h
  have hvv : (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hne : (1 : ℂ) - ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (1 - ‖v‖ ^ 2 : ℝ) ≠ 0 := by nlinarith [norm_nonneg v]
    exact_mod_cast this
  have key : (z₁ - z₂) * (1 - ((‖v‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    rw [← hvv]
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)

/-! ### Maximum modulus and the Schwarz lemma on the half-plane -/

theorem isPreconnected_rightHalf : IsPreconnected rightHalf :=
  (convex_halfSpace_re_gt (1 / 2)).isPreconnected

/-- A Schur function attaining modulus one is constant. -/
theorem eqOn_const_of_norm_eq_one {θ : ℂ → ℂ} (hθ : DifferentiableOn ℂ θ rightHalf)
    (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1) {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalf) (h1 : ‖θ s₀‖ = 1) :
    EqOn θ (fun _ => θ s₀) rightHalf := by
  have hmax : IsMaxOn (norm ∘ θ) rightHalf s₀ := fun z hz => by
    show ‖θ z‖ ≤ ‖θ s₀‖
    rw [h1]
    exact hb z hz
  exact Complex.eqOn_of_isPreconnected_of_isMaxOn_norm isPreconnected_rightHalf isOpen_rightHalf
    hθ hs₀ hmax

theorem defectInv_zero (w : ℂ) : defectInv w 0 = w := by
  rw [defectInv]
  simp

/-- **The Schwarz lemma on the half-plane.** A Schur function vanishing at `s₀` is bounded by the
defect factor of `s₀`. -/
theorem norm_le_norm_defectFactor {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f rightHalf)
    (hb : ∀ s ∈ rightHalf, ‖f s‖ ≤ 1) {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalf) (h0 : f s₀ = 0) {s : ℂ}
    (hs : s ∈ rightHalf) : ‖f s‖ ≤ ‖defectFactor s₀ s‖ := by
  have hgd : DifferentiableOn ℂ (fun ζ => f (defectInv s₀ ζ)) (ball 0 1) :=
    hf.comp (differentiableOn_defectInv s₀) fun ζ hζ => defectInv_mem_rightHalf hs₀ hζ
  have hmaps : MapsTo (fun ζ => f (defectInv s₀ ζ)) (ball 0 1) (closedBall 0 1) := fun ζ hζ =>
    mem_closedBall_zero_iff.mpr (hb _ (defectInv_mem_rightHalf hs₀ hζ))
  have hg0 : f (defectInv s₀ 0) = 0 := by rw [defectInv_zero, h0]
  have hm := defectFactor_mem_ball hs₀ hs
  have h : ‖f (defectInv s₀ (defectFactor s₀ s))‖ ≤ ‖defectFactor s₀ s‖ :=
    Complex.norm_le_norm_of_mapsTo_ball hgd hmaps hg0 (mem_ball_zero_iff.mp hm)
  rwa [defectInv_defectFactor hs₀ hs] at h

theorem defectFactor_ne_zero {s₀ s : ℂ} (hs₀ : s₀ ∈ rightHalf) (hs : s ∈ rightHalf)
    (hne : s ≠ s₀) : defectFactor s₀ s ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hne) (defect_denom_ne_zero hs₀ hs)

/-- **A Schur function vanishing at a node is divisible by its defect factor**, and the quotient
is a Schur function. -/
theorem exists_quotient_by_defectFactor {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f rightHalf)
    (hb : ∀ s ∈ rightHalf, ‖f s‖ ≤ 1) {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalf) (h0 : f s₀ = 0) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ rightHalf ∧ (∀ s ∈ rightHalf, ‖φ s‖ ≤ 1) ∧
      ∀ s ∈ rightHalf, φ s * defectFactor s₀ s = f s := by
  have hφd : DifferentiableOn ℂ
      (fun s => dslope f s₀ s * (s - (1 - (starRingEnd ℂ) s₀))) rightHalf :=
    ((differentiableOn_dslope (isOpen_rightHalf.mem_nhds hs₀)).mpr hf).mul
      (differentiableOn_id.sub (differentiableOn_const _))
  have hprod : ∀ s ∈ rightHalf,
      dslope f s₀ s * (s - (1 - (starRingEnd ℂ) s₀)) * defectFactor s₀ s = f s := by
    intro s hs
    have hD := defect_denom_ne_zero hs₀ hs
    have hsm := sub_smul_dslope f s₀ s
    rw [smul_eq_mul, h0, sub_zero] at hsm
    rw [defectFactor, mul_assoc, mul_div_cancel₀ _ hD, mul_comm, hsm]
  -- off the node the bound is the Schwarz lemma
  have hoff : ∀ s ∈ rightHalf, s ≠ s₀ →
      ‖dslope f s₀ s * (s - (1 - (starRingEnd ℂ) s₀))‖ ≤ 1 := by
    intro s hs hne
    have hb0 := defectFactor_ne_zero hs₀ hs hne
    have hsw := norm_le_norm_defectFactor hf hb hs₀ h0 hs
    rw [← hprod s hs, norm_mul] at hsw
    exact le_of_mul_le_mul_right (by rwa [one_mul]) (norm_pos_iff.mpr hb0)
  refine ⟨_, hφd, fun s hs => ?_, hprod⟩
  by_cases hne : s = s₀
  · -- at the node by continuity
    subst hne
    have hd : ContinuousAt (fun z => dslope f s z * (z - (1 - (starRingEnd ℂ) s))) s :=
      (hφd.differentiableAt (isOpen_rightHalf.mem_nhds hs)).continuousAt
    have hcont : ContinuousAt (fun z => ‖dslope f s z * (z - (1 - (starRingEnd ℂ) s))‖) s :=
      hd.norm
    have hev : ∀ᶠ z in 𝓝[≠] s, ‖dslope f s z * (z - (1 - (starRingEnd ℂ) s))‖ ≤ 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_rightHalf.mem_nhds hs)] with z hz hzr
      exact hoff z hzr hz
    exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  · exact hoff s hs hne

/-- `M_v ∘ θ` is holomorphic on the half-plane for a Schur function `θ` and `‖v‖ < 1`. -/
theorem differentiableOn_mobius_comp {θ : ℂ → ℂ} (hθ : DifferentiableOn ℂ θ rightHalf)
    (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1) {v : ℂ} (hv : ‖v‖ < 1) :
    DifferentiableOn ℂ (fun s => mobius v (θ s)) rightHalf := by
  intro s hs
  have hD := mobius_denom_ne_zero hv (hb s hs)
  have h1 : DifferentiableWithinAt ℂ (fun s => θ s - v) rightHalf s := (hθ s hs).sub_const _
  have h2 : DifferentiableWithinAt ℂ (fun s => 1 - (starRingEnd ℂ) v * θ s) rightHalf s :=
    ((hθ s hs).const_mul _).const_sub 1
  exact h1.div h2 hD

/-- **The Schur reduction at a node.** For a Schur function `θ` and a node `s₀` with
`‖θ(s₀)‖ < 1` there is a Schur function `φ` with `φ · b_{s₀} = M_{θ(s₀)} ∘ θ`. -/
theorem exists_schur_reduction {θ : ℂ → ℂ} (hθ : DifferentiableOn ℂ θ rightHalf)
    (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1) {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalf) (hv : ‖θ s₀‖ < 1) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ rightHalf ∧ (∀ s ∈ rightHalf, ‖φ s‖ ≤ 1) ∧
      ∀ s ∈ rightHalf, φ s * defectFactor s₀ s = mobius (θ s₀) (θ s) :=
  exists_quotient_by_defectFactor (differentiableOn_mobius_comp hθ hb hv)
    (fun s hs => norm_mobius_le hv (hb s hs)) hs₀ (mobius_self _)

end

end GaloisForLFunctions.InfiniteRankPurityTheory
