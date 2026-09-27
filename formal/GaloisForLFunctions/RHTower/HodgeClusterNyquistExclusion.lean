import GaloisForLFunctions.RHTower.ClusterInterpolationContour

/-!
# The level-`a` Hodge index excludes clustered off-line zeros up to the Nyquist height

Let `ρ₀ = β₀ + it₀` be a zero of `ζ` with `β₀ > ½`, `t₀ ≥ 101`, and let the level-`a` Hodge
index hold. Divide Riemann's kernel `Φ` (with `Φ̂ = Ξ`) by the divisor of *all* zeros of depth
`> y₀` in the window around `t₀` (`ClusterInterpolationContour`), and consider the test

`f = N_Q P_{s_p}(χ_{a-1/4} K)`,    `K = D_L Φ`,

where `χ` is a smooth plateau, `P_{s_p}` the polar operator with symbol vanishing at `±i/2`,
and `N_Q` the shift operator whose symbol `Q(e^{iκz})` takes the value `±i/(P K̂)` at every node.
Every node contributes `-m_ρ(1 - 2η - η²)` to `Re W(f,f)` (`re_summand_node_le`); every other
zero is killed by `Ξ` up to the truncation tail `η` (`test_off_node`, `re_W_le_nodes_add`).
Hodge positivity therefore forces `η ≳ 1`, while `η` is at most the tail of `Φ` beyond
`a - 3/8`, of size `exp(-πe^{2a-3/4})`, times the size of `Q`, of size
`exp(πt₀/4 + O(N(log N + log(1/δ₀)) + log t₀))` (`hodgeIndex_excludes_clustered_zero`).

In logarithmic form (`hodgeIndex_cluster_nyquist_horizon`):

`πe^{2a-3/4} ≤ π(t₀+1)/2 + O(N(log N + log(1/δ₀)) + log t₀ + N a)`,  `N = O(log t₀)`,

so the level-`a` Hodge index excludes every off-line zero below height
`2e^{2a-3/4} - O(log t₀(log log t₀ + log(1/δ₀)))`, with no separation hypothesis: the internal
geometry of a cluster never enters.
-/

open Complex MeasureTheory Filter Topology Set Polynomial GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel
local notation "shw" => OffLinePairData.sh

/-! ## Smooth truncation of a kernel -/

/-- The truncated kernel `χ_b h`, with the plateau of width `1/8`. -/
def truncK (b : ℝ) (h : ℝ → ℂ) : ℝ → ℂ := fun x => ((plateau b shw x : ℝ) : ℂ) * h x

/-- The discarded tail `(1 - χ_b) h`. -/
def tailK (b : ℝ) (h : ℝ → ℂ) : ℝ → ℂ := fun x => (1 - ((plateau b shw x : ℝ) : ℂ)) * h x

theorem superExpDecay_truncK {h : ℝ → ℂ} (hh : SuperExpDecay h) (b : ℝ) :
    SuperExpDecay (truncK b h) :=
  hh.mul_bounded (OffLinePairData.continuous_plateauC b) (OffLinePairData.norm_plateau_le b)

theorem superExpDecay_tailK {h : ℝ → ℂ} (hh : SuperExpDecay h) (b : ℝ) :
    SuperExpDecay (tailK b h) :=
  hh.mul_bounded (continuous_const.sub (OffLinePairData.continuous_plateauC b))
    (OffLinePairData.norm_one_sub_plateau_le b)

theorem paperFT_truncK {h : ℝ → ℂ} (hh : SuperExpDecay h) (b : ℝ) (z : ℂ) :
    paperFT (truncK b h) z = paperFT h z - paperFT (tailK b h) z := by
  unfold paperFT
  rw [← integral_sub (hh.integrable_mul_cexp z) ((superExpDecay_tailK hh b).integrable_mul_cexp z)]
  congr 1; funext x; unfold truncK tailK; ring

theorem norm_paperFT_tailK_le {h : ℝ → ℂ} (hh : SuperExpDecay h) (b : ℝ) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) : ‖paperFT (tailK b h) z‖ ≤ expTail h (1 / 2) (b - shw) := by
  unfold paperFT expTail
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _)
    (hh.integrable_tail _ _) (Eventually.of_forall fun u => ?_))
  simp only [indicator, mem_setOf_eq]
  split_ifs with hu
  · rw [norm_mul]
    unfold tailK
    rw [norm_mul]
    calc ‖1 - ((plateau b shw u : ℝ) : ℂ)‖ * ‖h u‖ * ‖Complex.exp (I * z * u)‖
        ≤ 1 * ‖h u‖ * Real.exp (1 / 2 * |u|) := by
          gcongr
          · exact OffLinePairData.norm_one_sub_plateau_le b u
          · exact norm_cexp_I_mul_le_exp hz u
      _ = ‖h u‖ * Real.exp (1 / 2 * |u|) := by ring
  · push Not at hu
    have hp : plateau b shw u = 1 := plateau_eq_one OffLinePairData.sh_pos (by linarith)
    unfold tailK
    simp [hp]

theorem truncK_eq_zero {b u : ℝ} (h : ℝ → ℂ) (hu : b ≤ |u|) : truncK b h u = 0 := by
  unfold truncK; rw [plateau_eq_zero OffLinePairData.sh_pos hu]; simp

/-! ## The cluster test -/

/-- The test `N_Q P_s (χ_b h)`. -/
def clusterTest (Q : ℂ[X]) (κ s b : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  expPolyShiftOp Q κ (polarOp s (truncK b h))

theorem paperFT_clusterTest {h : ℝ → ℂ} (hh : SuperExpDecay h) (Q : ℂ[X]) (κ s b : ℝ) (z : ℂ) :
    paperFT (clusterTest Q κ s b h) z = Q.eval (Complex.exp (I * z * κ)) * polarSymbol s z *
      (paperFT h z - paperFT (tailK b h) z) := by
  have ht := superExpDecay_truncK hh b
  have hp := ht.polarOp s
  unfold clusterTest
  rw [paperFT_expPolyShiftOp (hp.integrable_mul_cexp z), paperFT_polarOp (ht.integrable_mul_cexp z),
    paperFT_truncK hh]
  ring

theorem clusterTest_eq_zero {h : ℝ → ℂ} {Q : ℂ[X]} {κ s b a u : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (hab : b + s + Q.natDegree * κ ≤ a) (hu : a ≤ |u|) : clusterTest Q κ s b h u = 0 := by
  unfold clusterTest
  refine expPolyShiftOp_eq_zero (b := b + s) hκ Q (fun v hv => ?_) (by linarith)
  exact polarOp_eq_zero hs (fun w hw => truncK_eq_zero h hw) hv

theorem clusterTest_supp {h : ℝ → ℂ} {Q : ℂ[X]} {κ s b a : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (hab : b + s + Q.natDegree * κ ≤ a) (u : ℝ) (hu : clusterTest Q κ s b h u ≠ 0) : |u| ≤ a := by
  by_contra hc; push Not at hc; exact hu (clusterTest_eq_zero hκ hs hab hc.le)

theorem tsupport_clusterTest {h : ℝ → ℂ} {Q : ℂ[X]} {κ s b a : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (hab : b + s + Q.natDegree * κ ≤ a) : tsupport (clusterTest Q κ s b h) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have := clusterTest_supp hκ hs hab u hu
  exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩

/-- **Calculus of the cluster test.** If `h` is twice differentiable with
`‖h‖₁ ≤ B`, `‖h'‖₁ ≤ (1+Γ)B`, `‖h''‖₁ ≤ (1+Γ)²B`, then the test is `C²` and
`‖f‖₁ + ‖f''‖₁ ≤ 4 Kp · Σ|c_k| · (1 + cosh(s/2)) · (1+Γ)² B`. -/
theorem clusterTest_calculus {h k₁ k₂ : ℝ → ℂ} (hh : SuperExpDecay h)
    (hd1 : ∀ x, HasDerivAt h (k₁ x) x) (hd2 : ∀ x, HasDerivAt k₁ (k₂ x) x) (ck₁ : Continuous k₁)
    (ck₂ : Continuous k₂) (ik₁ : Integrable k₁) (ik₂ : Integrable k₂) {Γ B : ℝ} (hΓ : 0 ≤ Γ)
    (nh : ∫ x, ‖h x‖ ≤ B) (nk₁ : ∫ x, ‖k₁ x‖ ≤ (1 + Γ) * B)
    (nk₂ : ∫ x, ‖k₂ x‖ ≤ (1 + Γ) ^ 2 * B) (Q : ℂ[X]) (κ s b : ℝ) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    ContDiff ℝ 2 (clusterTest Q κ s b h) ∧
    (∫ u, ‖clusterTest Q κ s b h u‖) + (∫ u, ‖deriv (deriv (clusterTest Q κ s b h)) u‖) ≤
      4 * Kp * (coeffMass Q * (1 + Real.cosh (s / 2))) * ((1 + Γ) ^ 2 * B) := by
  have hB : 0 ≤ B := (integral_nonneg fun _ => norm_nonneg _).trans nh
  set pC : ℝ → ℂ := fun x => ((plateau b shw x : ℝ) : ℂ) with hpC
  set p₁C : ℝ → ℂ := fun x => ((plateau₁ b shw x : ℝ) : ℂ) with hp₁C
  set p₂C : ℝ → ℂ := fun x => ((plateau₂ b shw x : ℝ) : ℂ) with hp₂C
  have hdp : ∀ x, HasDerivAt pC (p₁C x) x := fun x =>
    (hasDerivAt_plateau (b := b) OffLinePairData.sh_pos.ne' x).ofReal_comp
  have hdp₁ : ∀ x, HasDerivAt p₁C (p₂C x) x := fun x =>
    (hasDerivAt_plateau₁ (b := b) OffLinePairData.sh_pos.ne' x).ofReal_comp
  have cp : Continuous pC := Complex.continuous_ofReal.comp (continuous_plateau b shw)
  have cp₁ : Continuous p₁C := Complex.continuous_ofReal.comp (continuous_plateau₁ b shw)
  have cp₂ : Continuous p₂C := Complex.continuous_ofReal.comp (continuous_plateau₂ b shw)
  have np : ∀ x, ‖pC x‖ ≤ 1 := fun x => OffLinePairData.norm_plateau_le b x
  have np₁ : ∀ x, ‖p₁C x‖ ≤ Kp := fun x => by
    simp only [hp₁C, Complex.norm_real, Real.norm_eq_abs]; exact (hKp b x).1
  have np₂ : ∀ x, ‖p₂C x‖ ≤ Kp := fun x => by
    simp only [hp₂C, Complex.norm_real, Real.norm_eq_abs]; exact (hKp b x).2
  set t₁ : ℝ → ℂ := fun x => p₁C x * h x + pC x * k₁ x with ht₁
  set t₂ : ℝ → ℂ := fun x => p₂C x * h x + 2 * (p₁C x * k₁ x) + pC x * k₂ x with ht₂
  have hdt : ∀ x, HasDerivAt (truncK b h) (t₁ x) x := fun x => (hdp x).mul (hd1 x)
  have hdt₁ : ∀ x, HasDerivAt t₁ (t₂ x) x := fun x =>
    (((hdp₁ x).mul (hd1 x)).add ((hdp x).mul (hd2 x))).congr_deriv (by simp only [ht₂]; ring)
  have ch : Continuous h := hh.1
  have ct₂ : Continuous t₂ := by simp only [ht₂]; fun_prop
  have hdT : ∀ x, HasDerivAt (clusterTest Q κ s b h) (expPolyShiftOp Q κ (polarOp s t₁) x) x :=
    hasDerivAt_expPolyShiftOp (hasDerivAt_polarOp hdt s) Q κ
  have hdT₁ : ∀ x, HasDerivAt (expPolyShiftOp Q κ (polarOp s t₁))
      (expPolyShiftOp Q κ (polarOp s t₂) x) x :=
    hasDerivAt_expPolyShiftOp (hasDerivAt_polarOp hdt₁ s) Q κ
  have cT₂ : Continuous (expPolyShiftOp Q κ (polarOp s t₂)) :=
    continuous_expPolyShiftOp (continuous_polarOp ct₂ s) _ _
  have hC2 : ContDiff ℝ 2 (clusterTest Q κ s b h) := contDiff_two_of_hasDerivAt hdT hdT₁ cT₂
  have hD2 : deriv (deriv (clusterTest Q κ s b h)) = expPolyShiftOp Q κ (polarOp s t₂) := by
    have h1 : deriv (clusterTest Q κ s b h) = expPolyShiftOp Q κ (polarOp s t₁) :=
      funext fun x => (hdT x).deriv
    rw [h1]; exact funext fun x => (hdT₁ x).deriv
  have it₂ : Integrable t₂ := by
    have i1 : Integrable (fun x => p₂C x * h x) :=
      Integrable.mono' (hh.integrable.norm.const_mul Kp) (cp₂.mul ch).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (np₂ x) (norm_nonneg _))
    have i2' : Integrable (fun x => p₁C x * k₁ x) :=
      Integrable.mono' (ik₁.norm.const_mul Kp) (cp₁.mul ck₁).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (np₁ x) (norm_nonneg _))
    have i3 : Integrable (fun x => pC x * k₂ x) :=
      Integrable.mono' (ik₂.norm.const_mul 1) (cp.mul ck₂).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (np x) (norm_nonneg _))
    exact (i1.add (i2'.const_mul 2)).add i3
  have iA : Integrable (fun x => Kp * ‖h x‖) := hh.integrable.norm.const_mul _
  have iB : Integrable (fun x => 2 * Kp * ‖k₁ x‖) := ik₁.norm.const_mul _
  have iC : Integrable (fun x => ‖k₂ x‖) := ik₂.norm
  have nt₂ : ∫ x, ‖t₂ x‖ ≤ Kp * (∫ x, ‖h x‖) + 2 * Kp * (∫ x, ‖k₁ x‖) + ∫ x, ‖k₂ x‖ := by
    have hsum3 : ∫ x, (Kp * ‖h x‖ + 2 * Kp * ‖k₁ x‖ + ‖k₂ x‖) =
        Kp * (∫ x, ‖h x‖) + 2 * Kp * (∫ x, ‖k₁ x‖) + ∫ x, ‖k₂ x‖ := by
      have iAB : Integrable (fun x => Kp * ‖h x‖ + 2 * Kp * ‖k₁ x‖) := iA.add iB
      rw [integral_add iAB iC, integral_add iA iB, integral_const_mul, integral_const_mul]
    rw [← hsum3]
    have iABC : Integrable (fun x => Kp * ‖h x‖ + 2 * Kp * ‖k₁ x‖ + ‖k₂ x‖) := (iA.add iB).add iC
    refine integral_mono it₂.norm iABC fun x => ?_
    simp only [ht₂]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_left (np₂ x) (norm_nonneg _) |>.trans
        (by rw [mul_comm])
    · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      have := mul_le_mul_of_nonneg_right (np₁ x) (norm_nonneg (k₁ x)); linarith
    · rw [norm_mul]; have := mul_le_mul_of_nonneg_right (np x) (norm_nonneg (k₂ x)); linarith
  have ntrunc : ∫ x, ‖truncK b h x‖ ≤ ∫ x, ‖h x‖ := by
    refine integral_mono (superExpDecay_truncK hh b).integrable.norm hh.integrable.norm fun x => ?_
    unfold truncK; rw [norm_mul]
    have := mul_le_mul_of_nonneg_right (OffLinePairData.norm_plateau_le b x) (norm_nonneg (h x))
    linarith
  set opF := coeffMass Q * (1 + Real.cosh (s / 2)) with hopF
  have hopF0 : 0 ≤ opF := mul_nonneg (coeffMass_nonneg Q) (by have := Real.cosh_pos (s / 2); positivity)
  have htest : ∫ u, ‖clusterTest Q κ s b h u‖ ≤ opF * ∫ x, ‖truncK b h x‖ := by
    unfold clusterTest
    refine (integral_norm_expPolyShiftOp_le ((superExpDecay_truncK hh b).polarOp s).integrable _ _).trans ?_
    rw [hopF, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_polarOp_le (superExpDecay_truncK hh b).integrable s) (coeffMass_nonneg Q)
  have htest2 : ∫ u, ‖deriv (deriv (clusterTest Q κ s b h)) u‖ ≤ opF * ∫ x, ‖t₂ x‖ := by
    rw [hD2]
    have ip : Integrable (polarOp s t₂) := by
      have h1 := it₂.comp_sub_right s
      have h2 := it₂.comp_add_right s
      have h3 := ((h1.add h2).div_const 2).sub (it₂.const_mul ((Real.cosh (s / 2) : ℝ) : ℂ))
      refine h3.congr (Eventually.of_forall fun x => ?_)
      simp [polarOp]
    refine (integral_norm_expPolyShiftOp_le ip _ _).trans ?_
    rw [hopF, mul_assoc]
    exact mul_le_mul_of_nonneg_left (integral_norm_polarOp_le it₂ s) (coeffMass_nonneg Q)
  refine ⟨hC2, ?_⟩
  have hΓ1 : 1 ≤ 1 + Γ := by linarith
  have e1 : ∫ x, ‖t₂ x‖ ≤ (3 * Kp + 1) * ((1 + Γ) ^ 2 * B) := by
    have hΓ2 : 1 ≤ (1 + Γ) ^ 2 := by nlinarith
    have hΓΓ : 1 + Γ ≤ (1 + Γ) ^ 2 := by nlinarith
    have s1 : Kp * (∫ x, ‖h x‖) ≤ Kp * ((1 + Γ) ^ 2 * B) :=
      mul_le_mul_of_nonneg_left (nh.trans (le_mul_of_one_le_left hB hΓ2)) (by linarith)
    have s2 : 2 * Kp * (∫ x, ‖k₁ x‖) ≤ 2 * Kp * ((1 + Γ) ^ 2 * B) :=
      mul_le_mul_of_nonneg_left (nk₁.trans (mul_le_mul_of_nonneg_right hΓΓ hB)) (by linarith)
    nlinarith
  have e2 : ∫ x, ‖truncK b h x‖ ≤ (1 + Γ) ^ 2 * B := by
    have hΓ2 : 1 ≤ (1 + Γ) ^ 2 := by nlinarith
    nlinarith
  calc (∫ u, ‖clusterTest Q κ s b h u‖) + (∫ u, ‖deriv (deriv (clusterTest Q κ s b h)) u‖)
      ≤ opF * ((1 + Γ) ^ 2 * B) + opF * ((3 * Kp + 1) * ((1 + Γ) ^ 2 * B)) := by
        gcongr
        · exact htest.trans (mul_le_mul_of_nonneg_left e2 hopF0)
        · exact htest2.trans (mul_le_mul_of_nonneg_left e1 hopF0)
    _ ≤ 4 * Kp * opF * ((1 + Γ) ^ 2 * B) := by
        have : 0 ≤ opF * ((1 + Γ) ^ 2 * B) := by positivity
        nlinarith

/-! ## Finitely many nodes against the other zeros -/

/-- **Finitely many nodes against the rest.** For a `C²` test supported in `[-a,a]` whose
transform is at most `η` at every zero outside a finite set `F`,
`Re W(f,f) ≤ Σ_{ρ ∈ F} Re(m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)) + (5/4) S_Z η e^{a/2} 4(‖f‖₁+‖f''‖₁)`. -/
theorem re_W_le_nodes_add {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (F : Finset zetaZeroConfig.carrier) {η : ℝ} (hη : 0 ≤ η)
    (hother : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F → ‖paperFT f (gammaOf (ρ : ℂ))‖ ≤ η) :
    (zetaZeroConfig.W f f).re ≤
      ∑ ρ ∈ F, (zetaZeroConfig.Wsummand f f ρ).re +
      (5 / 4) * zeroSumZ * (η * (Real.exp (a / 2) *
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)))) := by
  set N : ℝ := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hN
  have hN1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun u => norm_nonneg _
  have hN2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun u => norm_nonneg _
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  set E : ℝ := Real.exp (a / 2) * N with hE
  have hE0 : 0 ≤ E := by positivity
  have hdec : ∀ ρ : ℂ, ∀ z : ℂ, |z.im| ≤ 1 / 2 → |z.re| = |ρ.im| →
      ‖paperFT f z‖ ≤ E * (1 / (1 + |ρ.im|) ^ 2) := by
    intro ρ z hz hre
    have h := norm_paperFT_le_decay hf hsupp z
    rw [hre] at h
    refine h.trans ?_
    have hea : Real.exp (|z.im| * a) ≤ Real.exp (a / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
    calc Real.exp (|z.im| * a) * N / (1 + |ρ.im|) ^ 2
        ≤ Real.exp (a / 2) * N / (1 + |ρ.im|) ^ 2 := by gcongr
      _ = E * (1 / (1 + |ρ.im|) ^ 2) := by rw [hE]; ring
  have hpt : ∀ ρ : zetaZeroConfig.carrier, |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 ∧
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 ∧
      |(gammaOf (ρ : ℂ)).re| = |(ρ : ℂ).im| ∧
      |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re| = |(ρ : ℂ).im| := by
    intro ρ
    have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := ρ.2
      exact ⟨h.2.1, h.2.2⟩
    have hIm := (WeilEF.abs_gammaOf_im_lt hstrip).le
    refine ⟨hIm, by rw [Complex.conj_im, abs_neg]; exact hIm, by rw [WeilEF.gammaOf_re],
      by rw [Complex.conj_re, WeilEF.gammaOf_re]⟩
  have hq : ∀ ρ : zetaZeroConfig.carrier, 1 / (1 + |(ρ : ℂ).im|) ^ 2 ≤
      (5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hstrip := zetaZeroConfig.strip ρ ρ.2
    exact one_div_one_add_abs_im_sq_le hstrip
  set ws : zetaZeroConfig.carrier → ℂ := fun ρ => zetaZeroConfig.Wsummand f f ρ with hws
  have hwsn : ∀ ρ : zetaZeroConfig.carrier, ‖ws ρ‖ = (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ := by
    intro ρ
    simp only [hws, ZeroConfig.Wsummand]
    rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hsum := summable_zeroSumZ
  have hall : ∀ ρ : zetaZeroConfig.carrier, ‖ws ρ‖ ≤ (5 / 4) * (E * E) *
      ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4⟩ := hpt ρ
    have b1 := hdec (ρ : ℂ) _ h1 h3
    have b2 := hdec (ρ : ℂ) _ h2 h4
    have hle1 : 1 / (1 + |(ρ : ℂ).im|) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [abs_nonneg (ρ : ℂ).im]
    have b1' : ‖paperFT f (gammaOf ρ)‖ ≤ E := b1.trans (by nlinarith)
    rw [hwsn]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ *
          ‖paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (zetaZeroConfig.mult ρ : ℝ) * E * (E * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf ρ))))) := by
          gcongr
          exact b2.trans (mul_le_mul_of_nonneg_left (hq ρ) hE0)
      _ = (5 / 4) * (E * E) * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          ring
  have hsumws : Summable ws :=
    Summable.of_norm_bounded (hsum.mul_left _) hall
  classical
  set T : Set zetaZeroConfig.carrier := ((↑F : Set zetaZeroConfig.carrier)ᶜ) with hT
  have hsplit : ∑ ρ ∈ F, ws ρ + ∑' x : T, ws x = ∑' ρ, ws ρ :=
    hsumws.sum_add_tsum_compl (s := F)
  have hW : zetaZeroConfig.W f f = ∑ ρ ∈ F, ws ρ + ∑' x : T, ws x := by
    unfold ZeroConfig.W; rw [hsplit]
  have hrest : (∑' x : T, ws x).re ≤ (5 / 4) * zeroSumZ * (η * E) := by
    have hb : ∀ x : T, ‖ws x‖ ≤ (5 / 4) * (η * E) *
        ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
          (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := by
      intro x
      have hx : (x : zetaZeroConfig.carrier) ∉ F := x.2
      obtain ⟨h1, h2, h3, h4⟩ := hpt (x : zetaZeroConfig.carrier)
      have b1 := hother _ hx
      have b2 := hdec _ _ h2 h4
      rw [hwsn]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult (x : zetaZeroConfig.carrier) := Nat.cast_nonneg _
      calc (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) *
            ‖paperFT f (gammaOf (x : zetaZeroConfig.carrier))‖ *
            ‖paperFT f ((starRingEnd ℂ) (gammaOf (x : zetaZeroConfig.carrier)))‖
          ≤ (zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) * η *
              (E * ((5 / 4) * (1 / (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))))) := by
            gcongr
            exact b2.trans (mul_le_mul_of_nonneg_left (hq _) hE0)
        _ = (5 / 4) * (η * E) * ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := by ring
    have hsT : Summable (fun x : T => (5 / 4) * (η * E) *
        ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
          (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier))))) :=
      (hsum.subtype T).mul_left _
    have hwsT : Summable (fun x : T => ‖ws x‖) := Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) hb hsT
    calc (∑' x : T, ws x).re ≤ ‖∑' x : T, ws x‖ := Complex.re_le_norm _
      _ ≤ ∑' x : T, ‖ws x‖ := norm_tsum_le_tsum_norm hwsT
      _ ≤ ∑' x : T, (5 / 4) * (η * E) *
            ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) :=
          Summable.tsum_le_tsum hb hwsT hsT
      _ = (5 / 4) * (η * E) * ∑' x : T,
            ((zetaZeroConfig.mult (x : zetaZeroConfig.carrier) : ℝ) /
              (1 + Complex.normSq (gammaOf (x : zetaZeroConfig.carrier)))) := tsum_mul_left
      _ ≤ (5 / 4) * (η * E) * zeroSumZ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Summable.tsum_subtype_le (fun ρ : zetaZeroConfig.carrier =>
            (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) T
            (fun _ => div_nonneg (Nat.cast_nonneg _)
              (add_pos_of_pos_of_nonneg one_pos (Complex.normSq_nonneg _)).le) hsum
      _ = (5 / 4) * zeroSumZ * (η * E) := by ring
  rw [hW, Complex.add_re, Complex.re_sum]
  linarith

/-! ## The cluster test at a cluster setup -/

namespace ClusterSetup

variable (C : ClusterSetup)

theorem node_copies_subset :
    C.nodes.sigma (fun _ => Finset.univ) ⊆ windowCopySet C.t₀ := by
  intro q hq
  rw [Finset.mem_sigma] at hq
  obtain ⟨h1, -⟩ := (mem_nodeSet (by linarith [C.hX2])).mp hq.1
  exact mem_windowCopySet.mpr (by linarith [C.hX2])

theorem orderSum_le : orderSum C.L ≤ windowCount C.t₀ := by
  rw [orderSum_nodeList]
  have h := Finset.card_le_card C.node_copies_subset
  rw [Finset.card_sigma] at h
  simpa [divMult] using h

theorem reflect_mem_nodes {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) :
    reflectSupport ρ ∈ C.nodes := by
  rw [mem_nodeSet (by linarith [C.hX2])] at hρ ⊢
  rw [reflectSupport_im, reflectSupport_re]
  refine ⟨hρ.1, ?_⟩
  rw [show 1 - (ρ : ℂ).re - 1 / 2 = -((ρ : ℂ).re - 1 / 2) by ring, abs_neg]
  exact hρ.2

theorem reflect_ne {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) : reflectSupport ρ ≠ ρ := by
  intro h
  have h1 := congrArg (fun ρ : XiDivisorSupport => (ρ : ℂ).re) h
  simp only [reflectSupport_re] at h1
  obtain ⟨-, h2⟩ := (mem_nodeSet (by linarith [C.hX2])).mp hρ
  have : (ρ : ℂ).re = 1 / 2 := by linarith
  rw [this, sub_self, abs_zero] at h2
  linarith [C.y₀_pos]

theorem two_le_orderSum {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) : 2 ≤ orderSum C.L := by
  have e : orderSum C.L = ∑ ν ∈ C.nodes, divMult ν := orderSum_nodeList _ _ _
  rw [e]
  have hsub : ({ρ, reflectSupport ρ} : Finset XiDivisorSupport) ⊆ C.nodes := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hρ
    · exact C.reflect_mem_nodes hρ
  have h := Finset.sum_le_sum_of_subset (f := divMult) hsub
  rw [Finset.sum_pair (C.reflect_ne hρ).symm] at h
  have := one_le_divMult ρ
  have := one_le_divMult (reflectSupport ρ)
  omega

theorem norm_node_le {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) :
    ‖gammaOf (ρ : ℂ)‖ ≤ C.t₀ + 2 := by
  obtain ⟨a, -, c⟩ := C.node_coords hρ
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have := C.hX2
  have h1 : |(gammaOf (ρ : ℂ)).re| ≤ C.t₀ + 1 := by
    have := abs_lt.mp a
    rw [abs_le]; constructor <;> linarith [C.ht₀]
  linarith

/-- `B = 2^N ∫ |Φ| e^{(3N/2)|u|}`. -/
def Bk : ℝ := 2 ^ windowCount C.t₀ * expTail Φ (3 / 2 * windowCount C.t₀) 0

theorem Bk_nonneg : 0 ≤ C.Bk := mul_nonneg (by positivity) (expTail_nonneg _ _ _)

theorem K_tail (c X : ℝ) (hc : 0 ≤ c) :
    expTail C.K c X ≤ 2 ^ windowCount C.t₀ * expTail Φ (c + 3 / 2 * windowCount C.t₀) X :=
  (multiResolvent_tail C.L superExpDecay_riemannPhiKernel (divisorData_nodeList _ _ _) c X hc).trans
    (pow_mul_expTail_le superExpDecay_riemannPhiKernel C.orderSum_le c X)

/-- The calculus of the divided kernel. -/
theorem K_calculus {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) :
    ∃ k₁ k₂ : ℝ → ℂ, (∀ x, HasDerivAt C.K (k₁ x) x) ∧ (∀ x, HasDerivAt k₁ (k₂ x) x) ∧
      Continuous k₁ ∧ Continuous k₂ ∧ Integrable k₁ ∧ Integrable k₂ ∧
      (∫ x, ‖C.K x‖) ≤ C.Bk ∧ (∫ x, ‖k₁ x‖) ≤ (1 + (C.t₀ + 2)) * C.Bk ∧
      (∫ x, ‖k₂ x‖) ≤ (1 + (C.t₀ + 2)) ^ 2 * C.Bk := by
  have hg := superExpDecay_riemannPhiKernel
  have hD := divisorData_nodeList C.t₀ C.X C.y₀
  have hpos : ∀ p ∈ C.L, 1 ≤ p.2 := by
    intro p hp
    obtain ⟨ν, -, rfl⟩ := mem_nodeList.mp hp
    exact one_le_divMult ν
  obtain ⟨a, b, g₂, ⟨pa, hpa, rfl⟩, ⟨pb, hpb, rfl⟩, hg₂, hgp, heq, htail₂, htailp⟩ :=
    multiResolvent_two_step hg hD hpos (C.two_le_orderSum hρ)
  have hnorm : ∀ p ∈ C.L, ‖p.1‖ ≤ C.t₀ + 2 := by
    intro p hp
    obtain ⟨ν, hν, rfl⟩ := mem_nodeList.mp hp
    exact C.norm_node_le hν
  have hL1 : ∀ f : ℝ → ℂ, (∀ c X : ℝ, 0 ≤ c → expTail f c X ≤
      2 ^ orderSum C.L * expTail Φ (c + 3 / 2 * orderSum C.L) X) → ∫ x, ‖f x‖ ≤ C.Bk := by
    intro f hf
    rw [integral_norm_eq_expTail]
    refine (hf 0 0 le_rfl).trans ?_
    have := pow_mul_expTail_le hg C.orderSum_le 0 0
    rw [zero_add]; unfold Bk; simpa using this
  have hK : SuperExpDecay C.K := (multiResolvent_spec C.L hg hD).1
  have hKt : ∀ c X : ℝ, 0 ≤ c → expTail C.K c X ≤
      2 ^ orderSum C.L * expTail Φ (c + 3 / 2 * orderSum C.L) X :=
    fun c X hc => multiResolvent_tail C.L hg hD c X hc
  have hh : SuperExpDecay (resolventDiv pa.1 (resolventDiv pb.1 g₂)) := by
    rw [← heq]; exact hK
  obtain ⟨k₁, k₂, hd1, hd2, ck₁, ck₂, ik₁, ik₂, nk₁, nk₂⟩ :=
    resolvent_pair_calculus hg₂ hgp hh (hnorm pa hpa) (hnorm pb hpb)
      (by rw [← heq]; exact hL1 _ hKt) (hL1 _ htailp) (hL1 _ htail₂)
  have heq' : C.K = resolventDiv pa.1 (resolventDiv pb.1 g₂) := heq
  refine ⟨k₁, k₂, ?_, hd2, ck₁, ck₂, ik₁, ik₂, hL1 _ hKt, nk₁, nk₂⟩
  intro x; rw [heq']; exact hd1 x

/-- The test at level `a`. -/
def test (a : ℝ) : ℝ → ℂ := clusterTest C.Q C.κ (heightPolarShift C.t₀) (a - 1 / 4) C.K

theorem natDegree_κ_le : (C.Q.natDegree : ℝ) * C.κ ≤ 1 / 8 := by
  have h : (C.Q.natDegree : ℝ) ≤ windowCount C.t₀ := by exact_mod_cast C.natDegree_Q_le
  have := C.κ_mul_count_le
  have := C.κ_pos
  nlinarith

theorem test_supp_bound (a : ℝ) :
    a - 1 / 4 + heightPolarShift C.t₀ + C.Q.natDegree * C.κ ≤ a := by
  have := (heightPolarShift_mem C.ht₀).2
  have := C.natDegree_κ_le
  linarith

theorem norm_Q_strip_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖C.Q.eval (Complex.exp (I * z * C.κ))‖ ≤ 2 * coeffMass C.Q := by
  rw [eval_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  unfold coeffMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul, norm_pow, C.norm_exp_I_mul_κ, mul_comm]
  gcongr
  have hk' : (k : ℝ) ≤ C.Q.natDegree := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← Real.exp_nat_mul]
  have hκ := C.κ_pos
  have h1 : (k : ℝ) * -(z.im * C.κ) ≤ 1 / 16 := by
    have h8 := C.natDegree_κ_le
    have hzi := (abs_le.mp hz).1
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h2 : (k : ℝ) * C.κ ≤ C.Q.natDegree * C.κ := mul_le_mul_of_nonneg_right hk' hκ.le
    have h3 : (k * C.κ) * (-z.im) ≤ (k * C.κ) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have h3 : Real.exp (1 / 16) ≤ 2 := by
    by_contra hc'
    push Not at hc'
    have hp : (2 : ℝ) ^ 16 ≤ Real.exp (1 / 16) ^ 16 := pow_le_pow_left₀ (by norm_num) hc'.le 16
    have he : Real.exp (1 / 16) ^ 16 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_lt_d9
    linarith
  exact (Real.exp_le_exp.mpr h1).trans h3

theorem coeffMass_le (hne : C.nodes.Nonempty) :
    coeffMass C.Q ≤ (windowCount C.t₀ + 1) * C.Mq := by
  unfold coeffMass
  have hb : ∀ k, ‖C.Q.coeff k‖ ≤ C.Mq :=
    HTGeometry.norm_coeff_le_of_forall_real C.Q C.κ_pos (C.norm_Q_eval_le hne)
  calc ∑ k ∈ Finset.range (C.Q.natDegree + 1), ‖C.Q.coeff k‖
      ≤ ∑ k ∈ Finset.range (C.Q.natDegree + 1), C.Mq := Finset.sum_le_sum fun k _ => hb k
    _ = (C.Q.natDegree + 1) * C.Mq := by rw [Finset.sum_const, Finset.card_range]; simp
    _ ≤ (windowCount C.t₀ + 1) * C.Mq := by
        have : (C.Q.natDegree : ℝ) ≤ windowCount C.t₀ := by exact_mod_cast C.natDegree_Q_le
        have := C.Mq_pos
        gcongr

/-- A divisor point as a nontrivial zero. -/
def toCarrier (ν : XiDivisorSupport) : zetaZeroConfig.carrier :=
  ⟨(ν : ℂ), divisorSupport_mem_carrier ν⟩

/-- The sign `±i` of a node. -/
def sgn (ν : XiDivisorSupport) : ℂ := if 0 < (gammaOf (ν : ℂ)).im then I else -I

theorem norm_Pp_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) : ‖C.Pp z‖ ≤ 3 := by
  have h := norm_polarSymbol_le (s := heightPolarShift C.t₀) (by linarith [(heightPolarShift_mem C.ht₀).1]) hz
  have h2 : Real.exp (heightPolarShift C.t₀ / 2) ≤ 3 / 2 := by
    have := (heightPolarShift_mem C.ht₀).2
    calc Real.exp (heightPolarShift C.t₀ / 2) ≤ Real.exp (OffLinePairData.sh / 2) := by
          apply Real.exp_le_exp.mpr; unfold OffLinePairData.sh; linarith
      _ ≤ 3 / 2 := OffLinePairData.exp_sh_half_le
  unfold Pp; linarith

/-- The transform of the test at a node is `±i` up to the truncation tail. -/
theorem test_at_node (a : ℝ) {ν : XiDivisorSupport} (hν : ν ∈ C.nodes) :
    ∃ Y : ℂ, paperFT (C.test a) (gammaOf (ν : ℂ)) = sgn ν - Y ∧
      ‖Y‖ ≤ 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := by
  obtain ⟨hK, -, hnode⟩ := C.K_spec
  have hγim : |(gammaOf (ν : ℂ)).im| ≤ 1 / 2 := (abs_gammaOf_divisorSupport_im_lt ν).le
  have hP : 1 ≤ ‖C.Pp (gammaOf (ν : ℂ))‖ := by
    apply one_le_norm_polarSymbol C.ht₀
    have := (C.node_coords hν).1
    linarith [C.hX2]
  have hP0 : C.Pp (gammaOf (ν : ℂ)) ≠ 0 := fun h => by rw [h, norm_zero] at hP; linarith
  have hK0 := hnode ν hν
  have hQ : C.Q.eval (Complex.exp (I * gammaOf (ν : ℂ) * C.κ)) = C.r ν := C.Q_eval_node hν
  have hPs : polarSymbol (heightPolarShift C.t₀) (gammaOf (ν : ℂ)) = C.Pp (gammaOf (ν : ℂ)) := rfl
  refine ⟨C.r ν * C.Pp (gammaOf (ν : ℂ)) * paperFT (tailK (a - 1 / 4) C.K) (gammaOf (ν : ℂ)),
    ?_, ?_⟩
  · unfold test
    rw [paperFT_clusterTest hK, hQ, hPs]
    have e : C.r ν * C.Pp (gammaOf (ν : ℂ)) * paperFT C.K (gammaOf (ν : ℂ)) = sgn ν := by
      unfold r sgn
      field_simp
    rw [mul_sub, e]
  · have h1 : ‖C.r ν‖ ≤ 2 * coeffMass C.Q := by rw [← hQ]; exact C.norm_Q_strip_le hγim
    have h2 := C.norm_Pp_le hγim
    have h3 := norm_paperFT_tailK_le hK (a - 1 / 4) hγim
    rw [norm_mul, norm_mul]
    have hc := coeffMass_nonneg C.Q
    calc ‖C.r ν‖ * ‖C.Pp (gammaOf (ν : ℂ))‖ * ‖paperFT (tailK (a - 1 / 4) C.K) (gammaOf (ν : ℂ))‖
        ≤ (2 * coeffMass C.Q) * 3 * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := by
          gcongr
      _ = 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := by ring

/-- The transform of the test at a zero that is not a node is the truncation tail. -/
theorem test_off_node (a : ℝ) {ρ : zetaZeroConfig.carrier}
    (hρ : ∀ ν ∈ C.nodes, (ρ : ℂ) ≠ (ν : ℂ)) :
    ‖paperFT (C.test a) (gammaOf (ρ : ℂ))‖ ≤
      6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := by
  obtain ⟨hK, hprod, -⟩ := C.K_spec
  set γ := gammaOf (ρ : ℂ)
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := ρ.2
    exact ⟨h.2.1, h.2.2⟩
  have hγim : |γ.im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip).le
  have hdiv : divisorEval C.L γ ≠ 0 := by
    refine C.divisorEval_ne_zero_of_not_node fun ν hν e => hρ ν hν ?_
    exact gammaOf_injective e
  have hK0 : paperFT C.K γ = 0 := by
    have h := hprod γ
    rw [riemannXiHat_gammaOf_eq_zero ρ.2] at h
    exact (mul_eq_zero.mp h).resolve_left hdiv
  unfold test
  rw [paperFT_clusterTest hK, hK0, zero_sub, mul_neg, norm_neg, norm_mul, norm_mul]
  have h1 := C.norm_Q_strip_le hγim
  have h2 := C.norm_Pp_le hγim
  have h3 := norm_paperFT_tailK_le hK (a - 1 / 4) hγim
  have hc := coeffMass_nonneg C.Q
  have : polarSymbol (heightPolarShift C.t₀) γ = C.Pp γ := rfl
  rw [this]
  calc ‖C.Q.eval (Complex.exp (I * γ * C.κ))‖ * ‖C.Pp γ‖ * ‖paperFT (tailK (a - 1 / 4) C.K) γ‖
      ≤ (2 * coeffMass C.Q) * 3 * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := by
        gcongr
    _ = 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := by ring

theorem sgn_mul_conj_sgn_reflect {ν : XiDivisorSupport} (hν : ν ∈ C.nodes) :
    sgn ν * (starRingEnd ℂ) (sgn (reflectSupport ν)) = -1 := by
  have h0 := C.node_im_ne_zero hν
  unfold sgn
  rw [gammaOf_reflectSupport, Complex.conj_im]
  rcases lt_or_gt_of_ne h0 with h | h
  · rw [if_neg (by linarith), if_pos (by linarith)]
    simp
  · rw [if_pos h, if_neg (by linarith)]
    simp

theorem norm_sgn (ν : XiDivisorSupport) : ‖sgn ν‖ = 1 := by
  unfold sgn; split_ifs <;> simp

/-- **The node block.** Every node contributes at most `m_ρ(-1 + 2η + η²)`. -/
theorem re_summand_node_le (a : ℝ) {ν : XiDivisorSupport} (hν : ν ∈ C.nodes) :
    (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
      (zetaZeroConfig.mult (toCarrier ν) : ℝ) *
        (-1 + 2 * (6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh)) +
          (6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh)) ^ 2) := by
  set η := 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh)
  obtain ⟨Y, hY, hYn⟩ := C.test_at_node a hν
  obtain ⟨Y', hY', hY'n⟩ := C.test_at_node a (C.reflect_mem_nodes hν)
  have hconj : (starRingEnd ℂ) (gammaOf ((toCarrier ν : zetaZeroConfig.carrier) : ℂ)) =
      gammaOf (reflectSupport ν : ℂ) := by
    rw [gammaOf_reflectSupport]; rfl
  unfold ZeroConfig.Wsummand
  rw [hconj]
  have hγ : gammaOf ((toCarrier ν : zetaZeroConfig.carrier) : ℂ) = gammaOf (ν : ℂ) := rfl
  rw [hγ, hY, hY']
  set X := sgn ν
  set X' := sgn (reflectSupport ν)
  have hXX := C.sgn_mul_conj_sgn_reflect hν
  have hX := norm_sgn ν
  have hX' := norm_sgn (reflectSupport ν)
  have e : (zetaZeroConfig.mult (toCarrier ν) : ℂ) * (X - Y) * (starRingEnd ℂ) (X' - Y') =
      ((zetaZeroConfig.mult (toCarrier ν) : ℝ) : ℂ) * ((X - Y) * (starRingEnd ℂ) (X' - Y')) := by
    push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hexp : (X - Y) * (starRingEnd ℂ) (X' - Y') = X * (starRingEnd ℂ) X' -
      X * (starRingEnd ℂ) Y' - Y * (starRingEnd ℂ) X' + Y * (starRingEnd ℂ) Y' := by
    rw [map_sub]; ring
  rw [hexp, hXX]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.one_re]
  have t1 : -(X * (starRingEnd ℂ) Y').re ≤ ‖Y'‖ := by
    have := Complex.abs_re_le_norm (X * (starRingEnd ℂ) Y')
    rw [norm_mul, hX, one_mul, RCLike.norm_conj] at this
    linarith [neg_abs_le (X * (starRingEnd ℂ) Y').re]
  have t2 : -(Y * (starRingEnd ℂ) X').re ≤ ‖Y‖ := by
    have := Complex.abs_re_le_norm (Y * (starRingEnd ℂ) X')
    rw [norm_mul, RCLike.norm_conj, hX', mul_one] at this
    linarith [neg_abs_le (Y * (starRingEnd ℂ) X').re]
  have t3 : (Y * (starRingEnd ℂ) Y').re ≤ ‖Y‖ * ‖Y'‖ := by
    have := Complex.re_le_norm (Y * (starRingEnd ℂ) Y')
    rwa [norm_mul, RCLike.norm_conj] at this
  have hη0 : 0 ≤ η := by
    have := coeffMass_nonneg C.Q; have := expTail_nonneg C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh)
    positivity
  have t4 : ‖Y‖ * ‖Y'‖ ≤ η ^ 2 := by
    rw [sq]; exact mul_le_mul hYn hY'n (norm_nonneg _) hη0
  linarith

theorem toCarrier_injective : Function.Injective toCarrier := fun _ _ h =>
  Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)

/-- **The raw cluster inequality.** If the level-`a` Hodge index holds and a node exists, then
with `η = 6 Σ|c_k| ε`, `ε` the truncation tail of `K` beyond `a - 3/8`,
`1 ≤ η (4 + 14 S_Z e^{a/2} · 4 Kp Σ|c_k| (1 + cosh(s/2)) (t₀+3)² B)`. -/
theorem cluster_inequality {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) {a : ℝ} (ha : 1 ≤ a)
    (hH : HodgeIndexAtLevel zetaZeroConfig a) {Kp : ℝ} (hKp2 : 2 ≤ Kp)
    (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    1 ≤ (6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh)) *
      (4 + 14 * zeroSumZ * Real.exp (a / 2) *
        (4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
          ((1 + (C.t₀ + 2)) ^ 2 * C.Bk))) := by
  classical
  set η := 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) with hη
  have hη0 : 0 ≤ η := by
    have := coeffMass_nonneg C.Q; have := expTail_nonneg C.K (1 / 2) (a - 1 / 4 - shw)
    positivity
  obtain ⟨hK, -, -⟩ := C.K_spec
  obtain ⟨k₁, k₂, hd1, hd2, ck₁, ck₂, ik₁, ik₂, nh, nk₁, nk₂⟩ := C.K_calculus hρ₀
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  obtain ⟨hC2, hN12⟩ := clusterTest_calculus hK hd1 hd2 ck₁ ck₂ ik₁ ik₂ hΓ nh nk₁ nk₂ C.Q C.κ
    (heightPolarShift C.t₀) (a - 1 / 4) hKp2 hKp
  have hsp0 : 0 ≤ heightPolarShift C.t₀ := by linarith [(heightPolarShift_mem C.ht₀).1]
  have hsupp : ∀ u, C.test a u ≠ 0 → |u| ≤ a :=
    clusterTest_supp C.κ_pos.le hsp0 (C.test_supp_bound a)
  have htsupp : tsupport (C.test a) ⊆ Icc (-a) a :=
    tsupport_clusterTest C.κ_pos.le hsp0 (C.test_supp_bound a)
  have hp1 : paperFT (C.test a) (I / 2) = 0 := by
    unfold test; rw [paperFT_clusterTest hK, polarSymbol_half_I]; ring
  have hp2 : paperFT (C.test a) (-(I / 2)) = 0 := by
    unfold test; rw [paperFT_clusterTest hK, polarSymbol_neg_half_I]; ring
  have hC2' : ContDiff ℝ 2 (C.test a) := hC2
  have hW0 := hH (C.test a) hC2' htsupp hp1 hp2
  set F : Finset zetaZeroConfig.carrier := C.nodes.image toCarrier with hF
  have hother : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F →
      ‖paperFT (C.test a) (gammaOf (ρ : ℂ))‖ ≤ η := by
    intro ρ hρ
    refine C.test_off_node a fun ν hν e => hρ ?_
    rw [hF, Finset.mem_image]
    exact ⟨ν, hν, Subtype.ext e.symm⟩
  have hsplit := re_W_le_nodes_add (by linarith) hC2' hsupp F hη0 hother
  set N12 := (∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖ with hN12def
  have hN120 : 0 ≤ N12 := by
    have h1 : 0 ≤ ∫ u, ‖C.test a u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv (C.test a)) u‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  have hS := zeroSumZ_nonneg
  -- the node block
  have hsumF : ∑ ρ ∈ F, (zetaZeroConfig.Wsummand (C.test a) (C.test a) ρ).re =
      ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re :=
    Finset.sum_image fun x _ y _ h => toCarrier_injective h
  set B' := 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
    ((1 + (C.t₀ + 2)) ^ 2 * C.Bk) with hB'
  have hNB : N12 ≤ B' := hN12
  have hexp := Real.exp_pos (a / 2)
  by_cases hηs : η ≤ 1 / 4
  · have hneg : -1 + 2 * η + η ^ 2 ≤ -(3 / 8) := by nlinarith
    have hterm : ∀ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
        (zetaZeroConfig.mult (toCarrier ν) : ℝ) * (-(3 / 8)) := by
      intro ν hν
      refine (C.re_summand_node_le a hν).trans ?_
      exact mul_le_mul_of_nonneg_left hneg (Nat.cast_nonneg _)
    have hblock : ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
        -(3 / 8) := by
      rw [← Finset.add_sum_erase _ _ hρ₀]
      have h1 := hterm ρ₀ hρ₀
      have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (toCarrier ρ₀) := by
        exact_mod_cast zetaZeroConfig.one_le_mult _ (toCarrier ρ₀).2
      have h2 : ∑ ν ∈ C.nodes.erase ρ₀,
          (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤ 0 := by
        refine Finset.sum_nonpos fun ν hν => (hterm ν (Finset.mem_of_mem_erase hν)).trans ?_
        have : (0 : ℝ) ≤ zetaZeroConfig.mult (toCarrier ν) := Nat.cast_nonneg _
        nlinarith
      nlinarith
    rw [hsumF] at hsplit
    have hR : 3 / 8 ≤ 5 * zeroSumZ * η * Real.exp (a / 2) * N12 := by nlinarith
    have hR' : 5 * zeroSumZ * η * Real.exp (a / 2) * N12 ≤ 5 * zeroSumZ * η * Real.exp (a / 2) * B' :=
      mul_le_mul_of_nonneg_left hNB (by positivity)
    nlinarith
  · push Not at hηs
    have : 0 ≤ 14 * zeroSumZ * Real.exp (a / 2) * B' := by
      have := hN120.trans hNB
      positivity
    nlinarith

/-- The explicit bound for the interpolant: it depends only on the height, the depth and the
window count. -/
def interpBound (t₀ δ₀ : ℝ) (W : ℕ) : ℝ :=
  32 * 3 ^ W * (32 * (W + 1 : ℝ)) ^ W * (16 * Real.exp 1 / δ₀) ^ (2 * W) *
    Real.exp (π * (t₀ + 1) / 4 + 2 + W * Real.log 5 + 3 * (windowLogConst * Real.log t₀)) / δ₀

theorem Mq_le_interpBound : C.Mq ≤ interpBound C.t₀ C.δ₀ (windowCount C.t₀) := by
  set W := windowCount C.t₀ with hW
  set E := π * (C.t₀ + 1) / 4 + 2 + W * Real.log 5 + 3 * (windowLogConst * Real.log C.t₀) with hE
  have hfL : frameLogLower C.t₀ = -E := by unfold frameLogLower; rw [hE]; ring
  have hδ := C.hδ₀
  have hy := C.y₀_pos
  have he := Real.exp_pos 1
  have hκ4 : C.κ / 4 * (32 * (W + 1 : ℝ)) = 1 := by
    unfold κ; field_simp; ring
  have hA : (C.κ / 4) ^ W * (32 * (W + 1 : ℝ)) ^ W = 1 := by rw [← mul_pow, hκ4, one_pow]
  have hDD : ((C.δ₀ / (16 * Real.exp 1)) ^ W) ^ 2 * (16 * Real.exp 1 / C.δ₀) ^ (2 * W) = 1 := by
    have hde : C.δ₀ / (16 * Real.exp 1) * (16 * Real.exp 1 / C.δ₀) = 1 := by field_simp
    rw [show (16 * Real.exp 1 / C.δ₀) ^ (2 * W) = ((16 * Real.exp 1 / C.δ₀) ^ W) ^ 2 by
      rw [← pow_mul, Nat.mul_comm W 2], ← mul_pow, ← mul_pow, hde, one_pow, one_pow]
  have hA0 : 0 < (C.κ / 4) ^ W := by have := C.κ_pos; positivity
  have hD0 : 0 < (C.δ₀ / (16 * Real.exp 1)) ^ W := by positivity
  have hMq : C.Mq = 8 * 3 ^ W * Real.exp E * (32 * (W + 1 : ℝ)) ^ W *
      (16 * Real.exp 1 / C.δ₀) ^ (2 * W) / C.y₀ := by
    unfold Mq Mb Lh
    rw [hfL, Real.exp_neg]
    have hEp := Real.exp_pos E
    generalize (C.κ / 4) ^ W = A at hA hA0 ⊢
    generalize (C.δ₀ / (16 * Real.exp 1)) ^ W = D at hDD hD0 ⊢
    generalize (32 * (W + 1 : ℝ)) ^ W = P at hA ⊢
    generalize (16 * Real.exp 1 / C.δ₀) ^ (2 * W) = R at hDD ⊢
    have hP : P = 1 / A := by field_simp; linarith
    have hR : R = 1 / D ^ 2 := by field_simp; linarith
    rw [hP, hR, ← hW]
    field_simp
    norm_num
  rw [hMq]
  unfold interpBound
  rw [← hE]
  have hpos : 0 ≤ 8 * 3 ^ W * Real.exp E * (32 * (W + 1 : ℝ)) ^ W *
      (16 * Real.exp 1 / C.δ₀) ^ (2 * W) := by positivity
  have hy' : 1 / C.y₀ ≤ 4 / C.δ₀ := by
    rw [div_le_div_iff₀ hy hδ]; linarith [C.hy₀]
  calc 8 * 3 ^ W * Real.exp E * (32 * (W + 1 : ℝ)) ^ W * (16 * Real.exp 1 / C.δ₀) ^ (2 * W) / C.y₀
      = (8 * 3 ^ W * Real.exp E * (32 * (W + 1 : ℝ)) ^ W * (16 * Real.exp 1 / C.δ₀) ^ (2 * W)) *
          (1 / C.y₀) := by ring
    _ ≤ (8 * 3 ^ W * Real.exp E * (32 * (W + 1 : ℝ)) ^ W * (16 * Real.exp 1 / C.δ₀) ^ (2 * W)) *
          (4 / C.δ₀) := mul_le_mul_of_nonneg_left hy' hpos
    _ = _ := by ring

theorem one_le_interpBound : 1 ≤ interpBound C.t₀ C.δ₀ (windowCount C.t₀) := by
  unfold interpBound
  have hδ := C.hδ₀
  have hδ1 := C.hδ₁
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have h1 : (1 : ℝ) ≤ 3 ^ windowCount C.t₀ := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (32 * (windowCount C.t₀ + 1 : ℝ)) ^ windowCount C.t₀ :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ windowCount C.t₀ := Nat.cast_nonneg _; linarith)
  have h3 : (1 : ℝ) ≤ (16 * Real.exp 1 / C.δ₀) ^ (2 * windowCount C.t₀) := by
    apply one_le_pow₀; rw [le_div_iff₀ hδ]; linarith
  have h4 : (1 : ℝ) ≤ Real.exp (π * (C.t₀ + 1) / 4 + 2 + windowCount C.t₀ * Real.log 5 +
      3 * (windowLogConst * Real.log C.t₀)) := by
    apply Real.one_le_exp
    have := Real.pi_pos
    have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have : 0 ≤ Real.log C.t₀ := Real.log_nonneg (by linarith [C.ht₀])
    have := windowLogConst_nonneg
    have : (0 : ℝ) ≤ windowCount C.t₀ := Nat.cast_nonneg _
    have : 0 ≤ C.t₀ + 1 := by linarith [C.ht₀]
    positivity
  rw [le_div_iff₀ hδ]
  have : 32 * 1 * 1 * 1 * 1 ≤ 32 * 3 ^ windowCount C.t₀ *
      (32 * (windowCount C.t₀ + 1 : ℝ)) ^ windowCount C.t₀ *
      (16 * Real.exp 1 / C.δ₀) ^ (2 * windowCount C.t₀) *
      Real.exp (π * (C.t₀ + 1) / 4 + 2 + windowCount C.t₀ * Real.log 5 +
        3 * (windowLogConst * Real.log C.t₀)) := by gcongr
  linarith

end ClusterSetup

/-! ## The cluster-robust Nyquist exclusion -/

local notation "Mθ" => jacobiThetaTailConstant

/-- **Cluster-robust Nyquist exclusion.** There is an absolute constant `K₀` such that, if the
level-`a` Hodge index holds (`a ≥ 1`), then every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > ½`
and `t₀ ≥ 101` satisfies

`1 ≤ K₀ · 2^N max(B_N, 1) · ((N+1) M)² · e^{a/2} (t₀+3)² · e^{(5 + 3N)X - π e^{2X}}`,

where `X = a - 3/8`, `N` is the number of zeros (with multiplicity) whose ordinate is within `2`
of `t₀`, `B_N = 2^N ∫|Φ| e^{3N|u|/2}`, and
`M = 32·3^N (32(N+1))^N (16e/δ₀)^{2N} e^{π(t₀+1)/4 + 2 + N log 5 + 3C log t₀}/δ₀`,
`δ₀ = β₀ - ½`, provided `6 + 3N ≤ 2πe^{2X}`.

No separation between zeros enters: the whole cluster of zeros of depth `> y₀` around `ρ₀` is
divided out of Riemann's kernel and interpolated by a shift operator whose size is controlled by
rectangle contours. Taking logarithms, `πe^{2a - 3/4} ≤ π t₀/2 + O(N (log N + log(1/δ₀)) +
log t₀ + N a)`, with `N = O(log t₀)`: the Hodge index at level `a` excludes every off-line zero
below height `2e^{2a-3/4} - O(log t₀ (log log t₀ + log(1/δ₀)))`. -/
theorem hodgeIndex_excludes_clustered_zero :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        1 ≤ K₀ * (2 ^ windowCount ρ₀.im *
            max (2 ^ windowCount ρ₀.im * expTail Φ (3 / 2 * windowCount ρ₀.im) 0) 1) *
          ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) ^ 2 *
          Real.exp (a / 2) * (ρ₀.im + 3) ^ 2 *
          Real.exp ((1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 9 / 2) * (a - 3 / 8) -
            π * Real.exp (2 * (a - 3 / 8))) := by
  obtain ⟨Kp, hKp2, hKp⟩ := OffLinePairData.exists_plateau_constant
  have hS := zeroSumZ_nonneg
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  set c₁ : ℝ := 140 * zeroSumZ * Kp with hc₁
  have hc₁0 : 0 ≤ c₁ := by
    rw [hc₁]; exact mul_nonneg (mul_nonneg (by norm_num) hS) (by linarith)
  refine ⟨6 * (4 + c₁) * (80 * Mθ * Real.exp π + 1), by positivity, ?_⟩
  intro a ha hH ρ₀ hρ₀ hβ ht hlam
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  -- the zero as a divisor point and the cluster setup
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero (by
    rw [xi_eq_xiUnit_mul_zeta (fun h => by rw [h] at hβ; norm_num at hβ)
      (fun h => by rw [h] at hnt; exact absurd hnt.2.2 (by norm_num)) hnt.2.1, hnt.1, mul_zero])
  set ν₀ : XiDivisorSupport := q.1
  have hν₀ : (ν₀ : ℂ) = ρ₀ := hq
  obtain ⟨C, hCt, hCδ⟩ := exists_clusterSetup ht (δ₀ := ρ₀.re - 1 / 2) (by linarith)
    (by linarith [hnt.2.2])
  have hν₀N : ν₀ ∈ C.nodes := by
    rw [mem_nodeSet (by linarith [C.hX2]), hν₀, hCt, sub_self, abs_zero]
    refine ⟨by linarith [C.hX1], ?_⟩
    rw [abs_of_pos (by linarith)]
    have := C.hy₁; rw [hCδ] at this; linarith
  have hraw := C.cluster_inequality hν₀N ha hH hKp2 hKp
  -- the pieces
  set W := windowCount C.t₀ with hWdef
  have hWt : windowCount C.t₀ = windowCount ρ₀.im := by rw [hCt]
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hne : C.nodes.Nonempty := ⟨ν₀, hν₀N⟩
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcM0 := coeffMass_nonneg C.Q
  -- the tail of the divided kernel
  obtain ⟨εΦ, hεΦdef⟩ : ∃ x, x = (80 * Mθ * Real.exp π + 1) *
    Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) :=
    ⟨_, rfl⟩
  have hε : expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) ≤ 2 ^ W * εΦ := by
    have h1 := C.K_tail (1 / 2) (a - 1 / 4 - OffLinePairData.sh) (by norm_num)
    have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by unfold OffLinePairData.sh; ring
    rw [hsh] at h1
    have h2 : expTail Φ (1 / 2 + 3 / 2 * W) (a - 3 / 8) ≤
        expTail Φ (1 / 2 + 3 / 2 * ((2 * W : ℕ) : ℝ)) (a - 3 / 8) := by
      apply expTail_mono_weight superExpDecay_riemannPhiKernel
      push_cast; have : (0 : ℝ) ≤ W := Nat.cast_nonneg _; linarith
    have h3 := expTail_riemannPhiKernel_level_le ha W (by rw [hWdef, hWt]; exact hlam)
    rw [hsh]
    calc expTail C.K (1 / 2) (a - 3 / 8) ≤ 2 ^ W * expTail Φ (1 / 2 + 3 / 2 * W) (a - 3 / 8) := h1
      _ ≤ 2 ^ W * εΦ := by rw [hεΦdef]; gcongr; exact h2.trans h3
  have hε0 : 0 ≤ expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := expTail_nonneg _ _ _
  have hεΦ0 : 0 ≤ εΦ := by rw [hεΦdef]; positivity
  have hcosh : 1 + Real.cosh (heightPolarShift C.t₀ / 2) ≤ 5 / 2 := by
    have := (heightPolarShift_mem C.ht₀).2
    have h := cosh_le_exp_abs (heightPolarShift C.t₀ / 2)
    rw [abs_of_pos (by linarith [(heightPolarShift_mem C.ht₀).1])] at h
    have h2 : Real.exp (heightPolarShift C.t₀ / 2) ≤ 3 / 2 :=
      (Real.exp_le_exp.mpr (by unfold OffLinePairData.sh; linarith)).trans
        OffLinePairData.exp_sh_half_le
    linarith
  have hB := C.Bk_nonneg
  have hMi0 : 0 ≤ Mi := by linarith
  have hW1 : (1 : ℝ) ≤ W + 1 := by have : (0 : ℝ) ≤ W := Nat.cast_nonneg _; linarith
  have hea := Real.one_le_exp (by linarith : (0 : ℝ) ≤ a / 2)
  have hT1 : (1 : ℝ) ≤ (C.t₀ + 3) ^ 2 := by have := C.ht₀; nlinarith
  have hT : (1 + (C.t₀ + 2)) ^ 2 = (C.t₀ + 3) ^ 2 := by ring
  rw [hT] at hraw
  -- opaque atoms
  obtain ⟨cM, hcMdef⟩ : ∃ x, x = coeffMass C.Q := ⟨_, rfl⟩
  obtain ⟨ε, hεdef⟩ : ∃ x, x = expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := ⟨_, rfl⟩
  obtain ⟨ch, hchdef⟩ : ∃ x, x = 1 + Real.cosh (heightPolarShift C.t₀ / 2) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ x, x = (C.t₀ + 3) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ea, hEadef⟩ : ∃ x, x = Real.exp (a / 2) := ⟨_, rfl⟩
  obtain ⟨Bk, hBkdef⟩ : ∃ x, x = C.Bk := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ x, x = zeroSumZ := ⟨_, rfl⟩
  rw [← hcMdef, ← hεdef, ← hchdef, ← hTdef, ← hEadef, ← hBkdef, ← hSdef] at hraw
  rw [← hcMdef] at hcM hcM0
  rw [← hεdef] at hε hε0
  rw [← hchdef] at hcosh
  rw [← hTdef] at hT1
  rw [← hEadef] at hea
  rw [← hBkdef] at hB
  rw [← hSdef] at hS hc₁
  have hch0 : 0 ≤ ch := by rw [hchdef]; have := Real.cosh_pos (heightPolarShift C.t₀ / 2); linarith
  set Bm := max Bk 1 with hBmdef
  have hBm : Bk ≤ Bm := le_max_left _ _
  have hBm1 : 1 ≤ Bm := le_max_right _ _
  have hK0 : 0 ≤ Kp := by linarith
  -- the product `P = (N+1) Mi Ea T Bm ≥ 1`
  obtain ⟨P, hPdef⟩ : ∃ x, x = (W + 1) * Mi * Ea * T * Bm := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hW1 hMi1) hea) hT1) hBm1
  have hinner : 4 + 14 * S * Ea * (4 * Kp * (cM * ch) * (T * Bk)) ≤ (4 + c₁) * P := by
    have h1 : cM * ch ≤ ((W + 1) * Mi) * (5 / 2) :=
      mul_le_mul hcM hcosh hch0 (by positivity)
    have h2 : T * Bk ≤ T * Bm := mul_le_mul_of_nonneg_left hBm (by linarith)
    have h3 : 4 * Kp * (cM * ch) * (T * Bk) ≤ 4 * Kp * (((W + 1) * Mi) * (5 / 2)) * (T * Bm) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
        (mul_nonneg (by linarith) hB) (by positivity)
    have h4 : 14 * S * Ea * (4 * Kp * (cM * ch) * (T * Bk)) ≤
        14 * S * Ea * (4 * Kp * (((W + 1) * Mi) * (5 / 2)) * (T * Bm)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 14 * S * Ea * (4 * Kp * (((W + 1) * Mi) * (5 / 2)) * (T * Bm)) = c₁ * P := by
      rw [hc₁, hPdef]; ring
    have h6 : 4 ≤ 4 * P := by linarith
    linarith
  have hfinal : 1 ≤ (6 * cM * ε) * ((4 + c₁) * P) :=
    hraw.trans (mul_le_mul_of_nonneg_left hinner (by positivity))
  have hfinal2 : (6 * cM * ε) * ((4 + c₁) * P) ≤ (6 * ((W + 1) * Mi) * (2 ^ W * εΦ)) * ((4 + c₁) * P) := by
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (by linarith))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcM (by norm_num)) hε hε0
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hMi0))
  have hgoal := hfinal.trans hfinal2
  -- rewrite into the stated form
  rw [← hWt, ← hCt]
  have hδ' : ρ₀.re - 1 / 2 = C.δ₀ := hCδ.symm
  have hBkC : 2 ^ W * expTail Φ (3 / 2 * W) 0 = Bk := by rw [hBkdef]; rfl
  have hMiC : ClusterSetup.interpBound C.t₀ (ρ₀.re - 1 / 2) W = Mi := by rw [hδ', hMidef]
  rw [hBkC, hMiC, ← hEadef, ← hTdef]
  rw [hPdef] at hgoal
  calc (1 : ℝ) ≤ _ := hgoal
    _ = 6 * (4 + c₁) * (80 * Mθ * Real.exp π + 1) * (2 ^ W * Bm) * ((W + 1) * Mi) ^ 2 * Ea * T *
          Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) -
            π * Real.exp (2 * (a - 3 / 8))) := by
        rw [hεΦdef]; ring

theorem log_interpBound (t₀ δ₀ : ℝ) (hδ : 0 < δ₀) (W : ℕ) :
    Real.log (ClusterSetup.interpBound t₀ δ₀ W) = Real.log 32 + W * Real.log 3 +
      W * Real.log (32 * (W + 1 : ℝ)) + 2 * W * Real.log (16 * Real.exp 1 / δ₀) +
      (π * (t₀ + 1) / 4 + 2 + W * Real.log 5 + 3 * (windowLogConst * Real.log t₀)) -
      Real.log δ₀ := by
  unfold ClusterSetup.interpBound
  have he := Real.exp_pos 1
  have h1 : (0 : ℝ) < 32 * (W + 1 : ℝ) := by positivity
  have h2 : (0 : ℝ) < 16 * Real.exp 1 / δ₀ := by positivity
  rw [Real.log_div (by positivity) hδ.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast; ring

/-- **The Nyquist horizon for clusters, logarithmic form.** Under the level-`a` Hodge index
(`a ≥ 1`), every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > ½`, `t₀ ≥ 101` and
`6 + 3N ≤ 2πe^{2X}`, `X = a - 3/8`, satisfies

`π e^{2X} ≤ π(t₀+1)/2 + 2 log(N+1) + 2 L_N(t₀, δ₀) + a/2 + 2 log(t₀+3) + (5+3N) X + log(K₀ 2^N B_N)`,

where `L_N = log 32 + N log 3 + N log(32(N+1)) + 2N log(16e/δ₀) + 2 + N log 5 + 3C log t₀
- log δ₀` and `B_N = max(2^N ∫|Φ| e^{3N|u|/2}, 1)`. Since `N = O(log t₀)`, the right side is
`π t₀/2 + O(log t₀ · (log log t₀ + log(1/δ₀)) + a log t₀)`: no zero with `β₀ > ½` exists below
`t₀ ≈ 2e^{2a-3/4}`, whatever the clustering. -/
theorem hodgeIndex_cluster_nyquist_horizon :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {a : ℝ}, 1 ≤ a → HodgeIndexAtLevel zetaZeroConfig a →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        π * Real.exp (2 * (a - 3 / 8)) ≤ π * (ρ₀.im + 1) / 2 +
          2 * Real.log (windowCount ρ₀.im + 1) +
          2 * (Real.log 32 + windowCount ρ₀.im * Real.log 3 +
            windowCount ρ₀.im * Real.log (32 * (windowCount ρ₀.im + 1 : ℝ)) +
            2 * windowCount ρ₀.im * Real.log (16 * Real.exp 1 / (ρ₀.re - 1 / 2)) +
            (2 + windowCount ρ₀.im * Real.log 5 + 3 * (windowLogConst * Real.log ρ₀.im)) -
            Real.log (ρ₀.re - 1 / 2)) +
          a / 2 + 2 * Real.log (ρ₀.im + 3) +
          (1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 9 / 2) * (a - 3 / 8) +
          Real.log (K₀ * (2 ^ windowCount ρ₀.im *
            max (2 ^ windowCount ρ₀.im * expTail Φ (3 / 2 * windowCount ρ₀.im) 0) 1)) := by
  obtain ⟨K₀, hK₀, h⟩ := hodgeIndex_excludes_clustered_zero
  refine ⟨K₀, hK₀, fun {a} ha hH {ρ₀} hρ₀ hβ ht hlam => ?_⟩
  have hmain := h ha hH hρ₀ hβ ht hlam
  set W := windowCount ρ₀.im
  set δ₀ := ρ₀.re - 1 / 2
  have hδ : 0 < δ₀ := by simp only [δ₀]; linarith
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound ρ₀.im δ₀ W := ⟨_, rfl⟩
  obtain ⟨Bm, hBmdef⟩ : ∃ x, x = K₀ * (2 ^ W * max (2 ^ W * expTail Φ (3 / 2 * W) 0) 1) :=
    ⟨_, rfl⟩
  have hBm : 0 < Bm := by rw [hBmdef]; positivity
  have hMi : 0 < Mi := by
    rw [hMidef]; unfold ClusterSetup.interpBound; have := Real.exp_pos 1; positivity
  rw [← hMidef] at hmain
  have hmain' : 1 ≤ Bm * ((W + 1) * Mi) ^ 2 * Real.exp (a / 2) * (ρ₀.im + 3) ^ 2 *
      Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) := by
    rw [hBmdef]; linarith [hmain]
  have hW1 : (0 : ℝ) < W + 1 := by positivity
  have ht3 : (0 : ℝ) < ρ₀.im + 3 := by linarith
  have hlog := Real.log_nonneg hmain'
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_exp, Real.log_mul hBm.ne' (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul hW1.ne' hMi.ne'] at hlog
  have hLMi := log_interpBound ρ₀.im δ₀ hδ W
  rw [← hMidef] at hLMi
  rw [← hBmdef]
  push_cast at hlog
  nlinarith [hLMi]

end

end RHTower
