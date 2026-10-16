import GaloisForLFunctions.RHTower.CHMDSpectralRiemannCriterion
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity

/-!
# Primitive bound states are paid for by off-line zeros

Let `R` be the arithmetic resolvent and suppose only finitely many nontrivial zeros of `ζ` lie off
the critical line. Then every orthonormal family of primitive eigenvectors of `R` with eigenvalues
above `1/2` has at most `2 · #(off-line zeros)` members.

Mechanism. The zero side of Weil's form is `W(f,f) = Σ_ρ m_ρ f̂(γ_ρ) conj f̂(γ̄_ρ)`; each summand is
at least `−(m_ρ/2)|f̂(γ_ρ) − f̂(γ̄_ρ)|²`, and the defect `f̂(γ_ρ) − f̂(γ̄_ρ)` vanishes at every
on-line zero. So `Re W(f,f) + Σ_{off-line ρ} (m_ρ/2)|defect_ρ(f)|² ≥ 0`: the Weil form is
nonnegative up to a finite-rank correction indexed by the off-line zeros. On the span of the Riesz
lifts of `k` orthonormal primitive eigenvectors above `1/2` the Weil form is negative definite
(`≤ −δ Σ c_i²`); negative definiteness survives a small perturbation of the basis to compact tests
(the Weil form is a bounded quadratic form), and on compact tests the Weil form is the zero-side
form. The linear map `c ↦ (defect_ρ(Σ c_i f_i))_ρ` into `ℂ^{off-line}` is then injective, hence
`k ≤ 2 · #(off-line zeros)`.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## The zero-side defect inequality -/

/-- The off-line nontrivial zeros. -/
def offLineZeros : Set ℂ := {ρ | ρ ∈ zetaZeroConfig.carrier ∧ ρ.re ≠ 1 / 2}

/-- The defect functional of a zero: `f̂(γ_ρ) − f̂(conj γ_ρ)`; it vanishes at on-line zeros. -/
def zeroDefect (f : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  paperFT f (gammaOf ρ) - paperFT f ((starRingEnd ℂ) (gammaOf ρ))

theorem zeroDefect_eq_zero {f : ℝ → ℂ} {ρ : ℂ} (h : ρ.re = 1 / 2) : zeroDefect f ρ = 0 := by
  unfold zeroDefect
  rw [ZeroSide.gammaOf_of_re_eq_half h, Complex.conj_ofReal, sub_self]

/-- The defect weight `(m_ρ/2)‖zeroDefect f ρ‖²`. -/
def defectWeight (f : ℝ → ℂ) (ρ : ℂ) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) / 2 * ‖zeroDefect f ρ‖ ^ 2

theorem defectWeight_nonneg (f : ℝ → ℂ) (ρ : ℂ) : 0 ≤ defectWeight f ρ := by
  unfold defectWeight
  positivity

theorem defectWeight_eq_zero {f : ℝ → ℂ} {ρ : ℂ} (h : ρ.re = 1 / 2) : defectWeight f ρ = 0 := by
  unfold defectWeight
  rw [zeroDefect_eq_zero h, norm_zero]
  ring

/-- Pointwise: every zero's Weil summand is at least minus its defect weight. -/
theorem neg_defectWeight_le_re_Wsummand (f : ℝ → ℂ) (ρ : ℂ) :
    -defectWeight f ρ ≤ (zetaZeroConfig.Wsummand f f ρ).re := by
  unfold defectWeight zeroDefect ZeroConfig.Wsummand
  have hm : (0 : ℝ) ≤ (zetaZeroConfig.mult ρ : ℝ) := Nat.cast_nonneg _
  have h1 : ((zetaZeroConfig.mult ρ : ℂ) * paperFT f (gammaOf ρ) *
      (starRingEnd ℂ) (paperFT f ((starRingEnd ℂ) (gammaOf ρ)))).re =
      (zetaZeroConfig.mult ρ : ℝ) * (paperFT f (gammaOf ρ) *
        (starRingEnd ℂ) (paperFT f ((starRingEnd ℂ) (gammaOf ρ)))).re := by
    rw [← Complex.ofReal_natCast, mul_assoc, Complex.re_ofReal_mul]
  have h2 := Complex.normSq_sub (paperFT f (gammaOf ρ)) (paperFT f ((starRingEnd ℂ) (gammaOf ρ)))
  have h3 : ‖paperFT f (gammaOf ρ) - paperFT f ((starRingEnd ℂ) (gammaOf ρ))‖ ^ 2 =
      Complex.normSq (paperFT f (gammaOf ρ) - paperFT f ((starRingEnd ℂ) (gammaOf ρ))) :=
    Complex.sq_norm _
  rw [h1, h3]
  have h4 := mul_nonneg hm (Complex.normSq_nonneg (paperFT f (gammaOf ρ)))
  have h5 := mul_nonneg hm (Complex.normSq_nonneg (paperFT f ((starRingEnd ℂ) (gammaOf ρ))))
  have h6 : (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (paperFT f (gammaOf ρ) -
      paperFT f ((starRingEnd ℂ) (gammaOf ρ))) = (zetaZeroConfig.mult ρ : ℝ) *
      (Complex.normSq (paperFT f (gammaOf ρ)) + Complex.normSq (paperFT f ((starRingEnd ℂ) (gammaOf ρ))) -
        2 * (paperFT f (gammaOf ρ) * (starRingEnd ℂ) (paperFT f ((starRingEnd ℂ) (gammaOf ρ)))).re) := by
    rw [h2]
  nlinarith [h4, h5, h6]

open Classical in
/-- The off-line zeros as a finset of the carrier. -/
def offLineFinset (hfin : offLineZeros.Finite) : Finset zetaZeroConfig.carrier :=
  hfin.toFinset.subtype (· ∈ zetaZeroConfig.carrier)

theorem mem_offLineFinset (hfin : offLineZeros.Finite) {ρ : zetaZeroConfig.carrier} :
    ρ ∈ offLineFinset hfin ↔ (ρ : ℂ).re ≠ 1 / 2 := by
  classical
  unfold offLineFinset
  rw [Finset.mem_subtype, hfin.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨ρ.2, h⟩⟩

theorem card_offLineFinset (hfin : offLineZeros.Finite) :
    (offLineFinset hfin).card = offLineZeros.ncard := by
  classical
  unfold offLineFinset
  rw [Finset.card_subtype, Finset.filter_true_of_mem fun ρ hρ => (hfin.mem_toFinset.mp hρ).1,
    Set.ncard_eq_toFinset_card _ hfin]

/-- **Zero-side bound**: `Re W(f,f) + Σ_{off-line ρ} (m_ρ/2)‖f̂(γ_ρ) − f̂(γ̄_ρ)‖² ≥ 0`. -/
theorem re_W_add_defect_nonneg (hfin : offLineZeros.Finite) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    0 ≤ (zetaZeroConfig.W f f).re + ∑ ρ ∈ offLineFinset hfin, defectWeight f ρ := by
  have hs := WeilConditional.summable_Wsummand hf hfc
  have hre : (zetaZeroConfig.W f f).re =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.Wsummand f f ρ).re := by
    unfold ZeroConfig.W
    exact Complex.re_tsum hs
  have hsre : Summable fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.Wsummand f f ρ).re :=
    hs.mapL Complex.reCLM
  have hDzero : ∀ ρ ∉ offLineFinset hfin, defectWeight f ρ = 0 := by
    intro ρ hρ
    rw [mem_offLineFinset] at hρ
    exact defectWeight_eq_zero (not_not.mp hρ)
  have hDs : Summable fun ρ : zetaZeroConfig.carrier => defectWeight f ρ :=
    summable_of_ne_finset_zero hDzero
  have hDsum : ∑' ρ : zetaZeroConfig.carrier, defectWeight f ρ =
      ∑ ρ ∈ offLineFinset hfin, defectWeight f ρ := tsum_eq_sum hDzero
  have hle : ∑' ρ : zetaZeroConfig.carrier, (-defectWeight f ρ) ≤
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.Wsummand f f ρ).re :=
    Summable.tsum_le_tsum (fun ρ => neg_defectWeight_le_re_Wsummand f ρ) hDs.neg hsre
  rw [tsum_neg] at hle
  rw [hre, ← hDsum]
  linarith

/-! ## Negative definiteness on the span of the Riesz lifts -/

theorem rieszLift_sum {k : ℕ} (c : Fin k → ℝ) (e : Fin k → MassSpace) :
    rieszLift (∑ i, c i • e i) = ∑ i, c i • rieszLift (e i) := by
  apply rieszLift_unique
  intro q
  rw [sum_inner, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_graph, real_inner_smul_left, inner_rieszLift]

theorem weilForm_le_sourceEnergy_of_primitive {p : SourceGraph} (hp : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    weilForm p ≤ sourceEnergy p := by
  unfold weilForm
  rw [hp]
  nlinarith [sq_nonneg ⟪p.val.fst, tanhL⟫_ℝ]

/-- On the span of the Riesz lifts of orthonormal primitive eigenvectors above `1/2` the Weil
form is negative definite. -/
theorem weilForm_rieszLift_sum_le {k : ℕ} {e : Fin k → MassSpace} (he : Orthonormal ℝ e)
    {μ : Fin k → ℝ} (hprim : ∀ i, ⟪e i, oneL⟫_ℝ = 0) (heig : ∀ i, resolvent (e i) = μ i • e i)
    {δ : ℝ} (hδ : ∀ i, δ ≤ μ i * (2 * μ i - 1)) (c : Fin k → ℝ) :
    weilForm (∑ i, c i • rieszLift (e i)) ≤ -δ * ∑ i, c i ^ 2 := by
  rw [← rieszLift_sum]
  set w := ∑ i, c i • e i with hw
  have hwprim : ⟪w, oneL⟫_ℝ = 0 := by
    rw [hw, sum_inner]
    exact Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_left, hprim i, mul_zero]
  have hRw : resolvent w = ∑ i, (c i * μ i) • e i := by
    rw [hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig i, smul_smul]
  have h1 : ⟪w, resolvent w⟫_ℝ = ∑ i, c i ^ 2 * μ i := by
    rw [hRw, hw, he.inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.conj_to_real]
    ring
  have h2 : ‖resolvent w‖ ^ 2 = ∑ i, c i ^ 2 * μ i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hRw, he.inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.conj_to_real]
    ring
  have hE := sourceEnergy_rieszLift w
  have hW := weilForm_le_sourceEnergy_of_primitive (primitiveGraph_rieszLift hwprim)
  rw [hE, h1, h2] at hW
  calc weilForm (rieszLift w) ≤ ∑ i, c i ^ 2 * μ i - 2 * ∑ i, c i ^ 2 * μ i ^ 2 := hW
    _ = ∑ i, c i ^ 2 * (μ i * (1 - 2 * μ i)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ∑ i, c i ^ 2 * (-δ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hδ i]) (sq_nonneg _)
    _ = -δ * ∑ i, c i ^ 2 := by
        rw [← Finset.sum_mul]
        ring

/-! ## The Weil form is a bounded quadratic form -/

/-- The bilinear form underlying the Weil form. -/
def weilBilin (p q : SourceGraph) : ℝ :=
  ⟪p, q⟫_ℝ - 2 * ⟪p.val.fst, q.val.fst⟫_ℝ + 2 * (⟪p.val.fst, oneL⟫_ℝ * ⟪q.val.fst, oneL⟫_ℝ) -
    2 * (⟪p.val.fst, tanhL⟫_ℝ * ⟪q.val.fst, tanhL⟫_ℝ)

theorem weilForm_eq_weilBilin (p : SourceGraph) : weilForm p = weilBilin p p := by
  unfold weilForm weilBilin
  rw [sourceEnergy_eq_graph_sub, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  ring

theorem weilBilin_sub_left (p p' q : SourceGraph) :
    weilBilin (p - p') q = weilBilin p q - weilBilin p' q := by
  unfold weilBilin
  have h : (p - p').val.fst = p.val.fst - p'.val.fst := rfl
  rw [h, inner_sub_graph, inner_sub_left, inner_sub_left, inner_sub_left]
  ring

theorem weilBilin_comm (p q : SourceGraph) : weilBilin p q = weilBilin q p := by
  unfold weilBilin
  rw [real_inner_comm p q, real_inner_comm p.val.fst q.val.fst]
  ring

theorem weilBilin_sub_right (p q q' : SourceGraph) :
    weilBilin p (q - q') = weilBilin p q - weilBilin p q' := by
  rw [weilBilin_comm, weilBilin_sub_left, weilBilin_comm q, weilBilin_comm q']

/-- The bound constant of the Weil bilinear form. -/
def weilBilinConst : ℝ := 1 + 2 + 2 * ‖oneL‖ ^ 2 + 2 * ‖tanhL‖ ^ 2

theorem weilBilinConst_pos : 0 < weilBilinConst := by
  unfold weilBilinConst
  positivity

theorem abs_weilBilin_le (p q : SourceGraph) : |weilBilin p q| ≤ weilBilinConst * (‖p‖ * ‖q‖) := by
  unfold weilBilin weilBilinConst
  have hp := norm_source_le_graph p
  have hq := norm_source_le_graph q
  have hpq : 0 ≤ ‖p‖ * ‖q‖ := by positivity
  have h1 : |⟪p, q⟫_ℝ| ≤ ‖p‖ * ‖q‖ := abs_real_inner_le_norm _ _
  have h2 : |⟪p.val.fst, q.val.fst⟫_ℝ| ≤ ‖p‖ * ‖q‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hp hq (norm_nonneg _) (norm_nonneg _))
  have h3 : |⟪p.val.fst, oneL⟫_ℝ * ⟪q.val.fst, oneL⟫_ℝ| ≤ ‖oneL‖ ^ 2 * (‖p‖ * ‖q‖) := by
    rw [abs_mul]
    calc |⟪p.val.fst, oneL⟫_ℝ| * |⟪q.val.fst, oneL⟫_ℝ|
        ≤ (‖p.val.fst‖ * ‖oneL‖) * (‖q.val.fst‖ * ‖oneL‖) :=
          mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _)
            (by positivity)
      _ ≤ (‖p‖ * ‖oneL‖) * (‖q‖ * ‖oneL‖) := by gcongr
      _ = ‖oneL‖ ^ 2 * (‖p‖ * ‖q‖) := by ring
  have h4 : |⟪p.val.fst, tanhL⟫_ℝ * ⟪q.val.fst, tanhL⟫_ℝ| ≤ ‖tanhL‖ ^ 2 * (‖p‖ * ‖q‖) := by
    rw [abs_mul]
    calc |⟪p.val.fst, tanhL⟫_ℝ| * |⟪q.val.fst, tanhL⟫_ℝ|
        ≤ (‖p.val.fst‖ * ‖tanhL‖) * (‖q.val.fst‖ * ‖tanhL‖) :=
          mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _)
            (by positivity)
      _ ≤ (‖p‖ * ‖tanhL‖) * (‖q‖ * ‖tanhL‖) := by gcongr
      _ = ‖tanhL‖ ^ 2 * (‖p‖ * ‖q‖) := by ring
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

theorem abs_weilForm_sub_le (p q : SourceGraph) :
    |weilForm p - weilForm q| ≤ weilBilinConst * ((‖p‖ + ‖q‖) * ‖p - q‖) := by
  rw [weilForm_eq_weilBilin, weilForm_eq_weilBilin]
  have h : weilBilin p p - weilBilin q q = weilBilin (p - q) p + weilBilin q (p - q) := by
    rw [weilBilin_sub_left, weilBilin_sub_right]
    ring
  rw [h]
  calc |weilBilin (p - q) p + weilBilin q (p - q)|
      ≤ |weilBilin (p - q) p| + |weilBilin q (p - q)| := abs_add_le _ _
    _ ≤ weilBilinConst * (‖p - q‖ * ‖p‖) + weilBilinConst * (‖q‖ * ‖p - q‖) :=
        add_le_add (abs_weilBilin_le _ _) (abs_weilBilin_le _ _)
    _ = weilBilinConst * ((‖p‖ + ‖q‖) * ‖p - q‖) := by ring

/-! ## Negative definiteness survives perturbation to compact tests -/

theorem sum_sq_pos_of_ne_zero {k : ℕ} {c : Fin k → ℝ} (hc : c ≠ 0) : 0 < ∑ i, c i ^ 2 := by
  by_contra h0
  rw [not_lt] at h0
  have h0' : ∑ i, c i ^ 2 = 0 := le_antisymm h0 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h0'
  exact hc (funext fun i => pow_eq_zero_iff two_ne_zero |>.mp (h0' i (Finset.mem_univ i)))

theorem exists_compactTests_negative_definite {k : ℕ} (p : Fin k → SourceGraph) {δ : ℝ}
    (hδ : 0 < δ) (hneg : ∀ c : Fin k → ℝ, weilForm (∑ i, c i • p i) ≤ -δ * ∑ i, c i ^ 2) :
    ∃ q : Fin k → SourceGraph, (∀ i, q i ∈ compactTests) ∧
      ∀ c : Fin k → ℝ, c ≠ 0 → weilForm (∑ i, c i • q i) < 0 := by
  have hC := weilBilinConst_pos
  set C := weilBilinConst with hC_def
  set P : ℝ := ∑ i, ‖p i‖ with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => norm_nonneg _
  set X : ℝ := C * (2 * P + 1) * ((k : ℝ) + 1) with hX
  have hX0 : 0 < X := by positivity
  set η : ℝ := min 1 (δ / (2 * X)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : X * η ≤ δ / 2 := by
    have h := min_le_right 1 (δ / (2 * X))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have happ : ∀ i, ∃ q : SourceGraph, q ∈ compactTests ∧ ‖q - p i‖ < η := fun i => by
    obtain ⟨q, hq, hd⟩ := dense_compactTests.exists_dist_lt (p i) hη0
    exact ⟨q, hq, by rwa [dist_comm, dist_eq_norm] at hd⟩
  choose q hq hqd using happ
  refine ⟨q, hq, fun c hc => ?_⟩
  set S : ℝ := ∑ i, |c i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hx : ‖∑ i, c i • p i‖ ≤ P * S := by
    calc ‖∑ i, c i • p i‖ ≤ ∑ i, ‖c i • p i‖ := norm_sum_le _ _
      _ = ∑ i, |c i| * ‖p i‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |c i| * P := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun j _ => norm_nonneg (p j)) (Finset.mem_univ i)) (abs_nonneg _)
      _ = P * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hxy : ‖∑ i, c i • p i - ∑ i, c i • q i‖ ≤ η * S := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i, (c i • p i - c i • q i)‖ ≤ ∑ i, ‖c i • p i - c i • q i‖ := norm_sum_le _ _
      _ = ∑ i, |c i| * ‖p i - q i‖ := by simp only [← smul_sub, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |c i| * η := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (by rw [norm_sub_rev]; exact (hqd i).le) (abs_nonneg _)
      _ = η * S := by rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hy : ‖∑ i, c i • q i‖ ≤ (P + η) * S := by
    have h := norm_sub_norm_le (∑ i, c i • q i) (∑ i, c i • p i)
    rw [norm_sub_rev] at h
    nlinarith
  have hS2 : S ^ 2 ≤ k * ∑ i, c i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|)
    simpa [sq_abs, Finset.card_univ, Fintype.card_fin] using h
  have hsumpos : 0 < ∑ i, c i ^ 2 := sum_sq_pos_of_ne_zero hc
  have hdiff := abs_weilForm_sub_le (∑ i, c i • q i) (∑ i, c i • p i)
  rw [norm_sub_rev] at hdiff
  have hub : weilForm (∑ i, c i • q i) ≤ weilForm (∑ i, c i • p i) +
      C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖) := by
    have := (abs_le.mp hdiff).2
    linarith
  have hcorr : C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖) ≤
      X * η * ∑ i, c i ^ 2 := by
    have h1 : (‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖ ≤
        ((P + η) * S + P * S) * (η * S) :=
      mul_le_mul (add_le_add hy hx) hxy (norm_nonneg _) (by positivity)
    have h2 : ((P + η) * S + P * S) * (η * S) = (2 * P + η) * η * S ^ 2 := by ring
    have h3 : (2 * P + η) * η * S ^ 2 ≤ (2 * P + 1) * η * (k * ∑ i, c i ^ 2) := by
      have h : (2 * P + η) * η ≤ (2 * P + 1) * η := by nlinarith
      calc (2 * P + η) * η * S ^ 2 ≤ (2 * P + 1) * η * S ^ 2 :=
            mul_le_mul_of_nonneg_right h (sq_nonneg _)
        _ ≤ (2 * P + 1) * η * (k * ∑ i, c i ^ 2) :=
            mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h4 : (2 * P + 1) * η * (k * ∑ i, c i ^ 2) ≤ (2 * P + 1) * ((k : ℝ) + 1) * η * ∑ i, c i ^ 2 := by
      have h5 : (0 : ℝ) ≤ (2 * P + 1) * η * ∑ i, c i ^ 2 := by positivity
      nlinarith
    calc C * ((‖∑ i, c i • q i‖ + ‖∑ i, c i • p i‖) * ‖∑ i, c i • p i - ∑ i, c i • q i‖)
        ≤ C * ((2 * P + 1) * ((k : ℝ) + 1) * η * ∑ i, c i ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [h1, h2, h3, h4]) hC.le
      _ = X * η * ∑ i, c i ^ 2 := by rw [hX]; ring
  have hfinal : X * η * ∑ i, c i ^ 2 ≤ δ / 2 * ∑ i, c i ^ 2 :=
    mul_le_mul_of_nonneg_right hηδ hsumpos.le
  have hneg' := hneg c
  calc weilForm (∑ i, c i • q i) ≤ -δ * ∑ i, c i ^ 2 + δ / 2 * ∑ i, c i ^ 2 := by linarith
    _ = -(δ / 2) * ∑ i, c i ^ 2 := by ring
    _ < 0 := by nlinarith

/-! ## Sources of combinations of compact tests -/

theorem Lp_coeFn_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → MassSpace) :
    ((∑ i ∈ s, c i • f i : MassSpace) : ℝ → ℝ) =ᵐ[massMeasure] fun x => ∑ i ∈ s, c i * f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 massMeasure] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • f a) (∑ i ∈ s, c i • f i), Lp.coeFn_smul (c a) (f a), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, Finset.sum_insert ha]

theorem paperFT_sum_mul {k : ℕ} (c : Fin k → ℝ) (g : Fin k → ℝ → ℂ) (hg : ∀ i, Continuous (g i))
    (hgc : ∀ i, HasCompactSupport (g i)) (z : ℂ) :
    paperFT (fun u => ∑ i, (c i : ℂ) * g i u) z = ∑ i, (c i : ℂ) * paperFT (g i) z := by
  simp only [paperFT_def]
  have hint : ∀ i, Integrable fun u => g i u * Complex.exp (Complex.I * z * (u : ℂ)) := fun i =>
    ((hg i).mul (Complex.continuous_exp.comp (by fun_prop))).integrable_of_hasCompactSupport
      (hgc i).mul_right
  have h : (fun u => (∑ i, (c i : ℂ) * g i u) * Complex.exp (Complex.I * z * (u : ℂ))) =
      fun u => ∑ i, (c i : ℂ) * (g i u * Complex.exp (Complex.I * z * (u : ℂ))) := by
    funext u
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, integral_finsetSum _ fun i _ => (hint i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem contDiff_phiDoobTest_ofReal {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 fun x => (phiDoobTest v x : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_phiDoobTest hv)

theorem hasCompactSupport_phiDoobTest_ofReal {v : ℝ → ℝ} (hvc : HasCompactSupport v) :
    HasCompactSupport fun x => (phiDoobTest v x : ℂ) :=
  (hasCompactSupport_phiDoobTest hvc).comp_left Complex.ofReal_zero

/-! ## The index bound -/

/-- **Index bound.** If the Weil form is negative definite on the span of `k` compact tests, then
`k ≤ 2 · #(off-line zeros)` (when the latter is finite). -/
theorem card_le_two_mul_offLine_of_negative_definite (hfin : offLineZeros.Finite) {k : ℕ}
    (q : Fin k → SourceGraph) (hq : ∀ i, q i ∈ compactTests)
    (hneg : ∀ c : Fin k → ℝ, c ≠ 0 → weilForm (∑ i, c i • q i) < 0) :
    k ≤ 2 * offLineZeros.ncard := by
  classical
  have hv : ∀ i, ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      q i = compactLift v hv hvc := hq
  choose v hv hvc hqv using hv
  set T := offLineFinset hfin with hT
  let a : Fin k → T → ℂ := fun i ρ => zeroDefect (fun x => (phiDoobTest (v i) x : ℂ)) ((ρ : zetaZeroConfig.carrier) : ℂ)
  let L : (Fin k → ℝ) →ₗ[ℝ] (T → ℂ) :=
    { toFun := fun c ρ => ∑ i, (c i : ℂ) * a i ρ
      map_add' := fun c d => by
        funext ρ
        simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext ρ
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Finset.smul_sum,
          Complex.real_smul, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    have hmem : (∑ i, c i • q i) ∈ compactTests :=
      Submodule.sum_mem _ fun i _ => compactTests.smul_mem _ (hq i)
    obtain ⟨w, hw, hwc, hqw⟩ := hmem
    have hW := weilForm_compactLift w hw hwc
    rw [← hqw] at hW
    -- the source of the combination is `Σ cᵢ vᵢ`
    have h2 : (compactLift w hw hwc).val.fst = ∑ i, c i • (q i).val.fst := by
      rw [← hqw]
      show sourceMap (∑ i, c i • q i) = ∑ i, c i • sourceMap (q i)
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h1 : ((compactLift w hw hwc).val.fst : ℝ → ℝ) =ᵐ[massMeasure] w :=
      compactLift_source_ae w hw hwc
    rw [h2] at h1
    have h3 := Lp_coeFn_sum_smul Finset.univ c fun i => (q i).val.fst
    have h4 : ∀ i, ((q i).val.fst : ℝ → ℝ) =ᵐ[massMeasure] v i := fun i => by
      rw [hqv i]
      exact compactLift_source_ae _ _ _
    have h4' : ∀ᵐ x ∂massMeasure, ∀ i, (q i).val.fst x = v i x := ae_all_iff.mpr h4
    have h5 : w =ᵐ[massMeasure] fun x => ∑ i, c i * v i x := by
      filter_upwards [h1, h3, h4'] with x hx1 hx3 hx4
      rw [← hx1, hx3]
      exact Finset.sum_congr rfl fun i _ => by rw [hx4 i]
    have h6 := volume_absolutelyContinuous_mass.ae_eq h5
    have hae : (fun x => (phiDoobTest w x : ℂ)) =ᵐ[volume]
        fun x => ∑ i, (c i : ℂ) * (phiDoobTest (v i) x : ℂ) := by
      filter_upwards [h6] with x hx
      simp only [phiDoobTest, hx]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hFT : ∀ z, paperFT (fun x => (phiDoobTest w x : ℂ)) z =
        ∑ i, (c i : ℂ) * paperFT (fun x => (phiDoobTest (v i) x : ℂ)) z := by
      intro z
      rw [← paperFT_sum_mul c (fun i x => (phiDoobTest (v i) x : ℂ))
        (fun i => (contDiff_phiDoobTest_ofReal (hv i)).continuous)
        (fun i => hasCompactSupport_phiDoobTest_ofReal (hvc i)) z]
      simp only [paperFT_def]
      exact integral_congr_ae (hae.mul (ae_eq_refl _))
    have hdef : ∀ ρ ∈ T, zeroDefect (fun x => (phiDoobTest w x : ℂ)) ρ = 0 := by
      intro ρ hρ
      have hL : L c ⟨ρ, hρ⟩ = 0 := by rw [hc]; rfl
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, a] at hL
      unfold zeroDefect at hL ⊢
      rw [hFT, hFT, ← Finset.sum_sub_distrib, ← hL]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hbound := re_W_add_defect_nonneg hfin (contDiff_phiDoobTest_ofReal hw)
      (hasCompactSupport_phiDoobTest_ofReal hwc)
    have hzero : ∑ ρ ∈ T, defectWeight (fun x => (phiDoobTest w x : ℂ)) ρ = 0 :=
      Finset.sum_eq_zero fun ρ hρ => by
        unfold defectWeight
        rw [hdef ρ hρ, norm_zero]
        ring
    rw [hzero, add_zero] at hbound
    have hneg' := hneg c hc0
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex,
    Finset.card_univ, Fintype.card_coe, card_offLineFinset, smul_eq_mul] at h
  linarith

/-! ## The Birman–Schwinger bound -/

/-- **Primitive bound states are paid for by off-line zeros.** If only finitely many nontrivial
zeros lie off the critical line, every orthonormal family of primitive eigenvectors of the
arithmetic resolvent with eigenvalues above `1/2` has at most `2 · #(off-line zeros)` members. -/
theorem orthonormal_primitive_bound_states_le (hfin : offLineZeros.Finite) {k : ℕ}
    {e : Fin k → MassSpace} (he : Orthonormal ℝ e) {μ : Fin k → ℝ} (hμ : ∀ i, 1 / 2 < μ i)
    (hprim : ∀ i, ⟪e i, oneL⟫_ℝ = 0) (heig : ∀ i, resolvent (e i) = μ i • e i) :
    k ≤ 2 * offLineZeros.ncard := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · omega
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => μ i * (2 * μ i - 1))
    Finset.univ_nonempty
  have hδ : 0 < μ i₀ * (2 * μ i₀ - 1) := mul_pos (by linarith [hμ i₀]) (by linarith [hμ i₀])
  have hneg := weilForm_rieszLift_sum_le he hprim heig (fun i => hi₀ i (Finset.mem_univ i))
  obtain ⟨q, hq, hqneg⟩ := exists_compactTests_negative_definite (fun i => rieszLift (e i)) hδ hneg
  exact card_le_two_mul_offLine_of_negative_definite hfin q hq hqneg

end RHTower.CHMDPolar
