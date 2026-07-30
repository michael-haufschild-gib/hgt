import GaloisForLFunctions.RHTower.SoninCofinalGlobalEulerCarrier

/-!
# Source-global singular-grade Sonin corona

Finite Sonin packets do not by themselves define one source-global chart:
their cofinal depths may depend on the packet.  This file removes that
dependence in two exact steps.

First, uniformly bounded moving sections are identified when their difference
is little-oh of a chosen positive singular scale.  The resulting quotient is
the singular-grade corona; equality is equality of grade classes, not equality
of depth schedules.

Second, a constructive countable diagonal controls the first `n + 1` source
coordinates at stage `n`.  One strictly cofinal depth schedule then transports
every fixed father/detail pair and every corresponding codiagonal with
`o(epsilon)` error.  No uniform bound on the moving packet is assumed: the
stagewise depth absorbs its complete finite load.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- Two moving sections determine the same singular grade when their
difference is little-oh of the positive grade scale. -/
def SingularGradeEquivalent
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (x y : ℕ → H) : Prop :=
  Tendsto (fun n => ‖x n - y n‖ / epsilon n) atTop (𝓝 0)

/-- Any two sections which recover a common reference to `o(epsilon)` have
the same singular grade. -/
theorem singularGradeEquivalent_of_common_reference
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (x y z : ℕ → H)
    (hx : Tendsto (fun n => ‖x n - z n‖ / epsilon n) atTop (𝓝 0))
    (hy : Tendsto (fun n => ‖y n - z n‖ / epsilon n) atTop (𝓝 0)) :
    SingularGradeEquivalent epsilon x y := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (norm_nonneg _) (hepsilon n).le)
    (Filter.Eventually.of_forall fun n => ?_)
    (by simpa using hx.add hy)
  calc
    ‖x n - y n‖ / epsilon n ≤
        (‖x n - z n‖ + ‖y n - z n‖) / epsilon n := by
      apply div_le_div_of_nonneg_right _ (hepsilon n).le
      calc
        ‖x n - y n‖ =
            ‖(x n - z n) + (z n - y n)‖ := by
          congr 1
          abel
        _ ≤ ‖x n - z n‖ + ‖z n - y n‖ := norm_add_le _ _
        _ = ‖x n - z n‖ + ‖y n - z n‖ := by
          congr 1
          exact norm_sub_rev _ _
    _ = ‖x n - z n‖ / epsilon n +
        ‖y n - z n‖ / epsilon n := by
      rw [add_div]

theorem singularGradeEquivalent_refl
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (x : ℕ → H) :
    SingularGradeEquivalent epsilon x x := by
  simp [SingularGradeEquivalent]

theorem singularGradeEquivalent_symm
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) {x y : ℕ → H}
    (hxy : SingularGradeEquivalent epsilon x y) :
    SingularGradeEquivalent epsilon y x := by
  simpa only [SingularGradeEquivalent, norm_sub_rev] using hxy

theorem singularGradeEquivalent_trans
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    {x y z : ℕ → H}
    (hxy : SingularGradeEquivalent epsilon x y)
    (hyz : SingularGradeEquivalent epsilon y z) :
    SingularGradeEquivalent epsilon x z := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (norm_nonneg _) (hepsilon n).le)
    (Filter.Eventually.of_forall fun n => ?_)
    (by simpa using hxy.add hyz)
  calc
    ‖x n - z n‖ / epsilon n ≤
        (‖x n - y n‖ + ‖y n - z n‖) / epsilon n := by
      apply div_le_div_of_nonneg_right _ (hepsilon n).le
      calc
        ‖x n - z n‖ =
            ‖(x n - y n) + (y n - z n)‖ := by
          congr 1
          abel
        _ ≤ ‖x n - y n‖ + ‖y n - z n‖ := norm_add_le _ _
    _ = ‖x n - y n‖ / epsilon n +
        ‖y n - z n‖ / epsilon n := by
      rw [add_div]

theorem singularGradeEquivalent_equivalence
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n) :
    Equivalence (SingularGradeEquivalent (H := H) epsilon) := by
  constructor
  · exact singularGradeEquivalent_refl epsilon
  · intro x y h
    exact singularGradeEquivalent_symm epsilon h
  · intro x y z hxy hyz
    exact singularGradeEquivalent_trans epsilon hepsilon hxy hyz

/-- Exact setoid of all singular-grade sections. -/
def singularGradeSetoid
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n) :
    Setoid (ℕ → H) where
  r := SingularGradeEquivalent epsilon
  iseqv := singularGradeEquivalent_equivalence epsilon hepsilon

/-- A section whose norm is uniformly bounded on the depth ray. -/
def SingularGradeBounded
    {H : Type*} [NormedAddCommGroup H] (x : ℕ → H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖x n‖ ≤ C

/-- Uniformly bounded sections on the depth ray. -/
def SingularGradeSection
    (H : Type*) [NormedAddCommGroup H] :=
  {x : ℕ → H // SingularGradeBounded x}

/-- Singular-grade equivalence restricted to uniformly bounded sections. -/
def singularGradeSectionSetoid
    (H : Type*) [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n) :
    Setoid (SingularGradeSection H) where
  r := fun x y => SingularGradeEquivalent epsilon x.1 y.1
  iseqv := by
    constructor
    · intro x
      exact singularGradeEquivalent_refl epsilon x.1
    · intro x y h
      exact singularGradeEquivalent_symm epsilon h
    · intro x y z hxy hyz
      exact singularGradeEquivalent_trans epsilon hepsilon hxy hyz

/-- Exact bounded singular-grade corona: uniformly bounded sections modulo
little-oh schedule difference. -/
def SingularGradeCorona
    (H : Type*) [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n) :=
  Quotient (singularGradeSectionSetoid H epsilon hepsilon)

/-- Two bounded representatives which recover the same reference to
`o(epsilon)` determine exactly the same corona class. -/
theorem singularGradeCorona_mk_eq_of_common_reference
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (x y : SingularGradeSection H) (z : ℕ → H)
    (hx : Tendsto (fun n => ‖x.1 n - z n‖ / epsilon n) atTop (𝓝 0))
    (hy : Tendsto (fun n => ‖y.1 n - z n‖ / epsilon n) atTop (𝓝 0)) :
    (Quotient.mk (singularGradeSectionSetoid H epsilon hepsilon) x :
        SingularGradeCorona H epsilon hepsilon) =
      Quotient.mk (singularGradeSectionSetoid H epsilon hepsilon) y := by
  exact Quotient.sound
    (singularGradeEquivalent_of_common_reference
      epsilon hepsilon x.1 y.1 z hx hy)

/-- **Countable-packet singular codiagonal law.**  One schedule transports
every fixed father/detail pair and its off-diagonal Gram coordinate at the
same singular grade.  Stage `n` controls the first `n + 1` source
coordinates, so the conclusion is genuinely countable rather than a family
of coordinate-dependent subsequences. -/
theorem exists_strictMono_singularDiagonal_transport_countable_codiagonal
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (B : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] K)
    (T : H →L[ℂ] K)
    (hbasis : ∀ i : ℕ, Tendsto (fun N =>
      T (A N (lp.single 2 i 1)) - B N (lp.single 2 i 1))
      atTop (𝓝 0))
    (father detail : ℕ → ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      ∀ i : ℕ,
        Tendsto (fun n =>
          ‖T (A (depth n) (father n i)) -
              B (depth n) (father n i)‖ / epsilon n)
          atTop (𝓝 0) ∧
        Tendsto (fun n =>
          ‖T (A (depth n) (detail n i)) -
              B (depth n) (detail n i)‖ / epsilon n)
          atTop (𝓝 0) ∧
        Tendsto (fun n =>
          ‖inner ℂ
                (T (A (depth n) (father n i)))
                (T (A (depth n) (detail n i))) -
              inner ℂ (father n i) (detail n i)‖ / epsilon n)
          atTop (𝓝 0) := by
  let load : ℕ → ℝ := fun n =>
    ∑ i ∈ Finset.range (n + 1),
      (‖T‖ * ‖detail n i‖ + ‖father n i‖)
  let scale : ℕ → ℝ := fun n =>
    epsilon n ^ 2 / (1 + load n)
  have hloadNonneg (n : ℕ) : 0 ≤ load n := by
    dsimp [load]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hdenPos (n : ℕ) : 0 < 1 + load n := by
    linarith [hloadNonneg n]
  have hscalePos (n : ℕ) : 0 < scale n := by
    exact div_pos (sq_pos_of_pos (hepsilon n)) (hdenPos n)
  have hscaleLe (n : ℕ) : scale n ≤ epsilon n ^ 2 := by
    dsimp [scale]
    rw [div_le_iff₀ (hdenPos n)]
    nlinarith [sq_nonneg (epsilon n), hloadNonneg n]
  have htermLe (n i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖T‖ * ‖detail n i‖ + ‖father n i‖ ≤ load n := by
    dsimp [load]
    exact Finset.single_le_sum
      (fun j _ => by
        exact add_nonneg
          (mul_nonneg (norm_nonneg T) (norm_nonneg (detail n j)))
          (norm_nonneg (father n j)))
      hi
  have hscaleLoadLe (n : ℕ) :
      scale n * load n ≤ epsilon n ^ 2 := by
    calc
      scale n * load n ≤ scale n * (1 + load n) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (hscalePos n).le
      _ = epsilon n ^ 2 := by
        dsimp [scale]
        field_simp [(hdenPos n).ne']
  have hthreshold : ∀ n : ℕ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ∀ i ∈ Finset.range (n + 1),
        ‖T (A N (father n i)) - B N (father n i)‖ ≤ scale n ∧
        ‖T (A N (detail n i)) - B N (detail n i)‖ ≤ scale n := by
    intro n
    have hevent : ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ Finset.range (n + 1),
          ‖T (A N (father n i)) - B N (father n i)‖ ≤ scale n ∧
          ‖T (A N (detail n i)) - B N (detail n i)‖ ≤ scale n := by
      apply (eventually_all_finset (Finset.range (n + 1))).2
      intro i hi
      have hfather :=
        cofinalOrthonormalEmbedding_strong_transport A B T hbasis (father n i)
      have hdetail :=
        cofinalOrthonormalEmbedding_strong_transport A B T hbasis (detail n i)
      have hfatherEventually : ∀ᶠ N : ℕ in atTop,
          ‖T (A N (father n i)) - B N (father n i)‖ < scale n := by
        have hball := hfather.eventually
          (Metric.ball_mem_nhds (0 : ℝ) (hscalePos n))
        filter_upwards [hball] with N hN
        simpa [Real.dist_eq] using hN
      have hdetailEventually : ∀ᶠ N : ℕ in atTop,
          ‖T (A N (detail n i)) - B N (detail n i)‖ < scale n := by
        have hball := hdetail.eventually
          (Metric.ball_mem_nhds (0 : ℝ) (hscalePos n))
        filter_upwards [hball] with N hN
        simpa [Real.dist_eq] using hN
      filter_upwards [hfatherEventually, hdetailEventually] with N hF hD
      exact ⟨hF.le, hD.le⟩
    exact eventually_atTop.1 hevent
  choose threshold hthresholdBound using hthreshold
  let depth : ℕ → ℕ :=
    fun n => n + ∑ k ∈ Finset.range (n + 1), threshold k
  have hdepthThreshold (n : ℕ) : threshold n ≤ depth n := by
    simp only [depth, Finset.sum_range_succ]
    omega
  have hdepthMono : StrictMono depth := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [depth, Finset.sum_range_succ]
    omega
  have hindexEventually (i : ℕ) :
      ∀ᶠ n : ℕ in atTop, i ∈ Finset.range (n + 1) :=
    eventually_atTop.2 ⟨i, fun n hn => by simp; omega⟩
  have hfatherAt (n i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖T (A (depth n) (father n i)) -
          B (depth n) (father n i)‖ ≤ scale n :=
    (hthresholdBound n (depth n) (hdepthThreshold n) i hi).1
  have hdetailAt (n i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      ‖T (A (depth n) (detail n i)) -
          B (depth n) (detail n i)‖ ≤ scale n :=
    (hthresholdBound n (depth n) (hdepthThreshold n) i hi).2
  refine ⟨depth, hdepthMono, ?_⟩
  intro i
  constructor
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (by
        filter_upwards [hindexEventually i] with n hi
        rw [div_le_iff₀ (hepsilon n)]
        simpa only [pow_two] using (hfatherAt n i hi).trans (hscaleLe n))
      hepsilonZero
  constructor
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (by
        filter_upwards [hindexEventually i] with n hi
        rw [div_le_iff₀ (hepsilon n)]
        simpa only [pow_two] using (hdetailAt n i hi).trans (hscaleLe n))
      hepsilonZero
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun n =>
        div_nonneg (norm_nonneg _) (hepsilon n).le)
      (by
        filter_upwards [hindexEventually i] with n hi
        rw [div_le_iff₀ (hepsilon n)]
        have hdecomp :
            inner ℂ
                  (T (A (depth n) (father n i)))
                  (T (A (depth n) (detail n i))) -
                inner ℂ (father n i) (detail n i) =
              inner ℂ
                  (T (A (depth n) (father n i)) -
                    B (depth n) (father n i))
                  (T (A (depth n) (detail n i))) +
                inner ℂ (B (depth n) (father n i))
                  (T (A (depth n) (detail n i)) -
                    B (depth n) (detail n i)) := by
          rw [← (B (depth n)).inner_map_map (father n i) (detail n i),
            inner_sub_left, inner_sub_right]
          abel
        rw [hdecomp]
        calc
          ‖inner ℂ
                (T (A (depth n) (father n i)) -
                  B (depth n) (father n i))
                (T (A (depth n) (detail n i))) +
              inner ℂ (B (depth n) (father n i))
                (T (A (depth n) (detail n i)) -
                  B (depth n) (detail n i))‖ ≤
              ‖T (A (depth n) (father n i)) -
                  B (depth n) (father n i)‖ *
                  ‖T (A (depth n) (detail n i))‖ +
                ‖B (depth n) (father n i)‖ *
                  ‖T (A (depth n) (detail n i)) -
                    B (depth n) (detail n i)‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
          _ ≤ scale n * (‖T‖ * ‖detail n i‖) +
                ‖father n i‖ * scale n := by
            exact add_le_add
              (mul_le_mul (hfatherAt n i hi)
                (by
                  calc
                    ‖T (A (depth n) (detail n i))‖ ≤
                        ‖T‖ * ‖A (depth n) (detail n i)‖ := T.le_opNorm _
                    _ = ‖T‖ * ‖detail n i‖ := by
                      rw [LinearIsometry.norm_map])
                (norm_nonneg _)
                (hscalePos n).le)
              (by
                rw [LinearIsometry.norm_map]
                exact mul_le_mul_of_nonneg_left
                  (hdetailAt n i hi) (norm_nonneg _))
          _ = scale n *
              (‖T‖ * ‖detail n i‖ + ‖father n i‖) := by ring
          _ ≤ scale n * load n :=
            mul_le_mul_of_nonneg_left (htermLe n i hi) (hscalePos n).le
          _ ≤ epsilon n * epsilon n := by
            simpa only [pow_two] using hscaleLoadLe n)
      hepsilonZero

/-- Two admissible codiagonal depth schedules define the same singular-grade
section.  This is the exact schedule-independence statement used by the
source-global corona: schedules need not agree pointwise or cofinally. -/
theorem singularCodiagonal_schedules_equivalent
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : ℕ → lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] H)
    (T : H →L[ℂ] K)
    (father detail : ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (depth₁ depth₂ : ℕ → ℕ)
    (hdepth₁ : Tendsto (fun n =>
      ‖inner ℂ
            (T (A (depth₁ n) (father n)))
            (T (A (depth₁ n) (detail n))) -
          inner ℂ (father n) (detail n)‖ / epsilon n)
      atTop (𝓝 0))
    (hdepth₂ : Tendsto (fun n =>
      ‖inner ℂ
            (T (A (depth₂ n) (father n)))
            (T (A (depth₂ n) (detail n))) -
          inner ℂ (father n) (detail n)‖ / epsilon n)
      atTop (𝓝 0)) :
    SingularGradeEquivalent epsilon
      (fun n => inner ℂ
        (T (A (depth₁ n) (father n)))
        (T (A (depth₁ n) (detail n))))
      (fun n => inner ℂ
        (T (A (depth₂ n) (father n)))
        (T (A (depth₂ n) (detail n)))) := by
  exact singularGradeEquivalent_of_common_reference epsilon hepsilon _ _ _
    hdepth₁ hdepth₂

/-- **Source-global countable Sonin codiagonal chart.**  The actual
non-diagonal Sonin dilation corner transports every coordinate in a
countable moving Euler father/detail family through one common strictly
cofinal schedule, including every corresponding codiagonal. -/
theorem exists_centralSoninDilationCorner_singularDiagonal_countable_codiagonal
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (father detail : ℕ → ℕ → lp (fun _ : ℕ => ℂ) 2)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (hepsilonZero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      ∀ i : ℕ,
        Tendsto (fun n =>
          ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
                centralSoninProjection a)
                (cofinalInverseDilatedShellEmbedding
                  c d r hc hcd hr (depth n) (father n i)) -
              cofinalEvenShellEmbedding c d hc hcd
                (depth n) (father n i)‖ /
            epsilon n)
          atTop (𝓝 0) ∧
        Tendsto (fun n =>
          ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
                centralSoninProjection a)
                (cofinalInverseDilatedShellEmbedding
                  c d r hc hcd hr (depth n) (detail n i)) -
              cofinalEvenShellEmbedding c d hc hcd
                (depth n) (detail n i)‖ /
            epsilon n)
          atTop (𝓝 0) ∧
        Tendsto (fun n =>
          ‖inner ℂ
                ((crossBoundary (centralSoninProjection a)
                      (dilationSum r hr) ∘L centralSoninProjection a)
                  (cofinalInverseDilatedShellEmbedding
                    c d r hc hcd hr (depth n) (father n i)))
                ((crossBoundary (centralSoninProjection a)
                      (dilationSum r hr) ∘L centralSoninProjection a)
                  (cofinalInverseDilatedShellEmbedding
                    c d r hc hcd hr (depth n) (detail n i))) -
              inner ℂ (father n i) (detail n i)‖ / epsilon n)
          atTop (𝓝 0) := by
  apply exists_strictMono_singularDiagonal_transport_countable_codiagonal
    (A := cofinalInverseDilatedShellEmbedding c d r hc hcd hr)
    (B := cofinalEvenShellEmbedding c d hc hcd)
    (T := crossBoundary (centralSoninProjection a) (dilationSum r hr) ∘L
      centralSoninProjection a)
    (hbasis := by
      intro i
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [cofinalInverseDilatedEvenShell, cofinalEvenShell] using!
        (centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
          a c d r ha hc hcd hda hr harc).comp
            (tendsto_add_atTop_nat i))
    (father := father) (detail := detail)
    (epsilon := epsilon) hepsilon hepsilonZero

end RHTower
